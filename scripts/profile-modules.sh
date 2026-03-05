#!/usr/bin/env bash
set -euo pipefail

# Strip leaked ghost cfg flags that break stable cargo flows
unset RUSTFLAGS
unset CARGO_ENCODED_RUSTFLAGS
if [[ -z "${TMPDIR:-}" || ! -d "${TMPDIR:-/nonexistent}" || ! -w "${TMPDIR:-/nonexistent}" ]]; then
  export TMPDIR="/tmp"
fi

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
TOOLCHAIN="${VERUS_TOOLCHAIN:-1.93.0-x86_64-unknown-linux-gnu}"

if [[ "${1:-}" == "-h" || "${1:-}" == "--help" ]]; then
  cat <<'EOF'
usage: ./scripts/profile-modules.sh [--top N] [--raw]

Run full crate verification with per-function timing and print a sorted
breakdown showing where SMT time is spent.

options:
  --top N  show top N functions (default: 25)
  --raw    print raw JSON output instead of the sorted summary
  -h       show this help
EOF
  exit 0
fi

RAW=0
TOP_N=25
while [[ "$#" -gt 0 ]]; do
  case "${1:-}" in
    --raw) RAW=1 ;;
    --top)
      TOP_N="${2:-25}"
      shift
      ;;
    *) echo "error: unknown arg '$1'"; exit 1 ;;
  esac
  shift
done

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  echo "error: cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus"
  echo "hint: build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
  exit 1
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  echo "error: expected patched z3 at $VERUS_SOURCE/z3"
  echo "hint: build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
  exit 1
fi

JSON_FILE="$(mktemp)"
trap 'rm -f "$JSON_FILE"' EXIT

run_cargo_verus() {
  if command -v rustup >/dev/null 2>&1; then
    export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
    export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
    export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
    cd "$ROOT_DIR"
    cargo verus verify --manifest-path Cargo.toml -p verus-gui \
      -- --output-json --time-expanded --triggers-mode silent 2>/dev/null > "$JSON_FILE"
  elif command -v nix-shell >/dev/null 2>&1; then
    nix-shell -p rustup --run "
      set -euo pipefail
      export RUSTUP_TOOLCHAIN='$TOOLCHAIN'
      export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
      export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
      cd '$ROOT_DIR'
      cargo verus verify --manifest-path Cargo.toml -p verus-gui \
        -- --output-json --time-expanded --triggers-mode silent 2>/dev/null > '$JSON_FILE'
    "
  else
    echo "error: neither rustup nor nix-shell found in PATH"
    exit 1
  fi
}

echo "=== verus-gui function profile ===" >&2
echo "" >&2

WALL_START="$(date +%s)"
set +e
run_cargo_verus
VERUS_STATUS=$?
set -e
WALL_END="$(date +%s)"
WALL_ELAPSED=$((WALL_END - WALL_START))

if [[ $RAW -eq 1 ]]; then
  cat "$JSON_FILE"
  exit $VERUS_STATUS
fi

# Parse JSON and print sorted per-function timing
python3 - "$JSON_FILE" "$TOP_N" "$WALL_ELAPSED" <<'PYEOF'
import json, sys

json_path = sys.argv[1]
top_n = int(sys.argv[2])
wall = int(sys.argv[3])

with open(json_path) as f:
    data = json.load(f)

times = data.get("times-ms", {})
smt = times.get("smt", {})
verified = data.get("verification-results", {}).get("verified", "?")
errors = data.get("verification-results", {}).get("errors", "?")

# Collect per-function data from smt-run-module-times
funcs = []
for mod in smt.get("smt-run-module-times", []):
    for fn in mod.get("function-breakdown", []):
        name = fn["function"].split("::")[-1]
        module = mod["module"]
        funcs.append({
            "name": name,
            "module": module,
            "time_us": fn["time-micros"],
            "rlimit": fn["rlimit"],
            "ok": fn.get("success", True),
        })

funcs.sort(key=lambda x: x["time_us"], reverse=True)
total_us = sum(f["time_us"] for f in funcs)

print(f"{'#':>3}  {'Function':<48} {'Time':>10} {'Rlimit':>12}  {'Module'}")
print("-" * 100)

for i, fn in enumerate(funcs[:top_n]):
    ms = fn["time_us"] / 1000
    pct = 100 * fn["time_us"] / total_us if total_us else 0
    status = "ok" if fn["ok"] else "FAIL"
    rlimit_s = f"{fn['rlimit']:,}"
    print(f"{i+1:>3}  {fn['name']:<48} {ms:>8.1f}ms {rlimit_s:>12}  {fn['module']}")

print()

# Module summary
mods = {}
for fn in funcs:
    m = fn["module"]
    if m not in mods:
        mods[m] = {"time_us": 0, "rlimit": 0, "count": 0}
    mods[m]["time_us"] += fn["time_us"]
    mods[m]["rlimit"] += fn["rlimit"]
    mods[m]["count"] += 1

print(f"{'Module':<35} {'Time':>10} {'Rlimit':>14}  {'Fns':>4}")
print("-" * 72)
for m, v in sorted(mods.items(), key=lambda x: x[1]["time_us"], reverse=True):
    ms = v["time_us"] / 1000
    print(f"{m:<35} {ms:>8.1f}ms {v['rlimit']:>14,}  {v['count']:>4}")

print()
print(f"Total: {len(funcs)} functions, {total_us/1000:.0f}ms SMT time, wall clock {wall}s")
print(f"Verification: {verified} verified, {errors} errors")
PYEOF

exit $VERUS_STATUS
