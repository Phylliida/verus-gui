#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_ROOT="${VERUS_ROOT:-$ROOT_DIR/../verus}"
VERUS_SOURCE="$VERUS_ROOT/source"
if [[ -z "${VERUS_TOOLCHAIN:-}" ]]; then
  case "$(uname -s)-$(uname -m)" in
    Darwin-arm64)  TOOLCHAIN="1.93.0-aarch64-apple-darwin" ;;
    Darwin-x86_64) TOOLCHAIN="1.93.0-x86_64-apple-darwin" ;;
    *)             TOOLCHAIN="1.93.0-x86_64-unknown-linux-gnu" ;;
  esac
else
  TOOLCHAIN="$VERUS_TOOLCHAIN"
fi

usage() {
  cat <<'USAGE'
usage: ./scripts/check.sh [--require-verus] [--forbid-trusted-escapes] [--offline]

options:
  --require-verus           fail instead of skipping when Verus verification cannot run
  --forbid-trusted-escapes  fail if non-test source uses trusted proof escapes (`admit`, `assume`, verifier externals, `#[verifier::truncate]`, `#[verifier::exec_allows_no_decreases_clause]`, or `unsafe`)
  --offline                 run cargo commands in offline mode (`cargo --offline`)
  -h, --help                show this help
USAGE
}

REQUIRE_VERUS=0
FORBID_TRUSTED_ESCAPES=0
OFFLINE=0
while [[ "$#" -gt 0 ]]; do
  case "${1:-}" in
    --require-verus)
      REQUIRE_VERUS=1
      ;;
    --forbid-trusted-escapes)
      FORBID_TRUSTED_ESCAPES=1
      ;;
    --offline)
      OFFLINE=1
      ;;
    -h|--help)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument '$1'"
      usage
      exit 1
      ;;
  esac
  shift
done

if [[ "$OFFLINE" == "1" ]]; then
  export CARGO_NET_OFFLINE=true
fi

CARGO_CMD=(cargo)
if [[ "$OFFLINE" == "1" ]]; then
  CARGO_CMD+=(--offline)
fi

require_command() {
  local cmd="$1"
  local hint="${2:-}"
  if ! command -v "$cmd" >/dev/null 2>&1; then
    echo "error: required command '$cmd' not found in PATH"
    if [[ -n "$hint" ]]; then
      echo "hint: $hint"
    fi
    exit 1
  fi
}

skip_or_fail_verus_unavailable() {
  local reason="$1"
  local hint="$2"
  if [[ "$REQUIRE_VERUS" == "1" ]]; then
    echo "error: Verus verification required but cannot run: $reason"
    echo "hint: $hint"
    exit 1
  else
    echo "[check] SKIP  Verus verification ($reason)"
    echo "[check] hint: $hint"
    echo "[check] pass (Verus verification skipped)"
    exit 0
  fi
}

check_no_trusted_escapes_in_non_test_sources() {
  echo "[check] Scanning non-test sources for trusted proof escapes"

  local src_files
  src_files="$(find "$ROOT_DIR/src" -name '*.rs' -not -path '*/tests/*' -not -name '*_test.rs')"

  local escape_pattern
  escape_pattern='(^|[^a-zA-Z_])(admit|assume)\s*\('
  escape_pattern+='|#\[verifier::external_body\]'
  escape_pattern+='|#\[verifier::external_fn_specification\]'
  escape_pattern+='|#\[verifier::external\]'
  escape_pattern+='|assume_specification'
  escape_pattern+='|#\[verifier::truncate\]'
  escape_pattern+='|#\[verifier::exec_allows_no_decreases_clause\]'
  escape_pattern+='|\bunsafe\b'

  local violations=""
  local file
  while IFS= read -r file; do
    [[ -z "$file" ]] && continue
    local hits
    hits="$(grep -nE "$escape_pattern" "$file" 2>/dev/null || true)"
    if [[ -n "$hits" ]]; then
      violations+="$file:
$hits
"
    fi
  done <<< "$src_files"

  if [[ -n "$violations" ]]; then
    echo "error: trusted proof escapes found in non-test sources:"
    echo "$violations"
    exit 1
  fi
  echo "[check] OK    no trusted proof escapes in non-test sources"
}

run_cargo_verus_verify() {
  local feature_flags="${1:-}"

  if command -v rustup >/dev/null 2>&1; then
    export PATH="$VERUS_SOURCE/target-verus/release:$PATH"
    export VERUS_Z3_PATH="$VERUS_SOURCE/z3"
    export RUSTUP_TOOLCHAIN="$TOOLCHAIN"
    cd "$ROOT_DIR"
    if [[ -n "$feature_flags" ]]; then
      # shellcheck disable=SC2086
      "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-gui $feature_flags -- --triggers-mode silent
    else
      "${CARGO_CMD[@]}" verus verify --manifest-path Cargo.toml -p verus-gui -- --triggers-mode silent
    fi
  elif command -v nix-shell >/dev/null 2>&1; then
    if nix-shell -p rustup --run "rustup --version >/dev/null 2>&1" >/dev/null 2>&1; then
      OFFLINE_CARGO_FLAG=""
      OFFLINE_EXPORT=""
      if [[ "$OFFLINE" == "1" ]]; then
        OFFLINE_CARGO_FLAG="--offline"
        OFFLINE_EXPORT="export CARGO_NET_OFFLINE=true"
      fi
      nix-shell -p rustup --run "
        set -euo pipefail
        $OFFLINE_EXPORT
        export RUSTUP_TOOLCHAIN='$TOOLCHAIN'
        export PATH='$VERUS_SOURCE/target-verus/release':\$PATH
        export VERUS_Z3_PATH='$VERUS_SOURCE/z3'
        cd '$ROOT_DIR'
        cargo $OFFLINE_CARGO_FLAG verus verify --manifest-path Cargo.toml -p verus-gui $feature_flags -- --triggers-mode silent
      "
    else
      skip_or_fail_verus_unavailable \
        "rustup is unavailable and nix-shell could not provide it in this environment" \
        "install rustup locally, or use an environment where nix-shell can access the nix daemon"
    fi
  else
    skip_or_fail_verus_unavailable \
      "rustup not found in PATH" \
      "install rustup with default toolchain $TOOLCHAIN"
  fi
}

extract_verus_verified_count() {
  local log_file="$1"
  local summary=""
  local verified_count=""
  local error_count=""

  summary="$(sed -nE 's/.*verification results::[[:space:]]*([0-9]+) verified,[[:space:]]*([0-9]+) errors.*/\1|\2/p' "$log_file" | tail -n 1 || true)"
  if [[ -z "$summary" ]]; then
    echo "error: could not parse Verus verification summary"
    cat "$log_file"
    exit 1
  fi

  verified_count="${summary%%|*}"
  error_count="${summary##*|}"
  if ! [[ "$verified_count" =~ ^[0-9]+$ && "$error_count" =~ ^[0-9]+$ ]]; then
    echo "error: malformed Verus verification summary: $summary"
    cat "$log_file"
    exit 1
  fi

  if (( error_count != 0 )); then
    echo "error: Verus verification summary reported nonzero errors: $error_count"
    cat "$log_file"
    exit 1
  fi

  printf '%s' "$verified_count"
}


run_cargo_verus_verify_and_check() {
  local feature_flags="${1:-}"
  local verus_log
  verus_log="$(mktemp)"
  trap "rm -f '$verus_log'" EXIT

  run_cargo_verus_verify "$feature_flags" 2>&1 | tee "$verus_log"

  local count
  count="$(extract_verus_verified_count "$verus_log")"
  echo "[check] Verus verification passed: $count verified, 0 errors"
}



if [[ "$FORBID_TRUSTED_ESCAPES" == "1" ]]; then
  echo "[check] Verifying non-test source tree excludes trusted proof escapes"
  check_no_trusted_escapes_in_non_test_sources
fi

if [[ ! -x "$VERUS_SOURCE/target-verus/release/cargo-verus" ]]; then
  skip_or_fail_verus_unavailable \
    "cargo-verus not found at $VERUS_SOURCE/target-verus/release/cargo-verus" \
    "build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
fi

if [[ ! -x "$VERUS_SOURCE/z3" ]]; then
  skip_or_fail_verus_unavailable \
    "z3 not found at $VERUS_SOURCE/z3" \
    "build Verus tools first (for example via ../VerusCAD/scripts/setup-verus.sh)"
fi

echo "[check] Running cargo verus verify"
run_cargo_verus_verify_and_check ""

echo "[check] pass"
