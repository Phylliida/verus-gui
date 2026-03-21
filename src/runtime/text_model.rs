use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::cursor::*;
use crate::text_model::proofs::*;
use crate::text_model::paragraph_proofs::*;
use crate::text_model::undo::*;
use crate::text_model::undo_proofs::*;
use crate::text_model::selection_geometry::*;
use crate::text_model::viewport::*;
use crate::text_model::word_wrap::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Runtime style types
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeStyleSet {
    pub bold: Option<bool>,
    pub italic: Option<bool>,
    pub underline: Option<bool>,
    pub strikethrough: Option<bool>,
    pub font_size: Option<usize>,
    pub font_family: Option<usize>,
    pub color: Option<u32>,
    pub bg_color: Option<u32>,
}

impl View for RuntimeStyleSet {
    type V = StyleSet;
    open spec fn view(&self) -> StyleSet {
        StyleSet {
            bold: self.bold,
            italic: self.italic,
            underline: self.underline,
            strikethrough: self.strikethrough,
            font_size: match self.font_size {
                Some(n) => Some(n as nat),
                None => None,
            },
            font_family: match self.font_family {
                Some(n) => Some(n as nat),
                None => None,
            },
            color: self.color,
            bg_color: self.bg_color,
        }
    }
}

pub struct RuntimeParagraphStyle {
    pub alignment: ParagraphAlignment,
    pub indent_left: usize,
    pub indent_right: usize,
    pub indent_first_line: i64,
    pub line_spacing: usize,
    pub space_before: usize,
    pub space_after: usize,
}

impl View for RuntimeParagraphStyle {
    type V = ParagraphStyle;
    open spec fn view(&self) -> ParagraphStyle {
        ParagraphStyle {
            alignment: self.alignment,
            indent_left: self.indent_left as nat,
            indent_right: self.indent_right as nat,
            indent_first_line: self.indent_first_line as int,
            line_spacing: self.line_spacing as nat,
            space_before: self.space_before as nat,
            space_after: self.space_after as nat,
        }
    }
}

pub struct RuntimeComposition {
    pub range_start: usize,
    pub range_end: usize,
    pub original: Vec<char>,
    pub provisional: Vec<char>,
    pub cursor: usize,
}

impl View for RuntimeComposition {
    type V = Composition;
    open spec fn view(&self) -> Composition {
        Composition {
            range_start: self.range_start as nat,
            range_end: self.range_end as nat,
            original: self.original@,
            provisional: self.provisional@,
            cursor: self.cursor as nat,
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// Runtime text model
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeTextModel {
    pub text: Vec<char>,
    pub styles: Vec<RuntimeStyleSet>,
    pub anchor: usize,
    pub focus: usize,
    pub focus_affinity: Affinity,
    pub preferred_column: Option<usize>,
    pub typing_style: RuntimeStyleSet,
    pub default_style: RuntimeStyleSet,
    pub composition: Option<RuntimeComposition>,
    pub paragraph_styles: Vec<RuntimeParagraphStyle>,
    pub model: Ghost<TextModel>,
}

impl View for RuntimeTextModel {
    type V = TextModel;
    open spec fn view(&self) -> TextModel {
        self.model@
    }
}

/// Spec helper: extract the StyleSet views from a sequence of RuntimeStyleSets.
pub open spec fn style_seq_view(styles: Seq<RuntimeStyleSet>) -> Seq<StyleSet> {
    Seq::new(styles.len(), |i: int| styles[i]@)
}

/// Spec helper: extract ParagraphStyle views from runtime sequence.
pub open spec fn para_seq_view(styles: Seq<RuntimeParagraphStyle>) -> Seq<ParagraphStyle> {
    Seq::new(styles.len(), |i: int| styles[i]@)
}

impl RuntimeTextModel {
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.model@.wf()
        &&& self.text@ == self.model@.text
        &&& self.styles@.len() == self.model@.styles.len()
        &&& forall|i: int| 0 <= i < self.styles@.len() ==>
            (#[trigger] self.styles@[i])@ == self.model@.styles[i]
        &&& self.anchor as nat == self.model@.anchor
        &&& self.focus as nat == self.model@.focus
        &&& self.focus_affinity == self.model@.focus_affinity
        &&& self.typing_style@ == self.model@.typing_style
        &&& self.default_style@ == self.model@.default_style
        &&& self.paragraph_styles@.len() == self.model@.paragraph_styles.len()
        &&& forall|i: int| 0 <= i < self.paragraph_styles@.len() ==>
            (#[trigger] self.paragraph_styles@[i])@ == self.model@.paragraph_styles[i]
        &&& match (self.preferred_column, self.model@.preferred_column) {
            (Some(n), Some(m)) => n as nat == m,
            (None, None) => true,
            _ => false,
        }
        &&& match (&self.composition, self.model@.composition) {
            (Some(rc), Some(sc)) => rc@ == sc,
            (None, None) => true,
            _ => false,
        }
        &&& self.text.len() < usize::MAX
    }
}

// ──────────────────────────────────────────────────────────────────────
// Copy helpers
// ──────────────────────────────────────────────────────────────────────

pub fn copy_style_set(s: &RuntimeStyleSet) -> (out: RuntimeStyleSet)
    ensures out@ == s@,
{
    RuntimeStyleSet {
        bold: s.bold,
        italic: s.italic,
        underline: s.underline,
        strikethrough: s.strikethrough,
        font_size: s.font_size,
        font_family: s.font_family,
        color: s.color,
        bg_color: s.bg_color,
    }
}

pub fn copy_paragraph_style(s: &RuntimeParagraphStyle) -> (out: RuntimeParagraphStyle)
    ensures out@ == s@,
{
    let alignment = match s.alignment {
        ParagraphAlignment::Left => ParagraphAlignment::Left,
        ParagraphAlignment::Center => ParagraphAlignment::Center,
        ParagraphAlignment::Right => ParagraphAlignment::Right,
        ParagraphAlignment::Justify => ParagraphAlignment::Justify,
    };
    RuntimeParagraphStyle {
        alignment,
        indent_left: s.indent_left,
        indent_right: s.indent_right,
        indent_first_line: s.indent_first_line,
        line_spacing: s.line_spacing,
        space_before: s.space_before,
        space_after: s.space_after,
    }
}

pub fn copy_char_vec(v: &Vec<char>) -> (out: Vec<char>)
    ensures out@ == v@,
{
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            out@ =~= v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        out.push(v[i]);
        proof {
            assert(v@.subrange(0, i as int).push(v@[i as int])
                =~= v@.subrange(0, (i + 1) as int));
        }
        i += 1;
    }
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    out
}

fn copy_style_vec(v: &Vec<RuntimeStyleSet>) -> (out: Vec<RuntimeStyleSet>)
    ensures
        out@.len() == v@.len(),
        forall|k: int| 0 <= k < out@.len() ==>
            (#[trigger] out@[k])@ == v@[k]@,
{
    let mut out: Vec<RuntimeStyleSet> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant
            i <= v.len(),
            out@.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] out@[k])@ == v@[k]@,
        decreases v.len() - i,
    {
        out.push(copy_style_set(&v[i]));
        i += 1;
    }
    out
}

pub fn default_paragraph_style_exec() -> (out: RuntimeParagraphStyle)
    ensures out@ == default_paragraph_style(),
{
    RuntimeParagraphStyle {
        alignment: ParagraphAlignment::Left,
        indent_left: 0,
        indent_right: 0,
        indent_first_line: 0,
        line_spacing: 0,
        space_before: 0,
        space_after: 0,
    }
}

pub fn merge_style_exec(base: &RuntimeStyleSet, overlay: &RuntimeStyleSet)
    -> (out: RuntimeStyleSet)
    ensures out@ == merge_style(base@, overlay@),
{
    RuntimeStyleSet {
        bold: if overlay.bold.is_some() { overlay.bold } else { base.bold },
        italic: if overlay.italic.is_some() { overlay.italic } else { base.italic },
        underline: if overlay.underline.is_some() { overlay.underline } else { base.underline },
        strikethrough: if overlay.strikethrough.is_some() { overlay.strikethrough } else { base.strikethrough },
        font_size: if overlay.font_size.is_some() { overlay.font_size } else { base.font_size },
        font_family: if overlay.font_family.is_some() { overlay.font_family } else { base.font_family },
        color: if overlay.color.is_some() { overlay.color } else { base.color },
        bg_color: if overlay.bg_color.is_some() { overlay.bg_color } else { base.bg_color },
    }
}

// ──────────────────────────────────────────────────────────────────────
// Vec splice helper (chars)
// ──────────────────────────────────────────────────────────────────────

fn vec_splice_chars(
    v: &Vec<char>, start: usize, end: usize, r: &Vec<char>,
) -> (result: Vec<char>)
    requires
        start <= end,
        end <= v.len(),
        v.len() - (end - start) + r.len() <= usize::MAX,
    ensures
        result@ =~= seq_splice(v@, start as int, end as int, r@),
{
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < start
        invariant
            i <= start,
            start <= end,
            end <= v.len(),
            result@ =~= v@.subrange(0, i as int),
        decreases start - i,
    {
        result.push(v[i]);
        proof {
            assert(v@.subrange(0, i as int).push(v@[i as int])
                =~= v@.subrange(0, (i + 1) as int));
        }
        i += 1;
    }
    let mut j: usize = 0;
    while j < r.len()
        invariant
            j <= r.len(),
            result@ =~= v@.subrange(0, start as int) + r@.subrange(0, j as int),
        decreases r.len() - j,
    {
        result.push(r[j]);
        proof {
            assert(r@.subrange(0, j as int).push(r@[j as int])
                =~= r@.subrange(0, (j + 1) as int));
        }
        j += 1;
    }
    proof { assert(r@.subrange(0, r@.len() as int) =~= r@); }
    let mut k: usize = end;
    while k < v.len()
        invariant
            end <= k,
            k <= v.len(),
            result@ =~= v@.subrange(0, start as int) + r@ + v@.subrange(end as int, k as int),
        decreases v.len() - k,
    {
        result.push(v[k]);
        proof {
            assert(v@.subrange(end as int, k as int).push(v@[k as int])
                =~= v@.subrange(end as int, (k + 1) as int));
        }
        k += 1;
    }
    result
}

// ──────────────────────────────────────────────────────────────────────
// Count char (exec)
// ──────────────────────────────────────────────────────────────────────

fn count_char_exec(text: &Vec<char>, c: char) -> (result: usize)
    ensures result as nat == count_char(text@, c),
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < text.len()
        invariant
            i <= text.len(),
            count as nat == count_char(text@.subrange(0, i as int), c),
            count <= i,
        decreases text.len() - i,
    {
        proof {
            lemma_count_char_push(text@.subrange(0, i as int), c, text@[i as int]);
            assert(text@.subrange(0, i as int).push(text@[i as int])
                =~= text@.subrange(0, (i + 1) as int));
        }
        if text[i] == c {
            count += 1;
        }
        i += 1;
    }
    proof {
        assert(text@.subrange(0, text@.len() as int) =~= text@);
    }
    count
}

fn count_char_range_exec(
    text: &Vec<char>, start: usize, end: usize, c: char,
) -> (result: usize)
    requires
        start <= end,
        end <= text.len(),
    ensures
        result as nat == count_char(text@.subrange(start as int, end as int), c),
{
    let mut count: usize = 0;
    let mut i: usize = start;
    while i < end
        invariant
            start <= i,
            i <= end,
            end <= text.len(),
            count as nat == count_char(
                text@.subrange(start as int, i as int), c),
            count <= i - start,
        decreases end - i,
    {
        proof {
            lemma_count_char_push(
                text@.subrange(start as int, i as int), c, text@[i as int]);
            assert(text@.subrange(start as int, i as int).push(text@[i as int])
                =~= text@.subrange(start as int, (i + 1) as int));
        }
        if text[i] == c {
            count += 1;
        }
        i += 1;
    }
    count
}

// ──────────────────────────────────────────────────────────────────────
// Adjust paragraph styles (exec)
// ──────────────────────────────────────────────────────────────────────

fn adjust_paragraph_styles_exec(
    old_styles: &Vec<RuntimeParagraphStyle>,
    old_text: &Vec<char>,
    start: usize,
    end: usize,
    new_text: &Vec<char>,
) -> (result: Vec<RuntimeParagraphStyle>)
    requires
        start <= end,
        end <= old_text.len(),
        old_text.len() < usize::MAX,
        old_styles@.len() as nat == paragraph_count(old_text@),
        forall|i: int| 0 <= i < old_styles@.len() ==>
            (#[trigger] old_styles@[i])@ == para_seq_view(old_styles@)[i],
    ensures
        para_seq_view(result@) =~= adjust_paragraph_styles(
            para_seq_view(old_styles@), old_text@, start as nat, end as nat, new_text@),
{
    let removed_newlines = count_char_range_exec(old_text, start, end, '\n');
    let inserted_newlines = count_char_exec(new_text, '\n');
    let para_of_start = count_char_range_exec(old_text, 0, start, '\n');

    proof {
        lemma_after_idx_in_bounds(
            para_seq_view(old_styles@), old_text@, start as nat, end as nat);
        lemma_count_char_le_len(old_text@.subrange(0, start as int), '\n');
        lemma_count_char_le_len(old_text@.subrange(start as int, end as int), '\n');
    }

    let before_end = para_of_start + 1;
    let after_idx = before_end + removed_newlines;

    let mut result: Vec<RuntimeParagraphStyle> = Vec::new();

    // Copy "before" styles [0..before_end)
    let mut i: usize = 0;
    while i < before_end
        invariant
            i <= before_end,
            before_end <= old_styles.len(),
            result@.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] result@[k])@ == old_styles@[k]@,
        decreases before_end - i,
    {
        result.push(copy_paragraph_style(&old_styles[i]));
        i += 1;
    }

    // Insert default styles for new paragraphs
    let mut j: usize = 0;
    while j < inserted_newlines
        invariant
            j <= inserted_newlines,
            result@.len() == before_end + j,
            forall|k: int| 0 <= k < before_end as int ==>
                (#[trigger] result@[k])@ == old_styles@[k]@,
            forall|k: int| 0 <= k < j as int ==>
                (#[trigger] result@[before_end as int + k])@
                    == default_paragraph_style(),
        decreases inserted_newlines - j,
    {
        result.push(default_paragraph_style_exec());
        j += 1;
    }

    // Copy "after" styles [after_idx..old_styles.len())
    let mut m: usize = after_idx;
    if after_idx <= old_styles.len() {
        while m < old_styles.len()
            invariant
                after_idx <= m,
                m <= old_styles.len(),
                result@.len() == before_end + inserted_newlines + (m - after_idx),
                forall|k: int| 0 <= k < before_end as int ==>
                    (#[trigger] result@[k])@ == old_styles@[k]@,
                forall|k: int| 0 <= k < inserted_newlines as int ==>
                    (#[trigger] result@[before_end as int + k])@
                        == default_paragraph_style(),
                forall|k: int| 0 <= k < (m - after_idx) as int ==>
                    (#[trigger] result@[(before_end + inserted_newlines) as int + k])@
                        == old_styles@[after_idx as int + k]@,
            decreases old_styles.len() - m,
        {
            result.push(copy_paragraph_style(&old_styles[m]));
            m += 1;
        }
    }

    proof {
        // Connect runtime result to spec adjust_paragraph_styles
        lemma_seq_repeat_len(default_paragraph_style(), inserted_newlines as nat);

        // Build the expected spec result piece by piece
        let spec_old = para_seq_view(old_styles@);
        let spec_before = spec_old.subrange(0, before_end as int);
        let spec_after_idx = after_idx as int;
        let spec_after = if spec_after_idx <= spec_old.len() as int {
            spec_old.subrange(spec_after_idx, spec_old.len() as int)
        } else {
            Seq::<ParagraphStyle>::empty()
        };
        let spec_new = seq_repeat(default_paragraph_style(), inserted_newlines as nat);
        let spec_result = spec_before + spec_new + spec_after;

        // Show para_seq_view(result@) =~= spec_result
        assert(para_seq_view(result@).len() == spec_result.len());

        assert forall|k: int| 0 <= k < para_seq_view(result@).len()
            implies para_seq_view(result@)[k] == spec_result[k]
        by {
            if k < before_end as int {
                assert(para_seq_view(result@)[k] == result@[k]@);
                assert(result@[k]@ == old_styles@[k]@);
                assert(spec_result[k] == spec_before[k]);
                assert(spec_before[k] == spec_old[k]);
            } else if k < (before_end + inserted_newlines) as int {
                let j_off = k - before_end as int;
                // LHS: para_seq_view(result@)[k] == result@[k]@
                assert(para_seq_view(result@)[k] == result@[k]@);
                // From second loop invariant (trigger match)
                assert(result@[before_end as int + j_off]@ == default_paragraph_style());
                assert(k == before_end as int + j_off);
                // RHS: spec_result[k] from spec_new
                assert(spec_new[j_off] == default_paragraph_style()) by {
                    lemma_seq_repeat_index(default_paragraph_style(), inserted_newlines as nat, j_off);
                };
            } else {
                let offset = k - (before_end + inserted_newlines) as int;
                assert(para_seq_view(result@)[k] == result@[k]@);
                // From third loop invariant (trigger match)
                assert(result@[(before_end + inserted_newlines) as int + offset]@ == old_styles@[after_idx as int + offset]@);
                assert(k == (before_end + inserted_newlines) as int + offset);
                // RHS: spec_result[k] from spec_after
                assert(spec_after[offset] == spec_old[after_idx as int + offset]);
            }
        }
    }
    result
}

// ──────────────────────────────────────────────────────────────────────
// Core splice (exec)
// ──────────────────────────────────────────────────────────────────────

fn splice_exec(
    model: RuntimeTextModel,
    start: usize,
    end: usize,
    new_text: Vec<char>,
    new_styles: Vec<RuntimeStyleSet>,
    new_focus: usize,
    Ghost(ghost_new_styles): Ghost<Seq<StyleSet>>,
) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        start <= end,
        end <= model.text.len(),
        new_text.len() == new_styles.len(),
        new_text@.len() == ghost_new_styles.len(),
        forall|i: int| 0 <= i < new_styles@.len() ==>
            (#[trigger] new_styles@[i])@ == ghost_new_styles[i],
        new_focus <= model.text.len() - (end - start) + new_text.len(),
        model.text.len() - (end - start) + new_text.len() < usize::MAX,
        wf_text(seq_splice(model.text@, start as int, end as int, new_text@)),
        is_grapheme_boundary(
            seq_splice(model.text@, start as int, end as int, new_text@),
            new_focus as nat),
    ensures
        result@ == splice(model@, start as nat, end as nat,
                           new_text@, ghost_new_styles, new_focus as nat),
        result.wf_spec(),
{
    // Build text'
    let text_prime = vec_splice_chars(&model.text, start, end, &new_text);

    // Build styles'
    let mut styles_prime: Vec<RuntimeStyleSet> = Vec::new();
    let mut i: usize = 0;
    while i < start
        invariant
            i <= start, start <= end, end <= model.styles.len(),
            model.wf_spec(),
            styles_prime@.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] styles_prime@[k])@ == model@.styles[k],
        decreases start - i,
    {
        styles_prime.push(copy_style_set(&model.styles[i]));
        i += 1;
    }
    let mut j: usize = 0;
    while j < new_styles.len()
        invariant
            j <= new_styles.len(),
            styles_prime@.len() == start + j,
            forall|k: int| 0 <= k < start as int ==>
                (#[trigger] styles_prime@[k])@ == model@.styles[k],
            forall|k: int| 0 <= k < j as int ==>
                (#[trigger] styles_prime@[start as int + k])@ == ghost_new_styles[k],
            forall|i2: int| 0 <= i2 < new_styles@.len() ==>
                (#[trigger] new_styles@[i2])@ == ghost_new_styles[i2],
        decreases new_styles.len() - j,
    {
        styles_prime.push(copy_style_set(&new_styles[j]));
        j += 1;
    }
    let mut k: usize = end;
    while k < model.styles.len()
        invariant
            end <= k, k <= model.styles.len(),
            model.wf_spec(),
            styles_prime@.len() == start + new_styles.len() + (k - end),
            forall|idx: int| 0 <= idx < start as int ==>
                (#[trigger] styles_prime@[idx])@ == model@.styles[idx],
            forall|idx: int| 0 <= idx < new_styles@.len() ==>
                (#[trigger] styles_prime@[start as int + idx])@ == ghost_new_styles[idx],
            forall|idx: int| 0 <= idx < (k - end) as int ==>
                (#[trigger] styles_prime@[(start + new_styles.len()) as int + idx])@
                    == model@.styles[end as int + idx],
        decreases model.styles.len() - k,
    {
        styles_prime.push(copy_style_set(&model.styles[k]));
        k += 1;
    }

    // Build paragraph styles'
    let para_styles_prime = adjust_paragraph_styles_exec(
        &model.paragraph_styles, &model.text, start, end, &new_text);

    // Compute typing style
    let typing_style_prime = if new_text.len() > 0 {
        copy_style_set(&model.typing_style)
    } else {
        resolve_typing_style_exec(
            &text_prime, &styles_prime, new_focus, &model.default_style)
    };

    proof {
        // Prove styles match spec splice
        let s_before = model@.styles.subrange(0, start as int);
        let s_after = model@.styles.subrange(end as int, model@.styles.len() as int);
        let spec_styles_prime = s_before + ghost_new_styles + s_after;
        // seq_splice unfolds to exactly this
        assert(spec_styles_prime =~= seq_splice(
            model@.styles, start as int, end as int, ghost_new_styles));
        lemma_seq_splice_len(
            model@.styles, start as int, end as int, ghost_new_styles);

        assert(styles_prime@.len() == spec_styles_prime.len());
        assert forall|idx: int| 0 <= idx < styles_prime@.len()
            implies (#[trigger] styles_prime@[idx])@ == spec_styles_prime[idx]
        by {
            if idx < start as int {
                // From first loop invariant
                assert(styles_prime@[idx]@ == model@.styles[idx]);
                assert(spec_styles_prime[idx] == s_before[idx]);
                assert(s_before[idx] == model@.styles[idx]);
            } else if idx < (start + new_styles.len()) as int {
                let ji = idx - start as int;
                // Trigger the second loop invariant: key is start as int + ji
                assert(styles_prime@[start as int + ji]@ == ghost_new_styles[ji]);
                assert(idx == start as int + ji); // help Z3
            } else {
                let ki = idx - (start + new_styles.len()) as int;
                // Trigger the third loop invariant
                assert(styles_prime@[(start + new_styles.len()) as int + ki]@
                    == model@.styles[end as int + ki]);
                assert(idx == (start + new_styles.len()) as int + ki);
            }
        }

        // Prove paragraph styles match
        lemma_adjust_paragraph_styles_len(
            model@.paragraph_styles, model@.text,
            start as nat, end as nat, new_text@);

        // wf of result
        lemma_splice_preserves_wf(
            model@, start as nat, end as nat,
            new_text@, ghost_new_styles, new_focus as nat);
    }

    let ghost spec_result = splice(
        model@, start as nat, end as nat,
        new_text@, ghost_new_styles, new_focus as nat);

    proof {
        // Help Z3 see that para_seq_view(model.paragraph_styles@) =~= model@.paragraph_styles
        assert(para_seq_view(model.paragraph_styles@) =~= model@.paragraph_styles);
        // And thus para_styles_prime matches spec_result.paragraph_styles
        assert(para_seq_view(para_styles_prime@) =~= spec_result.paragraph_styles);
        // styles match
        assert(style_seq_view(styles_prime@) =~= spec_result.styles);
    }

    RuntimeTextModel {
        text: text_prime,
        styles: styles_prime,
        anchor: new_focus,
        focus: new_focus,
        focus_affinity: Affinity::Downstream,
        preferred_column: None,
        typing_style: typing_style_prime,
        default_style: model.default_style,
        composition: None,
        paragraph_styles: para_styles_prime,
        model: Ghost(spec_result),
    }
}

// ──────────────────────────────────────────────────────────────────────
// Resolve typing style (exec)
// ──────────────────────────────────────────────────────────────────────

fn resolve_typing_style_exec(
    text: &Vec<char>,
    styles: &Vec<RuntimeStyleSet>,
    focus: usize,
    default_style: &RuntimeStyleSet,
) -> (out: RuntimeStyleSet)
    requires
        styles@.len() == text@.len(),
        focus <= text.len(),
    ensures
        out@ == resolve_typing_style(
            text@,
            Seq::new(styles@.len(), |i: int| styles@[i]@),
            focus as nat,
            default_style@),
{
    if text.len() == 0 {
        copy_style_set(default_style)
    } else if focus > 0 {
        copy_style_set(&styles[focus - 1])
    } else {
        copy_style_set(&styles[0])
    }
}

// ──────────────────────────────────────────────────────────────────────
// External body: Unicode boundary functions
// ──────────────────────────────────────────────────────────────────────

#[verifier::external_body]
pub fn prev_grapheme_boundary_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == prev_grapheme_boundary(text@, pos as nat),
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let clamped = pos.min(s.len());
    // Find byte offset for char position `clamped`
    let byte_pos = s.char_indices().nth(clamped).map(|(i, _)| i).unwrap_or(s.len());
    // Find the previous grapheme boundary
    let prev_byte = s[..byte_pos].grapheme_indices(true).last()
        .map(|(i, _)| i).unwrap_or(0);
    // Convert byte offset back to char offset
    s[..prev_byte].chars().count()
}

#[verifier::external_body]
pub fn next_grapheme_boundary_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == next_grapheme_boundary(text@, pos as nat),
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let char_len = s.chars().count();
    let clamped = pos.min(char_len);
    // Find byte offset for char position `clamped`
    let byte_pos = s.char_indices().nth(clamped).map(|(i, _)| i).unwrap_or(s.len());
    // Find the next grapheme boundary after byte_pos
    let next_byte = s[byte_pos..].grapheme_indices(true).nth(1)
        .map(|(i, _)| byte_pos + i).unwrap_or(s.len());
    // Convert byte offset back to char offset
    s[..next_byte].chars().count()
}

#[verifier::external_body]
pub fn prev_word_start_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == prev_boundary_in(word_start_boundaries(text@), pos as nat),
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let clamped = pos.min(s.chars().count());
    // Build word boundary set (char offsets where words start)
    let mut boundaries: Vec<usize> = Vec::new();
    let mut char_offset = 0usize;
    for (_, word) in s.split_word_bound_indices() {
        let word_char_len = word.chars().count();
        // A word start boundary is at the start of a non-whitespace word
        if word_char_len > 0 && !word.chars().next().unwrap().is_whitespace() {
            boundaries.push(char_offset);
        }
        char_offset += word_char_len;
    }
    // Find the largest boundary strictly less than clamped
    let mut best = 0usize;
    for &b in boundaries.iter() {
        if b < clamped {
            best = b;
        }
    }
    best
}

#[verifier::external_body]
pub fn next_word_end_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == next_boundary_in(word_end_boundaries(text@), pos as nat),
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let char_len = s.chars().count();
    let clamped = pos.min(char_len);
    // Build word end boundary set (char offsets where words end)
    let mut boundaries: Vec<usize> = Vec::new();
    let mut char_offset = 0usize;
    for (_, word) in s.split_word_bound_indices() {
        let word_char_len = word.chars().count();
        // A word end boundary is at the end of a non-whitespace word
        if word_char_len > 0 && !word.chars().next().unwrap().is_whitespace() {
            boundaries.push(char_offset + word_char_len);
        }
        char_offset += word_char_len;
    }
    // Find the smallest boundary strictly greater than clamped
    for &b in boundaries.iter() {
        if b > clamped {
            return b;
        }
    }
    char_len
}

// ──────────────────────────────────────────────────────────────────────
// Editing operations (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn insert_char_exec(model: RuntimeTextModel, ch: char) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        is_permitted(ch),
        ch != '\r',
        // Result text must fit in usize with room for wf_spec
        model.text.len() + 1 < usize::MAX || has_selection(model@.anchor, model@.focus),
        ({
            let (sel_start, sel_end) = selection_range(model@.anchor, model@.focus);
            let text_prime = seq_splice(model@.text, sel_start as int, sel_end as int, seq![ch]);
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start + 1)
        }),
    ensures
        result@ == insert_char(model@, ch),
        result.wf_spec(),
{
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    let typing_style = copy_style_set(&model.typing_style);
    let ghost ghost_styles: Seq<StyleSet> = seq![model@.typing_style];
    let mut new_text: Vec<char> = Vec::new();
    new_text.push(ch);
    let mut new_styles: Vec<RuntimeStyleSet> = Vec::new();
    new_styles.push(typing_style);
    splice_exec(
        model, sel_start, sel_end,
        new_text, new_styles, sel_start + 1,
        Ghost(ghost_styles),
    )
}

pub fn delete_selection_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        has_selection(model@.anchor, model@.focus),
        ({
            let (sel_start, sel_end) = selection_range(model@.anchor, model@.focus);
            let text_prime = seq_splice(
                model@.text, sel_start as int, sel_end as int, Seq::<char>::empty());
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start)
        }),
    ensures
        result@ == delete_selection(model@),
        result.wf_spec(),
{
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    splice_exec(
        model, sel_start, sel_end,
        Vec::new(), Vec::new(), sel_start,
        Ghost(Seq::empty()),
    )
}

pub fn delete_backward_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        !has_selection(model@.anchor, model@.focus),
        model@.focus > 0,
        model@.text.len() > 0,
        ({
            let prev = prev_grapheme_boundary(model@.text, model@.focus);
            let text_prime = seq_splice(
                model@.text, prev as int, model@.focus as int, Seq::<char>::empty());
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, prev)
        }),
    ensures
        result@ == delete_backward(model@),
        result.wf_spec(),
{
    let prev = prev_grapheme_boundary_exec(&model.text, model.focus);
    let focus = model.focus;
    proof { lemma_prev_grapheme_lt(model@.text, model@.focus); }
    splice_exec(
        model, prev, focus,
        Vec::new(), Vec::new(), prev,
        Ghost(Seq::empty()),
    )
}

pub fn delete_forward_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        !has_selection(model@.anchor, model@.focus),
        model@.focus < model@.text.len(),
        ({
            let next = next_grapheme_boundary(model@.text, model@.focus);
            let text_prime = seq_splice(
                model@.text, model@.focus as int, next as int, Seq::<char>::empty());
            &&& next <= model@.text.len()
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, model@.focus)
        }),
    ensures
        result@ == delete_forward(model@),
        result.wf_spec(),
{
    let focus = model.focus;
    let next = next_grapheme_boundary_exec(&model.text, focus);
    proof { lemma_next_grapheme_gt(model@.text, model@.focus); }
    splice_exec(
        model, focus, next,
        Vec::new(), Vec::new(), focus,
        Ghost(Seq::empty()),
    )
}

// ──────────────────────────────────────────────────────────────────────
// Formatting operations (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn toggle_bold_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires model.wf_spec(),
    ensures
        result@ == toggle_bold(model@),
        result.wf_spec(),
{
    let current = match model.typing_style.bold {
        Some(b) => b,
        None => false,
    };
    let new_typing_style = RuntimeStyleSet {
        bold: Some(!current),
        italic: model.typing_style.italic,
        underline: model.typing_style.underline,
        strikethrough: model.typing_style.strikethrough,
        font_size: model.typing_style.font_size,
        font_family: model.typing_style.font_family,
        color: model.typing_style.color,
        bg_color: model.typing_style.bg_color,
    };
    let ghost spec_result = toggle_bold(model@);
    RuntimeTextModel {
        typing_style: new_typing_style,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        anchor: model.anchor,
        focus: model.focus,
        focus_affinity: model.focus_affinity,
        preferred_column: model.preferred_column,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

pub fn toggle_italic_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires model.wf_spec(),
    ensures
        result@ == toggle_italic(model@),
        result.wf_spec(),
{
    let current = match model.typing_style.italic {
        Some(b) => b,
        None => false,
    };
    let new_typing_style = RuntimeStyleSet {
        bold: model.typing_style.bold,
        italic: Some(!current),
        underline: model.typing_style.underline,
        strikethrough: model.typing_style.strikethrough,
        font_size: model.typing_style.font_size,
        font_family: model.typing_style.font_family,
        color: model.typing_style.color,
        bg_color: model.typing_style.bg_color,
    };
    let ghost spec_result = toggle_italic(model@);
    RuntimeTextModel {
        typing_style: new_typing_style,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        anchor: model.anchor,
        focus: model.focus,
        focus_affinity: model.focus_affinity,
        preferred_column: model.preferred_column,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

pub fn apply_style_to_range_exec(
    model: RuntimeTextModel, start: usize, end: usize, style: &RuntimeStyleSet,
) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        start <= end,
        end as nat <= model@.text.len(),
    ensures
        result@ == apply_style_to_range(model@, start as nat, end as nat, style@),
        result.wf_spec(),
{
    let mut new_styles: Vec<RuntimeStyleSet> = Vec::new();
    let mut i: usize = 0;
    while i < model.styles.len()
        invariant
            i <= model.styles.len(),
            model.wf_spec(),
            start <= end,
            end as nat <= model@.text.len(),
            new_styles@.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] new_styles@[k])@ == (
                    if start as int <= k && k < end as int {
                        merge_style(model@.styles[k], style@)
                    } else {
                        model@.styles[k]
                    }
                ),
        decreases model.styles.len() - i,
    {
        if i >= start && i < end {
            new_styles.push(merge_style_exec(&model.styles[i], style));
        } else {
            new_styles.push(copy_style_set(&model.styles[i]));
        }
        i += 1;
    }

    proof {
        lemma_apply_style_preserves_wf(
            model@, start as nat, end as nat, style@);
    }

    let ghost spec_result = apply_style_to_range(
        model@, start as nat, end as nat, style@);
    RuntimeTextModel {
        styles: new_styles,
        model: Ghost(spec_result),
        text: model.text,
        anchor: model.anchor,
        focus: model.focus,
        focus_affinity: model.focus_affinity,
        preferred_column: model.preferred_column,
        typing_style: model.typing_style,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Cursor operations (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn select_all_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires model.wf_spec(),
    ensures
        result@ == select_all(model@),
        result.wf_spec(),
{
    proof { lemma_select_all_preserves_wf(model@); }
    let ghost spec_result = select_all(model@);
    RuntimeTextModel {
        anchor: 0,
        focus: model.text.len(),
        focus_affinity: Affinity::Upstream,
        preferred_column: None,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        typing_style: model.typing_style,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

pub fn collapse_left_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires model.wf_spec(),
    ensures
        result@ == collapse_left(model@),
        result.wf_spec(),
{
    let pos = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let new_typing = resolve_typing_style_exec(
        &model.text, &model.styles, pos, &model.default_style);
    let ghost spec_result = collapse_left(model@);
    RuntimeTextModel {
        anchor: pos,
        focus: pos,
        focus_affinity: Affinity::Downstream,
        preferred_column: None,
        typing_style: new_typing,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

pub fn collapse_right_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires model.wf_spec(),
    ensures
        result@ == collapse_right(model@),
        result.wf_spec(),
{
    let pos = if model.anchor >= model.focus { model.anchor } else { model.focus };
    let new_typing = resolve_typing_style_exec(
        &model.text, &model.styles, pos, &model.default_style);
    let ghost spec_result = collapse_right(model@);
    RuntimeTextModel {
        anchor: pos,
        focus: pos,
        focus_affinity: Affinity::Upstream,
        preferred_column: None,
        typing_style: new_typing,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

// ──────────────────────────────────────────────────────────────────────
// IME operations (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn compose_start_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        model@.composition.is_none(),
    ensures
        result@ == compose_start(model@),
        result.wf_spec(),
{
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };

    // Copy original text from selection range
    let mut original: Vec<char> = Vec::new();
    let mut i: usize = sel_start;
    while i < sel_end
        invariant
            sel_start <= i, i <= sel_end, sel_end <= model.text.len(),
            original@ =~= model.text@.subrange(sel_start as int, i as int),
        decreases sel_end - i,
    {
        original.push(model.text[i]);
        proof {
            assert(model.text@.subrange(sel_start as int, i as int).push(model.text@[i as int])
                =~= model.text@.subrange(sel_start as int, (i + 1) as int));
        }
        i += 1;
    }

    proof { lemma_compose_start_preserves_wf(model@); }
    let ghost spec_result = compose_start(model@);
    let comp = RuntimeComposition {
        range_start: sel_start,
        range_end: sel_end,
        original,
        provisional: Vec::new(),
        cursor: 0,
    };
    proof {
        // Help Z3 connect runtime composition view to spec composition
        let (ss, se) = selection_range(model@.anchor, model@.focus);
        assert(sel_start as nat == ss);
        assert(sel_end as nat == se);
        assert(comp@ == spec_result.composition.unwrap());
    }
    RuntimeTextModel {
        composition: Some(comp),
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        anchor: model.anchor,
        focus: model.focus,
        focus_affinity: model.focus_affinity,
        preferred_column: model.preferred_column,
        typing_style: model.typing_style,
        default_style: model.default_style,
        paragraph_styles: model.paragraph_styles,
    }
}

pub fn compose_update_exec(
    model: RuntimeTextModel, provisional: Vec<char>, cursor: usize,
) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        model@.composition.is_some(),
        cursor <= provisional.len(),
    ensures
        result@ == compose_update(model@, provisional@, cursor as nat),
        result.wf_spec(),
{
    match model.composition {
        Some(c) => {
            let ghost spec_result = compose_update(model@, provisional@, cursor as nat);
            let new_comp = RuntimeComposition {
                range_start: c.range_start,
                range_end: c.range_end,
                original: c.original,
                provisional,
                cursor,
            };
            proof {
                assert(new_comp@ == spec_result.composition.unwrap());
            }
            RuntimeTextModel {
                composition: Some(new_comp),
                model: Ghost(spec_result),
                text: model.text,
                styles: model.styles,
                anchor: model.anchor,
                focus: model.focus,
                focus_affinity: model.focus_affinity,
                preferred_column: model.preferred_column,
                typing_style: model.typing_style,
                default_style: model.default_style,
                paragraph_styles: model.paragraph_styles,
            }
        },
        None => {
            // Shouldn't happen per requires, but needed for exhaustive match
            model
        },
    }
}

pub fn compose_commit_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        model@.composition.is_some(),
        ({
            let c = model@.composition.unwrap();
            let text_prime = seq_splice(
                model@.text, c.range_start as int, c.range_end as int, c.provisional);
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, c.range_start + c.provisional.len())
            &&& model@.text.len() - (c.range_end - c.range_start) + c.provisional.len() < usize::MAX
        }),
    ensures
        result@ == compose_commit(model@),
        result.wf_spec(),
{
    // We need to extract composition fields without consuming model.
    // Strategy: read fields through references, then pass model to splice_exec.
    if model.composition.is_some() {
        let comp_ref = model.composition.as_ref().unwrap();
        let range_start = comp_ref.range_start;
        let range_end = comp_ref.range_end;
        let prov_len = comp_ref.provisional.len();
        let ghost ghost_prov = comp_ref.provisional@;
        // Copy provisional text since we can't move it out of model
        let mut provisional: Vec<char> = Vec::new();
        let mut pi: usize = 0;
        while pi < prov_len
            invariant
                pi <= prov_len,
                prov_len == comp_ref.provisional.len(),
                ghost_prov == comp_ref.provisional@,
                provisional@ =~= ghost_prov.subrange(0, pi as int),
            decreases prov_len - pi,
        {
            provisional.push(comp_ref.provisional[pi]);
            proof {
                assert(ghost_prov.subrange(0, pi as int)
                    .push(ghost_prov[pi as int])
                    =~= ghost_prov.subrange(0, (pi + 1) as int));
            }
            pi += 1;
        }
        proof {
            assert(provisional@ =~= ghost_prov.subrange(0, ghost_prov.len() as int));
            assert(provisional@ =~= ghost_prov);
        }

        // Build styles for provisional text
        let mut new_styles: Vec<RuntimeStyleSet> = Vec::new();
        let mut i: usize = 0;
        while i < prov_len
            invariant
                i <= prov_len,
                model.wf_spec(),
                new_styles@.len() == i,
                forall|k: int| 0 <= k < i as int ==>
                    (#[trigger] new_styles@[k])@ == model@.typing_style,
            decreases prov_len - i,
        {
            new_styles.push(copy_style_set(&model.typing_style));
            i += 1;
        }
        proof {
            lemma_seq_repeat_len(model@.typing_style, provisional@.len());
            let gs = seq_repeat(model@.typing_style, provisional@.len());
            assert forall|k: int| 0 <= k < new_styles@.len()
                implies (#[trigger] new_styles@[k])@ == gs[k]
            by {
                lemma_seq_repeat_index(model@.typing_style, provisional@.len(), k);
            };
        }
        let ghost ghost_styles = seq_repeat(model@.typing_style, provisional@.len());
        splice_exec(
            model,
            range_start, range_end,
            provisional, new_styles,
            range_start + prov_len,
            Ghost(ghost_styles),
        )
    } else {
        model
    }
}

pub fn compose_cancel_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires model.wf_spec(),
    ensures
        result@ == compose_cancel(model@),
        result.wf_spec(),
{
    proof { lemma_compose_cancel_preserves_wf(model@); }
    let ghost spec_result = compose_cancel(model@);
    RuntimeTextModel {
        composition: None,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        anchor: model.anchor,
        focus: model.focus,
        focus_affinity: model.focus_affinity,
        preferred_column: model.preferred_column,
        typing_style: model.typing_style,
        default_style: model.default_style,
        paragraph_styles: model.paragraph_styles,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Sanitization helpers (exec)
// ──────────────────────────────────────────────────────────────────────

fn is_permitted_exec(c: char) -> (result: bool)
    ensures result == is_permitted(c),
{
    c != '\0' && c != '\u{FFF9}' && c != '\u{FFFA}' && c != '\u{FFFB}'
}

pub fn filter_permitted_exec(s: &Vec<char>) -> (out: Vec<char>)
    ensures out@ =~= filter_permitted(s@),
{
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ =~= filter_permitted(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        proof {
            let sub_i = s@.subrange(0, i as int);
            let sub_i1 = s@.subrange(0, (i + 1) as int);
            assert(sub_i1.len() > 0);
            assert(sub_i1.drop_last() =~= sub_i);
            assert(sub_i1.last() == s@[i as int]);
        }
        if is_permitted_exec(s[i]) {
            out.push(s[i]);
        }
        i += 1;
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
    out
}

pub fn canonicalize_newlines_exec(s: &Vec<char>) -> (out: Vec<char>)
    ensures out@ =~= canonicalize_newlines(s@),
{
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            out@ =~= canonicalize_newlines(s@.subrange(0, i as int)),
            // If prev char was \r, current can't be \n (consumed together)
            i > 0 && i < s.len() ==> (
                s@[(i - 1) as int] == '\r' ==> s@[i as int] != '\n'),
        decreases s.len() - i,
    {
        if s[i] == '\r' {
            if i + 1 < s.len() && s[i + 1] == '\n' {
                // \r\n pair → single \n
                out.push('\n');
                proof {
                    let sub = s@.subrange(0, (i + 2) as int);
                    assert(sub.len() >= 2);
                    assert(sub.last() == s@[(i + 1) as int]);
                    assert(sub[sub.len() as int - 2] == s@[i as int]);
                    assert(sub.subrange(0, sub.len() as int - 2)
                        =~= s@.subrange(0, i as int));
                }
                i += 2;
            } else {
                // bare \r → \n
                out.push('\n');
                proof {
                    let sub = s@.subrange(0, (i + 1) as int);
                    assert(sub.last() == s@[i as int]);
                    assert(sub.drop_last() =~= s@.subrange(0, i as int));
                }
                i += 1;
            }
        } else {
            out.push(s[i]);
            proof {
                let sub = s@.subrange(0, (i + 1) as int);
                assert(sub.last() == s@[i as int]);
                assert(sub.drop_last() =~= s@.subrange(0, i as int));
                if s@[i as int] == '\n' && i > 0 {
                    assert(sub.len() >= 2);
                    assert(sub[sub.len() as int - 2] == s@[(i - 1) as int]);
                    assert(s@[(i - 1) as int] != '\r');
                }
            }
            i += 1;
        }
    }
    proof { assert(s@.subrange(0, s@.len() as int) =~= s@); }
    out
}

// ──────────────────────────────────────────────────────────────────────
// Additional editing operations (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn insert_seq_exec(
    model: RuntimeTextModel,
    s: Vec<char>,
    styles: Vec<RuntimeStyleSet>,
    Ghost(ghost_styles): Ghost<Seq<StyleSet>>,
) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        s.len() == styles.len(),
        s@.len() == ghost_styles.len(),
        forall|i: int| 0 <= i < styles@.len() ==>
            (#[trigger] styles@[i])@ == ghost_styles[i],
        ({
            let (sel_start, sel_end) = selection_range(model@.anchor, model@.focus);
            let text_prime = seq_splice(
                model@.text, sel_start as int, sel_end as int, s@);
            &&& model@.text.len() - (sel_end - sel_start) + s@.len() < usize::MAX
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start + s@.len())
        }),
    ensures
        result@ == insert_seq(model@, s@, ghost_styles),
        result.wf_spec(),
{
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    let new_focus = sel_start + s.len();
    splice_exec(
        model, sel_start, sel_end,
        s, styles, new_focus,
        Ghost(ghost_styles),
    )
}

pub fn paste_exec(model: RuntimeTextModel, text: &Vec<char>) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        ({
            let clean = canonicalize_newlines(filter_permitted(text@));
            let (sel_start, sel_end) = selection_range(model@.anchor, model@.focus);
            let text_prime = seq_splice(
                model@.text, sel_start as int, sel_end as int, clean);
            &&& model@.text.len() - (sel_end - sel_start) + clean.len() < usize::MAX
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, sel_start + clean.len())
        }),
    ensures
        result@ == paste(model@, text@, Seq::empty()),
        result.wf_spec(),
{
    let filtered = filter_permitted_exec(text);
    let clean = canonicalize_newlines_exec(&filtered);

    // Build styles: seq_repeat(typing_style, clean.len())
    let mut clean_styles: Vec<RuntimeStyleSet> = Vec::new();
    let mut i: usize = 0;
    while i < clean.len()
        invariant
            i <= clean.len(),
            model.wf_spec(),
            clean_styles@.len() == i,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] clean_styles@[k])@ == model@.typing_style,
        decreases clean.len() - i,
    {
        clean_styles.push(copy_style_set(&model.typing_style));
        i += 1;
    }

    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    let new_focus = sel_start + clean.len();

    let ghost ghost_clean_styles = seq_repeat(model@.typing_style, clean@.len());
    proof {
        lemma_seq_repeat_len(model@.typing_style, clean@.len());
        assert forall|k: int| 0 <= k < clean_styles@.len()
            implies (#[trigger] clean_styles@[k])@ == ghost_clean_styles[k]
        by {
            lemma_seq_repeat_index(model@.typing_style, clean@.len(), k);
        };
    }

    splice_exec(
        model, sel_start, sel_end,
        clean, clean_styles, new_focus,
        Ghost(ghost_clean_styles),
    )
}

pub fn delete_word_backward_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        !has_selection(model@.anchor, model@.focus),
        model@.focus > 0,
        model@.text.len() > 0,
        ({
            let prev = prev_boundary_in(word_start_boundaries(model@.text), model@.focus);
            let text_prime = seq_splice(
                model@.text, prev as int, model@.focus as int, Seq::<char>::empty());
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, prev)
        }),
    ensures
        result@ == delete_word_backward(model@),
        result.wf_spec(),
{
    let prev = prev_word_start_exec(&model.text, model.focus);
    let focus = model.focus;
    proof {
        axiom_word_start_boundaries_valid(model@.text);
        lemma_prev_boundary_lt(word_start_boundaries(model@.text), model@.focus);
        // prev < focus, hence prev <= focus (start <= end for splice)
    }
    splice_exec(
        model, prev, focus,
        Vec::new(), Vec::new(), prev,
        Ghost(Seq::empty()),
    )
}

pub fn delete_word_forward_exec(model: RuntimeTextModel) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        !has_selection(model@.anchor, model@.focus),
        model@.focus < model@.text.len(),
        ({
            let next = next_boundary_in(word_end_boundaries(model@.text), model@.focus);
            let text_prime = seq_splice(
                model@.text, model@.focus as int, next as int, Seq::<char>::empty());
            &&& next <= model@.text.len()
            &&& wf_text(text_prime)
            &&& is_grapheme_boundary(text_prime, model@.focus)
        }),
    ensures
        result@ == delete_word_forward(model@),
        result.wf_spec(),
{
    let focus = model.focus;
    let next = next_word_end_exec(&model.text, focus);
    proof {
        axiom_word_end_boundaries_valid(model@.text);
        lemma_next_boundary_gt(word_end_boundaries(model@.text), model@.focus);
        // next > focus, hence focus <= next (start <= end for splice)
    }
    splice_exec(
        model, focus, next,
        Vec::new(), Vec::new(), focus,
        Ghost(Seq::empty()),
    )
}

// ──────────────────────────────────────────────────────────────────────
// Line helpers (exec)
// ──────────────────────────────────────────────────────────────────────

fn line_start_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires pos <= text.len(),
    ensures result as nat == line_start(text@, pos as nat),
{
    let mut p = pos;
    while p > 0
        invariant
            p <= pos, pos <= text.len(),
            line_start(text@, p as nat) == line_start(text@, pos as nat),
        decreases p,
    {
        if text[p - 1] == '\n' {
            return p;
        }
        p -= 1;
    }
    0
}

fn line_end_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires pos <= text.len(),
    ensures result as nat == line_end(text@, pos as nat),
{
    let mut p = pos;
    while p < text.len()
        invariant
            pos <= p, p <= text.len(),
            line_end(text@, p as nat) == line_end(text@, pos as nat),
        decreases text.len() - p,
    {
        if text[p] == '\n' {
            return p;
        }
        p += 1;
    }
    text.len()
}

// ──────────────────────────────────────────────────────────────────────
// Visual layout (external body)
// ──────────────────────────────────────────────────────────────────────

#[verifier::external_body]
pub fn text_pos_to_visual_exec(
    text: &Vec<char>, pos: usize, aff: Affinity,
) -> (result: (usize, usize))
    ensures
        result.0 as nat == text_pos_to_visual(text@, pos as nat, aff).0,
        result.1 as nat == text_pos_to_visual(text@, pos as nat, aff).1,
        result.0 <= text.len(),
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let clamped = pos.min(text.len());
    // Count '\n' before pos for line, grapheme clusters since last '\n' for column
    let prefix: String = s.chars().take(clamped).collect();
    let line = prefix.matches('\n').count();
    // Column = grapheme clusters from last '\n' to pos
    let last_newline = prefix.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let col = prefix[last_newline..].graphemes(true).count();
    (line, col)
}

#[verifier::external_body]
pub fn visual_to_text_pos_exec(
    text: &Vec<char>, line: usize, col: usize,
) -> (result: (usize, Affinity))
    ensures
        result.0 as nat == visual_to_text_pos(text@, line as nat, col as nat).0,
        result.1 == visual_to_text_pos(text@, line as nat, col as nat).1,
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    // Find the start of the target line by counting '\n'
    let mut current_line: usize = 0;
    let mut byte_pos: usize = 0;
    for (i, ch) in s.char_indices() {
        if current_line >= line {
            byte_pos = i;
            break;
        }
        if ch == '\n' {
            current_line += 1;
        }
        byte_pos = i + ch.len_utf8();
    }
    if current_line < line {
        // Target line doesn't exist, return end of text
        return (text.len(), Affinity::Upstream);
    }
    let line_start_byte = byte_pos;
    let line_start_char = s[..line_start_byte].chars().count();
    // Advance by col grapheme clusters within this line
    let line_str = &s[line_start_byte..];
    let line_end_byte = line_str.find('\n').unwrap_or(line_str.len());
    let line_content = &line_str[..line_end_byte];
    let mut char_offset = line_start_char;
    let mut grapheme_count = 0usize;
    for grapheme in line_content.graphemes(true) {
        if grapheme_count >= col {
            break;
        }
        char_offset += grapheme.chars().count();
        grapheme_count += 1;
    }
    let aff = if char_offset > line_start_char {
        Affinity::Upstream
    } else {
        Affinity::Downstream
    };
    (char_offset, aff)
}

// ──────────────────────────────────────────────────────────────────────
// Cursor movement (exec)
// ──────────────────────────────────────────────────────────────────────

/// Spec helper: convert Option<usize> to Option<nat>.
pub open spec fn opt_nat_view(o: Option<usize>) -> Option<nat> {
    match o { Some(n) => Some(n as nat), None => None }
}

pub fn move_cursor_exec(model: RuntimeTextModel, dir: MoveDirection) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        model.text.len() < usize::MAX,
        ({
            let (new_focus, _, _) = resolve_movement(
                model@.text, model@.focus, model@.focus_affinity,
                model@.preferred_column, dir);
            &&& new_focus <= model@.text.len()
            &&& is_grapheme_boundary(model@.text, new_focus)
        }),
    ensures
        result@ == move_cursor(model@, dir),
        result.wf_spec(),
{
    let ghost spec_resolve = resolve_movement(
        model@.text, model@.focus, model@.focus_affinity,
        model@.preferred_column, dir);

    // Compute new_focus, new_aff, new_pref based on direction
    let (new_focus, new_aff, new_pref): (usize, Affinity, Option<usize>) = match dir {
        MoveDirection::Left => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                prev_grapheme_boundary_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::Right => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                next_grapheme_boundary_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::WordLeft => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                prev_word_start_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::WordRight => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                next_word_end_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::LineStart => {
            let new_pos = line_start_exec(&model.text, model.focus);
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::LineEnd => {
            let new_pos = line_end_exec(&model.text, model.focus);
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::Home => {
            (0, Affinity::Downstream, None)
        },
        MoveDirection::End => {
            (model.text.len(), Affinity::Upstream, None)
        },
        MoveDirection::Up => {
            let aff = match model.focus_affinity {
                Affinity::Upstream => Affinity::Upstream,
                Affinity::Downstream => Affinity::Downstream,
            };
            let (cur_line, cur_col) = text_pos_to_visual_exec(
                &model.text, model.focus, aff);
            let col = match model.preferred_column {
                Some(c) => c,
                None => cur_col,
            };
            if cur_line == 0 {
                (0, Affinity::Downstream, Some(col))
            } else {
                let (new_pos, new_aff) = visual_to_text_pos_exec(
                    &model.text, cur_line - 1, col);
                (new_pos, new_aff, Some(col))
            }
        },
        MoveDirection::Down => {
            let aff = match model.focus_affinity {
                Affinity::Upstream => Affinity::Upstream,
                Affinity::Downstream => Affinity::Downstream,
            };
            let (cur_line, cur_col) = text_pos_to_visual_exec(
                &model.text, model.focus, aff);
            let col = match model.preferred_column {
                Some(c) => c,
                None => cur_col,
            };
            let (new_pos, new_aff) = visual_to_text_pos_exec(
                &model.text, cur_line + 1, col);
            if new_pos > model.text.len() {
                (model.text.len(), Affinity::Upstream, Some(col))
            } else {
                (new_pos, new_aff, Some(col))
            }
        },
    };

    let new_typing = resolve_typing_style_exec(
        &model.text, &model.styles, new_focus, &model.default_style);

    proof {
        lemma_move_cursor_preserves_wf(model@, dir);
    }

    let ghost spec_result = move_cursor(model@, dir);

    RuntimeTextModel {
        anchor: new_focus,
        focus: new_focus,
        focus_affinity: new_aff,
        preferred_column: new_pref,
        typing_style: new_typing,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

pub fn extend_selection_exec(model: RuntimeTextModel, dir: MoveDirection) -> (result: RuntimeTextModel)
    requires
        model.wf_spec(),
        model.text.len() < usize::MAX,
        ({
            let (new_focus, _, _) = resolve_movement(
                model@.text, model@.focus, model@.focus_affinity,
                model@.preferred_column, dir);
            &&& new_focus <= model@.text.len()
            &&& is_grapheme_boundary(model@.text, new_focus)
        }),
    ensures
        result@ == extend_selection(model@, dir),
        result.wf_spec(),
{
    // Compute new_focus, new_aff, new_pref based on direction
    let (new_focus, new_aff, new_pref): (usize, Affinity, Option<usize>) = match dir {
        MoveDirection::Left => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                prev_grapheme_boundary_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::Right => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                next_grapheme_boundary_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::WordLeft => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                prev_word_start_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::WordRight => {
            let new_pos = if model.text.len() == 0 { 0 } else {
                next_word_end_exec(&model.text, model.focus)
            };
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::LineStart => {
            let new_pos = line_start_exec(&model.text, model.focus);
            (new_pos, Affinity::Downstream, None)
        },
        MoveDirection::LineEnd => {
            let new_pos = line_end_exec(&model.text, model.focus);
            (new_pos, Affinity::Upstream, None)
        },
        MoveDirection::Home => {
            (0, Affinity::Downstream, None)
        },
        MoveDirection::End => {
            (model.text.len(), Affinity::Upstream, None)
        },
        MoveDirection::Up => {
            let aff = match model.focus_affinity {
                Affinity::Upstream => Affinity::Upstream,
                Affinity::Downstream => Affinity::Downstream,
            };
            let (cur_line, cur_col) = text_pos_to_visual_exec(
                &model.text, model.focus, aff);
            let col = match model.preferred_column {
                Some(c) => c,
                None => cur_col,
            };
            if cur_line == 0 {
                (0, Affinity::Downstream, Some(col))
            } else {
                let (new_pos, new_aff) = visual_to_text_pos_exec(
                    &model.text, cur_line - 1, col);
                (new_pos, new_aff, Some(col))
            }
        },
        MoveDirection::Down => {
            let aff = match model.focus_affinity {
                Affinity::Upstream => Affinity::Upstream,
                Affinity::Downstream => Affinity::Downstream,
            };
            let (cur_line, cur_col) = text_pos_to_visual_exec(
                &model.text, model.focus, aff);
            let col = match model.preferred_column {
                Some(c) => c,
                None => cur_col,
            };
            let (new_pos, new_aff) = visual_to_text_pos_exec(
                &model.text, cur_line + 1, col);
            if new_pos > model.text.len() {
                (model.text.len(), Affinity::Upstream, Some(col))
            } else {
                (new_pos, new_aff, Some(col))
            }
        },
    };

    // extend_selection uses is_horizontal to decide preferred_column
    let final_pref = match dir {
        MoveDirection::Up | MoveDirection::Down => new_pref,
        _ => None,
    };

    proof {
        lemma_extend_selection_preserves_wf(model@, dir);
    }

    let ghost spec_result = extend_selection(model@, dir);

    RuntimeTextModel {
        focus: new_focus,
        focus_affinity: new_aff,
        preferred_column: final_pref,
        model: Ghost(spec_result),
        text: model.text,
        styles: model.styles,
        anchor: model.anchor,
        typing_style: model.typing_style,
        default_style: model.default_style,
        composition: model.composition,
        paragraph_styles: model.paragraph_styles,
    }
}

// ──────────────────────────────────────────────────────────────────────
// Undo runtime types
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeUndoEntry {
    pub start: usize,
    pub removed_text: Vec<char>,
    pub removed_styles: Vec<RuntimeStyleSet>,
    pub inserted_text: Vec<char>,
    pub inserted_styles: Vec<RuntimeStyleSet>,
    pub anchor_before: usize,
    pub focus_before: usize,
    pub focus_after: usize,
}

impl View for RuntimeUndoEntry {
    type V = UndoEntry;
    open spec fn view(&self) -> UndoEntry {
        UndoEntry {
            start: self.start as nat,
            removed_text: self.removed_text@,
            removed_styles: style_seq_view(self.removed_styles@),
            inserted_text: self.inserted_text@,
            inserted_styles: style_seq_view(self.inserted_styles@),
            anchor_before: self.anchor_before as nat,
            focus_before: self.focus_before as nat,
            focus_after: self.focus_after as nat,
        }
    }
}

pub struct RuntimeUndoStack {
    pub entries: Vec<RuntimeUndoEntry>,
    pub position: usize,
    pub model: Ghost<UndoStack>,
}

impl View for RuntimeUndoStack {
    type V = UndoStack;
    open spec fn view(&self) -> UndoStack {
        self.model@
    }
}

impl RuntimeUndoStack {
    pub open spec fn wf_spec(&self) -> bool {
        &&& undo_stack_wf(self.model@)
        &&& self.position as nat == self.model@.position
        &&& self.entries@.len() == self.model@.entries.len()
        &&& forall|i: int| 0 <= i < self.entries@.len() ==>
            (#[trigger] self.entries@[i])@ == self.model@.entries[i]
    }
}

pub fn empty_undo_stack_exec() -> (out: RuntimeUndoStack)
    ensures
        out@ == empty_undo_stack(),
        out.wf_spec(),
{
    RuntimeUndoStack {
        entries: Vec::new(),
        position: 0,
        model: Ghost(empty_undo_stack()),
    }
}

pub fn can_undo_exec(stack: &RuntimeUndoStack) -> (result: bool)
    requires stack.wf_spec(),
    ensures result == can_undo(stack@),
{
    stack.position > 0
}

pub fn can_redo_exec(stack: &RuntimeUndoStack) -> (result: bool)
    requires stack.wf_spec(),
    ensures result == can_redo(stack@),
{
    stack.position < stack.entries.len()
}

// ──────────────────────────────────────────────────────────────────────
// Undo operations (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn undo_entry_for_splice_exec(
    model: &RuntimeTextModel,
    start: usize,
    end: usize,
    new_text: &Vec<char>,
    new_styles: &Vec<RuntimeStyleSet>,
    new_focus: usize,
) -> (out: RuntimeUndoEntry)
    requires
        model.wf_spec(),
        start <= end,
        end <= model.text.len(),
        new_text@.len() == new_styles@.len(),
    ensures
        out@ == undo_entry_for_splice(
            model@, start as nat, end as nat,
            new_text@, style_seq_view(new_styles@), new_focus as nat),
        undo_entry_wf(out@),
{
    // Copy model.text[start..end) into removed_text
    let mut removed_text: Vec<char> = Vec::new();
    let mut i: usize = start;
    while i < end
        invariant
            start <= i, i <= end, end <= model.text.len(),
            removed_text@ =~= model.text@.subrange(start as int, i as int),
        decreases end - i,
    {
        removed_text.push(model.text[i]);
        proof {
            assert(model.text@.subrange(start as int, i as int)
                .push(model.text@[i as int])
                =~= model.text@.subrange(start as int, (i + 1) as int));
        }
        i += 1;
    }

    // Copy model.styles[start..end) into removed_styles
    let mut removed_styles: Vec<RuntimeStyleSet> = Vec::new();
    let mut j: usize = start;
    while j < end
        invariant
            start <= j, j <= end, end <= model.styles.len(),
            model.wf_spec(),
            removed_styles@.len() == j - start,
            forall|k: int| 0 <= k < (j - start) as int ==>
                (#[trigger] removed_styles@[k])@ == model@.styles[start as int + k],
        decreases end - j,
    {
        removed_styles.push(copy_style_set(&model.styles[j]));
        j += 1;
    }

    // Copy new_text and new_styles
    let inserted_text = copy_char_vec(new_text);
    let inserted_styles = copy_style_vec(new_styles);

    proof {
        // Connect removed_styles view to spec subrange
        let spec_removed = model@.styles.subrange(start as int, end as int);
        assert(style_seq_view(removed_styles@) =~= spec_removed) by {
            assert(style_seq_view(removed_styles@).len() == spec_removed.len());
            assert forall|k: int| 0 <= k < style_seq_view(removed_styles@).len()
                implies style_seq_view(removed_styles@)[k] == spec_removed[k]
            by {
                assert(removed_styles@[k]@ == model@.styles[start as int + k]);
            };
        };
        // Connect inserted_styles view
        assert(style_seq_view(inserted_styles@) =~= style_seq_view(new_styles@)) by {
            assert(style_seq_view(inserted_styles@).len() == style_seq_view(new_styles@).len());
            assert forall|k: int| 0 <= k < style_seq_view(inserted_styles@).len()
                implies style_seq_view(inserted_styles@)[k] == style_seq_view(new_styles@)[k]
            by {};
        };
    }

    RuntimeUndoEntry {
        start,
        removed_text,
        removed_styles,
        inserted_text,
        inserted_styles,
        anchor_before: model.anchor,
        focus_before: model.focus,
        focus_after: new_focus,
    }
}

pub fn push_undo_exec(stack: RuntimeUndoStack, entry: RuntimeUndoEntry) -> (out: RuntimeUndoStack)
    requires
        stack.wf_spec(),
        undo_entry_wf(entry@),
        stack.entries.len() < usize::MAX,
    ensures
        out@ == push_undo(stack@, entry@),
        out.wf_spec(),
{
    let ghost old_spec = stack@;
    let ghost entry_view = entry@;
    let pos = stack.position;
    let mut entries = stack.entries;

    // Truncate entries beyond position
    while entries.len() > pos
        invariant
            pos <= entries.len(),
            forall|i: int| 0 <= i < entries@.len() ==>
                (#[trigger] entries@[i])@ == old_spec.entries[i],
        decreases entries.len() - pos,
    {
        entries.pop();
    }

    entries.push(entry);

    proof {
        lemma_push_preserves_wf(old_spec, entry_view);
        let new_spec = push_undo(old_spec, entry_view);
        assert forall|i: int| 0 <= i < entries@.len()
            implies (#[trigger] entries@[i])@ == new_spec.entries[i]
        by {
            if i < pos as int {
                assert(new_spec.entries[i]
                    == old_spec.entries.subrange(0, old_spec.position as int)[i]);
            }
        };
    }

    RuntimeUndoStack {
        entries,
        position: pos + 1,
        model: Ghost(push_undo(old_spec, entry_view)),
    }
}

pub fn record_edit_exec(
    stack: RuntimeUndoStack,
    model: &RuntimeTextModel,
    start: usize,
    end: usize,
    new_text: &Vec<char>,
    new_styles: &Vec<RuntimeStyleSet>,
    new_focus: usize,
) -> (out: RuntimeUndoStack)
    requires
        stack.wf_spec(),
        model.wf_spec(),
        start <= end,
        end <= model.text.len(),
        new_text@.len() == new_styles@.len(),
        stack.entries.len() < usize::MAX,
    ensures
        out@ == record_edit(stack@, model@, start as nat, end as nat,
                            new_text@, style_seq_view(new_styles@), new_focus as nat),
        out.wf_spec(),
{
    let entry = undo_entry_for_splice_exec(model, start, end, new_text, new_styles, new_focus);
    push_undo_exec(stack, entry)
}

pub fn can_merge_entries_exec(e1: &RuntimeUndoEntry, e2: &RuntimeUndoEntry) -> (result: bool)
    ensures result == can_merge_entries(e1@, e2@),
{
    e1.removed_text.len() == 0
        && e2.removed_text.len() == 0
        && e2.start >= e1.start
        && e2.start - e1.start == e1.inserted_text.len()
}

pub fn merge_entries_exec(
    e1: RuntimeUndoEntry, e2: RuntimeUndoEntry,
) -> (out: RuntimeUndoEntry)
    requires
        undo_entry_wf(e1@),
        undo_entry_wf(e2@),
        can_merge_entries(e1@, e2@),
    ensures
        out@ == merge_entries(e1@, e2@),
        undo_entry_wf(out@),
{
    let ghost e1_spec = e1@;
    let ghost e2_spec = e2@;

    let e1_start = e1.start;
    let e1_anchor_before = e1.anchor_before;
    let e1_focus_before = e1.focus_before;
    let e2_focus_after = e2.focus_after;

    // Concatenate inserted_text: e1.inserted_text + e2.inserted_text
    let mut ins_text = e1.inserted_text;
    let e2_inserted_text = e2.inserted_text;
    let mut i: usize = 0;
    while i < e2_inserted_text.len()
        invariant
            i <= e2_inserted_text.len(),
            e2_inserted_text@ == e2_spec.inserted_text,
            ins_text@ =~= e1_spec.inserted_text + e2_spec.inserted_text.subrange(0, i as int),
        decreases e2_inserted_text.len() - i,
    {
        ins_text.push(e2_inserted_text[i]);
        proof {
            assert(e2_spec.inserted_text.subrange(0, i as int).push(e2_spec.inserted_text[i as int])
                =~= e2_spec.inserted_text.subrange(0, (i + 1) as int));
        }
        i += 1;
    }
    proof {
        assert(e2_spec.inserted_text.subrange(0, e2_spec.inserted_text.len() as int)
            =~= e2_spec.inserted_text);
    }

    // Concatenate inserted_styles: e1.inserted_styles + e2.inserted_styles
    let mut ins_styles = e1.inserted_styles;
    let e2_inserted_styles = e2.inserted_styles;
    let mut j: usize = 0;
    while j < e2_inserted_styles.len()
        invariant
            j <= e2_inserted_styles.len(),
            ins_styles@.len() == e1_spec.inserted_styles.len() + j,
            forall|k: int| 0 <= k < e1_spec.inserted_styles.len() ==>
                (#[trigger] ins_styles@[k])@ == e1_spec.inserted_styles[k],
            forall|k: int| 0 <= k < j as int ==>
                (#[trigger] ins_styles@[e1_spec.inserted_styles.len() as int + k])@
                    == e2_spec.inserted_styles[k],
            forall|k: int| 0 <= k < e2_inserted_styles@.len() ==>
                (#[trigger] e2_inserted_styles@[k])@ == e2_spec.inserted_styles[k],
        decreases e2_inserted_styles.len() - j,
    {
        ins_styles.push(copy_style_set(&e2_inserted_styles[j]));
        j += 1;
    }

    let removed_text: Vec<char> = Vec::new();
    let removed_styles: Vec<RuntimeStyleSet> = Vec::new();

    proof {
        lemma_merge_entry_wf(e1_spec, e2_spec);
        let merged_spec = merge_entries(e1_spec, e2_spec);
        // Empty removed seqs
        assert(removed_text@ =~= Seq::<char>::empty());
        assert(style_seq_view(removed_styles@) =~= Seq::<StyleSet>::empty());
        // Connect style_seq_view(ins_styles@) to merged entry spec
        assert(style_seq_view(ins_styles@) =~= merged_spec.inserted_styles) by {
            assert forall|k: int| 0 <= k < style_seq_view(ins_styles@).len()
                implies style_seq_view(ins_styles@)[k] == merged_spec.inserted_styles[k]
            by {
                if k < e1_spec.inserted_styles.len() as int {
                    assert(ins_styles@[k]@ == e1_spec.inserted_styles[k]);
                } else {
                    let offset = k - e1_spec.inserted_styles.len() as int;
                    assert(ins_styles@[e1_spec.inserted_styles.len() as int + offset]@
                        == e2_spec.inserted_styles[offset]);
                    assert(k == e1_spec.inserted_styles.len() as int + offset);
                }
            };
        };
    }

    let out = RuntimeUndoEntry {
        start: e1_start,
        removed_text,
        removed_styles,
        inserted_text: ins_text,
        inserted_styles: ins_styles,
        anchor_before: e1_anchor_before,
        focus_before: e1_focus_before,
        focus_after: e2_focus_after,
    };

    proof {
        let merged_spec = merge_entries(e1_spec, e2_spec);
        assert(out@.start == merged_spec.start);
        assert(out@.removed_text =~= merged_spec.removed_text);
        assert(out@.removed_styles =~= merged_spec.removed_styles);
        assert(out@.inserted_text =~= merged_spec.inserted_text);
        assert(out@.inserted_styles =~= merged_spec.inserted_styles);
        assert(out@.anchor_before == merged_spec.anchor_before);
        assert(out@.focus_before == merged_spec.focus_before);
        assert(out@.focus_after == merged_spec.focus_after);
    }
    out
}

fn copy_undo_entry(e: &RuntimeUndoEntry) -> (out: RuntimeUndoEntry)
    ensures out@ == e@,
{
    let removed_text = copy_char_vec(&e.removed_text);
    let removed_styles = copy_style_vec(&e.removed_styles);
    let inserted_text = copy_char_vec(&e.inserted_text);
    let inserted_styles = copy_style_vec(&e.inserted_styles);

    let out = RuntimeUndoEntry {
        start: e.start,
        removed_text,
        removed_styles,
        inserted_text,
        inserted_styles,
        anchor_before: e.anchor_before,
        focus_before: e.focus_before,
        focus_after: e.focus_after,
    };

    proof {
        // Connect style_seq_view for removed_styles
        assert(style_seq_view(out.removed_styles@) =~= e@.removed_styles) by {
            assert forall|k: int| 0 <= k < out.removed_styles@.len()
                implies style_seq_view(out.removed_styles@)[k] == e@.removed_styles[k]
            by {
                assert(out.removed_styles@[k]@ == e.removed_styles@[k]@);
            };
        };
        // Connect style_seq_view for inserted_styles
        assert(style_seq_view(out.inserted_styles@) =~= e@.inserted_styles) by {
            assert forall|k: int| 0 <= k < out.inserted_styles@.len()
                implies style_seq_view(out.inserted_styles@)[k] == e@.inserted_styles[k]
            by {
                assert(out.inserted_styles@[k]@ == e.inserted_styles@[k]@);
            };
        };
    }
    out
}

pub fn push_undo_or_merge_exec(
    stack: RuntimeUndoStack, entry: RuntimeUndoEntry, merge: bool,
) -> (out: RuntimeUndoStack)
    requires
        stack.wf_spec(),
        undo_entry_wf(entry@),
        stack.entries.len() < usize::MAX,
    ensures
        out@ == push_undo_or_merge(stack@, entry@, merge),
        out.wf_spec(),
{
    if merge && can_undo_exec(&stack) {
        let pos = stack.position;
        if can_merge_entries_exec(&stack.entries[pos - 1], &entry) {
            let ghost old_spec = stack@;
            let ghost entry_spec = entry@;

            // Copy top entry and merge
            let top_copy = copy_undo_entry(&stack.entries[pos - 1]);
            let merged = merge_entries_exec(top_copy, entry);

            // Create a temp stack at position-1, reuse push_undo_exec
            let ghost temp_spec = UndoStack {
                entries: old_spec.entries,
                position: (old_spec.position - 1) as nat,
            };
            proof {
                // temp_spec is wf
                assert(undo_stack_wf(temp_spec)) by {
                    assert(temp_spec.position <= temp_spec.entries.len());
                    assert forall|i: int| 0 <= i < temp_spec.entries.len()
                        implies undo_entry_wf(#[trigger] temp_spec.entries[i])
                    by {
                        assert(temp_spec.entries[i] == old_spec.entries[i]);
                    };
                };
                assert(undo_entry_wf(merged@));
            }

            let temp_stack = RuntimeUndoStack {
                entries: stack.entries,
                position: pos - 1,
                model: Ghost(temp_spec),
            };

            let result = push_undo_exec(temp_stack, merged);

            proof {
                // push_undo(temp_spec, merged@) == push_undo_or_merge(old_spec, entry_spec, merge)
                // push_undo truncates to position and pushes:
                //   entries = temp_spec.entries.subrange(0, temp_spec.position).push(merged@)
                //           = old_spec.entries.subrange(0, (pos-1)).push(merged@)
                //   position = temp_spec.position + 1 = pos
                // push_undo_or_merge in merge path:
                //   entries = old_spec.entries.subrange(0, (pos-1)).push(merge_entries(top, entry_spec))
                //   position = pos
                // These are equal since merged@ == merge_entries(top@, entry_spec)
                //   and top@ == old_spec.entries[(pos-1)]
                lemma_push_or_merge_preserves_wf(old_spec, entry_spec, merge);
            }

            proof {
                // result@ == push_undo(temp_spec, merged@)
                // Need to show this equals push_undo_or_merge(old_spec, entry_spec, merge)
                assert(result@ == push_undo(temp_spec, merged@));
                assert(push_undo_or_merge(old_spec, entry_spec, merge)
                    == UndoStack {
                        entries: old_spec.entries.subrange(0, (old_spec.position - 1) as int)
                            .push(merge_entries(
                                old_spec.entries[(old_spec.position - 1) as int],
                                entry_spec)),
                        position: old_spec.position,
                    });
                assert(push_undo(temp_spec, merged@)
                    == UndoStack {
                        entries: temp_spec.entries.subrange(0, temp_spec.position as int)
                            .push(merged@),
                        position: temp_spec.position + 1,
                    });
                // temp_spec.position = old_spec.position - 1
                // temp_spec.entries = old_spec.entries
                // merged@ = merge_entries(top_copy@, entry_spec) = merge_entries(old_spec.entries[pos-1], entry_spec)
                assert(temp_spec.entries.subrange(0, temp_spec.position as int)
                    =~= old_spec.entries.subrange(0, (old_spec.position - 1) as int));
                assert(merged@ == merge_entries(
                    old_spec.entries[(old_spec.position - 1) as int], entry_spec));
            }

            result
        } else {
            push_undo_exec(stack, entry)
        }
    } else {
        push_undo_exec(stack, entry)
    }
}

pub fn apply_undo_exec(stack: RuntimeUndoStack, model: RuntimeTextModel)
    -> (out: (RuntimeUndoStack, RuntimeTextModel))
    requires
        stack.wf_spec(),
        model.wf_spec(),
        can_undo(stack@),
        ({
            let entry = stack@.entries[(stack@.position - 1) as int];
            let undo_end = entry.start + entry.inserted_text.len();
            &&& undo_end <= model@.text.len()
            &&& entry.focus_before <= model@.text.len()
                - entry.inserted_text.len() + entry.removed_text.len()
            &&& model@.text.len() - entry.inserted_text.len()
                + entry.removed_text.len() < usize::MAX
            &&& wf_text(seq_splice(model@.text, entry.start as int,
                    undo_end as int, entry.removed_text))
            &&& is_grapheme_boundary(
                    seq_splice(model@.text, entry.start as int,
                        undo_end as int, entry.removed_text),
                    entry.focus_before)
        }),
    ensures
        out.0@ == apply_undo(stack@, model@).0,
        out.1@ == apply_undo(stack@, model@).1,
        out.0.wf_spec(),
        out.1.wf_spec(),
{
    let ghost old_stack_view = stack@;
    let ghost old_model_view = model@;
    let pos = stack.position - 1;

    // Read entry fields
    let start = stack.entries[pos].start;
    let ins_len = stack.entries[pos].inserted_text.len();
    let undo_end = start + ins_len;
    let new_focus = stack.entries[pos].focus_before;

    // Copy removed text/styles from entry (these become splice input)
    let new_text = copy_char_vec(&stack.entries[pos].removed_text);
    let new_styles = copy_style_vec(&stack.entries[pos].removed_styles);

    let ghost spec_entry = old_stack_view.entries[(old_stack_view.position - 1) as int];
    let ghost ghost_new_styles = spec_entry.removed_styles;

    proof {
        // Connect runtime entry to spec entry
        assert(stack.entries@[pos as int]@ == spec_entry);
        assert(start as nat == spec_entry.start);
        assert(undo_end as nat == spec_entry.start + spec_entry.inserted_text.len());
        assert(new_focus as nat == spec_entry.focus_before);
        assert(new_text@ =~= spec_entry.removed_text);

        // new_styles correspondence
        assert forall|i: int| 0 <= i < new_styles@.len()
            implies (#[trigger] new_styles@[i])@ == ghost_new_styles[i]
        by {
            assert(new_styles@[i]@ == stack.entries@[pos as int].removed_styles@[i]@);
        };

        // removed_text.len() == removed_styles.len() from undo_entry_wf
        assert(undo_entry_wf(spec_entry));
        assert(new_text.len() == new_styles.len());
    }

    let new_model = splice_exec(
        model, start, undo_end,
        new_text, new_styles, new_focus,
        Ghost(ghost_new_styles),
    );

    let ghost new_stack_spec = apply_undo(old_stack_view, old_model_view).0;

    proof {
        lemma_undo_preserves_wf(old_stack_view, old_model_view);
        // Entry correspondence (entries unchanged)
        assert forall|i: int| 0 <= i < stack.entries@.len()
            implies (#[trigger] stack.entries@[i])@ == new_stack_spec.entries[i]
        by {
            assert(stack.entries@[i]@ == old_stack_view.entries[i]);
            assert(new_stack_spec.entries[i] == old_stack_view.entries[i]);
        };
    }

    let new_stack = RuntimeUndoStack {
        entries: stack.entries,
        position: pos,
        model: Ghost(new_stack_spec),
    };

    (new_stack, new_model)
}

pub fn apply_redo_exec(stack: RuntimeUndoStack, model: RuntimeTextModel)
    -> (out: (RuntimeUndoStack, RuntimeTextModel))
    requires
        stack.wf_spec(),
        model.wf_spec(),
        can_redo(stack@),
        ({
            let entry = stack@.entries[stack@.position as int];
            let redo_end = entry.start + entry.removed_text.len();
            &&& redo_end <= model@.text.len()
            &&& entry.focus_after <= model@.text.len()
                - entry.removed_text.len() + entry.inserted_text.len()
            &&& model@.text.len() - entry.removed_text.len()
                + entry.inserted_text.len() < usize::MAX
            &&& wf_text(seq_splice(model@.text, entry.start as int,
                    redo_end as int, entry.inserted_text))
            &&& is_grapheme_boundary(
                    seq_splice(model@.text, entry.start as int,
                        redo_end as int, entry.inserted_text),
                    entry.focus_after)
        }),
    ensures
        out.0@ == apply_redo(stack@, model@).0,
        out.1@ == apply_redo(stack@, model@).1,
        out.0.wf_spec(),
        out.1.wf_spec(),
{
    let ghost old_stack_view = stack@;
    let ghost old_model_view = model@;
    let pos = stack.position;

    // Read entry fields
    let start = stack.entries[pos].start;
    let rem_len = stack.entries[pos].removed_text.len();
    let redo_end = start + rem_len;
    let new_focus = stack.entries[pos].focus_after;

    // Copy inserted text/styles from entry (these become splice input)
    let new_text = copy_char_vec(&stack.entries[pos].inserted_text);
    let new_styles = copy_style_vec(&stack.entries[pos].inserted_styles);

    let ghost spec_entry = old_stack_view.entries[old_stack_view.position as int];
    let ghost ghost_new_styles = spec_entry.inserted_styles;

    proof {
        // Connect runtime entry to spec entry
        assert(stack.entries@[pos as int]@ == spec_entry);
        assert(start as nat == spec_entry.start);
        assert(redo_end as nat == spec_entry.start + spec_entry.removed_text.len());
        assert(new_focus as nat == spec_entry.focus_after);
        assert(new_text@ =~= spec_entry.inserted_text);

        // new_styles correspondence
        assert forall|i: int| 0 <= i < new_styles@.len()
            implies (#[trigger] new_styles@[i])@ == ghost_new_styles[i]
        by {
            assert(new_styles@[i]@ == stack.entries@[pos as int].inserted_styles@[i]@);
        };

        // inserted_text.len() == inserted_styles.len() from undo_entry_wf
        assert(undo_entry_wf(spec_entry));
        assert(new_text.len() == new_styles.len());
    }

    let new_model = splice_exec(
        model, start, redo_end,
        new_text, new_styles, new_focus,
        Ghost(ghost_new_styles),
    );

    let ghost new_stack_spec = apply_redo(old_stack_view, old_model_view).0;

    proof {
        lemma_redo_preserves_wf(old_stack_view, old_model_view);
        // Entry correspondence (entries unchanged)
        assert forall|i: int| 0 <= i < stack.entries@.len()
            implies (#[trigger] stack.entries@[i])@ == new_stack_spec.entries[i]
        by {
            assert(stack.entries@[i]@ == old_stack_view.entries[i]);
            assert(new_stack_spec.entries[i] == old_stack_view.entries[i]);
        };
    }

    proof {
        // can_redo: pos < entries.len(), so pos + 1 won't overflow
        assert(pos < stack.entries.len());
    }

    let new_stack = RuntimeUndoStack {
        entries: stack.entries,
        position: pos + 1,
        model: Ghost(new_stack_spec),
    };

    (new_stack, new_model)
}

// ──────────────────────────────────────────────────────────────────────
// Selection extraction (exec)
// ──────────────────────────────────────────────────────────────────────

pub fn get_selection_text_exec(model: &RuntimeTextModel) -> (out: Vec<char>)
    requires model.wf_spec(),
    ensures out@ == get_selection_text(model@),
{
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    let mut out: Vec<char> = Vec::new();
    let mut i: usize = sel_start;
    while i < sel_end
        invariant
            sel_start <= i,
            i <= sel_end,
            sel_end <= model.text.len(),
            model.wf_spec(),
            out@ =~= model.text@.subrange(sel_start as int, i as int),
        decreases sel_end - i,
    {
        out.push(model.text[i]);
        proof {
            assert(model.text@.subrange(sel_start as int, i as int)
                .push(model.text@[i as int])
                =~= model.text@.subrange(sel_start as int, (i + 1) as int));
        }
        i += 1;
    }
    out
}

pub fn get_selection_styles_exec(model: &RuntimeTextModel) -> (out: Vec<RuntimeStyleSet>)
    requires model.wf_spec(),
    ensures
        out@.len() == get_selection_styles(model@).len(),
        forall|k: int| 0 <= k < out@.len() ==>
            (#[trigger] out@[k])@ == get_selection_styles(model@)[k],
{
    let sel_start = if model.anchor <= model.focus { model.anchor } else { model.focus };
    let sel_end = if model.anchor <= model.focus { model.focus } else { model.anchor };
    let mut out: Vec<RuntimeStyleSet> = Vec::new();
    let mut i: usize = sel_start;
    while i < sel_end
        invariant
            sel_start <= i,
            i <= sel_end,
            sel_end <= model.styles.len(),
            model.wf_spec(),
            out@.len() == (i - sel_start) as nat,
            forall|k: int| 0 <= k < out@.len() ==>
                (#[trigger] out@[k])@ == model@.styles[sel_start as int + k],
        decreases sel_end - i,
    {
        out.push(copy_style_set(&model.styles[i]));
        i += 1;
    }
    out
}

// ──────────────────────────────────────────────────────────────────────
// Selection geometry (exec)
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeSelectionRect {
    pub line: usize,
    pub start_col: usize,
    pub end_col: usize,
}

/// Compute selection highlight rectangles. External body because it
/// relies on text_pos_to_visual_exec and line geometry.
#[verifier::external_body]
pub fn selection_rects_exec(
    text: &Vec<char>, anchor: usize, focus: usize,
) -> (out: Vec<RuntimeSelectionRect>)
    requires
        anchor <= text.len(),
        focus <= text.len(),
{
    if anchor == focus {
        return Vec::new();
    }
    let sel_start = if anchor <= focus { anchor } else { focus };
    let sel_end = if anchor <= focus { focus } else { anchor };
    let (start_line, start_col) = text_pos_to_visual_exec(
        text, sel_start, Affinity::Downstream);
    let (end_line, end_col) = text_pos_to_visual_exec(
        text, sel_end, Affinity::Upstream);

    let mut rects: Vec<RuntimeSelectionRect> = Vec::new();
    if start_line == end_line {
        rects.push(RuntimeSelectionRect {
            line: start_line, start_col, end_col,
        });
    } else {
        // First line: partial
        rects.push(RuntimeSelectionRect {
            line: start_line, start_col, end_col: usize::MAX,
        });
        // Middle lines: full
        let mut line = start_line + 1;
        while line < end_line {
            rects.push(RuntimeSelectionRect {
                line, start_col: 0, end_col: usize::MAX,
            });
            line += 1;
        }
        // Last line: partial
        rects.push(RuntimeSelectionRect {
            line: end_line, start_col: 0, end_col,
        });
    }
    rects
}

// ──────────────────────────────────────────────────────────────────────
// Viewport (exec)
// ──────────────────────────────────────────────────────────────────────

pub struct RuntimeTextViewport {
    pub scroll_line: usize,
    pub visible_lines: usize,
}

impl View for RuntimeTextViewport {
    type V = TextViewport;
    open spec fn view(&self) -> TextViewport {
        TextViewport {
            scroll_line: self.scroll_line as nat,
            visible_lines: self.visible_lines as nat,
        }
    }
}

pub fn cursor_visible_exec(
    vp: &RuntimeTextViewport, cursor_line: usize,
) -> (result: bool)
    requires
        vp.scroll_line as u64 + vp.visible_lines as u64 <= usize::MAX as u64,
    ensures result == cursor_visible(vp@, cursor_line as nat),
{
    cursor_line >= vp.scroll_line
    && cursor_line < vp.scroll_line + vp.visible_lines
}

pub fn scroll_to_cursor_exec(
    vp: RuntimeTextViewport, cursor_line: usize,
) -> (result: RuntimeTextViewport)
    requires
        cursor_line < usize::MAX,
        vp.scroll_line as u64 + vp.visible_lines as u64 <= usize::MAX as u64,
    ensures result@ == scroll_to_cursor(vp@, cursor_line as nat),
{
    if vp.visible_lines == 0 {
        vp
    } else if cursor_line < vp.scroll_line {
        RuntimeTextViewport { scroll_line: cursor_line, ..vp }
    } else if cursor_line >= vp.scroll_line + vp.visible_lines {
        RuntimeTextViewport {
            scroll_line: cursor_line - vp.visible_lines + 1,
            ..vp
        }
    } else {
        vp
    }
}

pub fn scroll_by_exec(
    vp: RuntimeTextViewport, delta: isize, total_lines: usize,
) -> (result: RuntimeTextViewport)
    requires
        total_lines < usize::MAX,
    ensures result@ == scroll_by(vp@, delta as int, total_lines as nat),
{
    if total_lines == 0 {
        RuntimeTextViewport { scroll_line: 0, ..vp }
    } else if delta == 0 {
        if vp.scroll_line >= total_lines {
            RuntimeTextViewport { scroll_line: total_lines - 1, ..vp }
        } else {
            vp
        }
    } else if delta > 0 {
        let d: usize = delta as usize;
        if vp.scroll_line >= total_lines {
            RuntimeTextViewport { scroll_line: total_lines - 1, ..vp }
        } else if d > total_lines - 1 - vp.scroll_line {
            RuntimeTextViewport { scroll_line: total_lines - 1, ..vp }
        } else {
            RuntimeTextViewport { scroll_line: vp.scroll_line + d, ..vp }
        }
    } else {
        // delta < 0, so delta != isize::MIN is possible but -delta fits in usize
        // because isize::MIN as int == -(isize::MAX as int + 1) and
        // -(isize::MIN as int) == isize::MAX + 1 <= usize::MAX
        let abs_d: usize = if delta == isize::MIN {
            // -isize::MIN would overflow isize, but isize::MIN as usize
            // wraps to the correct absolute value on two's complement
            (isize::MAX as usize) + 1
        } else {
            (-delta) as usize
        };
        proof {
            if delta == isize::MIN {
                assert(abs_d as int == (isize::MAX as int) + 1);
                assert(delta as int == -(isize::MAX as int + 1));
                assert(abs_d as int == -(delta as int));
            }
        }
        if abs_d > vp.scroll_line {
            RuntimeTextViewport { scroll_line: 0, ..vp }
        } else {
            let ns_val: usize = vp.scroll_line - abs_d;
            if ns_val >= total_lines {
                RuntimeTextViewport { scroll_line: total_lines - 1, ..vp }
            } else {
                RuntimeTextViewport { scroll_line: ns_val, ..vp }
            }
        }
    }
}

// ──────────────────────────────────────────────────────────────────────
// Soft word wrap (exec)
// ──────────────────────────────────────────────────────────────────────

/// Compute soft wrap break positions. External body — uses runtime
/// character width and greedy break algorithm.
#[verifier::external_body]
pub fn compute_wrap_breaks_exec(
    text: &Vec<char>, line_width: usize,
) -> (out: Vec<usize>)
{
    if line_width == 0 || text.len() == 0 {
        return Vec::new();
    }
    let mut breaks: Vec<usize> = Vec::new();
    let mut pos: usize = 0;
    while pos < text.len() {
        // Find end of current hard line
        let mut hard_end = pos;
        while hard_end < text.len() && text[hard_end] != '\n' {
            hard_end += 1;
        }
        // Wrap this hard line
        let mut line_start = pos;
        while line_start < hard_end {
            let segment_end = (line_start + line_width).min(hard_end);
            if segment_end >= hard_end {
                break;
            }
            // Find last break opportunity
            let mut bp = segment_end;
            while bp > line_start {
                let c = text[bp - 1];
                if c == ' ' || c == '\t' || c == '-' {
                    break;
                }
                bp -= 1;
            }
            let actual_break = if bp > line_start { bp } else { segment_end };
            breaks.push(actual_break);
            line_start = actual_break;
        }
        // Skip past '\n'
        pos = if hard_end < text.len() { hard_end + 1 } else { hard_end };
    }
    breaks
}

/// Count wrapped visual lines. External body.
#[verifier::external_body]
pub fn wrapped_line_count_exec(
    text: &Vec<char>, line_width: usize,
) -> (out: usize)
{
    if line_width == 0 || text.len() == 0 {
        return 1;
    }
    let breaks = compute_wrap_breaks_exec(text, line_width);
    // Each hard line produces (soft_breaks_in_line + 1) visual lines.
    // Total = breaks.len() + paragraph_count
    let mut newline_count: usize = 0;
    let mut i: usize = 0;
    while i < text.len() {
        if text[i] == '\n' {
            newline_count += 1;
        }
        i += 1;
    }
    breaks.len() + newline_count + 1
}

/// Map text position to visual (line, col) with soft wrap. External body.
#[verifier::external_body]
pub fn wrapped_pos_to_visual_exec(
    text: &Vec<char>, pos: usize, line_width: usize,
) -> (out: (usize, usize))
    ensures
        out.0 as nat == wrapped_pos_to_visual(text@, pos as nat, line_width as nat).0,
        out.1 as nat == wrapped_pos_to_visual(text@, pos as nat, line_width as nat).1,
        out.0 <= text.len(),
{
    if text.len() == 0 || line_width == 0 {
        return (0, pos);
    }
    let breaks = compute_wrap_breaks_exec(text, line_width);
    let mut visual_line: usize = 0;
    let mut line_start: usize = 0;
    // Walk through hard lines and soft breaks
    let mut p: usize = 0;
    let mut bi: usize = 0;  // index into breaks
    while p < text.len() {
        // Find end of current hard line
        let mut hard_end = p;
        while hard_end < text.len() && text[hard_end] != '\n' {
            hard_end += 1;
        }
        // Walk soft breaks within this hard line
        let mut seg_start = p;
        while bi < breaks.len() && breaks[bi] <= hard_end {
            if pos >= seg_start && pos < breaks[bi] {
                return (visual_line, pos - seg_start);
            }
            seg_start = breaks[bi];
            bi += 1;
            visual_line += 1;
        }
        // Check if pos is in last segment of this hard line
        if pos >= seg_start && pos <= hard_end {
            return (visual_line, pos - seg_start);
        }
        visual_line += 1;
        p = if hard_end < text.len() { hard_end + 1 } else { hard_end };
    }
    (visual_line, 0)
}

/// Map visual (line, col) to text position with soft wrap. External body.
#[verifier::external_body]
pub fn wrapped_visual_to_pos_exec(
    text: &Vec<char>, line: usize, col: usize, line_width: usize,
) -> (out: usize)
    ensures out as nat == wrapped_visual_to_pos(text@, line as nat, col as nat, line_width as nat),
{
    if text.len() == 0 || line_width == 0 {
        return col.min(text.len());
    }
    let breaks = compute_wrap_breaks_exec(text, line_width);
    let mut visual_line: usize = 0;
    let mut p: usize = 0;
    let mut bi: usize = 0;
    while p < text.len() {
        let mut hard_end = p;
        while hard_end < text.len() && text[hard_end] != '\n' {
            hard_end += 1;
        }
        let mut seg_start = p;
        while bi < breaks.len() && breaks[bi] <= hard_end {
            if visual_line == line {
                return (seg_start + col).min(breaks[bi]);
            }
            seg_start = breaks[bi];
            bi += 1;
            visual_line += 1;
        }
        if visual_line == line {
            return (seg_start + col).min(hard_end);
        }
        visual_line += 1;
        p = if hard_end < text.len() { hard_end + 1 } else { hard_end };
    }
    // Target line beyond content
    text.len()
}

// ── Unicode boundary exec bridges ────────────────────────────────

/// Compute grapheme cluster boundaries using unicode-segmentation.
/// Bridges the uninterpreted spec fn to runtime.
#[verifier::external_body]
pub fn grapheme_boundaries_exec(text: &Vec<char>) -> (out: Vec<usize>)
    requires text@.len() > 0,
    ensures
        out@.len() == grapheme_boundaries(text@).len(),
        forall|i: int| 0 <= i < out@.len() ==>
            out@[i] as nat == (#[trigger] grapheme_boundaries(text@))[i],
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let mut bounds: Vec<usize> = Vec::new();
    bounds.push(0);
    let mut offset: usize = 0;
    for grapheme in s.graphemes(true) {
        offset += grapheme.chars().count();
        bounds.push(offset);
    }
    bounds
}

/// Compute word start boundaries using unicode-segmentation.
#[verifier::external_body]
pub fn word_start_boundaries_exec(text: &Vec<char>) -> (out: Vec<usize>)
    requires text@.len() > 0,
    ensures
        out@.len() == word_start_boundaries(text@).len(),
        forall|i: int| 0 <= i < out@.len() ==>
            out@[i] as nat == (#[trigger] word_start_boundaries(text@))[i],
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let mut bounds: Vec<usize> = Vec::new();
    bounds.push(0);
    let mut offset: usize = 0;
    for word in s.split_word_bounds() {
        if offset > 0 {
            bounds.push(offset);
        }
        offset += word.chars().count();
    }
    if bounds.last() != Some(&text.len()) {
        bounds.push(text.len());
    }
    bounds
}

/// Compute word end boundaries using unicode-segmentation.
#[verifier::external_body]
pub fn word_end_boundaries_exec(text: &Vec<char>) -> (out: Vec<usize>)
    requires text@.len() > 0,
    ensures
        out@.len() == word_end_boundaries(text@).len(),
        forall|i: int| 0 <= i < out@.len() ==>
            out@[i] as nat == (#[trigger] word_end_boundaries(text@))[i],
{
    use unicode_segmentation::UnicodeSegmentation;
    let s: String = text.iter().collect();
    let mut bounds: Vec<usize> = Vec::new();
    bounds.push(0);
    let mut offset: usize = 0;
    for word in s.split_word_bounds() {
        offset += word.chars().count();
        bounds.push(offset);
    }
    bounds
}

/// Compute line break opportunities.
#[verifier::external_body]
pub fn line_break_opportunities_exec(text: &Vec<char>) -> (out: Vec<usize>)
    requires text@.len() > 0,
    ensures
        out@.len() == line_break_opportunities(text@).len(),
        forall|i: int| 0 <= i < out@.len() ==>
            out@[i] as nat == (#[trigger] line_break_opportunities(text@))[i],
{
    // Line breaks occur at '\n' characters
    let s: String = text.iter().collect();
    let mut bounds: Vec<usize> = Vec::new();
    bounds.push(0);
    let mut char_offset: usize = 0;
    for ch in s.chars() {
        char_offset += 1;
        if ch == '\n' {
            bounds.push(char_offset);
        }
    }
    if bounds.last() != Some(&text.len()) {
        bounds.push(text.len());
    }
    bounds
}

} // verus!
