use vstd::prelude::*;
use crate::text_model::*;
use crate::text_model::operations::*;
use crate::text_model::cursor::*;
use crate::text_model::proofs::*;
use crate::text_model::paragraph_proofs::*;
use crate::text_model::undo::*;

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
{ unimplemented!() }

#[verifier::external_body]
pub fn next_grapheme_boundary_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == next_grapheme_boundary(text@, pos as nat),
{ unimplemented!() }

#[verifier::external_body]
pub fn prev_word_start_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == prev_boundary_in(word_start_boundaries(text@), pos as nat),
{ unimplemented!() }

#[verifier::external_body]
pub fn next_word_end_exec(text: &Vec<char>, pos: usize) -> (result: usize)
    requires text@.len() > 0,
    ensures result as nat == next_boundary_in(word_end_boundaries(text@), pos as nat),
{ unimplemented!() }

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

} // verus!
