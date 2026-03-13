use vstd::prelude::*;
use super::*;

verus! {

// ──────────────────────────────────────────────────────────────────────
// Style merging
// ──────────────────────────────────────────────────────────────────────

/// Merge `overlay` on top of `base`: overlay fields take precedence when `Some`.
pub open spec fn merge_style(base: StyleSet, overlay: StyleSet) -> StyleSet {
    StyleSet {
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
// Paragraph style adjustment
// ──────────────────────────────────────────────────────────────────────

/// Default paragraph style.
pub open spec fn default_paragraph_style() -> ParagraphStyle {
    ParagraphStyle {
        alignment: ParagraphAlignment::Left,
        indent_left: 0,
        indent_right: 0,
        indent_first_line: 0,
        line_spacing: 0,
        space_before: 0,
        space_after: 0,
    }
}

/// Adjust paragraph_styles after a text splice.
/// Removed paragraphs lose their styles; inserted paragraphs get `default_paragraph_style()`.
pub open spec fn adjust_paragraph_styles(
    old_styles: Seq<ParagraphStyle>,
    old_text: Seq<char>,
    start: nat,
    end: nat,
    new_text: Seq<char>,
) -> Seq<ParagraphStyle> {
    let removed_newlines = count_char(old_text.subrange(start as int, end as int), '\n');
    let inserted_newlines = count_char(new_text, '\n');
    // The paragraph containing `start` keeps its style.
    // We remove styles for paragraphs whose newlines were deleted,
    // and insert default styles for new paragraphs.
    let para_of_start = count_char(old_text.subrange(0, start as int), '\n');
    // Keep styles [0..para_of_start] and [para_of_start + 1 + removed_newlines..]
    let before = old_styles.subrange(0, (para_of_start + 1) as int);
    let after_idx = (para_of_start + 1 + removed_newlines) as int;
    let after = if after_idx <= old_styles.len() as int {
        old_styles.subrange(after_idx, old_styles.len() as int)
    } else {
        Seq::empty()
    };
    let new_para_styles = seq_repeat(default_paragraph_style(), inserted_newlines);
    before + new_para_styles + after
}

// ──────────────────────────────────────────────────────────────────────
// Typing style resolution
// ──────────────────────────────────────────────────────────────────────

/// Resolve typing style after cursor movement or deletion.
/// If focus > 0 and text is non-empty: style of character before focus.
/// If focus == 0 and text is non-empty: style of first character.
/// If text is empty: default_style.
pub open spec fn resolve_typing_style(
    text: Seq<char>,
    styles: Seq<StyleSet>,
    focus: nat,
    default_style: StyleSet,
) -> StyleSet {
    if text.len() == 0 {
        default_style
    } else if focus > 0 {
        styles[focus as int - 1]
    } else {
        styles[0]
    }
}

// ──────────────────────────────────────────────────────────────────────
// Core splice
// ──────────────────────────────────────────────────────────────────────

/// Central text mutation: replace `text[start..end)` with `new_text`/`new_styles`,
/// place cursor at `new_focus`, clear composition and preferred_column.
pub open spec fn splice(
    model: TextModel,
    start: nat,
    end: nat,
    new_text: Seq<char>,
    new_styles: Seq<StyleSet>,
    new_focus: nat,
) -> TextModel {
    let text_prime = seq_splice(model.text, start as int, end as int, new_text);
    let styles_prime = seq_splice(model.styles, start as int, end as int, new_styles);
    // Preserve paragraph styles for unmodified paragraphs; new paragraphs get defaults.
    let para_styles_prime = adjust_paragraph_styles(
        model.paragraph_styles, model.text, start, end, new_text);
    let typing_style_prime = if new_text.len() > 0 {
        // After insert: keep current typing_style
        model.typing_style
    } else {
        // After delete: resolve from surrounding context
        resolve_typing_style(text_prime, styles_prime, new_focus, model.default_style)
    };
    TextModel {
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
    }
}

// ──────────────────────────────────────────────────────────────────────
// Text editing operations
// ──────────────────────────────────────────────────────────────────────

/// Insert a single character, replacing any selection.
pub open spec fn insert_char(model: TextModel, ch: char) -> TextModel {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    splice(
        model,
        sel_start, sel_end,
        seq![ch],
        seq![model.typing_style],
        sel_start + 1,
    )
}

/// Insert a sequence of characters with corresponding styles, replacing any selection.
pub open spec fn insert_seq(
    model: TextModel,
    s: Seq<char>,
    st: Seq<StyleSet>,
) -> TextModel {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    splice(
        model,
        sel_start, sel_end,
        s, st,
        sel_start + s.len(),
    )
}

/// Delete the current selection (no-op if no selection).
pub open spec fn delete_selection(model: TextModel) -> TextModel {
    if !has_selection(model.anchor, model.focus) {
        model
    } else {
        let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
        splice(model, sel_start, sel_end, Seq::empty(), Seq::empty(), sel_start)
    }
}

/// Delete backward: delete selection if any, else delete one grapheme before focus.
pub open spec fn delete_backward(model: TextModel) -> TextModel {
    if has_selection(model.anchor, model.focus) {
        delete_selection(model)
    } else if model.focus == 0 {
        model
    } else {
        let prev = prev_grapheme_boundary(model.text, model.focus);
        splice(model, prev, model.focus, Seq::empty(), Seq::empty(), prev)
    }
}

/// Delete forward: delete selection if any, else delete one grapheme after focus.
pub open spec fn delete_forward(model: TextModel) -> TextModel {
    if has_selection(model.anchor, model.focus) {
        delete_selection(model)
    } else if model.focus >= model.text.len() {
        model
    } else {
        let next = next_grapheme_boundary(model.text, model.focus);
        splice(model, model.focus, next, Seq::empty(), Seq::empty(), model.focus)
    }
}

/// Delete backward by word: delete selection if any, else delete from previous word start to focus.
pub open spec fn delete_word_backward(model: TextModel) -> TextModel {
    if has_selection(model.anchor, model.focus) {
        delete_selection(model)
    } else if model.focus == 0 {
        model
    } else {
        let prev = prev_boundary_in(word_start_boundaries(model.text), model.focus);
        splice(model, prev, model.focus, Seq::empty(), Seq::empty(), prev)
    }
}

/// Delete forward by word: delete selection if any, else delete from focus to next word end.
pub open spec fn delete_word_forward(model: TextModel) -> TextModel {
    if has_selection(model.anchor, model.focus) {
        delete_selection(model)
    } else if model.focus >= model.text.len() {
        model
    } else {
        let next = next_boundary_in(word_end_boundaries(model.text), model.focus);
        splice(model, model.focus, next, Seq::empty(), Seq::empty(), model.focus)
    }
}

// ──────────────────────────────────────────────────────────────────────
// Paste (with sanitization)
// ──────────────────────────────────────────────────────────────────────

/// Filter a character sequence to only permitted characters.
pub open spec fn filter_permitted(s: Seq<char>) -> Seq<char>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let rest = filter_permitted(s.drop_last());
        if is_permitted(s.last()) {
            rest.push(s.last())
        } else {
            rest
        }
    }
}

/// Canonicalize line endings: replace '\r\n' with '\n' and bare '\r' with '\n'.
pub open spec fn canonicalize_newlines(s: Seq<char>) -> Seq<char>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else if s.last() == '\n' && s.len() >= 2 && s[s.len() - 2] == '\r' {
        // \r\n → \n
        canonicalize_newlines(s.subrange(0, s.len() as int - 2)).push('\n')
    } else if s.last() == '\r' {
        // bare \r → \n
        canonicalize_newlines(s.drop_last()).push('\n')
    } else {
        canonicalize_newlines(s.drop_last()).push(s.last())
    }
}

/// Paste text, sanitizing and applying the given styles.
/// Styles sequence must match input text length (pre-sanitization);
/// styles corresponding to filtered-out characters are dropped.
pub open spec fn paste(model: TextModel, text: Seq<char>, styles: Seq<StyleSet>) -> TextModel {
    let clean = canonicalize_newlines(filter_permitted(text));
    let clean_styles = seq_repeat(model.typing_style, clean.len());
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    splice(model, sel_start, sel_end, clean, clean_styles, sel_start + clean.len())
}

// ──────────────────────────────────────────────────────────────────────
// Formatting operations
// ──────────────────────────────────────────────────────────────────────

/// Apply a style overlay to a range of characters.
pub open spec fn apply_style_to_range(
    model: TextModel,
    start: nat,
    end: nat,
    style: StyleSet,
) -> TextModel {
    let new_styles = Seq::new(
        model.styles.len(),
        |i: int| {
            if start as int <= i && i < end as int {
                merge_style(model.styles[i], style)
            } else {
                model.styles[i]
            }
        },
    );
    TextModel {
        styles: new_styles,
        ..model
    }
}

/// Toggle bold in the typing style.
pub open spec fn toggle_bold(model: TextModel) -> TextModel {
    let current = match model.typing_style.bold {
        Some(b) => b,
        None => false,
    };
    TextModel {
        typing_style: StyleSet {
            bold: Some(!current),
            ..model.typing_style
        },
        ..model
    }
}

/// Toggle italic in the typing style.
pub open spec fn toggle_italic(model: TextModel) -> TextModel {
    let current = match model.typing_style.italic {
        Some(b) => b,
        None => false,
    };
    TextModel {
        typing_style: StyleSet {
            italic: Some(!current),
            ..model.typing_style
        },
        ..model
    }
}

// ──────────────────────────────────────────────────────────────────────
// IME Composition
// ──────────────────────────────────────────────────────────────────────

/// Start a new composition session at the current selection.
pub open spec fn compose_start(model: TextModel) -> TextModel {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    TextModel {
        composition: Some(Composition {
            range_start: sel_start,
            range_end: sel_end,
            original: model.text.subrange(sel_start as int, sel_end as int),
            provisional: Seq::empty(),
            cursor: 0,
        }),
        ..model
    }
}

/// Update the provisional text and cursor within the active composition.
pub open spec fn compose_update(
    model: TextModel,
    provisional: Seq<char>,
    cursor: nat,
) -> TextModel {
    match model.composition {
        Some(c) => TextModel {
            composition: Some(Composition {
                provisional,
                cursor,
                ..c
            }),
            ..model
        },
        None => model,
    }
}

/// Commit the composition: replace the original range with provisional text,
/// using `typing_style` for each committed character.
pub open spec fn compose_commit(model: TextModel) -> TextModel {
    match model.composition {
        Some(c) => {
            let new_styles = seq_repeat(model.typing_style, c.provisional.len());
            splice(
                model,
                c.range_start,
                c.range_end,
                c.provisional,
                new_styles,
                c.range_start + c.provisional.len(),
            )
        },
        None => model,
    }
}

/// Cancel the composition: restore original text (no-op on text since original is still there).
pub open spec fn compose_cancel(model: TextModel) -> TextModel {
    TextModel {
        composition: None,
        ..model
    }
}

// ──────────────────────────────────────────────────────────────────────
// Selection extraction helpers
// ──────────────────────────────────────────────────────────────────────

/// Extract the text within the current selection.
pub open spec fn get_selection_text(model: TextModel) -> Seq<char> {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    model.text.subrange(sel_start as int, sel_end as int)
}

/// Extract the styles within the current selection.
pub open spec fn get_selection_styles(model: TextModel) -> Seq<StyleSet> {
    let (sel_start, sel_end) = selection_range(model.anchor, model.focus);
    model.styles.subrange(sel_start as int, sel_end as int)
}

} // verus!
