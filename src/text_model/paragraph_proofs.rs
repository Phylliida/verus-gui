use vstd::prelude::*;
use super::*;
use super::operations::*;
use super::proofs::*;

verus! {

//  ──────────────────────────────────────────────────────────────────────
//  count_char helpers
//  ──────────────────────────────────────────────────────────────────────

///  count_char of an empty sequence is 0.
pub proof fn lemma_count_char_empty(c: char)
    ensures
        count_char(Seq::<char>::empty(), c) == 0,
{
}

///  count_char after pushing a character.
pub proof fn lemma_count_char_push(text: Seq<char>, c: char, x: char)
    ensures
        count_char(text.push(x), c) == count_char(text, c) + if x == c { 1nat } else { 0nat },
{
    //  Direct from definition: text.push(x).drop_last() =~= text
    assert(text.push(x).drop_last() =~= text);
    assert(text.push(x).last() == x);
}

///  count_char of a sequence is at most the sequence length.
pub proof fn lemma_count_char_le_len(text: Seq<char>, c: char)
    ensures
        count_char(text, c) <= text.len(),
    decreases text.len(),
{
    if text.len() > 0 {
        lemma_count_char_le_len(text.drop_last(), c);
    }
}

///  Every element of seq_repeat(val, count) is val.
pub proof fn lemma_seq_repeat_index<A>(val: A, count: nat, i: int)
    requires 0 <= i < count as int,
    ensures seq_repeat(val, count)[i] == val,
    decreases count,
{
    lemma_seq_repeat_len(val, (count - 1) as nat);
    if i < count as int - 1 {
        lemma_seq_repeat_index(val, (count - 1) as nat, i);
    }
}

///  count_char of a subrange: additive decomposition.
///  count_char(text[a..c), ch) == count_char(text[a..b), ch) + count_char(text[b..c), ch)
pub proof fn lemma_count_char_subrange_additive(
    text: Seq<char>, a: int, b: int, c: int, ch: char,
)
    requires
        0 <= a <= b,
        b <= c <= text.len(),
    ensures
        count_char(text.subrange(a, c), ch)
            == count_char(text.subrange(a, b), ch)
                + count_char(text.subrange(b, c), ch),
{
    //  text[a..c) = text[a..b) + text[b..c)
    assert(text.subrange(a, c)
        =~= text.subrange(a, b) + text.subrange(b, c));
    lemma_count_char_concat(
        text.subrange(a, b), text.subrange(b, c), ch);
}

//  ──────────────────────────────────────────────────────────────────────
//  Paragraph count decomposition
//  ──────────────────────────────────────────────────────────────────────

///  Three-way decomposition of paragraph count around a splice region.
///  paragraph_count(text) decomposes into newlines before, inside, and after [start..end).
pub proof fn lemma_paragraph_count_decompose(
    text: Seq<char>, start: nat, end: nat,
)
    requires
        start <= end,
        end <= text.len(),
    ensures
        count_char(text, '\n')
            == count_char(text.subrange(0, start as int), '\n')
                + count_char(text.subrange(start as int, end as int), '\n')
                + count_char(text.subrange(end as int, text.len() as int), '\n'),
{
    //  text = text[0..start) + text[start..end) + text[end..len)
    //  First split: text = text[0..end) + text[end..len)
    assert(text =~= text.subrange(0int, end as int)
        + text.subrange(end as int, text.len() as int));
    lemma_count_char_concat(
        text.subrange(0int, end as int),
        text.subrange(end as int, text.len() as int),
        '\n',
    );

    //  Second split: text[0..end) = text[0..start) + text[start..end)
    lemma_count_char_subrange_additive(text, 0int, start as int, end as int, '\n');
}

///  Newline count after a splice.
pub proof fn lemma_splice_paragraph_count(
    old_text: Seq<char>, start: nat, end: nat, new_text: Seq<char>,
)
    requires
        start <= end,
        end <= old_text.len(),
    ensures
        count_char(seq_splice(old_text, start as int, end as int, new_text), '\n')
            == count_char(old_text.subrange(0, start as int), '\n')
                + count_char(new_text, '\n')
                + count_char(old_text.subrange(end as int, old_text.len() as int), '\n'),
{
    let result = seq_splice(old_text, start as int, end as int, new_text);
    let prefix = old_text.subrange(0, start as int);
    let suffix = old_text.subrange(end as int, old_text.len() as int);

    //  result = prefix + new_text + suffix
    assert(result =~= prefix + new_text + suffix);

    //  Split: (prefix + new_text) + suffix
    lemma_count_char_concat(prefix + new_text, suffix, '\n');
    //  Split: prefix + new_text
    lemma_count_char_concat(prefix, new_text, '\n');
}

//  ──────────────────────────────────────────────────────────────────────
//  adjust_paragraph_styles correctness
//  ──────────────────────────────────────────────────────────────────────

///  The `after_idx` used in adjust_paragraph_styles is in bounds.
pub proof fn lemma_after_idx_in_bounds(
    old_styles: Seq<ParagraphStyle>,
    old_text: Seq<char>,
    start: nat,
    end: nat,
)
    requires
        start <= end,
        end <= old_text.len(),
        old_styles.len() == paragraph_count(old_text),
    ensures
        ({
            let para_of_start = count_char(old_text.subrange(0, start as int), '\n');
            let removed_newlines = count_char(
                old_text.subrange(start as int, end as int), '\n');
            para_of_start + 1 + removed_newlines <= old_styles.len()
        }),
{
    let para_of_start = count_char(old_text.subrange(0, start as int), '\n');
    let removed_newlines = count_char(
        old_text.subrange(start as int, end as int), '\n');
    let after_newlines = count_char(
        old_text.subrange(end as int, old_text.len() as int), '\n');

    lemma_paragraph_count_decompose(old_text, start, end);
    //  count_char(old_text, '\n') == para_of_start + removed_newlines + after_newlines
    //  old_styles.len() == paragraph_count(old_text) == count_char(old_text, '\n') + 1
    //  So: para_of_start + 1 + removed_newlines
    //      = para_of_start + removed_newlines + 1
    //      <= para_of_start + removed_newlines + after_newlines + 1
    //      = count_char(old_text, '\n') + 1
    //      = old_styles.len()
}

///  Central theorem: adjust_paragraph_styles produces the correct length.
pub proof fn lemma_adjust_paragraph_styles_len(
    old_styles: Seq<ParagraphStyle>,
    old_text: Seq<char>,
    start: nat,
    end: nat,
    new_text: Seq<char>,
)
    requires
        start <= end,
        end <= old_text.len(),
        old_styles.len() == paragraph_count(old_text),
    ensures
        adjust_paragraph_styles(old_styles, old_text, start, end, new_text).len()
            == paragraph_count(
                seq_splice(old_text, start as int, end as int, new_text)),
{
    let removed_newlines = count_char(
        old_text.subrange(start as int, end as int), '\n');
    let inserted_newlines = count_char(new_text, '\n');
    let para_of_start = count_char(old_text.subrange(0, start as int), '\n');
    let after_newlines = count_char(
        old_text.subrange(end as int, old_text.len() as int), '\n');

    //  Three-way decomposition of old text
    lemma_paragraph_count_decompose(old_text, start, end);
    //  old_text newlines = para_of_start + removed_newlines + after_newlines
    //  paragraph_count(old_text) = para_of_start + removed_newlines + after_newlines + 1

    //  after_idx bound
    lemma_after_idx_in_bounds(old_styles, old_text, start, end);
    let after_idx = (para_of_start + 1 + removed_newlines) as int;

    //  Components of the result
    let before = old_styles.subrange(0, (para_of_start + 1) as int);
    let after = if after_idx <= old_styles.len() as int {
        old_styles.subrange(after_idx, old_styles.len() as int)
    } else {
        Seq::empty()
    };
    let new_para_styles = seq_repeat(default_paragraph_style(), inserted_newlines);
    lemma_seq_repeat_len(default_paragraph_style(), inserted_newlines);

    //  before.len() = para_of_start + 1
    assert(before.len() == para_of_start + 1);
    //  new_para_styles.len() = inserted_newlines
    assert(new_para_styles.len() == inserted_newlines);
    //  after.len() = old_styles.len() - after_idx = after_newlines
    assert(after_idx <= old_styles.len() as int);
    assert(after.len() == old_styles.len() - after_idx);
    assert(old_styles.len() as int == (para_of_start + removed_newlines + after_newlines + 1) as int);
    assert(after.len() == after_newlines);

    //  Result length
    let result = before + new_para_styles + after;
    assert((before + new_para_styles).len()
        == before.len() + new_para_styles.len());
    assert(result.len()
        == before.len() + new_para_styles.len() + after.len());
    assert(result.len()
        == (para_of_start + 1) + inserted_newlines + after_newlines);

    //  Target: paragraph_count of spliced text
    lemma_splice_paragraph_count(old_text, start, end, new_text);
    //  count_char(spliced, '\n') = para_of_start + inserted_newlines + after_newlines
    //  paragraph_count(spliced) = para_of_start + inserted_newlines + after_newlines + 1
    assert(paragraph_count(
        seq_splice(old_text, start as int, end as int, new_text))
            == para_of_start + inserted_newlines + after_newlines + 1);

    //  QED: result.len() == paragraph_count(spliced)
}

///  Paragraphs before the splice region keep their styles.
pub proof fn lemma_adjust_preserves_before(
    old_styles: Seq<ParagraphStyle>,
    old_text: Seq<char>,
    start: nat,
    end: nat,
    new_text: Seq<char>,
)
    requires
        start <= end,
        end <= old_text.len(),
        old_styles.len() == paragraph_count(old_text),
    ensures
        ({
            let result = adjust_paragraph_styles(
                old_styles, old_text, start, end, new_text);
            let para_of_start = count_char(
                old_text.subrange(0, start as int), '\n');
            forall|i: int| 0 <= i <= para_of_start
                ==> result[i] == old_styles[i]
        }),
{
    let para_of_start = count_char(
        old_text.subrange(0, start as int), '\n');
    let result = adjust_paragraph_styles(
        old_styles, old_text, start, end, new_text);

    //  result starts with old_styles[0..para_of_start+1)
    let before = old_styles.subrange(0, (para_of_start + 1) as int);

    lemma_after_idx_in_bounds(old_styles, old_text, start, end);
    lemma_paragraph_count_decompose(old_text, start, end);

    assert forall|i: int| 0 <= i <= para_of_start
        implies result[i] == old_styles[i]
    by {
        //  result = before + new_para_styles + after
        //  For i < before.len() = para_of_start + 1:
        //  (before + x)[i] = before[i] = old_styles[i]
        assert(before[i] == old_styles[i]);
    }
}

///  Paragraphs after the splice region keep their styles.
pub proof fn lemma_adjust_preserves_after(
    old_styles: Seq<ParagraphStyle>,
    old_text: Seq<char>,
    start: nat,
    end: nat,
    new_text: Seq<char>,
)
    requires
        start <= end,
        end <= old_text.len(),
        old_styles.len() == paragraph_count(old_text),
    ensures
        ({
            let result = adjust_paragraph_styles(
                old_styles, old_text, start, end, new_text);
            let para_of_start = count_char(
                old_text.subrange(0, start as int), '\n');
            let removed_newlines = count_char(
                old_text.subrange(start as int, end as int), '\n');
            let inserted_newlines = count_char(new_text, '\n');
            let after_newlines = count_char(
                old_text.subrange(end as int, old_text.len() as int), '\n');
            let result_offset = (para_of_start + 1 + inserted_newlines) as int;
            let old_offset = (para_of_start + 1 + removed_newlines) as int;
            forall|k: int| 0 <= k < after_newlines ==>
                #[trigger] result[result_offset + k]
                    == old_styles[old_offset + k]
        }),
{
    let para_of_start = count_char(
        old_text.subrange(0, start as int), '\n');
    let removed_newlines = count_char(
        old_text.subrange(start as int, end as int), '\n');
    let inserted_newlines = count_char(new_text, '\n');
    let after_newlines = count_char(
        old_text.subrange(end as int, old_text.len() as int), '\n');

    lemma_paragraph_count_decompose(old_text, start, end);
    lemma_after_idx_in_bounds(old_styles, old_text, start, end);
    lemma_seq_repeat_len(default_paragraph_style(), inserted_newlines);

    let before = old_styles.subrange(0, (para_of_start + 1) as int);
    let after_idx = (para_of_start + 1 + removed_newlines) as int;
    let after = old_styles.subrange(after_idx, old_styles.len() as int);
    let new_para_styles = seq_repeat(
        default_paragraph_style(), inserted_newlines);

    let result = before + new_para_styles + after;
    let result_offset = (para_of_start + 1 + inserted_newlines) as int;

    assert forall|k: int| 0 <= k < after_newlines
        implies #[trigger] result[result_offset + k]
            == old_styles[after_idx + k]
    by {
        //  result_offset + k = before.len() + new_para_styles.len() + k
        //  In the concatenation, this falls in the 'after' part
        assert(before.len() == para_of_start + 1);
        assert(new_para_styles.len() == inserted_newlines);
        assert(result_offset + k
            == (before.len() + new_para_styles.len() + k) as int);
        //  after[k] = old_styles[after_idx + k]
        assert(after[k] == old_styles[after_idx + k]);
    }
}

} //  verus!
