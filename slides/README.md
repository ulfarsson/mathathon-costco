# Slides: Polynomial removal for binary matrices

Beamer slides for the team's write-up (team costco, Problem #96 at the Caltech × SAIR Mathathon,
November 15, 2026): the polynomial removal conjecture for ordered binary matrices, OpenAI's
counterexample and why it works, and the team's two reductions (direct sums, duplication). 26
frames, with step-by-step overlays.

If you are an agent editing these slides, read this file first, then `slides-template.tex`.

## Files

| File | What it is |
|---|---|
| `slides-template.tex` | **The source of the slides.** All text lives here. Markers like `%%HOSTVIEW%%` stand for pictures and numbers that the script computes. Edit this file. |
| `make_slides.py` | Fills the markers and writes `slides-2026-11-15T0054Z.tex`. Every example matrix, highlighted copy and count is computed, and checked, before it is drawn (copies by brute force; the hosts from `construction.py`). |
| `construction.py` | OpenAI's 66 × 66 pattern H and its host matrices A_h, rebuilt from Section 2 of OpenAI's preprint. A copy of the project's `code/construction.py`; do not edit it here. |
| `check_slide_jumps.py` | Checks a compiled PDF for frames that jump between overlay steps. |
| `slides-2026-11-15T0054Z.tex` | The generated slides: one self-contained file (all pictures are TikZ inside it). **Do not edit;** the script overwrites it. |
| `slides-2026-11-15T0054Z.pdf` | The compiled slides. |

The file names carry the date of the write-up version the slides were made from
(`writeup-2026-11-15T0054Z.tex`, in the folder above). To write the slides elsewhere, pass a file
name: `python3 make_slides.py my-slides.tex`.

## Requirements

- Python 3, standard library only.
- pdflatex (TeX Live) with beamer, tgheros, booktabs, amsmath and TikZ.
- `pdftotext` from poppler-utils, for `check_slide_jumps.py`.

## Build

```bash
python3 make_slides.py                                   # writes slides-2026-11-15T0054Z.tex
pdflatex slides-2026-11-15T0054Z.tex                     # twice: the title page needs
pdflatex slides-2026-11-15T0054Z.tex                     # a second pass
python3 check_slide_jumps.py slides-2026-11-15T0054Z.pdf # must print OK
```

Then look at the frames you changed, every overlay step of them.

**Overleaf** needs only the generated `.tex` (compiler: pdfLaTeX). Overleaf cannot run the script,
so changes made there must be carried back into `slides-template.tex` by hand, or the next run of
`make_slides.py` loses them.

## Rules for editing

1. **Edit the template, never the generated file.**
2. **Never type a matrix, a highlighted copy or a count by hand.** If a slide needs a new picture
   or number, write a function in `make_slides.py` that computes it, asserts what the slide will
   claim about it, and returns TikZ; then add a marker to the template and fill it in `main()`.
   If an assertion fails, the slide's claim is wrong: fix the claim, not the assertion.
3. **No jumps between overlay steps.** Frames are top-aligned (class option `t`; only the title
   page is centered).
   - Text that changes from step to step goes in an `overprint` area, one
     `\onslide<k>` with `\raggedright` per step; plain `\only` swaps of text make the frame jump.
   - A picture must keep the same bounding box on every step (`\useasboundingbox`); `\only` inside
     a picture is fine when the box stays the same.
   - Run `check_slide_jumps.py` after every change. It compares the positions of words between
     consecutive steps. It skips one-character words such as matrix entries, so check pictures by
     eye.
4. **TikZ grids:** draw grid lines explicitly. `\draw ... grid ...` spaces its lines 1 cm apart
   whatever the picture's unit is, so they miss the cells.
5. **Define every symbol before it is used on a slide** (a δ, a τ, an m), and name objects
   exactly ("leaf cell", "leaf row", not "leaf").
6. **Wording:** always "OpenAI's preprint", never "the preprint" on its own. American spelling.
   Result numbers as in the PDF of OpenAI's preprint.
7. **No overfull boxes:** check the log (`grep Overfull`); shorten text or use `\small` rather than
   letting a frame run into the footer.

## Facts the slides rely on

- OpenAI, "Polynomial removal fails for ordered binary matrices", preprint, 25 September 2026,
  <https://github.com/openai/math/tree/main/preprints/Polynomial-removal-fails-for-ordered-binary-matrices-September-25-2026>.
  - A 66 × 66 pattern H = [S e1 e2; e1ᵀ 1 0; e2ᵀ 1 1] with a 64 × 64 anchor S and body
    P = [1 0; 1 1]; hosts A_h with m = 2^h and n = (386h + 2)m.
  - Proposition 3.1: every repair of A_h changes at least m² = εn² entries, ε = (386h + 2)^(−2).
  - Lemmas 4.1–4.4 and Corollary 4.5: every copy of S sits in one mode's anchor, one position per
    group; Lemma 4.3: the tree and dummy rows show at most 27 of the 32 five-bit words on any five
    columns.
  - Proposition 4.6: every copy of H passes through one of the m leaf cells; A_h has at most
    ε·2^(−h)·n^132 copies. Remark 4.7: changing the leaf cells creates new copies.
- Checked by the project, by computer: setting the dummy rows against the leaf columns to 0 (m²
  changes) leaves no copy of H for h ≤ 5, so m² is the exact distance there; A_h has exactly
  2m^130 copies (h ≤ 5).
- History (all dates 2026 unless stated): Alon, Fischer and Newman, SIAM J. Comput. 2007;
  Alon, Ben-Eliezer and Fischer, FOCS 2017 (removal for ordered matrices; their proof gives a
  wowzer-type 1/δ); Alon and Ben-Eliezer, Order 2020 (Problem 1.4; Theorem 1.2 on disjoint
  copies); Gishboliner and Shapira, survey, Comput. Sci. Rev. 2025 (Conjecture 4.5, "one of the
  key open problems"); ProveIt project, 5 × 5 draft, 7 October; Erebos Labs, a 4 × 4 with a Lean
  proof, 9 October; Wang, the same 4 × 4 on arXiv (2610.15370), 11 October; Shea, a claimed
  3 × 3, manuscript of 12 October, **unrefereed**; Lupini, Zenodo, 2 November: the 2 × 2 identity
  I_2 has polynomial removal.
- The team's results are in the write-up. The direct-sum theorem, its zero-column variant, their
  corollaries and the family obtained by adding (1) repeatedly are proved in Lean (Mathlib
  v4.35.0, no `sorry`, only the standard axioms), and the one-zero-column case in Agda. The
  duplication theorem's proof in the write-up was read and found sound by the agent that made the
  slides (2026-11-15); no one else has reviewed it. Its two directions get a frame each: Fact 1
  (two completions of a frame make a copy of the doubled pattern; Jensen) and Fact 2 (the blow-up
  A^(q): few copies stay few, and far stays far, D_H(A^(q)) >= q^2 D_R(A)/2 for large q).
- Open: whether the 2 × 2 corner P = [1 0; 1 1] has polynomial removal.

## Style

The title page follows the title block of the team's report: the title, the subtitle "Problem #96
at the Caltech × SAIR Mathathon", the team, the authors with their affiliations, and the date (shown
above the title).

Taken from the team's earlier slides (their style only): TeX Gyre Heros; paper `#FBF8F4`, ink
`#2B0B1E`, orange accent `#F26322`, muted gray `#79646E`; bold frame titles with a one-line
takeaway as `\framesubtitle` and an orange rule beneath; a footer with the event name (macro
`\eventline` at the top of the template) and the frame number.

## `construction.py`, briefly

Indices are 0-based. The script uses: `pattern_matrix()` (H), `anchor_matrix()` (S),
`TreeMatrix(h)` (A_h) with `.modes`, `.row_blocks`, `.column_blocks`, `.positions(axis)`,
`.entry(row_block, column_block)`, `.designated_role(block, mode, axis)`, `.full_matrix_rows()`,
`.block_size(block)`, and `Block`. Inside the project repository, `make_slides.py` stops if this
copy differs from the project's `code/construction.py`; outside it, the copy here is used.
