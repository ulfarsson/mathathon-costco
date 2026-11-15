"""Build the slides from slides-template.tex.

Every matrix, copy and count on the slides that is not plain text is computed here and checked
before it is drawn:
- the motivation frame's random 12 x 12 matrix (seed 1) and a sample of 2 rows and 2 columns that
  reads H = [1 0; 1 1], with the number of such samples (261 of 4356);
- the small examples (H = [1 0; 1 1] in a 3 x 3 matrix A): copies found by brute force, D_H by
  brute force over all 3 x 3 matrices;
- OpenAI's 66 x 66 pattern H, drawn from construction.py;
- all of A_1 with one copy of H: the mode's block, its marks, the 2 x 2 body (it must read P), the
  66 rows and columns (they must read H in the full host), and all 8 bodies;
- the tree and dummy part of A_1 under three edits (one leaf cell, both leaf cells, the dummy rows
  against the leaf columns), with its bodies (2 x 2 blocks on a mode's first and second rows and
  columns that read P); the body counts must be 8, 8, 8, 0, as the project's page "The Host, Step
  by Step" and its test find;
- the tree and dummy part of A_2 read on the five columns that show the most of the 32 five-bit
  words of S (there must be 9);
- the direct-sum example: H' = [H 0; 0 Z] and A^+ = [A 0; 0 Zhat] built from the write-up's
  definitions with H = P, Z = (1) and the 3 x 3 example A; every copy of H' found by brute force must
  be a copy of H in A plus a new row and a new column (27 of them), and D_H'(A^+) = D_H(A) = 1;
- the proof of the direct-sum theorem, as schematics of [X 0; 0 Zhat] drawn with p = q = 2 and
  Z = [1 0; 1 1]: Step 1 (two of the p + 1 rows fall in one group and read the same), Step 2, and
  Step 3 (picked lines, bad lines, a copy of H in B° completed to a copy of H');
- the reduction red(H) of the write-up's example.
- the Lean frames: code quoted verbatim from the repository's Lean files, and checked against them
  when the repository is found (see lean_repo).
- the duplication proof on the 3 x 3 example: Fact 1's frames and completions (sum x_F = N_H and
  the copies of H' from pairs of completions), Fact 2(a) with q = 2, and Fact 2(b) with q = 3, where
  all 729 random picks are checked (at least half contain R) and B' must still contain H.

construction.py (the construction of OpenAI's preprint) is read from this folder. Inside the
project repository the script also finds the project's code/construction.py and stops if the two
differ, so the copy here cannot drift.

The template's markers %%NAME%% are replaced by the generated code, and the result is written to
the file named on the command line (default: slides-2026-11-15T0054Z.tex next to this script).

Usage: python3 make_slides.py [output.tex]
"""

import itertools
import math
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
LOCAL_COPY = HERE / "construction.py"
PROJECT_COPY = HERE.parent.parent.parent / "code" / "construction.py"  # inside the project repository
if LOCAL_COPY.exists():
    if PROJECT_COPY.exists() and PROJECT_COPY.read_bytes() != LOCAL_COPY.read_bytes():
        raise SystemExit("construction.py here differs from the project's code/construction.py: copy the project's file over it")
    sys.path.insert(0, str(HERE))
else:
    sys.path.insert(0, str(PROJECT_COPY.parent))

from construction import Block, TreeMatrix, anchor_matrix, pattern_matrix  # noqa: E402

TEMPLATE = HERE / "slides-template.tex"
DEFAULT_OUT = HERE / "slides-2026-11-15T0054Z.tex"

P = [[1, 0], [1, 1]]
A_EX = [[1, 0, 0], [1, 1, 1], [1, 0, 1]]


# ---------------------------------------------------------------- brute force

def copies(H, A):
    """All ordered copies of H in A, as (rows, columns), 0-based."""
    k, l = len(H), len(H[0])
    out = []
    for rows in itertools.combinations(range(len(A)), k):
        for cols in itertools.combinations(range(len(A[0])), l):
            if all(A[rows[i]][cols[j]] == H[i][j] for i in range(k) for j in range(l)):
                out.append((rows, cols))
    return out


def distance(H, A):
    """D_H(A) by brute force over all matrices of A's shape (small A only)."""
    n, m = len(A), len(A[0])
    best = None
    for bits in range(2 ** (n * m)):
        B = [[(bits >> (i * m + j)) & 1 for j in range(m)] for i in range(n)]
        if copies(H, B):
            continue
        d = sum(A[i][j] != B[i][j] for i in range(n) for j in range(m))
        best = d if best is None else min(best, d)
    return best


def flipped(A, cells):
    B = [row[:] for row in A]
    for i, j in cells:
        B[i][j] = 1 - B[i][j]
    return B


# ---------------------------------------------------------------- TikZ helpers

def fmt(x):
    return ("%.3f" % x).rstrip("0").rstrip(".") if x != 0 else "0"


class Grid:
    """A matrix drawn cell by cell: cell (i, j) has its top-left corner at (j*s, -i*s)."""

    def __init__(self, s, x0=0.0, y0=0.0):
        self.s, self.x0, self.y0 = s, x0, y0

    def rect(self, i, j, pad=0.0):
        s = self.s
        return (self.x0 + j * s + pad, self.y0 - i * s - pad, self.x0 + (j + 1) * s - pad, self.y0 - (i + 1) * s + pad)

    def center(self, i, j):
        s = self.s
        return (self.x0 + (j + 0.5) * s, self.y0 - (i + 0.5) * s)

    def block_center(self, rows, cols):
        s = self.s
        return (self.x0 + (min(cols) + max(cols) + 1) * s / 2, self.y0 - (min(rows) + max(rows) + 1) * s / 2)

    def fill(self, cells, style, pad=0.0):
        out = []
        for i, j in cells:
            a, b, c, d = self.rect(i, j, pad)
            out.append(r"\fill[%s] (%s,%s) rectangle (%s,%s);" % (style, fmt(a), fmt(b), fmt(c), fmt(d)))
        return out

    def outline(self, cells, style, pad=0.06):
        out = []
        for i, j in cells:
            a, b, c, d = self.rect(i, j, pad)
            out.append(r"\draw[%s] (%s,%s) rectangle (%s,%s);" % (style, fmt(a), fmt(b), fmt(c), fmt(d)))
        return out

    def box(self, rows, cols, style, pad=0.03):
        a, b, _, _ = self.rect(min(rows), min(cols), pad)
        _, _, c, d = self.rect(max(rows), max(cols), pad)
        return r"\draw[%s] (%s,%s) rectangle (%s,%s);" % (style, fmt(a), fmt(b), fmt(c), fmt(d))

    def digits(self, M, style="font=\\small"):
        out = []
        for i, row in enumerate(M):
            for j, v in enumerate(row):
                x, y = self.center(i, j)
                out.append(r"\node[%s] at (%s,%s) {$%d$};" % (style, fmt(x), fmt(y), v))
        return out

    def lines(self, n, m, style="gray!55"):
        s = self.s
        out = []
        for i in range(n + 1):
            out.append(r"\draw[%s] (%s,%s) -- (%s,%s);" % (style, fmt(self.x0), fmt(self.y0 - i * s), fmt(self.x0 + m * s), fmt(self.y0 - i * s)))
        for j in range(m + 1):
            out.append(r"\draw[%s] (%s,%s) -- (%s,%s);" % (style, fmt(self.x0 + j * s), fmt(self.y0), fmt(self.x0 + j * s), fmt(self.y0 - n * s)))
        return out

    def labels(self, row_labels, col_labels, style="font=\\scriptsize"):
        out = []
        for i, lab in enumerate(row_labels):
            x, y = self.center(i, 0)
            out.append(r"\node[%s, anchor=east] at (%s,%s) {%s};" % (style, fmt(self.x0 - 0.08), fmt(y), lab))
        for j, lab in enumerate(col_labels):
            x, y = self.center(0, j)
            out.append(r"\node[%s, anchor=south] at (%s,%s) {%s};" % (style, fmt(x), fmt(self.y0 + 0.05), lab))
        return out


def only(spec, lines):
    """Wrap TikZ commands in \\only<spec>{...}."""
    if not lines:
        return []
    return [r"\only<%s>{%%" % spec] + ["  " + line for line in lines] + ["}"]


def tikz(lines, options=""):
    return "\n".join([r"\begin{tikzpicture}[%s]" % options] + lines + [r"\end{tikzpicture}"])


def copy_cells(copy):
    rows, cols = copy
    return [(i, j) for i in rows for j in cols]


# ---------------------------------------------------------------- the small examples

def small_examples():
    found = copies(P, A_EX)
    order = [((0, 1), (0, 2)), ((0, 1), (0, 1)), ((0, 2), (0, 2))]
    assert sorted(found) == sorted(order), found
    assert distance(P, A_EX) == 1
    A_free = flipped(A_EX, [(0, 0)])
    assert copies(P, A_free) == []
    A_new = flipped(A_EX, [(0, 1)])
    after = copies(P, A_new)
    destroyed, created = ((0, 1), (0, 1)), ((0, 1), (1, 2))
    assert destroyed in found and destroyed not in after and created in after and created not in found
    assert len(after) == 3 and set(found) - {destroyed} <= set(after)
    assert all((0, 0) in copy_cells(c) for c in found)  # every copy uses A(1,1)

    g = Grid(0.8)
    labels = g.labels(["$1$", "$2$", "$3$"], ["$1$", "$2$", "$3$"])
    colors = ["accent!25", "teal!22", "violet!18"]

    # frame: the copies, one at a time
    lines = []
    for k, c in enumerate(order):
        lines += only(str(k + 2), g.fill(copy_cells(c), colors[k]))
    lines += only("5", g.fill([(0, 0)], "accent!40"))
    lines += g.lines(3, 3) + g.digits(A_EX) + labels
    outline_styles = ["accent", "teal!70!black", "violet!70!black"]
    for k, (c, st) in enumerate(zip(order, outline_styles)):
        lines += only("5", g.outline(copy_cells(c), "%s, thick" % st, pad=0.05 + 0.06 * k))
    copies_pic = tikz(lines)

    # frame: one change removes all of them
    lines = []
    lines += only("1", g.fill([(0, 0)], "accent!40"))
    lines += only("2-", g.fill([(0, 0)], "green!25"))
    lines += g.lines(3, 3)
    lines += only("1", g.digits(A_EX))
    lines += only("2-", g.digits(A_free))
    lines += labels
    distance_pic = tikz(lines)

    # frame: a change creates a copy
    lines = []
    lines += only("1-2", g.fill(copy_cells(destroyed), "accent!22"))
    lines += only("2", g.fill([(0, 1)], "accent!50"))
    lines += only("3-", g.fill([(0, 1)], "accent!30"))
    lines += only("4-", g.fill([c for c in copy_cells(created) if c != (0, 1)], "green!28"))
    lines += g.lines(3, 3)
    lines += only("1-2", g.digits(A_EX))
    lines += only("3-", g.digits(A_new))
    lines += labels
    lines += only("3-", g.outline(copy_cells(destroyed), "red!75!black, dashed, thick", pad=0.08))
    lines += only("4-", g.outline(copy_cells(created), "green!50!black, very thick", pad=0.04))
    create_pic = tikz(lines)

    # frame: all copies share one entry
    lines = []
    lines += g.fill([(0, 0)], "accent!40")
    lines += g.lines(3, 3) + g.digits(A_EX) + labels
    styles = ["accent", "teal!70!black", "violet!70!black"]
    for k, (c, st) in enumerate(zip(order, styles)):
        pad = 0.05 + 0.06 * k
        lines += only("%d-" % (k + 1), g.outline(copy_cells(c), "%s, thick" % st, pad=pad))
    disjoint_pic = tikz(lines)
    return {"COPIES": copies_pic, "DISTANCE": distance_pic, "CREATE": create_pic, "DISJOINT": disjoint_pic}


# ---------------------------------------------------------------- OpenAI's H

def h_picture(s=0.072, gap=0.16, labels=True):
    H = pattern_matrix()
    def x(j):
        return j * s + (gap if j >= 64 else 0)
    def y(i):
        return -(i * s + (gap if i >= 64 else 0))
    lines = []
    regions = [((0, 64), (0, 64), "ink!6"), ((0, 64), (64, 66), "teal!16"), ((64, 66), (0, 64), "teal!16"),
               ((64, 66), (64, 66), "accent!30")]
    for (r0, r1), (c0, c1), col in regions:
        lines.append(r"\fill[%s] (%s,%s) rectangle (%s,%s);" % (col, fmt(x(c0)), fmt(y(r0)), fmt(x(c1 - 1) + s), fmt(y(r1 - 1) - s)))
    for i, row in enumerate(H):
        j = 0
        while j < 66:
            if row[j] == 1:
                k = j
                while k + 1 < 66 and row[k + 1] == 1 and (k + 1 != 64):
                    k += 1
                lines.append(r"\fill[ink] (%s,%s) rectangle (%s,%s);" % (fmt(x(j)), fmt(y(i)), fmt(x(k) + s), fmt(y(i) - s)))
                j = k + 1
            else:
                j += 1
    if not labels:
        return tikz(lines)
    # outline of the five-bit words
    lines.append(r"\draw[accent, thick] (%s,%s) rectangle (%s,%s);" % (fmt(x(59)), fmt(y(32)), fmt(x(63) + s), fmt(y(63) - s)))
    lines.append(r"\node[font=\scriptsize, anchor=west, align=left] at (%s,%s) {32 five-bit\\ words};" % (fmt(x(66) + 0.15), fmt(y(48))))
    lines.append(r"\draw[accent] (%s,%s) -- (%s,%s);" % (fmt(x(63) + s), fmt(y(48)), fmt(x(66) + 0.15), fmt(y(48))))
    lines.append(r"\node[font=\scriptsize, anchor=west] at (%s,%s) {marks};" % (fmt(x(66) + 0.15), fmt(y(64) - s)))
    lines.append(r"\node[font=\scriptsize, anchor=north] at (%s,%s) {body $P$};" % (fmt(x(65)), fmt(y(66) - 0.05)))
    lines.append(r"\node[font=\scriptsize, anchor=north] at (%s,%s) {anchor $S$, $64\times64$};" % (fmt(x(32)), fmt(y(66) - 0.05)))
    return tikz(lines)


# ---------------------------------------------------------------- A_1: the tree and dummy part under edits

def core_frame():
    h = 1
    t = TreeMatrix(h)
    m = t.leaf_count
    rpos, cpos = t.positions("row"), t.positions("column")
    rows = [k for k, b in enumerate(rpos) if b.kind != "anchor"]
    cols = [k for k, b in enumerate(cpos) if b.kind != "anchor"]
    full = t.full_matrix_rows()
    N = len(rows)
    base = [[(full[r] >> c) & 1 for c in cols] for r in rows]
    rb, cb = [rpos[r] for r in rows], [cpos[c] for c in cols]
    sets = []
    for mode in t.modes:
        R1 = [i for i in range(N) if t.designated_role(rb[i], mode, "row") == 1]
        R2 = [i for i in range(N) if t.designated_role(rb[i], mode, "row") == 2]
        C1 = [j for j in range(N) if t.designated_role(cb[j], mode, "column") == 1]
        C2 = [j for j in range(N) if t.designated_role(cb[j], mode, "column") == 2]
        sets.append((mode, R1, R2, C1, C2))

    def bodies(B):
        out = []
        for mode, R1, R2, C1, C2 in sets:
            for r1 in R1:
                for r2 in R2:
                    if r1 >= r2:
                        continue
                    for c1 in C1:
                        for c2 in C2:
                            if c1 < c2 and (B[r1][c1], B[r1][c2], B[r2][c1], B[r2][c2]) == (1, 0, 1, 1):
                                if mode.kind == "V":
                                    tail, head = (r2, c2), (r1, c2)
                                else:
                                    tail, head = (r1, c1), (r1, c2)
                                out.append((tail, head))
        return out

    leaf_row = {b.node: i for i, b in enumerate(rb) if b.kind == "leaf"}
    leaf_col = {b.node: j for j, b in enumerate(cb) if b.kind == "leaf"}
    dummy_rows = [i for i, b in enumerate(rb) if b.kind == "dummy"]

    def edit(cells_to_zero):
        B = [row[:] for row in base]
        for i, j in cells_to_zero:
            B[i][j] = 0
        return B

    steps = [
        edit([]),
        edit([(leaf_row[0], leaf_col[0])]),
        edit([(leaf_row[p], leaf_col[p]) for p in range(m)]),
        edit([(i, leaf_col[p]) for i in dummy_rows for p in range(m)]),
    ]
    counts = [len(bodies(B)) for B in steps]
    changed = [sum(B[i][j] != base[i][j] for i in range(N) for j in range(N)) for B in steps]
    assert counts == [8, 8, 8, 0], counts
    assert changed == [0, 1, 2, 4], changed
    # the last state stays on screen for one more step (the m^2 argument)
    spec = lambda k: "%d-" % (k + 1) if k == len(steps) - 1 else str(k + 1)

    def label(axis, b):
        if b.kind == "dummy":
            return "$%s_*$" % axis
        if b.kind == "leaf":
            return "$%s_{%d}$" % (axis.lower(), b.node)
        return "$%s_{%d}^{%s}$" % (axis, b.level, b.sign)

    g = Grid(0.5)
    lines = []
    # dummy lines shaded
    lines += g.fill([(i, j) for i in dummy_rows for j in range(N)] + [(i, j) for i in range(N) for j in range(N) if cb[j].kind == "dummy" and i not in dummy_rows], "gray!12")
    for k, B in enumerate(steps):
        changed_cells = [(i, j) for i in range(N) for j in range(N) if B[i][j] != base[i][j]]
        body_cells = sorted({c for tail, head in bodies(B) for c in (tail, head)})
        lines += only(spec(k), g.fill(body_cells, "accent!22") + g.fill(changed_cells, "green!30"))
    lines += g.lines(N, N, "gray!45")
    for k, B in enumerate(steps):
        lines += only(spec(k), g.digits(B, "font=\\footnotesize"))
    lines += g.labels([label("R", b) for b in rb], [label("C", b) for b in cb])
    # the root's square of 1s (plus) and of 0s (minus)
    plus_rows = [i for i, b in enumerate(rb) if b.kind == "variable" and b.sign == "+" and b.level == 0]
    minus_rows = [i for i, b in enumerate(rb) if b.kind == "variable" and b.sign == "-" and b.level == 0]
    root_plus_cols = [j for j, b in enumerate(cb) if b.kind == "variable" and b.sign == "+" and b.level == 0]
    root_minus_cols = [j for j, b in enumerate(cb) if b.kind == "variable" and b.sign == "-" and b.level == 0]
    lines.append(g.box(plus_rows, root_plus_cols, "blue!70!black, very thick"))
    lines.append(g.box(minus_rows, root_minus_cols, "orange!90!black, very thick"))
    for p in range(m):
        x, y = g.center(leaf_row[p], leaf_col[p])
        lines.append(r"\draw[violet, thick] (%s,%s) circle (0.2);" % (fmt(x), fmt(y)))
    # drops, grouped by the blocks of their tail and head
    def block_of(cell):
        i, j = cell
        return (rb[i], cb[j])
    def cells_of(key):
        r, c = key
        return [i for i in range(N) if rb[i] == r], [j for j in range(N) if cb[j] == c]
    for k, B in enumerate(steps):
        groups = {}
        for tail, head in bodies(B):
            key = (block_of(tail), block_of(head))
            groups[key] = groups.get(key, 0) + 1
        arrows = []
        for (tk, hk), cnt in groups.items():
            (tr, tc), (hr, hc) = cells_of(tk), cells_of(hk)
            x1, y1 = g.block_center(tr, tc)
            x2, y2 = g.block_center(hr, hc)
            dx, dy = x2 - x1, y2 - y1
            length = math.hypot(dx, dy)
            ux, uy = dx / length, dy / length
            sx, sy, ex, ey = x1 + ux * 0.12, y1 + uy * 0.12, x2 - ux * 0.12, y2 - uy * 0.12
            arrows.append(r"\draw[-{Stealth[length=2.2mm]}, accent!90!black, very thick] (%s,%s) -- (%s,%s);" % (fmt(sx), fmt(sy), fmt(ex), fmt(ey)))
            lx, ly = (sx + ex) / 2, (sy + ey) / 2
            offx, offy = (-uy * 0.22, ux * 0.22)
            arrows.append(r"\node[font=\scriptsize\bfseries, text=accent!90!black, fill=paper, inner sep=1pt] at (%s,%s) {%d};" % (fmt(lx + offx), fmt(ly + offy), cnt))
        lines += only(spec(k), arrows)
    pic = tikz(lines)
    return pic, counts, changed


# ---------------------------------------------------------------- direct sum example

def direct_sum(H, Z):
    """H' = [H 0; 0 Z], as in the write-up's Setup."""
    k, l, p, q = len(H), len(H[0]), len(Z), len(Z[0])
    return [row + [0] * q for row in H] + [[0] * l + row for row in Z]


def direct_sum_host(A, Z):
    """A+ = [A 0; 0 Zhat], where Zhat replaces every entry of Z by a constant block with qn rows
    and pn columns (the write-up's Setup). Returns A+ and the group (0-based) of each new row and
    each new column."""
    n, p, q = len(A), len(Z), len(Z[0])
    row_group = [i for i in range(p) for _ in range(q * n)]
    col_group = [j for j in range(q) for _ in range(p * n)]
    zhat = [[Z[a][b] for b in col_group] for a in row_group]
    assert len(zhat) == len(zhat[0]) == p * q * n            # Zhat is pqn x pqn
    Aplus = direct_sum(A, zhat)
    assert len(Aplus) == len(Aplus[0]) == (1 + p * q) * n    # size m = (1 + pq) n
    return Aplus, row_group, col_group


def direct_sum_example():
    """The direct-sum theorem on H = P, Z = (1) and the 3 x 3 example A, step by step: the host
    A+, one copy of H', all copies (each one a copy of H in A plus a new row and a new column), and
    the distance."""
    H, Z, A = P, [[1]], A_EX
    k, l, p, q, n = len(H), len(H[0]), len(Z), len(Z[0]), len(A)
    H2 = direct_sum(H, Z)
    Aplus, row_group, col_group = direct_sum_host(A, Z)
    m = len(Aplus)
    old, new = range(n), range(n, m)
    copies_H, copies_H2 = copies(H, A), copies(H2, Aplus)
    # Step 1 of the proof, on this example: every copy of H' is a copy of H in A (its H-rows and
    # H-columns) together with any new row and any new column (its Z-row and Z-column)
    assert sorted(copies_H2) == sorted((rows + (z,), cols + (w,)) for rows, cols in copies_H for z in new for w in new)
    nh, nh2 = len(copies_H), len(copies_H2)
    assert (p, q, m) == (1, 1, 6) and nh2 == nh * len(new) ** 2 == 27 and nh2 <= m ** (p + q) * nh
    # the copy shown: the first copy of H in A, with the first new row and column
    shown_H = ((0, 1), (0, 2))
    assert shown_H in copies_H
    shown = (shown_H[0] + (n,), shown_H[1] + (n,))
    assert [[Aplus[i][j] for j in shown[1]] for i in shown[0]] == H2
    # distance: D_H(A) = 1 by brute force; changing A(1,1) in A+ leaves no copy of H', and A+ has
    # copies, so D_H'(A+) = 1 too
    d = distance(H, A)
    fixed = flipped(Aplus, [(0, 0)])
    assert d == 1 and copies(H, flipped(A, [(0, 0)])) == [] and copies(H2, fixed) == [] and nh2 > 0

    g = Grid(0.5)
    W = m * g.s
    lines = [r"\useasboundingbox (-1.3,1.05) rectangle (%s,%s);" % (fmt(W + 0.1), fmt(-W - 0.1))]
    # old-old block and new-new block (Zhat) lightly tinted on every step
    lines += g.fill([(i, j) for i in old for j in old], "accent!7")
    lines += g.fill([(i, j) for i in new for j in new], "gray!16")
    # step 2: one copy (H-part orange, Z-part teal, the 0s between them pale)
    h_cells = [(i, j) for i in shown_H[0] for j in shown_H[1]]
    z_cells = [(n, n)]
    cross = [c for c in copy_cells(shown) if c not in h_cells and c not in z_cells]
    lines += only("2", g.fill(h_cells, "accent!38") + g.fill(z_cells, "teal!35") + g.fill(cross, "accent!13"))
    # step 3: all the Z-row and Z-column choices
    lines += only("3", g.fill([(i, j) for i in new for j in new], "teal!28"))
    # step 4: the changed entry
    lines += only("4", g.fill([(0, 0)], "green!30"))
    lines += g.lines(m, m, "gray!45")
    lines += only("1-3", g.digits(Aplus, "font=\\footnotesize"))
    lines += only("4", g.digits(fixed, "font=\\footnotesize"))
    lines.append(g.box(old, old, "accent, thick"))
    lines.append(g.box(new, new, "black!60, thick"))
    lines += g.labels(["$%d$" % (i + 1) for i in range(m)], ["$%d$" % (j + 1) for j in range(m)])
    # step 3: the three copies of H in A, outlined as on the first slides
    styles = ["accent", "teal!70!black", "violet!70!black"]
    outl = []
    for k_, (c, st) in enumerate(zip(copies(H, A), styles)):
        outl += g.outline(copy_cells(c), "%s, thick" % st, pad=0.04 + 0.05 * k_)
    lines += only("3", outl)
    # old / new braces
    for (a, b, lab) in [(0, n, "old"), (n, m, "new")]:
        lines.append(r"\draw[decorate, decoration={brace, amplitude=3pt}, muted] (%s,0.52) -- (%s,0.52) node[midway, above=2pt, font=\scriptsize, text=muted] {%s};" % (fmt(a * g.s + 0.03), fmt(b * g.s - 0.03), lab))
        lines.append(r"\draw[decorate, decoration={brace, amplitude=3pt, mirror}, muted] (-0.5,%s) -- (-0.5,%s) node[midway, left=2pt, font=\scriptsize, text=muted] {%s};" % (fmt(-a * g.s - 0.03), fmt(-b * g.s + 0.03), lab))
    pic = tikz(lines)

    def mat(M):
        """M as a LaTeX array, with rules between the H-part and the Z-part."""
        rows = [" & ".join(str(v) for v in row) for row in M]
        body = r"\\ ".join(rows[:k]) + r"\\ \hline " + r"\\ ".join(rows[k:])
        return r"\left(\begin{smallmatrix}%s\end{smallmatrix}\right)" % body.replace(r"\\ \hline ", r"\\ ")

    one = lambda xs: ",".join(str(x + 1) for x in xs)
    numbers = {"DS_NH": str(nh), "DS_NH2": str(nh2), "DS_DH": str(d), "DS_M": str(m), "DS_NEW": str(len(new)),
               "DS_BOUND": "%d^{%d}\\cdot%d=%d" % (m, p + q, nh, m ** (p + q) * nh),
               "DS_HPRIME": mat(H2), "DS_HROWS": one(shown_H[0]), "DS_HCOLS": one(shown_H[1]),
               "DS_ZROW": one([n]), "DS_ZCOL": one([n]), "DS_OLD": "$1$--$%d$" % n, "DS_NEWR": "$%d$--$%d$" % (n + 1, m)}
    assert q * n == p * n == len(new)  # the single group of new rows and of new columns has 3 lines
    return pic, numbers


# ---------------------------------------------------------------- direct sums: the proof, as diagrams

class Schematic:
    """A schematic of [X 0; 0 Zhat], not to scale: an old part of size `old` and, on each axis, the
    groups of new lines (p groups of rows, q groups of columns, each of size `grp`). Positions along
    an axis are (part, fraction), part "old" or a group index 0, 1, ..."""

    def __init__(self, Z, old=1.0, grp=1.5):
        self.Z, self.p, self.q = Z, len(Z), len(Z[0])
        self.old, self.grp = old, grp
        self.W = old + self.p * grp
        assert self.p == self.q  # drawn square

    def t(self, pos):
        part, f = pos
        return f * self.old if part == "old" else self.old + (part + f) * self.grp

    def x(self, col):
        return self.t(col)

    def y(self, row):
        return -self.t(row)

    def group(self, pos):
        return pos[0]

    def value(self, row, col):
        """The entry of [X 0; 0 Zhat] at a new row and a new column, or in a mixed block (0);
        None in the old-old block (X)."""
        if row[0] == "old" and col[0] == "old":
            return None
        if row[0] == "old" or col[0] == "old":
            return 0
        return self.Z[row[0]][col[0]]

    def base(self, old_label, label_at=(0.5, 0.5), zero_labels=True, block_fill=True):
        W, a, g = self.W, self.old, self.grp
        L = [r"\useasboundingbox (-0.55,0.75) rectangle (%s,%s);" % (fmt(W + 0.8), fmt(-W - 0.4))]
        if block_fill:
            for i in range(self.p):
                for j in range(self.q):
                    if self.Z[i][j]:
                        L.append(r"\fill[ink!13] (%s,%s) rectangle (%s,%s);" % (fmt(a + j * g), fmt(-a - i * g), fmt(a + (j + 1) * g), fmt(-a - (i + 1) * g)))
        for k in range(1, self.p):
            L.append(r"\draw[muted, dashed, line width=0.3pt] (%s,%s) -- (%s,%s);" % (fmt(a), fmt(-a - k * g), fmt(W), fmt(-a - k * g)))
            L.append(r"\draw[muted, dashed, line width=0.3pt] (%s,%s) -- (%s,%s);" % (fmt(a + k * g), fmt(-a), fmt(a + k * g), fmt(-W)))
        L.append(r"\draw[ink, line width=0.6pt] (0,0) rectangle (%s,%s);" % (fmt(W), fmt(-W)))
        L.append(r"\draw[ink, line width=0.6pt] (%s,0) -- (%s,%s); \draw[ink, line width=0.6pt] (0,%s) -- (%s,%s);" % (fmt(a), fmt(a), fmt(-W), fmt(-a), fmt(W), fmt(-a)))
        if old_label:
            L.append(r"\node[font=\small] at (%s,%s) {%s};" % (fmt(label_at[0] * a), fmt(-label_at[1] * a), old_label))
        if zero_labels:
            for (cx, cy) in [((a + W) / 2, -a / 2), (a / 2, -(a + W) / 2)]:
                L.append(r"\node[font=\small, text=muted] at (%s,%s) {$0$};" % (fmt(cx), fmt(cy)))
        # braces: old and the groups, on both axes
        spans = [(0, a, "old")] + [(a + k * g, a + (k + 1) * g, "group %d" % (k + 1)) for k in range(self.p)]
        for s0, s1, lab in spans:
            L.append(r"\draw[decorate, decoration={brace, amplitude=3pt}, muted] (%s,0.08) -- (%s,0.08) node[midway, above=2pt, font=\scriptsize, text=muted] {%s};" % (fmt(s0 + 0.03), fmt(s1 - 0.03), lab))
            L.append(r"\draw[decorate, decoration={brace, amplitude=3pt, mirror}, muted] (-0.08,%s) -- (-0.08,%s) node[midway, xshift=-3pt, rotate=90, anchor=south, font=\scriptsize, text=muted] {%s};" % (fmt(-s0 - 0.03), fmt(-s1 + 0.03), lab))
        return L

    def hline(self, row, label, style, x0=None, x1=None):
        y = self.y(row)
        x0 = 0 if x0 is None else x0
        x1 = self.W if x1 is None else x1
        return [r"\draw[%s] (%s,%s) -- (%s,%s);" % (style, fmt(x0), fmt(y), fmt(x1), fmt(y)),
                r"\node[font=\scriptsize, anchor=west, inner sep=1pt] at (%s,%s) {%s};" % (fmt(self.W + 0.06), fmt(y), label)]

    def vline(self, col, label, style):
        x = self.x(col)
        return [r"\draw[%s] (%s,0) -- (%s,%s);" % (style, fmt(x), fmt(x), fmt(-self.W)),
                r"\node[font=\scriptsize, anchor=north, inner sep=1pt] at (%s,%s) {%s};" % (fmt(x), fmt(-self.W - 0.04), label)]

    def dot(self, row, col, text, draw="ink", fill="paper"):
        return r"\node[circle, draw=%s, fill=%s, line width=0.6pt, inner sep=0pt, minimum size=3.2mm, font=\tiny] at (%s,%s) {$%s$};" % (draw, fill, fmt(self.x(col)), fmt(self.y(row)), text)

    def cross(self, row, col, style="red!75!black"):
        x, y, d = self.x(col), self.y(row), 0.06
        return r"\draw[%s, line width=1pt] (%s,%s) -- (%s,%s) (%s,%s) -- (%s,%s);" % (style, fmt(x - d), fmt(y - d), fmt(x + d), fmt(y + d), fmt(x - d), fmt(y + d), fmt(x + d), fmt(y - d))


DS_Z = [[1, 0], [1, 1]]   # the Z the proof diagrams are drawn with (pairwise distinct rows)
H_COL, Z_COL = "accent!90!black", "teal!75!black"


def ds_proof_step1():
    """Step 1: in every copy of H' in [X 0; 0 Zhat], the H-rows and H-columns are old. The picture
    supposes the last H-row r_k is new and follows the argument to the two equal rows."""
    Z = DS_Z
    S = Schematic(Z)
    p, q = S.p, S.q
    assert len(set(map(tuple, Z))) == p                     # rows of Z pairwise distinct
    need = direct_sum([[1]], Z)                             # what rows r_k..r_{k+p}, columns c_j, c_{l+1}.. must read
    assert len(set(map(tuple, need))) == p + 1              # ... and its p+1 rows are pairwise distinct
    rows = [(0, 0.3), (0, 0.75), (1, 0.5)]                  # r_k, r_{k+1}, r_{k+2}: new
    cols = [(0, 0.3), (0, 0.75), (1, 0.5)]                  # c_j, c_{l+1}, c_{l+2}: new
    assert len(rows) == p + 1 and len(cols) == q + 1
    assert all(r[0] != "old" for r in rows) and all(c[0] != "old" for c in cols)
    assert rows == sorted(rows) and cols == sorted(cols)
    read = [[S.value(r, c) for c in cols] for r in rows]
    assert read[0][0] == 1                                  # M(r_k, c_j) = 1, as row k of H needs
    same = [(a, b) for a, b in itertools.combinations(range(p + 1), 2) if rows[a][0] == rows[b][0]]
    assert same == [(0, 1)] and read[0] == read[1] and need[0] != need[1]   # pigeonhole: two equal rows
    assert read != need
    row_labels = ["$r_k$", "$r_{k+1}$", "$r_{k+2}$"]
    col_labels = ["$c_j$", "$c_{l+1}$", "$c_{l+2}$"]
    L = S.base("$X$", label_at=(0.22, 0.53))
    # step 2-4: the rows; step 3-4: the columns; step 4: all nine entries
    L += only("2-4", S.hline(rows[0], row_labels[0], "%s, thick" % H_COL))
    L += only("2-4", sum((S.hline(r, lab, "%s, thick" % Z_COL) for r, lab in zip(rows[1:], row_labels[1:])), []))
    L += only("3-4", S.vline(cols[0], col_labels[0], "%s, thick" % H_COL))
    L += only("3-4", sum((S.vline(c, lab, "%s, thick" % Z_COL) for c, lab in zip(cols[1:], col_labels[1:])), []))
    L += only("3", [S.dot(rows[0], cols[0], "1", draw=H_COL)])
    dots = [S.dot(r, c, str(read[a][b]), draw="red!75!black" if read[a][b] != need[a][b] else "ink")
            for a, r in enumerate(rows) for b, c in enumerate(cols)]
    L += only("4", dots)
    # step 4: the two rows in one group, bracketed on the far right
    ya, yb = S.y(rows[0]), S.y(rows[1])
    L += only("4", [r"\draw[red!75!black, line width=0.8pt] (%s,%s) -- ++(0.1,0) |- (%s,%s);" % (fmt(S.W + 0.68), fmt(ya), fmt(S.W + 0.68), fmt(yb))])
    # step 5: the old part, r_i and c_l crossing at a 1
    ri, rk, cl = ("old", 0.3), ("old", 0.75), ("old", 0.6)
    assert S.value(ri, (0, 0.5)) == 0          # an old row reads 0 against every new column
    L += only("5", S.hline(ri, "$r_i$", "%s, thick" % H_COL) + S.hline(rk, "$r_k$", "%s, thick" % H_COL) + S.vline(cl, "$c_l$", "%s, thick" % H_COL))
    L += only("5", [S.dot(ri, cl, "1", draw=H_COL)])
    numbers = {"DSP_Z": r"\smallmat{%s}" % r"\\".join("&".join(map(str, r)) for r in Z),
               "DSP_NEED_K": "(%s)" % ",".join(map(str, need[0])), "DSP_NEED_K1": "(%s)" % ",".join(map(str, need[1])),
               "DSP_READ_K": "(%s)" % ",".join(map(str, read[0]))}
    return tikz(L), numbers


def ds_proof_step2():
    """Step 2: a copy of H' in A+ is a copy of H in A plus p new rows and q new columns; and a
    repair of A, with the rest of A+ unchanged, is a repair of A+."""
    S = Schematic(DS_Z, old=1.5, grp=1.25)
    h_rows, h_cols = [("old", 0.25), ("old", 0.75)], [("old", 0.25), ("old", 0.75)]
    z_rows, z_cols = [(0, 0.55), (1, 0.4)], [(0, 0.4), (1, 0.6)]
    # the H-lines meet the Z-lines in 0s, and the Z-lines read Z: the only freedom is where they are
    assert all(S.value(r, c) == 0 for r in h_rows for c in z_cols) and all(S.value(r, c) == 0 for r in z_rows for c in h_cols)
    assert [[S.value(r, c) for c in z_cols] for r in z_rows] == DS_Z
    L = [r"\only<1>{\node[font=\small] at (%s,%s) {$A$};}" % (fmt(S.old / 2), fmt(-S.old / 2))]
    L = S.base("") + L
    L += only("2-", [r"\fill[green!22] (0,0) rectangle (%s,%s);" % (fmt(S.old), fmt(-S.old)),
                     r"\node[font=\small, align=center] at (%s,%s) {$A_0$\\[-1pt] {\scriptsize $H$-free}};" % (fmt(S.old / 2), fmt(-S.old / 2)),
                     r"\draw[ink, line width=0.6pt] (0,0) rectangle (%s,%s);" % (fmt(S.old), fmt(-S.old))])
    lines = []
    for r, lab in zip(h_rows, ["$r_1$", "$r_2$"]):
        lines += S.hline(r, lab, "%s, thick" % H_COL)
    for c, lab in zip(h_cols, ["$c_1$", "$c_2$"]):
        lines += S.vline(c, lab, "%s, thick" % H_COL)
    for r, lab in zip(z_rows, ["$r_3$", "$r_4$"]):
        lines += S.hline(r, lab, "%s, thick, dashed" % Z_COL)
    for c, lab in zip(z_cols, ["$c_3$", "$c_4$"]):
        lines += S.vline(c, lab, "%s, thick, dashed" % Z_COL)
    lines += [S.dot(r, c, "", draw=H_COL, fill="accent!45") for r in h_rows for c in h_cols]
    L += only("1", lines)
    return tikz(L)


def ds_proof_step3():
    """Step 3: from an H'-free B, pick one line per group of new lines, zero the bad old lines, and
    find a repair of A in the old block. Positions are schematic; the asserts check the picture."""
    S = Schematic(DS_Z, old=1.75, grp=1.2)
    rho = [(0, 0.55), (1, 0.4)]            # picked rows, one per group
    gamma = [(0, 0.45), (1, 0.6)]          # picked columns, one per group
    E0 = [(("old", 0.18), ("old", 0.8)), (("old", 0.88), ("old", 0.3))]
    E1 = [(("old", 0.5), gamma[0]), (("old", 0.15), (1, 0.2)), (("old", 0.82), (1, 0.3)),   # top right
          (rho[1], ("old", 0.6)), ((0, 0.15), ("old", 0.15))]                               # bottom left
    E2 = [((0, 0.2), (0, 0.85)), ((1, 0.85), (0, 0.4)), ((1, 0.12), (1, 0.25))]
    assert all(r[0] == "old" and c[0] == "old" for r, c in E0)
    assert all((r[0] == "old") != (c[0] == "old") for r, c in E1)
    assert all(r[0] != "old" and c[0] != "old" for r, c in E2)
    # the pick is good: no change of B at a crossing of picked lines
    assert all((r, c) not in E2 for r in rho for c in gamma)
    # bad lines: old rows with a change (a 1 in B) on a picked column, old columns with one on a picked row
    bad_rows = sorted({r for r, c in E1 if r[0] == "old" and c in gamma})
    bad_cols = sorted({c for r, c in E1 if c[0] == "old" and r in rho})
    assert bad_rows == [("old", 0.5)] and bad_cols == [("old", 0.6)]
    # a copy of H in B° on lines that are not bad; it meets the picked lines in 0s
    h_rows, h_cols = [("old", 0.3), ("old", 0.72)], [("old", 0.25), ("old", 0.85)]
    assert not set(h_rows) & set(bad_rows) and not set(h_cols) & set(bad_cols)
    cross_cells = [(r, c) for r in h_rows for c in gamma] + [(r, c) for r in rho for c in h_cols]
    assert all(S.value(r, c) == 0 and (r, c) not in E1 for r, c in cross_cells)
    L = S.base("", zero_labels=False)
    L += [r"\node[font=\scriptsize, anchor=south east, inner sep=1.5pt] at (%s,%s) {$E_0$};" % (fmt(S.old), fmt(-S.old)),
          r"\node[font=\scriptsize, anchor=south east, inner sep=1.5pt] at (%s,%s) {$E_1$};" % (fmt(S.W), fmt(-S.old)),
          r"\node[font=\scriptsize, anchor=south east, inner sep=1.5pt] at (%s,%s) {$E_1$};" % (fmt(S.old), fmt(-S.W)),
          r"\node[font=\scriptsize, anchor=south east, inner sep=1.5pt] at (%s,%s) {$E_2$};" % (fmt(S.W), fmt(-S.W))]
    # step 3-: bad lines zeroed in the old block (drawn under everything else)
    zeroed = []
    for r in bad_rows:   # the zeroed row in the old block, and a trace to the change that makes it bad
        zeroed.append(r"\fill[red!16] (0,%s) rectangle (%s,%s);" % (fmt(S.y(r) + 0.07), fmt(S.old), fmt(S.y(r) - 0.07)))
        zeroed.append(r"\draw[red!60, dashed] (%s,%s) -- (%s,%s);" % (fmt(S.old), fmt(S.y(r)), fmt(S.x(gamma[0])), fmt(S.y(r))))
    for c in bad_cols:
        zeroed.append(r"\fill[red!16] (%s,0) rectangle (%s,%s);" % (fmt(S.x(c) - 0.07), fmt(S.x(c) + 0.07), fmt(-S.old)))
        zeroed.append(r"\draw[red!60, dashed] (%s,%s) -- (%s,%s);" % (fmt(S.x(c)), fmt(-S.old), fmt(S.x(c)), fmt(S.y(rho[1]))))
    L = L[:1] + only("3-", zeroed) + L[1:]
    L += [S.cross(r, c) for r, c in E0 + E1 + E2]
    # step 2-: the picked lines, and their crossings reading Z
    picked = []
    for i, r in enumerate(rho):
        picked += S.hline(r, r"$\rho_{%d}$" % (i + 1), "%s, thick" % Z_COL)
    for j, c in enumerate(gamma):
        picked += S.vline(c, r"$\gamma_{%d}$" % (j + 1), "%s, thick" % Z_COL)
    picked += [S.dot(r, c, str(S.value(r, c)), draw=Z_COL) for r in rho for c in gamma]
    L += only("2-", picked)
    # step 3-: the bad lines labelled; B° in the old block
    L += only("3-", [r"\node[font=\scriptsize, text=red!75!black, anchor=south west, inner sep=1pt] at (%s,%s) {bad};" % (fmt(S.x(gamma[0]) + 0.08), fmt(S.y(bad_rows[0]))),
                     r"\node[font=\scriptsize, text=red!75!black, anchor=north east, inner sep=1pt] at (%s,%s) {bad};" % (fmt(S.x(bad_cols[0]) - 0.04), fmt(S.y(rho[1]) - 0.08))])
    L += only("3-", [r"\node[font=\scriptsize, inner sep=0.5pt] at (%s,%s) {$B^\circ$};" % (fmt(0.42 * S.old), fmt(-0.12 * S.old))])
    # step 4-: a copy of H in B°, completed by the picked lines to a copy of H'
    copy = []
    for r in h_rows:
        copy.append(r"\draw[%s, thick] (0,%s) -- (%s,%s);" % (H_COL, fmt(S.y(r)), fmt(S.W), fmt(S.y(r))))
    for c in h_cols:
        copy.append(r"\draw[%s, thick] (%s,0) -- (%s,%s);" % (H_COL, fmt(S.x(c)), fmt(S.x(c)), fmt(-S.W)))
    copy += [S.dot(r, c, "", draw=H_COL, fill="accent!45") for r in h_rows for c in h_cols]
    copy += [S.dot(r, c, "0", draw="muted") for r, c in cross_cells]
    copy += [S.dot(r, c, str(S.value(r, c)), draw=Z_COL) for r in rho for c in gamma]
    L += only("4-", copy)
    return tikz(L)


# ---------------------------------------------------------------- red(H)

def reduce_pattern(M):
    """red(M): delete a row equal to the row above it, or a column equal to the column to its left,
    until none is left."""
    changed = True
    while changed:
        changed = False
        for i in range(1, len(M)):
            if M[i] == M[i - 1]:
                M = M[:i] + M[i + 1:]
                changed = True
                break
        if changed:
            continue
        for j in range(1, len(M[0])):
            if all(row[j] == row[j - 1] for row in M):
                M = [row[:j] + row[j + 1:] for row in M]
                changed = True
                break
    return M


def reduction_example():
    H3 = [[1, 1, 0], [1, 1, 0], [0, 0, 1]]

    def red(M):
        changed = True
        while changed:
            changed = False
            for i in range(1, len(M)):
                if M[i] == M[i - 1]:
                    M = M[:i] + M[i + 1:]
                    changed = True
                    break
            if changed:
                continue
            for j in range(1, len(M[0])):
                if all(row[j] == row[j - 1] for row in M):
                    M = [row[:j] + row[j + 1:] for row in M]
                    changed = True
                    break
        return M

    assert red(H3) == [[1, 0], [0, 1]]
    step2 = [H3[0], H3[2]]
    step4 = [[1, 0], [0, 1]]
    g = Grid(0.55)
    # the same box on every step, so the picture does not change size as rows and columns go
    lines = [r"\useasboundingbox (-0.05,0.05) rectangle (%s,%s);" % (fmt(3 * 0.55 + 0.05), fmt(-(3 * 0.55 + 0.05)))]
    lines += only("1", g.fill([(1, j) for j in range(3)], "accent!30"))
    lines += only("3", g.fill([(i, 1) for i in range(2)], "accent!30"))
    lines += only("1", g.lines(3, 3) + g.digits(H3))
    lines += only("2-3", g.lines(2, 3) + g.digits(step2))
    lines += only("4", g.lines(2, 2) + g.digits(step4))
    return tikz(lines)


# ---------------------------------------------------------------- duplication: the two directions

def blow_up(A, q):
    """A^(q): every entry of A replaced by a constant q x q block."""
    return [[A[i // q][j // q] for j in range(q * len(A[0]))] for i in range(q * len(A))]


def frames_and_completions(H, B, j):
    """Fact 1, Steps 1-2: every frame of B for H with column j (0-based) left out, and its
    completions. A frame is (rows, columns other than the jth), in increasing order."""
    k, l, n = len(H), len(H[0]), len(B)
    out = {}
    for rows in itertools.combinations(range(n), k):
        for cols in itertools.combinations(range(len(B[0])), l - 1):
            lo = cols[j - 1] if j > 0 else -1
            hi = cols[j] if j < l - 1 else len(B[0])
            done = []
            for c in range(lo + 1, hi):
                full = cols[:j] + (c,) + cols[j:]
                if all(B[rows[a]][full[b]] == H[a][b] for a in range(k) for b in range(l)):
                    done.append(c)
            out[(rows, cols)] = done
    return out


def fact1_frames():
    """Fact 1 on the 3 x 3 example: H = P with column 2 (j = 2) written twice, B = A_EX. Frames,
    their completions, sum x_F = N_H(B), and copies of H' from pairs of completions."""
    H, B, j = P, A_EX, 1                       # j = 1 is the paper's j = 2
    Hd = [row[:j + 1] + [row[j]] + row[j + 1:] for row in H]
    assert Hd == [[1, 0, 0], [1, 1, 1]]
    k, l, n = len(H), len(H[0]), len(B)
    F = frames_and_completions(H, B, j)
    T = len(F)
    assert T == math.comb(n, k) * math.comb(n, l - 1) and T <= n ** (k + l - 1)
    x = {f: len(c) for f, c in F.items()}
    N, Nd = len(copies(H, B)), len(copies(Hd, B))
    assert sum(x.values()) == N                                    # Step 2
    pairs = sorted((rows, cols[:j] + (a, b) + cols[j:]) for (rows, cols), done in F.items()
                   for a, b in itertools.combinations(done, 2))
    assert pairs == sorted(copies(Hd, B))                          # Step 3 (equality here)
    assert Nd == sum(math.comb(v, 2) for v in x.values())
    sq = sum(v * v for v in x.values())
    assert N * N <= T * sq                                         # Step 4
    assert Nd >= N * N / (2 * n ** (k + l - 1)) - N / 2            # Fact 1
    shown = sorted((f for f in F if F[f]), key=lambda f: -len(F[f]))
    assert [(f, F[f]) for f in shown] == [(((0, 1), (0,)), [1, 2]), (((0, 2), (0,)), [2])]
    g = Grid(0.75)
    labels = g.labels(["$1$", "$2$", "$3$"], ["$1$", "$2$", "$3$"])
    lines = [r"\useasboundingbox (-0.45,0.4) rectangle (2.35,-2.35);"]
    for spec, (rows, cols) in [("2,4", shown[0]), ("3", shown[1])]:
        lines += only(spec, g.fill([(r, c) for r in rows for c in cols], "accent!32")
                      + g.fill([(r, c) for r in rows for c in F[(rows, cols)]], "teal!28"))
    lines += g.lines(3, 3) + g.digits(B) + labels
    lines += only("4", g.outline(copy_cells(pairs[0]), "green!50!black, very thick", pad=0.05))
    one = lambda xs: ",".join(str(v + 1) for v in xs)
    numbers = {"F1_T": str(T), "F1_N": str(N), "F1_ND": str(Nd), "F1_SQ": str(sq),
               "F1_HD": r"\smallmat{%s}" % r"\\".join("&".join(map(str, r)) for r in Hd),
               "F1_A_ROWS": one(shown[0][0]), "F1_A_COL": one(shown[0][1]), "F1_A_DONE": " and ".join("$%d$" % (c + 1) for c in F[shown[0]]),
               "F1_A_X": str(len(F[shown[0]])),
               "F1_B_ROWS": one(shown[1][0]), "F1_B_COL": one(shown[1][1]), "F1_B_DONE": one(F[shown[1]]),
               "F1_REST": str(T - len(shown)),
               "F1_XSUM": "+".join(str(len(F[f])) for f in shown),
               "F1_BINOMS": "+".join(r"\binom{%d}{2}" % len(F[f]) for f in shown),
               "F1_COPY_ROWS": one(pairs[0][0]), "F1_COPY_COLS": one(pairs[0][1])}
    return tikz(lines), numbers


def fact1_bars():
    """Fact 1, Step 4: N completions spread over T frames. Spread evenly, they make the fewest pairs,
    N^2/(2T) - N/2; piled up, many more."""
    N, T = 6, 3
    cases = [(2, 2, 2), (4, 1, 1), (6, 0, 0)]
    assert all(sum(c) == N and len(c) == T for c in cases)
    pairs = [sum(math.comb(v, 2) for v in c) for c in cases]
    least = min(sum(math.comb(v, 2) for v in c) for c in itertools.product(range(N + 1), repeat=T) if sum(c) == N)
    assert least == pairs[0] == N * N / (2 * T) - N / 2 and pairs == sorted(pairs)
    s, w, gap = 0.27, 0.36, 0.6
    L = [r"\useasboundingbox (-0.65,0.45) rectangle (%s,%s);" % (fmt(3 * T * w + 2 * gap + 0.1), fmt(-N * s - 0.95))]
    x0 = 0.0
    base = -N * s
    for c, pr in zip(cases, pairs):
        for b, v in enumerate(c):
            x = x0 + b * w
            for u in range(v):
                L.append(r"\fill[teal!35, draw=teal!70!black, line width=0.4pt] (%s,%s) rectangle (%s,%s);" % (fmt(x + 0.04), fmt(base + u * s), fmt(x + w - 0.04), fmt(base + (u + 1) * s)))
            L.append(r"\node[font=\tiny, text=muted, anchor=north] at (%s,%s) {$%d$};" % (fmt(x + w / 2), fmt(base - 0.02), v))
        L.append(r"\draw[muted, line width=0.4pt] (%s,%s) -- (%s,%s);" % (fmt(x0 - 0.03), fmt(base), fmt(x0 + T * w + 0.03), fmt(base)))
        L.append(r"\node[font=\scriptsize, anchor=north] at (%s,%s) {$%d$ pairs};" % (fmt(x0 + T * w / 2), fmt(base - 0.3), pr))
        x0 += T * w + gap
    # the average N/T, dashed, over the even case
    L.append(r"\draw[accent, dashed, line width=0.6pt] (%s,%s) -- (%s,%s) node[left, font=\tiny, text=accent!90!black] {$N/T$};" % (fmt(T * w + 0.05), fmt(base + N / T * s), fmt(-0.05), fmt(base + N / T * s)))
    L.append(r"\node[font=\scriptsize, anchor=south west] at (0,0.05) {$N=%d$ completions on $T=%d$ frames:};" % (N, T))
    return tikz(L), {}


def fact2a():
    """Fact 2(a) on the example: A blown up with q = 2, a copy of H = R with row 1 doubled, the
    kept lines (one per row and column of R) in distinct blocks, and the copy of R in A they come from."""
    R, Hr, A = P, [[1, 0], [1, 0], [1, 1]], A_EX
    assert reduce_pattern(Hr) == R
    q, n = 2, len(A)
    k, l, k0, l0 = len(Hr), len(Hr[0]), len(R), len(R[0])
    Aq = blow_up(A, q)
    copies_R, copies_H = copies(R, A), copies(Hr, Aq)
    shown = ((0, 1, 2), (0, 4))
    assert shown in copies_H
    kept = ((0, 2), (0, 4))                          # one row per run of equal rows of H; all columns
    from_A = (tuple(r // q for r in kept[0]), tuple(c // q for c in kept[1]))
    assert len(set(from_A[0])) == k0 and len(set(from_A[1])) == l0 and from_A in copies_R
    assert [[Aq[i][j] for j in kept[1]] for i in kept[0]] == R
    # every copy of H in A^(q): its kept lines lie in distinct blocks and come from a copy of R in A
    def kept_of(c):
        rows, cols = c
        runs_r = [a for a in range(k) if a == 0 or Hr[a] != Hr[a - 1]]
        runs_c = [b for b in range(l) if b == 0 or any(Hr[a][b] != Hr[a][b - 1] for a in range(k))]
        return tuple(rows[a] for a in runs_r), tuple(cols[b] for b in runs_c)
    for c in copies_H:
        kr, kc = kept_of(c)
        assert len({r // q for r in kr}) == k0 and len({x // q for x in kc}) == l0
        assert (tuple(r // q for r in kr), tuple(x // q for x in kc)) in copies_R
    nR, nH = len(copies_R), len(copies_H)
    per = q ** (k0 + l0) * (q * n) ** (k + l - k0 - l0)
    assert nH <= nR * per and nH * n ** (k0 + l0) <= nR * (q * n) ** (k + l)
    s = 0.4
    gA, gQ = Grid(s), Grid(s, x0=1.85)
    lines = [r"\useasboundingbox (-0.4,0.75) rectangle (4.35,-2.6);"]
    lines.append(r"\node[font=\scriptsize, anchor=south] at (%s,0.35) {$A$};" % fmt(1.5 * s))
    lines.append(r"\node[font=\scriptsize, anchor=south] at (%s,0.35) {$A^{(2)}$};" % fmt(1.85 + 3 * s))
    lines += only("3-", gA.fill(copy_cells(from_A), "teal!30"))
    lines += only("2-", gQ.fill(copy_cells(shown), "accent!32"))
    lines += gA.lines(3, 3) + gA.digits(A, "font=\\scriptsize") + gA.labels(["$1$", "$2$", "$3$"], ["$1$", "$2$", "$3$"], "font=\\tiny")
    lines += gQ.lines(6, 6) + gQ.digits(Aq, "font=\\scriptsize")
    lines += gQ.labels(["$%d$" % (i + 1) for i in range(6)], ["$%d$" % (j + 1) for j in range(6)], "font=\\tiny")
    for kk in range(0, 7, 2):
        lines.append(r"\draw[ink, line width=0.7pt] (%s,0) -- (%s,%s);" % (fmt(1.85 + kk * s), fmt(1.85 + kk * s), fmt(-6 * s)))
        lines.append(r"\draw[ink, line width=0.7pt] (1.85,%s) -- (%s,%s);" % (fmt(-kk * s), fmt(1.85 + 6 * s), fmt(-kk * s)))
    lines += only("3-", gQ.outline(copy_cells(kept), "teal!70!black, very thick", pad=0.04)
                  + gA.outline(copy_cells(from_A), "teal!70!black, very thick", pad=0.04))
    one = lambda xs: ",".join(str(v + 1) for v in xs)
    numbers = {"F2A_NR": str(nR), "F2A_NH": str(nH), "F2A_PER": "%d^{%d}\\cdot%d^{%d}" % (q, k0 + l0, q * n, k + l - k0 - l0),
               "F2A_BOUND": str(nR * per), "F2A_ROWS": one(shown[0]), "F2A_COLS": one(shown[1]),
               "F2A_KROWS": one(kept[0]), "F2A_KCOLS": one(kept[1]), "F2A_AROWS": one(from_A[0]), "F2A_ACOLS": one(from_A[1])}
    return tikz(lines), numbers


def fact2b():
    """Fact 2(b) on the example with q = 3: change floor(q^2 D_R(A) / 2) entries of A^(q), all in the
    block of A(1,1) (the entry every copy of R uses), pick one line per block, and count."""
    R, Hr, A = P, [[1, 0], [1, 0], [1, 1]], A_EX
    q, n = 3, len(A)
    k0, l0 = len(R), len(R[0])
    Aq = blow_up(A, q)
    dR = distance(R, A)
    budget = q * q * dR // 2
    changed = [(0, 0), (1, 1), (2, 2), (0, 1)]
    assert len(changed) == budget == 4 and all(i // q == 0 and j // q == 0 for i, j in changed)
    Bp = flipped(Aq, changed)
    # all picks: one row per block of rows, one column per block of columns
    picks = list(itertools.product(*[range(b * q, (b + 1) * q) for b in range(n)]))
    assert len(picks) == q ** n
    good = 0
    expected_changes = 0
    for rows in picks:
        for cols in picks:
            Bsub = [[Bp[r][c] for c in cols] for r in rows]
            diff = sum(Bsub[a][b] != A[a][b] for a in range(n) for b in range(n))
            expected_changes += diff
            if diff < dR:
                assert copies(R, Bsub)
            if copies(R, Bsub):
                good += 1
    total = len(picks) ** 2
    assert expected_changes * 2 <= dR * total                        # on average at most D_R(A)/2 changes
    assert 2 * good >= total
    nRp = len(copies(R, Bp))
    assert 2 * nRp >= q ** (k0 + l0)
    nHp = len(copies(Hr, Bp))
    assert nHp > 0                                                   # B' still contains H
    shown_rows, shown_cols = (1, 4, 7), (2, 3, 8)
    assert all((r, c) not in changed for r in shown_rows for c in shown_cols)
    Bshown = [[Bp[r][c] for c in shown_cols] for r in shown_rows]
    assert Bshown == A
    s = 0.3
    gQ, gB = Grid(s), Grid(0.4, x0=3.35, y0=-0.75)
    L = [r"\useasboundingbox (-0.4,0.75) rectangle (4.75,%s);" % fmt(-9 * s - 0.15)]
    L.append(r"\node[font=\scriptsize, anchor=south] at (%s,0.32) {$B'$};" % fmt(4.5 * s))
    L += only("2-", gQ.fill([(r, c) for r in shown_rows for c in range(9)] + [(r, c) for r in range(9) for c in shown_cols if r not in shown_rows], "teal!18"))
    L += only("2-", gQ.fill([(r, c) for r in shown_rows for c in shown_cols], "teal!45"))
    L += gQ.fill(changed, "green!40")
    L += gQ.lines(9, 9, "gray!40") + gQ.digits(Bp, "font=\\tiny")
    for kk in range(0, 10, 3):
        L.append(r"\draw[ink, line width=0.7pt] (%s,0) -- (%s,%s);" % (fmt(kk * s), fmt(kk * s), fmt(-9 * s)))
        L.append(r"\draw[ink, line width=0.7pt] (0,%s) -- (%s,%s);" % (fmt(-kk * s), fmt(9 * s), fmt(-kk * s)))
    L += gQ.labels(["$%d$" % (i + 1) for i in range(9)], ["$%d$" % (j + 1) for j in range(9)], "font=\\tiny")
    pickedB = gB.lines(3, 3) + gB.digits(Bshown, "font=\\scriptsize")
    pickedB.append(r"\node[font=\scriptsize, anchor=south] at (%s,%s) {$B$};" % (fmt(3.35 + 0.6), fmt(-0.75 + 0.05)))
    pickedB.append(r"\draw[-{Stealth[length=2mm]}, teal!70!black, thick] (%s,%s) -- (%s,%s);" % (fmt(9 * s + 0.1), fmt(-1.35), fmt(3.3), fmt(-1.35)))
    L += only("2-", pickedB)
    one = lambda xs: ",".join(str(v + 1) for v in xs)
    numbers = {"F2B_DR": str(dR), "F2B_BUDGET": str(budget), "F2B_GOOD": str(good), "F2B_TOTAL": str(total),
               "F2B_NRP": str(nRp), "F2B_HALF": r"\tfrac12\cdot %d^{%d}" % (q, k0 + l0), "F2B_NHP": str(nHp),
               "F2B_PR": one(shown_rows), "F2B_PC": one(shown_cols), "F2B_EXP": r"\tfrac{%d}{%d}" % (budget, q * q)}
    return tikz(L), numbers


def core_parts(h):
    """The tree and dummy part of A_h: the blocks of its rows and columns, and its entries."""
    t = TreeMatrix(h)
    rpos, cpos = t.positions("row"), t.positions("column")
    rows = [k for k, b in enumerate(rpos) if b.kind != "anchor"]
    cols = [k for k, b in enumerate(cpos) if b.kind != "anchor"]
    full = t.full_matrix_rows()
    base = [[(full[r] >> c) & 1 for c in cols] for r in rows]
    return t, [rpos[r] for r in rows], [cpos[c] for c in cols], base


def bodies_of(t, rb, cb, B):
    """The bodies of B (a matrix on the tree and dummy part): (mode, r1, r2, c1, c2) reading P."""
    N = len(B)
    out = []
    for mode in t.modes:
        R1 = [i for i in range(N) if t.designated_role(rb[i], mode, "row") == 1]
        R2 = [i for i in range(N) if t.designated_role(rb[i], mode, "row") == 2]
        C1 = [j for j in range(N) if t.designated_role(cb[j], mode, "column") == 1]
        C2 = [j for j in range(N) if t.designated_role(cb[j], mode, "column") == 2]
        for r1 in R1:
            for r2 in R2:
                for c1 in C1:
                    for c2 in C2:
                        if r1 < r2 and c1 < c2 and (B[r1][c1], B[r1][c2], B[r2][c1], B[r2][c2]) == (1, 0, 1, 1):
                            out.append((mode, r1, r2, c1, c2))
    return out


# ---------------------------------------------------------------- where a copy of H can sit, in A_1

def host_view():
    """All of A_1, each anchor shrunk to four rows and four columns (groups 1 and 2, and groups
    3-64 as one block of two), the tree and dummy part at full size; overlays: one mode's block,
    its marks, the body, the whole copy, all bodies."""
    h = 1
    t = TreeMatrix(h)
    modes = t.modes
    n_modes = len(modes)

    def units(blocks):
        out = []
        for m in range(n_modes):
            out += [("anchor", Block("anchor", mode_index=m, group=1), 1), ("anchor", Block("anchor", mode_index=m, group=2), 2),
                    ("anchor", Block("anchor", mode_index=m, group=3), 0), ("anchor", Block("anchor", mode_index=m, group=3), 0)]
        for b in blocks:
            if b.kind != "anchor":
                out += [(b.kind, b, None)] * t.block_size(b)
        return out

    ru, cu = units(t.row_blocks), units(t.column_blocks)
    N, base0 = len(ru), 4 * n_modes

    def value(i, j):
        (rk, rb_, rp), (ck, cb_, cp) = ru[i], cu[j]
        if rk == ck == "anchor" and rb_.mode_index == cb_.mode_index and rp == 0 and cp == 0:
            return 2  # groups 3-64 against themselves: a blown-up copy of S
        return t.entry(rb_, cb_)

    V = [[value(i, j) for j in range(N)] for i in range(N)]
    mode_index = next(k for k, md in enumerate(modes) if md.kind == "W" and md.level == h and md.sign == "-" and md.parity == 0)
    first_unit = lambda units_, test: next(i for i, u in enumerate(units_) if test(u))
    r1 = first_unit(ru, lambda u: u[0] == "leaf" and u[1].node == 0)
    r2 = first_unit(ru, lambda u: u[0] == "dummy")
    c1 = first_unit(cu, lambda u: u[0] == "leaf" and u[1].node == 0)
    c2 = first_unit(cu, lambda u: u[0] == "variable" and u[1].level == h - 1 and u[1].sign == "-")
    assert [[V[r1][c1], V[r1][c2]], [V[r2][c1], V[r2][c2]]] == P
    # the copy itself, in the full host: one position from each group of the mode, then the body
    full = t.full_matrix_rows()
    rpos, cpos = t.positions("row"), t.positions("column")
    first_pos = lambda pos, test: next(k for k, b in enumerate(pos) if test(b))
    rows = [first_pos(rpos, lambda b, g=g: b.kind == "anchor" and b.mode_index == mode_index and b.group == g) for g in range(1, 65)]
    cols = [first_pos(cpos, lambda b, g=g: b.kind == "anchor" and b.mode_index == mode_index and b.group == g) for g in range(1, 65)]
    rows += [first_pos(rpos, lambda b: b.kind == "leaf" and b.node == 0), first_pos(rpos, lambda b: b.kind == "dummy")]
    cols += [first_pos(cpos, lambda b: b.kind == "leaf" and b.node == 0),
             first_pos(cpos, lambda b: b.kind == "variable" and b.level == h - 1 and b.sign == "-")]
    assert [[(full[r] >> c) & 1 for c in cols] for r in rows] == pattern_matrix()
    # the marks of this mode, against the tree and dummy part
    g1, g2 = 4 * mode_index, 4 * mode_index + 1
    marks1 = [(g1, j) for j in range(base0, N) if V[g1][j] == 1] + [(i, g1) for i in range(base0, N) if V[i][g1] == 1]
    marks2 = [(g2, j) for j in range(base0, N) if V[g2][j] == 1] + [(i, g2) for i in range(base0, N) if V[i][g2] == 1]
    assert sorted(marks1) == sorted([(g1, c1), (r1, g1)])
    role = lambda u, axis: t.designated_role(u[1], modes[mode_index], axis) if u[0] != "anchor" else 0
    assert all(role(cu[j], "column") == 1 for _, j in marks1 if j >= base0) and all(role(ru[i], "row") == 1 for i, _ in marks1 if i >= base0)
    assert all(role(cu[j], "column") == 2 for _, j in marks2 if j >= base0) and all(role(ru[i], "row") == 2 for i, _ in marks2 if i >= base0)
    # all bodies of A_1, from the tree and dummy part
    tt, rb, cb, base = core_parts(h)
    bodies = bodies_of(tt, rb, cb, base)
    assert len(bodies) == 2 * t.leaf_count ** 2
    body_cells = sorted({(base0 + a, base0 + b) for _, x1, x2, y1, y2 in bodies for a in (x1, x2) for b in (y1, y2)})

    # the anchors drawn small, the tree and dummy part large (where the bodies are)
    size = [0.105 if u[0] == "anchor" else 0.30 for u in ru]
    assert size == [0.105 if u[0] == "anchor" else 0.30 for u in cu]
    pos = [0.0]
    for z in size:
        pos.append(pos[-1] + z)
    W = pos[-1]
    X = lambda j: pos[j]
    Y = lambda i: -pos[i]
    rect = lambda i, j, pad=0.0: r"(%s,%s) rectangle (%s,%s)" % (fmt(X(j) + pad), fmt(Y(i) - pad), fmt(X(j) + size[j] - pad), fmt(Y(i) - size[i] + pad))
    center = lambda i, j: (X(j) + size[j] / 2, Y(i) - size[i] / 2)
    lines = [r"\useasboundingbox (-1.05,0.95) rectangle (%s,%s);" % (fmt(W + 0.2), fmt(-W - 0.2))]
    band = "accent!14"
    mode_units = range(4 * mode_index, 4 * mode_index + 4)
    row_band = lambda i: r"\fill[%s] (0,%s) rectangle (%s,%s);" % (band, fmt(Y(i)), fmt(W), fmt(Y(i) - size[i]))
    col_band = lambda j: r"\fill[%s] (%s,0) rectangle (%s,%s);" % (band, fmt(X(j)), fmt(X(j) + size[j]), fmt(-W))
    lines += only("2-", [row_band(i) for i in mode_units] + [col_band(j) for j in mode_units])
    lines += only("5-", [row_band(i) for i in (r1, r2)] + [col_band(j) for j in (c1, c2)])
    # the entries
    for i in range(N):
        for j in range(N):
            if V[i][j] == 1:
                lines.append(r"\fill[ink] %s;" % rect(i, j))
            elif V[i][j] == 2 and ru[i - 1][2] != 0 and cu[j - 1][2] != 0:
                x0, y0, d = X(j), Y(i), size[i] + size[i + 1]
                lines.append(r"\fill[ink] (%s,%s) rectangle (%s,%s);" % (fmt(x0), fmt(y0), fmt(x0 + d), fmt(y0 - d)))
                lines.append(r"\draw[paper, line width=0.4pt] (%s,%s) -- (%s,%s);" % (fmt(x0), fmt(y0), fmt(x0 + d), fmt(y0 - d)))
            if V[i][j] == 0 and i >= base0 and j >= base0:
                x, y = center(i, j)
                lines.append(r"\node[font=\tiny, text=muted] at (%s,%s) {0};" % (fmt(x), fmt(y)))
            elif V[i][j] == 1 and i >= base0 and j >= base0:
                x, y = center(i, j)
                lines.append(r"\node[font=\tiny, text=paper] at (%s,%s) {1};" % (fmt(x), fmt(y)))
    # block lines: between modes, around the tree part, between tree blocks
    for k in range(1, n_modes + 1):
        z = pos[4 * k]
        lines.append(r"\draw[muted!60, line width=0.3pt] (0,%s) -- (%s,%s);" % (fmt(-z), fmt(W), fmt(-z)))
        lines.append(r"\draw[muted!60, line width=0.3pt] (%s,0) -- (%s,%s);" % (fmt(z), fmt(z), fmt(-W)))
    for i in range(base0 + 1, N):
        if ru[i][1] != ru[i - 1][1]:
            lines.append(r"\draw[rulecol, line width=0.4pt] (%s,%s) -- (%s,%s);" % (fmt(pos[base0]), fmt(Y(i)), fmt(W), fmt(Y(i))))
        if cu[i][1] != cu[i - 1][1]:
            lines.append(r"\draw[rulecol, line width=0.4pt] (%s,%s) -- (%s,%s);" % (fmt(X(i)), fmt(-pos[base0]), fmt(X(i)), fmt(-W)))
    lines.append(r"\draw[ink, line width=0.6pt] (0,0) rectangle (%s,%s);" % (fmt(W), fmt(-W)))
    lines.append(r"\draw[ink, line width=0.6pt] (%s,%s) rectangle (%s,%s);" % (fmt(pos[base0]), fmt(-pos[base0]), fmt(W), fmt(-W)))
    # labels: the modes on the left, the tree's rows and columns
    sub = lambda md: "%s_{%d%s}^{%s}" % (md.kind, md.level, "" if md.parity is None else ",%d" % md.parity, md.sign)
    for m, md in enumerate(modes):
        lines.append(r"\node[font=\tiny, anchor=east, inner sep=1pt] at (-0.04,%s) {$%s$};" % (fmt(-(pos[4 * m] + pos[4 * m + 4]) / 2), sub(md)))
    def row_label(u):
        b = u[1]
        return "R_*" if u[0] == "dummy" else "r_{%d}" % b.node if u[0] == "leaf" else "R_{%d}^{%s}" % (b.level, b.sign)
    def col_label(u):
        b = u[1]
        return "C_*" if u[0] == "dummy" else "c_{%d}" % b.node if u[0] == "leaf" else "C_{%d}^{%s}" % (b.level, b.sign)
    i = base0
    while i < N:
        k = i
        while k + 1 < N and ru[k + 1][1] == ru[i][1]:
            k += 1
        lines.append(r"\node[font=\tiny, anchor=east, inner sep=1pt] at (-0.04,%s) {$%s$};" % (fmt(-(pos[i] + pos[k + 1]) / 2), row_label(ru[i])))
        i = k + 1
    j = base0
    while j < N:
        k = j
        while k + 1 < N and cu[k + 1][1] == cu[j][1]:
            k += 1
        lines.append(r"\node[font=\tiny, anchor=south, inner sep=1pt] at (%s,0.02) {$%s$};" % (fmt((pos[j] + pos[k + 1]) / 2), col_label(cu[j])))
        j = k + 1
    lines.append(r"\node[font=\scriptsize, anchor=south] at (%s,0.32) {anchors};" % fmt(pos[base0] / 2))
    lines.append(r"\node[font=\scriptsize, anchor=south] at (%s,0.32) {tree part and dummies};" % fmt((pos[base0] + W) / 2))
    # step 2: frame the mode's block
    a0, a1 = pos[4 * mode_index], pos[4 * mode_index + 4]
    lines += only("2-", [r"\draw[accent, very thick] (%s,%s) rectangle (%s,%s);" % (fmt(a0), fmt(-a0), fmt(a1), fmt(-a1))])
    # step 3: the marks (teal: group 1, first rows and columns; amber: group 2, second ones)
    first, second = "teal!80!black", "orange!70!yellow!90!black"
    lines += only("3-", [r"\draw[%s, line width=1.1pt] %s;" % (first, rect(i, j)) for i, j in marks1]
                  + [r"\draw[%s, line width=1.1pt] %s;" % (second, rect(i, j)) for i, j in marks2])
    tick = []
    for i in range(base0, N):
        r = role(ru[i], "row")
        if r:
            tick.append(r"\fill[%s] (%s,%s) rectangle (%s,%s);" % (first if r == 1 else second, fmt(W + 0.04), fmt(Y(i) - 0.02), fmt(W + 0.14), fmt(Y(i) - size[i] + 0.02)))
    for j in range(base0, N):
        c = role(cu[j], "column")
        if c:
            tick.append(r"\fill[%s] (%s,%s) rectangle (%s,%s);" % (first if c == 1 else second, fmt(X(j) + 0.02), fmt(-W - 0.04), fmt(X(j) + size[j] - 0.02), fmt(-W - 0.14)))
    lines += only("3-", tick)
    # step 4: the body
    circles = []
    for (i, j) in [(r1, c1), (r1, c2), (r2, c1), (r2, c2)]:
        x, y = center(i, j)
        circles.append(r"\draw[accent, line width=1.3pt] (%s,%s) circle (%s);" % (fmt(x), fmt(y), fmt(0.6 * size[i])))
    lines += only("4-5", circles)
    # step 6: every body of A_1 outlined; the leaf cells circled
    lines += only("6", [r"\draw[accent, line width=1.1pt] %s;" % rect(i, j, 0.035) for i, j in body_cells])
    leaf_cells = [(base0 + a, base0 + b) for a in range(len(rb)) for b in range(len(cb)) if rb[a].kind == "leaf" and cb[b].kind == "leaf" and rb[a].node == cb[b].node]
    lines += only("6", [r"\draw[violet, line width=1.3pt] (%s,%s) circle (%s);" % (fmt(center(i, j)[0]), fmt(center(i, j)[1]), fmt(0.62 * size[i])) for i, j in leaf_cells])
    return tikz(lines), modes[mode_index], len(bodies)


# ---------------------------------------------------------------- why S cannot hide in the tree part (A_2)

def words_view():
    h = 2
    t, rb, cb, base = core_parts(h)
    N = len(base)
    firsts = [j for j in range(N) if j == 0 or cb[j] != cb[j - 1]]

    def words_on(cs):
        cs = sorted(cs)
        return {"".join(str(base[i][c]) for c in cs) for i in range(N)}

    best, arg = -1, None
    for combo in itertools.combinations(firsts, 5):
        k = len(words_on(combo))
        if k > best:
            best, arg = k, list(combo)
    assert best == 9, best
    found = words_on(arg)
    S = anchor_matrix()
    corner = ["".join(str(S[u][v]) for v in range(59, 64)) for u in range(32, 64)]
    assert corner == sorted(set(corner)) and len(corner) == 32 and found <= set(corner)

    s = 0.128
    lines = [r"\useasboundingbox (-0.45,0.45) rectangle (6.6,%s);" % fmt(-32 * s - 0.55)]
    # S's corner: 32 rows x 5 columns
    gS = Grid(s)
    lines.append(r"\node[font=\tiny, anchor=south] at (%s,0.02) {$S$};" % fmt(2.5 * s))
    lines.append(r"\node[font=\tiny, anchor=east] at (-0.03,%s) {33};" % fmt(-0.5 * s))
    lines.append(r"\node[font=\tiny, anchor=east] at (-0.03,%s) {64};" % fmt(-31.5 * s))
    for u, w in enumerate(corner):
        for v, bit in enumerate(w):
            if bit == "1":
                x0, y0 = v * s, -u * s
                rect = r"(%s,%s) rectangle (%s,%s)" % (fmt(x0), fmt(y0), fmt(x0 + s), fmt(y0 - s))
                if w in found:
                    lines.append(r"\fill[ink] %s;" % rect)
                else:
                    lines += only("1-2", [r"\fill[ink] %s;" % rect])
                    lines += only("3-", [r"\fill[ink!18] %s;" % rect])
        if w in found:
            lines += only("3-", [r"\fill[accent] (%s,%s) rectangle (%s,%s);" % (fmt(5 * s + 0.04), fmt(-u * s - 0.02), fmt(5 * s + 0.12), fmt(-(u + 1) * s + 0.02))])
    lines.append(r"\draw[muted, line width=0.4pt] (0,0) rectangle (%s,%s);" % (fmt(5 * s), fmt(-32 * s)))
    lines.append(r"\node[font=\tiny, align=center, anchor=north] at (%s,%s) {rows 33--64,\\ columns 60--64};" % (fmt(2.5 * s), fmt(-32 * s - 0.05)))
    # the tree and dummy part of A_2, and its rows read on the five columns
    x0 = 1.35
    gT = Grid(s, x0=x0)
    lines += only("2-", [r"\fill[teal!30] (%s,0) rectangle (%s,%s);" % (fmt(x0 + j * s), fmt(x0 + (j + 1) * s), fmt(-N * s)) for j in arg])
    for i in range(N):
        for j in range(N):
            if base[i][j]:
                lines.append(r"\fill[ink] (%s,%s) rectangle (%s,%s);" % (fmt(x0 + j * s), fmt(-i * s), fmt(x0 + (j + 1) * s), fmt(-(i + 1) * s)))
    lines += only("2-", [r"\draw[teal!80!black, line width=0.6pt] (%s,0) rectangle (%s,%s);" % (fmt(x0 + j * s), fmt(x0 + (j + 1) * s), fmt(-N * s)) for j in arg])
    lines.append(r"\draw[muted, line width=0.4pt] (%s,0) rectangle (%s,%s);" % (fmt(x0), fmt(x0 + N * s), fmt(-N * s)))
    lines.append(r"\node[font=\tiny, align=center, anchor=north] at (%s,%s) {tree and dummy part of $A_2$};" % (fmt(x0 + N * s / 2), fmt(-N * s - 0.05)))
    xs = x0 + N * s + 0.35
    strip = []
    for i in range(N):
        for k, j in enumerate(sorted(arg)):
            if base[i][j]:
                strip.append(r"\fill[ink] (%s,%s) rectangle (%s,%s);" % (fmt(xs + k * s), fmt(-i * s), fmt(xs + (k + 1) * s), fmt(-(i + 1) * s)))
    strip.append(r"\draw[teal!80!black, line width=0.6pt] (%s,0) rectangle (%s,%s);" % (fmt(xs), fmt(xs + 5 * s), fmt(-N * s)))
    strip.append(r"\node[font=\tiny, align=center, anchor=north] at (%s,%s) {its rows on\\ the 5 columns};" % (fmt(xs + 2.5 * s), fmt(-N * s - 0.05)))
    lines += only("2-", strip)
    return tikz(lines), best


# ---------------------------------------------------------------- motivation: testing by sampling

def motivation_sample():
    """A random 12 x 12 matrix (seed 1) and a random-looking sample of 2 rows and 2 columns that
    reads H = P. Returns the picture and the counts the slide states."""
    import random
    rng = random.Random(1)
    n = 12
    A = [[1 if rng.random() < 0.5 else 0 for _ in range(n)] for _ in range(n)]
    found = copies(P, A)
    total = math.comb(n, 2) ** 2
    assert (len(found), total) == (261, 4356)
    rows, cols = next((r, c) for r, c in sorted(found) if r[1] - r[0] >= 4 and c[1] - c[0] >= 4 and r[0] >= 2 and c[0] >= 2)
    read = [[A[i][j] for j in cols] for i in rows]
    assert read == P
    tries = math.ceil(total / len(found))
    s = 0.24
    g = Grid(s)
    W = n * s
    L = [r"\useasboundingbox (-0.1,0.55) rectangle (%s,%s);" % (fmt(W + 2.1), fmt(-W - 0.1))]
    L.append(r"\node[font=\scriptsize, anchor=south] at (%s,0.08) {a large matrix $A$};" % fmt(W / 2))
    L += only("2-", [r"\fill[teal!22] (0,%s) rectangle (%s,%s);" % (fmt(-i * s), fmt(W), fmt(-(i + 1) * s)) for i in rows]
              + [r"\fill[teal!22] (%s,0) rectangle (%s,%s);" % (fmt(j * s), fmt((j + 1) * s), fmt(-W)) for j in cols])
    for i in range(n):
        for j in range(n):
            if A[i][j]:
                a, b, c, d = g.rect(i, j, 0.035)
                L.append(r"\fill[ink!80] (%s,%s) rectangle (%s,%s);" % (fmt(a), fmt(b), fmt(c), fmt(d)))
    L.append(r"\draw[ink, line width=0.5pt] (0,0) rectangle (%s,%s);" % (fmt(W), fmt(-W)))
    L += only("2-", g.outline([(i, j) for i in rows for j in cols], "accent, line width=1.2pt", pad=-0.01))
    # the pattern, and on step 2 what the sample reads
    h = Grid(0.42, x0=W + 0.75, y0=-0.55)
    L.append(r"\node[font=\scriptsize, anchor=south] at (%s,%s) {pattern $H$};" % (fmt(W + 0.75 + 0.42), fmt(-0.5)))
    L += h.lines(2, 2) + h.digits(P, "font=\\scriptsize")
    rd = Grid(0.42, x0=W + 0.75, y0=-2.25)
    L += only("2-", [r"\node[font=\scriptsize, anchor=south, align=center] at (%s,%s) {the sample\\[-2pt] reads};" % (fmt(W + 0.75 + 0.42), fmt(-2.2))]
              + [r"\fill[accent!20] (%s,%s) rectangle (%s,%s);" % (fmt(W + 0.75), fmt(-2.25), fmt(W + 0.75 + 0.84), fmt(-2.25 - 0.84))]
              + rd.lines(2, 2) + rd.digits(read, "font=\\scriptsize"))
    pic = tikz(L)
    numbers = {"MOT_N": str(len(found)), "MOT_TOTAL": str(total), "MOT_TRIES": str(tries)}
    return pic, numbers


# ---------------------------------------------------------------- the Lean formalization (repository mathathon-costco)

# Quoted verbatim from the repository's Lean files; checked against them when the repository is found.
LEAN_SNIPPETS = {
    "defs": ("lean/OrderedRemoval/Statements.lean", [
        "abbrev BMat (a b : ℕ) := Fin a → Fin b → Bool",
        "def IsCopy {k l n m : ℕ} (H : BMat k l) (A : BMat n m) (r : Fin k → Fin n) (c : Fin l → Fin m) :\n"
        "    Prop :=\n"
        "  StrictMono r ∧ StrictMono c ∧ ∀ i j, A (r i) (c j) = H i j",
        "noncomputable def editDist {k l n m : ℕ} (H : BMat k l) (A : BMat n m) : ℕ :=\n"
        "  sInf {d | ∃ B : BMat n m, Free H B ∧ hamming A B = d}",
        "def PolyRemoval {a b : ℕ} (H : BMat a b) : Prop :=\n"
        "  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧\n"
        "    ∀ (n : ℕ) (A : BMat n n) (ε : ℝ), 0 < ε → ε ≤ 1 →\n"
        "      ε * (n : ℝ) ^ 2 ≤ (editDist H A : ℝ) →\n"
        "        c * ε ^ C * (n : ℝ) ^ (a + b) ≤ (copyCount H A : ℝ)",
    ]),
    "directsum": ("lean/OrderedRemoval/Statements.lean", [
        "theorem editDist_blockDiag {k l p q n : ℕ} (H : BMat k l) (hH : NoZeroLine H)\n"
        "    (hk : 0 < k) (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)\n"
        "    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j)) (A : BMat n n) :\n"
        "    editDist (blockDiag H Z) (blockDiag A (blowup Z n)) = editDist H A",
        "theorem not_polyRemoval_blockDiag {k l p q : ℕ} (H : BMat k l) (hH : NoZeroLine H)\n"
        "    (Z : BMat p q) (hp : 0 < p) (hq : 0 < q)\n"
        "    (hZ : Function.Injective Z ∨ Function.Injective (fun j i => Z i j))\n"
        "    (hcounter : ¬ PolyRemoval H) :\n"
        "    ¬ PolyRemoval (blockDiag H Z)",
    ]),
    "uncond": ("lean-unconditional/OrderedRemoval/Unconditional.lean", [
        "theorem oai_not_polyRemoval : ¬ PolyRemoval (fixedH : BMat 66 66)",
        "theorem infinitely_many_counterexamples :\n"
        "    ∃ f : ℕ → Pattern, Function.Injective f ∧\n"
        "      ∀ t, NoZeroLine (f t).2 ∧ ¬ PolyRemoval (f t).2",
    ]),
}

# Facts about the repository that the Lean slides state; checked against it when it is found.
LEAN_FACTS = {"LEAN_OAI_FILES": 61, "LEAN_BRIDGE": 8, "LEAN_STMT_LINES": 4059, "LEAN_AUDIT_DECLS": 1803,
              "LEAN_OAI_COMMIT": "4eaee87"}
LEAN_KEYWORDS = ("noncomputable", "abbrev", "def", "theorem", "fun", "Prop")


def lean_repo():
    """The repository root: MATHATHON_REPO if set, else the folder above this one (slides/ inside it)."""
    import os
    root = Path(os.environ["MATHATHON_REPO"]) if os.environ.get("MATHATHON_REPO") else HERE.parent
    return root if (root / "lean" / "OrderedRemoval" / "Statements.lean").exists() else None


def check_lean():
    root = lean_repo()
    if root is None:
        print("note: Lean repository not found; the Lean snippets and facts were not checked")
        return
    for key, (path, snippets) in LEAN_SNIPPETS.items():
        text = (root / path).read_text(encoding="utf-8")
        for s in snippets:
            assert s in text, "Lean snippet not found verbatim in %s: %s" % (path, s.splitlines()[0])
    oai = sorted((root / "lean-unconditional" / "OAI" / "Combinatorics" / "MatrixRemoval").glob("*.lean"))
    assert len(oai) == LEAN_FACTS["LEAN_OAI_FILES"], len(oai)
    unc = (root / "lean-unconditional" / "OrderedRemoval" / "Unconditional.lean").read_text(encoding="utf-8")
    assert len(re.findall(r"^theorem ", unc, re.M)) == LEAN_FACTS["LEAN_BRIDGE"]
    stmt = (root / "lean" / "OrderedRemoval" / "Statements.lean").read_text(encoding="utf-8")
    assert stmt.count("\n") == LEAN_FACTS["LEAN_STMT_LINES"]
    report = (root / "lean-unconditional" / "results" / "REPORT.md").read_text(encoding="utf-8")
    assert "AUDIT_DECL_COUNT %d" % LEAN_FACTS["LEAN_AUDIT_DECLS"] in report and "AUDIT_BAD_COUNT 0" in report
    assert "Build completed successfully" in report
    assert LEAN_FACTS["LEAN_OAI_COMMIT"] in report
    print("checked the Lean snippets and facts against", root)


def lean_code(key, size="\\scriptsize"):
    """The snippets of LEAN_SNIPPETS[key] as a framed block of typewriter lines."""
    symbols = {"ℕ": r"$\mathbb{N}$", "ℝ": r"$\mathbb{R}$", "→": r"$\to$", "∀": r"$\forall$", "∃": r"$\exists$",
               "ε": r"$\varepsilon$", "≤": r"$\le$", "¬": r"$\neg$", "∧": r"$\wedge$", "∨": r"$\vee$",
               "↔": r"$\leftrightarrow$", "≠": r"$\ne$"}
    special = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "$": r"\$", "&": r"\&", "#": r"\#",
               "_": r"\_", "%": r"\%", "^": r"\^{}", "~": r"\~{}", " ": r"\ ", "|": r"\textbar{}"}

    def line(s):
        out = []
        for tok in re.split(r"(\w+)", s):
            if tok in LEAN_KEYWORDS:
                out.append(r"\textcolor{accent!85!black}{%s}" % tok)
            elif re.fullmatch(r"\w+", tok) and not any(ch in symbols for ch in tok):
                out.append(tok.replace("_", r"\_"))
            else:
                out.append("".join(symbols.get(ch, special.get(ch, ch)) for ch in tok))
        return "".join(out) if out else r"\ "

    _, snippets = LEAN_SNIPPETS[key]
    body = []
    for k, s in enumerate(snippets):
        if k:
            body.append(r"\vspace{0.35em}")
        body += [r"\mbox{%s}\par" % line(x) for x in s.split("\n")]
    for ch in "".join(s for s in snippets):
        assert ord(ch) < 128 or ch in symbols, "no LaTeX for %r" % ch
    return "\n".join([r"{\setlength{\fboxsep}{5pt}\fcolorbox{rulecol}{white}{\begin{minipage}{\dimexpr\linewidth-2\fboxsep-0.8pt\relax}",
                      r"\ttfamily%s\setlength{\parskip}{0pt}\setlength{\parindent}{0pt}\raggedright" % size]
                     + body + [r"\end{minipage}}}"])


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else DEFAULT_OUT
    parts = small_examples()
    parts["HPICTURE"] = h_picture()
    parts["TITLEPIC"] = h_picture(s=0.048, gap=0.1, labels=False)
    core_pic, counts, changed = core_frame()
    parts["CORE"] = core_pic
    for k, (c, ch) in enumerate(zip(counts, changed)):
        parts["CORE_BODIES_%d" % (k + 1)] = str(c)
        parts["CORE_CHANGED_%d" % (k + 1)] = str(ch)
    ds_pic, ds_numbers = direct_sum_example()
    parts["DIRECTSUM"] = ds_pic
    parts.update(ds_numbers)
    parts["DSPROOF1"], dsp_numbers = ds_proof_step1()
    parts.update(dsp_numbers)
    parts["DSPROOF2"] = ds_proof_step2()
    parts["DSPROOF3"] = ds_proof_step3()
    parts["RED"] = reduction_example()
    host_pic, host_mode, a1_bodies = host_view()
    parts["HOSTVIEW"], parts["A1_BODIES"] = host_pic, str(a1_bodies)
    words_pic, words_found = words_view()
    parts["WORDSVIEW"], parts["WORDS_FOUND"] = words_pic, str(words_found)
    for key, fn in [("F1PIC", fact1_frames), ("F1BARS", fact1_bars), ("F2APIC", fact2a), ("F2BPIC", fact2b)]:
        pic, nums = fn()
        parts[key] = pic
        parts.update(nums)
    pic, nums = motivation_sample()
    parts["MOTIVPIC"] = pic
    parts.update(nums)
    check_lean()
    for key in LEAN_SNIPPETS:
        parts["LEAN_" + key.upper()] = lean_code(key, "\\fontsize{7}{8.4}\\selectfont" if key == "defs" else "\\scriptsize")
    parts.update({k: str(v) for k, v in LEAN_FACTS.items()})
    text = TEMPLATE.read_text(encoding="utf-8")
    for key, value in parts.items():
        marker = "%%" + key + "%%"
        if marker not in text:
            if key.startswith(("CORE_BODIES_", "CORE_CHANGED_")):
                continue  # numbers the template may leave unused
            raise SystemExit("marker %s missing from the template" % marker)
        text = text.replace(marker, value)
    left = re.findall(r"%%[A-Z][A-Z0-9_]*%%", text)
    if left:
        raise SystemExit("unfilled markers: %s" % left)
    out.write_text(text, encoding="utf-8")
    print("wrote", out, "; A_1 bodies per step", counts, "changes", changed, "; direct sum copies", ds_numbers["DS_NH"], "->", ds_numbers["DS_NH2"])


if __name__ == "__main__":
    main()
