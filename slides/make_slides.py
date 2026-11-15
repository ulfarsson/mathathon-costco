"""Build the slides from slides-template.tex.

Every matrix, copy and count on the slides that is not plain text is computed here and checked
before it is drawn:
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
- the direct-sum example A^+ = [A 0; 0 J_3] for H' = [H 0; 0 (1)], by brute force;
- the reduction red(H) of the write-up's example.

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

def direct_sum_example():
    n = 3
    H2 = [[1, 0, 0], [1, 1, 0], [0, 0, 1]]  # [P 0; 0 (1)]
    Aplus = [A_EX[i] + [0] * n for i in range(n)] + [[0] * n + [1] * n for _ in range(n)]
    nh = len(copies(P, A_EX))
    nh2 = len(copies(H2, Aplus))
    assert (nh, nh2) == (3, 27) and nh2 <= (2 * n) ** 2 * nh
    shown = ((0, 1, 3), (0, 2, 3))
    assert shown in copies(H2, Aplus)
    fixed = flipped(Aplus, [(0, 0)])
    assert copies(H2, fixed) == []
    g = Grid(0.55)
    lines = []
    lines += g.fill([(i, j) for i in range(n) for j in range(n)], "accent!8")
    lines += g.fill([(i, j) for i in range(n, 2 * n) for j in range(n, 2 * n)], "gray!18")
    lines += only("2", g.fill(copy_cells(shown), "accent!35"))
    lines += only("3", g.fill([(0, 0)], "green!30"))
    lines += g.lines(2 * n, 2 * n, "gray!45")
    lines += only("1-2", g.digits(Aplus, "font=\\footnotesize"))
    lines += only("3", g.digits(fixed, "font=\\footnotesize"))
    lines.append(g.box(range(n), range(n), "accent, thick"))
    lines.append(g.box(range(n, 2 * n), range(n, 2 * n), "black!70, thick"))
    lines += g.labels(["$%d$" % (i + 1) for i in range(2 * n)], ["$%d$" % (j + 1) for j in range(2 * n)])
    return tikz(lines), nh, nh2


# ---------------------------------------------------------------- red(H)

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

def duplication_pictures():
    """(1) Fact 1 on the 3 x 3 example: frames of R = [1 0; 1 1] and their completing columns, and
    the copies of H' = R with column 2 doubled. (2) Fact 2: the example blown up with q = 2, a copy
    of H = R with row 1 doubled, its R-part in distinct blocks, and the copy of R it comes from."""
    R = P
    Hc = [[1, 0, 0], [1, 1, 1]]          # column 2 of R doubled
    Hr = [[1, 0], [1, 0], [1, 1]]        # row 1 of R doubled
    A = A_EX
    copies_R = copies(R, A)
    frames = {}
    for rows, cols in copies_R:
        frames.setdefault((rows, cols[0]), []).append(cols[1])
    assert frames == {((0, 1), 0): [1, 2], ((0, 2), 0): [2]}, frames
    copies_Hc = copies(Hc, A)
    # a copy of H' is a frame with two of its completing columns
    assert sorted(copies_Hc) == sorted((rows, (c0, a, b)) for (rows, c0), done in frames.items()
                                       for a, b in itertools.combinations(done, 2))
    assert copies_Hc == [((0, 1), (0, 1, 2))]

    # (1): the 3 x 3 example with the frames and their completions
    g = Grid(0.75)
    labels = g.labels(["$1$", "$2$", "$3$"], ["$1$", "$2$", "$3$"])
    lines = [r"\useasboundingbox (-0.45,0.4) rectangle (2.35,-2.35);"]
    lines += only("2-3", g.fill([(0, 0), (1, 0)], "accent!32") + g.fill([(0, 1), (1, 1), (0, 2), (1, 2)], "teal!28"))
    lines += only("4", g.fill([(0, 0), (2, 0)], "accent!32") + g.fill([(0, 2), (2, 2)], "teal!28"))
    lines += g.lines(3, 3) + g.digits(A) + labels
    lines += only("3", g.outline(copy_cells(copies_Hc[0]), "green!50!black, very thick", pad=0.05))
    dup1 = tikz(lines)

    # (2): the blow-up with q = 2
    q, n = 2, 3
    Aq = [[A[i // q][j // q] for j in range(n * q)] for i in range(n * q)]
    copies_Hr = copies(Hr, Aq)
    shown = ((0, 1, 2), (0, 4))
    assert shown in copies_Hr
    r_part = ((0, 2), (0, 4))                        # one row per run of equal rows of H
    from_A = ((0 // q, 2 // q), (0 // q, 4 // q))    # the blocks they lie in
    assert from_A == ((0, 1), (0, 2)) and from_A in copies_R
    assert [[Aq[i][j] for j in r_part[1]] for i in r_part[0]] == R
    # few stay few: N_H(A^(q)) / (qn)^(k+l) <= N_R(A) / n^(k0+l0)
    n_R, n_H = len(copies_R), len(copies_Hr)
    assert n_H * n ** 4 <= n_R * (q * n) ** 5, (n_H, n_R)
    # far stays far: the fewest changes that make A^(2) free of H, by search
    cells = [(i, j) for i in range(n * q) for j in range(n * q)]
    d_H = None
    for size in range(0, 4):
        for change in itertools.combinations(cells, size):
            if not copies(Hr, flipped(Aq, change)):
                d_H = size
                break
        if d_H is not None:
            break
    d_R = distance(R, A)
    assert d_R == 1 and d_H is not None and d_H >= q * q * d_R / 2, (d_H, d_R)
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
    for k in range(0, 7, 2):
        lines.append(r"\draw[ink, line width=0.7pt] (%s,0) -- (%s,%s);" % (fmt(1.85 + k * s), fmt(1.85 + k * s), fmt(-6 * s)))
        lines.append(r"\draw[ink, line width=0.7pt] (1.85,%s) -- (%s,%s);" % (fmt(-k * s), fmt(1.85 + 6 * s), fmt(-k * s)))
    lines += only("3-", gQ.outline(copy_cells(r_part), "teal!70!black, very thick", pad=0.04)
                  + gA.outline(copy_cells(from_A), "teal!70!black, very thick", pad=0.04))
    dup2 = tikz(lines)
    assert (q * q * d_R) % 2 == 0
    bound = q * q * d_R // 2                         # the slide's 1/2 * q^2 * D_R(A)
    assert d_H >= bound
    # N_H'(A) as a sum over the frames of (completions choose 2), in the order the slide names them
    binoms = "+".join(r"\binom{%d}{2}" % len(done) for done in frames.values())
    assert sum(math.comb(len(done), 2) for done in frames.values()) == len(copies_Hc)
    numbers = {"DUP_NR": str(n_R), "DUP_NHC": str(len(copies_Hc)), "DUP_NH2": str(n_H), "DUP_D2": str(d_H),
               "DUP_DR": str(d_R), "DUP_BOUND": str(bound), "DUP_BINOMS": binoms}
    return dup1, dup2, numbers


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
    ds_pic, nh, nh2 = direct_sum_example()
    parts["DIRECTSUM"] = ds_pic
    parts["DS_NH"], parts["DS_NH2"] = str(nh), str(nh2)
    parts["RED"] = reduction_example()
    host_pic, host_mode, a1_bodies = host_view()
    parts["HOSTVIEW"], parts["A1_BODIES"] = host_pic, str(a1_bodies)
    words_pic, words_found = words_view()
    parts["WORDSVIEW"], parts["WORDS_FOUND"] = words_pic, str(words_found)
    dup1, dup2, dup_numbers = duplication_pictures()
    parts["DUP1"], parts["DUP2"] = dup1, dup2
    parts.update(dup_numbers)
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
    print("wrote", out, "; A_1 bodies per step", counts, "changes", changed, "; direct sum copies", nh, "->", nh2)


if __name__ == "__main__":
    main()
