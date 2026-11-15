"""The pattern H and the host matrices A_h of OpenAI's preprint
"Polynomial removal fails for ordered binary matrices" (OpenAI, 2026-09-25),
https://github.com/openai/math/tree/main/preprints/Polynomial-removal-fails-for-ordered-binary-matrices-September-25-2026

Rebuilt from the definitions in its Section 2 (sections/02-construction.tex).

Paper notation -> code (the only place where indices are converted):
  S(u, v), 1 <= u, v <= 64         anchor_matrix()[u - 1][v - 1]
  H(i, j), 1 <= i, j <= 66         pattern_matrix()[i - 1][j - 1]
  mode V_i^+                       Mode("V", i, "+", None)
  mode W_{i,d}^-                   Mode("W", i, "-", d)
  anchor group R^_t(u), C^_t(v)    Block("anchor", mode_index=t, group=u)   (u, v 1-based)
  variable block R_i^s(p), C_i^s(p), i < h
                                   Block("variable", level=i, sign=s, node=p)
  leaf block R_h^+(p) = R_h^-(p)   Block("leaf", level=h, node=p)
  dummy block R_*, C_*             Block("dummy")

A matrix is a list of rows, each row a list of 0/1.  Axes are lists of
blocks in their order; positions are numbered from 0 along an axis.
"""

from dataclasses import dataclass
from typing import List, Optional, Tuple

ANCHOR_SIZE = 64  # s in the paper
PATTERN_SIZE = ANCHOR_SIZE + 2  # k in the paper


def five_bit_digit(word_index: int, bit: int) -> int:
    """eta_b(a) = floor(a / 2^(5-b)) mod 2, for 0 <= a < 32 and 1 <= b <= 5."""
    return (word_index >> (5 - bit)) & 1


def anchor_matrix() -> List[List[int]]:
    """The 64 x 64 anchor S, as defined in Section 2.1 (equation (2.1))."""
    rows = []
    for u in range(1, ANCHOR_SIZE + 1):
        row = []
        for v in range(1, ANCHOR_SIZE + 1):
            if 33 <= u <= 64 and 60 <= v <= 64:
                row.append(five_bit_digit(u - 33, v - 59))
            else:
                row.append(1 if u != v else 0)
        rows.append(row)
    return rows


def unit_marks(size: int):
    """The paper's marks: e_1 and e_2 on both axes, as
    (first row mark, second row mark, first column mark, second column mark)."""
    first = [1 if v == 1 else 0 for v in range(1, size + 1)]
    second = [1 if v == 2 else 0 for v in range(1, size + 1)]
    return (first, second, list(first), list(second))


def pattern_matrix(anchor: Optional[List[List[int]]] = None, marks=None) -> List[List[int]]:
    """H = [[S, e1, e2], [e1^T, 1, 0], [e2^T, 1, 1]], a 66 x 66 matrix for the
    paper's S; any s x s anchor (s >= 2) may be given instead, and other marks
    (row_first, row_second, column_first, column_second) in place of e1, e2:
    H = [[S, column_first, column_second], [row_first, 1, 0], [row_second, 1, 1]]."""
    if anchor is None:
        anchor = anchor_matrix()
    size = len(anchor)
    row_first, row_second, column_first, column_second = marks or unit_marks(size)
    rows = []
    for u in range(size):
        rows.append(list(anchor[u]) + [column_first[u], column_second[u]])
    rows.append(list(row_first) + [1, 0])
    rows.append(list(row_second) + [1, 1])
    return rows


BODY = [[1, 0], [1, 1]]  # P, the lower-right 2 x 2 block of H


@dataclass(frozen=True)
class Mode:
    kind: str  # "V" or "W"
    level: int  # i, 1 <= i <= h
    sign: str  # "+" or "-"
    parity: Optional[int]  # d for W modes, None for V modes

    def name(self) -> str:
        if self.kind == "V":
            return f"V_{self.level}^{self.sign}"
        return f"W_{{{self.level},{self.parity}}}^{self.sign}"


def modes(depth: int) -> List[Mode]:
    """The 6h modes in the paper's order: by level, then
    V^+, V^-, W_0^+, W_1^+, W_0^-, W_1^-."""
    result = []
    for level in range(1, depth + 1):
        result.append(Mode("V", level, "+", None))
        result.append(Mode("V", level, "-", None))
        result.append(Mode("W", level, "+", 0))
        result.append(Mode("W", level, "+", 1))
        result.append(Mode("W", level, "-", 0))
        result.append(Mode("W", level, "-", 1))
    return result


@dataclass(frozen=True)
class Block:
    kind: str  # "anchor", "variable", "leaf" or "dummy"
    mode_index: int = -1
    group: int = 0  # 1-based anchor group u (rows) or v (columns)
    level: int = -1
    sign: str = ""
    node: int = -1

    def name(self, axis: str) -> str:
        letter = "R" if axis == "row" else "C"
        if self.kind == "anchor":
            return f"{letter}^_{self.mode_index}({self.group})"
        if self.kind == "variable":
            return f"{letter}_{self.level}^{self.sign}({self.node})"
        if self.kind == "leaf":
            return f"{letter}_{self.level}({self.node})"
        return f"{letter}_*"


def parent(node: int) -> int:
    return node // 2


class TreeMatrix:
    """The ordered binary matrix A_h with its block structure."""

    def __init__(self, depth: int, anchor: Optional[List[List[int]]] = None, marks=None):
        """The paper's A_h; with `anchor`, the same construction with another
        s x s anchor S in place of the 64 x 64 one, and with `marks` (see
        pattern_matrix) other marks than e_1, e_2 between the anchors and the
        rows and columns of the designated sets."""
        if depth < 1:
            raise ValueError("h must be at least 1")
        self.depth = depth
        self.leaf_count = 2 ** depth  # m
        self.anchor = anchor_matrix() if anchor is None else [list(row) for row in anchor]
        self.anchor_size = len(self.anchor)
        self.marks = marks or unit_marks(self.anchor_size)
        self.modes = modes(depth)
        self.row_blocks = self._anchor_blocks() + self._variable_rows(0, 0) + [Block("dummy")]
        self.column_blocks = self._anchor_blocks() + [Block("dummy")] + self._variable_columns(0, 0)

    # ----- block sizes and orders ------------------------------------------------

    def block_size(self, block: Block) -> int:
        if block.kind in ("anchor", "dummy"):
            return self.leaf_count
        if block.kind == "variable":
            return self.leaf_count >> block.level
        return 1

    def _anchor_blocks(self) -> List[Block]:
        return [Block("anchor", mode_index=t, group=u)
                for t in range(len(self.modes)) for u in range(1, self.anchor_size + 1)]

    def _variable_rows(self, level: int, node: int) -> List[Block]:
        """Rows: minus block, the subtrees of 2p and 2p+1, plus block."""
        if level == self.depth:
            return [Block("leaf", level=level, node=node)]
        return ([Block("variable", level=level, sign="-", node=node)]
                + self._variable_rows(level + 1, 2 * node)
                + self._variable_rows(level + 1, 2 * node + 1)
                + [Block("variable", level=level, sign="+", node=node)])

    def _variable_columns(self, level: int, node: int) -> List[Block]:
        """Columns: the same recursion with the signs reversed."""
        if level == self.depth:
            return [Block("leaf", level=level, node=node)]
        return ([Block("variable", level=level, sign="+", node=node)]
                + self._variable_columns(level + 1, 2 * node)
                + self._variable_columns(level + 1, 2 * node + 1)
                + [Block("variable", level=level, sign="-", node=node)])

    def size(self) -> int:
        return sum(self.block_size(block) for block in self.row_blocks)

    # ----- the named sets ------------------------------------------------------

    def in_class(self, block: Block, level: int, sign: str, parity: Optional[int] = None) -> bool:
        """Is the block part of R_level^sign (or C_level^sign), restricted to node
        parity `parity` if given?  Leaves carry both signs."""
        if block.kind == "variable":
            matches = block.level == level and block.sign == sign
        elif block.kind == "leaf":
            matches = level == self.depth
        else:
            return False
        return matches and (parity is None or block.node % 2 == parity)

    def designated_role(self, block: Block, mode: Mode, axis: str) -> int:
        """0 if the non-anchor block lies in neither designated set of the mode
        on this axis, else j in {1, 2} for R_j(t) (rows) or C_j(t) (columns)."""
        level = mode.level
        is_dummy = block.kind == "dummy"
        if mode.kind == "V":
            if axis == "row":
                first = self.in_class(block, level, "+") if mode.sign == "+" else self.in_class(block, level - 1, "-")
                second = self.in_class(block, level - 1, "+") if mode.sign == "+" else self.in_class(block, level, "-")
            else:
                first = is_dummy
                second = self.in_class(block, level - 1, mode.sign)
        else:
            if axis == "row":
                first = self.in_class(block, level, mode.sign, mode.parity)
                second = is_dummy
            elif mode.sign == "+":
                first = self.in_class(block, level - 1, "+")
                second = self.in_class(block, level, "+", mode.parity)
            else:
                first = self.in_class(block, level, "-", mode.parity)
                second = self.in_class(block, level - 1, "-")
        if first and second:
            raise AssertionError(f"block {block} is in both designated sets of {mode.name()}")
        return 1 if first else 2 if second else 0

    # ----- the entries ---------------------------------------------------------

    def variable_table_matches(self, row: Block, column: Block) -> List[Tuple[int, int]]:
        """All lines of table (2.5) that apply to the pair, as (line, value)."""
        matches = []
        for level in range(self.depth + 1):
            if self.in_class(row, level, "+") and self.in_class(column, level, "+"):
                matches.append((1, int(row.node <= column.node)))
            if level < self.depth and self.in_class(row, level, "-") and self.in_class(column, level, "-"):
                matches.append((2, int(row.node < column.node)))
            if level >= 1 and self.in_class(row, level, "+") and self.in_class(column, level - 1, "+"):
                matches.append((3, int(parent(row.node) <= column.node)))
            if level >= 1 and self.in_class(row, level, "-") and self.in_class(column, level - 1, "-"):
                matches.append((4, int(parent(row.node) < column.node)))
        return matches

    def entry(self, row: Block, column: Block) -> int:
        """The entry of A_h between a row block and a column block."""
        if row.kind == "anchor" and column.kind == "anchor":
            if row.mode_index != column.mode_index:
                return 0
            return self.anchor[row.group - 1][column.group - 1]
        if column.kind == "anchor":
            role = self.designated_role(row, self.modes[column.mode_index], "row")
            return self.marks[role - 1][column.group - 1] if role else 0
        if row.kind == "anchor":
            role = self.designated_role(column, self.modes[row.mode_index], "column")
            return self.marks[role + 1][row.group - 1] if role else 0
        if row.kind == "dummy" or column.kind == "dummy":
            return 1
        matches = self.variable_table_matches(row, column)
        if not matches:
            return 0
        values = {value for _, value in matches}
        if len(values) != 1:
            raise AssertionError(f"conflicting table entries for {row} x {column}: {matches}")
        return values.pop()

    # ----- the matrices --------------------------------------------------------

    def block_matrix(self) -> List[List[int]]:
        """The quotient: one row per row block, one column per column block."""
        return [[self.entry(row, column) for column in self.column_blocks] for row in self.row_blocks]

    def full_matrix_rows(self) -> List[int]:
        """A_h as n row bitmasks; bit c of row r is A_h(r, c), positions from 0."""
        column_masks = []
        position = 0
        for column in self.column_blocks:
            width = self.block_size(column)
            column_masks.append(((1 << width) - 1) << position)
            position += width
        rows = []
        for row in self.row_blocks:
            mask = 0
            for column_index, column in enumerate(self.column_blocks):
                if self.entry(row, column):
                    mask |= column_masks[column_index]
            rows.extend([mask] * self.block_size(row))
        return rows

    def positions(self, axis: str) -> List[Block]:
        """The block of each position along an axis."""
        blocks = self.row_blocks if axis == "row" else self.column_blocks
        result = []
        for block in blocks:
            result.extend([block] * self.block_size(block))
        return result
