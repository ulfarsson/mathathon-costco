"""Find jumps between the overlay steps of a Beamer PDF.

A word that appears on two consecutive pages of the same frame (same text, same left edge) should
stay at the same height; if it moves, the frame jumps when the speaker steps through it. Uses
pdftotext -bbox. Prints the frames that jump and the largest move on each, then OK or JUMPS.

Usage: python3 check_slide_jumps.py slides.pdf
"""
import re
import subprocess
import sys
from html import unescape


def pages(pdf):
    out = subprocess.run(["pdftotext", "-bbox", pdf, "-"], capture_output=True, text=True, check=True).stdout
    result = []
    for page in re.findall(r"<page[^>]*>(.*?)</page>", out, re.S):
        words = [(unescape(w), float(x0), float(y0)) for x0, y0, w in
                 re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="[\d.]+" yMax="[\d.]+">(.*?)</word>', page)]
        result.append(words)
    return result


def frame_number(words):
    """The footer reads 'n / N' at the bottom right."""
    tokens = [w for w, x, y in sorted(words, key=lambda t: (t[2], t[1]))]
    for i in range(len(tokens) - 2, 0, -1):
        if tokens[i] == "/" and tokens[i - 1].isdigit() and tokens[i + 1].isdigit():
            return int(tokens[i - 1])
    return None


def main():
    data = pages(sys.argv[1])
    jumps = {}
    for k in range(1, len(data)):
        a, b = data[k - 1], data[k]
        fa, fb = frame_number(a), frame_number(b)
        if fa is None or fa != fb:
            continue
        ia, ib = {}, {}
        for w, x, y in a:
            ia.setdefault((w, round(x, 1)), []).append(y)
        for w, x, y in b:
            ib.setdefault((w, round(x, 1)), []).append(y)
        for key, ya in ia.items():
            yb = ib.get(key)
            if not yb or len(key[0]) < 2:
                continue
            # pair the occurrences one way round: each occurrence on the page with fewer of them
            # is matched with the nearest one on the other page, so words a step reveals or hides
            # are not taken for moved words
            few, many = (ya, yb) if len(ya) <= len(yb) else (yb, ya)
            move = max(min(abs(y - z) for z in many) for y in few)
            if move > 0.6:
                best = jumps.get(fa, (0, ""))
                if move > best[0]:
                    jumps[fa] = (move, "page %d->%d: '%s' moved %.1fpt" % (k, k + 1, key[0], move))
    for f in sorted(jumps):
        print("frame %d: %s" % (f, jumps[f][1]))
    print("JUMPS" if jumps else "OK: no word moves between the steps of a frame")


if __name__ == "__main__":
    main()
