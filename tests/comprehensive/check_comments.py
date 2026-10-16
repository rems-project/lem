#!/usr/bin/env python3
"""Gate: the author's comments survive translation to Lean, and the layout
of the generated file is sound (output-niceness S1, 2026-10-03).

Usage: check_comments.py SOURCE.lem GENERATED.lean

Fails (exit 1, naming each violation) if
  C1  a comment of SOURCE is missing from GENERATED, unless its text
      contains KNOWN-LOST (a registered loss; it must then be ABSENT, so a
      fix forces the tag's removal);
  C2  a comment of SOURCE appears more than once in GENERATED;
  C3  a multi-line comment of GENERATED is followed by code on the line it
      ends (Lean's layout is column-sensitive: the next token would sit at
      the comment's last column, e.g. a `|` that ends the enclosing match);
  C4  GENERATED has a whitespace-only line or two consecutive blank lines.
A comment of SOURCE is present when a comment of GENERATED — a nested one
counts on its own — has exactly the same alphanumeric text; so the change
of delimiters, the escaping and line breaks do not matter, and a comment
whose text merely occurs inside another comment does not count (the
pre-merge audit's substring plant, 2026-10-03).
"""
import re
import sys


def lem_comments(s):
    """Top-level (* ... *) comments of a .lem file, skipping string literals."""
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith('(*', i):
            d, j = 1, i + 2
            while j < n and d:
                if s.startswith('(*', j):
                    d, j = d + 1, j + 2
                elif s.startswith('*)', j):
                    d, j = d - 1, j + 2
                else:
                    j += 1
            out.append((s.count('\n', 0, i) + 1, s[i + 2:j - 2]))
            i = j
        elif s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            i = j + 1
        else:
            i += 1
    return out


def lean_comments(s):
    """Every /- ... -/ comment of a .lean file, nested ones included, as
    (start, end, text) in order of their start."""
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith('/-', i):
            stack, j = [i], i + 2
            while j < n and stack:
                if s.startswith('/-', j):
                    stack.append(j)
                    j += 2
                elif s.startswith('-/', j):
                    k = stack.pop()
                    j += 2
                    out.append((k, j, s[k + 2:j - 2]))
                else:
                    j += 1
            i = j
        elif s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            i = j + 1
        else:
            i += 1
    return out


def norm(t):
    return re.sub(r'[^A-Za-z0-9]', '', t)


def main(src_path, gen_path):
    src = open(src_path, encoding='utf-8').read()
    gen = open(gen_path, encoding='utf-8').read()
    gcs = sorted(lean_comments(gen))
    texts = [norm(t) for (_, _, t) in gcs]
    errors = []
    for line, c in lem_comments(src):
        k = norm(c)
        if not k:
            continue
        hits = sum(1 for t in texts if k == t)
        if 'KNOWN-LOST' in c:
            if hits:
                errors.append(f'C1 {src_path}:{line}: comment tagged KNOWN-LOST now appears; remove the tag')
        elif hits == 0:
            errors.append(f'C1 {src_path}:{line}: comment missing: {c.strip()[:60]!r}')
        elif hits > 1:
            errors.append(f'C2 {src_path}:{line}: comment emitted {hits} times: {c.strip()[:60]!r}')
    for (i, j, t) in gcs:
        if '\n' in t:
            e = gen.find('\n', j)
            rest = gen[j:e if e >= 0 else len(gen)].strip()
            if rest and not rest.startswith('/-') and not rest.startswith('--'):
                errors.append(f'C3 {gen_path}:{gen.count(chr(10), 0, j) + 1}: code after a multi-line comment: {rest[:40]!r}')
    # C4 is about the layout of code: the lines inside a multi-line comment
    # are the author's text and are copied as written (blank lines included)
    in_comment = set()
    for (i, j, t) in gcs:
        if '\n' in t:
            first = gen.count('\n', 0, i) + 1
            for k in range(first + 1, first + t.count('\n') + 1):
                in_comment.add(k)
    lines = gen.split('\n')
    for n, l in enumerate(lines, 1):
        if n in in_comment:
            continue
        if l and not l.strip():
            errors.append(f'C4 {gen_path}:{n}: whitespace-only line')
        if n > 1 and not l and not lines[n - 2] and n < len(lines) and (n - 1) not in in_comment:
            errors.append(f'C4 {gen_path}:{n}: two consecutive blank lines')
    for e in errors:
        print('  FAIL:', e)
    if errors:
        return 1
    print(f'  OK: {gen_path}: comments preserved, layout sound')
    return 0


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1], sys.argv[2]))
