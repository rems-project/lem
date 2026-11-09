#!/usr/bin/env python3
"""Gate: the layout of a generated Lean file (output-niceness S3-A, 2026-10-03).

Usage: check_layout.py GENERATED.lean [WIDTH]

The layout pass (src/lean_layout.ml) breaks long declarations over lines.
Its invariants, checked here on the generated test file:
  L1  every `|` (a match alternative, an equation, a constructor) is the
      first token of its line — Lean requires the alternatives of one match
      to start at a column no smaller than the first one's; one per line is
      how the pass guarantees it;
  L2  a `;` (the end of a `let` binding) is the last code token of its line:
      the let's body starts a new line, as in the source;
  L3  a line without a string literal or a comment is at most WIDTH columns
      wide (default 100; strings and comments are never broken);
  L4  no code follows a multi-line comment on the line it ends (the token
      would sit at the comment's last column; also C3 of check_comments.py);
  L5  vacuity: the file must contain a match alternative, a `let` and a
      comment, or the test no longer exercises the layout.
Strings, character literals and nested comments are lexed as in Lean;
columns count characters.
"""
import sys


def tokens(s):
    """(line, column, kind, text) for every token; kind in {code, str, comment}."""
    out, i, n, line, col = [], 0, len(s), 1, 0
    while i < n:
        c = s[i]
        if c == '\n':
            line, col, i = line + 1, 0, i + 1
        elif c in ' \t':
            col, i = col + 1, i + 1
        elif s.startswith('/-', i):
            d, j = 1, i + 2
            while j < n and d:
                if s.startswith('/-', j):
                    d, j = d + 1, j + 2
                elif s.startswith('-/', j):
                    d, j = d - 1, j + 2
                else:
                    j += 1
            t = s[i:j]
            out.append((line, col, 'comment', t))
            nl = t.count('\n')
            if nl:
                line, col = line + nl, len(t) - t.rfind('\n') - 1
            else:
                col += len(t)
            i = j
        elif s.startswith('--', i):
            j = s.find('\n', i)
            j = n if j < 0 else j
            out.append((line, col, 'comment', s[i:j]))
            col += j - i
            i = j
        elif c == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            j += 1
            out.append((line, col, 'str', s[i:j]))
            col += j - i
            i = j
        elif c == "'" and i + 2 < n and (s[i + 1] == '\\' or s[i + 2] == "'") \
                and (i == 0 or not (s[i - 1].isalnum() or s[i - 1] in "_'.")):
            j = s.find("'", i + 3 if s[i + 1] == '\\' else i + 2) + 1
            out.append((line, col, 'str', s[i:j]))
            col += j - i
            i = j
        elif c in '()[]{},;':
            out.append((line, col, 'code', c))
            col, i = col + 1, i + 1
        else:
            j = i
            while j < n and s[j] not in ' \t\n"()[]{},;' and not s.startswith('/-', j) \
                    and not (j > i and s.startswith('--', j)):
                j += 1
            out.append((line, col, 'code', s[i:j]))
            col += j - i
            i = j
    return out


def main(path, width):
    text = open(path, encoding='utf-8').read()
    toks = tokens(text)
    lines = text.split('\n')
    by_line = {}
    for t in toks:
        by_line.setdefault(t[0], []).append(t)
    errors = []
    bars = lets = comments = 0
    for ln, ts in sorted(by_line.items()):
        code = [t for t in ts if t[2] == 'code']
        for k, t in enumerate(code):
            if t[3] == '|':
                bars += 1
                if k > 0:
                    errors.append(f'L1 {path}:{ln}: `|` is not the first token of its line: {lines[ln - 1].strip()[:60]!r}')
            if t[3] == 'let':
                lets += 1
            if t[3] == ';' and k != len(code) - 1:
                errors.append(f'L2 {path}:{ln}: code after the `;` of a let: {lines[ln - 1].strip()[:60]!r}')
        if not any(t[2] in ('str', 'comment') for t in ts) and len(lines[ln - 1]) > width:
            errors.append(f'L3 {path}:{ln}: {len(lines[ln - 1])} columns, no string or comment to excuse it')
        for t in ts:
            if t[2] == 'comment':
                comments += 1
    for (ln, col, kind, t) in toks:
        if kind == 'comment' and '\n' in t:
            # the comment's last line is a new physical line (end_line > ln), so
            # every code token recorded on it starts after the comment
            end_line = ln + t.count('\n')
            after = [u for u in by_line.get(end_line, []) if u[2] != 'comment']
            if after:
                errors.append(f'L4 {path}:{end_line}: code after a multi-line comment: {after[0][3][:40]!r}')
    if bars == 0 or lets == 0 or comments == 0:
        errors.append(f'L5 {path}: vacuous — alternatives={bars} lets={lets} comments={comments}')
    for e in errors:
        print('  FAIL:', e)
    if errors:
        return 1
    print(f'  OK: {path}: layout sound ({bars} alternatives, {lets} lets, {comments} comments, width {width})')
    return 0


if __name__ == '__main__':
    if len(sys.argv) not in (2, 3):
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) == 3 else 100))
