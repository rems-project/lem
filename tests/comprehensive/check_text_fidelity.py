#!/usr/bin/env python3
"""Gate: text that must come through the spacing and layout passes byte for
byte (pre-merge audit of output-niceness, 2026-10-03; arc record §13).

Usage: check_text_fidelity.py GENERATED.lean [GENERATED_auxiliary.lean ...]

The shapes come from test_text_fidelity.lem through `declare lean
target_rep` text; the asserts (the `#eval do` blocks) are in the auxiliary
module. Comments and string literals are blanked before the checks, so
only code counts. Fails (exit 1, naming each violation) if
  T1  `×'` (a dependent pair) is not one token: the code must hold ` ×' `
      and never `× '`;
  T2  `(p).1` did not come out as `p.1`: the code must hold `p.1)` and
      never ` .1`;
  T3  the character literal `'×'` is not intact: the code must hold `'×'`
      and never `' × '`;
  T4  `«a b»` is not one token on one line: the code must hold `«a b»`, and
      no line may end with `«a`;
  T5  a `#eval do` block was touched: each `#eval` must start its line at
      column 0, followed by the block's three lines `  if …`, `  then …`,
      `  else …` as the backend emits an assert;
  T6  vacuity: every positive shape of T1–T5 must occur at least once (over
      all the files given).
"""
import sys


def blank_comments_and_strings(s):
    """The code of a .lean file: comments and string literals replaced by
    spaces of the same length (line breaks kept), character literals kept."""
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith('/-', i):
            d, j = 1, i + 2
            while j < n and d:
                if s.startswith('/-', j):
                    d, j = d + 1, j + 2
                elif s.startswith('-/', j):
                    d, j = d - 1, j + 2
                else:
                    j += 1
            out.append(''.join(c if c == '\n' else ' ' for c in s[i:j]))
            i = j
        elif s.startswith('--', i):
            j = s.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i))
            i = j
        elif s[i] == '"':
            j = i + 1
            while j < n and s[j] != '"':
                j += 2 if s[j] == '\\' else 1
            j += 1
            out.append(''.join(c if c == '\n' else ' ' for c in s[i:j]))
            i = j
        else:
            out.append(s[i])
            i += 1
    return ''.join(out)


def main(paths):
    errors = []
    found = {'×\'': False, 'p.1': False, "'×'": False, '«a b»': False, '#eval do': False}
    for path in paths:
        code = blank_comments_and_strings(open(path, encoding='utf-8').read())
        lines = code.split('\n')

        def absent(what, rule):
            if what in code:
                n = code[:code.index(what)].count('\n') + 1
                errors.append(f'{rule} {path}:{n}: `{what}` found')

        found['×\''] |= " ×' " in code
        absent("× '", 'T1')
        found['p.1'] |= 'p.1)' in code
        absent(' .1', 'T2')
        found["'×'"] |= "'×'" in code
        absent("' × '", 'T3')
        found['«a b»'] |= '«a b»' in code
        for n, l in enumerate(lines, 1):
            if l.rstrip().endswith('«a'):
                errors.append(f'T4 {path}:{n}: `«a b»` broken over a line')
            if '#eval' in l and not l.startswith('#eval'):
                errors.append(f'T5 {path}:{n}: `#eval` not at the start of its line: {l.strip()[:60]!r}')
        for n, l in enumerate(lines, 1):
            if l.startswith('#eval do'):
                found['#eval do'] = True
                block = lines[n:n + 3]
                ok = (len(block) == 3 and block[0].startswith('  if ') and block[1].startswith('  then ')
                      and block[2].startswith('  else '))
                if not ok:
                    errors.append(f'T5 {path}:{n}: `#eval do` block changed: {[b[:30] for b in block]!r}')
    for k, v in found.items():
        if not v:
            errors.append(f'T6 {" ".join(paths)}: `{k}` never occurs (vacuous)')
    for e in errors:
        print('  FAIL:', e)
    if errors:
        return 1
    print(f'  OK: {" ".join(paths)}: target_rep text intact')
    return 0


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
