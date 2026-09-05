#!/usr/bin/env python3
"""One-shot modernization of Harrison's sources for OCaml 5 + dune.

Walks each file with an OCaml-aware lexer so that comments, string
literals and char literals are never rewritten, and applies:

  <<p ==> q>>   ->  {%fml|p ==> q|}      (camlp5 quotation -> ppx extension)
  <<|x + y|>>   ->  {%tm|x + y|}
  a & b         ->  a && b               (removed in OCaml 5)
  a or b        ->  a || b               (removed in OCaml 5)
  Pervasives    ->  Stdlib               (renamed in OCaml 4.07)

`&` and `or` are replaced textually rather than redefined as operators:
a user-defined `let ( & ) = ( && )` would evaluate both sides eagerly,
and this code relies on short-circuiting (e.g. unif.ml's
`defined env y & istriv env x (apply env y)`).
"""

import re
import sys

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
CHAR_LIT = re.compile(r"'(\\[\\'\"ntbr ]|\\[0-9]{3}|\\x[0-9a-fA-F]{2}|[^\\'])'")
QUOTED_OPEN = re.compile(r"\{([a-z_]*)\|")
RENAME = {'Pervasives': 'Stdlib'}


def skip_string(s, i):
    """i points at the opening '"'; returns index just past the closing one."""
    i += 1
    while i < len(s):
        if s[i] == '\\':
            i += 2
        elif s[i] == '"':
            return i + 1
        else:
            i += 1
    raise ValueError('unterminated string')


def skip_comment(s, i):
    """i points at '(*'; returns index just past the matching '*)'."""
    depth = 0
    while i < len(s):
        if s.startswith('(*', i):
            depth += 1
            i += 2
        elif s.startswith('*)', i):
            depth -= 1
            i += 2
            if depth == 0:
                return i
        elif s[i] == '"':
            i = skip_string(s, i)
        else:
            i += 1
    raise ValueError('unterminated comment')


def skip_quoted(s, i, tag):
    """i points just past '{tag|'; returns index just past '|tag}'."""
    close = '|' + tag + '}'
    j = s.find(close, i)
    if j < 0:
        raise ValueError('unterminated quoted string')
    return j + len(close)


def find_quotation_end(s, i):
    """i points just past '<<'; returns (content, index past '>>').

    A '>>' preceded by a single backslash is escaped and does not close.
    """
    j = i
    while True:
        j = s.find('>>', j)
        if j < 0:
            raise ValueError('unterminated quotation')
        # escaped if preceded by an odd number of backslashes
        k = j - 1
        n = 0
        while k >= i and s[k] == '\\':
            n += 1
            k -= 1
        if n % 2 == 0:
            return s[i:j], j + 2
        j += 2


def convert_quotation(text):
    is_term = re.match(r'(?s)^\|(.*)\|$', text)
    if is_term:
        text = text[1:-1]
    # camlp5 required \< \> \\ to be escaped inside a quotation
    text = re.sub(r'\\([\\<>])', r'\1', text)
    if '|}' in text or '{|' in text:
        raise ValueError('quotation not representable as {|...|}: ' + text)
    return '{%' + ('tm' if is_term else 'fml') + '|' + text + '|}'


def transform(src, ops=True, stats=None):
    """Rewrite `src`.

    Quotations are always rewritten, including inside comments: Harrison
    disables whole example blocks with `(*** ... ***)`, and those are code
    that should still work when uncommented.  Operator and module renames
    are applied with ops=True only, i.e. never inside a comment, where
    `or` is usually English prose.
    """
    out = []
    i, n = 0, len(src)
    if stats is None:
        stats = {'fml': 0, 'tm': 0, '&': 0, 'or': 0, 'Pervasives': 0}
    while i < n:
        c = src[i]
        if src.startswith('(*', i):
            j = skip_comment(src, i)
            inner, _ = transform(src[i + 2:j - 2], ops=False, stats=stats)
            out.append('(*' + inner + '*)')
            i = j
        elif c == '"':
            j = skip_string(src, i)
            out.append(src[i:j])
            i = j
        elif c == '{' and QUOTED_OPEN.match(src, i):
            m = QUOTED_OPEN.match(src, i)
            j = skip_quoted(src, m.end(), m.group(1))
            out.append(src[i:j])
            i = j
        elif c == "'" and CHAR_LIT.match(src, i):
            m = CHAR_LIT.match(src, i)
            out.append(m.group(0))
            i = m.end()
        elif src.startswith('<<', i):
            try:
                content, j = find_quotation_end(src, i + 2)
            except ValueError:
                out.append(c)
                i += 1
                continue
            rewritten = convert_quotation(content)
            stats['tm' if rewritten.startswith('{%tm') else 'fml'] += 1
            out.append(rewritten)
            i = j
        elif IDENT.match(src, i):
            m = IDENT.match(src, i)
            word = m.group(0)
            if not ops:
                out.append(word)
            elif word == 'or':
                out.append('||')
                stats['or'] += 1
            elif word in RENAME:
                out.append(RENAME[word])
                stats['Pervasives'] += 1
            else:
                out.append(word)
            i = m.end()
        elif c == '&' and ops:
            if src.startswith('&&', i):
                out.append('&&')
                i += 2
            else:
                out.append('&&')
                stats['&'] += 1
                i += 1
        else:
            out.append(c)
            i += 1
    return ''.join(out), stats


def main(paths):
    totals = {}
    for p in paths:
        with open(p) as f:
            src = f.read()
        try:
            new, stats = transform(src)
        except ValueError as e:
            print('%s: %s' % (p, e), file=sys.stderr)
            return 1
        if new != src:
            with open(p, 'w') as f:
                f.write(new)
        for k, v in stats.items():
            totals[k] = totals.get(k, 0) + v
        if any(stats.values()):
            print('%-22s %s' % (p, ' '.join('%s=%d' % (k, v)
                                            for k, v in stats.items() if v)))
    print('TOTAL', totals)
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
