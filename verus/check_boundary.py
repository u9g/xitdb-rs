"""Checks the boundary between verified and unverified code in src/.

Code outside `verus!` blocks isn't checked by Verus, so it could call a
verified function without meeting its `requires`, and the function's
guarantees would no longer hold. This fails if code outside `verus!` calls
a verified function that has a `requires` clause; those check their
preconditions at run time instead.

Functions are matched by name: `Type::f(` against methods of `Type`,
`.f(` against every verified method named `f` (the receiver's type isn't
known, so this errs on the side of failing), and `f(` against free
functions. Test modules (`*_tests.rs`) are skipped.

Run from the repository root: python verus/check_boundary.py
"""

import pathlib
import re
import sys

src = pathlib.Path('src')
free = {}  # name -> has requires
methods = {}  # (type, name) -> has requires
outside = []  # (file, line number, text) outside verus! blocks

for path in sorted(src.glob('*.rs')):
    if path.name.endswith('_tests.rs'):
        continue
    inside = False
    impl = None
    lines = path.read_text(encoding='utf-8').split('\n')
    for i, line in enumerate(lines):
        if line.startswith('verus! {'):
            inside = True
            continue
        if line.startswith('} // verus!'):
            inside = False
            continue
        if not inside:
            if not line.lstrip().startswith('//'):
                outside.append((path, i + 1, line))
            continue
        m = re.match(r'impl(?:<[^>]*>)? (?:[\w:<>]+ for )?(\w+)', line)
        if m:
            impl = m.group(1)
            continue
        if line == '}':
            impl = None
            continue
        m = re.match(r'\s*(?:pub(?:\([a-z]+\))? )?(?:open |closed )?(spec |proof )?fn (\w+)', line)
        if not m or m.group(1):
            continue
        j = i
        while j < len(lines) and lines[j].strip() != '{' and not lines[j].rstrip().endswith(') {'):
            j += 1
        has = bool(re.search(r'^\s*requires\b', '\n'.join(lines[i:j]), re.M))
        if line.startswith(' ') and impl:
            methods[(impl, m.group(2))] = methods.get((impl, m.group(2)), False) or has
        else:
            free[m.group(2)] = free.get(m.group(2), False) or has

bad = []
for path, n, line in outside:
    if re.match(r'\s*(pub(\([a-z]+\))? )?fn ', line):
        continue
    for m in re.finditer(r'(\.|\b(\w+)::)?(\w+)\s*\(', line):
        dot, ty, name = m.group(1), m.group(2), m.group(3)
        if dot == '.':
            hit = any(has for (t, f), has in methods.items() if f == name)
        elif ty and ty[0].isupper():
            hit = methods.get((ty, name), False)
        else:
            hit = free.get(name, False)
        if hit:
            bad.append(f'{path}:{n}: {line.strip()}')
for b in bad:
    print(b)
total = len(free) + len(methods)
req = sum(free.values()) + sum(methods.values())
print(f'{total} verified functions, {req} with requires; {len(bad)} calls from unverified code to one with requires')
sys.exit(1 if bad else 0)
