"""Six-cycle example where deleting or bypassing one shared AND is insufficient."""

# Order: points a,b,c then lines x,y,z.  The nonedges are ay, bx, cz.
EDGES = ((0, 3), (1, 4), (0, 5), (1, 5), (2, 3), (2, 4))


def edge(bits):
    return any(bits[i] and bits[j] for i, j in EDGES)


def circuit(bits, replace=None, kill_first=False, kill_second=False):
    a, b, c, x, y, z = bits
    points = a or b
    lines = x or y
    shared = points and lines
    if replace == 'points':
        shared = points
    if replace == 'lines':
        shared = lines
    r1 = (False if kill_first else shared) or a
    r2 = (False if kill_second else shared) or y
    matched = r1 and r2 and (a or y) and (b or x)
    return matched or (a and z) or (b and z) or (c and x) or (c and y)


def bits(mask):
    return tuple(bool(mask & (1 << i)) for i in range(6))


assert all(edge(bits(m)) == circuit(bits(m)) for m in range(64))
for name, mask, args in [('replace by points', 3, {'replace':'points'}),
                         ('replace by lines', 24, {'replace':'lines'}),
                         ('erase first OR use', 18, {'kill_first':True}),
                         ('erase second OR use', 9, {'kill_second':True})]:
    assert edge(bits(mask)) != circuit(bits(mask), **args)
    print(name, 'fails at mask', mask, 'target', int(edge(bits(mask))))
assert not edge(bits(17)) and (bits(17)[0] or bits(17)[1]) and (bits(17)[3] or bits(17)[4])
print('64/64 canonical assignments match. Shared AND is dirty at independent pair {a,y}.')
