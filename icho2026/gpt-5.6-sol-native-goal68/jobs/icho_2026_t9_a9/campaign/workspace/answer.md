# IChO 2026 T9-A9

The number of arrangements is

\[
\boxed{120}.
\]

Alpha-cyclodextrin contains six glucopyranoside units, so modifying only the
primary `CH2OH` positions gives six sites.  “Hexadifferentiated” means that the
six sites carry six different functional groups.

First choose any one of those distinct groups as an anchor.  Its position only
chooses where we start reading the same cyclic molecule; it does not create a
new arrangement.  In the fixed direction around the ring, the other five
distinct groups can be placed in

\[
5! = 120
\]

orders.  Equivalently, there are `6! = 720` labelled linear assignments and
each cyclic arrangement has six readings related by rotation, so
`720 / 6 = 120`.

Reflections are not divided out.  The alpha-1,4-linked ring made from the
stated alpha-D-glucopyranoside units is directionally and stereochemically
oriented.  This reading is also grounded by the instruction immediately
before 9.9, which distinguishes clockwise from counterclockwise modification.
Consequently, reversing a generic order is not merely a rotation of the same
arrangement.

## Source grounding

- `TASK.json` and theory problem page Q9-1 state that alpha-CD has six
  alpha-D-glucopyranoside units.
- Theory problem page Q9-5 asks for arrangements of a hexadifferentiated
  alpha-CD when only the `CH2OH` groups are modified.
- Theory problem page Q9-4 explicitly distinguishes clockwise and
  counterclockwise in 9.8, grounding the oriented-cycle convention used in
  the count.
- The blank student answer sheet A9-5 supplies an unrestricted response box
  for 9.9 and adds no further equivalence convention or constraint.

No official solution, marking scheme, answer repository, or supplementary
scientific premise was used.
