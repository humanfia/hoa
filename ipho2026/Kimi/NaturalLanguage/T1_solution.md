# IPhO 2026 — Theory Problem 1 (T1): Solution

*Three independent problems: a hydrostatic gate (A), an electron–positron
pair (B), and the photodissociation of ozone (C). Throughout,
$k \equiv 1/(4\pi\varepsilon_0)$, $g$ is the gravitational acceleration, and
$\rho_0$ is the density of water. All work is classical and
non-relativistic, as stipulated in the statement.*

---

## A. Hydrostatic gate

### A.1 — Side length $a$ for a maximum level difference $\Delta h = 1.41\ \mathrm{m}$

**Geometry read from Fig. 1a.**
The cubic block of side $a$ is drawn in cross-section as a square rotated by
$45^\circ$ (a diamond). The hinge $O$ lies on the wall $MN$, and the figure
marks the distance from the left vertex $L$ of the diamond to $O$, measured
along the upper-left edge, as $\tfrac12 a$; that is, *$O$ is the midpoint of
the upper-left edge*. Because the edges are at $45^\circ$ to the (vertical)
wall, the vertical wall through $O$ then meets the lower-left edge at its
midpoint $P$, and

$$|OP| = \frac{a}{2}\sin 45^\circ + \frac{a}{2}\sin 45^\circ
      = \frac{a\sqrt 2}{2},$$

exactly the stated vertical size of the slot — the geometry of Fig. 1a and
the text are mutually consistent. The corner triangle $OLP$ (right isosceles,
legs $|OL|=|LP|=a/2$) protrudes into the **left** reservoir; the rest of the
cube lies in the right reservoir. The block is fully submerged on both sides.
Extruded through the cube's thickness $a$ (perpendicular to the figure), the
slot is a rectangle $(a\sqrt2/2)\times a$, and each protruding face strip
($OL$ and $LP$) is a rectangle $\frac a2 \times a$ of area $a^2/2$.

Set coordinates with $O$ as origin, $x$ horizontal toward the right
reservoir, $z$ upward; then
$L=(-\tfrac{a\sqrt2}{4},-\tfrac{a\sqrt2}{4})$, $P=(0,-\tfrac{a\sqrt2}{2})$,
and the cube's centre is $C=(+\tfrac{a\sqrt2}{4},-\tfrac{a\sqrt2}{4})$.

**Forces on the block.** Split the hydrostatic problem into (i) a *base* part
with both reservoirs at the lower (right) level, and (ii) the *excess* due to
the left level being higher by $\Delta h$.

*Base part.* With equal levels the block is surrounded by a single connected
pressure field, so the water exerts the Archimedean buoyancy
$\rho_0 g a^3$ upward at the centre $C$. Together with the weight
$3\rho_0 g a^3$ downward at $C$, the net base force is the **effective
weight**

$$W' = (3\rho_0-\rho_0)\,g a^3 = 2\rho_0 g a^3$$

acting vertically downward at $C$.

*Excess part.* Since the whole block lies below *both* free surfaces, the
left pressure exceeds the right pressure at every point of the block by the
same amount

$$\Delta p = \rho_0 g\,\Delta h .$$

This uniform excess pressure acts on the two left-exposed strips $OL$ and
$LP$ (area $a^2/2$ each), normal to each face, pushing the block away from
the left reservoir.

**Torque balance about $O$** (the hinge reaction exerts no torque about $O$).

*Restoring torque (effective weight).* The vertical force $W'$ at $C$ has
lever arm $x_C = a\sqrt2/4$:

$$|\tau_{\rm grav}| = W'\,x_C
= 2\rho_0 g a^3\cdot\frac{a\sqrt2}{4}
= \frac{\sqrt2}{2}\,\rho_0 g a^4 .$$

*Opening torque (excess pressure).* On each strip the resultant
$\Delta p\,a^2/2$ is normal to the face and acts at the strip centroid.

- Strip $OL$: the face passes through $O$, the centroid is at distance
  $a/4$ from $O$ along the face, and the force is normal to the face, so
  $$|\tau_1| = \Delta p\,\frac{a^2}{2}\cdot\frac{a}{4}
   = \frac{\Delta p\,a^3}{8}.$$
- Strip $LP$: centroid $M_2=(-\tfrac{a\sqrt2}{8},-\tfrac{3a\sqrt2}{8})$;
  with $\vec F_2 = \Delta p\frac{a^2}{2}\big(\tfrac{\sqrt2}{2},+\tfrac{\sqrt2}{2}\big)$
  the torque $zF_x - xF_z$ evaluates to
  $$|\tau_2| = \frac{\Delta p\,a^3}{8},$$
  in the *same* rotational sense as $\tau_1$.

Both strips therefore produce

$$|\tau_{\rm press}| = \frac{\Delta p\,a^3}{4}
= \frac{\rho_0 g\,\Delta h\, a^3}{4},$$

tending to rotate the block so that the slot opens; $|\tau_{\rm grav}|$
opposes this.

*Cross-check (resultant method).* The vertical components of the two strip
forces cancel (equal areas, normals at $\pm45^\circ$); the horizontal
components add to $\Delta p\,A_{\rm slot}$ with
$A_{\rm slot} = (a\sqrt2/2)\,a = a^2\sqrt2/2$. The resultant acts at the
centroid of the slot projection, i.e. at depth $a\sqrt2/4$ below $O$, giving
$|\tau_{\rm press}| = \rho_0 g\Delta h \cdot \frac{a^2\sqrt2}{2}\cdot\frac{a\sqrt2}{4} = \rho_0 g\,\Delta h\, a^3/4$ — identical to the
strip-by-strip sum. $\checkmark$

**Threshold condition.** The level difference is maximal when the two torques
balance:

$$\frac{\rho_0 g\,\Delta h_{\max}\, a^3}{4} = \frac{\sqrt2}{2}\,\rho_0 g a^4
\qquad\Longrightarrow\qquad \Delta h_{\max} = 2\sqrt2\, a .$$

Hence

$$\boxed{\,a = \frac{\Delta h}{2\sqrt2}
= \frac{1.41\ \mathrm{m}}{2\sqrt2}
= 0.4985\ \mathrm{m} \approx 0.50\ \mathrm{m}\,}$$

(0.499 m to three significant figures; $\rho_0$ and $g$ cancel, so no
numerical values for them are needed).

*Checks.* Dimensions: $[\rho_0 g\,\Delta h\,a^3] = (\mathrm{kg\,m^{-3}})(\mathrm{m\,s^{-2}})(\mathrm{m})(\mathrm{m^3}) = \mathrm{N\,m}$ ✓ (torque), so $a$ comes out as a length ✓. The result grows
linearly with $\Delta h$ and is independent of $\rho_0$ — the density ratio
$3$ entered only through $W'=2\rho_0ga^3$; a neutrally buoyant block
($\rho=\rho_0$) would give zero restoring torque and could not seal at all,
as it should. ✓

---

## B. Electron–positron pair

**Set-up common to B.1 and B.2.**
At $t=0$ the particles are $r_0 = 100\,a_0$ apart, with velocities
anti-parallel and perpendicular to the separation line. Each has angular
momentum $\mu\hbar$ about the centre of mass (CM). Equal masses $m$ imply the
CM is the midpoint, and $m v_0 (r_0/2) = \mu\hbar$ for each particle gives
equal speeds

$$v_0 = \frac{2\mu\hbar}{m r_0},$$

so the total momentum vanishes: the CM is at rest in the lab frame.

The two-body problem reduces to the relative coordinate
$\vec r = \vec r_{+}-\vec r_{-}$ of a single particle with **reduced mass**
$m_r = m/2$ moving in $U(r) = -ke^2/r$, with

$$L = L_{\rm tot} = 2\mu\hbar,
\qquad
E = 2\cdot\tfrac12 m v_0^2 - \frac{ke^2}{r_0}
  = \frac{4\mu^2\hbar^2}{m r_0^2} - \frac{ke^2}{r_0}.$$

Using the given Bohr radius
$a_0 = 4\pi\varepsilon_0\hbar^2/(me^2) = \hbar^2/(kme^2)$, i.e.
$ke^2 = \hbar^2/(ma_0)$, and $r_0 = 100\,a_0$:

$$E = \frac{\hbar^2}{m a_0^2}
\left(\frac{4\mu^2}{10^{4}} - \frac{1}{100}\right),
\qquad
\frac{L^2}{2m_r} = \frac{(2\mu\hbar)^2}{m} = \frac{4\mu^2\hbar^2}{m}.$$

Because the initial velocities are perpendicular to the separation,
$\dot r(0)=0$: **the motion starts at an apsis (turning point of the radial
motion).**

### B.1 — $\mu = 4$: maximum separation

With $\mu = 4$:

$$E = \frac{\hbar^2}{ma_0^2}\left(\frac{64}{10^4}-\frac{1}{100}\right)
= -3.6\times10^{-3}\,\frac{\hbar^2}{ma_0^2} < 0,$$

so the pair is bound, as stated. Turning points $r$ satisfy
$E = \dfrac{L^2}{2m_r r^2} - \dfrac{ke^2}{r}$; writing $u = a_0/r$ and
multiplying through by $ma_0^2/\hbar^2$:

$$64u^2 - u + 0.0036 = 0
\quad\Longrightarrow\quad
u = \frac{1 \pm \sqrt{1 - 4(64)(0.0036)}}{128}
  = \frac{1 \pm \sqrt{0.0784}}{128}
  = \frac{1 \pm 0.28}{128}.$$

The two roots are $u_1 = 0.0100 \Rightarrow r = 100\,a_0$ (the initial
configuration — confirming it is a turning point ✓) and
$u_2 = 5.625\times10^{-3}$, giving

$$\boxed{\,r_{\max} = \frac{a_0}{5.625\times10^{-3}}
= \frac{1600}{9}\,a_0 \approx 1.78\times10^{2}\,a_0 \;(\approx 178\,a_0)\,}$$

*Checks.* Eccentricity from Hint 1:
$\varepsilon = \sqrt{1 + 4L^2E/(k^2e^4m)}$; here
$4L^2E/(k^2e^4m) = 4(8\hbar)^2\big({-}3.6\times10^{-3}\tfrac{\hbar^2}{ma_0^2}\big)\big/\big(\tfrac{\hbar^4}{ma_0^2}\big) = -0.9216$,
so $\varepsilon = 0.28 < 1$ (ellipse ✓). The semi-latus rectum is
$p = L^2/(m_r k e^2) = 128\,a_0$, and the conic
$r = p/(1-\varepsilon\cos\theta)$ gives
$r_{\max} = p/(1-\varepsilon) = 128/0.72\,a_0 = 1600/9\,a_0$ ✓. Also
$r_{\min}+r_{\max} = 277.78\,a_0 = -ke^2/E = a_0/0.0036$ ✓ (orbit energy
$E=-ke^2/(2A)$ with semi-major axis $A$).

### B.2 — $\mu = \tfrac{15}{2}$: angle between $\vec u_\infty$ and the initial line of motion

With $\mu = 15/2$:

$$E = \frac{\hbar^2}{ma_0^2}\left(\frac{225}{10^4}-\frac{1}{100}\right)
= +1.25\times10^{-2}\,\frac{\hbar^2}{ma_0^2} > 0,$$

unbound, as stated. Now $L = 15\hbar$, and Hint 1 gives

$$\varepsilon = \sqrt{1+\frac{4L^2E}{k^2e^4m}}
= \sqrt{1 + \frac{4(15\hbar)^2(1.25\times10^{-2})\,
\hbar^2/(ma_0^2)}{\hbar^4/(ma_0^2)}}
= \sqrt{1+11.25} = \sqrt{12.25} = 3.5 > 1$$

(hyperbola ✓). The semi-latus rectum is
$p = L^2/(m_r k e^2) = (15\hbar)^2\big/\big(\tfrac{m}{2}\cdot\tfrac{\hbar^2}{m a_0}\big) = 225\hbar^2 \cdot \frac{2a_0}{\hbar^2} = 450\,a_0$.

**Locating the initial point on the hyperbola.**
For an unbound orbit the radial motion has a single turning point, the
periapsis. From Hint 2, $r = p/(1-\varepsilon\cos\theta)$, the periapsis
($\theta = \pi$) is

$$r_{\rm peri} = \frac{p}{1+\varepsilon} = \frac{450\,a_0}{4.5} = 100\,a_0 = r_0.$$

So the initial separation *is* the periapsis (consistent with $\dot r(0)=0$
✓), and the initial relative velocity $\vec u_0$ is perpendicular to the
periapsis radius.

**Asymptote.** As $r\to\infty$, $1-\varepsilon\cos\theta_\infty = 0$, so

$$\cos\theta_\infty = \frac{1}{\varepsilon} = \frac{2}{7},
\qquad \theta_\infty = 73.40^\circ,$$

measured from the symmetry axis of the hyperbola (the periapsis lies at
$\theta = 180^\circ$). The outgoing relative velocity $\vec u_\infty$ is
directed along the outgoing asymptote. The initial velocity, perpendicular
to the periapsis radius, points along $180^\circ - 90^\circ = 90^\circ$ in
the same polar frame, while the outgoing asymptote lies at
$\theta_\infty = 73.40^\circ$ (or its mirror image for the opposite sense of
rotation — the angle is the same). Therefore

$$\boxed{\;\varphi = 90^\circ - \theta_\infty
= 90^\circ - \arccos\frac{2}{7}
= \arcsin\frac{2}{7} \approx 16.6^\circ\;}$$

between $\vec u_\infty$ and the initial line of motion of $e^+$ (the $e^+$
velocity in the CM frame is $\vec u/2$, i.e. parallel to $\vec u$ at all
times).

*Checks.* (i) Speed at infinity:
$u_\infty = \sqrt{2E/m_r} = \sqrt{0.05}\,\hbar/(ma_0)$; impact parameter
$b = L/(m_r u_\infty) = 134.2\,a_0$; the Rutherford relation
$\tan(\Theta/2) = ke^2/(m_r u_\infty^2 b)$ gives $\tan(\Theta/2) = 0.298$,
$\Theta = 33.2^\circ$ for the full deflection between the incoming and
outgoing asymptotes. By the mirror symmetry of the hyperbola about its axis,
the periapsis velocity bisects the asymptote directions, so the angle sought
here is $\Theta/2 = 16.6^\circ$ ✓. (ii) Kinematics at $t=0$:
$u_0 = 0.30\,\hbar/(ma_0)$ from energy conservation, hence
$m_r u_0 r_0 = 15\hbar = L$ ✓ and per-particle
$mv_0 r_0/2 = 7.5\,\hbar = \mu\hbar$ ✓.

---

## C. Photodissociation of ozone

### C.1 — Minimum angular frequency $\omega_{\min}$ for dissociation at angle $\theta$

**Conservation laws.** Let $\vec q$ be the photon momentum,
$q = \hbar\omega/c$ along the $x$-axis; let $\vec p$ be the momentum of the
outgoing $\mathrm O_2$ (mass $2m$) at angle $\theta$ to $\vec q$, and
$\vec p^{\,\prime}$ the momentum of the O atom (mass $m$). The O$_3$ is
initially at rest, and the photon is absorbed:

$$\text{momentum:}\quad \vec q = \vec p + \vec p^{\,\prime}
\quad\Longrightarrow\quad
p^{\,\prime 2} = q^2 + p^2 - 2qp\cos\theta ,$$

$$\text{energy:}\quad \hbar\omega + U_i = U_f + \frac{p^2}{2(2m)} +
\frac{p^{\,\prime 2}}{2m}
\quad\Longrightarrow\quad
E - \Delta U = \frac{p^2}{4m} + \frac{p^{\,\prime 2}}{2m},$$

with $E \equiv \hbar\omega$ and $\Delta U = U_f - U_i$.

**Eliminating the O atom.** Substituting $p^{\,\prime 2}$:

$$E - \Delta U = \frac{p^2}{4m} + \frac{q^2 + p^2 - 2qp\cos\theta}{2m},$$

$$3p^2 - 4q\cos\theta\; p + 2q^2 - 4m(E-\Delta U) = 0 .$$

A physical event at angle $\theta$ requires a real positive root $p$, i.e. a
non-negative discriminant:

$$\mathcal D = 16q^2\cos^2\theta - 12\big[2q^2 - 4m(E-\Delta U)\big] \ge 0
\;\Longrightarrow\;
6m(E-\Delta U) \ge q^2\big(3 - 2\cos^2\theta\big).$$

The minimum frequency saturates the inequality ($\mathcal D = 0$, i.e. a
double root $p = \tfrac{2}{3}q\cos\theta > 0$ ✓). With $q = E/c$:

$$\big(3-2\cos^2\theta\big)\,E^2 - 6mc^2\,E + 6mc^2\,\Delta U = 0,$$

$$E = \frac{3mc^2}{3-2\cos^2\theta}
\left[1 \pm \sqrt{1 - \frac{2\big(3-2\cos^2\theta\big)\,\Delta U}{3mc^2}}\,\right].$$

**Branch choice.** The $+$ branch gives $E \sim 6mc^2/(3-2\cos^2\theta)$, a
rest-energy-scale result incompatible with the non-relativistic
dissociation regime; the physical threshold continuously reduces to
$E\to\Delta U$ as $mc^2\to\infty$, which is the $-$ branch. Hence

$$\boxed{\;\hbar\omega_{\min}
= \frac{3mc^2}{3-2\cos^2\theta}
\left[1 - \sqrt{1 -
\frac{2\big(3-2\cos^2\theta\big)\,\Delta U}{3mc^2}}\,\right]
= \frac{2\Delta U}
{1 + \sqrt{1 - \dfrac{2\big(3-2\cos^2\theta\big)\Delta U}{3mc^2}}}\;}$$

(the second, rationalised, form follows from
$(1-\sqrt y)(1+\sqrt y) = 1-y$ and is numerically stabler).

**Domain of validity.** The threshold was set by the coalescing root
$p = \tfrac{2}{3}q\cos\theta$, which is positive only for
$0 \le \theta < \pi/2$ — the forward hemisphere drawn in Fig. 1c and the
regime used in C.2 ($\theta = \pi/6$). At $\theta = \pi/2$ this root tends
to $p = 0$ and the condition reduces continuously to
$E - \Delta U = q^2/(2m)$; for backward angles ($\theta > \pi/2$) the
threshold is set by that $p \to 0$ boundary rather than by the discriminant.

**Expansion (using the given hint).** Since molecular binding energies obey
$\Delta U \ll mc^2$, with $x = 2(3-2\cos^2\theta)\Delta U/(3mc^2) \ll 1$ the
binomial series $\sqrt{1-x} = 1 - \tfrac{x}{2} - \tfrac{x^2}{8} - \cdots$
gives

$$\hbar\omega_{\min}
\simeq \Delta U + \frac{\big(3-2\cos^2\theta\big)\,\Delta U^2}{6mc^2}
= \Delta U\left[1 +
\frac{\big(1+2\sin^2\theta\big)\,\Delta U}{6mc^2}\right].$$

*Checks.* If the photon momentum were neglected entirely, energy balance
alone gives $\hbar\omega_{\min} = \Delta U$ (both fragments emerge at rest)
— recovered here as the leading term ✓. The correction
$\propto \Delta U^2/(mc^2)$ is an energy ✓, positive for all $\theta$ ✓, and
grows with $\sin^2\theta$: transverse photon momentum must be supplied by
fragment recoil, costing extra energy ✓. Dimensions of every term: energy ✓.

### C.2 — Numerical value of $\hbar\omega_{\min} - \Delta U$ for $\theta = \pi/6$

With $\theta = \pi/6$: $\cos^2\theta = 3/4$, so
$3 - 2\cos^2\theta = \tfrac32$ and

$$\hbar\omega_{\min} - \Delta U \simeq
\frac{\tfrac32\,\Delta U^2}{6mc^2} = \frac{\Delta U^2}{4mc^2}.$$

Insert $\Delta U = 1.10\ \mathrm{eV}$ and
$m = 16.0\ \mathrm{u}$, using $1\ \mathrm{u}\,c^2 = 931.5\ \mathrm{MeV}$
(so $mc^2 = 16.0\times 931.5\ \mathrm{MeV} = 1.490\times10^{10}\ \mathrm{eV}$):

$$\hbar\omega_{\min} - \Delta U
= \frac{(1.10\ \mathrm{eV})^2}{4\times 1.490\times10^{10}\ \mathrm{eV}}
= \frac{1.21}{5.962\times10^{10}}\ \mathrm{eV}
\approx \boxed{\,2.03\times10^{-11}\ \mathrm{eV}\,}.$$

Evaluating the *exact* expression instead, with
$\delta \equiv \Delta U/(mc^2) = 7.38\times10^{-11}$:
$E = \dfrac{2\Delta U}{1+\sqrt{1-\delta}} = \Delta U\big(1 + \tfrac{\delta}{4} + \mathcal O(\delta^2)\big)$ gives
$E - \Delta U = 1.10 \times 1.85\times10^{-11}\ \mathrm{eV} = 2.03\times10^{-11}\ \mathrm{eV}$ — identical to the expanded result at this precision ✓.

The correction is extremely small (a relative shift $\delta/4 \approx 1.8\times10^{-11}$ of the threshold)
because the photon momentum $\hbar\omega/c$ is utterly negligible compared
with fragment momenta $\sim\sqrt{m\Delta U}$; the dissociation threshold is
essentially $\hbar\omega_{\min} \approx \Delta U = 1.10\ \mathrm{eV}$, with
the recoil correction $2.03\times10^{-11}\ \mathrm{eV}$ on top. ✓

---

## Summary of results

| Part | Result |
|------|--------|
| A.1 | $a = \Delta h/(2\sqrt2) = 0.499\ \mathrm{m}\ (\approx 0.50\ \mathrm{m})$ for $\Delta h = 1.41\ \mathrm{m}$ |
| B.1 | $r_{\max} = \dfrac{1600}{9}\,a_0 \approx 1.78\times10^{2}\,a_0$ |
| B.2 | $\varphi = \arcsin(2/7) = 90^\circ - \arccos(2/7) \approx 16.6^\circ$ |
| C.1 | $\hbar\omega_{\min} = \dfrac{2\Delta U}{1+\sqrt{1-2(3-2\cos^2\theta)\Delta U/(3mc^2)}} \simeq \Delta U + \dfrac{(3-2\cos^2\theta)\,\Delta U^2}{6mc^2}$ |
| C.2 | $\hbar\omega_{\min} - \Delta U \approx 2.03\times10^{-11}\ \mathrm{eV}$ |
