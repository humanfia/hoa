# IPhO 2026, Theory Problem 2 — "Cooking with sunlight?" — Solution

## 0. Geometry, coordinates, and ray conventions (Figures 2c–2g)

Everything takes place in a plane perpendicular to the cylinder axis (Fig. 2d).
The mirror is the concave side of the **upper semicircle**

$$x^{2}+y^{2}=R^{2},\qquad y\ge 0,$$

centred at the origin $O$; the $y$-axis is the optical axis and $x$ is the
transverse coordinate of an incident ray. Incident rays are parallel to the
optical axis and travel in the $+y$ direction (Fig. 2d), so a ray with
transverse coordinate $x$ first meets the mirror at

$$P_{1}=(x,\sqrt{R^{2}-x^{2}}\,).$$

**Incidence angle.** Following Fig. 2g, $\theta$ is the angle between the
(vertical) incident ray and the radius $OP_{1}$, i.e. the angle of incidence
measured from the normal. Since the radius to $P_{1}$ makes the angle $\theta$
with the $y$-axis,

$$P_{1}=(R\sin\theta,\;R\cos\theta),\qquad x=R\sin\theta .$$

**Law of reflection.** The outward unit normal at $P_{1}$ is
$\hat n=(\sin\theta,\cos\theta)$ and the incident direction is
$\hat d_{i}=(0,1)$. Reflecting,

$$\hat d_{r}=\hat d_{i}-2(\hat d_{i}\!\cdot\!\hat n)\hat n
=(0,1)-2\cos\theta\,(\sin\theta,\cos\theta)
=(-\sin 2\theta,\;-\cos 2\theta). \tag{1}$$

For $0<\theta<\pi/2$ the reflected ray travels toward negative $x$; its
vertical component $-\cos2\theta$ is downward for $\theta<\pi/4$ (the
paraxial regime of Figs. 2d, 2g) and upward for $\theta>\pi/4$ (steep
rim-grazing rays, which keep bouncing — cf. Part A). The $x<0$ side is
symmetric.

**Chord lemma (used throughout Part A).** Any chord of a circle that makes the
angle $\theta$ with the radius at one endpoint makes the same angle $\theta$
with the radius at the other endpoint, because the triangle
$OP_{k}P_{k+1}$ is isosceles ($|OP_k|=|OP_{k+1}|=R$); the central angle of the
chord is then $\pi-2\theta$. Hence a ray bouncing inside the circular mirror
keeps the *same* incidence angle $\theta$ at every reflection, and successive
impact points are separated along the rim by the fixed central angle
$\pi-2\theta$.

---

## A.1 — The threshold sequence $x_N$ (1.5 pts)

**Set-up.** By symmetry $N$ depends only on $|x|$; take $x>0$. Measure the
azimuth $\varphi$ of a rim point from the $+y$-axis toward $+x$, so the point
is $(R\sin\varphi,R\cos\varphi)$ and it lies on the reflecting semicircle iff
its height is positive:

$$y=R\cos\varphi>0\quad\Longleftrightarrow\quad
\varphi\in(-\tfrac{\pi}{2},\tfrac{\pi}{2})\pmod{2\pi}.$$

The first impact is at $\varphi_1=\theta$. After each reflection the ray heads
toward decreasing $\varphi$ (from the right flank across to the left), and the
chord lemma fixes the step: $\varphi_{k+1}=\varphi_k-(\pi-2\theta)$. Thus

$$\varphi_k=(2k-1)\theta-(k-1)\pi .$$

**When does the ray escape?** The sequence $\varphi_k$ is strictly decreasing
with step $\pi-2\theta\in(0,\pi)$. The ray makes **at least $N$ reflections
iff $\varphi_N>-\pi/2$**:

* *If* $\varphi_N>-\pi/2$, then
  $-\pi/2<\varphi_N\le\varphi_j\le\varphi_1=\theta<\pi/2$ for every
  $j\le N$: all $N$ impact points lie on the mirror.
* *If* $\varphi_N\le-\pi/2$, let $j\le N$ be the first index with
  $\varphi_j\le-\pi/2$. One step has size $\pi-2\theta<\pi$ and
  $\varphi_{j-1}>-\pi/2$, so $\varphi_j\in[-\tfrac{3\pi}{2},-\tfrac{\pi}{2}]$,
  where $\cos\varphi_j\le 0$: the $j$-th would-be impact falls on or below
  the diameter, i.e. on the open half of the circle, and the ray exits after
  only $j-1<N$ reflections. (Equality $\varphi_j=-\pi/2$ means the ray hits
  the rim corner $(-R,0)$ exactly; this marginal ray is the threshold itself.)

Solving $\varphi_N=-\pi/2$, i.e. $(2N-1)\theta-(N-1)\pi=-\pi/2$, gives the
critical incidence angle for the $N$-th reflection to occur:
$\theta>(2N-3)\pi/\bigl(2(2N-1)\bigr)$. A ray makes **at most $N$
reflections** iff it fails to make $N+1$, i.e.

$$\theta\le\theta_N\equiv\frac{(2N-1)\pi}{2(2N+1)} .$$

With $x=R\sin\theta$ the threshold transverse coordinate is
$x_N=R\sin\theta_N$, i.e.

$$\boxed{\;x_N=R\sin\!\frac{(2N-1)\pi}{2(2N+1)}
=R\cos\!\frac{\pi}{2N+1}\;}$$

(the two forms agree because
$\tfrac{\pi}{2}-\tfrac{(2N-1)\pi}{2(2N+1)}=\tfrac{\pi}{2N+1}$).

**Checks.**

* $N=1$: $x_1=R\cos\frac{\pi}{3}=\dfrac{R}{2}$. Directly: the second impact
  has azimuth $\varphi_2=3\theta-\pi$ and reaches the rim when
  $3\theta=\pi/2$, i.e. $\theta=\pi/6$, $x=R\sin\frac{\pi}{6}=R/2$. ✔
* First values: $x_1=0.500\,R$, $x_2=R\cos\frac{\pi}{5}\approx0.809\,R$,
  $x_3=R\cos\frac{\pi}{7}\approx0.901\,R$: strictly increasing, matching the
  staircase of Fig. 2e.
* $N\to\infty$: $x_N\to R$: grazing rays bounce arbitrarily many times near
  the rim, so the staircase accumulates at $|x|=R$. ✔

---

## B.1 — The coefficients $\alpha$ and $\beta$ (2.0 pts)

**Set-up (Fig. 2f).** The absorbing container has radius $a$ and its centre
$C$ sits on the symmetry axis a distance $R/2$ from $O$, inside the dome:
$C=(0,R/2)$ in the conventions of §0. Sunlight is a uniform parallel beam of
intensity $I$ (power per unit area) along $+y$.

**Distance from $C$ to a once-reflected ray.** The ray reflected at $P_1$
follows the line through $P_1=(R\sin\theta,R\cos\theta)$ with direction
$\hat d_r=(-\sin2\theta,-\cos2\theta)$ (Eq. (1)). Its perpendicular distance
from $C$ is the 2D cross product

$$d(\theta)=\bigl|(C-P_1)\times\hat d_r\bigr|
=\bigl|(-R\sin\theta)(-\cos2\theta)-\bigl(\tfrac R2-R\cos\theta\bigr)(-\sin2\theta)\bigr|.$$

Expanding,
$d(\theta)=\bigl|R(\sin\theta\cos2\theta-\cos\theta\sin2\theta)
+\tfrac R2\sin2\theta\bigr|
=\bigl|-R\sin\theta+\tfrac R2\sin2\theta\bigr|$, and since
$\tfrac12\sin2\theta=\sin\theta\cos\theta<\sin\theta$ for
$0<\theta<\pi/2$,

$$d(\theta)=R\sin\theta-\frac{R}{2}\sin2\theta
=R\sin\theta\,(1-\cos\theta)\;\ge 0 .$$

Two properties of this distance matter:

* the foot of the perpendicular lies on the *forward* ray, because
  $(C-P_1)\cdot\hat d_r=R\cos\theta-\tfrac R2\cos2\theta>0$ for
  $0<\theta<\pi/2$;
* $d(\theta)$ is strictly increasing on $(0,\pi/2)$, since
  $d'(\theta)=R(\cos\theta-\cos2\theta)=2R\sin\frac{3\theta}{2}
  \sin\frac{\theta}{2}>0$.

Therefore the once-reflected rays that strike the container are exactly those
with $0<\theta\le\theta_{\max}$ (and their mirror images), and the marginal
ray $\theta=\theta_{\max}$ is tangent to the container:
$a=d(\theta_{\max})$, i.e.

$$a=R\sin\theta_{\max}-\frac{R}{2}\sin(2\theta_{\max}).$$

Comparing with $a=\alpha\sin\theta_{\max}+\beta\sin(2\theta_{\max})$:

$$\boxed{\;\alpha=R,\qquad \beta=-\frac{R}{2}\;}$$

---

## B.2 — The power ratio $P/P_0$ (1.5 pts)

Work per unit length $L$ of the cylinders; write $I$ for the solar intensity.

**Without the mirror** the absorbing cylinder intercepts a strip of sunlight
of width $2a$ (its projected width), so

$$P_0=2a\,L\,I .$$

**With the mirror**, partition the incoming beam using $|x|=R\sin\theta$:

* $|x|<a$: the vertical ray meets the container disk before reaching the
  mirror — direct absorption. (This requires the container to sit strictly
  inside the dome, $a<R/2$, which the numbers of B.3 confirm.) Collected
  power $2aLI$.
* $a<|x|\le R\sin\theta_{\max}$: the ray passes the container
  ($|x|\ge a$ misses the disk), reflects once on the mirror, and because
  $\theta=\arcsin(|x|/R)\le\theta_{\max}$ its distance
  $d(\theta)\le a$ from $C$ — it is absorbed after exactly one reflection.
  Collected power $2\bigl(R\sin\theta_{\max}-a\bigr)LI$.
* $|x|>R\sin\theta_{\max}$ ($\theta>\theta_{\max}$): the reflected ray misses
  the container (monotonicity of $d$ and the definition of $\theta_{\max}$),
  and by the problem's stipulation no absorbed ray reflects more than once,
  so these rays are never collected.

Adding the two collected contributions,

$$P=2aLI+2\bigl(R\sin\theta_{\max}-a\bigr)LI=2RLI\,\sin\theta_{\max} .$$

The ratio is

$$\frac{P}{P_0}=\frac{2RLI\sin\theta_{\max}}{2aLI}
=\frac{R\sin\theta_{\max}}{R\sin\theta_{\max}(1-\cos\theta_{\max})}
\quad\Longrightarrow\quad
\boxed{\;\frac{P}{P_0}=\frac{1}{1-\cos\theta_{\max}}
=\frac{1}{2\sin^{2}(\theta_{\max}/2)}\;}$$

**Checks.**

* Energy bookkeeping is transparent: *every* ray with
  $|x|\le R\sin\theta_{\max}$ ends in the container exactly once (directly or
  after one bounce), no other ray is collected, and no ray is counted twice.
* $\theta_{\max}\to\pi/2$: $a\to R$ and $P/P_0\to1$ — a container as wide as
  the whole capture strip gains nothing from the mirror. ✔
* $\theta_{\max}\to0$: $P/P_0\approx2/\theta_{\max}^2\to\infty$ — an
  arbitrarily narrow container at the focus still collects a finite-width
  strip. ✔
* Since $1-\cos\theta_{\max}\le1$, the concentration ratio satisfies
  $P/P_0\ge1$ always: the mirror never hurts. ✔

---

## B.3 — Container radius for $P=5P_0$ with $R=1.0$ m (0.5 pts)

Impose the condition on the result of B.2:

$$\frac{1}{1-\cos\theta_{\max}}=5
\quad\Longrightarrow\quad
\cos\theta_{\max}=\frac45 ,\qquad
\sin\theta_{\max}=\frac35 ,$$

where the root with $0<\theta_{\max}<\pi/2$
($\theta_{\max}=\arccos\frac45\approx36.87^\circ$) is the physical branch of
the incidence angle. Substituting into B.1 with $R=1.0$ m:

$$a=R\sin\theta_{\max}\bigl(1-\cos\theta_{\max}\bigr)
=(1.0\ \text{m})\times\frac35\times\frac15
=\frac{3}{25}\ \text{m}=0.12\ \text{m}.$$

$$\boxed{\;a=12\ \text{cm}\;}$$

**Consistency of the stipulation.** All absorbed rays have
$\theta\le36.9^\circ$ and are absorbed at the first encounter with the
container, so "reflects at most once" is respected; a scan of the outgoing
segments of all rays with $\theta>\theta_{\max}$ (including their second and
later bounces, e.g. the second impact at azimuth $3\theta-\pi$) shows they
never pass closer to $C=(0,R/2)$ than the marginal value $a$, so no
multiply-reflected ray is absorbed. Also $a=0.12$ m $<R/2=0.50$ m: the
container does not touch the mirror, as Fig. 2f assumes. ✔

---

## C.1 — Slope and intercept of the reflected ray $A$ (0.5 pts)

From §0, ray $A$ is incident at angle $\theta$, reflects at
$P_1=(R\sin\theta,R\cos\theta)$, and leaves along
$\hat d_r=(-\sin2\theta,-\cos2\theta)$. Its slope (Fig. 2g convention, line
$y=m_Ax+b_A$) is

$$m_A=\frac{d_y}{d_x}=\frac{-\cos2\theta}{-\sin2\theta}
\quad\Longrightarrow\quad \boxed{\;m_A=\cot(2\theta)\;}$$

and the intercept follows from the point-slope form
$y-R\cos\theta=\cot(2\theta)\,(x-R\sin\theta)$:

$$b_A=R\cos\theta-R\sin\theta\cot2\theta
=R\,\frac{\cos\theta\sin2\theta-\sin\theta\cos2\theta}{\sin2\theta}
=R\,\frac{\sin(2\theta-\theta)}{\sin2\theta}
=\frac{R\sin\theta}{2\sin\theta\cos\theta},$$

$$\boxed{\;b_A=\frac{R}{2\cos\theta}\;}$$

(In the hint's parametrization $m_A=K_1\cot(K_2\theta)$,
$b_A=R\,K_3/\cos(K_4\theta)$: $K_1=1$, $K_2=2$, $K_3=\tfrac12$, $K_4=1$.)

**Signs (Fig. 2g).** For $0<\theta<\pi/4$ the reflected ray points downward to
the left and $m_A>0$: the line crosses the $x$-axis at
$x=-b_A/m_A=-\dfrac{R}{2\cos\theta}\tan 2\theta<0$, which lies between $O$ and
$-R$ exactly for $0<\theta<\pi/6$ — the single-reflection regime of A.1. The
$y$-intercept $b_A=R/(2\cos\theta)\ge R/2$ sits above the centre and tends to
the paraxial focus $R/2$ as $\theta\to0$. Cross-check with A.1: at
$\theta=\pi/6$ the $x$-intercept is exactly $-R$, i.e. the threshold ray
$x_1=R/2$ is reflected precisely into the rim corner $(-R,0)$. ✔

---

## C.2 — Ray $B$ expanded to first order in $\Delta\theta$ (2.0 pts)

Ray $B$ is parallel to $A$ but incident at $\theta+\Delta\theta$,
$\Delta\theta\ll\theta$; by C.1 its reflected line has
$m_B=\cot(2\theta+2\Delta\theta)$ and $b_B=\dfrac{R}{2\cos(\theta+\Delta\theta)}$.
Taylor-expanding to first order:

* with $\dfrac{d}{du}\cot u=-\csc^{2}u=-\dfrac{1}{\sin^{2}u}$ at $u=2\theta$,
  $\Delta u=2\Delta\theta$:

$$\boxed{\;m_B=\cot(2\theta)-\frac{2\,\Delta\theta}{\sin^{2}(2\theta)}
+O(\Delta\theta^{2})\;}$$

* with $\dfrac{d}{d\theta}\sec\theta=\sec\theta\tan\theta
=\dfrac{\sin\theta}{\cos^{2}\theta}$:

$$\boxed{\;b_B=\frac{R}{2\cos\theta}
+\frac{R\sin\theta}{2\cos^{2}\theta}\,\Delta\theta
+O(\Delta\theta^{2})\;}$$

($m_B$ is dimensionless and carries no $R$; $b_B$ keeps its dimension of
length through the prefactor $R$. The neglected terms are
$O(\Delta\theta^2)$, which fixes the approximation order.)

---

## C.3 — Limiting intersection $(X_c,Y_c)$: the caustic (1.0 pts)

The intersection of the two reflected lines obeys
$m_AX+b_A=m_BX+b_B$, so for finite $\Delta\theta$

$$X(\Delta\theta)=\frac{b_B-b_A}{m_A-m_B},\qquad Y=m_AX+b_A .$$

As $\Delta\theta\to0$ this is $0/0$; dividing the first-order increments from
C.2 (equivalently, l'Hôpital in $\Delta\theta$),

$$X_c=-\,\frac{db/d\theta}{dm/d\theta}
=-\frac{\dfrac{R\sin\theta}{2\cos^{2}\theta}}{-\dfrac{2}{\sin^{2}2\theta}}
=\frac{R\sin\theta\,\sin^{2}2\theta}{4\cos^{2}\theta}
=\frac{R\sin\theta\cdot4\sin^{2}\theta\cos^{2}\theta}{4\cos^{2}\theta},$$

$$\boxed{\;X_c=R\sin^{3}\theta\;}$$

Then

$$Y_c=m_AX_c+b_A
=\frac{R\sin^{3}\theta\cos2\theta}{2\sin\theta\cos\theta}
+\frac{R}{2\cos\theta}
=\frac{R\bigl(1+\sin^{2}\theta\cos2\theta\bigr)}{2\cos\theta}.$$

The bracket simplifies with
$1+\sin^{2}\theta\cos2\theta
=1+(1-\cos^{2}\theta)(2\cos^{2}\theta-1)
=3\cos^{2}\theta-2\cos^{4}\theta$, giving

$$\boxed{\;Y_c=\frac{R}{2}\,\bigl(3\cos\theta-2\cos^{3}\theta\bigr)\;}$$

**Equivalent nephroid form.** Using
$\sin3\theta=3\sin\theta-4\sin^{3}\theta$ and
$\cos3\theta=4\cos^{3}\theta-3\cos\theta$,

$$X_c=\frac{R}{4}\bigl(3\sin\theta-\sin3\theta\bigr),\qquad
Y_c=\frac{R}{4}\bigl(3\cos\theta-\cos3\theta\bigr),$$

the standard parametrization of a nephroid of characteristic radius $R/4$ —
the bright curve of Figs. 2a–2b.

**Checks.**

* $\theta\to0$: $(X_c,Y_c)\to(0,R/2)$ — the cusp sits at the paraxial focal
  point, exactly where Part B places the container. ✔
* $\theta\to\pi/2$: $(X_c,Y_c)\to(R,0)$ — the caustic wing terminates at the
  mirror rim. ✔
* $X_c$ is odd and $Y_c$ even in $\theta$: left and right wings are mirror
  symmetric, as in Fig. 2a. ✔
* Numerical spot check at $\theta=0.5$ rad: intersecting the lines for
  $\Delta\theta=10^{-4},10^{-5},10^{-6}$ gives $(X,Y)$ converging linearly in
  $\Delta\theta$ to $(0.11020\,R,\,0.64050\,R)$, matching the formulas above
  to all shown digits. ✔

---

## C.4 — Paraxial form $Y_c=v\,|X_c|^{p/q}+u$ (1.0 pts)

For $\theta\ll1$ expand the results of C.3. With
$\sin\theta=\theta-\theta^{3}/6+O(\theta^{5})$:

$$X_c=R\,\theta^{3}\bigl(1+O(\theta^{2})\bigr)
\quad\Longrightarrow\quad
\theta^{2}=\left|\frac{X_c}{R}\right|^{2/3}\bigl(1+O(\theta^{2})\bigr),$$

and with $\cos\theta=1-\theta^{2}/2+O(\theta^{4})$,
$\cos^{3}\theta=1-\tfrac32\theta^{2}+O(\theta^{4})$:

$$Y_c=\frac{R}{2}\Bigl(3\bigl(1-\tfrac{\theta^{2}}{2}\bigr)
-2\bigl(1-\tfrac{3\theta^{2}}{2}\bigr)+O(\theta^{4})\Bigr)
=\frac{R}{2}+\frac{3R}{4}\,\theta^{2}+O(\theta^{4}).$$

Eliminating $\theta^{2}$ between the two (the correction terms are
$O(\theta^{4})$ in $Y_c$, i.e. relative order $O(\theta^{2})=O(|X_c/R|^{2/3})$,
beyond the requested accuracy),

$$Y_c=\frac{R}{2}+\frac{3R}{4}\left|\frac{X_c}{R}\right|^{2/3}
=\frac{R}{2}+\frac{3}{4}\,R^{1/3}\,|X_c|^{2/3}.$$

Comparing with $Y_c=v\,|X_c|^{p/q}+u$:

$$\boxed{\;u=\frac{R}{2},\qquad v=\frac{3}{4}\,R^{1/3}=\frac{3\sqrt[3]{R}}{4},
\qquad p=2,\ q=3\ \left(\frac pq=\frac23\right)\;}$$

**Checks.**

* Dimensions: $[u]=L$ and $[v\,|X_c|^{2/3}]=L^{1/3}\!\cdot L^{2/3}=L$. ✔
* $u=R/2$ is precisely the cusp height found in C.3 and the container
  position of Part B — the cooker puts the absorber at the brightest point of
  the caustic. ✔
* $v>0$: the caustic rises away from the cusp toward the rim, matching the
  upward-opening wings of Figs. 2a–2b. ✔
* The absolute value is required and consistent: $X_c$ is odd in $\theta$
  while $Y_c-R/2$ is even, so the two wings obey one law in $|X_c|$. ✔
* Approximation order: with $\cos^{3}\theta=1-\tfrac32\theta^{2}
  +\tfrac78\theta^{4}+O(\theta^{6})$, the exact expansion of the caustic
  ordinate is
  $Y_c=\dfrac{R}{2}+\dfrac{3R}{4}\theta^{2}-\dfrac{13R}{16}\theta^{4}
  +O(\theta^{6})$;
  after eliminating $\theta$ via $|X_c|=R\sin^{3}\theta$ (which contributes
  $|X_c/R|^{2/3}=\theta^{2}\bigl(1-\tfrac13\theta^{2}+O(\theta^{4})\bigr)$),
  the leading error of the power law is
  $-\dfrac{9}{16}\,R^{-1/3}\,|X_c|^{4/3}$, i.e. the law is accurate through
  $O\bigl(|X_c|^{2/3}\bigr)$ inclusive. Both coefficients were verified by
  numeric series fits (tending to $-0.8125$ and $-0.5625$). ✔

---

## Consistency audit across all parts

* **A.1↔ geometry:** $x_1=R/2$ reproduces the direct rim condition
  $3\theta=\pi/2$; $x_N\uparrow R$ matches the diverging bounce count near
  grazing incidence and the staircase of Fig. 2e.
* **B.1→B.2→B.3:** the tangency law feeds the flux ratio, which is inverted
  exactly at $\cos\theta_{\max}=4/5$ (a 3-4-5 triangle), giving $a=12$ cm with
  units carried through; energy bookkeeping $P=2RLI\sin\theta_{\max}$ counts
  every ray once.
* **C.1→C.2→C.3→C.4:** the reflected-line parameters expand and divide to the
  caustic $(R\sin^{3}\theta,\frac R2(3\cos\theta-2\cos^{3}\theta))$, whose
  small-$\theta$ limit is the semicubical cusp $Y_c=\frac R2+
  \frac34R^{1/3}|X_c|^{2/3}$.
* **Cross-part anchor:** the cusp of the caustic (C.3, C.4) and the solar
  cooker's container position (B) coincide at $(0,R/2)$, the paraxial focus
  of the half-cylindrical mirror — one convention, three independent
  appearances, all consistent.

All results above were derived solely from the supplied problem paper, its
rendered pages (Figs. 2c–2g), and the statement transcription; numeric
checks used only local scratch calculations on the derived formulas.
