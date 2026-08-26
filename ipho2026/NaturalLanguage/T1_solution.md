# Theory Problem 1

## A.1 Hydrostatic gate

Let $x$ point to the right and $z$ upward, and take moments about the hinge
axis through $O$. Counterclockwise moments in the plane of Figure 1a will be
positive. The hinge force then produces no moment.

The cube is entirely below both free surfaces. At any fixed height on the
cube, the pressures in the two reservoirs differ by the constant amount

\[
\Delta p=\rho _0 g\,\Delta h .
\]

It is useful to split the water pressure into two parts. A common hydrostatic
pressure field acting over the whole cube gives the usual buoyant force
$B=\rho _0ga^3$, upward through the cube's centre $C$. The remaining part
is the uniform excess pressure $\Delta p$ on the part of the cube facing the
left reservoir.

To find the resultant of that excess pressure, close the left-hand portion of
the cube by an imaginary surface in the plane of the wall. Uniform pressure on
a closed surface has neither a resultant force nor a resultant moment, so the
excess pressure on the actual cube surface is equivalent to a horizontal force
to the right on the wall opening. The opening is a vertical rectangle whose
height and out-of-plane width are, respectively,

\[
h_s=\frac{a\sqrt2}{2}=\frac{a}{\sqrt2},
\qquad w=a.
\]

Thus this force and its downward lever arm from $O$ are

\[
F_{\Delta p}=\Delta p\,wh_s
 =\rho _0g\Delta h\,\frac{a^2}{\sqrt2},
\qquad
d_{\Delta p}=\frac{h_s}{2}=\frac{a}{2\sqrt2}.
\]

Because the force acts below $O$ and points right, its moment is positive:

\[
\tau_{\Delta p}=F_{\Delta p}d_{\Delta p}
=\frac{\rho _0g\Delta h\,a^3}{4}.
\]

The weight is $W=3\rho _0ga^3$. Weight and buoyancy both act through $C$,
so together they are equivalent, for the moment balance, to a downward force

\[
W-B=2\rho _0ga^3.
\]

As shown in Figure 1a, $O$ is the midpoint of one edge of the square cross
section. Hence $OC=a/2$, perpendicular to that edge, and the horizontal
distance from $O$ to $C$ is

\[
x_C=\frac{a}{2}\cos 45^\circ=\frac{a}{2\sqrt2}.
\]

The resulting clockwise moment is therefore

\[
\tau_{W-B}=-(W-B)x_C=-\frac{\rho _0ga^4}{\sqrt2}.
\]

At the maximum permissible level difference the block is just at rotational
equilibrium. Therefore

\[
\frac{\rho _0g\Delta h\,a^3}{4}
=\frac{\rho _0ga^4}{\sqrt2},
\]

and the nonzero solution is

\[
\boxed{a=\frac{\Delta h}{2\sqrt2}}.
\]

For $\Delta h=1.41\ \mathrm{m}$,

\[
a=\frac{1.41\ \mathrm{m}}{2\sqrt2}
  =0.4985\ \mathrm{m}
  \simeq \boxed{0.499\ \mathrm{m}}
  \quad (\text{about }0.50\ \mathrm{m}).
\]

As checks, both moments have units of $\mathrm{N\,m}$, and inserting
$a=0.4985\ \mathrm{m}$ into the rearranged threshold relation
$\Delta h=2\sqrt2\,a$ gives $1.410\ \mathrm{m}$. Moreover, increasing
$\Delta h$ above this value makes the positive pressure moment dominate,
whereas below it the effective weight holds the block in the opposite sense;
the equality is therefore the required limiting condition.

## B.1 Bound orbit

Let

\[
\mathbf r=\mathbf r_+-\mathbf r_-,
\qquad r_0=100a_0,
\qquad \mathbf u=\dot{\mathbf r}
\]

be the relative position and velocity of the positron with respect to the
electron. In the centre-of-mass frame the two particles have equal speeds
$v$ in opposite directions, so their relative speed is $u_0=2v$. Each
particle is initially a distance $r_0/2$ from the centre of mass, and its
velocity is perpendicular to that radius. The given individual angular
momentum therefore gives

\[
\mu\hbar=m\frac{r_0}{2}v,
\qquad
v=\frac{2\mu\hbar}{mr_0},
\qquad
u_0=\frac{4\mu\hbar}{mr_0}.
\]

The reduced mass for the relative motion is $m_{\rm r}=m/2$. Consequently,
the total angular momentum and total mechanical energy of the pair are

\[
L=m_{\rm r}r_0u_0=2\mu\hbar,
\]

\[
E=\frac12m_{\rm r}u_0^2-\frac{ke^2}{r_0}
 =\frac{4\mu^2\hbar^2}{mr_0^2}-\frac{ke^2}{r_0}.
\]

The definition of the Bohr radius in the question is equivalent to

\[
ke^2=\frac{\hbar^2}{ma_0}.
\]

It is therefore convenient to introduce $R=r/a_0$, $R_0=100$, and the
energy scale $E_a=\hbar^2/(ma_0^2)$. The initial energy becomes

\[
\frac{E}{E_a}=\frac{4\mu^2}{R_0^2}-\frac{1}{R_0}.
\]

At either endpoint of the radial motion, $\dot r=0$. All the kinetic energy
there is angular, so

\[
E=\frac{L^2}{2m_{\rm r}r^2}-\frac{ke^2}{r},
\qquad
\frac{E}{E_a}=\frac{4\mu^2}{R^2}-\frac1R.
\]

For $\mu=4$, the conserved energy is

\[
\frac{E}{E_a}=\frac{64}{100^2}-\frac1{100}
=-\frac9{2500}<0,
\]

which confirms that the orbit is bound. The turning-point equation is then

\[
-\frac9{2500}=\frac{64}{R^2}-\frac1R,
\]

or

\[
9R^2-2500R+160000
=(R-100)(9R-1600)=0.
\]

Thus $R=100$ is the smaller turning point at the stated instant, while the
larger one is the maximum separation:

\[
\boxed{r_{\max}=\frac{1600}{9}a_0\simeq177.8a_0}.
\]

As an exact substitution check, at the second root

\[
\frac{64}{(1600/9)^2}-\frac{1}{1600/9}
=\frac{81}{40000}-\frac{225}{40000}
=-\frac9{2500},
\]

the same energy as at $R=100$. The two positive turning points together with
$E<0$ are also the expected structure of a bound Kepler orbit.

## B.2 Unbound orbit

For $\mu=15/2$, the common reduction above gives

\[
L=15\hbar,
\]

\[
\frac{E}{E_a}
=\frac{4(15/2)^2}{100^2}-\frac1{100}
=\frac1{80}>0.
\]

The positive energy already confirms that this trajectory is unbound. Write
$\kappa=ke^2=\hbar^2/(ma_0)$. Using the eccentricity given in the question,

\[
\begin{aligned}
\varepsilon
&=\sqrt{1+\frac{4L^2E}{m\kappa^2}} \\
&=\sqrt{1+
 \frac{4(15\hbar)^2[\hbar^2/(80ma_0^2)]}
 {m[\hbar^2/(ma_0)]^2}} \\
&=\sqrt{1+\frac{45}{4}}
=\frac72.
\end{aligned}
\]

To determine which asymptote is relevant, define the true anomaly $f$ from
the outward periapsis direction, positive counterclockwise. In this convention
the attractive conic is

\[
r=\frac{\ell}{1+\varepsilon\cos f},
\qquad
\ell=\frac{L^2}{m_{\rm r}\kappa}.
\]

Here

\[
\ell=\frac{(15\hbar)^2}
{(m/2)[\hbar^2/(ma_0)]}=450a_0,
\qquad
r(f=0)=\frac{450a_0}{1+7/2}=100a_0.
\]

Thus the stated configuration is exactly the periapsis. In Figure 1b the
relative position $\mathbf r$ initially points upward, while the relative
velocity and the initial positron velocity point right. Hence the angular
momentum points into the page and $f$ decreases after the stated instant.

At an asymptote, $r\to\infty$, so

\[
1+\varepsilon\cos f_\infty=0,
\qquad
\cos f_\infty=-\frac1\varepsilon=-\frac27.
\]

The future, clockwise branch is therefore

\[
f_\infty=-\cos^{-1}\!\left(-\frac27\right)
=-106.6015^\circ.
\]

The periapsis radius is directed $90^\circ$ counterclockwise from the initial
positron line of motion. Also, as $r\to\infty$, the transverse speed
$L/(m_{\rm r}r)$ vanishes, so $\mathbf u_\infty$ is parallel to the outgoing
radial asymptote. Its signed direction relative to the initial rightward line
is consequently

\[
\alpha=90^\circ+f_\infty
=\frac{\pi}{2}-\cos^{-1}\!\left(-\frac27\right)
=-\sin^{-1}\!\left(\frac27\right)
=-16.6015^\circ.
\]

Thus the requested (nonnegative) angle between the two directions is

\[
\boxed{|\alpha|=16.6^\circ}.
\]

The minus sign specifies the orientation: the outgoing relative velocity is
$16.6^\circ$ clockwise, or below, the initial positron direction in Figure
1b. The alternative solution
$f_\infty=+\cos^{-1}(-2/7)$ is the incoming, time-reversed asymptote and is
not the future branch selected by the arrows. Finally, $E>0$,
$\varepsilon>1$, and $\ell/(1+\varepsilon)=100a_0$ independently check the
unbound classification and the conic orientation.

## C.1 Threshold at a fixed angle

Take the incident photon direction as the positive $x$-axis, and write its
energy and momentum magnitude as

\[
E_\gamma=\hbar\omega,
\qquad
P=\frac{E_\gamma}{c}.
\]

Let the outgoing oxygen molecule have momentum $\mathbf p$, with magnitude
$p\geq0$ and angle $\theta$ from the incident photon. If $\mathbf q$ is the
momentum of the outgoing oxygen atom, momentum conservation gives

\[
\mathbf q=P\,\hat{\mathbf x}-\mathbf p,
\qquad
q^2=P^2+p^2-2Pp\cos\theta.
\]

The masses of $\mathrm O_2$ and $\mathrm O$ are $2m$ and $m$. Their total
kinetic energy is therefore

\[
\begin{aligned}
K(p)
&=\frac{p^2}{2(2m)}+\frac{q^2}{2m} \\
&=\frac{p^2}{4m}
  +\frac{P^2+p^2-2Pp\cos\theta}{2m} \\
&=\frac{3p^2}{4m}-\frac{Pp\cos\theta}{m}
  +\frac{P^2}{2m}.
\end{aligned}
\]

Energy conservation, with $\Delta U=U_f-U_i$, reads

\[
U_i+E_\gamma=U_f+K,
\qquad
E_\gamma-\Delta U=K.
\]

For fixed $E_\gamma$ and $\theta$, threshold dissociation occurs when the
required kinetic energy is as small as momentum conservation permits.
Completing the square gives

\[
K(p)=\frac{3}{4m}
\left(p-\frac{2P\cos\theta}{3}\right)^2
+\frac{P^2}{6m}\left(1+2\sin^2\theta\right).
\]

In the forward-angle domain shown in Figure 1c,
$0\leq\theta<\pi/2$, the unconstrained minimum respects $p\geq0$:

\[
p_*=\frac{2P\cos\theta}{3},
\qquad
K_{\min}=\frac{P^2}{6m}\left(1+2\sin^2\theta\right).
\]

The endpoint $\theta=\pi/2$ is obtained as the limit $p_*\to0$. For a
backward angle, $\cos\theta<0$, the quadratic's vertex would have negative
$p$; the constrained minimum is instead at $p=0$, with
$K_{\min}=P^2/(2m)$. Since zero momentum has no direction, for a strictly
specified backward direction this is an infimum approached as $p\to0^+$.
The requested configuration and C.2 are in the forward domain.

Define

\[
A=1+2\sin^2\theta,
\qquad
\beta=\frac{A}{6mc^2}.
\]

At the forward threshold, substituting $P=E_\gamma/c$ into energy
conservation gives

\[
E_\gamma-\Delta U
=\frac{A E_\gamma^2}{6mc^2}
=\beta E_\gamma^2.
\]

Thus the two algebraic intersections are

\[
E_{\gamma,\pm}
=\frac{1\pm\sqrt{1-4\beta\Delta U}}{2\beta}
=\frac{3mc^2}{A}
 \left[1\pm
 \sqrt{1-\frac{2A\Delta U}{3mc^2}}\right].
\]

The discriminant condition is

\[
1-\frac{2A\Delta U}{3mc^2}\geq0.
\]

It is overwhelmingly satisfied for the data in C.2. The plus root is not the
minimum threshold; moreover, it grows as $6mc^2/A$ when recoil becomes small,
outside the intended non-relativistic regime. The minus root instead tends to
$\Delta U$ as $m c^2\to\infty$, as it must when the photon momentum becomes
negligible. Therefore

\[
\boxed{
\omega_{\min}
=\frac{3mc^2}{\hbar A}
 \left[1-\sqrt{1-\frac{2A\Delta U}{3mc^2}}\right]
=\frac{2\Delta U}
 {\hbar\left[1+\sqrt{1-2A\Delta U/(3mc^2)}\right]}
},
\qquad A=1+2\sin^2\theta.
\]

The second form is obtained by rationalizing the numerator and is numerically
stable. Dimensional consistency is explicit: $\beta$ has units of inverse
energy, so $\beta E_\gamma^2$ is an energy, and every square-root argument is
dimensionless. As kinematic checks, at $\theta=0$ the two fragments have the
same velocity at the minimum and
$K_{\min}=P^2/[2(3m)]=P^2/(6m)$, the translational recoil energy of total mass
$3m$. As $\theta\to\pi/2$, the oxygen atom takes all the photon momentum and
$K_{\min}\to P^2/(2m)$, agreeing with the boundary result. For backward
angles the same threshold formula applies with $A$ replaced by $3$, in the
infimum sense described above.

## C.2 Numerical threshold excess

For $\theta=\pi/6$,

\[
A=1+2\sin^2\!\left(\frac\pi6\right)=\frac32.
\]

The physical root from C.1 then becomes

\[
E_{\gamma,\min}
=2mc^2\left(1-\sqrt{1-x}\right),
\qquad
x=\frac{\Delta U}{mc^2}.
\]

Here $x\ll1$. Applying the supplied binomial expansion,

\[
\sqrt{1-x}=1-\frac{x}{2}-\frac{x^2}{8}
-\frac{x^3}{16}+O(x^4),
\]

so

\[
\begin{aligned}
E_{\gamma,\min}-\Delta U
&=\frac{\Delta U^2}{4mc^2}
 +\frac{\Delta U^3}{8m^2c^4}
 +O\!\left(\frac{\Delta U^4}{m^3c^6}\right) \\
&=\frac{\Delta U^2}{4mc^2}
 \left[1+\frac{\Delta U}{2mc^2}
 +O\!\left(\frac{\Delta U^2}{m^2c^4}\right)\right].
\end{aligned}
\]

For a cancellation-free exact check, the same excess can be written as

\[
E_{\gamma,\min}-\Delta U
=\frac{\Delta U^2}
 {mc^2\left(1+\sqrt{1-x}\right)^2}.
\]

Using $1\ \mathrm{u}\,c^2=931.494\ \mathrm{MeV}$,

\[
mc^2=(16.0)(931.494\ \mathrm{MeV})
=1.49039\times10^{10}\ \mathrm{eV},
\]

and hence

\[
x=\frac{1.10\ \mathrm{eV}}
        {1.49039\times10^{10}\ \mathrm{eV}}
=7.3806\times10^{-11}.
\]

The first omitted relative correction to the leading result is only
$x/2=3.69\times10^{-11}$. Therefore

\[
\begin{aligned}
\hbar\omega_{\min}-\Delta U
&\simeq\frac{(1.10\ \mathrm{eV})^2}
 {4(1.49039\times10^{10}\ \mathrm{eV})} \\
&=2.0297\times10^{-11}\ \mathrm{eV}
 \simeq\boxed{2.03\times10^{-11}\ \mathrm{eV}}.
\end{aligned}
\]

Using the displayed $931.494\ \mathrm{MeV}$ conversion, the cancellation-free
exact expression gives $2.02967\times10^{-11}\ \mathrm{eV}$, agreeing with
the controlled expansion. The result is positive, as expected: even at
threshold, some photon energy in excess of the dissociation energy is required
to carry the fragments' recoil momentum.
