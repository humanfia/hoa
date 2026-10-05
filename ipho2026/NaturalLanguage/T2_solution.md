# IPhO 2026 Theory Problem 2 — Cooking with sunlight?

In the cross-section of Fig. 2d, take the centre of the semicircle as the
origin. The reflecting arc is \(x^2+y^2=R^2\), \(y\geq 0\), and the incident
rays travel in the \(+y\)-direction. Results for negative \(x\) follow by
reflection in the \(y\)-axis.

## A.1

First label a ray by its initial point of contact with the mirror. For a ray
on the \(x>0\) side, write that point as

\[
 P_1=(R\cos\delta,R\sin\delta),
 \qquad 0<\delta\leq \frac{\pi}{2}.
\]

Thus the transverse coordinate of the incident ray is

\[
 x=R\cos\delta.
\]

The incidence angle measured from the normal is
\(\theta=\pi/2-\delta\). At each reflection the angle with the radius is
preserved. The triangle formed by the centre and two consecutive contact
points is isosceles, so the central angle between those points is

\[
 \pi-2\theta=2\delta.
\]

If the circle were complete, the polar angle of the \(k\)-th possible contact
would consequently be

\[
 \phi_k=\delta+(k-1)2\delta=(2k-1)\delta .
\]

The actual mirror contains only \(0\leq\phi\leq\pi\). While the successive
points remain on this upper semicircle, the whole chord joining two of them
also remains above the opening. Once the next possible contact is at or below
the rim, the ray leaves through the opening instead. The limiting ray with
only \(N\) reflections reaches the opposite rim at its next possible contact:

\[
 \phi_{N+1}=(2N+1)\delta_N=\pi.
\]

(The endpoint at the open rim is not an additional reflection.) Therefore

\[
 \delta_N=\frac{\pi}{2N+1},
 \qquad
 \boxed{x_N=R\cos\!\left(\frac{\pi}{2N+1}\right)} .
\]

As checks, \(x_1=R/2\), in agreement with the one-reflection limiting chord,
and \(x_N\to R^{-}\) as \(N\to\infty\). The expression has units of length,
and the thresholds on the other side are \(-x_N\) by symmetry.

## B.1

Let a ray on the \(x>0\) side strike the arc at incidence angle \(\theta\),
where the angle is measured as in Fig. 2f. Its contact point and the outward
radial unit vector are

\[
 P=(R\sin\theta,R\cos\theta),
 \qquad
 \boldsymbol n=(\sin\theta,\cos\theta).
\]

The incident unit direction is \(\boldsymbol k=(0,1)\). Specular reflection
therefore gives

\[
 \boldsymbol k_{\rm r}
 =\boldsymbol k-2(\boldsymbol k\mathbin{\cdot}\boldsymbol n)\boldsymbol n
 =(-\sin 2\theta,-\cos 2\theta).
\]

Hence the reflected line through \(P\) is

\[
 y-R\cos\theta
   =\cot(2\theta)\bigl(x-R\sin\theta\bigr),
\]

or, after simplifying its intercept,

\[
 y=\cot(2\theta)x+\frac{R}{2\cos\theta}.                 \tag{1}
\]

The centre of the container is \(C=(0,R/2)\). On the physical branch
\(0<\theta<\pi/2\), the perpendicular distance from \(C\) to (1) is

\[
\begin{aligned}
 d(\theta)
 &=\frac{\dfrac{R}{2\cos\theta}-\dfrac R2}
         {\sqrt{1+\cot^2(2\theta)}} \\
 &=\left(\frac{R}{2\cos\theta}-\frac R2\right)\sin 2\theta \\
 &=R\sin\theta(1-\cos\theta).
\end{aligned}
\]

The extremal ray that still reaches the container is tangent to it, so
\(d(\theta_{\max})=a\). Thus

\[
 a=R\sin\theta_{\max}-\frac R2\sin(2\theta_{\max}),
\]

and comparison with the form in the question gives

\[
 \boxed{\alpha=R,\qquad \beta=-\frac R2}.
\]

Both constants have units of length. Also,
\(a\sim R\theta_{\max}^3/2>0\) for small positive
\(\theta_{\max}\), which checks both the sign choice and the near-axis limit.

## B.2

Let the uniform incident irradiance be \(I\) and consider a length \(L\) of
the container. Without the mirror, the projected collecting area is \(2aL\),
so

\[
 P_0=2aLI.
\]

With the mirror present, rays with \(|x|\leq a\) hit the container directly.
On either side, the additional rays that reach the mirror and are then
absorbed extend out to

\[
 |x|=R\sin\theta_{\max}.
\]

The distance \(d(\theta)=R\sin\theta(1-\cos\theta)\) increases on the physical
branch, since

\[
 d'(\theta)=R(1-\cos\theta)(1+2\cos\theta)>0,
\]

so there is no gap in this collected interval. Its total projected width is
therefore \(2R\sin\theta_{\max}\), and flux conservation gives

\[
 P=2R\sin\theta_{\max}LI.
\]

Consequently, using the result of B.1,

\[
 \boxed{
 \frac{P}{P_0}
 =\frac{R\sin\theta_{\max}}{a}
 =\frac{1}{1-\cos\theta_{\max}}
 }.
\]

This is dimensionless. The bookkeeping also shows the physical meaning of
the gain: the mirror redirects power from a wider incident strip; it does not
create power.

## B.3

On the physical branch, the required gain gives

\[
 5=\frac{1}{1-\cos\theta_{\max}}
 \quad\Longrightarrow\quad
 \cos\theta_{\max}=\frac45,
 \qquad
 \sin\theta_{\max}=\frac35.
\]

Thus \(\theta_{\max}=\arccos(4/5)\simeq0.6435\ {\rm rad}\), and for
\(R=1.0\ {\rm m}\),

\[
 a=R\sin\theta_{\max}(1-\cos\theta_{\max})
   =(1.0\ {\rm m})\frac35\frac15
   =0.120\ {\rm m}.
\]

Therefore

\[
 \boxed{a=12.0\ {\rm cm}}.
\]

Substitution back into B.2 gives
\((R\sin\theta_{\max})/a=0.600/0.120=5.00\), as required.

## C.1

Consider first the ray on the \(x>0\) side of Fig. 2g. The figure's angle
convention gives the point of incidence and the outward unit normal as

\[
 P_A=(R\sin\theta,R\cos\theta),
 \qquad
 \boldsymbol n_A=(\sin\theta,\cos\theta).
\]

As in B.1, reflection of the incident direction \((0,1)\) gives

\[
 \boldsymbol k_{{\rm r},A}
 =(0,1)-2\cos\theta\,\boldsymbol n_A
 =(-\sin 2\theta,-\cos 2\theta).
\]

The slope of the reflected line is the ratio of these two components:

\[
 m_A=\frac{-\cos 2\theta}{-\sin 2\theta}
     =\cot(2\theta).
\]

Writing the line through \(P_A\) as \(y=m_Ax+b_A\), its intercept is

\[
\begin{aligned}
 b_A
 &=R\cos\theta-R\sin\theta\cot(2\theta)\\
 &=R\frac{\cos\theta\sin2\theta-\sin\theta\cos2\theta}
          {\sin2\theta}\\
 &=R\frac{\sin\theta}{2\sin\theta\cos\theta}
 =\frac{R}{2\cos\theta}.
\end{aligned}
\]

Thus

\[
 \boxed{m_A=\cot(2\theta),\qquad
        b_A=\frac{R}{2\cos\theta}}.
\]

The slope is dimensionless and \(b_A\) has units of length, as required for
the equation \(y=m_Ax+b_A\).

## C.2

Define

\[
 m(\theta)=\cot(2\theta),\qquad
 b(\theta)=\frac R2\sec\theta .
\]

Ray \(B\) has parameter \(\theta+\Delta\theta\). For fixed nonzero \(\theta\)
and \(|\Delta\theta|\ll|\theta|\), the needed derivatives are

\[
 m'(\theta)=-2\csc^2(2\theta),\qquad
 b'(\theta)=\frac{R\sin\theta}{2\cos^2\theta}.
\]

Taylor expansion therefore gives

\[
 \boxed{
 m_B=\cot(2\theta)
     -2\csc^2(2\theta)\,\Delta\theta
     +O\!\left((\Delta\theta)^2\right)
 }
\]

and

\[
 \boxed{
 b_B=\frac{R}{2\cos\theta}
     +\frac{R\sin\theta}{2\cos^2\theta}\,\Delta\theta
     +O\!\left(R(\Delta\theta)^2\right)
 }.
\]

Angles in radians are dimensionless, so the remainder in \(m_B\) is
dimensionless, while every term in \(b_B\) has units
of length.

## C.3

For a finite nonzero \(\Delta\theta\), let the two reflected lines intersect
at \((X(\Delta\theta),Y(\Delta\theta))\). Equating their ordinates before
taking any limit gives

\[
 m(\theta)X+b(\theta)
 =m(\theta+\Delta\theta)X+b(\theta+\Delta\theta),
\]

so

\[
 X(\Delta\theta)
 =\frac{b(\theta+\Delta\theta)-b(\theta)}
        {m(\theta)-m(\theta+\Delta\theta)}.
\]

Using the expansions from C.2 and only then taking
\(\Delta\theta\to0\),

\[
\begin{aligned}
 X(\Delta\theta)
 &=-\frac{b'(\theta)\Delta\theta
              +O\!\left(R(\Delta\theta)^2\right)}
             {m'(\theta)\Delta\theta
              +O\!\left((\Delta\theta)^2\right)}\\
 &=-\frac{b'(\theta)}{m'(\theta)}+O(R\Delta\theta).
\end{aligned}
\]

Therefore

\[
 X_c
 =-\frac{b'(\theta)}{m'(\theta)}
 =\frac{R\sin\theta}{4\cos^2\theta}\sin^2(2\theta)
 =\boxed{R\sin^3\theta}.
\]

The corresponding limiting ordinate follows from ray \(A\):

\[
\begin{aligned}
 Y_c
 &=m(\theta)X_c+b(\theta)\\
 &=R\sin^3\theta\cot(2\theta)+\frac{R}{2\cos\theta}\\
 &=\frac{R}{2\cos\theta}
   \left(1+\sin^2\theta\cos2\theta\right)\\
 &=\frac{R}{2\cos\theta}
   \left[\cos^2\theta\left(1+2\sin^2\theta\right)\right]\\
 &=\boxed{\frac R2\cos\theta\bigl(1+2\sin^2\theta\bigr)}.
\end{aligned}
\]

These expressions describe the branch generated on the \(x>0\) side. By
reflection in the \(y\)-axis, the complete caustic is

\[
 \boxed{
 X_c=\pm R\sin^3\theta,\qquad
 Y_c=\frac R2\cos\theta\bigl(1+2\sin^2\theta\bigr)
 }.
\]

Both coordinates have units of length. In the axial limit
\(\theta\to0\), the two branches meet at
\((X_c,Y_c)=(0,R/2)\), the cusp shown in Fig. 2a.

## C.4

For \(\theta\ll1\), the parametric coordinates from C.3 have the expansions

\[
\begin{aligned}
 |X_c|
 &=R\sin^3\theta
  =R\theta^3+O(R\theta^5),\\
 Y_c
 &=\frac R2\cos\theta(1+2\sin^2\theta)\\
 &=\frac R2+\frac{3R}{4}\theta^2+O(R\theta^4).
\end{aligned}
\]

To eliminate \(\theta\) with its branch fixed, take
\(0\leq\theta\ll1\) and define

\[
 z=\left(\frac{|X_c|}{R}\right)^{2/3}.
\]

Because \(|X_c|/R=\sin^3\theta\) on this branch, this definition gives
\(z=\sin^2\theta\) exactly, while
\(\cos\theta=\sqrt{1-z}\) takes the positive square-root branch. Hence

\[
\begin{aligned}
 Y_c
 &=\frac R2\sqrt{1-z}\,(1+2z)\\
 &=\frac R2\left[1+\frac32z+O(z^2)\right]\\
 &=\frac R2+\frac34R^{1/3}|X_c|^{2/3}
   +O\!\left(R^{-1/3}|X_c|^{4/3}\right).
\end{aligned}
\]

Comparison with \(Y_c=v|X_c|^{p/q}+u\) therefore yields, with \(p\) and \(q\)
chosen coprime and positive,

\[
 \boxed{
 u=\frac R2,\qquad
 v=\frac34R^{1/3},\qquad
 p=2,\qquad q=3
 }.
\]

In particular, \(p/q=2/3\). The coefficient \(u\) has units of length and
\(v\) has units \(L^{1/3}\), so \(v|X_c|^{2/3}\) also has units of length.
The absolute value incorporates both symmetric caustic branches, and at
\(X_c=0\) the law returns the cusp height \(Y_c=R/2\).
