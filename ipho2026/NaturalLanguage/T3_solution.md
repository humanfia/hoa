# Theory Problem 3 — Chasing the absolute zero

Throughout the solution, heat and work are positive when they enter the
paramagnetic torus. Thus the first law will be written as

\[
 dU=\delta Q+\delta W.
\]

The fields are treated as uniform over the thin torus, as stipulated. When a
field is changed, its direction is kept fixed; \(H,B,M\) denote the signed
components along that direction (and are positive for the orientation chosen
with the current). This lets the signs of \(dB\) and \(dM\) keep track of the
direction of energy transfer.

## A. Work in the paramagnetic torus

### A.1 Field inside the torus

Choose an Ampèrian circle running once around the torus at its mean radius
\(R\). It links all \(N\) turns. Since \(H\) is approximately constant and
tangent to this circle,

\[
 \oint \mathbf H\mathbin{\cdot}d\boldsymbol\ell
 =H(2\pi R)=NI.
\]

The torus volume is its cross-sectional area times its mean circumference,

\[
 V=(2\pi R)A.
\]

Consequently,

\[
 \boxed{H=\frac{NI}{2\pi R}=\frac{NIA}{V}}.
\]

As a dimensional check, \(A/V\) has units \(\mathrm{m^{-1}}\), so the result
has units \(\mathrm{A\,m^{-1}}\), as a magnetic-field strength must.

### A.2 Work supplied while the magnetic induction changes

The magnetic flux through one turn is \(\Phi=BA\). Faraday's law therefore
gives the induced emf around all turns as

\[
 \mathcal E_{\mathrm{ind}}=-N\frac{d\Phi}{dt}
 =-NA\frac{dB}{dt}.
\]

Because the wire resistance is negligible, the external source must provide
the opposite voltage, \(\mathcal E_{\mathrm{ext}}=NA\,dB/dt\). Its power
delivered to the coil-field system is

\[
 P_{\mathrm{emf}}=I\mathcal E_{\mathrm{ext}}
 =NIA\frac{dB}{dt}=VH\frac{dB}{dt},
\]

where A.1 was used in the last equality. Hence the work done by the source is

\[
 \boxed{\delta W_{\mathrm{emf}}=VH\,dB}.
\]

The sign has physical content: increasing \(B\) at positive \(H\) requires
positive source work, whereas decreasing \(B\) gives
\(\delta W_{\mathrm{emf}}<0\), meaning that energy is returned to the source.
Also, \(\mathrm{m^3}\,(\mathrm{A\,m^{-1}})\,\mathrm{T}=\mathrm{A\,m^2\,T}=\mathrm{J}\),
confirming the dimensions.

### A.3 Work done on the paramagnetic material

Using

\[
 B=\mu_0(H+M), \qquad dB=\mu_0(dH+dM),
\]

the source work separates as

\[
 \delta W_{\mathrm{emf}}
 =\mu_0VH\,dH+\mu_0VH\,dM.
\]

For a vacuum core, \(M=0\), and the first term is precisely the change of
vacuum magnetic-field energy:

\[
 \delta W_{\mathrm{vac}}=\mu_0VH\,dH
 =d\!\left(\frac{\mu_0VH^2}{2}\right).
\]

Subtracting this vacuum contribution leaves the work entering the material:

\[
 \boxed{\delta W
 =\delta W_{\mathrm{emf}}-\delta W_{\mathrm{vac}}
 =\mu_0VH\,dM}.
\]

This decomposition gives two immediate consistency checks. If the core is
vacuum, \(M=0\) throughout and the material term vanishes. For a paramagnet
magnetized quasistatically at \(H>0\), \(dM>0\) and the material receives
positive work, in agreement with the adopted sign convention.

## B. Heat and temperature in the paramagnetic torus

The given equation of state and heat capacity are

\[
 TMV=nKH,
 \qquad
 C_M=\frac{n\lambda}{T^2},
\]

and the internal-energy differential is \(dU=C_M\,dT\). We continue to use
\(dU=\delta Q+\delta W\), with \(\delta W=\mu_0VH\,dM\).

### B.1 Isothermal change

At fixed temperature, \(dT=0\), so the stated internal-energy relation gives
\(dU=0\). The equation of state becomes

\[
 M=\frac{nK}{VT}H,
 \qquad
 dM=\frac{nK}{VT}\,dH.
\]

The first law therefore requires the heat entering the torus to be the
negative of the magnetic work entering it:

\[
 \delta Q=-\delta W
 =-\mu_0VH\,dM
 =-\frac{\mu_0nK}{T}H\,dH.
\]

Integrating as the field magnitude changes from \(H_i\) to \(H_f\),

\[
 \boxed{
 Q=\frac{\mu_0nK}{2T}\left(H_i^2-H_f^2\right)
 }.
\]

The volume in the work expression cancels the \(1/V\) in \(dM\). If the
torus is magnetized isothermally, \(H_f>H_i\), then \(Q<0\): magnetic work
enters the material and the same energy must leave as heat because \(U\) is
unchanged. During isothermal demagnetization, \(H_f<H_i\), the torus instead
absorbs the positive heat \(Q\).

### B.2 Adiabatic change

For an adiabatic process, \(\delta Q=0\), and hence

\[
 \frac{n\lambda}{T^2}\,dT
 =dU=\delta W=\mu_0VH\,dM.
\]

It is essential here to differentiate both \(H\) and \(T\) in the equation
of state:

\[
 dM=\frac{nK}{V}
 \left(\frac{dH}{T}-\frac{H}{T^2}\,dT\right).
\]

Substitution gives

\[
 \frac{n\lambda}{T^2}\,dT
 =\mu_0nK\left(\frac{H}{T}\,dH
 -\frac{H^2}{T^2}\,dT\right).
\]

After collecting the \(dT\) terms, both the number of moles \(n\) and the
volume \(V\) have canceled:

\[
 \frac{dT}{T}
 =\frac{\mu_0KH\,dH}{\lambda+\mu_0KH^2}
 =\frac12\,d\!\ln\!\left(\lambda+\mu_0KH^2\right).
\]

Integrating from \((H_i,T_i)\) to \((H_f,T_f)\) yields the adiabatic
invariant

\[
 \frac{T}{\sqrt{\lambda+\mu_0KH^2}}=\text{constant},
\]

and therefore

\[
 T_f=T_i\sqrt{
 \frac{\lambda+\mu_0KH_f^2}{\lambda+\mu_0KH_i^2}}
\]

or

\[
 \boxed{
 \Delta T=T_f-T_i
 =T_i\left[
 \sqrt{\frac{\lambda+\mu_0KH_f^2}
 {\lambda+\mu_0KH_i^2}}-1
 \right]
 }.
\]

The cancellations have a physical origin: both \(U\) and the magnetic work
are extensive in the amount of material, while the \(1/V\) in the
magnetization cancels the explicit material volume in the work. For a unit
check, \(C_M=n\lambda/T^2\) implies that \(\lambda\) has units
\(\mathrm{J\,K\,mol^{-1}}\). The equation of state gives
\([K]=\mathrm{K\,m^3\,mol^{-1}}\), so \(\mu_0KH^2\) has the same units as
\(\lambda\), making the square-root ratio dimensionless. Finally,
\(H_f=H_i\) gives \(\Delta T=0\), while adiabatic demagnetization
\(H_f<H_i\) gives \(\Delta T<0\), as expected for magnetic cooling.

## C. Carnot refrigerator using the paramagnetic torus

### C.1 Temperatures and heat-transfer processes

In the supplied \(H\)-versus-\(T\) diagram, states 1 and 4 lie on the
right-hand vertical line, so that line is \(T=T_h\). States 2 and 3 lie on
the left-hand vertical line, which is \(T=T_c\). Thus the four directed legs
are

- \(1\to2\): adiabatic demagnetization from \(T_h\) to \(T_c\);
- \(2\to3\): the cold isotherm at \(T_c\), on which the torus absorbs
  \(Q_c\) from the cold reservoir;
- \(3\to4\): adiabatic magnetization from \(T_c\) to \(T_h\);
- \(4\to1\): the hot isotherm at \(T_h\), on which the torus rejects
  \(Q_h\) to the hot reservoir.

Indeed, \(H\) decreases on \(2\to3\), so B.1 gives positive heat into the
torus. On \(4\to1\), \(H\) increases and B.1 gives negative heat into the
torus, whose positive magnitude is the heat \(Q_h\) delivered to the hot
reservoir.

### C.2 Relation among the four magnetizations

The adiabatic invariant from B.2 can be recast in terms of \(M\). Using
\(H=TMV/(nK)\), squaring and inverting the invariant gives

\[
 \frac{\lambda}{T^2}
 +\frac{\mu_0V^2}{n^2K}M^2
 =\text{constant on an adiabat}.
\]

Write \(a=\mu_0V^2/(n^2K)\). Applied to the adiabat \(1\to2\), this says

\[
 a\left(M_1^2-M_2^2\right)
 =\lambda\left(\frac{1}{T_c^2}-\frac{1}{T_h^2}\right).
\]

The other adiabat, \(3\to4\), gives

\[
 a\left(M_4^2-M_3^2\right)
 =\lambda\left(\frac{1}{T_c^2}-\frac{1}{T_h^2}\right).
\]

The right-hand sides are equal, so
\(M_1^2-M_2^2=M_4^2-M_3^2\). Since each \(M_i\) denotes a magnitude, the
physical branch is nonnegative:

\[
 \boxed{M_1=\sqrt{M_2^2+M_4^2-M_3^2}}.
\]

### C.3 Temperature of the liquid helium after one cycle

First account for the supplied material data. The \(2.0\) mol of potassium
chromate has mass

\[
 m_s=(2.0\ \mathrm{mol})(0.19\ \mathrm{kg\,mol^{-1}})
 =0.38\ \mathrm{kg},
\]

and hence torus volume

\[
 V=\frac{m_s}{\rho_s}
 =\frac{(2.0)(0.19)}{2730}
 =1.39194\times10^{-4}\ \mathrm{m^3}.
\]

This volume would be needed to calculate the individual magnetizations from
\(M=nKH/(VT)\). It does not appear in the heat on an isotherm, because the
explicit \(V\) in \(\delta W=\mu_0VH\,dM\) cancels the \(1/V\) in
\(dM=nK\,dH/(VT)\).

All four stated fields provide an independent closure check. For a reversible
Carnot cycle, \(Q_h/T_h=Q_c/T_c\). The magnitudes from B.1 are

\[
 Q_h=\frac{\mu_0nK}{2T_h}\left(H_1^2-H_4^2\right),
 \qquad
 Q_c=\frac{\mu_0nK}{2T_c}\left(H_2^2-H_3^2\right).
\]

Consequently,

\[
 \frac{T_h}{T_c}
 =\sqrt{\frac{H_1^2-H_4^2}{H_2^2-H_3^2}}
 =\sqrt{\frac{411624^2-240446^2}
 {311306^2-204618^2}}
 =1.42403>1.
\]

Thus the four field values are mutually consistent with a refrigerator
operating between a hotter and a colder reservoir. During this first cycle
the cold reservoir is initially at \(T_c=1.00\ \mathrm{K}\). The heat drawn
from it on \(2\to3\) is therefore

\[
\begin{aligned}
 Q_c
 &=\frac{(4\pi\times10^{-7}\ \mathrm{N\,A^{-2}})
 (2.0\ \mathrm{mol})(1.87\times10^{-6}\ \mathrm{K\,m^3\,mol^{-1}})}
 {2(1.00\ \mathrm{K})}\\
 &\quad\times\left[(311306\ \mathrm{A\,m^{-1}})^2
 -(204618\ \mathrm{A\,m^{-1}})^2\right]\\
 &=0.129346\ \mathrm{J}.
\end{aligned}
\]

The units reduce to joules because
\([\mu_0nKH^2/T]=\mathrm{N\,m}\).

The helium volume is \(1.00\ \mathrm{L}=1.00\times10^{-3}\ \mathrm{m^3}\),
so its mass and total heat capacity are

\[
 m_{\mathrm{He}}=(130\ \mathrm{kg\,m^{-3}})
 (1.00\times10^{-3}\ \mathrm{m^3})=0.130\ \mathrm{kg},
\]

\[
 C_{\mathrm{He}}=m_{\mathrm{He}}c
 =(0.130\ \mathrm{kg})(100\ \mathrm{J\,kg^{-1}K^{-1}})
 =13.0\ \mathrm{J\,K^{-1}}.
\]

Energy conservation for the helium gives
\(Q_c=C_{\mathrm{He}}(1.00\ \mathrm{K}-T_f)\). Hence

\[
 T_f=1.00\ \mathrm{K}-\frac{0.129346\ \mathrm{J}}
 {13.0\ \mathrm{J\,K^{-1}}}
 =0.990050\ldots\ \mathrm{K},
\]

so, to the precision of the supplied thermal data,

\[
 \boxed{T_f\approx0.990\ \mathrm{K}}.
\]

### C.4 Time required for continuous cooling

Let \(dQ_c>0\) be the heat extracted from the cooled body in one
infinitesimal cycle, and let \(dQ_h>0\) be the heat delivered to the hot
reservoir. If the body's instantaneous temperature changes by
\(dT_c<0\), its constant heat capacity gives

\[
 dQ_c=-C_c\,dT_c.
\]

Reversibility supplies the stated Carnot relation, while energy conservation
relates the work input to the two heat magnitudes:

\[
 \frac{dQ_c}{dQ_h}=\frac{T_c}{T_h},
 \qquad
 P\,dt=dW=dQ_h-dQ_c.
\]

Eliminating \(dQ_h\) and then using the heat-capacity relation gives

\[
 P\,dt=dQ_c\left(\frac{T_h}{T_c}-1\right)
 =-C_c\left(\frac{T_h}{T_c}-1\right)dT_c.
\]

Integrate from \(t=0\), when \(T_c=T_0\), to time \(t\), when \(T_c=T\):

\[
\begin{aligned}
 Pt
 &=-C_c\int_{T_0}^{T}\left(\frac{T_h}{T_c}-1\right)dT_c\\
 &=C_c\left[T_h\ln\!\left(\frac{T_0}{T}\right)+T-T_0\right].
\end{aligned}
\]

Therefore

\[
 \boxed{
 t=\frac{C_c}{P}
 \left[T_h\ln\!\left(\frac{T_0}{T}\right)+T-T_0\right]
 }.
\]

The bracket has units of kelvin, while \(C_c/P\) has units
\(\mathrm{s\,K^{-1}}\), so \(t\) is measured in seconds. It vanishes at
\(T=T_0\). For refrigeration, \(0<T<T_0<T_h\), and the integral form shows
directly that \(t>0\). The differential cooling law obtained before
integration is

\[
 \frac{dT_c}{dt}=-\frac{P\,T_c}{C_c(T_h-T_c)},
\]

which is also recovered by differentiating the boxed expression for
\(t(T)\).

### C.5 Overall coefficient of performance

Over all cycles, the total heat removed from the body is

\[
 Q_c^{\mathrm{tot}}=C_c(T_0-T),
\]

whereas the total work input, using C.4, is

\[
 W=Pt=C_c\left[T_h\ln\!\left(\frac{T_0}{T}\right)+T-T_0\right].
\]

The overall coefficient of performance is consequently

\[
 \boxed{
 \mathrm{COP}
 =\frac{T_0-T}
 {T_h\ln\!\left(T_0/T\right)+T-T_0}
 }.
\]

Both numerator and denominator have units of temperature, so the COP is
dimensionless; both are positive for \(0<T<T_0<T_h\). There are two useful
consistency checks. First, differentiating the cumulative formulas gives

\[
 \frac{dQ_c^{\mathrm{tot}}}{dW}
 =\frac{T}{T_h-T},
\]

the instantaneous Carnot-refrigerator COP at the current cold-side
temperature, exactly as follows from the differential heat and work balance
in C.4. Second, as the total temperature drop tends to zero,

\[
 \lim_{T\to T_0}\mathrm{COP}
 =\frac{T_0}{T_h-T_0},
\]

which is the same instantaneous COP evaluated at the initial temperature.
Thus the cooling law, elapsed work, cumulative heat, and limiting performance
are mutually consistent.
