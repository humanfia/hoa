# IPhO 2026 — Theory Problem 3: Chasing the Absolute Zero

**Solution (natural language, answer-blind)**

## Setup, notation, and conventions

The paramagnetic torus (Pm-T) has mean radius $R$, inner radius $r\ll R$,
cross-sectional area $A$, and volume

$$V = 2\pi R\,A$$

(the circumference of the mean circle times the cross-section, correct to
leading order in $r/R$). A dense $N$-turn winding carries the instantaneous
current $I$. The fields $\vec H$, $\vec B$ and the magnetization $\vec M$ are
taken uniform inside the torus, with

$$\vec B = \mu_0\vec H + \mu_0\vec M, \qquad \vec M \parallel \vec H .$$

Ampère's law for $\vec H$ in a magnetic material is

$$\oint_C \vec H\cdot d\vec\ell = I_C,$$

with $I_C$ the net *free* current through the area bounded by the closed
curve $C$.

**Sign convention (used throughout).** Work $W$ and heat $Q$ are positive
when they flow *into* the Pm-T. The first law therefore reads

$$dU = \delta Q + \delta W .$$

---

## Part A — Work in the Pm-T

### A.1 Field magnitude inside the torus

Choose as Amperian loop the mean circle of radius $R$ running along the
inside of the torus. Every one of the $N$ turns threads this loop once, so
the enclosed free current is $I_C = NI$. Since $H$ is uniform and tangential
along the path,

$$H\,(2\pi R) = NI .$$

Eliminating $2\pi R = V/A$,

$$\boxed{\,H = \frac{NI}{2\pi R} = \frac{NIA}{V}\,}$$

*Check (units):* $[NIA/V] = \mathrm{A\cdot m^2/m^3 = A/m}$, the SI unit of
$H$. ✓

### A.2 Work performed by the external source

Each turn encloses the flux $\Phi = BA$ through the cross-section $A$, so the
$N$-turn winding links the total flux $N\Phi = NBA$. When $B$ changes,
Faraday's law induces the emf

$$|\mathcal E| = N A\,\frac{dB}{dt}$$

around the winding. To keep the instantaneous current $I$ flowing, the
external source must oppose this induced emf, and in the time $dt$ during
which $B$ changes by $dB$ it performs the work

$$dW_{emf} = I\,|\mathcal E|\,dt = NAI\,dB .$$

Using $NAI = HV$ from A.1,

$$\boxed{\,dW_{emf} = V H\, dB\,}$$

*Check (units and sign):* $[VH\,dB] = \mathrm{m^3\cdot (A/m)\cdot T}
= \mathrm{A\cdot m^2\cdot T} = \mathrm{Wb\cdot A} = \mathrm{J}$. ✓ For
$dB>0$ with $I>0$ the source delivers positive work, as Lenz's law
requires. ✓

### A.3 Work done on the paramagnetic material

With a vacuum core the same current would give $B_0 = \mu_0 H$, so the vacuum
part of the source work is

$$dW_{vac} = V H\, dB_0 = \mu_0 V H\, dH .$$

Subtracting and using $dB = \mu_0\,dH + \mu_0\,dM$,

$$\boxed{\,dW = dW_{emf} - dW_{vac} = VH\,(dB - \mu_0 dH) = \mu_0 V H\, dM\,}$$

*Check (energy separation):* $dW_{vac} = d\!\left(\tfrac12\mu_0 H^2 V\right)$
is exactly the change of the vacuum field energy
$\int \tfrac12 \vec B\!\cdot\!\vec H\, dV = \tfrac12\mu_0 H^2 V$; the
remainder $dW=\mu_0 V H\,dM$ is the part that couples to the material's
magnetization. This is the magnetic work quoted in Part B. ✓

---

## Part B — Heat and temperature in the Pm-T

Given data for the Pm-T (state functions $H$, $M$, $T$; constants $K$,
$\lambda$, $n$; fixed volume $V$):

$$TMV = nKH, \qquad C_M = \frac{n\lambda}{T^2}, \qquad dU = C_M\,dT
\ \text{in any process}, \qquad \delta W = \mu_0 V H\, dM .$$

A combination used in both checks below is the entropy of the Pm-T. From the
first law, $\delta Q_{\rm rev} = dU - \delta W$, so

$$dS = \frac{\delta Q_{\rm rev}}{T}
 = \frac{C_M}{T}\,dT - \frac{\mu_0 V H}{T}\,dM
 = \frac{n\lambda}{T^3}\,dT - \frac{\mu_0 V^2 M}{nK}\,dM ,$$

where the equation of state $H/T = MV/(nK)$ was used in the second term. The
cross-derivatives of the two coefficients both vanish, so this is an exact
differential:

$$S(T,M) = -\,\frac{n\lambda}{2T^2} - \frac{\mu_0 V^2 M^2}{2nK} + \text{const} .$$

### B.1 Isothermal change $H_i \to H_f$ at temperature $T$

At constant $T$ we have $dT=0$, hence $dU = C_M\,dT = 0$: the internal energy
of the Pm-T depends on temperature alone, so it does not change. The first
law then gives

$$\delta Q = -\,\delta W = -\mu_0 V H\, dM .$$

At fixed $T$ the equation of state gives $M = nKH/(VT)$, i.e.
$dM = \dfrac{nK}{VT}\,dH$. Therefore

$$Q = -\mu_0 V\,\frac{nK}{VT}\int_{H_i}^{H_f} H\,dH
 = -\,\frac{\mu_0 n K}{2T}\left(H_f^2 - H_i^2\right),$$

$$\boxed{\,Q = \frac{\mu_0 n K}{2T}\left(H_i^2 - H_f^2\right)\,}$$

(The allowed variable $V$ cancels; the result depends on $\mu_0, n, K, T,
H_i, H_f$.)

*Check (sign):* on isothermal **magnetization** ($H_f>H_i$), $Q<0$ — heat
must leave the torus, because aligning the spins at fixed temperature lowers
their entropy. This is the physically required direction. ✓
*Check (entropy):* at fixed $T$,
$Q = T\Delta S = T\left[-\dfrac{\mu_0 V^2 (M_f^2-M_i^2)}{2nK}\right]$ with
$M_{i,f} = nKH_{i,f}/(VT)$ reproduces exactly the boxed formula. ✓
*Check (units):* $[\mu_0 n K H^2/T] = \mathrm{(T\,m/A)\, mol\, (K\,m^3/mol)\,
(A/m)^2 / K} = \mathrm{T\cdot A\cdot m^2} = \mathrm{J}$. ✓

### B.2 Adiabatic change $H_i \to H_f$ starting at $T_i$

An adiabatic change has $\delta Q = 0$, so the first law reads
$C_M\,dT = \mu_0 V H\, dM$. Write the equation of state as
$M = \dfrac{nK}{V}\dfrac{H}{T}$, whence

$$dM = \frac{nK}{V}\left(\frac{dH}{T} - \frac{H\,dT}{T^2}\right).$$

Substituting this and $C_M = n\lambda/T^2$:

$$\frac{n\lambda}{T^2}\,dT
 = \mu_0 n K\left(\frac{H}{T}\,dH - \frac{H^2}{T^2}\,dT\right).$$

Multiplying by $T^2$ and collecting the $dT$ terms,

$$\left(n\lambda + \mu_0 n K H^2\right) dT = \mu_0 n K\, T H\, dH
\quad\Longrightarrow\quad
\frac{dT}{T} = \frac{\mu_0 K\, H\, dH}{\lambda + \mu_0 K H^2} .$$

This integrates immediately:

$$\ln\frac{T_f}{T_i}
 = \frac12\,\ln\frac{\lambda + \mu_0 K H_f^2}{\lambda + \mu_0 K H_i^2},$$

so that

$$\boxed{\;T_f = T_i\,
\sqrt{\dfrac{\lambda + \mu_0 K H_f^2}{\lambda + \mu_0 K H_i^2}}\;},
\qquad
\Delta T = T_f - T_i
 = T_i\left(
 \sqrt{\dfrac{\lambda + \mu_0 K H_f^2}{\lambda + \mu_0 K H_i^2}} - 1
 \right).$$

Equivalently, along a reversible adiabat

$$\frac{T^2}{\lambda + \mu_0 K H^2} = \text{const} .$$

(The factors of $n$ cancel; like $V$, they drop out of the final relation.)

*Check (sign, magnetocaloric effect):* $H_f > H_i$ gives $T_f > T_i$
(adiabatic magnetization heats) and $H_f < H_i$ gives $T_f < T_i$ (adiabatic
demagnetization cools) — the Giauque–Debye cooling mechanism on which the
whole problem is based. ✓
*Check (entropy):* $S(T,M)=\text{const}$ means
$\dfrac{n\lambda}{T^2} + \dfrac{\mu_0 V^2 M^2}{nK} = \text{const}$; inserting
$M = nKH/(VT)$ gives $\dfrac{n\lambda + \mu_0 n K H^2}{T^2} = \text{const}$,
the same invariant. ✓
*Check (limit):* for weak fields, $\mu_0 K H^2 \ll \lambda$,
$\Delta T \approx \dfrac{\mu_0 K T_i}{2\lambda}\left(H_f^2 - H_i^2\right)$,
i.e. the temperature shift is linear in $H_f^2-H_i^2$ with a positive
coefficient. ✓

---

## Part C — The Carnot refrigerator of the Pm-T

Figure 3b shows the cycle $1\to2\to3\to4\to1$ in the $H$-versus-$T$ plane.
The two **vertical** segments $2\to3$ (left) and $4\to1$ (right) are
**isotherms** (constant $T$); the two **curved** segments $1\to2$ and
$3\to4$ are **adiabats** — along them $T$ rises monotonically with $H$, in
agreement with the invariant of B.2.

### C.1 Labelling of Figure 3b

- The right-hand isotherm through vertices 4 and 1 is at the **higher**
  temperature: mark $T_h$ at the foot of its dashed line on the $T$ axis.
  The left-hand isotherm through vertices 2 and 3 is at the **lower**
  temperature: mark $T_c$ there. ($T_c < T_h$.)
- **Process $4\to1$** (isothermal magnetization at $T_h$, $H$ increases from
  $H_4$ to $H_1$): by B.1, $Q_{4\to1} = \dfrac{\mu_0 n K}{2T_h}
  (H_4^2 - H_1^2) < 0$ — heat flows *out* of the Pm-T. This is the process
  on which $\mathbf{Q_h}$ **is transferred to the hot reservoir**.
- **Process $2\to3$** (isothermal demagnetization at $T_c$, $H$ decreases
  from $H_2$ to $H_3$): by B.1, $Q_{2\to3} = \dfrac{\mu_0 n K}{2T_c}
  (H_2^2 - H_3^2) > 0$ — heat flows *into* the Pm-T. This is the process on
  which $\mathbf{Q_c}$ **is absorbed from the cold reservoir**.
- The adiabats carry no heat: $1\to2$ is adiabatic demagnetization
  ($T_h \to T_c$, the cooling stroke) and $3\to4$ is adiabatic
  magnetization ($T_c \to T_h$, the reheating stroke).

Annotated sketch of Figure 3b (schematic):

```
H
^
|                    1
|          2 ------. |
|          |       . |     4 -> 1 : isotherm at T_h (H rises, Q_h out)
|          |       4 |     2 -> 3 : isotherm at T_c (H falls, Q_c in)
|          3 ------.        1 -> 2 : adiabat (demagnetization, cools)
|                           3 -> 4 : adiabat (magnetization, heats)
+------|------------|----------> T
       T_c          T_h
```

(The adiabats are drawn concave, steep at low $T$ and flattening at high
$T$; this matches the B.2 invariant $T^2 \propto \lambda + \mu_0 K H^2$,
for which $dH/dT$ decreases as $T$ grows along the curve.) ✓

*Check (directions):* with the fields of C.3, $H_1 > H_2 > H_4 > H_3$,
exactly the ordering drawn in the figure (vertex 1 highest, vertex 3
lowest), and the heat-flow directions above are those of a refrigerator
running the cycle counterclockwise in the $(T,S)$ sense. ✓

### C.2 Relation among the vertex magnetizations

Along each adiabat the entropy of Part B is constant, i.e.
$\dfrac{n\lambda}{T^2} + \dfrac{\mu_0 V^2 M^2}{nK} = \text{const}$. Vertices
1 and 4 are at $T_h$; vertices 2 and 3 at $T_c$. Hence

$$1\to2:\quad
\frac{n\lambda}{T_h^2} + \frac{\mu_0 V^2 M_1^2}{nK}
 = \frac{n\lambda}{T_c^2} + \frac{\mu_0 V^2 M_2^2}{nK},$$

$$3\to4:\quad
\frac{n\lambda}{T_c^2} + \frac{\mu_0 V^2 M_3^2}{nK}
 = \frac{n\lambda}{T_h^2} + \frac{\mu_0 V^2 M_4^2}{nK}.$$

Rearranging each,

$$\frac{\mu_0 V^2}{nK}\left(M_1^2 - M_2^2\right)
 = n\lambda\left(\frac{1}{T_c^2} - \frac{1}{T_h^2}\right)
 = \frac{\mu_0 V^2}{nK}\left(M_4^2 - M_3^2\right),$$

so $M_1^2 - M_2^2 = M_4^2 - M_3^2$, i.e.

$$\boxed{\,M_1 = \sqrt{M_2^2 + M_4^2 - M_3^2}\,}$$

(taking the positive root, since $M$ is a magnitude).

*Independent check (Carnot heat identity):* converting the isothermal heats
of B.1 to magnetizations via $H = TMV/(nK)$ at each vertex,

$$Q_h = \frac{\mu_0 V^2 T_h}{2nK}\left(M_1^2 - M_4^2\right), \qquad
Q_c = \frac{\mu_0 V^2 T_c}{2nK}\left(M_2^2 - M_3^2\right).$$

The Carnot identity $Q_h/Q_c = T_h/T_c$ then demands
$M_1^2 - M_4^2 = M_2^2 - M_3^2$ — exactly the same relation. ✓ The two
derivations are independent (one uses only the adiabats, the other only the
isotherms plus Carnot), so the result is doubly secured. ✓

### C.3 One cycle cooling liquid helium — numerical evaluation

**Given data.** Helium (cold body): volume $V_{\rm He} = 1.00~
\mathrm{L} = 1.00\times10^{-3}~\mathrm{m^3}$, initial temperature
$T_c = 1.00~\mathrm{K}$, specific heat $c = 100~\mathrm{J/(kg\cdot K)}$,
density $\rho_{\rm He} = 130~\mathrm{kg/m^3}$ (both constant).
Pm-T (potassium chromate): $n = 2.0~\mathrm{mol}$,
$K = 1.87\times10^{-6}~\mathrm{K\cdot m^3/mol}$, density
$\rho_s = 2730~\mathrm{kg/m^3}$, molar mass $\mu_m = 0.19~\mathrm{kg/mol}$.
Cycle fields: $H_1 = 411624~\mathrm{A/m}$, $H_2 = 311306~\mathrm{A/m}$,
$H_3 = 204618~\mathrm{A/m}$, $H_4 = 240446~\mathrm{A/m}$.
$\mu_0 = 4\pi\times10^{-7}~\mathrm{T\,m/A}$.

**Strategy.** The heat removed from the helium in one cycle is the heat
absorbed by the Pm-T on the cold isotherm $2\to3$, given by B.1 with
$T = T_c = 1.00~\mathrm{K}$. No other property of the cycle (in particular
not $T_h$ or $\lambda$) is needed for this energy balance.

**Step 1 — torus volume** (uses the salt density and molar mass):

$$V = \frac{n\,\mu_m}{\rho_s}
 = \frac{2.0~\mathrm{mol}\times 0.19~\mathrm{kg/mol}}
 {2730~\mathrm{kg/m^3}}
 = \frac{0.38~\mathrm{kg}}{2730~\mathrm{kg/m^3}}
 = 1.39\times10^{-4}~\mathrm{m^3} .$$

**Step 2 — heat absorbed from the helium on $2\to3$:**

$$H_2^2 - H_3^2 = (3.11306\times10^{5})^2 - (2.04618\times10^{5})^2
 = 9.6911\times10^{10} - 4.1869\times10^{10}
 = 5.5043\times10^{10}~\mathrm{(A/m)^2},$$

$$Q_c = \frac{\mu_0 n K}{2T_c}\left(H_2^2 - H_3^2\right)
 = \frac{(4\pi\times10^{-7})(2.0)(1.87\times10^{-6})(5.5043\times10^{10})}
 {2\times 1.00}~\mathrm{J}
 = 1.29\times10^{-1}~\mathrm{J} .$$

**Step 2′ — cross-check via the magnetization form** (uses $V$ from Step 1):
$M_2 = \dfrac{nKH_2}{VT_c} = 8.36\times10^{3}~\mathrm{A/m}$ and
$M_3 = \dfrac{nKH_3}{VT_c} = 5.50\times10^{3}~\mathrm{A/m}$, so

$$Q_c = \frac{\mu_0 V^2 T_c}{2nK}\left(M_2^2 - M_3^2\right)
 = 1.29\times10^{-1}~\mathrm{J},$$

identical to Step 2 (the two forms are algebraically the same, since $V$
cancels out of the $H$-form). ✓

**Step 3 — helium heat capacity and temperature drop:**

$$C_{\rm He} = \rho_{\rm He} V_{\rm He}\, c
 = 130\times 1.00\times10^{-3}\times 100~\mathrm{J/K}
 = 13.0~\mathrm{J/K},$$

$$\Delta T_{\rm He} = \frac{Q_c}{C_{\rm He}}
 = \frac{1.29\times10^{-1}~\mathrm{J}}{13.0~\mathrm{J/K}}
 = 9.9\times10^{-3}~\mathrm{K} .$$

Since $\Delta T_{\rm He} \ll T_c$, treating the cold isotherm as occurring
at the constant temperature $T_c = 1.00~\mathrm{K}$ throughout the single
cycle is self-consistent (a correction would enter only at relative order
$\Delta T_{\rm He}/T_c \sim 1\%$ of the 1% drop itself).

$$\boxed{\;T_{\rm final} = 1.00~\mathrm{K} - 9.9\times10^{-3}~\mathrm{K}
 \approx 0.990~\mathrm{K}\;}$$

**Cycle-closure check (uses the remaining data $H_1$, $H_4$).** The hot
isotherm $4\to1$ rejects
$Q_h = \dfrac{\mu_0 n K}{2T_h}\left(H_1^2 - H_4^2\right)$. Combining the
Carnot identity $Q_h/Q_c = T_h/T_c$ with the two isothermal heats fixes the
reservoir ratio from the given fields alone:

$$\frac{T_h^2}{T_c^2} = \frac{H_1^2 - H_4^2}{H_2^2 - H_3^2}
 = \frac{1.1162\times10^{11}}{5.5043\times10^{10}} = 2.028
 \quad\Longrightarrow\quad \frac{T_h}{T_c} = 1.424 ,$$

i.e. the hot reservoir sits at $T_h \approx 1.42~\mathrm{K}$ for this cycle.
With that value, $Q_h = 0.184~\mathrm{J}$, the work supplied per cycle is
$W = Q_h - Q_c = 0.0548~\mathrm{J}$, and

$$\mathrm{COP}_{\rm cycle} = \frac{Q_c}{W} = 2.36
 = \frac{T_c}{T_h - T_c},$$

exactly the Carnot value for $T_c = 1.00~\mathrm{K}$ and
$T_h = 1.42~\mathrm{K}$ — the isothermal heats close the cycle
consistently. ✓ (The adiabatic branches involve the material constant
$\lambda$, which is not numerically specified and is not needed anywhere in
this question: the heat extracted from the helium depends only on the cold
isotherm.)

*Dimensional check of Step 2:*
$[\mu_0 n K H^2/T] = \mathrm{(T\,m/A)(mol)(K\,m^3/mol)(A^2/m^2)/K}
= \mathrm{T\,A\,m^2} = \mathrm{J}$. ✓

### C.4 Time to cool a body from $T_0$ to $T$ at constant input power

Consider one infinitesimal Carnot cycle performed while the cooled body is
at temperature $T_c$ (with $T_0 \ge T_c \ge T$). During that cycle:

- the heat extracted from the body is
  $$dQ_c = -\,C_c\, dT_c \quad (>0\text{, since } dT_c < 0);$$
- the Carnot relation given in the problem fixes the rejected heat:
  $$dQ_h = \frac{T_h}{T_c}\, dQ_c ;$$
- hence the work supplied to the refrigerator is
  $$dW = dQ_h - dQ_c = dQ_c\,\frac{T_h - T_c}{T_c}
  = -\,C_c\,\frac{T_h - T_c}{T_c}\, dT_c .$$

With constant input power $P = \dfrac{dW}{dt}$,

$$dt = \frac{dW}{P}
 = -\,\frac{C_c}{P}\,\frac{T_h - T_c}{T_c}\, dT_c ,$$

and the total time to bring the body from $T_0$ down to $T < T_0$ is

$$t = \frac{C_c}{P}\int_T^{T_0}\left(\frac{T_h}{T_c} - 1\right) dT_c ,$$

$$\boxed{\;t = \frac{C_c}{P}\left[\,T_h\,\ln\frac{T_0}{T} - (T_0 - T)\,
\right]\;}$$

*Check (units):* $\dfrac{[\mathrm{J/K}]\cdot[\mathrm{K}]}{[\mathrm{J/s}]}
= \mathrm{s}$. ✓
*Check (positivity and monotonicity):* since $\ln x \ge 1 - 1/x$ for
$x > 0$ (equivalently $\ln(1/y) \ge 1 - y$), applied at $x = T_0/T \ge 1$,
and $T_h \ge T_0 > T$,

$$T_h \ln\frac{T_0}{T} \ge T_0\ln\frac{T_0}{T}
\ge T_0\left(1 - \frac{T}{T_0}\right) = T_0 - T ,$$

the first step using $T_h \ge T_0$ and $\ln(T_0/T) \ge 0$, the second
using $\ln(T_0/T) \ge 1 - T/T_0$; so $t \ge 0$, with equality only at
$T = T_0$; moreover $dt/dT < 0$: lower target temperatures take longer. ✓
*Check (limiting cases):* for $T \to T_0$,
$t \approx \dfrac{C_c}{P}\dfrac{T_h - T_0}{T_0}(T_0 - T) \to 0$, i.e. the
initial cooling rate has magnitude $\left|\dfrac{dT_c}{dt}\right|_{0}
= \dfrac{P}{C_c}\,\dfrac{T_0}{T_h - T_0}
= \dfrac{P}{C_c}\,\mathrm{COP}_{\rm inst}(T_0)$ — the input power times the
instantaneous Carnot COP, per unit heat capacity, as it must. For $T \to 0$
the time diverges like $T_h \ln(T_0/T)$: absolute zero cannot be reached in
finite time — in the spirit of the problem's title. ✓

### C.5 Overall coefficient of performance up to time $t$

Over the whole cooling process of C.4 the totals are path-independent
integrals of the infinitesimal relations:

$$Q_c^{\rm tot} = \int dQ_c = C_c\,(T_0 - T), \qquad
W^{\rm tot} = Pt = C_c\left[T_h\ln\frac{T_0}{T} - (T_0 - T)\right].$$

Therefore

$$\boxed{\;\mathrm{COP} = \frac{Q_c^{\rm tot}}{W^{\rm tot}}
 = \frac{T_0 - T}{\,T_h\,\ln\dfrac{T_0}{T} - (T_0 - T)\,}\;}$$

*Check (instantaneous vs cumulative consistency):* the instantaneous Carnot
COP at cold-body temperature $T_c$ is
$\mathrm{COP}_{\rm inst}(T_c) = \dfrac{T_c}{T_h - T_c}$. Since
$\mathrm{COP} = \dfrac{\int dQ_c}{\int dQ_c\,/\,\mathrm{COP}_{\rm inst}}$
is an average of $\mathrm{COP}_{\rm inst}$ over the run, it must lie between
its endpoint values,

$$\frac{T}{T_h - T} \;\le\; \mathrm{COP} \;\le\; \frac{T_0}{T_h - T_0},$$

and indeed as $T \to T_0$ the expansion
$\ln(T_0/T) = \dfrac{T_0 - T}{T_0} + O\!\left((T_0-T)^2\right)$ gives
$\mathrm{COP} \to \dfrac{T_0}{T_h - T_0} = \mathrm{COP}_{\rm inst}(T_0)$. ✓
*Check (dimensions):* numerator and denominator are both temperatures, so
COP is dimensionless. ✓
*Check (second-law bound):* a reversible refrigerator whose cold reservoir
is held at the *final* temperature $T$ throughout would have
$\mathrm{COP} = \dfrac{T}{T_h - T}$. Our overall COP is larger than that
value precisely because the cold body is warmer than $T$ during most of the
process; no conflict with the second law arises. ✓

---

## Summary of results

| Part | Result |
|------|--------|
| A.1 | $H = \dfrac{NIA}{V}$ |
| A.2 | $dW_{emf} = V H\, dB$ |
| A.3 | $dW = \mu_0 V H\, dM$ |
| B.1 | $Q = \dfrac{\mu_0 n K}{2T}\left(H_i^2 - H_f^2\right)$ |
| B.2 | $\Delta T = T_i\!\left(\sqrt{\dfrac{\lambda + \mu_0 K H_f^2}{\lambda + \mu_0 K H_i^2}} - 1\right)$ |
| C.1 | $T_h$ at the right isotherm ($4\to1$, $Q_h$ rejected); $T_c$ at the left isotherm ($2\to3$, $Q_c$ absorbed); $1\to2$, $3\to4$ adiabats |
| C.2 | $M_1 = \sqrt{M_2^2 + M_4^2 - M_3^2}$ |
| C.3 | $Q_c = 0.129~\mathrm{J}$ per cycle; helium cools by $9.9\times10^{-3}~\mathrm{K}$ to $T_{\rm final} \approx 0.990~\mathrm{K}$ |
| C.4 | $t = \dfrac{C_c}{P}\left[T_h\ln\dfrac{T_0}{T} - (T_0 - T)\right]$ |
| C.5 | $\mathrm{COP} = \dfrac{T_0 - T}{T_h\ln(T_0/T) - (T_0 - T)}$ |
