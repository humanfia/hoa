/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QAlgBench.Init
public import QAlgBench.Base.Components.Oracle.Common
public import QAlgBench.Base.Components.Oracle.Reflection
public import QAlgBench.Base.Components.Oracle.BlockEncoding

/-!
# Oracle components

Stable re-export header for reusable oracle components.  Algorithm-specific
oracle hypotheses remain in `QAlgBench.Algorithms`; primitive-specific wrappers
remain in `QAlgBench.Primitives`.  This namespace collects Core-level oracle
building blocks that do not import those layers.

When introducing an oracle-based algorithm, first search this module and its
submodules for an existing XOR, phase, reflection, projector-controlled NOT, or
block-encoding constructor.  Add a new Core oracle only when the constructor is
reusable without importing `Primitives` or `Algorithms`; keep algorithm-specific
oracle models local to the algorithm module.
-/

@[expose] public section

