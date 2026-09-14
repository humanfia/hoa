import Mathlib
import Physlib.Units.Dimension
import Physlib.Units.WithDim.Basic
import CRNT.Basic.Reaction

/-!
This import probe keeps the pinned Mathlib, Physlib units, and CRNT reaction
core in the verified project graph used by the IChO automation run. LeanExplore
may still search the full installed `Mathlib`, `Physlib`, and `CRNT` module trees.
-/
