import Mathlib
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace LiuBangXiangYu

/-- The multiset of piece lengths obtained by cutting `[0,1]` at the points of a
finite set `S ⊆ (0,1)`.  We sort `S` ascending, prepend `0` and append `1`, and
take consecutive differences.  The result is a list of `|S| + 1` positive reals
summing to `1` (when `S ⊆ (0,1)`). -/
noncomputable def pieceLengths (S : Finset ℝ) : List ℝ :=
  let l : List ℝ := (0 : ℝ) :: (S.sort (· ≤ ·)) ++ [1]
  List.zipWith (fun a b => b - a) l l.tail

/-- The sum of the entries of a list `L` at the (0-indexed) even positions, after
sorting `L` in non-increasing order.  These are the entries in the `1`st, `3`rd,
`5`th, … positions of the sorted (decreasing) list, i.e. the pieces claimed by
the first mover under the greedy claiming rule. -/
noncomputable def firstPlayerShare (L : List ℝ) : ℝ :=
  let sorted := L.mergeSort (· ≥ ·)
  ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

/-- `L(A,B)`: Liu Bang's total length, given Liu Bang's marks `A` and Xiang Yu's
marks `B`. -/
noncomputable def L (A B : Finset ℝ) : ℝ :=
  firstPlayerShare (pieceLengths (A ∪ B))

/-- The set of admissible markings for a player: a finite subset of `(0,1)` of
size at most `n`.  We encode it as a `Finset ℝ` subject to the side conditions. -/
def AdmissibleMark (n : ℕ) (X : Finset ℝ) : Prop :=
  (↑X ⊆ Set.Ioo (0 : ℝ) 1) ∧ X.card ≤ n

/-- The value Liu Bang can guarantee.

`V n` is the supremum over Liu Bang's admissible markings `A` of the infimum,
over Xiang Yu's admissible markings `B` disjoint from `A`, of `L A B`. -/
noncomputable def V (n : ℕ) : ℝ :=
  ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
    ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1

/-- The claimed answer value `V(n) = 2^n / (2^(n+1) - 1)`. -/
noncomputable def answer (n : ℕ) : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)

/-! ## Correctness statements for the definitions

These pin down that the encoded definitions behave as intended. -/

/-- The piece lengths of an admissible cut set sum to `1` (the total stick
length). -/
theorem pieceLengths_sum (S : Finset ℝ) (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    (pieceLengths S).sum = 1 := by
  have htel : ∀ (a b : ℝ) (l : List ℝ),
      (List.zipWith (fun x y => y - x) (a :: l ++ [b]) (l ++ [b])).sum = b - a := by
    intro a b l
    induction l generalizing a with
    | nil => simp
    | cons x l ih =>
        simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
        rw [← List.cons_append, ih]
        ring
  simpa [pieceLengths] using htel (0 : ℝ) 1 (S.sort (· ≤ ·))

private theorem sum_consecutive_differences (a b : ℝ) (l : List ℝ) :
    (List.zipWith (fun x y => y - x) (a :: l ++ [b]) (l ++ [b])).sum = b - a := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons]
      rw [← List.cons_append, ih]
      ring

private theorem consecutive_differences_nonneg (l : List ℝ)
    (hl : l.Pairwise (· ≤ ·)) :
    ∀ x ∈ List.zipWith (fun a b => b - a) l l.tail, 0 ≤ x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          have hab : a ≤ b := (List.pairwise_cons.1 hl).1 b (by simp)
          have htail : (b :: l).Pairwise (· ≤ ·) := (List.pairwise_cons.1 hl).2
          simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons]
          intro x hx
          rcases hx with rfl | hx
          · linarith
          · exact ih htail x hx

private theorem sorted_with_endpoints (S : Finset ℝ)
    (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).Pairwise (· ≤ ·) := by
  rw [List.pairwise_append]
  constructor
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      exact (hS ((Finset.mem_sort (r := (· ≤ ·))).1 hx)).1.le
    · exact Finset.pairwise_sort S (· ≤ ·)
  constructor
  · simp
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · norm_num
    · exact (hS ((Finset.mem_sort (r := (· ≤ ·))).1 hx)).2.le

private theorem pieceLengths_nonneg (S : Finset ℝ)
    (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ x ∈ pieceLengths S, 0 ≤ x := by
  apply consecutive_differences_nonneg
  exact sorted_with_endpoints S hS

private theorem consecutive_differences_pos (l : List ℝ)
    (hl : l.Pairwise (· < ·)) :
    ∀ x ∈ List.zipWith (fun a b => b - a) l l.tail, 0 < x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      cases l with
      | nil => simp
      | cons b l =>
          have hab : a < b := (List.pairwise_cons.1 hl).1 b (by simp)
          have htail : (b :: l).Pairwise (· < ·) := (List.pairwise_cons.1 hl).2
          simp only [List.tail_cons, List.zipWith_cons_cons, List.mem_cons]
          intro x hx
          rcases hx with rfl | hx
          · linarith
          · exact ih htail x hx

private theorem sorted_with_endpoints_strict (S : Finset ℝ)
    (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ((0 : ℝ) :: S.sort (· ≤ ·) ++ [1]).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  constructor
  · rw [List.pairwise_cons]
    constructor
    · intro x hx
      exact (hS ((Finset.mem_sort (r := (· ≤ ·))).1 hx)).1
    · exact (Finset.sortedLT_sort S).pairwise
  constructor
  · simp
  · intro x hx y hy
    simp only [List.mem_singleton] at hy
    subst y
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · norm_num
    · exact (hS ((Finset.mem_sort (r := (· ≤ ·))).1 hx)).2

private theorem pieceLengths_pos (S : Finset ℝ)
    (hS : ↑S ⊆ Set.Ioo (0 : ℝ) 1) :
    ∀ x ∈ pieceLengths S, 0 < x := by
  apply consecutive_differences_pos
  exact sorted_with_endpoints_strict S hS

private def indexedShare (l : List ℝ) (k : ℕ) : ℝ :=
  (((l.zipIdx k).filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)).sum

private theorem indexedShare_cons (a : ℝ) (l : List ℝ) (k : ℕ) :
    indexedShare (a :: l) k =
      (if k % 2 = 0 then a else 0) + indexedShare l (k + 1) := by
  by_cases h : k % 2 = 0 <;> simp [indexedShare, List.zipIdx_cons, h]

private theorem indexedShare_add_two (l : List ℝ) (k : ℕ) :
    indexedShare l (k + 2) = indexedShare l k := by
  induction l generalizing k with
  | nil => simp [indexedShare]
  | cons a l ih =>
      rw [indexedShare_cons, indexedShare_cons, ih]
      have hmod : (k + 2) % 2 = k % 2 := by omega
      rw [hmod]

private theorem two_mul_indexedShare_zero (l : List ℝ) :
    2 * indexedShare l 0 = l.sum + l.alternatingSum := by
  induction l using List.twoStepInduction with
  | nil => simp [indexedShare]
  | singleton a => simp [indexedShare, List.alternatingSum]; ring
  | cons_cons a b l ih _ =>
      rw [indexedShare_cons, indexedShare_cons]
      norm_num
      rw [indexedShare_add_two]
      linarith

private theorem alternatingSum_nonneg_of_pairwise :
    ∀ l : List ℝ, l.Pairwise (· ≥ ·) → (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.alternatingSum
  | [], _, _ => by simp
  | [a], _, ha => by simpa [List.alternatingSum] using ha a (by simp)
  | a :: b :: l, hsorted, hnonneg => by
      have hab : b ≤ a := (List.pairwise_cons.1 hsorted).1 b (by simp)
      have htail : l.Pairwise (· ≥ ·) := (List.pairwise_cons.1
        (List.pairwise_cons.1 hsorted).2).2
      have htail_nonneg : ∀ x ∈ l, 0 ≤ x := by
        intro x hx
        exact hnonneg x (by simp [hx])
      have ih := alternatingSum_nonneg_of_pairwise l htail htail_nonneg
      simp only [List.alternatingSum]
      linarith

private theorem two_mul_firstPlayerShare (l : List ℝ) :
    2 * firstPlayerShare l =
      l.sum + (l.mergeSort (· ≥ ·)).alternatingSum := by
  let sorted := l.mergeSort (· ≥ ·)
  have hindexed := two_mul_indexedShare_zero sorted
  have hsum : sorted.sum = l.sum := (List.mergeSort_perm l (· ≥ ·)).sum_eq
  simpa [firstPlayerShare, indexedShare, sorted, hsum] using hindexed

private def gaps (a b : ℝ) (l : List ℝ) : List ℝ :=
  List.zipWith (fun x y => y - x) (a :: l ++ [b]) (l ++ [b])

private theorem gaps_orderedInsert (a b c : ℝ) (l : List ℝ) :
    ∃ pre : List ℝ, ∃ x y : ℝ, ∃ post : List ℝ,
      gaps a b (l.orderedInsert (· ≤ ·) c) = pre ++ x :: y :: post ∧
      gaps a b l = pre ++ (x + y) :: post := by
  induction l generalizing a with
  | nil =>
      refine ⟨[], c - a, b - c, [], ?_, ?_⟩
      · simp [gaps]
      · simp [gaps]
  | cons d l ih =>
      by_cases hcd : c ≤ d
      · refine ⟨[], c - a, d - c, gaps d b l, ?_, ?_⟩
        · simp [gaps, List.orderedInsert_cons, hcd]
        · simp [gaps]
      · obtain ⟨pre, x, y, post, hnew, hold⟩ := ih d
        refine ⟨(d - a) :: pre, x, y, post, ?_, ?_⟩
        · rw [List.orderedInsert_cons, if_neg hcd]
          simpa [gaps] using congrArg (List.cons (d - a)) hnew
        · simpa [gaps] using congrArg (List.cons (d - a)) hold

private theorem sort_insert_eq_orderedInsert (S : Finset ℝ) {c : ℝ} (hc : c ∉ S) :
    (insert c S).sort (· ≤ ·) = (S.sort (· ≤ ·)).orderedInsert (· ≤ ·) c := by
  apply List.Perm.eq_of_pairwise' (r := fun x y : ℝ => x ≤ y)
  · exact Finset.pairwise_sort (insert c S) (· ≤ ·)
  · exact (Finset.pairwise_sort S (· ≤ ·)).orderedInsert c _
  · have hnord : ((S.sort (· ≤ ·)).orderedInsert (· ≤ ·) c).Nodup :=
      ((List.perm_orderedInsert (· ≤ ·) c (S.sort (· ≤ ·))).nodup_iff).2
        (by
          rw [List.nodup_cons]
          exact ⟨by simpa, Finset.sort_nodup S (· ≤ ·)⟩)
    exact (List.perm_ext_iff_of_nodup
      (Finset.sort_nodup (insert c S) (· ≤ ·)) hnord).2 (by
        intro x
        simp [hc])

private theorem pieceLengths_insert_split (S : Finset ℝ) {c : ℝ} (hc : c ∉ S) :
    ∃ pre : List ℝ, ∃ x y : ℝ, ∃ post : List ℝ,
      pieceLengths (insert c S) = pre ++ x :: y :: post ∧
      pieceLengths S = pre ++ (x + y) :: post := by
  simpa [pieceLengths, gaps, sort_insert_eq_orderedInsert S hc] using
    gaps_orderedInsert (0 : ℝ) 1 c (S.sort (· ≤ ·))

private def canonicalLabels (base : List ℝ) : List (Fin base.length) :=
  List.ofFn fun i => i

private inductive LabeledRefines (base : List ℝ) :
    List ℝ → List (Fin base.length) → ℕ → Prop
  | refl : LabeledRefines base base (canonicalLabels base) 0
  | split {k : ℕ} {pre post : List ℝ} {lpre lpost : List (Fin base.length)}
      {x y : ℝ} {i : Fin base.length}
      (hpre : pre.length = lpre.length) (hpost : post.length = lpost.length)
      (h : LabeledRefines base (pre ++ (x + y) :: post) (lpre ++ i :: lpost) k) :
      LabeledRefines base (pre ++ x :: y :: post) (lpre ++ i :: i :: lpost) (k + 1)

private theorem LabeledRefines.length_eq {base values : List ℝ}
    {labels : List (Fin base.length)} {k : ℕ}
    (h : LabeledRefines base values labels k) : values.length = labels.length := by
  induction h with
  | refl => simp [canonicalLabels]
  | split hpre hpost h ih => simp_all

private theorem LabeledRefines.length_eq_add {base values : List ℝ}
    {labels : List (Fin base.length)} {k : ℕ}
    (h : LabeledRefines base values labels k) : values.length = base.length + k := by
  induction h with
  | refl => simp
  | split hpre hpost h ih => simp_all; omega

private def labeledWeight {ι : Type*} (values : List ℝ) (labels : List ι)
    (e : ι → ℝ) : ℝ :=
  (List.zipWith (fun x i => e i * x) values labels).sum

private theorem LabeledRefines.weight_eq {base values : List ℝ}
    {labels : List (Fin base.length)} {k : ℕ}
    (h : LabeledRefines base values labels k) (e : Fin base.length → ℝ) :
    labeledWeight values labels e = labeledWeight base (canonicalLabels base) e := by
  induction h with
  | refl => rfl
  | @split k pre post lpre lpost x y i hpre hpost h ih =>
      simp only [labeledWeight, List.zipWith_append hpre, List.sum_append,
        List.zipWith_cons_cons, List.sum_cons] at ih ⊢
      rw [← ih]
      ring

private theorem LabeledRefines.split_one {base old : List ℝ}
    {labels : List (Fin base.length)} {k : ℕ}
    (h : LabeledRefines base old labels k) (pre post : List ℝ) (x y : ℝ)
    (hold : old = pre ++ (x + y) :: post) :
    ∃ newLabels : List (Fin base.length),
      LabeledRefines base (pre ++ x :: y :: post) newLabels (k + 1) := by
  subst old
  have hlen := h.length_eq
  have hp : pre.length < labels.length := by
    rw [← hlen]
    simp
  let lpre := labels.take pre.length
  let i : Fin base.length := labels[pre.length]
  let lpost := labels.drop (pre.length + 1)
  have hlabels : labels = lpre ++ i :: lpost := by
    calc
      labels = labels.take pre.length ++ labels.drop pre.length :=
        (List.take_append_drop pre.length labels).symm
      _ = lpre ++ i :: lpost := by
        rw [List.drop_eq_getElem_cons hp]
  have hpre : pre.length = lpre.length := by simp [lpre, hp.le]
  have hpost : post.length = lpost.length := by
    simp only [lpost, List.length_drop]
    simp only [List.length_append, List.length_cons] at hlen
    omega
  rw [hlabels] at h
  exact ⟨lpre ++ i :: i :: lpost, .split hpre hpost h⟩

private theorem pieceLengths_union_refines (A C : Finset ℝ) (hAC : Disjoint A C) :
    ∃ labels : List (Fin (pieceLengths A).length),
      LabeledRefines (pieceLengths A) (pieceLengths (A ∪ C)) labels C.card := by
  induction C using Finset.induction_on with
  | empty =>
      exact ⟨canonicalLabels (pieceLengths A), by simpa using
        (LabeledRefines.refl : LabeledRefines (pieceLengths A) (pieceLengths A)
          (canonicalLabels (pieceLengths A)) 0)⟩
  | @insert c C hc ih =>
      have hcA : c ∉ A := by
        intro hcA
        exact Finset.disjoint_left.1 hAC hcA (Finset.mem_insert_self c C)
      have hAC' : Disjoint A C := hAC.mono_right (Finset.subset_insert c C)
      obtain ⟨labels, href⟩ := ih hAC'
      have hcU : c ∉ A ∪ C := by simp [hcA, hc]
      obtain ⟨pre, x, y, post, hnew, hold⟩ := pieceLengths_insert_split (A ∪ C) hcU
      obtain ⟨newLabels, href'⟩ := href.split_one pre post x y hold
      refine ⟨newLabels, ?_⟩
      have hunion : A ∪ insert c C = insert c (A ∪ C) := by ext; simp [or_assoc]
      rw [hunion, hnew, Finset.card_insert_of_notMem hc]
      exact href'

private def ternarySign (z : ZMod 3) : ℝ :=
  if z = 0 then 0 else if z = 1 then 1 else -1

private theorem abs_ternarySign_le_one (z : ZMod 3) : |ternarySign z| ≤ 1 := by
  fin_cases z
  · norm_num [ternarySign]
  · norm_num [ternarySign]
  · simp [ternarySign, show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

private theorem ternarySign_eq_zero_iff (z : ZMod 3) : ternarySign z = 0 ↔ z = 0 := by
  fin_cases z
  · norm_num [ternarySign]
  · norm_num [ternarySign]
  · simp [ternarySign, show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

private theorem ternarySign_neg (z : ZMod 3) : ternarySign (-z) = -ternarySign z := by
  fin_cases z
  · norm_num [ternarySign]
  · norm_num [ternarySign, show (-1 : ZMod 3) = 2 by decide,
      show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide]
  · change ternarySign (-(2 : ZMod 3)) = -ternarySign (2 : ZMod 3)
    rw [show (-(2 : ZMod 3)) = 1 by decide]
    simp [ternarySign, show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

private theorem ternarySign_add_eq_zero {z w : ZMod 3} (h : z + w = 0) :
    ternarySign z + ternarySign w = 0 := by
  have hz : z = -w := add_eq_zero_iff_eq_neg.mp h
  have hw : w = -z := by
    calc
      w = -(-w) := by simp
      _ = -z := congrArg Neg.neg hz.symm
  rw [hw, ternarySign_neg]
  ring

private theorem map_fst_zip_of_length_eq {α β : Type*} {l : List α} {r : List β}
    (h : l.length = r.length) : (l.zip r).map Prod.fst = l := by
  induction l generalizing r with
  | nil => simp
  | cons a l ih =>
      cases r with
      | nil => simp at h
      | cons b r =>
          simp only [List.length_cons] at h
          have h' : l.length = r.length := by omega
          simp [ih h']

private theorem sorted_tagged_values {values : List ℝ} {m : ℕ} {labels : List (Fin m)}
    (hlen : values.length = labels.length) :
    let tagged := values.zip labels
    let sortedTagged := tagged.mergeSort (fun p q => p.1 ≥ q.1)
    sortedTagged.map Prod.fst = values.mergeSort (· ≥ ·) := by
  dsimp
  apply List.Perm.eq_of_pairwise' (r := fun x y : ℝ => x ≥ y)
  · have hpair := List.pairwise_mergeSort
      (le := fun x y : ℝ × Fin m => decide (x.1 ≥ y.1))
      (fun _ _ _ hxy hyz => by
        simp only [decide_eq_true_eq] at hxy hyz ⊢
        exact ge_trans hxy hyz)
      (fun x y => by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact le_total y.1 x.1)
      (values.zip labels)
    simpa only [List.pairwise_map, decide_eq_true_eq] using hpair
  · exact List.pairwise_mergeSort' (fun x y : ℝ => x ≥ y) values
  · have hleft := (List.mergeSort_perm (values.zip labels)
      (fun p q : ℝ × Fin m => p.1 ≥ q.1)).map Prod.fst
    have hzip : (values.zip labels).map Prod.fst = values :=
      map_fst_zip_of_length_eq hlen
    rw [hzip] at hleft
    have hleft' : List.Perm
        (((values.zip labels).mergeSort (fun p q : ℝ × Fin m => p.1 ≥ q.1)).map Prod.fst)
        values := hleft
    exact hleft'.trans (List.mergeSort_perm values (· ≥ ·)).symm

private inductive PairCanceled {ι : Type*} (e : ι → ℝ) : List ι → Prop
  | nil : PairCanceled e []
  | singleton (i : ι) : PairCanceled e [i]
  | cons (i j : ι) (l : List ι) (hij : e i + e j = 0)
      (hl : PairCanceled e l) : PairCanceled e (i :: j :: l)

private theorem pairCanceled_of_indexed {ι : Type*} (e : ι → ℝ) (labels : List ι)
    (h : ∀ q : Fin (labels.length / 2),
      e labels[2 * q.val] + e labels[2 * q.val + 1] = 0) :
    PairCanceled e labels := by
  induction labels using List.twoStepInduction with
  | nil => exact .nil
  | singleton i => exact .singleton i
  | cons_cons i j labels ih _ =>
      apply PairCanceled.cons i j labels
      · simpa using h ⟨0, by simp⟩
      · apply ih
        intro q
        have hq := h ⟨q.val + 1, by
          simp only [List.length_cons]
          omega⟩
        simpa only [List.getElem_cons_succ, Nat.add_eq, Nat.mul_add] using hq

private theorem abs_labeledWeight_le_alternatingSum {ι : Type*}
    (e : ι → ℝ) (he : ∀ i, |e i| ≤ 1) :
    ∀ {values : List ℝ} {labels : List ι},
      values.length = labels.length →
      values.Pairwise (· ≥ ·) →
      (∀ x ∈ values, 0 ≤ x) →
      PairCanceled e labels →
      |labeledWeight values labels e| ≤ values.alternatingSum
  | [], [], _, _, _, _ => by simp [labeledWeight]
  | [x], [i], _, _, hx, _ => by
      have hx0 : 0 ≤ x := hx x (by simp)
      simp only [labeledWeight, List.zipWith_cons_cons, List.zipWith_nil, List.sum_cons,
        List.sum_nil, add_zero, List.alternatingSum]
      rw [abs_mul, abs_of_nonneg hx0]
      nlinarith [he i]
  | x :: y :: values, i :: j :: labels, hlen, hsorted, hnonneg,
      PairCanceled.cons _ _ _ hij hcancel => by
      have hxy : y ≤ x := (List.pairwise_cons.1 hsorted).1 y (by simp)
      have htail : values.Pairwise (· ≥ ·) :=
        (List.pairwise_cons.1 (List.pairwise_cons.1 hsorted).2).2
      have htail_nonneg : ∀ z ∈ values, 0 ≤ z := by
        intro z hz
        exact hnonneg z (by simp [hz])
      have htail_len : values.length = labels.length := by simpa using hlen
      have ih := abs_labeledWeight_le_alternatingSum e he htail_len htail
        htail_nonneg hcancel
      have hrewrite : e i * x + e j * y = e i * (x - y) := by
        have hej : e j = -e i := by linarith
        rw [hej]
        ring
      simp only [labeledWeight, List.zipWith_cons_cons, List.sum_cons,
        List.alternatingSum]
      rw [← add_assoc, hrewrite]
      calc
        |e i * (x - y) + labeledWeight values labels e|
            ≤ |e i * (x - y)| + |labeledWeight values labels e| := abs_add_le _ _
        _ ≤ (x - y) + values.alternatingSum := by
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hxy)]
          nlinarith [he i]
        _ = x + -y + values.alternatingSum := by ring
  | [], _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], hlen, _, _, _ => by simp at hlen
  | [x], _ :: _ :: _, hlen, _, _, _ => by simp at hlen
  | _ :: _ :: _, [i], hlen, _, _, _ => by simp at hlen

private theorem zipWith_map_fst_snd {α β γ : Type*} (g : α → β → γ) :
    ∀ l : List (α × β),
      List.zipWith g (l.map Prod.fst) (l.map Prod.snd) =
        l.map (fun p => g p.1 p.2)
  | [] => rfl
  | p :: l => by simp [zipWith_map_fst_snd g l]

private theorem zipWith_eq_map_zip {α β γ : Type*} (g : α → β → γ) :
    ∀ (l : List α) (r : List β),
      List.zipWith g l r = (l.zip r).map (fun p => g p.1 p.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, b :: r => by simp [zipWith_eq_map_zip g l r]

private theorem labeledWeight_sortedTagged {values : List ℝ} {m : ℕ}
    {labels : List (Fin m)} (hlen : values.length = labels.length)
    (e : Fin m → ℝ) :
    let tagged := values.zip labels
    let sortedTagged := tagged.mergeSort (fun p q => p.1 ≥ q.1)
    labeledWeight (sortedTagged.map Prod.fst) (sortedTagged.map Prod.snd) e =
      labeledWeight values labels e := by
  dsimp
  let f : ℝ × Fin m → ℝ := fun p => e p.2 * p.1
  have hperm := (List.mergeSort_perm (values.zip labels)
    (fun p q : ℝ × Fin m => p.1 ≥ q.1)).map f
  have hsum := hperm.sum_eq
  simp only [labeledWeight]
  rw [zipWith_map_fst_snd]
  rw [zipWith_eq_map_zip]
  simpa [f] using hsum

private theorem exists_pair_certificate {base values : List ℝ}
    {labels : List (Fin base.length)} {k : ℕ}
    (href : LabeledRefines base values labels k) (hk : k < base.length) :
    let tagged := values.zip labels
    let sortedTagged := tagged.mergeSort (fun p q => p.1 ≥ q.1)
    ∃ eps : Fin base.length → ZMod 3, eps ≠ 0 ∧
      PairCanceled (fun i => ternarySign (eps i)) (sortedTagged.map Prod.snd) := by
  dsimp
  let sortedTagged := (values.zip labels).mergeSort (fun p q => p.1 ≥ q.1)
  let sortedLabels := sortedTagged.map Prod.snd
  have hlen := href.length_eq
  have hsortedLabels : sortedLabels.length = values.length := by
    simp [sortedLabels, sortedTagged, hlen]
  have hpairs_lt : sortedLabels.length / 2 < base.length := by
    rw [hsortedLabels, href.length_eq_add]
    omega
  let pairMap : (Fin base.length → ZMod 3) →ₗ[ZMod 3]
      (Fin (sortedLabels.length / 2) → ZMod 3) :=
    { toFun := fun eps q =>
        eps sortedLabels[2 * q.val] + eps sortedLabels[2 * q.val + 1]
      map_add' := by
        intro eps eta
        funext q
        dsimp
        ring
      map_smul' := by
        intro c eps
        funext q
        dsimp
        ring }
  have hdim : Module.finrank (ZMod 3)
      (Fin (sortedLabels.length / 2) → ZMod 3) <
      Module.finrank (ZMod 3) (Fin base.length → ZMod 3) := by
    simpa only [Module.finrank_fin_fun] using hpairs_lt
  have hker : LinearMap.ker pairMap ≠ ⊥ :=
    pairMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨eps, heps_mem, heps_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have heps_eq : pairMap eps = 0 := (LinearMap.mem_ker).1 heps_mem
  have hpairs : ∀ q : Fin (sortedLabels.length / 2),
      eps sortedLabels[2 * q.val] + eps sortedLabels[2 * q.val + 1] = 0 := by
    intro q
    have hq := congrFun heps_eq q
    simpa [pairMap] using hq
  refine ⟨eps, heps_ne, ?_⟩
  apply pairCanceled_of_indexed
  intro q
  exact ternarySign_add_eq_zero (hpairs q)

private theorem alternatingSum_refinement_ge {base values : List ℝ}
    {labels : List (Fin base.length)} {k : ℕ}
    (href : LabeledRefines base values labels k) (hk : k < base.length)
    (hnonneg : ∀ x ∈ values, 0 ≤ x) (unit : ℝ)
    (hsep : ∀ eps : Fin base.length → ZMod 3, eps ≠ 0 →
      unit ≤ |labeledWeight base (canonicalLabels base)
        (fun i => ternarySign (eps i))|) :
    unit ≤ (values.mergeSort (· ≥ ·)).alternatingSum := by
  let tagged := values.zip labels
  let sortedTagged := tagged.mergeSort (fun p q => p.1 ≥ q.1)
  let sortedValues := sortedTagged.map Prod.fst
  let sortedLabels := sortedTagged.map Prod.snd
  obtain ⟨eps, heps, hcancel⟩ := exists_pair_certificate href hk
  let e : Fin base.length → ℝ := fun i => ternarySign (eps i)
  have hlen := href.length_eq
  have hsortedValues : sortedValues = values.mergeSort (· ≥ ·) := by
    simpa [tagged, sortedTagged, sortedValues] using sorted_tagged_values hlen
  have hsorted : sortedValues.Pairwise (· ≥ ·) := by
    rw [hsortedValues]
    exact List.pairwise_mergeSort' (fun x y : ℝ => x ≥ y) values
  have hsorted_nonneg : ∀ x ∈ sortedValues, 0 ≤ x := by
    intro x hx
    rw [hsortedValues] at hx
    exact hnonneg x ((List.mergeSort_perm values (· ≥ ·)).mem_iff.1 hx)
  have hsorted_len : sortedValues.length = sortedLabels.length := by
    simp [sortedValues, sortedLabels]
  have habs : |labeledWeight sortedValues sortedLabels e| ≤
      sortedValues.alternatingSum :=
    abs_labeledWeight_le_alternatingSum e (fun i => abs_ternarySign_le_one (eps i))
      hsorted_len hsorted hsorted_nonneg (by simpa [e, sortedLabels, sortedTagged, tagged] using hcancel)
  have hweight_sorted : labeledWeight sortedValues sortedLabels e =
      labeledWeight values labels e := by
    simpa [tagged, sortedTagged, sortedValues, sortedLabels, e] using
      labeledWeight_sortedTagged hlen e
  have hweight_base : labeledWeight values labels e =
      labeledWeight base (canonicalLabels base) e := href.weight_eq e
  calc
    unit ≤ |labeledWeight base (canonicalLabels base) e| := hsep eps heps
    _ = |labeledWeight values labels e| := by rw [hweight_base]
    _ = |labeledWeight sortedValues sortedLabels e| := by rw [hweight_sorted]
    _ ≤ sortedValues.alternatingSum := habs
    _ = (values.mergeSort (· ≥ ·)).alternatingSum := by rw [hsortedValues]

private def geoDen (n : ℕ) : ℝ := (2 : ℝ) ^ (n + 1) - 1

private noncomputable def geoPoint (D : ℝ) (k : ℕ) : ℝ := ((2 : ℝ) ^ (k + 1) - 1) / D

private noncomputable def geoLength (D : ℝ) (k : ℕ) : ℝ := (2 : ℝ) ^ k / D

private noncomputable def geoPieces (n : ℕ) : List ℝ :=
  (List.range (n + 1)).map (geoLength (geoDen n))

private theorem geoDen_pos (n : ℕ) : 0 < geoDen n := by
  have hp : (1 : ℝ) < 2 ^ (n + 1) := one_lt_pow₀ (by norm_num) (by omega)
  simpa [geoDen] using sub_pos.mpr hp

private theorem geoPoint_strictMono (D : ℝ) (hD : 0 < D) : StrictMono (geoPoint D) := by
  intro a b hab
  apply div_lt_div_of_pos_right _ hD
  have hp : (2 : ℝ) ^ (a + 1) < 2 ^ (b + 1) :=
    pow_lt_pow_right₀ (by norm_num) (by omega)
  linarith

private noncomputable def geoPointEmbedding (n : ℕ) : ℕ ↪ ℝ :=
  ⟨geoPoint (geoDen n), (geoPoint_strictMono (geoDen n) (geoDen_pos n)).injective⟩

private noncomputable def geoMarks (n : ℕ) : Finset ℝ :=
  (Finset.range n).map (geoPointEmbedding n)

private theorem geoMarks_sort (n : ℕ) :
    (geoMarks n).sort (· ≤ ·) = (List.range n).map (geoPoint (geoDen n)) := by
  have hmono : StrictMonoOn (geoPointEmbedding n) (↑(Finset.range n) : Set ℕ) := by
    intro a ha b hb hab
    exact geoPoint_strictMono (geoDen n) (geoDen_pos n) hab
  symm
  simpa [geoMarks, geoPointEmbedding] using
    hmono.map_finsetSort

private theorem gaps_append_last (a b c : ℝ) (l : List ℝ) :
    gaps a c (l ++ [b]) = gaps a b l ++ [c - b] := by
  induction l generalizing a with
  | nil => simp [gaps]
  | cons x l ih =>
      simpa [gaps, List.append_assoc] using congrArg (List.cons (x - a)) (ih x)

private theorem gaps_geo (D : ℝ) (hD : D ≠ 0) (n : ℕ) :
    gaps 0 (geoPoint D n) ((List.range n).map (geoPoint D)) =
      (List.range (n + 1)).map (geoLength D) := by
  induction n with
  | zero =>
      simp [gaps, geoPoint, geoLength]
      field_simp
      norm_num
  | succ n ih =>
      rw [List.range_succ, List.map_append]
      simp only [List.map_singleton]
      rw [gaps_append_last, ih]
      have hdiff : geoPoint D (n + 1) - geoPoint D n = geoLength D (n + 1) := by
        simp [geoPoint, geoLength]
        field_simp
        ring
      rw [hdiff, List.range_succ]
      simp [List.range_succ]

private theorem geoPoint_den_eq_one (n : ℕ) : geoPoint (geoDen n) n = 1 := by
  rw [geoPoint, geoDen]
  exact div_self (ne_of_gt (geoDen_pos n))

private theorem pieceLengths_geoMarks (n : ℕ) : pieceLengths (geoMarks n) = geoPieces n := by
  rw [pieceLengths, geoMarks_sort]
  change gaps 0 1 ((List.range n).map (geoPoint (geoDen n))) = geoPieces n
  rw [← geoPoint_den_eq_one n, gaps_geo (geoDen n) (ne_of_gt (geoDen_pos n))]
  rfl

private theorem geoMarks_admissible (n : ℕ) : AdmissibleMark n (geoMarks n) := by
  constructor
  · intro x hx
    change x ∈ geoMarks n at hx
    rw [geoMarks, Finset.mem_map] at hx
    obtain ⟨k, hk, hkx⟩ := hx
    have hkn : k < n := Finset.mem_range.1 hk
    change geoPoint (geoDen n) k = x at hkx
    rw [← hkx]
    have hD := geoDen_pos n
    have hpow_pos : (1 : ℝ) < 2 ^ (k + 1) := one_lt_pow₀ (by norm_num) (by omega)
    have hpow_lt : (2 : ℝ) ^ (k + 1) < 2 ^ (n + 1) :=
      pow_lt_pow_right₀ (by norm_num) (by omega)
    constructor
    · exact div_pos (sub_pos.mpr hpow_pos) hD
    · rw [geoPoint, div_lt_one hD]
      simpa [geoDen] using sub_lt_sub_right hpow_lt 1
  · simp [geoMarks]

private def ternaryInt (z : ZMod 3) : ℤ :=
  if z = 0 then 0 else if z = 1 then 1 else -1

private theorem ternaryInt_bounds (z : ZMod 3) : -1 ≤ ternaryInt z ∧ ternaryInt z ≤ 1 := by
  fin_cases z
  · norm_num [ternaryInt]
  · norm_num [ternaryInt]
  · simp [ternaryInt, show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

private theorem ternaryInt_eq_zero_iff (z : ZMod 3) : ternaryInt z = 0 ↔ z = 0 := by
  fin_cases z
  · norm_num [ternaryInt]
  · norm_num [ternaryInt]
  · simp [ternaryInt, show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

private theorem ternaryInt_cast (z : ZMod 3) : (ternaryInt z : ℝ) = ternarySign z := by
  fin_cases z
  · norm_num [ternaryInt, ternarySign]
  · norm_num [ternaryInt, ternarySign]
  · simp [ternaryInt, ternarySign, show (2 : ZMod 3) ≠ 0 by decide,
      show (2 : ZMod 3) ≠ 1 by decide]

private def binaryFinValue {m : ℕ} (eps : Fin m → ZMod 3) : ℤ :=
  ∑ i : Fin m, ternaryInt (eps i) * 2 ^ i.val

private theorem binaryFinValue_eq_zero_iff :
    ∀ {m : ℕ} (eps : Fin m → ZMod 3), binaryFinValue eps = 0 ↔ eps = 0
  | 0, eps => by
      constructor
      · intro _
        funext i
        exact Fin.elim0 i
      · intro _
        simp [binaryFinValue]
  | m + 1, eps => by
      let tail : Fin m → ZMod 3 := fun i => eps i.succ
      have hdecomp : binaryFinValue eps =
          ternaryInt (eps 0) + 2 * binaryFinValue tail := by
        unfold binaryFinValue
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, pow_zero, mul_one, tail, Fin.val_succ]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [pow_succ]
        ring
      constructor
      · intro hzero
        rw [hdecomp] at hzero
        have hb := ternaryInt_bounds (eps 0)
        have hhead : ternaryInt (eps 0) = 0 := by omega
        have htailzero : binaryFinValue tail = 0 := by omega
        have heps0 : eps 0 = 0 := (ternaryInt_eq_zero_iff _).1 hhead
        have htail : tail = 0 := (binaryFinValue_eq_zero_iff tail).1 htailzero
        funext i
        refine Fin.cases heps0 (fun j => ?_) i
        exact congrFun htail j
      · intro heps
        subst eps
        unfold binaryFinValue
        apply Finset.sum_eq_zero
        intro i hi
        simp [ternaryInt]

private theorem labeledWeight_canonical (l : List ℝ) (e : Fin l.length → ℝ) :
    labeledWeight l (canonicalLabels l) e = ∑ i : Fin l.length, e i * l[i] := by
  have hz : List.zipWith (fun x i => e i * x) l (canonicalLabels l) =
      List.ofFn (fun i : Fin l.length => e i * l[i]) := by
    apply List.ext_getElem
    · simp [canonicalLabels]
    · intro i hi hj
      simp [canonicalLabels]
  rw [labeledWeight, hz, List.sum_ofFn]

private theorem geoPieces_get (n : ℕ) (i : Fin (geoPieces n).length) :
    (geoPieces n)[i] = geoLength (geoDen n) i.val := by
  change ((List.range (n + 1)).map (geoLength (geoDen n)))[i.val] =
    geoLength (geoDen n) i.val
  rw [List.getElem_map]
  simp

private theorem geo_weight_eq (n : ℕ) (eps : Fin (geoPieces n).length → ZMod 3) :
    labeledWeight (geoPieces n) (canonicalLabels (geoPieces n))
        (fun i => ternarySign (eps i)) =
      (binaryFinValue eps : ℝ) / geoDen n := by
  rw [labeledWeight_canonical, binaryFinValue]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [geoPieces_get, geoLength, ← ternaryInt_cast]
  ring

private theorem geo_separation (n : ℕ) (eps : Fin (geoPieces n).length → ZMod 3)
    (heps : eps ≠ 0) :
    1 / geoDen n ≤
      |labeledWeight (geoPieces n) (canonicalLabels (geoPieces n))
        (fun i => ternarySign (eps i))| := by
  have hbne : binaryFinValue eps ≠ 0 := by
    intro hb
    exact heps ((binaryFinValue_eq_zero_iff eps).1 hb)
  have habsInt : (1 : ℝ) ≤ |(binaryFinValue eps : ℝ)| := by
    exact_mod_cast (Int.one_le_abs hbne)
  rw [geo_weight_eq, abs_div, abs_of_pos (geoDen_pos n)]
  exact (div_le_div_iff_of_pos_right (geoDen_pos n)).2 habsInt

private theorem labeledWeight_canonical_congr {l r : List ℝ} (h : l = r)
    (e : Fin l.length → ℝ) :
    labeledWeight l (canonicalLabels l) e =
      labeledWeight r (canonicalLabels r)
        (fun i => e (Fin.cast (congrArg List.length h).symm i)) := by
  subst r
  rfl

private theorem lower_bound_aux (n : ℕ) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  refine ⟨geoMarks n, geoMarks_admissible n, ?_⟩
  intro B hB hdisj
  have hAB : ↑(geoMarks n ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (geoMarks_admissible n).1 hx
    · exact hB.1 hx
  obtain ⟨labels, href⟩ := pieceLengths_union_refines (geoMarks n) B hdisj
  have hgeo := pieceLengths_geoMarks n
  have hgeolen : (pieceLengths (geoMarks n)).length = (geoPieces n).length :=
    congrArg List.length hgeo
  have hBcard : B.card ≤ n := hB.2
  have hk : B.card < (pieceLengths (geoMarks n)).length := by
    rw [hgeolen]
    simp only [geoPieces, List.length_map, List.length_range]
    omega
  have hnonneg : ∀ x ∈ pieceLengths (geoMarks n ∪ B), 0 ≤ x :=
    pieceLengths_nonneg (geoMarks n ∪ B) hAB
  have halt : 1 / geoDen n ≤
      ((pieceLengths (geoMarks n ∪ B)).mergeSort (· ≥ ·)).alternatingSum :=
    alternatingSum_refinement_ge href hk hnonneg (1 / geoDen n) (by
      intro eps heps
      let epsGeo : Fin (geoPieces n).length → ZMod 3 := fun i =>
        eps (Fin.cast hgeolen.symm i)
      have hepsGeo : epsGeo ≠ 0 := by
        intro hz
        apply heps
        funext i
        have hi := congrFun hz (Fin.cast hgeolen i)
        simpa [epsGeo] using hi
      have hw := labeledWeight_canonical_congr hgeo
        (fun i => ternarySign (eps i))
      rw [hw]
      simpa [epsGeo] using geo_separation n epsGeo hepsGeo)
  have hshare := two_mul_firstPlayerShare (pieceLengths (geoMarks n ∪ B))
  have hsum : (pieceLengths (geoMarks n ∪ B)).sum = 1 := by
    simpa [pieceLengths] using
      (sum_consecutive_differences (0 : ℝ) 1 ((geoMarks n ∪ B).sort (· ≤ ·)))
  rw [hsum] at hshare
  have hformula : (2 : ℝ) ^ n / geoDen n = (1 + 1 / geoDen n) / 2 := by
    have hD : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := by
      simpa [geoDen] using (ne_of_gt (geoDen_pos n))
    rw [geoDen]
    field_simp [hD]
    rw [pow_succ]
    ring
  change (2 : ℝ) ^ n / geoDen n ≤
    firstPlayerShare (pieceLengths (geoMarks n ∪ B))
  rw [hformula]
  linarith

private def internalSums (l : List ℝ) : List ℝ := l.dropLast.partialSums.tail

private noncomputable def marksOfPieces (l : List ℝ) : Finset ℝ :=
  (internalSums l).toFinset

private theorem gaps_translate (a c b : ℝ) (l : List ℝ) :
    gaps (a + c) (a + b) (l.map (a + ·)) = gaps c b l := by
  induction l generalizing c with
  | nil => simp [gaps]
  | cons x l ih =>
      simp only [List.map_cons, gaps, List.cons_append, List.zipWith_cons_cons]
      congr 1
      · ring
      · simpa [gaps] using ih x

private theorem scanl_add (a : ℝ) (l : List ℝ) :
    List.scanl (· + ·) a l = l.partialSums.map (a + ·) := by
  induction l generalizing a with
  | nil => simp [List.partialSums]
  | cons x l ih =>
      simp only [List.scanl_cons, List.partialSums_cons, List.map_cons, List.map_map]
      congr 1
      · ring
      · simpa [Function.comp_def, add_assoc] using ih (a + x)

private theorem internalSums_cons_cons (a b : ℝ) (l : List ℝ) :
    internalSums (a :: b :: l) = a :: (internalSums (b :: l)).map (a + ·) := by
  simp only [internalSums]
  simp
  rw [List.partialSums_cons]
  simp only [List.tail_cons]
  cases h : (b :: l).dropLast <;> simp [List.partialSums, h]

private theorem gaps_internalSums : ∀ (l : List ℝ), l ≠ [] →
    gaps 0 l.sum (internalSums l) = l
  | [], hl => by contradiction
  | [a], _ => by simp [gaps, internalSums, List.partialSums]
  | a :: b :: l, _ => by
      rw [internalSums_cons_cons]
      simp only [List.sum_cons]
      change (a - 0) :: gaps a (a + (b + l.sum))
        ((internalSums (b :: l)).map (a + ·)) = a :: b :: l
      have ht := gaps_translate a 0 (b + l.sum) (internalSums (b :: l))
      simp only [add_zero] at ht
      rw [ht]
      have ih := gaps_internalSums (b :: l) (by simp)
      simpa using congrArg (List.cons a) ih

private theorem partialSums_nonneg {l : List ℝ} (h : ∀ x ∈ l, 0 ≤ x) :
    ∀ s ∈ l.partialSums, 0 ≤ s := by
  induction l with
  | nil => simp [List.partialSums]
  | cons a l ih =>
      rw [List.partialSums_cons]
      intro s hs
      simp only [List.mem_cons, List.mem_map] at hs
      rcases hs with rfl | ⟨t, ht, rfl⟩
      · norm_num
      · have ha : 0 ≤ a := h a (by simp)
        have ht0 : 0 ≤ t := ih (fun x hx => h x (by simp [hx])) t ht
        linarith

private theorem partialSums_pairwise_lt {l : List ℝ} (h : ∀ x ∈ l, 0 < x) :
    l.partialSums.Pairwise (· < ·) := by
  induction l with
  | nil => simp [List.partialSums]
  | cons a l ih =>
      rw [List.partialSums_cons, List.pairwise_cons]
      constructor
      · intro s hs
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hs
        have ha : 0 < a := h a (by simp)
        have ht0 : 0 ≤ t := partialSums_nonneg
          (fun x hx => (h x (by simp [hx])).le) t ht
        linarith
      · have htail := ih (fun x hx => h x (by simp [hx]))
        simp only [List.pairwise_map]
        exact htail.imp fun hxy => by linarith

private theorem internalSums_pairwise_lt {l : List ℝ} (h : ∀ x ∈ l, 0 < x) :
    (internalSums l).Pairwise (· < ·) := by
  have hp := partialSums_pairwise_lt
    (l := l.dropLast) (fun x hx => h x (List.mem_of_mem_dropLast hx))
  exact hp.sublist (List.tail_sublist _)

private theorem marksOfPieces_sort {l : List ℝ} (h : ∀ x ∈ l, 0 < x) :
    (marksOfPieces l).sort (· ≤ ·) = internalSums l := by
  have hlt := internalSums_pairwise_lt h
  have hnodup : (internalSums l).Nodup := hlt.imp fun hxy => ne_of_lt hxy
  exact (List.toFinset_sort (· ≤ ·) hnodup).2 (hlt.imp fun hxy => le_of_lt hxy)

private theorem pieceLengths_marksOfPieces {l : List ℝ} (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    pieceLengths (marksOfPieces l) = l := by
  rw [pieceLengths, marksOfPieces_sort hpos]
  change gaps 0 1 (internalSums l) = l
  rw [← hsum]
  exact gaps_internalSums l hl

private theorem internalSums_gaps (a b : ℝ) : ∀ l : List ℝ,
    internalSums (gaps a b l) = l.map (· - a)
  | [] => by simp [gaps, internalSums, List.partialSums]
  | [x] => by
      simp [gaps, internalSums_cons_cons, internalSums, List.partialSums]
  | x :: y :: l => by
      change internalSums ((x - a) :: (y - x) :: gaps y b l) =
        (x - a) :: (y - a) :: l.map (· - a)
      rw [internalSums_cons_cons]
      have ih := internalSums_gaps x b (y :: l)
      change internalSums ((y - x) :: gaps y b l) =
        (y - x) :: l.map (· - x) at ih
      rw [ih]
      simp only [List.map_cons, List.map_map, List.cons.injEq, true_and]
      constructor
      · ring
      · apply List.map_congr_left
        intro z hz
        simp [Function.comp_def]

private theorem marksOfPieces_pieceLengths (S : Finset ℝ) :
    marksOfPieces (pieceLengths S) = S := by
  unfold marksOfPieces pieceLengths
  change (internalSums (gaps 0 1 (S.sort (· ≤ ·)))).toFinset = S
  rw [internalSums_gaps]
  simp

private theorem internalSums_length (l : List ℝ) :
    (internalSums l).length = l.length - 1 := by
  simp [internalSums]

private theorem marksOfPieces_card {l : List ℝ} (hpos : ∀ x ∈ l, 0 < x) :
    (marksOfPieces l).card = l.length - 1 := by
  unfold marksOfPieces
  rw [List.toFinset_card_of_nodup]
  · exact internalSums_length l
  · exact (internalSums_pairwise_lt hpos).imp fun hxy => ne_of_lt hxy

private theorem internalSums_mem_Ioo {l : List ℝ} (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    ∀ x ∈ internalSums l, x ∈ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  change x ∈ l.dropLast.partialSums.tail at hx
  obtain ⟨i, hi, hix⟩ := (List.mem_iff_getElem).1 hx
  have hidx : i + 1 < l.dropLast.partialSums.length := by
    rw [List.length_tail, List.length_partialSums] at hi
    rw [List.length_partialSums]
    omega
  have hidrop : i < l.dropLast.length := by
    rw [List.length_partialSums] at hidx
    omega
  have hxsum : x = ((l.dropLast).take (i + 1)).sum := by
    calc
      x = l.dropLast.partialSums.tail[i] := hix.symm
      _ = l.dropLast.partialSums[i + 1] := by simp
      _ = ((l.dropLast).take (i + 1)).sum := by simp
  have htake_ne : (l.dropLast).take (i + 1) ≠ [] := by
    have : 0 < ((l.dropLast).take (i + 1)).length := by
      rw [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt hidrop)]
      omega
    exact List.ne_nil_of_length_pos this
  have htake_pos : 0 < ((l.dropLast).take (i + 1)).sum :=
    List.sum_pos _ (fun y hy => hpos y
      (List.mem_of_mem_dropLast (List.mem_of_mem_take hy))) htake_ne
  have htake_le : ((l.dropLast).take (i + 1)).sum ≤ l.dropLast.sum :=
    (List.take_sublist (l := l.dropLast) (i + 1)).sum_le_sum
      (fun y hy => (hpos y (List.mem_of_mem_dropLast hy)).le)
  have hlast_pos : 0 < l.getLast hl := hpos _ (List.getLast_mem hl)
  have hdrop_lt : l.dropLast.sum < 1 := by
    have hs := congrArg List.sum (List.dropLast_append_getLast hl)
    simp only [List.sum_append, List.sum_singleton] at hs
    rw [hsum] at hs
    linarith
  rw [hxsum]
  exact ⟨htake_pos, htake_le.trans_lt hdrop_lt⟩

private theorem marksOfPieces_mem_Ioo {l : List ℝ} (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x) (hsum : l.sum = 1) :
    ↑(marksOfPieces l) ⊆ Set.Ioo (0 : ℝ) 1 := by
  intro x hx
  exact internalSums_mem_Ioo hl hpos hsum x (by simpa [marksOfPieces] using hx)

private theorem groupBoundary_mem_flattenPartialSums (groups : List (List ℝ)) :
    ∀ x ∈ (groups.map List.sum).partialSums, x ∈ groups.flatten.partialSums := by
  intro x hx
  obtain ⟨k, hk, hkx⟩ := (List.mem_iff_getElem).1 hx
  have hk' : k ≤ groups.length := by
    simpa [List.length_partialSums] using hk
  let j := (groups.take k).flatten.length
  have hjle : j ≤ groups.flatten.length := by
    exact ((List.take_sublist k groups).flatten).length_le
  have hj : j < groups.flatten.partialSums.length := by
    rw [List.length_partialSums]
    omega
  apply (List.mem_iff_getElem).2
  refine ⟨j, hj, ?_⟩
  rw [List.getElem_partialSums]
  have htake : groups.flatten.take j = (groups.take k).flatten := by
    have hj_eq : j = ((groups.map List.length).take k).sum := by
      simp [j, List.length_flatten, List.map_take]
    rw [hj_eq, List.take_sum_flatten]
  rw [htake, List.sum_flatten]
  simpa [List.map_take] using hkx

private theorem internalSums_mem_partialSums (l : List ℝ) :
    ∀ x ∈ internalSums l, x ∈ l.partialSums := by
  intro x hx
  obtain ⟨i, hi, hix⟩ := (List.mem_iff_getElem).1 hx
  let k := i + 1
  have hkdrop : k ≤ l.dropLast.length := by
    rw [internalSums_length] at hi
    simp [k] at hi ⊢
    omega
  have hk : k < l.partialSums.length := by
    rw [List.length_partialSums]
    have hlen : l.dropLast.length ≤ l.length := by simp
    omega
  have hkdropPS : k < l.dropLast.partialSums.length := by
    rw [List.length_partialSums]
    omega
  apply (List.mem_iff_getElem).2
  refine ⟨k, hk, ?_⟩
  have htake : l.dropLast.take k = l.take k := by
    have hklen : k ≤ l.length := by
      exact hkdrop.trans (by simp)
    have hkdrop' : k ≤ l.length - 1 := by simpa using hkdrop
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left hkdrop']
  calc
    l.partialSums[k] = (l.take k).sum := by simp
    _ = (l.dropLast.take k).sum := by rw [htake]
    _ = (l.dropLast.partialSums)[k]'hkdropPS := by simp
    _ = (internalSums l)[i] := by simp [internalSums, k]
    _ = x := hix

private theorem mem_internalSums_of_mem_partialSums {l : List ℝ} {x : ℝ}
    (hx : x ∈ l.partialSums) (hx0 : 0 < x) (hxsum : x < l.sum) :
    x ∈ internalSums l := by
  obtain ⟨k, hk, hkx⟩ := (List.mem_iff_getElem).1 hx
  have hkle : k ≤ l.length := by
    rw [List.length_partialSums] at hk
    omega
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    simp at hkx
    linarith
  have hklt : k < l.length := by
    by_contra h
    have hkeq : k = l.length := by omega
    subst k
    exact hxsum.ne (by simpa using hkx.symm)
  have hkdrop : k ≤ l.dropLast.length := by simp; omega
  have hi : k - 1 < (internalSums l).length := by
    rw [internalSums_length]
    omega
  apply (List.mem_iff_getElem).2
  refine ⟨k - 1, hi, ?_⟩
  have htake : l.dropLast.take k = l.take k := by
    have hklen : k ≤ l.length := le_of_lt hklt
    have hkdrop' : k ≤ l.length - 1 := by simpa using hkdrop
    rw [List.dropLast_eq_take, List.take_take, Nat.min_eq_left hkdrop']
  have hkdropPS : k < l.dropLast.partialSums.length := by
    rw [List.length_partialSums]
    omega
  calc
    (internalSums l)[k - 1] = (l.dropLast.partialSums)[k]'hkdropPS := by
      have hkpred : k - 1 + 1 = k := by omega
      simp [internalSums, hkpred]
    _ = (l.dropLast.take k).sum := by simp
    _ = (l.take k).sum := by rw [htake]
    _ = l.partialSums[k] := by simp
    _ = x := hkx

private theorem groupBoundary_mem_internalSums {groups : List (List ℝ)}
    (hgroupPos : ∀ g ∈ groups, ∀ x ∈ g, 0 < x)
    (hgroupSumPos : ∀ g ∈ groups, 0 < g.sum)
    (hgroupsSum : (groups.map List.sum).sum = 1) :
    ∀ x ∈ internalSums (groups.map List.sum), x ∈ internalSums groups.flatten := by
  intro x hx
  have hbasePos : ∀ y ∈ groups.map List.sum, 0 < y := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hy
    exact hgroupSumPos g hg
  have hbase_ne : groups.map List.sum ≠ [] := by
    intro hnil
    rw [hnil] at hgroupsSum
    simp at hgroupsSum
  have hxIoo := internalSums_mem_Ioo hbase_ne hbasePos hgroupsSum x hx
  have hxFull : x ∈ (groups.map List.sum).partialSums :=
    internalSums_mem_partialSums _ x hx
  have hxFlatten : x ∈ groups.flatten.partialSums :=
    groupBoundary_mem_flattenPartialSums groups x hxFull
  have hflattenSum : groups.flatten.sum = 1 := by
    rw [List.sum_flatten]
    exact hgroupsSum
  exact mem_internalSums_of_mem_partialSums hxFlatten hxIoo.1 (by
    rw [hflattenSum]
    exact hxIoo.2)

private theorem exists_close_in_finset (S : Finset ℝ) (hcard : 2 ≤ S.card)
    (h0 : 0 ∈ S) (h1 : 1 ∈ S) (hIcc : ↑S ⊆ Set.Icc (0 : ℝ) 1) :
    ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ |y - x| ≤ 1 / (S.card - 1 : ℝ) := by
  let T := (S.erase 0).erase 1
  have h1e : 1 ∈ S.erase 0 := Finset.mem_erase.2 ⟨one_ne_zero, h1⟩
  have hTcard : T.card = S.card - 2 := by
    simp only [T, Finset.card_erase_of_mem h1e, Finset.card_erase_of_mem h0]
    omega
  have hT : ↑T ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    have hx1 := Finset.mem_of_mem_erase hx
    have hxS := Finset.mem_of_mem_erase hx1
    have hxne1 : x ≠ 1 := (Finset.mem_erase.1 hx).1
    have hxne0 : x ≠ 0 := (Finset.mem_erase.1 hx1).1
    have hb := hIcc hxS
    exact ⟨hb.1.lt_of_ne hxne0.symm, hb.2.lt_of_ne hxne1⟩
  let g := pieceLengths T
  have hglen : g.length = S.card - 1 := by
    simp [g, pieceLengths, List.length_zipWith, hTcard]
    omega
  have hgsum : g.sum = 1 := by
    simpa [g, pieceLengths] using
      (sum_consecutive_differences (0 : ℝ) 1 (T.sort (· ≤ ·)))
  have hgpos : ∀ z ∈ g, 0 < z := pieceLengths_pos T hT
  have hgne : g ≠ [] := by
    intro hg
    have := congrArg List.length hg
    simp [hglen] at this
    omega
  let q : ℝ := 1 / (S.card - 1 : ℝ)
  have hcast : ((S.card - 1 : ℕ) : ℝ) = (S.card : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ S.card)]
    norm_num
  have hqsum : (g.map fun _ => q).sum = 1 := by
    simp [q, hglen, nsmul_eq_mul]
    rw [hcast]
    have hd : (S.card : ℝ) - 1 ≠ 0 := by
      have : (1 : ℝ) < S.card := by exact_mod_cast hcard
      linarith
    field_simp [hd]
  have havg : (g.map id).sum ≤ (g.map fun _ => q).sum := by
    rw [List.map_id, hgsum, hqsum]
  obtain ⟨p, hp, hpq⟩ := List.exists_le_of_sum_le hgne id (fun _ => q) havg
  obtain ⟨i, hi, hip⟩ := (List.mem_iff_getElem).1 hp
  let lefts : List ℝ := (0 : ℝ) :: T.sort (· ≤ ·) ++ [1]
  let rights : List ℝ := T.sort (· ≤ ·) ++ [1]
  have hglenT : g.length = T.card + 1 := by
    simp [g, pieceLengths, List.length_zipWith]
  have hil : i < lefts.length := by
    rw [hglenT] at hi
    simp [lefts]
    omega
  have hir : i < rights.length := by
    rw [hglenT] at hi
    simpa [rights] using hi
  let x := lefts[i]
  let y := rights[i]
  have hgap : y - x = p := by
    rw [← hip]
    simp [g, pieceLengths, lefts, rights, x, y]
  have hxS : x ∈ S := by
    have hxmem : x ∈ lefts := List.getElem_mem hil
    simp only [lefts, List.mem_append, List.mem_cons, List.mem_singleton] at hxmem
    rcases hxmem with (hx0 | hxT) | hx1
    · simpa [hx0] using h0
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase
        ((Finset.mem_sort (r := (· ≤ ·))).1 hxT))
    · rcases hx1 with hx1 | hxnil
      · rw [hx1]
        exact h1
      · simp at hxnil
  have hyS : y ∈ S := by
    have hymem : y ∈ rights := List.getElem_mem hir
    simp only [rights, List.mem_append, Finset.mem_sort, List.mem_singleton] at hymem
    rcases hymem with hyT | hy1
    · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hyT)
    · simpa [hy1] using h1
  have hp0 : 0 < p := hgpos p hp
  refine ⟨x, hxS, y, hyS, ?_, ?_⟩
  · intro hxy
    rw [hxy] at hgap
    linarith
  · rw [abs_of_nonneg (by linarith [hgap]), hgap]
    exact hpq

private structure PairingRefinement (p q : List ℝ) where
  pGroups : List (List ℝ)
  qGroups : List (List ℝ)
  paired : List ℝ
  residual : List ℝ
  p_sums : pGroups.map List.sum = p
  q_sums : qGroups.map List.sum = q
  p_perm : pGroups.flatten.Perm (paired ++ residual)
  q_perm : qGroups.flatten.Perm paired
  p_pos : ∀ x ∈ pGroups.flatten, 0 < x
  q_pos : ∀ x ∈ qGroups.flatten, 0 < x
  residual_sum : residual.sum = p.sum - q.sum
  length_bound : pGroups.flatten.length + qGroups.flatten.length ≤
    2 * (p.length + q.length) - 1

private theorem singletonGroups_sums (l : List ℝ) :
    (l.map fun x => [x]).map List.sum = l := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private theorem singletonGroups_flatten (l : List ℝ) :
    (l.map fun x => [x]).flatten = l := by
  induction l with
  | nil => simp
  | cons x l ih => simp [ih]

private noncomputable def pairingRefinement (p q : List ℝ)
    (hp : ∀ x ∈ p, 0 < x) (hq : ∀ x ∈ q, 0 < x)
    (hsum : q.sum ≤ p.sum) : PairingRefinement p q := by
  classical
  cases p with
  | nil =>
      cases q with
      | nil =>
          exact ⟨[], [], [], [], by simp, by simp, by simp, by simp, by simp,
            by simp, by simp, by simp⟩
      | cons b qs =>
          have hb : 0 < b := hq b (by simp)
          have hqs : 0 ≤ qs.sum := List.sum_nonneg fun x hx => (hq x (by simp [hx])).le
          simp only [List.sum_nil, List.sum_cons] at hsum
          exact (by linarith : False).elim
  | cons a ps =>
      cases q with
      | nil =>
          refine ⟨(a :: ps).map (fun x => [x]), [], [], a :: ps,
            ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact singletonGroups_sums (a :: ps)
          · simp
          · rw [singletonGroups_flatten]
            simp
          · simp
          · rw [singletonGroups_flatten]
            exact hp
          · simp
          · simp
          · rw [singletonGroups_flatten]
            simp
            omega
      | cons b qs =>
          have ha : 0 < a := hp a (by simp)
          have hb : 0 < b := hq b (by simp)
          have hp' : ∀ x ∈ ps, 0 < x := fun x hx => hp x (by simp [hx])
          have hq' : ∀ x ∈ qs, 0 < x := fun x hx => hq x (by simp [hx])
          by_cases hab : a < b
          · have hrec_sum : ((b - a) :: qs).sum ≤ ps.sum := by
              simp only [List.sum_cons] at hsum ⊢
              linarith
            let r := pairingRefinement ps ((b - a) :: qs) hp'
              (by
                intro x hx
                simp only [List.mem_cons] at hx
                rcases hx with rfl | hx
                · linarith
                · exact hq' x hx)
              hrec_sum
            cases hrg : r.qGroups with
            | nil =>
                have := r.q_sums
                simp [hrg] at this
            | cons g gs =>
                refine ⟨[a] :: r.pGroups, (a :: g) :: gs, a :: r.paired,
                  r.residual, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · simpa [r.p_sums]
                · have hrs := r.q_sums
                  simp only [hrg, List.map_cons, List.cons.injEq] at hrs
                  rcases hrs with ⟨hgsum, hgs⟩
                  simp only [List.map_cons, List.sum_cons, List.cons.injEq]
                  constructor
                  · linarith
                  · exact hgs
                · simpa using r.p_perm.cons a
                · simpa [hrg] using r.q_perm.cons a
                · intro x hx
                  simp only [List.flatten_cons, List.mem_append, List.mem_singleton] at hx
                  rcases hx with rfl | hx
                  · exact ha
                  · exact r.p_pos x hx
                · intro x hx
                  simp only [hrg, List.flatten_cons, List.mem_append, List.mem_cons] at hx
                  rcases hx with (rfl | hx) | hx
                  · exact ha
                  · exact r.q_pos x (by simp [hrg, hx])
                  · exact r.q_pos x (by simp [hrg, hx])
                · rw [r.residual_sum]
                  simp only [List.sum_cons]
                  ring
                · have hrlen := r.length_bound
                  simp only [hrg, List.flatten_cons, List.length_append, List.length_cons,
                    List.length_singleton, List.length_nil] at hrlen ⊢
                  omega
          · by_cases hba : b < a
            · have hrec_sum : qs.sum ≤ ((a - b) :: ps).sum := by
                simp only [List.sum_cons] at hsum ⊢
                linarith
              let r := pairingRefinement ((a - b) :: ps) qs
                (by
                  intro x hx
                  simp only [List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · linarith
                  · exact hp' x hx)
                hq' hrec_sum
              cases hrg : r.pGroups with
              | nil =>
                  have := r.p_sums
                  simp [hrg] at this
              | cons g gs =>
                  refine ⟨(b :: g) :: gs, [b] :: r.qGroups, b :: r.paired,
                    r.residual, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · have hrs := r.p_sums
                    simp only [hrg, List.map_cons, List.cons.injEq] at hrs
                    rcases hrs with ⟨hgsum, hgs⟩
                    simp only [List.map_cons, List.sum_cons, List.cons.injEq]
                    constructor
                    · linarith
                    · exact hgs
                  · simpa [r.q_sums]
                  · simpa [hrg] using r.p_perm.cons b
                  · simpa using r.q_perm.cons b
                  · intro x hx
                    simp only [hrg, List.flatten_cons, List.mem_append, List.mem_cons] at hx
                    rcases hx with (rfl | hx) | hx
                    · exact hb
                    · exact r.p_pos x (by simp [hrg, hx])
                    · exact r.p_pos x (by simp [hrg, hx])
                  · intro x hx
                    simp only [List.flatten_cons, List.mem_append, List.mem_singleton] at hx
                    rcases hx with rfl | hx
                    · exact hb
                    · exact r.q_pos x hx
                  · rw [r.residual_sum]
                    simp only [List.sum_cons]
                    ring
                  · have hrlen := r.length_bound
                    simp only [hrg, List.flatten_cons, List.length_append, List.length_cons,
                      List.length_singleton, List.length_nil] at hrlen ⊢
                    omega
            · have habEq : a = b := le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
              subst b
              let r := pairingRefinement ps qs hp' hq' (by
                simp only [List.sum_cons] at hsum
                linarith)
              refine ⟨[a] :: r.pGroups, [a] :: r.qGroups, a :: r.paired,
                r.residual, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · simpa [r.p_sums]
              · simpa [r.q_sums]
              · simpa using r.p_perm.cons a
              · simpa using r.q_perm.cons a
              · intro x hx
                simp only [List.flatten_cons, List.mem_append, List.mem_singleton] at hx
                rcases hx with rfl | hx
                · exact ha
                · exact r.p_pos x hx
              · intro x hx
                simp only [List.flatten_cons, List.mem_append, List.mem_singleton] at hx
                rcases hx with rfl | hx
                · exact ha
                · exact r.q_pos x hx
              · rw [r.residual_sum]
                simp only [List.sum_cons]
                ring
              · have hrlen := r.length_bound
                simp only [List.flatten_cons, List.length_append,
                  List.length_singleton, List.length_cons, List.length_nil] at hrlen ⊢
                omega
termination_by p.length + q.length

private inductive RefinementSide
  | positive
  | negative
  | neutral
  deriving DecidableEq

private def positiveValues : List (RefinementSide × ℝ) → List ℝ
  | [] => []
  | (.positive, x) :: l => x :: positiveValues l
  | _ :: l => positiveValues l

private def negativeValues : List (RefinementSide × ℝ) → List ℝ
  | [] => []
  | (.negative, x) :: l => x :: negativeValues l
  | _ :: l => negativeValues l

private noncomputable def neutralPieces : List (RefinementSide × ℝ) → List ℝ
  | [] => []
  | (.neutral, x) :: l => x / 2 :: x / 2 :: neutralPieces l
  | _ :: l => neutralPieces l

private noncomputable def neutralHalves : List (RefinementSide × ℝ) → List ℝ
  | [] => []
  | (.neutral, x) :: l => x / 2 :: neutralHalves l
  | _ :: l => neutralHalves l

private theorem refinementSide_length (l : List (RefinementSide × ℝ)) :
    2 * l.length =
      2 * (positiveValues l).length + 2 * (negativeValues l).length +
        (neutralPieces l).length := by
  induction l with
  | nil => simp [positiveValues, negativeValues, neutralPieces]
  | cons p l ih =>
      rcases p with ⟨s, x⟩
      cases s <;> simp [positiveValues, negativeValues, neutralPieces] at ih ⊢ <;> omega

private theorem neutralPieces_pos {l : List (RefinementSide × ℝ)}
    (h : ∀ p ∈ l, 0 < p.2) : ∀ x ∈ neutralPieces l, 0 < x := by
  induction l with
  | nil => simp [neutralPieces]
  | cons p l ih =>
      rcases p with ⟨s, a⟩
      cases s
      · simp only [neutralPieces]
        exact ih fun p hp => h p (by simp [hp])
      · simp only [neutralPieces]
        exact ih fun p hp => h p (by simp [hp])
      · have ha : 0 < a := h (.neutral, a) (by simp)
        have hi := ih fun p hp => h p (by simp [hp])
        simp only [neutralPieces, List.mem_cons]
        intro x hx
        rcases hx with rfl | rfl | hx
        · linarith
        · linarith
        · exact hi x hx

private theorem neutralPieces_perm (l : List (RefinementSide × ℝ)) :
    (neutralPieces l).Perm (neutralHalves l ++ neutralHalves l) := by
  classical
  induction l with
  | nil => simp [neutralPieces, neutralHalves]
  | cons p l ih =>
      rcases p with ⟨s, a⟩
      cases s
      · simpa [neutralPieces, neutralHalves] using ih
      · simpa [neutralPieces, neutralHalves] using ih
      · apply List.perm_iff_count.mpr
        intro x
        simp only [neutralPieces, neutralHalves, List.count_cons, List.count_append]
        rw [ih.count_eq]
        simp only [List.count_append]
        omega

private theorem assembleRefinement {l : List (RefinementSide × ℝ)}
    {pGroups qGroups : List (List ℝ)}
    (hp : pGroups.map List.sum = positiveValues l)
    (hq : qGroups.map List.sum = negativeValues l) :
    ∃ groups : List (List ℝ),
      groups.map List.sum = l.map Prod.snd ∧
      groups.flatten.Perm
        (pGroups.flatten ++ qGroups.flatten ++ neutralPieces l) := by
  classical
  induction l generalizing pGroups qGroups with
  | nil =>
      have hp' : pGroups = [] := by simpa [positiveValues] using congrArg List.length hp
      have hq' : qGroups = [] := by simpa [negativeValues] using congrArg List.length hq
      subst pGroups
      subst qGroups
      exact ⟨[], by simp, by simp [neutralPieces]⟩
  | cons p l ih =>
      rcases p with ⟨s, a⟩
      cases s with
      | positive =>
          cases pGroups with
          | nil => simp [positiveValues] at hp
          | cons g pGroups =>
              simp only [positiveValues, List.map_cons, List.cons.injEq] at hp
              obtain ⟨hgsum, hp⟩ := hp
              obtain ⟨groups, hsums, hperm⟩ := ih hp hq
              refine ⟨g :: groups, ?_, ?_⟩
              · simp [hgsum, hsums]
              · simpa [neutralPieces, List.append_assoc] using
                  (List.Perm.refl g).append hperm
      | negative =>
          cases qGroups with
          | nil => simp [negativeValues] at hq
          | cons g qGroups =>
              simp only [negativeValues, List.map_cons, List.cons.injEq] at hq
              obtain ⟨hgsum, hq⟩ := hq
              obtain ⟨groups, hsums, hperm⟩ := ih hp hq
              refine ⟨g :: groups, ?_, ?_⟩
              · simp [hgsum, hsums]
              · have hfront := (List.Perm.refl g).append hperm
                have hswap0 : (g ++ pGroups.flatten).Perm (pGroups.flatten ++ g) :=
                  List.perm_append_comm
                have hswap := hswap0.append
                  (List.Perm.refl (qGroups.flatten ++ neutralPieces l))
                exact hfront.trans (by
                  simpa [negativeValues, neutralPieces, List.append_assoc] using hswap)
      | neutral =>
          obtain ⟨groups, hsums, hperm⟩ := ih hp hq
          refine ⟨[a / 2, a / 2] :: groups, ?_, ?_⟩
          · simp only [List.map_cons, List.sum_cons, List.sum_singleton,
              List.sum_nil, List.cons.injEq]
            constructor
            · ring
            · exact hsums
          · have hfront := (List.Perm.refl [a / 2, a / 2]).append hperm
            have hswap0 :
                ([a / 2, a / 2] ++ (pGroups.flatten ++ qGroups.flatten)).Perm
                  ((pGroups.flatten ++ qGroups.flatten) ++ [a / 2, a / 2]) :=
              List.perm_append_comm
            have hswap := hswap0.append (List.Perm.refl (neutralPieces l))
            exact hfront.trans (by simpa [neutralPieces, List.append_assoc] using hswap)

private def subsetWeight {m : ℕ} (w : Fin m → ℝ) (P : Finset (Fin m)) : ℝ :=
  ∑ i ∈ P, w i

private theorem exists_close_subset_sums {m : ℕ} (hm : 0 < m)
    (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) :
    ∃ P Q : Finset (Fin m), P ≠ Q ∧
      |subsetWeight w P - subsetWeight w Q| ≤ 1 / ((2 : ℝ) ^ m - 1) := by
  classical
  let U : Finset (Finset (Fin m)) := Finset.univ.powerset
  let S : Finset ℝ := U.image (subsetWeight w)
  have hUcard : U.card = 2 ^ m := by simp [U]
  have hScard_le : S.card ≤ U.card := Finset.card_image_le
  have hden_pos : (0 : ℝ) < (2 : ℝ) ^ m - 1 := by
    have : (1 : ℝ) < 2 ^ m := one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hm)
    linarith
  by_cases hcollision : S.card < U.card
  · obtain ⟨P, hPU, Q, hQU, hPQ, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_image_lt hcollision
    refine ⟨P, Q, hPQ, ?_⟩
    rw [heq, sub_self, abs_zero]
    exact one_div_nonneg.mpr hden_pos.le
  · have hScard : S.card = 2 ^ m := by
      rw [← hUcard]
      exact Nat.le_antisymm hScard_le (Nat.le_of_not_gt hcollision)
    have h0 : 0 ∈ S := by
      apply Finset.mem_image.2
      refine ⟨∅, by simp [U], ?_⟩
      simp [subsetWeight]
    have h1 : 1 ∈ S := by
      apply Finset.mem_image.2
      refine ⟨Finset.univ, by simp [U], ?_⟩
      simpa [subsetWeight] using hsum
    have hIcc : ↑S ⊆ Set.Icc (0 : ℝ) 1 := by
      intro x hx
      obtain ⟨P, hPU, rfl⟩ := Finset.mem_image.1 hx
      have hPsub : P ⊆ Finset.univ := Finset.mem_powerset.1 hPU
      constructor
      · exact Finset.sum_nonneg fun i hi => hw i
      · rw [← hsum]
        exact Finset.sum_le_sum_of_subset_of_nonneg hPsub
          (fun i hi hnot => hw i)
    have hcard2 : 2 ≤ S.card := by
      rw [hScard]
      have hpow : (2 : ℕ) ^ 1 ≤ 2 ^ m :=
        pow_le_pow_right' (by norm_num) (by omega)
      simpa using hpow
    obtain ⟨x, hxS, y, hyS, hxy, hclose⟩ :=
      exists_close_in_finset S hcard2 h0 h1 hIcc
    obtain ⟨P, hPU, hPx⟩ := Finset.mem_image.1 hxS
    obtain ⟨Q, hQU, hQy⟩ := Finset.mem_image.1 hyS
    refine ⟨P, Q, ?_, ?_⟩
    · intro hPQ
      subst Q
      exact hxy (hPx.symm.trans hQy)
    · rw [← hPx, ← hQy] at hclose
      rw [abs_sub_comm]
      simpa [hScard] using hclose

private def refinementSideOf {m : ℕ} (P Q : Finset (Fin m)) (i : Fin m) :
    RefinementSide :=
  if i ∈ P then
    if i ∈ Q then .neutral else .positive
  else if i ∈ Q then .negative else .neutral

private def refinementTagged (base : List ℝ)
    (P Q : Finset (Fin base.length)) : List (RefinementSide × ℝ) :=
  (List.finRange base.length).map fun i => (refinementSideOf P Q i, base[i])

private theorem refinementTagged_values (base : List ℝ)
    (P Q : Finset (Fin base.length)) :
    (refinementTagged base P Q).map Prod.snd = base := by
  simp [refinementTagged, List.map_map, Function.comp_def, List.map_getElem_finRange]

private theorem positiveValues_map_sum {m : ℕ} (w : Fin m → ℝ)
    (P Q : Finset (Fin m)) (indices : List (Fin m)) :
    (positiveValues
      (indices.map fun i => (refinementSideOf P Q i, w i))).sum =
      (indices.map fun i => if i ∈ P ∧ i ∉ Q then w i else 0).sum := by
  induction indices with
  | nil => simp [positiveValues]
  | cons i indices ih =>
      by_cases hiP : i ∈ P <;> by_cases hiQ : i ∈ Q
      · have hside : refinementSideOf P Q i = .neutral := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [positiveValues, hiP, hiQ] using ih
      · have hside : refinementSideOf P Q i = .positive := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [positiveValues, hiP, hiQ] using congrArg (w i + ·) ih
      · have hside : refinementSideOf P Q i = .negative := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [positiveValues, hiP, hiQ] using ih
      · have hside : refinementSideOf P Q i = .neutral := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [positiveValues, hiP, hiQ] using ih

private theorem negativeValues_map_sum {m : ℕ} (w : Fin m → ℝ)
    (P Q : Finset (Fin m)) (indices : List (Fin m)) :
    (negativeValues
      (indices.map fun i => (refinementSideOf P Q i, w i))).sum =
      (indices.map fun i => if i ∉ P ∧ i ∈ Q then w i else 0).sum := by
  induction indices with
  | nil => simp [negativeValues]
  | cons i indices ih =>
      by_cases hiP : i ∈ P <;> by_cases hiQ : i ∈ Q
      · have hside : refinementSideOf P Q i = .neutral := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [negativeValues, hiP, hiQ] using ih
      · have hside : refinementSideOf P Q i = .positive := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [negativeValues, hiP, hiQ] using ih
      · have hside : refinementSideOf P Q i = .negative := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [negativeValues, hiP, hiQ] using congrArg (w i + ·) ih
      · have hside : refinementSideOf P Q i = .neutral := by
          simp [refinementSideOf, hiP, hiQ]
        simp only [List.map_cons, hside]
        simpa [negativeValues, hiP, hiQ] using ih

private theorem positiveValues_refinementTagged_sum (base : List ℝ)
    (P Q : Finset (Fin base.length)) :
    (positiveValues (refinementTagged base P Q)).sum =
      subsetWeight (fun i => base[i]) (P \ Q) := by
  rw [refinementTagged, positiveValues_map_sum]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  unfold subsetWeight
  have hset : P \ Q = Finset.univ.filter (fun i => i ∈ P ∧ i ∉ Q) := by
    ext i
    simp
  rw [hset, Finset.sum_filter]

private theorem negativeValues_refinementTagged_sum (base : List ℝ)
    (P Q : Finset (Fin base.length)) :
    (negativeValues (refinementTagged base P Q)).sum =
      subsetWeight (fun i => base[i]) (Q \ P) := by
  rw [refinementTagged, negativeValues_map_sum]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  unfold subsetWeight
  have hset : Q \ P = Finset.univ.filter (fun i => i ∉ P ∧ i ∈ Q) := by
    ext i
    simp [and_comm]
  rw [hset, Finset.sum_filter]

private theorem positiveValues_pos_of_snd {l : List (RefinementSide × ℝ)}
    (h : ∀ p ∈ l, 0 < p.2) : ∀ x ∈ positiveValues l, 0 < x := by
  induction l with
  | nil => simp [positiveValues]
  | cons p l ih =>
      rcases p with ⟨s, a⟩
      have ht : ∀ p ∈ l, 0 < p.2 := fun p hp => h p (by simp [hp])
      have hhead : 0 < a := h (s, a) (by simp)
      cases s with
      | positive =>
          simp only [positiveValues, List.mem_cons]
          intro x hx
          rcases hx with rfl | hx
          · exact hhead
          · exact ih ht x hx
      | negative => simpa [positiveValues] using ih ht
      | neutral => simpa [positiveValues] using ih ht

private theorem negativeValues_pos_of_snd {l : List (RefinementSide × ℝ)}
    (h : ∀ p ∈ l, 0 < p.2) : ∀ x ∈ negativeValues l, 0 < x := by
  induction l with
  | nil => simp [negativeValues]
  | cons p l ih =>
      rcases p with ⟨s, a⟩
      have ht : ∀ p ∈ l, 0 < p.2 := fun p hp => h p (by simp [hp])
      have hhead : 0 < a := h (s, a) (by simp)
      cases s with
      | positive => simpa [negativeValues] using ih ht
      | negative =>
          simp only [negativeValues, List.mem_cons]
          intro x hx
          rcases hx with rfl | hx
          · exact hhead
          · exact ih ht x hx
      | neutral => simpa [negativeValues] using ih ht

private theorem positiveValues_refinementTagged_pos {base : List ℝ}
    (hbase : ∀ x ∈ base, 0 < x) (P Q : Finset (Fin base.length)) :
    ∀ x ∈ positiveValues (refinementTagged base P Q), 0 < x := by
  apply positiveValues_pos_of_snd
  intro z hz
  rw [refinementTagged] at hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
  exact hbase base[i] (List.getElem_mem i.isLt)

private theorem negativeValues_refinementTagged_pos {base : List ℝ}
    (hbase : ∀ x ∈ base, 0 < x) (P Q : Finset (Fin base.length)) :
    ∀ x ∈ negativeValues (refinementTagged base P Q), 0 < x := by
  apply negativeValues_pos_of_snd
  intro z hz
  rw [refinementTagged] at hz
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hz
  exact hbase base[i] (List.getElem_mem i.isLt)

private theorem refinementTagged_pos {base : List ℝ}
    (hbase : ∀ x ∈ base, 0 < x) (P Q : Finset (Fin base.length)) :
    ∀ p ∈ refinementTagged base P Q, 0 < p.2 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  exact hbase base[i] (List.getElem_mem i.isLt)

private theorem subsetWeight_sub (base : List ℝ)
    (P Q : Finset (Fin base.length)) :
    subsetWeight (fun i => base[i]) P - subsetWeight (fun i => base[i]) Q =
      subsetWeight (fun i => base[i]) (P \ Q) -
        subsetWeight (fun i => base[i]) (Q \ P) := by
  let w : Fin base.length → ℝ := fun i => base[i]
  have hP : subsetWeight w P =
      subsetWeight w (P \ Q) + subsetWeight w (P ∩ Q) := by
    calc
      subsetWeight w P = subsetWeight w ((P \ Q) ∪ (P ∩ Q)) := by
        rw [Finset.sdiff_union_inter]
      _ = subsetWeight w (P \ Q) + subsetWeight w (P ∩ Q) := by
        unfold subsetWeight
        rw [Finset.sum_union (Finset.disjoint_sdiff_inter P Q)]
  have hQ : subsetWeight w Q =
      subsetWeight w (Q \ P) + subsetWeight w (P ∩ Q) := by
    calc
      subsetWeight w Q = subsetWeight w ((Q \ P) ∪ (Q ∩ P)) := by
        rw [Finset.sdiff_union_inter]
      _ = subsetWeight w (Q \ P) + subsetWeight w (P ∩ Q) := by
        unfold subsetWeight
        rw [Finset.sum_union (Finset.disjoint_sdiff_inter Q P),
          Finset.inter_comm Q P]
  change subsetWeight w P - subsetWeight w Q =
    subsetWeight w (P \ Q) - subsetWeight w (Q \ P)
  rw [hP, hQ]
  ring

private theorem symmetricDifference_nonempty {α : Type*} [DecidableEq α]
    {P Q : Finset α} (hPQ : P ≠ Q) :
    (P \ Q).Nonempty ∨ (Q \ P).Nonempty := by
  by_contra h
  rw [not_or] at h
  have hPempty : P \ Q = ∅ := Finset.not_nonempty_iff_eq_empty.1 h.1
  have hQempty : Q \ P = ∅ := Finset.not_nonempty_iff_eq_empty.1 h.2
  have hPsubQ : P ⊆ Q := Finset.sdiff_eq_empty_iff_subset.1 hPempty
  have hQsubP : Q ⊆ P := Finset.sdiff_eq_empty_iff_subset.1 hQempty
  exact hPQ (Finset.Subset.antisymm hPsubQ hQsubP)

private theorem refinement_from_subsets {base : List ℝ}
    (hbase : ∀ x ∈ base, 0 < x)
    (P Q : Finset (Fin base.length)) (hPQ : P ≠ Q)
    (hle : subsetWeight (fun i => base[i]) Q ≤
      subsetWeight (fun i => base[i]) P) :
    ∃ groups : List (List ℝ), ∃ paired residual : List ℝ,
      groups.map List.sum = base ∧
      groups.flatten.Perm (paired ++ paired ++ residual) ∧
      (∀ x ∈ groups.flatten, 0 < x) ∧
      residual.sum = subsetWeight (fun i => base[i]) P -
        subsetWeight (fun i => base[i]) Q ∧
      groups.flatten.length ≤ 2 * base.length - 1 := by
  classical
  let tagged := refinementTagged base P Q
  let p := positiveValues tagged
  let q := negativeValues tagged
  have hp : ∀ x ∈ p, 0 < x := by
    simpa [p, tagged] using positiveValues_refinementTagged_pos hbase P Q
  have hq : ∀ x ∈ q, 0 < x := by
    simpa [q, tagged] using negativeValues_refinementTagged_pos hbase P Q
  have hpsum : p.sum = subsetWeight (fun i => base[i]) (P \ Q) := by
    simpa [p, tagged] using positiveValues_refinementTagged_sum base P Q
  have hqsum : q.sum = subsetWeight (fun i => base[i]) (Q \ P) := by
    simpa [q, tagged] using negativeValues_refinementTagged_sum base P Q
  have hdiff := subsetWeight_sub base P Q
  have hqp : q.sum ≤ p.sum := by
    rw [hpsum, hqsum]
    linarith
  let r := pairingRefinement p q hp hq hqp
  have hpmap : r.pGroups.map List.sum = positiveValues tagged := by
    simpa [p] using r.p_sums
  have hqmap : r.qGroups.map List.sum = negativeValues tagged := by
    simpa [q] using r.q_sums
  obtain ⟨groups, hgroups_sum, hgroups_perm⟩ := assembleRefinement hpmap hqmap
  let halves := neutralHalves tagged
  let paired := r.paired ++ halves
  have hcomponents :
      (r.pGroups.flatten ++ r.qGroups.flatten ++ neutralPieces tagged).Perm
        (paired ++ paired ++ r.residual) := by
    apply List.perm_iff_count.mpr
    intro x
    simp only [List.count_append]
    rw [r.p_perm.count_eq, r.q_perm.count_eq,
      (neutralPieces_perm tagged).count_eq]
    simp only [paired, halves, List.count_append]
    omega
  have hperm : groups.flatten.Perm (paired ++ paired ++ r.residual) :=
    hgroups_perm.trans hcomponents
  have htagpos : ∀ z ∈ tagged, 0 < z.2 := by
    simpa [tagged] using refinementTagged_pos hbase P Q
  have hneutral : ∀ x ∈ neutralPieces tagged, 0 < x := neutralPieces_pos htagpos
  have hgroups_pos : ∀ x ∈ groups.flatten, 0 < x := by
    intro x hx
    have hx' := hgroups_perm.mem_iff.1 hx
    rcases List.mem_append.1 hx' with hpq | hn
    · rcases List.mem_append.1 hpq with hp' | hq'
      · exact r.p_pos x hp'
      · exact r.q_pos x hq'
    · exact hneutral x hn
  have hactive : 0 < p.length + q.length := by
    rcases symmetricDifference_nonempty hPQ with hP | hQ
    · have hpos : 0 < subsetWeight (fun i => base[i]) (P \ Q) :=
        Finset.sum_pos (fun i hi => hbase base[i] (List.getElem_mem i.isLt)) hP
      by_contra hlen
      have : p = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at hpsum
      simp at hpsum
      exact (ne_of_gt hpos) hpsum.symm
    · have hpos : 0 < subsetWeight (fun i => base[i]) (Q \ P) :=
        Finset.sum_pos (fun i hi => hbase base[i] (List.getElem_mem i.isLt)) hQ
      by_contra hlen
      have : q = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this] at hqsum
      simp at hqsum
      exact (ne_of_gt hpos) hqsum.symm
  have hside := refinementSide_length tagged
  have htaglen : tagged.length = base.length := by simp [tagged, refinementTagged]
  have hgroups_len : groups.flatten.length =
      r.pGroups.flatten.length + r.qGroups.flatten.length +
        (neutralPieces tagged).length := by
    simpa [List.length_append, Nat.add_assoc] using hgroups_perm.length_eq
  have hlength : groups.flatten.length ≤ 2 * base.length - 1 := by
    have hrlen := r.length_bound
    rw [htaglen] at hside
    rw [hgroups_len]
    simp only [p, q] at hrlen hactive
    omega
  refine ⟨groups, paired, r.residual, ?_, hperm, hgroups_pos, ?_, hlength⟩
  · simpa [tagged] using hgroups_sum.trans (refinementTagged_values base P Q)
  · rw [r.residual_sum, hpsum, hqsum]
    exact hdiff.symm

private theorem alternatingSum_cons : ∀ (a : ℝ) (l : List ℝ),
    (a :: l).alternatingSum = a - l.alternatingSum
  | a, [] => by simp [List.alternatingSum]
  | a, [b] => by simp [List.alternatingSum]; ring
  | a, b :: c :: l => by
      simp only [List.alternatingSum]
      rw [alternatingSum_cons c l]
      ring

private theorem alternatingSum_le_head {a : ℝ} {l : List ℝ}
    (hsorted : (a :: l).Pairwise (· ≥ ·))
    (hnonneg : ∀ x ∈ a :: l, 0 ≤ x) : (a :: l).alternatingSum ≤ a := by
  rw [alternatingSum_cons]
  have htail : l.Pairwise (· ≥ ·) := (List.pairwise_cons.1 hsorted).2
  have htail_nonneg : ∀ x ∈ l, 0 ≤ x := by
    intro x hx
    exact hnonneg x (by simp [hx])
  have halt := alternatingSum_nonneg_of_pairwise l htail htail_nonneg
  linarith

private theorem alternatingSum_orderedInsert_abs (x : ℝ) (hx : 0 ≤ x) :
    ∀ l : List ℝ, l.Pairwise (· ≥ ·) → (∀ y ∈ l, 0 ≤ y) →
      |(l.orderedInsert (· ≥ ·) x).alternatingSum - l.alternatingSum| ≤ x
  | [], _, _ => by simp [List.alternatingSum, abs_of_nonneg hx]
  | a :: l, hsorted, hnonneg => by
      by_cases hxa : x ≥ a
      · rw [List.orderedInsert_cons_of_le (r := (· ≥ ·)) l hxa]
        rw [alternatingSum_cons x (a :: l)]
        have halt0 : 0 ≤ (a :: l).alternatingSum :=
          alternatingSum_nonneg_of_pairwise (a :: l) hsorted hnonneg
        have halta : (a :: l).alternatingSum ≤ a :=
          alternatingSum_le_head hsorted hnonneg
        rw [abs_le]
        constructor <;> linarith
      · rw [List.orderedInsert_of_not_le (r := (· ≥ ·)) l hxa]
        rw [alternatingSum_cons a (l.orderedInsert (· ≥ ·) x),
          alternatingSum_cons a l]
        have ih := alternatingSum_orderedInsert_abs x hx l
          (List.pairwise_cons.1 hsorted).2 (fun y hy => hnonneg y (by simp [hy]))
        have heq :
            (a - (l.orderedInsert (· ≥ ·) x).alternatingSum) -
                (a - l.alternatingSum) =
              -((l.orderedInsert (· ≥ ·) x).alternatingSum - l.alternatingSum) := by
          ring
        rw [heq, abs_neg]
        exact ih

private def duplicateEach : List ℝ → List ℝ
  | [] => []
  | x :: l => x :: x :: duplicateEach l

private theorem duplicateEach_perm (l : List ℝ) :
    (duplicateEach l).Perm (l ++ l) := by
  classical
  induction l with
  | nil => simp [duplicateEach]
  | cons a l ih =>
      apply List.perm_iff_count.mpr
      intro x
      simp only [duplicateEach, List.count_cons, List.count_append]
      rw [ih.count_eq]
      simp only [List.count_append]
      omega

private theorem duplicateEach_pairwise : ∀ {l : List ℝ},
    l.Pairwise (· ≥ ·) → (duplicateEach l).Pairwise (· ≥ ·)
  | [], _ => by simp [duplicateEach]
  | a :: l, hsorted => by
      have hhead : ∀ b ∈ l, a ≥ b := (List.pairwise_cons.1 hsorted).1
      have htail : l.Pairwise (· ≥ ·) := (List.pairwise_cons.1 hsorted).2
      have ih := duplicateEach_pairwise htail
      have hmem : ∀ {b}, b ∈ duplicateEach l → b ∈ l := by
        intro b hb
        have hb' := (duplicateEach_perm l).mem_iff.1 hb
        simpa using hb'
      rw [duplicateEach, List.pairwise_cons]
      constructor
      · intro b hb
        simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact le_rfl
        · exact hhead b (hmem hb)
      · rw [List.pairwise_cons]
        constructor
        · intro b hb
          exact hhead b (hmem hb)
        · exact ih

private theorem duplicateEach_alternatingSum (l : List ℝ) :
    (duplicateEach l).alternatingSum = 0 := by
  induction l with
  | nil => simp [duplicateEach, List.alternatingSum]
  | cons a l ih => simp [duplicateEach, List.alternatingSum, ih]

private noncomputable def insertAll (extra sorted : List ℝ) : List ℝ :=
  extra.foldr (fun x l => l.orderedInsert (· ≥ ·) x) sorted

private theorem insertAll_perm (extra sorted : List ℝ) :
    (insertAll extra sorted).Perm (extra ++ sorted) := by
  induction extra with
  | nil => simp [insertAll]
  | cons x extra ih =>
      simp only [insertAll, List.foldr_cons]
      exact (List.perm_orderedInsert (r := (· ≥ ·)) x _).trans (ih.cons x)

private theorem insertAll_pairwise {extra sorted : List ℝ}
    (hsorted : sorted.Pairwise (· ≥ ·)) :
    (insertAll extra sorted).Pairwise (· ≥ ·) := by
  induction extra with
  | nil => simpa [insertAll]
  | cons x extra ih =>
      simp only [insertAll, List.foldr_cons]
      exact ih.orderedInsert x _

private theorem insertAll_nonneg {extra sorted : List ℝ}
    (hextra : ∀ x ∈ extra, 0 ≤ x) (hsorted : ∀ x ∈ sorted, 0 ≤ x) :
    ∀ x ∈ insertAll extra sorted, 0 ≤ x := by
  intro x hx
  have hx' := (insertAll_perm extra sorted).mem_iff.1 hx
  rcases List.mem_append.1 hx' with hx' | hx'
  · exact hextra x hx'
  · exact hsorted x hx'

private theorem insertAll_alternatingSum_le {extra sorted : List ℝ}
    (hextra : ∀ x ∈ extra, 0 ≤ x)
    (hsorted_pairwise : sorted.Pairwise (· ≥ ·))
    (hsorted_nonneg : ∀ x ∈ sorted, 0 ≤ x) :
    (insertAll extra sorted).alternatingSum ≤
      sorted.alternatingSum + extra.sum := by
  induction extra with
  | nil => simp [insertAll]
  | cons x extra ih =>
      have hx : 0 ≤ x := hextra x (by simp)
      have hextra' : ∀ y ∈ extra, 0 ≤ y := fun y hy => hextra y (by simp [hy])
      let current := insertAll extra sorted
      have hcurrent_sorted : current.Pairwise (· ≥ ·) :=
        insertAll_pairwise hsorted_pairwise
      have hcurrent_nonneg : ∀ y ∈ current, 0 ≤ y :=
        insertAll_nonneg hextra' hsorted_nonneg
      have hins := alternatingSum_orderedInsert_abs x hx current
        hcurrent_sorted hcurrent_nonneg
      have hstep : (current.orderedInsert (· ≥ ·) x).alternatingSum ≤
          current.alternatingSum + x := by
        have hdifference :
            (current.orderedInsert (· ≥ ·) x).alternatingSum -
                current.alternatingSum ≤ x :=
          le_trans (le_abs_self _) hins
        linarith
      have hcurrent_bound := ih hextra'
      change (current.orderedInsert (· ≥ ·) x).alternatingSum ≤
        sorted.alternatingSum + (x + extra.sum)
      linarith

private theorem alternatingSum_le_residual {values paired residual : List ℝ}
    (hperm : values.Perm (paired ++ paired ++ residual))
    (hnonneg : ∀ x ∈ values, 0 ≤ x) :
    (values.mergeSort (· ≥ ·)).alternatingSum ≤ residual.sum := by
  let sortedPaired := paired.mergeSort (· ≥ ·)
  let doubled := duplicateEach sortedPaired
  let canonical := insertAll residual doubled
  have htarget_nonneg : ∀ x ∈ paired ++ paired ++ residual, 0 ≤ x := by
    intro x hx
    exact hnonneg x (hperm.mem_iff.2 hx)
  have hpaired_nonneg : ∀ x ∈ paired, 0 ≤ x := by
    intro x hx
    exact htarget_nonneg x (by simp [hx])
  have hresidual_nonneg : ∀ x ∈ residual, 0 ≤ x := by
    intro x hx
    exact htarget_nonneg x (by simp [hx])
  have hsortedPaired_nonneg : ∀ x ∈ sortedPaired, 0 ≤ x := by
    intro x hx
    exact hpaired_nonneg x
      ((List.mergeSort_perm paired (· ≥ ·)).mem_iff.1 (by simpa [sortedPaired] using hx))
  have hdoubled_nonneg : ∀ x ∈ doubled, 0 ≤ x := by
    intro x hx
    apply hsortedPaired_nonneg x
    have hx' : x ∈ sortedPaired ++ sortedPaired :=
      (duplicateEach_perm sortedPaired).mem_iff.1 (by simpa [doubled] using hx)
    simpa using hx'
  have hsortedPaired_pairwise : sortedPaired.Pairwise (· ≥ ·) := by
    exact List.pairwise_mergeSort' (fun x y : ℝ => x ≥ y) paired
  have hdoubled_pairwise : doubled.Pairwise (· ≥ ·) := by
    exact duplicateEach_pairwise hsortedPaired_pairwise
  have hcanonical_pairwise : canonical.Pairwise (· ≥ ·) := by
    exact insertAll_pairwise hdoubled_pairwise
  have hcanonical_perm : canonical.Perm (paired ++ paired ++ residual) := by
    have h1 := insertAll_perm residual doubled
    have h2 : doubled.Perm (paired ++ paired) := by
      exact (duplicateEach_perm sortedPaired).trans
        ((List.mergeSort_perm paired (· ≥ ·)).append
          (List.mergeSort_perm paired (· ≥ ·)))
    have h3 : (residual ++ doubled).Perm (residual ++ (paired ++ paired)) :=
      (List.Perm.refl residual).append h2
    have h4 : (residual ++ (paired ++ paired)).Perm
        ((paired ++ paired) ++ residual) := List.perm_append_comm
    exact h1.trans (h3.trans (by simpa [List.append_assoc] using h4))
  have hmerge_pairwise : (values.mergeSort (· ≥ ·)).Pairwise (· ≥ ·) :=
    List.pairwise_mergeSort' (fun x y : ℝ => x ≥ y) values
  have hmerge_perm : (values.mergeSort (· ≥ ·)).Perm canonical :=
    (List.mergeSort_perm values (· ≥ ·)).trans (hperm.trans hcanonical_perm.symm)
  have heq : values.mergeSort (· ≥ ·) = canonical :=
    List.Perm.eq_of_pairwise' hmerge_pairwise hcanonical_pairwise hmerge_perm
  rw [heq]
  have hbound := insertAll_alternatingSum_le hresidual_nonneg
    hdoubled_pairwise hdoubled_nonneg
  simpa [canonical, doubled, duplicateEach_alternatingSum] using hbound

private theorem halvesGroups_sum (l : List ℝ) :
    ((l.map fun x => [x / 2, x / 2]).map List.sum) = l := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, List.sum_singleton, List.cons.injEq,
        List.sum_nil]
      constructor
      · ring
      · exact ih

private theorem halvesGroups_perm (l : List ℝ) :
    (l.map fun x => [x / 2, x / 2]).flatten.Perm
      ((l.map fun x => x / 2) ++ (l.map fun x => x / 2)) := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
      apply List.perm_iff_count.mpr
      intro x
      simp only [List.map_cons, List.flatten_cons, List.count_append, List.count_cons]
      rw [ih.count_eq]
      simp only [List.count_append, List.count_nil]
      omega

private theorem realize_group_refinement (n : ℕ) (A : Finset ℝ)
    (hA : AdmissibleMark n A) (groups : List (List ℝ))
    (paired residual : List ℝ)
    (hgroups : groups.map List.sum = pieceLengths A)
    (hperm : groups.flatten.Perm (paired ++ paired ++ residual))
    (hpos : ∀ x ∈ groups.flatten, 0 < x)
    (hlength : groups.flatten.length ≤ A.card + n + 1)
    (hresidual : residual.sum ≤ 1 / geoDen n) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  let values := groups.flatten
  have hbasePos : ∀ x ∈ pieceLengths A, 0 < x := pieceLengths_pos A hA.1
  have hbaseSum : (pieceLengths A).sum = 1 := by
    simpa [pieceLengths] using
      (sum_consecutive_differences (0 : ℝ) 1 (A.sort (· ≤ ·)))
  have hgroupsSum : (groups.map List.sum).sum = 1 := by rw [hgroups, hbaseSum]
  have hvaluesSum : values.sum = 1 := by
    simpa [values, List.sum_flatten] using hgroupsSum
  have hvaluesNe : values ≠ [] := by
    intro hnil
    rw [hnil] at hvaluesSum
    simp at hvaluesSum
  have hgroupPos : ∀ g ∈ groups, ∀ x ∈ g, 0 < x := by
    intro g hg x hx
    exact hpos x (by
      apply List.mem_flatten.2
      exact ⟨g, hg, hx⟩)
  have hgroupSumPos : ∀ g ∈ groups, 0 < g.sum := by
    intro g hg
    have hmem : g.sum ∈ groups.map List.sum := List.mem_map.2 ⟨g, hg, rfl⟩
    rw [hgroups] at hmem
    exact hbasePos g.sum hmem
  let C := marksOfPieces values
  have hAsubC : A ⊆ C := by
    intro x hx
    have hmarksA := marksOfPieces_pieceLengths A
    have hxBase : x ∈ internalSums (pieceLengths A) := by
      rw [← hmarksA] at hx
      simpa [marksOfPieces] using hx
    have hxGroups : x ∈ internalSums (groups.map List.sum) := by
      simpa [hgroups] using hxBase
    have hxValues := groupBoundary_mem_internalSums hgroupPos hgroupSumPos
      hgroupsSum x hxGroups
    simpa [C, marksOfPieces, values] using hxValues
  let B := C \ A
  have hdisj : Disjoint A B := by
    exact disjoint_sdiff_self_right
  have hUnion : A ∪ B = C := by
    apply Finset.Subset.antisymm
    · intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact hAsubC hx
      · exact (Finset.mem_sdiff.1 hx).1
    · intro x hx
      by_cases hxA : x ∈ A
      · exact Finset.mem_union_left _ hxA
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hx, hxA⟩)
  have hCmem : ↑C ⊆ Set.Ioo (0 : ℝ) 1 := by
    simpa [C, values] using marksOfPieces_mem_Ioo hvaluesNe hpos hvaluesSum
  have hBcard : B.card ≤ n := by
    have hCcard := marksOfPieces_card hpos
    change (C \ A).card ≤ n
    rw [Finset.card_sdiff_of_subset hAsubC]
    simpa [C, values] using (show C.card - A.card ≤ n by
      rw [hCcard]
      omega)
  have hBadm : AdmissibleMark n B := by
    constructor
    · intro x hx
      exact hCmem (Finset.mem_sdiff.1 hx).1
    · exact hBcard
  have hpieces : pieceLengths (A ∪ B) = values := by
    rw [hUnion]
    exact pieceLengths_marksOfPieces hvaluesNe hpos hvaluesSum
  have halt : (values.mergeSort (· ≥ ·)).alternatingSum ≤ 1 / geoDen n := by
    exact (alternatingSum_le_residual hperm (fun x hx => (hpos x hx).le)).trans hresidual
  have hshare := two_mul_firstPlayerShare values
  rw [hvaluesSum] at hshare
  have hformula : (2 : ℝ) ^ n / geoDen n = (1 + 1 / geoDen n) / 2 := by
    have hD : (2 : ℝ) ^ (n + 1) - 1 ≠ 0 := by
      simpa [geoDen] using (ne_of_gt (geoDen_pos n))
    rw [geoDen]
    field_simp [hD]
    rw [pow_succ]
    ring
  refine ⟨B, hBadm, hdisj, ?_⟩
  change firstPlayerShare (pieceLengths (A ∪ B)) ≤ (2 : ℝ) ^ n / geoDen n
  rw [hpieces, hformula]
  linarith

private theorem upper_bound_aux (n : ℕ) (A : Finset ℝ)
    (hA : AdmissibleMark n A) :
    ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
      L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  let base := pieceLengths A
  have hbasePos : ∀ x ∈ base, 0 < x := by
    simpa [base] using pieceLengths_pos A hA.1
  have hbaseSum : base.sum = 1 := by
    simpa [base, pieceLengths] using
      (sum_consecutive_differences (0 : ℝ) 1 (A.sort (· ≤ ·)))
  have hbaseLen : base.length = A.card + 1 := by
    simp [base, pieceLengths, List.length_zipWith]
  by_cases hcard : A.card < n
  · let groups := base.map fun x => [x / 2, x / 2]
    let paired := base.map fun x => x / 2
    have hgroups : groups.map List.sum = pieceLengths A := by
      simpa [groups, base] using halvesGroups_sum base
    have hperm : groups.flatten.Perm (paired ++ paired ++ ([] : List ℝ)) := by
      simpa [groups, paired] using halvesGroups_perm base
    have hpos : ∀ x ∈ groups.flatten, 0 < x := by
      intro x hx
      simp only [groups, List.mem_flatten, List.mem_map] at hx
      obtain ⟨g, ⟨a, ha, rfl⟩, hx⟩ := hx
      have hxEq : x = a / 2 := by simpa using hx
      rw [hxEq]
      linarith [hbasePos a ha]
    have hlength : groups.flatten.length ≤ A.card + n + 1 := by
      have hlen : groups.flatten.length = 2 * base.length := by
        simp [groups, List.length_flatten, Function.comp_def, Nat.mul_comm]
      rw [hlen, hbaseLen]
      omega
    apply realize_group_refinement n A hA groups paired [] hgroups hperm hpos hlength
    simpa using (one_div_pos.mpr (geoDen_pos n)).le
  · have hcardEq : A.card = n :=
      Nat.le_antisymm hA.2 (Nat.le_of_not_gt hcard)
    have hm : 0 < base.length := by rw [hbaseLen]; omega
    let w : Fin base.length → ℝ := fun i => base[i]
    have hw : ∀ i, 0 ≤ w i := fun i => (hbasePos base[i] (List.getElem_mem i.isLt)).le
    have hwsum : ∑ i, w i = 1 := by
      rw [← List.sum_ofFn]
      simpa [w] using hbaseSum
    obtain ⟨P, Q, hPQ, hclose⟩ := exists_close_subset_sums hm w hw hwsum
    by_cases hle : subsetWeight w Q ≤ subsetWeight w P
    · obtain ⟨groups, paired, residual, hgroups, hperm, hpos, hres, hlength⟩ :=
        refinement_from_subsets hbasePos P Q hPQ hle
      have hresBound : residual.sum ≤ 1 / geoDen n := by
        rw [hres]
        have hclose' := hclose
        rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hclose'
        simpa [w, geoDen, hbaseLen, hcardEq] using hclose'
      have hlength' : groups.flatten.length ≤ A.card + n + 1 := by
        rw [hbaseLen, hcardEq] at hlength
        omega
      exact realize_group_refinement n A hA groups paired residual hgroups hperm hpos
        hlength' hresBound
    · have hle' : subsetWeight w P ≤ subsetWeight w Q := le_of_not_ge hle
      obtain ⟨groups, paired, residual, hgroups, hperm, hpos, hres, hlength⟩ :=
        refinement_from_subsets hbasePos Q P hPQ.symm hle'
      have hresBound : residual.sum ≤ 1 / geoDen n := by
        rw [hres]
        have hclose' := hclose
        rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle')] at hclose'
        simpa [w, geoDen, hbaseLen, hcardEq] using hclose'
      have hlength' : groups.flatten.length ≤ A.card + n + 1 := by
        rw [hbaseLen, hcardEq] at hlength
        omega
      exact realize_group_refinement n A hA groups paired residual hgroups hperm hpos
        hlength' hresBound

/-- There are `|S| + 1` pieces. -/
theorem pieceLengths_length (S : Finset ℝ) :
    (pieceLengths S).length = S.card + 1 := by
  simp [pieceLengths, List.length_zipWith]

/-- Basic sanity bound: Liu Bang's share lies in `[0, 1]` for admissible cut
sets (it is a subset-sum of the piece lengths, which are nonnegative and sum to
`1`). -/
theorem L_mem_Icc (A B : Finset ℝ)
    (hA : ↑A ⊆ Set.Ioo (0 : ℝ) 1) (hB : ↑B ⊆ Set.Ioo (0 : ℝ) 1) :
    L A B ∈ Set.Icc (0 : ℝ) 1 := by
  let pieces := pieceLengths (A ∪ B)
  let sorted := pieces.mergeSort (· ≥ ·)
  let chosen := (sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1)
  have hAB : ↑(A ∪ B) ⊆ Set.Ioo (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact hA hx
    · exact hB hx
  have hpieces : ∀ x ∈ pieces, 0 ≤ x := pieceLengths_nonneg (A ∪ B) hAB
  have hsorted : ∀ x ∈ sorted, 0 ≤ x := by
    intro x hx
    exact hpieces x ((List.mergeSort_perm pieces (· ≥ ·)).mem_iff.1 hx)
  have hchosen : ∀ x ∈ chosen, 0 ≤ x := by
    intro x hx
    simp only [chosen, List.mem_map, List.mem_filter] at hx
    obtain ⟨p, ⟨hp, _⟩, rfl⟩ := hx
    exact hsorted p.1 (by
      have hp' : p.1 ∈ sorted.zipIdx.map Prod.fst :=
        List.mem_map.mpr ⟨p, hp, rfl⟩
      simpa using hp')
  have hsub : List.Sublist chosen sorted := by
    simpa [chosen] using
      (List.filter_sublist.map (fun p : ℝ × ℕ => p.1) :
        List.Sublist
          ((sorted.zipIdx.filter (fun p => p.2 % 2 = 0)).map (fun p => p.1))
          (sorted.zipIdx.map (fun p => p.1)))
  have hsum : pieces.sum = 1 := pieceLengths_sum (A ∪ B) hAB
  have hsorted_sum : sorted.sum = 1 := by
    rw [← hsum]
    exact (List.mergeSort_perm pieces (· ≥ ·)).sum_eq
  change chosen.sum ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact List.sum_nonneg hchosen
  · rw [← hsorted_sum]
    exact hsub.sum_le_sum hsorted

/-! ## Main Statements -/

/-- **Main statement.** For every positive integer `n`, Liu Bang's guaranteed
value equals `2^n / (2^(n+1) - 1)`. -/
theorem V_eq (n : ℕ) (hn : 0 < n) : V n = (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  let target : ℝ := (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1)
  let emptyA : {A : Finset ℝ // AdmissibleMark n A} := by
    refine ⟨∅, ?_⟩
    simp [AdmissibleMark]
  letI : Nonempty {A : Finset ℝ // AdmissibleMark n A} := ⟨emptyA⟩
  have hInnerBddBelow (A : {A : Finset ℝ // AdmissibleMark n A}) :
      BddBelow (Set.range fun B :
        {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} => L A.1 B.1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨B, rfl⟩
    exact (L_mem_Icc A.1 B.1 A.2.1 B.2.1.1).1
  have hInnerLeOne (A : {A : Finset ℝ // AdmissibleMark n A}) :
      (⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) ≤ 1 := by
    let emptyB : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} := by
      refine ⟨∅, ?_, ?_⟩
      · simp [AdmissibleMark]
      · simp
    exact (ciInf_le (hInnerBddBelow A) emptyB).trans
      (L_mem_Icc A.1 ∅ A.2.1 (by simp)).2
  have hOuterBdd : BddAbove (Set.range fun A :
      {A : Finset ℝ // AdmissibleMark n A} =>
        ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) := by
    refine ⟨1, ?_⟩
    rintro y ⟨A, rfl⟩
    exact hInnerLeOne A
  have hlower : target ≤ V n := by
    obtain ⟨A, hA, hguarantee⟩ := lower_bound_aux n
    let markedA : {A : Finset ℝ // AdmissibleMark n A} := ⟨A, hA⟩
    have hAt : target ≤
        ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint markedA.1 B},
          L markedA.1 B.1 := by
      let emptyB : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint markedA.1 B} := by
        refine ⟨∅, ?_, ?_⟩
        · simp [AdmissibleMark]
        · simp
      letI : Nonempty
          {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint markedA.1 B} := ⟨emptyB⟩
      apply le_ciInf
      intro B
      exact hguarantee B.1 B.2.1 B.2.2
    change target ≤ ⨆ A : {A : Finset ℝ // AdmissibleMark n A},
      ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1
    exact le_ciSup_of_le hOuterBdd markedA hAt
  have hupper : V n ≤ target := by
    change (⨆ A : {A : Finset ℝ // AdmissibleMark n A},
      ⨅ B : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B}, L A.1 B.1) ≤ target
    apply ciSup_le
    intro A
    obtain ⟨B, hB, hdisj, hL⟩ := upper_bound_aux n A.1 A.2
    let markedB : {B : Finset ℝ // AdmissibleMark n B ∧ Disjoint A.1 B} :=
      ⟨B, hB, hdisj⟩
    exact (ciInf_le (hInnerBddBelow A) markedB).trans hL
  change V n = target
  exact le_antisymm hupper hlower

/-- **Lower bound.** Liu Bang has an admissible marking `A` such that for every
admissible marking `B` disjoint from `A`, his guaranteed share is at least
`2^n / (2^(n+1) - 1)`. -/
theorem lower_bound (n : ℕ) (hn : 0 < n) :
    ∃ A : Finset ℝ, AdmissibleMark n A ∧
      ∀ B : Finset ℝ, AdmissibleMark n B → Disjoint A B →
        (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) ≤ L A B := by
  exact lower_bound_aux n

/-- **Upper bound / optimality.** For every admissible marking `A` of Liu Bang,
Xiang Yu has an admissible marking `B` disjoint from `A` with
`L A B ≤ 2^n / (2^(n+1) - 1)`, so Liu Bang cannot guarantee more. -/
theorem upper_bound (n : ℕ) (hn : 0 < n) :
    ∀ A : Finset ℝ, AdmissibleMark n A →
      ∃ B : Finset ℝ, AdmissibleMark n B ∧ Disjoint A B ∧
        L A B ≤ (2 : ℝ) ^ n / ((2 : ℝ) ^ (n + 1) - 1) := by
  intro A hA
  exact upper_bound_aux n A hA

end LiuBangXiangYu
