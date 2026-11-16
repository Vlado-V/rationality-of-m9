module

public import M9StacksIntegration.FlagThreeQuotient
public import M9StacksIntegration.HomDualBundleTensor
public import M9StacksIntegration.FlagThreeIncidenceSection
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.WhitneySum
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapRuleTwist

/-!
# The actual incidence tensor Chern family on the three-step flag

The actual quotient sequences on the native flag tower remain short
exact after tensoring by the actual rank-ten bundle. Applying the
genuine native Whitney formula twice factors the actual rank-thirty
tensor Chern family into the three actual rank-ten line twists.

No splitting or Chern-factorization property is supplied as input.
This is the geometric Chern-filtration step before the three actual
projective Gysin evaluations.
-/

@[expose] public noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u v

namespace M9Native.FlagThreeTensorChern

/-- Actual exact tensoring, using the native finite-local-freeness/flatness
bridge and the native sheaf-tensor short-exact theorem. -/
private theorem exists_shortExact_tensor {T : Scheme.{u}} {A B G : T.Modules}
    (F : T.Modules) (hF : SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (v : A ⟶ B) (w : B ⟶ G) (hw : v ≫ w = 0)
    (h : (ShortComplex.mk v w hw).ShortExact) :
    ∃ (v' : Scheme.Modules.tensorObj A F ⟶ Scheme.Modules.tensorObj B F)
      (w' : Scheme.Modules.tensorObj B F ⟶ Scheme.Modules.tensorObj G F)
      (hz : v' ≫ w' = 0), (ShortComplex.mk v' w' hz).ShortExact := by
  have := h.mono_f
  have := h.epi_g
  let : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := T.ringCatSheaf) F :=
    Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree F (hM := hF)
  exact Scheme.Modules.tensorObj_shortExact v w hw h.exact F
    (Scheme.Modules.isFlat_of_isFiniteLocallyFree F)

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u, u, u} D]

local instance quotient1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeQuotient.quotientBundle D 0) 1 := FlagThreeQuotient.quotientBundle_rank D 0

local instance quotient2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeQuotient.quotientBundle D 1) 2 := FlagThreeQuotient.quotientBundle_rank D 1

local instance quotient3Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeQuotient.quotientBundle D 2) 3 := FlagThreeQuotient.quotientBundle_rank D 2

local instance line1Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (FlagThreeQuotient.line1 D) 1 := FlagThreeQuotient.line1_rank D

local instance line2Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (FlagThreeQuotient.line2 D) 1 := FlagThreeQuotient.line2_rank D

local instance line3Rank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (FlagThreeQuotient.line3 D) 1 := FlagThreeQuotient.line3_rank D

/-- The native tensor rank theorem, stated at the literal scheme tensor object. -/
theorem tensor_rank {T : Scheme.{u}} (A B : T.Modules) (a b : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} A a]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} B b] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Modules.tensorObj A B) (a * b) :=
  SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf T A B a b

/-- The actual tensor Chern family factors by the actual flag line
pieces. Exact tensoring and native Whitney supply both equalities. -/
theorem tensor_chernFamily_eq_three_factors (C : ChowSituation.{u})
    (q : FlagThreeQuotient.space D ⟶ C.S) [LocallyOfFiniteType q]
    (F : (FlagThreeQuotient.space D).Modules)
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10] :
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) F) 30 :=
      tensor_rank (FlagThreeQuotient.quotientBundle D 2) F 3 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10 :=
      tensor_rank (FlagThreeQuotient.line3 D) F 1 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F) 10 :=
      tensor_rank (FlagThreeQuotient.line2 D) F 1 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F) 10 :=
      tensor_rank (FlagThreeQuotient.line1 D) F 1 10
    chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) F) 30 =
      chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10 *
        (chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F) 10 *
          chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F) 10) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 1) F) 20 :=
    tensor_rank (FlagThreeQuotient.quotientBundle D 1) F 2 10
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F) 10 :=
    tensor_rank (FlagThreeQuotient.line1 D) F 1 10
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F) 10 :=
    tensor_rank (FlagThreeQuotient.line2 D) F 1 10
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10 :=
    tensor_rank (FlagThreeQuotient.line3 D) F 1 10
  obtain ⟨u32, v32, w32, h32⟩ := exists_shortExact_tensor F
    hF.isFiniteLocallyFree (kernel.ι (FlagThreeQuotient.step32 D))
    (FlagThreeQuotient.step32 D) (kernel.condition _) (FlagThreeQuotient.sequence32_shortExact D)
  obtain ⟨u21, v21, w21, h21⟩ := exists_shortExact_tensor F
    hF.isFiniteLocallyFree (kernel.ι (FlagThreeQuotient.step21 D))
    (FlagThreeQuotient.step21 D) (kernel.condition _) (FlagThreeQuotient.sequence21_shortExact D)
  have h32' := @chernFamily_eq_mul_of_shortExact C _ q _
    (ShortComplex.mk u32 v32 w32) h32 10 20
    (tensor_rank (FlagThreeQuotient.line3 D) F 1 10)
    (tensor_rank (FlagThreeQuotient.quotientBundle D 1) F 2 10)
  have h21' := @chernFamily_eq_mul_of_shortExact C _ q _
    (ShortComplex.mk u21 v21 w21) h21 10 10
    (tensor_rank (FlagThreeQuotient.line2 D) F 1 10)
    (tensor_rank (FlagThreeQuotient.line1 D) F 1 10)
  exact h32'.trans (congrArg
    (fun z => chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10 * z)
    h21')

private theorem graded_mul_of_gt {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]
    (A B : GradedCapFamily G) (a b : ℕ)
    (hA : ∀ k i, a < i → A k i = 0) (hB : ∀ k i, b < i → B k i = 0)
    (k : ℤ) (m : ℕ) (hm : a + b < m) : (A * B) k m = 0 := by
  apply AddMonoidHom.ext
  intro x
  rw [gradedCap_mul_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
  rw [convolveTerm_of_le _ _ _ hjm]
  by_cases hjb : j ≤ b
  · exact capTo_of_eq_zero A _ (hA _ _ (by omega)) _
  · simp only [hB k j (by omega), AddMonoidHom.zero_apply, capTo_zero]

private theorem graded_mul_top_heq {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]
    (A B : GradedCapFamily G) (a b : ℕ)
    (hA : ∀ k i, a < i → A k i = 0) (hB : ∀ k i, b < i → B k i = 0)
    (k : ℤ) (x : G k) :
    (A * B) k (a + b) x ≍ A (k - (b : ℤ)) a (B k b x) := by
  have hs : (A * B) k (a + b) x = convolveTerm A B k (a + b) b x := by
    rw [gradedCap_mul_apply]
    apply Finset.sum_eq_single b
    · intro j hj hjb
      have hjm : j ≤ a + b := by have := Finset.mem_range.mp hj; omega
      rw [convolveTerm_of_le _ _ _ hjm]
      by_cases hjle : j ≤ b
      · exact capTo_of_eq_zero A _ (hA _ _ (by omega)) _
      · simp only [hB k j (by omega), AddMonoidHom.zero_apply, capTo_zero]
    · intro hb
      exact (hb (Finset.mem_range.mpr (by omega))).elim
  refine (heq_of_eq hs).trans ?_
  rw [convolveTerm_of_le _ _ _ (show b ≤ a + b by omega),
    capTo_congr_index A (Nat.add_sub_cancel a b), capTo_def]
  exact gradedDegreeCast_heq _ _

private theorem graded_apply_heq {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]
    (A : GradedCapFamily G) (i : ℕ) {k l : ℤ} (hkl : k = l)
    {x : G k} {y : G l} (hxy : x ≍ y) : A k i x ≍ A l i y := by
  cases hkl
  exact heq_of_eq (congrArg (A k i) (eq_of_heq hxy))

/-- The actual top-rank tensor cap is the three ordered genuine line-twist
caps. Only the equality of the integer grading is heterogeneous. -/
theorem tensor_topCap_heq (C : ChowSituation.{u})
    (q : FlagThreeQuotient.space D ⟶ C.S) [LocallyOfFiniteType q]
    (F : (FlagThreeQuotient.space D).Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10]
    (k : ℤ) (α : chowGroup C q k) :
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) F) 30 :=
      tensor_rank (FlagThreeQuotient.quotientBundle D 2) F 3 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10 :=
      tensor_rank (FlagThreeQuotient.line3 D) F 1 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F) 10 :=
      tensor_rank (FlagThreeQuotient.line2 D) F 1 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F) 10 :=
      tensor_rank (FlagThreeQuotient.line1 D) F 1 10
    chernCap C 30 q (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) F)
      k (Fin.last 30) α ≍
    chernCap C 10 q (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F)
      ((k - 10) - 10) (Fin.last 10)
      (chernCap C 10 q (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F)
        (k - 10) (Fin.last 10)
        (chernCap C 10 q (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F)
          k (Fin.last 10) α)) := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) F) 30 :=
    tensor_rank (FlagThreeQuotient.quotientBundle D 2) F 3 10
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10 :=
    tensor_rank (FlagThreeQuotient.line3 D) F 1 10
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F) 10 :=
    tensor_rank (FlagThreeQuotient.line2 D) F 1 10
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F) 10 :=
    tensor_rank (FlagThreeQuotient.line1 D) F 1 10
  let A := chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line3 D) F) 10
  let B := chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line2 D) F) 10
  let L := chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.line1 D) F) 10
  have hA : ∀ l i, 10 < i → A l i = 0 := by
    intro l i hi
    exact chernCapFamilyOnChow_of_gt C (chernCap C) q _ 10 l (by omega)
  have hB : ∀ l i, 10 < i → B l i = 0 := by
    intro l i hi
    exact chernCapFamilyOnChow_of_gt C (chernCap C) q _ 10 l (by omega)
  have hL : ∀ l i, 10 < i → L l i = 0 := by
    intro l i hi
    exact chernCapFamilyOnChow_of_gt C (chernCap C) q _ 10 l (by omega)
  have hBL : ∀ l i, 20 < i → (B * L) l i = 0 :=
    fun l i hi => graded_mul_of_gt B L 10 10 hB hL l i hi
  have houter := graded_mul_top_heq A (B * L) 10 20 hA hBL k α
  have hinner := graded_mul_top_heq B L 10 10 hB hL k α
  have hstep := graded_apply_heq A 10 (show k - 20 = (k - 10) - 10 by omega) hinner
  have he := congrArg (fun T : GradedCapFamily (chowGroup C q) => T k 30 α)
    (tensor_chernFamily_eq_three_factors D C q F)
  change chernFamily C q (Scheme.Modules.tensorObj (FlagThreeQuotient.quotientBundle D 2) F)
      30 k 30 α ≍ A ((k - 10) - 10) 10 (B (k - 10) 10 (L k 10 α))
  exact (heq_of_eq he).trans (houter.trans hstep)


/-- Tensor-factor order is changed by the actual native braiding
isomorphism, rather than by identifying the two tensor objects. -/
theorem topCap_tensor_braiding {T : Scheme.{u}} (C : ChowSituation.{u})
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (L F : T.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10]
    (k : ℤ) (α : chowGroup C q k) :
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj L F) 10 := tensor_rank L F 1 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj F L) 10 := tensor_rank F L 10 1
    chernCap C 10 q (Scheme.Modules.tensorObj L F) k (Fin.last 10) α =
      chernCap C 10 q (Scheme.Modules.tensorObj F L) k (Fin.last 10) α := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj L F) 10 := tensor_rank L F 1 10
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj F L) 10 := tensor_rank F L 10 1
  let e : Scheme.Modules.tensorObj L F ≅ Scheme.Modules.tensorObj F L :=
    Scheme.Modules.tensorObjBraiding L F
  exact chernCap_congr C q 10 e k (Fin.last 10) α

local instance dualFiniteLocallyFree {T : Scheme.{u}} (E : T.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} (dualSheaf E) :=
  isFiniteLocallyFree_dualSheaf E inferInstance

/-- The literal incidence Hom top cap equals the actual tensor top cap.
Composing with `tensor_topCap_heq` yields the three ordered line-twist caps. -/
theorem incidence_topCap_eq_tensor {Y : Scheme.{u}} (E F : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F 10]
    (C : ChowSituation.{u}) (q : FlagThreeIncidence.space E ⟶ C.S)
    [LocallyOfFiniteType q] (k : ℤ) (α : chowGroup C q k) :
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (FlagThreeIncidence.projection E)).obj F) 10 :=
      @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _
        (FlagThreeIncidence.projection E) F 10 hF
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeIncidence.quotientBundle E) 3 := FlagThreeIncidence.quotientBundle_rank E
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeIncidence.quotientBundle E)
        ((Scheme.Modules.pullback (FlagThreeIncidence.projection E)).obj F)) 30 :=
      tensor_rank (FlagThreeIncidence.quotientBundle E) _ 3 10
    letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeIncidence.incidenceBundle E F) 30 :=
      FlagThreeIncidence.incidenceBundle_rank_thirty E F hF
    chernCap C 30 q (FlagThreeIncidence.incidenceBundle E F) k (Fin.last 30) α =
      chernCap C 30 q (Scheme.Modules.tensorObj (FlagThreeIncidence.quotientBundle E)
        ((Scheme.Modules.pullback (FlagThreeIncidence.projection E)).obj F))
        k (Fin.last 30) α := by
  let F3 := (Scheme.Modules.pullback (FlagThreeIncidence.projection E)).obj F
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F3 10 :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _
      (FlagThreeIncidence.projection E) F 10 hF
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeIncidence.quotientBundle E) 3 := FlagThreeIncidence.quotientBundle_rank E
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (FlagThreeIncidence.quotientBundle E) F3) 30 :=
    tensor_rank (FlagThreeIncidence.quotientBundle E) F3 3 10
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (FlagThreeIncidence.incidenceBundle E F) 30 :=
    FlagThreeIncidence.incidenceBundle_rank_thirty E F hF
  let e : Scheme.Modules.tensorObj (FlagThreeIncidence.quotientBundle E) F3 ≅
      FlagThreeIncidence.incidenceBundle E F :=
    HomDualBundleTensor.tensorIsoHomDualBundle (FlagThreeIncidence.quotientBundle E) F3 3
  exact (chernCap_congr C q 30 e k (Fin.last 30) α).symm

end M9Native.FlagThreeTensorChern
