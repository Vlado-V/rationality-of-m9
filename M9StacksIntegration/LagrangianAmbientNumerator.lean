module

public import M9StacksIntegration.LagrangianPluckerCapDegree
public import M9StacksIntegration.LagrangianTopChernCycle
public import M9StacksIntegration.ChowLineProperPush
public import M9StacksIntegration.LineFamilyCapPower
public import M9StacksIntegration.LagrangianPluckerOperationalDegree

/-!
# The actual LG determinant degree on the original Grassmannian

The true inclusion pushforward, the true determinant pullback, and the
proved top-Chern fundamental class give the original Grassmannian
numerator. No numerical value or class comparison is an input.
-/

@[expose] public noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u v

namespace M9Native.LagrangianActualDegree

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianDegree
open ChowCapWords GradedLineCapSubring GradedCapVirtualSchur

/-- The actual ordered convolution in grades six and three, proved
before any large geometric scheme or cap expression is substituted. -/
theorem degreeNine_product_six_three {G : ℤ → Type v}
    [∀ k, AddCommGroup (G k)] (a b : GradedCapFamily G) (α : G 9) :
    (a * homComponent 3 b) 9 9 α = a 6 6 (b 9 3 α) := by
  rw [mul_apply_of_homogeneous_right _ (isHomogeneous_homComponent 3 _) 6,
    homComponent_apply_self]
  rfl

/-- The same generic identity with the original native rank-three
Chern cap, retaining the native final Fin index before specialization. -/
theorem degreeNine_chern_product_six_three (C : ChowSituation.{u}) {T : Scheme.{u}}
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (E : T.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (a : GradedCapFamily (chowGroup C q)) (α : chowGroup C q 9) :
    (a * homComponent 3 (chernFamily C q E 3)) 9 9 α =
      a 6 6 (chernCap C 3 q E 9 (Fin.last 3) α) := by
  have h := degreeNine_product_six_three a (chernFamily C q E 3) α
  have hc := congrArg (fun f => f α)
    (chernFamily_apply_of_le C q E 3 9 (by decide : 3 ≤ 3))
  exact h.trans (congrArg (a 6 6) hc)

/-- The same actual coefficient identity with the output grade explicitly zero. -/
theorem degreeNine_chern_product_six_three_zero (C : ChowSituation.{u}) {T : Scheme.{u}}
    (q : T ⟶ C.S) [LocallyOfFiniteType q] (E : T.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (a : GradedCapFamily (chowGroup C q)) (α : chowGroup C q 9) :
    capTo (a * homComponent 3 (chernFamily C q E 3))
      9 (by decide : (9:ℤ)-(9:ℕ)=0) α =
    capTo a 6 (by decide : (6:ℤ)-(6:ℕ)=0)
      (chernCap C 3 q E 9 (Fin.last 3) α) := by
  apply eq_of_heq
  exact (gradedDegreeCast_heq _ _).trans
    ((heq_of_eq (degreeNine_chern_product_six_three C q E a α)).trans
      (gradedDegreeCast_heq _ _).symm)

/-- Genuine proper naturality also commutes with an explicit output-grade transport. -/
theorem properPush_lineFamily_pow_capTo (C : ChowSituation.{u}) {T Y : Scheme.{u}}
    (qT : T ⟶ C.S) [LocallyOfFiniteType qT] (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (p : T ⟶ Y) [IsProper p] (hp : p ≫ qY = qT)
    (A : InvertibleLine Y) (L : InvertibleLine T)
    (e : L.1 ≅ (Scheme.Modules.pullback p).obj A.1)
    (n : ℕ) (k : ℤ) (i : ℕ) (m : ℤ) (hm : k-(i:ℤ)=m) (α : chowGroup C qT k) :
    ChowLineProperPush.properPush C qT qY p hp m
      (capTo (lineFamily C qT L ^ n) i hm α) =
    capTo (lineFamily C qY A ^ n) i hm
      (ChowLineProperPush.properPush C qT qY p hp k α) := by
  subst m
  simpa only [capTo_def,gradedDegreeCast_rfl] using
    ChowLineProperPush.properPush_lineFamily_pow_apply C qT qY p hp A L e n k i α

/-- Output-grade normalization can be done before any large native degree is substituted. -/
theorem degree_six_cast {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]
    (a : GradedCapFamily G) (α : G 6) (degree : G 0 → ℤ) :
    degree (capTo a 6 (by decide : (6:ℤ)-(6:ℕ)=0) α) = degree (a 6 6 α) := by
  rfl

variable (K : Type u) [Field K] [CharZero K]

local instance ambientQuotientFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientBundle K) :=
  (LagrangianGrassmannian.quotientBundle_rank K).isFiniteLocallyFree
local instance lagrangianQuotientFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientOnLG K).target :=
  (LagrangianPluckerQuotient.quotientOnLG_rank K).isFiniteLocallyFree
local instance determinantFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (determinantLine K) :=
  (LagrangianPluckerQuotient.determinantLine_rank K).isFiniteLocallyFree
local instance equationFinite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (equationBundle K) :=
  (LagrangianGrassmannian.equationBundle_rank K).isFiniteLocallyFree

/-- Actual ambient properness follows from the original native Plucker
closed immersion of the original Grassmannian. -/
instance ambient_projection_isProper : IsProper (grassmannianProjection K) :=
  isProper_of_isProjectiveMorphism _
    (AlgebraicGeometry.Grassmannian.isProjectiveMorphism_schemeOver 3 6 (Spec (.of K)))

/-- The original determinant line on the original Grassmannian. -/
def ambientDeterminantLine : InvertibleLine (grassmannian K) :=
  ⟨Scheme.Modules.exteriorPower (quotientBundle K) 3,
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry
      (grassmannian K).presheaf (grassmannian K).ringCatSheaf.2 _).1
      (Scheme.Modules.isInvertible_exteriorPower_self (quotientBundle K) 3)⟩

/-- The same actual ample determinant used in the numerical degree. -/
def actualDeterminantLine : InvertibleLine (space K) :=
  ⟨determinantLine K, LagrangianPluckerQuotient.determinantLine_invertible K⟩

/-- Actual exterior-power pullback identifies the original two determinants. -/
def determinantPullbackIso :
    (actualDeterminantLine K).1 ≅
      (Scheme.Modules.pullback (inclusion K)).obj (ambientDeterminantLine K).1 :=
  (LagrangianPullback.exteriorPullbackIso (inclusion K) (quotientBundle K) 3).symm

/-- Six original determinant caps followed by the original equation top cap. -/
def ambientNumerator :
    GradedCapFamily (chowGroup (fieldChowSituation K) (grassmannianProjection K)) :=
  lineFamily (fieldChowSituation K) (grassmannianProjection K)
      (ambientDeterminantLine K) ^ 6 *
    homComponent 3 (chernFamily (fieldChowSituation K) (grassmannianProjection K)
      (equationBundle K) 3)

/-- The literal original ambient numerator, with its proved zero output grade. -/
def ambientNumeratorClass :
    chowGroup (fieldChowSituation K) (grassmannianProjection K) 0 :=
  capTo (ambientNumerator K) 9 (by decide : (9:ℤ)-(9:ℕ)=0) (ambientFundamental K)

/-- The actual degree of the actual LG equals its actual ambient numerator degree. -/
theorem pluckerCapDegree_eq_ambientNumerator :
    pluckerCapDegree K =
      chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
        (grassmannianProjection K) (IsLocalRing.closedPoint K)
        (ambientNumeratorClass K) := by
  let C := fieldChowSituation K
  let L := actualDeterminantLine K
  let A := ambientDeterminantLine K
  have hPower := properPush_lineFamily_pow_capTo C
    (projection K) (grassmannianProjection K) (inclusion K) rfl A L
    (determinantPullbackIso K) 6 6 6 0 (by decide) (lagrangianOwnFundamental K)
  have hFund : ChowLineProperPush.properPush C (projection K)
      (grassmannianProjection K) (inclusion K) rfl 6 (lagrangianOwnFundamental K) =
      lagrangianFundamental K := inclusionChowPush_fundamental K
  rw [hFund, ← topChern_cap_ambient_eq_lagrangian K] at hPower
  have hNumerator := degreeNine_chern_product_six_three_zero C (grassmannianProjection K)
    (equationBundle K) (lineFamily C (grassmannianProjection K) A ^ 6)
    (ambientFundamental K)
  let degGr := chowDegree C (fieldChowSituation_dimensionFunction_eq_zero K)
    (grassmannianProjection K) (IsLocalRing.closedPoint K)
  have hLine : lineFamily C (projection K) L =
      LagrangianQuotientChernRelation.H K C (projection K) := rfl
  have hLinePower := congrArg
    (fun a : GradedCapFamily (chowGroup C (projection K)) =>
      capTo (a ^ 6) 6 (by decide : (6:ℤ)-(6:ℕ)=0) (lagrangianOwnFundamental K)) hLine
  have hPushH := (congrArg
    (ChowLineProperPush.properPush C (projection K) (grassmannianProjection K)
      (inclusion K) rfl 0) hLinePower).symm.trans hPower
  have hFirst := (pluckerCapDegree_eq_operationalDegree K).trans
    (degree_six_cast
      (LagrangianQuotientChernRelation.H K C (projection K) ^ 6)
      (lagrangianOwnFundamental K)
      (chowDegree C (fieldChowSituation_dimensionFunction_eq_zero K)
        (projection K) (IsLocalRing.closedPoint K))).symm
  have hDegree := chowDegree_properChowPushforward K (grassmannianProjection K)
    (projection K) (inclusion K) rfl
      (capTo (LagrangianQuotientChernRelation.H K C (projection K) ^ 6)
        6 (by decide : (6:ℤ)-(6:ℕ)=0) (lagrangianOwnFundamental K))
  exact hFirst.trans (hDegree.trans (congrArg degGr (hPushH.trans hNumerator.symm)))

end M9Native.LagrangianActualDegree
