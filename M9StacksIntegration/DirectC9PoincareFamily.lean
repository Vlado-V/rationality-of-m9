module

public import M9StacksIntegration.CurvePowerGraphRestrictions
public import M9StacksIntegration.DualLinePicard
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition

/-!
# The actual normalized degree-eight family on the actual ninth curve power

The positive family is seventeen fixed points and nine actual coordinate
points. Subtracting the actual eighteen-fold fixed-point divisor gives
the degree-eight line family. Its restriction to the actual fixed section
is cancelled by the dual of that restriction, as an actual line module.
The ordinary direct-image bundles and their ranks are subsequent steps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DirectC9PoincareFamily

open PoincareChern (lineClass lineClass_tensor lineClass_pullback lineClass_divisor)

section Normalization

variable {Y T : Scheme.{u}} (π : Y ⟶ T) (σ : T ⟶ Y)
  (A : Y.Modules) [hA : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 A]

/-- The actual dual of the actual section restriction. -/
abbrev normalizationLine : T.Modules :=
  dualSheaf ((Scheme.Modules.pullback σ).obj A)

instance normalizationLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      (normalizationLine σ A) :=
  Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf _ _ _

/-- Cancellation of the section restriction uses a genuine base line. -/
abbrev normalizedLine : Y.Modules :=
  Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback π).obj (normalizationLine σ A)) A

instance normalizedLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (normalizedLine π σ A) := PoincareChern.lineTensor_isInvertible _ _

theorem normalizationLine_class :
    lineClass (normalizationLine σ A) =
      -Stacks.Picard.schemePullbackClass σ (lineClass A) := by
  dsimp only [normalizationLine]
  rw [DualLinePicard.lineClass_dual, lineClass_pullback]

theorem normalizedLine_class :
    lineClass (normalizedLine π σ A) =
      Stacks.Picard.schemePullbackClass π
        (-Stacks.Picard.schemePullbackClass σ (lineClass A)) + lineClass A := by
  dsimp only [normalizedLine]
  rw [lineClass_tensor, lineClass_pullback, normalizationLine_class]

/-- The genuine normalized family is actually trivial on the section. -/
theorem normalizedLine_sectionClass (hσ : σ ≫ π = 𝟙 T) :
    lineClass ((Scheme.Modules.pullback σ).obj (normalizedLine π σ A)) = 0 := by
  rw [lineClass_pullback, normalizedLine_class, Stacks.Picard.schemePullbackClass_add,
    Stacks.Picard.schemePullbackClass_comp, hσ, Stacks.Picard.schemePullbackClass_id,
    neg_add_cancel]

/-- Equality of the proved native Picard classes supplies an actual
isomorphism with the actual unit module, without a chosen triviality premise. -/
theorem nonempty_normalizedLine_sectionIso (hσ : σ ≫ π = 𝟙 T) :
    Nonempty ((Scheme.Modules.pullback σ).obj (normalizedLine π σ A) ≅
      (show T.Modules from SheafOfModules.unit T.ringCatSheaf)) := by
  letI : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2
      (SheafOfModules.unit T.ringCatSheaf) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _
      (SheafOfModules.isInvertible_unit T.presheaf T.ringCatSheaf.2)
  apply (Stacks.SheafOfModules.picardClass_eq_iff T.presheaf T.ringCatSheaf.2
    _ _ inferInstance inferInstance).1
  exact (normalizedLine_sectionClass π σ A hσ).trans
    (Stacks.SheafOfModules.picardClass_zero T.presheaf T.ringCatIsSheaf).symm

end Normalization

variable {S : Scheme.{u}} (C : Over S) [IsSeparated C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

local notation "T" => power C 9
local notation "Y" => power C 10

/-- The actual constant relative point on the actual ninth power. -/
abbrev constantPoint : T ⟶ C := toUnit T ≫ c₀

/-- Its actual graph, the section used for normalization. -/
abbrev fixedSection : (T).left ⟶ (Y).left :=
  CurvePowerGraphCartier.graphSection C 9 (constantPoint C c₀)

/-- The actual original-family projection. -/
abbrev projection : (Y).left ⟶ (T).left := (snd C T).left

@[simp] theorem fixedSection_projection :
    fixedSection C c₀ ≫ projection C = 𝟙 (T).left :=
  CurvePowerGraphCartier.graphSection_comp_second C 9 (constantPoint C c₀)

/-- A positive number of copies of the actual fixed-point graph,
with its genuine finite-flat Hilbert-family structure. -/
def constantFamily : (q : ℕ) → Stacks.Hilbert.HilbertFamily C T (q + 1)
  | 0 => GraphNormalPicard.graphFamily C T (constantPoint C c₀)
  | q + 1 => Stacks.Hilbert.familyAddPoint C T (constantFamily q)
      (constantPoint C c₀)
      (Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C T _)

/-- The genuine family `17[c₀]+Γ₀+⋯+Γ_(j−1)`. -/
def partialFamily : (j : ℕ) → j ≤ 9 → Stacks.Hilbert.HilbertFamily C T (17 + j)
  | 0, _ => constantFamily C c₀ 16
  | j + 1, hj => Stacks.Hilbert.familyAddPoint C T (partialFamily j (by omega))
      (coord C 9 ⟨j, by omega⟩)
      (Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C T _)

instance constantFamily_isEffectiveCartier (q : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor (constantFamily C c₀ q).ideal :=
  (constantFamily C c₀ q).isEffectiveCartierDivisor_ideal

instance partialFamily_isEffectiveCartier (j : ℕ) (hj : j ≤ 9) :
    Stacks.Divisors.IsEffectiveCartierDivisor (partialFamily C c₀ j hj).ideal :=
  (partialFamily C c₀ j hj).isEffectiveCartierDivisor_ideal

/-- Adding each moving point is literal multiplication of actual ideals. -/
theorem partialFamily_successor_ideal (j : ℕ) (hj : j + 1 ≤ 9) :
    (partialFamily C c₀ (j + 1) hj).ideal =
      (partialFamily C c₀ j (by omega)).ideal *
        Stacks.Hilbert.pointIdeal C T (coord C 9 ⟨j, by omega⟩) := rfl

theorem constantFamily_successor_ideal (q : ℕ) :
    (constantFamily C c₀ (q + 1)).ideal = (constantFamily C c₀ q).ideal *
      Stacks.Hilbert.pointIdeal C T (constantPoint C c₀) := rfl

/-- The literal degree-twenty-six Hilbert family. -/
abbrev totalFamily : Stacks.Hilbert.HilbertFamily C T 26 :=
  partialFamily C c₀ 9 (by omega)

/-- The actual positive line of the fixed-point family. -/
abbrev fixedLine (q : ℕ) : (Y).left.Modules :=
  Stacks.Divisors.divisorSheaf (constantFamily C c₀ q).ideal

instance fixedLine_isInvertible (q : ℕ) :
    Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (fixedLine C c₀ q) :=
  @Stacks.Divisors.isInvertible_invertibleSheaf_picard (Y).left
    (constantFamily C c₀ q).ideal (constantFamily_isEffectiveCartier C c₀ q)

abbrev positiveLine : (Y).left.Modules :=
  Stacks.Divisors.divisorSheaf (totalFamily C c₀).ideal

instance positiveLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (positiveLine C c₀) :=
  @Stacks.Divisors.isInvertible_invertibleSheaf_picard (Y).left
    (totalFamily C c₀).ideal (partialFamily_isEffectiveCartier C c₀ 9 (by omega))

/-- The actual line `O(ΣΓᵢ+17c₀) ⊗ O(18c₀)∨`, before normalization. -/
abbrev baseline : (Y).left.Modules :=
  Scheme.Modules.tensorObj (positiveLine C c₀) (dualSheaf (fixedLine C c₀ 17))

instance baseline_isInvertible :
    Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (baseline C c₀) := by
  letI : Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (dualSheaf (fixedLine C c₀ 17)) :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf _ _ _
  exact PoincareChern.lineTensor_isInvertible _ _

/-- The actual inverse normalization line, retained for the filtration. -/
abbrev inverseNormalizationLine : (T).left.Modules :=
  normalizationLine (fixedSection C c₀) (baseline C c₀)

/-- The actual normalized family on the original curve times `C⁹`. -/
abbrev degreeEightLine : (Y).left.Modules :=
  normalizedLine (projection C) (fixedSection C c₀) (baseline C c₀)

instance degreeEightLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (degreeEightLine C c₀) := normalizedLine_isInvertible _ _ _

/-- The section normalization is proved for the actual constructed line. -/
theorem nonempty_degreeEightLine_sectionIso :
    Nonempty ((Scheme.Modules.pullback (fixedSection C c₀)).obj (degreeEightLine C c₀) ≅
      (show (T).left.Modules from SheafOfModules.unit (T).left.ringCatSheaf)) :=
  nonempty_normalizedLine_sectionIso (projection C) (fixedSection C c₀)
    (baseline C c₀) (fixedSection_projection C c₀)

/-- The actual partial lines for the nine ordinary moving-graph rows. -/
abbrev partialLine (j : ℕ) (hj : j ≤ 9) : (Y).left.Modules :=
  Scheme.Modules.tensorObj
    ((Scheme.Modules.pullback (projection C)).obj (inverseNormalizationLine C c₀))
    (Stacks.Divisors.divisorSheaf (partialFamily C c₀ j hj).ideal)

instance partialLine_isInvertible (j : ℕ) (hj : j ≤ 9) :
    Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (partialLine C c₀ j hj) := by
  letI : Stacks.SheafOfModules.IsInvertible (Y).left.presheaf (Y).left.ringCatSheaf.2
      (Stacks.Divisors.divisorSheaf (partialFamily C c₀ j hj).ideal) :=
    @Stacks.Divisors.isInvertible_invertibleSheaf_picard (Y).left
      (partialFamily C c₀ j hj).ideal (partialFamily_isEffectiveCartier C c₀ j hj)
  exact PoincareChern.lineTensor_isInvertible _ _

/-- These are the actual ordinary direct images, before any rank assertion. -/
abbrev partialPushforward (j : ℕ) (hj : j ≤ 9) : (T).left.Modules :=
  (Scheme.Modules.pushforward (projection C)).obj (partialLine C c₀ j hj)

end M9Native.DirectC9PoincareFamily
