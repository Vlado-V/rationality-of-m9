module

public import M9StacksIntegration.DirectC9PoincareFamily
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMapDegree

/-!
# Actual degrees of the normalized ninth-power family

Native finite-flat Hilbert degrees compute the actual positive divisors.
Every actual base line restricts to a line over the residue field, whose
Picard group vanishes. This proves degree eight for the normalized line
and degree seventeen through twenty-six for the actual partial lines.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 10000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.DirectC9FamilyDegree

open DirectC9PoincareFamily
open PoincareChern (lineClass lineClass_tensor lineClass_pullback)

/-- A genuine base line has degree zero on every actual fibre. -/
theorem relativeDegree_baseClass {Y T : Scheme.{u}} (π : Y ⟶ T) [IsProper π]
    (hdim : ∀ t : T, topologicalKrullDim (π.fiber t) ≤ 1)
    (t : T) (x : Stacks.Picard.ofScheme T) :
    relativeInvertibleDegreeHomAt π hdim t (Stacks.Picard.schemePullbackClass π x) = 0 := by
  rw [relativeInvertibleDegreeHomAt_apply,Stacks.Picard.schemePullbackClass_comp]
  have hc : π.fiberι t ≫ π = π.fiberToSpecResidueField t ≫ T.fromSpecResidueField t :=
    pullback.condition
  rw [hc,← Stacks.Picard.schemePullbackClass_comp,
    Stacks.Picard.eq_zero_of_isField (T.residueField t)
      (Stacks.Picard.schemePullbackClass (T.fromSpecResidueField t) x)]
  have h0 : Stacks.Picard.schemePullbackClass (π.fiberToSpecResidueField t)
      (0 : Stacks.Picard.ofScheme (Spec (T.residueField t))) = 0 :=
    (Stacks.Picard.schemePullbackClassHom (π.fiberToSpecResidueField t)).map_zero
  rw [h0]
  exact (invertibleCurveDegreeHom (T.residueField t) (π.fiberToSpecResidueField t)
    (hdim t)).map_zero

variable {S : Scheme.{u}} (C : Over S) [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

/-- The actual native fibre-product spelling of the family ambient scheme. -/
abbrev familySpace : Scheme.{u} := pullback C.hom (power C 9).hom

abbrev familyProjection : familySpace C ⟶ (power C 9).left :=
  pullback.snd C.hom (power C 9).hom

/-- A native Hilbert class with its actual ambient scheme pinned explicitly. -/
abbrev familyClass {d : ℕ} (D : Stacks.Hilbert.HilbertFamily C (power C 9) d) :
    Stacks.Picard.ofScheme (familySpace C) := D.picardClass

instance inverseNormalizationLine_isInvertible :
    Stacks.SheafOfModules.IsInvertible (power C 9).left.presheaf (power C 9).left.ringCatSheaf.2
      (inverseNormalizationLine C c₀) :=
  @DirectC9PoincareFamily.normalizationLine_isInvertible (familySpace C) (power C 9).left
    (fixedSection C c₀) (baseline C c₀) (baseline_isInvertible C c₀)

theorem baseline_class :
    @lineClass (familySpace C) (baseline C c₀) (baseline_isInvertible C c₀) =
      familyClass C (totalFamily C c₀) - familyClass C (constantFamily C c₀ 17) := by
  let L : (familySpace C).Modules := positiveLine C c₀
  let M : (familySpace C).Modules := fixedLine C c₀ 17
  letI hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L := positiveLine_isInvertible C c₀
  letI hM : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 M := fixedLine_isInvertible C c₀ 17
  letI hMd : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 (dualSheaf M) :=
    Stacks.SheafOfModules.Invertible.isInvertible_dualSheaf _ _ M
  have ht := @lineClass_tensor (familySpace C) L (dualSheaf M) hL hMd
  have hd := @DualLinePicard.lineClass_dual (familySpace C) M hM
  have hLc : @lineClass (familySpace C) L hL = familyClass C (totalFamily C c₀) := rfl
  have hMc : @lineClass (familySpace C) M hM =
      familyClass C (constantFamily C c₀ 17) := rfl
  exact ht.trans (congrArg₂ (fun a b : Stacks.Picard.ofScheme (familySpace C) => a + b)
    hLc (hd.trans (congrArg Neg.neg hMc)))

theorem partialLine_class (j : ℕ) (hj : j ≤ 9) :
    @lineClass (familySpace C) (partialLine C c₀ j hj) (partialLine_isInvertible C c₀ j hj) =
      Stacks.Picard.schemePullbackClass (familyProjection C)
        (@lineClass (power C 9).left (inverseNormalizationLine C c₀)
          (inverseNormalizationLine_isInvertible C c₀)) +
      familyClass C (partialFamily C c₀ j hj) := by
  let N : (power C 9).left.Modules := inverseNormalizationLine C c₀
  let P : (familySpace C).Modules := (Scheme.Modules.pullback (familyProjection C)).obj N
  let D : (familySpace C).Modules :=
    Stacks.Divisors.divisorSheaf (partialFamily C c₀ j hj).ideal
  letI hN : Stacks.SheafOfModules.IsInvertible (power C 9).left.presheaf
      (power C 9).left.ringCatSheaf.2 N := inverseNormalizationLine_isInvertible C c₀
  letI hP : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 P := inferInstance
  have hCartier : @Stacks.Divisors.IsEffectiveCartierDivisor (familySpace C)
      (partialFamily C c₀ j hj).ideal := partialFamily_isEffectiveCartier C c₀ j hj
  letI hD : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 D :=
    @Stacks.Divisors.isInvertible_invertibleSheaf_picard (familySpace C)
      (partialFamily C c₀ j hj).ideal hCartier
  have ht := @lineClass_tensor (familySpace C) P D hP hD
  have hp := @lineClass_pullback (familySpace C) (power C 9).left (familyProjection C) N hN
  have hDc : @lineClass (familySpace C) D hD =
      familyClass C (partialFamily C c₀ j hj) := rfl
  exact ht.trans (congrArg₂ (fun a b : Stacks.Picard.ofScheme (familySpace C) => a + b) hp hDc)

variable (hdim : ∀ t : (power C 9).left,
  topologicalKrullDim ((familyProjection C).fiber t) ≤ 1)

include hdim

/-- Native Hilbert degree, on the actual fixed ambient fibre product. -/
theorem familyClass_degree {d : ℕ} (D : Stacks.Hilbert.HilbertFamily C (power C 9) d)
    (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C) hdim t (familyClass C D) = d := by
  letI : IsProper ((Over.pullback (power C 9).hom).obj C).hom :=
    inferInstanceAs (IsProper (pullback.snd C.hom (power C 9).hom))
  exact Stacks.Hilbert.relativeInvertibleDegreeHomAt_abelClass D hdim t

theorem constantFamily_degree (q : ℕ) (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C) hdim t
      (familyClass C (constantFamily C c₀ q)) = q + 1 := by
  simpa only [Nat.cast_add,Nat.cast_one] using
    familyClass_degree C hdim (constantFamily C c₀ q) t

theorem partialFamily_degree (j : ℕ) (hj : j ≤ 9) (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C) hdim t
      (familyClass C (partialFamily C c₀ j hj)) = 17 + j := by
  simpa only [Nat.cast_add,Nat.cast_ofNat] using
    familyClass_degree C hdim (partialFamily C c₀ j hj) t

theorem baseline_degree (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C) hdim t
      (@lineClass (familySpace C) (baseline C c₀) (baseline_isInvertible C c₀)) = 8 := by
  rw [baseline_class,map_sub]
  change relativeInvertibleDegreeHomAt (familyProjection C) hdim t
    (familyClass C (partialFamily C c₀ 9 (by omega))) - _ = 8
  rw [partialFamily_degree,constantFamily_degree]
  norm_num

/-- The degree-eight conclusion is proved for the actual normalized line. -/
theorem degreeEightLine_degree (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C) hdim t
      (@lineClass (familySpace C) (degreeEightLine C c₀) (degreeEightLine_isInvertible C c₀)) = 8 := by
  change relativeInvertibleDegreeHomAt (familyProjection C) hdim t
    (lineClass (normalizedLine (familyProjection C) (fixedSection C c₀) (baseline C c₀))) = 8
  rw [normalizedLine_class,map_add,relativeDegree_baseClass,zero_add,baseline_degree]

theorem partialLine_degree (j : ℕ) (hj : j ≤ 9) (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C) hdim t
      (@lineClass (familySpace C) (partialLine C c₀ j hj) (partialLine_isInvertible C c₀ j hj)) = 17 + j := by
  rw [partialLine_class,map_add,relativeDegree_baseClass,zero_add,partialFamily_degree]

end M9Native.DirectC9FamilyDegree
