module

public import M9StacksIntegration.CurveGenericResidueSeparable
public import M9StacksIntegration.MukaiShortExactFiberRank
public import M9StacksIntegration.SmoothDifferentialsRankThin
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Triangle
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The original generic differential of a finite map from a smooth curve

The original finite scheme morphism gives its actual finite residue-field
extension. Characteristic zero proves separability. At the integral
source's generic point its local ring is a field, so the maximal-ideal
criterion proves formal unramifiedness of the actual stalk map. The
native stalk Kähler isomorphism and exact cotangent triangle then show
that the original relative differential is surjective on its actual
generic residue fibre. For a smooth curve the target has rank one.

The target scheme need not be a curve or the image of a normalization.
No nonzero differential, generic rank, or separability premise is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeDifferentialStalkMap
open scoped TensorProduct

universe u

namespace M9Native.CurveGenericDifferentialRank

theorem residueFieldAlgebra_eq {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X) :
    letI := (g.stalkMap x).hom.toAlgebra
    haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (g x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (g.stalkMap x).hom)
    (g.residueFieldMap x).hom.toAlgebra =
      (inferInstance : Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (g x)))
        (IsLocalRing.ResidueField (X.presheaf.stalk x))) := by
  apply Algebra.algebra_ext
  intro a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  rfl

theorem isSeparable_residueField_of_isFinite_charZero
    {X Y : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) [IsFinite g] (x : X) :
    letI := (g.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (g x)) (X.residueField x) := by
  letI := (g.residueFieldMap x).hom.toAlgebra
  have := CurveGenericResidueSeparable.residueField_charZero pY (g x)
  have := CurveGenericResidueSeparable.finite_residueField_of_isFinite g x
  infer_instance

section IntegralSource

variable {X Y : Scheme.{u}} [IsIntegral X]
    (k : Type u) [Field k] [CharZero k] (pY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) [IsFinite g]

include k pY

theorem formallyUnramified_stalkMap_generic_of_isFinite :
    (g.stalkMap (genericPoint X)).hom.FormallyUnramified := by
  let η := genericPoint X
  algebraize [(g.stalkMap η).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (g η)) (X.presheaf.stalk η)) :=
    inferInstanceAs (IsLocalHom (g.stalkMap η).hom)
  have : Algebra.EssFiniteType (Y.presheaf.stalk (g η)) (X.presheaf.stalk η) :=
    RingHom.essFiniteType_algebraMap.mpr (LocallyOfFiniteType.stalkMap g η)
  letI : Field (X.presheaf.stalk η) := inferInstanceAs (Field X.functionField)
  have : Algebra.IsSeparable (IsLocalRing.ResidueField (Y.presheaf.stalk (g η)))
      (IsLocalRing.ResidueField (X.presheaf.stalk η)) := by
    convert! isSeparable_residueField_of_isFinite_charZero k pY g η
    exact (residueFieldAlgebra_eq g η).symm
  have hmax : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g η))).map
      (algebraMap (Y.presheaf.stalk (g η)) (X.presheaf.stalk η)) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk η) := by
    apply le_antisymm (IsLocalRing.map_maximalIdeal_le _)
    rw [IsLocalRing.maximalIdeal_eq_bot]
    exact bot_le
  rw [← RingHom.algebraMap_toAlgebra (g.stalkMap η).hom,
    RingHom.formallyUnramified_algebraMap]
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hmax

theorem subsingleton_relativeDifferentials_generic_of_isFinite :
    Subsingleton ((Scheme.Hom.relativeDifferentials g).presheaf.stalk (genericPoint X)) := by
  classical
  let η := genericPoint X
  letI : Algebra (Y.presheaf.stalk (g η)) (X.presheaf.stalk η) := algebraStalkMap g η
  have hformal : Algebra.FormallyUnramified
      (Y.presheaf.stalk (g η)) (X.presheaf.stalk η) :=
    RingHom.formallyUnramified_algebraMap.mpr
      (formallyUnramified_stalkMap_generic_of_isFinite k pY g)
  have hK : Subsingleton (KaehlerDifferential
      (Y.presheaf.stalk (g η)) (X.presheaf.stalk η)) :=
    (Algebra.formallyUnramified_iff _ _).mp hformal
  exact (Equiv.subsingleton_congr (relativeDifferentialsStalkKaehlerEquiv g η).toEquiv).mpr hK

theorem differential_generic_fiber_surjective_of_isFinite :
    Function.Surjective (MukaiSemiIrreducible.fiberMap
      (Scheme.Hom.relativeDifferentialsMap g pY (g ≫ pY) (𝟙 _)
        (Category.comp_id (g ≫ pY)).symm) (genericPoint X)) := by
  let η := genericPoint X
  letI := TupleEvaluationFiber.residueAlgebra η
  have := subsingleton_relativeDifferentials_generic_of_isFinite k pY g
  obtain ⟨hzero, hexact⟩ := Scheme.Hom.toRelativeDifferentials_exact g pY
  have : Epi (g.toRelativeDifferentials pY) := Scheme.Hom.toRelativeDifferentials_epi g pY
  have he := MukaiShortExactFiberRank.fiberMap_exact (ShortComplex.mk _ _ hzero) hexact η
  change Function.Surjective (TupleEvaluationFiber.inducedFiberMap
    (Scheme.Hom.relativeDifferentialsMap g pY (g ≫ pY) (𝟙 _)
      (Category.comp_id (g ≫ pY)).symm) η)
  apply LinearMap.range_eq_top.mp
  rw [← he.linearMap_ker_eq]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

end IntegralSource

variable {X Y : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
    (pY : Y ⟶ Spec (.of k)) (g : X ⟶ Y) [IsFinite g]

theorem relativeDifferentialsMap_rank_one_of_isFinite
    (pX : X ⟶ Spec (.of k)) [IsCurve k pX] [Smooth pX]
    (hg : g ≫ pY = pX) :
    MukaiSemiIrreducible.mapRankAt
      (Scheme.Hom.relativeDifferentialsMap g pY pX (𝟙 _) (by simpa using hg))
      (genericPoint X) = 1 := by
  subst pX
  let η := genericPoint X
  letI := TupleEvaluationFiber.residueAlgebra η
  have := smoothOfRelativeDimension_one_of_isCurve k (g ≫ pY)
  have := SmoothDifferentialsRankThin.relativeDifferentials_rank (g ≫ pY) 1
  change Module.finrank (X.residueField η) (LinearMap.range
    (TupleEvaluationFiber.inducedFiberMap
      (Scheme.Hom.relativeDifferentialsMap g pY (g ≫ pY) (𝟙 _) _) η)) = 1
  have hs : Function.Surjective (TupleEvaluationFiber.inducedFiberMap
      (Scheme.Hom.relativeDifferentialsMap g pY (g ≫ pY) (𝟙 _)
        (Category.comp_id (g ≫ pY)).symm) η) :=
    differential_generic_fiber_surjective_of_isFinite k pY g
  rw [LinearMap.range_eq_top.mpr hs, finrank_top]
  exact TupleEvaluationFiber.finrank_fiber (Scheme.Hom.relativeDifferentials (g ≫ pY)) 1 η

end M9Native.CurveGenericDifferentialRank
