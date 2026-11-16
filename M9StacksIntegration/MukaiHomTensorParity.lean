module

public import M9StacksIntegration.MukaiHomWedgePairing
public import M9StacksIntegration.MukaiCohomologyYonedaBoundary
public import M9StacksIntegration.MukaiEulerEven

/-!
# Actual normalized tensor parity via native Hom--Serre duality

The actual Yoneda boundary is paired by the constructed wedge morphism
and genuine native Hom duality. Every H0 class is its actual section image,
so the original wedge postcomposition proves its zero diagonal. Actual
exactness and native Euler parity then prove even H0 of the middle bundle.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace M9Native.MukaiHomTensorParity

open M9Native.MukaiCupAlternating M9Native.MukaiHomCoefficient
open M9Native.MukaiTensorSection M9Native.MukaiTensorDiagonal M9Native.MukaiTensorSequence
open M9Native.MukaiHomWedgePairing M9Native.MukaiCohomologyYonedaBoundary
open M9Native.UnitExtCohomologyAllDegrees
open M9Native.InvertibleExtCancellation (unit)

variable {X : Scheme.{u}}

local instance nativeHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f]

/-- The actual original Yoneda boundary with its actual tensor source
and coefficient typed explicitly, rather than hidden as complex projections. -/
def tensorExtensionBoundary (C : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFree.{u,u,u} C) {N B : X.Modules}
    (i : N ⟶ B) (q : B ⟶ unit X) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact) :
    letI := modulesLinearOverField k f
    cohomologyOverField k f (tensorQuotient C) 0 →ₗ[k]
      Ext.{u} (unit X) (tensor N C) 1 := by
  letI := modulesLinearOverField k f
  let S : ShortComplex X.Modules := ShortComplex.mk i q w
  let hT : (tensorSequence C S).ShortExact := tensorSequence_shortExact C hC hS
  exact extBoundaryFromH0 k f (S := tensorSequence C S) hT

/-- The actual native Hom--Serre pairing has zero diagonal on the actual
Yoneda boundary for every H0 class; alternation is proved geometrically. -/
theorem tensorExtension_diagonal_zero (C N B : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (i : N ⟶ B) (q : B ⟶ unit X) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact)
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f)
    (x : cohomologyOverField k f (tensorQuotient C) 0) :
    letI := modulesLinearOverField k f
    homWedgeExtPairing k f C N hC d x
      (tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS x) = 0 := by
  let := modulesLinearOverField k f
  let := tensorRight_additive C
  let : PreservesFiniteLimits (tensorRight C) := (tensorRight_exact C hC.isFiniteLocallyFree).1
  let : PreservesFiniteColimits (tensorRight C) := (tensorRight_exact C hC.isFiniteLocallyFree).2
  let hT := tensorSequence_shortExact C hC.isFiniteLocallyFree hS
  let e₀ := unitHomCohomologyLinearEquivZero k f (tensorQuotient C)
  let r : unit X ⟶ tensorQuotient C := e₀.symm x
  let s : unit X ⟶ C := r ≫ (unitLeftIso C).hom
  have hs : (tensorSection C s).app (unit X) = r := section_eq_tensorSection C r
  have hx : unitHomCohomologyLinearEquivZero k f (tensorQuotient C) r = x :=
    e₀.apply_symm_apply x
  have hy : tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS x =
      sectionExtensionClass C hC.isFiniteLocallyFree hS.extClass s := by
    have h := extBoundaryFromH0_unitHom k f
      (S := tensorSequence C (ShortComplex.mk i q w)) hT r
    change tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS
      (unitHomCohomologyLinearEquivZero k f (tensorQuotient C) r) =
        (Ext.mk₀ r).comp hT.extClass (zero_add 1) at h
    rw [hx] at h
    have hclass : hS.extClass.mapExactFunctor (tensorRight C) = hT.extClass :=
      Ext.mapExactFunctor_extClass (tensorRight C) hS
    change tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS x =
      (Ext.mk₀ ((tensorSection C s).app (unit X))).comp
        (hS.extClass.mapExactFunctor (tensorRight C)) (zero_add 1)
    rw [hs, hclass]
    exact h
  have h := homWedgeExtPairing_section_diagonal_zero k f C N hC d hS.extClass r
  rw [hx, ← hy] at h
  exact h

/-- The actual normalized connecting map has even rank, with no
alternation, perfectness, cohomology dimension, or boundary-comparison premise. -/
theorem even_tensorExtension_boundary_rank [CharZero k] (C N B : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (i : N ⟶ B) (q : B ⟶ unit X) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact)
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f) :
    letI := modulesLinearOverField k f
    Even (Module.finrank k (LinearMap.range
      (tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS))) := by
  let := modulesLinearOverField k f
  let : Module.Finite k (cohomologyOverField k f (tensorQuotient C) 0) :=
    M9Native.MukaiCurvePairingGeometry.tensorQuotient_cohomology_finite k f C 2 hC 0
  let δ : cohomologyOverField k f (tensorQuotient C) 0 →ₗ[k]
      Ext.{u} (unit X) (tensor N C) 1 :=
    tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS
  have hAlt : ∀ x, homWedgeExtPairing k f C N hC d x (δ x) = 0 :=
    tensorExtension_diagonal_zero k f C N B hC i q w hS d
  exact M9Native.MukaiParityLinear.even_finrank_range_of_alternating_pairing
    (homWedgeExtPairing k f C N hC d) (homWedgeExtPairing_isPerfPair k f C N hC d)
    δ hAlt

/-- Original even degree and the actual line-extension determinant
prove genuine even H0 of the actual tensor middle bundle. -/
theorem even_H0_tensorExtension [CharZero k] (C N B : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (i : N ⟶ B) (q : B ⟶ unit X) (w : i ≫ q = 0)
    (hS : (ShortComplex.mk i q w).ShortExact)
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hdeg : letI := hC
      Even (curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le C 2)) :
    Even (Module.finrank k (cohomologyOverField k f (tensor B C) 0)) := by
  let := modulesLinearOverField k f
  let := hC
  let := extensionMiddle_rank i q w hS
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor B C) 4 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X B C 2 2
  let : (tensor B C).IsCoherent :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f (tensor B C) 4
  let : Module.Finite k (cohomologyOverField k f (tensor B C) 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f (tensor B C) 0
  let : Module.Finite k (cohomologyOverField k f (tensorQuotient C) 0) :=
    M9Native.MukaiCurvePairingGeometry.tensorQuotient_cohomology_finite k f C 2 hC 0
  let hT := tensorSequence_shortExact C hC.isFiniteLocallyFree hS
  let a : cohomologyOverField k f (tensor N C) 0 →ₗ[k]
      cohomologyOverField k f (tensor B C) 0 :=
    (cohomologyOverFieldMap k f (tensorSequence C (ShortComplex.mk i q w)).f 0).hom
  let b : cohomologyOverField k f (tensor B C) 0 →ₗ[k]
      cohomologyOverField k f (tensorQuotient C) 0 :=
    (cohomologyOverFieldMap k f (tensorSequence C (ShortComplex.mk i q w)).g 0).hom
  let δ : cohomologyOverField k f (tensorQuotient C) 0 →ₗ[k]
      Ext.{u} (unit X) (tensor N C) 1 :=
    tensorExtensionBoundary k f C hC.isFiniteLocallyFree i q w hS
  have ha : Function.Injective a :=
    M9Native.MukaiCohomologyParity.cohomologyBoundary_injective_left k f hT
  have hab : Function.Exact a b :=
    M9Native.MukaiCohomologyParity.cohomologyBoundary_exact_left k f hT 0
  have hbδ : Function.Exact b δ := extBoundaryFromH0_exact_middle k f
    (S := tensorSequence C (ShortComplex.mk i q w)) hT
  have hAlt : ∀ x, homWedgeExtPairing k f C N hC d x (δ x) = 0 :=
    tensorExtension_diagonal_zero k f C N B hC i q w hS d
  have hdiff := M9Native.MukaiParityLinear.even_dimension_difference_of_exact_alternating
    a b δ ha hab hbδ
    (homWedgeExtPairing k f C N hC d) (homWedgeExtPairing_isPerfPair k f C N hC d)
    hAlt
  rw [(unitExtCohomologyLinearEquivAll k f (tensor N C) 1).finrank_eq] at hdiff
  have heuler : Even ((Module.finrank k (cohomologyOverField k f (tensor N C) 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k f (tensor N C) 1) : ℤ)) := by
    rw [finrank_cohomologyOverField_eq_of_iso k f
        (M9Native.MukaiHomAdjunction.tensorSwap N C) 0,
      finrank_cohomologyOverField_eq_of_iso k f
        (M9Native.MukaiHomAdjunction.tensorSwap N C) 1]
    exact M9Native.MukaiEulerEven.even_H0_sub_H1_tensor_line k f C hC N hdeg
  obtain ⟨a,ha⟩ := hdiff
  obtain ⟨b,hb⟩ := heuler
  refine ⟨Module.finrank k (cohomologyOverField k f (tensor B C) 0) / 2, ?_⟩
  omega

end M9Native.MukaiHomTensorParity
