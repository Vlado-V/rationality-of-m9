module

public import M9StacksIntegration.MukaiSectionWedge
public import M9StacksIntegration.MukaiTensorSequence
public import M9StacksIntegration.MukaiHomSerreTrace
public import M9StacksIntegration.MukaiCurvePairingGeometry
public import M9StacksIntegration.MukaiEulerEven

/-!
# Actual Mukai pairing from native Hom--Serre duality

The genuine line coefficient, original rank-two wedge duality, and fully
faithful tensoring give a linear equivalence from the actual quotient H0
to Hom of the actual coefficient bundle into the dualizing sheaf. Native
Hom--Serre duality then gives a perfect pairing with original unit Ext.
Its actual section diagonal is zero by the checked Yoneda wedge identity.
General Ext duality and independently normalized cup comparisons are unused.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace M9Native.MukaiHomWedgePairing

open M9Native.MukaiCupAlternating M9Native.MukaiHomCoefficient
open M9Native.MukaiSectionWedge M9Native.MukaiTensorDiagonal
open M9Native.MukaiTensorSequence M9Native.MukaiHomSerreTrace
open M9Native.UnitExtCohomologyAllDegrees
open M9Native.InvertibleExtCancellation (unit)

variable {X : Scheme.{u}}

local instance nativeHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

/-- The genuine quotient of the actual tensorized normalized sequence. -/
abbrev tensorQuotient (C : X.Modules) : X.Modules :=
  (tensorRight C).obj (unit X)

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))
    [IsCurve k f] [IsProper f]

include k f in
omit [IsProper f] in
/-- The actual coefficient bundle is coherent, from its original rank
two and its actual line coefficient. -/
theorem tensorCoefficient_coherent (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] :
    (tensor N C).IsCoherent := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor C N) 2 :=
    M9Native.MukaiEulerEven.rankTwoTensorLine_rank C hC N
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor N C) 2 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      (M9Native.MukaiHomAdjunction.tensorSwap C N) inferInstance
  exact SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f (tensor N C) 2

/-- Every actual cohomology group of that genuine coefficient is finite. -/
theorem tensorCoefficient_cohomology_finite (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N] (n : ℕ) :
    Module.Finite k (cohomologyOverField k f (tensor N C) n) := by
  let : (tensor N C).IsCoherent := tensorCoefficient_coherent k f C N hC
  exact finiteDimensional_cohomologyOverField_of_isProper k f (tensor N C) n

/-- The actual quotient H0 is the actual Hom into the genuine dualizing
sheaf, with no supplied self-duality or dimension comparison. -/
def sectionCoefficientLinearEquiv (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f) :
    letI := modulesLinearOverField k f
    cohomologyOverField k f (tensorQuotient C) 0 ≃ₗ[k]
      (tensor N C ⟶ Stacks.Duality.dualizingSheafOverField f) := by
  letI := modulesLinearOverField k f
  exact (unitHomCohomologyLinearEquivZero k f (tensorQuotient C)).symm.trans
    ((Linear.homCongr k (Iso.refl (unit X))
      (unitLeftIso C)).trans
        (twistedSectionWedgeHomLinearEquiv k f C N
          (Stacks.Duality.dualizingSheafOverField f) hC d))

omit [IsCurve k f] in
/-- The actual H0 image of a genuine section has precisely its original
tensor-wedge coefficient morphism. -/
theorem sectionCoefficientLinearEquiv_unitHom (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f)
    (r : unit X ⟶ tensorQuotient C) :
    letI := modulesLinearOverField k f
    sectionCoefficientLinearEquiv k f C N hC d
      (unitHomCohomologyLinearEquivZero k f (tensorQuotient C) r) =
        tensorWedgeMap C (r ≫ (unitLeftIso C).hom) N ≫ d.hom := by
  let := modulesLinearOverField k f
  change twistedSectionWedgeHomLinearEquiv k f C N
      (Stacks.Duality.dualizingSheafOverField f) hC d
      ((Linear.homCongr k (Iso.refl (unit X))
        (unitLeftIso C))
          ((unitHomCohomologyLinearEquivZero k f (tensorQuotient C)).symm
            (unitHomCohomologyLinearEquivZero k f (tensorQuotient C) r))) = _
  rw [LinearEquiv.symm_apply_apply, Linear.homCongr_apply]
  exact (congrArg
    (twistedSectionWedgeHomLinearEquiv k f C N
      (Stacks.Duality.dualizingSheafOverField f) hC d)
    (congrArg (fun g => g ≫ (unitLeftIso C).hom) (Category.id_comp r))).trans
      (twistedSectionWedgeHomLinearEquiv_apply k f C N
        (Stacks.Duality.dualizingSheafOverField f) hC d (r ≫ (unitLeftIso C).hom))

/-- The actual native Hom--Serre pairing, pulled back along the original
all-degree linear unit-Ext comparison. -/
def homWedgeExtPairing (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f) :
    letI := modulesLinearOverField k f
    cohomologyOverField k f (tensorQuotient C) 0 →ₗ[k]
      Ext.{u} (unit X) (tensor N C) 1 →ₗ[k] k := by
  letI := modulesLinearOverField k f
  letI : (tensor N C).IsCoherent := tensorCoefficient_coherent k f C N hC
  let e := (sectionCoefficientLinearEquiv k f C N hC d).trans
    (Stacks.Duality.homDualizingSheafLinearEquiv f
      (IsCurve.topologicalKrullDim_eq_one f).le (tensor N C) (isQuasicoherent_of_isCoherent _))
  exact e.toLinearMap.compl₁₂ LinearMap.id
    (unitExtCohomologyLinearEquivAll k f (tensor N C) 1).toLinearMap

/-- Perfectness is derived from actual native Hom duality and actual
finite cohomology of the genuine coefficient bundle. -/
theorem homWedgeExtPairing_isPerfPair (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f) :
    letI := modulesLinearOverField k f
    (homWedgeExtPairing k f C N hC d).IsPerfPair := by
  let := modulesLinearOverField k f
  let : (tensor N C).IsCoherent := tensorCoefficient_coherent k f C N hC
  let : Module.Finite k (cohomologyOverField k f (tensor N C) 1) :=
    tensorCoefficient_cohomology_finite k f C N hC 1
  let e := (sectionCoefficientLinearEquiv k f C N hC d).trans
    (Stacks.Duality.homDualizingSheafLinearEquiv f
      (IsCurve.topologicalKrullDim_eq_one f).le (tensor N C) (isQuasicoherent_of_isCoherent _))
  let : e.toLinearMap.IsPerfPair := LinearMap.IsPerfPair.of_bijective e.toLinearMap e.bijective
  exact LinearMap.IsPerfPair.compl₁₂ e.toLinearMap (LinearEquiv.refl k _)
    (unitExtCohomologyLinearEquivAll k f (tensor N C) 1)

/-- The actual section diagonal vanishes by original wedge Yoneda
postcomposition and the proved native Hom--Serre trace formula. -/
theorem homWedgeExtPairing_section_diagonal_zero (C N : X.Modules)
    (hC : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} C 2)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (d : tensor N (exteriorSquare C) ≅ Stacks.Duality.dualizingSheafOverField f)
    (ξ : Ext.{u} (unit X) N 1)
    (r : unit X ⟶ tensorQuotient C) :
    letI := modulesLinearOverField k f
    homWedgeExtPairing k f C N hC d
      (unitHomCohomologyLinearEquivZero k f (tensorQuotient C) r)
      (sectionExtensionClass C hC.isFiniteLocallyFree ξ (r ≫ (unitLeftIso C).hom)) = 0 := by
  let := modulesLinearOverField k f
  let : (tensor N C).IsCoherent := tensorCoefficient_coherent k f C N hC
  let s := r ≫ (unitLeftIso C).hom
  let e := sectionExtensionClass C hC.isFiniteLocallyFree ξ s
  change Stacks.Duality.homDualizingSheafLinearEquiv f
    (IsCurve.topologicalKrullDim_eq_one f).le (tensor N C) (isQuasicoherent_of_isCoherent _)
    (sectionCoefficientLinearEquiv k f C N hC d
      (unitHomCohomologyLinearEquivZero k f (tensorQuotient C) r))
    (unitExtCohomologyLinearEquivAll k f (tensor N C) 1 e) = 0
  rw [sectionCoefficientLinearEquiv_unitHom]
  apply homSerre_unitExt_eq_zero_of_postcomp_zero
  have hz : e.comp (Ext.mk₀ (tensorWedgeMap C s N)) (add_zero 1) = 0 :=
    sectionExtensionClass_wedge_zero C hC.isFiniteLocallyFree ξ s
  rw [← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc _ _ _ (add_zero 1) (zero_add 0) (add_zero 1), hz, Ext.zero_comp]

end M9Native.MukaiHomWedgePairing
