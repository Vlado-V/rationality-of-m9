module

public import M9StacksIntegration.MukaiYonedaExact
public import M9StacksIntegration.MukaiCohomologyParity
public import M9StacksIntegration.UnitExtCohomologyAllDegrees

/-!
# The actual Yoneda boundary on the original H0 and H1 spaces

The native all-degree linear comparison transports the actual Yoneda
boundary. Its exactness follows from the actual Ext long exact sequence
and proved coefficient naturality. Its rank agrees with the previously
chosen cohomology boundary through their actual kernels; no equality of
independently normalized boundary comparisons is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace M9Native.MukaiCohomologyYonedaBoundary

open M9Native.InvertibleExtCancellation
open M9Native.UnitExtCohomologyAllDegrees

variable {X : Scheme.{u}}

local instance nativeHasExt : HasExt.{u} X.Modules :=
  hasExt_of_enoughInjectives X.Modules

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The actual Yoneda boundary on original H0, with its original small
Ext target and the exact original categorical scalar action. -/
def extBoundaryFromH0 {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    letI := modulesLinearOverField k f
    cohomologyOverField k f S.X₃ 0 →ₗ[k] Ext.{u} (unit X) S.X₁ 1 := by
  letI := modulesLinearOverField k f
  exact (M9Native.MukaiYonedaExact.boundary k (unit X) hS).comp
    (unitExtCohomologyLinearEquivAll k f S.X₃ 0).symm.toLinearMap

/-- In particular, the actual section has its original actual Yoneda
pullback class, without identifying a chosen boundary with a canonical one. -/
theorem extBoundaryFromH0_unitHom {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (s : unit X ⟶ S.X₃) :
    letI := modulesLinearOverField k f
    extBoundaryFromH0 k f hS (unitHomCohomologyLinearEquivZero k f S.X₃ s) =
      (Ext.mk₀ s).comp hS.extClass (zero_add 1) := by
  let := modulesLinearOverField k f
  change (M9Native.MukaiYonedaExact.boundary k (unit X) hS)
    ((unitExtCohomologyLinearEquivAll k f S.X₃ 0).symm
      ((unitExtCohomologyLinearEquivAll k f S.X₃ 0)
        ((Ext.linearEquiv₀ (R := k)).symm s))) = _
  rw [LinearEquiv.symm_apply_apply, Ext.linearEquiv₀_symm_apply]
  rfl

/-- Its value on the actual H0 image of a section and the actual
normalization vector κ is the original actual pullback class. -/
theorem extBoundaryFromH0_kappa {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (s : unit X ⟶ S.X₃) :
    letI := modulesLinearOverField k f
    extBoundaryFromH0 k f hS (cohomologyOverFieldMap k f s 0 (kappa k f)) =
      (Ext.mk₀ s).comp hS.extClass (zero_add 1) := by
  let := modulesLinearOverField k f
  rw [← unitHomCohomologyLinearEquivZero_apply k f s]
  exact extBoundaryFromH0_unitHom k f hS s

/-- The actual Yoneda boundary on H0 fits the actual preceding H0 map
exactly, by the native Ext exact sequence and actual coefficient naturality. -/
theorem extBoundaryFromH0_exact_middle {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    letI := modulesLinearOverField k f
    Function.Exact (cohomologyOverFieldMap k f S.g 0).hom (extBoundaryFromH0 k f hS) := by
  let := modulesLinearOverField k f
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := unitExtCohomologyLinearEquivAll k f S.X₂ 0)
    (e₂ := unitExtCohomologyLinearEquivAll k f S.X₃ 0)
    (e₃ := LinearEquiv.refl k (Ext.{u} (unit X) S.X₁ 1)) ?_ ?_
    (M9Native.MukaiYonedaExact.exact_middle k (unit X) hS)
  · ext e
    exact (unitExtCohomologyAddEquiv_naturality k f S.g 0 e).symm
  · ext e
    change (M9Native.MukaiYonedaExact.boundary k (unit X) hS)
      ((unitExtCohomologyLinearEquivAll k f S.X₃ 0).symm
        ((unitExtCohomologyLinearEquivAll k f S.X₃ 0) e)) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

/-- The same actual boundary, in original H1, using the genuine linear
unit-Ext/cohomology comparison. -/
def cohomologyYonedaBoundary {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    cohomologyOverField k f S.X₃ 0 →ₗ[k] cohomologyOverField k f S.X₁ 1 := by
  letI := modulesLinearOverField k f
  exact (unitExtCohomologyLinearEquivAll k f S.X₁ 1).toLinearMap.comp
    (extBoundaryFromH0 k f hS)

/-- Exactness before the actual cohomology-valued Yoneda boundary is
proved, rather than assumed as a boundary comparison premise. -/
theorem cohomologyYonedaBoundary_exact_middle {S : ShortComplex X.Modules}
    (hS : S.ShortExact) :
    Function.Exact (cohomologyOverFieldMap k f S.g 0).hom (cohomologyYonedaBoundary k f hS) := by
  let := modulesLinearOverField k f
  exact Function.Exact.comp_injective
    (fun e => unitExtCohomologyLinearEquivAll k f S.X₁ 1 e)
    (extBoundaryFromH0_exact_middle k f hS)
    (unitExtCohomologyLinearEquivAll k f S.X₁ 1).injective
    (unitExtCohomologyLinearEquivAll k f S.X₁ 1).map_zero

/-- Exactness after the actual cohomology-valued Yoneda boundary is
transported from the native Ext exact sequence by proved naturality. -/
theorem cohomologyYonedaBoundary_exact_right {S : ShortComplex X.Modules}
    (hS : S.ShortExact) :
    Function.Exact (cohomologyYonedaBoundary k f hS) (cohomologyOverFieldMap k f S.f 1).hom := by
  let := modulesLinearOverField k f
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := unitExtCohomologyLinearEquivAll k f S.X₃ 0)
    (e₂ := unitExtCohomologyLinearEquivAll k f S.X₁ 1)
    (e₃ := unitExtCohomologyLinearEquivAll k f S.X₂ 1) ?_ ?_
    (M9Native.MukaiYonedaExact.exact_right k (unit X) hS)
  · ext e
    change (unitExtCohomologyLinearEquivAll k f S.X₁ 1)
      ((M9Native.MukaiYonedaExact.boundary k (unit X) hS)
        ((unitExtCohomologyLinearEquivAll k f S.X₃ 0).symm
          ((unitExtCohomologyLinearEquivAll k f S.X₃ 0) e))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · ext e
    exact (unitExtCohomologyAddEquiv_naturality k f S.f 1 e).symm

/-- The native chosen boundary and the actual Ext boundary have the same
rank because their actual kernels are the same preceding H0 image. -/
theorem chosen_boundary_rank_eq_extBoundaryFromH0 {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [Module.Finite k (cohomologyOverField k f S.X₃ 0)] :
    letI := modulesLinearOverField k f
    Module.finrank k (LinearMap.range
        (M9Native.MukaiCohomologyParity.cohomologyBoundary k f hS 0).hom) =
      Module.finrank k (LinearMap.range (extBoundaryFromH0 k f hS)) := by
  let := modulesLinearOverField k f
  have h := (M9Native.MukaiCohomologyParity.cohomologyBoundary k f hS 0).hom.finrank_range_add_finrank_ker
  have h' := (extBoundaryFromH0 k f hS).finrank_range_add_finrank_ker
  have hker : LinearMap.ker
      (M9Native.MukaiCohomologyParity.cohomologyBoundary k f hS 0).hom =
      LinearMap.ker (extBoundaryFromH0 k f hS) := by
    ext x
    change (M9Native.MukaiCohomologyParity.cohomologyBoundary k f hS 0).hom x = 0 ↔
      extBoundaryFromH0 k f hS x = 0
    exact (M9Native.MukaiCohomologyParity.cohomologyBoundary_exact_middle k f hS 0 x).trans
      (extBoundaryFromH0_exact_middle k f hS x).symm
  rw [hker] at h
  omega

end M9Native.MukaiCohomologyYonedaBoundary
