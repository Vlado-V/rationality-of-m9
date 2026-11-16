module

public import M9StacksIntegration.PrimitiveGaussFamily

/-! The literal localized Gauss matrix as a morphism to the actual native symplectic group
scheme, through its checked all-test-scheme representing equivalence. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveGaussGroupScheme

local instance : GrpObj (Sp6GroupScheme.obj (Spec (.of ℂ))) :=
  Sp6GroupScheme.groupObj _

open PrimitiveGaussCoordinates

abbrev source : Scheme := Spec (.of (sourceRing ℂ))

def sourceProjection : source ⟶ Spec (.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (sourceRing ℂ)))

abbrev sourceOver : Over (Spec (.of ℂ)) := Over.mk sourceProjection

def globalFamily : Matrix.symplecticGroup (Fin 3) Γ(source, ⊤) :=
  Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom
    (PrimitiveGaussFamily.family ℂ)

/-- A genuine family of symplectic transformations, not an inferred pointwise assignment. -/
def gaussFamily : sourceOver ⟶ Sp6GroupScheme.obj (Spec (.of ℂ)) :=
  (Sp6GroupScheme.pointsMulEquiv (Spec (.of ℂ)) sourceOver).symm globalFamily

@[simp] theorem pointsMulEquiv_gaussFamily :
    Sp6GroupScheme.pointsMulEquiv (Spec (.of ℂ)) sourceOver gaussFamily = globalFamily :=
  (Sp6GroupScheme.pointsMulEquiv _ _).apply_symm_apply _

@[reassoc] theorem gaussFamily_over :
    gaussFamily.left ≫ (Sp6GroupScheme.obj (Spec (.of ℂ))).hom = sourceProjection :=
  gaussFamily.w

theorem globalFamily_scaled :
    (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv
        (algebraMap (polynomial ℂ) (sourceRing ℂ) (MvPolynomial.X 0)) •
      LagrangianTransitivity.matrixSix Γ(source, ⊤) globalFamily =
        ((M9.PrimitiveOpenOrbit.formalMatrix ℂ).map
          (algebraMap (polynomial ℂ) (sourceRing ℂ))).map
            (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom := by
  rw [globalFamily]
  have hm : Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom
      (PrimitiveGaussFamily.family ℂ) =
      LagrangianTransitivity.mapSymplectic (sourceRing ℂ)
        (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv.hom (PrimitiveGaussFamily.family ℂ) := by
    apply Subtype.ext
    rfl
  rw [hm, LagrangianTransitivity.matrixSix_map]
  ext i j
  have he := congrArg (fun M : Matrix (Fin 6) (Fin 6) (sourceRing ℂ) =>
    (Scheme.ΓSpecIso (.of (sourceRing ℂ))).inv (M i j))
      (PrimitiveGaussFamily.family_scaled ℂ)
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.map_apply] using he

end M9Native.PrimitiveGaussGroupScheme
