module

public import M9StacksIntegration.LagrangianChartCotangent

/-! The actual affine section comparison, with its original scalar ring. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianPolynomialDifferentials

open LagrangianChartCotangent
open Stacks.AlgebraicGeometry.AffineDifferentialsIso

variable (K : Type u) [Field K]

local instance polynomialSectionsModule : Module (LagrangianChartCotangent.Ring K)
    Γ(Scheme.Hom.relativeDifferentials (chartProjection K),⊤) :=
  show Module (LagrangianChartCotangent.Ring K)
    (moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (chartProjection K))) from inferInstance

/-- The original affine scheme's genuine ring of global functions. -/
def scalarEquiv : LagrangianChartCotangent.Ring K ≃+* Γ(chart K,⊤) :=
  (Scheme.ΓSpecIso (.of (LagrangianChartCotangent.Ring K))).symm.commRingCatIsoToRingEquiv

local instance scalarInvPair : RingHomInvPair (scalarEquiv K).toRingHom
    (scalarEquiv K).symm.toRingHom := RingHomInvPair.of_ringEquiv (scalarEquiv K)
local instance scalarInvPairSymm : RingHomInvPair (scalarEquiv K).symm.toRingHom
    (scalarEquiv K).toRingHom := RingHomInvPair.of_ringEquiv_symm (scalarEquiv K)

/-- The actual polynomial algebra and the original affine coefficient
map induce equal, rather than merely isomorphic, algebra structures. -/
def sourceIso : ModuleCat.of (LagrangianChartCotangent.Ring K) Ω[LagrangianChartCotangent.Ring K⁄K] ≅
    CommRingCat.KaehlerDifferential (coefficient K) :=
  (kaehlerAlgebraIso ((coefficient K).hom.toAlgebra)
    (inferInstance : Algebra K (LagrangianChartCotangent.Ring K))
      (Algebra.algebra_ext _ _ (fun _ => rfl))).symm

/-- This is the native affine comparison, read as the genuine
semilinear equivalence over the actual structure-ring isomorphism. -/
def sectionsEquiv : LinearEquiv (scalarEquiv K).toRingHom
    (σ' := (scalarEquiv K).symm.toRingHom) Ω[LagrangianChartCotangent.Ring K⁄K]
    Γ(Scheme.Hom.relativeDifferentials (chartProjection K),⊤) :=
  { __ := ((sourceIso K) ≪≫ sectionsIso (coefficient K)).toLinearEquiv.toAddEquiv
    map_smul' := fun r m =>
      (((sourceIso K) ≪≫ sectionsIso (coefficient K)).toLinearEquiv.map_smul r m) }

/-- Changing equal algebra structures preserves the literal universal
Kähler differential, not just its span. -/
theorem kaehlerAlgebraIso_d {A B : Type u} [CommRing A] [CommRing B]
    (i₁ i₂ : Algebra A B) (h : i₁=i₂) (x : B) :
    (kaehlerAlgebraIso i₁ i₂ h).hom.hom
      (letI := i₁; KaehlerDifferential.D A B x)=
        (letI := i₂; KaehlerDifferential.D A B x) := by
  cases h
  rfl

theorem kaehlerAlgebraIso_inv_d {A B : Type u} [CommRing A] [CommRing B]
    (i₁ i₂ : Algebra A B) (h : i₁=i₂) (x : B) :
    (kaehlerAlgebraIso i₁ i₂ h).inv.hom
      (letI := i₂; KaehlerDifferential.D A B x)=
        (letI := i₁; KaehlerDifferential.D A B x) := by
  cases h
  rfl

/-- The actual section comparison carries each original polynomial
differential to the actual universal relative differential. -/
theorem sectionsEquiv_d (x : LagrangianChartCotangent.Ring K) :
    sectionsEquiv K (KaehlerDifferential.D K (LagrangianChartCotangent.Ring K) x)=
      (Scheme.Hom.universalRelativeDerivation (chartProjection K)).d
        ((scalarEquiv K) x) := by
  change (sectionsIso (coefficient K)).hom.hom
    ((sourceIso K).hom.hom (KaehlerDifferential.D K (LagrangianChartCotangent.Ring K) x))=_
  have h : (sourceIso K).hom.hom (KaehlerDifferential.D K (LagrangianChartCotangent.Ring K) x)=
      CommRingCat.KaehlerDifferential.d (f := coefficient K) x := by
    exact kaehlerAlgebraIso_inv_d ((coefficient K).hom.toAlgebra)
      (inferInstance : Algebra K (LagrangianChartCotangent.Ring K))
        (Algebra.algebra_ext _ _ (fun _ => rfl)) x
  rw [h,sectionsIso_d]
  rfl

/-- The original six coordinate derivatives form a genuine basis of the
native cotangent sheaf's actual global sections. -/
def sectionsBasis : Module.Basis (Fin 6) Γ(chart K,⊤)
    Γ(Scheme.Hom.relativeDifferentials (chartProjection K),⊤) :=
  let b : Module.Basis (Fin 6) (LagrangianChartCotangent.Ring K)
      Γ(Scheme.Hom.relativeDifferentials (chartProjection K),⊤) :=
    (KaehlerDifferential.mvPolynomialBasis K (Fin 6)).map
      (((sourceIso K) ≪≫ sectionsIso (coefficient K)).toLinearEquiv)
  b.mapCoeffs (scalarEquiv K) (fun _ _ => rfl)

@[simp] theorem sectionsBasis_apply (i : Fin 6) :
    sectionsBasis K i=
      (Scheme.Hom.universalRelativeDerivation (chartProjection K)).d
        ((scalarEquiv K) (MvPolynomial.X i)) := by
  simp only [sectionsBasis,Module.Basis.mapCoeffs_apply,Module.Basis.map_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact sectionsEquiv_d K _

end M9Native.LagrangianPolynomialDifferentials
