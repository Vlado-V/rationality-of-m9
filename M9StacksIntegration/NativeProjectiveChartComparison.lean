module

public import M9StacksIntegration.ConicFrameGammaAction
import all StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
import all StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-! Named-coordinate compatibility for the genuine two native Proj models. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace M9Native.NativeProjectiveChartComparison

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (σ : Type u)

theorem affineSpecIso_inv_toIntegral :
    (AffineSpace.SpecIso σ (.of R)).inv ≫
        AffineSpace.toSpecMvPoly σ (Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (integralCoeffHom R))) := by
  apply (AffineSpace.toSpecMvPolyIntEquiv σ).injective
  funext i
  rw [AffineSpace.toSpecMvPolyIntEquiv_comp]
  change (AffineSpace.SpecIso σ (.of R)).inv.appTop
      (AffineSpace.coord (Spec (.of R)) i) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord]
  change (Scheme.ΓSpecIso (.of (MvPolynomial σ R))).inv (MvPolynomial.X i) =
    ((Spec.map (CommRingCat.ofHom (MvPolynomial.map (integralCoeffHom R)))).appTop.hom.comp
      (Scheme.ΓSpecIso (.of (MvPolynomial σ (ULift.{u} ℤ)))).inv.hom) (MvPolynomial.X i)
  have h := Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MvPolynomial.map (integralCoeffHom R) :
      MvPolynomial σ (ULift.{u} ℤ) →+* MvPolynomial σ R))
  simpa only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply,
    MvPolynomial.map_X] using
      congrArg (fun f => f (MvPolynomial.X i)) (congrArg CommRingCat.Hom.hom h)

variable (n : ℕ) (i : Fin (n+1)) (e : σ ≃ {j : Fin (n+1) // j ≠ i})

def chartRingEquiv : MvPolynomial σ R ≃+*
    HomogeneousLocalization.Away (polyGrading R n) (MvPolynomial.X i) :=
  (MvPolynomial.renameEquiv R e).toRingEquiv.trans
    (Stacks.AlgebraicGeometry.ProjPolyChart.chartEquiv R n i)

theorem chartRingEquiv_natural (p : MvPolynomial σ (ULift.{u} ℤ)) :
    chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom R) i
        (chartRingEquiv (ULift.{u} ℤ) σ n i e p) =
      chartRingEquiv R σ n i e (MvPolynomial.map (integralCoeffHom R) p) := by
  change chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom R) i
      (chartHom (ULift.{u} ℤ) n i (MvPolynomial.rename e p)) =
    chartHom R n i (MvPolynomial.rename e (MvPolynomial.map (integralCoeffHom R) p))
  rw [chartBaseChange_chartHom,MvPolynomial.map_rename]

@[simp] theorem chartRingEquiv_C (r : R) :
    chartRingEquiv R σ n i e (MvPolynomial.C r) = coeffToAway R n i r := by
  simp [chartRingEquiv]

theorem chartRingEquiv_symm_natural :
    (chartRingEquiv R σ n i e).symm.toRingHom.comp
        (chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom R) i) =
      (MvPolynomial.map (σ := σ) (integralCoeffHom R)).comp
        (chartRingEquiv (ULift.{u} ℤ) σ n i e).symm.toRingHom := by
  ext a
  obtain ⟨p,rfl⟩ := (chartRingEquiv (ULift.{u} ℤ) σ n i e).surjective a
  simp only [RingHom.comp_apply,RingEquiv.toRingHom_eq_coe,RingEquiv.coe_toRingHom,
    chartRingEquiv_natural,RingEquiv.symm_apply_apply]

def polynomialChart : Spec (.of (MvPolynomial σ R)) ⟶ Proj (polyGrading R n) :=
  Spec.map (CommRingCat.ofHom (chartRingEquiv R σ n i e).symm.toRingHom) ≫
    Proj.awayι (polyGrading R n) (MvPolynomial.X i) (X_mem_one R n i) Nat.one_pos

@[reassoc] theorem polynomialChart_toBase :
    polynomialChart R σ n i e ≫ projToSpecCoeff R n =
      Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial σ R))) := by
  rw [polynomialChart,Category.assoc,
    Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projToSpecCoeff,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change (chartRingEquiv R σ n i e).symm (coeffToAway R n i r) = MvPolynomial.C r
  exact (RingEquiv.symm_apply_eq (chartRingEquiv R σ n i e)).mpr
    (chartRingEquiv_C R σ n i e r).symm

@[reassoc] theorem polynomialChart_toIntegral :
    polynomialChart R σ n i e ≫
        coordinateProjMap R n (integralGradedHom R n) (mapDomain_integralGradedHom_eq_top R n) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.map (integralCoeffHom R))) ≫
        Spec.map (CommRingCat.ofHom (chartRingEquiv (ULift.{u} ℤ) σ n i e).symm.toRingHom) ≫
          Stacks.AlgebraicGeometry.ProjBaseChange.integralChart n i := by
  rw [polynomialChart,Category.assoc,
    Stacks.AlgebraicGeometry.ProjBaseChange.coordinateProjMap_eq_projMap,
    Stacks.AlgebraicGeometry.ProjBaseChange.awayι_comp_projMap
      (polyGrading (ULift.{u} ℤ) n) (polyGrading R n) (integralGradedHom R n)
      (Stacks.AlgebraicGeometry.ProjBaseChange.irrelevant_le_map_integralGradedHom R n)
      Nat.one_pos (X_mem_one (ULift.{u} ℤ) n i) (X_mem_one R n i) (by simp)
      (chartBaseChange (ULift.{u} ℤ) n (integralCoeffHom R) i)
      (fun k a ha ha' => chartBaseChange_mk (ULift.{u} ℤ) n (integralCoeffHom R) i k a ha ha'),
    ← Category.assoc,← Spec.map_comp,← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (chartRingEquiv_symm_natural R σ n i e)

theorem affineChart_comparison :
    (AffineSpace.SpecIso σ (.of R)).inv ≫
        projectiveSpaceOver.affineChart n i e (Spec (.of R)) =
      polynomialChart R σ n i e ≫ projCompare R n := by
  apply pullback.hom_ext
  · simp only [Category.assoc,projectiveSpaceOver.affineChart_comp_fst,
      projCompare_fst,polynomialChart_toBase]
    change (AffineSpace.SpecIso σ (.of R)).inv ≫
        (AffineSpace σ (Spec (.of R)) ↘ Spec (.of R)) = _
    exact AffineSpace.SpecIso_inv_over (.of R)
  · rw [Category.assoc,projectiveSpaceOver.affineChart_comp_snd]
    change (AffineSpace.SpecIso σ (.of R)).inv ≫
        AffineSpace.toSpecMvPoly σ (Spec (.of R)) ≫
          projectiveSpaceOver.affineChartAtUniverse n i e = _
    rw [← Category.assoc,affineSpecIso_inv_toIntegral,Category.assoc,
      projCompare_snd,polynomialChart_toIntegral]
    congr 1

end M9Native.NativeProjectiveChartComparison
