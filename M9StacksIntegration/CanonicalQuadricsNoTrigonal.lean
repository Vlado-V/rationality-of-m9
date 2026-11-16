module

public import M9StacksIntegration.DivisorProjectiveSpan
public import M9StacksIntegration.TrisecantImageFactor

/-! A genuine canonical closed immersion, cut scheme-theoretically by
actual equations of degree one and two, excludes an ORIGINAL g1_3.
The full divisor of one pencil section constructs the actual line;
base points and nonreduced zeros are included throughout. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory
open Stacks.AmpleProjectiveImmersion
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjBaseChange (polynomialComparison)
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension
universe u

namespace M9Native.CanonicalQuadricsNoTrigonal

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

local instance canonicalInvertible :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField f) :=
  CurveCanonicalInvertibility.dualizing_isInvertible f

/-- No pencil/span/rank or reduced-divisor premise is present: the
actual native g1_3 itself constructs the full length-three line divisor.
The ideal hypothesis concerns the ORIGINAL closed scheme, not its radical. -/
theorem no_g1_three (hdim : topologicalKrullDim X ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (κ : X ⟶ projectiveSpaceOver n (Spec (.of K))) [IsClosedImmersion κ]
    (hκ : κ ≫ Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of K)) = f)
    (e : (Scheme.Modules.pullback κ).obj
      (projectiveSpaceTwistingSheaf n (Spec (.of K))) ≅
        Stacks.Duality.dualizingSheafOverField f)
    (hgenus : genus f ≠ 0)
    {ι κq : Type u} (F : ι → polyGrading K n 1) (Q : κq → polyGrading K n 2)
    (hI : (κ ≫ (polynomialComparison K n).iso.hom).ker =
      (⨆a, MixedQuadraticTrisecant.degreeIdeal K n 1 (F a)) ⊔
        (⨆b, quadraticIdeal K n (polynomialSection K n (Q b)))) :
    ¬ Nonempty (LinearSeries K f hdim 3 1) := by
  classical
  rintro ⟨A⟩
  letI : Module.Finite K A.V := Module.finite_of_finrank_pos (by rw [A.finrank_eq]; norm_num)
  let b : Module.Basis (Fin 2) K A.V :=
    Module.finBasisOfFinrankEq K A.V (by simpa only [Nat.reduceAdd] using A.finrank_eq)
  let D := PencilCanonicalDivisor.divisor f hdim A b
  letI : IsFinite (D.subschemeι ≫ f) := PencilCanonicalDivisor.divisor_finite f hdim A b
  let L := Stacks.Duality.dualizingSheafOverField f
  letI : Stacks.Ample.IsInvertibleModule X L :=
    canonicalInvertible f
  let c := DivisorProjectiveSpan.coordinateH0 f κ e
  let E := (CanonicalDivisorEvaluation.evaluation f D L).comp c
  have hE : Module.finrank K (LinearMap.range E) ≤ 2 := by
    exact CanonicalDivisorEvaluation.pencil_evaluation_rank_le f hdim A b c
  have hsource : 2 ≤ Module.finrank K (Fin (n+1) → K) := by
    simpa only [Module.finrank_pi, Fintype.card_fin] using (show 2 ≤ n+1 by omega)
  obtain ⟨q, g, hq, hg⟩ := RankTwoQuotientFactor.exists_surjective_factor E hsource hE
  obtain ⟨t, htbase, ht⟩ := DivisorProjectiveSpan.polynomial_factor_of_evaluation_quotient
    f κ e D hκ q hq g hg
  let κp := κ ≫ (polynomialComparison K n).iso.hom
  have hκp : κp ≫ projToSpecCoeff K n = f := by
    change (κ ≫ (polynomialComparison K n).iso.hom) ≫ projToSpecCoeff K n = f
    rw [Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff]
    exact hκ
  let ψ := ProjectiveLinearSystemFactor.gradedHom K
    (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin 2)) q
  have hψ : Function.Surjective ψ := ProjectiveLinearSystemFactor.gradedHom_surjective K
    (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin 2)) q hq
  have hl : QuadraticTrisecant.linearMap K n ψ hψ ≫ projToSpecCoeff K n =
      projToSpecCoeff K 1 := ProjectiveLinearSystemFactor.polynomialEmbedding_over K
    (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin 2)) q hq
  have ht' : t ≫ QuadraticTrisecant.linearMap K n ψ hψ = D.subschemeι ≫ κp := by
    simpa only [κp, ψ, QuadraticTrisecant.linearMap,
      ProjectiveLinearSystemFactor.polynomialEmbedding, Nat.reduceAdd, Category.assoc] using ht
  have hD : 3 ≤ Module.finrank K (structureSheafCohomology (D.subschemeι ≫ f) 0) := by
    rw [FiniteClosedSectionH0.structureH0_finrank_eq_functions K (D.subschemeι ≫ f)]
    letI : Algebra K Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    have hlen := PencilCanonicalDivisor.divisor_length f hdim A b
    change Module.finrank K Γ(D.subscheme, ⊤) = 3 at hlen
    exact hlen.ge
  exact TrisecantImageFactor.no_mixed_trisecant K f κp hκp hgenus F Q hI
    D.subschemeι hD ψ hψ hl t htbase ht'

end M9Native.CanonicalQuadricsNoTrigonal
