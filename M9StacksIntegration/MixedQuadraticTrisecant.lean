module

public import M9StacksIntegration.QuadraticTrisecant
public import StacksFrontier.AlgebraicGeometry.Divisors.ProjClosedSubschemeKernel

/-! Linear and quadratic equations on a genuine trisecant line.
The linear case is derived by squaring the original section on the
FULL closed scheme. This treats a quadratic ambient variety cut by
actual linear equations, without replacing the original cut by its support. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)
open Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection
open M9Native.ProjectiveQuadraticCohomology M9Native.ProjectiveQuadraticDimension

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.MixedQuadraticTrisecant

variable (K : Type u) [Field K]

def degreeIdeal (n d : ℕ) (F : polyGrading K n d) : (projective K n).IdealSheafData :=
  zeroScheme (projective K n) (twist K n (d : ℤ)) (degreeSection (polyGrading K n) d F)

/-- The actual original LINEAR polynomial vanishes; D may have nilpotents. -/
theorem linear_polynomial_eq_zero_of_ideal_le
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (F : polyGrading K 1 1) (hvan : degreeIdeal K 1 1 F ≤ D) :
    (F : MvPolynomial (Fin 2) K) = 0 := by
  have hv : pullbackGlobalSections D.subschemeι (twist K 1 1)
      (degreeSection (polyGrading K 1) 1 F) = 0 :=
    (pullbackSection_eq_zero_iff_factorsThrough_zeroScheme (projective K 1)
      (twist K 1 1) (degreeSection (polyGrading K 1) 1 F) D.subschemeι).mpr
      ⟨Scheme.IdealSheafData.inclusion hvan, Scheme.IdealSheafData.inclusion_subschemeι hvan⟩
  let F2 : polyGrading K 1 2 := ⟨(F : MvPolynomial (Fin 2) K) * F,
    SetLike.mul_mem_graded F.property F.property⟩
  have hv2 := pullbackGlobalSections_degreeSection_mul_eq_zero
    (polyGrading K 1) D.subschemeι F F hv
  have hsq : degreeSection (polyGrading K 1) 2 F2 = 0 := by
    have h := QuadraticTrisecant.quadratic_eval_eq_zero_of_pullback_eq_zero K D hD
      (polynomialSection K 1 F2) (by
        simpa only [polynomialSection_eval, F2, twist, Nat.reduceAdd, Nat.cast_ofNat] using hv2)
    simpa only [polynomialSection_eval] using h
  have hzero : (F2 : MvPolynomial (Fin 2) K) = 0 := by
    by_contra h
    exact Stacks.ProjectiveSpace.Cohomology.degreeSection_ne_zero K 1 2 F2 h hsq
  exact (mul_eq_zero.mp hzero).elim id id

section Line

variable (n : ℕ) (ψ : polyGrading K n →+*ᵍ polyGrading K 1)
    (hψ : Function.Surjective ψ)

def restricted (d : ℕ) (F : polyGrading K n d) : polyGrading K 1 d :=
  ⟨ψ F, ψ.map_mem F.property⟩

private theorem pullbackGlobal_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) : pullbackGlobalSections f M s =
      Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.AlgebraicGeometry.PullbackUnit.pullbackSection f M s) = _
  exact Functor.map_id_apply _ _ _

/-- Genuine zero-ideal pullback for the actual linear projective morphism. -/
theorem degreeIdeal_comap_linearMap (d : ℕ) (F : polyGrading K n d) :
    (degreeIdeal K n d F).comap (QuadraticTrisecant.linearMap K n ψ hψ) =
      degreeIdeal K 1 d (restricted K n ψ d F) := by
  rw [degreeIdeal, ← Stacks.Divisors.zeroScheme_pullback]
  dsimp only [degreeIdeal]
  apply zeroScheme_eq_of_iso
    (pullbackTwistIso ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) d)
  rw [pullbackGlobal_eq]
  exact pullbackTwistIso_degreeSection ψ (Proj.irrelevant_le_map_of_surjective ψ hψ) hψ
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) d F

theorem linear_generated_comap_eq_bot
    {ι : Type u} (F : ι → polyGrading K n 1)
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (hvan : (⨆a,degreeIdeal K n 1 (F a)).comap
      (QuadraticTrisecant.linearMap K n ψ hψ) ≤ D) :
    (⨆a,degreeIdeal K n 1 (F a)).comap (QuadraticTrisecant.linearMap K n ψ hψ) = ⊥ := by
  apply le_antisymm _ bot_le
  apply (Scheme.IdealSheafData.le_map_iff_comap_le).mp
  apply iSup_le
  intro a
  apply (Scheme.IdealSheafData.le_map_iff_comap_le).mpr
  have hFa : (degreeIdeal K n 1 (F a)).comap (QuadraticTrisecant.linearMap K n ψ hψ) ≤ D :=
    (Scheme.IdealSheafData.comap_mono (QuadraticTrisecant.linearMap K n ψ hψ)
      (le_iSup (fun a => degreeIdeal K n 1 (F a)) a)).trans hvan
  rw [degreeIdeal_comap_linearMap K n ψ hψ] at hFa ⊢
  have hz := linear_polynomial_eq_zero_of_ideal_le K D hD (restricted K n ψ 1 (F a)) hFa
  have hF : restricted K n ψ 1 (F a)=0 := Subtype.ext hz
  rw [hF, degreeIdeal, degreeSection_zero, zeroScheme_zero]

/-- The original mixed linear/quadratic ideal pulls back to ZERO,
because every one of its actual equations is forced to vanish online. -/
theorem mixed_generated_comap_eq_bot
    {ι κ : Type u} (F : ι → polyGrading K n 1) (Q : κ → polyGrading K n 2)
    (I : (projective K n).IdealSheafData)
    (hI : I = (⨆a,degreeIdeal K n 1 (F a)) ⊔
      (⨆b,quadraticIdeal K n (polynomialSection K n (Q b))))
    (D : (projective K 1).IdealSheafData)
    (hD : 3 ≤ Module.finrank K
      (structureSheafCohomology (D.subschemeι ≫ projToSpecCoeff K 1) 0))
    (hvan : I.comap (QuadraticTrisecant.linearMap K n ψ hψ) ≤ D) :
    I.comap (QuadraticTrisecant.linearMap K n ψ hψ) = ⊥ := by
  have hlin : (⨆a,degreeIdeal K n 1 (F a)).comap
      (QuadraticTrisecant.linearMap K n ψ hψ) ≤ D :=
    (Scheme.IdealSheafData.comap_mono (QuadraticTrisecant.linearMap K n ψ hψ)
      (hI ▸ le_sup_left)).trans hvan
  have hquad : (⨆b,quadraticIdeal K n (polynomialSection K n (Q b))).comap
      (QuadraticTrisecant.linearMap K n ψ hψ) ≤ D :=
    (Scheme.IdealSheafData.comap_mono (QuadraticTrisecant.linearMap K n ψ hψ)
      (hI ▸ le_sup_right)).trans hvan
  rw [hI, Scheme.IdealSheafData.comap_sup,
    linear_generated_comap_eq_bot K n ψ hψ F D hD hlin,
    QuadraticTrisecant.quadratic_generated_comap_eq_bot K n ψ hψ Q _ rfl D hD hquad,
    sup_idem]

end Line
end M9Native.MixedQuadraticTrisecant
