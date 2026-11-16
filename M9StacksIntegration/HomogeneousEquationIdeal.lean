module

public import M9StacksIntegration.NativeProjectiveVector
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.HomogeneousIdealSheaf

/-! Finite homogeneous equations define their actual projective ideal
sheaf. A literal homogeneous evaluation killing the equations factors
through the genuine graded quotient, on every test scheme. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.HomogeneousIdeal

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace M9Native.HomogeneousEquationIdeal

variable (K : Type u) [CommRing K] (n d : ℕ)
    {ι : Type v} [Finite ι] (F : ι → polyGrading K n d)

def homogeneousSpan : HomogeneousIdeal (polyGrading K n) where
  toSubmodule := Ideal.span (Set.range fun i => (F i : MvPolynomial (Fin (n+1)) K))
  is_homogeneous' := Ideal.homogeneous_span _ _ (by
    rintro _ ⟨i, rfl⟩
    exact ⟨d, (F i).property⟩)

omit [Finite ι] in
theorem homogeneousSpan_toIdeal : (homogeneousSpan K n d F).toIdeal =
    Ideal.span (Set.range fun i => (F i : MvPolynomial (Fin (n+1)) K)) := rfl

instance twist_isInvertible : AlgebraicGeometry.SheafOfModules.IsInvertible
    (AlgebraicGeometry.Proj (polyGrading K n)).sheaf.obj
      (AlgebraicGeometry.Proj (polyGrading K n)).ringCatSheaf.property
      (twistingSheafModule (polyGrading K n) (d : ℤ)) :=
  algebraicGeometry_isInvertible_twistingSheaf (polyGrading K n)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K) d

def equationIdeal (i : ι) : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData :=
  zeroScheme (AlgebraicGeometry.Proj (polyGrading K n)) (twistingSheafModule (polyGrading K n) (d : ℤ))
    (degreeSection (polyGrading K n) d (F i))

/-- Equality of full ideal sheaves, retaining all nilpotents. -/
theorem homogeneousIdealSheaf_eq_iSup_equationIdeal :
    homogeneousIdealSheaf (polyGrading K n) (homogeneousSpan K n d F) =
      ⨆ i, equationIdeal K n d F i := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun g : polyGrading K n 1 =>
      (⟨Proj.basicOpen (polyGrading K n) (g : MvPolynomial (Fin (n+1)) K),
        Proj.isAffineOpen_basicOpen _ _ g.2 Nat.one_pos⟩ :
        (AlgebraicGeometry.Proj (polyGrading K n)).affineOpens)) ?_ fun g => ?_
  · exact Stacks.AlgebraicGeometry.ProjDegreeOne.iSup_basicOpen_degreeOne_eq_top _
      (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n+1)) K)
  · rw [homogeneousIdealSheaf_ideal_basicOpen_eq_span_range _ _ g.2 Nat.one_pos
      (fun i => (F i : MvPolynomial (Fin (n+1)) K)) (fun _ => d)
      (fun i => by simpa only [smul_eq_mul, mul_one] using (F i).property)
      (homogeneousSpan_toIdeal K n d F)]
    simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    have hh (i : ι) : (equationIdeal K n d F i).ideal
        ⟨Proj.basicOpen (polyGrading K n) (g : MvPolynomial (Fin (n+1)) K),
          Proj.isAffineOpen_basicOpen _ _ g.2 Nat.one_pos⟩ =
        Ideal.span {(chartFraction (polyGrading K n) g.2 d
          ⟨(F i : MvPolynomial (Fin (n+1)) K),
            (by simpa only [smul_eq_mul, mul_one] using (F i).property)⟩)} := by
      exact zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq _ g.2 Nat.one_pos d
        (by simp) (F i) (by simpa only [smul_eq_mul, mul_one] using (F i).property)
    simp_rw [hh]
    exact Ideal.span_range_eq_iSup _

def quotientMap : AlgebraicGeometry.Proj (quotientGrading (homogeneousSpan K n d F)) ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  Proj.map (quotientMk (homogeneousSpan K n d F))
    (Proj.irrelevant_le_map_of_surjective _ (surjective_quotientMk _))

instance quotientMap_isClosedImmersion : IsClosedImmersion (quotientMap K n d F) :=
  Proj.isClosedImmersion_map_of_surjective' _ (surjective_quotientMk _)

theorem quotientMap_ker : (quotientMap K n d F).ker = ⨆ i, equationIdeal K n d F i :=
  homogeneousIdealSheaf_eq_iSup_equationIdeal K n d F

section TestScheme

variable {K n d F} {T : Scheme.{u}}
    (e : MvPolynomial (Fin (n+1)) K →+* Γ(T,⊤))
    (he : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map e = ⊤)
    (hF : ∀ i, e (F i) = 0)

include hF in
theorem span_le_ker : (homogeneousSpan K n d F).toIdeal ≤ RingHom.ker e := by
  rw [homogeneousSpan_toIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hF i

def quotientEvaluation :
    (MvPolynomial (Fin (n+1)) K ⧸ (homogeneousSpan K n d F).toIdeal) →+* Γ(T,⊤) :=
  Ideal.Quotient.lift _ e (span_le_ker e hF)

theorem quotientEvaluation_comp : (quotientEvaluation e hF).comp
    (quotientMk (homogeneousSpan K n d F)).toRingHom = e := by
  apply RingHom.ext
  intro x
  rfl

include he in
theorem quotientEvaluation_irrelevant :
    (HomogeneousIdeal.irrelevant (quotientGrading (homogeneousSpan K n d F))).toIdeal.map
      (quotientEvaluation e hF) = ⊤ := by
  have hmap : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map
      (quotientMk (homogeneousSpan K n d F)).toRingHom ≤
      (HomogeneousIdeal.irrelevant (quotientGrading (homogeneousSpan K n d F))).toIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    exact (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr fun j hj a ha =>
      HomogeneousIdeal.mem_irrelevant_of_mem _ hj ((quotientMk _).map_mem ha)
  apply top_unique
  calc
    ⊤ = (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map e := he.symm
    _ = (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map
        ((quotientEvaluation e hF).comp (quotientMk (homogeneousSpan K n d F)).toRingHom) := by
      rw [quotientEvaluation_comp]
    _ = ((HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map
        (quotientMk (homogeneousSpan K n d F)).toRingHom).map (quotientEvaluation e hF) := by
      rw [Ideal.map_map]
    _ ≤ _ := Ideal.map_mono hmap

include hF in
/-- A genuine morphism into the actual graded quotient is constructed;
the evaluation-zero condition is on literal polynomials over Γ(T,O). -/
theorem exists_factor_fromOfGlobalSections :
    ∃ f : T ⟶ AlgebraicGeometry.Proj (quotientGrading (homogeneousSpan K n d F)),
      f ≫ quotientMap K n d F = Proj.fromOfGlobalSections (polyGrading K n) e he := by
  refine ⟨Proj.fromOfGlobalSections _ (quotientEvaluation e hF)
    (quotientEvaluation_irrelevant e he hF), ?_⟩
  rw [quotientMap, Proj.fromOfGlobalSections_comp_map _ _ _ _
    (by rw [quotientEvaluation_comp]; exact he)]
  exact Proj.fromOfGlobalSections_congr (quotientEvaluation_comp e hF) _ _

include hF in
theorem iSup_equationIdeal_le_ker_fromOfGlobalSections :
    (⨆ i, equationIdeal K n d F i) ≤ (Proj.fromOfGlobalSections (polyGrading K n) e he).ker := by
  obtain ⟨f, hf⟩ := exists_factor_fromOfGlobalSections e he hF
  rw [← quotientMap_ker, ← hf]
  exact f.le_ker_comp (quotientMap K n d F)

include hF in
/-- Literal polynomial evaluation zero implies the actual pulled-back
degree section is zero on every test scheme, including nonreduced ones. -/
theorem pullback_degreeSection_eq_zero (i : ι) :
    pullbackGlobalSections (Proj.fromOfGlobalSections (polyGrading K n) e he)
      (twistingSheafModule (polyGrading K n) (d : ℤ))
      (degreeSection (polyGrading K n) d (F i)) = 0 := by
  apply (pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker _ _ _).mpr
  exact (le_iSup (fun i => equationIdeal K n d F i) i).trans
    (iSup_equationIdeal_le_ker_fromOfGlobalSections e he hF)

end TestScheme

end M9Native.HomogeneousEquationIdeal
