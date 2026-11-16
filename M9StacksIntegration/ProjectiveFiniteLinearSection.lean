module

public import M9StacksIntegration.LagrangianPlaneHyperplanes

/-!
# Actual finite systems of projective linear equations

For a genuine finite family of vectors, the kernel ideal of the native
quotient-projective immersion is the supremum of the literal degree-one
zero ideals. Its all-test-scheme factorization criterion retains the
full scheme structure and requires no rank or independence assumption.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module
open AlgebraicGeometry.ProjectiveSpaceOfModule AlgebraicGeometry.ProjectiveSpectrum.Proj
open scoped BigOperators
universe u v

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace M9Native.ProjectiveFiniteLinearSection

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
  {ι : Type v} [Finite ι] (rows : ι → V)

abbrev constraints : Submodule K V := Submodule.span K (Set.range rows)
abbrev grading := fun n : ℕ => SymPow.symmetricPower n K V
abbrev quotientGrading := fun n : ℕ => SymPow.symmetricPower n K (V ⧸ constraints K V rows)

def forms : ι → SymmetricAlgebra K V := fun j => SymmetricAlgebra.ι K V (rows j)

theorem span_iota_constraints :
    Ideal.span (SymmetricAlgebra.ι K V '' (constraints K V rows : Set V)) =
      Ideal.span (Set.range (forms K V rows)) := by
  let J := Ideal.span (Set.range (forms K V rows))
  have hW : constraints K V rows ≤ Submodule.comap (SymmetricAlgebra.ι K V)
      (J.restrictScalars K) := by
    rw [constraints, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact hW hw
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨rows j, Submodule.subset_span ⟨j, rfl⟩, rfl⟩

theorem forms_homogeneous_one (j : ι) : forms K V rows j ∈ grading K V 1 :=
  ι_mem_symmetricPower_one K V (rows j)

def homogeneousKernel : HomogeneousIdeal (grading K V) :=
  Stacks.GradedKerQuotient.homogeneousKer (grading K V) (quotientGrading K V rows)
    (quotientGradedHom K V (constraints K V rows))

theorem homogeneousKernel_generated_by_rows : (homogeneousKernel K V rows).toIdeal =
    Ideal.span (Set.range (forms K V rows)) := by
  change RingHom.ker (SymPow.symAlgMap (constraints K V rows).mkQ) = _
  rw [Stacks.Chow.GenuineChern.ker_symAlgMap_eq_span _ (constraints K V rows).mkQ_surjective,
    Submodule.ker_mkQ, span_iota_constraints]

theorem quotientMap_kernel : (quotientMap K V (constraints K V rows)).ker =
    homogeneousIdealSheaf (grading K V) (homogeneousKernel K V rows) := by
  have h := Stacks.GradedKerQuotient.projMap_eq (grading K V) (quotientGrading K V rows)
    (quotientGradedHom K V (constraints K V rows))
    (SymPow.surjective_gradedSymAlgMap (constraints K V rows).mkQ
      (constraints K V rows).mkQ_surjective)
    (Proj.irrelevant_le_map_of_surjective _ (surjective_gradedSymAlgMap_mkQ (constraints K V rows)))
  change (Proj.map (quotientGradedHom K V (constraints K V rows)) _).ker = _
  rw [h, Scheme.Hom.ker_comp_of_isIso]
  rfl

theorem quotientMap_kernel_on_chart {f : SymmetricAlgebra K V} (hf : f ∈ grading K V 1) :
    ((quotientMap K V (constraints K V rows)).ker).ideal
        ⟨Proj.basicOpen (grading K V) f,
          Proj.isAffineOpen_basicOpen (grading K V) f hf Nat.one_pos⟩ =
      Ideal.span (Set.range fun j : ι => chartFraction (grading K V) hf 1
        ⟨forms K V rows j, forms_homogeneous_one K V rows j⟩) := by
  rw [quotientMap_kernel]
  exact homogeneousIdealSheaf_ideal_basicOpen_eq_span_range (grading K V)
    (homogeneousKernel K V rows) hf Nat.one_pos (forms K V rows) (fun _ => 1)
    (fun j => forms_homogeneous_one K V rows j) (homogeneousKernel_generated_by_rows K V rows)

theorem grading_generated_one :
    Algebra.adjoin (grading K V 0) ((grading K V 1 : Set (SymmetricAlgebra K V))) = ⊤ :=
  SymmetricAlgebra.adjoin_symmetricPower_one_eq_top K V

instance twistingLine_invertible : AlgebraicGeometry.SheafOfModules.IsInvertible
    (AlgebraicGeometry.Proj (grading K V)).sheaf.obj
      (AlgebraicGeometry.Proj (grading K V)).ringCatSheaf.property
      (twistingSheaf (grading K V) (1 : ℤ)) :=
  algebraicGeometry_isInvertible_twistingSheaf (grading K V) (grading_generated_one K V) 1

def hyperplane (j : ι) : (projectiveSpaceOfModule K V).IdealSheafData :=
  zeroScheme (projectiveSpaceOfModule K V) (twistingSheafModule (grading K V) (1 : ℤ))
    (degreeSection (grading K V) 1 ⟨forms K V rows j, forms_homogeneous_one K V rows j⟩)

/-- Equality of the full native ideal sheaves, without a reduced replacement. -/
theorem quotientMap_kernel_eq_hyperplanes :
    (quotientMap K V (constraints K V rows)).ker = ⨆ j : ι, hyperplane K V rows j := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun g : grading K V 1 => (⟨Proj.basicOpen (grading K V) (g : SymmetricAlgebra K V),
      Proj.isAffineOpen_basicOpen (grading K V) (g : SymmetricAlgebra K V) g.2 Nat.one_pos⟩ :
      (projectiveSpaceOfModule K V).affineOpens)) ?_ fun g => ?_
  · refine Proj.iSup_basicOpen_eq_top' (grading K V)
      (fun g : grading K V 1 => (g : SymmetricAlgebra K V)) (fun g => ⟨1, g.2⟩) ?_
    rw [show Set.range (fun g : grading K V 1 => (g : SymmetricAlgebra K V)) =
      (grading K V 1 : Set (SymmetricAlgebra K V)) from Subtype.range_coe]
    exact grading_generated_one K V
  · rw [quotientMap_kernel_on_chart K V rows g.2]
    simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    have hh (j : ι) : (hyperplane K V rows j).ideal
        ⟨Proj.basicOpen (grading K V) (g : SymmetricAlgebra K V),
          Proj.isAffineOpen_basicOpen (grading K V) (g : SymmetricAlgebra K V) g.2 Nat.one_pos⟩ =
        Ideal.span {(chartFraction (grading K V) g.2 1
          ⟨forms K V rows j, forms_homogeneous_one K V rows j⟩)} := by
      exact zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq (grading K V)
        g.2 Nat.one_pos 1 (by simp) ⟨forms K V rows j, forms_homogeneous_one K V rows j⟩
        (forms_homogeneous_one K V rows j)
    simp_rw [hh]
    exact Ideal.span_range_eq_iSup _

/-- Every native test scheme factors through the actual quotient
projective scheme exactly when its pulled linear equations vanish. -/
theorem factorsThrough_iff_sections_zero {T : Scheme.{u}}
    (f : T ⟶ projectiveSpaceOfModule K V) :
    (∃ g : T ⟶ projectiveSpaceOfModule K (V ⧸ constraints K V rows),
      g ≫ quotientMap K V (constraints K V rows) = f) ↔
    ∀ j : ι, pullbackGlobalSections f (twistingSheafModule (grading K V) (1 : ℤ))
      (degreeSection (grading K V) 1
        ⟨forms K V rows j, forms_homogeneous_one K V rows j⟩) = 0 := by
  let q := quotientMap K V (constraints K V rows)
  have hlift : (∃ g : T ⟶ projectiveSpaceOfModule K (V ⧸ constraints K V rows),
      g ≫ q = f) ↔ q.ker ≤ f.ker := by
    constructor
    · rintro ⟨g, hg⟩
      apply (factorsThrough_ideal_iff_ideal_le_ker q.ker f).mp
      refine ⟨g ≫ q.toImage, ?_⟩
      rw [Category.assoc, Scheme.Hom.toImage_imageι, hg]
    · intro h
      obtain ⟨g, hg⟩ := (factorsThrough_ideal_iff_ideal_le_ker q.ker f).mpr h
      refine ⟨g ≫ (asIso q.toImage).inv, ?_⟩
      rw [Category.assoc, LagrangianMatrixChart.asIso_toImage_inv_imageι]
      exact hg
  rw [hlift, quotientMap_kernel_eq_hyperplanes, iSup_le_iff]
  apply forall_congr'
  intro j
  exact (pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker
    (grading K V) f ⟨forms K V rows j, forms_homogeneous_one K V rows j⟩).symm

end M9Native.ProjectiveFiniteLinearSection
