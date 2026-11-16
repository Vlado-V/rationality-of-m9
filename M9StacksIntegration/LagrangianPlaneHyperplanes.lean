module

public import M9StacksIntegration.LagrangianProjectivePlaneKernel
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksFrontier.LinearAlgebra.SymmetricPower.DegreeOneGeneration

/-! The genuine native quotient plane is the scheme intersection of its
five actual degree-one hyperplanes. Its all-test factorization criterion
is actual vanishing of the five pulled twisted sections, including on
nonreduced schemes. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module TopologicalSpace
open AlgebraicGeometry.ProjectiveSpaceOfModule AlgebraicGeometry.ProjectiveSpectrum.Proj
open M9Native.LagrangianProjectiveIntersection M9Native.LagrangianProjectiveLinearForms
open M9Native.LagrangianProjectivePlaneKernel

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace M9Native.LagrangianPlaneHyperplanes

variable (K : Type u) [Field K]

theorem sourceGrading_generated_one :
    Algebra.adjoin (sourceGrading K 0)
      ((sourceGrading K 1 : Set (SymmetricAlgebra K (Forms K)))) = ⊤ :=
  SymmetricAlgebra.adjoin_symmetricPower_one_eq_top K (Forms K)

instance twistingLine_invertible : AlgebraicGeometry.SheafOfModules.IsInvertible
    (AlgebraicGeometry.Proj (sourceGrading K)).sheaf.obj
      (AlgebraicGeometry.Proj (sourceGrading K)).ringCatSheaf.property
    (twistingSheaf (sourceGrading K) (1 : ℤ)) :=
  algebraicGeometry_isInvertible_twistingSheaf (sourceGrading K)
    (sourceGrading_generated_one K) 1

variable (L : Coordinates K →ₗ[K] (Fin 5 → K))

def hyperplane (j : Fin 5) : (AlgebraicGeometry.Proj (sourceGrading K)).IdealSheafData :=
  zeroScheme (AlgebraicGeometry.Proj (sourceGrading K)) (twistingSheafModule (sourceGrading K) (1 : ℤ))
    (degreeSection (sourceGrading K) 1 ⟨fiveForms K L j, fiveForms_homogeneous_one K L j⟩)

/-- Equality of actual ideal sheaves, retaining the nonreduced scheme
structure of the intersection of the five actual hyperplanes. -/
theorem quotientMap_kernel_eq_hyperplanes :
    (quotientMap K (Forms K) (constraints K L)).ker = ⨆ j : Fin 5, hyperplane K L j := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun g : sourceGrading K 1 => (⟨Proj.basicOpen (sourceGrading K) (g : SymmetricAlgebra K (Forms K)),
      Proj.isAffineOpen_basicOpen (sourceGrading K) (g : SymmetricAlgebra K (Forms K)) g.2 Nat.one_pos⟩ :
      (AlgebraicGeometry.Proj (sourceGrading K)).affineOpens)) ?_ fun g => ?_
  · refine Proj.iSup_basicOpen_eq_top' (sourceGrading K)
      (fun g : sourceGrading K 1 => (g : SymmetricAlgebra K (Forms K))) (fun g => ⟨1, g.2⟩) ?_
    rw [show Set.range (fun g : sourceGrading K 1 => (g : SymmetricAlgebra K (Forms K))) =
      (sourceGrading K 1 : Set (SymmetricAlgebra K (Forms K))) from Subtype.range_coe]
    exact sourceGrading_generated_one K
  · rw [quotientMap_kernel_on_chart]
    simp only [Scheme.IdealSheafData.ideal_iSup, iSup_apply]
    have hh (j : Fin 5) : (hyperplane K L j).ideal
        ⟨Proj.basicOpen (sourceGrading K) (g : SymmetricAlgebra K (Forms K)),
          Proj.isAffineOpen_basicOpen (sourceGrading K) (g : SymmetricAlgebra K (Forms K)) g.2 Nat.one_pos⟩ =
        Ideal.span {(chartFraction (sourceGrading K) g.2 1
          ⟨fiveForms K L j, fiveForms_homogeneous_one K L j⟩)} := by
      exact zeroScheme_degreeSection_ideal_basicOpen_of_degree_eq (sourceGrading K)
        g.2 Nat.one_pos 1 (by simp) ⟨fiveForms K L j, fiveForms_homogeneous_one K L j⟩
        (fiveForms_homogeneous_one K L j)
    simp_rw [hh]
    exact Ideal.span_range_eq_iSup _

/-- The original closed plane represents vanishing of its five actual
twisted sections on every scheme, without a reducedness assumption. -/
theorem factorsThrough_iff_sections_zero {X : Scheme.{u}}
    (f : X ⟶ projectiveSpaceOfModule K (Forms K)) :
    (∃ g : X ⟶ projectiveSpaceOfModule K (Forms K ⧸ constraints K L),
      g ≫ quotientMap K (Forms K) (constraints K L) = f) ↔
    ∀ j : Fin 5, pullbackGlobalSections f (twistingSheafModule (sourceGrading K) (1 : ℤ))
      (degreeSection (sourceGrading K) 1
        ⟨fiveForms K L j, fiveForms_homogeneous_one K L j⟩) = 0 := by
  let q := quotientMap K (Forms K) (constraints K L)
  have hlift : (∃ g : X ⟶ projectiveSpaceOfModule K (Forms K ⧸ constraints K L),
      g ≫ q = f) ↔ q.ker ≤ f.ker := by
    constructor
    · rintro ⟨g, hg⟩
      apply (factorsThrough_ideal_iff_ideal_le_ker q.ker f).mp
      refine ⟨g ≫ q.toImage, ?_⟩
      rw [Category.assoc, Scheme.Hom.toImage_imageι, hg]
    · intro h
      obtain ⟨g, hg⟩ := (factorsThrough_ideal_iff_ideal_le_ker q.ker f).mpr h
      refine ⟨g ≫ (asIso q.toImage).inv, ?_⟩
      rw [Category.assoc, M9Native.LagrangianMatrixChart.asIso_toImage_inv_imageι]
      exact hg
  rw [hlift, quotientMap_kernel_eq_hyperplanes, iSup_le_iff]
  apply forall_congr'
  intro j
  exact (pullbackGlobalSections_degreeSection_eq_zero_iff_zeroScheme_le_ker
    (sourceGrading K) f ⟨fiveForms K L j, fiveForms_homogeneous_one K L j⟩).symm

end M9Native.LagrangianPlaneHyperplanes
