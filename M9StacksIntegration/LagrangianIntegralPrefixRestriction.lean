module

public import M9StacksIntegration.LagrangianPrimitiveSystem
public import M9StacksIntegration.LagrangianPrimitiveRestriction
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom

/-! Mukai II, Lemma 4.2 for the literal original five determinant rows,
with genuine integral-prefix geometry as the only ladder input. The
kernel and nine-dimensional image are derived. Canonical surjectivity
then follows from the actual canonical-line iso and actual genus nine. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianIntegralPrefixRestriction

open LagrangianPrimitiveSystem

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

abbrev structuralMap (M : Matrix (Fin 5) (Fin 14) K) :
    (sectionCut K M).left ⟶ Spec (.of K) :=
  (sectionCut K M).hom ≫ LagrangianGrassmannian.projection K

theorem primitiveRestriction_kernel (M : Matrix (Fin 5) (Fin 14) K)
    (h : IntegralPrefixes K M) :
    LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (structuralMap K M) (sectionCut K M).hom) = Submodule.span K (Set.range M) := by
  rw [← sectionCut_kernel K M h]
  ext v
  rw [LinearMap.mem_ker,LagrangianPrimitiveRestriction.primitiveRestriction_ker_iff K _ _ rfl]
  change pullbackGlobalSections (sectionCut K M).hom (LagrangianPluckerQuotient.determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K v) = 0 ↔
    pullbackGlobalSections (sectionCut K M).hom (system K).L ((system K).sectionOf v) = 0
  rw [system_section]
  rfl

theorem primitiveRestriction_kernel_finrank (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (h : IntegralPrefixes K M) :
    finrank K (LinearMap.ker (LagrangianPrimitiveRestriction.primitiveRestriction K
      (structuralMap K M) (sectionCut K M).hom)) = 5 := by
  rw [primitiveRestriction_kernel K M h]
  have hr := (Matrix.mulVec_surjective_iff_rank_eq_card (M := M)).mp hM
  rw [Matrix.rank_eq_finrank_span_row] at hr
  exact hr

theorem primitiveRestriction_range_finrank (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (h : IntegralPrefixes K M) :
    finrank K (LinearMap.range (LagrangianPrimitiveRestriction.primitiveRestriction K
      (structuralMap K M) (sectionCut K M).hom)) = 9 := by
  have hd := (LagrangianPrimitiveRestriction.primitiveRestriction K
    (structuralMap K M) (sectionCut K M).hom).finrank_range_add_finrank_ker
  rw [primitiveRestriction_kernel_finrank K M hM h] at hd
  have h14 : finrank K (Fin 14 → K) = 14 := by simp
  rw [h14] at hd
  omega

theorem primitiveH0_span_finrank (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (h : IntegralPrefixes K M) :
    finrank K (Submodule.span K (Set.range
      (LagrangianPrimitiveRestriction.sectionH0 K (structuralMap K M) (sectionCut K M).hom))) = 9 := by
  rw [← LagrangianPrimitiveRestriction.primitiveRestriction_range]
  exact primitiveRestriction_range_finrank K M hM h

omit [IsAlgClosed K] in
instance sectionCut_proper (M : Matrix (Fin 5) (Fin 14) K) : IsProper (structuralMap K M) := by
  let : IsProper (LagrangianGrassmannian.projection K) :=
    isProper_of_isProjectiveMorphism _ (LagrangianPluckerClosed.isProjectiveMorphism_projection K)
  change IsProper ((sectionCut K M).hom ≫ LagrangianGrassmannian.projection K)
  let : IsClosedImmersion (sectionCut K M).hom :=
    IteratedLineSectionCuts.simultaneousCut_closed _ _
  infer_instance

theorem canonicalRestriction_kernel (M : Matrix (Fin 5) (Fin 14) K)
    (h : IntegralPrefixes K M)
    (c : LagrangianPrimitiveRestriction.restrictedLine K (sectionCut K M).hom ≅
      Stacks.Duality.dualizingSheafOverField (structuralMap K M)) :
    LinearMap.ker (LagrangianPrimitiveRestriction.canonicalRestriction K
      (structuralMap K M) (sectionCut K M).hom c) = Submodule.span K (Set.range M) := by
  rw [LagrangianPrimitiveRestriction.canonicalRestriction_kernel,primitiveRestriction_kernel K M h]

theorem canonicalRestriction_surjective (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (h : IntegralPrefixes K M)
    [IsCurve K (structuralMap K M)]
    (c : LagrangianPrimitiveRestriction.restrictedLine K (sectionCut K M).hom ≅
      Stacks.Duality.dualizingSheafOverField (structuralMap K M))
    (hg : genus (structuralMap K M) = 9) :
    Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K
      (structuralMap K M) (sectionCut K M).hom c) := by
  let F := LagrangianPrimitiveRestriction.canonicalRestriction K
    (structuralMap K M) (sectionCut K M).hom c
  have hk : finrank K (LinearMap.ker F) = 5 := by
    rw [LagrangianPrimitiveRestriction.canonicalRestriction_kernel]
    exact primitiveRestriction_kernel_finrank K M hM h
  have h9 : finrank K (cohomologyOverField K (structuralMap K M)
      (Stacks.Duality.dualizingSheafOverField (structuralMap K M)) 0) = 9 :=
    (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField
      (structuralMap K M) (IsCurve.topologicalKrullDim_eq_one (structuralMap K M)).le).trans hg
  let : FiniteDimensional K (cohomologyOverField K (structuralMap K M)
      (Stacks.Duality.dualizingSheafOverField (structuralMap K M)) 0) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  have hd := F.finrank_range_add_finrank_ker
  rw [hk] at hd
  have h14 : finrank K (Fin 14 → K) = 14 := by simp
  rw [h14] at hd
  have hr : finrank K (LinearMap.range F) = 9 := by omega
  exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq (hr.trans h9.symm))

end M9Native.LagrangianIntegralPrefixRestriction
end
