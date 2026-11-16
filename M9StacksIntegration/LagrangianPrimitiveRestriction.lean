module

public import M9StacksIntegration.LagrangianUniversalSections
public import M9StacksIntegration.LagrangianHyperplaneCoordinates

/-! The actual original fourteen-section restriction map into native
H0 of the restricted quotient determinant.  Its target may be transported
to the actual canonical line by an actual line isomorphism. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open scoped BigOperators

universe u

namespace M9Native.LagrangianPrimitiveRestriction

open LagrangianPluckerQuotient

variable {X : Scheme.{u}} (k : Type u) [Field k]
  (f : X ⟶ Spec (.of k)) (l : X ⟶ LagrangianGrassmannian.space k)

abbrev restrictedLine : X.Modules := (Scheme.Modules.pullback l).obj (determinantLine k)

def restrictedSection (i : Fin 14) : Γ(restrictedLine k l,⊤) :=
  pullbackGlobalSections l (determinantLine k) (primitiveSections k i)

def sectionH0 (i : Fin 14) : cohomologyOverField k f (restrictedLine k l) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).inv (restrictedSection k l i)

/-- Literal original fourteen coefficients, with the original native
cohomology and original structural scalar action. -/
def primitiveRestriction :
    (Fin 14 → k) →ₗ[k] cohomologyOverField k f (restrictedLine k l) 0 :=
  ∑ i : Fin 14, (LinearMap.proj i).smulRight (sectionH0 k f l i)

theorem primitiveRestriction_apply (v : Fin 14 → k) :
    primitiveRestriction k f l v = ∑ i : Fin 14, v i • sectionH0 k f l i := by
  simp only [primitiveRestriction,LinearMap.sum_apply,LinearMap.smulRight_apply,
    LinearMap.proj_apply]

theorem primitiveRestriction_basis (i : Fin 14) :
    primitiveRestriction k f l (Pi.single i 1) = sectionH0 k f l i := by
  classical
  simp [primitiveRestriction_apply,Pi.single_apply]

theorem primitiveRestriction_range :
    LinearMap.range (primitiveRestriction k f l) =
      Submodule.span k (Set.range (sectionH0 k f l)) := by
  have hm : primitiveRestriction k f l = Fintype.linearCombination k (sectionH0 k f l) := by
    apply LinearMap.ext
    intro v
    rw [primitiveRestriction_apply,Fintype.linearCombination_apply]
  rw [hm,Fintype.range_linearCombination]

theorem primitiveRestriction_sections (v : Fin 14 → k) :
    (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).hom
      (primitiveRestriction k f l v) =
        ∑ i : Fin 14, ExteriorEvaluation.baseRingMap k f (v i) • restrictedSection k l i := by
  have hscalar (a : k) (s : cohomologyOverField k f (restrictedLine k l) 0) :
      (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).hom (a • s) =
        ExteriorEvaluation.baseRingMap k f a •
          (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).hom s :=
    (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).hom.hom.map_smul a s
  rw [primitiveRestriction_apply,map_sum]
  simp only [hscalar,sectionH0,Iso.inv_hom_id_apply]

theorem coefficients (hl : l ≫ LagrangianGrassmannian.projection k = f) :
    l.appTop.hom.comp (LagrangianHyperplaneCoordinates.coefficientMap k) =
      ExteriorEvaluation.baseRingMap k f := by
  have h : l.appTop.hom.comp (LagrangianHyperplaneCoordinates.coefficientMap k) =
      LagrangianPlucker.coefficientMap k l := by
    simpa only [Category.comp_id,LagrangianHyperplaneCoordinates.coefficientMap] using
      (LagrangianPlucker.coefficientMap_comp k (𝟙 _) l).symm
  exact h.trans (LagrangianUniversalSections.coefficients k f l hl)

/-- Native H0/global-sections comparison recovers restriction of the
original actual determinant combination, rather than a new linear system. -/
theorem primitiveRestriction_sections_eq_pullback
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (v : Fin 14 → k) :
    (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).hom
      (primitiveRestriction k f l v) =
        pullbackGlobalSections l (determinantLine k)
          (LagrangianHyperplaneCoordinates.determinantSection k v) := by
  rw [primitiveRestriction_sections]
  simp only [LagrangianHyperplaneCoordinates.determinantSection,map_sum,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul]
  apply Finset.sum_congr rfl
  intro i _
  change ExteriorEvaluation.baseRingMap k f (v i) • restrictedSection k l i =
    l.appTop.hom (LagrangianHyperplaneCoordinates.coefficientMap k (v i)) •
      restrictedSection k l i
  exact congrArg (fun a : Γ(X,⊤) => a • restrictedSection k l i)
    (RingHom.congr_fun (coefficients k f l hl) (v i)).symm

/-- The exact zero criterion for the actual primitive restriction map. -/
theorem primitiveRestriction_ker_iff
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (v : Fin 14 → k) :
    primitiveRestriction k f l v = 0 ↔
      pullbackGlobalSections l (determinantLine k)
        (LagrangianHyperplaneCoordinates.determinantSection k v) = 0 := by
  rw [← primitiveRestriction_sections_eq_pullback k f l hl v]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (restrictedLine k l)).hom).injective).symm

section Canonical
variable [IsProper f]

/-- Transport to the genuine native canonical line uses the actual
cohomology functor applied to the actual line isomorphism. -/
def canonicalRestriction (c : restrictedLine k l ≅ Stacks.Duality.dualizingSheafOverField f) :
    (Fin 14 → k) →ₗ[k]
      cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0 :=
  (cohomologyOverFieldIso k f c 0).hom.hom.comp (primitiveRestriction k f l)

theorem canonicalRestriction_ker_iff
    (c : restrictedLine k l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (v : Fin 14 → k) :
    canonicalRestriction k f l c v = 0 ↔
      pullbackGlobalSections l (determinantLine k)
        (LagrangianHyperplaneCoordinates.determinantSection k v) = 0 := by
  change (cohomologyOverFieldIso k f c 0).hom (primitiveRestriction k f l v) = 0 ↔ _
  rw [map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldIso k f c 0).hom).injective]
  exact primitiveRestriction_ker_iff k f l hl v

theorem canonicalRestriction_kernel
    (c : restrictedLine k l ≅ Stacks.Duality.dualizingSheafOverField f) :
    LinearMap.ker (canonicalRestriction k f l c) =
      LinearMap.ker (primitiveRestriction k f l) := by
  ext v
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldIso k f c 0).hom).injective

end Canonical

end M9Native.LagrangianPrimitiveRestriction
end
