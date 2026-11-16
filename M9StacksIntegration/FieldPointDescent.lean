module

public import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Field-valued point detection and effective descent of field elements

Equality on every field-valued point detects equality in an actual
reduced algebra. Applied to the two actual tensor-square embeddings,
faithfully flat descent identifies the common element with an element
of the original ground field. The geometric application must prove the
field-point condition from its actual kernel-pair geometry.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace M9Native.FieldPointDescent

variable (F : Type u) [Field F]

/-- Actual residue-field points detect equality in a reduced algebra;
no algebraic closedness or finite-type hypothesis is required. -/
theorem eq_of_forall_field_points {A : Type v} [CommRing A] [Algebra F A]
    [IsReduced A] {a b : A}
    (h : ∀ (L : Type v) [Field L] [Algebra F L]
      (q : A →ₐ[F] L), q a = q b) : a = b := by
  apply sub_eq_zero.mp
  apply IsReduced.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro I hI
  let := hI
  let : Algebra F I.ResidueField :=
    ((algebraMap A I.ResidueField).comp (algebraMap F A)).toAlgebra
  let : IsScalarTower F A I.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let q : A →ₐ[F] I.ResidueField := IsScalarTower.toAlgHom F A I.ResidueField
  apply Ideal.algebraMap_residueField_eq_zero.mp
  change q (a - b) = 0
  rw [map_sub, h I.ResidueField q, sub_self]

/-- Equality of the two embeddings at all actual field-valued points
of the tensor square forces an element to descend to the ground field. -/
theorem mem_range_of_forall_field_embeddings {E : Type v} [Field E] [Algebra F E]
    [IsReduced (E ⊗[F] E)] [Module.FaithfullyFlat F E] {x : E}
    (h : ∀ (L : Type v) [Field L] [Algebra F L]
      (s t : E →ₐ[F] L), s x = t x) :
    x ∈ Set.range (algebraMap F E) := by
  have heq : (Algebra.TensorProduct.includeLeft : E →ₐ[F] E ⊗[F] E) x =
      (Algebra.TensorProduct.includeRight : E →ₐ[F] E ⊗[F] E) x := by
    apply eq_of_forall_field_points F
    intro L _ _ q
    exact h L (q.comp Algebra.TensorProduct.includeLeft)
      (q.comp Algebra.TensorProduct.includeRight)
  rw [← Algebra.IsEffective.eqLocus_includeLeft_includeRight
    (Algebra.IsEffective.of_faithfullyFlat F E)]
  exact heq

/-- The descent criterion is an equivalence, with both actual field
embeddings restricting to the same original ground-field structure. -/
theorem mem_range_iff_forall_field_embeddings {E : Type v} [Field E] [Algebra F E]
    [IsReduced (E ⊗[F] E)] [Module.FaithfullyFlat F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔
      ∀ (L : Type v) [Field L] [Algebra F L]
        (s t : E →ₐ[F] L), s x = t x := by
  constructor
  · rintro ⟨a, rfl⟩ L _ _ s t
    rw [s.commutes, t.commutes]
  · exact mem_range_of_forall_field_embeddings F

end M9Native.FieldPointDescent
