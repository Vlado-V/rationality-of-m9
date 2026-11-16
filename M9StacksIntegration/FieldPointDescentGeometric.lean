module

public import M9StacksIntegration.FieldPointDescentPerfect
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! The effective field descent criterion may be tested on genuinely
algebraically closed target fields, by the injective actual algebraic
closure map of every target field. -/

@[expose] public noncomputable section

universe u v

namespace M9Native.FieldPointDescent

variable (F : Type u) [Field F]

/-- Agreement of all pairs of embeddings into algebraically closed
fields implies agreement for embeddings into every field. -/
theorem embeddings_agree_of_algClosed_targets
    {E : Type v} [Field E] [Algebra F E] (x : E)
    (h : ∀ (L : Type v) [Field L] [IsAlgClosed L] [Algebra F L]
      (s t : E →ₐ[F] L), s x = t x)
    (L : Type v) [Field L] [Algebra F L] (s t : E →ₐ[F] L) : s x = t x := by
  let q : L →ₐ[F] AlgebraicClosure L := IsScalarTower.toAlgHom F L (AlgebraicClosure L)
  apply (algebraMap L (AlgebraicClosure L)).injective
  exact h (AlgebraicClosure L) (q.comp s) (q.comp t)

/-- Geometric field-valued points detect precisely the original ground
field inside every extension of a perfect field. -/
theorem mem_range_iff_forall_algClosed_embeddings_of_perfect
    [PerfectField F] {E : Type v} [Field E] [Algebra F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔
      ∀ (L : Type v) [Field L] [IsAlgClosed L] [Algebra F L]
        (s t : E →ₐ[F] L), s x = t x := by
  constructor
  · rintro ⟨a, rfl⟩ L _ _ _ s t
    rw [s.commutes, t.commutes]
  · intro h
    apply (mem_range_iff_forall_field_embeddings_of_perfect F x).2
    intro L _ _ s t
    exact embeddings_agree_of_algClosed_targets F x h L s t

/-- In characteristic zero the geometric test has no additional
separability, tensor-reducedness or finite-type premise. -/
theorem mem_range_iff_forall_algClosed_embeddings_charZero
    [CharZero F] {E : Type v} [Field E] [Algebra F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔
      ∀ (L : Type v) [Field L] [IsAlgClosed L] [Algebra F L]
        (s t : E →ₐ[F] L), s x = t x :=
  mem_range_iff_forall_algClosed_embeddings_of_perfect F x

end M9Native.FieldPointDescent
