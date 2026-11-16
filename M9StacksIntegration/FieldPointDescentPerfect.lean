module

public import M9StacksIntegration.FieldPointDescent
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

/-! Over a perfect field the genuine tensor-square reducedness and
faithful flatness conditions in field-point descent are automatic. -/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v

namespace M9Native.FieldPointDescent

variable (F : Type u) [Field F]

/-- In every field extension of a perfect field, an element descends
exactly when all pairs of actual field embeddings agree on it. -/
theorem mem_range_iff_forall_field_embeddings_of_perfect
    [PerfectField F] {E : Type v} [Field E] [Algebra F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔
      ∀ (L : Type v) [Field L] [Algebra F L]
        (s t : E →ₐ[F] L), s x = t x := by
  let : Module.Free F E := Module.Free.of_divisionRing F E
  let : Module.FaithfullyFlat F E := inferInstance
  let : IsReduced (E ⊗[F] E) :=
    Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      (Or.inl (Algebra.isSeparableExtension_of_perfectField F E))
  exact mem_range_iff_forall_field_embeddings F x

/-- In characteristic zero no separate tensor-reducedness, separability,
finite-type, or faithful-flatness premise is needed for this criterion. -/
theorem mem_range_iff_forall_field_embeddings_charZero
    [CharZero F] {E : Type v} [Field E] [Algebra F E] (x : E) :
    x ∈ Set.range (algebraMap F E) ↔
      ∀ (L : Type v) [Field L] [Algebra F L]
        (s t : E →ₐ[F] L), s x = t x :=
  mem_range_iff_forall_field_embeddings_of_perfect F x

end M9Native.FieldPointDescent
