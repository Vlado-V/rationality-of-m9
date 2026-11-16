module

public import M9StacksIntegration.PrimitiveRadicalRestrictionFixed
public import M9StacksIntegration.PrimitiveRadicalStabilizerDescent

@[expose] public section

/-! The genuine global native radical/stabilizer invariant-field comparison.
Both fields are the fixed fields of the original native actions. The
equivalence preserves the two actual function-field embeddings into the
actual orbit-family source, rather than an arbitrary rational model. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.PrimitiveRadicalFixedFieldComparison
open PrimitiveRadicalInvariantDescent PrimitiveRadicalRestrictionFixed PrimitiveRadicalSliceField

theorem toStabilizerFixed_surjective : Function.Surjective toStabilizerFixed := by
  intro f
  obtain ⟨a,ha⟩ := PrimitiveRadicalStabilizerDescent.restriction_covers_stabilizer f
  exact ⟨a,Subtype.ext ha⟩

/-- Actual native Gr9(14)/Sp6 and the actual native reduced Gr4(12) stabilizer
quotient have canonically equivalent invariant function fields. -/
def nativeFixedEquiv : nativeFixedField ≃ₐ[ℂ] ReducedGraphTwistedAction.nativeHFixedField :=
  AlgEquiv.ofBijective toStabilizerFixed ⟨toStabilizerFixed.injective,toStabilizerFixed_surjective⟩

/-- The comparison is the genuine radical/fiber restriction: its two actual
pullbacks agree inside the original native orbit-family function field. -/
theorem nativeFixedEquiv_spec (f : nativeFixedField) :
    sliceEmbedding (nativeFixedEquiv f).val =
      PrimitiveRadicalOrbitDominance.functionFieldEmbedding f.val :=
  restriction_spec f

end M9Native.PrimitiveRadicalFixedFieldComparison
