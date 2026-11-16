module

public import M9StacksIntegration.ConicNativeOddFramedEquivariance
public import M9StacksIntegration.ConicFramedFullFixedField

/-! Exact invariant-field comparison for the original native reduced
Grassmannian. The map is the literal moving-frame inclusion, restricted
using the proved original native stabilizer action and actual deck image. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

open scoped Classical

namespace M9Native.ConicNativeFullFixedField

open M9.GraphBundleDescent
open ConicCompatibleTwistedAction ConicNativeOddFramedEquivariance

abbrev TwistedField := ConicCompatibleTwistedAction.twistedHFixedField
abbrev FramedField := ConicFramedFullFixedField.fullField
abbrev NativeField := ReducedGraphTwistedAction.nativeHFixedField

theorem embedding_mem_fullField (f : TwistedField) :
    ConicFramedGraphField.embedding f.val ∈ FramedField := by
  have hf := (mem_twistedHFixedField_iff_framed f.val).mp f.property
  apply (ConicFramedFullFixedField.mem_fullField _).mpr
  refine ⟨(ConicFramedEvenFixedField.mem_jointField _).mpr ⟨hf.1, ?_⟩, hf.2⟩
  exact (ConicFramedGraphField.embedding_image_iff _).mp ⟨f.val, rfl⟩

/-- The original native twisted fixed field is included by the actual
framed graph map, rather than by an arbitrary rational isomorphism. -/
def toFull : TwistedField →ₐ[ℂ] FramedField where
  toFun f := ⟨ConicFramedGraphField.embedding f.val, embedding_mem_fullField f⟩
  map_zero' := Subtype.ext (map_zero ConicFramedGraphField.embedding)
  map_one' := Subtype.ext (map_one ConicFramedGraphField.embedding)
  map_add' f g := Subtype.ext (map_add ConicFramedGraphField.embedding f.val g.val)
  map_mul' f g := Subtype.ext (map_mul ConicFramedGraphField.embedding f.val g.val)
  commutes' c := Subtype.ext (ConicFramedGraphField.embedding.commutes c)

theorem toFull_coe (f : TwistedField) :
    (toFull f).val = ConicFramedGraphField.embedding f.val := rfl

theorem toFull_surjective : Function.Surjective toFull := by
  intro z
  have hz := (ConicFramedFullFixedField.mem_fullField z.val).mp z.property
  have hj := (ConicFramedEvenFixedField.mem_jointField z.val).mp hz.1
  obtain ⟨f, hf⟩ := (ConicFramedGraphField.embedding_image_iff z.val).mpr hj.2
  have hfixed : f ∈ ConicCompatibleTwistedAction.twistedHFixedField := by
    apply (mem_twistedHFixedField_iff_framed f).mpr
    constructor
    · intro g
      rw [hf]
      exact hj.1 g
    · rw [hf]
      exact hz.2
  refine ⟨⟨f, hfixed⟩, ?_⟩
  exact Subtype.ext hf

/-- The exact native determinant-twisted stabilizer field and literal
framed full fixed field are isomorphic by their original inclusion. -/
def twistedFullEquiv : TwistedField ≃ₐ[ℂ] FramedField :=
  AlgEquiv.ofBijective toFull ⟨toFull.injective, toFull_surjective⟩

theorem twistedFullEquiv_coe (f : TwistedField) :
    (twistedFullEquiv f).val = ConicFramedGraphField.embedding f.val := rfl

/-- Exact comparison from the original native Gr4(12) full SL3 semidirect
C2 fixed field, retaining its proved basis change and central quotient. -/
def nativeFullEquiv : NativeField ≃ₐ[ℂ] FramedField :=
  ConicCompatibleTwistedAction.originalNativeFullFixedEquiv.trans twistedFullEquiv

theorem nativeFullEquiv_coe (f : NativeField) :
    (nativeFullEquiv f).val = ConicFramedGraphField.embedding
      (ConicCompatibleTwistedAction.originalNativeFullFixedEquiv f).val := rfl

/-- The actual original reduced-Grassmannian full stabilizer invariant
field is rational of dimension twenty-four over the original complex field. -/
def rationalEquiv : NativeField ≃ₐ[ℂ] M9.RationalField ℂ 24 :=
  nativeFullEquiv.trans ConicFramedFullFixedField.rationalEquiv

end M9Native.ConicNativeFullFixedField
