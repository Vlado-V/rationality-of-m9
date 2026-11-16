module

public import M9StacksIntegration.AllOriginalChosenCoarseClassifier
public import M9StacksIntegration.BoundedAffineFamilyValueAgreement

/-!
# The actual all-original classifier agrees with the actual bounded values

For a bounded affine base, its canonical spectrum over the original field
belongs to the same native site by the actual scheme isomorphism. The
actual spectrum agreement and the two genuine Cartesian naturality laws
then give agreement on that entire affine base. The checked affine-cover
descent theorem extends this to every bounded base. Original families with
nonschematic total algebraic spaces are retained throughout.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9Native.AllOriginalChosenCoarseAffineAgreement
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestSpecToAffineFamilyValues
  M9StacksIntegration.AllTestFamilyPullback
  M9StacksIntegration.AllTestOriginalFamilyCategory

universe u

section CanonicalSpectrum
variable (B : BigFppfSite.{u}) (K : Type u) [Field K]
  (hK : B.Contains (Spec (.of K)))
  (T : BigFppfOver B (Spec (.of K)) hK)
  (hT : IsAffine ((boundedInclusion B K hK).obj T).left)

include hT in
/-- The canonical spectrum is contained because it is the SAME affine base
up to an actual original-field scheme isomorphism. -/
theorem contains_canonicalSpectrum :
    B.Contains (Spec (.of Γ(((boundedInclusion B K hK).obj T).left, ⊤))) := by
  let S := (boundedInclusion B K hK).obj T
  let : Algebra K Γ(S.left, ⊤) := canonicalAlgebra K S hT
  let e := canonicalSpecIso K S hT
  exact (Scheme.size_congr ((Over.forget (M9StandaloneDraft.Base K)).mapIso e)).trans_lt
    T.left.property

/-- The actual native spectrum with its DERIVED original K-algebra structure. -/
def canonicalSpectrumObject : BigFppfOver B (Spec (.of K)) hK := by
  let S := (boundedInclusion B K hK).obj T
  letI : Algebra K Γ(S.left, ⊤) := canonicalAlgebra K S hT
  exact siteObject B (Spec (.of K)) hK (contains_canonicalSpectrum B K hK T hT)
    (Spec.map (CommRingCat.ofHom (algebraMap K Γ(S.left, ⊤))))

/-- Its original image is the literal spectrum with that actual K-structure. -/
theorem canonicalSpectrumObject_original :
    letI : Algebra K Γ(((boundedInclusion B K hK).obj T).left, ⊤) :=
      canonicalAlgebra K ((boundedInclusion B K hK).obj T) hT
    (boundedInclusion B K hK).obj (canonicalSpectrumObject B K hK T hT) =
      specOverK K Γ(((boundedInclusion B K hK).obj T).left, ⊤) := rfl

/-- The actual canonical over-K map is an actual native base arrow. -/
def canonicalSpectrumMap : canonicalSpectrumObject B K hK T hT ⟶ T := by
  let S := (boundedInclusion B K hK).obj T
  letI : Algebra K Γ(S.left, ⊤) := canonicalAlgebra K S hT
  exact boundedPreimage B K hK (canonicalSpecIso K S hT).hom

/-- No base-map comparison is supplied: the native arrow retains the
literal original canonical spectrum map by construction. -/
theorem canonicalSpectrumMap_original :
    letI : Algebra K Γ(((boundedInclusion B K hK).obj T).left, ⊤) :=
      canonicalAlgebra K ((boundedInclusion B K hK).obj T) hT
    (boundedInclusion B K hK).map (canonicalSpectrumMap B K hK T hT) =
      (canonicalSpecIso K ((boundedInclusion B K hK).obj T) hT).hom := rfl

end CanonicalSpectrum

section ActualAgreement
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K))) (g : ℕ) (hg : 2 ≤ g)

/-- The ACTUAL constructed full classifier equals the literal ACTUAL native
bounded value on every affine bounded base and every original family. -/
theorem classifier_value_affine
    (T : BigFppfOver B (Spec (.of K)) hK)
    (hT : IsAffine ((boundedInclusion B K hK).obj T).left)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).value
        ((boundedInclusion B K hK).obj T) F =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F := by
  let S := (boundedInclusion B K hK).obj T
  let M := (AllOriginalChosenCoarseClassifier.space B hZ K hK g hg).obj
  let : Algebra K Γ(S.left, ⊤) := canonicalAlgebra K S hT
  let e := canonicalSpecIso K S hT
  let TA := canonicalSpectrumObject B K hK T hT
  let a : TA ⟶ T := canonicalSpectrumMap B K hK T hT
  let FΓ := pullbackFamily K F e.hom
  let p := pullbackMap K g (⟨S, F⟩ : CurveObject K g) e.hom
  have hc : M.map e.hom.op
      ((AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).value S F) =
      (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).value
        (specOverK K Γ(S.left, ⊤)) FΓ :=
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).naturality
      S (specOverK K Γ(S.left, ⊤)) e.hom F FΓ p.totalMap p.cartesian
  have hs : (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).value
      (specOverK K Γ(S.left, ⊤)) FΓ =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg (T := TA) FΓ :=
    (AllOriginalChosenCoarseClassifier.classifier_value_spec B hZ K hK g hg
      Γ(S.left, ⊤) FΓ).trans
        (RelativeOriginalFamilyCoarseValue.valueSpec_eq_originalValue B hZ K hK g hg
          Γ(S.left, ⊤) (contains_canonicalSpectrum B K hK T hT) FΓ)
  have hb : M.map e.hom.op
      (BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F) =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg (T := TA) FΓ :=
    BoundedOriginalFamilyCoarseValue.originalValue_naturality B hZ K hK g hg
      (U := TA) (T := T) a F FΓ p.totalMap p.cartesian
  have he := hc.trans (hs.trans hb.symm)
  have hi := congrArg (M.map e.inv.op) he
  simpa only [← Functor.map_comp_apply, ← op_comp, e.inv_hom_id, op_id, M.map_id,
    types_id_apply] using hi

/-- Actual affine agreement and actual bounded Cartesian naturality give
the literal agreement on EVERY bounded base, with no affineness premise. -/
theorem classifier_value_bounded
    (T : BigFppfOver B (Spec (.of K)) hK)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).value
        ((boundedInclusion B K hK).obj T) F =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F :=
  BoundedAffineFamilyValueAgreement.bounded_value_agreement_of_affine B K hK g
    (AllOriginalChosenCoarseClassifier.space B hZ K hK g hg).isSheaf
    (fun T F => BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg (T := T) F)
    (fun T U a F G r hcart =>
      BoundedOriginalFamilyCoarseValue.originalValue_naturality B hZ K hK g hg
        (T := T) (U := U) a F G r hcart)
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg)
    (classifier_value_affine B hZ K hK g hg) T F

end ActualAgreement
end M9Native.AllOriginalChosenCoarseAffineAgreement
