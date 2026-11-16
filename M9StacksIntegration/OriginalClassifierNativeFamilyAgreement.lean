module

public import M9StacksIntegration.AllTestNativeOriginalFamily
public import M9StacksIntegration.AllTestNativeFamilyFull

/-!
# Original classifier values from actual native family recovery

The actual recovery isomorphism and the specified native isomorphism
compose to an arrow over the identity of the original coefficient base.
Native fullness then produces a literal original family isomorphism on
all tests. Every original classifier carries that isomorphism to equality
by its identity-base Cartesian naturality, for an arbitrary target presheaf.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.OriginalClassifierNativeFamilyAgreement

open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily
  M9StacksIntegration.AllTestNativeOriginalFamily

section ClassifierValues

variable (K : Type u) [Field K] {g : ℕ}
  {M : M9StandaloneDraft.Presheaves K}
  {T : M9StandaloneDraft.Schemes K}

/-- Every full original classifier respects an actual original family
isomorphism, without a sheaf or geometric assumption on its target. -/
theorem classifier_value_of_familyIsomorphic
    (d : M9StandaloneDraft.Classifier K g M)
    {F G : M9StandaloneDraft.Family K T g}
    (hFG : M9StandaloneDraft.FamilyIsomorphic K F G) :
    d.value T F = d.value T G := by
  obtain ⟨e, he⟩ := hFG
  have hcart : IsPullback e.hom F.projection G.projection (yoneda.map (𝟙 T)) := by
    rw [(yoneda (C := M9StandaloneDraft.Schemes K)).map_id]
    exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  simpa using (d.naturality T T (𝟙 T) G F e.hom hcart).symm

end ClassifierValues

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (T : BigFppfOver B (Spec (.of K)) hK) (g : ℕ)
  (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
  (G : CurveFamily B hZ)
  (hbaseG : G.base = nativeBase B hZ K hK T)
  (hG : IsSmoothH0FamilyOfFibreGenus B hZ g G)
  (e : G ≅ nativeCurveFamily B hZ K hK F)

/-- The actual recovery arrow followed by the actual given native
isomorphism. No original comparison is supplied. -/
def nativeIdentityArrow :
    nativeCurveFamily B hZ K hK (originalFamily B hZ K hK T G hbaseG g hG) ⟶
      nativeCurveFamily B hZ K hK F :=
  (originalFamilyNativeIso B hZ K hK T G hbaseG g hG).hom ≫ e.hom

/-- The two specified base transports cancel, retaining the original
coefficient map literally. -/
theorem nativeIdentityArrow_baseMap
    (he : e.hom.baseMap = eqToHom hbaseG) :
    (nativeIdentityArrow B hZ K hK T g F G hbaseG hG e).baseMap =
      𝟙 (nativeBase B hZ K hK T) := by
  change (originalFamilyNativeIso B hZ K hK T G hbaseG g hG).hom.baseMap ≫
    e.hom.baseMap = _
  rw [originalFamilyNativeIso_baseMap B hZ K hK T G hbaseG g hG, he]
  simp

/-- Genuine native fullness turns the actual identity-base arrow into
the literal original family isomorphism, including nonschematic totals. -/
theorem recoveredFamilyIsomorphic
    (he : e.hom.baseMap = eqToHom hbaseG) :
    M9StandaloneDraft.FamilyIsomorphic K
      (originalFamily B hZ K hK T G hbaseG g hG) F := by
  apply (M9StacksIntegration.AllTestNativeFamilyFull.familyIsomorphic_iff_native_identity_arrow
    B hZ K hK (originalFamily B hZ K hK T G hbaseG g hG) F).mpr
  exact ⟨nativeIdentityArrow B hZ K hK T g F G hbaseG hG e,
    nativeIdentityArrow_baseMap B hZ K hK T g F G hbaseG hG e he⟩

/-- Any full original classifier has the SAME value on the recovered
actual native family and the specified original family. No classifier
comparison, sheaf, coarseness or desired value equality is a premise. -/
theorem classifier_value_recovered
    {M : M9StandaloneDraft.Presheaves K}
    (d : M9StandaloneDraft.Classifier K g M)
    (he : e.hom.baseMap = eqToHom hbaseG) :
    d.value ((boundedInclusion B K hK).obj T)
        (originalFamily B hZ K hK T G hbaseG g hG) =
      d.value ((boundedInclusion B K hK).obj T) F :=
  classifier_value_of_familyIsomorphic K d
    (recoveredFamilyIsomorphic B hZ K hK T g F G hbaseG hG e he)

end M9Native.OriginalClassifierNativeFamilyAgreement
