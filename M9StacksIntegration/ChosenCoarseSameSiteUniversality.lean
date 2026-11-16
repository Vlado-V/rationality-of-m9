module

public import M9StacksIntegration.GenusNineOriginalClassifierCoarseCompatibility
public import M9StacksIntegration.GenusNineCoarseCategoricalFactorization
public import M9StacksIntegration.OriginalClassifierNativeFamilyAgreement
public import M9StacksIntegration.AllTestClassifierBoundedExt

/-!
# Same-site universality of the actual chosen original coarse classifier

The native factor is constructed from the actual categorical coarse map.
Actual restriction compatibility and the actual source recovery give its
equations on all original families with bounded bases. Genuine finite-stage
classifier extension gives the equations on every original family.
Full faithfulness of the same-site original-space functor and native
categorical uniqueness give uniqueness against every original presheaf map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u

namespace M9Native.ChosenCoarseSameSiteUniversality

open M9StacksIntegration M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily
  M9StacksIntegration.AllTestNativeOriginalFunctor

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)

/-- The literal original presheaf of the independently chosen native coarse space. -/
abbrev originalCoarse : M9StandaloneDraft.Presheaves K :=
  (originalPresheafFunctor K B hK).obj
    (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)

/-- The actual original target is a sheaf; no target property is supplied. -/
theorem originalTarget_isSheaf (W : AlgebraicSpaces B (Spec (.of K)) hK) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K))
      ((originalPresheafFunctor K B hK).obj W) :=
  (M9StacksIntegration.AllTestNativeOriginalSpace.originalSpaceOfNative
    K B hK W.obj W.property).isSheaf

/-- The native factor is produced by actual coarse universality on the
actual restriction of the original classifier. -/
def nativeFactor (W : AlgebraicSpaces B (Spec (.of K)) hK)
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj W)) :
    GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W :=
  GenusNineCoarseCategoricalFactorization.factorMap B hZ K hK g hg W
    (GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg W d)

/-- The same actual factor, as a map on all original tests. -/
def factor (W : AlgebraicSpaces B (Spec (.of K)) hK)
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj W)) :
    originalCoarse B hZ K hK g hg ⟶ (originalPresheafFunctor K B hK).obj W :=
  (originalPresheafFunctor K B hK).map (nativeFactor B hZ K hK g hg W d)

/-- The actual original family at an actual chosen-source object. -/
abbrev sourceFamily
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    AllTestOriginalFamilyCategory.CurveObject K g :=
  (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg).obj x

/-- Actual forward recovery and native fullness recover every original
classifier value at the actual source object of every bounded family. -/
theorem sourceObject_value_recovery {P : M9StandaloneDraft.Presheaves K}
    (a : M9StandaloneDraft.Classifier K g P)
    {T : BigFppfOver B (Spec (.of K)) hK}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    a.value
        (sourceFamily B hZ K hK g hg
          (BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg F)).base
        (sourceFamily B hZ K hK g hg
          (BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg F)).family =
      a.value ((boundedInclusion B K hK).obj T) F :=
  OriginalClassifierNativeFamilyAgreement.classifier_value_recovered B hZ K hK T g F
    ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
      (BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg F))
    (BoundedOriginalFamilyCoarseRecovery.sourceObject_original_base B hZ K hK g hg F)
    (BoundedOriginalFamilyCoarseRecovery.sourceObject_original_membership B hZ K hK g hg F)
    (BoundedOriginalFamilyCoarseRecovery.sourceObject_originalIso B hZ K hK g hg F) a
    (BoundedOriginalFamilyCoarseRecovery.sourceObject_originalIso_baseMap B hZ K hK g hg F)

/-- The genuine native factor satisfies its actual target's native values. -/
theorem nativeFactor_sections (W : AlgebraicSpaces B (Spec (.of K)) hK)
    (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj W))
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    (nativeFactor B hZ K hK g hg W d).hom.app
        (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x))
        (GenusNineCoarseCategoricalFactorization.coarseValue B hZ K hK g hg x) =
      GenusNineOriginalClassifierNativeRestriction.nativeValue B hZ K hK g hg W d x :=
  (GenusNineCoarseCategoricalFactorization.factorization_sections B hZ K hK g hg W
    (GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg W d) x).trans
      (GenusNineOriginalClassifierNativeRestriction.classifier_namedValue B hZ K hK g hg W d x)

variable
  (c : M9StandaloneDraft.Classifier K g (originalCoarse B hZ K hK g hg))
  (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
    c.value ((boundedInclusion B K hK).obj T) F =
      BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F)

include hB

/-- Actual bounded agreement derives compatibility with the same chosen
coarse functor, rather than assuming a native compatibility isomorphism. -/
theorem restrictedCoarseValue_eq
    (x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj) :
    GenusNineOriginalClassifierNativeRestriction.nativeValue B hZ K hK g hg
        (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c x =
      GenusNineCoarseCategoricalFactorization.coarseValue B hZ K hK g hg x :=
  (GenusNineOriginalClassifierNativeRestriction.classifier_namedValue B hZ K hK g hg
    (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c x).symm.trans
      (GenusNineOriginalClassifierCoarseCompatibility.classifier_namedValue_eq
        B hZ K hK g hg c hB x)

variable (W : AlgebraicSpaces B (Spec (.of K)) hK)
  (d : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj W))

/-- Restriction reflection gives actual original equations on every
actual family constructed from the chosen source. -/
theorem factor_source :
    ∀ x : (GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj,
      (factor B hZ K hK g hg W d).app (op (sourceFamily B hZ K hK g hg x).base)
          (c.value (sourceFamily B hZ K hK g hg x).base
            (sourceFamily B hZ K hK g hg x).family) =
        d.value (sourceFamily B hZ K hK g hg x).base
          (sourceFamily B hZ K hK g hg x).family := by
  apply (GenusNineOriginalClassifierNativeRestriction.nativeValue_factorization_iff
    B hZ K hK g hg W d (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c
    (nativeFactor B hZ K hK g hg W d)).mp
  intro x
  exact (congrArg
    ((nativeFactor B hZ K hK g hg W d).hom.app
      (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)))
    (restrictedCoarseValue_eq B hZ K hK g hg c hB x)).trans
      (nativeFactor_sections B hZ K hK g hg W d x)

/-- Actual source-object recovery gives factorization on ALL original
families over bounded bases, including nonschematic total spaces. -/
theorem factor_bounded (T : BigFppfOver B (Spec (.of K)) hK)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (factor B hZ K hK g hg W d).app (op ((boundedInclusion B K hK).obj T))
        (c.value ((boundedInclusion B K hK).obj T) F) =
      d.value ((boundedInclusion B K hK).obj T) F := by
  have hs := factor_source B hZ K hK g hg c hB W d
    (BoundedOriginalFamilyCoarseValue.sourceObject B hZ K hK g hg F)
  exact ((congrArg ((factor B hZ K hK g hg W d).app
      (op ((boundedInclusion B K hK).obj T)))
    (sourceObject_value_recovery B hZ K hK g hg c F)).symm.trans hs).trans
      (sourceObject_value_recovery B hZ K hK g hg d F)

/-- Genuine finite-stage classifier extension proves the full original
classifier factorization, with no bound on the other tests. -/
theorem factorization_classifier :
    OriginalClassifierNativeCompatibility.postcompose K g c
      (factor B hZ K hK g hg W d) = d :=
  AllTestClassifierBoundedExt.classifier_ext_of_bounded K B hK g
    (originalTarget_isSheaf B K hK W)
    (OriginalClassifierNativeCompatibility.postcompose K g c (factor B hZ K hK g hg W d)) d
    (factor_bounded B hZ K hK g hg c hB W d)

/-- The derived factor satisfies its value equation on EVERY original
base and EVERY original family, not only native bounded tests. -/
theorem factorization_all
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g) :
    (factor B hZ K hK g hg W d).app (op T) (c.value T F) = d.value T F :=
  congrArg (fun a : M9StandaloneDraft.Classifier K g
    ((originalPresheafFunctor K B hK).obj W) => a.value T F)
      (factorization_classifier B hZ K hK g hg c hB W d)

/-- Native uniqueness is detected by the literal all-original equations,
using actual restriction compatibility and the native section criterion. -/
theorem nativeFactor_unique
    (p : GenusNineCoarseOverField.coarseSpace B hZ K hK g hg ⟶ W)
    (hp : ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
      ((originalPresheafFunctor K B hK).map p).app (op T) (c.value T F) = d.value T F) :
    p = nativeFactor B hZ K hK g hg W d := by
  apply (GenusNineCoarseCategoricalFactorization.factorMap_eq_iff_sections
    B hZ K hK g hg W
    (GenusNineOriginalClassifierNativeRestriction.classifier B hZ K hK g hg W d) p).mpr
  have hn := (GenusNineOriginalClassifierNativeRestriction.nativeValue_factorization_iff
    B hZ K hK g hg W d (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c p).mpr
      (fun x => hp (sourceFamily B hZ K hK g hg x).base
        (sourceFamily B hZ K hK g hg x).family)
  intro x
  exact (congrArg (p.hom.app
      (op ((GenusNineOriginalFamilyFunctor.baseProjection B hZ K hK g hg).obj x)))
    (restrictedCoarseValue_eq B hZ K hK g hg c hB x).symm).trans
      ((hn x).trans
        (GenusNineOriginalClassifierNativeRestriction.classifier_namedValue
          B hZ K hK g hg W d x).symm)

/-- Every arbitrary original map between the SAME-SITE original spaces
has a genuine native preimage. Native uniqueness therefore proves
uniqueness against all original presheaf maps. -/
theorem factor_unique
    (q : originalCoarse B hZ K hK g hg ⟶ (originalPresheafFunctor K B hK).obj W)
    (hq : ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
      q.app (op T) (c.value T F) = d.value T F) :
    q = factor B hZ K hK g hg W d := by
  let p := (originalPresheafFullyFaithful K B hK).preimage q
  have hmap : (originalPresheafFunctor K B hK).map p = q :=
    (originalPresheafFullyFaithful K B hK).map_preimage q
  have hp : ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
      ((originalPresheafFunctor K B hK).map p).app (op T) (c.value T F) = d.value T F := by
    intro T F
    exact (congrArg (fun f => f.app (op T) (c.value T F)) hmap).trans (hq T F)
  exact hmap.symm.trans (congrArg (fun p => (originalPresheafFunctor K B hK).map p)
    (nativeFactor_unique B hZ K hK g hg c hB W d p hp))

/-- The actual chosen original coarse classifier is universal against
every SAME-SITE native target's actual original space, on ALL original
families. No compatibility isomorphism, native factorization or
categorical-moduli conclusion is supplied as an input. -/
theorem existsUnique_factor :
    ∃! q : originalCoarse B hZ K hK g hg ⟶ (originalPresheafFunctor K B hK).obj W,
      ∀ (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g),
        q.app (op T) (c.value T F) = d.value T F :=
  ⟨factor B hZ K hK g hg W d, factorization_all B hZ K hK g hg c hB W d,
    factor_unique B hZ K hK g hg c hB W d⟩

end M9Native.ChosenCoarseSameSiteUniversality
