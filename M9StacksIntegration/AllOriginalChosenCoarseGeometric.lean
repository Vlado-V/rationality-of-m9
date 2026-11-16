module

public import M9StacksIntegration.AllOriginalClassifierSurjectivity
public import M9StacksIntegration.GenusNineOriginalClassifierCoarseCompatibility
public import M9StacksIntegration.AllOriginalChosenCoarseGeometricFibres
public import M9StacksIntegration.AllOriginalChosenCoarseAffineAgreement

/-! The actual chosen coarse map is geometric on all original algebraically
closed extension fields. The full original classifier's bounded agreement
is the sole semantic input; native compatibility and all field lifting are
proved upstream, including families with nonschematic total space. -/

set_option autoImplicit false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Opposite

namespace M9Native.AllOriginalChosenCoarseGeometric
open M9StacksIntegration M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)
  (c : M9StandaloneDraft.Classifier K g
    ((originalPresheafFunctor K B hK).obj
      (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg)))
  (hB : ∀ (T : BigFppfOver B (Spec (.of K)) hK)
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g),
    c.value _ F = BoundedOriginalFamilyCoarseValue.originalValue B hZ K hK g hg F)

include hB in
/-- Surjectivity uses the actual native universal homeomorphism and the
proved original-classifier compatibility, with no field containment input. -/
theorem surjective_value (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    Function.Surjective (c.value (M9StandaloneDraft.FieldPoint K L)) :=
  M9StacksIntegration.AllOriginalClassifierSurjectivity.surjective_value K B hK g
    (GenusNineCoarseOverField.smoothStack B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal B hZ K hK g hg)
    (GenusNineOriginalFamilyFunctor.toOriginal_projection B hZ K hK g hg)
    (GenusNineCoarseOverField.coarseSpace B hZ K hK g hg) c
    (GenusNineCoarseOverField.coarseMap B hZ K hK g hg)
    (GenusNineCoarseOverField.coarseMap_universalHomeomorphism B hZ K hK g hg)
    (GenusNineOriginalClassifierCoarseCompatibility.comparisonIso B hZ K hK g hg c hB).hom L

include hB in
/-- The actual geometric coarse-moduli condition on ALL original field
families, preserving unpointed curve isomorphism and the original scalars. -/
theorem isGeometric : M9StandaloneDraft.IsGeometric K c := by
  intro L _ _ _
  refine ⟨surjective_value B hZ K hK g hg c hB L, ?_⟩
  intro F G
  exact AllOriginalChosenCoarseGeometricFibres.value_eq_iff_familyIsomorphic
    B hZ K hK g hg c hB L F G

/-- Surjectivity of the independently constructed full original classifier,
with its bounded agreement derived from the actual construction. -/
theorem classifier_surjective (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    Function.Surjective ((AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg).value
      (M9StandaloneDraft.FieldPoint K L)) :=
  surjective_value B hZ K hK g hg
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg)
    (fun T F => AllOriginalChosenCoarseAffineAgreement.classifier_value_bounded
      B hZ K hK g hg T F) L

/-- The actual full original classifier has exactly the genuine geometric
coarse-moduli property, without any classifier-comparison premise. -/
theorem classifier_isGeometric : M9StandaloneDraft.IsGeometric K
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg) :=
  isGeometric B hZ K hK g hg
    (AllOriginalChosenCoarseClassifier.classifier B hZ K hK g hg)
    (fun T F => AllOriginalChosenCoarseAffineAgreement.classifier_value_bounded
      B hZ K hK g hg T F)

end M9Native.AllOriginalChosenCoarseGeometric
