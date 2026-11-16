module

public import M9StacksIntegration.AllTestLargeMonoFlatDescent

/-!
# Unbounded original-test monomorphic descent

There is no selected native site in the theorem's hypotheses. A site is
chosen internally to contain the three actual original chart schemes and
the coefficient field, then the checked actual full-original-site descent
theorem applies. Every original test scheme remains in the conclusion.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestOriginalMonoFlatDescent
open AllTestBoundedCharts AllTestLargeSpaceSmallSections
universe u
variable (K : Type u) [Field K]

/-- Actual full-site monomorphic finite-type descent over one actual
original fppf cover, without a bounded-site or representation premise. -/
theorem isRepresentable_of_single_flat_chart
    {A : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (hA : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) A)
    (T U R : M9StandaloneDraft.Schemes K) (q : U ⟶ T) (r : R ⟶ U)
    (f : A ⟶ (largeYoneda K).obj T) [Mono f]
    (a : (largeYoneda K).obj R ⟶ A)
    (h : IsPullback a ((largeYoneda K).map r) f ((largeYoneda K).map q))
    (hqf : Flat q.left) (hqp : LocallyOfFinitePresentation q.left)
    (hqs : Surjective q.left) (hrm : Mono r.left) (hrl : LocallyOfFiniteType r.left) :
    A.IsRepresentable := by
  have hm : Mono f := inferInstance
  rcases T with ⟨T, ⟨⟨⟩⟩, Thom⟩
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  rcases R with ⟨R, ⟨⟨⟩⟩, Rhom⟩
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({Spec (.of K), T, U, R} : Set Scheme.{u})
  let hK := hB (Spec (.of K)) (by simp)
  let Tn := siteObject B (Spec (.of K)) hK (hB T (by simp)) Thom
  let Un := siteObject B (Spec (.of K)) hK (hB U (by simp)) Uhom
  let Rn := siteObject B (Spec (.of K)) hK (hB R (by simp)) Rhom
  let qn : Un ⟶ Tn := boundedPreimage B K hK q
  let rn : Rn ⟶ Un := boundedPreimage B K hK r
  let : Mono (f : A ⟶ (largeYoneda K).obj ((boundedInclusion B K hK).obj Tn)) := hm
  exact @AllTestLargeMonoFlatDescent.isRepresentable_of_single_flat_chart
    K _ B hK A hA Tn Un Rn qn rn f hm a h hqf hqp hqs hrm hrl

end M9StacksIntegration.AllTestOriginalMonoFlatDescent
