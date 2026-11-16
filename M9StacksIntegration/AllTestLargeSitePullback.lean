module

public import M9StacksIntegration.AllTestSiteCocontinuity
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Actual sheaf extension to every original test scheme

Values are in Type (u+1), so the actual full original site admits the
sheafification used here. The extension is the left adjoint to literal
restriction. It preserves finite limits, as proved by the filtered-colimit
description of left Kan extension; no equivalence-of-sites premise is used.

The two general Kan-extension proofs below are the proofs of Mathlib's
`Functor.lanEvaluationIsoColim` and `lan_preservesFiniteLimits_of_flat`,
with object and morphism universes separated. Their original SmallCategory
specialization does not apply directly to the original category of schemes.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeSitePullback
universe u

section GeneralKan
variable {C D : Type (u+1)} [Category.{u} C] [Category.{u} D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual left Kan extension is computed pointwise by its comma colimit. -/
def lanEvaluationIsoColim (F : C ⥤ D) (X : D) :
    (F.lan : (C ⥤ Type (u+1)) ⥤ (D ⥤ Type (u+1))) ⋙
        (evaluation D (Type (u+1))).obj X ≅
      (Functor.whiskeringLeft _ _ (Type (u+1))).obj
        (CostructuredArrow.proj F X) ⋙ colim :=
  NatIso.ofComponents (fun G =>
    IsColimit.coconePointUniqueUpToIso
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
      (colimit.isColimit _)) (fun {G₁ G₂} φ => by
    apply (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G₁ X).hom_ext
    intro T
    have h₁ := fun (G : C ⥤ Type (u+1)) =>
      IsColimit.comp_coconePointUniqueUpToIso_hom
        (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit F G X)
        (colimit.isColimit _) T
    have h₂ := congr_app (F.lanUnit.naturality φ) T.left
    dsimp at h₁ h₂ ⊢
    simp only [Category.assoc] at h₁ ⊢
    simp only [Functor.lan, Functor.lanUnit] at h₂ ⊢
    rw [reassoc_of% h₁, NatTrans.naturality_assoc, ← reassoc_of% h₂, h₁,
      ι_colimMap, Functor.whiskerLeft_app]
    rfl)

/-- Flat left Kan extension is left exact with the actual universe sizes. -/
theorem lan_preservesFiniteLimits_of_flat (F : C ⥤ D) [RepresentablyFlat F] :
    PreservesFiniteLimits (F.op.lan : (Cᵒᵖ ⥤ Type (u+1)) ⥤ Dᵒᵖ ⥤ Type (u+1)) := by
  apply preservesFiniteLimits_of_preservesFiniteLimitsOfSize.{u+1}
  intro J _ _
  apply preservesLimitsOfShape_of_evaluation
    (F.op.lan : (Cᵒᵖ ⥤ Type (u+1)) ⥤ Dᵒᵖ ⥤ Type (u+1)) J
  intro X
  have : IsFiltered (CostructuredArrow F.op X) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence F (unop X))
  exact preservesLimitsOfShape_of_natIso (lanEvaluationIsoColim F.op X).symm

end GeneralKan

open AllTestBoundedCharts AllTestBoundedRestriction
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The literal inclusion of bounded tests preserves finite limits. -/
theorem boundedInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (boundedInclusion B K hK) := by
  let : PreservesLimitsOfShape (Discrete.{0} PEmpty) (boundedInclusion B K hK) :=
    by
      have h : IsTerminal ((boundedInclusion B K hK).obj
          (⊤_ (BigFppfOver B (Spec (.of K)) hK))) :=
        IsTerminal.ofIso (Over.mkIdTerminal (X := Spec (.of K)))
          ((boundedInclusion B K hK).mapIso
            (terminalIsTerminal.uniqueUpToIso
              (isTerminal_mkId_bigFppfOver B (Spec (.of K)) hK))).symm
      have := preservesTerminal_of_iso (boundedInclusion B K hK)
        (h.uniqueUpToIso terminalIsTerminal)
      exact preservesLimitsOfShape_pempty_of_preservesTerminal _
  let : PreservesLimitsOfShape WalkingCospan (boundedInclusion B K hK) := by
    let : PreservesLimitsOfShape WalkingCospan
        (boundedInclusion B K hK ⋙ Over.forget (M9StandaloneDraft.Base K)) :=
      preservesPullbacks_bigFppfOverToScheme B (Spec (.of K)) hK
    exact preservesLimitsOfShape_of_reflects_of_preserves _
      (Over.forget (M9StandaloneDraft.Base K))
  exact preservesFiniteLimits_of_preservesTerminal_and_pullbacks _

/-- Genuine extension of large-valued native sheaves to the full original site. -/
def extendSheaf :
    Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type (u+1)) ⥤
      Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1)) :=
  (boundedInclusion B K hK).sheafPullback (Type (u+1))
    (BigFppfOver.topology B (Spec (.of K)) hK)
    (Scheme.fppfTopology.over (M9StandaloneDraft.Base K))

/-- The extension is adjoint to actual restriction on every original test. -/
def extendSheafAdjunction :
    extendSheaf K B hK ⊣ (boundedInclusion B K hK).sheafPushforwardContinuous
      (Type (u+1)) (BigFppfOver.topology B (Spec (.of K)) hK)
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) :=
  (boundedInclusion B K hK).sheafAdjunctionContinuous _ _ _

/-- The constructed extension preserves actual finite-limit diagrams. -/
theorem extendSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (extendSheaf K B hK) := by
  let : HasFiniteLimits (BigFppfOver B (Spec (.of K)) hK) :=
    hasFiniteLimits_of_hasTerminal_and_pullbacks
  let : PreservesFiniteLimits (boundedInclusion B K hK) :=
    boundedInclusion_preservesFiniteLimits K B hK
  let : RepresentablyFlat (boundedInclusion B K hK) := flat_of_preservesFiniteLimits _
  let : PreservesFiniteLimits ((boundedInclusion B K hK).op.lan :
      (_ ⥤ Type (u+1)) ⥤ _ ⥤ Type (u+1)) :=
    lan_preservesFiniteLimits_of_flat _
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

end M9StacksIntegration.AllTestLargeSitePullback
