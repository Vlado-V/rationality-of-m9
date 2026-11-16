module

public import M9StacksIntegration.GrassmannianFieldBaseChange
public import M9StacksIntegration.LagrangianPluckerTrivialization
public import M9StacksIntegration.IteratedLineSectionCuts

/-! The genuine original LG zero scheme commutes with field base change.
The actual quotient classifiers identify the pulled universal quotients;
their actual exterior bivector vanishing gives the all-test comparison.
No base-change isomorphism or quotient frame is assumed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianGrassmannian M9Native.IteratedLineSectionCuts

universe u

namespace M9Native.LagrangianFieldBaseChange

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)

abbrev grassMap : grassmannian L ⟶ grassmannian K :=
  GrassmannianFieldBaseChange.map φ 3 6

theorem quotient_isomorphic {T : Scheme.{u}} (f : T ⟶ grassmannian L) :
    (pullbackPresentation (f ≫ grassMap φ) (universalQuotient K)).Isomorphic
      (pullbackPresentation f (universalQuotient L)) := by
  apply presentation_isomorphic_of_class_eq
  rw [pullbackUniversal_class K, pullbackUniversal_class L]
  rw [Category.assoc, GrassmannianFieldBaseChange.map_toIntegral]

theorem factorsThrough_iff {T : Scheme.{u}} (f : T ⟶ grassmannian L) :
    (∃ z : T ⟶ space L, z ≫ inclusion L = f) ↔
      (∃ z : T ⟶ space K, z ≫ inclusion K = f ≫ grassMap φ) := by
  rw [factorsThrough_iff_pullbackQuotient_annihilates L,
    factorsThrough_iff_pullbackQuotient_annihilates K]
  obtain ⟨e, he⟩ := quotient_isomorphic φ f
  exact (annihilatesSigma_iff_of_iso T _ _ e he).symm

abbrev preimage : Scheme.{u} := pullback (grassMap φ) (inclusion K)

theorem preimage_factorsThrough_iff {T : Scheme.{u}} (f : T ⟶ grassmannian L) :
    (∃ z : T ⟶ preimage φ, z ≫ pullback.fst (grassMap φ) (inclusion K) = f) ↔
      (∃ z : T ⟶ space K, z ≫ inclusion K = f ≫ grassMap φ) := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z ≫ pullback.snd _ _, ?_⟩
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hz]
  · rintro ⟨z, hz⟩
    exact ⟨pullback.lift f z hz.symm, pullback.lift_fst _ _ _⟩

def preimageIso : space L ≅ preimage φ := by
  let A : Over (grassmannian L) := Over.mk (inclusion L)
  let B : Over (grassmannian L) := Over.mk (pullback.fst (grassMap φ) (inclusion K))
  let : Mono A.hom := by change Mono (inclusion L); infer_instance
  let : Mono B.hom := by change Mono (pullback.fst (grassMap φ) (inclusion K)); infer_instance
  exact comparisonIso A B (fun T f =>
    (factorsThrough_iff φ f).trans (preimage_factorsThrough_iff φ f).symm)

@[reassoc (attr := simp)] theorem preimageIso_hom_fst :
    (preimageIso φ).hom ≫ pullback.fst (grassMap φ) (inclusion K) = inclusion L :=
  comparisonHom_comp (Over.mk (inclusion L))
    (Over.mk (pullback.fst (grassMap φ) (inclusion K)))
    (fun T f => (factorsThrough_iff φ f).trans (preimage_factorsThrough_iff φ f).symm)

def map : space L ⟶ space K := (preimageIso φ).hom ≫ pullback.snd _ _

@[reassoc (attr := simp)] theorem map_inclusion :
    map φ ≫ inclusion K = inclusion L ≫ grassMap φ := by
  rw [map, Category.assoc, ← pullback.condition, ← Category.assoc, preimageIso_hom_fst]

theorem inclusion_isPullback : IsPullback (inclusion L) (map φ) (grassMap φ) (inclusion K) :=
  IsPullback.of_iso_pullback ⟨(map_inclusion φ).symm⟩ (preimageIso φ)
    (preimageIso_hom_fst φ) rfl

theorem map_isPullback : IsPullback (map φ) (projection L) (projection K)
    (GrassmannianFieldBaseChange.specMap φ) :=
  (inclusion_isPullback φ).flip.paste_vert
    (GrassmannianFieldBaseChange.map_isPullback φ 3 6)

@[reassoc (attr := simp)] theorem map_projection :
    map φ ≫ projection K = projection L ≫ GrassmannianFieldBaseChange.specMap φ :=
  (map_isPullback φ).w

/-- The actual native LG over L is the actual base change of the original
LG over K, with both original projections retained. -/
def baseChangeIso : space L ≅ pullback (projection K) (GrassmannianFieldBaseChange.specMap φ) :=
  (map_isPullback φ).isoPullback

@[reassoc (attr := simp)] theorem baseChangeIso_hom_fst :
    (baseChangeIso φ).hom ≫ pullback.fst _ _ = map φ := IsPullback.isoPullback_hom_fst _

@[reassoc (attr := simp)] theorem baseChangeIso_hom_snd :
    (baseChangeIso φ).hom ≫ pullback.snd _ _ = projection L := IsPullback.isoPullback_hom_snd _

end M9Native.LagrangianFieldBaseChange
