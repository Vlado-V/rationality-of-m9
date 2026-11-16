module

public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Target naturality of the actual Proj morphism attached to global sections -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Stacks.ProjGlobalSectionsAppTop

universe u

namespace M9Native.MukaiProjSectionsNaturality

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  {X : Scheme.{u}} (ψ : 𝒜 →+*ᵍ ℬ) (f : B →+* Γ(X, ⊤))

theorem projAwayHom_comp {d : ℕ} {t : A} (ht : t ∈ 𝒜 d) :
    (projAwayHom ℬ f).comp (Away.map ψ t) = projAwayHom 𝒜 (f.comp ψ.toRingHom) := by
  apply away_ringHom_ext 𝒜 ht
  intro k p hp
  rw [RingHom.comp_apply,Away.map_mk,projAwayHom_apply_mk]
  exact (projAwayHom_apply_mk 𝒜 (f.comp ψ.toRingHom) ht k p hp).symm

private theorem chart_inclusion_factor {d : ℕ} {t : A} (hd : 0 < d) (ht : t ∈ 𝒜 d) :
    (Proj.basicOpen 𝒜 t).ι =
      (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom ≫ Proj.awayι 𝒜 t ht hd := by
  simp only [Proj.awayι,← Category.assoc,Iso.hom_inv_id,Category.id_comp]

/-- The actual global-sections Proj morphism is contravariantly natural in its graded target. -/
theorem fromOfGlobalSections_comp_map
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (hf : (HomogeneousIdeal.irrelevant ℬ).toIdeal.map f = ⊤)
    (hcomp : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (f.comp ψ.toRingHom) = ⊤) :
    Proj.fromOfGlobalSections ℬ f hf ≫ Proj.map ψ hψ =
      Proj.fromOfGlobalSections 𝒜 (f.comp ψ.toRingHom) hcomp := by
  apply (Proj.openCoverOfMapIrrelevantEqTop 𝒜 (f.comp ψ.toRingHom) hcomp).hom_ext
  rintro ⟨d,t,hd,ht⟩
  change (X.basicOpen (f (ψ t))).ι ≫ (Proj.fromOfGlobalSections ℬ f hf ≫ Proj.map ψ hψ) =
    (X.basicOpen (f (ψ t))).ι ≫ Proj.fromOfGlobalSections 𝒜 (f.comp ψ.toRingHom) hcomp
  rw [← Category.assoc]
  erw [ι_comp_fromOfGlobalSections ℬ f hf hd (ψ.map_mem ht),
    ι_comp_fromOfGlobalSections 𝒜 (f.comp ψ.toRingHom) hcomp hd ht]
  rw [chart_inclusion_factor ℬ hd (ψ.map_mem ht),Category.assoc,Category.assoc]
  erw [Proj.awayι_comp_map ψ hψ hd t ht]
  rw [← Category.assoc, toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom ℬ f hd (ψ.map_mem ht)]
  simp only [Category.assoc]
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom (projAwayHom ℬ f)))
    (Spec.map (CommRingCat.ofHom (Away.map ψ t))) (Proj.awayι 𝒜 t ht hd)]
  rw [← Spec.map_comp,← CommRingCat.ofHom_comp,projAwayHom_comp 𝒜 ℬ ψ f ht]
  rw [chart_inclusion_factor 𝒜 hd ht]
  rw [← Category.assoc (Proj.toBasicOpenOfGlobalSections 𝒜 (f.comp ψ.toRingHom) rfl hd ht)
    (Proj.basicOpenIsoSpec 𝒜 t ht hd).hom (Proj.awayι 𝒜 t ht hd)]
  erw [toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom 𝒜 (f.comp ψ.toRingHom) hd ht]
  simp only [Category.assoc]
  rfl

end M9Native.MukaiProjSectionsNaturality
