module

public import M9StacksIntegration.StandaloneModuliDraft

/-! Affine common-open geometry under a genuine isomorphism of bases, in
one unchanged scheme universe. The physical common-open source is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9Native.StandaloneAffineCoefficientTransport

universe u

variable {K L : Type u} [Field K] [Field L]

/-- The actual affine-space isomorphism induced by an isomorphism of its
original base schemes, with the original coordinate index retained. -/
def affineIso (n : ℕ) (e : M9StandaloneDraft.Base K ≅ M9StandaloneDraft.Base L) :
    AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base K) ≅
      AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base L) where
  hom := AffineSpace.map _ e.hom
  inv := AffineSpace.map _ e.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, e.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, e.inv_hom_id, AffineSpace.map_id]

/-- Relabel the base of the actual affine chart without replacing its
physical source scheme. -/
def chart (n : ℕ) (e : M9StandaloneDraft.Base K ≅ M9StandaloneDraft.Base L)
    {U : M9StandaloneDraft.Schemes K}
    (a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base K)) :
    U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base L) :=
  a ≫ (affineIso n e).hom

/-- The same original structure map is transported by the specified base
isomorphism, rather than by a supplied coefficient identification. -/
theorem chart_over (n : ℕ) (e : M9StandaloneDraft.Base K ≅ M9StandaloneDraft.Base L)
    {U : M9StandaloneDraft.Schemes K}
    (a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base K))
    (ha : a ≫ pullback.fst _ _ = U.hom) :
    chart n e a ≫ pullback.fst _ _ = ((Over.map e.hom).obj U).hom := by
  change (a ≫ AffineSpace.map _ e.hom) ≫ pullback.fst _ _ = U.hom ≫ e.hom
  rw [Category.assoc]
  erw [AffineSpace.map_over]
  rw [← Category.assoc]
  exact congrArg (fun f : U.left ⟶ M9StandaloneDraft.Base K => f ≫ e.hom) ha

theorem chart_isOpenImmersion (n : ℕ)
    (e : M9StandaloneDraft.Base K ≅ M9StandaloneDraft.Base L)
    {U : M9StandaloneDraft.Schemes K}
    (a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base K))
    [IsOpenImmersion a] : IsOpenImmersion (chart n e a) := by
  unfold chart
  infer_instance

theorem chart_dense (n : ℕ) (e : M9StandaloneDraft.Base K ≅ M9StandaloneDraft.Base L)
    {U : M9StandaloneDraft.Schemes K}
    (a : U.left ⟶ AffineSpace (ULift.{u} (Fin n)) (M9StandaloneDraft.Base K))
    (ha : DenseRange a) : DenseRange (chart n e a) :=
  (affineIso n e).hom.surjective.denseRange.comp ha (affineIso n e).hom.continuous

end M9Native.StandaloneAffineCoefficientTransport
