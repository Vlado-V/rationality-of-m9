module

public import M9StacksIntegration.NativeRelativeAffineModels
public import StacksFrontier.AlgebraicGeometry.Limits.StageFactorizationOfLimitMorphism
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Actual eventual open factorization along relative K-affine models

The exact native factorization provider is pinned and ready.
An actual limiting affine diagram whose original limit map lands in an open
of a stage already lands in that open at a later stage. We apply the actual
LFP factorization theorem to the TAIL over that stage; its base is that
actual stage, with no finite-type assertion over Spec Z and no noetherian
assumption on the ORIGINAL coefficient ring. The relative K[s] corollary
works even when Spec A is outside the chosen native site.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local instance] CategoryTheory.IsCofiltered.isConnected

namespace M9StacksIntegration.NativeRelativeAffineOpenStage
universe u

/-- The actual affine tail over a stage gives eventual factorization into
an ORIGINAL open, retaining the exact transition and limit maps. -/
theorem exists_stage_factor_open
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (haff : ∀ i, IsAffine (D.obj i)) (i : I) (U : (D.obj i).Opens)
    (f : c.pt ⟶ U) (hf : f ≫ U.ι = c.π.app i) :
    ∃ (j : I) (a : j ⟶ i) (g : D.obj j ⟶ U),
      g ≫ U.ι = D.map a ∧ c.π.app j ≫ g = f := by
  let E := Over.post (X := i) D
  let V := Over.forget (D.obj i)
  let ct := (Over.conePost D i).obj c
  let d := V.mapCone ct
  have hd : IsLimit d := isLimitOfPreserves V (Over.isLimitConePost i hc)
  let p : E ⋙ V ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun a => (E.obj a).hom
      naturality := fun a b v => by
        change (E.map v).left ≫ (E.obj b).hom = (E.obj a).hom ≫ 𝟙 (D.obj i)
        rw [Category.comp_id]
        exact Over.w (E.map v) }
  have hm : ∀ a, d.π.app a ≫ p.app a = c.π.app i := fun a => Over.w (ct.π.app a)
  obtain ⟨a, g, hg, hgf⟩ := exists_stage_comp_eq_of_locallyOfFinitePresentation
    (E ⋙ V) p d hd (c.π.app i) hm (fun a => haff a.left) U.ι f hf
  exact ⟨a.left, a.hom, g, hg, hgf⟩

variable (K A : Type u) [CommRing K] [CommRing A] [Algebra K A]

/-- Eventual factorization along the ACTUAL relative K[s] diagram, with
no absolute finite-type assumption or fixed cutoff on A. -/
theorem exists_relative_stage_factor_open
    (s : Finset A) (U : ((AdjoinFinset.specDiagram K A).obj (op s)).Opens)
    (f : Spec (.of A) ⟶ U)
    (hf : f ≫ U.ι = (AdjoinFinset.specCone K A).π.app (op s)) :
    ∃ (t : Finset A) (a : op t ⟶ op s)
      (g : (AdjoinFinset.specDiagram K A).obj (op t) ⟶ U),
      g ≫ U.ι = (AdjoinFinset.specDiagram K A).map a ∧
        (AdjoinFinset.specCone K A).π.app (op t) ≫ g = f := by
  obtain ⟨j, a, g, hg, hgf⟩ := exists_stage_factor_open
    (AdjoinFinset.specDiagram K A) (AdjoinFinset.specCone K A)
    (AdjoinFinset.isLimitSpecCone K A) (fun j => by
      change IsAffine (Spec (.of (Algebra.adjoin K (j.unop : Set A))))
      infer_instance) (op s) U f hf
  exact ⟨j.unop, a, g, hg, hgf⟩

/-- The eventual stage genuinely belongs to EVERY native site containing
Spec K, even if the full original Spec A does not. -/
theorem exists_small_relative_stage_factor_open
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
    (s : Finset A) (U : ((AdjoinFinset.specDiagram K A).obj (op s)).Opens)
    (f : Spec (.of A) ⟶ U)
    (hf : f ≫ U.ι = (AdjoinFinset.specCone K A).π.app (op s)) :
    ∃ (t : Finset A) (a : op t ⟶ op s)
      (g : (AdjoinFinset.specDiagram K A).obj (op t) ⟶ U),
      B.Contains ((AdjoinFinset.specDiagram K A).obj (op t)) ∧
        g ≫ U.ι = (AdjoinFinset.specDiagram K A).map a ∧
        (AdjoinFinset.specCone K A).π.app (op t) ≫ g = f := by
  obtain ⟨t, a, g, hg, hgf⟩ := exists_relative_stage_factor_open K A s U f hf
  exact ⟨t, a, g, NativeRelativeAffineModels.contains_stage K A B hK t, hg, hgf⟩

/-- The actual open itself belongs to EVERY base-containing native site. -/
theorem contains_open_stage (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
    (s : Finset A) (U : ((AdjoinFinset.specDiagram K A).obj (op s)).Opens) :
    B.Contains U :=
  Scheme.size_lt_of_isOpenImmersion U.ι (NativeRelativeAffineModels.contains_stage K A B hK s)

/-- The actual eventual factor retains the ORIGINAL K-coefficient map. -/
theorem relative_stage_factor_coefficient
    (s t : Finset A) (a : op t ⟶ op s)
    (U : ((AdjoinFinset.specDiagram K A).obj (op s)).Opens)
    (g : (AdjoinFinset.specDiagram K A).obj (op t) ⟶ U)
    (hg : g ≫ U.ι = (AdjoinFinset.specDiagram K A).map a) :
    g ≫ (U.ι ≫ (AdjoinFinset.specToBase K A).app (op s)) =
      (AdjoinFinset.specToBase K A).app (op t) := by
  rw [← Category.assoc, hg]
  exact ((AdjoinFinset.specToBase K A).naturality a).trans (Category.comp_id _)

end M9StacksIntegration.NativeRelativeAffineOpenStage
