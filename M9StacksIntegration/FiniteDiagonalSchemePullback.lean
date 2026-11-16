module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaDiagonalToProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalStructureMorphismComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteCriteriaRepresentable03ZQ
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection

/-!
# A genuine scheme representing the fibre product of two scheme classifiers

The fibre product is the original native two-fibre-product category. The
scheme is obtained from the actual base change of the diagonal over the
product of the two original schemes, and is finite over that product.
The returned equivalence is over the original big site, so its universal
point retains the actual two projections and the original comparison arrow.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.PresheafOfCategories
open CategoryTheory.TwoFibreProductOver.DiagonalFibre

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u

namespace M9Native.FiniteDiagonalSchemePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local instance siteProducts : HasBinaryProducts (BigFppfOver B S hS) :=
  Stack.hasBinaryProducts_bigFppfOver B S hS

/-- The original product of the two original scheme-valued bases. -/
abbrev productSite (Y V : BigFppfOver B S hS) := Y ⨯ V

variable (M : Stack.AlgebraicStacks.{u, u + 1} B S hS)
  (Y V : BigFppfOver B S hS)
  (a : Stack.schemeStack.{u, u + 1} B S hS Y ⟶ M)
  (b : Stack.schemeStack.{u, u + 1} B S hS V ⟶ M)

/-- Projection of the actual native fibre product of the two classifiers. -/
abbrev pairProjection :=
  TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget V)
    M.val.val.p a.hom.hom.toFunctor b.hom.hom.toFunctor

private theorem isEquivalence_comp' {A : Type*} [Category A]
    {D : Type*} [Category D] {E : Type*} [Category E]
    (F : A ⥤ D) (G : D ⥤ E) (hF : F.IsEquivalence) (hG : G.IsEquivalence) :
    (F ⋙ G).IsEquivalence :=
  ((@Functor.asEquivalence A _ D _ F hF).trans
    (@Functor.asEquivalence D _ E _ G hG)).isEquivalence_functor

private theorem isFiberedInGroupoids_product {C : Type*} [Category C]
    {A : Type*} [Category A] {D : Type*} [Category D]
    (p : A ⥤ C) (q : D ⥤ C)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) :
    (TwoFibreProductOver.structureFunctor p q (𝟭 C) p q).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids p q (𝟭 _) p q hp hq
    Functor.isFiberedInGroupoids_id rfl rfl

/-- A finite diagonal produces an actual scheme representing the full
native fibre product, finite over the product of its two original bases.
The diagonal hypothesis is honest and generic; actual M9 clients derive it
from the checked source constructor. -/
theorem exists_scheme
    (hΔ : Stack.RelativeProperty B S hS (Space.finiteMorphismProperty B S hS)
      (Stack.diagonal.{u, u, u + 1} B S hS M.val)) :
    ∃ (P : BigFppfOver B S hS) (q : P ⟶ productSite B S hS Y V),
      IsFinite ((BigFppfOver.toScheme B S hS).map q) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (Over.forget P) (pairProjection B S hS M Y V a b)) := by
  let xf : Over Y ⥤ M.val.val.obj := a.hom.hom.toFunctor
  let yf : Over V ⥤ M.val.val.obj := b.hom.hom.toFunctor
  have hxw : xf ⋙ M.val.val.p = Over.forget Y := a.hom.hom.w
  have hyw : yf ⋙ M.val.val.p = Over.forget V := b.hom.hom.w
  have hpZ : (TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget V)
      (𝟭 _) (Over.forget Y) (Over.forget V)).IsFiberedInGroupoids :=
    isFiberedInGroupoids_product _ _ (Functor.IsFiberedInGroupoids.over_forget Y)
      (Functor.IsFiberedInGroupoids.over_forget V)
  have hte : (Over.iteratedSliceBackward (Y ⨯ V) ⋙
      TwoFibreProductOver.sliceProd Y V).IsEquivalence :=
    isEquivalence_comp' _ _ (Over.iteratedSliceEquiv (Y ⨯ V)).symm.isEquivalence_functor
      (TwoFibreProductOver.instIsEquivalenceSliceProd Y V)
  let z := (Over.iteratedSliceBackward (Y ⨯ V) ⋙
      TwoFibreProductOver.sliceProd Y V) ⋙
    TwoFibreProductOver.prodMap xf yf hxw hyw
  have hz : z ⋙ ProdP M.val.val.p = Over.map (Y ⨯ V).hom := rfl
  obtain ⟨F, hF, ⟨e⟩⟩ :=
    Stack.isRepresentableByAlgebraicSpaces_diagonal_algebraicStack B S hS M
      (Y ⨯ V) z hz
  let H := (spacesOverSmallerBaseFunctor B (Y ⨯ V).left.1 S
    (Y ⨯ V).left.2 hS (Y ⨯ V).hom).obj ⟨F, hF⟩
  have hf : Space.IsFinite B S hS H.obj.hom := hΔ (Y ⨯ V) z hz F hF ⟨e⟩
  have hr : yoneda.relativelyRepresentable H.obj.hom :=
    Space.relativelyRepresentable_of_isFinite B S hS H.property.isSheaf
      (isAlgebraicSpace_yoneda B S hS (Y ⨯ V)).isSheaf hf
  obtain ⟨P, q, i, hpb⟩ := hr (𝟙 (yoneda.obj (Y ⨯ V)))
  have hi : IsIso i := hpb.isIso_fst_of_isIso inferInstance
  have hq : IsFinite ((BigFppfOver.toScheme B S hS).map q) :=
    (Space.presheaf_isFinite_of_isFinite H.obj.hom hr hf).property
      (𝟙 (yoneda.obj (Y ⨯ V))) i q hpb
  let eH : StacksRepresentableCFG.EquivalenceOver
      ((TwoFibreProductOver.fst (Over.map (Y ⨯ V).hom) M.val.val.p
        (ProdP M.val.val.p) z (Diag M.val.val.p)) ⋙ Over.map (Y ⨯ V).hom)
      (discreteProjection H.obj.left) :=
    (e.compRight (Over.map (Y ⨯ V).hom)).trans
      ((relocalizeElementsEquivalenceOver (Y ⨯ V).hom F).trans
        (equivalenceOverOfIso
          ((spacesOverSmallerBaseFunctorForgetIso B (Y ⨯ V).left.1 S
            (Y ⨯ V).left.2 hS (Y ⨯ V).hom).app ⟨F, hF⟩).symm))
  have hcmp := TwoFibreProductOver.isEquivalence_precomposeFst
    (Over.map (Y ⨯ V).hom)
    (TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget V) (𝟭 _)
      (Over.forget Y) (Over.forget V))
    M.val.val.p (ProdP M.val.val.p)
    (TwoFibreProductOver.prodMap xf yf hxw hyw) (Diag M.val.val.p)
    (Over.iteratedSliceBackward (Y ⨯ V) ⋙ TwoFibreProductOver.sliceProd Y V) rfl
    M.val.isFiberedInGroupoids (Functor.IsFiberedInGroupoids.over_map (Y ⨯ V).hom)
    hpZ hte rfl
  have hQ : (TwoFibreProductOver.structureFunctor (Over.map (Y ⨯ V).hom)
      M.val.val.p (ProdP M.val.val.p) z (Diag M.val.val.p)).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
      (Functor.IsFiberedInGroupoids.over_map (Y ⨯ V).hom) M.val.isFiberedInGroupoids
      (isFiberedInGroupoids_product _ _ M.val.isFiberedInGroupoids
        M.val.isFiberedInGroupoids) hz rfl
  have hT : (pairProjection B S hS M Y V a b).IsFiberedInGroupoids :=
    TwoFibreProductOver.isFiberedInGroupoids (Over.forget Y) (Over.forget V) M.val.val.p
      xf yf (Functor.IsFiberedInGroupoids.over_forget Y)
      (Functor.IsFiberedInGroupoids.over_forget V) M.val.isFiberedInGroupoids hxw hyw
  obtain ⟨k⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence hQ hT
    (TwoFibreProductOver.precomposeFst (Over.map (Y ⨯ V).hom)
        (TwoFibreProductOver.structureFunctor (Over.forget Y) (Over.forget V) (𝟭 _)
          (Over.forget Y) (Over.forget V))
        M.val.val.p (ProdP M.val.val.p)
        (TwoFibreProductOver.prodMap xf yf hxw hyw) (Diag M.val.val.p)
        (Over.iteratedSliceBackward (Y ⨯ V) ⋙ TwoFibreProductOver.sliceProd Y V) rfl ⋙
      TwoFibreProductOver.prodDiagComparison xf yf hxw hyw) rfl
    (isEquivalence_comp' _ _ hcmp
      (TwoFibreProductOver.instIsEquivalenceProdDiagComparison xf yf hxw hyw))
  refine ⟨P, q, hq, ⟨?_⟩⟩
  exact (((sliceElementsEquivalenceOver P).trans
    (equivalenceOverOfIso (asIso i))).trans
      (StacksRepresentableCFG.EquivalenceOver.ofEq
        TwoFibreProductOver.fst_comp_eq eH).symm).trans k

end M9Native.FiniteDiagonalSchemePullback
