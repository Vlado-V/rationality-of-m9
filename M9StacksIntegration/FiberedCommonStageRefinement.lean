module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent

/-! Fullness gives a common refinement of two actual stage choices.
Both factorization equations keep the same original limit object and its
two original arrows. No common-refinement or comparison isomorphism is an
input. The native-curve client discharges the fullness/descent hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
attribute [local implicit_reducible] Functor.Fiber

namespace M9Native.FiberedCommonStageRefinement

universe uC vC uY vY uI vI

/-- Two genuine stage arrows out of the same limit object admit one
later-stage source, with both original arrows recovered exactly. -/
theorem exists_common_stage
    {C : Type uC} [Category.{vC} C] {Y : Type uY} [Category.{vY} Y]
    (p : Y ⥤ C) (hp : p.IsFiberedInGroupoids)
    {I : Type uI} [Category.{vI} I] [IsCofiltered I]
    (D : I ⥤ C) (c : Cone D) (hHom : Deformation.Artin.DescentHom p D c)
    (x : p.Fiber c.pt) (i j : I)
    (xi : p.Fiber (D.obj i)) (yj : p.Fiber (D.obj j))
    (δ : x.1 ⟶ xi.1) (ε : x.1 ⟶ yj.1)
    (hδ : p.IsHomLift (c.π.app i) δ) (hε : p.IsHomLift (c.π.app j) ε) :
    ∃ (k : I) (a : k ⟶ i) (b : k ⟶ j) (z : p.Fiber (D.obj k))
      (χ : x.1 ⟶ z.1) (η : z.1 ⟶ xi.1) (θ : z.1 ⟶ yj.1),
      p.IsHomLift (c.π.app k) χ ∧ p.IsHomLift (D.map a) η ∧
      p.IsHomLift (D.map b) θ ∧ χ ≫ η = δ ∧ χ ≫ θ = ε := by
  let _ := hp.isFibered
  let _ := hδ
  let _ := hε
  obtain ⟨k₀, a₀, b₀, -⟩ := IsCofilteredOrEmpty.cone_objs i j
  obtain ⟨xi₀, η₀, hη₀⟩ := hp.exists_lift (D.map a₀) xi.1 xi.2
  obtain ⟨yj₀, θ₀, hθ₀⟩ := hp.exists_lift (D.map b₀) yj.1 yj.2
  let _ := hη₀
  let _ := hθ₀
  let _ := hp.isStronglyCartesian_homLift (D.map a₀) η₀
  let _ := hp.isStronglyCartesian_homLift (D.map b₀) θ₀
  let xi₀f : p.Fiber (D.obj k₀) :=
    ⟨xi₀, IsHomLift.domain_eq p (D.map a₀) η₀⟩
  let yj₀f : p.Fiber (D.obj k₀) :=
    ⟨yj₀, IsHomLift.domain_eq p (D.map b₀) θ₀⟩
  let δ₀ : x.1 ⟶ xi₀f.1 :=
    Functor.IsStronglyCartesian.map p (D.map a₀) η₀ (c.w a₀).symm δ
  let ε₀ : x.1 ⟶ yj₀f.1 :=
    Functor.IsStronglyCartesian.map p (D.map b₀) θ₀ (c.w b₀).symm ε
  have hδ₀ : p.IsHomLift (c.π.app k₀) δ₀ :=
    Functor.IsStronglyCartesian.map_isHomLift p (D.map a₀) η₀ (c.w a₀).symm δ
  have hε₀ : p.IsHomLift (c.π.app k₀) ε₀ :=
    Functor.IsStronglyCartesian.map_isHomLift p (D.map b₀) θ₀ (c.w b₀).symm ε
  have hδ₀fac : δ₀ ≫ η₀ = δ :=
    Functor.IsStronglyCartesian.fac p (D.map a₀) η₀ (c.w a₀).symm δ
  have hε₀fac : ε₀ ≫ θ₀ = ε :=
    Functor.IsStronglyCartesian.fac p (D.map b₀) θ₀ (c.w b₀).symm ε
  obtain ⟨k, s, xk, yk, dx, dy, χ, ψ, hdx, hdy, hχ, hψ, hχdx, hχψdy⟩ :=
    hHom k₀ xi₀f yj₀f x x δ₀ ε₀ hδ₀ hε₀ (𝟙 x.1) (IsHomLift.id x.2)
  let _ := hdx
  let _ := hdy
  let _ := hψ
  refine ⟨k, s ≫ a₀, s ≫ b₀, xk, χ, dx ≫ η₀, (ψ ≫ dy) ≫ θ₀,
    hχ, ?_, ?_, ?_, ?_⟩
  · rw [D.map_comp]
    infer_instance
  · rw [D.map_comp]
    infer_instance
  · calc
      χ ≫ (dx ≫ η₀) = (χ ≫ dx) ≫ η₀ := (Category.assoc _ _ _).symm
      _ = δ₀ ≫ η₀ := by rw [hχdx]
      _ = δ := hδ₀fac
  · calc
      χ ≫ ((ψ ≫ dy) ≫ θ₀) = (χ ≫ ψ ≫ dy) ≫ θ₀ := by simp only [Category.assoc]
      _ = (𝟙 x.1 ≫ ε₀) ≫ θ₀ := by rw [hχψdy]
      _ = ε := by simpa only [Category.id_comp] using hε₀fac

end M9Native.FiberedCommonStageRefinement
