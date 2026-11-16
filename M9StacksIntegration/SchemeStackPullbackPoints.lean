module

public import M9StacksIntegration.FiniteDiagonalSchemePullback

/-! Original scheme projections, actual vertical comparison and every-site-point
coverage extracted from a genuine represented native two-fibre product. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
universe u
namespace M9Native.SchemeStackPullbackPoints

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (M : Stack.AlgebraicStacks.{u,u+1} B S hS)
  (Y V : BigFppfOver B S hS)
  (a : Stack.schemeStack.{u,u+1} B S hS Y ⟶ M)
  (b : Stack.schemeStack.{u,u+1} B S hS V ⟶ M)

abbrev pairCategory := TwoFibreProductOver (Over.forget Y) (Over.forget V)
  M.val.val.p a.hom.hom.toFunctor b.hom.hom.toFunctor
abbrev pairProjection := FiniteDiagonalSchemePullback.pairProjection B S hS M Y V a b

variable {P : BigFppfOver B S hS}

/-- Actual projections and the actual vertical comparison in the original
native fibre product; these are data carried by its universal object. -/
structure PointData where
  left : P ⟶ Y
  right : P ⟶ V
  comparison : a.hom.hom.toFunctor.obj (Over.mk left) ≅
    b.hom.hom.toFunctor.obj (Over.mk right)
  vertical : (M).val.val.p.IsHomLift (𝟙 P) comparison.hom

/-- The exact object of the original fibre product specified by these data. -/
def pointObject (D : PointData B S hS M Y V a b (P := P)) :
    pairCategory B S hS M Y V a b :=
  { base := P
    x := Over.mk D.left
    y := Over.mk D.right
    hx := rfl
    hy := rfl
    iso := D.comparison
    vertical := D.vertical }

/-- Its original comparison object is forced by the actual representing
equivalence, not supplied as an extra family-isomorphism premise. -/
theorem exists_pointData
    (e : StacksRepresentableCFG.EquivalenceOver
      (Over.forget P) (pairProjection B S hS M Y V a b)) :
    ∃ D : PointData B S hS M Y V a b (P := P),
      e.hom.functor.obj (Over.mk (𝟙 P)) = pointObject B S hS M Y V a b D := by
  let z := e.hom.functor.obj (Over.mk (𝟙 P))
  change ∃ D : PointData B S hS M Y V a b (P := P),
    z = pointObject B S hS M Y V a b D
  have hb : z.base = P := Functor.congr_obj e.hom.w (Over.mk (𝟙 P))
  obtain ⟨base, x, y, hx, hy, iso, vertical⟩ := z
  change base = P at hb
  cases hb.symm
  obtain ⟨xbase, ⟨⟨⟩⟩, xhom⟩ := x
  obtain ⟨ybase, ⟨⟨⟩⟩, yhom⟩ := y
  change xbase = P at hx
  change ybase = P at hy
  cases hx.symm
  cases hy.symm
  exact ⟨⟨xhom, yhom, iso, vertical⟩, rfl⟩

/-- Every native pair-point with its original vertical comparison lifts to
the actual representing scheme, retaining BOTH original parameter maps. -/
theorem covers_native_point
    (e : StacksRepresentableCFG.EquivalenceOver
      (Over.forget P) (pairProjection B S hS M Y V a b))
    (D : PointData B S hS M Y V a b (P := P))
    (hD : e.hom.functor.obj (Over.mk (𝟙 P)) = pointObject B S hS M Y V a b D)
    {T : BigFppfOver B S hS}
    (E : PointData B S hS M Y V a b (P := T)) :
    ∃ w : T ⟶ P, w ≫ D.left = E.left ∧ w ≫ D.right = E.right := by
  let z := pointObject B S hS M Y V a b E
  let c := e.inv.functor.obj z
  let ρ : c ⟶ Over.mk (𝟙 P) := Over.homMk c.hom (by simp)
  let δ : z ⟶ pointObject B S hS M Y V a b D :=
    (e.counitIso.app z).inv ≫ e.hom.functor.map ρ ≫ eqToHom hD
  have ha : δ.a.left = δ.hbase := by
    have := δ.ha
    simpa using IsHomLift.fac' (Over.forget Y) δ.hbase δ.a
  have hb : δ.b.left = δ.hbase := by
    have := δ.hb
    simpa using IsHomLift.fac' (Over.forget V) δ.hbase δ.b
  refine ⟨δ.hbase, ?_, ?_⟩
  · rw [← ha]
    exact Over.w δ.a
  · rw [← hb]
    exact Over.w δ.b

end M9Native.SchemeStackPullbackPoints
