module

public import M9StacksIntegration.GenusNineCoverSourcePointLift
public import M9StacksIntegration.GenusNinePhysicalCoverParameterPoint
public import M9StacksIntegration.BoundedCoverAtlasPullback

/-! One fixed finite system of actual polarized models and their five
actual cover schemes covers every original algebraically closed field
curve with a nonconstant map of degree at most five. The original source
square and coefficient map are retained in the universal-source lift. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space
attribute [local instance] isCurve_projectiveSpaceOver_one

universe u v

namespace M9Native.GenusNineFiniteCoverSystem

open GenusNineBoundedCoverFamilies

variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Honest original curve coverage of the constructed polarized models.
The true model polarization and all-field degree forty-eight are part of
the constructed `Model`, and are not premises of this predicate. -/
def CoversOriginalCurves {m : ℕ} {I : Type v}
    (D : I → GenusNineGroundFieldPolarizedModels.Model.{u} K m) : Prop :=
  ∀ (L : Type u) [Field L] [IsAlgClosed L] (σ : Spec (.of L) ⟶ Spec (.of K))
    (C : Scheme.{u}) (f : C ⟶ Spec (.of L)) [IsProper f] [IsCurve L f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ f.appTop)], genus f = 9 →
    ∃ (i : I) (y : Spec (.of L) ⟶ (D i).parameter) (r : C ⟶ (D i).total),
      IsPullback r f (D i).projection y ∧ y ≫ (D i).structureMap = σ

/-- The models and all five representers are chosen before any original
field, curve, or cover. Their original curve coverage is derived from the
actual finite equation models with their genuine embedding and line. -/
theorem exists_finite_system :
    ∃ (m t : ℕ) (n : Fin t → ℕ)
      (D : (Σ i : Fin t, Fin (n i)) → GenusNineGroundFieldPolarizedModels.Model.{u} K m)
      (P : ∀ i j, Presentation K B hK (D i) j), CoversOriginalCurves K D := by
  classical
  obtain ⟨m,t,n,D,hcov⟩ := GenusNineGroundFieldPolarizedModels.exists_finite_models K
  let P : ∀ i j, Presentation K B hK (D i) j :=
    fun i => Classical.choice (exists_presentations K B hK (D i))
  refine ⟨m,t,n,D,P,?_⟩
  intro L _ _ σ C f _ _ _ _ hg
  obtain ⟨i,y,r,κ,sq,hσ,_⟩ := hcov L σ C f hg
  exact ⟨i,y,r,sq,hσ⟩

section UniversalSource

variable {m : ℕ} {I : Type v}
  (D : I → GenusNineGroundFieldPolarizedModels.Model.{u} K m)
  (P : ∀ i j, Presentation K B hK (D i) j)
  (hcov : CoversOriginalCurves K D)
  (L : Type u) [Field L] [IsAlgClosed L] (hL : B.Contains (Spec (.of L)))
  (coefficient : K →+* L) (C : Scheme.{u}) (f : C ⟶ Spec (.of L))
  [IsProper f] [IsCurve L f] [Smooth f]
  [IsIso ((Scheme.ΓSpecIso (.of L)).inv ≫ f.appTop)]

include hcov

/-- Every actual bounded-degree physical cover has an actual field
point on one of the SAME universal source families. Its original source
square and original coefficient map are derived, without a curve-model
isomorphism, graph polynomial, or classifier-comparison premise. -/
theorem exists_universal_source_point (hg : genus f = 9)
    (g : C ⟶ PencilProjectiveLineGeometry.Line L)
    (hover : g ≫ PencilProjectiveLineGeometry.toBase L = f)
    (hnc : ¬ ∃ y : PencilProjectiveLineGeometry.Line L, ∀ c : C, g.base c = y)
    (hdeg : PencilDegreePullback.curveMapDegree f
      (PencilProjectiveLineGeometry.toBase L) g hover hnc ≤ 5) :
    ∃ (i : I) (j : Fin 5)
      (a : siteObject B (Spec (.of K)) hK hL (Spec.map (CommRingCat.ofHom coefficient)) ⟶
        BoundedCoverAtlasPullback.sourceBase B K hK (P i j).boundedFamily)
      (r : C ⟶ (P i j).boundedFamily.total),
      IsPullback r f (P i j).boundedFamily.projection (B.inclusion.map a.left) := by
  obtain ⟨i,y,r,sq,hσ⟩ :=
    hcov L (Spec.map (CommRingCat.ofHom coefficient)) C f hg
  let c : GenusNinePhysicalCoverParameterPoint.PhysicalCover (D i) L
      (Spec.map (CommRingCat.ofHom coefficient)) :=
    ⟨C,f,y,r,sq,hσ,g,hover,hnc⟩
  obtain ⟨j,w,_,hw,_⟩ := GenusNinePhysicalCoverParameterPoint.exists_parameter_point
    K B hK (D i) (fun j => (P i j).parameter) (fun j => (P i j).representative)
    (fun j => (P i j).parameterMap) (fun j => (P i j).representing)
    (fun j => (P i j).projection_triangle) L hL
    (Spec.map (CommRingCat.ofHom coefficient)) c hdeg
  let w₀ : Spec (.of L) ⟶ (P i j).boundedFamily.parameter :=
    (BigFppfOver.toScheme B integerBase (B.contains_integerBase)).map w
  have hw₀ : w₀ ≫ GenusNineCoverSourcePointLift.baseMap (P i j) = y := hw
  have hground : w₀ ≫ (P i j).boundedFamily.structureMap =
      Spec.map (CommRingCat.ofHom coefficient) := by
    change w₀ ≫ (P i j).groundMap = _
    rw [(P i j).groundMap_eq,← Category.assoc,hw]
    exact hσ
  let a : siteObject B (Spec (.of K)) hK hL (Spec.map (CommRingCat.ofHom coefficient)) ⟶
      BoundedCoverAtlasPullback.sourceBase B K hK (P i j).boundedFamily :=
    Over.homMk (ObjectProperty.homMk w₀) (by
      apply B.inclusion.map_injective
      exact hground)
  refine ⟨i,j,a,GenusNineCoverSourcePointLift.lift (P i j) y r f sq w₀ hw₀,?_⟩
  exact GenusNineCoverSourcePointLift.lift_isPullback (P i j) y r f sq w₀ hw₀

end UniversalSource

end M9Native.GenusNineFiniteCoverSystem
end
