module

public import M9StacksIntegration.LagrangianAffineIsomorphism
public import M9StacksIntegration.MukaiConormalFieldCoordinates
public import M9StacksIntegration.FiniteLocallyFreeExteriorCriterion
public import M9StacksIntegration.LagrangianGrassmannian
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# A genuine point and determinant criterion for bundle maps on a curve

Actual injectivity on original field-point sections makes the original
equal-rank point pullback an isomorphism. Naturality of the genuine
exterior-power pullback comparison makes the pulled top map invertible,
so the original top map is nonzero. On a proper curve, isomorphic actual
determinant lines have equal degree, and the nonzero top map is an
isomorphism. The original equal-rank bundle map is therefore invertible.

These reusable inputs are mathematical data, not an assertion of the
desired map: the actual Mukai application separately constructs the
determinant-line comparison and proves point injectivity from its genuine
full-LG first jet.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.CurveMapPointDeterminantCriterion

/-- The true native field-point section functor detects an equal-rank
isomorphism from actual injectivity. Quasicoherence and dimensions are
derived from the actual finite locally free ranks. -/
theorem isIso_of_field_sections_injective (K : Type u) [Field K]
    {A B : (Spec (.of K)).Modules} (r : ℕ)
    [hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A r]
    [hB : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B r]
    (a : A ⟶ B) (ha : Function.Injective (moduleSpecΓFunctor.map a).hom) : IsIso a := by
  obtain ⟨hAf,hAd⟩ := MukaiConormalFieldCoordinates.finite_and_finrank_sections K A r
  obtain ⟨hBf,hBd⟩ := MukaiConormalFieldCoordinates.finite_and_finrank_sections K B r
  letI := hAf
  letI := hBf
  have hs : Function.Surjective (moduleSpecΓFunctor.map a).hom := by
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq
      ((LinearMap.finrank_range_of_inj ha).trans (hAd.trans hBd.symm))
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} A := hA.isFiniteLocallyFree
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} B := hB.isFiniteLocallyFree
  letI : A.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree A
  letI : B.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree B
  exact LagrangianAffineIsomorphism.isIso_of_globalSections_bijective a ⟨ha,hs⟩

/-- The actual exterior map commutes with original scheme pullback;
invertibility of the point map implies invertibility of the pulled
exterior map, in every native integer degree. -/
theorem isIso_pullback_exteriorPowerMap {X Y : Scheme.{u}} (p : Y ⟶ X)
    {E F : X.Modules} (a : E ⟶ F) (n : ℤ)
    [IsIso ((Scheme.Modules.pullback p).map a)] :
    IsIso ((Scheme.Modules.pullback p).map (Scheme.Modules.exteriorPowerMap a n)) := by
  let eE := LagrangianPullback.exteriorPullbackIso p E n
  let eF := LagrangianPullback.exteriorPullbackIso p F n
  letI : IsIso (Scheme.Modules.exteriorPowerMap ((Scheme.Modules.pullback p).map a) n) := by
    change IsIso ((Scheme.Modules.exteriorPowerFunctor Y n).map ((Scheme.Modules.pullback p).map a))
    infer_instance
  have hn : (Scheme.Modules.pullback p).map (Scheme.Modules.exteriorPowerMap a n) ≫ eF.hom =
      eE.hom ≫ Scheme.Modules.exteriorPowerMap ((Scheme.Modules.pullback p).map a) n :=
    LagrangianPullback.exteriorPullbackIso_natural p a n
  have hr : IsIso (eE.hom ≫ Scheme.Modules.exteriorPowerMap ((Scheme.Modules.pullback p).map a) n) :=
    inferInstance
  letI : IsIso ((Scheme.Modules.pullback p).map (Scheme.Modules.exteriorPowerMap a n) ≫ eF.hom) :=
    hn.symm ▸ hr
  exact (isIso_comp_right_iff _ eF.hom).mp inferInstance

/-- A morphism from an actual line cannot be zero when its actual
pullback at a genuine field point is invertible. -/
theorem hom_ne_zero_of_point_isIso (K : Type u) [Field K] {X : Scheme.{u}}
    {L M : X.Modules}
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (a : L ⟶ M) (p : Spec (.of K) ⟶ X)
    [IsIso ((Scheme.Modules.pullback p).map a)] : a ≠ 0 := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X L
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ((Scheme.Modules.pullback p).obj L) 1 :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      p.base p.toRingCatSheafHom L 1 inferInstance
  obtain ⟨hfinite,hdim⟩ := MukaiConormalFieldCoordinates.finite_and_finrank_sections K
    ((Scheme.Modules.pullback p).obj L) 1
  letI := hfinite
  intro hz
  have hi := (ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map a))).injective
  have hzero : moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map a) = 0 := by
    ext x
    change (((Scheme.Modules.pullback p).map a).app ⊤) x = 0
    rw [hz, Functor.map_zero]
    rfl
  letI : Subsingleton (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj L)) :=
    ⟨fun x y => hi (by rw [hzero]; rfl)⟩
  have hdim0 : finrank K (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj L)) = 0 :=
    Module.finrank_zero_of_subsingleton
  omega

/-- A true determinant-line comparison and proved injectivity on one
actual original field point imply invertibility of the original bundle
map. The actual Mukai caller derives every one of these geometric data. -/
theorem isIso_of_point_sections_injective_of_determinantIso
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [IsCurve K f] [IsProper f] {E F : X.Modules} (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower E (r : ℤ))]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Scheme.Modules.exteriorPower F (r : ℤ))]
    (a : E ⟶ F)
    (d : Scheme.Modules.exteriorPower E (r : ℤ) ≅ Scheme.Modules.exteriorPower F (r : ℤ))
    (p : Spec (.of K) ⟶ X)
    (hp : Function.Injective (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map a)).hom) :
    IsIso a := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ((Scheme.Modules.pullback p).obj E) r :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      p.base p.toRingCatSheafHom E r inferInstance
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} ((Scheme.Modules.pullback p).obj F) r :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      p.base p.toRingCatSheafHom F r inferInstance
  letI := isIso_of_field_sections_injective K r ((Scheme.Modules.pullback p).map a) hp
  letI := isIso_pullback_exteriorPowerMap p a (r : ℤ)
  have hne : Scheme.Modules.exteriorPowerMap a (r : ℤ) ≠ 0 :=
    hom_ne_zero_of_point_isIso K (Scheme.Modules.exteriorPowerMap a (r : ℤ)) p
  letI := isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero K f
    (IsCurve.topologicalKrullDim_eq_one (f := f)).le
    (Scheme.Modules.exteriorPower E (r : ℤ)) (Scheme.Modules.exteriorPower F (r : ℤ))
    (Scheme.Modules.exteriorPowerMap a (r : ℤ)) hne (invertibleCurveDegree_eq_of_iso K f
      (IsCurve.topologicalKrullDim_eq_one (f := f)).le d)
  exact FiniteLocallyFreeExteriorCriterion.isIso_of_isIso_exteriorPowerMap a r

end M9Native.CurveMapPointDeterminantCriterion
