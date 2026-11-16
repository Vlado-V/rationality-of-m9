module

public import M9StacksIntegration.FieldPointMapRank
public import M9StacksIntegration.LagrangianRowDifferential
public import M9StacksIntegration.MukaiConormalFieldCoordinates

/-!
# Genuine residue-fibre injection survives any actual field-valued point

The original residue rank is the rank of the actual pulled global-section
map. Actual finite local freeness supplies both genuine finite dimensions,
so rank-nullity proves injection without a flatness or comparison premise.
The original nonzero defining-row differential is a concrete application.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.FieldPointFiberInjectivity

open SpecFieldStalkSections TupleEvaluationFiber
open Stacks.AlgebraicGeometry.ReflexiveModules

variable (K : Type u) [Field K] {X : Scheme.{u}}

/-- Genuine injection on the original residue fibre implies genuine injection after any actual field point. -/
theorem pullbackSections_injective {A B : X.Modules} (a : A ⟶ B)
    (p : Spec (.of K) ⟶ X) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A r]
    (hi : Function.Injective (MukaiSemiIrreducible.fiberMap a (p (point K)))) :
    Function.Injective (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map a)).hom := by
  let x := p (point K)
  letI := residueAlgebra x
  letI : Module.Finite (X.residueField x) (Fiber A x) := fiberFinite A r x
  have hr : MukaiSemiIrreducible.mapRankAt a x = r :=
    (LinearMap.finrank_range_of_inj hi).trans (finrank_fiber A r x)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj A) r :=
    isFiniteLocallyFreeOfRank_pullback p A r
  obtain ⟨hfinite,hfinrank⟩ := MukaiConormalFieldCoordinates.finite_and_finrank_sections K
    ((Scheme.Modules.pullback p).obj A) r
  letI := hfinite
  let t := (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map a)).hom
  have ht : finrank K (LinearMap.range t) = r :=
    (FieldPointMapRank.finrank_range_pullbackSections_eq_mapRankAt K a p).trans hr
  have hd : finrank K (LinearMap.range t) + finrank K (LinearMap.ker t) =
      finrank K (moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj A)) :=
    LinearMap.finrank_range_add_finrank_ker t
  rw [ht,hfinrank] at hd
  have hk : finrank K (LinearMap.ker t) = 0 := by omega
  exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)

variable (k : Type u) [Field k]
  (s : Γ(LagrangianFiveSectionModel.equationBundle k,⊤))
  [SmoothOfRelativeDimension 1 (LagrangianFiveSectionModel.structureMap k s)]

/-- The actual nonzero original row remains injective at every actual extension-field point. -/
theorem rowDifferential_pullbackSections_injective (a : Fin 5 → k) (ha : a ≠ 0)
    (p : Spec (.of K) ⟶ LagrangianFiveSectionModel.curve k s) :
    Function.Injective (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
      (LagrangianRowDifferential.rowDifferential k s a))).hom := by
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
        (LagrangianPluckerQuotient.determinantLine k)) 1 :=
    isFiniteLocallyFreeOfRank_dualSheaf (LagrangianPluckerQuotient.determinantLine k)
      1 (LagrangianPluckerQuotient.determinantLine_rank k)
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (LagrangianFiveSectionModel.inclusion k s)).obj
        (Stacks.AlgebraicGeometry.ReflexiveModules.dualSheaf
          (LagrangianPluckerQuotient.determinantLine k))) 1 :=
    isFiniteLocallyFreeOfRank_pullback _ _ 1
  exact pullbackSections_injective K _ p 1
    (LagrangianRowDifferential.rowDifferential_fiber_injective k s a ha _)

end M9Native.FieldPointFiberInjectivity
