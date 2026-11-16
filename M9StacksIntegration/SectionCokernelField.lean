module

public import M9StacksIntegration.SheafFieldKernelObstruction
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Modules.DualShortExact
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Field-fiber algebra for a nowhere-zero section

These helpers concern actual sheaves and actual maps on Spec K. A nonzero
map to a rank-one bundle is epi, and the actual dual functor detects a
nonzero map into a finite locally free sheaf. No cokernel flatness or
local-splitting hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionCokernelLocallyFree

/-- The actual structure sheaf, typed in the native abelian category. -/
abbrev unitModule (X : Scheme.{u}) : X.Modules :=
  _root_.SheafOfModules.unit X.ringCatSheaf

theorem unitModule_rank (X : Scheme.{u}) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (unitModule X) 1 :=
  SheafOfModules.isFiniteLocallyFreeOfRank_unit X

/-- Duality preserves the zero map, directly from its actual evaluation. -/
theorem dualMap_zero_map {X : Scheme.{u}} (F G : X.Modules) :
    dualMap (0 : F ⟶ G) = 0 := by
  apply hom_ext_dualSheaf
  intro U x W y
  simp only [dualPairing_dualMap, Scheme.Modules.Hom.zero_app]
  change ((x.app (op W)).hom (0 : Γ(G, W.left))) = 0
  exact map_zero _

/-- Reflexivity of the target makes the actual dual faithful on maps. -/
theorem dualMap_injective {X : Scheme.{u}} {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} G] :
    Function.Injective (dualMap (F := F) (G := G)) := by
  let := isIso_toDoubleDual_of_isFiniteLocallyFree G
  intro f g h
  apply (cancel_mono (toDoubleDual G)).1
  rw [toDoubleDual_naturality, toDoubleDual_naturality]
  exact congrArg (fun a => toDoubleDual F ≫ dualMap a) h

theorem dualMap_ne_zero {X : Scheme.{u}} {F G : X.Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} G]
    (f : F ⟶ G) (hf : f ≠ 0) : dualMap f ≠ 0 := by
  intro h
  exact hf (dualMap_injective (h.trans (dualMap_zero_map F G).symm))

/-- On a genuine affine native scheme, Γ detects nonzero maps whose
source is actually quasi-coherent. -/
theorem gamma_map_ne_zero {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] (f : M ⟶ N) (hf : f ≠ 0) :
    moduleSpecΓFunctor.map f ≠ 0 := by
  let := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have hn : (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f
  intro h
  apply hf
  apply (cancel_epi M.fromTildeΓ).1
  rw [← hn, h, Functor.map_zero, zero_comp, comp_zero]

/-- A surjective actual Γ map is epi when the native source and target
have their genuine affine quasi-coherent identifications. -/
theorem epi_of_gamma_surjective {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hf : Function.Surjective (moduleSpecΓFunctor.map f).hom) : Epi f := by
  let := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let : (tilde.functor (R := R)).IsLeftAdjoint := (tilde.adjunction (R := R)).isLeftAdjoint
  let : Epi (moduleSpecΓFunctor.map f) := (ModuleCat.epi_iff_surjective _).2 hf
  have hn : (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
      M.fromTildeΓ ≫ f := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality f
  have hcomp : Epi (M.fromTildeΓ ≫ f) := by
    rw [← hn]
    infer_instance
  exact epi_of_epi M.fromTildeΓ f

/-- Over an actual field point, a nonzero map to a rank-one bundle is
surjective. This applies to the actual pulled-back dual section. -/
theorem epi_of_ne_zero_to_rank_one (K : Type u) [Field K]
    {M N : (Spec (.of K)).Modules}
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} M]
    [hN : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} N 1]
    (f : M ⟶ N) (hf : f ≠ 0) : Epi f := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} N := hN.isFiniteLocallyFree
  let : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  let : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree N
  have hn := SheafFieldKernelObstruction.finite_and_finrank_sections K N 1
  let : Module.Finite K (moduleSpecΓFunctor.obj N) := hn.1
  have hΓ := gamma_map_ne_zero f hf
  have hlin : (moduleSpecΓFunctor.map f).hom ≠ 0 := by
    intro h
    exact hΓ (ModuleCat.hom_ext h)
  exact epi_of_gamma_surjective f (surjective_of_nonzero_of_finrank_eq_one hn.2 hlin)

end M9Native.SectionCokernelLocallyFree
