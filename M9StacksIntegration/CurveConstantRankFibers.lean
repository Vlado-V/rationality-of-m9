module

public import M9StacksIntegration.MukaiShortExactFiberRank
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Actual cokernel fibres and short-exact fibre injections

All fibres are the original residue-field tensors of the actual sheaf
stalks. Tensor right exactness computes the actual cokernel fibre rank.
A finite locally free quotient makes the first map of an actual short
exact sequence injective after residue-field tensoring.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.CurveConstantRankFibers

open MukaiSaturationRank TupleEvaluationFiber MukaiShortExactFiberRank

variable {X : Scheme.{u}}

/-- The native rank function is the dimension of the actual residue tensor. -/
theorem fiberRank_eq_finrank (F : X.Modules) (x : X) :
    Scheme.Modules.fiberRank F x = Module.finrank (X.residueField x) (Fiber F x) := rfl

/-- The actual map rank plus the actual cokernel fibre dimension is the
original target rank. Only tensor right exactness enters. -/
theorem mapRankAt_add_cokernel_fiberRank {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n] (x : X) :
    MukaiSemiIrreducible.mapRankAt φ x + Scheme.Modules.fiberRank (cokernel φ) x = n := by
  let := residueAlgebra x
  let : Module.Finite (X.residueField x) (Fiber G x) := fiberFinite G n x
  have hsurj := fiberMap_surjective (cokernel.π φ) x
  let : Module.Finite (X.residueField x) (Fiber (cokernel φ) x) :=
    Module.Finite.of_surjective (inducedFiberMap (cokernel.π φ) x) hsurj
  have hexact := fiberMap_exact (ShortComplex.cokernelSequence φ)
    (ShortComplex.cokernelSequence_exact φ) x
  change Function.Exact (inducedFiberMap φ x) (inducedFiberMap (cokernel.π φ) x) at hexact
  have hdim := (inducedFiberMap (cokernel.π φ) x).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
    hexact.linearMap_ker_eq, finrank_fiber G n x] at hdim
  change Module.finrank (X.residueField x) (LinearMap.range (inducedFiberMap φ x)) +
    Module.finrank (X.residueField x) (Fiber (cokernel φ) x) = n
  exact (Nat.add_comm _ _).trans hdim

/-- Constant rank of the original map determines the actual cokernel's
residue-fibre rank, without a flatness or local-freeness premise on it. -/
theorem cokernel_fiberRank_of_everywhereRank {F G : X.Modules} (φ : F ⟶ G) (n r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n]
    (hr : MukaiSemiIrreducible.EverywhereRank φ r) (x : X) :
    Scheme.Modules.fiberRank (cokernel φ) x = n-r := by
  have h := mapRankAt_add_cokernel_fiberRank φ n x
  rw [hr x] at h
  omega

/-- Finite local freeness supplies genuine flatness of the actual local-ring stalk. -/
theorem stalk_flat_of_finiteLocallyFree (F : X.Modules)
    (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F) (x : X) :
    Module.Flat (X.presheaf.stalk x) (Stalk F x) := by
  obtain ⟨q,hq,_⟩ := hF.exists_isFiniteLocallyFreeData
  let : Module.Free (X.presheaf.stalk x) (Stalk F x) :=
    Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFreeData_stalkFree F q hq x
  exact Module.Flat.of_free

/-- A genuine finite locally free quotient proves that the actual first
map remains injective on the original residue-field fibres. -/
theorem fiberMap_injective_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hQ : SheafOfModules.IsFiniteLocallyFree.{u,u,u} S.X₃) (x : X) :
    Function.Injective (inducedFiberMap S.f x) := by
  let := residueAlgebra x
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  let : Module.Flat (X.presheaf.stalk x) (Stalk S.X₃ x) :=
    stalk_flat_of_finiteLocallyFree S.X₃ hQ x
  change Function.Injective ((stalkMap S.f x).baseChange (X.residueField x))
  simpa only [LinearMap.baseChange_eq_lTensor] using
    (LinearMap.lTensor_injective_of_exact_of_flat (stalkMap S.g x)
      (MukaiEvaluationImage.stalkMap_surjective S.g x) (stalkMap S.f x)
      (stalkMap_injective S.f x) (stalkMap_exact S hS.exact x) (X.residueField x))

end M9Native.CurveConstantRankFibers
