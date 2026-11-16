module

public import M9StacksIntegration.SectionCokernelRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.EpiResidueFields
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeNaturality
public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# A nowhere-zero section is a line subbundle with locally free cokernel

The input is genuine nonvanishing of the actual section map after every
field-valued pullback. The dual map is then epi by actual rank-one fiber
linear algebra and residue-field Nakayama. Its kernel is finite locally
free; dualizing the genuine exact kernel sequence identifies the actual
cokernel of the original section. Neither cokernel flatness nor a
constant-rank condition on a bundle map is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionCokernelLocallyFree

variable {X : Scheme.{u}}

/-- The section map stays genuinely nonzero at every actual field-valued
point. This is a property of the native sheaf map, not supplied quotient data. -/
def NonzeroFieldFibers {H : X.Modules} (s : unitModule X ⟶ H) : Prop :=
  ∀ (K : Type u) [Field K] (p : Spec (.of K) ⟶ X),
    (Scheme.Modules.pullback p).map s ≠ 0

/-- The actual pullback-dual square transports nonvanishing. -/
theorem pullback_dualMap_ne_zero {H : X.Modules}
    [hH : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H]
    (s : unitModule X ⟶ H) {Y : Scheme.{u}} (p : Y ⟶ X)
    (hs : (Scheme.Modules.pullback p).map s ≠ 0) :
    (Scheme.Modules.pullback p).map (dualMap s) ≠ 0 := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      ((Scheme.Modules.pullback p).obj H) := Stacks.Chow.isFiniteLocallyFree_pullback p H hH
  let e : (Scheme.Modules.pullback p).obj (dualSheaf H) ≅
      dualSheaf ((Scheme.Modules.pullback p).obj H) :=
    @asIso _ _ _ _ (Stacks.Chow.pullbackDualMap p H) (Stacks.Chow.pullbackDualMap_isIso p H hH)
  have hn : (Scheme.Modules.pullback p).map (dualMap s) ≫
      Stacks.Chow.pullbackDualMap p (unitModule X) =
      Stacks.Chow.pullbackDualMap p H ≫ dualMap ((Scheme.Modules.pullback p).map s) :=
    Stacks.Chow.pullbackDualMap_naturality p s
  intro hz
  apply dualMap_ne_zero ((Scheme.Modules.pullback p).map s) hs
  have hzero : e.hom ≫ dualMap ((Scheme.Modules.pullback p).map s) = 0 :=
    hn.symm.trans ((congrArg (fun a => a ≫ Stacks.Chow.pullbackDualMap p (unitModule X)) hz).trans
      zero_comp)
  exact (e.inv_hom_id_assoc _).symm.trans
    ((congrArg (fun a => e.inv ≫ a) hzero).trans comp_zero)

/-- At an actual field point, the pulled dual section is epi because its
target is genuinely one-dimensional. -/
theorem field_pullback_dualMap_epi {H : X.Modules}
    [hH : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H]
    (s : unitModule X ⟶ H) (K : Type u) [Field K] (p : Spec (.of K) ⟶ X)
    (hs : (Scheme.Modules.pullback p).map s ≠ 0) :
    Epi ((Scheme.Modules.pullback p).map (dualMap s)) := by
  let hD := isFiniteLocallyFree_dualSheaf H hH
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      ((Scheme.Modules.pullback p).obj (dualSheaf H)) :=
    Stacks.Chow.isFiniteLocallyFree_pullback p (dualSheaf H) hD
  have hU := isFiniteLocallyFreeOfRank_dualSheaf (unitModule X) 1 (unitModule_rank X)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback p).obj (dualSheaf (unitModule X))) 1 :=
    @isFiniteLocallyFreeOfRank_pullback _ _ p _ 1 hU
  exact epi_of_ne_zero_to_rank_one K _ (pullback_dualMap_ne_zero s p hs)

/-- Actual field nonvanishing implies an actual global epimorphism of
duals by the native residue-field form of Nakayama's lemma. -/
theorem dualMap_epi_of_nonzeroFieldFibers {H : X.Modules}
    [hH : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H]
    (s : unitModule X ⟶ H) (hs : NonzeroFieldFibers s) : Epi (dualMap s) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (dualSheaf (unitModule X)) :=
    (isFiniteLocallyFreeOfRank_dualSheaf (unitModule X) 1 (unitModule_rank X)).isFiniteLocallyFree
  apply Scheme.Modules.epi_of_forall_epi_pullback_fromSpecResidueField (dualMap s)
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_of_isFiniteLocallyFree _)
  intro x
  exact field_pullback_dualMap_epi s (X.residueField x) (X.fromSpecResidueField x)
    (hs (X.residueField x) (X.fromSpecResidueField x))

theorem mono_of_nonzeroFieldFibers {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hs : NonzeroFieldFibers s) : Mono s := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H := hH.isFiniteLocallyFree
  exact mono_of_dualMap_epi s r hH (dualMap_epi_of_nonzeroFieldFibers s hs)

theorem cokernel_rank {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hs : NonzeroFieldFibers s) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel s) (r-1) := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H := hH.isFiniteLocallyFree
  exact cokernel_rank_of_dualMap_epi s r hH (dualMap_epi_of_nonzeroFieldFibers s hs)

theorem cokernelSequence_shortExact {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hs : NonzeroFieldFibers s) : (cokernelSequence s).ShortExact := by
  let : Mono s := mono_of_nonzeroFieldFibers s r hH hs
  exact { exact := ShortComplex.exact_cokernel s }

/-- The derived finite locally free quotient makes the actual inclusion
split over a neighbourhood of every point. -/
theorem cokernelSequence_locally_split {H : X.Modules} (s : unitModule X ⟶ H)
    (r : ℕ) (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H r)
    (hs : NonzeroFieldFibers s) (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((cokernelSequence s).map (Scheme.Modules.restrictFunctor U.ι)).Splitting := by
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} H := hH.isFiniteLocallyFree
  exact cokernelSequence_locally_split_of_dualMap_epi s r hH
    (dualMap_epi_of_nonzeroFieldFibers s hs) x

theorem cokernel_rank_twentyNine {H : X.Modules} (s : unitModule X ⟶ H)
    (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H 30)
    (hs : NonzeroFieldFibers s) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel s) 29 :=
  cokernel_rank s 30 hH hs

end M9Native.SectionCokernelLocallyFree
