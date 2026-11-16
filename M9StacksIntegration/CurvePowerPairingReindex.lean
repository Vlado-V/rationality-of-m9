module

public import M9StacksIntegration.ChowPicardPairingPushforward
public import M9StacksIntegration.CurvePowerPointTrace
public import M9StacksIntegration.CurvePowerGraphBlockRestriction

/-!
# Actual partition pairings under an actual block permutation

The inverse curve-power map is constructed from the inverse finite
equivalence. The pairing comparison uses proper pushforward of the
actual fundamental class, and then the literal partition-map equality.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerPairingReindex

open CurvePowerChowFunctional CurvePowerPointTrace CurvePowerGraphMaps
open CurvePowerGraphLocal CurvePowerGraphMapReindex

theorem wordDegree_isIso_over (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (fY : Y ⟶ Spec (.of k)) [IsProper fY]
    (i : Y ⟶ X) [IsIso i] (hi : i ≫ f = fY)
    (xs : List (Stacks.Picard.ofScheme X)) :
    wordDegree k fY ((xs.map (Stacks.Picard.schemePullbackClass i)).map chosenLine) =
      wordDegree k f (xs.map chosenLine) := by
  let x : Fin xs.length → Stacks.Picard.ofScheme X := xs.get
  have hL : List.ofFn (fun j => Stacks.Picard.schemePullbackClass i (x j)) =
      xs.map (Stacks.Picard.schemePullbackClass i) := by
    have h := congrArg (List.map (Stacks.Picard.schemePullbackClass i)) (List.ofFn_get xs)
    simpa only [List.map_ofFn, Function.comp_def, x] using h
  have hl := wordDegree_ofFn k fY (fun j => Stacks.Picard.schemePullbackClass i (x j))
  have hr := wordDegree_ofFn k f x
  have hwl := congrArg (fun ws => wordDegree k fY (ws.map chosenLine)) hL
  have hwr := congrArg (fun ws => wordDegree k f (ws.map chosenLine)) (List.ofFn_get xs)
  exact hwl.symm.trans (hl.trans
    ((ChowPicardPairingPushforward.capDegreePicard_isIso_over k f fY i hi x).trans
      (hr.symm.trans hwr)))

def reindexIso {S : Scheme.{u}} (C : Over S) {m n : ℕ} (e : Fin n ≃ Fin m) :
    power C m ≅ power C n where
  hom := reindex C e
  inv := reindex C e.symm
  hom_inv_id := by
    rw [reindex_comp]
    have he : (e ∘ e.symm : Fin m → Fin m) = id := by
      funext j
      exact e.apply_symm_apply j
    rw [he, reindex_id]
  inv_hom_id := by
    rw [reindex_comp]
    have he : (e.symm ∘ e : Fin n → Fin n) = id := by
      funext j
      exact e.symm_apply_apply j
    rw [he, reindex_id]

def reindexLeftIso {S : Scheme.{u}} (C : Over S) {m n : ℕ} (e : Fin n ≃ Fin m) :
    (power C m).left ≅ (power C n).left :=
  (Over.forget S).mapIso (reindexIso C e)

theorem isIso_reindex_left {S : Scheme.{u}} (C : Over S) {m n : ℕ}
    (e : Fin n ≃ Fin m) : IsIso (reindex C e).left :=
  inferInstanceAs (IsIso (reindexLeftIso C e).hom)

variable (k : Type u) [Field k] (C : Over (Spec (.of k))) [IsProper C.hom]

theorem wordDegree_reindex {m n : ℕ} (e : Fin n ≃ Fin m)
    (xs : List (Stacks.Picard.ofScheme (power C n).left)) :
    wordDegree k (power C m).hom
        ((xs.map (Stacks.Picard.schemePullbackClass (reindex C e).left)).map chosenLine) =
      wordDegree k (power C n).hom (xs.map chosenLine) := by
  let := isIso_reindex_left C e
  exact wordDegree_isIso_over k (power C n).hom (power C m).hom
    (reindex C e).left (Over.w (reindex C e)) xs

theorem partitionFunctional_state_perm (c₀ : power C 0 ⟶ C) (ambient : ℕ)
    (word : List (LineClass C ambient)) (s t : State)
    (hs : s.Nodup) (ht : t.Nodup) (hsep : Separated s) (h : s.Perm t) :
    partitionFunctional k C c₀ ambient word s = partitionFunctional k C c₀ ambient word t := by
  let e := indexEquiv s t hs ht h
  let xs := word.map (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient t).left)
  have hp (x : LineClass C ambient) :
      Stacks.Picard.schemePullbackClass (reindex C e).left
        (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient t).left x) =
      Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left x := by
    rw [Stacks.Picard.schemePullbackClass_comp, ← Over.comp_left,
      stateMap_perm C c₀ ambient s t hs ht hsep h]
  have hxs : xs.map (Stacks.Picard.schemePullbackClass (reindex C e).left) =
      word.map (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient s).left) := by
    change (word.map (Stacks.Picard.schemePullbackClass (stateMap C c₀ ambient t).left)).map _ = _
    rw [List.map_map]
    apply List.map_congr_left
    intro x _
    exact hp x
  have hv := congrArg (fun ws => wordDegree k (power C s.length).hom (ws.map chosenLine)) hxs
  simpa only [partitionFunctional, List.map_map, Function.comp_def, xs] using
    hv.symm.trans (wordDegree_reindex k C e xs)

end M9Native.CurvePowerPairingReindex
