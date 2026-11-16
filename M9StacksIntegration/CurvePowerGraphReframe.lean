module

public import M9StacksIntegration.CurvePowerGraphContexts

/-!
# Reframing the outside blocks without changing the modified diagonal

Only the three distinguished masks matter individually. The remaining
unmarked blocks form an unordered list. Selecting new outside labels
therefore preserves every actual transported modified-diagonal state.
-/

@[expose] public noncomputable section

namespace M9Native.CurvePowerGraphReframe

open CurvePowerGraphLocal CurvePowerGraphContexts

def outside (ctx : Context) : State :=
  ([ctx.label 3, ctx.label 4].filter (· ≠ 0)) ++ ctx.spectator

theorem transport_tripod (ctx : Context) (b : ℕ) :
    transport ctx [b, 8, 16] =
      canonical (([liftMask ctx.label b].filter (· ≠ 0)) ++ outside ctx) := by
  have h8 : liftMask ctx.label 8 = ctx.label 3 := by
    simp [liftMask, Nat.testBit, Nat.shiftRight_eq_div_pow]
  have h16 : liftMask ctx.label 16 = ctx.label 4 := by
    simp [liftMask, Nat.testBit, Nat.shiftRight_eq_div_pow]
  simp only [transport, List.map_cons, List.map_nil, h8, h16]
  change canonical ((([liftMask ctx.label b] ++ [ctx.label 3, ctx.label 4]).filter (· ≠ 0)) ++
      ctx.spectator) = _
  rw [List.filter_append, List.append_assoc]
  rfl

theorem transport_localGamma_of_outside_perm (ctx ctx' : Context)
    (h0 : ctx.label 0 = ctx'.label 0) (h1 : ctx.label 1 = ctx'.label 1)
    (h2 : ctx.label 2 = ctx'.label 2) (ho : (outside ctx).Perm (outside ctx'))
    (s : State) (hs : s ∈ keys (embed localGamma)) : transport ctx s = transport ctx' s := by
  have hstates : s = [7, 8, 16] ∨ s = [3, 8, 16] ∨ s = [5, 8, 16] ∨
      s = [6, 8, 16] ∨ s = [4, 8, 16] ∨ s = [2, 8, 16] ∨ s = [1, 8, 16] := by
    simpa only [localGamma_explicit, keys, embed, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, eq_comm] using hs
  rcases hstates with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [transport_tripod, transport_tripod]
    simp only [liftMask, Nat.testBit, Nat.shiftRight_eq_div_pow, h0, h1, h2]
    norm_num
    apply canonical_eq_of_perm
    exact ho.append_left _

variable {M : Type*} [AddCommGroup M]

theorem realization_localGamma_of_outside_perm (t : ℤ) (F : State → M) (ctx ctx' : Context)
    (h0 : ctx.label 0 = ctx'.label 0) (h1 : ctx.label 1 = ctx'.label 1)
    (h2 : ctx.label 2 = ctx'.label 2) (ho : (outside ctx).Perm (outside ctx')) :
    realization t (F ∘ transport ctx) (embed localGamma) =
      realization t (F ∘ transport ctx') (embed localGamma) := by
  rw [realization_embed, realization_embed]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rcases a with ⟨s, c⟩
  have hs : s ∈ keys (embed localGamma) :=
    List.mem_map.mpr ⟨(s, (c, 0)), List.mem_map.mpr ⟨(s, c), ha, rfl⟩, rfl⟩
  exact congrArg (fun s => c • F s)
    (transport_localGamma_of_outside_perm ctx ctx' h0 h1 h2 ho s hs)

end M9Native.CurvePowerGraphReframe
