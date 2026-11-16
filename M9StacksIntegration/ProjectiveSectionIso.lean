module

public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.Morphism
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.Basic

/-!
# Native projective evaluation under an actual line isomorphism

The native projective morphisms agree when an actual module isomorphism
carries their generating sections to each other.  This is proved by the
checked projective-space moduli equivalence and native pinning, over every
test scheme.  No equality of morphisms is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.ProjectiveSectionIso

open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceModuli

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} {M N : X.Modules}
  [Stacks.Ample.IsInvertibleModule X M] [Stacks.Ample.IsInvertibleModule X N]
  {n : ℕ} (s : Fin (n + 1) → Γ(M, ⊤)) (t : Fin (n + 1) → Γ(N, ⊤))
  (hs : GeneratesStalks s) (ht : GeneratesStalks t)
  (e : M ≅ N) (he : ∀ i, e.hom.app ⊤ (s i) = t i)

include e he

/-- Native pinning identifies the two actual integral projective
evaluation morphisms. -/
theorem toProjectiveSpaceAtUniverse_iso :
    toProjectiveSpaceAtUniverse s hs = toProjectiveSpaceAtUniverse t ht := by
  let a : GeneratingTuple X n := ⟨M, inferInstance, s, hs⟩
  let b : GeneratingTuple X n := ⟨N, inferInstance, t, ht⟩
  have ha : (pointsEquiv X n).symm ⟦a⟧ = toProjectiveSpaceAtUniverse s hs :=
    pointsEquiv_symm_eq (t := a) (fun i => ι_toProjectiveSpaceAtUniverse s hs i)
  have hb : (pointsEquiv X n).symm ⟦b⟧ = toProjectiveSpaceAtUniverse t ht :=
    pointsEquiv_symm_eq (t := b) (fun i => ι_toProjectiveSpaceAtUniverse t ht i)
  have hc : (⟦a⟧ : Points X n) = ⟦b⟧ := Quotient.sound ⟨e, he⟩
  exact ha.symm.trans ((congrArg (pointsEquiv X n).symm hc).trans hb)

/-- The same equality is an equality of the actual morphisms over their
original base scheme. -/
theorem toProjectiveSpaceOver_iso {S : Scheme.{u}} (f : X ⟶ S) :
    toProjectiveSpaceOver s hs f = toProjectiveSpaceOver t ht f := by
  apply pullback.hom_ext
  · simp only [toProjectiveSpaceOver_fst]
  · simp only [toProjectiveSpaceOver_snd]
    exact toProjectiveSpaceAtUniverse_iso s t hs ht e he

end M9Native.ProjectiveSectionIso
