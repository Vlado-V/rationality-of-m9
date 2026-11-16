module

public import M9StacksIntegration.SpecFieldPullbackSections
public import M9StacksIntegration.LagrangianDualPullback

/-! Actual local dual evaluation at the original field-valued point,
including genuine nonvanishing from a local pairing equal to one. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.FieldPointDualPairing

open SpecFieldStalkSections SpecFieldPullbackSections
open Stacks.AlgebraicGeometry.ReflexiveModules

variable (K : Type u) [Field K] {X : Scheme.{u}} (p : Spec (.of K) ⟶ X)
  (Q : X.Modules) (U : X.Opens) (hp : p.base (point K) ∈ U)

/-- Actual dual pullback and actual local section pullback retain the original local evaluation. -/
theorem evalAt_pulledSection (tau : Γ(dualSheaf Q,U)) (m : Γ(Q,U)) :
    evalAt ((Scheme.Modules.pullback p).obj Q)
      (Scheme.Modules.Hom.app (X := Spec (.of K)) (Stacks.Chow.pullbackDualMap p Q) ⊤
        (pulledSection K p (dualSheaf Q) U hp tau))
      (pulledSection K p Q U hp m) =
      p.appLE U ⊤ (preimageTop K p U hp) (evalAt Q tau m) := by
  let h := preimageTop K p U hp
  let t := (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app
    (dualSheaf Q)).val.app (op U)) tau
  let v := (((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app Q).val.app (op U)) m
  let d : (Scheme.Modules.pullback p).obj (dualSheaf Q) ⟶
      dualSheaf ((Scheme.Modules.pullback p).obj Q) := Stacks.Chow.pullbackDualMap p Q
  have hn := PresheafOfModules.naturality_apply d.val
    (homOfLE h).op t
  have he := evalAt_map ((Scheme.Modules.pullback p).obj Q) h
    (d.app (p ⁻¹ᵁ U) t) v
  have hu : evalAt ((Scheme.Modules.pullback p).obj Q) (d.app (p ⁻¹ᵁ U) t) v =
      p.app U (evalAt Q tau m) :=
    LagrangianDualPullback.dualPullback_evaluation_unit p Q U tau m
  change evalAt ((Scheme.Modules.pullback p).obj Q)
    (Scheme.Modules.Hom.app (X := Spec (.of K)) (Stacks.Chow.pullbackDualMap p Q) ⊤
      (((Scheme.Modules.pullback p).obj (dualSheaf Q)).presheaf.map (homOfLE h).op t))
    (((Scheme.Modules.pullback p).obj Q).presheaf.map (homOfLE h).op v) = _
  exact (congrArg (fun z => evalAt ((Scheme.Modules.pullback p).obj Q) z
    (((Scheme.Modules.pullback p).obj Q).presheaf.map (homOfLE h).op v)) hn).trans
      (he.trans (congrArg (fun z =>
        (Spec (.of K)).presheaf.map (homOfLE h).op z) hu))

/-- A genuine unit pairing makes the actual pulled original dual section nonzero. -/
theorem pulledSection_ne_zero_of_pairing_one
    (tau : Γ(dualSheaf Q,U)) (m : Γ(Q,U)) (hm : evalAt Q tau m = 1) :
    pulledSection K p (dualSheaf Q) U hp tau ≠ 0 := by
  intro hz
  have he := evalAt_pulledSection K p Q U hp tau m
  have hzero : evalAt ((Scheme.Modules.pullback p).obj Q)
      (Scheme.Modules.Hom.app (X := Spec (.of K)) (Stacks.Chow.pullbackDualMap p Q) ⊤
        (pulledSection K p (dualSheaf Q) U hp tau))
      (pulledSection K p Q U hp m) = 0 := by
    rw [hz,map_zero]
    rfl
  exact zero_ne_one ((hzero.symm.trans he).trans
    ((congrArg (fun z => p.appLE U ⊤ (preimageTop K p U hp) z) hm).trans (map_one _)))

end M9Native.FieldPointDualPairing
