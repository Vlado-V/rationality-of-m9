module

public import M9StacksIntegration.StackChangeOfBaseClassifier

/-! Actual arrows in a strict change of base are recovered from a full
original projection while keeping the specified base object fixed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 512
open CategoryTheory

namespace M9Native.StrictPullbackOriginalArrow

universe vC uC vD uD vA uA vR uR
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {A : Type uA} [Category.{vA} A] {R : Type uR} [Category.{vR} R]
  (f : C ⥤ D) (p : A ⥤ D) (H : A ⥤ R) (q : R ⥤ D)
  (hH : H.FullyFaithful) (w : H ⋙ q = p)
  (T : C) {x y : StrictPullback f p} (hx : x.base = T) (hy : y.base = T)
  (α : H.obj x.fib ⟶ H.obj y.fib) (hα : q.IsHomLift (𝟙 (f.obj T)) α)

/-- Fullness recovers the original component. Its prescribed base component
is the identity of T transported only along the actual endpoint equalities. -/
def liftArrow : x ⟶ y where
  base := eqToHom hx ≫ eqToHom hy.symm
  fib := hH.preimage α
  over := by
    have hmap : q.IsHomLift (𝟙 (f.obj T)) (H.map (hH.preimage α)) := by
      rw [hH.map_preimage]
      exact hα
    have hc := (Functor.isHomLift_comp_iff H q (𝟙 (f.obj T)) (hH.preimage α)).mpr hmap
    have hp : p.IsHomLift (𝟙 (f.obj T)) (hH.preimage α) := by rwa [w] at hc
    have := hp
    have he := IsHomLift.fac' p (𝟙 (f.obj T)) (hH.preimage α)
    simpa only [Functor.map_comp, eqToHom_map, Category.id_comp,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans] using he

/-- The complete original arrow, rather than just its base, is retained. -/
theorem liftArrow_original :
    (StrictPullback.pr f p ⋙ H).map
      (liftArrow f p H q hH w T hx hy α hα) = α :=
  hH.map_preimage α

/-- The recovered arrow lies over the identity of the SAME original T. -/
theorem liftArrow_isHomLift :
    (StrictPullback.structureFunctor f p).IsHomLift (𝟙 T)
      (liftArrow f p H q hH w T hx hy α hα) := by
  apply IsHomLift.of_fac' (StrictPullback.structureFunctor f p) (𝟙 T)
    (liftArrow f p H q hH w T hx hy α hα) hx hy
  simp only [liftArrow, StrictPullback.structureFunctor, Category.id_comp]

end M9Native.StrictPullbackOriginalArrow
