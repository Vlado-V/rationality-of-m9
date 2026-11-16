module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksFrontier.Topology.Dimension.Krull

/-! Restricting the base to an open containing an actual point retains
its actual fibre, with both projection morphisms. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.OpenRestrictionPointFiber

variable {X Y T : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    (p : T ⟶ Y) (hp : ∀ t : T, p t ∈ U)

/-- The actual point map lifted to the open containing its image. -/
def lift : T ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι p (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hp t)

@[reassoc (attr := simp)]
theorem lift_comp : lift U p hp ≫ U.ι = p :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted fibre is an actual pullback of the original family. -/
theorem isPullback_fiber :
    IsPullback (pullback.fst (f ∣_ U) (lift U p hp) ≫ (f ⁻¹ᵁ U).ι)
      (pullback.snd (f ∣_ U) (lift U p hp)) f p := by
  have h := (IsPullback.of_hasPullback (f ∣_ U) (lift U p hp)).paste_horiz
    (isPullback_morphismRestrict f U).flip
  simpa only [lift_comp] using h

/-- The actual fibre scheme before and after restricting the base. -/
def fiberIso :
    pullback (C := Scheme.{u}) (f ∣_ U) (lift U p hp) ≅ pullback (C := Scheme.{u}) f p :=
  (isPullback_fiber f U p hp).isoPullback

@[reassoc (attr := simp)]
theorem fiberIso_hom_fst :
    (fiberIso f U p hp).hom ≫ pullback.fst f p =
      pullback.fst (f ∣_ U) (lift U p hp) ≫ (f ⁻¹ᵁ U).ι :=
  (isPullback_fiber f U p hp).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem fiberIso_hom_snd :
    (fiberIso f U p hp).hom ≫ pullback.snd f p = pullback.snd (f ∣_ U) (lift U p hp) :=
  (isPullback_fiber f U p hp).isoPullback_hom_snd

/-- Connectedness of the actual point fibre is retained by the open restriction. -/
theorem fiber_connected [ConnectedSpace (pullback (C := Scheme.{u}) f p)] :
    ConnectedSpace (pullback (C := Scheme.{u}) (f ∣_ U) (lift U p hp)) :=
  (Scheme.homeoOfIso (fiberIso f U p hp)).connectedSpace_iff.mpr inferInstance

/-- Irreducibility of the actual point fibre is retained by the open restriction. -/
theorem fiber_irreducible [IrreducibleSpace (pullback (C := Scheme.{u}) f p)] :
    IrreducibleSpace (pullback (C := Scheme.{u}) (f ∣_ U) (lift U p hp)) :=
  (Scheme.homeoOfIso (fiberIso f U p hp)).irreducibleSpace_iff.mpr inferInstance

/-- Dimension is retained by the exact actual fibre isomorphism. -/
theorem fiber_dimension :
    topologicalKrullDim (pullback (C := Scheme.{u}) (f ∣_ U) (lift U p hp)) =
      topologicalKrullDim (pullback (C := Scheme.{u}) f p) := by
  let e := Scheme.homeoOfIso (fiberIso f U p hp)
  exact IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph

/-- Smoothness of the actual point-fibre morphism is retained, with its
original base projection identified by the exact isomorphism. -/
theorem fiber_smooth [Smooth (pullback.snd f p)] :
    Smooth (pullback.snd (f ∣_ U) (lift U p hp)) := by
  rw [← fiberIso_hom_snd f U p hp]
  infer_instance

end M9Native.OpenRestrictionPointFiber
