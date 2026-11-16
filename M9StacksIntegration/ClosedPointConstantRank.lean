module

public import M9StacksIntegration.CurveConstantRank
public import M9StacksIntegration.FiniteTypeFiberSemicontinuity
public import M9StacksIntegration.JacobsonClosedPointConstancy
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

@[expose] public section

/-! Actual closed-point rank determines every residue-fibre rank.

The actual cokernel is coherent by local Noetherianity. Its residue-fibre rank
is upper semicontinuous by the finite-type theorem, with no stalk freeness
assumed. Jacobson closed-point density forces that rank to be constant.
The original map then has the prescribed rank everywhere. On a reduced
scheme, the frozen constant-rank theorem constructs its actual locally free
kernel, image, and cokernel, and the canonical residue-kernel comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.ClosedPointConstantRank

open CurveConstantRankFibers

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [JacobsonSpace X]

/-- Closed-point ranks of the original map determine the actual cokernel
fibre dimension at every point. -/
theorem cokernel_fiberRank_of_closedRank {F G : X.Modules} (φ : F ⟶ G)
    (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) :
    ∀ x : X, Scheme.Modules.fiberRank (cokernel φ) x = n-r := by
  let := hF
  let := hG
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F := hF.isFiniteLocallyFree
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G := hG.isFiniteLocallyFree
  let : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X G
  let : (cokernel φ).IsCoherent := _root_.SheafOfModules.cokernel_isCoherent φ
  let : (cokernel φ).IsFiniteType := _root_.IsCoherent.toIsFiniteType _
  apply JacobsonClosedPointConstancy.nat_eq_of_closed_points
    (Scheme.Modules.fiberRank (cokernel φ))
    (FiniteTypeFiberSemicontinuity.isOpen_fiberRank_le (cokernel φ)) (n-r)
  intro x hx
  have hdim := mapRankAt_add_cokernel_fiberRank φ n x
  rw [hclosed x hx] at hdim
  omega

/-- The residue rank at every point follows from the original map's rank at
every closed point. No reducedness or quotient-flatness assumption is needed
for this rank propagation itself. -/
theorem everywhereRank_of_closedRank {F G : X.Modules} (φ : F ⟶ G)
    (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) :
    MukaiSemiIrreducible.EverywhereRank φ r := by
  let := hG
  have hq := cokernel_fiberRank_of_closedRank φ m n r hF hG hclosed
  intro x
  obtain ⟨y, hy⟩ := JacobsonClosedPointConstancy.exists_closed_point x
  have hbound := mapRankAt_add_cokernel_fiberRank φ n y
  rw [hclosed y hy] at hbound
  have hdim := mapRankAt_add_cokernel_fiberRank φ n x
  rw [hq x] at hdim
  omega

section Reduced

variable [IsReduced X]

/-- On a reduced locally Noetherian Jacobson scheme, closed-point ranks
construct all three original locally free objects with the correct ranks. -/
theorem ranks_of_closedRank {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (kernel φ) (m-r) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (image φ) r ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (cokernel φ) (n-r) :=
  CurveConstantRank.ranks φ m n r hF hG
    (everywhereRank_of_closedRank φ m n r hF hG hclosed)

/-- The actual residue fibre of the original kernel equals the kernel of the
original residue-fibre map, with local freeness derived from closed ranks. -/
def residueKernelEquiv_of_closedRank {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) (x : X) :
    TupleEvaluationFiber.Fiber (kernel φ) x ≃ₗ[X.residueField x]
      LinearMap.ker (TupleEvaluationFiber.inducedFiberMap φ x) :=
  CurveConstantRank.residueKernelEquiv φ m n r hF hG
    (everywhereRank_of_closedRank φ m n r hF hG hclosed) x

/-- The comparison keeps the literal original kernel inclusion. -/
theorem residueKernelEquiv_of_closedRank_ι {F G : X.Modules} (φ : F ⟶ G) (m n r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt φ x = r) (x : X)
    (v : TupleEvaluationFiber.Fiber (kernel φ) x) :
    (residueKernelEquiv_of_closedRank φ m n r hF hG hclosed x v).val =
      TupleEvaluationFiber.inducedFiberMap (kernel.ι φ) x v := rfl

end Reduced

end M9Native.ClosedPointConstantRank
