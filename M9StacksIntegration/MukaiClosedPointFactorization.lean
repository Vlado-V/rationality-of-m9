module

public import M9StacksIntegration.ClosedPointConstantRank
public import M9StacksIntegration.MukaiPointLine
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsOperator

@[expose] public section

/-!
# Genuine closed-point detection and factorization into the dual point line

This thin compatibility leaf retains legacy visibility for the frozen
closed-point-rank providers. Rank-zero detection uses their actual
reduced-scheme constant-rank theorem. The point-line factor is produced
by the universal property of the actual kernel, after proving the
composite is zero; it is not supplied as data.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.MukaiClosedPointFactorization

open MukaiPointLine LagrangianMatrixChart

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [JacobsonSpace X] [IsReduced X]

theorem eq_zero_of_closedRank_zero {F G : X.Modules} (a : F ⟶ G) (m n : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) → MukaiSemiIrreducible.mapRankAt a x = 0) :
    a = 0 := by
  have hI := (ClosedPointConstantRank.ranks_of_closedRank a m n 0 hF hG hclosed).2.1
  have hz : IsZero (image a) :=
    Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero (image a) hI
  calc
    a = factorThruImage a ≫ image.ι a := (image.fac a).symm
    _ = 0 := by rw [hz.eq_of_src (image.ι a) 0, comp_zero]

theorem isIso_of_closedRank_one {F G : X.Modules} (a : F ⟶ G)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 1)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 1)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) → MukaiSemiIrreducible.mapRankAt a x = 1) :
    IsIso a := by
  have hQ := (ClosedPointConstantRank.ranks_of_closedRank a 1 1 1 hF hG hclosed).2.2
  have hz : IsZero (cokernel a) :=
    Stacks.SheafOfModules.isZero_of_isFiniteLocallyFreeOfRank_zero (cokernel a) hQ
  let : Epi a := Preadditive.epi_of_isZero_cokernel a hz
  let := hF
  let := hG
  exact SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfRank a 1

theorem factor_through_pointLine_of_closed_zero {Q A : X.Modules} {r : ℕ}
    (q : freeOn X r ⟶ Q) [Epi q]
    (hQ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 1)
    (c : A ⟶ freeOn X r) (m : ℕ)
    (hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A m)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      MukaiSemiIrreducible.mapRankAt (c ≫ pointCokernelProjection q) x = 0) :
    ∃ a : A ⟶ dualSheaf Q, a ≫ pointLineMap q = c := by
  let e : cokernel (pointLineMap q) ≅ dualSheaf (kernel q) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (pointLineMap q))
      (pointSequence_shortExact q hQ).gIsCokernel
  have hT : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (dualSheaf (kernel q)) (r-1) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e (pointLineCokernel_rank q hQ)
  have hz : c ≫ pointCokernelProjection q = 0 :=
    eq_zero_of_closedRank_zero _ m (r-1) hA hT hclosed
  let : Mono (pointSequence q).f := (pointSequence_shortExact q hQ).mono_f
  obtain ⟨a, ha⟩ := KernelFork.IsLimit.lift'
    (pointSequence_shortExact q hQ).exact.fIsKernel c hz
  exact ⟨a, ha⟩

end M9Native.MukaiClosedPointFactorization
