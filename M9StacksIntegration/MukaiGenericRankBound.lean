module

public import M9StacksIntegration.ClosedPointConstantRank
public import Mathlib.AlgebraicGeometry.FunctionField

@[expose] public section

/-!
# Actual map-rank loci and closed-point control near the generic point

This thin compatibility leaf uses legacy visibility because its frozen
closed-point semicontinuity providers are native legacy modules. Their
source and proof bodies are preserved unchanged.

The actual coherent cokernel supplies upper semicontinuity. Thus an
original bundle map has its largest residue rank at the generic point.
On a Jacobson integral scheme, rank bounds at closed points where a
second actual map has rank one suffice for a global bound, provided that
second map genuinely has generic rank one.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.MukaiGenericRankBound

open CurveConstantRankFibers MukaiSemiIrreducible

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

theorem cokernel_isFiniteType {F G : X.Modules} (a : F ⟶ G)
    (hF : SheafOfModules.IsFiniteLocallyFree.{u,u,u} F)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u,u,u} G) :
    (cokernel a).IsFiniteType := by
  let := hF
  let := hG
  let : F.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X F
  let : G.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X G
  let : (cokernel a).IsCoherent := _root_.SheafOfModules.cokernel_isCoherent a
  exact _root_.IsCoherent.toIsFiniteType _

theorem isOpen_mapRankAt_ge {F G : X.Modules} (a : F ⟶ G) (m n : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n) (r : ℕ) :
    IsOpen {x : X | r ≤ mapRankAt a x} := by
  let := hG
  let : (cokernel a).IsFiniteType :=
    cokernel_isFiniteType a hF.isFiniteLocallyFree hG.isFiniteLocallyFree
  by_cases hr : r ≤ n
  · have hset : {x : X | r ≤ mapRankAt a x} =
        {x : X | Scheme.Modules.fiberRank (cokernel a) x ≤ n-r} := by
      ext x
      have h := mapRankAt_add_cokernel_fiberRank a n x
      simp only [Set.mem_ofPred_eq]
      omega
    rw [hset]
    exact FiniteTypeFiberSemicontinuity.isOpen_fiberRank_le (cokernel a) (n-r)
  · have hset : {x : X | r ≤ mapRankAt a x} = ∅ := by
      ext x
      have h := mapRankAt_add_cokernel_fiberRank a n x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      omega
    rw [hset]
    exact isOpen_empty

variable [IsIntegral X]

theorem mapRankAt_le_generic {F G : X.Modules} (a : F ⟶ G) (m n : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n) (x : X) :
    mapRankAt a x ≤ mapRankAt a (genericPoint X) := by
  let := hG
  let : (cokernel a).IsFiniteType :=
    cokernel_isFiniteType a hF.isFiniteLocallyFree hG.isFiniteLocallyFree
  obtain ⟨U, hxU, hU⟩ :=
    FiniteTypeFiberSemicontinuity.exists_open_fiberRank_le (cokernel a) x
  have hηU : genericPoint X ∈ U := (genericPoint_specializes x).mem_open U.isOpen hxU
  have hq := hU (genericPoint X) hηU
  have hx := mapRankAt_add_cokernel_fiberRank a n x
  have hη := mapRankAt_add_cokernel_fiberRank a n (genericPoint X)
  omega

variable [JacobsonSpace X]

/-- The dense rank-one locus is derived from the original generic
differential rank; every point used in the comparison is a closed point
of the original scheme. No extension-field point API is required. -/
theorem bound_of_closed_rank_one_locus {F G H J : X.Modules}
    (a : F ⟶ G) (δ : H ⟶ J) (m n p q r : ℕ)
    (hF : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F m)
    (hG : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G n)
    (hH : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} H p)
    (hJ : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} J q)
    (hδ : mapRankAt δ (genericPoint X) = 1)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) → mapRankAt δ x = 1 →
      mapRankAt a x ≤ r) :
    ∀ x : X, mapRankAt a x ≤ r := by
  intro x
  by_contra hx
  have hηa : r+1 ≤ mapRankAt a (genericPoint X) := by
    have hmax := mapRankAt_le_generic a m n hF hG x
    omega
  let Z := {y : X | r+1 ≤ mapRankAt a y} ∩ {y : X | 1 ≤ mapRankAt δ y}
  have hZ : IsOpen Z :=
    (isOpen_mapRankAt_ge a m n hF hG (r+1)).inter
      (isOpen_mapRankAt_ge δ p q hH hJ 1)
  have hηZ : genericPoint X ∈ Z := ⟨hηa, by
    change 1 ≤ mapRankAt δ (genericPoint X)
    rw [hδ]⟩
  obtain ⟨y, hyZ, hyc⟩ := nonempty_inter_closedPoints
    (Z := Z) ⟨genericPoint X, hηZ⟩ hZ.isLocallyClosed
  have hyδ : mapRankAt δ y = 1 := by
    have hmax := mapRankAt_le_generic δ p q hH hJ y
    have hlow := hyZ.2
    change 1 ≤ mapRankAt δ y at hlow
    rw [hδ] at hmax
    omega
  have hbound := hclosed y hyc hyδ
  have hlow := hyZ.1
  change r+1 ≤ mapRankAt a y at hlow
  omega

end M9Native.MukaiGenericRankBound
