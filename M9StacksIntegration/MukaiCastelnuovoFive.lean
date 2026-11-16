module

public import M9StacksIntegration.MukaiCastelnuovoFiveIntersection
public import M9StacksIntegration.MukaiPluckerKernelPoint

/-!
# The five-section Castelnuovo criterion from the original Grassmannian

The actual native Grassmannian of two-dimensional quotients of a
five-dimensional space is used with all twenty ordered Pluecker
coordinates. Projective intersection produces a normalized matrix point
in the original linear kernel locus. The original minors then give an
independent pair killed by the original alternating evaluation map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Module

universe u

namespace M9Native.MukaiCastelnuovoFive

variable (K : Type u) [Field K] [IsAlgClosed K]
variable {W : Type u} [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/-- Five actual linear equations in the original ordered twenty-minor
space leave a nonzero genuine decomposable minor tuple in the kernel. -/
theorem exists_independent_pair_zero_minors
    (L : (MukaiOrderedMinors.OrderedPair → K) →ₗ[K] W)
    (hW : finrank K W ≤ 5) :
    ∃ a b : Fin 5 → K, LinearIndependent K ![a,b] ∧
      L (MukaiOrderedMinors.orderedMinorCoordinates a b) = 0 := by
  obtain ⟨ι,M,hM,hpoint⟩ :=
    MukaiCastelnuovoFiveIntersection.exists_matrixPoint_in_kernel K L hW
  have hm : MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1) ≠ 0 := by
    intro hz
    have hi := congrFun hz ι
    change MukaiOrderedMinors.orderedMinorCoordinates (M 0) (M 1) ι = 0 at hi
    rw [MukaiOrderedMinors.orderedMinorCoordinates_eq_det,hM,Matrix.det_one] at hi
    exact one_ne_zero hi
  exact ⟨M 0,M 1,MukaiOrderedMinors.linearIndependent_of_orderedMinors_ne_zero hm,
    (MukaiPluckerKernelPoint.matrixPoint_mem_kernelLinearSubspace_iff K L ι M hM).mp hpoint⟩

variable {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Five independent source vectors and a target of dimension at most
five force an independent pair with zero actual alternating evaluation. -/
theorem exists_independent_pair_zero_of_finrank
    (B : V [⋀^Fin 2]→ₗ[K] W)
    (hV : 5 ≤ finrank K V) (hW : finrank K W ≤ 5) :
    ∃ a b : V, LinearIndependent K ![a,b] ∧ B ![a,b] = 0 := by
  obtain ⟨s,hs⟩ := exists_linearIndependent_of_le_finrank hV
  let j := Fintype.linearCombination K s
  have hj : Function.Injective j :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hs
  let B' := B.compLinearMap j
  obtain ⟨a,b,hab,hzero⟩ :=
    exists_independent_pair_zero_minors K (MukaiOrderedMinors.orderedMinorMap B') hW
  refine ⟨j a,j b,?_,?_⟩
  · convert hab.map' j (LinearMap.ker_eq_bot.mpr hj) using 1
    ext i
    fin_cases i <;> rfl
  · rw [MukaiOrderedMinors.orderedMinorMap_minors] at hzero
    change B (fun i => j (![a,b] i)) = 0 at hzero
    convert hzero using 1
    congr 1
    ext i
    fin_cases i <;> rfl

end M9Native.MukaiCastelnuovoFive
