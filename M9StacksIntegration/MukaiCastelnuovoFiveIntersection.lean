module

public import M9StacksIntegration.MukaiGrassmannianPlucker
public import M9StacksIntegration.MukaiProjectiveKernelCoordinates
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SubvarietyIntersection
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Actual projective intersection for the five-section Castelnuovo argument

The original native Grassmannian is closed in the projective space of
twenty ordered minors, of dimension19. Its actual affine-six chart gives
a dimension lower bound6. At most five genuine linear equations define a
linear subspace of dimension at least14. Native projective intersection
therefore gives a point of the original Grassmannian satisfying the
equations. Properness supplies a closed point; algebraic closedness and
the actual chart normal form then give a genuine normalized matrix.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Module

universe u

namespace M9Native.MukaiCastelnuovoFiveIntersection

open MukaiGrassmannianPlucker MukaiProjectiveKernelCoordinates

variable (K : Type u) [Field K]
variable {Z : Type u} [AddCommGroup Z] [Module K Z] [FiniteDimensional K Z]

theorem ambient_dimension_nineteen :
    topologicalKrullDim (MukaiGrassmannianPlucker.ambient K) = (19 : WithBot ℕ∞) := by
  exact topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq
    (n := 19) (finrank_forms K)

/-- The original closed Plücker image meets the actual linear equations
coming from L; no kernel point is an input. -/
theorem image_inter_kernel_nonempty (L : Coordinates K →ₗ[K] Z)
    (hZ : finrank K Z ≤ 5) :
    (image K ∩ kernelLinearSubspace K L).Nonempty := by
  have hforms : Nontrivial (Forms K) := Module.nontrivial_of_finrank_pos
    (by rw [finrank_forms K]; decide)
  let := hforms
  have hdL := kernelLinearSubspace_dimension_ge_fourteen K L hZ
  have hneL : (kernelLinearSubspace K L).Nonempty := by
    by_contra hn
    have : IsEmpty (kernelLinearSubspace K L) :=
      ⟨fun x => hn ⟨x.val,x.property⟩⟩
    have hb := (topologicalKrullDim_eq_bot_iff_isEmpty (kernelLinearSubspace K L)).mpr
      inferInstance
    rw [hb] at hdL
    simp at hdL
  apply nonempty_inter_projectiveSpaceOfModule (image_isClosed K)
    (ProjectiveSpaceOfModule.isClosed_linearSubspace K (Forms K) (constraints K L))
    (image_nonempty K) hneL
  rw [ambient_dimension_nineteen K]
  exact le_trans (by norm_num : (19 : WithBot ℕ∞) ≤ 6 + 14)
    (add_le_add (image_dimension_lower K) hdL)

/-- Choose a closed point on the original proper Grassmannian satisfying
the actual linear equations. -/
theorem exists_closed_grass_point_in_kernel (L : Coordinates K →ₗ[K] Z)
    (hZ : finrank K Z ≤ 5) :
    ∃ x : grass K, IsClosed ({x} : Set (grass K)) ∧ plucker K x ∈ kernelLinearSubspace K L := by
  obtain ⟨y,⟨⟨x,rfl⟩,hx⟩⟩ := image_inter_kernel_nonempty K L hZ
  have hS : IsClosed ((plucker K) ⁻¹' kernelLinearSubspace K L) :=
    (ProjectiveSpaceOfModule.isClosed_linearSubspace K (Forms K) (constraints K L)).preimage
      (plucker K).continuous
  let : IsProper (GrassmannianCharts.projection K 3 5) :=
    isProper_of_isProjectiveMorphism _
      (Grassmannian.isProjectiveMorphism_schemeOver 3 5 (Spec (.of K)))
  let : CompactSpace (grass K) :=
    QuasiCompact.compactSpace_of_compactSpace (GrassmannianCharts.projection K 3 5)
  obtain ⟨z,hz,hzc⟩ := hS.exists_closed_singleton ⟨x,hx⟩
  exact ⟨z,hzc,hz⟩

/-- The intersection produces an actual normalized K-matrix point of
the original Grassmannian in the linear kernel locus. -/
theorem exists_matrixPoint_in_kernel [IsAlgClosed K] (L : Coordinates K →ₗ[K] Z)
    (hZ : finrank K Z ≤ 5) :
    ∃ (ι : MukaiOrderedMinors.OrderedPair) (M : Matrix (Fin 2) (Fin 5) K),
      M.submatrix id ι = 1 ∧
        plucker K (matrixPoint K ι M (IsLocalRing.closedPoint K)) ∈ kernelLinearSubspace K L := by
  obtain ⟨x,hxc,hx⟩ := exists_closed_grass_point_in_kernel K L hZ
  let : IsProper (GrassmannianCharts.projection K 3 5) :=
    isProper_of_isProjectiveMorphism _
      (Grassmannian.isProjectiveMorphism_schemeOver 3 5 (Spec (.of K)))
  let p := pointOfClosedPoint (GrassmannianCharts.projection K 3 5) x hxc
  have hp : p ≫ GrassmannianCharts.projection K 3 5 = 𝟙 _ :=
    pointOfClosedPoint_comp _ _ _
  obtain ⟨ι,M,hM,hpM⟩ := MukaiGrassmannianPoints.exists_matrixPoint K p hp
  refine ⟨ι,M,hM,?_⟩
  change plucker K (MukaiGrassmannianPoints.matrixPoint K ι M
    (IsLocalRing.closedPoint K)) ∈ kernelLinearSubspace K L
  rw [hpM]
  simpa only [p,pointOfClosedPoint_apply] using hx

end M9Native.MukaiCastelnuovoFiveIntersection
