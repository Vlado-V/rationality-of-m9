module

public import M9StacksIntegration.PoincareLargeDegreeField
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.TensorEulerZeroDim.FiniteRank
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Devissage
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteOverFieldStalks
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Divisors.ClosedSubschemeDimensionDrop

/-!
# Actual cohomology of a line on a finite flat field scheme

The actual rank of the finite scheme computes the actual line's H0.
Higher cohomology vanishes because the original scheme is affine.
Only the native zero-dimensional Euler tensor formula is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.FiniteFlatLineCohomology

/-- The finite clause of the native finite-flat characterization. -/
theorem finiteLocallyFree_isFinite {Z S : Scheme.{u}} (p : Z ⟶ S) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] : IsFinite p :=
  ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p r)).1

/-- A line bundle on a finite rank-`r` scheme over a field has exactly `r`
sections and no higher cohomology. The count is by the actual coherent
Euler characteristic on a zero-dimensional support. -/
theorem finiteLocallyFree_lineBundle_cohomology
    (K : Type u) [Field K] {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r]
    (L : Z.Modules) [hL : SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] (n : ℕ) :
    Module.finrank K (cohomologyOverField K p L n) = if n = 0 then r else 0 := by
  haveI : IsFinite p := finiteLocallyFree_isFinite p r
  haveI : IsAffine Z := isAffine_of_isAffineHom p
  haveI : IsProper p := inferInstance
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme Z L
  haveI : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have hLcoh : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible Z L
  have hucoh : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hqc : L.IsQuasicoherent :=
    Stacks.Divisors.isQuasicoherent_of_isInvertible L
  have hdim : topologicalKrullDim Z ≤ 0 := by
    haveI : IsArtinianRing Γ(Z, ⊤) := isArtinianRing_globalSections_of_isFinite_over_field K p
    haveI : DiscreteTopology Z :=
      (Scheme.homeoOfIso Z.isoSpec).isEmbedding.discreteTopology
    exact topologicalKrullDim_zero_of_discreteTopology Z
  by_cases hn : n = 0
  · subst n
    rw [if_pos rfl]
    have huSupp : topologicalKrullDim (_root_.SheafOfModules.supp
        (SheafOfModules.unit Z.ringCatSheaf)) ≤ 0 :=
      (topologicalKrullDim_subspace_le Z _).trans hdim
    obtain ⟨hT, hχ⟩ := exists_eulerCharacteristic_tensorSheaf_eq_rank_mul K p
      (SheafOfModules.unit Z.ringCatSheaf) huSupp L 1
    have hswap := eulerCharacteristic_unit_tensorSheaf K p L hLcoh hucoh
    have heuler : @eulerCharacteristic K _ Z p _ L hLcoh =
        @eulerCharacteristic K _ Z p _ (SheafOfModules.unit Z.ringCatSheaf) hucoh := by
      rw [← hswap]
      rw [show (@SheafOfModules.tensorSheaf_isCoherent Z.toRingedSpace _ L hucoh hLcoh) = hT
        from Subsingleton.elim _ _, hχ, Nat.cast_one, one_mul]
    letI := hLcoh
    letI := hucoh
    have hLSupp : topologicalKrullDim (_root_.SheafOfModules.supp L) ≤ 0 :=
      (topologicalKrullDim_subspace_le Z _).trans hdim
    rw [eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero K p L hLSupp,
      eulerCharacteristic_eq_finrank_cohomologyOverField_zero_of_supp_le_zero K p _ huSupp] at heuler
    have heq : Module.finrank K (cohomologyOverField K p L 0) =
        Module.finrank K (cohomologyOverField K p (SheafOfModules.unit Z.ringCatSheaf) 0) :=
      Nat.cast_injective heuler
    rw [heq, finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K p]
    exact ((Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq p r).mp
      inferInstance).2.2
  · rw [if_neg hn]
    haveI := hqc
    have hzero := isZero_cohomologyOverField_pos_of_isAffine K p L n (Nat.pos_of_ne_zero hn)
    haveI := ModuleCat.subsingleton_of_isZero hzero
    exact Module.finrank_zero_of_subsingleton


end M9Native.FiniteFlatLineCohomology
