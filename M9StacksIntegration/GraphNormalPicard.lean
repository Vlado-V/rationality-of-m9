module

public import M9StacksIntegration.DiagonalNormalPicard
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass

/-!
# Self-restriction of actual graph divisors

The graph of any relative point of a separated smooth relative curve is
an actual degree-one Hilbert family.  Its divisor class is the base change
of the original diagonal class.  Restricting it along that same graph
therefore gives the negative pullback of the original cotangent class,
over arbitrary base schemes, including nonreduced bases.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

universe u

namespace M9Native.GraphNormalPicard

variable {S : Scheme.{u}} (X T : Over S) [IsSeparated X.hom]
  [SmoothOfRelativeDimension 1 X.hom]

/-- The actual original point-graph, as a genuine degree-one Hilbert family. -/
def graphFamily (y : T ⟶ X) : Stacks.Hilbert.HilbertFamily X T 1 where
  ideal := Stacks.Hilbert.pointIdeal X T y
  isFiniteLocallyFreeOfRank := by
    let := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated X T y
    exact Stacks.Hilbert.isFiniteLocallyFreeOfRank_pointIdeal X T y

/-- Its actual positive divisor class is obtained by base changing the diagonal. -/
theorem graphFamily_class_baseChange (y : T ⟶ X) :
    Stacks.Picard.schemePullbackClass (Stacks.Hilbert.familyBaseChangeMap X y)
        (graphFamily X X (𝟙 X)).picardClass = (graphFamily X T y).picardClass := by
  let := Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated X X (𝟙 X)
  apply Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
    (graphFamily X X (𝟙 X)) (graphFamily X T y)
  change Stacks.Hilbert.pointIdeal X T y =
    (Stacks.Hilbert.pointIdeal X X (𝟙 X)).comap (Stacks.Hilbert.familyBaseChangeMap X y)
  simpa only [Category.comp_id] using
    (Stacks.Hilbert.pointIdeal_comap_familyBaseChangeMap X y (𝟙 X)).symm

/-- The identity point's original graph is the original diagonal. -/
theorem pointGraph_id_eq_diagonal :
    Stacks.Hilbert.pointGraph X X (𝟙 X) = pullback.diagonal X.hom := by
  apply pullback.hom_ext
  · rw [Stacks.Hilbert.pointGraph_comp_fst, pullback.diagonal_fst]
    rfl
  · rw [Stacks.Hilbert.pointGraph_comp_snd, pullback.diagonal_snd]

/-- The actual graph line restricted to its own original graph has
the negative cotangent class pulled back along the relative point. -/
theorem graph_self_picardClass (y : T ⟶ X) :
    Stacks.Picard.schemePullbackClass (Stacks.Hilbert.pointGraph X T y)
        (graphFamily X T y).picardClass =
      -Stacks.Picard.schemePullbackClass y.left
        (Stacks.SheafOfModules.picardClass X.left.presheaf X.left.ringCatIsSheaf
          (Scheme.Hom.relativeDifferentials X.hom)
          (DiagonalNormalPicard.differentials_isInvertible X.hom)) := by
  let := Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal X.hom
  have hD : (graphFamily X X (𝟙 X)).picardClass =
      Stacks.Divisors.picardClass (Stacks.Hilbert.diagonalIdeal X.hom) := rfl
  have hw : Stacks.Hilbert.pointGraph X T y ≫ Stacks.Hilbert.familyBaseChangeMap X y =
      y.left ≫ pullback.diagonal X.hom := by
    simpa only [Category.comp_id, pointGraph_id_eq_diagonal X] using
      Stacks.Hilbert.pointGraph_comp_familyBaseChangeMap X y (𝟙 X)
  rw [← graphFamily_class_baseChange X T y, hD,
    Stacks.Picard.schemePullbackClass_comp, hw,
    ← Stacks.Picard.schemePullbackClass_comp,
    DiagonalNormalPicard.diagonal_picardClass_pullback X.hom]
  exact map_neg (Stacks.Picard.schemePullbackClassHom y.left) _

end M9Native.GraphNormalPicard
