module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! Independence of a full-sized coordinate family from genuine algebraic field recovery. -/

@[expose] public noncomputable section

namespace M9Native.GeneratedCoordinateIndependence

open scoped IntermediateField.algebraAdjoinAdjoin

variable {k L ι : Type} [Field k] [Field L] [Algebra k L] [Fintype ι]

theorem algebraicIndependent_of_recovery (y : ι → L)
    (hAlg : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range y)) L)
    (htrdeg : Algebra.trdeg k L = Fintype.card ι) : AlgebraicIndependent k y := by
  let F := IntermediateField.adjoin k (Set.range y)
  let A := Algebra.adjoin k (Set.range y)
  letI : Algebra.IsAlgebraic F L := hAlg
  haveI : Algebra.IsAlgebraic A L := Algebra.IsAlgebraic.trans A F L
  have h := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite k y
    (by rw [htrdeg,Cardinal.mk_fintype])
  exact h.1

end M9Native.GeneratedCoordinateIndependence
