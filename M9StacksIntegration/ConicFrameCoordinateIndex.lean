module

public import M9StacksIntegration.GrassmannianCharts
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic

/-! The concrete correspondence between eight normalized quotient entries
and the native Grassmannian chart's actual coordinate indices. -/

@[expose] public noncomputable section

namespace M9Native.ConicFrameCoordinateIndex

open AlgebraicGeometry.Grassmannian

universe u

def pivotEmbedding : Fin 2 ↪ Fin 6 := Fin.castLEEmb (by decide)

theorem notMem_range_iff (j : Fin 6) : j ∉ Set.range pivotEmbedding ↔ 2 ≤ j.val := by
  fin_cases j <;> decide

def nonpivotEquiv : Fin 4 ≃ {j : Fin 6 // j ∉ Set.range pivotEmbedding} where
  toFun j := ⟨Fin.natAdd 2 j,(notMem_range_iff _).mpr (by
    change 2 ≤ 2 + j.val
    omega)⟩
  invFun j := ⟨j.val.val - 2,by
    have h := (notMem_range_iff j.val).mp j.property
    have hj := j.val.isLt
    omega⟩
  left_inv j := by
    apply Fin.ext
    dsimp
    omega
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have h := (notMem_range_iff j.val).mp j.property
    dsimp
    omega

/-- Native coordinates are ordered by nonpivot column and then quotient row. -/
def coordinateEquiv : ChartIndex.{u} (k := 4) (n := 6) pivotEmbedding ≃ Fin 8 :=
  (Equiv.ulift.trans (Equiv.prodCongr nonpivotEquiv.symm (Equiv.refl (Fin 2)))).trans finProdFinEquiv

theorem coordinateEquiv_symm_row (j : Fin 8) :
    ((coordinateEquiv.{u}).symm j).down.2 =
      ((finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8).symm j).2 := rfl

theorem coordinateEquiv_symm_column (j : Fin 8) :
    ((coordinateEquiv.{u}).symm j).down.1.val =
      Fin.natAdd 2 ((finProdFinEquiv : Fin 4 × Fin 2 ≃ Fin 8).symm j).1 := by
  simp [coordinateEquiv,nonpivotEquiv]

end M9Native.ConicFrameCoordinateIndex
