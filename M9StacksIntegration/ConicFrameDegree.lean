module

public import M9StacksIntegration.ConicFrameFieldComparison
public import M9StacksIntegration.ConicFramePointFiber

/-! The actual conic-frame morphism has function-field degree twenty-four.
The finite extension is derived from its concrete closed fibres, through
generic finite étale localization. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9Native.ConicFrameDegree

open ConicFrameProjective ConicFrameSourceAlgebra ConicFrameCoordinates
open ConicFrameExtension ConicFrameFieldComparison

theorem coordinateField_finite_degree :
    Module.Finite (targetField ℂ) (rationalField ℂ) ∧
      Module.finrank (targetField ℂ) (rationalField ℂ) = 24 :=
  finite_degree_of_pointLifts_card ℂ 24 (by norm_num)
    ConicFramePointFiber.card_pointLifts

theorem native_field_finrank :
    Module.finrank (GrassmannianCharts.space ℂ 4 6).functionField
      (ConicFrameProjective.space ℂ).functionField = 24 :=
  (native_finrank_eq ℂ).trans coordinateField_finite_degree.2

theorem native_field_finite :
    Module.Finite (GrassmannianCharts.space ℂ 4 6).functionField
      (ConicFrameProjective.space ℂ).functionField := by
  apply Module.finite_of_finrank_pos
  rw [native_field_finrank]
  norm_num

end M9Native.ConicFrameDegree
