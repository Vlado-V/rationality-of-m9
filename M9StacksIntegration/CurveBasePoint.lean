module

public import M9StacksIntegration.BaseFieldPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurvePower
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs

/-! An actual original-field point of an original curve over an
algebraically closed field. This removes a choice of marking from the
downstream genus-nine existence statement. -/

@[expose] public noncomputable section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Stacks.CurvePower

universe u
namespace M9Native.CurveBasePoint

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsCurve k C.hom]

theorem nonempty : Nonempty (power C 0 ⟶ C) := by
  obtain ⟨p, hp⟩ := BaseFieldPoints.exists_point C.hom
  exact ⟨Over.homMk p hp⟩

def point : power C 0 ⟶ C := Classical.choice (nonempty k C)

theorem point_over : (point k C).left ≫ C.hom = 𝟙 (Spec (.of k)) :=
  Over.w (point k C)

end M9Native.CurveBasePoint
