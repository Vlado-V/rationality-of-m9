module

public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointResidueField

/-! Actual closed-point residue-field comparisons over the original algebraically closed base. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.ParameterClosedResidueField

variable (K : Type u) [Field K] [IsAlgClosed K] {T : Scheme.{u}}
  (s : T ⟶ Spec (.of K)) [LocallyOfFiniteType s]

/-- The isomorphism comes from the original structural residue map at the closed point. -/
def residueIso (x : T) (hx : IsClosed ({x} : Set T)) :
    CommRingCat.of K ≅ T.residueField x := by
  have : LocallyOfFiniteType (s ≫ 𝟙 _) := by simpa using (inferInstance : LocallyOfFiniteType s)
  have : IsIso (s.residueFieldMap x) :=
    isIso_residueFieldMap_of_isClosed s (𝟙 _) x hx
  exact (Scheme.Spec.residueFieldIsoOfField (s x)).symm ≪≫ asIso (s.residueFieldMap x)

include K s in
/-- Algebraic closedness of the actual residue field is derived, not supplied. -/
theorem isAlgClosed (x : T) (hx : IsClosed ({x} : Set T)) :
    IsAlgClosed (T.residueField x) :=
  IsAlgClosed.of_ringEquiv K (T.residueField x)
    (residueIso K s x hx).commRingCatIsoToRingEquiv

include K s in
/-- Characteristic zero reaches the same original residue field. -/
theorem charZero [CharZero K] (x : T) (hx : IsClosed ({x} : Set T)) :
    CharZero (T.residueField x) :=
  charZero_of_injective_ringHom (residueIso K s x hx).commRingCatIsoToRingEquiv.injective

end M9Native.ParameterClosedResidueField
