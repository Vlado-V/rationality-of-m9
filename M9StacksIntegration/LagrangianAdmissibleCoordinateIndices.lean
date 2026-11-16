module

public import M9StacksIntegration.LagrangianPrimitiveQuadrics
public import M9StacksIntegration.LagrangianAdmissibleMinors

/-! Exact original primitive coordinate indices of the eight admissible
minors. The native coordinateBasis14 reindex is retained literally. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
open MvPolynomial
universe u

namespace M9Native.LagrangianAdmissibleCoordinateIndices
open LagrangianHomogeneousQuadrics LagrangianPrimitiveQuadrics
def admissibleBlockIndex : AdmissibleIndex → CoordinateIndex.{u} :=
  Sum.elim (fun _ => Sum.inl ())
    (Sum.elim (fun _ => Sum.inr (Sum.inr (Sum.inr ())))
      (Sum.elim (fun i => Sum.inr (Sum.inr (Sum.inl (ULift.up ⟨(i,i), le_rfl⟩))))
        (fun i => Sum.inr (Sum.inl (ULift.up ⟨(i,i), le_rfl⟩)))))

def admissibleIndex (i : AdmissibleIndex) : Fin 14 :=
  LagrangianCoordinateBasisEntries.indexEquiv
    (Sum.elim (fun _ => Sum.inl ())
      (Sum.elim (fun _ => Sum.inr (Sum.inr (Sum.inr ())))
        (Sum.elim (fun j => Sum.inr (Sum.inr (Sum.inl ⟨(j,j), le_rfl⟩)))
          (fun j => Sum.inr (Sum.inl ⟨(j,j), le_rfl⟩)))) i)

variable (K : Type u) [Field K]

theorem rename_admissibleCoordinate (i : AdmissibleIndex) :
    (MvPolynomial.rename coordinateIndexEquiv : LagrangianHomogeneousQuadrics.Ring K →ₐ[K]
      MvPolynomial (Fin 14) K) (admissibleCoordinate K i) = X (admissibleIndex i) := by
  cases i with
  | inl i =>
    simp [admissibleCoordinate, aVariable, admissibleIndex, coordinateIndexEquiv, blockIndexEquiv]
  | inr i =>
    cases i with
    | inl i =>
      simp [admissibleCoordinate, bVariable, admissibleIndex, coordinateIndexEquiv, blockIndexEquiv]
    | inr i =>
      cases i with
      | inl i =>
        simp [admissibleCoordinate, pMatrix, admissibleIndex, admissibleBlockIndex,
          LagrangianMatrixChart.symmetricIndex, coordinateIndexEquiv, blockIndexEquiv]
      | inr i =>
        simp [admissibleCoordinate, qMatrix, admissibleIndex, admissibleBlockIndex,
          LagrangianMatrixChart.symmetricIndex, coordinateIndexEquiv, blockIndexEquiv]



def choiceAdmissible (s : LagrangianAdmissibleMinors.Choice) : AdmissibleIndex :=
  if s 0 then
    if s 1 then
      if s 2 then Sum.inr (Sum.inl ()) else Sum.inr (Sum.inr (Sum.inr 2))
    else
      if s 2 then Sum.inr (Sum.inr (Sum.inr 1)) else Sum.inr (Sum.inr (Sum.inl 0))
  else
    if s 1 then
      if s 2 then Sum.inr (Sum.inr (Sum.inr 0)) else Sum.inr (Sum.inr (Sum.inl 1))
    else
      if s 2 then Sum.inr (Sum.inr (Sum.inl 2)) else Sum.inl ()

def choiceIndex (s : LagrangianAdmissibleMinors.Choice) : Fin 14 :=
  admissibleIndex (choiceAdmissible s)

def choiceForAdmissible : AdmissibleIndex → LagrangianAdmissibleMinors.Choice :=
  Sum.elim (fun _ _ => false)
    (Sum.elim (fun _ _ => true)
      (Sum.elim (fun j i => decide (i = j)) (fun j i => decide (i ≠ j))))

theorem choiceAdmissible_choiceForAdmissible (i : AdmissibleIndex) :
    choiceAdmissible (choiceForAdmissible i) = i := by
  cases i with
  | inl i => simp [choiceAdmissible, choiceForAdmissible]
  | inr i =>
    cases i with
    | inl i => simp [choiceAdmissible, choiceForAdmissible]
    | inr i =>
      cases i with
      | inl i => fin_cases i <;> simp [choiceAdmissible, choiceForAdmissible]
      | inr i => fin_cases i <;> simp [choiceAdmissible, choiceForAdmissible]

theorem choiceAdmissible_surjective : Function.Surjective choiceAdmissible :=
  fun i => ⟨choiceForAdmissible i, choiceAdmissible_choiceForAdmissible i⟩

end M9Native.LagrangianAdmissibleCoordinateIndices
