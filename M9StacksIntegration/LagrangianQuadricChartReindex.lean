module

public import M9StacksIntegration.LagrangianPrimitiveQuadrics
public import M9StacksIntegration.LagrangianQuadricDehomogenization
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Dehomogenization

/-! The native projective a-chart, with its actual Fin.succAbove
coordinate order, is identified with the literal (q,b,p) graph ring.
The coordinate change retains the original primitive basis reindex. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open MvPolynomial

universe u

namespace M9Native.LagrangianQuadricChartReindex

open LagrangianQuadricChartAlgebra LagrangianPrimitiveQuadrics

def localRestEquiv : LocalIndex.{u} ≃ (SymIndex.{u} ⊕ (SymIndex.{u} ⊕ Unit)) :=
  (Equiv.sumAssoc SymIndex.{u} Unit SymIndex.{u}).trans
    (Equiv.sumCongr (Equiv.refl SymIndex.{u}) (Equiv.sumComm Unit SymIndex.{u}))

def localInjection (j : LocalIndex.{u}) : LagrangianHomogeneousQuadrics.CoordinateIndex.{u} :=
  Sum.inr (localRestEquiv j)

def optionCoordinateEquiv : Option LocalIndex.{u} ≃ LagrangianHomogeneousQuadrics.CoordinateIndex.{u} where
  toFun := Option.elim' (Sum.inl ()) localInjection
  invFun := Sum.elim (fun _ => none) (fun r => some (localRestEquiv.symm r))
  left_inv j := by cases j <;> simp [localInjection]
  right_inv j := by
    cases j with
    | inl j => cases j; rfl
    | inr r => simp [localInjection]

def aIndex : Fin 14 := LagrangianCoordinateBasisEntries.indexEquiv (Sum.inl ())

def localComplementEquiv : LocalIndex.{u} ≃
    {i : LagrangianHomogeneousQuadrics.CoordinateIndex.{u} // i ≠ Sum.inl ()} := by
  classical
  exact Equiv.optionSubtype (Sum.inl ()) ⟨optionCoordinateEquiv, rfl⟩

def coordinateComplementEquiv :
    {i : LagrangianHomogeneousQuadrics.CoordinateIndex.{u} // i ≠ Sum.inl ()} ≃
      {j : Fin 14 // j ≠ aIndex} :=
  coordinateIndexEquiv.subtypeEquiv (fun i => by
    exact (not_congr coordinateIndexEquiv.injective.eq_iff).symm)

def localIndexEquiv : LocalIndex.{u} ≃ Fin 13 :=
  (localComplementEquiv.trans coordinateComplementEquiv).trans (finSuccAboveEquiv aIndex).symm

theorem succAbove_localIndexEquiv (j : LocalIndex.{u}) :
    aIndex.succAbove (localIndexEquiv j) = coordinateIndexEquiv (localInjection j) := by
  have h := congrArg Subtype.val ((finSuccAboveEquiv aIndex).apply_symm_apply
    (coordinateComplementEquiv (localComplementEquiv j)))
  exact h

variable (R : Type u) [CommRing R]

def chartRingEquiv : MvPolynomial (Fin 13) R ≃ₐ[R] LocalRing R :=
  MvPolynomial.renameEquiv R localIndexEquiv.symm

def nativeDehom : MvPolynomial (Fin 14) R →+* LocalRing R :=
  (chartRingEquiv R).toRingHom.comp (Stacks.ProjectiveChart.dehomCoeff R aIndex)

theorem nativeDehom_a : nativeDehom R (X aIndex) = 1 := by
  simp [nativeDehom, Stacks.ProjectiveChart.dehomCoeff_eq_aeval]

theorem dehomCoeff_localCoordinate (j : LocalIndex.{u}) :
    Stacks.ProjectiveChart.dehomCoeff R aIndex (X (coordinateIndexEquiv (localInjection j))) =
      X (localIndexEquiv j) := by
  rw [← succAbove_localIndexEquiv, Stacks.ProjectiveChart.dehomCoeff_eq_aeval]
  simp

theorem nativeDehom_localCoordinate (j : LocalIndex.{u}) :
    nativeDehom R (X (coordinateIndexEquiv (localInjection j))) = X j := by
  rw [nativeDehom, RingHom.comp_apply, dehomCoeff_localCoordinate]
  simp [chartRingEquiv]

theorem blockDehom_localCoordinate (j : LocalIndex.{u}) :
    LagrangianQuadricDehomogenization.dehom R (X (localInjection j)) = X j := by
  cases j with
  | inl j => cases j <;> simp [localInjection, localRestEquiv, LagrangianQuadricDehomogenization.dehom]
  | inr j => simp [localInjection, localRestEquiv, LagrangianQuadricDehomogenization.dehom]

/-- The actual native dehomogenization diagram commutes on the entire
polynomial ring, not only on points or on degree-two forms. -/
theorem nativeDehom_comp_rename :
    (nativeDehom R).comp
      (MvPolynomial.rename coordinateIndexEquiv : LagrangianHomogeneousQuadrics.Ring R →ₐ[R]
        MvPolynomial (Fin 14) R).toRingHom =
      (LagrangianQuadricDehomogenization.dehom R).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [nativeDehom, Stacks.ProjectiveChart.dehomCoeff_eq_aeval, chartRingEquiv,
      LagrangianQuadricDehomogenization.dehom]
  · intro i
    change nativeDehom R (MvPolynomial.rename coordinateIndexEquiv (X i)) =
      LagrangianQuadricDehomogenization.dehom R (X i)
    rw [MvPolynomial.rename_X]
    obtain ⟨o, rfl⟩ := optionCoordinateEquiv.surjective i
    cases o with
    | none =>
      change nativeDehom R (X aIndex) = _
      rw [nativeDehom_a]
      simp [optionCoordinateEquiv, LagrangianQuadricDehomogenization.dehom]
    | some j =>
      change nativeDehom R (X (coordinateIndexEquiv (localInjection j))) = _
      rw [nativeDehom_localCoordinate]
      exact (blockDehom_localCoordinate R j).symm

variable (K : Type u) [Field K]

theorem nativeDehom_quadric (i : LagrangianHomogeneousQuadrics.QuadricIndex.{u}) :
    nativeDehom K (LagrangianPrimitiveQuadrics.quadric K i) =
      LagrangianQuadricDehomogenization.dehom K (LagrangianHomogeneousQuadrics.quadric K i) :=
  RingHom.congr_fun (nativeDehom_comp_rename K) _

def nativeChartIdeal : Ideal (MvPolynomial (Fin 13) K) :=
  Ideal.span (Set.range fun i : LagrangianHomogeneousQuadrics.QuadricIndex.{u} =>
    Stacks.ProjectiveChart.dehomCoeff K aIndex (LagrangianPrimitiveQuadrics.quadric K i))

theorem map_nativeChartIdeal : (nativeChartIdeal K).map (chartRingEquiv K).toRingHom =
    LagrangianQuadricDehomogenization.dehomIdeal K := by
  rw [nativeChartIdeal, Ideal.map_span, ← Set.range_comp,
    LagrangianQuadricDehomogenization.dehomIdeal]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  exact nativeDehom_quadric K i

def nativeGraphMap : MvPolynomial (Fin 13) K →ₐ[K] AffineRing K :=
  (graphMap K).comp (chartRingEquiv K).toAlgHom

/-- The exact kernel on the ORIGINAL native projective a-chart is the
ideal of the actual dehomogenized twenty-one equations. -/
theorem ker_nativeGraphMap : RingHom.ker (nativeGraphMap K).toRingHom = nativeChartIdeal K := by
  change (RingHom.ker (graphMap K).toRingHom).comap (chartRingEquiv K).toRingHom = _
  rw [← LagrangianQuadricDehomogenization.dehomIdeal_eq_graphKernel, ← map_nativeChartIdeal]
  exact Ideal.comap_map_of_bijective _ (chartRingEquiv K).bijective

end M9Native.LagrangianQuadricChartReindex
