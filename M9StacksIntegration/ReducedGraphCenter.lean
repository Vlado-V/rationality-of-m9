module

public import M9StacksIntegration.ReducedGraphGenericPoint
public import M9StacksIntegration.GraphCentralMatrices

/-! Actual cubic-center action on the genuine native graph generic point.
The determinant twist is kept as a fixed-field quotient. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

namespace M9Native.ReducedGraphCenter

open M9.GraphBundleDescent GraphGrassmannianChart GraphCentralMatrices
open ReducedGraphAction ReducedGraphGenericPoint
open AlgebraicGeometry.Grassmannian LagrangianMatrixChart

abbrev FF := ChartFunctionField ℂ
abbrev GS := GenericSpec ℂ
abbrev NativeField := (GrassmannianCharts.space ℂ 4 12).functionField
abbrev Roots := rootsOfUnity 3 ℂ

theorem root_cube (a : Roots) : (a.val : ℂ) ^ 3 = 1 := by
  have h : a.val ^ 3 = 1 := (mem_rootsOfUnity 3 a.val).mp a.property
  exact congrArg Units.val h

def centralElement (a : Roots) : Stabilizer ℂ :=
  SemidirectProduct.inl (M9.PrimitiveRepresentation.centralElement ℂ (a.val : ℂ) (root_cube a))

def rootF (a : Roots) : FFˣ := Units.map (algebraMap ℂ FF).toMonoidHom a.val

def globalRoot (a : Roots) : Γ(GS, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (.of FF)).inv.hom.toMonoidHom (rootF a)

theorem rootF_cube (a : Roots) : rootF a ^ 3 = 1 := by
  rw [rootF, ← map_pow]
  have h : a.val ^ 3 = 1 := (mem_rootsOfUnity 3 a.val).mp a.property
  rw [h, map_one]

theorem rootF_weights (a : Roots) : (rootF a : FF)^2 = (↑(rootF a)⁻¹ : FF)^2 * (rootF a : FF) := by
  have h : rootF a ^ 2 = ((rootF a)⁻¹)^2 * rootF a := by
    calc
      rootF a ^ 2 = (rootF a)⁻¹ * rootF a ^ 3 := by group
      _ = (rootF a)⁻¹ := by rw [rootF_cube, mul_one]
      _ = ((rootF a)⁻¹)^2 * rootF a := by group
  exact congrArg Units.val h

/-- The existing actual matrix-coordinate field action on this generic spectrum. -/
def chartSchemeAction (a : Roots) : GS ⟶ GS :=
  Spec.map (CommRingCat.ofHom (chartCentralAction a).toRingHom)

instance chartSchemeAction_isIso (a : Roots) : IsIso (chartSchemeAction a) := by
  unfold chartSchemeAction
  have : IsIso (CommRingCat.ofHom (chartCentralAction a).toRingHom) :=
    (chartCentralAction a).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

instance chartSchemeAction_isDominant (a : Roots) : IsDominant (chartSchemeAction a) :=
  ⟨(chartSchemeAction a).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem chartSchemeAction_projection (a : Roots) :
    chartSchemeAction a ≫ genericProjection ℂ = genericProjection ℂ := by
  rw [chartSchemeAction, genericProjection, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (chartCentralAction a).toAlgHom.comp_algebraMap

theorem nativeGraphPoint_projection :
    nativeGraphPoint ℂ ≫ GrassmannianCharts.projection ℂ 4 12 = genericProjection ℂ := by
  rw [nativeGraphPoint, Category.assoc, graphMap_projection,
    genericToDomain, domainProjection, genericProjection, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (chartLocalizationToField ℂ).comp_algebraMap

/-- Pullback of the genuine free target is normalized by its canonical iso. -/
def shiftedPresentation (a : Roots) : QuotientPresentation GS 4 12 := by
  let q := pullbackPresentation (chartSchemeAction a) (genericPresentation ℂ)
  let : Epi q.map := q.map_epi
  exact { target := freeOn GS 8
          map := q.map ≫ (pullbackFreeIso (chartSchemeAction a) 8).hom
          map_epi := inferInstance
          finiteLocallyFree := free_isFiniteLocallyFreeOfRank GS 8 }

theorem shiftedPresentation_isomorphic (a : Roots) :
    (pullbackPresentation (chartSchemeAction a) (genericPresentation ℂ)).Isomorphic
      (shiftedPresentation a) := ⟨pullbackFreeIso (chartSchemeAction a) 8, rfl⟩

theorem shiftedPresentation_matrix (a : Roots) :
    Stacks.FreeSheafMatrix.toMatrix (shiftedPresentation a).map =
      (Stacks.FreeSheafMatrix.toMatrix (genericPresentation ℂ).map).map (chartSchemeAction a).appTop.hom := by
  change Stacks.FreeSheafMatrix.toMatrix
    (ConicFrameLeftEquivariance.pulledFreeMap (chartSchemeAction a) 12 8 (genericPresentation ℂ).map) = _
  exact ConicFrameLeftEquivariance.pulledFreeMap_matrix _ _ _ _

theorem genericBase_shift (a : Roots) (s : Fin 2) :
    (genericBase ℂ s).map (chartCentralAction a).toRingHom = genericBase ℂ s := by
  ext i j
  change chartCentralAction a (chartLocalizationToField ℂ
    (algebraMap (ChartRing ℂ) (IsomChartRing ℂ) (MvPolynomial.X (Sum.inl (s,(i,j)))))) =
    chartLocalizationToField ℂ
      (algebraMap (ChartRing ℂ) (IsomChartRing ℂ) (MvPolynomial.X (Sum.inl (s,(i,j)))))
  rw [chartLocalizationToField_polynomial, chartCentralAction_base]

theorem genericIsomorphism_val : (genericIsomorphism ℂ).val = chartGenericFiber ℂ := by
  ext i j
  exact chartLocalizationToField_polynomial ℂ _

theorem genericIsomorphism_shift (a : Roots) :
    (genericIsomorphism ℂ).val.map (chartCentralAction a).toRingHom =
      (rootF a : FF) • (genericIsomorphism ℂ).val := by
  rw [genericIsomorphism_val]
  ext i j
  exact chartCentralAction_fiber a (i,j)

theorem globalize_pullback (σ : FF →+* FF) (M : Matrix (Fin 8) (Fin 12) FF) :
    (globalize ℂ M).map (Spec.map (CommRingCat.ofHom σ)).appTop.hom =
      globalize ℂ (M.map σ) := by
  ext i j
  change (Spec.map (CommRingCat.ofHom σ)).appTop ((Scheme.ΓSpecIso (.of FF)).inv (M i j)) =
    (Scheme.ΓSpecIso (.of FF)).inv (σ (M i j))
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem shiftedPresentation_matrix_actual (a : Roots) :
    Stacks.FreeSheafMatrix.toMatrix (shiftedPresentation a).map =
      globalize ℂ (kernelMatrix (blockRows (genericBase ℂ 0)
        ((rootF a : FF) • (genericIsomorphism ℂ).val)
        (genericBase ℂ 1 * ((rootF a : FF) • (genericIsomorphism ℂ).val)))) := by
  rw [shiftedPresentation_matrix, genericPresentation_matrix_actual]
  change (globalize ℂ _).map (Spec.map (CommRingCat.ofHom (chartCentralAction a).toRingHom)).appTop.hom = _
  rw [globalize_pullback, kernelMatrix_map, blockRows_map, Matrix.map_mul,
    genericBase_shift, genericBase_shift, genericIsomorphism_shift]

/-- A literal unit matrix gives an actual free-sheaf isomorphism in every rank. -/
def freeMatrixIso (T : Scheme) (n : ℕ) (g : Matrix.GeneralLinearGroup (Fin n) Γ(T, ⊤)) :
    freeOn T n ≅ freeOn T n where
  hom := Stacks.FreeSheafMatrix.ofMatrix g.val
  inv := Stacks.FreeSheafMatrix.ofMatrix g⁻¹.val
  hom_inv_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id]
    exact Units.inv_mul g
  inv_hom_id := by
    apply Stacks.FreeSheafMatrix.toMatrix_injective
    rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
      Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_id]
    exact Units.mul_inv g

theorem freeMatrixIso_matrix (T : Scheme) (n : ℕ)
    (g : Matrix.GeneralLinearGroup (Fin n) Γ(T, ⊤)) :
    Stacks.FreeSheafMatrix.toMatrix (freeMatrixIso T n g).hom = g.val :=
  Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

theorem scalarMap_genericProjection :
    GraphGrassmannianLinearAction.scalarMap ℂ (genericProjection ℂ) =
      (Scheme.ΓSpecIso (.of FF)).inv.hom.comp (algebraMap ℂ FF) := by
  ext c
  change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ FF))).appTop) c = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem nativeCenter_constantMatrix (a : Roots) :
    GraphGrassmannianLinearAction.constantMatrix ℂ (genericProjection ℂ)
        (matrixRepresentation ℂ (centralElement a)) =
      Matrix.diagonal (ambientWeights ((globalRoot a : Γ(GS, ⊤))^2)
        ((↑(globalRoot a)⁻¹ : Γ(GS, ⊤))^2)) := by
  rw [GraphGrassmannianLinearAction.constantMatrix, centralElement,
    matrixRepresentation_center_diagonal, diagonal_ambientWeights_map]
  have hv : (globalRoot a : Γ(GS, ⊤)) =
      GraphGrassmannianLinearAction.scalarMap ℂ (genericProjection ℂ) (a.val : ℂ) := by
    rw [scalarMap_genericProjection]
    rfl
  have hvi : (↑(globalRoot a)⁻¹ : Γ(GS, ⊤)) =
      GraphGrassmannianLinearAction.scalarMap ℂ (genericProjection ℂ) (↑a.val⁻¹ : ℂ) := by
    rw [scalarMap_genericProjection]
    rfl
  rw [map_pow, map_pow, ← Units.val_inv_eq_inv_val, ← hv, ← hvi]

def targetIso (a : Roots) : freeOn GS 8 ≅ freeOn GS 8 :=
  freeMatrixIso GS 8 (rowDiagonalUnit ((globalRoot a)^2) (((globalRoot a)⁻¹)^2))

theorem targetIso_matrix (a : Roots) :
    Stacks.FreeSheafMatrix.toMatrix (targetIso a).hom =
      Matrix.diagonal (rowWeights ((globalRoot a : Γ(GS, ⊤))^2)
        ((↑(globalRoot a)⁻¹ : Γ(GS, ⊤))^2)) := by
  rw [targetIso, freeMatrixIso_matrix, rowDiagonalUnit_val]
  rfl

/-- The actual two graph quotients differ by the explicit target diagonal iso. -/
theorem shiftedPresentation_transform (a : Roots) :
    (shiftedPresentation a).Isomorphic
      (GraphGrassmannianLinearAction.transform ℂ (genericProjection ℂ)
        (matrixRepresentation ℂ (centralElement a)) (genericPresentation ℂ)) := by
  refine ⟨targetIso a, ?_⟩
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  change Stacks.FreeSheafMatrix.toMatrix ((shiftedPresentation a).map ≫ (targetIso a).hom) =
    Stacks.FreeSheafMatrix.toMatrix
      ((GraphGrassmannianLinearAction.constantFreeIso ℂ (genericProjection ℂ)
        (matrixRepresentation ℂ (centralElement a))).hom ≫ (genericPresentation ℂ).map)
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_comp,
    targetIso_matrix, GraphGrassmannianLinearAction.constantFreeIso_matrix,
    shiftedPresentation_matrix_actual, genericPresentation_matrix_actual, nativeCenter_constantMatrix]
  have h := congrArg (fun M : Matrix (Fin 8) (Fin 12) FF =>
      M.map (Scheme.ΓSpecIso (.of FF)).inv.hom)
    (kernelMatrix_scaled (genericBase ℂ 0) (genericBase ℂ 1) (genericIsomorphism ℂ).val
      ((rootF a : FF)^2) ((↑(rootF a)⁻¹ : FF)^2) (rootF a : FF) (rootF_weights a))
  rw [Matrix.map_mul, Matrix.map_mul, diagonal_ambientWeights_map,
    diagonal_rowWeights_map, map_pow, map_pow] at h
  exact h.symm

/-- Equality of actual native scheme maps on the original generic spectrum. -/
theorem nativeGraphPoint_center (a : Roots) :
    chartSchemeAction a ≫ nativeGraphPoint ℂ =
      nativeGraphPoint ℂ ≫ nativeAction ℂ (centralElement a) := by
  apply GraphGrassmannianLinearAction.hom_ext ℂ
  · simp only [Category.assoc, nativeAction_projection, nativeGraphPoint_projection,
      chartSchemeAction_projection]
  · change GraphGrassmannianLinearAction.pointClass ℂ (chartSchemeAction a ≫ nativeGraphPoint ℂ) =
      GraphGrassmannianLinearAction.pointClass ℂ
        (nativeGraphPoint ℂ ≫ GraphGrassmannianLinearAction.action ℂ
          (matrixRepresentation ℂ (centralElement a)))
    rw [GraphGrassmannianLinearAction.pointClass_comp, nativeGraphPoint_class,
      GraphGrassmannianLinearAction.pointClass_action, nativeGraphPoint_projection, nativeGraphPoint_class]
    change (⟦pullbackPresentation (chartSchemeAction a) (genericPresentation ℂ)⟧ : Points GS 4 12) =
      ⟦GraphGrassmannianLinearAction.transform ℂ (genericProjection ℂ)
        (matrixRepresentation ℂ (centralElement a)) (genericPresentation ℂ)⟧
    exact Quotient.sound (.trans _ _ _
      (.rel _ _ (shiftedPresentation_isomorphic a))
      (.rel _ _ (shiftedPresentation_transform a)))

theorem affineFieldEquiv_chartAction (a : Roots) (z : GS.functionField) :
    affineFieldEquiv ℂ (NativeDominantFunctionField.map (chartSchemeAction a) z) =
      chartCentralAction a (affineFieldEquiv ℂ z) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (chartCentralAction a).toRingHom)) :=
    chartSchemeAction_isDominant a
  have hh : (affineFieldEquiv ℂ).toRingHom.comp
      (NativeDominantFunctionField.map (chartSchemeAction a)) =
        (chartCentralAction a).toRingHom.comp (affineFieldEquiv ℂ).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := FF)
    intro b
    change affineFieldEquiv ℂ (NativeDominantFunctionField.map
      (Spec.map (CommRingCat.ofHom (chartCentralAction a).toRingHom))
        (algebraMap FF GS.functionField b)) = _
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, affineFieldEquiv_algebraMap]
    change chartCentralAction a b = chartCentralAction a
      (affineFieldEquiv ℂ (algebraMap FF GS.functionField b))
    rw [affineFieldEquiv_algebraMap]
  exact DFunLike.congr_fun hh z

/-- The actual native cubic-center action is the actual graph-coordinate
scaling action, through the original native generic-stalk comparison. -/
theorem nativeField_center (a : Roots) (z : NativeField) :
    graphFunctionFieldEquiv ℂ (nativeFieldRepresentation ℂ (centralElement a) z) =
      chartCentralAction a (graphFunctionFieldEquiv ℂ z) := by
  have hh := GraphGrassmannianLinearAction.dominantMap_congr (nativeGraphPoint_center a)
  rw [NativeFunctionFieldFunctor.map_comp, NativeFunctionFieldFunctor.map_comp] at hh
  have hz := DFunLike.congr_fun hh z
  change NativeDominantFunctionField.map (chartSchemeAction a)
      (NativeDominantFunctionField.map (nativeGraphPoint ℂ) z) =
    NativeDominantFunctionField.map (nativeGraphPoint ℂ)
      (NativeDominantFunctionField.map (nativeAction ℂ (centralElement a)) z) at hz
  rw [← nativeGraphPoint_pullback, ← nativeGraphPoint_pullback]
  change affineFieldEquiv ℂ (NativeDominantFunctionField.map (nativeGraphPoint ℂ)
      ((nativeFieldRepresentation ℂ (centralElement a)).toRingHom z)) = _
  rw [nativeFieldRepresentation_eq_map, ← hz, affineFieldEquiv_chartAction]

/-- This subfield is identified below with the actual native central invariants. -/
def nativeCentralFixedField : IntermediateField ℂ NativeField :=
  chartCentralFixedField.comap (graphFunctionFieldEquiv ℂ).toAlgHom

theorem mem_nativeCentralFixedField_iff (z : NativeField) : z ∈ nativeCentralFixedField ↔
    ∀ a : Roots, nativeFieldRepresentation ℂ (centralElement a) z = z := by
  change graphFunctionFieldEquiv ℂ z ∈ chartCentralFixedField ↔ _
  rw [mem_chartCentralFixedField_iff]
  constructor
  · intro h a
    apply (graphFunctionFieldEquiv ℂ).injective
    rw [nativeField_center]
    exact h a
  · intro h a
    rw [← nativeField_center, h a]

def nativeCentralCoordinates : nativeCentralFixedField ≃ₐ[ℂ] chartCentralFixedField where
  toFun z := ⟨graphFunctionFieldEquiv ℂ z.val, z.property⟩
  invFun z := ⟨(graphFunctionFieldEquiv ℂ).symm z.val, by
    change graphFunctionFieldEquiv ℂ ((graphFunctionFieldEquiv ℂ).symm z.val) ∈ chartCentralFixedField
    rw [AlgEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv z := Subtype.ext ((graphFunctionFieldEquiv ℂ).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((graphFunctionFieldEquiv ℂ).apply_symm_apply z.val)
  map_mul' z w := Subtype.ext (map_mul _ _ _)
  map_add' z w := Subtype.ext (map_add _ _ _)
  commutes' c := Subtype.ext ((graphFunctionFieldEquiv ℂ).commutes c)

/-- Actual determinant-twisted generic coordinates parametrize the actual
native cubic-center fixed field. The original native field is not replaced. -/
def nativeDeterminantQuotient : ChartFunctionField ℂ ≃ₐ[ℂ] nativeCentralFixedField :=
  chartCentralQuotientEquiv.trans nativeCentralCoordinates.symm

theorem nativeDeterminantQuotient_coordinates (z : ChartFunctionField ℂ) :
    graphFunctionFieldEquiv ℂ (nativeDeterminantQuotient z).val =
      (chartCentralQuotientEquiv z).val :=
  congrArg Subtype.val (nativeCentralCoordinates.apply_symm_apply (chartCentralQuotientEquiv z))

theorem nativeDeterminantQuotient_base (b : BaseIndex) :
    graphFunctionFieldEquiv ℂ (nativeDeterminantQuotient
      (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (MvPolynomial.X (Sum.inl b)))).val =
      algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (MvPolynomial.X (Sum.inl b)) := by
  rw [nativeDeterminantQuotient_coordinates]
  exact chartCentralQuotient_base_coordinate b

theorem nativeDeterminantQuotient_fiber (ij : FiberIndex) :
    graphFunctionFieldEquiv ℂ (nativeDeterminantQuotient
      (algebraMap (ChartRing ℂ) (ChartFunctionField ℂ) (MvPolynomial.X (Sum.inr ij)))).val =
        M9.DeterminantTwist.twist (chartGenericFiber ℂ) ij.1 ij.2 := by
  rw [nativeDeterminantQuotient_coordinates]
  exact chartCentralQuotient_fiber_coordinate ij

end M9Native.ReducedGraphCenter
