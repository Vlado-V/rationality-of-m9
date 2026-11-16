module

public import M9StacksIntegration.ReducedGraphAction
public import M9StacksIntegration.ConicFrameLeftEquivariance
public import M9StacksIntegration.ConicFrameFieldComparison

/-! The actual native generic graph point, its literal graph quotient
presentation and its genuine generic-stalk coordinate pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

universe u

namespace M9Native.ReducedGraphGenericPoint

open M9.GraphBundleDescent GraphGrassmannianChart
open AlgebraicGeometry.Grassmannian LagrangianMatrixChart

variable (K : Type u) [Field K]

abbrev F := ChartFunctionField K
abbrev GenericSpec : Scheme.{u} := Spec (.of (F K))

def genericProjection : GenericSpec K ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (F K)))

def genericToDomain : GenericSpec K ⟶ domain K :=
  Spec.map (CommRingCat.ofHom (chartLocalizationToField K).toRingHom)

instance genericToDomain_isDominant : IsDominant (genericToDomain K) :=
  NativeDominantFunctionField.specMap_isDominant _
    (IsFractionRing.injective (IsomChartRing K) (F K))

instance graphMap_isDominant : IsDominant (graphMap K) := ⟨graphMap_dense K⟩

def nativeGraphPoint : GenericSpec K ⟶ GrassmannianCharts.space K 4 12 :=
  genericToDomain K ≫ graphMap K

instance nativeGraphPoint_isDominant : IsDominant (nativeGraphPoint K) := by
  unfold nativeGraphPoint
  infer_instance

def affineFieldEquiv : (GenericSpec K).functionField ≃+* F K :=
  (IsFractionRing.algEquiv (F K) (F K) (GenericSpec K).functionField).symm.toRingEquiv

@[simp] theorem affineFieldEquiv_algebraMap (z : F K) :
    affineFieldEquiv K (algebraMap (F K) (GenericSpec K).functionField z) = z :=
  (IsFractionRing.algEquiv (F K) (F K) (GenericSpec K).functionField).symm.commutes z

theorem genericToDomain_pullback (z : (domain K).functionField) :
    affineFieldEquiv K (NativeDominantFunctionField.map (genericToDomain K) z) =
      graphStalkCoordinates K z := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (chartLocalizationToField K).toRingHom)) :=
    genericToDomain_isDominant K
  have h : (affineFieldEquiv K).toRingHom.comp
        (NativeDominantFunctionField.map (genericToDomain K)) = (graphStalkCoordinates K).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := IsomChartRing K)
    intro b
    change affineFieldEquiv K (NativeDominantFunctionField.map
        (Spec.map (CommRingCat.ofHom (chartLocalizationToField K).toRingHom))
          (algebraMap (IsomChartRing K) (domain K).functionField b)) = _
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, affineFieldEquiv_algebraMap]
    change chartLocalizationToField K b = graphStalkCoordinates K
      (algebraMap (IsomChartRing K) (domain K).functionField b)
    rw [graphStalkCoordinates_coordinate]
    rfl
  exact DFunLike.congr_fun h z

/-- Exact native generic-stalk pullback, preserving all 32 original coordinates. -/
theorem nativeGraphPoint_pullback (z : (GrassmannianCharts.space K 4 12).functionField) :
    affineFieldEquiv K (NativeDominantFunctionField.map (nativeGraphPoint K) z) =
      graphFunctionFieldEquiv K z := by
  change affineFieldEquiv K (NativeDominantFunctionField.map (genericToDomain K ≫ graphMap K) z) = _
  rw [NativeFunctionFieldFunctor.map_comp, RingHom.comp_apply, genericToDomain_pullback]
  change graphFunctionFieldEquiv K ((grassmannianGraphStalkEquiv K).symm
    (NativeDominantFunctionField.map (graphMap K) z)) = _
  rw [← ConicFrameFieldComparison.openIso_eq_map (graphMap K)]
  exact congrArg (graphFunctionFieldEquiv K) ((grassmannianGraphStalkEquiv K).symm_apply_apply z)

def genericPresentation : QuotientPresentation (GenericSpec K) 4 12 := by
  let q := pullbackPresentation (genericToDomain K) (graphPresentation K)
  let : Epi q.map := q.map_epi
  exact { target := freeOn (GenericSpec K) 8
          map := q.map ≫ (pullbackFreeIso (genericToDomain K) 8).hom
          map_epi := inferInstance
          finiteLocallyFree := free_isFiniteLocallyFreeOfRank (GenericSpec K) 8 }

theorem genericPresentation_isomorphic :
    (pullbackPresentation (genericToDomain K) (graphPresentation K)).Isomorphic
      (genericPresentation K) := by
  exact ⟨pullbackFreeIso (genericToDomain K) 8, rfl⟩

/-- The generic native point classifies this actual pullback graph quotient. -/
theorem nativeGraphPoint_class :
    GraphGrassmannianLinearAction.pointClass K (nativeGraphPoint K) =
      ⟦genericPresentation K⟧ := by
  rw [nativeGraphPoint, GraphGrassmannianLinearAction.pointClass_comp]
  have hc : GraphGrassmannianLinearAction.pointClass K (graphMap K) =
      ⟦graphPresentation K⟧ := graphMap_class K
  rw [hc]
  exact Quotient.sound (.rel _ _ (genericPresentation_isomorphic K))

/-- Its actual free quotient matrix is obtained by literal coefficient pullback. -/
theorem genericPresentation_matrix : Stacks.FreeSheafMatrix.toMatrix (genericPresentation K).map =
    (Stacks.FreeSheafMatrix.toMatrix (graphQuotient K)).map (genericToDomain K).appTop.hom := by
  change Stacks.FreeSheafMatrix.toMatrix
    (ConicFrameLeftEquivariance.pulledFreeMap (genericToDomain K) 12 8 (graphQuotient K)) = _
  exact ConicFrameLeftEquivariance.pulledFreeMap_matrix _ _ _ _

def genericBase (s : Fin 2) : BaseMatrix (F K) :=
  (universalBaseLocalized (K := K) s).map (chartLocalizationToField K).toRingHom

def genericIsomorphism : Matrix.GeneralLinearGroup (Fin 4) (F K) :=
  Matrix.GeneralLinearGroup.map (chartLocalizationToField K).toRingHom (universalIsomorphism (K := K))

def globalize (M : Matrix (Fin 8) (Fin 12) (F K)) : Matrix (Fin 8) (Fin 12) Γ(GenericSpec K, ⊤) :=
  M.map (Scheme.ΓSpecIso (.of (F K))).inv.hom

theorem kernelMatrix_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (D : Matrix (Fin 8) (Fin 4) R) :
    (kernelMatrix D).map φ = kernelMatrix (D.map φ) := by
  classical
  ext i j
  obtain ⟨r, rfl⟩ := (finSumFinEquiv : Fin 4 ⊕ Fin 8 ≃ Fin 12).surjective j
  rcases r with j | j <;> simp [kernelMatrix, Matrix.map_apply]

theorem genericPresentation_matrix_actual :
    Stacks.FreeSheafMatrix.toMatrix (genericPresentation K).map =
      globalize K (kernelMatrix (blockRows (genericBase K 0) (genericIsomorphism K).val
        (genericBase K 1 * (genericIsomorphism K).val))) := by
  rw [genericPresentation_matrix, graphQuotient_matrix]
  rw [kernelMatrix_map, globalize, kernelMatrix_map]
  congr 1
  have hp (b : IsomChartRing K) : (genericToDomain K).appTop
      ((Scheme.ΓSpecIso (.of (IsomChartRing K))).inv b) =
      (Scheme.ΓSpecIso (.of (F K))).inv (chartLocalizationToField K b) := by
    change ((Scheme.ΓSpecIso (.of (IsomChartRing K))).inv ≫
      (Spec.map (CommRingCat.ofHom (chartLocalizationToField K).toRingHom)).appTop) b = _
    rw [← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have ha (s : Fin 2) : (globalBase K s).map (genericToDomain K).appTop.hom =
      (genericBase K s).map (Scheme.ΓSpecIso (.of (F K))).inv.hom := by
    ext i j
    exact hp _
  have hx : (globalIsomorphism K).val.map (genericToDomain K).appTop.hom =
      (genericIsomorphism K).val.map (Scheme.ΓSpecIso (.of (F K))).inv.hom := by
    ext i j
    exact hp _
  rw [blockRows_map, blockRows_map, Matrix.map_mul, Matrix.map_mul, ha 0, ha 1, hx]

end M9Native.ReducedGraphGenericPoint
