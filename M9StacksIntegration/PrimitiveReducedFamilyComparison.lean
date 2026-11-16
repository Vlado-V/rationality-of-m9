module

public import M9StacksIntegration.PrimitiveReducedFieldMatrixComposition
public import M9StacksIntegration.SL3UniversalFieldAction
public import M9StacksIntegration.SL3OddBaseChange

@[expose] public section

/-! Exact native field-point comparison with the genuine varying SL3 family
and the constant odd component, preserving all original matrix conventions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Classical Matrix

namespace M9Native.PrimitiveReducedFamilyComparison
open PrimitiveReducedFieldMatrixAction PrimitiveReducedFieldMatrixComposition

abbrev SliceField := (GrassmannianCharts.space ℂ 4 12).functionField

variable (K : Type) [Field K] [Algebra ℂ K]
local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K

theorem connected_matrix_map (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
        (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl g)) =
      ReducedGraphAction.matrixRepresentation K
        (SemidirectProduct.inl (Matrix.SpecialLinearGroup.map (algebraMap ℂ K) g)) := by
  apply Units.ext
  change (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl g)).val.map
    (algebraMap ℂ K) = _
  rw [← SL3ReducedFamily.matrixGL_eq_original,← SL3ReducedFamily.matrixGL_eq_original]
  exact SL3ReducedFamilyNaturality.matrixGL_map ℂ (algebraMap ℂ K) g

theorem inr_matrix_map (c : M9.CentralSignQuotient.C2) :
    Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
        (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inr c)) =
      ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inr c) := by
  rcases M9.CentralSignQuotient.c2_cases c with rfl | rfl
  · simp only [map_one]
  · apply Units.ext
    exact SL3OddBaseChange.odd_matrix_map K

/-- Literal extension of both components of a constant stabilizer element. -/
def extendConstant (w : ReducedGraphAction.Stabilizer ℂ) : ReducedGraphAction.Stabilizer K :=
  SemidirectProduct.inl (Matrix.SpecialLinearGroup.map (algebraMap ℂ K) w.left) *
    SemidirectProduct.inr w.right

theorem extendConstant_matrix (w : ReducedGraphAction.Stabilizer ℂ) :
    Matrix.GeneralLinearGroup.map (algebraMap ℂ K) (ReducedGraphAction.matrixRepresentation ℂ w) =
      ReducedGraphAction.matrixRepresentation K (extendConstant K w) := by
  calc
    Matrix.GeneralLinearGroup.map (algebraMap ℂ K) (ReducedGraphAction.matrixRepresentation ℂ w) =
      Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
        (ReducedGraphAction.matrixRepresentation ℂ
          (SemidirectProduct.inl w.left * SemidirectProduct.inr w.right)) := by
      rw [SemidirectProduct.inl_left_mul_inr_right]
    _ = Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
          (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inl w.left)) *
        Matrix.GeneralLinearGroup.map (algebraMap ℂ K)
          (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inr w.right)) := by
      rw [map_mul,map_mul]
    _ = ReducedGraphAction.matrixRepresentation K
          (SemidirectProduct.inl (Matrix.SpecialLinearGroup.map (algebraMap ℂ K) w.left)) *
        ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inr w.right) := by
      rw [connected_matrix_map,inr_matrix_map]
    _ = ReducedGraphAction.matrixRepresentation K (extendConstant K w) := by
      rw [extendConstant,map_mul]

/-- The actual native quotient-point relation determines the literal graph
subspaces in the exact inverse matrix convention. -/
theorem graph_ranges_of_fieldAction (M : Matrix.GeneralLinearGroup (Fin 12) K)
    (f g : PrimitiveRhoFiberNondegenerate.nondegenerateRing →ₐ[ℂ] K)
    (h : fieldAction K M (PrimitiveRhoGraphNativePoints.point K f) =
      PrimitiveRhoGraphNativePoints.point K g) :
    (Matrix.toLin' (PrimitiveRhoFiberNondegenerate.localizedGraph.map g)).range =
      ((Matrix.toLin' (PrimitiveRhoFiberNondegenerate.localizedGraph.map f)).range).map
        (Matrix.toLin' (M⁻¹).val) := by
  have hb : fieldAction K M (PrimitiveRhoGraphNativePoints.point K f) ≫
      GrassmannianCharts.projection ℂ 4 12 =
    PrimitiveRhoGraphNativePoints.point K g ≫ GrassmannianCharts.projection ℂ 4 12 := by
    rw [fieldAction_projection,PrimitiveRhoGraphNativePoints.point_projection,
      PrimitiveRhoGraphNativePoints.point_projection]
  have hq := (GrassmannianFieldKernels.points_eq_iff_kernel_eq (K := K) (k := 4) (n := 12)
    (fieldAction K M (PrimitiveRhoGraphNativePoints.point K f)) (PrimitiveRhoGraphNativePoints.point K g)
    (PrimitiveRhoGraphNativePoints.quotient K f * M.val) (PrimitiveRhoGraphNativePoints.quotient K g)
    (acted_surjective K M _ (PrimitiveRhoGraphNativePoints.quotient_surjective K f))
    (PrimitiveRhoGraphNativePoints.quotient_surjective K g)
    (fieldAction_fieldPresentation K M _ _ (PrimitiveRhoGraphNativePoints.quotient_surjective K f)
      (PrimitiveRhoGraphNativePoints.point_class K f))
    (PrimitiveRhoGraphNativePoints.point_class K g) hb).mp h
  change (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K f * M.val)).ker =
    (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K g)).ker at hq
  calc
    (Matrix.toLin' (PrimitiveRhoFiberNondegenerate.localizedGraph.map g)).range =
        (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K g)).ker :=
      (PrimitiveRhoGraphNativePoints.quotient_kernel K g).symm
    _ = (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K f * M.val)).ker := hq.symm
    _ = (Matrix.toLin' (PrimitiveRhoGraphNativePoints.quotient K f)).ker.map (Matrix.toLin' (M⁻¹).val) := by
      simpa only [inv_inv] using kernel_mul_inverse K M⁻¹ (PrimitiveRhoGraphNativePoints.quotient K f)
    _ = _ := congrArg (fun V : Submodule K (Fin 12 → K) => V.map (Matrix.toLin' (M⁻¹).val))
      (PrimitiveRhoGraphNativePoints.quotient_kernel K f)

/-- The genuine connected parameter morphism equals the genuine field-point
matrix operation, by actual quotient classes and the actual base projection. -/
theorem parameterPoint_action_eq (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (s : SliceField →ₐ[ℂ] K) :
    (SL3UniversalFieldAction.parameterPoint g s).left ≫ SL3UniversalFieldAction.actionMap =
      fieldAction K (ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inl g))
        (NativeGenericPullbackEvaluation.point s.toRingHom) := by
  apply GraphGrassmannianLinearAction.hom_ext ℂ
  · have hb : ((SL3UniversalFieldAction.parameterPoint g s) ≫
        SL3UniversalFieldAction.actionOver).left ≫ GrassmannianCharts.projection ℂ 4 12 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) :=
      ((SL3UniversalFieldAction.parameterPoint g s) ≫ SL3UniversalFieldAction.actionOver).w
    refine hb.trans ?_
    rw [fieldAction_projection]
    exact (NativeGenericFieldPoints.point_projection ℂ
      (GrassmannianCharts.projection ℂ 4 12) rfl s).symm
  · rw [SL3UniversalFieldAction.parameterPoint_action_class,fieldAction_class]
    exact SL3FamilyFreeAction.transformPoints_spec K _ g _

def fullPoint (g : Matrix.SpecialLinearGroup (Fin 3) K) (c : M9.CentralSignQuotient.C2)
    (s : SliceField →ₐ[ℂ] K) : Spec (.of K) ⟶ space :=
  (SL3UniversalFieldAction.parameterPoint g s).left ≫ SL3UniversalFieldAction.actionMap ≫
    ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c)

/-- The full varying-plus-odd family has exactly the native positive quotient
matrix of the actual semidirect element. This holds before any invariance claim. -/
theorem fullPoint_eq (g : Matrix.SpecialLinearGroup (Fin 3) K) (c : M9.CentralSignQuotient.C2)
    (s : SliceField →ₐ[ℂ] K) :
    fullPoint K g c s =
      fieldAction K (ReducedGraphAction.matrixRepresentation K
        (SemidirectProduct.inl g * SemidirectProduct.inr c))
          (NativeGenericPullbackEvaluation.point s.toRingHom) := by
  let p := NativeGenericPullbackEvaluation.point s.toRingHom
  let M := ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inl g)
  have hp : fieldAction K M p ≫ GrassmannianCharts.projection ℂ 4 12 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ K)) := by
    rw [fieldAction_projection]
    exact NativeGenericFieldPoints.point_projection ℂ (GrassmannianCharts.projection ℂ 4 12) rfl s
  have ho : fieldAction K (ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inr c))
        (fieldAction K M p) =
      fieldAction K M p ≫ ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c) := by
    have he := fieldAction_constant K
      (ReducedGraphAction.matrixRepresentation ℂ (SemidirectProduct.inr c)) (fieldAction K M p) hp
    rw [inr_matrix_map] at he
    exact he
  calc
    fullPoint K g c s = fieldAction K M p ≫
        ReducedGraphAction.nativeAction ℂ (SemidirectProduct.inr c) := by
      rw [fullPoint,← Category.assoc,parameterPoint_action_eq]
    _ = fieldAction K (ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inr c))
        (fieldAction K M p) := ho.symm
    _ = fieldAction K (M * ReducedGraphAction.matrixRepresentation K (SemidirectProduct.inr c)) p :=
      fieldAction_mul K M _ p
    _ = _ := by rw [map_mul]

end M9Native.PrimitiveReducedFamilyComparison
