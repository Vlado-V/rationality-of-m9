module

public import M9StacksIntegration.MukaiPrimitiveCanonicalEvaluation
public import M9StacksIntegration.LagrangianOriginOrbit
public import M9StacksIntegration.MukaiCurvePointCoordinates
public import M9StacksIntegration.MukaiConormalOriginImage
public import M9StacksIntegration.MukaiConormalNativeCovariance
public import M9StacksIntegration.MukaiQuarticGradientTransport
public import M9StacksIntegration.MukaiTupleEvaluationCoordinates
public import M9StacksIntegration.MukaiEvaluationCurveJets

/-! Genuine same-base normalization of the original complete evaluation
at an actual field point. The target frame is transported through the
original evaluation diagram, not chosen from equality of ranks. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

universe u

namespace M9Native.MukaiEvaluationPointFrame

open MukaiPrimitiveCanonicalEvaluation LagrangianOriginOrbit LagrangianMatrixChart
open AlgebraicGeometry.Grassmannian LagrangianTransitivity LagrangianGrassmannian
open SplitMatrixGrassmannianNaturality
open LagrangianPluckerTrivialization

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

omit [CharZero K] in
/-- Original complete evaluation and original native LG point have the
same actual symplectic normal form, in a constructed quotient frame. -/
theorem exists_origin_action_with_evaluation_frame
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K)
      (e : (Scheme.Modules.pullback p).obj E ≅ freeOn (Spec (.of K)) 3),
      p ≫ d.map = MukaiConormalOriginFrame.origin K ≫ LagrangianSymplecticAction.action K g ∧
      (pullbackFreeIso p 6).inv ≫
        (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) ≫ e.hom =
        Stacks.FreeSheafMatrix.ofMatrix ((standardQuotient K * matrixSix K g).map
          (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) := by
  have hbase : (p ≫ d.map) ≫ projection K = 𝟙 _ := by
    rw [Category.assoc, d.over_base, hp]
  obtain ⟨g,eQ,hpoint,hframe⟩ := exists_origin_action_with_frame K (p ≫ d.map) hbase
  let q := pullbackPresentation (d.map ≫ inclusion K) (universalQuotient K)
  let q₁ := pullbackPresentation p q
  let q₂ := pullbackPresentation ((p ≫ d.map) ≫ inclusion K) (universalQuotient K)
  have hi : q₁.Isomorphic q₂ := by
    change (pullbackPresentation p (pullbackPresentation (d.map ≫ inclusion K)
      (universalQuotient K))).Isomorphic
        (pullbackPresentation ((p ≫ d.map) ≫ inclusion K) (universalQuotient K))
    rw [Category.assoc]
    exact pullbackPresentation_comp_isomorphic (d.map ≫ inclusion K) p (universalQuotient K)
  obtain ⟨a,ha⟩ := hi
  let eD : q₁.target ≅ (Scheme.Modules.pullback p).obj E :=
    (Scheme.Modules.pullback p).mapIso d.quotientIso
  have heval : (pullbackFreeIso p 6).inv ≫
      (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) =
      q₁.map ≫ eD.hom := by
    change (pullbackFreeIso p 6).inv ≫
      (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) =
      ((pullbackFreeIso p 6).inv ≫ (Scheme.Modules.pullback p).map q.map) ≫
        (Scheme.Modules.pullback p).map d.quotientIso.hom
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, d.triangle]
  refine ⟨g,eD.symm ≪≫ a ≪≫ eQ,hpoint,?_⟩
  rw [← Category.assoc, heval]
  change (q₁.map ≫ eD.hom) ≫ (eD.inv ≫ (a.hom ≫ eQ.hom)) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, ha]
  exact hframe

omit [CharZero K] in
/-- Every original triple in the original complete basis retains its
literal three columns under the same actual field-point target frame. -/
theorem triple_point_frame (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (e : (Scheme.Modules.pullback p).obj E ≅ freeOn (Spec (.of K)) 3)
    (M : Matrix (Fin 3) (Fin 6) K)
    (hM : (pullbackFreeIso p 6).inv ≫
      (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) ≫ e.hom =
      Stacks.FreeSheafMatrix.ofMatrix
        (M.map (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom))
    (s : Fin 3 → (Fin 6 → K)) :
    (pullbackFreeIso p 3).inv ≫
      (Scheme.Modules.pullback p).map
        (MukaiSemiIrreducible.evaluation K f E (fun i => b.equivFun.symm (s i))) ≫ e.hom =
      Stacks.FreeSheafMatrix.ofMatrix
        ((M * LagrangianUniversalTriples.columnMatrix K s).map
          (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) := by
  have hc : ((LagrangianUniversalTriples.columnMatrix K s).map
      (ExteriorEvaluation.baseRingMap K f)).map p.appTop.hom =
      (LagrangianUniversalTriples.columnMatrix K s).map
        (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom := by
    ext i j
    change p.appTop (ExteriorEvaluation.baseRingMap K f _) = _
    rw [MukaiEvaluationCurveJets.baseRingMap_eq_baseScalar]
    exact MukaiEvaluationCurveJets.fieldPoint_baseScalar K f p hp _
  calc
    _ = pulledFreeMap p (LagrangianUniversalTriples.sourceMap K f s) ≫
        ((pullbackFreeIso p 6).inv ≫
          (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) ≫ e.hom) := by
      rw [MukaiTupleEvaluationCoordinates.evaluation_eq_sourceMap]
      simp only [pulledFreeMap, CategoryTheory.Functor.map_comp, Category.assoc,
        Iso.hom_inv_id_assoc]
    _ = Stacks.FreeSheafMatrix.ofMatrix
          ((LagrangianUniversalTriples.columnMatrix K s).map
            (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) ≫
        Stacks.FreeSheafMatrix.ofMatrix
          (M.map (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) := by
      rw [hM]
      change pulledFreeMap p (Stacks.FreeSheafMatrix.ofMatrix
        ((LagrangianUniversalTriples.columnMatrix K s).map (ExteriorEvaluation.baseRingMap K f))) ≫ _ = _
      rw [pulledFreeMap_ofMatrix, hc]
    _ = _ := by
      apply Stacks.FreeSheafMatrix.toMatrix_injective
      rw [Stacks.FreeSheafMatrix.toMatrix_comp, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
        Stacks.FreeSheafMatrix.toMatrix_ofMatrix, Stacks.FreeSheafMatrix.toMatrix_ofMatrix,
        Matrix.map_mul]

theorem range_conormalForm :
    LinearMap.range (MukaiConormalPrimitive.conormalForm K) =
      MukaiConormalOrigin.originConormal K := by
  ext ell
  constructor
  · rintro ⟨v,rfl⟩
    exact MukaiConormalOrigin.conormalForm_mem_originConormal K v
  · intro h
    let a : MukaiConormalOrigin.originConormal K := ⟨ell,h⟩
    refine ⟨(MukaiConormalOrigin.originConormalIso K).symm a,?_⟩
    have he := congrArg Subtype.val ((MukaiConormalOrigin.originConormalIso K).apply_symm_apply a)
    simpa only [MukaiConormalOrigin.originConormalIso_apply] using he

variable [IsAlgClosed K]

/-- The original field-point conormal image has precisely the
inverse-dual normal form corresponding to the actual point action. -/
theorem range_pointFormsMap_of_origin_action (p : Spec (.of K) ⟶ X)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (hg : p ≫ d.map = MukaiConormalOriginFrame.origin K ≫ LagrangianSymplecticAction.action K g) :
    LinearMap.range (MukaiCurvePointCoordinates.pointFormsMap K f E b d p) =
      LinearMap.range ((MukaiQuarticGradientTransport.formsAction K g⁻¹).toLinearMap.comp
        (MukaiConormalPrimitive.conormalForm K)) := by
  calc
    _ = LinearMap.range (MukaiConormalFieldCoordinates.formsMap K (p ≫ d.map)) := by
      rw [MukaiCurvePointCoordinates.pointFormsMap_eq]
      exact LinearMap.range_comp_of_range_eq_top _
        (MukaiCurvePointCoordinates.sourcePointEquiv K f E b d p).range
    _ = (MukaiConormalOrigin.originConormal K).map
        (MukaiPrimitiveQuartic.quotientMap K (matrixSix K g⁻¹).mulVecLin) := by
      rw [hg,MukaiConormalNativeCovariance.range_formsMap_action K _
        (MukaiConormalOriginFrame.origin_over_base K) g,
        MukaiConormalOriginImage.range_formsMap_origin]
    _ = _ := by
      rw [← range_conormalForm K, LinearMap.range_comp,
        MukaiPrimitiveQuarticAction.quotientMap_eq_dualMap_transpose]

/-- The two original maps are normalized together; no conormal-image
or point-normalization condition is assumed. -/
theorem exists_simultaneous_normal_form (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K)
      (e : (Scheme.Modules.pullback p).obj E ≅ freeOn (Spec (.of K)) 3),
      p ≫ d.map = MukaiConormalOriginFrame.origin K ≫ LagrangianSymplecticAction.action K g ∧
      (pullbackFreeIso p 6).inv ≫
        (Scheme.Modules.pullback p).map (MukaiSemiIrreducible.evaluation K f E b) ≫ e.hom =
        Stacks.FreeSheafMatrix.ofMatrix ((standardQuotient K * matrixSix K g).map
          (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) ∧
      LinearMap.range (MukaiCurvePointCoordinates.pointFormsMap K f E b d p) =
        LinearMap.range ((MukaiQuarticGradientTransport.formsAction K g⁻¹).toLinearMap.comp
          (MukaiConormalPrimitive.conormalForm K)) := by
  obtain ⟨g,e,hg,he⟩ := exists_origin_action_with_evaluation_frame K f E b d p hp
  exact ⟨g,e,hg,he,range_pointFormsMap_of_origin_action K f E b d p g hg⟩

end M9Native.MukaiEvaluationPointFrame
