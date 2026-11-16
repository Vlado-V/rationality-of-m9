module

public import M9StacksIntegration.MukaiConormalOriginFrame
public import M9StacksIntegration.SplitMatrixGrassmannianNaturality
public import M9StacksIntegration.LagrangianSymplecticAction
public import M9StacksIntegration.LagrangianTranslatedCharts

/-! Genuine same-base symplectic transitivity from the actual standard
quotient. The original quotient presentation and its normalized frame
are retained, rather than replacing a point by an abstract normal form. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.LagrangianOriginOrbit

open AlgebraicGeometry.Grassmannian LagrangianGrassmannian LagrangianMatrixChart
open LagrangianPluckerQuotient LagrangianBigCellQuotient LagrangianPluckerTrivialization
open LagrangianSymplecticAction LagrangianTransitivity
open MukaiConormalBigCellSections MukaiConormalBigCellFirstJet MukaiConormalOriginFrame
open Stacks.FreeSheafMatrix SplitMatrixGrassmannianNaturality

/-- Transport an existing genuine free quotient frame through a genuine
isomorphism of the original presentations. -/
theorem frame_of_isomorphic {X : Scheme.{u}} (q q' : QuotientPresentation X 3 6)
    (e : q.target ≅ freeOn X 3) (M : Matrix (Fin 3) (Fin 6) Γ(X,⊤))
    (he : q.map ≫ e.hom = ofMatrix M) (h : q.Isomorphic q') :
    ∃ e' : q'.target ≅ freeOn X 3, q'.map ≫ e'.hom = ofMatrix M := by
  obtain ⟨a,ha⟩ := h
  refine ⟨a.symm ≪≫ e,?_⟩
  change q'.map ≫ (a.inv ≫ e.hom) = _
  calc
    _ = (q'.map ≫ a.inv) ≫ e.hom := (Category.assoc _ _ _).symm
    _ = ((q.map ≫ a.hom) ≫ a.inv) ≫ e.hom :=
      congrArg (fun t => (t ≫ a.inv) ≫ e.hom) ha.symm
    _ = _ := by rw [Category.assoc q.map a.hom a.inv,Iso.hom_inv_id,Category.comp_id,he]

/-- Canonical pullback of the same actual free frame pulls its literal
rectangular matrix by the original map of global functions. -/
theorem pullback_frame {X Y : Scheme.{u}} (f : Y ⟶ X) (q : QuotientPresentation X 3 6)
    (e : q.target ≅ freeOn X 3) (M : Matrix (Fin 3) (Fin 6) Γ(X,⊤))
    (he : q.map ≫ e.hom = ofMatrix M) :
    ∃ e' : (pullbackPresentation f q).target ≅ freeOn Y 3,
      (pullbackPresentation f q).map ≫ e'.hom = ofMatrix (M.map f.appTop.hom) := by
  refine ⟨(Scheme.Modules.pullback f).mapIso e ≪≫ pullbackFreeIso f 3,?_⟩
  change ((pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map q.map) ≫
    ((Scheme.Modules.pullback f).map e.hom ≫ (pullbackFreeIso f 3).hom) = _
  calc
    _ = pulledFreeMap f (q.map ≫ e.hom) := by
      simp only [pulledFreeMap,Functor.map_comp,Category.assoc]
    _ = pulledFreeMap f (ofMatrix M) := congrArg (pulledFreeMap f) he
    _ = _ := pulledFreeMap_ofMatrix f M

/-- Two actual quotient frames with the same literal quotient map give
an actual presentation isomorphism. -/
theorem isomorphic_of_common_frame {X : Scheme.{u}} (q q' : QuotientPresentation X 3 6)
    (e : q.target ≅ freeOn X 3) (e' : q'.target ≅ freeOn X 3)
    (h : q.map ≫ e.hom = q'.map ≫ e'.hom) : q.Isomorphic q' := by
  refine ⟨e ≪≫ e'.symm,?_⟩
  change q.map ≫ (e.hom ≫ e'.inv) = q'.map
  calc
    _ = (q.map ≫ e.hom) ≫ e'.inv := (Category.assoc _ _ _).symm
    _ = (q'.map ≫ e'.hom) ≫ e'.inv := congrArg (fun t => t ≫ e'.inv) h
    _ = _ := by rw [Category.assoc,Iso.hom_inv_id,Category.comp_id]

variable (K : Type u) [Field K]

theorem standard_zero_eq : LagrangianPluckerFirstJet.standard K 0 = standardQuotient K := by
  ext i j
  refine Fin.addCases (m:=3) (n:=3) (fun j => ?_) (fun j => ?_) j
  · rw [LagrangianPluckerFirstJet.standard_e,standardQuotient_first]
  · rw [LagrangianPluckerFirstJet.standard_f,standardQuotient_last]
    rfl

/-- The true polynomial big-cell frame evaluates to the true standard
quotient at the actual zero scheme point. -/
theorem bigCell_matrix_at_zero :
    ((graphQuotientMatrix K).map (MukaiConormalBigCellSections.scalarEquiv K).toRingHom).map
        (zeroPoint K).appTop.hom = standardQuotient Γ(Spec (.of K),⊤) := by
  calc
    _ = ((graphQuotientMatrix K).map (originEval K).toRingHom).map
        (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom := by
      ext i j
      exact zeroPoint_scalar K _
    _ = (standardQuotient K).map (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom := by
      rw [graphQuotient_origin,standard_zero_eq]
    _ = _ := standardQuotient_map K _

/-- The original native origin has a genuine standard quotient frame,
with the original quotient projection normalized, not just its rank. -/
theorem exists_origin_quotient_frame :
    ∃ e : (pullbackPresentation (origin K ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of K)) 3,
      (pullbackPresentation (origin K ≫ inclusion K) (universalQuotient K)).map ≫ e.hom =
        ofMatrix (standardQuotient Γ(Spec (.of K),⊤)) := by
  let qb := pullbackPresentation (bigCell K) (quotientOnLG K)
  let qo := pullbackPresentation (bigCell K ≫ inclusion K) (universalQuotient K)
  let M := (graphQuotientMatrix K).map (MukaiConormalBigCellSections.scalarEquiv K).toRingHom
  have hm : qb.map ≫ (bigCellQuotientIso K).hom = ofMatrix M := by
    apply toMatrix_injective
    rw [MukaiConormalBigCellSections.original_bigCell_matrix,toMatrix_ofMatrix]
  obtain ⟨e,he⟩ := frame_of_isomorphic qb qo (bigCellQuotientIso K) M hm
    (pullbackPresentation_comp_isomorphic (inclusion K) (bigCell K) (universalQuotient K))
  obtain ⟨ep,hep⟩ := pullback_frame (zeroPoint K) qo e M he
  have hep' : (pullbackPresentation (zeroPoint K) qo).map ≫ ep.hom =
      ofMatrix (standardQuotient Γ(Spec (.of K),⊤)) := by
    rw [hep]
    exact congrArg ofMatrix (bigCell_matrix_at_zero K)
  have hc : (⟦pullbackPresentation (zeroPoint K) qo⟧ : Points (Spec (.of K)) 3 6) =
      pointClass K (origin K) := (pointClass_comp K (zeroPoint K) (bigCell K)).symm
  exact frame_of_isomorphic _ _ ep _ hep' (presentation_isomorphic_of_class_eq hc)

/-- Every genuine rational LG point is an actual symplectic translate
of the actual origin over the original field. -/
theorem exists_origin_action (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K = 𝟙 _) :
    ∃ g : Matrix.symplecticGroup (Fin 3) K, p = origin K ≫ action K g := by
  obtain ⟨g,e,he⟩ := exists_point_action_normalForm K p hp
  obtain ⟨e0,he0⟩ := exists_origin_quotient_frame K
  have heq : p ≫ action K g = origin K := by
    apply hom_ext K
    · rw [Category.assoc,action_projection,hp,origin_over_base]
    · exact Quotient.sound (.rel _ _
        (isomorphic_of_common_frame _ _ e e0 (he.trans he0.symm)))
  refine ⟨g⁻¹,?_⟩
  calc
    p = (p ≫ action K g) ≫ action K g⁻¹ := by
      rw [Category.assoc,action_mul,mul_inv_cancel,action_one,Category.comp_id]
    _ = _ := congrArg (fun f => f ≫ action K g⁻¹) heq

/-- The original quotient over every test scheme retains the literal
matrix of quotient precomposition under the actual LG action. -/
theorem action_quotient_frame {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) K)
    (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅ freeOn T 3)
    (M : Matrix (Fin 3) (Fin 6) Γ(T,⊤))
    (he : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom =
      ofMatrix M) :
    ∃ e' : (pullbackPresentation ((p ≫ action K g) ≫ inclusion K)
        (universalQuotient K)).target ≅ freeOn T 3,
      (pullbackPresentation ((p ≫ action K g) ≫ inclusion K) (universalQuotient K)).map ≫
        e'.hom = ofMatrix (M * constantMatrix K (p ≫ projection K) g) := by
  obtain ⟨a,ha⟩ := pullback_action_isomorphic K p g
  refine ⟨a ≪≫ e,?_⟩
  change (pullbackPresentation ((p ≫ action K g) ≫ inclusion K) (universalQuotient K)).map ≫
    (a.hom ≫ e.hom) = _
  calc
    _ = ((pullbackPresentation ((p ≫ action K g) ≫ inclusion K) (universalQuotient K)).map ≫
        a.hom) ≫ e.hom := (Category.assoc _ _ _).symm
    _ = ((constantFreeIso K (p ≫ projection K) g).hom ≫
        (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map) ≫ e.hom :=
      congrArg (fun t => t ≫ e.hom) ha
    _ = (constantFreeIso K (p ≫ projection K) g).hom ≫
        ((pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom) :=
      Category.assoc _ _ _
    _ = (constantFreeIso K (p ≫ projection K) g).hom ≫ ofMatrix M :=
      congrArg (fun t => (constantFreeIso K (p ≫ projection K) g).hom ≫ t) he
    _ = _ := by
      apply toMatrix_injective
      rw [toMatrix_comp,constantFreeIso_matrix,toMatrix_ofMatrix,toMatrix_ofMatrix]

/-- The original translated-origin quotient has the literal standard
three rows times the original six-by-six symplectic matrix. -/
theorem exists_translated_origin_quotient_frame (g : Matrix.symplecticGroup (Fin 3) K) :
    ∃ e : (pullbackPresentation ((origin K ≫ action K g) ≫ inclusion K)
        (universalQuotient K)).target ≅ freeOn (Spec (.of K)) 3,
      (pullbackPresentation ((origin K ≫ action K g) ≫ inclusion K)
        (universalQuotient K)).map ≫ e.hom =
      ofMatrix ((standardQuotient K * matrixSix K g).map
        (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) := by
  obtain ⟨e,he⟩ := exists_origin_quotient_frame K
  obtain ⟨e',he'⟩ := action_quotient_frame K (origin K) g e _ he
  refine ⟨e',he'.trans ?_⟩
  apply congrArg ofMatrix
  rw [origin_over_base]
  have hs : scalarMap K (𝟙 (Spec (.of K))) =
      (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom := by
    ext c
    exact scalarMap_id K c
  change standardQuotient Γ(Spec (.of K),⊤) *
    (matrixSix K g).map (scalarMap K (𝟙 _)) = _
  rw [hs,Matrix.map_mul,standardQuotient_map]

/-- Actual rational-point transitivity together with the normalized
original quotient projection. No point or frame is supplied as a premise. -/
theorem exists_origin_action_with_frame (p : Spec (.of K) ⟶ space K)
    (hp : p ≫ projection K = 𝟙 _) :
    ∃ (g : Matrix.symplecticGroup (Fin 3) K)
      (e : (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).target ≅
        freeOn (Spec (.of K)) 3),
      p = origin K ≫ action K g ∧
      (pullbackPresentation (p ≫ inclusion K) (universalQuotient K)).map ≫ e.hom =
        ofMatrix ((standardQuotient K * matrixSix K g).map
          (MukaiConormalFieldCoordinates.scalarEquiv K).toRingHom) := by
  obtain ⟨g,hg⟩ := exists_origin_action K p hp
  subst p
  obtain ⟨e,he⟩ := exists_translated_origin_quotient_frame K g
  exact ⟨g,e,rfl,he⟩

end M9Native.LagrangianOriginOrbit
