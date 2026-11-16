module

public import M9StacksIntegration.LagrangianPointVolumeRanks
public import M9StacksIntegration.LagrangianOriginalSectionPoint
public import M9StacksIntegration.LagrangianPrimitiveRestriction
public import M9StacksIntegration.SectionZeroSubbundle

/-! The actual original primitive rows evaluate the actual original
canonical sections at the same original field-valued curve points.
All line frames and coefficient comparisons are constructed from the
native LG chart and pullback functors; none is supplied as compatibility
data. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.LagrangianCanonicalPointRows
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianPrimitiveRestriction
open LagrangianPointKernelCoordinates LagrangianPointVolumeRanks

variable (K : Type u) [Field K] [CharZero K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (l : X ⟶ space K)

def pointLineFrame (p : Spec (.of K) ⟶ X) :
    (Scheme.Modules.pullback p).obj (restrictedLine K l) ≅
      ProjectiveSectionFunctions.UnitLine (Spec (.of K)) :=
  (Scheme.Modules.pullbackComp p l).app (determinantLine K) ≪≫
    LagrangianPluckerGeneration.chartLineIso K (p ≫ l)
      (pointChart K (p ≫ l)).index (pointChart K (p ≫ l)).map (pointChart K (p ≫ l)).triangle

theorem pointLineFrame_primitive (p : Spec (.of K) ⟶ X) (j : Fin 14) :
    (pointLineFrame K l p).hom.app ⊤
      (pullbackGlobalSections p (restrictedLine K l) (restrictedSection K l j)) =
      LagrangianPlucker.chartCoordinates K (p ≫ l)
        (pointChart K (p ≫ l)).index (pointChart K (p ≫ l)).map j := by
  have h := congrArg
    ((LagrangianPluckerGeneration.chartLineIso K (p ≫ l)
      (pointChart K (p ≫ l)).index (pointChart K (p ≫ l)).map
        (pointChart K (p ≫ l)).triangle).hom.app ⊤)
    (SectionsEqualizer.pullbackGlobalSections_comp p l (determinantLine K) (primitiveSections K j))
  exact h.trans (LagrangianPluckerGeneration.chartLineIso_primitive K (p ≫ l)
    (pointChart K (p ≫ l)).index (pointChart K (p ≫ l)).map
      (pointChart K (p ≫ l)).triangle j)

def primitivePointScalar (p : Spec (.of K) ⟶ X) (a : Fin 14 → K) : K :=
  (Scheme.ΓSpecIso (.of K)).hom
    ((pointLineFrame K l p).hom.app ⊤
      (pullbackGlobalSections p (restrictedLine K l)
        ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
          (primitiveRestriction K f l a))))

theorem primitivePointScalar_eq (hl : l ≫ projection K = f)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (a : Fin 14 → K) :
    primitivePointScalar K f l p a = ∑ j : Fin 14, a j * fourteen K (p ≫ l) j := by
  let ρ := (Scheme.ΓSpecIso (.of K)).hom.hom
  have hκ : ExteriorEvaluation.baseRingMap K (𝟙 (Spec (.of K))) =
      (Scheme.ΓSpecIso (.of K)).inv.hom := by
    unfold ExteriorEvaluation.baseRingMap
    rw [appLE_top_top_eq_appTop, Scheme.Hom.id_appTop, Category.comp_id]
  have hc (b : K) : ρ (p.appTop (ExteriorEvaluation.baseRingMap K f b)) = b := by
    have h := RingHom.congr_fun (LagrangianTripleNaturality.baseRingMap_comp K f p) b
    change ExteriorEvaluation.baseRingMap K (p ≫ f) b = p.appTop (ExteriorEvaluation.baseRingMap K f b) at h
    rw [hp,hκ] at h
    rw [← h]
    exact (Scheme.ΓSpecIso (.of K)).inv_hom_id_apply b
  have hpL : (p ≫ l) ≫ projection K = 𝟙 _ := by rw [Category.assoc,hl,hp]
  have hr (j : Fin 14) :
      ρ (LagrangianPlucker.chartCoordinates K (p ≫ l)
        (pointChart K (p ≫ l)).index (pointChart K (p ≫ l)).map j) = fourteen K (p ≫ l) j := by
    have h := congrFun (chartCoordinates_eq_rowFourteen K (p ≫ l) hpL) j
    change ρ (LagrangianPlucker.chartCoordinates K (p ≫ l) _ _ j) = _ at h
    exact h
  unfold primitivePointScalar
  rw [primitiveRestriction_sections]
  simp only [map_sum, SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, pointLineFrame_primitive, smul_eq_mul]
  change ∑ j : Fin 14, ρ (p.appTop (ExteriorEvaluation.baseRingMap K f (a j)) *
    LagrangianPlucker.chartCoordinates K (p ≫ l) (pointChart K (p ≫ l)).index
      (pointChart K (p ≫ l)).map j) = _
  simp only [map_mul,hc,hr]

theorem primitive_point_zero_iff_row (hl : l ≫ projection K = f)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) (a : Fin 14 → K) :
    pullbackGlobalSections p (restrictedLine K l)
      ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
        (primitiveRestriction K f l a)) = 0 ↔
      ∑ j : Fin 14, fourteen K (p ≫ l) j * a j = 0 := by
  have hs : primitivePointScalar K f l p a = 0 ↔
      pullbackGlobalSections p (restrictedLine K l)
        ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
          (primitiveRestriction K f l a)) = 0 := by
    let z := pullbackGlobalSections p (restrictedLine K l)
      ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
        (primitiveRestriction K f l a))
    change (Scheme.ΓSpecIso (.of K)).hom.hom
      ((pointLineFrame K l p).hom.app ⊤ z) = 0 ↔ z = 0
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of K)).hom).injective).trans
        (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
          ((pointLineFrame K l p).hom.app ⊤)).injective)
  rw [← hs, primitivePointScalar_eq K f l hl p hp a]
  simp only [mul_comm]

variable [IsProper f]

theorem canonical_point_zero_iff_row
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hl : l ≫ projection K = f) (p : Spec (.of K) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (a : Fin 14 → K) :
    pullbackGlobalSections p (Stacks.Duality.dualizingSheafOverField f)
      ((cohomologyOverFieldZeroLinearIso K f
        (Stacks.Duality.dualizingSheafOverField f)).hom
          (LagrangianPrimitiveRestriction.canonicalRestriction K f l c a)) = 0 ↔
      ∑ j : Fin 14, fourteen K (p ≫ l) j * a j = 0 := by
  have hm : (cohomologyOverFieldIso K f c 0).hom = cohomologyOverFieldMap K f c.hom 0 := by
    with_unfolding_all rfl
  have he : (cohomologyOverFieldZeroLinearIso K f
      (Stacks.Duality.dualizingSheafOverField f)).hom
        (LagrangianPrimitiveRestriction.canonicalRestriction K f l c a) =
      c.hom.app ⊤ ((cohomologyOverFieldZeroLinearIso K f (restrictedLine K l)).hom
        (primitiveRestriction K f l a)) := by
    change (cohomologyOverFieldZeroLinearIso K f _).hom
      ((cohomologyOverFieldIso K f c 0).hom (primitiveRestriction K f l a)) = _
    rw [hm,cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap]
  rw [he, SectionZeroSubbundle.pullback_image_eq_zero_iff c.hom (by
    intro T g
    infer_instance)]
  exact primitive_point_zero_iff_row K f l hl p hp a

def rows {n : ℕ} (p : Fin n → (Spec (.of K) ⟶ X)) : Matrix (Fin n) (Fin 14) K :=
  fun i => fourteen K (p i ≫ l)

theorem rows_zero_iff_canonical_points {n : ℕ}
    (c : restrictedLine K l ≅ Stacks.Duality.dualizingSheafOverField f)
    (hl : l ≫ projection K = f) (p : Fin n → (Spec (.of K) ⟶ X))
    (hp : ∀ i, p i ≫ f = 𝟙 _) (a : Fin 14 → K) :
    (rows K l p).mulVec a = 0 ↔ ∀ i,
      pullbackGlobalSections (p i) (Stacks.Duality.dualizingSheafOverField f)
        ((cohomologyOverFieldZeroLinearIso K f
          (Stacks.Duality.dualizingSheafOverField f)).hom
            (LagrangianPrimitiveRestriction.canonicalRestriction K f l c a)) = 0 := by
  rw [funext_iff]
  simp only [rows,Matrix.mulVec,dotProduct,Pi.zero_apply]
  exact forall_congr' fun i => (canonical_point_zero_iff_row K f l c hl (p i) (hp i) a).symm

end M9Native.LagrangianCanonicalPointRows
