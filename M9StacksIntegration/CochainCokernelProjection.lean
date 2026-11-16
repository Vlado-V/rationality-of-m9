module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.SingleHomology
public import StacksFrontier.Homology.DoubleHomology

/-!
# The actual degree-zero cokernel projection of a cochain complex

The homology comparison is the original canonical homology inclusion
into opcycles, followed by the original cokernel isomorphism. The
projection is the actual chain map to that cokernel in degree zero.
Its homology map is computed explicitly, with no normalization premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits

universe u v

namespace M9Native.CochainCokernelProjection

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : CochainComplex C ℤ) (hK : K.d 0 ((ComplexShape.up ℤ).next 0) = 0)

/-- The original homology/opcycle map gives the actual cokernel iso. -/
def homologyCokernelIso : K.homology 0 ≅ cokernel (K.sc 0).f :=
  K.isoHomologyι 0 _ rfl hK ≪≫ (K.sc 0).opcyclesIsoCokernel

/-- Every degree-zero section is an actual cycle when the outgoing
map is zero, so it has an actual homology class. -/
def toHomology : K.X 0 ⟶ K.homology 0 :=
  (K.iCyclesIso 0 _ rfl hK).inv ≫ K.homologyπ 0

instance toHomology_epi : Epi (toHomology K hK) := by
  dsimp only [toHomology]
  infer_instance

/-- The actual homology class followed by the actual cokernel iso is
the original cokernel projection. -/
theorem toHomology_comp_iso :
    toHomology K hK ≫ (homologyCokernelIso K hK).hom =
      cokernel.π (K.sc 0).f := by
  simp only [toHomology, homologyCokernelIso, Iso.trans_hom,
    HomologicalComplex.isoHomologyι_hom, ShortComplex.opcyclesIsoCokernel_hom]
  rw [Category.assoc, HomologicalComplex.homology_π_ι_assoc,
    ← Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id, Category.id_comp]
  exact (K.sc 0).p_descOpcycles _ _

variable {K} {L : CochainComplex C ℤ} (hL : L.d 0 ((ComplexShape.up ℤ).next 0) = 0) (a : K ⟶ L)

/-- Original homology classes commute with every original chain map. -/
theorem toHomology_naturality :
    toHomology K hK ≫ HomologicalComplex.homologyMap a 0 =
      a.f 0 ≫ toHomology L hL := by
  have h : (K.iCyclesIso 0 _ rfl hK).inv ≫ HomologicalComplex.cyclesMap a 0 =
      a.f 0 ≫ (L.iCyclesIso 0 _ rfl hL).inv := by
    apply (cancel_mono (L.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.iCyclesIso_inv_hom_id, Category.comp_id]
    rw [← Category.assoc, HomologicalComplex.iCyclesIso_inv_hom_id, Category.id_comp]
  dsimp only [toHomology]
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc, h, Category.assoc]

variable (K)

/-- The actual canonical chain map to the cokernel in degree zero. -/
def projection : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj
    (cokernel (K.sc 0).f) :=
  HomologicalComplex.mkHomToSingle (cokernel.π (K.sc 0).f) fun i hi => by
    rw [← (ComplexShape.up ℤ).prev_eq' hi]
    exact cokernel.condition (K.sc 0).f

/-- Its degree-zero component is the actual cokernel projection. -/
theorem projection_f_zero :
    (projection K).f 0 = cokernel.π (K.sc 0).f ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- On a single complex the actual class projection is inverse to the
original canonical computation of its homology. -/
theorem toHomology_single (M : C) :
    toHomology ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) (by simp) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).hom := by
  dsimp only [toHomology]
  rw [Category.assoc, HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom,
    HomologicalComplex.singleObjCyclesSelfIso_hom, ← Category.assoc,
    HomologicalComplex.iCyclesIso_inv_hom_id, Category.id_comp]

/-- The actual chain projection has exactly the original cokernel
normalization on homology. -/
theorem homology_projection :
    HomologicalComplex.homologyMap (projection K) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
          (cokernel (K.sc 0).f)).hom =
      (homologyCokernelIso K hK).hom := by
  apply (cancel_epi (toHomology K hK)).mp
  calc
    _ = ((projection K).f 0 ≫ toHomology
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (cokernel (K.sc 0).f)) (by simp)) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 _).hom := by
      rw [← Category.assoc, toHomology_naturality hK]
    _ = (projection K).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom := by
      rw [Category.assoc, toHomology_single]
    _ = cokernel.π (K.sc 0).f := by
      rw [projection_f_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := (toHomology_comp_iso K hK).symm

/-- The actual degree-zero class map kills the original boundaries. -/
theorem differential_toHomology :
    (K.sc 0).f ≫ toHomology K hK = 0 := by
  apply (cancel_mono (homologyCokernelIso K hK).hom).mp
  rw [Category.assoc, toHomology_comp_iso, cokernel.condition, zero_comp]

/-- The actual chain map to original degree-zero homology. -/
def toSingleHomology : K ⟶
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (K.homology 0) :=
  HomologicalComplex.mkHomToSingle (toHomology K hK) fun i hi => by
    rw [← (ComplexShape.up ℤ).prev_eq' hi]
    exact differential_toHomology K hK

/-- Its degree-zero part is the literal actual homology class. -/
theorem toSingleHomology_f_zero :
    (toSingleHomology K hK).f 0 = toHomology K hK ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv :=
  HomologicalComplex.mkHomToSingle_f _ _

/-- The original homology of the actual homology projection is the identity. -/
theorem homology_toSingleHomology :
    HomologicalComplex.homologyMap (toSingleHomology K hK) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
          (K.homology 0)).hom = 𝟙 _ := by
  apply (cancel_epi (toHomology K hK)).mp
  calc
    _ = ((toSingleHomology K hK).f 0 ≫ toHomology
        ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj (K.homology 0))
          (by simp)) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 _).hom := by
      rw [← Category.assoc, toHomology_naturality hK]
    _ = (toSingleHomology K hK).f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).hom := by
      rw [Category.assoc, toHomology_single]
    _ = toHomology K hK := by
      rw [toSingleHomology_f_zero, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = _ := (Category.comp_id _).symm

/-- The actual chain map to any genuinely identified degree-zero homology sheaf. -/
def toSingle (M : C) (e : K.homology 0 ≅ M) :
    K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M :=
  toSingleHomology K hK ≫
    (HomologicalComplex.single C (ComplexShape.up ℤ) 0).map e.hom

/-- Its degree-zero component retains the chosen original homology isomorphism. -/
theorem toSingle_f_zero (M : C) (e : K.homology 0 ≅ M) :
    (toSingle K hK M e).f 0 = toHomology K hK ≫ e.hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M).inv := by
  simp only [toSingle, HomologicalComplex.comp_f, toSingleHomology_f_zero,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]

/-- Actual chain homology gives exactly the original specified comparison. -/
theorem homology_toSingle (M : C) (e : K.homology 0 ≅ M) :
    HomologicalComplex.homologyMap (toSingle K hK M e) 0 ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 M).hom =
      e.hom := by
  rw [toSingle, HomologicalComplex.homologyMap_comp, Category.assoc,
    HomologicalComplex.singleObjHomologySelfIso_hom_naturality,
    ← Category.assoc, homology_toSingleHomology, Category.id_comp]

/-- The original two-term homology isomorphism has the literal cokernel
projection normalization on degree-zero classes. -/
theorem toHomology_doubleIso {M N : C} (f : M ⟶ N) :
    toHomology (HomologicalComplex.double f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide))
        (HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide)) ≫
      (HomologicalComplex.doubleHomologyIsoCokernel f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
        (HomologicalComplex.doubleXIso₁ f
          (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom ≫
          cokernel.π f := by
  let D := HomologicalComplex.double f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)
  let S := ShortComplex.mk f (0 : N ⟶ D.X ((ComplexShape.up ℤ).next 0)) (comp_zero)
  let e : D.sc 0 ≅ S := HomologicalComplex.doubleScIso₁ f
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
  have he : e.hom.τ₂ = (HomologicalComplex.doubleXIso₁ f
      (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom := by
    simp [e, HomologicalComplex.doubleScIso₁]
    exact Category.id_comp _
  have h : D.homologyπ 0 ≫
      (HomologicalComplex.doubleHomologyIsoCokernel f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      D.iCycles 0 ≫ e.hom.τ₂ ≫ cokernel.π f := by
    change (D.sc 0).homologyπ ≫ ShortComplex.homologyMap e.hom ≫
        S.homologyι ≫ S.descOpcycles (cokernel.π f) _ = _
    rw [ShortComplex.homologyπ_naturality_assoc, ShortComplex.homology_π_ι_assoc,
      ShortComplex.p_descOpcycles, ← Category.assoc, ShortComplex.cyclesMap_i,
      Category.assoc]
    rfl
  have h' : D.homologyπ 0 ≫
      (HomologicalComplex.doubleHomologyIsoCokernel f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom =
      D.iCycles 0 ≫ (HomologicalComplex.doubleXIso₁ f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)).hom ≫
          cokernel.π f :=
    h.trans (congrArg (fun t : D.X 0 ⟶ N => D.iCycles 0 ≫ t ≫ cokernel.π f) he)
  dsimp only [toHomology]
  change ((D.iCyclesIso 0 _ rfl
      (HomologicalComplex.double_d_eq_zero₀ _ _ _ _ (by decide))).inv ≫
        D.homologyπ 0) ≫ _ = _
  rw [Category.assoc, h', ← Category.assoc,
    HomologicalComplex.iCyclesIso_inv_hom_id, Category.id_comp]

end M9Native.CochainCokernelProjection
