module

public import M9StacksIntegration.ConicFramePairRawPullback
public import M9StacksIntegration.GrassmannianPairLinearAction
public import M9.PrimitiveRepresentation
public import M9StacksIntegration.ProjectivePairSLFixedField

/-! Genuine diagonal SL3 action on the native product Grassmannian and
its literal original-frame conic pullback. The first ambient action is
Sym²(g), and the second is Sym²(g⁻ᵀ), as in the primitive representation. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix

namespace M9Native.ConicFramePairSLAction

open ConicFramePairRawPullback
open ConicFrameLeftEquivariance
open M9.FrameFieldElimination

abbrev SL3 := Matrix.SpecialLinearGroup (Fin 3) ℂ
abbrev PF := ConicFramePairRawPullback.PF
abbrev GrassPair := ConicFramePairRawPullback.GrassPair

/-- The actual inverse-transpose from the primitive representation. -/
def dualHom : SL3 →* SL3 where
  toFun := M9.PrimitiveRepresentation.inverseTranspose ℂ
  map_one' := by
    apply Subtype.ext
    simp [M9.PrimitiveRepresentation.inverseTranspose]
  map_mul' g h := by
    apply Subtype.ext
    change ((g * h)⁻¹).val.transpose = (g⁻¹).val.transpose * (h⁻¹).val.transpose
    rw [_root_.mul_inv_rev]
    exact Matrix.transpose_mul _ _

theorem dualHom_involutive (g : SL3) : dualHom (dualHom g) = g := by
  apply Subtype.ext
  change ((M9.PrimitiveRepresentation.inverseTranspose ℂ g)⁻¹).val.transpose = g.val
  rw [M9.PrimitiveRepresentation.inverseTranspose_inv]
  exact Matrix.transpose_transpose _

def ambientHom : SL3 →*
    (Matrix.GeneralLinearGroup (Fin 6) ℂ × Matrix.GeneralLinearGroup (Fin 6) ℂ) :=
  symmetricSquare.prod (symmetricSquare.comp dualHom)

/-- Actual right action on the two native quotient functors. -/
def nativeAction (g : SL3) : GrassPair ⟶ GrassPair :=
  GrassmannianPairLinearAction.action ℂ (symmetricSquare g) (symmetricSquare (dualHom g))

def nativeFieldRepresentation : SL3 →* (GrassPair.functionField ≃ₐ[ℂ] GrassPair.functionField) :=
  (GrassmannianPairLinearAction.fieldRepresentation ℂ).comp ambientHom

instance nativeAction_isIso (g : SL3) : IsIso (nativeAction g) := by
  unfold nativeAction
  infer_instance

instance nativeAction_isDominant (g : SL3) : IsDominant (nativeAction g) := by
  unfold nativeAction
  infer_instance

theorem nativeFieldRepresentation_eq_map (g : SL3) :
    (nativeFieldRepresentation g).toRingHom = NativeDominantFunctionField.map (nativeAction g) :=
  GrassmannianPairLinearAction.fieldAutomorphism_eq_map ℂ _ _

/-- The original raw independent-frame field action, with canonical SL3.toGL. -/
def rawFieldAutomorphism (g : SL3) : PF ≃ₐ[ℂ] PF where
  __ := pairActionHom ℂ (Matrix.SpecialLinearGroup.toGL g)
  commutes' := pairAction_constant ℂ (Matrix.SpecialLinearGroup.toGL g)

def rawSchemeAction (g : SL3) : RawSpec ⟶ RawSpec :=
  Spec.map (CommRingCat.ofHom (rawFieldAutomorphism g).toRingHom)

instance rawSchemeAction_isIso (g : SL3) : IsIso (rawSchemeAction g) := by
  unfold rawSchemeAction
  have : IsIso (CommRingCat.ofHom (rawFieldAutomorphism g).toRingHom) :=
    (rawFieldAutomorphism g).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

instance rawSchemeAction_isDominant (g : SL3) : IsDominant (rawSchemeAction g) :=
  ⟨(rawSchemeAction g).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

theorem rawSchemeAction_projection (g : SL3) :
    rawSchemeAction g ≫ rawProjection = rawProjection := by
  rw [rawSchemeAction, rawProjection, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (rawFieldAutomorphism g).toAlgHom.comp_algebraMap

theorem globalize_pullback (σ : PF →+* PF) (F : ConicFrame.Mat3 PF) :
    (globalize F).map (Spec.map (CommRingCat.ofHom σ)).appTop.hom = globalize (F.map σ) := by
  ext i j
  change (Spec.map (CommRingCat.ofHom σ)).appTop ((Scheme.ΓSpecIso (.of PF)).inv (F i j)) =
    (Scheme.ΓSpecIso (.of PF)).inv (σ (F i j))
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem scalarMap_rawProjection : GrassmannianLinearAction.scalarMap ℂ rawProjection =
    (Scheme.ΓSpecIso (.of PF)).inv.hom.comp (algebraMap ℂ PF) := by
  ext c
  change ((Scheme.ΓSpecIso (.of ℂ)).inv ≫
    (Spec.map (CommRingCat.ofHom (algebraMap ℂ PF))).appTop) c = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  rfl

theorem inverseFrame_globalize (g : SL3) (F : ConicFrame.Mat3 PF) :
    inverseFrame ℂ rawProjection g (globalize F) =
      globalize ((g⁻¹).val.map (algebraMap ℂ PF) * F) := by
  simp only [inverseFrame, globalize, Matrix.map_mul]
  congr 1
  have hm : (constantSL ℂ rawProjection g)⁻¹ = constantSL ℂ rawProjection g⁻¹ :=
    (map_inv (Matrix.SpecialLinearGroup.map (GrassmannianLinearAction.scalarMap ℂ rawProjection)) g).symm
  rw [hm, constantSL_val, scalarMap_rawProjection]
  rfl

theorem rawAction_firstFrame (g : SL3) :
    (firstFrame ℂ).map (rawFieldAutomorphism g).toRingHom =
      (g⁻¹).val.map (algebraMap ℂ PF) * firstFrame ℂ :=
  pairAction_firstFrame ℂ (Matrix.SpecialLinearGroup.toGL g)

theorem rawAction_secondFrame (g : SL3) :
    (secondFrame ℂ).map (rawFieldAutomorphism g).toRingHom =
      ((dualHom g)⁻¹).val.map (algebraMap ℂ PF) * secondFrame ℂ := by
  rw [show (dualHom g)⁻¹ = g.transpose from M9.PrimitiveRepresentation.inverseTranspose_inv ℂ g]
  exact pairAction_secondFrame ℂ (Matrix.SpecialLinearGroup.toGL g)

theorem conicPoint_equivariance (g h : SL3) (F : ConicFrame.Mat3 PF) (hF : IsUnit F.det)
    (hmat : F.map (rawFieldAutomorphism g).toRingHom =
      (h⁻¹).val.map (algebraMap ℂ PF) * F) :
    rawSchemeAction g ≫ ConicFrame.map RawSpec ℂ rawProjection (globalize F)
        (globalize_det_unit F hF) =
      ConicFrame.map RawSpec ℂ rawProjection (globalize F) (globalize_det_unit F hF) ≫
        GrassmannianLinearAction.action ℂ (symmetricSquare h) := by
  have hu : IsUnit ((globalize F).map (rawSchemeAction g).appTop.hom).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (globalize_det_unit F hF).map _
  rw [map_natural ℂ _ _ _ _ hu, rawSchemeAction_projection]
  have hm : (globalize F).map (rawSchemeAction g).appTop.hom =
      inverseFrame ℂ rawProjection h (globalize F) := by
    change (globalize F).map (Spec.map (CommRingCat.ofHom (rawFieldAutomorphism g).toRingHom)).appTop.hom = _
    rw [globalize_pullback, hmat, inverseFrame_globalize]
  simpa only [hm] using map_inverseFrame ℂ rawProjection h (globalize F) (globalize_det_unit F hF)

theorem firstConicPoint_equivariance (g : SL3) :
    rawSchemeAction g ≫ firstConicPoint =
      firstConicPoint ≫ GrassmannianLinearAction.action ℂ (symmetricSquare g) :=
  conicPoint_equivariance g g (firstFrame ℂ) firstFrame_det_unit (rawAction_firstFrame g)

theorem secondConicPoint_equivariance (g : SL3) :
    rawSchemeAction g ≫ secondConicPoint =
      secondConicPoint ≫ GrassmannianLinearAction.action ℂ (symmetricSquare (dualHom g)) :=
  conicPoint_equivariance g (dualHom g) (secondFrame ℂ) secondFrame_det_unit (rawAction_secondFrame g)

/-- Literal conic pullback equivariance on the actual native product, with
Sym² on Q and the actual inverse-transpose Sym² action on its dual. -/
theorem rawPoint_equivariance (g : SL3) :
    rawSchemeAction g ≫ rawPoint = rawPoint ≫ nativeAction g := by
  apply pullback.hom_ext
  · rw [Category.assoc, rawPoint_fst, firstConicPoint_equivariance]
    change firstConicPoint ≫ GrassmannianLinearAction.action ℂ (symmetricSquare g) =
      rawPoint ≫ (GrassmannianPairLinearAction.action ℂ _ _ ≫ pullback.fst _ _)
    rw [GrassmannianPairLinearAction.action_fst, ← Category.assoc, rawPoint_fst]
  · rw [Category.assoc, rawPoint_snd, secondConicPoint_equivariance]
    change secondConicPoint ≫ GrassmannianLinearAction.action ℂ (symmetricSquare (dualHom g)) =
      rawPoint ≫ (GrassmannianPairLinearAction.action ℂ _ _ ≫ pullback.snd _ _)
    rw [GrassmannianPairLinearAction.action_snd, ← Category.assoc, rawPoint_snd]

theorem affineFieldEquiv_rawAction (g : SL3) (z : RawSpec.functionField) :
    affineFieldEquiv (NativeDominantFunctionField.map (rawSchemeAction g) z) =
      rawFieldAutomorphism g (affineFieldEquiv z) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (rawFieldAutomorphism g).toRingHom)) :=
    rawSchemeAction_isDominant g
  have hh : affineFieldEquiv.toRingHom.comp (NativeDominantFunctionField.map (rawSchemeAction g)) =
      (rawFieldAutomorphism g).toRingHom.comp affineFieldEquiv.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := PF)
    intro a
    change affineFieldEquiv (NativeDominantFunctionField.map
        (Spec.map (CommRingCat.ofHom (rawFieldAutomorphism g).toRingHom))
          (algebraMap PF RawSpec.functionField a)) = _
    rw [NativeFunctionFieldFunctor.affine_map_algebraMap, affineFieldEquiv_algebraMap]
    change rawFieldAutomorphism g a = rawFieldAutomorphism g (affineFieldEquiv
      (algebraMap PF RawSpec.functionField a))
    rw [affineFieldEquiv_algebraMap]
  exact DFunLike.congr_fun hh z

/-- The genuine native diagonal action intertwines the exact original
independent-frame field embedding; no invariant-field identification is assumed. -/
theorem rawEmbedding_equivariance (g : SL3) (z : GrassPair.functionField) :
    rawEmbedding (nativeFieldRepresentation g z) = rawFieldAutomorphism g (rawEmbedding z) := by
  have hh := GrassmannianLinearAction.dominantMap_congr (rawPoint_equivariance g)
  rw [NativeFunctionFieldFunctor.map_comp, NativeFunctionFieldFunctor.map_comp] at hh
  have hz := DFunLike.congr_fun hh z
  change NativeDominantFunctionField.map (rawSchemeAction g)
      (NativeDominantFunctionField.map rawPoint z) =
    NativeDominantFunctionField.map rawPoint (NativeDominantFunctionField.map (nativeAction g) z) at hz
  rw [rawEmbedding_eq_pullback, rawEmbedding_eq_pullback]
  change affineFieldEquiv (NativeDominantFunctionField.map rawPoint
    ((nativeFieldRepresentation g).toRingHom z)) = _
  rw [nativeFieldRepresentation_eq_map, ← hz, affineFieldEquiv_rawAction]

end M9Native.ConicFramePairSLAction
