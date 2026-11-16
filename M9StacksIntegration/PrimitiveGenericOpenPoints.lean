module

public import M9StacksIntegration.PrimitiveGeometricExtensionInvariance
public import M9StacksIntegration.NativeGenericPointNaturality
public import M9StacksIntegration.OpenRestrictionPointFiber

@[expose] public section

/-! Actual generic field points in every nonempty open of the original
native primitive Grassmannian. The generic-stalk comparison is induced by
the original open immersion, and all point squares are proved. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.PrimitiveGenericOpenPoints

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction PrimitiveUniversalExtensionPoints
open NativeGenericPullbackEvaluation

variable (U : space.Opens) [Nonempty U]

abbrev openOver : Over PrimitiveFamilyFreeAction.base := Over.mk (U.ι ≫ projection)

def inclusionOver : openOver U ⟶ overSpace := Over.homMk U.ι rfl

instance inclusion_isDominant : IsDominant U.ι :=
  ⟨U.ι.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- Literal actual generic-stalk restriction through the chosen native open. -/
def fieldIso : E ≃+* U.toScheme.functionField :=
  (GrassmannianCharts.openImmersionFunctionFieldIso U.ι).commRingCatIsoToRingEquiv

theorem fieldIso_eq_map : (fieldIso U).toRingHom = NativeDominantFunctionField.map U.ι := by
  change (GrassmannianCharts.openImmersionFunctionFieldIso U.ι).hom.hom = _
  simp only [GrassmannianCharts.openImmersionFunctionFieldIso,
    NativeDominantFunctionField.map, Iso.trans_hom, asIso_hom]

theorem fieldIso_scalar : (fieldIso U).toRingHom.comp (algebraMap ℂ E) =
    GrassmannianCharts.structureScalarMap ℂ (U.ι ≫ projection) :=
  GrassmannianCharts.openImmersionFunctionFieldIso_scalar ℂ U.ι projection

theorem genericPoint_mem : genericPoint space ∈ U :=
  ((genericPoint_spec space).mem_open_set_iff U.isOpen).mpr (by
    obtain ⟨u⟩ := (inferInstance : Nonempty U)
    exact ⟨u.val, Set.mem_univ _, u.property⟩)

def pointOpenRing {L : Type} [Field L] (s : E →+* L) : Spec (.of L) ⟶ U.toScheme :=
  OpenRestrictionPointFiber.lift U (point s) (fun z => by
    rw [point_apply]
    exact genericPoint_mem U)

@[reassoc] theorem pointOpenRing_comp {L : Type} [Field L] (s : E →+* L) :
    pointOpenRing U s ≫ U.ι = point s :=
  OpenRestrictionPointFiber.lift_comp _ _ _

/-- The lifted point is exactly the generic point induced by the original
open-immersion generic-stalk isomorphism. -/
theorem pointOpenRing_generic {L : Type} [Field L] (s : E →+* L) :
    pointOpenRing U s = point (s.comp (fieldIso U).symm.toRingHom) := by
  apply (cancel_mono U.ι).mp
  rw [pointOpenRing_comp, NativeGenericPointNaturality.point_comp_dominant]
  have hc : (s.comp (fieldIso U).symm.toRingHom).comp
      (NativeDominantFunctionField.map U.ι) = s := by
    rw [← fieldIso_eq_map]
    ext x
    change s ((fieldIso U).symm (fieldIso U x)) = s x
    rw [RingEquiv.symm_apply_apply]
  rw [hc]

def pointOpen {L : Type} [Field L] [Algebra ℂ L] (s : E →ₐ[ℂ] L) :
    overField L ⟶ openOver U :=
  Over.homMk (pointOpenRing U s.toRingHom) (by
    change pointOpenRing U s.toRingHom ≫ (U.ι ≫ projection) =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L))
    rw [← Category.assoc, pointOpenRing_comp]
    exact NativeGenericFieldPoints.point_projection ℂ projection rfl s)

theorem pointOpen_left {L : Type} [Field L] [Algebra ℂ L] (s : E →ₐ[ℂ] L) :
    (pointOpen U s).left = pointOpenRing U s.toRingHom := rfl

/-- The lift uses exactly the original coefficient-preserving generic point. -/
theorem pointOpen_inclusion {L : Type} [Field L] [Algebra ℂ L] (s : E →ₐ[ℂ] L) :
    pointOpen U s ≫ inclusionOver U =
      NativeGenericFieldPoints.overPoint ℂ projection rfl s := by
  apply Over.OverMorphism.ext
  exact pointOpenRing_comp U s.toRingHom

/-- A dominant actual map of the chosen open acts by its actual native
stalk pullback, after the original open-immersion field comparison. -/
theorem pointOpenRing_map {Y : Scheme} [IsIntegral Y] (q : U.toScheme ⟶ Y) [IsDominant q]
    {L : Type} [Field L] (s : E →+* L) :
    pointOpenRing U s ≫ q =
      point (s.comp ((fieldIso U).symm.toRingHom.comp (NativeDominantFunctionField.map q))) := by
  rw [pointOpenRing_generic, NativeGenericPointNaturality.point_comp_dominant]
  rfl

/-- Equality of actual generic scheme points detects equality of their
original field embeddings. -/
theorem genericPointHom_injective {Y : Scheme} [IsIntegral Y] {L : Type} [Field L] :
    Function.Injective (point (X := Y) (L := L)) := by
  intro s t h
  have he : CommRingCat.ofHom s = CommRingCat.ofHom t :=
    Spec.map_injective ((cancel_mono (NativeFunctionFieldFunctor.genericSpec Y)).mp h)
  exact congrArg CommRingCat.Hom.hom he

end M9Native.PrimitiveGenericOpenPoints
