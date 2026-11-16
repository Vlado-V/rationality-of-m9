module

public import M9StacksIntegration.LagrangianGoodOpenOrderedModel
public import M9StacksIntegration.LagrangianGoodFieldParameterAction
public import M9StacksIntegration.MukaiNonpentagonalParameterOrbitConverse
public import M9StacksIntegration.LagrangianFamilyOrbitIsomorphism

@[expose] public section

/-! A physical original-field isomorphism of two entire original good
fibres, and the actual source no-pencil condition, give an actual native
Sp6(L) orbit. Ordered models, their geometry and parameter identities are
constructed. Raw and original primitive coordinates remain explicit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianGoodFieldOrbit
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open LagrangianGoodFieldParameterAction LagrangianExtensionParameterCoordinates
open LagrangianTransverseRestriction

variable (L : Type) [Field L] [Algebra ℂ L] [IsAlgClosed L]
local instance extensionCharZero : CharZero L := PrimitiveExtensionFieldBridge.charZero_extension L

abbrev fibre (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : Scheme :=
  pullback (restrictedProjection ℂ) x
abbrev fibreProjection (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : fibre L x ⟶ Spec (.of L) :=
  pullback.snd (restrictedProjection ℂ) x

theorem fibre_integral (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : IsIntegral (fibre L x) :=
  LagrangianGeometricGenericSections.baseChange_integral ℂ L x
local instance fibreIntegral (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : IsIntegral (fibre L x) :=
  fibre_integral L x
local instance fibreSmooth (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : Smooth (fibreProjection L x) :=
  SmoothOfRelativeDimension.smooth 1 _

theorem fibre_isCurve (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : IsCurve L (fibreProjection L x) :=
  (isCurve_iff L (fibreProjection L x)).mpr
    ⟨⟨⟩, topologicalKrullDim_eq_of_smoothOfRelativeDimension (fibreProjection L x) 1⟩
local instance fibreCurve (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : IsCurve L (fibreProjection L x) :=
  fibre_isCurve L x

/-- The actual original whole fibre has Krull dimension one. -/
theorem fibre_dimension (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) :
    topologicalKrullDim (pullback (C := Scheme) (restrictedProjection ℂ) x) = 1 :=
  IsCurve.topologicalKrullDim_eq_one (k := L) (f := fibreProjection L x)

/-- The honest source no-five-pencil condition on the original whole
restricted-family fibre. No corresponding target condition is needed. -/
abbrev SourceNoFivePencil (x : Spec (.of L) ⟶ (goodOpen ℂ).toScheme) : Prop :=
  ¬ Nonempty (LinearSeries L (fibreProjection L x)
    (fibre_dimension L x).le 5 1)

/-- Equality of actual field-valued parameter maps transports the
native action together with its dependent coefficient-map proof. -/
theorem actPoint_congr (g : M9.PrimitiveStabilizer.Sp6 L)
    (p q : Spec (.of L) ⟶ parameter ℂ)
    (hp : p ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hq : q ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (h : p = q) :
    PrimitiveFieldMatrixAction.actPoint L g p hp = PrimitiveFieldMatrixAction.actPoint L g q hq := by
  subst q
  rfl

/-- Both the native original-coordinate action and its actual raw
conjugate realize the same orbit of the original parameter points. -/
theorem exists_native_and_raw_orbit_of_curveIso
    (x y : Spec (.of L) ⟶ (goodOpen ℂ).toScheme)
    (hx : (x ≫ (goodOpen ℂ).ι) ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hy : (y ≫ (goodOpen ℂ).ι) ≫ parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (e : fibre L x ≅ fibre L y)
    (he : e.hom ≫ fibreProjection L y = fibreProjection L x)
    (hnp : SourceNoFivePencil L x) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g (originalCoordinates L (x ≫ (goodOpen ℂ).ι))
        (originalCoordinates_projection L _ hx) = originalCoordinates L (y ≫ (goodOpen ℂ).ι) ∧
      rawActPoint L g (x ≫ (goodOpen ℂ).ι) hx = y ≫ (goodOpen ℂ).ι := by
  obtain ⟨M,hM,eM,hpM,hbaseM,hIM,hSM,_⟩ :=
    LagrangianGoodOpenOrderedModel.exists_ordered_model ℂ L (algebraMap ℂ L) x
      (by simpa only [Category.assoc] using hx)
  obtain ⟨N,hN,eN,hpN,hbaseN,hIN,hSN,_⟩ :=
    LagrangianGoodOpenOrderedModel.exists_ordered_model ℂ L (algebraMap ℂ L) y
      (by simpa only [Category.assoc] using hy)
  letI : IsIntegral (curve L M) := hIM
  letI : SmoothOfRelativeDimension 1 (curveProjection L M) := hSM
  letI : IsIntegral (curve L N) := hIN
  letI : SmoothOfRelativeDimension 1 (curveProjection L N) := hSN
  let eMN := eM ≪≫ e ≪≫ eN.symm
  have heMN : eMN.hom ≫ curveProjection L N = curveProjection L M := by
    simp only [eMN, Iso.trans_hom, Iso.symm_hom, Category.assoc]
    have hi : eN.inv ≫ curveProjection L N = fibreProjection L y :=
      LagrangianGoodOpenOrderedModel.iso_inv_base eN _ _ hbaseN
    rw [hi,he,hbaseM]
  have hnpM : ¬ Nonempty (LinearSeries L (curveProjection L M)
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le 5 1) :=
    (MukaiCurveIsoLinearSeries.no_degree_five_pencil_iff L
      (curveProjection L M) (fibreProjection L x) eM hbaseM
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := curveProjection L M)).le
      (IsCurve.topologicalKrullDim_eq_one (k := L) (f := fibreProjection L x)).le).mpr hnp
  obtain ⟨g,hg⟩ := MukaiNonpentagonalParameterOrbitConverse.exists_native_parameter_orbit_of_curveIso
    L M N hM hN eMN heMN hnpM
  change rawPoint L M hM = x ≫ (goodOpen ℂ).ι at hpM
  change rawPoint L N hN = y ≫ (goodOpen ℂ).ι at hpN
  have hPM := congrArg (originalCoordinates L) hpM
  have hPN := congrArg (originalCoordinates L) hpN
  change originalPoint L M hM = originalCoordinates L (x ≫ (goodOpen ℂ).ι) at hPM
  change originalPoint L N hN = originalCoordinates L (y ≫ (goodOpen ℂ).ι) at hPN
  have horbit : PrimitiveFieldMatrixAction.actPoint L g
      (originalCoordinates L (x ≫ (goodOpen ℂ).ι)) (originalCoordinates_projection L _ hx) =
      originalCoordinates L (y ≫ (goodOpen ℂ).ι) := by
    have hc := actPoint_congr L g (originalPoint L M hM)
      (originalCoordinates L (x ≫ (goodOpen ℂ).ι)) (originalPoint_projection L M hM)
      (originalCoordinates_projection L _ hx) hPM
    exact hc.symm.trans (hg.trans hPN)
  exact ⟨g,horbit,(rawActPoint_eq_iff L g _ _ hx).mpr horbit⟩

/-- The existing coordinate-good map exactly recovers the original
native point after converting its actual raw parameter back by C inverse. -/
theorem originalCoordinates_coordinateGoodMap
    (z : Spec (.of L) ⟶ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.toScheme) :
    originalCoordinates L ((z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) ≫ (goodOpen ℂ).ι) =
      z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι := by
  unfold originalCoordinates
  rw [Category.assoc z LagrangianFamilyOrbitIsomorphism.coordinateGoodMap,
    LagrangianFamilyOrbitIsomorphism.coordinateGoodMap_inclusion]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The raw coordinate-good point has the same actual field coefficient map. -/
theorem coordinateGoodPoint_projection
    (a : Spec (.of L) ⟶ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.toScheme)
    (ha : (a ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L))) :
    ((a ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) ≫ (goodOpen ℂ).ι) ≫
      parameterProjection ℂ = Spec.map (CommRingCat.ofHom (algebraMap ℂ L)) := by
  calc
    _ = (a ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫
        (LagrangianParameterCoordinates.coordinateChange.hom ≫ parameterProjection ℂ) := by
      simp only [Category.assoc,
        LagrangianFamilyOrbitIsomorphism.coordinateGoodMap_inclusion_assoc]
    _ = _ := by rw [LagrangianParameterCoordinates.coordinateChange_projection]; exact ha

/-- On the genuine coordinate-good domain used by the original native
quotient, the very same physical curve isomorphism yields the literal
native action on the original z and w points themselves. -/
theorem exists_coordinate_native_orbit_of_curveIso
    (z w : Spec (.of L) ⟶ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.toScheme)
    (hz : (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (hw : (w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) ≫ parameterProjection ℂ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ L)))
    (e : fibre L (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) ≅
      fibre L (w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap))
    (he : e.hom ≫ fibreProjection L (w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) =
      fibreProjection L (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap))
    (hnp : SourceNoFivePencil L (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap)) :
    ∃ g : M9.PrimitiveStabilizer.Sp6 L,
      PrimitiveFieldMatrixAction.actPoint L g
        (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι) hz =
      w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι := by
  obtain ⟨g,hg,_⟩ := exists_native_and_raw_orbit_of_curveIso L
    (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap)
    (w ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap)
    (coordinateGoodPoint_projection L z hz) (coordinateGoodPoint_projection L w hw) e he hnp
  refine ⟨g,?_⟩
  have hc := actPoint_congr L g
    (originalCoordinates L ((z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodMap) ≫ (goodOpen ℂ).ι))
    (z ≫ LagrangianFamilyOrbitIsomorphism.coordinateGoodOpen.ι)
    (originalCoordinates_projection L _ (coordinateGoodPoint_projection L z hz)) hz
    (originalCoordinates_coordinateGoodMap L z)
  exact hc.symm.trans (hg.trans (originalCoordinates_coordinateGoodMap L w))

end M9Native.LagrangianGoodFieldOrbit
