module

public import M9StacksIntegration.PrimitiveGenericOpenPoints
public import M9StacksIntegration.PrimitiveNativeInvariantRationality
public import M9StacksIntegration.FieldPointDescentGeometric

@[expose] public section

/-! A genuine quotient-field criterion for a dominant actual morphism
from an actual nonempty open of the native primitive Grassmannian.

Only morphism invariance on its actual common domain and geometric
field-point orbit classification are inputs. The field image is a
conclusion, via effective characteristic-zero field descent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace M9Native.PrimitiveGeometricQuotientField

open PrimitiveGrassmannianAction PrimitiveUniversalFieldAction PrimitiveUniversalExtensionPoints
open PrimitiveGenericOpenPoints NativeGenericPullbackEvaluation

variable (U : space.Opens) [Nonempty U]
variable {Y : Scheme} [IsIntegral Y] (pY : Y ⟶ PrimitiveFamilyFreeAction.base)
  (q : U.toScheme ⟶ Y) [IsDominant q]

/-- The exact geometric obligations of the future actual classifier.
No field-image, rational-function descent or quotient-field premise occurs. -/
structure Geometry : Prop where
  over_base : q ≫ pY = U.ι ≫ projection
  invariant : ∀ (T : Over PrimitiveFamilyFreeAction.base)
    (x y : T ⟶ openOver U) (g : PrimitiveConstantFieldAction.Sp6),
    x ≫ inclusionOver U ≫ PrimitiveConstantFieldAction.overMap g = y ≫ inclusionOver U →
      x.left ≫ q = y.left ≫ q
  orbit_fibers : ∀ (L : Type) [Field L] [IsAlgClosed L] [Algebra ℂ L]
    (x y : overField L ⟶ openOver U), x.left ≫ q = y.left ≫ q →
      ∃ g : M9.PrimitiveStabilizer.Sp6 L,
        (lift (PrimitiveOriginalExtensionAction.nativeGroupPoint g)
          (x ≫ inclusionOver U) ≫ nativeAction.act).left = (y ≫ inclusionOver U).left

/-- The native generic-stalk pullback of the actual map, transported back
through the original open immersion into the original Grassmannian field. -/
def pullbackRing : Y.functionField →+* E :=
  (fieldIso U).symm.toRingHom.comp (NativeDominantFunctionField.map q)

/-- The original structural complex coefficient map is retained. -/
theorem pullbackRing_scalar (hbase : q ≫ pY = U.ι ≫ projection) :
    (pullbackRing U q).comp (GrassmannianCharts.structureScalarMap ℂ pY) = algebraMap ℂ E := by
  apply RingHom.ext
  intro c
  apply (fieldIso U).injective
  change fieldIso U ((fieldIso U).symm
    (NativeDominantFunctionField.map q (GrassmannianCharts.structureScalarMap ℂ pY c))) =
      fieldIso U (algebraMap ℂ E c)
  rw [RingEquiv.apply_symm_apply]
  have h := RingHom.congr_fun (NativeDominantFunctionField.map_scalar ℂ q pY) c
  rw [hbase] at h
  exact h.trans (RingHom.congr_fun (fieldIso_scalar U) c).symm

/-- The source is the actual target generic stalk with its actual
structure-map algebra, not a replacement field. -/
def pullback (hbase : q ≫ pY = U.ι ≫ projection) :
    letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
    Y.functionField →ₐ[ℂ] E := by
  letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
  exact { __ := pullbackRing U q
          commutes' := RingHom.congr_fun (pullbackRing_scalar U pY q hbase) }

theorem point_map {L : Type} [Field L] [Algebra ℂ L] (s : E →ₐ[ℂ] L) :
    (pointOpen U s).left ≫ q = point (s.toRingHom.comp (pullbackRing U q)) :=
  pointOpenRing_map U q s.toRingHom

/-- Actual morphism invariance on the common domain forces every native
rational pullback to be fixed by the original constant Sp6 action. -/
theorem pullbackRing_mem_fixed (h : Geometry U pY q) (a : Y.functionField) :
    pullbackRing U q a ∈ PrimitiveRadicalInvariantDescent.nativeFixedField := by
  apply (PrimitiveRadicalInvariantDescent.mem_nativeFixedField_iff _).mpr
  intro g
  let s : E →ₐ[ℂ] E := AlgHom.id ℂ E
  let t : E →ₐ[ℂ] E := (PrimitiveConstantFieldAction.fieldPullback g).toAlgHom
  have hact : pointOpen U s ≫ inclusionOver U ≫ PrimitiveConstantFieldAction.overMap g =
      pointOpen U t ≫ inclusionOver U := by
    apply Over.OverMorphism.ext
    change (pointOpenRing U s.toRingHom ≫ U.ι) ≫ PrimitiveConstantFieldAction.schemeMap g =
      pointOpenRing U t.toRingHom ≫ U.ι
    rw [pointOpenRing_comp, pointOpenRing_comp, NativeGenericPointNaturality.constant_action]
    rfl
  have hq := h.invariant (overField E) (pointOpen U s) (pointOpen U t) g hact
  rw [point_map, point_map] at hq
  have he := genericPointHom_injective hq
  have ha := RingHom.congr_fun he a
  change pullbackRing U q a = PrimitiveConstantFieldAction.fieldPullback g (pullbackRing U q a) at ha
  exact ha.symm

/-- The geometric orbit classification supplies equality of invariant
values on the actual scheme-theoretic generic kernel pair. -/
theorem invariant_equal_on_fibers (h : Geometry U pY q) (f : E)
    (hf : f ∈ PrimitiveRadicalInvariantDescent.nativeFixedField)
    {L : Type} [Field L] [IsAlgClosed L] [Algebra ℂ L]
    (s t : E →ₐ[ℂ] L)
    (he : s.toRingHom.comp (pullbackRing U q) = t.toRingHom.comp (pullbackRing U q)) :
    s f = t f := by
  have hq : (pointOpen U s).left ≫ q = (pointOpen U t).left ≫ q := by
    rw [point_map, point_map, he]
  obtain ⟨g, hg⟩ := h.orbit_fibers L (pointOpen U s) (pointOpen U t) hq
  rw [pointOpen_inclusion, pointOpen_inclusion] at hg
  exact PrimitiveGeometricExtensionInvariance.eq_of_original_action f
    ((PrimitiveRadicalInvariantDescent.mem_nativeFixedField_iff f).mp hf) g s t hg

/-- Every actual native invariant descends to the actual target's native
function field. Characteristic-zero field descent discharges separability
and tensor-reducedness; no orbit section is chosen. -/
theorem invariant_mem_image (h : Geometry U pY q) (f : E)
    (hf : f ∈ PrimitiveRadicalInvariantDescent.nativeFixedField) :
    f ∈ Set.range (pullbackRing U q) := by
  let : Algebra ℂ Y.functionField := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
  let pb : Y.functionField →ₐ[ℂ] E := pullback U pY q h.over_base
  let : Algebra Y.functionField E := pb.toRingHom.toAlgebra
  let : IsScalarTower ℂ Y.functionField E :=
    IsScalarTower.of_algebraMap_eq' pb.comp_algebraMap.symm
  let : CharZero Y.functionField := PrimitiveExtensionFieldBridge.charZero_extension Y.functionField
  change f ∈ Set.range (algebraMap Y.functionField E)
  apply (FieldPointDescent.mem_range_iff_forall_algClosed_embeddings_charZero Y.functionField f).mpr
  intro L _ _ _ s t
  let : Algebra ℂ L :=
    ((algebraMap Y.functionField L).comp (algebraMap ℂ Y.functionField)).toAlgebra
  let : IsScalarTower ℂ Y.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  let sC : E →ₐ[ℂ] L := s.restrictScalars ℂ
  let tC : E →ₐ[ℂ] L := t.restrictScalars ℂ
  have he : sC.toRingHom.comp (pullbackRing U q) = tC.toRingHom.comp (pullbackRing U q) := by
    apply RingHom.ext
    intro a
    change s (algebraMap Y.functionField E a) = t (algebraMap Y.functionField E a)
    exact (s.commutes a).trans (t.commutes a).symm
  exact invariant_equal_on_fibers U pY q h f hf sC tC he

/-- Exact image of the actual dominant scheme map: the equality is derived
from its actual morphism invariance and actual geometric fibers. -/
theorem image_eq_fixed (h : Geometry U pY q) (f : E) :
    f ∈ Set.range (pullbackRing U q) ↔ f ∈ PrimitiveRadicalInvariantDescent.nativeFixedField := by
  constructor
  · rintro ⟨a, rfl⟩
    exact pullbackRing_mem_fixed U pY q h a
  · exact invariant_mem_image U pY q h f

/-- The original target field identifies with the actual native fixed
field through the actual map's pullback. -/
def fixedFieldEquiv (h : Geometry U pY q) :
    letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
    Y.functionField ≃ₐ[ℂ] PrimitiveRadicalInvariantDescent.nativeFixedField := by
  letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
  let pb := pullback U pY q h.over_base
  let e : Y.functionField →ₐ[ℂ] PrimitiveRadicalInvariantDescent.nativeFixedField :=
    { toFun := fun a => ⟨pb a, pullbackRing_mem_fixed U pY q h a⟩
      map_zero' := Subtype.ext (map_zero pb)
      map_one' := Subtype.ext (map_one pb)
      map_add' := fun a b => Subtype.ext (map_add pb a b)
      map_mul' := fun a b => Subtype.ext (map_mul pb a b)
      commutes' := fun c => Subtype.ext (pb.commutes c) }
  refine AlgEquiv.ofBijective e ⟨e.injective, ?_⟩
  intro f
  obtain ⟨a, ha⟩ := invariant_mem_image U pY q h f.val f.property
  exact ⟨a, Subtype.ext ha⟩

theorem fixedFieldEquiv_coe (h : Geometry U pY q) (a : Y.functionField) :
    letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
    (fixedFieldEquiv U pY q h a).val = pullbackRing U q a := rfl

/-- Conditional only on the displayed actual geometric map/classification,
the target's genuine structural function field is rational in dimension24. -/
def rationalEquiv (h : Geometry U pY q) :
    letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
    Y.functionField ≃ₐ[ℂ] M9.RationalField ℂ 24 := by
  letI := (GrassmannianCharts.structureScalarMap ℂ pY).toAlgebra
  exact (fixedFieldEquiv U pY q h).trans PrimitiveNativeInvariantRationality.rationalEquiv

end M9Native.PrimitiveGeometricQuotientField
