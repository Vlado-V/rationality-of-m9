module

public import M9StacksIntegration.AllTestNativeOriginalFamilyNaturality
public import M9StacksIntegration.AllTestOriginalFamilyCategory

/-!
An actual functor from native curve families to literal ALL-original families.
The inputs are native functors, their proved structural square, and intrinsic
genus membership on every object. Root's native fullness constructs each
original Cartesian arrow. Native total-map injectivity and the actual recovery
isomorphisms prove the functor laws and natural recovery. No original functor,
comparison, lifting, source equivalence or naturality is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeOriginalFamilyFunctor

open AllTestBoundedCharts AllTestBoundedRestriction AllTestNativeCurveFamily
  AllTestNativeCurveNaturality AllTestNativeOriginalFamily
  AllTestNativeOriginalFamilyNaturality AllTestOriginalFamilyCategory

universe u v w

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- Restriction and actual coefficient extension preserve the original identity. -/
theorem nativeTotalMap_id {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    nativeTotalMap B hZ K hK F F (𝟙 F.total.obj) = 𝟙 (nativeTotal B hZ K hK F) := by
  apply ObjectProperty.hom_ext
  change (OverShriek.relocalizePresheafFunctor (fieldToInteger B hZ K hK)).map
      (𝟙 _) = 𝟙 _
  exact (OverShriek.relocalizePresheafFunctor (fieldToInteger B hZ K hK)).map_id _

/-- Restriction and actual coefficient extension preserve original composition. -/
theorem nativeTotalMap_comp
    {T U V : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g)
    (G : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj U) g)
    (H : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj V) g)
    (a : H.total.obj ⟶ G.total.obj) (b : G.total.obj ⟶ F.total.obj) :
    nativeTotalMap B hZ K hK F H (a ≫ b) =
      nativeTotalMap B hZ K hK G H a ≫ nativeTotalMap B hZ K hK F G b := by
  apply ObjectProperty.hom_ext
  change (OverShriek.relocalizePresheafFunctor (fieldToInteger B hZ K hK)).map
      (restrictMap K B hK a ≫ restrictMap K B hK b) = _
  exact (OverShriek.relocalizePresheafFunctor (fieldToInteger B hZ K hK)).map_comp _ _

variable {C : Type v} [Category.{w} C]
  (π : C ⥤ CurveFamily B hZ)
  (p : C ⥤ BigFppfOver B (Spec (.of K)) hK)
  (square : π ⋙ curvesProjectionOver B hZ =
    p ⋙ Over.map (fieldToInteger B hZ K hK))
  (g : ℕ) (genus : ∀ x : C, IsSmoothH0FamilyOfFibreGenus B hZ g (π.obj x))

/-- The native structural square gives the actual base equality on every object. -/
def baseEq (x : C) : (π.obj x).base = nativeBase B hZ K hK (p.obj x) :=
  Functor.congr_obj square x

/-- The same square supplies the precise base transports on every native arrow. -/
theorem native_baseMap {x y : C} (a : x ⟶ y) :
    (π.map a).baseMap = eqToHom (baseEq B hZ K hK π p square x) ≫
      (Over.map (fieldToInteger B hZ K hK)).map (p.map a) ≫
        eqToHom (baseEq B hZ K hK π p square y).symm :=
  Functor.congr_hom square a

/-- Intrinsic native genus constructs the literal original family and original base. -/
def originalObject (x : C) : CurveObject K g :=
  ⟨(boundedInclusion B K hK).obj (p.obj x),
    originalFamily B hZ K hK (p.obj x) (π.obj x)
      (baseEq B hZ K hK π p square x) g (genus x)⟩

/-- The constructed original family recovers the actual specified native object. -/
def recoveryIso (x : C) :
    nativeCurveFamily B hZ K hK (originalObject B hZ K hK π p square g genus x).family ≅
      π.obj x :=
  originalFamilyNativeIso B hZ K hK (p.obj x) (π.obj x)
    (baseEq B hZ K hK π p square x) g (genus x)

/-- Recovery retains the specified base and coefficient map literally. -/
theorem recoveryIso_baseMap (x : C) :
    (recoveryIso B hZ K hK π p square g genus x).hom.baseMap =
      eqToHom (baseEq B hZ K hK π p square x).symm :=
  originalFamilyNativeIso_baseMap B hZ K hK (p.obj x) (π.obj x)
    (baseEq B hZ K hK π p square x) g (genus x)

/-- The inverse recovery has the inverse, equally specified, base identification. -/
theorem recoveryIso_inv_baseMap (x : C) :
    (recoveryIso B hZ K hK π p square g genus x).inv.baseMap =
      eqToHom (baseEq B hZ K hK π p square x) :=
  originalFamilyNativeIso_inv_baseMap B hZ K hK (p.obj x) (π.obj x)
    (baseEq B hZ K hK π p square x) g (genus x)

/-- Conjugation by the actual recovery isomorphisms, with no chosen comparison input. -/
def conjugateMap {x y : C} (a : x ⟶ y) :
    nativeCurveFamily B hZ K hK (originalObject B hZ K hK π p square g genus x).family ⟶
      nativeCurveFamily B hZ K hK (originalObject B hZ K hK π p square g genus y).family :=
  (recoveryIso B hZ K hK π p square g genus x).hom ≫ π.map a ≫
    (recoveryIso B hZ K hK π p square g genus y).inv

theorem conjugateMap_id (x : C) :
    conjugateMap B hZ K hK π p square g genus (𝟙 x) = 𝟙 _ := by
  simp [conjugateMap]

theorem conjugateMap_comp {x y z : C} (a : x ⟶ y) (b : y ⟶ z) :
    conjugateMap B hZ K hK π p square g genus (a ≫ b) =
      conjugateMap B hZ K hK π p square g genus a ≫
        conjugateMap B hZ K hK π p square g genus b := by
  simp [conjugateMap, Category.assoc]

/-- Genuine native fullness constructs each actual ALL-original Cartesian arrow. -/
def originalArrow {x y : C} (a : x ⟶ y) :
    originalObject B hZ K hK π p square g genus x ⟶
      originalObject B hZ K hK π p square g genus y where
  baseMap := (boundedInclusion B K hK).map (p.map a)
  totalMap := originalCartesianMap B hZ K hK (p.obj y) (p.obj x) (π.obj y) (π.obj x)
    (baseEq B hZ K hK π p square y) (baseEq B hZ K hK π p square x)
    g (genus y) (genus x) (p.map a) (π.map a) (native_baseMap B hZ K hK π p square a)
  cartesian := originalCartesianMap_isPullback B hZ K hK
    (p.obj y) (p.obj x) (π.obj y) (π.obj x)
    (baseEq B hZ K hK π p square y) (baseEq B hZ K hK π p square x)
    g (genus y) (genus x) (p.map a) (π.map a) (native_baseMap B hZ K hK π p square a)

/-- The actual original arrow recovers the actual native total map, not an assumed lift. -/
theorem originalArrow_nativeTotalMap {x y : C} (a : x ⟶ y) :
    nativeTotalMap B hZ K hK
        (originalObject B hZ K hK π p square g genus y).family
        (originalObject B hZ K hK π p square g genus x).family
        (originalArrow B hZ K hK π p square g genus a).totalMap =
      (conjugateMap B hZ K hK π p square g genus a).totalMap :=
  originalCartesianMap_nativeTotalMap B hZ K hK
    (p.obj y) (p.obj x) (π.obj y) (π.obj x)
    (baseEq B hZ K hK π p square y) (baseEq B hZ K hK π p square x)
    g (genus y) (genus x) (p.map a) (π.map a) (native_baseMap B hZ K hK π p square a)

/-- Recovery holds for the whole native Cartesian arrow, including its actual base map. -/
theorem originalArrow_nativeCartesianMap {x y : C} (a : x ⟶ y) :
    nativeCartesianMap B hZ K hK (p.map a)
        (originalObject B hZ K hK π p square g genus y).family
        (originalObject B hZ K hK π p square g genus x).family
        (originalArrow B hZ K hK π p square g genus a).totalMap
        (originalArrow B hZ K hK π p square g genus a).cartesian =
      conjugateMap B hZ K hK π p square g genus a := by
  apply CurveFamily.Hom.ext
  · exact (comparisonArrow_baseMap B hZ K hK
      (p.obj y) (p.obj x) (π.obj y) (π.obj x)
      (baseEq B hZ K hK π p square y) (baseEq B hZ K hK π p square x)
      g (genus y) (genus x) (p.map a) (π.map a)
      (native_baseMap B hZ K hK π p square a)).symm
  · exact originalArrow_nativeTotalMap B hZ K hK π p square g genus a

/-- Identity is forced by genuine native faithfulness and the actual recovery isomorphism. -/
theorem originalArrow_id (x : C) :
    originalArrow B hZ K hK π p square g genus (𝟙 x) = 𝟙 _ := by
  apply CurveHom.ext
  · change (boundedInclusion B K hK).map (p.map (𝟙 x)) = 𝟙 _
    rw [p.map_id, (boundedInclusion B K hK).map_id]
  · apply AllTestBoundedFaithful.nativeTotalMap_injective K B hK hZ
      (originalObject B hZ K hK π p square g genus x).family
      (originalObject B hZ K hK π p square g genus x).family
    change nativeTotalMap B hZ K hK _ _
        (originalArrow B hZ K hK π p square g genus (𝟙 x)).totalMap =
      nativeTotalMap B hZ K hK _ _
        (𝟙 (originalObject B hZ K hK π p square g genus x).family.total.obj)
    rw [originalArrow_nativeTotalMap, conjugateMap_id]
    exact (nativeTotalMap_id B hZ K hK (T := p.obj x)
      (originalObject B hZ K hK π p square g genus x).family).symm

/-- Composition is forced by genuine native faithfulness and cancellation of recovery. -/
theorem originalArrow_comp {x y z : C} (a : x ⟶ y) (b : y ⟶ z) :
    originalArrow B hZ K hK π p square g genus (a ≫ b) =
      originalArrow B hZ K hK π p square g genus a ≫
        originalArrow B hZ K hK π p square g genus b := by
  apply CurveHom.ext
  · change (boundedInclusion B K hK).map (p.map (a ≫ b)) =
      (boundedInclusion B K hK).map (p.map a) ≫ (boundedInclusion B K hK).map (p.map b)
    rw [p.map_comp, (boundedInclusion B K hK).map_comp]
  · apply AllTestBoundedFaithful.nativeTotalMap_injective K B hK hZ
      (originalObject B hZ K hK π p square g genus z).family
      (originalObject B hZ K hK π p square g genus x).family
    change nativeTotalMap B hZ K hK _ _
        (originalArrow B hZ K hK π p square g genus (a ≫ b)).totalMap =
      nativeTotalMap B hZ K hK _ _
        ((originalArrow B hZ K hK π p square g genus a).totalMap ≫
          (originalArrow B hZ K hK π p square g genus b).totalMap)
    rw [originalArrow_nativeTotalMap, nativeTotalMap_comp,
      originalArrow_nativeTotalMap, originalArrow_nativeTotalMap, conjugateMap_comp]
    rfl

/-- The derived functor of literal ALL-original genus-g families. -/
def toOriginal : C ⥤ CurveObject K g where
  obj := originalObject B hZ K hK π p square g genus
  map := originalArrow B hZ K hK π p square g genus
  map_id := originalArrow_id B hZ K hK π p square g genus
  map_comp := originalArrow_comp B hZ K hK π p square g genus

/-- The original coefficient and base functor are retained literally on all objects/arrows. -/
theorem toOriginal_projection :
    toOriginal B hZ K hK π p square g genus ⋙ projection K g =
      p ⋙ boundedInclusion B K hK := rfl

/-- The actual native image of the constructed ORIGINAL functor, on objects and arrows. -/
def nativeImage : C ⥤ CurveFamily B hZ where
  obj x := nativeCurveFamily B hZ K hK
    (originalObject B hZ K hK π p square g genus x).family
  map {x y} a := nativeCartesianMap B hZ K hK (p.map a)
    (originalObject B hZ K hK π p square g genus y).family
    (originalObject B hZ K hK π p square g genus x).family
    (originalArrow B hZ K hK π p square g genus a).totalMap
    (originalArrow B hZ K hK π p square g genus a).cartesian
  map_id x := by
    rw [originalArrow_nativeCartesianMap, conjugateMap_id]
  map_comp a b := by
    simpa only [originalArrow_nativeCartesianMap] using
      conjugateMap_comp B hZ K hK π p square g genus a b

/-- The actual native-image arrow is the genuine recovery conjugation. -/
theorem nativeImage_map {x y : C} (a : x ⟶ y) :
    (nativeImage B hZ K hK π p square g genus).map a =
      (recoveryIso B hZ K hK π p square g genus x).hom ≫ π.map a ≫
        (recoveryIso B hZ K hK π p square g genus y).inv :=
  originalArrow_nativeCartesianMap B hZ K hK π p square g genus a

/-- Actual recovery is natural on every native arrow over every native base. -/
theorem recovery_naturality {x y : C} (a : x ⟶ y) :
    (nativeImage B hZ K hK π p square g genus).map a ≫
        (recoveryIso B hZ K hK π p square g genus y).hom =
      (recoveryIso B hZ K hK π p square g genus x).hom ≫ π.map a := by
  rw [nativeImage_map]
  simp [Category.assoc]

/-- The natural recovery is DERIVED from the constructed full-original functor. -/
def recoveryNatIso : nativeImage B hZ K hK π p square g genus ≅ π :=
  NatIso.ofComponents (recoveryIso B hZ K hK π p square g genus)
    (fun a => recovery_naturality B hZ K hK π p square g genus a)

end M9StacksIntegration.AllTestNativeOriginalFamilyFunctor
