module

public import M9StacksIntegration.AllTestNativeOriginalFamilyFunctor
public import M9StacksIntegration.NativeChosenGenusObjectMembership

/-!
The actual chosen smooth-genus stack maps to the actual ALL-original family
category on every native object and every native arrow, over arbitrary native
bases. The structural square comes from the proved original projection; genus
comes from the actual smooth-open object. No original functor, comparison,
source equivalence, genus membership, lifting or naturality is a premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace M9Native.GenusNineOriginalFamilyFunctor

open M9StacksIntegration M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeCurveFamily M9StacksIntegration.AllTestNativeCurveNaturality

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

abbrev source (g : ℕ) (hg : 2 ≤ g) :=
  M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg

abbrev rawProjection (g : ℕ) (hg : 2 ≤ g) :=
  NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg

abbrev baseProjection (g : ℕ) (hg : 2 ≤ g) :=
  (source B hZ K hK g hg).val.val.p

/-- The two existing coefficient arrows are the same actual map to the integer scheme. -/
theorem coefficientArrow_eq_fieldToInteger :
    NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK =
      fieldToInteger B hZ K hK := by
  apply B.inclusion.map_injective
  exact specULiftZIsTerminal.hom_ext _ _

/-- The genuine chosen-source projection gives the full native structural square. -/
theorem structuralSquare (g : ℕ) (hg : 2 ≤ g) :
    rawProjection B hZ K hK g hg ⋙ curvesProjectionOver B hZ =
      baseProjection B hZ K hK g hg ⋙ Over.map (fieldToInteger B hZ K hK) := by
  simpa only [coefficientArrow_eq_fieldToInteger B hZ K hK] using
    NativeSmoothGenusCoarseClassifier.originalProjection_comp B hZ K hK g hg

/-- Intrinsic genus is derived on EVERY actual native object, not only field objects. -/
theorem membership (g : ℕ) (hg : 2 ≤ g)
    (x : (source B hZ K hK g hg).val.val.obj) :
    IsSmoothH0FamilyOfFibreGenus B hZ g ((rawProjection B hZ K hK g hg).obj x) :=
  NativeGenusNineFieldObjectCurve.originalProjection_membership B hZ K hK g hg x

/-- The actual chosen source has a derived functor of literal ALL-original families. -/
def toOriginal (g : ℕ) (hg : 2 ≤ g) :
    (source B hZ K hK g hg).val.val.obj ⥤ AllTestOriginalFamilyCategory.CurveObject K g :=
  AllTestNativeOriginalFamilyFunctor.toOriginal B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg)

/-- Original bases and coefficient maps are retained on every object and arrow. -/
theorem toOriginal_projection (g : ℕ) (hg : 2 ≤ g) :
    toOriginal B hZ K hK g hg ⋙ AllTestOriginalFamilyCategory.projection K g =
      baseProjection B hZ K hK g hg ⋙ boundedInclusion B K hK :=
  AllTestNativeOriginalFamilyFunctor.toOriginal_projection B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg)

/-- The constructed original object recovers the same actual projected native family. -/
def recoveryIso (g : ℕ) (hg : 2 ≤ g)
    (x : (source B hZ K hK g hg).val.val.obj) :
    nativeCurveFamily B hZ K hK ((toOriginal B hZ K hK g hg).obj x).family ≅
      (rawProjection B hZ K hK g hg).obj x :=
  AllTestNativeOriginalFamilyFunctor.recoveryIso B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg) x

/-- Recovery has exactly the base identification derived from the structural square. -/
theorem recoveryIso_baseMap (g : ℕ) (hg : 2 ≤ g)
    (x : (source B hZ K hK g hg).val.val.obj) :
    (recoveryIso B hZ K hK g hg x).hom.baseMap =
      eqToHom (Functor.congr_obj (structuralSquare B hZ K hK g hg) x).symm :=
  AllTestNativeOriginalFamilyFunctor.recoveryIso_baseMap B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg) x

/-- The actual native image uses the actual constructed original Cartesian maps. -/
abbrev nativeImage (g : ℕ) (hg : 2 ≤ g) :=
  AllTestNativeOriginalFamilyFunctor.nativeImage B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg)

/-- Every chosen-source arrow is recovered by the literal native total-map comparison. -/
theorem nativeTotalMap_map (g : ℕ) (hg : 2 ≤ g)
    {x y : (source B hZ K hK g hg).val.val.obj} (a : x ⟶ y) :
    nativeTotalMap B hZ K hK
        ((toOriginal B hZ K hK g hg).obj y).family
        ((toOriginal B hZ K hK g hg).obj x).family
        ((toOriginal B hZ K hK g hg).map a).totalMap =
      ((recoveryIso B hZ K hK g hg x).hom ≫
        (rawProjection B hZ K hK g hg).map a ≫
          (recoveryIso B hZ K hK g hg y).inv).totalMap :=
  AllTestNativeOriginalFamilyFunctor.originalArrow_nativeTotalMap B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg) a

/-- The whole native arrow, including the coefficient-base map, is recovered. -/
theorem nativeImage_map (g : ℕ) (hg : 2 ≤ g)
    {x y : (source B hZ K hK g hg).val.val.obj} (a : x ⟶ y) :
    (nativeImage B hZ K hK g hg).map a =
      (recoveryIso B hZ K hK g hg x).hom ≫
        (rawProjection B hZ K hK g hg).map a ≫
          (recoveryIso B hZ K hK g hg y).inv :=
  AllTestNativeOriginalFamilyFunctor.nativeImage_map B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg) a

/-- Recovery is natural for ALL actual source arrows over ALL native bases. -/
theorem recovery_naturality (g : ℕ) (hg : 2 ≤ g)
    {x y : (source B hZ K hK g hg).val.val.obj} (a : x ⟶ y) :
    (nativeImage B hZ K hK g hg).map a ≫ (recoveryIso B hZ K hK g hg y).hom =
      (recoveryIso B hZ K hK g hg x).hom ≫ (rawProjection B hZ K hK g hg).map a :=
  AllTestNativeOriginalFamilyFunctor.recovery_naturality B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg) a

/-- The actual native family comparison is a DERIVED natural isomorphism. -/
def recoveryNatIso (g : ℕ) (hg : 2 ≤ g) :
    nativeImage B hZ K hK g hg ≅ rawProjection B hZ K hK g hg :=
  AllTestNativeOriginalFamilyFunctor.recoveryNatIso B hZ K hK
    (rawProjection B hZ K hK g hg) (baseProjection B hZ K hK g hg)
    (structuralSquare B hZ K hK g hg) g (membership B hZ K hK g hg)

/-- The literal genus-nine categorical functor on the actual chosen source. -/
abbrev genusNineToOriginal := toOriginal B hZ K hK 9 (by decide)

theorem genusNine_projection :
    genusNineToOriginal B hZ K hK ⋙ AllTestOriginalFamilyCategory.projection K 9 =
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
        B hZ K hK 9 (by decide)).val.val.p ⋙ boundedInclusion B K hK :=
  toOriginal_projection B hZ K hK 9 (by decide)

end M9Native.GenusNineOriginalFamilyFunctor
