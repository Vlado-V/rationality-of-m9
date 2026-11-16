module

public import M9StacksIntegration.AllTestNativeCartesianCover
public import M9StacksIntegration.AllTestBoundedCurveProper
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies

/-!
# An actual native curve family from every original all-test family

The original total algebraic space is first restricted on the actual
field-base site, then extended by the actual lower-shriek functor to the
integer-base site used by native curve stacks. Its base retains the original
map to Spec K. Actual cartesian schematic covers prove all CurveFamily
fields over the entire test base. No native curve-family, classification,
H0 base-change or coarse-space premise is supplied.
-/

set_option autoImplicit false

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeCurveFamily
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedCartesian
  AllTestBoundedAlgebraicSpace AllTestBoundedCurveSmooth AllTestBoundedCurveProper
  AllTestNativeCartesianCover
universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The actual structural map of the original field to the native integer base. -/
def fieldToInteger : B.obj hK ⟶ B.obj hZ :=
  ObjectProperty.homMk (specULiftZIsTerminal.from (Spec (.of K)))

/-- The same original base scheme, with its native integer-base structure. -/
abbrev nativeBase (T : BigFppfOver B (Spec (.of K)) hK) : BigFppfOver B integerBase hZ :=
  (Over.map (fieldToInteger B hZ K hK)).obj T

/-- The actual original total presheaf, restricted over K and lower-shriek
extended to the native integer-base site. -/
def nativeTotal {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    AlgebraicSpaces B integerBase hZ :=
  extendedSpace B integerBase hZ (Spec (.of K)) hK (fieldToInteger B hZ K hK)
    (restrictedFamilySpace K B hK F)

/-- The actual extended original projection, with its literal native base. -/
def nativeProjection {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    nativeTotal B hZ K hK F ⟶ schemeSpace (nativeBase B hZ K hK T) :=
  ObjectProperty.homMk
    (extendedProjection B integerBase hZ (Spec (.of K)) hK (fieldToInteger B hZ K hK) T
      (baseMap K B hK T F.projection))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Both actual properness and smooth relative dimension one of the extended
original projection follow from the same original schematic cartesian cover. -/
theorem nativeProjection_properties {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    Space.IsProper B integerBase hZ (nativeProjection B hZ K hK F).hom ∧
      Space.IsSmoothOfRelativeDimension B integerBase hZ 1
        (nativeProjection B hZ K hK F).hom := by
  have hT : B.Contains ((boundedInclusion B K hK).obj T).left := T.left.property
  obtain ⟨U, Z, v, q, r, hU, hZs, hv, hs, hcart, hq⟩ :=
    AllTestSingleSchematicCover.exists_bounded_schematic_etale_cover B K
      (T := (boundedInclusion B K hK).obj T) (g := g) hT F
  rcases U with ⟨U, ⟨⟨⟩⟩, Uhom⟩
  rcases Z with ⟨Z, ⟨⟨⟩⟩, Zhom⟩
  let Un := siteObject B (Spec (.of K)) hK hU Uhom
  let Zn := siteObject B (Spec (.of K)) hK hZs Zhom
  let qn : Zn ⟶ Un := boundedPreimage B K hK q
  let vn : Un ⟶ T := boundedPreimage B K hK v
  let a := fieldToInteger B hZ K hK
  have hcart' := extended_square B integerBase hZ (Spec (.of K)) hK a
    (chartMap K B hK Zn r) (baseMap K B hK T F.projection) qn vn
    (chart_isPullback K B hK qn vn r F.projection hcart)
  have hqp := Space.isProper_yoneda_map B integerBase hZ ((Over.map a).map qn) hq.1
  let : SmoothOfRelativeDimension 1
      ((BigFppfOver.toScheme B integerBase hZ).map ((Over.map a).map qn)) := hq.2.1
  have hqs := Space.isSmoothOfRelativeDimension_yoneda_map B integerBase hZ
    ((Over.map a).map qn) 1
  constructor
  · exact AllTestNativeCartesianCover.property_of_schematic_cover B integerBase hZ
      (Space.properProperty B integerBase hZ) (nativeTotal B hZ K hK F)
      (relocalizeChart B (Spec (.of K)) integerBase hK hZ a (chartMap K B hK Zn r))
      (nativeProjection B hZ K hK F).hom ((Over.map a).map qn) ((Over.map a).map vn)
      hcart' hs hv hqp
  · exact AllTestNativeCartesianCover.property_of_schematic_cover B integerBase hZ
      (Space.smoothOfRelativeDimensionProperty B integerBase hZ 1) (nativeTotal B hZ K hK F)
      (relocalizeChart B (Spec (.of K)) integerBase hK hZ a (chartMap K B hK Zn r))
      (nativeProjection B hZ K hK F).hom ((Over.map a).map qn) ((Over.map a).map vn)
      hcart' hs hv hqs

/-- EVERY original all-test family over a bounded original test base gives
an actual native CurveFamily. Properness, flatness, finite presentation and
relative dimension are proved from the unchanged original geometry. -/
def nativeCurveFamily {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) : CurveFamily B hZ :=
  { base := nativeBase B hZ K hK T
    total := nativeTotal B hZ K hK F
    toBase := nativeProjection B hZ K hK F
    flat := Space.isFlat_of_isSmooth B integerBase hZ _
      (nativeProjection_properties B hZ K hK F).2.1
    proper := (nativeProjection_properties B hZ K hK F).1
    finitePresentation :=
      ⟨Space.isLocallyOfFinitePresentation_of_isSmooth B integerBase hZ
          (nativeProjection_properties B hZ K hK F).2.1,
        (nativeProjection_properties B hZ K hK F).1.2.1.2,
        Space.isQuasiSeparated_of_isSeparated B integerBase hZ
          (nativeProjection_properties B hZ K hK F).1.1⟩
    relativeDimensionLE := (nativeProjection_properties B hZ K hK F).2.2.hasRelativeDimensionLE }

@[simp] theorem nativeCurveFamily_base {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (nativeCurveFamily B hZ K hK F).base = nativeBase B hZ K hK T := rfl

@[simp] theorem nativeCurveFamily_total {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (nativeCurveFamily B hZ K hK F).total = nativeTotal B hZ K hK F := rfl

@[simp] theorem nativeCurveFamily_toBase {T : BigFppfOver B (Spec (.of K)) hK} {g : ℕ}
    (F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj T) g) :
    (nativeCurveFamily B hZ K hK F).toBase = nativeProjection B hZ K hK F := rfl

/-- The native base still carries the actual original map to Spec K. -/
def baseCoefficientMap (T : BigFppfOver B (Spec (.of K)) hK) :
    nativeBase B hZ K hK T ⟶ Over.mk (fieldToInteger B hZ K hK) :=
  Over.homMk T.hom rfl

@[simp] theorem baseCoefficientMap_toScheme (T : BigFppfOver B (Spec (.of K)) hK) :
    (BigFppfOver.toScheme B integerBase hZ).map (baseCoefficientMap B hZ K hK T) =
      ((boundedInclusion B K hK).obj T).hom := rfl

end M9StacksIntegration.AllTestNativeCurveFamily
