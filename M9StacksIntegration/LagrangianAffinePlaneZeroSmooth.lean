module

public import M9StacksIntegration.LagrangianAffinePlaneSection
public import M9StacksIntegration.NativeVectorSectionZeroTransport
public import M9StacksIntegration.LagrangianCommonKernelSmooth

/-! The actual full arbitrary-plane line equation has a genuine
relative affine-line fixed-zero model. The proof transports the literal
native section zero scheme through a constructed scheme/bundle/section
isomorphism, retaining nilpotents and the original ground-field map. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module
universe u

namespace M9Native.LagrangianAffinePlaneZeroSmooth

open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianAffinePlaneSection
variable (K : Type u) [Field K]

abbrev lineIdeal (w : Fin 2 → LagrangianRing.V K) : (chartSpace K).IdealSheafData :=
  Stacks.Chow.zeroSchemeOfSection (chartSpace K) (LagrangianAffinePlaneSection.quotientBundle K) (lineSection K w)
abbrev lineZero (w : Fin 2 → LagrangianRing.V K) : Scheme.{u} := (lineIdeal K w).subscheme
abbrev lineInclusion (w : Fin 2 → LagrangianRing.V K) : lineZero K w ⟶ chartSpace K :=
  (lineIdeal K w).subschemeι
abbrev lineProjection (w : Fin 2 → LagrangianRing.V K) : lineZero K w ⟶ Spec (.of K) :=
  lineInclusion K w ≫ toLG K ≫ projection K

abbrev fixedIdeal : (chartSpace K).IdealSheafData :=
  Stacks.Chow.zeroSchemeOfSection (chartSpace K) (LagrangianAffinePlaneSection.quotientBundle K) (fixedSection K)
abbrev fixedZero : Scheme.{u} := (fixedIdeal K).subscheme
abbrev fixedInclusion : fixedZero K ⟶ chartSpace K := (fixedIdeal K).subschemeι
abbrev fixedProjection : fixedZero K ⟶ Spec (.of K) :=
  fixedInclusion K ≫ toLG K ≫ projection K

/-- The actual full zero scheme of the original arbitrary-plane line
is carried to the actual full first-section zero scheme on the chart. -/
def lineFixedIso (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    lineZero K w ≅ fixedZero K :=
  NativeVectorSectionZeroTransport.zeroSchemeIso (LagrangianAffinePlaneSection.quotientBundle K) (LagrangianAffinePlaneSection.quotientBundle K) 3
    (automorphism K w hw) (sectionIso K w hw) (fixedSection K) (lineSection K w)
    (sectionIso_apply K w hw)

@[reassoc] theorem lineFixedIso_projection (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) :
    (lineFixedIso K w hw).hom ≫ fixedProjection K = lineProjection K w :=
  NativeVectorSectionZeroTransport.zeroSchemeIso_over (LagrangianAffinePlaneSection.quotientBundle K) (LagrangianAffinePlaneSection.quotientBundle K) 3
    (automorphism K w hw) (sectionIso K w hw) (fixedSection K) (lineSection K w)
    (sectionIso_apply K w hw) (toLG K ≫ projection K) (toLG K ≫ projection K)
    (automorphism_groundProjection K w hw)

local instance originalQuotient_finite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientOnLG K).target :=
  (quotientOnLG K).finiteLocallyFree.isFiniteLocallyFree

/-- The original full native zero ideal commutes with this actual
pullback; no reduced-locus or pointwise comparison is used. -/
theorem fixedIdeal_eq_comap :
    fixedIdeal K = (LagrangianCommonKernelZero.zeroIdeal K).comap (toLG K) :=
  NativeVectorSectionZeroPullback.zeroSchemeOfSection_pullback (toLG K)
    (quotientOnLG K).target 3 (LagrangianCommonKernelZero.standardSection K)

/-- The actual first-section zero on the affine-line chart is the
actual native affine line over the original common-kernel zero scheme. -/
def fixedIsoAffine : fixedZero K ≅
    𝔸(CoordinateIndex.{u}; LagrangianCommonKernelZero.zeroSpace K) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (fixedIdeal_eq_comap K)) ≪≫
    (LagrangianCommonKernelZero.zeroIdeal K).comapIso (toLG K) ≪≫
    (AffineSpace.isPullback_map (n:=CoordinateIndex.{u})
      (LagrangianCommonKernelZero.zeroInclusion K)).isoPullback.symm

private theorem subschemeι_transport {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

@[reassoc] theorem fixedIsoAffine_map :
    (fixedIsoAffine K).hom ≫ AffineSpace.map CoordinateIndex.{u}
      (LagrangianCommonKernelZero.zeroInclusion K) = fixedInclusion K := by
  simp only [fixedIsoAffine,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    IsPullback.isoPullback_inv_fst,Scheme.IdealSheafData.comapIso_hom_fst]
  exact subschemeι_transport (fixedIdeal_eq_comap K)

/-- The actual original ground-field triangle is retained by the full
scheme isomorphism, not supplied as an assumption. -/
@[reassoc] theorem fixedIsoAffine_projection :
    (fixedIsoAffine K).hom ≫
      (𝔸(CoordinateIndex.{u}; LagrangianCommonKernelZero.zeroSpace K) ↘
        LagrangianCommonKernelZero.zeroSpace K) ≫
      LagrangianCommonKernelZero.zeroProjection K = fixedProjection K := by
  calc
    _ = ((fixedIsoAffine K).hom ≫ AffineSpace.map CoordinateIndex.{u}
        (LagrangianCommonKernelZero.zeroInclusion K)) ≫ toLG K ≫ projection K := by
      simp only [LagrangianCommonKernelZero.zeroProjection,Category.assoc,
        AffineSpace.map_over_assoc]
    _ = _ := by rw [fixedIsoAffine_map]

/-- A genuine full local model of the arbitrary-plane incidence zero,
including all nilpotents and its original structural map. -/
def lineIsoAffine (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    lineZero K w ≅ 𝔸(CoordinateIndex.{u}; LagrangianCommonKernelZero.zeroSpace K) :=
  lineFixedIso K w hw ≪≫ fixedIsoAffine K

@[reassoc] theorem lineIsoAffine_projection (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) :
    (lineIsoAffine K w hw).hom ≫
      (𝔸(CoordinateIndex.{u}; LagrangianCommonKernelZero.zeroSpace K) ↘
        LagrangianCommonKernelZero.zeroSpace K) ≫
      LagrangianCommonKernelZero.zeroProjection K = lineProjection K w := by
  rw [lineIsoAffine,Iso.trans_hom,Category.assoc,fixedIsoAffine_projection,lineFixedIso_projection]

variable [CharZero K]

instance fixedProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 4 (fixedProjection K) := by
  have hs : SmoothOfRelativeDimension (1+3)
      ((𝔸(CoordinateIndex.{u}; LagrangianCommonKernelZero.zeroSpace K) ↘
        LagrangianCommonKernelZero.zeroSpace K) ≫
        LagrangianCommonKernelZero.zeroProjection K) := inferInstance
  rw [← fixedIsoAffine_projection,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension 4)]
  exact hs

/-- Genuine local smoothness is derived from the actual full-zero
isomorphism and the original fixed-zero affine-three cover. -/
theorem lineProjection_smoothOfRelativeDimension (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) : SmoothOfRelativeDimension 4 (lineProjection K w) := by
  rw [← lineFixedIso_projection K w hw,
    MorphismProperty.cancel_left_of_respectsIso (P:=@SmoothOfRelativeDimension 4)]
  infer_instance

end M9Native.LagrangianAffinePlaneZeroSmooth
