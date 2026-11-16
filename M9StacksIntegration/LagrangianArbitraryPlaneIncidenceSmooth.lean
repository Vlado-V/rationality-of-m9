module

public import M9StacksIntegration.LagrangianArbitraryPlaneChartFrame
public import M9StacksIntegration.LagrangianAffinePlaneZeroSmooth
public import M9StacksIntegration.FreeTwoProjectiveChartCover
public import M9StacksIntegration.LagrangianIntegral
public import M9StacksIntegration.LagrangianPluckerClosed
public import M9StacksIntegration.SmoothZeroRegularity
public import M9StacksIntegration.SmoothRelativeChowDimension
public import M9StacksIntegration.CoverIsoRefinement

/-! Actual global smoothness and length-three regularity of the
original incidence for every independent two-plane, including isotropic
planes. Both true P1 charts identify the full original section-zero
scheme with the proved smooth affine-line fixed-zero model. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option Elab.async false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix Module TopologicalSpace
universe u

namespace M9Native.LagrangianArbitraryPlaneIncidenceSmooth

open LagrangianGrassmannian LagrangianPluckerQuotient
open LagrangianArbitraryPlaneChartFrame
variable (K : Type u) [Field K]

abbrev ambientProjection : LagrangianArbitraryPlaneIncidence.ambient K ⟶ Spec (.of K) :=
  LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K
abbrev toBase (w : Fin 2 → LagrangianRing.V K) :
    LagrangianArbitraryPlaneIncidence.incidence K w ⟶ Spec (.of K) :=
  LagrangianArbitraryPlaneIncidence.incidenceToLG K w ≫ projection K

local instance equationBundle_finite :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (LagrangianArbitraryPlaneIncidence.equationBundle K) :=
  (LagrangianArbitraryPlaneIncidence.equationBundle_rank K).isFiniteLocallyFree

/-- Both native constructions use the same original dual-evaluation ideal. -/
theorem zeroSchemeOfSection_eq_incidenceIdeal (w : Fin 2 → LagrangianRing.V K) :
    Stacks.Chow.zeroSchemeOfSection (LagrangianArbitraryPlaneIncidence.ambient K)
      (LagrangianArbitraryPlaneIncidence.equationBundle K)
      (LagrangianArbitraryPlaneIncidence.equationSection K w) =
        LagrangianArbitraryPlaneIncidence.incidenceIdeal K w := rfl

/-- The literal original tensor-zero ideal on each actual P1 chart
is the literal original normalized line-zero ideal. -/
theorem lineIdeal_eq_comap (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    LagrangianAffinePlaneZeroSmooth.lineIdeal K (orderedFrame K w i) =
      (LagrangianArbitraryPlaneIncidence.incidenceIdeal K w).comap (chart K i) :=
  NativeVectorSectionZeroTransport.ideal_eq_comap_of_iso
    (LagrangianArbitraryPlaneIncidence.equationBundle K)
    (LagrangianAffinePlaneSection.quotientBundle K) 3 (chart K i) (tensorFrame K i)
    (LagrangianArbitraryPlaneIncidence.equationSection K w)
    (LagrangianAffinePlaneSection.lineSection K (orderedFrame K w i))
    (tensorFrame_equationSection K i w)

abbrev chartZero (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) : Scheme.{u} :=
  pullback (chart K i) (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)

/-- Actual full schemes, not reductions or field points, are identified. -/
def chartZeroIsoLine (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    chartZero K w i ≅ LagrangianAffinePlaneZeroSmooth.lineZero K (orderedFrame K w i) :=
  ((LagrangianArbitraryPlaneIncidence.incidenceIdeal K w).comapIso (chart K i)).symm ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme (lineIdeal_eq_comap K w i).symm)

private theorem subschemeι_transport {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme h)).hom ≫ J.subschemeι = I.subschemeι := by
  subst J
  simp

@[reassoc] theorem chartZeroIsoLine_hom_inclusion
    (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    (chartZeroIsoLine K w i).hom ≫ LagrangianAffinePlaneZeroSmooth.lineInclusion K (orderedFrame K w i) =
      pullback.fst (chart K i) (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w) := by
  rw [chartZeroIsoLine,Iso.trans_hom,Category.assoc,
    subschemeι_transport (lineIdeal_eq_comap K w i).symm,Iso.symm_hom]
  exact Scheme.IdealSheafData.comapIso_inv_subschemeι
    (LagrangianArbitraryPlaneIncidence.incidenceIdeal K w) (chart K i)

@[reassoc] theorem chartZeroIsoLine_inv_inclusion
    (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    (chartZeroIsoLine K w i).inv ≫
      pullback.fst (chart K i) (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w) =
        LagrangianAffinePlaneZeroSmooth.lineInclusion K (orderedFrame K w i) := by
  rw [← chartZeroIsoLine_hom_inclusion,Iso.inv_hom_id_assoc]

def lineChart (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    LagrangianAffinePlaneZeroSmooth.lineZero K (orderedFrame K w i) ⟶
      LagrangianArbitraryPlaneIncidence.incidence K w :=
  (chartZeroIsoLine K w i).inv ≫
    pullback.snd (chart K i) (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)

instance lineChart_isOpenImmersion (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    IsOpenImmersion (lineChart K w i) := by
  dsimp [lineChart]
  infer_instance

@[reassoc] theorem lineChart_inclusion (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    lineChart K w i ≫ LagrangianArbitraryPlaneIncidence.incidenceInclusion K w =
      LagrangianAffinePlaneZeroSmooth.lineInclusion K (orderedFrame K w i) ≫ chart K i := by
  rw [lineChart,Category.assoc,
    ← pullback.condition (f:=chart K i) (g:=LagrangianArbitraryPlaneIncidence.incidenceInclusion K w),
    ← Category.assoc,chartZeroIsoLine_inv_inclusion]

@[reassoc] theorem lineChart_projection (w : Fin 2 → LagrangianRing.V K) (i : Fin 2) :
    lineChart K w i ≫ toBase K w =
      LagrangianAffinePlaneZeroSmooth.lineProjection K (orderedFrame K w i) := by
  calc
    _ = (lineChart K w i ≫ LagrangianArbitraryPlaneIncidence.incidenceInclusion K w) ≫
        LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K := by
      simp only [toBase,LagrangianArbitraryPlaneIncidence.incidenceToLG,Category.assoc]
    _ = (LagrangianAffinePlaneZeroSmooth.lineInclusion K (orderedFrame K w i) ≫ chart K i) ≫
        LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K := by rw [lineChart_inclusion]
    _ = _ := by rw [Category.assoc,chart_projection_assoc]

private def incidenceChartCover (w : Fin 2 → LagrangianRing.V K) :
    (LagrangianArbitraryPlaneIncidence.incidence K w).OpenCover :=
  (FreeTwoProjectiveChartCover.chartCover (space K)).pullback₁
    (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)

private def incidenceChartIndex (w : Fin 2 → LagrangianRing.V K)
    (i : (incidenceChartCover K w).I₀) : Fin 2 := i

private theorem incidenceChart_arrow (w : Fin 2 → LagrangianRing.V K)
    (i : (incidenceChartCover K w).I₀) :
    (FreeTwoProjectiveChartCover.chartCover (space K)).f i =
      chart K (incidenceChartIndex K w i) := rfl

private def incidenceChartIsoLine (w : Fin 2 → LagrangianRing.V K)
    (i : (incidenceChartCover K w).I₀) :
    (incidenceChartCover K w).X i ≅
      LagrangianAffinePlaneZeroSmooth.lineZero K (orderedFrame K w (incidenceChartIndex K w i)) :=
  pullback.congrHom rfl (incidenceChart_arrow K w i) ≪≫
    pullbackSymmetry (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w)
      (chart K (incidenceChartIndex K w i)) ≪≫
    chartZeroIsoLine K w (incidenceChartIndex K w i)

private theorem incidenceChartIsoLine_triangle (w : Fin 2 → LagrangianRing.V K)
    (i : (incidenceChartCover K w).I₀) :
    (incidenceChartIsoLine K w i).hom ≫ lineChart K w (incidenceChartIndex K w i) =
      (incidenceChartCover K w).f i := by
  dsimp only [incidenceChartIsoLine,Iso.trans_hom,lineChart]
  rw [Category.assoc,Category.assoc,Iso.hom_inv_id_assoc,
    pullbackSymmetry_hom_comp_snd]
  simp only [pullback.congrHom_hom,pullback.map_fst,Category.comp_id]
  rfl

/-- The true two-chart cover of P1 pulls back to the original full
incidence scheme; no pointwise normal-form coverage is supplied. -/
theorem lineCharts_cover (w : Fin 2 → LagrangianRing.V K)
    (x : LagrangianArbitraryPlaneIncidence.incidence K w) :
    ∃ i : Fin 2, x ∈ Set.range (lineChart K w i) :=
  CoverIsoRefinement.covers (incidenceChartCover K w)
    (fun i => LagrangianAffinePlaneZeroSmooth.lineZero K (orderedFrame K w i))
    (lineChart K w) (incidenceChartIndex K w) (incidenceChartIsoLine K w)
    (incidenceChartIsoLine_triangle K w) x

def lineCover (w : Fin 2 → LagrangianRing.V K) :
    (LagrangianArbitraryPlaneIncidence.incidence K w).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin 2)
    (fun i => LagrangianAffinePlaneZeroSmooth.lineZero K (orderedFrame K w i))
    (lineChart K w) (fun x => lineCharts_cover K w x)

/-- The actual P1-bundle ambient is a genuine smooth sevenfold. -/
instance ambientProjection_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 7 (ambientProjection K) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 7 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P:=@SmoothOfRelativeDimension 7)
    (FreeTwoProjectiveChartCover.chartCover (space K)) fun i => ?_
  change SmoothOfRelativeDimension 7
    (FreeTwoProjectiveCharts.chart (space K) i ≫ LagrangianArbitraryPlaneIncidence.toLG K ≫ projection K)
  rw [FreeTwoProjectiveCharts.chart_projection_assoc]
  have hs : SmoothOfRelativeDimension (1+6)
      ((𝔸(ULift.{u} (Fin 1);space K) ↘ space K) ≫ projection K) := inferInstance
  exact hs

instance ambientProjection_smooth : Smooth (ambientProjection K) :=
  SmoothOfRelativeDimension.smooth 7 (ambientProjection K)

instance toBase_locallyOfFiniteType (w : Fin 2 → LagrangianRing.V K) :
    LocallyOfFiniteType (toBase K w) := by
  have h : LocallyOfFiniteType
      (LagrangianArbitraryPlaneIncidence.incidenceInclusion K w ≫ ambientProjection K) := inferInstance
  simpa only [ambientProjection,toBase,LagrangianArbitraryPlaneIncidence.incidenceToLG,Category.assoc]
    using h

theorem ambient_delta_dimension_le :
    Stacks.Chow.schemeDeltaDimension (Stacks.Chow.fieldChowSituation K) (ambientProjection K) ≤
      ((7 : ℤ) : EInt) := by
  simpa only [Nat.cast_ofNat] using
    SmoothRelativeChowDimension.schemeDeltaDimension_le_of_smooth_relative_dimension K
      (ambientProjection K) 7

variable [CharZero K]

instance toBase_isProper (w : Fin 2 → LagrangianRing.V K) : IsProper (toBase K w) := by
  let : IsProper (projection K) := isProper_of_isProjectiveMorphism _
    (LagrangianPluckerClosed.isProjectiveMorphism_projection K)
  dsimp [toBase]
  infer_instance

/-- Every original independent two-plane, including isotropic planes,
has an actual full incidence zero scheme smooth of dimension four. -/
theorem toBase_smoothOfRelativeDimension (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) : SmoothOfRelativeDimension 4 (toBase K w) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 4 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P:=@SmoothOfRelativeDimension 4)
    (lineCover K w) fun i => ?_
  change SmoothOfRelativeDimension 4 (lineChart K w i ≫ toBase K w)
  rw [lineChart_projection]
  exact LagrangianAffinePlaneZeroSmooth.lineProjection_smoothOfRelativeDimension K
    (orderedFrame K w i) (orderedFrame_independent K w hw i)

/-- The genuine native field-Chow dimension bound follows from actual
full-zero smoothness, without an integrality or class premise. -/
theorem incidence_delta_dimension_le (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) :
    Stacks.Chow.schemeDeltaDimension (Stacks.Chow.fieldChowSituation K) (toBase K w) ≤
      ((4 : ℤ) : EInt) := by
  let : SmoothOfRelativeDimension 4 (toBase K w) := toBase_smoothOfRelativeDimension K w hw
  simpa only [Nat.cast_ofNat] using
    SmoothRelativeChowDimension.schemeDeltaDimension_le_of_smooth_relative_dimension K
      (toBase K w) 4

/-- A literal point of an original fixed-zero affine-three chart,
transported through the constructed full line-zero isomorphism, supplies
an actual point of the original incidence. -/
theorem incidence_nonempty (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    Nonempty (LagrangianArbitraryPlaneIncidence.incidence K w) := by
  let y : Spec (.of (MvPolynomial (Fin 3) K)) :=
    (Spec.map (CommRingCat.ofHom (MvPolynomial.eval (fun _ : Fin 3 => (0 : K)))))
      (IsLocalRing.closedPoint K)
  let z : LagrangianCommonKernelZero.zeroSpace K :=
    LagrangianCommonKernelChartIso.affineThreeMap K (fun _ => true) rfl y
  let a : 𝔸(ULift.{u} (Fin 1);LagrangianCommonKernelZero.zeroSpace K) :=
    AffineSpace.homOfVector (𝟙 (LagrangianCommonKernelZero.zeroSpace K)) (fun _ => 0) z
  exact ⟨lineChart K w 0
    ((LagrangianAffinePlaneZeroSmooth.lineIsoAffine K (orderedFrame K w 0)
      (orderedFrame_independent K w hw 0)).inv a)⟩

/-- Pure dimension follows from the actual constant smooth relative
dimension and the native local-dimension criterion. -/
theorem incidence_equidimensional (w : Fin 2 → LagrangianRing.V K)
    (hw : LinearIndependent K w) :
    TopologicalSpace.Equidimensional (LagrangianArbitraryPlaneIncidence.incidence K w) := by
  let : SmoothOfRelativeDimension 4 (toBase K w) := toBase_smoothOfRelativeDimension K w hw
  let : Smooth (toBase K w) := SmoothOfRelativeDimension.smooth 4 (toBase K w)
  exact equidimensional_of_topologicalKrullDimAt_eq K
    (LagrangianArbitraryPlaneIncidence.incidence K w) (toBase K w)
    (fun x => FiniteZeroRegularity.localDimension_of_smooth_relative_dimension K (toBase K w) 4 x)

/-- The actual original full incidence has topological dimension four;
nonemptiness is constructed above, not assumed. -/
theorem incidence_dimension (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    topologicalKrullDim (LagrangianArbitraryPlaneIncidence.incidence K w) = (4 : WithBot ℕ∞) := by
  let : SmoothOfRelativeDimension 4 (toBase K w) := toBase_smoothOfRelativeDimension K w hw
  let : Nonempty (LagrangianArbitraryPlaneIncidence.incidence K w) := incidence_nonempty K w hw
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  simp_rw [← topologicalKrullDimAt_eq_localKrullDim,
    FiniteZeroRegularity.localDimension_of_smooth_relative_dimension K (toBase K w) 4]
  simp

/-- Literal length-three stalk regularity for the actual original
Q-first rank-three incidence section, derived from the proved smooth
ambient and full zero scheme. -/
theorem regularSequence (w : Fin 2 → LagrangianRing.V K) (hw : LinearIndependent K w) :
    Stacks.Chow.IsRegularZeroSchemeSequence (Stacks.Chow.fieldChowSituation K)
      (ambientProjection K) (LagrangianArbitraryPlaneIncidence.equationBundle K)
      (LagrangianArbitraryPlaneIncidence.equationSection K w) 3 4 := by
  let : SmoothOfRelativeDimension 4
      ((Stacks.Chow.zeroSchemeOfSection (LagrangianArbitraryPlaneIncidence.ambient K)
        (LagrangianArbitraryPlaneIncidence.equationBundle K)
        (LagrangianArbitraryPlaneIncidence.equationSection K w)).subschemeι ≫ ambientProjection K) := by
    rw [zeroSchemeOfSection_eq_incidenceIdeal]
    simpa only [ambientProjection,toBase,LagrangianArbitraryPlaneIncidence.incidenceToLG,Category.assoc]
      using toBase_smoothOfRelativeDimension K w hw
  exact SmoothZeroRegularity.rank_three_regular_of_smooth_zero K (ambientProjection K)
    (LagrangianArbitraryPlaneIncidence.equationBundle K)
    (LagrangianArbitraryPlaneIncidence.equationSection K w)

end M9Native.LagrangianArbitraryPlaneIncidenceSmooth
