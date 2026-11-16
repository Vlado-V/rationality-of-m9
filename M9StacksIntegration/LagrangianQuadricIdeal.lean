module

public import M9StacksIntegration.LagrangianBigCellQuadricKernel
public import M9StacksIntegration.LagrangianAdmissibleSwapCoordinate
public import M9StacksIntegration.LagrangianQuadricProjectiveCover
public import M9StacksIntegration.CommonOpenCoverIso

/-! The original primitive Plucker closed image of LG(3,6) is defined
scheme-theoretically by genuine quadrics. The actual native graph chart,
the actual eight admissible opens, and actual closed lifts construct a
global inverse to the finite quadratic zero scheme. No reduction or
field-point identification is used for the ideal comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianQuadricIdeal

open LagrangianGrassmannian LagrangianSymplecticAction
open LagrangianBigCellQuadricCoordinates (NativeRing)
open LagrangianBigCellQuadricMap LagrangianBigCellQuadricKernel
open LagrangianPolynomialPluckerEquivariance
open LagrangianTranslatedQuadricFamily
open LagrangianAdmissibleCoordinateIndices
open LagrangianPrimitiveQuadricVanishing (originalQuadricIdeal)

variable (K : Type u) [Field K] [CharZero K]

abbrev Choice := LagrangianAdmissibleMinors.Choice
abbrev chartSource := Spec (.of (NativeRing K))

def sourceChart (s : Choice) : chartSource K ⟶ space K :=
  LagrangianAdmissibleCharts.chart K s

instance sourceChart_isOpenImmersion (s : Choice) : IsOpenImmersion (sourceChart K s) := by
  dsimp only [sourceChart]
  infer_instance

omit [CharZero K] in
theorem sourceCharts_cover (x : space K) : ∃ s : Choice, x ∈ Set.range (sourceChart K s) :=
  LagrangianAdmissibleCharts.charts_cover K x

def ambientAutomorphism (s : Choice) :
    AlgebraicGeometry.Proj (polyGrading K 13) ≅ AlgebraicGeometry.Proj (polyGrading K 13) :=
  NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K (LagrangianAdmissibleCharts.swap K s))

def ambientOpenMap (s : Choice) : (aOpen K).toScheme ⟶ AlgebraicGeometry.Proj (polyGrading K 13) :=
  (aOpen K).ι ≫ (ambientAutomorphism K s).inv

instance ambientOpenMap_isOpenImmersion (s : Choice) : IsOpenImmersion (ambientOpenMap K s) := by
  dsimp only [ambientOpenMap]
  infer_instance

theorem inverse_action_polynomialPlucker (g : Matrix.symplecticGroup (Fin 3) K) :
    action K g⁻¹ ≫ polynomialPlucker K = polynomialPlucker K ≫
      (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).inv := by
  apply (cancel_mono (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).hom).mp
  calc
    (action K g⁻¹ ≫ polynomialPlucker K) ≫
        (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).hom =
      action K g⁻¹ ≫ (action K g ≫ polynomialPlucker K) := by
        rw [Category.assoc, ← action_polynomialPlucker]
    _ = polynomialPlucker K := by
      rw [← Category.assoc, action_mul, inv_mul_cancel, action_one, Category.id_comp]
    _ = (polynomialPlucker K ≫
        (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).inv) ≫
          (NativeProjectiveLinear.projectiveLinear K 13 (primitiveGL K g)).hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem sourceChart_ambient (s : Choice) : sourceChart K s ≫ polynomialPlucker K =
    graphChartMap K ≫ ambientOpenMap K s := by
  calc
    _ = (LagrangianMatrixChart.bigCell K ≫ polynomialPlucker K) ≫
        (ambientAutomorphism K s).inv := by
      change (LagrangianMatrixChart.bigCell K ≫
        action K (LagrangianAdmissibleCharts.swap K s)⁻¹) ≫ polynomialPlucker K = _
      rw [Category.assoc, inverse_action_polynomialPlucker, ← Category.assoc]
      rfl
    _ = (graphChartMap K ≫ (aOpen K).ι) ≫ (ambientAutomorphism K s).inv := by
      rw [graphChartMap_ambient]
    _ = _ := Category.assoc _ _ _

theorem graphKernel_le_comap_family (s : Choice) :
    (graphChartMap K).ker ≤ (familyIdeal K).comap (ambientOpenMap K s) := by
  rw [graphChartMap_kernel]
  have ht : (originalIdeal K).comap (ambientAutomorphism K s).hom ≤ familyIdeal K := by
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mp
    change (⨆ i, originalQuadricIdeal K i) ≤ (familyIdeal K).map (ambientAutomorphism K s).hom
    apply iSup_le
    intro i
    apply Scheme.IdealSheafData.le_map_iff_comap_le.mpr
    exact (translatedIdeal_eq_comap K (LagrangianAdmissibleCharts.swap K s) i) ▸
      (translated_swap_le_familyIdeal K s i)
  have h := Scheme.IdealSheafData.comap_mono (ambientOpenMap K s) ht
  change ((originalIdeal K).comap (ambientAutomorphism K s).hom).comap
    (ambientOpenMap K s) ≤ (familyIdeal K).comap (ambientOpenMap K s) at h
  rw [← Scheme.IdealSheafData.comap_comp] at h
  change (originalIdeal K).comap
    (((aOpen K).ι ≫ (ambientAutomorphism K s).inv) ≫ (ambientAutomorphism K s).hom) ≤ _ at h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using h

theorem comap_family_le_graphKernel (s : Choice) :
    (familyIdeal K).comap (ambientOpenMap K s) ≤ (graphChartMap K).ker := by
  have h : familyIdeal K ≤ (sourceChart K s ≫ polynomialPlucker K).ker :=
    (familyIdeal_le_kernel K).trans ((sourceChart K s).le_ker_comp (polynomialPlucker K))
  rw [sourceChart_ambient, ← Scheme.IdealSheafData.map_ker] at h
  exact Scheme.IdealSheafData.le_map_iff_comap_le.mp h

/-- Equality of full actual ideal sheaves on the same native affine
chart, derived from genuine quadratic generators and global vanishing. -/
theorem graphChartMap_kernel_family (s : Choice) :
    (graphChartMap K).ker = (familyIdeal K).comap (ambientOpenMap K s) :=
  (graphKernel_le_comap_family K s).antisymm (comap_family_le_graphKernel K s)

def closedChartLift (s : Choice) : chartSource K ⟶
    ((familyIdeal K).comap (ambientOpenMap K s)).subscheme :=
  IsClosedImmersion.lift ((familyIdeal K).comap (ambientOpenMap K s)).subschemeι
    (graphChartMap K) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, graphChartMap_kernel_family])

theorem closedChartLift_fac (s : Choice) : closedChartLift K s ≫
    ((familyIdeal K).comap (ambientOpenMap K s)).subschemeι = graphChartMap K :=
  IsClosedImmersion.lift_fac _ _ _

instance closedChartLift_isIso (s : Choice) : IsIso (closedChartLift K s) := by
  apply IsClosedImmersion.isIso_of_ker_eq (graphChartMap K)
    ((familyIdeal K).comap (ambientOpenMap K s)).subschemeι (closedChartLift K s)
    (closedChartLift_fac K s)
  rw [Scheme.IdealSheafData.ker_subschemeι, graphChartMap_kernel_family]

def targetChart (s : Choice) : chartSource K ⟶ (familyIdeal K).subscheme :=
  closedChartLift K s ≫ ((familyIdeal K).comapIso (ambientOpenMap K s)).hom ≫
    pullback.snd (ambientOpenMap K s) (familyIdeal K).subschemeι

instance targetChart_isOpenImmersion (s : Choice) : IsOpenImmersion (targetChart K s) := by
  dsimp only [targetChart]
  infer_instance

theorem targetChart_ambient (s : Choice) : targetChart K s ≫ (familyIdeal K).subschemeι =
    sourceChart K s ≫ polynomialPlucker K := by
  calc
    _ = (closedChartLift K s ≫ ((familyIdeal K).comapIso (ambientOpenMap K s)).hom) ≫
      (pullback.snd (ambientOpenMap K s) (familyIdeal K).subschemeι ≫ (familyIdeal K).subschemeι) := by
        simp only [targetChart, Category.assoc]
    _ = (closedChartLift K s ≫ ((familyIdeal K).comapIso (ambientOpenMap K s)).hom) ≫
      (pullback.fst (ambientOpenMap K s) (familyIdeal K).subschemeι ≫ ambientOpenMap K s) := by
        rw [← pullback.condition]
    _ = (closedChartLift K s ≫ ((familyIdeal K).comap (ambientOpenMap K s)).subschemeι) ≫
        ambientOpenMap K s := by simp only [Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst_assoc]
    _ = graphChartMap K ≫ ambientOpenMap K s := by rw [closedChartLift_fac]
    _ = _ := (sourceChart_ambient K s).symm

theorem automorphism_preimage_aOpen (s : Choice) :
    (ambientAutomorphism K s).hom ⁻¹ᵁ aOpen K =
      Proj.basicOpen (polyGrading K 13) (MvPolynomial.X (choiceIndex s)) := by
  change Proj.map (NativeProjectiveLinear.substitution K 13
      (primitiveGL K (LagrangianAdmissibleCharts.swap K s)).val) _ ⁻¹ᵁ
      Proj.basicOpen (polyGrading K 13) (MvPolynomial.X LagrangianQuadricChartReindex.aIndex) = _
  rw [Proj.map_preimage_basicOpen, LagrangianAdmissibleSwapCoordinate.substitution_a_swap]

/-- Actual points of the full finite quadratic zero scheme lie in one
of the constructed actual open charts; no scheme reduction is made. -/
theorem targetCharts_cover (x : (familyIdeal K).subscheme) :
    ∃ s : Choice, x ∈ Set.range (targetChart K s) := by
  obtain ⟨i, hi⟩ := LagrangianQuadricProjectiveCover.charts_cover K x
  let s := choiceForAdmissible i
  let p := (familyIdeal K).subschemeι x
  have hs : p ∈ Proj.basicOpen (polyGrading K 13) (MvPolynomial.X (choiceIndex s)) := by
    change p ∈ Proj.basicOpen (polyGrading K 13) (MvPolynomial.X (admissibleIndex i)) at hi
    simpa only [s, choiceIndex, choiceAdmissible_choiceForAdmissible] using hi
  have hp : (ambientAutomorphism K s).hom p ∈ aOpen K := by
    change p ∈ (ambientAutomorphism K s).hom ⁻¹ᵁ aOpen K
    rw [automorphism_preimage_aOpen]
    exact hs
  let y : (aOpen K).toScheme := ⟨(ambientAutomorphism K s).hom p, hp⟩
  have hy : ambientOpenMap K s y = p := by
    change (ambientAutomorphism K s).inv ((ambientAutomorphism K s).hom p) = p
    exact congrArg (fun f : AlgebraicGeometry.Proj (polyGrading K 13) ⟶
      AlgebraicGeometry.Proj (polyGrading K 13) => f p) (ambientAutomorphism K s).hom_inv_id
  have hx : x ∈ Set.range (pullback.snd (ambientOpenMap K s) (familyIdeal K).subschemeι) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, hy⟩
  obtain ⟨z, hz⟩ := hx
  let e : chartSource K ≅ pullback (ambientOpenMap K s) (familyIdeal K).subschemeι :=
    asIso (closedChartLift K s) ≪≫ (familyIdeal K).comapIso (ambientOpenMap K s)
  refine ⟨s, e.inv z, ?_⟩
  change pullback.snd (ambientOpenMap K s) (familyIdeal K).subschemeι (e.hom (e.inv z)) = x
  have he : e.hom (e.inv z) = z := congrArg
    (fun f : pullback (ambientOpenMap K s) (familyIdeal K).subschemeι ⟶
      pullback (ambientOpenMap K s) (familyIdeal K).subschemeι => f z) e.inv_hom_id
  rw [he]
  exact hz

/-- Both directions are actual scheme morphisms glued from the actual
native affine-six charts over the original polynomial P13. -/
def quadricZeroIso : space K ≅ (familyIdeal K).subscheme := by
  let := LagrangianPrimitiveQuadricVanishing.polynomialPlucker_isClosedImmersion K
  exact CommonOpenCoverIso.iso (fun _ : Choice => chartSource K)
    (sourceChart K) (targetChart K) (sourceCharts_cover K) (targetCharts_cover K)
    (polynomialPlucker K) (familyIdeal K).subschemeι (fun s => (targetChart_ambient K s).symm)

theorem quadricZeroIso_ambient : (quadricZeroIso K).hom ≫ (familyIdeal K).subschemeι =
    polynomialPlucker K := by
  let := LagrangianPrimitiveQuadricVanishing.polynomialPlucker_isClosedImmersion K
  exact CommonOpenCoverIso.iso_hom_ambient (fun _ : Choice => chartSource K)
    (sourceChart K) (targetChart K) (sourceCharts_cover K) (targetCharts_cover K)
    (polynomialPlucker K) (familyIdeal K).subschemeι (fun s => (targetChart_ambient K s).symm)

/-- The original LG primitive Plucker closed-image ideal is generated
by the genuine finite family of original-basis homogeneous quadrics. -/
theorem polynomialPlucker_ker_eq_familyIdeal : (polynomialPlucker K).ker = familyIdeal K := by
  calc
    _ = ((quadricZeroIso K).hom ≫ (familyIdeal K).subschemeι).ker :=
      congrArg (fun f : space K ⟶ AlgebraicGeometry.Proj (polyGrading K 13) => f.ker)
        (quadricZeroIso_ambient K).symm
    _ = (familyIdeal K).subschemeι.ker := Scheme.Hom.ker_comp_of_isIso _ _
    _ = familyIdeal K := Scheme.IdealSheafData.ker_subschemeι _

theorem polynomialPlucker_ker_eq_iSup_quadrics :
    (LagrangianPlucker.primitivePlucker K ≫
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K 13).iso.hom).ker =
      ⨆ i : FamilyIndex.{u}, HomogeneousEquationIdeal.equationIdeal K 13 2 (familyForm K) i :=
  polynomialPlucker_ker_eq_familyIdeal K

end M9Native.LagrangianQuadricIdeal
