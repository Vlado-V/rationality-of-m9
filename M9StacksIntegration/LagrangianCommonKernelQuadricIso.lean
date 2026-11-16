module

public import M9StacksIntegration.LagrangianKernelLocalQuadricMap
public import M9StacksIntegration.CommonOpenCoverIso

/-!
# The actual original common-kernel zero scheme is the literal split quadric

The original section-zero scheme and the actual degree-two hypersurface
are glued from their genuine affine charts. Their actual ambient maps
agree by the original five minors. The resulting scheme isomorphism
retains the original base field and original primitive Plucker immersion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.ProjectiveSpaceChartRatio
open Stacks.AlgebraicGeometry.ProjBaseChange

universe u

namespace M9Native.LagrangianCommonKernelQuadricIso

open LagrangianKernelTailMatrix LagrangianKernelAffineFiveSections LagrangianKernelLocalQuadricMap
open LagrangianCommonKernelZero LagrangianKernelFiveSections LagrangianKernelChartTriangle
open LagrangianKernelLinearEmbedding SplitQuadricLinearSection

/-- The actual four choices exhaust exactly the surviving original charts. -/
theorem choice_surjective (s : LagrangianAdmissibleMinors.Choice) (hs : s 0 = true) :
    ∃ c : Fin 4, choice c = s := by
  cases h1 : s 1 <;> cases h2 : s 2
  · refine ⟨0, ?_⟩
    funext i
    fin_cases i <;> simp [choice, hs, h1, h2]
  · refine ⟨2, ?_⟩
    funext i
    fin_cases i <;> simp [choice, hs, h1, h2]
  · refine ⟨1, ?_⟩
    funext i
    fin_cases i <;> simp [choice, hs, h1, h2]
  · refine ⟨3, ?_⟩
    funext i
    fin_cases i <;> simp [choice, hs, h1, h2]

variable (K : Type u) [Field K] [CharZero K]

theorem zeroChartMap_isOpenImmersion (c : Fin 4) : IsOpenImmersion (zeroChartMap K c) := by
  dsimp [zeroChartMap]
  infer_instance

theorem zeroChartMaps_cover (x : zeroSpace K) : ∃ c : Fin 4, x ∈ Set.range (zeroChartMap K c) := by
  obtain ⟨s,hs,y,hy⟩ := LagrangianCommonKernelChartIso.affineThreeMaps_cover K x
  obtain ⟨c,hc⟩ := choice_surjective s hs
  subst s
  exact ⟨c,y,hy⟩

/-- The genuine original P4 map in the native polynomial projective model. -/
def zeroPolynomialMap : zeroSpace K ⟶ ambient K :=
  zeroProjectiveMap K ≫ (polynomialComparison K 4).iso.hom

theorem zeroPolynomialMap_isClosedImmersion : IsClosedImmersion (zeroPolynomialMap K) := by
  letI := zeroProjectiveMap_isClosedImmersion K
  dsimp [zeroPolynomialMap]
  infer_instance

/-- The actual scheme isomorphism, without any model/comparison premise. -/
def modelIso : zeroSpace K ≅ quadric K := by
  letI (c : Fin 4) := zeroChartMap_isOpenImmersion K c
  letI (c : Fin 4) := SplitQuadricStandardCharts.affineThreeMap_isOpenImmersion K c
  letI := zeroPolynomialMap_isClosedImmersion K
  exact CommonOpenCoverIso.iso (fun _ : Fin 4 => Spec (.of (ThreeRing K)))
    (zeroChartMap K) (SplitQuadricStandardCharts.affineThreeMap K)
    (zeroChartMaps_cover K) (SplitQuadricStandardCharts.affineThreeMaps_cover K)
    (zeroPolynomialMap K) (quadricInclusion K)
    (fun c => by simpa only [zeroPolynomialMap, Category.assoc] using local_ambient_equal K c)

/-- The isomorphism retains the exact original projective coordinate morphism. -/
theorem modelIso_hom_ambient : (modelIso K).hom ≫ quadricInclusion K = zeroPolynomialMap K := by
  letI (c : Fin 4) := zeroChartMap_isOpenImmersion K c
  letI (c : Fin 4) := SplitQuadricStandardCharts.affineThreeMap_isOpenImmersion K c
  letI := zeroPolynomialMap_isClosedImmersion K
  exact CommonOpenCoverIso.iso_hom_ambient (fun _ : Fin 4 => Spec (.of (ThreeRing K)))
    (zeroChartMap K) (SplitQuadricStandardCharts.affineThreeMap K)
    (zeroChartMaps_cover K) (SplitQuadricStandardCharts.affineThreeMaps_cover K)
    (zeroPolynomialMap K) (quadricInclusion K)
    (fun c => by simpa only [zeroPolynomialMap, Category.assoc] using local_ambient_equal K c)

/-- The actual original coefficient field and actual structure morphism are preserved. -/
theorem modelIso_hom_projection : (modelIso K).hom ≫ quadricProjection K = zeroProjection K := by
  change (modelIso K).hom ≫ (quadricInclusion K ≫
    Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K 4) = _
  rw [← Category.assoc, modelIso_hom_ambient, zeroPolynomialMap, Category.assoc,
    polynomialComparison_iso_hom_comp_projToSpecCoeff]
  exact zeroProjectiveMap_fst K

/-- The original primitive P13 immersion is retained through the genuine quadric model. -/
theorem modelIso_hom_primitive :
    (modelIso K).hom ≫ quadricInclusion K ≫ (polynomialComparison K 4).iso.inv ≫
      fixedLinearEmbedding K = zeroInclusion K ≫ LagrangianPlucker.primitivePlucker K := by
  rw [← Category.assoc, ← Category.assoc, modelIso_hom_ambient, zeroPolynomialMap]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using zeroProjectiveMap_triangle K

end M9Native.LagrangianCommonKernelQuadricIso
