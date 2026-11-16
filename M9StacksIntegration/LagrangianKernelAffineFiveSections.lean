module

public import M9StacksIntegration.LagrangianKernelAffineFiveFrames

/-!
# The original five-section projective map on the actual affine charts

The genuine source naturality and the actual determinant frame identify
the original zero-scheme projective map with its literal polynomial tuple.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite Matrix
universe u
namespace M9Native.LagrangianKernelAffineFiveSections
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianMatrixChart
open LagrangianAdmissibleCharts LagrangianCommonKernelChartAlgebra LagrangianKernelTailMatrix
open LagrangianKernelFivePullback LagrangianKernelFiveSections
open LagrangianCommonKernelZero LagrangianKernelChartTriangle LagrangianKernelProjectiveComparison
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  LagrangianAdmissibleCharts.chart LagrangianKernelFivePullback.pulledFiveSections
variable (K : Type u) [Field K] [CharZero K]

def zeroChartMap (c : Fin 4) : Spec (.of (ThreeRing K)) ⟶ zeroSpace K :=
  LagrangianCommonKernelChartIso.affineThreeMap K (choice c) (choice_first c)

theorem zeroChartMap_inclusion (c : Fin 4) :
    zeroChartMap K c ≫ zeroInclusion K = LagrangianCommonKernelChartIso.affineLGMap K (choice c) :=
  LagrangianCommonKernelChartIso.affineThreeMap_inclusion K (choice c) (choice_first c)

theorem zeroChartMap_projection (c : Fin 4) :
    zeroChartMap K c ≫ zeroProjection K =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* ThreeRing K)) :=
  LagrangianCommonKernelChartIso.affineThreeMap_projection K (choice c) (choice_first c)

/-- Actual source naturality and a genuine line frame determine the
native five-section map on an arbitrary original test scheme. -/
theorem zeroProjectiveMap_comp_framed {T : Scheme.{u}} (t : T ⟶ zeroSpace K)
    (f : T ⟶ Spec (.of K)) (l : T ⟶ space K)
    (hf : t ≫ zeroProjection K = f) (hi : t ≫ zeroInclusion K = l)
    (e : (Scheme.Modules.pullback l).obj (determinantLine K) ≅
      ProjectiveSectionFunctions.UnitLine T)
    (r : Fin 5 → Γ(T, ⊤)) (hr : Ideal.span (Set.range r) = ⊤)
    (he : ∀ a, (show Γ(T, ⊤) from e.hom.app ⊤ (pulledFiveSections K l a)) = r a) :
    t ≫ zeroProjectiveMap K =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver r hr f := by
  subst f
  subst l
  let hq := quotient_first_section_zero_comp K t
  have hl : (t ≫ zeroInclusion K) ≫ projection K = t ≫ zeroProjection K := by
    simp only [zeroProjection, Category.assoc]
  let hs := pulledFiveSections_generatesStalks K (t ≫ zeroProjection K)
    (t ≫ zeroInclusion K) hl hq
  have hn : t ≫ zeroProjectiveMap K =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (pulledFiveSections K (t ≫ zeroInclusion K)) hs (t ≫ zeroProjection K) :=
    (projectiveMap_comp K (zeroProjection K) (zeroInclusion K) rfl
      (quotient_first_section_zero K) t hq).trans
      (projectiveMap_eq_pulled K (t ≫ zeroProjection K) (t ≫ zeroInclusion K) hl hq)
  have heq : (fun a => (show Γ(T, ⊤) from e.hom.app ⊤
      (pulledFiveSections K (t ≫ zeroInclusion K) a))) = r := funext he
  have hspan : Ideal.span (Set.range (fun a => (show Γ(T, ⊤) from
      e.hom.app ⊤ (pulledFiveSections K (t ≫ zeroInclusion K) a)))) = ⊤ := by
    rw [heq]
    exact hr
  exact hn.trans (by
    simpa only [heq] using toProjectiveSpaceOver_framed
      (pulledFiveSections K (t ≫ zeroInclusion K)) hs e (t ≫ zeroProjection K) hspan)

/-- The original native P4 map, with the actual base map and literal five coordinates. -/
theorem zeroChartMap_projectiveMap (c : Fin 4) :
    zeroChartMap K c ≫ zeroProjectiveMap K =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver (normalizedFunctions K c)
        (normalizedFunctions_span K c)
        (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* ThreeRing K))) :=
  zeroProjectiveMap_comp_framed K (zeroChartMap K c)
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* ThreeRing K)))
    (LagrangianCommonKernelChartIso.affineLGMap K (choice c))
    (zeroChartMap_projection K c) (zeroChartMap_inclusion K c)
    (LagrangianCommonKernelChartIso.determinantFrame K (choice c))
    (normalizedFunctions K c) (normalizedFunctions_span K c)
    (determinantFrame_five_choice K c)

end M9Native.LagrangianKernelAffineFiveSections
