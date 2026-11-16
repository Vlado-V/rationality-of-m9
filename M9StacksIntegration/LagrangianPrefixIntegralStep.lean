module

public import M9StacksIntegration.LagrangianTailSupport
public import M9StacksIntegration.LagrangianPrefixRegularPoint
public import M9StacksIntegration.ProjectiveCurveComponentIntegral
public import M9StacksIntegration.IntegralLineCutSerreDimension

/-!
# The actual geometric integral-prefixCut successor step

The previous integral prefixCut, its previously computed Serre/dimension data,
and the actual nonzero next restricted section are the induction inputs.
The next actual zero scheme is Cartier; native theorems derive every
component dimension and the next Serre condition. The actual tail-row
intersection and a regular point derived from the smooth integral final
curve then prove the next actual prefixCut integral.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace M9Native.LagrangianPrefixIntegralStep
open LagrangianGrassmannian LagrangianPluckerQuotient IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K]

local instance determinantLine_invertible :
    SheafOfModules.IsInvertible (space K).sheaf.obj (space K).ringCatSheaf.property (determinantLine K) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (LagrangianPluckerQuotient.determinantLine_invertible K)

local instance space_locallyNoetherian : IsLocallyNoetherian (space K) :=
  LocallyOfFiniteType.isLocallyNoetherian (projection K)

abbrev sections (M : Matrix (Fin 5) (Fin 14) K) := LagrangianTailSupport.sectionList K M

abbrev prefixCut (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) : Over (space K) :=
  simultaneousCut (determinantLine K) ((sections K M).take i)

local instance prefix_locallyNoetherian (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) :
    IsLocallyNoetherian (prefixCut K M i).left :=
  LocallyOfFiniteType.isLocallyNoetherian (prefixCut K M i).hom

theorem prefix_succ_eq (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i < 5) :
    prefixCut K M (i + 1) = cut (determinantLine K) (prefixCut K M i)
      (LagrangianHyperplaneCoordinates.determinantSection K (M ⟨i, hi⟩)) := by
  have hlen : (sections K M).length = 5 := by simp [sections, LagrangianTailSupport.sectionList]
  simp only [prefixCut, simultaneousCut]
  rw [List.take_succ_eq_append_getElem (by omega),
    IntegralLineCutSerreDimension.iteratedCut_append_singleton]
  congr 1
  simp only [sections, LagrangianTailSupport.sectionList, List.getElem_ofFn]

theorem integral_successor (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin) (i : ℕ) (hi : i < 4)
    [IsIntegral (prefixCut K M i).left]
    (hS : HasPropertySk (prefixCut K M i).left (6 - i))
    (hD : topologicalKrullDim (prefixCut K M i).left = ((6 - i : ℕ) : WithBot ℕ∞))
    (hNext : pullbackGlobalSections (prefixCut K M i).hom (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K (M ⟨i, by omega⟩)) ≠ 0)
    [IsIntegral (simultaneousCut (determinantLine K) (sections K M)).left]
    [SmoothOfRelativeDimension 1
      ((simultaneousCut (determinantLine K) (sections K M)).hom ≫ projection K)] :
    IsIntegral (prefixCut K M (i + 1)).left ∧
      HasPropertySk (prefixCut K M (i + 1)).left (5 - i) ∧
      topologicalKrullDim (prefixCut K M (i + 1)).left = ((5 - i : ℕ) : WithBot ℕ∞) := by
  let L := determinantLine K
  let ss := sections K M
  let A := prefixCut K M i
  let s := LagrangianHyperplaneCoordinates.determinantSection K (M ⟨i, by omega⟩)
  let B := cut L A s
  let I := cutIdeal L A s
  let : IsClosedImmersion B.hom := cut_closed L A s
  let : IsLocallyNoetherian B.left := LocallyOfFiniteType.isLocallyNoetherian B.hom
  have hB : B = prefixCut K M (i + 1) := (prefix_succ_eq K M i (by omega)).symm
  let eOver : B ≅ prefixCut K M (i + 1) := eqToIso hB
  let e : B.left ≅ (prefixCut K M (i + 1)).left :=
    (Over.forget (space K)).mapIso eOver
  have heh : e.hom ≫ (prefixCut K M (i + 1)).hom = B.hom := eOver.hom.w
  have hei : e.inv ≫ B.hom = (prefixCut K M (i + 1)).hom := eOver.inv.w
  let C := simultaneousCut L ss
  let c : C.left ⟶ B.left := LineSectionPrefixes.prefixHom L ss (i + 1) ≫ e.inv
  let : IsClosedImmersion (LineSectionPrefixes.prefixHom L ss (i + 1)) :=
    LineSectionPrefixes.prefixHom_closed L ss (i + 1)
  let : IsClosedImmersion c := by dsimp only [c]; infer_instance
  have hlen : ss.length = 5 := by simp [ss, LagrangianTailSupport.sectionList]
  obtain ⟨z, _, hreg⟩ := LagrangianPrefixRegularPoint.exists_common_regular_point K ss hlen
  have hne : Nonempty I.subscheme := ⟨c z⟩
  have hComp := IntegralLineCutSerreDimension.zeroScheme_components_dimension K
    (A.hom ≫ projection K) ((Scheme.Modules.pullback A.hom).obj L)
    (pullbackGlobalSections A.hom L s) hNext (6 - i) hD hne
  have hSY := IntegralLineCutSerreDimension.zeroScheme_serre
    ((Scheme.Modules.pullback A.hom).obj L) (pullbackGlobalSections A.hom L s)
    hNext (6 - i) (by omega) hS
  have hS1 : HasPropertySk B.left 1 := by
    intro y
    have hle : min (1 : WithBot ℕ∞) (ringKrullDim (B.left.presheaf.stalk y)) ≤
        min (((6 - i) - 1 : ℕ) : WithBot ℕ∞) (ringKrullDim (B.left.presheaf.stalk y)) :=
      min_le_min (by exact_mod_cast (show 1 ≤ (6 - i) - 1 by omega)) le_rfl
    exact hle.trans (hSY y)
  let p := LineSectionPrefixes.prefixHom L ss (i + 1) z
  let : IsRegularLocalRing ((prefixCut K M (i + 1)).left.presheaf.stalk p) := hreg (i + 1) (by omega)
  have hR : IsRegularLocalRing (B.left.presheaf.stalk (c z)) :=
    IsRegularLocalRing.of_ringEquiv (asIso (e.inv.stalkMap p)).commRingCatIsoToRingEquiv.symm
  let j := B.hom ≫ LagrangianPlucker.primitivePlucker K
  have hFull : c ≫ j = C.hom ≫ LagrangianPlucker.primitivePlucker K := by
    dsimp only [c, j]
    calc
      _ = LineSectionPrefixes.prefixHom L ss (i + 1) ≫ (e.inv ≫ B.hom) ≫
          LagrangianPlucker.primitivePlucker K := by simp only [Category.assoc]
      _ = LineSectionPrefixes.prefixHom L ss (i + 1) ≫ (prefixCut K M (i + 1)).hom ≫
          LagrangianPlucker.primitivePlucker K := by rw [hei]
      _ = C.hom ≫ LagrangianPlucker.primitivePlucker K := by
        rw [LineSectionPrefixes.prefixHom_over_assoc]
  have hRange : Set.range j =
      Set.range ((prefixCut K M (i + 1)).hom ≫ LagrangianPlucker.primitivePlucker K) := by
    dsimp only [j]
    rw [← heh, Category.assoc]
    exact range_eq_range_of_surjective _ _ e.hom rfl
  have hInter : Set.range j ∩ LagrangianTailLinearSpace.locus K M (i + 1) (by omega) ⊆
      Set.range (c ≫ j) := by
    rw [hRange, hFull]
    exact LagrangianTailSupport.image_inter_subset_full K M (i + 1) (by omega)
  let fC := C.hom ≫ projection K
  have hCdim : topologicalKrullDim C.left = (1 : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension fC 1
  have hCY : ∀ W ∈ irreducibleComponents B.left,
      topologicalKrullDim W = ((6 - (i + 1) : ℕ) : WithBot ℕ∞) := by
    intro W hW
    simpa only [show (6 - i) - 1 = 6 - (i + 1) by omega] using hComp.1 W hW
  have hInt : IsIntegral B.left :=
    ProjectiveCurveComponentIntegral.integral_of_component_dimensions_and_tail_intersection
      K (i + 1) (by omega) B.left hS1 j C.left c hCdim z hR
      (LagrangianTailLinearSpace.locus K M (i + 1) (by omega))
      (LagrangianTailLinearSpace.locus_isClosed K M (i + 1) (by omega))
      (LagrangianTailLinearSpace.locus_nonempty K M hM (i + 1) (by omega))
      (LagrangianTailLinearSpace.locus_dimension K M hM (i + 1) (by omega)) hCY hInter
  let : IsIntegral B.left := hInt
  have hSkNext := SerreCommonPointIntegral.hasPropertySk_of_iso e ((6 - i) - 1) hSY
  have hdNext : topologicalKrullDim (prefixCut K M (i + 1)).left =
      (((6 - i) - 1 : ℕ) : WithBot ℕ∞) :=
    (e.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq _).symm.trans hComp.2
  have hn : (6 - i) - 1 = 5 - i := by omega
  exact ⟨IsIntegral.of_isIso e.hom, hn ▸ hSkNext, hn ▸ hdNext⟩

end M9Native.LagrangianPrefixIntegralStep
