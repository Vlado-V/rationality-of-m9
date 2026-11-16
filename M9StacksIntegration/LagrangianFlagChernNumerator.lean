module

public import M9StacksIntegration.LagrangianFlagDeterminant
public import M9StacksIntegration.RankThreeFlagChowCap
public import M9StacksIntegration.ChowPicardLineFamily
public import M9StacksIntegration.LineFamilyCapWords
public import M9StacksIntegration.ChowVirtualPullback

/-!
# Actual determinant and exterior-square caps on the full quotient flag

The three roots below are the original named invertible quotient lines.
The determinant relation follows from their actual tensor isomorphism.
The exterior-square relation follows from the two original exact rows
and the native Whitney top-cap theorem, on every original Chow class.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Stacks.Chow.GenuineChern

universe u

namespace M9Native.LagrangianFlagChernNumerator

open FlagThreeQuotient MukaiBundleDeterminant ChowCapWords GradedLineCapSubring
open ChowPicardLineFamily ChowLineFamilyComparison GradedCapVirtualSchur

local instance actualHasKernels {T : Scheme.{u}} : HasKernels T.Modules := inferInstance
local instance actualHasKernel {T : Scheme.{u}} {A B : T.Modules} (f : A ⟶ B) : HasKernel f :=
  HasKernels.has_limit f

local instance invertibleLineRank {T : Scheme.{u}} (L : InvertibleLine T) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L.1 1 :=
  @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible T L.1 L.2

variable {X : Scheme.{u}} (D : X.Modules)
  [SheafOfModules.IsFiniteLocallyFree.{u,u,u} D]

local instance line1Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (line1 D) 1 := line1_rank D
local instance line2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (line2 D) 1 := line2_rank D
local instance line3Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (line3 D) 1 := line3_rank D
local instance quotient2Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientBundle D 1) 2 :=
  quotientBundle_rank D 1
local instance quotient3Rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientBundle D 2) 3 :=
  quotientBundle_rank D 2
local instance quotientExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (topExterior (quotientBundle D 2) 2) 3 := by
  simpa only [topExterior,show Nat.choose 3 2 = 3 by decide] using
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (quotientBundle D 2) 3 2

/-- The first original positive quotient line. -/
def firstLine : InvertibleLine (space D) :=
  ⟨line1 D, GenuineChern.isInvertible_of_rank_one (line1 D)⟩

/-- The second original positive quotient line. -/
def secondLine : InvertibleLine (space D) :=
  ⟨line2 D, GenuineChern.isInvertible_of_rank_one (line2 D)⟩

/-- The third original positive quotient line. -/
def thirdLine : InvertibleLine (space D) :=
  ⟨line3 D, GenuineChern.isInvertible_of_rank_one (line3 D)⟩

/-- The actual determinant of the last original quotient. -/
def quotientDeterminantLine : InvertibleLine (space D) :=
  ⟨topExterior (quotientBundle D 2) 3,
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry
      (space D).presheaf (space D).ringCatSheaf.2 _).1
      (Scheme.Modules.isInvertible_exteriorPower_self (quotientBundle D 2) 3)⟩

variable (C : ChowSituation.{u}) (q : space D ⟶ C.S) [LocallyOfFiniteType q]

/-- The determinant cap is the sum of the same actual three line caps. -/
theorem quotientDeterminant_lineFamily :
    lineFamily C q (quotientDeterminantLine D) =
      lineFamily C q (firstLine D) + lineFamily C q (secondLine D) +
        lineFamily C q (thirdLine D) := by
  have h := lineFamily_congr C q (quotientDeterminantLine D)
    (tensorLine (tensorLine (firstLine D) (secondLine D)) (thirdLine D))
    (LagrangianFlagDeterminant.quotientDeterminantIso D)
  rw [lineFamily_tensor, lineFamily_tensor] at h
  exact h

/-- Native Whitney on the actual named flag rows gives the actual
top exterior-square cap, with only its original Chow-grade transport. -/
theorem exteriorSquare_top_cap (k : ℤ) (α : chowGroup C q k) :
    chernCap C 3 q (topExterior (quotientBundle D 2) 2) k (Fin.last 3) α ≍
      LineFamilyCapWords.familyWord C q
        [tensorLine (secondLine D) (thirdLine D),
          tensorLine (firstLine D) (thirdLine D),
          tensorLine (firstLine D) (secondLine D)] k 3 α := by
  have hRows := RankThreeFlagChowCap.exteriorSquare_top_cap
    (line1 D) (line2 D) (line3 D) (quotientBundle D 1) (quotientBundle D 2)
    (kernel.ι (step21 D)) (step21 D) (kernel.condition (step21 D)) (sequence21_shortExact D)
    (kernel.ι (step32 D)) (step32 D) (kernel.condition (step32 D)) (sequence32_shortExact D)
    C q k α
  let L12 := tensorLine (firstLine D) (secondLine D)
  let L13 := tensorLine (firstLine D) (thirdLine D)
  let L23 := tensorLine (secondLine D) (thirdLine D)
  have hLine (L : InvertibleLine (space D)) (m : ℤ) (β : chowGroup C q m) :
      chernCap C 1 q L.1 m (Fin.last 1) β = lineFamily C q L m 1 β := by
    letI := L.2
    letI := @SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible
      (space D) L.1 L.2
    have h := congrArg (fun a : GradedCapFamily (chowGroup C q) => a m 1 β)
      (lineFamily_eq_homComponent C q L)
    rw [homComponent_apply_self,
      chernFamily_apply_of_le C q L.1 1 m (by decide : 1 ≤ 1)] at h
    exact h.symm
  have h3 := hLine L23 ((k-1)-1)
    (chernCap C 1 q L13.1 (k-1) (Fin.last 1)
      (chernCap C 1 q L12.1 k (Fin.last 1) α))
  have h2 := hLine L13 (k-1) (chernCap C 1 q L12.1 k (Fin.last 1) α)
  have h1 := hLine L12 k α
  have hWord : LineFamilyCapWords.familyWord C q [L23,L13,L12] k 3 α ≍
      lineFamily C q L23 ((k-1)-1) 1
        (lineFamily C q L13 (k-1) 1 (lineFamily C q L12 k 1 α)) := by
    simp only [LineFamilyCapWords.familyWord,List.map_cons,List.map_nil,
      List.prod_cons,List.prod_nil,mul_one]
    rw [mul_apply_of_homogeneous_right _
      ((lineFamily_homogeneous C q L13).mul (lineFamily_homogeneous C q L12)) 1]
    unfold capTo
    refine (gradedDegreeCast_heq _ _).trans ?_
    rw [mul_apply_of_homogeneous_right _ (lineFamily_homogeneous C q L12) 1]
    unfold capTo
    exact (lineFamily C q L23).apply_heq (by omega) 1 (gradedDegreeCast_heq _ _)
  exact hRows.trans ((heq_of_eq (h3.trans (by rw [h2,h1]))).trans hWord.symm)

/-- This is an equality of the original operational families, proved
on every original class by the preceding native cap comparison. -/
theorem exteriorSquare_homComponent :
    homComponent 3 (chernFamily C q (topExterior (quotientBundle D 2) 2) 3) =
      LineFamilyCapWords.familyWord C q
        [tensorLine (secondLine D) (thirdLine D),
          tensorLine (firstLine D) (thirdLine D),
          tensorLine (firstLine D) (secondLine D)] := by
  let Ls := [tensorLine (secondLine D) (thirdLine D),
    tensorLine (firstLine D) (thirdLine D),
    tensorLine (firstLine D) (secondLine D)]
  have hCoefficients : ∀ k,
      chernFamily C q (topExterior (quotientBundle D 2) 2) 3 k 3 =
        LineFamilyCapWords.familyWord C q Ls k 3 := by
    intro k
    apply AddMonoidHom.ext
    intro α
    rw [chernFamily_apply_of_le C q (topExterior (quotientBundle D 2) 2) 3 k
      (by decide : 3 ≤ 3)]
    exact eq_of_heq (exteriorSquare_top_cap D C q k α)
  have hWord : (LineFamilyCapWords.familyWord C q Ls).IsHomogeneous 3 :=
    LineFamilyCapWords.familyWord_homogeneous C q Ls
  exact (homComponent_congr hCoefficients).trans hWord.homComponent_self

/-- The literal positive quotient roots yield the three expected pair
factors. Reordering uses native commutation of these actual line caps. -/
theorem exteriorSquare_pair_lineFamilies :
    homComponent 3 (chernFamily C q (topExterior (quotientBundle D 2) 2) 3) =
      (lineFamily C q (firstLine D) + lineFamily C q (secondLine D)) *
        (lineFamily C q (firstLine D) + lineFamily C q (thirdLine D)) *
        (lineFamily C q (secondLine D) + lineFamily C q (thirdLine D)) := by
  rw [exteriorSquare_homComponent]
  let L12 := tensorLine (firstLine D) (secondLine D)
  let L13 := tensorLine (firstLine D) (thirdLine D)
  let L23 := tensorLine (secondLine D) (thirdLine D)
  have hReverse : lineFamily C q L23 * (lineFamily C q L13 * lineFamily C q L12) =
      lineFamily C q L12 * lineFamily C q L13 * lineFamily C q L23 := by
    rw [(lineFamily_commute C q L13 L12).eq, ← mul_assoc,
      (lineFamily_commute C q L23 L12).eq, mul_assoc,
      (lineFamily_commute C q L23 L13).eq, ← mul_assoc]
  change lineFamily C q L23 * (lineFamily C q L13 *
    (lineFamily C q L12 * 1)) = _
  rw [mul_one,hReverse]
  simp only [L12,L13,L23,lineFamily_tensor]

section FullRankThree

variable [hD : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} D 3]

/-- The original determinant on the original rank-three source. -/
def originalDeterminantLine : InvertibleLine X :=
  ⟨topExterior D 3,
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf X.ringCatSheaf.2 _).1
      (Scheme.Modules.isInvertible_exteriorPower_self D 3)⟩

/-- Its literal pullback along the actual full flag projection. -/
def pulledDeterminantLine : InvertibleLine (space D) := by
  letI := (originalDeterminantLine D).2
  exact ⟨(Scheme.Modules.pullback (projection D)).obj (topExterior D 3),
    Stacks.Chow.isInvertible_pullback (projection D) (originalDeterminantLine D).1⟩

/-- The actual pulled source determinant has the sum of the actual roots. -/
theorem pulledDeterminant_lineFamily :
    lineFamily C q (pulledDeterminantLine D) =
      lineFamily C q (firstLine D) + lineFamily C q (secondLine D) +
        lineFamily C q (thirdLine D) := by
  have h := lineFamily_congr C q (pulledDeterminantLine D)
    (tensorLine (tensorLine (firstLine D) (secondLine D)) (thirdLine D))
    (LagrangianFlagDeterminant.pulledDeterminantIso D)
  rw [lineFamily_tensor,lineFamily_tensor] at h
  exact h

local instance sourceExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (topExterior D 2) 3 := by
  simpa only [topExterior,show Nat.choose 3 2 = 3 by decide] using
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower D 3 2

local instance pulledExteriorRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (projection D)).obj (topExterior D 2)) 3 :=
  @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (space D) X
    (projection D) (topExterior D 2) 3 (sourceExteriorRank D)

/-- The full last quotient gives the actual pulled exterior square. -/
def pulledExteriorSquareIso :
    (Scheme.Modules.pullback (projection D)).obj (topExterior D 2) ≅
      topExterior (quotientBundle D 2) 2 :=
  LagrangianPullback.exteriorPullbackIso (projection D) D 2 ≪≫
    (Scheme.Modules.exteriorPowerFunctor (space D) 2).mapIso
      (FlagThreeTautological.fullQuotientIso D).symm

/-- The actual exterior-square top Chern component of the pulled source
is the product of the three literal pair-line sums. -/
theorem pulledExteriorSquare_pair_lineFamilies :
    homComponent 3 (chernFamily C q
      ((Scheme.Modules.pullback (projection D)).obj (topExterior D 2)) 3) =
      (lineFamily C q (firstLine D) + lineFamily C q (secondLine D)) *
        (lineFamily C q (firstLine D) + lineFamily C q (thirdLine D)) *
        (lineFamily C q (secondLine D) + lineFamily C q (thirdLine D)) := by
  rw [chernFamily_congr C q (topExterior (quotientBundle D 2) 2) 3
    (pulledExteriorSquareIso D) rfl,exteriorSquare_pair_lineFamilies]

end FullRankThree

end M9Native.LagrangianFlagChernNumerator
