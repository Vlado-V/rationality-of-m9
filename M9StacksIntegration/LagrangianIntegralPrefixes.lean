module

public import M9StacksIntegration.LagrangianPrefixIntegralStep
public import M9StacksIntegration.LagrangianPrimitiveSystem
public import M9StacksIntegration.LagrangianRowPrefixes
public import M9StacksIntegration.IntegralRestrictionSuccessor

/-!
# Every actual prefixCut of a transverse integral LG curve is integral

The only geometric input is that the actual final five-section cut is a
smooth integral curve. The original surjective matrix supplies independent
rows. The restriction kernel, next section nonvanishing, Serre predicates,
component dimensions, and actual prefixCut integrality are derived together
by induction. No desired prefixCut or restriction-kernel premise is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Module
universe u
namespace M9Native.LagrangianIntegralPrefixes
open LagrangianGrassmannian LagrangianPluckerQuotient IteratedLineSectionCuts
  IntegralRestrictionLadder LagrangianPrefixIntegralStep

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]

local instance determinantLine_invertible :
    SheafOfModules.IsInvertible (space K).sheaf.obj (space K).ringCatSheaf.property (determinantLine K) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (LagrangianPluckerQuotient.determinantLine_invertible K)

local instance space_locallyNoetherian : IsLocallyNoetherian (space K) :=
  LocallyOfFiniteType.isLocallyNoetherian (projection K)

local instance prefix_locallyNoetherian (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) :
    IsLocallyNoetherian (prefixCut K M i).left :=
  LocallyOfFiniteType.isLocallyNoetherian (prefixCut K M i).hom

theorem prefix_induction_state (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin)
    [IsIntegral (simultaneousCut (determinantLine K) (sections K M)).left]
    [SmoothOfRelativeDimension 1
      ((simultaneousCut (determinantLine K) (sections K M)).hom ≫ projection K)] :
    ∀ i ≤ 4,
      IsIntegral (prefixCut K M i).left ∧
      HasPropertySk (prefixCut K M i).left (6 - i) ∧
      topologicalKrullDim (prefixCut K M i).left = ((6 - i : ℕ) : WithBot ℕ∞) ∧
      LinearMap.ker (restrictionMap (LagrangianPrimitiveSystem.system K) (prefixCut K M i).hom) =
        Submodule.span K {v : Fin 14 → K | v ∈ (List.ofFn M).take i} := by
  let D := LagrangianPrimitiveSystem.system K
  let : IsAlgClosed D.k := (inferInstance : IsAlgClosed K)
  have hProper : IsProper D.toBase := LagrangianPrimitiveSystem.system_proper K
  let : IsProper D.toBase := hProper
  have state : ∀ i ≤ 4,
      IsIntegral (prefixCut K M i).left ∧
      HasPropertySk (prefixCut K M i).left (6 - i) ∧
      topologicalKrullDim (prefixCut K M i).left = ((6 - i : ℕ) : WithBot ℕ∞) ∧
      LinearMap.ker (restrictionMap D (prefixCut K M i).hom) =
        Submodule.span K {v : Fin 14 → K | v ∈ (List.ofFn M).take i} := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨LagrangianIntegral.space_integral K, ?_, LagrangianIntegral.space_dimension K, ?_⟩
      · exact IntegralLineCutSerreDimension.hasPropertySk_of_regular (space K)
          (isRegular_of_smooth_over_field (projection K)) 6
      · change LinearMap.ker (restrictionMap D (𝟙 D.X)) = _
        rw [ker_pullback_identity D]
        change LinearMap.ker (LagrangianPrimitiveSystem.system K).ψ = _
        rw [LagrangianPrimitiveSystem.system_kernel]
        simp
    | succ i ih =>
      intro hi
      obtain ⟨hInt, hS, hDim, hKernel⟩ := ih (by omega)
      let : IsIntegral (prefixCut K M i).left := hInt
      have hi5 : i < 5 := by omega
      let previous := LagrangianRowPrefixes.headRows K M i (Nat.le_of_lt hi5)
      let w := M ⟨i, hi5⟩
      have hKH : LinearMap.ker (restrictionMap D (prefixCut K M i).hom) =
          Submodule.span K (Set.range previous) := by
        rw [LagrangianRowPrefixes.range_headRows]
        exact hKernel
      have hLI : LinearIndependent K (Fin.snoc previous w) :=
        LagrangianRowPrefixes.headRows_snoc_linearIndependent K M hM i hi5
      have hNZ := IntegralRestrictionSuccessor.next_section_ne_zero_of_independent
        D (prefixCut K M i).hom previous w hKH hLI
      have hNext : pullbackGlobalSections (prefixCut K M i).hom (determinantLine K)
          (LagrangianHyperplaneCoordinates.determinantSection K (M ⟨i, hi5⟩)) ≠ 0 := by
        change pullbackGlobalSections (prefixCut K M i).hom (determinantLine K)
          ((LagrangianPrimitiveSystem.system K).sectionOf (M ⟨i, hi5⟩)) ≠ 0 at hNZ
        rw [LagrangianPrimitiveSystem.system_section] at hNZ
        exact hNZ
      have hGeom := integral_successor K M hM i (by omega) hS hDim hNext
      have hCutEq : cut D.L (prefixCut K M i) (D.sectionOf w) = prefixCut K M (i + 1) := by
        change cut (determinantLine K) (prefixCut K M i)
          ((LagrangianPrimitiveSystem.system K).sectionOf w) = _
        rw [LagrangianPrimitiveSystem.system_section]
        exact (prefix_succ_eq K M i hi5).symm
      have hKerCut := ker_cut D (prefixCut K M i) w hNZ
      rw [hCutEq, hKernel] at hKerCut
      have hSet : {v : Fin 14 → K | v ∈ (List.ofFn M).take (i + 1)} =
          {v : Fin 14 → K | v ∈ (List.ofFn M).take i} ∪ {w} := by
        rw [List.take_succ_eq_append_getElem (by simpa using hi5)]
        ext v
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff, List.mem_append,
          List.mem_singleton, List.getElem_ofFn]
        rfl
      have hKernelNext : LinearMap.ker (restrictionMap D (prefixCut K M (i + 1)).hom) =
          Submodule.span K {v : Fin 14 → K | v ∈ (List.ofFn M).take (i + 1)} := by
        rw [hSet, Submodule.span_union]
        exact hKerCut
      have hn : 5 - i = 6 - (i + 1) := by omega
      exact ⟨hGeom.1, hn ▸ hGeom.2.1, hn ▸ hGeom.2.2, hKernelNext⟩
  exact state

theorem prefix_section_ne_zero (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin)
    [IsIntegral (simultaneousCut (determinantLine K) (sections K M)).left]
    [SmoothOfRelativeDimension 1
      ((simultaneousCut (determinantLine K) (sections K M)).hom ≫ projection K)] (i : ℕ) (hi : i < 5) :
    pullbackGlobalSections (prefixCut K M i).hom (determinantLine K)
      (LagrangianHyperplaneCoordinates.determinantSection K (M ⟨i, hi⟩)) ≠ 0 := by
  let D := LagrangianPrimitiveSystem.system K
  let previous := LagrangianRowPrefixes.headRows K M i hi.le
  let w := M ⟨i, hi⟩
  have hKernel := (prefix_induction_state K M hM i (by omega)).2.2.2
  have hKH : LinearMap.ker (restrictionMap D (prefixCut K M i).hom) =
      Submodule.span K (Set.range previous) := by
    rw [LagrangianRowPrefixes.range_headRows]
    exact hKernel
  have hLI : LinearIndependent K (Fin.snoc previous w) :=
    LagrangianRowPrefixes.headRows_snoc_linearIndependent K M hM i hi
  have hNZ := IntegralRestrictionSuccessor.next_section_ne_zero_of_independent
    D (prefixCut K M i).hom previous w hKH hLI
  change pullbackGlobalSections (prefixCut K M i).hom (determinantLine K)
    ((LagrangianPrimitiveSystem.system K).sectionOf (M ⟨i, hi⟩)) ≠ 0 at hNZ
  rw [LagrangianPrimitiveSystem.system_section] at hNZ
  exact hNZ

theorem integral_prefixes (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin)
    [IsIntegral (simultaneousCut (determinantLine K) (sections K M)).left]
    [SmoothOfRelativeDimension 1
      ((simultaneousCut (determinantLine K) (sections K M)).hom ≫ projection K)] :
    ∀ i ≤ 5, IsIntegral (prefixCut K M i).left := by
  intro i hi
  by_cases hi4 : i ≤ 4
  · exact (prefix_induction_state K M hM i hi4).1
  · have he : i = 5 := by omega
    subst i
    have ht : (sections K M).take 5 = sections K M :=
      List.take_of_length_le (by simp [sections, LagrangianTailSupport.sectionList])
    change IsIntegral (simultaneousCut (determinantLine K) ((sections K M).take 5)).left
    rw [ht]
    infer_instance

end M9Native.LagrangianIntegralPrefixes
