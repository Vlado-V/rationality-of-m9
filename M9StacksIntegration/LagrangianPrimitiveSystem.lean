module

public import M9StacksIntegration.LagrangianPrimitiveIndependence
public import M9StacksIntegration.IntegralRestrictionLadder
public import M9StacksIntegration.LagrangianHyperplaneRows

/-! The actual original determinant linear system and the precise
geometric-prefix version of Mukai II, Lemma 4.2. Its initial kernel is
proved zero on the native chart; the ladder kernel is then a conclusion. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.Bertini
open scoped BigOperators

universe u

namespace M9Native.LagrangianPrimitiveSystem

open LagrangianGrassmannian LagrangianPluckerQuotient
open IteratedLineSectionCuts IntegralRestrictionLadder

variable (K : Type u) [Field K] [CharZero K]

/-- The genuine original fourteen-section system on the genuine LG. -/
def system : FamilyDivisors.{u,u} where
  k := K
  V := Fin 14 → K
  X := space K
  toBase := projection K
  L := determinantLine K
  isInvertible := Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (determinantLine_invertible K)
  ψ := ∑ i : Fin 14, (LinearMap.proj i).smulRight (primitiveSections K i)
  basis := (Pi.basisFun K (Fin 14)).reindex (finCongr (by simp))

omit [CharZero K] in
theorem system_section (v : Fin 14 → K) :
    (system K).sectionOf v = LagrangianHyperplaneCoordinates.determinantSection K v := by
  simp only [FamilyDivisors.sectionOf,system,LinearMap.sum_apply,
    LinearMap.smulRight_apply,LinearMap.proj_apply,
    LagrangianHyperplaneCoordinates.determinantSection]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Stacks.Bertini.globalSections,ModuleCat.restrictScalars.smul_def]
  congr 1

theorem system_kernel : LinearMap.ker (system K).ψ = ⊥ := by
  apply le_antisymm
  · intro v hv
    change v = 0
    apply LagrangianPrimitiveIndependence.coefficients_eq_zero_of_determinantSection K v
    rw [← system_section]
    exact hv
  · exact bot_le

instance system_proper : IsProper (system K).toBase := by
  change IsProper (projection K)
  exact isProper_of_isProjectiveMorphism _
    (LagrangianPluckerClosed.isProjectiveMorphism_projection K)

def sectionList (M : Matrix (Fin 5) (Fin 14) K) : List Γ(determinantLine K,⊤) :=
  List.ofFn (fun j : Fin 5 => LagrangianHyperplaneCoordinates.determinantSection K (M j))

omit [CharZero K] in
theorem coefficientSectionList_eq (M : Matrix (Fin 5) (Fin 14) K) :
    (List.ofFn M).map (system K).sectionOf = sectionList K M := by
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  exact system_section K (M j)

/-- Exactly the original five successive determinant-section zero schemes. -/
def sectionCut (M : Matrix (Fin 5) (Fin 14) K) : Over (space K) :=
  simultaneousCut (determinantLine K) (sectionList K M)

/-- This input contains only integral actual prefixes and nonzero
actual next sections.  In particular it contains no kernel or span claim. -/
abbrev IntegralPrefixes (M : Matrix (Fin 5) (Fin 14) K) : Prop :=
  IntegralSteps (system K) (List.ofFn M) (Over.mk (𝟙 (space K)))

theorem sectionCut_kernel [IsAlgClosed K] (M : Matrix (Fin 5) (Fin 14) K)
    (h : IntegralPrefixes K M) :
    LinearMap.ker (restrictionMap (system K) (sectionCut K M).hom) =
      Submodule.span K (Set.range M) := by
  let : IsAlgClosed (system K).k := (inferInstance : IsAlgClosed K)
  have hk := ker_simultaneousCut (system K) (List.ofFn M) h
  rw [coefficientSectionList_eq,system_kernel,bot_sup_eq] at hk
  change LinearMap.ker (restrictionMap (system K) (sectionCut K M).hom) =
    Submodule.span K {v : Fin 14 → K | v ∈ List.ofFn M} at hk
  have hs : {v : Fin 14 → K | v ∈ List.ofFn M} = Set.range M := by
    ext v
    simp only [Set.mem_ofPred_eq,List.mem_ofFn,Set.mem_range]
  rw [hs] at hk
  exact hk

theorem sectionCut_kernel_finrank [IsAlgClosed K] (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (h : IntegralPrefixes K M) :
    finrank K (LinearMap.ker (restrictionMap (system K) (sectionCut K M).hom)) = 5 := by
  rw [sectionCut_kernel K M h]
  have hr := (Matrix.mulVec_surjective_iff_rank_eq_card (M := M)).mp hM
  rw [Matrix.rank_eq_finrank_span_row] at hr
  exact hr

end M9Native.LagrangianPrimitiveSystem
end
