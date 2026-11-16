module

public import M9StacksIntegration.ExteriorEvaluation
public import M9StacksIntegration.MukaiThreeDimensionalBivectors

/-!
# The actual determinant lower bound from three original sections

If the original ambient bundle's native exterior evaluation is
nonzero on every independent pair, then any original monic subsheaf
with three sections has at least three determinant sections. Actual
H0 injectivity and actual exterior-evaluation naturality transfer the
pair condition. Genuine three-dimensional exterior decomposition
proves injectivity on the three-section exterior square. Thus the
determinant lower bound is a conclusion, not an assumption about the
original generated image or its saturation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiThreeSectionDeterminant

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The original monomorphism induces an actual injection on native H0. -/
theorem cohomologyMap_injective_of_mono {F E : X.Modules} (j : F ⟶ E) [Mono j] :
    Function.Injective (cohomologyOverFieldMap k f j 0) := by
  have hS : (ShortComplex.cokernelSequence j).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := by change Mono j; infer_instance
      epi_g := by change Epi (cokernel.π j); infer_instance }
  obtain ⟨_,hinj,_⟩ := exists_cohomologyOverField_longExactSequence k f hS
  exact hinj

/-- Three actual sections give three actual determinant sections when
every ambient independent pair has nonzero native exterior evaluation. -/
theorem three_le_h0_exterior_two_of_mono
    (F E : X.Modules) (j : F ⟶ E) [Mono j]
    [FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0)]
    (h3 : 3 ≤ Module.finrank k (cohomologyOverField k f F 0))
    (hpair : ∀ s : Fin 2 → cohomologyOverField k f E 0,
      LinearIndependent k s →
        ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 s) ≠ 0) :
    3 ≤ Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower F 2) 0) := by
  obtain ⟨v,hv⟩ := exists_linearIndependent_of_le_finrank h3
  let a := Fintype.linearCombination k v
  have ha : Function.Injective a :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hv
  let g := (cohomologyOverFieldMap k f j 0).hom
  have hg : Function.Injective g := cohomologyMap_injective_of_mono k f j
  let B := ((ExteriorEvaluation.lambda k f F 2).compAlternatingMap
    (exteriorPower.ιMulti k 2)).compLinearMap a
  let L := exteriorPower.alternatingMapLinearEquiv B
  apply MukaiThreeDimensionalBivectors.three_le_finrank_of_independent_wedges_ne_zero
    (by simp : Module.finrank k (Fin 3 → k) = 3) L
  intro x y hxy hz
  have hFpair : LinearIndependent k ![a x,a y] := by
    convert hxy.map' a (LinearMap.ker_eq_bot.mpr ha) using 1
    ext i
    fin_cases i <;> rfl
  have hEpair := hFpair.map' g (LinearMap.ker_eq_bot.mpr hg)
  apply hpair (g ∘ ![a x,a y]) hEpair
  change exteriorPower.alternatingMapLinearEquiv B (exteriorPower.ιMulti k 2 ![x,y]) = 0 at hz
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] at hz
  change ExteriorEvaluation.lambda k f F 2
    (exteriorPower.ιMulti k 2 (fun i => a (![x,y] i))) = 0 at hz
  have hvec : (fun i : Fin 2 => a (![x,y] i)) = ![a x,a y] := by
    ext i
    fin_cases i <;> rfl
  rw [hvec] at hz
  have hnat := congrArg
    (fun M => M (exteriorPower.ιMulti k 2 ![a x,a y]))
    (ExteriorEvaluation.lambda_naturality k f j 2)
  simp only [LinearMap.comp_apply,exteriorPower.map_apply_ιMulti] at hnat
  rw [hz,map_zero] at hnat
  exact hnat.symm

end M9Native.MukaiThreeSectionDeterminant
