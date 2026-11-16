module

public import M9StacksIntegration.LagrangianIncidenceFourCutBase
public import M9StacksIntegration.LagrangianIncidenceRankDrop
public import M9StacksIntegration.ClosedPullbackKernelIso
public import M9StacksIntegration.LineSectionZeroRowDrop
public import M9StacksIntegration.LagrangianIncidenceFourCutKernel

/-! The FULL four-cut on the original arbitrary-plane incidence is
the actual Cartesian pullback of the original five-equation curve.
The vanishing original triple row is proved on incidence by its genuine
quotient relation; an actual GL5 row change preserves the full ideal.
The argument does not identify incidence with its rank-drop image.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.LagrangianIncidenceFourCut
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianHyperplaneCoordinates
open LagrangianOrderedFibre LagrangianIncidenceFourCutBase
variable (K : Type u) [Field K] [CharZero K]

theorem zeroSection_ideal_eq_bot {X : Scheme.{u}} (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    Stacks.Divisors.zeroScheme X L (0 : Γ(L, ⊤)) = ⊥ := by
  exact LineSectionZeroRowDrop.zeroSection_ideal_eq_bot L

/-- The first actual changed row vanishes on the full original
incidence for the selected original pair, including isotropic pairs. -/
theorem firstSection_zero (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (N : Matrix (Fin 5) (Fin 14) K)
    (hfirst : N 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    pullbackGlobalSections (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))
      (determinantLine K) (determinantSection K (N 0)) = 0 := by
  rw [hfirst]
  exact LagrangianIncidenceRankDrop.incidence_triple_hyperplane_zero K s e

/-- Pullback of the FULL original model kernel is EXACTLY the four
remaining original changed row ideals on the FULL incidence. -/
theorem model_kernel_comap_eq_fourIdeal (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (modelInclusion K M hM).ker.comap
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e)) =
        fourIdeal K (s ∘ e) (A.val * M) := by
  exact LagrangianIncidenceFourCutKernel.model_kernel_comap_eq_fourIdeal_of_first_zero
    K M hM (s ∘ e) A (firstSection_zero K s e (A.val * M) hfirst)

theorem pullback_projection_kernel (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (pullback.fst (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))
      (modelInclusion K M hM)).ker = fourIdeal K (s ∘ e) (A.val * M) := by
  rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  exact model_kernel_comap_eq_fourIdeal K M hM s e A hfirst

def fourIsoLeftCurvePullback (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    fourCut K (s ∘ e) (A.val * M) ≅
      pullback (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))
        (modelInclusion K M hM) :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (model_kernel_comap_eq_fourIdeal K M hM s e A hfirst).symm) ≪≫
      ClosedPullbackKernelIso.leftIso (modelInclusion K M hM)
        (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))

@[reassoc] theorem fourIsoLeftCurvePullback_hom_fst (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (fourIsoLeftCurvePullback K M hM s e A hfirst).hom ≫ pullback.fst _ _ =
      fourInclusion K (s ∘ e) (A.val * M) := by
  rw [fourIsoLeftCurvePullback, Iso.trans_hom, Category.assoc,
    ClosedPullbackKernelIso.leftIso_hom_fst]
  exact LagrangianMatrixChart.eqToIso_subscheme_ι _ _
    (model_kernel_comap_eq_fourIdeal K M hM s e A hfirst).symm

/-- The orientation is exactly the original-C-first pullback used by
the separate C-only incidence comparison. -/
def fourIsoCurvePullback (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    fourCut K (s ∘ e) (A.val * M) ≅ pullback (modelInclusion K M hM)
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e)) :=
  fourIsoLeftCurvePullback K M hM s e A hfirst ≪≫
    pullbackSymmetry (LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e))
      (modelInclusion K M hM)

@[reassoc] theorem fourIsoCurvePullback_hom_snd (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (fourIsoCurvePullback K M hM s e A hfirst).hom ≫ pullback.snd _ _ =
      fourInclusion K (s ∘ e) (A.val * M) := by
  simp only [fourIsoCurvePullback, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd, fourIsoLeftCurvePullback_hom_fst]

@[reassoc] theorem fourIsoCurvePullback_hom_toLG (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (fourIsoCurvePullback K M hM s e A hfirst).hom ≫ pullback.fst _ _ ≫
      modelInclusion K M hM =
        fourInclusion K (s ∘ e) (A.val * M) ≫
          LagrangianArbitraryPlaneIncidence.incidenceToLG K (s ∘ e) := by
  rw [pullback.condition, ← Category.assoc, fourIsoCurvePullback_hom_snd]

@[reassoc] theorem fourIsoCurvePullback_inv_inclusion (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVec) (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (fourIsoCurvePullback K M hM s e A hfirst).inv ≫
      fourInclusion K (s ∘ e) (A.val * M) = pullback.snd _ _ := by
  rw [← fourIsoCurvePullback_hom_snd K M hM s e A hfirst, Iso.inv_hom_id_assoc]

end M9Native.LagrangianIncidenceFourCut
