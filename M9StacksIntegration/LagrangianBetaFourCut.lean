module

public import M9StacksIntegration.LagrangianBetaRankDrop
public import M9StacksIntegration.LagrangianPairDeterminantContainment
public import M9StacksIntegration.LagrangianMatrixRowChange
public import M9StacksIntegration.LineSectionIdealOperations
public import M9StacksIntegration.IdealIntersectionPullback
public import M9StacksIntegration.NonzeroSectionZeroFinite

/-!
# The actual beta divisor is the actual four-hyperplane cut on rank drop

The selected original pair may be isotropic. The full rank-drop ideal
is contained in the original triple hyperplane scheme-theoretically.
An actual invertible change of the original five equations makes this
hyperplane first; removing it on rank drop leaves exactly the four
remaining original hyperplanes. Actual ideal equalities construct actual
scheme isomorphisms with their original LG and field projections.
No Schubert class or numerical degree is asserted here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.LagrangianBetaFourCut
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianHyperplaneCoordinates
open LagrangianOrderedFibre LagrangianPrimitiveSystem LagrangianRankTwoSubsystemBundles
open LagrangianBetaRankDrop
variable (K : Type u) [Field K] [CharZero K]

def remainingSections (N : Matrix (Fin 5) (Fin 14) K) : Fin 4 → Γ(determinantLine K, ⊤) :=
  fun i => determinantSection K (N i.succ)

def remainingIdeal (N : Matrix (Fin 5) (Fin 14) K) : (space K).IdealSheafData :=
  LineSectionIdealSum.ideal (determinantLine K) (List.ofFn (remainingSections K N))

theorem fiveIdeal_eq_first_sup_remaining (N : Matrix (Fin 5) (Fin 14) K) :
    LineSectionIdealSum.ideal (determinantLine K) (sectionList K N) =
      Stacks.Divisors.zeroScheme (space K) (determinantLine K) (determinantSection K (N 0)) ⊔
        remainingIdeal K N := by
  rw [sectionList, List.ofFn_succ, LineSectionIdealOperations.ideal_cons]
  rfl

/-- The full intersection with all five original equations is EXACTLY
the full intersection with the four remaining changed equations. -/
theorem ambientIntersectionIdeal_eq_four (M : Matrix (Fin 5) (Fin 14) K)
    (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔
        LineSectionIdealSum.ideal (determinantLine K) (sectionList K M) =
      LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔ remainingIdeal K (A.val * M) := by
  rw [LagrangianMatrixRowChange.equationIdeal_eq K A M,
    fiveIdeal_eq_first_sup_remaining, hfirst, ← sup_assoc,
    sup_eq_left.mpr (LagrangianPairDeterminantContainment.hyperplaneIdeal_le_rankDrop K s e)]

abbrev rankDropInclusion (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :=
  LagrangianArbitraryPlaneIncidence.rankDropInclusion K (s ∘ e)

abbrev fourLine (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3) :=
  (Scheme.Modules.pullback (rankDropInclusion K s e)).obj (determinantLine K)

/-- Four ACTUAL pulled-back original determinant hyperplane sections. -/
def fourSections (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (N : Matrix (Fin 5) (Fin 14) K) : Fin 4 → Γ(fourLine K s e, ⊤) :=
  fun i => pullbackGlobalSections (rankDropInclusion K s e) (determinantLine K)
    (remainingSections K N i)

/-- The actual four-line-section sum ideal on the original rank-drop scheme. -/
def fourIdeal (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (N : Matrix (Fin 5) (Fin 14) K) :
    (LagrangianArbitraryPlaneIncidence.rankDrop K (s ∘ e)).IdealSheafData :=
  LineSectionIdealSum.ideal (fourLine K s e) (List.ofFn (fourSections K s e N))

theorem remainingIdeal_comap (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (N : Matrix (Fin 5) (Fin 14) K) :
    (remainingIdeal K N).comap (rankDropInclusion K s e) = fourIdeal K s e N :=
  LineSectionIdealOperations.tupleIdeal_comap (determinantLine K) (rankDropInclusion K s e)
    (remainingSections K N)

def fourIsoAmbientIntersection (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (N : Matrix (Fin 5) (Fin 14) K) :
    (fourIdeal K s e N).subscheme ≅
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔ remainingIdeal K N).subscheme :=
  eqToIso (congrArg (fun I : (LagrangianArbitraryPlaneIncidence.rankDrop K (s ∘ e)).IdealSheafData =>
    I.subscheme) (remainingIdeal_comap K s e N).symm) ≪≫
    IdealIntersectionPullback.closedComapIsoSup (rankDropInclusion K s e) (remainingIdeal K N) ≪≫
      eqToIso (congrArg (fun I : (space K).IdealSheafData => I.subscheme)
        (congrArg (fun I => I ⊔ remainingIdeal K N)
          (Scheme.IdealSheafData.ker_subschemeι
            (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e)))))

@[reassoc]
theorem fourIsoAmbientIntersection_hom_toLG (s : Fin 3 → (Fin 6 → K)) (e : Fin 2 ↪ Fin 3)
    (N : Matrix (Fin 5) (Fin 14) K) :
    (fourIsoAmbientIntersection K s e N).hom ≫
        (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔ remainingIdeal K N).subschemeι =
      (fourIdeal K s e N).subschemeι ≫ rankDropInclusion K s e := by
  simp only [fourIsoAmbientIntersection, Iso.trans_hom, Category.assoc,
    ]
  rw [LagrangianMatrixChart.eqToIso_subscheme_ι _ _
      (congrArg (fun I => I ⊔ remainingIdeal K N)
        (Scheme.IdealSheafData.ker_subschemeι
          (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e)))),
    IdealIntersectionPullback.closedComapIsoSup_hom_comp,
    LagrangianMatrixChart.eqToIso_subscheme_ι_assoc _ _ (remainingIdeal_comap K s e N).symm]

section Model
variable (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  [IsIntegral (model K M hM)] [SmoothOfRelativeDimension 1 (modelProjection K M hM)]

def betaIsoAmbientIntersection (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3) :
    betaZero K M hM s hr e ≅
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔
        LineSectionIdealSum.ideal (determinantLine K) (sectionList K M)).subscheme :=
  eqToIso (congrArg (fun I : (model K M hM).IdealSheafData => I.subscheme)
    (betaZeroIdeal_eq_rankDrop_comap K M hM s hr e)) ≪≫
    IdealIntersectionPullback.closedComapIsoSup (modelInclusion K M hM)
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e)) ≪≫
        eqToIso (congrArg (fun I : (space K).IdealSheafData => I.subscheme) (by
          rw [LagrangianMatrixRowChange.modelInclusion_ker, sup_comm]))

@[reassoc]
theorem betaIsoAmbientIntersection_hom_toLG (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3) :
    (betaIsoAmbientIntersection K M hM s hr e).hom ≫
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔
        LineSectionIdealSum.ideal (determinantLine K) (sectionList K M)).subschemeι =
      (betaZeroIdeal K M hM s hr e).subschemeι ≫ modelInclusion K M hM := by
  simp only [betaIsoAmbientIntersection, Iso.trans_hom, Category.assoc,
    ]
  rw [LagrangianMatrixChart.eqToIso_subscheme_ι _ _
      (show (modelInclusion K M hM).ker ⊔
          LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) =
        LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔
          LineSectionIdealSum.ideal (determinantLine K) (sectionList K M) by
        rw [LagrangianMatrixRowChange.modelInclusion_ker, sup_comm]),
    IdealIntersectionPullback.closedComapIsoSup_hom_comp,
    ]
  simpa only [Category.assoc, originalPair, betaZeroIdeal, betaZero] using congrArg
    (fun a => a ≫ modelInclusion K M hM)
    (LagrangianMatrixChart.eqToIso_subscheme_ι _ _
      (betaZeroIdeal_eq_rankDrop_comap K M hM s hr e))

/-- The SAME original beta zero scheme is the FULL four-hyperplane cut
on the SAME original pair rank-drop scheme. -/
def betaZeroIsoFourCut (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    betaZero K M hM s hr e ≅ (fourIdeal K s e (A.val * M)).subscheme :=
  betaIsoAmbientIntersection K M hM s hr e ≪≫
    eqToIso (congrArg (fun I : (space K).IdealSheafData => I.subscheme)
      (ambientIntersectionIdeal_eq_four K M s e A hfirst)) ≪≫
        (fourIsoAmbientIntersection K s e (A.val * M)).symm

@[reassoc]
theorem betaZeroIsoFourCut_hom_toLG (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (betaZeroIsoFourCut K M hM s hr e A hfirst).hom ≫
      (fourIdeal K s e (A.val * M)).subschemeι ≫ rankDropInclusion K s e =
      (betaZeroIdeal K M hM s hr e).subschemeι ≫ modelInclusion K M hM := by
  have hi : (fourIsoAmbientIntersection K s e (A.val * M)).inv ≫
      (fourIdeal K s e (A.val * M)).subschemeι ≫ rankDropInclusion K s e =
      (LagrangianArbitraryPlaneIncidence.rankDropIdeal K (s ∘ e) ⊔
        remainingIdeal K (A.val * M)).subschemeι := by
    rw [← fourIsoAmbientIntersection_hom_toLG, Iso.inv_hom_id_assoc]
  simp only [betaZeroIsoFourCut, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [hi, LagrangianMatrixChart.eqToIso_subscheme_ι _ _
      (ambientIntersectionIdeal_eq_four K M s e A hfirst),
    betaIsoAmbientIntersection_hom_toLG]

theorem nativeBetaZeroIdeal_eq_betaZeroIdeal (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3) :
    Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s)
      (betaSection K M hM s hr e) = betaZeroIdeal K M hM s hr e :=
  (nativeBetaZeroIdeal_eq_rankDrop_comap K M hM s hr e).trans
    (betaZeroIdeal_eq_rankDrop_comap K M hM s hr e).symm

/-- The literal native Chow zero-scheme itself has this actual four-cut
isomorphism, without replacing its defining ideal by a support. -/
def nativeBetaZeroIsoFourCut (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s)
      (betaSection K M hM s hr e)).subscheme ≅ (fourIdeal K s e (A.val * M)).subscheme :=
  eqToIso (congrArg (fun I : (model K M hM).IdealSheafData => I.subscheme)
    (nativeBetaZeroIdeal_eq_betaZeroIdeal K M hM s hr e)) ≪≫
      betaZeroIsoFourCut K M hM s hr e A hfirst

@[reassoc]
theorem nativeBetaZeroIsoFourCut_hom_toLG (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    (nativeBetaZeroIsoFourCut K M hM s hr e A hfirst).hom ≫
      (fourIdeal K s e (A.val * M)).subschemeι ≫ rankDropInclusion K s e =
      (Stacks.Chow.zeroSchemeOfSection (model K M hM) (beta K M hM s)
        (betaSection K M hM s hr e)).subschemeι ≫ modelInclusion K M hM := by
  simp only [nativeBetaZeroIsoFourCut, Iso.trans_hom, Category.assoc]
  rw [betaZeroIsoFourCut_hom_toLG]
  exact LagrangianMatrixChart.eqToIso_subscheme_ι_assoc _ _
    (nativeBetaZeroIdeal_eq_betaZeroIdeal K M hM s hr e) _

/-- Nonzero section on the actual original proper integral curve gives
finiteness of the full native beta zero scheme, including nilpotents. -/
theorem betaZero_isFinite (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (he : LagrangianRankTwoSubsystemExistence.pairBetaSection K M hM s hr e ≠ 0) :
    IsFinite ((betaZeroIdeal K M hM s hr e).subschemeι ≫ modelProjection K M hM) := by
  letI := beta_rank K M hM s hr
  letI : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (beta K M hM s) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
  letI := model_isCurve K M hM
  have h := NonzeroSectionZeroFinite.isFinite_zeroSchemeOfSection_of_isCurve
    (beta K M hM s) (betaSection K M hM s hr e) K (modelProjection K M hM)
      (betaSection_ne_zero K M hM s hr e he)
  rw [NativeVectorSectionZeroPullback.zeroSchemeOfSection_eq_evaluationIdeal] at h
  exact h

/-- Thus the actual FOUR-cut, not a reduced support, is finite. -/
theorem fourCut_isFinite (s : Fin 3 → (Fin 6 → K))
    (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2) (e : Fin 2 ↪ Fin 3)
    (he : LagrangianRankTwoSubsystemExistence.pairBetaSection K M hM s hr e ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 5) K)
    (hfirst : (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s) :
    IsFinite ((fourIdeal K s e (A.val * M)).subschemeι ≫ rankDropInclusion K s e ≫ projection K) := by
  letI := betaZero_isFinite K M hM s hr e he
  have h : (betaZeroIsoFourCut K M hM s hr e A hfirst).inv ≫
      ((betaZeroIdeal K M hM s hr e).subschemeι ≫ modelProjection K M hM) =
      (fourIdeal K s e (A.val * M)).subschemeι ≫ rankDropInclusion K s e ≫ projection K := by
    have hLG := congrArg
      (fun a => (betaZeroIsoFourCut K M hM s hr e A hfirst).inv ≫ a ≫ projection K)
      (betaZeroIsoFourCut_hom_toLG K M hM s hr e A hfirst)
    simp only [Category.assoc, Iso.inv_hom_id_assoc] at hLG
    exact hLG.symm
  rw [← h]
  infer_instance

variable [IsAlgClosed K]

/-- The actual original curve PRODUCES its original independent pair,
nonzero beta section, genuine equation change and finite full four-cut;
none of those data or scheme comparisons is supplied as a premise. -/
theorem exists_finite_fourCut :
    ∃ (s : Fin 3 → (Fin 6 → K))
      (hr : MukaiSemiIrreducible.EverywhereRank (originalMap K M hM s) 2)
      (e : Fin 2 ↪ Fin 3) (A : Matrix.GeneralLinearGroup (Fin 5) K),
      LinearIndependent K s ∧ LinearIndependent K (s ∘ e) ∧
      betaSection K M hM s hr e ≠ 0 ∧ Function.Surjective (A.val * M).mulVec ∧
      (A.val * M) 0 = PrimitiveDecomposableNonzero.coefficients K s ∧
      determinantSection K ((A.val * M) 0) ≠ 0 ∧
      Nonempty (betaZero K M hM s hr e ≅ (fourIdeal K s e (A.val * M)).subscheme) ∧
      IsFinite ((fourIdeal K s e (A.val * M)).subschemeι ≫
        rankDropInclusion K s e ≫ projection K) := by
  obtain ⟨s, hs, hsections, hdet, hr⟩ :=
    MukaiDeterminantZeroSubsystem.exists_rank_two_subsystem K M hM
  obtain ⟨e, he⟩ := LagrangianRankTwoSubsystemExistence.exists_nonzero_pair_section K M hM s hr
  obtain ⟨A, hAM, hfirst, hnonzero⟩ :=
    LagrangianTripleFirstEquation.exists_first_equation K M hM s hs hdet
  exact ⟨s, hr, e, A, hs, hs.comp e e.injective, betaSection_ne_zero K M hM s hr e he,
    hAM, hfirst, hnonzero, ⟨betaZeroIsoFourCut K M hM s hr e A hfirst⟩,
      fourCut_isFinite K M hM s hr e he A hfirst⟩

end Model
end M9Native.LagrangianBetaFourCut
