module

public import M9StacksIntegration.LagrangianBetaFourCut
public import M9StacksIntegration.LineTupleZeroScheme

/-! Actual four original determinant hyperplane cuts on the FULL
arbitrary-plane incidence. This leaf defines the literal line, original
sections and full ideal, and identifies its full scheme with the actual
Cartesian pullback of the four hyperplanes on LG. No smoothness,+finiteness, class, degree or incidence-to-rank-drop isomorphism is used. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.LagrangianIncidenceFourCutBase
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianHyperplaneCoordinates
open ChowCapWords
variable (K : Type u) [Field K]

abbrev fourLine (w : Fin 2 → (Fin 6 → K)) :
    (LagrangianArbitraryPlaneIncidence.incidence K w).Modules :=
  (Scheme.Modules.pullback (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)).obj
    (determinantLine K)

instance fourLine_invertible (w : Fin 2 → (Fin 6 → K)) :
    SheafOfModules.IsInvertible (LagrangianArbitraryPlaneIncidence.incidence K w).sheaf.obj
      (LagrangianArbitraryPlaneIncidence.incidence K w).ringCatSheaf.property (fourLine K w) := by
  dsimp only [fourLine]
  infer_instance

def invertibleLine (w : Fin 2 → (Fin 6 → K)) :
    InvertibleLine (LagrangianArbitraryPlaneIncidence.incidence K w) :=
  ⟨fourLine K w, fourLine_invertible K w⟩

def fourSections (w : Fin 2 → (Fin 6 → K)) (N : Matrix (Fin 5) (Fin 14) K) :
    Fin 4 → Γ(fourLine K w, ⊤) :=
  fun i => pullbackGlobalSections (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
    (determinantLine K) (determinantSection K (N i.succ))

def fourIdeal (w : Fin 2 → (Fin 6 → K)) (N : Matrix (Fin 5) (Fin 14) K) :
    (LagrangianArbitraryPlaneIncidence.incidence K w).IdealSheafData :=
  LineSectionIdealSum.ideal (fourLine K w) (List.ofFn (fourSections K w N))

abbrev fourCut (w : Fin 2 → (Fin 6 → K)) (N : Matrix (Fin 5) (Fin 14) K) : Scheme.{u} :=
  (fourIdeal K w N).subscheme

abbrev fourInclusion (w : Fin 2 → (Fin 6 → K)) (N : Matrix (Fin 5) (Fin 14) K) :
    fourCut K w N ⟶ LagrangianArbitraryPlaneIncidence.incidence K w :=
  (fourIdeal K w N).subschemeι

theorem fourIdeal_eq_comap_remaining (w : Fin 2 → (Fin 6 → K))
    (N : Matrix (Fin 5) (Fin 14) K) :
    fourIdeal K w N = (LagrangianBetaFourCut.remainingIdeal K N).comap
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K w) :=
  (LineSectionIdealOperations.tupleIdeal_comap (determinantLine K)
    (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
    (LagrangianBetaFourCut.remainingSections K N)).symm

/-- Equality of the FULL native rank-four tuple zero ideal, including
all nilpotents, not just equality of its support. -/
theorem fourIdeal_eq_native_tuple_zero (w : Fin 2 → (Fin 6 → K))
    (N : Matrix (Fin 5) (Fin 14) K) :
    fourIdeal K w N = Stacks.Chow.zeroSchemeOfSection
      (LagrangianArbitraryPlaneIncidence.incidence K w)
      (LineTupleZeroScheme.tupleBundle (invertibleLine K w) 4)
      (LineTupleZeroScheme.tupleSection (invertibleLine K w) 4 (fourSections K w N)) :=
  (LineTupleZeroScheme.zeroIdeal_eq (invertibleLine K w) 4 (fourSections K w N)).symm

def fourIsoRemainingPullback (w : Fin 2 → (Fin 6 → K)) (N : Matrix (Fin 5) (Fin 14) K) :
    fourCut K w N ≅ pullback (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)
      (LagrangianBetaFourCut.remainingIdeal K N).subschemeι :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (fourIdeal_eq_comap_remaining K w N)) ≪≫
    (LagrangianBetaFourCut.remainingIdeal K N).comapIso
      (LagrangianArbitraryPlaneIncidence.incidenceToLG K w)

@[reassoc] theorem fourIsoRemainingPullback_hom_fst (w : Fin 2 → (Fin 6 → K))
    (N : Matrix (Fin 5) (Fin 14) K) :
    (fourIsoRemainingPullback K w N).hom ≫ pullback.fst _ _ = fourInclusion K w N := by
  rw [fourIsoRemainingPullback, Iso.trans_hom, Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]
  exact LagrangianMatrixChart.eqToIso_subscheme_ι _ _ (fourIdeal_eq_comap_remaining K w N)

@[reassoc] theorem fourIsoRemainingPullback_hom_toLG (w : Fin 2 → (Fin 6 → K))
    (N : Matrix (Fin 5) (Fin 14) K) :
    (fourIsoRemainingPullback K w N).hom ≫ pullback.snd _ _ ≫
      (LagrangianBetaFourCut.remainingIdeal K N).subschemeι =
    fourInclusion K w N ≫ LagrangianArbitraryPlaneIncidence.incidenceToLG K w := by
  rw [← pullback.condition, ← Category.assoc, fourIsoRemainingPullback_hom_fst]

end M9Native.LagrangianIncidenceFourCutBase
