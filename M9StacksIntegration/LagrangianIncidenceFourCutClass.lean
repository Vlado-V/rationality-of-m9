module

public import M9StacksIntegration.LagrangianIncidenceFourCapPush
public import M9StacksIntegration.LagrangianArbitraryPlaneIncidenceClass
public import M9StacksIntegration.LagrangianSecondChernCapOrder
public import M9StacksIntegration.FiniteFourLineCuts

/-! Genuine cap and degree identities on the original incidence.
Actual smoothness, pure dimension and the second-Chern push class are
derived from the original independent plane. Actual proper-push cap
naturality is proved from native operators. Finiteness of the FULL
four-cut is the remaining honest geometric input of the length theorem;
the original-curve incidence comparison supplies it separately.
No intersection class, compatibility, or degree value is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow Stacks.Chow.GenuineChern
universe u
namespace M9Native.LagrangianIncidenceFourCutClass
open LagrangianGrassmannian LagrangianPluckerQuotient LagrangianDegree
open LagrangianIncidenceFourCutBase LagrangianSecondChernDegree
open LagrangianIncidenceFourCapPush
open ChowCapWords GradedLineCapSubring
variable (K : Type u) [Field K] [CharZero K]

/-- Genuine independent-plane geometry and genuine native proper cap
naturality identify the actual four-cap degree with the actual LG mixed degree. -/
theorem fourCap_degree_eq_mixedDegree (w : Fin 2 → (Fin 6 → K))
    (hw : LinearIndependent K w) :
    chowDegree (fieldChowSituation K) (fieldChowSituation_dimensionFunction_eq_zero K)
      (structuralMap K w) (IsLocalRing.closedPoint K)
      (capPow (fieldChowSituation K) (structuralMap K w)
        (lineCap (fieldChowSituation K) (structuralMap K w) (invertibleLine K w))
        4 4 0 (by omega)
        (fundamentalChowClass (fieldChowSituation K) (structuralMap K w) 4)) = mixedDegree K := by
  have hfund : ChowLineProperPush.properPush (fieldChowSituation K) (structuralMap K w)
      (projection K) (LagrangianArbitraryPlaneIncidence.incidenceToLG K w) rfl 4
      (fundamentalChowClass (fieldChowSituation K) (structuralMap K w) 4) =
      chernCap (fieldChowSituation K) 3 (projection K) (quotientOnLG K).target 6
        ⟨2,by decide⟩ (fundamentalChowClass (fieldChowSituation K) (projection K) 6) := by
    simpa only [structuralMap, LagrangianArbitraryPlaneIncidenceSmooth.toBase] using
      LagrangianArbitraryPlaneIncidenceClass.incidence_fundamental_push_eq_secondChern K w hw
  have hp := fourCap_push K w
    (fundamentalChowClass (fieldChowSituation K) (structuralMap K w) 4)
  rw [hfund] at hp
  have hd := CurveSingleCapDegree.zeroCycleDegree_proper K (projection K)
    (structuralMap K w) (LagrangianArbitraryPlaneIncidence.incidenceToLG K w) rfl
    (capPow (fieldChowSituation K) (structuralMap K w)
      (lineCap (fieldChowSituation K) (structuralMap K w) (invertibleLine K w))
      4 4 0 (by omega)
      (fundamentalChowClass (fieldChowSituation K) (structuralMap K w) 4))
  rw [hp] at hd
  exact hd.trans (LagrangianSecondChernCapOrder.four_caps_secondChern_degree_eq_mixedDegree K)

/-- Finiteness is a genuine property of the FULL original four-cut,
not a prescribed length or class. Its nilpotent-counting length equals
the original mixed degree by the actual finite-four-cut theorem. -/
theorem finrank_fourCut_eq_mixedDegree (w : Fin 2 → (Fin 6 → K))
    (hw : LinearIndependent K w) (N : Matrix (Fin 5) (Fin 14) K)
    [IsFinite (fourInclusion K w N ≫ structuralMap K w)] :
    letI : Algebra K Γ(fourCut K w N, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (fourInclusion K w N ≫ structuralMap K w).appTop).hom.toAlgebra
    (Module.finrank K Γ(fourCut K w N, ⊤) : ℤ) = mixedDegree K := by
  let : SmoothOfRelativeDimension 4 (structuralMap K w) :=
    LagrangianArbitraryPlaneIncidenceSmooth.toBase_smoothOfRelativeDimension K w hw
  let := SmoothOfRelativeDimension.smooth 4 (structuralMap K w)
  letI : IsFinite ((FiniteFourLineCuts.fourCutIdeal
      (invertibleLine K w) (fourSections K w N)).subschemeι ≫ structuralMap K w) := by
    change IsFinite (fourInclusion K w N ≫ structuralMap K w)
    infer_instance
  have h := FiniteFourLineCuts.degree_four_caps_eq_finrank K (structuralMap K w)
    (LagrangianArbitraryPlaneIncidenceSmooth.incidence_equidimensional K w hw)
    (LagrangianArbitraryPlaneIncidenceSmooth.incidence_dimension K w hw)
    (invertibleLine K w) (fourSections K w N)
  exact h.symm.trans (fourCap_degree_eq_mixedDegree K w hw)

/-- The original finite algebra and original Plucker cap degree obey
the true integral relation. No division in Chow and no value sixteen
or eight is assumed. -/
theorem two_mul_finrank_fourCut_eq_pluckerCapDegree (w : Fin 2 → (Fin 6 → K))
    (hw : LinearIndependent K w) (N : Matrix (Fin 5) (Fin 14) K)
    [IsFinite (fourInclusion K w N ≫ structuralMap K w)] :
    letI : Algebra K Γ(fourCut K w N, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (fourInclusion K w N ≫ structuralMap K w).appTop).hom.toAlgebra
    2 * (Module.finrank K Γ(fourCut K w N, ⊤) : ℤ) = LagrangianActualDegree.pluckerCapDegree K := by
  rw [finrank_fourCut_eq_mixedDegree K w hw N]
  exact two_mul_mixedDegree_eq_pluckerCapDegree K

end M9Native.LagrangianIncidenceFourCutClass
