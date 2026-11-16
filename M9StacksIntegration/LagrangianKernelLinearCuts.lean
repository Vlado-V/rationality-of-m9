module

public import M9StacksIntegration.LagrangianKernelSymmetricSections
public import M9StacksIntegration.ProjectiveFiniteLinearSection
public import M9StacksIntegration.IteratedLineSectionCuts

/-!
# Genuine linear sections of the original common-kernel zero scheme

Actual cuts by the original five-generator linear system are identified
with the native quotient-projective linear sections of the literal split
quadric. Both comparison maps are constructed from the all-test-scheme
factorization laws, retaining nilpotents and the original base field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u

namespace M9Native.LagrangianKernelLinearCuts

open LagrangianCommonKernelZero LagrangianCommonKernelQuadricIso
open LagrangianKernelSymmetricSections IteratedLineSectionCuts

variable (K : Type u) [Field K] [CharZero K] {m : ℕ}
  (rows : Fin m → coefficientSpace K)

abbrev equations : Submodule K (coefficientSpace K) :=
  Submodule.span K (Set.range rows)

/-- Literal successive zero schemes of the actual linear combinations. -/
def cut : Over (zeroSpace K) :=
  simultaneousCut (line K) (List.ofFn fun j : Fin m => sectionLinear K (rows j))

instance cut_closed : IsClosedImmersion (cut K rows).hom := by
  dsimp only [cut]
  infer_instance

/-- The actual native quotient-projective intersection, mapped back to Z. -/
def toZero : SplitQuadricLinearSection.linearSection K (equations K rows) ⟶ zeroSpace K :=
  (SplitQuadricLinearSection.sectionIsoPullback K (equations K rows)).hom ≫
    pullback.snd (SplitQuadricLinearSection.linearInclusion K (equations K rows))
      (SplitQuadricLinearSection.quadricInclusion K) ≫ (modelIso K).inv

instance toZero_closed : IsClosedImmersion (toZero K rows) := by
  dsimp only [toZero]
  infer_instance

instance toZeroOver_mono : Mono (Over.mk (toZero K rows)).hom := by
  change Mono (toZero K rows)
  infer_instance

theorem toZero_factors_iff_quotient {T : Scheme.{u}} (t : T ⟶ zeroSpace K) :
    (∃ g : T ⟶ SplitQuadricLinearSection.linearSection K (equations K rows),
      g ≫ toZero K rows = t) ↔
    ∃ a : T ⟶ projectiveSpaceOfModule K (coefficientSpace K ⧸ equations K rows),
      a ≫ AlgebraicGeometry.ProjectiveSpaceOfModule.quotientMap K (coefficientSpace K)
        (equations K rows) = t ≫ symmetricMap K := by
  let e := SplitQuadricLinearSection.sectionIsoPullback K (equations K rows)
  let lin := SplitQuadricLinearSection.linearInclusion K (equations K rows)
  let qi := SplitQuadricLinearSection.quadricInclusion K
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g ≫ e.hom ≫ pullback.fst lin qi, ?_⟩
    have hq : g ≫ e.hom ≫ pullback.snd lin qi = t ≫ (modelIso K).hom := by
      have h := congrArg (fun r => r ≫ (modelIso K).hom) hg
      simpa only [toZero, e, Category.assoc, Iso.inv_hom_id, Category.comp_id] using h
    apply (cancel_mono (SplitQuadricLinearSection.coordinateIso K).hom).mp
    change (g ≫ e.hom ≫ pullback.fst lin qi) ≫ lin =
      (t ≫ symmetricMap K) ≫ (SplitQuadricLinearSection.coordinateIso K).hom
    calc
      _ = (g ≫ e.hom ≫ pullback.snd lin qi) ≫ qi := by
        simpa only [Category.assoc] using congrArg
          (fun r => (g ≫ e.hom) ≫ r) (pullback.condition (f := lin) (g := qi))
      _ = (t ≫ (modelIso K).hom) ≫ qi := congrArg (fun r => r ≫ qi) hq
      _ = t ≫ zeroPolynomialMap K := by
        rw [Category.assoc, modelIso_hom_ambient]
      _ = _ := by rw [Category.assoc, symmetricMap_toPolynomial]
  · rintro ⟨a, ha⟩
    have hc : a ≫ lin = (t ≫ (modelIso K).hom) ≫ qi := by
      change (a ≫ AlgebraicGeometry.ProjectiveSpaceOfModule.quotientMap K
        (coefficientSpace K) (equations K rows)) ≫
          (SplitQuadricLinearSection.coordinateIso K).hom = _
      rw [ha, Category.assoc, symmetricMap_toPolynomial]
      exact congrArg (fun r => t ≫ r) (modelIso_hom_ambient K).symm
    refine ⟨pullback.lift a (t ≫ (modelIso K).hom) hc ≫ e.inv, ?_⟩
    simp only [toZero, e, lin, qi, Category.assoc, Iso.inv_hom_id_assoc,
      pullback.lift_snd_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Full native factorization is simultaneous actual linear vanishing. -/
theorem toZero_factors_iff_sections {T : Scheme.{u}} (t : T ⟶ zeroSpace K) :
    (∃ g : T ⟶ SplitQuadricLinearSection.linearSection K (equations K rows),
      g ≫ toZero K rows = t) ↔
    ∀ j : Fin m, pullbackGlobalSections t (line K) (sectionLinear K (rows j)) = 0 := by
  rw [toZero_factors_iff_quotient]
  rw [ProjectiveFiniteLinearSection.factorsThrough_iff_sections_zero K (coefficientSpace K)
    rows (t ≫ symmetricMap K)]
  apply forall_congr'
  intro j
  exact LagrangianKernelSymmetricSections.pullback_section_zero_iff K t (rows j)

theorem factorization {T : Scheme.{u}} (t : T ⟶ zeroSpace K) :
    FactorsThrough t (cut K rows) ↔ FactorsThrough t (Over.mk (toZero K rows)) := by
  rw [cut, simultaneousCut_factors_iff, List.forall_mem_ofFn_iff]
  exact (toZero_factors_iff_sections K rows t).symm

/-- Actual scheme isomorphism; no model or comparison is supplied. -/
def cutIsoLinearSection : (cut K rows).left ≅
    SplitQuadricLinearSection.linearSection K (equations K rows) :=
  comparisonIso (cut K rows) (Over.mk (toZero K rows))
    (fun _ t => factorization K rows t)

@[reassoc] theorem cutIsoLinearSection_hom_toZero :
    (cutIsoLinearSection K rows).hom ≫ toZero K rows = (cut K rows).hom :=
  comparisonIso_hom_comp (cut K rows) (Over.mk (toZero K rows))
    (fun _ t => factorization K rows t)

end M9Native.LagrangianKernelLinearCuts
