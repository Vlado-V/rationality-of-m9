module

public import M9StacksIntegration.MukaiEvaluationSaturation

/-!
# The original sections inside their native saturation

An actual section of the source of `φ` lifts to the constructed saturated
image. Its image in native zeroth cohomology is exactly the original
section. Applied to evaluation of an independent `r`-tuple this proves
`h⁰(saturation image) ≥ r`, the first dimension assertion of Mukai
Proposition 5.3, without an assumed line/subbundle model.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.MukaiSaturationSections

open MukaiEvaluationSaturation

variable (k : Type u) [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (f : X ⟶ Spec (.of k)) {F E : X.Modules} (φ : F ⟶ E)
variable [(cokernel φ).IsQuasicoherent]

/-- The original image of a genuine source section, in native H0. -/
def imageSectionH0 (s : F.sections) : cohomologyOverField k f E 0 :=
  (cohomologyOverFieldZeroLinearIso k f E).inv
    ((_root_.SheafOfModules.sectionsMap φ s).eval (op ⊤))

/-- The canonical actual lift of a source section into the constructed
saturation, expressed in native H0 through the public linear comparison. -/
def liftedSectionH0 (s : F.sections) : cohomologyOverField k f (saturation φ) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (saturation φ)).inv
    ((_root_.SheafOfModules.sectionsMap (factor φ) s).eval (op ⊤))

/-- The lift maps to the original section under the original inclusion
of sheaves, not an independently chosen vector-space identification. -/
theorem cohomologyMap_liftedSectionH0 (s : F.sections) :
    cohomologyOverFieldMap k f (inclusion φ) 0 (liftedSectionH0 k f φ s) =
      imageSectionH0 k f φ s := by
  apply (ModuleCat.mono_iff_injective (cohomologyOverFieldZeroLinearIso k f E).hom).mp
    inferInstance
  rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap]
  simp only [liftedSectionH0,imageSectionH0,Iso.inv_hom_id_apply]
  exact congrArg (fun t => t.eval (op ⊤)) (sectionsMap_factor_inclusion φ s)

/-- The original inclusion induces an injection of the actual native
spaces of sections, by the actual sheaf cohomology long exact sequence. -/
theorem cohomologyMap_inclusion_injective :
    Function.Injective (cohomologyOverFieldMap k f (inclusion φ) 0) := by
  obtain ⟨_,hinj,_⟩ := exists_cohomologyOverField_longExactSequence k f (sequence_shortExact φ)
  exact hinj

/-- Independent image sections remain independent as actual sections of
the prescribed saturation. -/
theorem liftedSectionH0_linearIndependent {r : ℕ} (s : Fin r → F.sections)
    (h : LinearIndependent k (fun i => imageSectionH0 k f φ (s i))) :
    LinearIndependent k (fun i => liftedSectionH0 k f φ (s i)) := by
  apply LinearIndependent.of_comp (cohomologyOverFieldMap k f (inclusion φ) 0).hom
  change LinearIndependent k (fun i =>
    cohomologyOverFieldMap k f (inclusion φ) 0 (liftedSectionH0 k f φ (s i)))
  simpa only [cohomologyMap_liftedSectionH0] using h

/-- Finite-dimensionality of original H0 descends to the prescribed
saturated subsheaf along its proved native H0 injection. -/
theorem finite_h0_saturation [FiniteDimensional k (cohomologyOverField k f E 0)] :
    FiniteDimensional k (cohomologyOverField k f (saturation φ) 0) :=
  Module.Finite.of_injective (cohomologyOverFieldMap k f (inclusion φ) 0).hom
    (cohomologyMap_inclusion_injective k f φ)

section Evaluation

variable (E : X.Modules) {r : ℕ} (s : Fin r → cohomologyOverField k f E 0)

omit [IsIntegral X] in
/-- Quasi-coherence needed by the saturation construction is derived
for the original evaluation map: its source is genuinely free of finite
rank and its target is the original quasi-coherent sheaf. -/
theorem evaluation_cokernel_isQuasicoherent [E.IsQuasicoherent] :
    (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent := by
  let A : X.Modules := _root_.SheafOfModules.free
    (R := X.ringCatSheaf) (ULift.{u} (Fin r))
  have hA : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A r :=
    SheafOfModules.isFiniteLocallyFreeOfRank_free_of_equiv (ULift.{u} (Fin r)) r Equiv.ulift
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} A := hA.isFiniteLocallyFree
  let : A.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree A
  exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel
    (MukaiSemiIrreducible.evaluation k f E s)

variable [(cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent]

omit [IsIntegral X] [(cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent] in
/-- Each actual free generator of evaluation has exactly the original
native section as its cohomological image. -/
theorem imageSectionH0_evaluation (i : Fin r) :
    imageSectionH0 k f (MukaiSemiIrreducible.evaluation k f E s)
      (_root_.SheafOfModules.freeSection (ULift.up i)) = s i := by
  simp only [imageSectionH0,MukaiSemiIrreducible.evaluation_freeSection,
    MukaiSemiIrreducible.sectionOfH0_eval_top,Iso.hom_inv_id_apply]

/-- The prescribed saturation of the image of an independent native
`r`-tuple has at least `r` actual sections. No rank or saturation equality
is assumed for the generated image. -/
theorem evaluation_saturation_h0_lower_bound
    [FiniteDimensional k (cohomologyOverField k f E 0)] (hs : LinearIndependent k s) :
    r ≤ Module.finrank k
      (cohomologyOverField k f
        (saturation (MukaiSemiIrreducible.evaluation k f E s)) 0) := by
  let φ := MukaiSemiIrreducible.evaluation k f E s
  let := finite_h0_saturation k f φ
  have ht := liftedSectionH0_linearIndependent k f φ
    (fun i : Fin r => _root_.SheafOfModules.freeSection (ULift.up i))
    (by
      have him : (fun i : Fin r => imageSectionH0 k f φ
          (_root_.SheafOfModules.freeSection (ULift.up i))) = s := by
        funext i
        exact imageSectionH0_evaluation k f E s i
      rw [him]
      exact hs)
  simpa only [Fintype.card_fin] using ht.fintype_card_le_finrank

end Evaluation

end M9Native.MukaiSaturationSections
