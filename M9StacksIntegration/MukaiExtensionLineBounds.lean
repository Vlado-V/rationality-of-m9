module

public import M9StacksIntegration.MukaiFilteredNoPencilLine
public import M9StacksIntegration.MukaiNetFromNoSeven
public import M9StacksIntegration.MukaiSaturationSections

/-!
# Actual line bounds in Mukai's nonsplit extension

The original generated degree-two/degree-six extension supplies the
no-pencil-line theorem for its middle sheaf Q. In a genuinely nonsplit
extension of a degree-eight line by this very Q, every nonzero line map
with two sections has degree below eight. Absence of a degree-seven net
therefore bounds its section space by two. In particular the prescribed
saturation of an independent triple's original evaluation image is not
invertible. No semi-irreducibility premise is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiExtensionLineBounds

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)
variable (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
variable (S : ShortComplex X.Modules) (hS : S.ShortExact)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
variable [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
variable (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
variable (hA : invertibleCurveDegree k f hdim S.X₁ = 2)
variable (hB : invertibleCurveDegree k f hdim S.X₃ = 6)
variable (E α : X.Modules)
variable [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 α]
variable (i : S.X₂ ⟶ E) (p : E ⟶ α) (w : i ≫ p = 0)
variable (hT : (ShortComplex.mk i p w).ShortExact)
variable (hnonsplit : ∀ t : α ⟶ E, t ≫ p ≠ 𝟙 _)
variable (hα : invertibleCurveDegree k f hdim α = 8)

include hnp hS hgen hA hB hT hnonsplit hα

/-- Every original nonzero line map with two sections has degree
strictly below eight, using the actual two original exact sequences. -/
theorem line_degree_lt_eight
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : 2 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (j : L ⟶ E) (hj : j ≠ 0) :
    invertibleCurveDegree k f hdim L < 8 := by
  have hQ : ∀ a : L ⟶ S.X₂, a = 0 :=
    MukaiFilteredNoPencilLine.hom_eq_zero_of_two_sections_of_degrees_two_six
      k f hdim hnp S hS hgen hA hB L hL
  let : Subsingleton (L ⟶ S.X₂) := ⟨fun a b => (hQ a).trans (hQ b).symm⟩
  have hlt := MukaiNonsplitLineExclusion.line_degree_lt_of_nonsplit
    k f hdim (ShortComplex.mk i p w) hT hnonsplit L j hj
  simpa only [hα] using hlt

variable (hn : ¬ Nonempty (LinearSeries k f hdim 7 2))

include hn

/-- A line mapping nontrivially into the original nonsplit extension
and possessing two sections has exactly two sections. -/
theorem h0_eq_two_of_nonzero_line_map
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : 2 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (j : L ⟶ E) (hj : j ≠ 0) :
    Module.finrank k (cohomologyOverField k f L 0) = 2 := by
  have hlt := line_degree_lt_eight k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα
    L hL j hj
  exact le_antisymm (MukaiNetFromNoSeven.h0_le_two_of_degree_lt_eight f hdim hn L hlt) hL

/-- There is no original nonzero line map with three sections into the
nonsplit extension; the degree lower bound is derived from an actual net. -/
theorem hom_eq_zero_of_three_sections
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : 3 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (j : L ⟶ E) : j = 0 := by
  by_contra hj
  have hlt := line_degree_lt_eight k f hdim hnp S hS hgen hA hB E α i p w hT hnonsplit hα
    L (by omega) j hj
  exact (not_le_of_gt hlt) (MukaiNetFromNoSeven.eight_le_degree_of_three_sections f hdim hn L hL)

/-- The actual prescribed saturation of an independent triple is not
a line bundle in the original nonsplit extension. -/
theorem evaluation_saturation_not_invertible
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} E]
    [FiniteDimensional k (cohomologyOverField k f E 0)]
    (s : Fin 3 → cohomologyOverField k f E 0) (hs : LinearIndependent k s) :
    letI : E.IsQuasicoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    letI : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
      MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
    ¬ SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MukaiEvaluationSaturation.saturation (MukaiSemiIrreducible.evaluation k f E s)) := by
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  let : (cokernel (MukaiSemiIrreducible.evaluation k f E s)).IsQuasicoherent :=
    MukaiSaturationSections.evaluation_cokernel_isQuasicoherent k f E s
  let φ := MukaiSemiIrreducible.evaluation k f E s
  intro hline
  let := hline
  have h0 := MukaiSaturationSections.evaluation_saturation_h0_lower_bound k f E s hs
  have hj := hom_eq_zero_of_three_sections k f hdim hnp S hS hgen hA hB E α i p w hT
    hnonsplit hα hn (MukaiEvaluationSaturation.saturation φ) h0
    (MukaiEvaluationSaturation.inclusion φ)
  have hid : 𝟙 (MukaiEvaluationSaturation.saturation φ) = 0 := by
    apply (cancel_mono (MukaiEvaluationSaturation.inclusion φ)).mp
    simp only [Category.id_comp,zero_comp,hj]
  have hzero : IsZero (MukaiEvaluationSaturation.saturation φ) :=
    (IsZero.iff_id_eq_zero _).mpr hid
  let : (cohomologyOverFieldFunctor k f 0).Additive := by
    dsimp [cohomologyOverFieldFunctor]
    infer_instance
  have hHZ := (cohomologyOverFieldFunctor k f 0).map_isZero hzero
  let : Subsingleton (cohomologyOverField k f (MukaiEvaluationSaturation.saturation φ) 0) :=
    ModuleCat.subsingleton_of_isZero hHZ
  have hz : Module.finrank k
      (cohomologyOverField k f (MukaiEvaluationSaturation.saturation φ) 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  change 3 ≤ Module.finrank k
    (cohomologyOverField k f (MukaiEvaluationSaturation.saturation φ) 0) at h0
  rw [hz] at h0
  omega

end M9Native.MukaiExtensionLineBounds
