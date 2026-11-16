module

public import M9StacksIntegration.UnitSectionPullback
public import M9StacksIntegration.LagrangianAffineDeterminant
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequence
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Picard.CurveLineBundles.RiemannRoch

/-! Actual one-step hyperplane restriction on a proper integral scheme.
The kernel statement is derived from the native regular-section sequence
and the genuine global-constant theorem, before any ladder is considered. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.IntegralHyperplaneRestriction

open LagrangianAffineDeterminant (unitHom_top_one unitHom_top_smul presheaf_map_top_apply)

theorem pullback_zero_iff_unit_composite_zero {X Y : Scheme.{u}} (i : Y ⟶ X)
    (L : X.Modules) (t : Γ(L, ⊤)) :
    pullbackGlobalSections i L t = 0 ↔
      Scheme.Modules.unitHomEquivTop L t ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L = 0 := by
  have he : UnitSectionPullback.unitSection
      (Scheme.Modules.unitHomEquivTop L t ≫
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L) =
      pullbackGlobalSections i L t := by
    change ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L).app ⊤
      ((Scheme.Modules.unitHomEquivTop L t).app ⊤ (1 : Γ(X, ⊤))) = _
    rw [unitHom_top_one]
    exact (ConcreteCategory.congr_hom (pullbackGlobalSections_eq_unit i L) t).symm
  constructor
  · intro ht
    exact UnitSectionPullback.eq_zero_of_unitSection_eq_zero _ (he.trans ht)
  · intro ht
    rw [← he, ht]
    change (0 : X.unitModule ⟶ _).app ⊤ (1 : Γ(X, ⊤)) = 0
    rw [Scheme.Modules.Hom.zero_app]
    rfl

variable {X : Scheme.{u}} [IsIntegral X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- The genuine regular-section sequence lifts a vanishing section
through multiplication by the original nonzero section. -/
theorem exists_function_multiple_of_pullback_zero (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (t : Γ(L, ⊤))
    (ht : pullbackGlobalSections (zeroScheme X L s).subschemeι L t = 0) :
    ∃ a : Γ(X, ⊤), t = a • s := by
  let sf := Scheme.Modules.sectionsTopEquiv L s
  have he : sf.eval (op ⊤) = s := by
    rw [show sf.eval (op ⊤) = (Scheme.Modules.sectionsTopEquiv L s).val (op ⊤) from rfl,
      Scheme.Modules.sectionsTopEquiv_val]
    exact presheaf_map_top_apply L _ s
  have hreg := isRegularSection_of_eval_top_ne_zero L sf (by rwa [he])
  let i := (zeroScheme X L s).subschemeι
  let a := Scheme.Modules.unitHomEquivTop L s
  let b := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app L
  have hseq : ∃ w : a ≫ b = 0, (ShortComplex.mk a b w).ShortExact := by
    have hn := shortExact_zeroScheme_of_isRegularSection X L sf hreg
    dsimp only at hn
    rw [he] at hn
    exact hn
  obtain ⟨w, hS⟩ := hseq
  have hz : Scheme.Modules.unitHomEquivTop L t ≫ b = 0 :=
    (pullback_zero_iff_unit_composite_zero i L t).mp ht
  obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift' hS.fIsKernel
    (Scheme.Modules.unitHomEquivTop L t) hz
  refine ⟨c.app ⊤ (1 : Γ(X, ⊤)), ?_⟩
  have hv := congrArg (fun q : X.unitModule ⟶ L => q.app ⊤ (1 : Γ(X, ⊤))) hc
  change (Scheme.Modules.unitHomEquivTop L s).app ⊤
    (c.app ⊤ (1 : Γ(X, ⊤))) = (Scheme.Modules.unitHomEquivTop L t).app ⊤
      (1 : Γ(X, ⊤)) at hv
  rw [unitHom_top_smul, unitHom_top_one] at hv
  exact hv.symm

section Field
variable (k : Type u) [Field k] [IsAlgClosed k] (f : X ⟶ Spec (.of k)) [IsProper f]

/-- The actual structural map from the original field into global functions. -/
abbrev coefficientMap : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom

/-- Actual global constants turn the actual kernel lift into a scalar multiple. -/
theorem exists_scalar_multiple_of_pullback_zero (s : Γ(L, ⊤)) (hs : s ≠ 0)
    (t : Γ(L, ⊤))
    (ht : pullbackGlobalSections (zeroScheme X L s).subschemeι L t = 0) :
    ∃ c : k, t = coefficientMap k f c • s := by
  obtain ⟨a, ha⟩ := exists_function_multiple_of_pullback_zero L s hs t ht
  let g := (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop
  let : IsIso g := isIso_globalSections_of_isAlgClosed k f
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso g).surjective a
  refine ⟨c, ?_⟩
  change t = g.hom c • s
  rw [hc]
  exact ha

end Field

end M9Native.IntegralHyperplaneRestriction
end
