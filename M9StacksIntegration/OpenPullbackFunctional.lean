module

public import M9StacksIntegration.LagrangianLocalFunctionalEquiv
public import M9StacksIntegration.SpecFieldPullbackSections
public import M9StacksIntegration.LagrangianFixedEquationRows

/-!
# Actual local dual functionals of an actual open-pullback frame

The canonical restriction/pullback comparison and the original local
functional equivalence construct a section of the original dual sheaf.
Its value is the original actual pullback value, and a genuine line
frame gives an actual local section paired to one. No functional,
normalization, or nonzero-fibre premise is supplied.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.OpenPullbackFunctional

open LagrangianDualCoefficients LagrangianLocalFunctionalEquiv LagrangianLocalIsotropy
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}} (Q : X.Modules) (U : X.Opens)

/-- The original local dual section induced by an actual open-pullback functional. -/
def ofPullback (a : (Scheme.Modules.pullback U.ι).obj Q ⟶
    SheafOfModules.unit U.toScheme.ringCatSheaf) : Γ(dualSheaf Q,U) :=
  (localFunctionalEquiv Q U).symm
    (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).hom ≫ a)

/-- The defining original local functional retains the literal canonical comparison. -/
theorem localFunctional_ofPullback (a : (Scheme.Modules.pullback U.ι).obj Q ⟶
    SheafOfModules.unit U.toScheme.ringCatSheaf) :
    localFunctional Q U (ofPullback Q U a) =
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).hom ≫ a :=
  (localFunctionalEquiv Q U).apply_symm_apply _

/-- Canonical pullback, canonical restriction, and original local sections agree literally. -/
theorem openSections_restrict_inv_pullback (s : Γ(Q,⊤)) :
    (openSectionsIso Q U).hom
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).inv.app ⊤
        (pullbackGlobalSections U.ι Q s)) =
      Q.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s := by
  have h := Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection U.ι Q
    ⊤ ⊤ (show ⊤ ≤ U.ι ⁻¹ᵁ ⊤ by simp) (show U.ι ''ᵁ ⊤ ≤ ⊤ from le_top) s
  rw [Scheme.Modules.pullbackSection_top] at h
  have hp := LagrangianFixedEquationRows.pullbackGlobalSections_eq_unit U.ι Q s
  have hn := (congrArg (fun z =>
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q).inv.app ⊤ z) hp).trans h
  rw [openSectionsIso_hom_apply, hn]
  change Q.presheaf.map (eqToHom U.ι_image_top.symm).op
      (Q.presheaf.map (homOfLE le_top).op s) = _
  rw [← ConcreteCategory.comp_apply, ← Q.presheaf.map_comp]
  rfl

/-- Evaluation of the constructed original dual section is the actual framed pullback value. -/
theorem eval_ofPullback (a : (Scheme.Modules.pullback U.ι).obj Q ⟶
    SheafOfModules.unit U.toScheme.ringCatSheaf) (s : Γ(Q,⊤)) :
    evalAt Q (ofPullback Q U a)
        (Q.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op s) =
      (Scheme.Opens.topIso U).hom (a.app ⊤ (pullbackGlobalSections U.ι Q s)) := by
  let A := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app Q
  let v := A.inv.app ⊤ (pullbackGlobalSections U.ι Q s)
  have h := localFunctional_top_evaluation Q U (ofPullback Q U a) v
  have he : (localFunctional Q U (ofPullback Q U a)).app ⊤ v =
      a.app ⊤ (pullbackGlobalSections U.ι Q s) := by
    rw [localFunctional_ofPullback]
    change a.app ⊤ (A.hom.app ⊤ (A.inv.app ⊤ (pullbackGlobalSections U.ι Q s))) = _
    exact congrArg (a.app ⊤)
      (congrArg (fun t => t.app ⊤ (pullbackGlobalSections U.ι Q s)) A.inv_hom_id)
  have hv := openSections_restrict_inv_pullback Q U s
  exact (congrArg (evalAt Q (ofPullback Q U a)) hv).symm.trans
    (h.symm.trans (congrArg (fun z => (Scheme.Opens.topIso U).hom z) he))

/-- A genuine line frame gives an invertible original local functional. -/
theorem localFunctional_ofPullback_isIso
    (e : (Scheme.Modules.pullback U.ι).obj Q ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    IsIso (localFunctional Q U (ofPullback Q U e.hom)) := by
  rw [localFunctional_ofPullback]
  infer_instance

/-- Thus the constructed original dual section pairs with an actual local section to one. -/
theorem exists_eval_ofPullback_eq_one
    (e : (Scheme.Modules.pullback U.ι).obj Q ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    ∃ m : Γ(Q,U), evalAt Q (ofPullback Q U e.hom) m = 1 := by
  letI := localFunctional_ofPullback_isIso Q U e
  let v := (asIso (localFunctional Q U (ofPullback Q U e.hom))).inv.app ⊤
    (1 : Γ(U.toScheme,⊤))
  refine ⟨(openSectionsIso Q U).hom v, ?_⟩
  rw [← localFunctional_top_evaluation]
  have hv : (localFunctional Q U (ofPullback Q U e.hom)).app ⊤ v =
      (1 : Γ(U.toScheme,⊤)) :=
    congrArg (fun t => t.app ⊤ (1 : Γ(U.toScheme,⊤)))
      (asIso (localFunctional Q U (ofPullback Q U e.hom))).inv_hom_id
  rw [hv, map_one]

end M9Native.OpenPullbackFunctional
