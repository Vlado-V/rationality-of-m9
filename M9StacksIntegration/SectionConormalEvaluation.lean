module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf

/-!
# The actual section-evaluation map into an actual ideal sheaf

The source is the genuine native sheaf dual. The map evaluates local
functionals at the original global section, and its factorization is
through the actual kernel ideal sheaf. The affine membership criterion
below is a generic construction interface; the LG specialization must
derive it from its literal zero ideal, not assume a normal-bundle map.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.SectionConormalEvaluation

variable {X : Scheme.{u}} (E : X.Modules) (s : Γ(E, (⊤ : X.Opens)))
  (I : X.IdealSheafData)
  (hmem : ∀ (V : X.affineOpens) (t : Γ(dualSheaf E, (V : X.Opens))),
    evalAt E t (E.presheaf.map (homOfLE le_top).op s) ∈ I.ideal V)

include hmem

/-- Evaluation is a section of the actual ideal sheaf. The gluing is
through its injective inclusion, not through nonunique dual preimages. -/
theorem exists_idealSection_eval (U : X.Opens) (t : Γ(dualSheaf E, U)) :
    ∃ y, Stacks.Divisors.idealSheafSection I y =
      evalAt E t (E.presheaf.map (homOfLE le_top).op s) := by
  refine exists_app_eq_of_locally
    (Stacks.Divisors.idealSheafOfModules I).isSheaf
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).isSheaf
    (kernel.ι (Stacks.Divisors.subschemeStructureHom I)).val
    (fun V => Stacks.Divisors.idealSheafSection_injective I) _ fun y hy => ?_
  obtain ⟨-, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
  refine ⟨W, hWU, hyW, ?_⟩
  obtain ⟨z, hz⟩ := (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection I ⟨W, hW⟩ _).1
    (hmem ⟨W, hW⟩ ((dualSheaf E).presheaf.map (homOfLE hWU).op t))
  exact ⟨z, hz.trans (evalAt_res_top E s hWU t)⟩

/-- Evaluation at the original section is killed by the actual
closed-subscheme structure-sheaf map. -/
theorem eval_comp_structure_zero :
    (dualEvalHom E s : dualModule E ⟶
      SheafOfModules.unit (structureSheafRing X.toRingedSpace)) ≫
        Stacks.Divisors.subschemeStructureHom I = 0 := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun t => ?_))
  change (Stacks.Divisors.subschemeStructureHom I).val.app U
    (Scheme.Modules.Hom.app (dualEvalHom E s) U.unop t) = 0
  obtain ⟨y, hy⟩ := exists_idealSection_eval E s I hmem U.unop t
  exact (congrArg (fun r : Γ(X, U.unop) =>
      (Stacks.Divisors.subschemeStructureHom I).val.app U r) hy).symm.trans
    (Stacks.Divisors.subschemeι_app_idealSheafSection I y)

/-- Actual kernel factorization of actual evaluation. -/
def evaluationIdealMap : dualModule E ⟶ Stacks.Divisors.idealSheafOfModules I :=
  kernel.lift (Stacks.Divisors.subschemeStructureHom I) (dualEvalHom E s)
    (eval_comp_structure_zero E s I hmem)

/-- The factorization retains literal original evaluation on sections. -/
theorem evaluationIdealMap_eval (U : X.Opens) (t : Γ(dualSheaf E, U)) :
    Stacks.Divisors.idealSheafSection I
      ((evaluationIdealMap E s I hmem).val.app (op U) t) =
        evalAt E t (E.presheaf.map (homOfLE le_top).op s) :=
  congrArg (fun φ : dualModule E ⟶ _ => φ.val.app (op U) t)
    (kernel.lift_ι (Stacks.Divisors.subschemeStructureHom I) (dualEvalHom E s)
      (eval_comp_structure_zero E s I hmem))

/-- The same genuine map in the canonical category of scheme modules. -/
def evaluationIdealModuleMap : dualSheaf E ⟶ idealSheafModule I :=
  evaluationIdealMap E s I hmem

theorem evaluationIdealModuleMap_eval (U : X.Opens) (t : Γ(dualSheaf E, U)) :
    Stacks.Divisors.idealSheafSection I
      (Scheme.Modules.Hom.app (evaluationIdealModuleMap E s I hmem) U t) =
        evalAt E t (E.presheaf.map (homOfLE le_top).op s) :=
  evaluationIdealMap_eval E s I hmem U t

end M9Native.SectionConormalEvaluation
