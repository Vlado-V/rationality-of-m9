module

public import M9StacksIntegration.ExteriorEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import Mathlib.Logic.Equiv.Fintype

/-!
# An actual zero pair wedge kills the actual triple wedge

This is a ring-theoretic and sheaf-theoretic statement on arbitrary
schemes, including nonreduced schemes. The section proof uses the actual
local-ring stalk exterior comparison; no field-point test is substituted
for equality of the original sections.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Opposite
universe u v
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

namespace M9Native.ExteriorPairZeroTriple

theorem algebraic {R : Type u} [CommRing R] {V : Type v}
    [AddCommGroup V] [Module R V] (s : Fin 3 → V) (e : Fin 2 ↪ Fin 3)
    (he : exteriorPower.ιMulti R 2 (s ∘ e) = 0) :
    exteriorPower.ιMulti R 3 s = 0 := by
  classical
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair
    (fun i : Fin 2 => i.castAdd 1) e (Fin.castAdd_injective 2 1) e.injective
  have hR : ExteriorAlgebra.ιMulti R 2 (s ∘ e) = 0 :=
    congrArg (fun z : ⋀[R]^2 V => (z : ExteriorAlgebra R V)) he
  have hv : s ∘ p = Fin.append (s ∘ e) (fun i : Fin 1 => s (p (Fin.natAdd 2 i))) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Function.comp_apply, Fin.append_left, hp]
    · simp only [Function.comp_apply, Fin.append_right]
  have hz : exteriorPower.ιMulti R 3 (s ∘ p) = 0 := by
    apply Subtype.ext
    change ExteriorAlgebra.ιMulti R 3 (s ∘ p) = 0
    rw [hv]
    exact (ExteriorAlgebra.ιMulti_mul_ιMulti (R := R) (s ∘ e)
      (fun i : Fin 1 => s (p (Fin.natAdd 2 i)))).symm.trans (by rw [hR, zero_mul])
  rw [(exteriorPower.ιMulti R 3).map_congr_perm s p, hz, smul_zero]

/-- A zero wedge of any two selected original sections annihilates the
triple section in the actual native exterior sheaf, over every scheme. -/
theorem sections {X : Scheme.{u}} (E : X.Modules) (s : Fin 3 → Γ(E, ⊤))
    (e : Fin 2 ↪ Fin 3)
    (he : ExteriorEvaluation.sectionComparison E 2 ⊤
      (exteriorPower.ιMulti Γ(X, ⊤) 2 (s ∘ e)) = 0) :
    ExteriorEvaluation.sectionComparison E 3 ⊤
      (exteriorPower.ιMulti Γ(X, ⊤) 3 s) = 0 := by
  refine TopCat.Presheaf.section_ext
    ((AlgebraicGeometry.SheafOfModules.toTopSheaf X.ringCatSheaf).obj
      (Scheme.Modules.exteriorPower E (3 : ℤ))) ⊤ _ _ (fun x hx => ?_)
  apply (ExteriorEvaluation.stalkComparison E 3 x).injective
  change ExteriorEvaluation.stalkComparison E 3 x
      (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (3 : ℤ)).presheaf ⊤ x hx
        (ExteriorEvaluation.sectionComparison E 3 ⊤ (exteriorPower.ιMulti Γ(X, ⊤) 3 s))) =
    ExteriorEvaluation.stalkComparison E 3 x
      (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (3 : ℤ)).presheaf ⊤ x hx 0)
  rw [map_zero, map_zero]
  refine (ExteriorEvaluation.sectionComparison_germ_ιMulti E 3 x ⊤ hx s).trans ?_
  have h := congrArg (fun z => ExteriorEvaluation.stalkComparison E 2 x
    (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (2 : ℤ)).presheaf ⊤ x hx z)) he
  have h2 := (ExteriorEvaluation.sectionComparison_germ_ιMulti E 2 x ⊤ hx (s ∘ e)).symm.trans h
  simp only [map_zero] at h2
  exact algebraic (fun i => TopCat.Presheaf.germ E.presheaf ⊤ x hx (s i)) e h2

end M9Native.ExteriorPairZeroTriple
