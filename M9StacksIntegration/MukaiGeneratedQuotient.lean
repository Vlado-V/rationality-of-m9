module

public import M9StacksIntegration.MukaiBundleUniqueness
public import M9StacksIntegration.MukaiSemiIrreducible
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Factoring a generated line through its one-dimensional section space

The maps below are the actual native sheaf morphisms. The finrank bound
is used to factor a given epimorphism from a free sheaf through one map
from the actual structure sheaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiGeneratedQuotient

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

theorem exists_epi_from_unit_of_h0_le_one
    (L : X.Modules) (I : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ L) [Epi e]
    [Module.Finite k (cohomologyOverField k f L 0)]
    (h : Module.finrank k (cohomologyOverField k f L 0) ≤ 1) :
    ∃ a : MukaiBundle.structureModule X ⟶ L, Epi a := by
  letI := modulesLinearOverField k f
  let E := unitHomLinearEquivCohomologyZero k f L
  letI : Module.Finite k (MukaiBundle.structureModule X ⟶ L) := E.symm.finiteDimensional
  have hdim : Module.finrank k (MukaiBundle.structureModule X ⟶ L) ≤ 1 := by
    rw [E.finrank_eq]
    exact h
  obtain ⟨a, ha⟩ := (finrank_le_one_iff (K := k)
    (V := MukaiBundle.structureModule X ⟶ L)).mp hdim
  choose c hc using fun i : I => ha (SheafOfModules.ιFree i ≫ e)
  let g : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ MukaiBundle.structureModule X :=
    Sigma.desc (fun i => c i • 𝟙 (MukaiBundle.structureModule X))
  have hfac : g ≫ a = e := by
    apply Sigma.hom_ext
    intro i
    simp only [g, Sigma.ι_comp_desc_assoc,
      Linear.smul_comp, Category.id_comp]
    exact hc i
  exact ⟨a, epi_of_epi_fac hfac⟩

/-- A generated invertible quotient has at least two sections when the
original sheaf has no morphism to the structure sheaf. With at most one
section, the actual generating epimorphism factors through an
epimorphism from the structure sheaf. It is then an isomorphism, giving
the forbidden quotient to the structure sheaf. -/
theorem two_le_h0_of_generated_no_unit_hom
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (E L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Module.Finite k (cohomologyOverField k f L 0)]
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (q : E ⟶ L) [Epi q]
    (hvan : ∀ b : E ⟶ MukaiBundle.structureModule X, b = 0) :
    2 ≤ Module.finrank k (cohomologyOverField k f L 0) := by
  by_contra h
  have hle : Module.finrank k (cohomologyOverField k f L 0) ≤ 1 := by omega
  obtain ⟨g⟩ := hgen
  obtain ⟨a, ha⟩ := exists_epi_from_unit_of_h0_le_one f L g.I (g.π ≫ q) hle
  letI := ha
  let hO : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MukaiBundle.structureModule X) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (Stacks.SheafOfModules.isInvertible_unit _ _)
  let hLs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL
  letI : IsIso a := @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible
    X.toRingedSpace (MukaiBundle.structureModule X) L a ha hO hLs
  let b : E ⟶ MukaiBundle.structureModule X := q ≫ (asIso a).inv
  letI : Epi b := by dsimp [b]; infer_instance
  have hzero : IsZero (MukaiBundle.structureModule X) := IsZero.of_epi_eq_zero b (hvan b)
  letI : (cohomologyOverFieldFunctor k f 0).Additive := by
    dsimp [cohomologyOverFieldFunctor]
    infer_instance
  have hH : IsZero (cohomologyOverField k f (MukaiBundle.structureModule X) 0) :=
    (cohomologyOverFieldFunctor k f 0).map_isZero hzero
  letI : Subsingleton (cohomologyOverField k f (MukaiBundle.structureModule X) 0) :=
    ModuleCat.subsingleton_of_isZero hH
  have hz : Module.finrank k (cohomologyOverField k f (MukaiBundle.structureModule X) 0) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hone := finrank_cohomologyOverField_unit_zero_eq_one f
  change Module.finrank k (cohomologyOverField k f (MukaiBundle.structureModule X) 0) = 1 at hone
  omega

end M9Native.MukaiGeneratedQuotient

