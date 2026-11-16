module

public import M9StacksIntegration.CohomologyRestriction
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom

/-!
# The native duality criterion for surjectivity of restriction

For a proper curve, naturality of the original Serre-duality isomorphism
turns extension of maps into the actual dualizing sheaf into injectivity on
`H¹`. The native long exact sequence then proves surjectivity on `H⁰`.

For the canonical degree-two application, the remaining geometric input is
that every map `Ω I_Z ⟶ Ω` extends across the inclusion `Ω I_Z ⟶ Ω`.
This is not assumed as a classification theorem: it must be deduced from
the actual tensor/Hom identification with `H⁰(O(Z))` and the no-pencil bound.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9StacksIntegration.CanonicalRestrictionDuality

open CategoryTheory AlgebraicGeometry
open Stacks.Duality

/-- A nonzero map spanning a one-dimensional Hom space allows every map
with the same source and target to extend as a scalar endomorphism. -/
theorem surjective_precomp_of_hom_finrank_eq_one
    {k C : Type*} [Field k] [Category* C] [Preadditive C] [Linear k C]
    {F G : C} (g : F ⟶ G) (hg : g ≠ 0) (hline : Module.finrank k (F ⟶ G) = 1) :
    ∀ β : F ⟶ G, ∃ α : G ⟶ G, g ≫ α = β := by
  intro β
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' g hg).mp hline β
  refine ⟨c • 𝟙 G, ?_⟩
  simpa only [Linear.comp_smul, Category.comp_id] using hc

/-- Monicity and a one-dimensional Hom space already ensure that the
spanning inclusion is nonzero. No extra geometric nonvanishing hypothesis
is required. -/
theorem surjective_precomp_of_mono_of_hom_finrank_eq_one
    {k C : Type*} [Field k] [Category* C] [Preadditive C] [Linear k C]
    {F G : C} (g : F ⟶ G) [Mono g] (hline : Module.finrank k (F ⟶ G) = 1) :
    ∀ β : F ⟶ G, ∃ α : G ⟶ G, g ≫ α = β := by
  apply surjective_precomp_of_hom_finrank_eq_one (k := k) g
  · intro hg
    have hF : CategoryTheory.Limits.IsZero F :=
      CategoryTheory.Limits.IsZero.of_mono_eq_zero g hg
    let : Subsingleton (F ⟶ G) := ⟨hF.eq_of_src⟩
    have hzero : Module.finrank k (F ⟶ G) = 0 := Module.finrank_zero_of_subsingleton
    omega
  · exact hline

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1)

include hdim

/-- Natural Serre duality for the original sheaves: extension of every map
into the native dualizing sheaf forces injectivity of the original `H¹` map. -/
theorem injective_cohomology_one_of_surjective_precomp
    {F G : X.Modules} (g : F ⟶ G) (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent)
    (hext : ∀ β : F ⟶ dualizingSheafOverField f,
      ∃ α : G ⟶ dualizingSheafOverField f, g ≫ α = β) :
    Function.Injective (cohomologyOverFieldMap k f g 1) := by
  let := modulesLinearOverField k f
  let eF := homDualizingSheafLinearEquiv f hdim F hF
  let eG := homDualizingSheafLinearEquiv f hdim G hG
  intro x y hxy
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k (x - y)).mp
  intro l
  obtain ⟨α, hα⟩ := hext (eF.symm l)
  have hn : eF (g ≫ α) = (eG α).comp (cohomologyOverFieldMap k f g 1).hom := by
    exact congrArg ModuleCat.Hom.hom
      (homDualizingSheafAddEquiv_naturality f hdim hF hG g α)
  rw [hα, LinearEquiv.apply_symm_apply] at hn
  rw [hn, LinearMap.comp_apply, map_sub, hxy, sub_self, map_zero]

/-- The native `H¹` map of a nonzero map into the actual dualizing sheaf is
injective as soon as the actual Hom space is one-dimensional. -/
theorem injective_cohomology_one_of_hom_finrank_eq_one
    {F : X.Modules} (g : F ⟶ dualizingSheafOverField f)
    (hF : F.IsQuasicoherent) (hω : (dualizingSheafOverField f).IsQuasicoherent)
    (hg : g ≠ 0)
    (hline : letI := modulesLinearOverField k f
      Module.finrank k (F ⟶ dualizingSheafOverField f) = 1) :
    Function.Injective (cohomologyOverFieldMap k f g 1) := by
  let := modulesLinearOverField k f
  exact injective_cohomology_one_of_surjective_precomp f hdim g hF hω
    (surjective_precomp_of_hom_finrank_eq_one (k := k) g hg hline)

/-- The actual ideal inclusion is already monic, so the dimension-one Hom
bound alone suffices to prove injectivity on native first cohomology. -/
theorem injective_cohomology_one_of_mono_of_hom_finrank_eq_one
    {F : X.Modules} (g : F ⟶ dualizingSheafOverField f) [Mono g]
    (hF : F.IsQuasicoherent) (hω : (dualizingSheafOverField f).IsQuasicoherent)
    (hline : letI := modulesLinearOverField k f
      Module.finrank k (F ⟶ dualizingSheafOverField f) = 1) :
    Function.Injective (cohomologyOverFieldMap k f g 1) := by
  let := modulesLinearOverField k f
  exact injective_cohomology_one_of_surjective_precomp f hdim g hF hω
    (surjective_precomp_of_mono_of_hom_finrank_eq_one (k := k) g hline)

/-- The original restriction map on global cohomology is surjective when
maps from its ideal twist into the native dualizing sheaf extend. -/
theorem surjective_cohomology_zero_of_surjective_precomp
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (hF : S.X₁.IsQuasicoherent) (hG : S.X₂.IsQuasicoherent)
    (hext : ∀ β : S.X₁ ⟶ dualizingSheafOverField f,
      ∃ α : S.X₂ ⟶ dualizingSheafOverField f, S.f ≫ α = β) :
    Function.Surjective (cohomologyOverFieldMap k f S.g 0) :=
  (CohomologyRestriction.surjective_cohomologyMap_iff_injective_successor f hS 0).mpr
    (injective_cohomology_one_of_surjective_precomp f hdim S.f hF hG hext)

end M9StacksIntegration.CanonicalRestrictionDuality
