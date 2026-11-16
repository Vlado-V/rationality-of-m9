module

public import M9StacksIntegration.MukaiGeneratedImage
public import M9StacksIntegration.MukaiBundleUniqueness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# An extra section generating the complete four-section image

Codimension one in the actual space of maps O_X→E provides an actual
extra section. Every original section then factors through the literal
generated image, so H0 of that image maps bijectively onto H0(E).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.Preadditive

universe u v

namespace M9Native.MukaiGeneratedImage

section LinearCategory

variable {k : Type*} [Field k] {C : Type u} [Category.{v} C] [Abelian C] [Linear k C]
variable {Q E O : C} (j : Q ⟶ E) [Mono j]

/-- The actual map on sections O→Q→E. -/
def postcomposeSection : (O ⟶ Q) →ₗ[k] (O ⟶ E) where
  toFun x := x ≫ j
  map_add' := fun x y => by simp only [Preadditive.add_comp]
  map_smul' := fun c x => by simp only [Linear.smul_comp, RingHom.id_apply]

theorem postcomposeSection_injective :
    Function.Injective (postcomposeSection (k := k) (O := O) j) :=
  fun _ _ h => (cancel_mono j).mp h

/-- A genuine extra section exists when this actual Hom space has
codimension one. Its sum with the original section image spans all. -/
theorem exists_extra_section
    [Module.Finite k (O ⟶ Q)] [Module.Finite k (O ⟶ E)]
    (hdim : Module.finrank k (O ⟶ E) = Module.finrank k (O ⟶ Q) + 1) :
    ∃ a : O ⟶ E, ∀ b : O ⟶ E,
      ∃ q : O ⟶ Q, ∃ c : k, b = q ≫ j + c • a := by
  let L := postcomposeSection (k := k) (O := O) j
  let W := LinearMap.range L
  have hW : Module.finrank k W = Module.finrank k (O ⟶ Q) :=
    LinearMap.finrank_range_of_inj (postcomposeSection_injective j)
  have hne : W ≠ ⊤ := by
    intro ht
    have htop : Module.finrank k W = Module.finrank k (O ⟶ E) := by
      rw [ht, finrank_top]
    omega
  obtain ⟨a, ha⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hne)
  have ha' : a ∉ W := ha.2
  have hquot : Module.finrank k ((O ⟶ E) ⧸ W) = 1 := by
    have h := Submodule.finrank_quotient_add_finrank W
    omega
  have hspan : W ⊔ Submodule.span k {a} = ⊤ :=
    (Submodule.sup_span_singleton_eq_top_iff ha').mpr hquot
  refine ⟨a, ?_⟩
  intro b
  have hb : b ∈ W ⊔ Submodule.span k {a} := hspan.symm ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp hb
  obtain ⟨q, hq⟩ := hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hy
  refine ⟨q, c, ?_⟩
  change b = L q + c • a
  exact hxy.symm.trans (congrArg₂ (· + ·) hq hc).symm

/-- If every original section is such a sum, it factors through the
literal generated image. -/
theorem postcompose_inclusion_surjective
    (a : O ⟶ E)
    (ha : ∀ b : O ⟶ E, ∃ q : O ⟶ Q, ∃ c : k, b = q ≫ j + c • a) :
    Function.Surjective (postcomposeSection (k := k) (O := O) (inclusion j a)) := by
  intro b
  obtain ⟨q,c,rfl⟩ := ha b
  refine ⟨q ≫ subobjectMap j a + c • sectionMap j a, ?_⟩
  change (q ≫ subobjectMap j a + c • sectionMap j a) ≫ inclusion j a = _
  simp only [Preadditive.add_comp, Linear.smul_comp,
    Category.assoc, subobjectMap_inclusion, sectionMap_inclusion]

end LinearCategory

section Sheaves
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable (Q E : X.Modules) (j : Q ⟶ E) [Mono j]
variable [Module.Finite k (cohomologyOverField k f Q 0)]
variable [Module.Finite k (cohomologyOverField k f E 0)]

/-- The original H0 dimension determines an actual extra section,
and the generated image has exactly the original section space. -/
theorem exists_extra_section_h0
    (hdim : Module.finrank k (cohomologyOverField k f E 0) =
      Module.finrank k (cohomologyOverField k f Q 0) + 1) :
    letI := modulesLinearOverField k f
    ∃ a : MukaiBundle.structureModule X ⟶ E,
      Function.Bijective (postcomposeSection (k := k) (O := MukaiBundle.structureModule X)
        (inclusion j a)) := by
  letI := modulesLinearOverField k f
  let eQ := unitHomLinearEquivCohomologyZero k f Q
  let eE := unitHomLinearEquivCohomologyZero k f E
  letI : Module.Finite k (MukaiBundle.structureModule X ⟶ Q) := eQ.symm.finiteDimensional
  letI : Module.Finite k (MukaiBundle.structureModule X ⟶ E) := eE.symm.finiteDimensional
  obtain ⟨a, ha⟩ := exists_extra_section (k := k) (O := MukaiBundle.structureModule X) j
    (by rw [eQ.finrank_eq, eE.finrank_eq]; exact hdim)
  exact ⟨a, postcomposeSection_injective _, postcompose_inclusion_surjective j a ha⟩

/-- Bijectivity on the actual Hom spaces gives the expected genuine
H0 dimension, through the actual Hom/cohomology equivalence. -/
theorem h0_eq_of_postcompose_bijective
    (a : MukaiBundle.structureModule X ⟶ E)
    (ha : letI := modulesLinearOverField k f
      Function.Bijective (postcomposeSection (k := k) (O := MukaiBundle.structureModule X)
        (inclusion j a))) :
    Module.finrank k (cohomologyOverField k f (generatedImage j a) 0) =
      Module.finrank k (cohomologyOverField k f E 0) := by
  letI := modulesLinearOverField k f
  let e := LinearEquiv.ofBijective
    (postcomposeSection (k := k) (O := MukaiBundle.structureModule X) (inclusion j a)) ha
  exact (unitHomLinearEquivCohomologyZero k f (generatedImage j a)).finrank_eq.symm.trans
    (e.finrank_eq.trans (unitHomLinearEquivCohomologyZero k f E).finrank_eq)

end Sheaves

end M9Native.MukaiGeneratedImage

