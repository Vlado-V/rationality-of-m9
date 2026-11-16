module

public import M9StacksIntegration.LagrangianRegularEquations
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Localization

/-!
# The original three LG chart equations generate regular stalk kernels

The actual affine quotient immersion is used. Its original stalk kernel
is the localized actual symmetry ideal, and the actual three original
equations remain weakly regular under this flat localization. Properness
of the actual stalk kernel gives regularity. No codimension or local
regularity conclusion is an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.LagrangianDegree

open M9Native.LagrangianMatrixChart RingTheory.Sequence

variable (K : Type u) [Field K]

abbrev chartStalk (z : symmetryScheme K) :=
  (Spec (.of (MatrixRing K))).presheaf.stalk (symmetryInclusion K z)

/-- The actual original coordinate-ring map to the actual chart stalk. -/
def chartGerm (z : symmetryScheme K) : MatrixRing K →+* chartStalk K z :=
  ((Spec (.of (MatrixRing K))).presheaf.germ ⊤ (symmetryInclusion K z)
    (by trivial)).hom.comp (Scheme.ΓSpecIso (.of (MatrixRing K))).inv.hom

theorem chartGerm_flat (z : symmetryScheme K) : (chartGerm K z).Flat := by
  let X := Spec (.of (MatrixRing K))
  let x : X := symmetryInclusion K z
  letI : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, by trivial⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, by trivial⟩).asIdeal :=
    (isAffineOpen_top X).isLocalization_stalk ⟨x, by trivial⟩
  have hg : (X.presheaf.germ ⊤ x (by trivial)).hom.Flat := by
    change Module.Flat Γ(X, ⊤) (X.presheaf.stalk x)
    exact IsLocalization.flat (X.presheaf.stalk x)
      ((isAffineOpen_top X).primeIdealOf ⟨x, Set.mem_univ x⟩).asIdeal.primeCompl
  have he : (Scheme.ΓSpecIso (.of (MatrixRing K))).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (MatrixRing K))).inv)
  exact he.comp hg

def chartRegularSequence (z : symmetryScheme K) : List (chartStalk K z) :=
  List.ofFn (fun i : Fin 3 => chartGerm K z (threeEquations K i))

@[simp] theorem chartRegularSequence_length (z : symmetryScheme K) :
    (chartRegularSequence K z).length = 3 := by
  simp [chartRegularSequence]

theorem chartRegularSequence_kernel (z : symmetryScheme K) :
    Ideal.ofList (chartRegularSequence K z) =
      RingHom.ker ((symmetryInclusion K).stalkMap z).hom := by
  let X := Spec (.of (MatrixRing K))
  let j := symmetryInclusion K
  have hsurj : Function.Surjective (j.appLE ⊤ (j ⁻¹ᵁ ⊤) le_rfl).hom := by
    rw [Scheme.Hom.appLE_eq_app]
    exact j.app_surjective ⊤ (isAffineOpen_top X)
  have hker := Stacks.Flatness.ker_stalkMap_eq_map_germ j (isAffineOpen_top X)
    ((isAffineOpen_top X).preimage j) le_rfl (show z ∈ j ⁻¹ᵁ ⊤ by trivial)
    (show j z ∈ (⊤ : X.Opens) by trivial) hsurj
  rw [Scheme.Hom.appLE_eq_app] at hker
  change RingHom.ker ((symmetryInclusion K).stalkMap z).hom =
    (RingHom.ker (symmetryInclusion K).appTop.hom).map
      (X.presheaf.germ ⊤ (j z) (by trivial)).hom at hker
  rw [symmetryInclusion_ker_appTop, Ideal.map_map] at hker
  have hseq : chartRegularSequence K z =
      (List.ofFn (threeEquations K)).map (chartGerm K z) := by
    simp only [chartRegularSequence, List.map_ofFn, Function.comp_def]
  rw [hseq, ← Ideal.map_ofList, ofList_threeEquations]
  exact hker.symm

theorem chartRegularSequence_isRegular (z : symmetryScheme K) :
    IsRegular (chartStalk K z) (chartRegularSequence K z) := by
  letI : Algebra (MatrixRing K) (chartStalk K z) := (chartGerm K z).toAlgebra
  letI : Module.Flat (MatrixRing K) (chartStalk K z) := chartGerm_flat K z
  have hweak : IsWeaklyRegular (chartStalk K z) (chartRegularSequence K z) :=
    threeEquations_flat_isWeaklyRegular K (chartStalk K z)
  refine ⟨hweak, ?_⟩
  intro htop
  have heq : Ideal.ofList (chartRegularSequence K z) = ⊤ := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using htop.symm
  rw [chartRegularSequence_kernel] at heq
  exact RingHom.ker_ne_top ((symmetryInclusion K).stalkMap z).hom heq

theorem symmetryInclusion_stalk_regular_three (z : symmetryScheme K) :
    ∃ rs : List (chartStalk K z), rs.length = 3 ∧
      IsRegular (chartStalk K z) rs ∧
      Ideal.ofList rs = RingHom.ker ((symmetryInclusion K).stalkMap z).hom :=
  ⟨chartRegularSequence K z, chartRegularSequence_length K z,
    chartRegularSequence_isRegular K z, chartRegularSequence_kernel K z⟩

end M9Native.LagrangianDegree
