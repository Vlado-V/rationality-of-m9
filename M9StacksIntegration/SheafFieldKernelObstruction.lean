module

public import M9.KernelRankThreeIncidence
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankSections
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Actual sheaf-field fibers and the rank-three kernel obstruction

The actual sections of a native rank-`r` locally free sheaf on `Spec K`
form an actual `r`-dimensional `K`-vector space. Consequently, restricting
an actual sheaf map with at most two-dimensional kernel on sections to
an actual injected rank-three sheaf is nonzero. No fiber dimension or
section-space identification is supplied as an extra input.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.SheafFieldKernelObstruction

theorem finite_and_finrank_sections (K : Type u) [Field K]
    (E : (Spec (.of K)).Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] :
    Module.Finite K (moduleSpecΓFunctor.obj E) ∧
      Module.finrank K (moduleSpecΓFunctor.obj E) = r := by
  let : SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    (inferInstance : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r).isFiniteLocallyFree
  let : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hfrom : IsIso E.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent E
  have hE := Scheme.Modules.isFiniteLocallyFreeOfRank_of_sheaf E r
  have htilde := Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso
    (@asIso _ _ _ _ E.fromTildeΓ hfrom).symm hE
  have hM := (tilde_isFiniteLocallyFreeOfRank_iff K (moduleSpecΓFunctor.obj E) r).mp htilde
  exact ⟨hM.finite, hM.finrank_eq⟩

/-- The actual native field-fiber obstruction, in the sheaf category. -/
theorem comp_ne_zero_of_kernel_finrank_le_two
    (K : Type u) [Field K] {A T B : (Spec (.of K)).Modules}
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} A 10]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T 3]
    (i : T ⟶ A) [Mono i] (v : A ⟶ B)
    (hker : Module.finrank K (LinearMap.ker (moduleSpecΓFunctor.map v).hom) ≤ 2) :
    i ≫ v ≠ 0 := by
  let : Module.Finite K (moduleSpecΓFunctor.obj A) := (finite_and_finrank_sections K A 10).1
  have hT := finite_and_finrank_sections K T 3
  let : Module.Finite K (moduleSpecΓFunctor.obj T) := hT.1
  let : (moduleSpecΓFunctor (R := .of K)).IsRightAdjoint :=
    (tilde.adjunction (R := .of K)).isRightAdjoint
  have hi : Function.Injective (moduleSpecΓFunctor.map i).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hne := M9.KernelRankThreeIncidence.restriction_ne_zero
    (moduleSpecΓFunctor.map v).hom hker (moduleSpecΓFunctor.map i).hom hi hT.2
  intro hz
  apply hne
  have hΓ := congrArg (fun a => moduleSpecΓFunctor.map a) hz
  rw [Functor.map_comp, Functor.map_zero] at hΓ
  exact congrArg ModuleCat.Hom.hom hΓ

end M9Native.SheafFieldKernelObstruction
