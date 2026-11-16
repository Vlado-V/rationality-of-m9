module

public import M9StacksIntegration.ProjectiveQuadraticCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! Actual finite closed subschemes have no more structural H0 than
the original finite scheme. The genuine affine ring restriction is
surjective; the original structural field actions are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory

universe u

namespace M9Native.FiniteClosedSectionH0

variable (K : Type u) [Field K]

/-- Degree-zero structural cohomology is the actual ring of functions,
with the field acting through the ORIGINAL structure morphism. -/
theorem structureH0_finrank_eq_functions {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) :
    letI : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
    Module.finrank K (structureSheafCohomology f 0) = Module.finrank K Γ(X, ⊤) := by
  letI : Algebra K Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop).hom.toAlgebra
  exact (structureSheafCohomologyIsoCohomologyOverField K f 0).toLinearEquiv.finrank_eq.trans
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections K f)

/-- A genuine closed immersion into a scheme finite over the field
gives the actual H0 length inequality, including all nilpotents. -/
theorem h0_le_of_closedImmersion {X Y : Scheme.{u}}
    (qX : X ⟶ Spec (.of K)) (qY : Y ⟶ Spec (.of K))
    [IsFinite qY] (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ qY = qX) :
    Module.finrank K (structureSheafCohomology qX 0) ≤
      Module.finrank K (structureSheafCohomology qY 0) := by
  letI : IsAffine Y := isAffine_of_isAffineHom qY
  let κX : K →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ qX.appTop).hom
  let κY : K →+* Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ qY.appTop).hom
  letI : Algebra K Γ(X, ⊤) := κX.toAlgebra
  letI : Algebra K Γ(Y, ⊤) := κY.toAlgebra
  have hκ : i.appTop.hom.comp κY = κX := by
    have hcat : ((Scheme.ΓSpecIso (.of K)).inv ≫ qY.appTop) ≫ i.appTop =
        (Scheme.ΓSpecIso (.of K)).inv ≫ qX.appTop := by
      rw [Category.assoc, ← Scheme.Hom.comp_appTop, hi]
    exact congrArg (fun f => f.hom) hcat
  let g : Γ(Y, ⊤) →ₐ[K] Γ(X, ⊤) :=
    { i.appTop.hom with
      commutes' := fun a => RingHom.congr_fun hκ a }
  letI : Module.Finite K Γ(Y, ⊤) :=
    qY.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have hg : Function.Surjective g := (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
  have hdim := LinearMap.finrank_le_finrank_of_surjective (f := g.toLinearMap) hg
  rw [structureH0_finrank_eq_functions K qX, structureH0_finrank_eq_functions K qY]
  exact hdim

/-- The inclusion is the ORIGINAL inclusion between the actual ideal
subschemes; the order hypothesis is ideal containment, not a length bound. -/
theorem h0_le_of_ideal_le {X : Scheme.{u}} (q : X ⟶ Spec (.of K))
    (I J : X.IdealSheafData) (hIJ : I ≤ J) [IsFinite (I.subschemeι ≫ q)] :
    Module.finrank K (structureSheafCohomology (J.subschemeι ≫ q) 0) ≤
      Module.finrank K (structureSheafCohomology (I.subschemeι ≫ q) 0) := by
  apply h0_le_of_closedImmersion K (J.subschemeι ≫ q) (I.subschemeι ≫ q)
    (Scheme.IdealSheafData.inclusion hIJ)
  rw [← Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι]

end M9Native.FiniteClosedSectionH0
