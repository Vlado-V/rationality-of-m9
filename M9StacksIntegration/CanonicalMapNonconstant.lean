module

public import M9StacksIntegration.ConstantMapPullback
public import M9StacksIntegration.MukaiCanonicalExteriorDegree
public import StacksFrontier.AlgebraicGeometry.CurveFiniteMorphism.Basic

/-!
# A map pulling a line back to the genus-nine canonical line is nonconstant

The canonical degree is calculated from native Serre duality and
Riemann--Roch. The actual line pullback proves canonical invertibility. A constant
map would pull the line back to the actual unit sheaf, which has degree
zero. Properness and the curve dimension then prove actual finiteness
of the original map to any separated target over the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.CanonicalMapNonconstant

open MukaiCanonicalExteriorCohomology

variable {X Y : Scheme.{u}} (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

include hdim

theorem canonical_h1_eq_one
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)] :
    Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) =
      1 := by
  let := modulesLinearOverField k f
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _
  let : (Stacks.Duality.dualizingSheafOverField f).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
      (Stacks.Duality.dualizingSheafOverField f) 1
  let : Module.Finite k
      (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f _ 1
  have h : Module.finrank k ((Stacks.Duality.dualizingSheafOverField f) ⟶
      (Stacks.Duality.dualizingSheafOverField f)) =
      Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) :=
    (Stacks.Duality.homDualizingSheafLinearEquiv f hdim
      (Stacks.Duality.dualizingSheafOverField f)
      (isQuasicoherent_of_isCoherent _)).finrank_eq.trans Subspace.dual_finrank_eq
  exact h.symm.trans (finrank_end_eq_one_of_isInvertible k f _)

theorem canonical_degree
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)] :
    invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) =
      2 * (genus f : ℤ) - 2 := by
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim
    (Stacks.Duality.dualizingSheafOverField f)
  rw [Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim,
    canonical_h1_eq_one k f hdim] at h
  push_cast at h
  linarith

variable (hg : genus f = 9)

include hg

theorem not_constant_of_canonical_line_pullback (g : X ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]
    (e : (Scheme.Modules.pullback g).obj L ≅ Stacks.Duality.dualizingSheafOverField f) :
    ¬ ∃ y : Y, ∀ x : X, g.base x = y := by
  intro hc
  obtain ⟨et⟩ := ConstantMapPullback.nonempty_pullback_line_iso_unit g L hc
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback g).obj L) 1 := isFiniteLocallyFreeOfRank_pullback g L 1
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e inferInstance
  let := Stacks.RingedSpace.isInvertible_of_isFiniteLocallyFreeOfRank_one X.toRingedSpace
    (Stacks.Duality.dualizingSheafOverField f)
  have hcan : invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) = 16 := by
    calc
      _ = 2 * (genus f : ℤ) - 2 :=
        canonical_degree k f hdim
      _ = 16 := by rw [hg]; norm_num
  have htriv := curveDegree_eq_of_iso k f hdim 1 (e.symm ≪≫ et)
  have hunit : curveDegree k f hdim (SheafOfModules.unit X.ringCatSheaf) 1 = 0 := by
    simp only [curveDegree, Nat.cast_one, one_mul, sub_self]
  rw [hunit, ← invertibleCurveDegree_eq_curveDegree] at htriv
  exact (by norm_num : (16 : ℤ) ≠ 0) (hcan.symm.trans htriv)

theorem exists_apply_ne_of_canonical_line_pullback [Nonempty X]
    (g : X ⟶ Y) (L : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]
    (e : (Scheme.Modules.pullback g).obj L ≅ Stacks.Duality.dualizingSheafOverField f) :
    ∃ a b : X, g.base a ≠ g.base b := by
  classical
  by_contra h
  push Not at h
  apply not_constant_of_canonical_line_pullback k f hdim hg g L e
  exact ⟨g.base (Classical.choice inferInstance), fun x => h x _⟩

theorem isFinite_of_canonical_line_pullback [IsCurve k f]
    (p : Y ⟶ Spec (.of k)) [IsSeparated p]
    (g : X ⟶ Y) (hgf : g ≫ p = f) (L : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1]
    (e : (Scheme.Modules.pullback g).obj L ≅ Stacks.Duality.dualizingSheafOverField f) :
    IsFinite g := by
  have : IsProper (g ≫ p) := hgf.symm ▸ inferInstance
  have : IsProper g := IsProper.of_comp g p
  have : IsNoetherian X := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve f
  exact isFinite_of_isProper_of_exists_apply_ne g hdim
    (exists_apply_ne_of_canonical_line_pullback k f hdim hg g L e)

end M9Native.CanonicalMapNonconstant
