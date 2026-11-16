module

public import M9.RadicalMapRank
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-! # The intrinsic radical-line map and its actual cofactor charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace M9.RadicalMap

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Actual nine-planes with a one-dimensional intrinsic radical. -/
def RankEightPlane (B : LinearMap.BilinForm K V) :=
  {U : Submodule K V // finrank K U = 9 ∧ finrank K (RadicalFiber.radical B U) = 1}

/-- The radical line is intrinsic, independent of every choice of frame. -/
def radicalPoint (B : LinearMap.BilinForm K V) (U : RankEightPlane B) :
    Projectivization K V :=
  Projectivization.mk'' (RadicalFiber.radical B U.val) U.property.2

@[simp] theorem radicalPoint_submodule (B : LinearMap.BilinForm K V) (U : RankEightPlane B) :
    (radicalPoint B U).submodule = RadicalFiber.radical B U.val :=
  Projectivization.submodule_mk'' _ _

theorem finrank_radical_of_rank_eight (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (hu : LinearIndependent K u) (hr : (gram B u).rank = 8) :
    finrank K (RadicalFiber.radical B (plane u)) = 1 := by
  have he := (Submodule.equivMapOfInjective (frameMap u)
    hu.fintypeLinearCombination_injective (LinearMap.ker (gram B u).mulVecLin)).finrank_eq
  rw [map_kernel_eq_radical B hB u] at he
  rw [← he,finrank_kernel_of_rank_eight B u hr]

/-- An actual independent rank-eight Gram frame lands in the intrinsic domain. -/
def framedPlane (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (u : Fin 9 → V)
    (hu : LinearIndependent K u) (hr : (gram B u).rank = 8) : RankEightPlane B :=
  ⟨plane u,finrank_plane u hu,finrank_radical_of_rank_eight B hB u hu hr⟩

section Cofactor

variable [CharZero K]

/-- On a nonzero cofactor chart the intrinsic map is given by polynomial coordinates. -/
theorem radicalPoint_eq_cofactor (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (hu : LinearIndependent K u) (hr : (gram B u).rank = 8)
    (i j : Fin 9) (hij : (gram B u).adjugate i j ≠ 0) :
    radicalPoint B (framedPlane B hB u hu hr) =
      Projectivization.mk K (radicalVector B u j) (radicalVector_ne_zero B u hu i j hij) := by
  apply Projectivization.submodule_injective
  rw [radicalPoint_submodule,Projectivization.submodule_mk]
  exact radical_eq_span_radicalVector B hB u hr i j hij

/-- Actual nonzero cofactor formulas agree on their overlaps. -/
theorem cofactor_points_eq (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (u : Fin 9 → V) (hu : LinearIndependent K u) (i j k l : Fin 9)
    (hij : (gram B u).adjugate i j ≠ 0) (hkl : (gram B u).adjugate k l ≠ 0) :
    Projectivization.mk K (radicalVector B u j) (radicalVector_ne_zero B u hu i j hij) =
      Projectivization.mk K (radicalVector B u l) (radicalVector_ne_zero B u hu k l hkl) := by
  have hr := rank_eight_of_nonzero_cofactor (gram B u) (gram_transpose B hB u) i j hij
  rw [← radicalPoint_eq_cofactor B hB u hu hr i j hij,
    ← radicalPoint_eq_cofactor B hB u hu hr k l hkl]

end Cofactor

/-- An actual form isometry carries the actual radical to the actual radical. -/
theorem radical_map_isometry (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, B (g x) (g y) = B x y) (U : Submodule K V) :
    (RadicalFiber.radical B U).map g.toLinearMap =
      RadicalFiber.radical B (U.map g.toLinearMap) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    obtain ⟨hxU,hxB⟩ := (RadicalFiber.mem_radical_iff B hB.isRefl U x).mp hx
    apply (RadicalFiber.mem_radical_iff B hB.isRefl _ _).mpr
    refine ⟨⟨x,hxU,rfl⟩,?_⟩
    rintro z ⟨w,hw,rfl⟩
    exact (hg x w).trans (hxB w hw)
  · intro y hy
    obtain ⟨hyU,hyB⟩ := (RadicalFiber.mem_radical_iff B hB.isRefl _ y).mp hy
    obtain ⟨x,hx,rfl⟩ := hyU
    refine ⟨x,?_,rfl⟩
    apply (RadicalFiber.mem_radical_iff B hB.isRefl U x).mpr
    refine ⟨hx,?_⟩
    intro w hw
    exact (hg x w).symm.trans (hyB (g w) ⟨w,hw,rfl⟩)

/-- The natural actual action on the domain of the radical map. -/
def isometryPlane (B : LinearMap.BilinForm K V) (hB : B.IsAlt) (g : V ≃ₗ[K] V)
    (hg : ∀ x y, B (g x) (g y) = B x y) (U : RankEightPlane B) : RankEightPlane B := by
  refine ⟨U.val.map g.toLinearMap,?_,?_⟩
  · rw [g.finrank_map_eq]
    exact U.property.1
  · rw [← radical_map_isometry B hB g hg,g.finrank_map_eq]
    exact U.property.2

/-- Equivariance is an equality in the genuine projective space. -/
theorem projective_submodule_map (g : V ≃ₗ[K] V) (p : Projectivization K V) :
    (Projectivization.map g.toLinearMap g.injective p).submodule =
      p.submodule.map g.toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [Projectivization.map_mk,Projectivization.submodule_mk,
      Projectivization.submodule_mk,Submodule.map_span,Set.image_singleton]

theorem radicalPoint_isometry (B : LinearMap.BilinForm K V) (hB : B.IsAlt)
    (g : V ≃ₗ[K] V) (hg : ∀ x y, B (g x) (g y) = B x y) (U : RankEightPlane B) :
    radicalPoint B (isometryPlane B hB g hg U) =
      Projectivization.map g.toLinearMap g.injective (radicalPoint B U) := by
  apply Projectivization.submodule_injective
  rw [radicalPoint_submodule,projective_submodule_map,radicalPoint_submodule]
  exact (radical_map_isometry B hB g hg U.val).symm

/-- The actual set-theoretic fiber is exactly the subspaces with this intrinsic radical. -/
def pointFiberEquiv (B : LinearMap.BilinForm K V) (L : Projectivization K V) :
    {U : RankEightPlane B // radicalPoint B U = L} ≃
      {U : Submodule K V // finrank K U = 9 ∧ RadicalFiber.radical B U = L.submodule} where
  toFun U := ⟨U.val.val,U.val.property.1,by
    have h := congrArg Projectivization.submodule U.property
    simpa only [radicalPoint_submodule] using h⟩
  invFun U := ⟨⟨U.val,U.property.1,by rw [U.property.2]; exact L.finrank_submodule⟩,by
    apply Projectivization.submodule_injective
    rw [radicalPoint_submodule]
    exact U.property.2⟩
  left_inv U := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv U := by apply Subtype.ext; rfl

end M9.RadicalMap
