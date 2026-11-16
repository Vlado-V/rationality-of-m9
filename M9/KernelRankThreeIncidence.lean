module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic

/-! The actual residue-field linear algebra for the rank-three kernel
incidence used in the Brill--Noether emptiness argument. These results do
not construct a Grassmannian scheme or replace its geometric fiber bridge. -/

@[expose] public section

namespace M9.KernelRankThreeIncidence

open Module

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [AddCommGroup W] [Module k W]

/-- Actual three-dimensional subspaces contained in the actual kernel. -/
def Incidence (u : V →ₗ[k] W) :=
  {S : Submodule k V // finrank k S=3 ∧ S ≤ LinearMap.ker u}

/-- No three-dimensional subspace can be contained in a kernel of
dimension at most two. -/
theorem not_le_ker (u : V →ₗ[k] W) (hker : finrank k (LinearMap.ker u)≤2)
    (S : Submodule k V) (hS : finrank k S=3) : ¬ S ≤ LinearMap.ker u := by
  intro hle
  have hdim := Submodule.finrank_mono hle
  omega

theorem incidence_isEmpty (u : V →ₗ[k] W) (hker : finrank k (LinearMap.ker u)≤2) :
    IsEmpty (Incidence u) :=
  ⟨fun x => not_le_ker u hker x.val x.property.1 x.property.2⟩

/-- Restricting the actual linear map to any injected rank-three space is
nonzero when its kernel has dimension at most two. This is the fiberwise
nonvanishing needed for the actual Grassmannian incidence section. -/
theorem restriction_ne_zero {T : Type*} [AddCommGroup T] [Module k T]
    [FiniteDimensional k T] (u : V →ₗ[k] W)
    (hker : finrank k (LinearMap.ker u)≤2) (i : T →ₗ[k] V)
    (hi : Function.Injective i) (hT : finrank k T=3) : u.comp i ≠ 0 := by
  intro hzero
  have hle : LinearMap.range i ≤ LinearMap.ker u := by
    rintro _ ⟨x,rfl⟩
    exact LinearMap.congr_fun hzero x
  have hrange : finrank k (LinearMap.range i)=3 :=
    (LinearMap.finrank_range_of_inj hi).trans hT
  exact not_le_ker u hker (LinearMap.range i) hrange hle

end M9.KernelRankThreeIncidence
