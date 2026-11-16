module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Basis.Fin
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic

/-!
# Actual exterior data for a minimal four-point Grassmannian circuit

The carrier is the actual third exterior power of the original six-dimensional
coordinate space. The every-three condition is literal linear independence
of each three-vector deletion. The weaker not-all-collinear condition is false;
its explicit counterexample is recorded in the research audit.

This foundational leaf does not assert the common-line theorem or a geometric
canonical-curve consequence. Those require the remaining actual pair lemmas.
-/

@[expose] public noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open Module
open scoped BigOperators

universe u
namespace M9Native.MukaiFourCircuit
variable (K : Type u) [Field K]

abbrev Six := Fin 6 → K
abbrev Three := ⋀[K]^3 (Six K)

def triple (s : Fin 3 → Six K) : Three K := exteriorPower.ιMulti K 3 s

def plane (s : Fin 3 → Six K) : Submodule K (Six K) :=
  Submodule.span K (Set.range s)

/-- Actual wedge multiplication by a trivector, with degree-one source. -/
def wedgeLeft (w : Three K) : Six K →ₗ[K] ExteriorAlgebra K (Six K) where
  toFun v := ExteriorAlgebra.ι K v * w.val
  map_add' := by intro v v'; rw [map_add, add_mul]
  map_smul' := by intro c v; simp only [map_smul, smul_mul_assoc, RingHom.id_apply]

/-- The intrinsic vector wedge-annihilator, without a chosen presentation. -/
def wedgeAnn (w : Three K) : Submodule K (Six K) := (wedgeLeft K w).ker

@[simp] theorem mem_wedgeAnn (w : Three K) (v : Six K) :
    v ∈ wedgeAnn K w ↔ ExteriorAlgebra.ι K v * w.val = 0 := Iff.rfl

/-- An independent tuple has a genuine nonzero exterior product. -/
theorem ιMulti_ne_zero {n : ℕ} (s : Fin n → Six K) (hs : LinearIndependent K s) :
    exteriorPower.ιMulti K n s ≠ 0 := by
  let t : Set.powersetCard (Fin n) n :=
    Set.powersetCard.ofFinEmbEquiv
      (OrderEmbedding.ofStrictMono (id : Fin n → Fin n) strictMono_id)
  have hli := exteriorPower.ιMulti_family_linearIndependent_field (n := n) hs
  have hn := LinearIndependent.ne_zero t hli
  simpa [t, exteriorPower.ιMulti_family] using hn

/-- Literal multiplication by a vector detects membership in the span of an
independent exterior tuple, in any degree. -/
theorem ι_mul_ιMulti_eq_zero_iff {n : ℕ} (s : Fin n → Six K)
    (hs : LinearIndependent K s) (v : Six K) :
    ExteriorAlgebra.ι K v * ExteriorAlgebra.ιMulti K n s = 0 ↔
      v ∈ Submodule.span K (Set.range s) := by
  have hprod : ExteriorAlgebra.ι K v * ExteriorAlgebra.ιMulti K n s =
      ExteriorAlgebra.ιMulti K (n+1) (Fin.cons v s) := by
    exact (ExteriorAlgebra.ιMulti_succ_apply (R := K) (Fin.cons v s)).symm
  rw [hprod]
  constructor
  · intro hz
    by_contra hv
    have hli := linearIndependent_finCons.mpr ⟨hs, hv⟩
    apply ιMulti_ne_zero K (Fin.cons v s) hli
    apply Subtype.ext
    exact hz
  · intro hv
    apply (ExteriorAlgebra.ιMulti K (n+1)).map_linearDependent
    intro hli
    exact (linearIndependent_finCons.mp hli).2 hv


/-- The actual underlying three-plane is the actual wedge-annihilator. -/
theorem wedgeAnn_triple_eq_plane (s : Fin 3 → Six K) (hs : LinearIndependent K s) :
    wedgeAnn K (triple K s) = plane K s := by
  ext v
  exact ι_mul_ιMulti_eq_zero_iff K s hs v

/-- Equal nonzero scalar multiples of independent exterior volumes have the
same literal vector span. -/
theorem span_eq_of_smul_ιMulti_eq {n : ℕ} (s t : Fin n → Six K)
    (hs : LinearIndependent K s) (ht : LinearIndependent K t)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a • exteriorPower.ιMulti K n s = b • exteriorPower.ιMulti K n t) :
    Submodule.span K (Set.range s) = Submodule.span K (Set.range t) := by
  have he : a • ExteriorAlgebra.ιMulti K n s = b • ExteriorAlgebra.ιMulti K n t :=
    congrArg Subtype.val h
  ext x
  rw [← ι_mul_ιMulti_eq_zero_iff K s hs, ← ι_mul_ιMulti_eq_zero_iff K t ht]
  have hx := congrArg (fun z => ExteriorAlgebra.ι K x * z) he
  simp only [mul_smul_comm] at hx
  have hzero := congrArg (fun z : ExteriorAlgebra K (Six K) => z = 0) hx
  simpa only [smul_eq_zero, ha, hb, false_or] using Iff.of_eq hzero

/-- Actual independent tuple planes have dimension three. -/
theorem plane_finrank (s : Fin 3 → Six K) (hs : LinearIndependent K s) :
    finrank K (plane K s) = 3 := by
  change finrank K (Submodule.span K (Set.range s)) = 3
  simpa only [Fintype.card_fin] using finrank_span_eq_card hs

/-- A top-degree alternating map with any vector-space target is its
basis value multiplied by the genuine determinant. -/
theorem alternating_apply_eq_det_smul
    {W N : Type*} [AddCommGroup W] [Module K W] [AddCommGroup N] [Module K N]
    (b : Module.Basis (Fin 3) K W) (F : W [⋀^Fin 3]→ₗ[K] N) (s : Fin 3 → W) :
    F s = b.det s • F b := by
  have hF : F = b.det.smulRight (F b) := by
    refine Module.Basis.ext_alternating b fun i hi => ?_
    let σ : Equiv.Perm (Fin 3) :=
      Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change F (b ∘ σ) = (b.det.smulRight (F b)) (b ∘ σ)
    simp [AlternatingMap.map_perm, Module.Basis.det_self]
  simpa using congrArg (fun G : W [⋀^Fin 3]→ₗ[K] N => G s) hF

/-- Three vectors in the actual span of an independent triple have an
actual scalar-multiple exterior volume. No plane/Pluecker identification is assumed. -/
theorem exists_triple_smul_of_mem_plane (s t : Fin 3 → Six K)
    (hs : LinearIndependent K s) (ht : ∀ i, t i ∈ plane K s) :
    ∃ c : K, triple K t = c • triple K s := by
  let b : Module.Basis (Fin 3) K (plane K s) := Module.Basis.span hs
  let t' : Fin 3 → plane K s := fun i => ⟨t i, ht i⟩
  let F : (plane K s) [⋀^Fin 3]→ₗ[K] Three K :=
    (exteriorPower.ιMulti K 3).compLinearMap (plane K s).subtype
  refine ⟨b.det t', ?_⟩
  have h := alternating_apply_eq_det_smul K b F t'
  simpa [F, t', b, triple, plane, AlternatingMap.compLinearMap_apply,
    Function.comp_def, Module.Basis.span_apply] using h

/-- Literal every-three linear independence, not merely noncollinearity. -/
def EveryThreeLI (z : Fin 4 → Three K) : Prop :=
  ∀ j : Fin 4, LinearIndependent K (j.removeNth z)

/-- Full span dimension three gives genuine dependence of the four vectors. -/
theorem dependent_of_span_finrank_three (z : Fin 4 → Three K)
    (hz : finrank K (Submodule.span K (Set.range z)) = 3) :
    ¬ LinearIndependent K z := by
  intro hli
  have hdim : finrank K (Submodule.span K (Set.range z)) = 4 := by
    simpa using Module.finrank_eq_card_basis (Module.Basis.span hli)
  omega

end M9Native.MukaiFourCircuit
