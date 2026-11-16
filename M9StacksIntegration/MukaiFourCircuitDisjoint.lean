module

public import M9StacksIntegration.MukaiPrimitiveProjector
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.FinCases

/-!
# Disjoint decomposable summands in the actual exterior cube

All interior and wedge products are the actual frozen exterior operations.
The coefficient functionals below are genuine fourth-exterior dual pairings.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public noncomputable section

open Module CategoryTheory
open M9Native.MukaiQuarticExterior M9Native.MukaiPrimitiveProjector

namespace M9Native.MukaiFourCircuitDisjoint

variable (K : Type*) [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]

abbrev Six := Fin 6 → K

theorem four_from_three_eq_zero (s : Fin 3 → V) (f : Fin 4 → Fin 3) :
    exteriorPower.ιMulti K 4 (s ∘ f) = 0 := by
  apply (exteriorPower.ιMulti K 4).map_eq_zero_of_not_injective
  intro h
  have hf : Function.Injective f := fun i j hij => h (congrArg s hij)
  have hc := Fintype.card_le_of_injective f hf
  norm_num at hc

theorem wedge_two_from_three_eq_zero (s : Fin 3 → V) (i j k l : Fin 3) :
    wedgeMul K 2 2 (wedge2 K (s i) (s j)) (wedge2 K (s k) (s l)) = 0 := by
  change wedgeMul K 2 2 (exteriorPower.ιMulti K 2 ![s i,s j])
    (exteriorPower.ιMulti K 2 ![s k,s l]) = 0
  rw [wedgeMul_ιMulti]
  have h : Fin.append ![s i,s j] ![s k,s l] = s ∘ ![i,j,k,l] := by
    funext n
    fin_cases n <;> rfl
  rw [h]
  exact four_from_three_eq_zero K s ![i,j,k,l]

theorem interior_decomposable_square_zero (φ : Module.Dual K V) (s : Fin 3 → V) :
    wedgeMul K 2 2 (interior K φ (exteriorPower.ιMulti K 3 s))
      (interior K φ (exteriorPower.ιMulti K 3 s)) = 0 := by
  simp only [interior_ιMulti, map_add, map_sub, map_smul,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    wedge_two_from_three_eq_zero, smul_zero, add_zero, sub_zero]

theorem interior_eq_zero_of_forall (φ : Module.Dual K V) (s : Fin 3 → V)
    (h : ∀ i, φ (s i) = 0) : interior K φ (exteriorPower.ιMulti K 3 s) = 0 := by
  simp [interior_ιMulti, h]

theorem wedge_two_comm (x y : ⋀[K]^2 V) : wedgeMul K 2 2 x y = wedgeMul K 2 2 y x := by
  have hx : x ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2 (M := V))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  have hy : y ∈ Submodule.span K (Set.range (exteriorPower.ιMulti K 2 (M := V))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  refine Submodule.span_induction₂
    (p := fun a b _ _ => wedgeMul K 2 2 a b = wedgeMul K 2 2 b a)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro a b ⟨u,rfl⟩ ⟨v,rfl⟩
    rw [wedgeMul_ιMulti, wedgeMul_ιMulti]
    apply Subtype.ext
    have h := ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm (R := K) u v
    simp only [show (-1 : ℤˣ) ^ (2 * 2) = 1 by decide, one_smul,
      ExteriorAlgebra.ιMulti_mul_ιMulti] at h
    simpa only [exteriorPower.ιMulti_apply_coe] using h
  all_goals simp +contextual [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]

theorem interior_sum_square (φ : Module.Dual K V) (s t : Fin 3 → V) :
    wedgeMul K 2 2
        (interior K φ (exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t))
        (interior K φ (exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t)) =
      (2 : K) • wedgeMul K 2 2 (interior K φ (exteriorPower.ιMulti K 3 s))
        (interior K φ (exteriorPower.ιMulti K 3 t)) := by
  simp only [map_add, LinearMap.add_apply]
  rw [interior_decomposable_square_zero, interior_decomposable_square_zero]
  rw [wedge_two_comm K (interior K φ (exteriorPower.ιMulti K 3 t))]
  simp [two_smul]

def cofactorIndex (i : Fin 3) : Fin 2 → Fin 3 := ![i+1,i+2]

theorem interior_cyclic (φ : Module.Dual K V) (s : Fin 3 → V) :
    interior K φ (exteriorPower.ιMulti K 3 s) =
      ∑ i : Fin 3, φ (s i) • wedge2 K (s (cofactorIndex i 0))
        (s (cofactorIndex i 1)) := by
  simp [Fin.sum_univ_succ, cofactorIndex, interior_ιMulti,
    wedge2_swap K (s 2) (s 0), sub_eq_add_neg, add_assoc]

def mixedIndices (i j : Fin 3) : Fin 4 → Fin 6 :=
  ![Fin.castAdd 3 (cofactorIndex i 0), Fin.castAdd 3 (cofactorIndex i 1),
    Fin.natAdd 3 (cofactorIndex j 0), Fin.natAdd 3 (cofactorIndex j 1)]

def mixedDuals (b : Basis (Fin 6) K V) (i j : Fin 3) : Fin 4 → Module.Dual K V :=
  fun q => b.coord (mixedIndices i j q)

def mixedIntegerCoefficient (i j : Fin 3) (a c d e : Fin 6) : ℤ :=
  (Matrix.of (fun r q : Fin 4 =>
    if Fin.append ![a,c] ![d,e] r = mixedIndices i j q then (1 : ℤ) else 0)).det

def mixedCoefficient (b : Basis (Fin 6) K V) (i j : Fin 3) :
    (⋀[K]^4 V) →ₗ[K] K :=
  exteriorPower.pairingDual K V 4 (exteriorPower.ιMulti K 4 (mixedDuals K b i j))

theorem mixedCoefficient_basis (b : Basis (Fin 6) K V) (i j : Fin 3)
    (a c d e : Fin 6) :
    mixedCoefficient K b i j
      (wedgeMul K 2 2 (wedge2 K (b a) (b c)) (wedge2 K (b d) (b e))) =
      (Int.castRingHom K) (mixedIntegerCoefficient i j a c d e) := by
  change mixedCoefficient K b i j
    (wedgeMul K 2 2 (exteriorPower.ιMulti K 2 ![b a,b c])
      (exteriorPower.ιMulti K 2 ![b d,b e])) = _
  rw [wedgeMul_ιMulti]
  rw [mixedCoefficient, exteriorPower.pairingDual_ιMulti_ιMulti]
  have hm : (Matrix.of (fun r q : Fin 4 =>
        mixedDuals K b i j q ((Fin.append ![b a,b c] ![b d,b e]) r))) =
      (Matrix.of (fun r q : Fin 4 =>
        if Fin.append ![a,c] ![d,e] r = mixedIndices i j q then (1 : ℤ) else 0)).map
          (Int.castRingHom K) := by
    have hf (r : Fin 4) : Fin.append ![b a,b c] ![b d,b e] r =
        b (Fin.append ![a,c] ![d,e] r) := by
      refine Fin.addCases
        (motive := fun z : Fin (2+2) => Fin.append ![b a,b c] ![b d,b e] z =
          b (Fin.append ![a,c] ![d,e] z))
        (fun z : Fin 2 => ?_) (fun z : Fin 2 => ?_) r
      · simp only [Fin.append_left]
        fin_cases z <;> rfl
      · simp only [Fin.append_right]
        fin_cases z <;> rfl
    ext r q
    simp [hf, mixedDuals, Matrix.map_apply, Basis.coord_apply, Finsupp.single_apply]
  rw [hm]
  exact ((Int.castRingHom K).map_det _).symm

theorem mixedIntegerCoefficient_cyclic : ∀ i j a c : Fin 3,
    mixedIntegerCoefficient i j
      (Fin.castAdd 3 (cofactorIndex a 0)) (Fin.castAdd 3 (cofactorIndex a 1))
      (Fin.natAdd 3 (cofactorIndex c 0)) (Fin.natAdd 3 (cofactorIndex c 1)) =
      if i = a ∧ j = c then 1 else 0 := by
  decide

theorem mixedCoefficient_cyclic (b : Basis (Fin 6) K V) (i j a c : Fin 3) :
    mixedCoefficient K b i j
      (wedgeMul K 2 2
        (wedge2 K (b (Fin.castAdd 3 (cofactorIndex a 0)))
          (b (Fin.castAdd 3 (cofactorIndex a 1))))
        (wedge2 K (b (Fin.natAdd 3 (cofactorIndex c 0)))
          (b (Fin.natAdd 3 (cofactorIndex c 1))))) =
      if i = a ∧ j = c then 1 else 0 := by
  rw [mixedCoefficient_basis, mixedIntegerCoefficient_cyclic]
  split_ifs <;> simp

theorem mixedCoefficient_interior (b : Basis (Fin 6) K V)
    (φ : Module.Dual K V) (i j : Fin 3) :
    mixedCoefficient K b i j
      (wedgeMul K 2 2
        (interior K φ (exteriorPower.ιMulti K 3 (fun k => b (Fin.castAdd 3 k))))
        (interior K φ (exteriorPower.ιMulti K 3 (fun k => b (Fin.natAdd 3 k))))) =
      φ (b (Fin.castAdd 3 i)) * φ (b (Fin.natAdd 3 j)) := by
  simp only [interior_cyclic, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, mixedCoefficient_cyclic]
  simp [smul_eq_mul, ite_and, mul_ite, mul_comm]

theorem interior_basis_sum_square_eq_zero_iff (h2 : (2 : K) ≠ 0)
    (b : Basis (Fin 6) K V) (φ : Module.Dual K V) :
    wedgeMul K 2 2
        (interior K φ (exteriorPower.ιMulti K 3 (fun k => b (Fin.castAdd 3 k)) +
          exteriorPower.ιMulti K 3 (fun k => b (Fin.natAdd 3 k))))
        (interior K φ (exteriorPower.ιMulti K 3 (fun k => b (Fin.castAdd 3 k)) +
          exteriorPower.ιMulti K 3 (fun k => b (Fin.natAdd 3 k)))) = 0 ↔
      (∀ i : Fin 3, φ (b (Fin.castAdd 3 i)) = 0) ∨
        (∀ j : Fin 3, φ (b (Fin.natAdd 3 j)) = 0) := by
  constructor
  · intro h
    rw [interior_sum_square] at h
    have hx := (smul_eq_zero.mp h).resolve_left h2
    have hp (i j : Fin 3) : φ (b (Fin.castAdd 3 i)) * φ (b (Fin.natAdd 3 j)) = 0 := by
      have hc := congrArg (mixedCoefficient K b i j) hx
      rwa [mixedCoefficient_interior, map_zero] at hc
    by_cases hs : ∀ i : Fin 3, φ (b (Fin.castAdd 3 i)) = 0
    · exact Or.inl hs
    · right
      obtain ⟨i,hi⟩ := not_forall.mp hs
      intro j
      exact (mul_eq_zero.mp (hp i j)).resolve_left hi
  · rintro (hs | ht)
    · simp only [map_add, interior_eq_zero_of_forall K φ _ hs, zero_add]
      exact interior_decomposable_square_zero K φ _
    · simp only [map_add, interior_eq_zero_of_forall K φ _ ht, add_zero]
      exact interior_decomposable_square_zero K φ _

theorem interior_disjoint_sum_square_eq_zero_iff (h2 : (2 : K) ≠ 0)
    (s t : Fin 3 → Six K) (hst : LinearIndependent K (Fin.append s t))
    (φ : Module.Dual K (Six K)) :
    wedgeMul K 2 2 (interior K φ (exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t))
      (interior K φ (exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t)) = 0 ↔
      (∀ i, φ (s i) = 0) ∨ (∀ j, φ (t j) = 0) := by
  let b : Basis (Fin 6) K (Six K) :=
    basisOfLinearIndependentOfCardEqFinrank hst (by simp [Six])
  have hb (i : Fin 6) : b i = Fin.append s t i :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hst (by simp [Six])) i
  simpa only [hb, Fin.append_left, Fin.append_right] using
    interior_basis_sum_square_eq_zero_iff K h2 b φ

theorem mem_annihilator_span_iff (s : Fin 3 → V) (φ : Module.Dual K V) :
    φ ∈ (Submodule.span K (Set.range s)).dualAnnihilator ↔ ∀ i, φ (s i) = 0 := by
  change φ ∈ ((Submodule.span K (Set.range s)).dualAnnihilator : Set (Module.Dual K V)) ↔ _
  rw [Submodule.coe_dualAnnihilator_span]
  simp only [Set.mem_ofPred_eq, Set.range_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]

/-- A sum of two complementary decomposable trivectors has no other
decomposable summand support, even without an independence assumption on `v`. -/
theorem span_eq_or_span_eq_of_disjoint_sum (h2 : (2 : K) ≠ 0)
    (s t u v : Fin 3 → Six K)
    (hst : LinearIndependent K (Fin.append s t)) (hu : LinearIndependent K u)
    (hsum : exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t =
      exteriorPower.ιMulti K 3 u + exteriorPower.ιMulti K 3 v) :
    Submodule.span K (Set.range u) = Submodule.span K (Set.range s) ∨
      Submodule.span K (Set.range u) = Submodule.span K (Set.range t) := by
  let U := Submodule.span K (Set.range u)
  let S := Submodule.span K (Set.range s)
  let T := Submodule.span K (Set.range t)
  have hsub : (U.dualAnnihilator : Set (Module.Dual K (Six K))) ⊆
      (S.dualAnnihilator : Set (Module.Dual K (Six K))) ∪ T.dualAnnihilator := by
    intro φ hφ
    have hzero := interior_eq_zero_of_forall K φ u ((mem_annihilator_span_iff K u φ).mp hφ)
    have hsquare : wedgeMul K 2 2
        (interior K φ (exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t))
        (interior K φ (exteriorPower.ιMulti K 3 s + exteriorPower.ιMulti K 3 t)) = 0 := by
      simpa only [hsum, map_add, hzero, zero_add] using interior_decomposable_square_zero K φ v
    exact ((interior_disjoint_sum_square_eq_zero_iff K h2 s t hst φ).mp hsquare).imp
      ((mem_annihilator_span_iff K s φ).mpr) ((mem_annihilator_span_iff K t φ).mpr)
  have hle : U.dualAnnihilator ≤ S.dualAnnihilator ∨ U.dualAnnihilator ≤ T.dualAnnihilator :=
    AddSubgroupClass.subset_union.mp hsub
  have hs : LinearIndependent K s := by
    simpa only [Function.comp_def, Fin.append_left] using
      hst.comp (Fin.castAdd 3) (Fin.castAdd_injective 3 3)
  have ht : LinearIndependent K t := by
    simpa only [Function.comp_def, Fin.append_right] using
      hst.comp (Fin.natAdd 3) (Fin.natAdd_injective 3 3)
  have hU : finrank K U = 3 := by simpa only [U, Fintype.card_fin] using finrank_span_eq_card hu
  rcases hle with hS | hT
  · left
    have hSU : S ≤ U := Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp hS
    have hSrank : finrank K S = 3 := by
      simpa only [S, Fintype.card_fin] using finrank_span_eq_card hs
    exact (Submodule.eq_of_le_of_finrank_eq hSU (hSrank.trans hU.symm)).symm
  · right
    have hTU : T ≤ U := Subspace.dualAnnihilator_le_dualAnnihilator_iff.mp hT
    have hTrank : finrank K T = 3 := by
      simpa only [T, Fintype.card_fin] using finrank_span_eq_card ht
    exact (Submodule.eq_of_le_of_finrank_eq hTU (hTrank.trans hU.symm)).symm

end M9Native.MukaiFourCircuitDisjoint
