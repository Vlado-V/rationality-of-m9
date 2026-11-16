module

public import M9StacksIntegration.LagrangianProjectiveIntersection

/-!
# Actual projective linear spaces of the remaining original rows

The original surjective five-by-fourteen matrix remains fixed. Restricting
its output to the final `5-i` rows is genuinely surjective, and the native
projective linear zero locus of these original equations has dimension
`8+i`. No tail-rank or projective-dimension premise is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Module
open AlgebraicGeometry.ProjectiveSpaceOfModule

universe u
namespace M9Native.LagrangianTailLinearSpace
open LagrangianProjectiveIntersection

variable (K : Type u) [Field K]

def tailEmbedding (i : ℕ) (hi : i ≤ 5) : Fin (5 - i) ↪ Fin 5 where
  toFun j := ⟨i + j.1, by omega⟩
  inj' := by
    intro a b h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega

def tailMatrix (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i ≤ 5) :
    Matrix (Fin (5 - i)) (Fin 14) K := M.submatrix (tailEmbedding i hi) id

theorem tailMatrix_surjective (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin) (i : ℕ) (hi : i ≤ 5) :
    Function.Surjective (tailMatrix K M i hi).mulVecLin := by
  intro y
  obtain ⟨v, hv⟩ := (tailEmbedding i hi).injective.surjective_comp_right y
  obtain ⟨x, hx⟩ := hM v
  refine ⟨x, ?_⟩
  ext j
  change M.mulVecLin x (tailEmbedding i hi j) = y j
  rw [hx]
  exact congrArg (fun f => f j) hv

def constraints (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i ≤ 5) :
    Submodule K (Forms K) := LinearMap.range (tailMatrix K M i hi).mulVecLin.dualMap

def locus (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i ≤ 5) : Set (ambient K) :=
  (coordinateIso K).hom ⁻¹' linearSubspace K (Forms K) (constraints K M i hi)

theorem locus_isClosed (M : Matrix (Fin 5) (Fin 14) K) (i : ℕ) (hi : i ≤ 5) :
    IsClosed (locus K M i hi) :=
  (isClosed_linearSubspace K (Forms K) (constraints K M i hi)).preimage
    (coordinateIso K).hom.continuous

theorem finrank_quotient_constraints (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin) (i : ℕ) (hi : i ≤ 5) :
    finrank K (Forms K ⧸ constraints K M i hi) = 8 + i + 1 := by
  have hr : finrank K (constraints K M i hi) = 5 - i := by
    rw [constraints, LinearMap.finrank_range_dualMap_eq_finrank_range,
      LinearMap.range_eq_top.mpr (tailMatrix_surjective K M hM i hi), finrank_top]
    simp
  have hs := (constraints K M i hi).finrank_quotient_add_finrank
  rw [finrank_forms K, hr] at hs
  omega

theorem locus_dimension (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin) (i : ℕ) (hi : i ≤ 5) :
    topologicalKrullDim (locus K M i hi) = ((8 + i : ℕ) : WithBot ℕ∞) := by
  have hd := topologicalKrullDim_linearSubspace_of_finrank_quotient_eq
    (k := K) (V := Forms K) (W := constraints K M i hi) (n := 8 + i)
    (finrank_quotient_constraints K M hM i hi)
  exact (topologicalKrullDim_preimage_of_homeomorph (coordinateIso K).hom.homeomorph
    (linearSubspace K (Forms K) (constraints K M i hi))).trans hd

theorem locus_nonempty (M : Matrix (Fin 5) (Fin 14) K)
    (hM : Function.Surjective M.mulVecLin) (i : ℕ) (hi : i ≤ 5) :
    (locus K M i hi).Nonempty := by
  by_contra hn
  have he : IsEmpty (locus K M i hi) := ⟨fun x => hn ⟨x.1, x.2⟩⟩
  have hb := (topologicalKrullDim_eq_bot_iff_isEmpty (locus K M i hi)).mpr he
  rw [locus_dimension K M hM i hi] at hb
  simp at hb

end M9Native.LagrangianTailLinearSpace
