module

public import M9StacksIntegration.PicardCartierCapDegreeRestriction
public import M9StacksIntegration.CurvePowerGraphBaseChange

/-!
# The actual marked-point cap degree on a curve power

The last factor is the actual constant-point graph divisor. Its cap
restricts the remaining factors to the original graph, which is a
section of the second projection. The recursion ends at the actual
degree of Spec of the base field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open CartesianMonoidalCategory MonoidalCategory Stacks.CurvePower

universe u

namespace M9Native.CurvePowerPointCapDegree

open Stacks.Chow CurveTopChowClass ChowCapDegreePicard CurvePowerChowFunctional

theorem capValue_structure_congr (k : Type u) [Field k] {X : Scheme.{u}}
    (f g : X ⟶ Spec (.of k)) [IsProper f] [IsProper g] (h : f = g)
    {m : ℕ} (x : Fin m → Stacks.Picard.ofScheme X) :
    capDegreePicard k f x (identityChowClass (fieldChowSituation k) f m) =
      capDegreePicard k g x (identityChowClass (fieldChowSituation k) g m) := by
  cases h
  rfl

theorem capDegreePicard_base (k : Type u) [Field k]
    (x : Fin 0 → Stacks.Picard.ofScheme (Spec (.of k))) :
    capDegreePicard k (𝟙 (Spec (.of k))) x
      (identityChowClass (fieldChowSituation k) (𝟙 (Spec (.of k))) 0) = 1 := by
  have h := wordDegree_eq_capDegreePicard k (𝟙 (Spec (.of k)))
    ([] : List (Stacks.Picard.ofScheme (Spec (.of k))))
  have hx : (fun j : Fin 0 => ([] : List (Stacks.Picard.ofScheme (Spec (.of k)))).get j) =
      x := by
    funext j
    exact j.elim0
  cases hx
  exact h.symm.trans (wordDegree_nil_base k)

section Family

variable {S : Scheme.{u}} (C : Over S) [IsSeparated C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)

abbrev pointGraph (m : ℕ) :=
  Stacks.Hilbert.pointGraph C (power C m) (toUnit (power C m) ≫ c₀)

abbrev fibrePointClass (m : ℕ) : Stacks.Picard.ofScheme (power C (m + 1)).left :=
  CurvePowerGraphCartier.graphClass C m (toUnit (power C m) ≫ c₀)

omit [SmoothOfRelativeDimension 1 C.hom] in
theorem pointGraph_isClosedImmersion (m : ℕ) : IsClosedImmersion (pointGraph C c₀ m) :=
  Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C m)
    (toUnit (power C m) ≫ c₀)

theorem pointGraph_isEffectiveCartier (m : ℕ) :
    Stacks.Divisors.IsEffectiveCartierDivisor (pointGraph C c₀ m).ker :=
  CurvePowerGraphCartier.graphIdeal_isEffectiveCartier C m (toUnit (power C m) ≫ c₀)

theorem fibrePointClass_eq_divisor (m : ℕ) :
    fibrePointClass C c₀ m = @Stacks.Divisors.picardClass _ (pointGraph C c₀ m).ker
      (pointGraph_isEffectiveCartier C c₀ m) :=
  (GraphNormalPicard.graphFamily C (power C m) (toUnit (power C m) ≫ c₀)).picardClass_eq
    (pointGraph_isEffectiveCartier C c₀ m)

def pointFamily : (m : ℕ) → Fin m → Stacks.Picard.ofScheme (power C m).left
  | 0 => Fin.elim0
  | m + 1 => Fin.snoc (α := fun _ => Stacks.Picard.ofScheme (power C (m + 1)).left)
      (fun j => Stacks.Picard.schemePullbackClass (snd C (power C m)).left (pointFamily m j))
      (fibrePointClass C c₀ m)

theorem pointGraph_pullback_tail (m : ℕ) (j : Fin m) :
    Stacks.Picard.schemePullbackClass (pointGraph C c₀ m)
        (Stacks.Picard.schemePullbackClass (snd C (power C m)).left
          (pointFamily C c₀ m j)) = pointFamily C c₀ m j := by
  rw [Stacks.Picard.schemePullbackClass_comp,
    CurvePowerGraphCartier.graphSection_comp_second,
    Stacks.Picard.schemePullbackClass_id]

end Family

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (c₀ : power C 0 ⟶ C)
  (hC : topologicalKrullDim C.left = 1)

include hC

theorem capDegreePicard_pointFamily (m : ℕ) :
    capDegreePicard k (power C m).hom (pointFamily C c₀ m)
      (identityChowClass (fieldChowSituation k) (power C m).hom m) = 1 := by
  induction m with
  | zero => exact capDegreePicard_base k (pointFamily C c₀ 0)
  | succ m ih =>
      have : IsIntegral (power C (m + 1)).left :=
        (isVariety_power C (m + 1)).toIsIntegral
      have hi : IsClosedImmersion (pointGraph C c₀ m) := pointGraph_isClosedImmersion C c₀ m
      have hD : Stacks.Divisors.IsEffectiveCartierDivisor (pointGraph C c₀ m).ker :=
        pointGraph_isEffectiveCartier C c₀ m
      let := hi
      let := hD
      have hdim : topologicalKrullDim (power C (m + 1)).left =
          ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [(isVariety_power_and_topologicalKrullDim C (m + 1)).2, hC, mul_one]
      have hn : schemeDeltaDimension (fieldChowSituation k) (power C (m + 1)).hom =
          (((m : ℤ) + 1) : EInt) := by
        have h := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
          (power C (m + 1)).hom hdim
        simpa [WithBotTop.coe] using h
      rw [pointFamily, fibrePointClass_eq_divisor]
      let x : Fin m → Stacks.Picard.ofScheme (power C (m + 1)).left :=
        fun j => Stacks.Picard.schemePullbackClass (snd C (power C m)).left
          (pointFamily C c₀ m j)
      have hr := @PicardCartierCapDegreeRestriction.capDegreePicard_snoc_divisor k _
        (power C (m + 1)).left (power C m).left (power C (m + 1)).hom
        inferInstance inferInstance (pointGraph C c₀ m) hi hD m x hn
      have hp : (fun j => Stacks.Picard.schemePullbackClass (pointGraph C c₀ m) (x j)) =
          pointFamily C c₀ m := by
        funext j
        exact pointGraph_pullback_tail C c₀ m j
      have hv := congrArg (fun z : Fin m → Stacks.Picard.ofScheme (power C m).left =>
        capDegreePicard k (pointGraph C c₀ m ≫ (power C (m + 1)).hom) z
          (identityChowClass (fieldChowSituation k)
            (pointGraph C c₀ m ≫ (power C (m + 1)).hom) m)) hp
      have hs := capValue_structure_congr k
        (pointGraph C c₀ m ≫ (power C (m + 1)).hom) (power C m).hom
        (CurvePowerGraphBaseChange.graphSection_comp_hom C m
          (toUnit (power C m) ≫ c₀)) (pointFamily C c₀ m)
      exact hr.trans (hv.trans (hs.trans ih))

end M9Native.CurvePowerPointCapDegree
