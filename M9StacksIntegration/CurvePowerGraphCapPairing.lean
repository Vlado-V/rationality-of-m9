module

public import M9StacksIntegration.CurvePowerPointTrace

/-!
# Actual graph restriction in every cap degree

The number of remaining factors is arbitrary. In the top degree this
is the proved Cartier restriction formula. In every other degree both
actual fundamental classes vanish in their native Chow grading.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.CurvePower

universe u

namespace M9Native.CurvePowerGraphCapPairing

open Stacks.Chow CurveTopChowClass ChowCapDegreePicard ChowCapWords

theorem capValue_eq_zero_of_genericDimension_ne (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    {n : ℕ} (x : Fin n → Stacks.Picard.ofScheme X)
    (hd : relativeDimension (fieldChowSituation k).dimensionFunction f (genericPoint X) ≠ n) :
    capDegreePicard k f x (identityChowClass (fieldChowSituation k) f n) = 0 := by
  rw [identityChowClass_eq_zero_of_genericDimension_ne (fieldChowSituation k) f n hd,
    map_zero]

variable (k : Type u) [Field k] [IsAlgClosed k]
  (C : Over (Spec (.of k))) [IsVariety k C.hom] [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom] (hC : topologicalKrullDim C.left = 1)

include hC

theorem capValue_snoc_graph (m n : ℕ) (y : power C m ⟶ C)
    (x : Fin n → Stacks.Picard.ofScheme (power C (m + 1)).left) :
    capDegreePicard k (power C (m + 1)).hom
        (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme (power C (m + 1)).left)
          x (CurvePowerGraphCartier.graphClass C m y))
        (identityChowClass (fieldChowSituation k) (power C (m + 1)).hom ((n + 1 : ℕ) : ℤ)) =
      capDegreePicard k (power C m).hom
        (fun j => Stacks.Picard.schemePullbackClass (Stacks.Hilbert.pointGraph C (power C m) y)
          (x j))
        (identityChowClass (fieldChowSituation k) (power C m).hom n) := by
  have hdim (a : ℕ) : topologicalKrullDim (power C a).left = (a : WithBot ℕ∞) := by
    rw [(isVariety_power_and_topologicalKrullDim C a).2, hC, mul_one]
  have hX : IsIntegral (power C (m + 1)).left :=
    (isVariety_power C (m + 1)).toIsIntegral
  have hY : IsIntegral (power C m).left := (isVariety_power C m).toIsIntegral
  by_cases he : n = m
  · subst n
    have hi : IsClosedImmersion (Stacks.Hilbert.pointGraph C (power C m) y) :=
      Stacks.Hilbert.isClosedImmersion_pointGraph_of_isSeparated C (power C m) y
    have hD : Stacks.Divisors.IsEffectiveCartierDivisor
        (Stacks.Hilbert.pointGraph C (power C m) y).ker :=
      CurvePowerGraphCartier.graphIdeal_isEffectiveCartier C m y
    have hc : CurvePowerGraphCartier.graphClass C m y =
        @Stacks.Divisors.picardClass _ (Stacks.Hilbert.pointGraph C (power C m) y).ker hD :=
      (GraphNormalPicard.graphFamily C (power C m) y).picardClass_eq hD
    have hn : schemeDeltaDimension (fieldChowSituation k) (power C (m + 1)).hom =
        (((m : ℤ) + 1) : EInt) := by
      have h := schemeDeltaDimension_fieldChowSituation_eq_of_topologicalKrullDim_eq
        (power C (m + 1)).hom (hdim (m + 1))
      simpa [WithBotTop.coe] using h
    have hl := congrArg (fun z : Stacks.Picard.ofScheme (power C (m + 1)).left =>
      capDegreePicard k (power C (m + 1)).hom
        (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme (power C (m + 1)).left) x z)
        (identityChowClass (fieldChowSituation k) (power C (m + 1)).hom ((m + 1 : ℕ) : ℤ))) hc
    have hr := @PicardCartierCapDegreeRestriction.capDegreePicard_snoc_divisor k _
      (power C (m + 1)).left (power C m).left (power C (m + 1)).hom
      inferInstance hX (Stacks.Hilbert.pointGraph C (power C m) y) hi hD m x hn
    have hs := CurvePowerPointCapDegree.capValue_structure_congr k
      (Stacks.Hilbert.pointGraph C (power C m) y ≫ (power C (m + 1)).hom)
      (power C m).hom (CurvePowerGraphBaseChange.graphSection_comp_hom C m y)
      (fun j => Stacks.Picard.schemePullbackClass (Stacks.Hilbert.pointGraph C (power C m) y)
        (x j))
    exact hl.trans (hr.trans hs)
  · have hzX : capDegreePicard k (power C (m + 1)).hom
        (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme (power C (m + 1)).left)
          x (CurvePowerGraphCartier.graphClass C m y))
        (identityChowClass (fieldChowSituation k) (power C (m + 1)).hom ((n + 1 : ℕ) : ℤ)) = 0 := by
      apply capValue_eq_zero_of_genericDimension_ne
      rw [relativeDimension_fieldChowSituation_genericPoint (power C (m + 1)).hom
        (hdim (m + 1))]
      exact_mod_cast Nat.succ_ne_succ_iff.mpr (Ne.symm he)
    have hzY : capDegreePicard k (power C m).hom
        (fun j => Stacks.Picard.schemePullbackClass (Stacks.Hilbert.pointGraph C (power C m) y)
          (x j))
        (identityChowClass (fieldChowSituation k) (power C m).hom n) = 0 := by
      apply capValue_eq_zero_of_genericDimension_ne
      rw [relativeDimension_fieldChowSituation_genericPoint (power C m).hom (hdim m)]
      exact_mod_cast Ne.symm he
    exact hzX.trans hzY.symm

theorem wordDegree_append_graph (m : ℕ) (y : power C m ⟶ C)
    (xs : List (Stacks.Picard.ofScheme (power C (m + 1)).left)) :
    CurvePowerChowFunctional.wordDegree k (power C (m + 1)).hom
        ((xs ++ [CurvePowerGraphCartier.graphClass C m y]).map
          CurvePowerChowFunctional.chosenLine) =
      CurvePowerChowFunctional.wordDegree k (power C m).hom
        ((xs.map (Stacks.Picard.schemePullbackClass
          (Stacks.Hilbert.pointGraph C (power C m) y))).map
            CurvePowerChowFunctional.chosenLine) := by
  let x : Fin xs.length → Stacks.Picard.ofScheme (power C (m + 1)).left := xs.get
  let g := Stacks.Hilbert.pointGraph C (power C m) y
  have hL : List.ofFn
      (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme (power C (m + 1)).left)
        x (CurvePowerGraphCartier.graphClass C m y)) =
      xs ++ [CurvePowerGraphCartier.graphClass C m y] := by
    rw [List.ofFn_succ', List.concat_eq_append]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [List.ofFn_get]
  have hR : List.ofFn (fun j => Stacks.Picard.schemePullbackClass g (x j)) =
      xs.map (Stacks.Picard.schemePullbackClass g) := by
    have h := congrArg (List.map (Stacks.Picard.schemePullbackClass g)) (List.ofFn_get xs)
    simpa only [List.map_ofFn, Function.comp_def, x] using h
  have hl := CurvePowerPointTrace.wordDegree_ofFn k (power C (m + 1)).hom
    (Fin.snoc (α := fun _ => Stacks.Picard.ofScheme (power C (m + 1)).left)
      x (CurvePowerGraphCartier.graphClass C m y))
  have hr := CurvePowerPointTrace.wordDegree_ofFn k (power C m).hom
    (fun j => Stacks.Picard.schemePullbackClass g (x j))
  have hwl := congrArg (fun ws => CurvePowerChowFunctional.wordDegree k
    (power C (m + 1)).hom (ws.map CurvePowerChowFunctional.chosenLine)) hL
  have hwr := congrArg (fun ws => CurvePowerChowFunctional.wordDegree k
    (power C m).hom (ws.map CurvePowerChowFunctional.chosenLine)) hR
  exact hwl.symm.trans (hl.trans
    ((capValue_snoc_graph k C hC m xs.length y x).trans (hr.symm.trans hwr)))

end M9Native.CurvePowerGraphCapPairing
