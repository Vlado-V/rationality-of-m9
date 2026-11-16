module

public import M9StacksIntegration.RankThreeFlagExterior
public import StacksFrontier.AlgebraicGeometry.Chow.SectionZeroScheme.WhitneyTop
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological

/-!
# The actual exterior-square top Chern cap of the named flag

This is an operational Chow-cap statement. The two actual short
exact sequences, followed by the genuine Whitney top-cap theorem,
give three actual first-Chern cap operations. It does not identify
a constructed abstract Chern rule with an operational cap by assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Chow Stacks.Chow.GenuineChern
open M9Native.MukaiBundleDeterminant

universe u

namespace M9Native.RankThreeFlagChowCap

private theorem tensor_rank {X : Scheme.{u}} (A B : X.Modules) (r s : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B s] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor A B) (r*s) :=
  SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X A B r s

local instance tensor_line_rank {X : Scheme.{u}} (A B : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 1] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor A B) 1 := by
  simpa using tensor_rank A B 1 1

local instance tensor_line_two_rank {X : Scheme.{u}} (A B : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} A 1]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} B 2] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (tensor A B) 2 := by
  simpa using tensor_rank A B 1 2

local instance exterior_rank {X : Scheme.{u}} (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (topExterior Q 2) 3 := by
  have hc : Nat.choose 3 2 = 3 := by decide
  simpa only [topExterior,hc] using
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower Q 3 2

variable {X : Scheme.{u}} (L1 L2 L3 F2 Q : X.Modules)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L1 1]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L2 1]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L3 1]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F2 2]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 3]
  (i21 : L2 ⟶ F2) (p21 : F2 ⟶ L1) (w21 : i21 ≫ p21 = 0)
  (h21 : (ShortComplex.mk i21 p21 w21).ShortExact)
  (i32 : L3 ⟶ Q) (p32 : Q ⟶ F2) (w32 : i32 ≫ p32 = 0)
  (h32 : (ShortComplex.mk i32 p32 w32).ShortExact)

include h21 in
/-- Reorder only the actual end lines of the checked tensor row by
the genuine tensor braiding; its middle bundle remains L3⊗F2. -/
theorem tensor21_reordered_shortExact :
    ∃ (a : tensor L2 L3 ⟶ tensor L3 F2) (b : tensor L3 F2 ⟶ tensor L1 L3)
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  obtain ⟨a0,b0,w0,h0⟩ :=
    RankThreeFlagDeterminant.tensor21_shortExact L1 L2 L3 F2 i21 p21 w21 h21
  let S := ShortComplex.mk a0 b0 w0
  let e1 : S.X₁ ≅ tensor L2 L3 := Scheme.Modules.tensorObjBraiding L3 L2
  let e2 : S.X₂ ≅ tensor L3 F2 := Iso.refl _
  let e3 : S.X₃ ≅ tensor L1 L3 := Scheme.Modules.tensorObjBraiding L3 L1
  let a := e1.inv ≫ S.f ≫ e2.hom
  let b := e2.inv ≫ S.g ≫ e3.hom
  have w : a ≫ b = 0 := by
    simp only [a,b,Category.assoc,Iso.hom_inv_id_assoc]
    rw [← Category.assoc S.f S.g e3.hom,S.zero,zero_comp,comp_zero]
  refine ⟨a,b,w,ShortComplex.shortExact_of_iso ?_ h0⟩
  exact ShortComplex.isoMk e1 e2 e3
    (by simp [a,S]) (by simp [b,S])

include h21 h32 in
/-- The actual operational c3(Λ²Q) cap is the composite of the
actual named pair-line first-Chern caps. The heterogeneous equality
records only the harmless reassociation of Chow grading subtraction. -/
theorem exteriorSquare_top_cap (C : ChowSituation.{u}) (q : X ⟶ C.S)
    [LocallyOfFiniteType q] (k : ℤ) (α : chowGroup C q k) :
    chernCap C 3 q (topExterior Q 2) k (Fin.last 3) α ≍
      chernCap C 1 q (tensor L2 L3) ((k-1)-1) (Fin.last 1)
        (chernCap C 1 q (tensor L1 L3) (k-1) (Fin.last 1)
          (chernCap C 1 q (tensor L1 L2) k (Fin.last 1) α)) := by
  obtain ⟨a,b,w,hW⟩ := RankThreeFlagExterior.exteriorSquare_shortExact
    L1 L2 L3 F2 Q i21 p21 w21 h21 i32 p32 w32 h32
  obtain ⟨c,d,z,hT⟩ := tensor21_reordered_shortExact L1 L2 L3 F2 i21 p21 w21 h21
  let W := ShortComplex.mk a b w
  let T := ShortComplex.mk c d z
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} W.X₂ (2+1) := exterior_rank Q
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} T.X₂ (1+1) :=
    tensor_line_two_rank L3 F2
  have hw := SectionZeroScheme.chernCap_top_eq_of_shortExact C q W hW 2 k α
  have ht := SectionZeroScheme.chernCap_top_eq_of_shortExact C q T hT 1 (k-1)
    (chernCap C 1 q (tensor L1 L2) k (Fin.last 1) α)
  exact hw.trans ht

end M9Native.RankThreeFlagChowCap

