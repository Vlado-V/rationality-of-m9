module

public import M9StacksIntegration.LagrangianChowPolynomials
public import M9StacksIntegration.ChowLineProperPush

/-!
# Actual polynomial line caps commute with genuine proper pushforward

The actual named line isomorphisms and native proper cap compatibility
give this for variables. Native convolution and integer linearity then
give every actual polynomial, without an ambient commutativity premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.LagrangianPolynomialProperPush

open ChowCapWords LagrangianChowPolynomials

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
  (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
  (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
  (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY = qX)
  (L : Fin 3 → InvertibleLine Y) (L' : Fin 3 → InvertibleLine X)
  (e : ∀ i, (L' i).1 ≅ (Scheme.Modules.pullback p).obj (L i).1)

include e in
theorem properPush_intertwines_evaluate (P : MvPolynomial (Fin 3) ℤ) :
    Stacks.Chow.Intertwines (ChowLineProperPush.actualPush C qX qY p hp)
      (evaluate C qX L' P) (evaluate C qY L P) := by
  apply (ChowVirtualPullback.intertwines_iff_lowering
    (ChowLineProperPush.actualPush C qX qY p hp) _ _).2
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [evaluate_C,evaluate_C]
      have hOne : (1 : GradedCapFamily (chowGroup C qX)).Intertwines (-(0 : ℤ))
          (ChowVirtualPullback.loweringPull (ChowLineProperPush.actualPush C qX qY p hp))
          (1 : GradedCapFamily (chowGroup C qY)) := GradedCapFamily.Intertwines.one
      simpa only [zsmul_one] using hOne.zsmul a
  | add P Q hP hQ =>
      rw [(evaluate C qX L').map_add P Q,(evaluate C qY L).map_add P Q]
      exact hP.add hQ
  | mul_X P i hP =>
      rw [(evaluate C qX L').map_mul P (MvPolynomial.X i),
        (evaluate C qY L).map_mul P (MvPolynomial.X i),evaluate_X,evaluate_X]
      exact hP.mul ((ChowVirtualPullback.intertwines_iff_lowering
        (ChowLineProperPush.actualPush C qX qY p hp) _ _).1
          (ChowLineProperPush.properPush_intertwines_lineFamily
            C qX qY p hp (L i) (L' i) (e i)))

include e in
/-- Literal coefficient formula for the original proper push, in every
actual Chow grade and on every actual input class. -/
theorem properPush_evaluate_apply (P : MvPolynomial (Fin 3) ℤ)
    (k : ℤ) (i : ℕ) (α : chowGroup C qX k) :
    ChowLineProperPush.properPush C qX qY p hp (k-(i:ℤ))
        (evaluate C qX L' P k i α) =
      evaluate C qY L P k i (ChowLineProperPush.properPush C qX qY p hp k α) :=
  (ChowLineProperPush.intertwines_iff C qX qY p hp _ _).1
    (properPush_intertwines_evaluate C qX qY p hp L L' e P) k i α

end M9Native.LagrangianPolynomialProperPush
