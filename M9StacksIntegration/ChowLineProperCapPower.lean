module

public import M9StacksIntegration.ChowLineProperPush
public import M9StacksIntegration.LineFamilyCapPower

/-! Native proper-push compatibility for actual line-cap powers in a
specified output grade. Degree normalization is proved on abstract
scheme variables, before applying the theorem to large original models.
An actual line pullback isomorphism is the geometric input; compatibility
of cap operations is derived from the native proper Chern theorem. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory Stacks.Chow
universe u
namespace M9Native.ChowLineProperCapPower
open ChowCapWords

theorem properPush_capPow (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (qX : X ⟶ C.S) [LocallyOfFiniteType qX]
    (qY : Y ⟶ C.S) [LocallyOfFiniteType qY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ qY = qX)
    (L : InvertibleLine Y) (L' : InvertibleLine X)
    (e : L'.1 ≅ (Scheme.Modules.pullback p).obj L.1)
    (n : ℕ) (k m : ℤ) (h : k = m + (n : ℤ)) (α : chowGroup C qX k) :
    ChowLineProperPush.properPush C qX qY p hp m
      (capPow C qX (lineCap C qX L') n k m h α) =
    capPow C qY (lineCap C qY L) n k m h
      (ChowLineProperPush.properPush C qX qY p hp k α) := by
  have hm : m = k - (n : ℤ) := by omega
  subst m
  have ht := ChowLineProperPush.properPush_lineFamily_pow_apply C qX qY p hp L L' e
    n k n α
  simpa only [LineFamilyCapPower.lineFamily_pow_apply] using ht

end M9Native.ChowLineProperCapPower
