module

public import M9StacksIntegration.ChowKernelTensorGysin
public import M9StacksIntegration.ChowSignedVirtualLineCommutation
public import M9StacksIntegration.LineFamilyCapPower

/-!
# Actual tensor-cap input to a projective Gysin map

The input is the original top Chern cap after an actual tautological
cap power and the original flat pullback. Its operational expression
and its proper push are proved from the genuine native maps. All
transports concern only the displayed Chow degrees.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern
universe u v
namespace M9Native.ChowProjectiveTensorInput
open ChowCapWords GradedLineCapSubring GradedCapVirtualSchur

section Generic
variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)]

/-- A homogeneous product is its ordered composition, up to degree only. -/
theorem homogeneous_mul_apply_heq (a b : GradedCapFamily G) (i j : ℕ)
    (hb : b.IsHomogeneous j) (k : ℤ) (α : G k) :
    (a*b) k (i+j) α ≍ a (k-(j:ℤ)) i (b k j α) := by
  rw [mul_apply_of_homogeneous_right a hb i k α, capTo_def]
  exact gradedDegreeCast_heq _ _

/-- An actual output-degree transport in the inner operation is
absorbed into the same ordered homogeneous product. -/
theorem apply_capTo_heq (a b : GradedCapFamily G) (i j : ℕ)
    (hb : b.IsHomogeneous j) {k m : ℤ} (h : k-(j:ℤ)=m) (α : G k) :
    a m i (capTo b j h α) ≍ (a*b) k (i+j) α := by
  exact (a.apply_heq h.symm i (gradedDegreeCast_heq h (b k j α))).trans
    (homogeneous_mul_apply_heq a b i j hb k α).symm

end Generic

section Tensor
variable (C : ChowSituation.{u}) {P : Scheme.{u}} (q : P ⟶ C.S)
  [LocallyOfFiniteType q] (F : P.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
  (L : InvertibleLine P)

local instance lineInvertible :
    SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L.1 := L.2
local instance tensorRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
    (((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj F).obj L.1) r :=
  isFiniteLocallyFreeOfRank_sheafTensor F r L.1

/-- The actual top Chern cap as a homogeneous operational family. -/
def tensorTopFamily : GradedCapFamily (chowGroup C q) :=
  homComponent r (chernFamily C q
    (((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj F).obj L.1) r)

theorem tensorTopFamily_apply (k : ℤ) (α : chowGroup C q k) :
    tensorTopFamily C q F r L k r α =
      ChowProjectiveTensorPush.tensorTopCap C q F r L.1 k α := by
  rw [tensorTopFamily, homComponent_apply_self,
    chernFamily_apply_of_le C q _ r k (le_refl r)]
  rfl

theorem tensorTopFamily_homogeneous :
    (tensorTopFamily C q F r L).IsHomogeneous r :=
  isHomogeneous_homComponent r _

/-- Commutation here is derived from the original tensor bundle and
the same original line, rather than supplied as an input. -/
theorem line_commute_tensorTopFamily :
    Commute (lineFamily C q L) (tensorTopFamily C q F r L) :=
  commute_homComponent (lineFamily_homogeneous C q L)
    (ChowChernLineCommutation.chernFamily_commute_lineFamily C q
      (((Stacks.SheafOfModules.Tensor.sheafTensor P.sheaf).obj F).obj L.1) r L).symm r

end Tensor

variable {X : Scheme.{u}} (E : X.Modules) (n : ℕ)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E (n+1)]
  (F : X.Modules) (r : ℕ)
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
  (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- The original actual class before the genuine proper pushforward. -/
def tensorInput (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k) :
    letI := hE.isFiniteLocallyFree
    letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
    chowGroup C (bundleProj E ≫ q) (k-b) := by
  letI := hE.isFiniteLocallyFree
  letI := @Stacks.Chow.flat_bundleProj X E n hE
  letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  exact chowGroupCast C (bundleProj E ≫ q) (by omega)
    (ChowProjectiveTensorPush.tensorTopCap C (bundleProj E ≫ q)
      ((Scheme.Modules.pullback (bundleProj E)).obj F) r (bundleTwist E) (k+n-a)
      (capPow C (bundleProj E ≫ q) (invCap C (bundleProj E ≫ q) (bundleTwist E))
        a (k+n) (k+n-a) (by ring)
        (bundlePullback C q (bundleProj E ≫ q) (bundleProj E) rfl n
          (@Stacks.Chow.relativeDimension_bundleProj X E n hE) k α)))

/-- The actual input followed by its literal proper push is precisely
the original geometric tensor Gysin operation. -/
theorem push_tensorInput :
    letI := hE.isFiniteLocallyFree
    letI := @Stacks.Chow.flat_bundleProj X E n hE
    letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
    ∀ (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k),
    ChowLineProperPush.properPush C (bundleProj E ≫ q) q (bundleProj E) rfl (k-b)
      (tensorInput E n F r C q a b hab k α) =
      ChowProjectiveTensorPush.tensorProjection E n F r C q a b hab k α := by
  letI := hE.isFiniteLocallyFree
  letI := @Stacks.Chow.flat_bundleProj X E n hE
  letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  intro a b hab k α
  rfl

/-- The pushed original input has the true signed inverse-source value. -/
theorem push_tensorInput_eq_signed :
    letI := hE.isFiniteLocallyFree
    letI := @Stacks.Chow.flat_bundleProj X E n hE
    letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
    ∀ (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k),
    ChowLineProperPush.properPush C (bundleProj E ≫ q) q (bundleProj E) rfl (k-b)
      (tensorInput E n F r C q a b hab k α) =
      ChowSignedVirtualFamily.family C q F E r (n+1) k b α := by
  letI := hE.isFiniteLocallyFree
  letI := @Stacks.Chow.flat_bundleProj X E n hE
  letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  intro a b hab k α
  rw [push_tensorInput,
    ChowProjectiveTensorPushFormula.tensorProjection_eq_chern_mul_moment,
    ChowProjectiveMomentInverse.momentFamily_eq_signed_inverse]
  rfl

/-- Operational notation for the same actual input, with the same
original quotient line and true flat pullback. -/
theorem tensorInput_eq_family :
    letI := hE.isFiniteLocallyFree
    letI := @Stacks.Chow.flat_bundleProj X E n hE
    letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
    ∀ (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k),
    tensorInput E n F r C q a b hab k α =
      capTo
        (tensorTopFamily C (bundleProj E ≫ q)
          ((Scheme.Modules.pullback (bundleProj E)).obj F) r
          ⟨bundleTwist E, Stacks.Chow.isInvertible_bundleTwist E⟩ *
          lineFamily C (bundleProj E ≫ q)
            ⟨bundleTwist E, Stacks.Chow.isInvertible_bundleTwist E⟩ ^ a)
        (r+a) (by push_cast; omega)
        (bundlePullback C q (bundleProj E ≫ q) (bundleProj E) rfl n
          (@Stacks.Chow.relativeDimension_bundleProj X E n hE) k α) := by
  letI := hE.isFiniteLocallyFree
  letI := @Stacks.Chow.flat_bundleProj X E n hE
  letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  intro a b hab k α
  let L : InvertibleLine (bundle E) :=
    ⟨bundleTwist E, Stacks.Chow.isInvertible_bundleTwist E⟩
  let B := tensorTopFamily C (bundleProj E ≫ q)
    ((Scheme.Modules.pullback (bundleProj E)).obj F) r L
  let y := lineFamily C (bundleProj E ≫ q) L
  let γ := bundlePullback C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (@Stacks.Chow.relativeDimension_bundleProj X E n hE) k α
  have hprod := homogeneous_mul_apply_heq B (y^a) r a
    ((lineFamily_homogeneous C (bundleProj E ≫ q) L).pow a) (k+n) γ
  have hp := LineFamilyCapPower.lineFamily_pow_apply C (bundleProj E ≫ q) L a (k+n) γ
  apply eq_of_heq
  refine (chowGroupCast_heq C (bundleProj E ≫ q) _ _).trans ?_
  refine (heq_of_eq (tensorTopFamily_apply C (bundleProj E ≫ q)
    ((Scheme.Modules.pullback (bundleProj E)).obj F) r L (k+n-a) _)).symm.trans ?_
  refine (heq_of_eq (congrArg (fun z => B (k+n-a) r z) hp)).symm.trans ?_
  exact hprod.symm.trans (gradedDegreeCast_heq _ _).symm

/-- An extra cap by the SAME original quotient line raises the genuine
input exponent by one. Tensor/line commutation is derived internally. -/
theorem line_tensorInput_succ :
    letI := hE.isFiniteLocallyFree
    letI := @Stacks.Chow.flat_bundleProj X E n hE
    letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
    letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
    ∀ (a b : ℕ) (hab : r+a=n+b) (k : ℤ) (α : chowGroup C q k),
    lineFamily C (bundleProj E ≫ q)
        ⟨bundleTwist E, Stacks.Chow.isInvertible_bundleTwist E⟩ (k-b) 1
        (tensorInput E n F r C q a b hab k α) ≍
      tensorInput E n F r C q (a+1) (b+1) (by omega) k α := by
  letI := hE.isFiniteLocallyFree
  letI := @Stacks.Chow.flat_bundleProj X E n hE
  letI := @Stacks.Chow.locallyOfFiniteType_bundleProj X E n hE
  letI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (bundleProj E) F r
  intro a b hab k α
  let L : InvertibleLine (bundle E) :=
    ⟨bundleTwist E, Stacks.Chow.isInvertible_bundleTwist E⟩
  let B := tensorTopFamily C (bundleProj E ≫ q)
    ((Scheme.Modules.pullback (bundleProj E)).obj F) r L
  let y := lineFamily C (bundleProj E ≫ q) L
  let γ := bundlePullback C q (bundleProj E ≫ q) (bundleProj E) rfl n
    (@Stacks.Chow.relativeDimension_bundleProj X E n hE) k α
  have hB : (B*y^a).IsHomogeneous (r+a) :=
    (tensorTopFamily_homogeneous C (bundleProj E ≫ q)
      ((Scheme.Modules.pullback (bundleProj E)).obj F) r L).mul
      ((lineFamily_homogeneous C (bundleProj E ≫ q) L).pow a)
  have hcomm : Commute y B := line_commute_tensorTopFamily C (bundleProj E ≫ q)
    ((Scheme.Modules.pullback (bundleProj E)).obj F) r L
  have hfamily : y*(B*y^a)=B*y^(a+1) := by
    rw [← mul_assoc, hcomm.eq, mul_assoc, ← pow_succ']
  have hInput := tensorInput_eq_family E n F r C q a b hab k α
  have hNext := tensorInput_eq_family E n F r C q (a+1) (b+1) (by omega) k α
  refine (heq_of_eq (congrArg (fun z => y (k-b) 1 z) hInput)).trans ?_
  refine (apply_capTo_heq y (B*y^a) 1 (r+a) hB (by push_cast; omega) γ).trans ?_
  have hvalue : (y*(B*y^a)) (k+n) (1+(r+a)) γ ≍
      (B*y^(a+1)) (k+n) (r+(a+1)) γ := by
    rw [hfamily]
    exact ChowProjectiveTensorPushFormula.family_apply_heq _ rfl (by omega) HEq.rfl
  refine hvalue.trans ?_
  exact (gradedDegreeCast_heq _ _).symm.trans (heq_of_eq hNext).symm

end M9Native.ChowProjectiveTensorInput
