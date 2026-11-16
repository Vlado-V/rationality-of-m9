module

public import M9StacksIntegration.ChowRegularSectionClass
public import M9StacksIntegration.ChowProjectiveTensorPushFormula
public import M9StacksIntegration.ChowProjectiveFreeMoments

/-!
# Actual regular-zero incidence on a trivialized projective line bundle

The ambient scheme is the genuine projective bundle of an actual
rank-two bundle with an actual free trivialization. The rank-three
bundle is the original pullback tensored, in the native order, with
O(1). Genuine Gysin/moment formulas show that its top cap pushes to
c2 of the original bundle. Native Stacks0FA9 then identifies the FULL
regular zero scheme's actual fundamental push with that same class.
No zero-class, pushforward, Chern, or incidence-image identity is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Stacks.Chow Stacks.Chow.GenuineChern

universe u v

namespace M9Native.ChowP1RegularSection

section GradedTransport

variable {G H : ℤ → Type v} [∀ k, AddCommGroup (G k)] [∀ k, AddCommGroup (H k)]

/-- Actual unshifted additive maps preserve heterogeneous equality in equal grades. -/
theorem gradedMap_heq (p : ∀ k, G k →+ H k) {a b : ℤ} (hab : a=b)
    {x : G a} {y : G b} (hxy : x ≍ y) : p a x ≍ p b y := by
  cases hab
  cases hxy
  rfl

/-- An actual degree-lowering additive map preserves equal-grade heterogeneous inputs. -/
theorem loweringMap_heq (d : ℤ) (p : ∀ k, G k →+ H (k-d))
    {a b : ℤ} (hab : a=b) {x : G a} {y : G b} (hxy : x ≍ y) :
    p a x ≍ p b y := by
  cases hab
  cases hxy
  rfl

end GradedTransport

variable {X : Scheme.{u}} (E : X.Modules)
  [hE : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 2]

local instance sourceFinite : SheafOfModules.IsFiniteLocallyFree.{u,u,u} E :=
  hE.isFiniteLocallyFree

abbrev ambient : Scheme.{u} := bundle E
abbrev projection : ambient E ⟶ X := bundleProj E
abbrev tautologicalLine : (ambient E).Modules := bundleTwist E
local instance projectionFlat : Flat (projection E) := @flat_bundleProj X E 1 hE
local instance projectionLFT : LocallyOfFiniteType (projection E) := @locallyOfFiniteType_bundleProj X E 1 hE
local instance lineInvertible :
    SheafOfModules.IsInvertible (ambient E).sheaf.obj (ambient E).ringCatSheaf.property
      (tautologicalLine E) := isInvertible_bundleTwist E

variable (F : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F 3]

abbrev pulledBundle : (ambient E).Modules := (Scheme.Modules.pullback (projection E)).obj F
local instance pulledRank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (pulledBundle E F) 3 :=
  AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (projection E) F 3

/-- Literal native tensor, with the pulled rank-three bundle FIRST and original O(1) SECOND. -/
abbrev equationBundle : (ambient E).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor (ambient E).sheaf).obj
    (pulledBundle E F)).obj (tautologicalLine E))

/-- The actual tensor equation bundle has rank three. -/
theorem equationBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle E F) 3 :=
  isFiniteLocallyFreeOfRank_sheafTensor (pulledBundle E F) 3 (tautologicalLine E)
local instance equationRank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle E F) 3 := equationBundle_rank E F

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

abbrev ambientStructure : ambient E ⟶ C.S := projection E ≫ q

def ambientPull (k : ℤ) : chowGroup C q k →+ chowGroup C (ambientStructure E C q) (k+1) :=
  bundlePullback C q (ambientStructure E C q) (projection E) rfl 1
    (@relativeDimension_bundleProj X E 1 hE) k

abbrev ambientPush (k : ℤ) : chowGroup C (ambientStructure E C q) k →+ chowGroup C q k :=
  ChowLineProperPush.properPush C (ambientStructure E C q) q (projection E) rfl k

/-- The actual rank-three top cap after the genuine P1 flat pullback;
only the true displayed output-degree cast is inserted. -/
def topClass (k : ℤ) (α : chowGroup C q k) : chowGroup C (ambientStructure E C q) (k-2) :=
  chowGroupCast C (ambientStructure E C q) (show (k+1)-(3:ℤ)=k-2 by omega)
    (chernCap C 3 (ambientStructure E C q) (equationBundle E F) (k+1) (Fin.last 3)
      (ambientPull E C q k α))

/-- The frozen genuine tensor-Gysin expression with zero extra power
is precisely the original actual push of topClass. -/
theorem tensorProjection_zero_eq (k : ℤ) (α : chowGroup C q k) :
    ChowProjectiveTensorPush.tensorProjection E 1 F 3 C q 0 2 (by decide) k α =
      ambientPush E C q (k-2) (topClass E F C q k α) := by
  let qP := ambientStructure E C q
  let PF := pulledBundle E F
  let L := tautologicalLine E
  let l : ℤ := k+((1:ℕ):ℤ)-((0:ℕ):ℤ)
  let β := ambientPull E C q k α
  let γ := capPow C qP (invCap C qP L) 0 (k+((1:ℕ):ℤ)) l (by ring) β
  have hγ : γ ≍ β := by
    dsimp only [γ]
    rw [capPow_zero_apply]
    exact chowGroupCast_heq C qP (show k+((1:ℕ):ℤ)=l by dsimp [l]; omega) β
  have ht := loweringMap_heq ((3:ℕ):ℤ)
    (ChowProjectiveTensorPush.tensorTopCap C qP PF 3 L)
    (show l=k+1 by dsimp [l]; omega) hγ
  have htop : chowGroupCast C qP (show l-((3:ℕ):ℤ)=k-((2:ℕ):ℤ) by dsimp [l]; omega)
      (ChowProjectiveTensorPush.tensorTopCap C qP PF 3 L l γ) ≍ topClass E F C q k α := by
    refine (chowGroupCast_heq C qP
      (show l-((3:ℕ):ℤ)=k-((2:ℕ):ℤ) by dsimp [l]; omega) _).trans (ht.trans ?_)
    exact (chowGroupCast_heq C qP (show (k+1)-((3:ℕ):ℤ)=k-2 by omega)
      (ChowProjectiveTensorPush.tensorTopCap C qP PF 3 L (k+1) β)).symm
  apply eq_of_heq
  exact gradedMap_heq (ambientPush E C q) (show k-((2:ℕ):ℤ)=k-2 by omega) htop

/-- Actual proper P1 push of c3(pulled F tensor O1) is the ORIGINAL c2(F),
on every integer-graded original Chow class. The free trivialization is geometric data. -/
theorem push_topClass_eq_secondChern
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2)))
    (k : ℤ) (α : chowGroup C q k) :
    ambientPush E C q (k-2) (topClass E F C q k α) =
      chernCap C 3 q F k ⟨2, by decide⟩ α := by
  have h := ChowProjectiveTensorPushFormula.tensorProjection_eq_chern_mul_moment
    E 1 F 3 C q 0 2 (by decide) k α
  rw [ChowProjectiveFreeMoments.momentFamily_eq_one_of_iso_free E 1 C q e, mul_one,
    tensorProjection_zero_eq E F C q k α,
    chernFamily_apply_of_le C q F 3 k (by decide : 2 ≤ 3)] at h
  exact h

/-- The actual ambient delta dimension bound follows from the actual P1 flat morphism. -/
theorem ambient_dimension_le (n : ℤ) (hX : schemeDeltaDimension C q ≤ (n : EInt)) :
    schemeDeltaDimension C (ambientStructure E C q) ≤ ((n+1:ℤ) : EInt) :=
  SectionZeroScheme.schemeDeltaDimension_le_of_flat C q (projection E) 1
    (@relativeDimension_bundleProj X E 1 hE) hX

/-- The actual ambient fundamental class is the actual flat pullback
of the actual original base fundamental class. -/
theorem ambientPull_fundamental (n : ℤ) (hX : schemeDeltaDimension C q ≤ (n : EInt)) :
    ambientPull E C q n (fundamentalChowClass C q n) =
      fundamentalChowClass C (ambientStructure E C q) (n+1) := by
  exact SectionZeroScheme.flatPullbackChow_mk_fundamental C q (projection E) 1
    (@relativeDimension_bundleProj X E 1 hE) n hX
    (flatPullbackFactorsThroughRationalEquivalence_general C (ambientStructure E C q) q
      (projection E) rfl 1 (@relativeDimension_bundleProj X E 1 hE) n)

/-- The grade-cast topClass on the original fundamental class is the actual ambient top cap. -/
theorem topClass_fundamental_heq (n : ℤ) (hX : schemeDeltaDimension C q ≤ (n : EInt)) :
    topClass E F C q n (fundamentalChowClass C q n) ≍
      chernCap C 3 (ambientStructure E C q) (equationBundle E F) (n+1) (Fin.last 3)
        (fundamentalChowClass C (ambientStructure E C q) (n+1)) := by
  unfold topClass
  rw [ambientPull_fundamental E C q n hX]
  exact chowGroupCast_heq C (ambientStructure E C q) _ _

section Zero

variable (s : Γ(equationBundle E F,⊤))

abbrev zeroIdeal : (ambient E).IdealSheafData := zeroSchemeOfSection (ambient E) (equationBundle E F) s
abbrev zeroScheme : Scheme.{u} := (zeroIdeal E F s).subscheme
abbrev zeroInclusion : zeroScheme E F s ⟶ ambient E := (zeroIdeal E F s).subschemeι
abbrev zeroProjection : zeroScheme E F s ⟶ X := zeroInclusion E F s ≫ projection E
abbrev zeroStructure : zeroScheme E F s ⟶ C.S := zeroInclusion E F s ≫ ambientStructure E C q

theorem fundamental_heq {T : Scheme.{u}} (qT : T ⟶ C.S) [LocallyOfFiniteType qT]
    {a b : ℤ} (hab : a=b) : fundamentalChowClass C qT a ≍ fundamentalChowClass C qT b := by
  cases hab
  rfl

/-- The actual full-zero inclusion push is the actual tensor top cap,
derived from Stacks0FA9 and genuine fundamental flat pullback. -/
theorem inclusionPush_fundamental_eq_topClass (n : ℤ)
    (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C (zeroStructure E F C q s) ≤ ((n-2:ℤ) : EInt))
    (hreg : IsRegularZeroSchemeSequence C (ambientStructure E C q) (equationBundle E F) s 3 (n-2)) :
    ChowLineProperPush.properPush C (zeroStructure E F C q s) (ambientStructure E C q)
        (zeroInclusion E F s) rfl (n-2)
        (fundamentalChowClass C (zeroStructure E F C q s) (n-2)) =
      topClass E F C q n (fundamentalChowClass C q n) := by
  have hn : (n+1)-((3:ℕ):ℤ)=n-2 := by omega
  have hz := ChowRegularSectionClass.inclusionPush_fundamental_eq_topCap C
    (ambientStructure E C q) (equationBundle E F) 3 s (n+1)
    (ambient_dimension_le E C q n hX)
    (by simpa only [zeroStructure, zeroInclusion, zeroIdeal, hn] using hZ)
    (by simpa only [hn] using hreg)
  apply eq_of_heq
  refine (gradedMap_heq (fun k => ChowLineProperPush.properPush C
      (zeroStructure E F C q s) (ambientStructure E C q) (zeroInclusion E F s) rfl k)
      (show n-2=(n+1)-((3:ℕ):ℤ) by omega)
      (fundamental_heq C (zeroStructure E F C q s) (by omega))).trans ?_
  exact (heq_of_eq hz).trans (topClass_fundamental_heq E F C q n hX).symm

/-- The two ACTUAL proper pushes of the FULL regular zero fundamental
class equal the original c2(F) cap. No zero/image/class identity is assumed. -/
theorem push_zeroFundamental_eq_secondChern
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) (n : ℤ)
    (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C (zeroStructure E F C q s) ≤ ((n-2:ℤ) : EInt))
    (hreg : IsRegularZeroSchemeSequence C (ambientStructure E C q) (equationBundle E F) s 3 (n-2)) :
    ambientPush E C q (n-2)
      (ChowLineProperPush.properPush C (zeroStructure E F C q s) (ambientStructure E C q)
        (zeroInclusion E F s) rfl (n-2)
        (fundamentalChowClass C (zeroStructure E F C q s) (n-2))) =
      chernCap C 3 q F n ⟨2, by decide⟩ (fundamentalChowClass C q n) := by
  rw [inclusionPush_fundamental_eq_topClass E F C q s n hX hZ hreg]
  exact push_topClass_eq_secondChern E F C q e n (fundamentalChowClass C q n)

/-- The same conclusion for the literal composite incidence projection,
using genuine proper-pushforward composition, not a push comparison premise. -/
theorem compositePush_zeroFundamental_eq_secondChern
    (e : E ≅ SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) (n : ℤ)
    (hX : schemeDeltaDimension C q ≤ (n : EInt))
    (hZ : schemeDeltaDimension C (zeroStructure E F C q s) ≤ ((n-2:ℤ) : EInt))
    (hreg : IsRegularZeroSchemeSequence C (ambientStructure E C q) (equationBundle E F) s 3 (n-2)) :
    ChowLineProperPush.properPush C (zeroStructure E F C q s) q (zeroProjection E F s)
      (Category.assoc _ _ _) (n-2)
      (fundamentalChowClass C (zeroStructure E F C q s) (n-2)) =
      chernCap C 3 q F n ⟨2, by decide⟩ (fundamentalChowClass C q n) := by
  have hc := ChowRegularSectionClass.properPush_comp_apply C
    (zeroStructure E F C q s) (ambientStructure E C q) q
    (zeroInclusion E F s) (projection E) rfl rfl (n-2)
    (fundamentalChowClass C (zeroStructure E F C q s) (n-2))
  exact hc.symm.trans (push_zeroFundamental_eq_secondChern E F C q s e n hX hZ hreg)

end Zero

end M9Native.ChowP1RegularSection
