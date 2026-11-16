module

public import M9StacksIntegration.DirectC9Cohomology
public import M9StacksIntegration.FiniteFlatLineCohomology
public import M9StacksIntegration.PoincareOrdinaryDegreeZero
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDegreeZeroFibres

/-!
# The actual ordinary E10 and F10 on the actual ninth curve power

All bundle ranks are consequences of the actual residue-field cohomology
calculations and native cohomology-and-base-change. The restriction term
is the direct image of the actual line on the actual tenth-point divisor.
The source and target below are actual ordinary module pushforwards.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 10000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.CurvePower
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace M9Native.DirectC9Bundles

/-- Native degree-zero concentration applied to the actual standard fibres. -/
theorem line_hasDerivedRank_of_fibreFinrank_baseChange {Y T : Scheme.{u}} (π : Y ⟶ T)
    [IsProper π] [Flat π] (hfp : FinitePresentation π) (L : Y.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (r : ℕ)
    (hcoh : ∀ (t : T) (n : ℕ), Module.finrank (T.residueField t)
      (cohomologyOverField (T.residueField t) (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (π.fiberι t)).obj L) n) = if n = 0 then r else 0)
    {Y' T' : Scheme.{u}} (a : T' ⟶ T) (π' : Y' ⟶ T') (q : Y' ⟶ Y)
    (hsq : IsPullback q π' π a) :
    HasDerivedPushforwardRank π' ((Scheme.Modules.pullback q).obj L) 0 r := by
  have hLF := isFinitePresentation_and_isFlatOver_of_isInvertible π L hL
  have hfib : ∀ t : T, ∃ (Yt : Scheme.{u}) (πt : Yt ⟶ Spec (T.residueField t)) (ιt : Yt ⟶ Y),
      IsPullback ιt πt π (T.fromSpecResidueField t) ∧
      Module.finrank (T.residueField t)
        (cohomologyOverField (T.residueField t) πt ((Scheme.Modules.pullback ιt).obj L) 0) = r ∧
      ∀ n : ℕ, 0 < n → Module.finrank (T.residueField t)
        (cohomologyOverField (T.residueField t) πt ((Scheme.Modules.pullback ιt).obj L) n) = 0 := by
    intro t
    refine ⟨π.fiber t,π.fiberToSpecResidueField t,π.fiberι t,
      IsPullback.of_hasPullback _ _,?_,?_⟩
    · simpa only [ite_eq_left rfl,ite_true] using hcoh t 0
    · intro n hn
      simpa only [ite_eq_right (Nat.ne_of_gt hn),ite_false] using hcoh t n
  exact hasDerivedPushforwardRank_zero_of_fibres π hfp L hLF.1 hLF.2 r hfib a π' q hsq

/-- The actual original direct image, as the identity-base-change case. -/
theorem line_hasDerivedRank_of_fibreFinrank {Y T : Scheme.{u}} (π : Y ⟶ T)
    [IsProper π] [Flat π] (hfp : FinitePresentation π) (L : Y.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L] (r : ℕ)
    (hcoh : ∀ (t : T) (n : ℕ), Module.finrank (T.residueField t)
      (cohomologyOverField (T.residueField t) (π.fiberToSpecResidueField t)
        ((Scheme.Modules.pullback (π.fiberι t)).obj L) n) = if n = 0 then r else 0) :
    HasDerivedPushforwardRank π L 0 r := by
  have h := line_hasDerivedRank_of_fibreFinrank_baseChange π hfp L r hcoh
    (𝟙 T) π (𝟙 Y) IsPullback.of_id_fst
  exact HasDerivedPushforwardRank.of_iso ((Scheme.Modules.pullbackId Y).app L) h

/-- A line on an actual finite-flat rank-r scheme has an actual rank-r
bundle as its derived direct image in degree zero. -/
theorem finiteFlat_line_hasDerivedRank {Z T : Scheme.{u}} (p : Z ⟶ T) (r : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank p r] (L : Z.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L] :
    HasDerivedPushforwardRank p L 0 r := by
  have hp := (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation p).mp
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree p r)
  letI : IsFinite p := hp.1
  letI : Flat p := hp.2.1
  letI : LocallyOfFinitePresentation p := hp.2.2
  letI : IsProper p := (IsFinite.iff_isProper_and_isAffineHom.mp hp.1).1
  have hfp : FinitePresentation p := ⟨inferInstance,inferInstance,IsSeparated.instQuasiSeparated _⟩
  apply line_hasDerivedRank_of_fibreFinrank p hfp L r
  intro t n
  letI : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (p.fiberToSpecResidueField t) r :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback (IsPullback.of_hasPullback _ _)
  letI hLf := Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (p.fiberι t) L
  letI : SheafOfModules.IsInvertible (p.fiber t).presheaf (p.fiber t).ringCatSheaf.2
      ((Scheme.Modules.pullback (p.fiberι t)).obj L) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hLf
  exact FiniteFlatLineCohomology.finiteLocallyFree_lineBundle_cohomology
    (T.residueField t) (p.fiberToSpecResidueField t) r
    ((Scheme.Modules.pullback (p.fiberι t)).obj L) n

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection)
open PoincareChern (lineClass)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

theorem largeDegree_line_hasDerivedRank (L : (familySpace C).Modules)
    [hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L] (hg : genus C.hom = 9) (r : ℕ) (hr : 9 ≤ r)
    (hd : ∀ t : (power C 9).left,
      relativeInvertibleDegreeHomAt (familyProjection C)
        (DirectC9FibreGeometry.fibre_dimension_le_one k C) t (@lineClass (familySpace C) L hL) =
          (r : ℤ) + 8) : HasDerivedPushforwardRank (familyProjection C) L 0 r :=
  line_hasDerivedRank_of_fibreFinrank (familyProjection C)
    (DirectC9FibreGeometry.projection_finitePresentation k C) L r
    (DirectC9Cohomology.largeDegree_fibreFinrank k C L hg r hr hd)

theorem partialLine_hasDerivedRank (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)
    (j : ℕ) (hj : j ≤ 9) :
    HasDerivedPushforwardRank (familyProjection C) (partialLine C c₀ j hj) 0 (9 + j) := by
  letI : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 (partialLine C c₀ j hj) := partialLine_isInvertible C c₀ j hj
  refine largeDegree_line_hasDerivedRank k C (partialLine C c₀ j hj) hg (9 + j) (by omega) ?_
  intro t
  have hd := DirectC9FamilyDegree.partialLine_degree C c₀
    (DirectC9FibreGeometry.fibre_dimension_le_one k C) j hj t
  exact hd.trans (by omega)

theorem twistedLine_hasDerivedRank (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)
    (q : ℕ) (hq : 8 ≤ q) :
    HasDerivedPushforwardRank (familyProjection C) (DirectC9Cohomology.twistedLine k C c₀ q) 0 (q + 1) := by
  refine largeDegree_line_hasDerivedRank k C (DirectC9Cohomology.twistedLine k C c₀ q)
    hg (q + 1) (by omega) ?_
  intro t
  exact (DirectC9Cohomology.twistedLine_degree k C c₀ q t).trans (by ring)

abbrev movingPushforward (c₀ : power C 0 ⟶ C) (j : ℕ) (hj : j ≤ 9) : (power C 9).left.Modules :=
  (Scheme.Modules.pushforward (familyProjection C)).obj (partialLine C c₀ j hj)

theorem movingPushforward_rank (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)
    (j : ℕ) (hj : j ≤ 9) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (movingPushforward k C c₀ j hj) (9 + j) :=
  PoincareChern.OrdinaryDegreeZero.ordinaryPushforward_rank_of_derivedRank
    (familyProjection C) (partialLine C c₀ j hj) (9 + j) (partialLine_hasDerivedRank k C c₀ hg j hj)

abbrev twistPushforward (c₀ : power C 0 ⟶ C) (q : ℕ) : (power C 9).left.Modules :=
  (Scheme.Modules.pushforward (familyProjection C)).obj (DirectC9Cohomology.twistedLine k C c₀ q)

theorem twistPushforward_rank (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)
    (q : ℕ) (hq : 8 ≤ q) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (twistPushforward k C c₀ q) (q + 1) :=
  PoincareChern.OrdinaryDegreeZero.ordinaryPushforward_rank_of_derivedRank
    (familyProjection C) (DirectC9Cohomology.twistedLine k C c₀ q) (q + 1)
    (twistedLine_hasDerivedRank k C c₀ hg q hq)

abbrev fixedDivisorProjection (c₀ : power C 0 ⟶ C) (q : ℕ) :
    (constantFamily C c₀ q).ideal.subscheme ⟶ (power C 9).left :=
  (constantFamily C c₀ q).ideal.subschemeι ≫ familyProjection C

instance fixedDivisorProjection_rank (c₀ : power C 0 ⟶ C) (q : ℕ) :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (fixedDivisorProjection k C c₀ q) (q + 1) :=
  (constantFamily C c₀ q).isFiniteLocallyFreeOfRank

/-- All restriction jets use the same actual degree-ten twist. -/
abbrev restrictedTwist (c₀ : power C 0 ⟶ C) (q : ℕ) :
    (constantFamily C c₀ q).ideal.subscheme.Modules :=
  (Scheme.Modules.pullback (constantFamily C c₀ q).ideal.subschemeι).obj
    (DirectC9Cohomology.twistedLine k C c₀ 9)

instance restrictedTwist_isInvertible (c₀ : power C 0 ⟶ C) (q : ℕ) :
    Stacks.SheafOfModules.IsInvertible (constantFamily C c₀ q).ideal.subscheme.presheaf
      (constantFamily C c₀ q).ideal.subscheme.ringCatSheaf.2 (restrictedTwist k C c₀ q) :=
  Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj
    (constantFamily C c₀ q).ideal.subschemeι (DirectC9Cohomology.twistedLine k C c₀ 9)

abbrev restrictionPushforward (c₀ : power C 0 ⟶ C) (q : ℕ) : (power C 9).left.Modules :=
  (Scheme.Modules.pushforward (fixedDivisorProjection k C c₀ q)).obj (restrictedTwist k C c₀ q)

theorem restrictedTwist_hasDerivedRank (c₀ : power C 0 ⟶ C) (q : ℕ) :
    HasDerivedPushforwardRank (fixedDivisorProjection k C c₀ q) (restrictedTwist k C c₀ q) 0 (q + 1) :=
  finiteFlat_line_hasDerivedRank (fixedDivisorProjection k C c₀ q) (q + 1) (restrictedTwist k C c₀ q)

theorem restrictionPushforward_rank (c₀ : power C 0 ⟶ C) (q : ℕ) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (restrictionPushforward k C c₀ q) (q + 1) :=
  PoincareChern.OrdinaryDegreeZero.ordinaryPushforward_rank_of_derivedRank
    (fixedDivisorProjection k C c₀ q) (restrictedTwist k C c₀ q) (q + 1)
    (restrictedTwist_hasDerivedRank k C c₀ q)

abbrev E10 (c₀ : power C 0 ⟶ C) : (power C 9).left.Modules := twistPushforward k C c₀ 9
abbrev F10 (c₀ : power C 0 ⟶ C) : (power C 9).left.Modules := restrictionPushforward k C c₀ 9
abbrev E18 (c₀ : power C 0 ⟶ C) : (power C 9).left.Modules := twistPushforward k C c₀ 17

theorem E10_rank (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E10 k C c₀) 10 :=
  twistPushforward_rank k C c₀ hg 9 (by omega)

theorem F10_rank (c₀ : power C 0 ⟶ C) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (F10 k C c₀) 10 :=
  restrictionPushforward_rank k C c₀ 9

theorem E18_rank (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (E18 k C c₀) 18 :=
  twistPushforward_rank k C c₀ hg 17 (by omega)

end M9Native.DirectC9Bundles
