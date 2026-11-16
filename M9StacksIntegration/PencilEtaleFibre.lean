module

public import M9StacksIntegration.CurveEtaleRationalFibreCard
public import M9StacksIntegration.CurveMapFiniteFlatDegree
public import M9StacksIntegration.PencilProjectiveLineBridge

/-!
# An actual four-point étale fibre from a degree-four pencil

The original native pencil constructs its nonconstant finite map after
removing the actual base locus. A smaller map degree would construct an
actual degree-three pencil by genuine effective-divisor padding. Thus
the map degree and the actual finite-flat rank equal four. The rational
étale fibre and its four original-field points are then constructed.

The no-degree-three-pencil input is a genuine lower-degree geometric
obligation. For the original transverse LG curve it is already proved
without any genus or no-degree-five premise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.PencilProjectiveLineGeometry M9Native.PencilDegreePullback

universe u

namespace M9Native.PencilEtaleFibre

attribute [local instance] isCurve_projectiveSpaceOver_one

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
  [IsCurve K f] [IsProper f] [Smooth f]
  (hdim : topologicalKrullDim X ≤ 1)

/-- No finiteness, rank, reducedness, fibre, or point tuple is assumed. -/
theorem exists_four_point_etale_fibre
    (A : LinearSeries K f hdim 4 1)
    (hno3 : ¬ Nonempty (LinearSeries K f hdim 3 1)) :
    ∃ (p : X ⟶ Line K) (hp : p ≫ toBase K = f)
      (hnc : ¬ ∃ y : Line K, ∀ x : X, p.base x = y),
      curveMapDegree f (toBase K) p hp hnc = 4 ∧
      ∃ q : Spec (.of K) ⟶ Line K, q ≫ toBase K = 𝟙 _ ∧
        Etale (pullback.snd p q) ∧
        Nat.card {a : Spec (.of K) ⟶ pullback p q //
          a ≫ pullback.snd p q = 𝟙 _} = 4 := by
  obtain ⟨p,hp,hnc,hd,hfinite⟩ :=
    PencilProjectiveLineBridge.exists_finite_map_of_pencil f hdim A
  have hlow : ¬ curveMapDegree f (toBase K) p hp hnc ≤ 3 := by
    intro h
    exact hno3 (PencilProjectiveLineBridge.nonempty_pencil_of_hasMapDegreeLE
      f hdim 3 ⟨p,hp,hnc,h⟩)
  have hdegree : curveMapDegree f (toBase K) p hp hnc = 4 := by omega
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K 1
  let : Smooth (toBase K) := smooth_of_iso_projectiveLine (toBase K) c.iso c.toBase
  let : IsNormal (Line K) := isNormal_of_isRegular _
    (isRegular_of_smooth_over_field (toBase K))
  let hr := CurveMapFiniteFlatDegree.finiteLocallyFreeOfRank_curveMapDegree
    f (toBase K) p hp hnc
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p 4 := hdegree ▸ hr
  obtain ⟨q,hq,he,hcard⟩ :=
    CurveEtaleRationalFibre.exists_fibre_card K f (toBase K) p hp hnc 4
  exact ⟨p,hp,hnc,hdegree,q,hq,he,hcard⟩

end M9Native.PencilEtaleFibre
