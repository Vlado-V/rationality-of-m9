module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertPointAddition
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections

/-!
# Actual point-divisor ordinary pushforward is section restriction

The actual closed point-graph cuts out a native point ideal. Its actual
divisor projection to the base is an isomorphism. The canonical inverse
followed by the original divisor inclusion is the original point graph.
Native pushforward-along-iso and pullback composition then identify the
ordinary image of the restricted line (indeed any module) with its
actual section pullback. No ordinary base-change/naturality, triviality,
cohomology, rank, or Chern comparison is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.GraphPointPushforward

open Stacks.Hilbert

variable {S : Scheme.{u}} (X T : Over S) (x : T ⟶ X)
  [IsClosedImmersion (pointGraph X T x)]

/-- The literal actual point-divisor projection. -/
abbrev pointProjection : (pointIdeal X T x).subscheme ⟶ T.left :=
  (pointIdeal X T x).subschemeι ≫ ((Over.pullback T.hom).obj X).hom

local instance pointProjection_isIso : IsIso (pointProjection X T x) :=
  isIso_subschemeι_pointIdeal_comp X T x

/-- The inverse projection gives the original actual section, rather
than an unidentified isomorphic graph. -/
theorem inverseProjection_comp_inclusion :
    (asIso (pointProjection X T x)).inv ≫ (pointIdeal X T x).subschemeι =
      pointGraph X T x := by
  have hle : (pointIdeal X T x).subschemeι.ker ≤ (pointGraph X T x).ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, pointIdeal]
  let a : T.left ⟶ (pointIdeal X T x).subscheme :=
    IsClosedImmersion.lift (pointIdeal X T x).subschemeι (pointGraph X T x) hle
  have ha : a ≫ (pointIdeal X T x).subschemeι = pointGraph X T x :=
    IsClosedImmersion.lift_fac _ _ hle
  have hap : a ≫ pointProjection X T x = 𝟙 _ := by
    rw [pointProjection, ← Category.assoc, ha, pointGraph_comp_hom]
  have hae : a = (asIso (pointProjection X T x)).inv := by
    apply (cancel_mono (pointProjection X T x)).1
    rw [hap]
    exact (Iso.inv_hom_id (asIso (pointProjection X T x))).symm
  exact (congrArg (fun b => b ≫ (pointIdeal X T x).subschemeι) hae).symm.trans ha

/-- The actual ordinary image along the actual point-divisor
projection equals pullback along the actual original section. -/
def pointPushforwardIso (L : ((Over.pullback T.hom).obj X).left.Modules) :
    (Scheme.Modules.pushforward (pointProjection X T x)).obj
      ((Scheme.Modules.pullback (pointIdeal X T x).subschemeι).obj L) ≅
    (Scheme.Modules.pullback (pointGraph X T x)).obj L :=
  ((Scheme.Modules.pullbackIsoPushforward (asIso (pointProjection X T x))).app
    ((Scheme.Modules.pullback (pointIdeal X T x).subschemeι).obj L)).symm ≪≫
  (Scheme.Modules.pullbackComp (asIso (pointProjection X T x)).inv
    (pointIdeal X T x).subschemeι).app L ≪≫
  (Scheme.Modules.pullbackCongr (inverseProjection_comp_inclusion X T x)).app L

/-- The same comparison starting from the two literal ordinary
pushforwards, for use with an actual divisor short exact sequence. -/
def pointDoublePushforwardIso (L : ((Over.pullback T.hom).obj X).left.Modules) :
    (Scheme.Modules.pushforward ((Over.pullback T.hom).obj X).hom).obj
      ((Scheme.Modules.pushforward (pointIdeal X T x).subschemeι).obj
        ((Scheme.Modules.pullback (pointIdeal X T x).subschemeι).obj L)) ≅
    (Scheme.Modules.pullback (pointGraph X T x)).obj L :=
  (Scheme.Modules.pushforwardComp (pointIdeal X T x).subschemeι
    ((Over.pullback T.hom).obj X).hom).app
      ((Scheme.Modules.pullback (pointIdeal X T x).subschemeι).obj L) ≪≫
    pointPushforwardIso X T x L

end M9Native.GraphPointPushforward
