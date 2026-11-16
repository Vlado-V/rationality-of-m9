module

public import M9StacksIntegration.PencilEtaleFibre
public import Mathlib.Data.Fintype.EquivFin

/-!
# The selected four actual points of the full étale pencil fibre

The original pencil and the absence of a degree-three pencil construct
all data. The four labels enumerate the complete actual fibre, and their
maps to the original curve are distinct. No fibre, point tuple, rank,
reducedness, or generation assumption is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.PencilProjectiveLineGeometry M9Native.PencilDegreePullback

universe u

namespace M9Native.PencilFourPointFibre

attribute [local instance] isCurve_projectiveSpaceOver_one

/-- All points are sections of the literal full pullback fibre. -/
structure FourPointFibre (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f] where
  map : X ⟶ Line K
  overBase : map ≫ toBase K = f
  nonconstant : ¬ ∃ y : Line K, ∀ x : X, map.base x = y
  degree_four : curveMapDegree f (toBase K) map overBase nonconstant = 4
  rank_four : Stacks.Morphisms.IsFiniteLocallyFreeOfRank map 4
  point : Spec (.of K) ⟶ Line K
  point_overBase : point ≫ toBase K = 𝟙 _
  fibre_etale : Etale (pullback.snd map point)
  enumeration : Fin 4 ≃ {a : Spec (.of K) ⟶ pullback map point //
    a ≫ pullback.snd map point = 𝟙 _}

variable {K : Type u} [Field K] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of K)} [IsCurve K f]

/-- The four original-field points of the original curve. -/
def curvePoint (D : FourPointFibre K f) (i : Fin 4) : Spec (.of K) ⟶ X :=
  (D.enumeration i).1 ≫ pullback.fst D.map D.point

/-- Their actual pencil images are the selected rational target point. -/
theorem curvePoint_map (D : FourPointFibre K f) (i : Fin 4) :
    curvePoint D i ≫ D.map = D.point := by
  rw [curvePoint, Category.assoc, pullback.condition, ← Category.assoc,
    (D.enumeration i).2, Category.id_comp]

/-- They are rational over the original structural field map. -/
theorem curvePoint_overBase (D : FourPointFibre K f) (i : Fin 4) :
    curvePoint D i ≫ f = 𝟙 _ := by
  calc
    curvePoint D i ≫ f = curvePoint D i ≫ (D.map ≫ toBase K) :=
      congrArg (fun t => curvePoint D i ≫ t) D.overBase.symm
    _ = (curvePoint D i ≫ D.map) ≫ toBase K := (Category.assoc _ _ _).symm
    _ = 𝟙 _ := by rw [curvePoint_map, D.point_overBase]

/-- Equality on the original curve forces equality in the full fibre. -/
theorem curvePoint_injective (D : FourPointFibre K f) :
    Function.Injective (curvePoint D) := by
  intro i j h
  apply D.enumeration.injective
  apply Subtype.ext
  apply pullback.hom_ext
  · exact h
  · exact (D.enumeration i).2.trans (D.enumeration j).2.symm

/-- Every original-field section of the full fibre has one of these four
labels, so the construction retains the entire finite scheme. -/
theorem enumeration_surjective (D : FourPointFibre K f)
    (a : Spec (.of K) ⟶ pullback D.map D.point)
    (ha : a ≫ pullback.snd D.map D.point = 𝟙 _) :
    ∃ i : Fin 4, (D.enumeration i).1 = a := by
  obtain ⟨i,hi⟩ := D.enumeration.surjective ⟨a,ha⟩
  exact ⟨i,congrArg Subtype.val hi⟩

variable [IsAlgClosed K] [CharZero K] [IsProper f] [Smooth f]

/-- The data come from the original pencil and a genuine lower-degree
obstruction, with degree and finite-flat rank both proved to equal four. -/
theorem nonempty_fourPointFibre (hdim : topologicalKrullDim X ≤ 1)
    (A : LinearSeries K f hdim 4 1)
    (hno3 : ¬ Nonempty (LinearSeries K f hdim 3 1)) :
    Nonempty (FourPointFibre K f) := by
  classical
  obtain ⟨p,hp,hnc,hd,q,hq,he,hcard⟩ :=
    PencilEtaleFibre.exists_four_point_etale_fibre K f hdim A hno3
  let c := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K 1
  let : Smooth (toBase K) := smooth_of_iso_projectiveLine (toBase K) c.iso c.toBase
  let : IsNormal (Line K) := isNormal_of_isRegular _
    (isRegular_of_smooth_over_field (toBase K))
  have hr := CurveMapFiniteFlatDegree.finiteLocallyFreeOfRank_curveMapDegree
    f (toBase K) p hp hnc
  have hr4 : Stacks.Morphisms.IsFiniteLocallyFreeOfRank p 4 := hd ▸ hr
  let S := {a : Spec (.of K) ⟶ pullback p q // a ≫ pullback.snd p q = 𝟙 _}
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let : Fintype S := Fintype.ofFinite S
  have hc : Fintype.card S = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  exact ⟨⟨p,hp,hnc,hd,hr4,q,hq,he,(Fintype.equivFinOfCardEq hc).symm⟩⟩

end M9Native.PencilFourPointFibre
