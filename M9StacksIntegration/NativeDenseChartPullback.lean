module

public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# Actual native point density on represented etale chart pullbacks

This is the arbitrary-source version of the geometric argument in the pinned
native `Spaces.PointsDenseBaseChange`: the exact range/preimage identity and
openness of the etale point map give density, and the genuine represented
point homeomorphisms retain the actual underlying scheme map.
-/

set_option autoImplicit false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace M9StacksIntegration.NativeDenseChartPullback
attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An actual dense native map, pulled back along an actual represented
etale chart, has a genuinely dense underlying scheme map. The original
native source is arbitrary, rather than assumed to be a represented scheme. -/
theorem denseRange_toScheme_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V U : BigFppfOver B S hS} (f : X ⟶ Y)
    (a : yoneda.obj V ⟶ X) (r : V ⟶ U) (q : yoneda.obj U ⟶ Y)
    (h : IsPullback a (yoneda.map r) f q)
    (hq : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q)
    (hd : DenseRange (Space.pointsMap B S hS X f)) :
    DenseRange ((BigFppfOver.toScheme B S hS).map r) := by
  have hrange := Space.preimage_image_pointsMap_of_isPullback B S hS h Set.univ
  rw [Set.image_univ, Set.preimage_univ, Set.image_univ] at hrange
  have hpd : DenseRange (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map r)) := by
    change Dense (Set.range (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map r)))
    rw [← hrange]
    exact hd.preimage (Space.isOpenMap_pointsMap_of_presheafEtale B S hS q hq)
  let eU := Space.schemePointsHomeomorph B S hS U
  let eV := Space.schemePointsHomeomorph B S hS V
  have hnat (v : Space.points B S hS (yoneda.obj V)) :
      eU (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map r) v) =
        (BigFppfOver.toScheme B S hS).map r (eV v) :=
    Space.pointsToScheme_pointsMap B S hS r v
  have himage : eU '' Set.range (Space.pointsMap B S hS (yoneda.obj V) (yoneda.map r)) =
      Set.range ((BigFppfOver.toScheme B S hS).map r) := by
    ext y
    constructor
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨eV v, (hnat v).symm⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨v, rfl⟩ := eV.surjective z
      exact ⟨_, ⟨v, rfl⟩, hnat v⟩
  rw [show DenseRange ((BigFppfOver.toScheme B S hS).map r) =
    Dense (Set.range ((BigFppfOver.toScheme B S hS).map r)) from rfl, ← himage]
  exact eU.surjective.denseRange.dense_image eU.continuous hpd

end M9StacksIntegration.NativeDenseChartPullback
