module

public import M9StacksIntegration.AllTestBoundedCurveSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Native cartesian covers over arbitrary bases and actual relocalization

The first lemma generalizes the checked field-base cover argument to an
arbitrary scheme base. The other constructions use the actual lower-shriek
extension, whose scheme charts and pullback squares preserve the same
underlying schemes and maps. No comparison equivalence is assumed.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestNativeCartesianCover
universe u
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual descent of an fppf-local property from one cartesian schematic
etale-surjective cover, over any native base scheme. -/
theorem property_of_schematic_cover
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u+1} B S hS)]
    (X : AlgebraicSpaces B S hS) {Z U T : BigFppfOver B S hS}
    (r : yoneda.obj Z ⟶ X.obj) (π : X.obj ⟶ yoneda.obj T) (q : Z ⟶ U) (v : U ⟶ T)
    (h : IsPullback r (yoneda.map q) π (yoneda.map v))
    (hs : Surjective ((BigFppfOver.toScheme B S hS).map v))
    (he : Etale ((BigFppfOver.toScheme B S hS).map v))
    (hq : P (schemeSpaceMap q)) : P (ObjectProperty.homMk π : X ⟶ schemeSpace T) := by
  let f : X ⟶ schemeSpace T := ObjectProperty.homMk π
  let a : schemeSpace U ⟶ schemeSpace T := schemeSpaceMap v
  have hsq : IsPullback (ObjectProperty.homMk r : schemeSpace Z ⟶ X)
      (schemeSpaceMap q) f a :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι (IsAlgebraicSpace B S hS)) h
  have hR := Space.ofArrows_atlas_mem_fppf_precoverage.{u, u+1} B S hS
    (isAlgebraicSpace_yoneda B S hS T)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ v).2 hs)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ v).2 he)
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hR
  intro V g _ hg
  obtain ⟨i⟩ := hg
  change P (pullback.snd f a)
  rw [← hsq.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso _ _).mpr hq

variable (W : Scheme.{u}) (hW : B.Contains W) (h : B.obj hW ⟶ B.obj hS)

/-- The actual lower-shriek extension of an actual native algebraic space. -/
def extendedSpace (X : AlgebraicSpaces B W hW) : AlgebraicSpaces B S hS :=
  ⟨(OverShriek.relocalizePresheafFunctor h).obj X.obj,
    Space.isAlgebraicSpace_relocalize B (B.obj hW) (B.obj hS) h X.obj X.property⟩

/-- The extended projection, using the actual representable comparison. -/
def extendedProjection {X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B W hW) (π : X ⟶ yoneda.obj T) :
    (OverShriek.relocalizePresheafFunctor h).obj X ⟶ yoneda.obj ((Over.map h).obj T) :=
  (OverShriek.relocalizePresheafFunctor h).map π ≫
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T).hom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The lower-shriek extension preserves the actual schematic chart square,
including its entire cartesian universal property. -/
theorem extended_square {X : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    {Z U T : BigFppfOver B W hW}
    (r : yoneda.obj Z ⟶ X) (π : X ⟶ yoneda.obj T) (q : Z ⟶ U) (v : U ⟶ T)
    (hcart : IsPullback r (yoneda.map q) π (yoneda.map v)) :
    IsPullback (relocalizeChart B W S hW hS h r)
      (yoneda.map ((Over.map h).map q)) (extendedProjection B S hS W hW h T π)
      (yoneda.map ((Over.map h).map v)) := by
  apply (hcart.map (OverShriek.relocalizePresheafFunctor h)).of_iso
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h Z) (Iso.refl _)
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h U)
    (relocalizedYonedaIso B (B.obj hW) (B.obj hS) h T)
  · simp only [Iso.refl_hom, Category.comp_id, relocalizeChart, Iso.hom_inv_id_assoc]
  · exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h q
  · simp only [Iso.refl_hom, extendedProjection, Category.id_comp]
  · exact relocalizedYonedaIso_naturality B (B.obj hW) (B.obj hS) h v

end M9StacksIntegration.AllTestNativeCartesianCover
