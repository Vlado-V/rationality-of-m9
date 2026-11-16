module

public import M9StacksIntegration.IdealIntersectionPullback

/-! The full pullback of an actual closed immersion is the subscheme
of the actual pulled kernel ideal. Native closed-immersion image
isomorphisms preserve both original projections. No reduction,
support comparison, or supplied Cartesian-isomorphism premise occurs. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.ClosedPullbackKernelIso

variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (f : Z ⟶ X)

def leftIso : (i.ker.comap f).subscheme ≅ pullback f i :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme
    (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f).symm) ≪≫
    (asIso (pullback.fst f i).toImage).symm

@[reassoc] theorem leftIso_hom_fst :
    (leftIso i f).hom ≫ pullback.fst f i = (i.ker.comap f).subschemeι := by
  rw [leftIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    LagrangianMatrixChart.asIso_toImage_inv_imageι]
  exact LagrangianMatrixChart.eqToIso_subscheme_ι _ _
    (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i f).symm

/-- The original closed-subscheme-first orientation. -/
def iso : (i.ker.comap f).subscheme ≅ pullback i f :=
  leftIso i f ≪≫ pullbackSymmetry f i

@[reassoc] theorem iso_hom_snd :
    (iso i f).hom ≫ pullback.snd i f = (i.ker.comap f).subschemeι := by
  simp only [iso, Iso.trans_hom, Category.assoc, pullbackSymmetry_hom_comp_snd,
    leftIso_hom_fst]

@[reassoc] theorem iso_hom_toBase :
    (iso i f).hom ≫ pullback.fst i f ≫ i = (i.ker.comap f).subschemeι ≫ f := by
  rw [pullback.condition, ← Category.assoc, iso_hom_snd]

end M9Native.ClosedPullbackKernelIso
