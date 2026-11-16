module

public import M9StacksIntegration.SectionZeroSubbundle

/-! A full ideal comparison in an actual cartesian square gives the
actual cartesian zero scheme, with its original base projection. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
namespace M9Native.ClosedIdealPullbackPaste

variable {X Y P Q : Scheme.{u}} (p : P ⟶ X) (q : Q ⟶ Y) (b : Q ⟶ P) (g : Y ⟶ X)
  (hsq : IsPullback q b g p) (I : P.IdealSheafData) (J : Q.IdealSheafData)
  (hJ : J = I.comap b)

def zeroMap : J.subscheme ⟶ I.subscheme :=
  (eqToIso (congrArg (fun A : Q.IdealSheafData => A.subscheme) hJ)).hom ≫
    (I.comapIso b).hom ≫ pullback.snd b I.subschemeι

@[reassoc]
theorem zeroMap_inclusion : zeroMap b I J hJ ≫ I.subschemeι = J.subschemeι ≫ b := by
  simp only [zeroMap,Category.assoc]
  rw [← pullback.condition,Scheme.IdealSheafData.comapIso_hom_fst_assoc]
  cases hJ
  simp

include hsq in
theorem zero_isPullback : IsPullback (J.subschemeι ≫ q)
    (zeroMap b I J hJ) g (I.subschemeι ≫ p) := by
  have hz : IsPullback J.subschemeι (zeroMap b I J hJ) b I.subschemeι :=
    isPullback_of_isClosedImmersion J.subschemeι I.subschemeι
      (zeroMap b I J hJ) b (zeroMap_inclusion b I J hJ).symm
      (by rw [Scheme.IdealSheafData.ker_subschemeι,Scheme.IdealSheafData.ker_subschemeι,hJ])
  exact (hz.flip.paste_vert hsq.flip).flip

def zeroIsoPullback : J.subscheme ≅ pullback g (I.subschemeι ≫ p) :=
  (zero_isPullback p q b g hsq I J hJ).isoPullback

@[reassoc]
theorem zeroIsoPullback_hom_fst : (zeroIsoPullback p q b g hsq I J hJ).hom ≫
    pullback.fst g (I.subschemeι ≫ p) = J.subschemeι ≫ q :=
  (zero_isPullback p q b g hsq I J hJ).isoPullback_hom_fst

end M9Native.ClosedIdealPullbackPaste
