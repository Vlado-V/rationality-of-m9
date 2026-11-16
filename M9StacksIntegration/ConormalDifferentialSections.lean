/-
This module replays only the underived Pinning subsection from
AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/MoreMorphisms/NaiveCotangentBaseChangeConormalCompatibility.lean.
The namespace is changed; the original actual conormal, quotient,
comparison, and differential maps are preserved. The unused later
naive-cotangent presentation import is excluded. Original source and
Apache-2.0 license are retained under audits/conormal-differential-sections/upstream.
-/
module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.Conormal.SplitCotangentFibre
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.CoborderDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import M9StacksIntegration.SectionZeroConormal

/-! The first actual native conormal arrow on original ambient ideal sections.
No differential or conormal-class comparison is supplied as a premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction
open TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.ClosedImmersion Stacks.Immersion Stacks.ConormalSequenceRight

universe u

namespace M9Native.ConormalDifferentialSections

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- The identification of the two presentations of the conormal sheaf carries the conormal class
of a section of the categorical ideal of the closed factor to the conormal class of the
corresponding section of the sectionwise ideal. -/
theorem conormalSheafBridge_inv_unit (V : Opens i.coborderRange.toScheme)
    (s : (Stacks.Conormal.Sites.idealSheafLift i).val.obj (op V)) :
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv.val.app
        (op (i.liftCoborder ⁻¹ᵁ V))
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i)).val.app (op V) s) =
      (conormalComparison i).val.app (op V)
        ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv.val.app (op V) s) := by
  have h := congr($((modulePullbackPushforwardAdjunction
    i.liftCoborder.toLRSHom.toShHom).unit.naturality
      (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv).val.app (op V) s)
  exact h.symm

/-- **The first arrow on the conormal class of a section of the ideal of the closed factor**: it
is `1 ⊗ d s`, moved onto `i^*Ω_{X/S}` by
`Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`. -/
theorem conormalDifferential_conormalSheafBridge_inv_unit (V : Opens i.coborderRange.toScheme)
    (s : (Stacks.Conormal.Sites.idealSheafLift i).val.obj (op V)) :
    ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
        conormalDifferential i p).val.app (op (i.liftCoborder ⁻¹ᵁ V))
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i)).val.app (op V) s) =
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
          (Scheme.Modules.pushforward i.liftCoborder).map
            (coborderPullbackDifferentialsIso i p).hom).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
          (Stacks.Conormal.idealSection i.liftCoborder V s)) := by
  have h1 := conormalSheafBridge_inv_unit i V s
  have h2 := congr($(conormalComparison_comp_conormalDifferential i p).val.app (op V)
    ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv.val.app (op V) s))
  have h3 : ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv.val.app (op V) s).1 =
      Stacks.Conormal.idealSection i.liftCoborder V s :=
    congr($(Stacks.Conormal.DefiningIdealBridge.idealSheafBridge_inv_comp_ι i).val.app (op V) s)
  refine Eq.trans (congrArg ((conormalDifferential i p).val.app (op (i.liftCoborder ⁻¹ᵁ V))) h1) ?_
  refine h2.trans ?_
  refine (conormalDifferentialTranspose_val_app i p (op V) _).trans ?_
  exact congrArg (fun a => (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
          (Scheme.Modules.pushforward i.liftCoborder).map
            (coborderPullbackDifferentialsIso i p).hom).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a)) h3

/-- For a morphism `θ` out of the relative differentials of the coborder neighbourhood, the germ
at `z` of `θ (d a)` only depends on the germ of `a` at the image of `z`. -/
theorem germ_coborder_d_eq {N : Z.Modules}
    (θ : Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p) ⟶
      (Scheme.Modules.pushforward i.liftCoborder).obj N)
    (z : Z) {U₁ U₂ : Opens i.coborderRange.toScheme} (h₁ : i.liftCoborder.base z ∈ U₁)
    (h₂ : i.liftCoborder.base z ∈ U₂) (a₁ : Γ(i.coborderRange.toScheme, U₁))
    (a₂ : Γ(i.coborderRange.toScheme, U₂))
    (hgerm : i.coborderRange.toScheme.presheaf.germ U₁ _ h₁ a₁ =
      i.coborderRange.toScheme.presheaf.germ U₂ _ h₂ a₂) :
    TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf (i.liftCoborder ⁻¹ᵁ U₁) z h₁
        ((θ.val.app (op U₁)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a₁)) =
      TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf (i.liftCoborder ⁻¹ᵁ U₂) z h₂
        ((θ.val.app (op U₂)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a₂)) := by
  obtain ⟨V, hV, ι₁, ι₂, heq⟩ := i.coborderRange.toScheme.presheaf.germ_eq _ h₁ h₂ a₁ a₂ hgerm
  have key : ∀ {U : Opens i.coborderRange.toScheme} (ιU : V ⟶ U)
      (a : Γ(i.coborderRange.toScheme, U)),
      N.val.presheaf.map ((Opens.map i.liftCoborder.base).map ιU).op
          ((θ.val.app (op U)).hom
            ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a)) =
        (θ.val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
            (i.coborderRange.toScheme.presheaf.map ιU.op a)) := by
    intro U ιU a
    have hd := (Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d_map ιU.op a
    have hn := θ.val.naturality ιU.op
    refine Eq.trans ?_ (congrArg (θ.val.app (op V)).hom hd).symm
    exact (ConcreteCategory.congr_hom hn _).symm
  refine (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.val.presheaf
    ((Opens.map i.liftCoborder.base).map ι₁) z hV _).symm.trans ?_
  refine Eq.trans (congrArg _ (key ι₁ a₁)) ?_
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.val.presheaf
    ((Opens.map i.liftCoborder.base).map ι₂) z hV _)
  refine Eq.trans ?_ (congrArg _ (key ι₂ a₂)).symm
  exact congrArg (fun a => TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf _ z hV
    ((θ.val.app (op V)).hom
      ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a))) heq

/-- **The first arrow on the conormal class of a section of the ideal sheaf of `i`**: it is
`1 ⊗ d a`. The class is the image under `Stacks.Immersion.canonicalConormalQuotientMap` of a
section `a` of the ideal sheaf of `i` itself, in the ambient scheme rather than in the coborder
neighbourhood; the two descriptions are matched on germs. -/
theorem conormalDifferential_canonicalConormalQuotientMap (A : X.Opens)
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op A)) :
    ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
        conormalDifferential i p).val.app (op (i ⁻¹ᵁ A))
        ((canonicalConormalQuotientMap i).val.app (op A) y) =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Hom.relativeDifferentials p)).val.app (op A)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d (Stacks.Conormal.idealSection i A y)) := by
  refine TopCat.Presheaf.section_ext
    (⟨((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf,
      ((Scheme.Modules.pullback i).obj
        (Scheme.Hom.relativeDifferentials p)).isSheaf⟩ : TopCat.Sheaf Ab.{u} Z)
    (i ⁻¹ᵁ A) _ _ fun z hz => ?_
  have hw := Stacks.Conormal.coborderStalkEquiv_mem_ker i z _
    (Stacks.Conormal.germ_idealSection_mem_ker_stalkMap i z A hz y)
  obtain ⟨V, hzV, s, hgerm⟩ := exists_germ_eq_of_mem_ker i.liftCoborder z _ hw
  let s' := (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom.val.app (op V) s
  have hs' : Stacks.Conormal.idealSection i.liftCoborder V s' = s.1 :=
    Stacks.Conormal.DefiningIdealBridge.idealSection_idealSheafBridge_hom i V s
  have hq : TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf i).val.presheaf
        (i ⁻¹ᵁ A) z hz ((canonicalConormalQuotientMap i).val.app (op A) y) =
      TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf i).val.presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hzV
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i)).val.app (op V) s') := by
    refine (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).injective ?_
    refine (Stacks.Conormal.germ_canonicalConormalQuotientMap i z A hz y).trans ?_
    refine Eq.trans ?_ (Stacks.Conormal.conormalSheafStalkEquivCotangent_germ i z V hzV s').symm
    refine congrArg (Ideal.toCotangent _) (Subtype.ext ?_)
    exact hgerm.symm.trans (congrArg _ hs'.symm)
  have hmem := Stacks.Conormal.mem_coborder_preimage i z A hz
  have hgermA : i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hzV
        (Stacks.Conormal.idealSection i.liftCoborder V s') =
      i.coborderRange.toScheme.presheaf.germ (i.coborderRange.ι ⁻¹ᵁ A)
        (i.liftCoborder.base z) hmem
        ((i.coborderRange.ι.app A).hom (Stacks.Conormal.idealSection i A y)) :=
    (congrArg _ hs').trans (hgerm.trans
      (Stacks.Conormal.coborderStalkEquiv_germ i z A hz hmem _))
  refine Eq.trans (stalkAb_map_germ _ z (i ⁻¹ᵁ A) hz _).symm ?_
  refine Eq.trans (congrArg ((stalkAb Z z).map _) hq) ?_
  refine Eq.trans (stalkAb_map_germ _ z (i.liftCoborder ⁻¹ᵁ V) hzV _) ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
    (i.liftCoborder ⁻¹ᵁ V) z hzV) (conormalDifferential_conormalSheafBridge_inv_unit i p V s')) ?_
  refine Eq.trans (germ_coborder_d_eq i p _ z hzV hmem _ _ hgermA) ?_
  exact coborderPullbackDifferentialsIso_germ i p A _ z hz hmem


end M9Native.ConormalDifferentialSections
