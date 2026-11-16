module

public import M9StacksIntegration.AllTestSheafCoproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift
public import Mathlib.CategoryTheory.Sites.Whiskering
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive

/-!
# Cartesian gluing of the original all-test schematic charts

Coproducts of represented schemes are sheaf coproducts in every larger value
universe. The temporary universe lift permits the proved infinitary van
Kampen theorem to be used on the full, large test category; final statements
are reflected back to the original Type-u-valued family, without changing its
test schemes, coefficient field, or family definition.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestCoproductCartesian
open AllTestSheafCoproducts
universe u v w a

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The disjoint-cover Yoneda coproduct criterion in an arbitrary larger
value universe. The proof glues actual sheaf sections, so it does not assume
sheafification in the smaller value universe. -/
def isColimitCofanMkUliftYoneda
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {I : Type a} (X : I → C) {c : Cofan X}
    (H : Sieve.ofArrows X c.inj ∈ J c.pt) [∀ i, Mono (c.inj i)]
    (hempty : ∀ Y : C, IsInitial Y → (⊥ : Sieve Y) ∈ J Y)
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Y : C} (f : Y ⟶ X i) (g : Y ⟶ X j),
      f ≫ c.inj i = g ≫ c.inj j → Nonempty (IsInitial Y)) :
    IsColimit (Cofan.mk ((J.uliftYoneda.{w}).obj c.pt)
      fun i => (J.uliftYoneda.{w}).map (c.inj i)) := by
  have hs (s : Cofan fun i => (J.uliftYoneda.{w}).obj (X i)) :
      ∃! t : s.pt.obj.obj (op c.pt), ∀ i,
        s.pt.obj.map (c.inj i).op t = J.uliftYonedaEquiv (s.inj i) := by
    have hsheaf : Presieve.IsSheafFor s.pt.obj (Presieve.ofArrows X c.inj) :=
      (Presieve.isSheafFor_iff_generate _).2 (s.pt.property.isSheafFor _ H)
    apply (Presieve.isSheafFor_arrows_iff s.pt.obj c.inj).1 hsheaf
    intro i j Y f g hfg
    by_cases hij : i = j
    · subst j
      rw [(cancel_mono _).mp hfg]
    · obtain ⟨hY⟩ := hdisj hij f g hfg
      letI := Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover s.pt Y (hempty Y hY))
      exact Subsingleton.elim _ _
  refine Cofan.IsColimit.mk _
    (fun s => J.uliftYonedaEquiv.symm (hs s).choose) ?_ ?_
  · intro s i
    change (J.uliftYoneda.{w}).map (c.inj i) ≫
      J.uliftYonedaEquiv.symm (hs s).choose = s.inj i
    apply J.uliftYonedaEquiv.injective
    rw [← J.uliftYonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact (hs s).choose_spec.1 i
  · intro s m hm
    apply J.uliftYonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply (hs s).choose_spec.2
    intro i
    rw [J.uliftYonedaEquiv_naturality]
    exact congrArg (fun f => J.uliftYonedaEquiv f) (hm i)

variable (K : Type u) [Field K] {I : Type u}

/-- Actual scheme coproducts on the original all-test site are also
coproducts of represented sheaves in Type (u+1). -/
def largeSumRepresentableIsColimit (Z : I → M9StandaloneDraft.Schemes K) :
    IsColimit (Cofan.mk (((topology K).uliftYoneda.{u+1}).obj (sumObject K Z))
      fun i => ((topology K).uliftYoneda.{u+1}).map (sumInclusion K Z i)) := by
  letI (i : I) : Mono (sumInclusion K Z i) :=
    (Over.forget (M9StandaloneDraft.Base K)).mono_of_mono_map
      (inferInstanceAs (Mono (Sigma.ι (fun j => (Z j).left) i)))
  letI (i : I) : Mono ((Cofan.mk (sumObject K Z) (sumInclusion K Z)).inj i) :=
    inferInstanceAs (Mono (sumInclusion K Z i))
  refine isColimitCofanMkUliftYoneda (topology K) Z
    (c := Cofan.mk (sumObject K Z) (sumInclusion K Z))
    (sumInclusions_cover K Z) (bot_cover_of_initial K) ?_
  intro i j hij Y f g hfg
  have heq : f.left ≫ Sigma.ι (fun j => (Z j).left) i =
      g.left ≫ Sigma.ι (fun j => (Z j).left) j := congrArg (fun h => h.left) hfg
  letI : IsEmpty Y.left := isEmpty_of_commSq_sigmaι_of_ne ⟨heq⟩ hij
  let hY : IsInitial Y.left := isInitialOfIsEmpty
  refine ⟨IsInitial.ofUniqueHom
    (fun W => Over.homMk (hY.to W.left) (hY.hom_ext _ _)) ?_⟩
  intro W f
  ext
  exact hY.hom_ext _ _

/-- The actual scheme coproduct is jointly covered by its original summands. -/
theorem sum_hom_ext (Z : I → M9StandaloneDraft.Schemes K)
    {T : M9StandaloneDraft.Schemes K} {f g : sumObject K Z ⟶ T}
    (h : ∀ i, sumInclusion K Z i ≫ f = sumInclusion K Z i ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  exact congrArg (fun a => a.left) (h i)

/-- Composition of actual coproduct scheme maps is computed on the original
summands, over the same coefficient field. -/
theorem sumMap_comp (Z : I → M9StandaloneDraft.Schemes K)
    {T V : M9StandaloneDraft.Schemes K} (f : ∀ i, Z i ⟶ T) (g : T ⟶ V) :
    sumMap K Z f ≫ g = sumMap K Z (fun i => f i ≫ g) := by
  apply sum_hom_ext K Z
  intro i
  rw [← Category.assoc, sumInclusion_sumMap, sumInclusion_sumMap]

abbrev largeLift : Sheaf (topology K) (Type u) ⥤ Sheaf (topology K) (Type (u+1)) :=
  sheafCompose (topology K) uliftFunctor.{u+1, u}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Actual cartesian charts glue to an actual cartesian square on the FULL
original all-test site. The map to the original total sheaf is the previously
constructed sheaf glue; all displayed scheme maps retain their original base.
The proof temporarily raises the value universe, applies actual infinitary
van Kampen descent, and reflects the resulting square back. -/
theorem isPullback_glueMaps
    (Z U : I → M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Space K)
    {T : M9StandaloneDraft.Schemes K} (π : F.obj ⟶ yoneda.obj T)
    (q : ∀ i, Z i ⟶ U i) (v : ∀ i, U i ⟶ T)
    (r : ∀ i, yoneda.obj (Z i) ⟶ F.obj)
    (h : ∀ i, IsPullback (r i) (yoneda.map (q i)) π (yoneda.map (v i))) :
    IsPullback (glueMaps K Z F r)
      (yoneda.map (sumMap K Z (fun i => q i ≫ sumInclusion K U i)))
      π (yoneda.map (sumMap K U v)) := by
  let J := topology K
  let Y := J.yoneda
  let L := largeLift K
  let F' : Sheaf J (Type u) := ⟨F.obj, F.isSheaf⟩
  let π' : F' ⟶ Y.obj T := ⟨π⟩
  let r' : ∀ i, Y.obj (Z i) ⟶ F' := fun i => ⟨r i⟩
  let R : Y.obj (sumObject K Z) ⟶ F' := ⟨glueMaps K Z F r⟩
  let Q := sumMap K Z (fun i => q i ≫ sumInclusion K U i)
  let V := sumMap K U v
  have hR (i : I) : Y.map (sumInclusion K Z i) ≫ R = r' i := by
    apply ObjectProperty.hom_ext
    exact sumInclusion_glueMaps K Z F r i
  have hQ (i : I) : Y.map (sumInclusion K Z i) ≫ Y.map Q =
      Y.map (q i) ≫ Y.map (sumInclusion K U i) := by
    rw [← Y.map_comp, sumInclusion_sumMap, Y.map_comp]
  have hV (i : I) : Y.map (sumInclusion K U i) ≫ Y.map V = Y.map (v i) := by
    rw [← Y.map_comp, sumInclusion_sumMap]
  have hlarge (i : I) :
      IsPullback (L.map (r' i)) (L.map (Y.map (q i)))
        (L.map π') (L.map (Y.map (v i))) := by
    let W := (Functor.whiskeringRight (M9StandaloneDraft.Schemes K)ᵒᵖ
      (Type u) (Type (u+1))).obj uliftFunctor.{u+1, u}
    have hw := (h i).map W
    apply IsPullback.of_map_of_faithful (sheafToPresheaf J (Type (u+1)))
    exact hw
  let hZ := largeSumRepresentableIsColimit K Z
  let hU := (Sheaf.isVanKampenColimit_of_isColimit_discrete J
    (largeSumRepresentableIsColimit K U)).isUniversal
  have hu (i : I) :
      (J.uliftYoneda.{u+1}).map (sumInclusion K U i) ≫ L.map (Y.map V) =
        L.map (Y.map (v i)) := by
    change L.map (Y.map (sumInclusion K U i)) ≫ L.map (Y.map V) = _
    rw [← L.map_comp, hV]
  have hs := hU.isPullback_of_isColimit_left
    (f := fun i => L.map (Y.map (v i)))
    (u := L.map (Y.map V)) (v := L.map π')
    (q₁ := fun i => L.map (r' i)) (q₂ := fun i => L.map (Y.map (q i)))
    (hP := hlarge) hZ hu
  have hRdesc : Cofan.IsColimit.desc hZ (fun i => L.map (r' i)) = L.map R := by
    apply Cofan.IsColimit.hom_ext hZ
    intro i
    rw [Cofan.IsColimit.fac]
    change L.map (r' i) = L.map (Y.map (sumInclusion K Z i)) ≫ L.map R
    rw [← L.map_comp, hR]
  have hQdesc : Cofan.IsColimit.desc hZ
      (fun i => L.map (Y.map (q i)) ≫ (J.uliftYoneda.{u+1}).map (sumInclusion K U i)) =
        L.map (Y.map Q) := by
    apply Cofan.IsColimit.hom_ext hZ
    intro i
    rw [Cofan.IsColimit.fac]
    change L.map (Y.map (q i)) ≫ L.map (Y.map (sumInclusion K U i)) =
      L.map (Y.map (sumInclusion K Z i)) ≫ L.map (Y.map Q)
    rw [← L.map_comp, ← L.map_comp, hQ]
  have hs' : IsPullback (L.map R) (L.map (Y.map Q)) (L.map π') (L.map (Y.map V)) := by
    convert hs using 1
    · rfl
    · rfl
    · exact hRdesc.symm
    · exact hQdesc.symm
  have hsmall : IsPullback R (Y.map Q) π' (Y.map V) := by
    apply IsPullback.of_map_of_faithful L
    exact hs'
  exact hsmall.map (sheafToPresheaf J (Type u))

end M9StacksIntegration.AllTestCoproductCartesian
