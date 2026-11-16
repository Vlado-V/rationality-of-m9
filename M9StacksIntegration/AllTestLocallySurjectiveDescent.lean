module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Yoneda

/-!
# Descent of maps along actual local surjections, in the original value universe

This proof uses only sheaf sections and their uniqueness on the actual image
sieve. It needs no sheafification, size assumption on the test category, or
classification/full-faithfulness premise. The local-section argument is a
generalization of the pinned native `Spaces/FppfMorphismDescent` argument,
with the covering-family factorization replaced by actual local surjectivity.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace M9StacksIntegration.AllTestLocallySurjectiveDescent
universe u v
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {X F H : Cᵒᵖ ⥤ Type v} (f : X ⟶ F) [hf : Presheaf.IsLocallySurjective J f]
  (hH : Presheaf.IsSheaf J H) (a : X ⟶ H)
  (ha : ∀ (P : Cᵒᵖ ⥤ Type v) (α β : P ⟶ X), α ≫ f = β ≫ f → α ≫ a = β ≫ a)

include J hf hH

include ha in
private theorem localSection (T : C) (y : F.obj (op T)) :
    ∃! z : H.obj (op T), ∀ (T' : C) (q : T' ⟶ T) (b : yoneda.obj T' ⟶ X),
      b ≫ f = yoneda.map q ≫ yonedaEquiv.symm y →
      H.map q.op z = yonedaEquiv (b ≫ a) := by
  classical
  have hH' : Presieve.IsSheaf J H := (isSheaf_iff_isSheaf_of_type J H).mp hH
  let R := Presheaf.imageSieve f y
  have hR : R ∈ J T := Presheaf.imageSieve_mem J f y
  let lift (W : C) (k : W ⟶ T) (hk : R k) : yoneda.obj W ⟶ X :=
    yonedaEquiv.symm (Presheaf.localPreimage f y k hk)
  have hlift (W : C) (k : W ⟶ T) (hk : R k) :
      lift W k hk ≫ f = yoneda.map k ≫ yonedaEquiv.symm y := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, ← yonedaEquiv_naturality, Equiv.apply_symm_apply]
    simpa only [Equiv.apply_symm_apply] using Presheaf.app_localPreimage f y k hk
  let x : Presieve.FamilyOfElements H R.arrows :=
    fun W k hk => yonedaEquiv (lift W k hk ≫ a)
  have hx : x.Compatible := by
    intro W₁ W₂ P e₁ e₂ k₁ k₂ h₁ h₂ hcomm
    have key : (yoneda.map e₁ ≫ lift W₁ k₁ h₁) ≫ f =
        (yoneda.map e₂ ≫ lift W₂ k₂ h₂) ≫ f := by
      rw [Category.assoc, Category.assoc, hlift, hlift, ← Category.assoc,
        ← Category.assoc, ← yoneda.map_comp, ← yoneda.map_comp, hcomm]
    change H.map e₁.op (yonedaEquiv (lift W₁ k₁ h₁ ≫ a)) =
      H.map e₂.op (yonedaEquiv (lift W₂ k₂ h₂ ≫ a))
    rw [yonedaEquiv_naturality, yonedaEquiv_naturality]
    exact congrArg yonedaEquiv (by simpa only [Category.assoc] using ha _ _ _ key)
  obtain ⟨z, hz, hzu⟩ := hH' R hR x hx
  refine ⟨z, ?_, ?_⟩
  · intro T' q b hb
    refine (hH' (R.pullback q) (J.pullback_stable q hR)).isSeparatedFor.ext ?_
    intro W r hr
    have hrR : R (r ≫ q) := hr
    have hfac : lift W (r ≫ q) hrR ≫ f = (yoneda.map r ≫ b) ≫ f := by
      rw [hlift, Category.assoc, hb, ← Category.assoc, ← yoneda.map_comp]
    calc
      H.map r.op (H.map q.op z) = H.map (r ≫ q).op z := by
        rw [← Functor.map_comp_apply, ← op_comp]
      _ = x (r ≫ q) hrR := hz _ hrR
      _ = yonedaEquiv ((yoneda.map r ≫ b) ≫ a) := congrArg yonedaEquiv (ha _ _ _ hfac)
      _ = H.map r.op (yonedaEquiv (b ≫ a)) := by
        rw [yonedaEquiv_naturality, Category.assoc]
  · intro z' hz'
    refine (hH' R hR).isSeparatedFor.ext ?_
    intro W k hk
    exact (hz' W k (lift W k hk) (hlift W k hk)).trans (hz k hk).symm

include ha in
/-- Any compatible map on an actual locally surjective atlas descends to a
map on the entire target presheaf, in the SAME original value universe. -/
theorem exists_desc : ∃ d : F ⟶ H, f ≫ d = a := by
  classical
  let localDesc := localSection J f hH a ha
  let sectionAt (T : C) (y : F.obj (op T)) : H.obj (op T) := (localDesc T y).choose
  have hspec (T : C) (y : F.obj (op T)) :
      ∀ (T' : C) (q : T' ⟶ T) (b : yoneda.obj T' ⟶ X),
        b ≫ f = yoneda.map q ≫ yonedaEquiv.symm y →
        H.map q.op (sectionAt T y) = yonedaEquiv (b ≫ a) :=
    (localDesc T y).choose_spec.1
  have huniq (T : C) (y : F.obj (op T)) (z : H.obj (op T))
      (hz : ∀ (T' : C) (q : T' ⟶ T) (b : yoneda.obj T' ⟶ X),
        b ≫ f = yoneda.map q ≫ yonedaEquiv.symm y →
        H.map q.op z = yonedaEquiv (b ≫ a)) : z = sectionAt T y :=
    (localDesc T y).choose_spec.2 z hz
  let η : F ⟶ H :=
    { app := fun T => TypeCat.ofHom (sectionAt T.unop)
      naturality := by
        intro T' T q
        apply ConcreteCategory.ext
        ext y
        change sectionAt T.unop (F.map q y) = H.map q (sectionAt T'.unop y)
        refine (huniq T.unop (F.map q y) (H.map q (sectionAt T'.unop y)) ?_).symm
        intro T'' r b hb
        have hfactor : b ≫ f = yoneda.map (r ≫ q.unop) ≫ yonedaEquiv.symm y := by
          rw [hb, yonedaEquiv_symm_map, yoneda.map_comp, Category.assoc]
        simpa only [op_comp, Functor.map_comp_apply, Quiver.Hom.op_unop] using
          hspec T'.unop y T'' (r ≫ q.unop) b hfactor }
  refine ⟨η, NatTrans.ext (funext fun T => ?_)⟩
  obtain ⟨T⟩ := T
  apply ConcreteCategory.ext
  ext w
  change sectionAt T (f.app (op T) w) = a.app (op T) w
  have hglocal : yonedaEquiv (yonedaEquiv.symm w ≫ a) = a.app (op T) w := by
    simpa using yonedaEquiv_comp (yonedaEquiv.symm w) a
  have hfac : yonedaEquiv.symm w ≫ f =
      yoneda.map (𝟙 T) ≫ yonedaEquiv.symm (f.app (op T) w) :=
    (yonedaEquiv_symm_naturality_right T f w).trans
      (((congrArg (fun m => m ≫ yonedaEquiv.symm (f.app (op T) w))
        (yoneda.map_id T)).trans (Category.id_comp _)).symm)
  simpa using (hspec T (f.app (op T) w) T (𝟙 T) (yonedaEquiv.symm w) hfac).trans hglocal

/-- Compatibility on an ACTUAL kernel-pair pullback is sufficient; no
coequalizer or effective-descent premise is supplied. -/
theorem exists_desc_of_isPullback
    {P : Cᵒᵖ ⥤ Type v} (p q : P ⟶ X) (h : IsPullback p q f f)
    (he : p ≫ a = q ≫ a) : ∃ d : F ⟶ H, f ≫ d = a := by
  apply exists_desc J f hH a
  intro Q α β hαβ
  calc
    α ≫ a = (h.lift α β hαβ ≫ p) ≫ a := by rw [h.lift_fst]
    _ = h.lift α β hαβ ≫ q ≫ a := by rw [Category.assoc, he]
    _ = β ≫ a := by rw [← Category.assoc, h.lift_snd]

end M9StacksIntegration.AllTestLocallySurjectiveDescent
