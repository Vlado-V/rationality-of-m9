module

public import M9StacksIntegration.AllTestSchemeFamilies
public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Sites.Subcanonical

/-!
# Gluing into the original all-test sheaf along a scheme coproduct

The actual scheme coproduct represents the coproduct in fppf sheaves, even
though it does not represent the coproduct in presheaves. The resulting map
below has the original all-test sheaf as its target and agrees with the given
maps on every original summand. No size cutoff is imposed on the test schemes.

This supplies the map-gluing step of the curve-family comparison; it does not
assume that the total family is schematic or assert its descent in advance.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestSheafCoproducts

universe u

variable (K : Type u) [Field K] {I : Type u}

abbrev topology := Scheme.fppfTopology.over (M9StandaloneDraft.Base K)

/-- The actual coproduct of the original total schemes, with its original
structural morphism to the original coefficient field. -/
def sumObject (Z : I → M9StandaloneDraft.Schemes K) : M9StandaloneDraft.Schemes K :=
  Over.mk (Sigma.desc fun i => (Z i).hom)

def sumInclusion (Z : I → M9StandaloneDraft.Schemes K) (i : I) :
    Z i ⟶ sumObject K Z :=
  Over.homMk (Sigma.ι (fun j => (Z j).left) i) (Sigma.ι_comp_desc _ i)

@[simp] theorem sumInclusion_left (Z : I → M9StandaloneDraft.Schemes K) (i : I) :
    (sumInclusion K Z i).left = Sigma.ι (fun j => (Z j).left) i := rfl

/-- A map of the actual scheme coproduct, over the original field. -/
def sumMap (Z : I → M9StandaloneDraft.Schemes K)
    {T : M9StandaloneDraft.Schemes K} (f : ∀ i, Z i ⟶ T) : sumObject K Z ⟶ T :=
  Over.homMk (Sigma.desc fun i => (f i).left) (by
    apply Sigma.hom_ext
    intro i
    change Sigma.ι (fun j => (Z j).left) i ≫
        (Sigma.desc (fun j => (f j).left) ≫ T.hom) =
      Sigma.ι (fun j => (Z j).left) i ≫ Sigma.desc (fun j => (Z j).hom)
    rw [← CategoryTheory.Category.assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
    exact Over.w (f i))

@[simp] theorem sumInclusion_sumMap (Z : I → M9StandaloneDraft.Schemes K)
    {T : M9StandaloneDraft.Schemes K} (f : ∀ i, Z i ⟶ T) (i : I) :
    sumInclusion K Z i ≫ sumMap K Z f = f i := by
  ext
  change Sigma.ι (fun j => (Z j).left) i ≫ Sigma.desc (fun j => (f j).left) = (f i).left
  exact Sigma.ι_comp_desc _ i

/-- The original summands form an actual fppf covering of their actual
coproduct on the full all-test site. -/
theorem sumInclusions_cover (Z : I → M9StandaloneDraft.Schemes K) :
    Sieve.ofArrows Z (sumInclusion K Z) ∈ topology K (sumObject K Z) := by
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _
    (sigmaOpenCover (fun i => (Z i).left)).mem₀

theorem bot_cover_of_initial (Y : M9StandaloneDraft.Schemes K)
    (hY : IsInitial Y) : (⊥ : Sieve Y) ∈ topology K Y := by
  letI : IsEmpty Y.left :=
    isInitial_iff_isEmpty.mp ⟨hY.isInitialObj (Over.forget (M9StandaloneDraft.Base K)) Y⟩
  rw [GrothendieckTopology.mem_over_iff, map_bot]
  exact Scheme.bot_mem_grothendieckTopology _

/-- The actual representable of a scheme coproduct is the coproduct in the
category of actual fppf sheaves on the full all-test site. -/
def sumRepresentableIsColimit (Z : I → M9StandaloneDraft.Schemes K) :
    IsColimit (Cofan.mk ((topology K).yoneda.obj (sumObject K Z))
      fun i => (topology K).yoneda.map (sumInclusion K Z i)) := by
  letI (i : I) : Mono (sumInclusion K Z i) :=
    (Over.forget (M9StandaloneDraft.Base K)).mono_of_mono_map
      (inferInstanceAs (Mono (Sigma.ι (fun j => (Z j).left) i)))
  letI (i : I) : Mono ((Cofan.mk (sumObject K Z) (sumInclusion K Z)).inj i) :=
    inferInstanceAs (Mono (sumInclusion K Z i))
  refine (topology K).isColimitCofanMkYoneda Z
    (c := Cofan.mk (sumObject K Z) (sumInclusion K Z))
    (sumInclusions_cover K Z) (bot_cover_of_initial K) ?_
  intro i j hij Y a b hab
  have heq : a.left ≫ Sigma.ι (fun j => (Z j).left) i =
      b.left ≫ Sigma.ι (fun j => (Z j).left) j := congrArg (fun z => z.left) hab
  letI : IsEmpty Y.left := isEmpty_of_commSq_sigmaι_of_ne ⟨heq⟩ hij
  let hY : IsInitial Y.left := isInitialOfIsEmpty
  refine ⟨IsInitial.ofUniqueHom
    (fun W => Over.homMk (hY.to W.left) (hY.hom_ext _ _)) ?_⟩
  intro W f
  ext
  exact hY.hom_ext _ _

/-- Glue the given actual maps from the summands to the original all-test
algebraic-space sheaf. This uses its sheaf condition. -/
def glueMaps (Z : I → M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Space K)
    (r : ∀ i, yoneda.obj (Z i) ⟶ F.obj) : yoneda.obj (sumObject K Z) ⟶ F.obj :=
  ((sumRepresentableIsColimit K Z).desc
    (Cofan.mk (⟨F.obj, F.isSheaf⟩ : Sheaf (topology K) (Type u))
      fun i => ⟨r i⟩)).hom

@[simp] theorem sumInclusion_glueMaps (Z : I → M9StandaloneDraft.Schemes K)
    (F : M9StandaloneDraft.Space K) (r : ∀ i, yoneda.obj (Z i) ⟶ F.obj) (i : I) :
    yoneda.map (sumInclusion K Z i) ≫ glueMaps K Z F r = r i := by
  exact congrArg (fun z => z.hom)
    ((sumRepresentableIsColimit K Z).fac
      (Cofan.mk (⟨F.obj, F.isSheaf⟩ : Sheaf (topology K) (Type u)) fun i => ⟨r i⟩)
      (Discrete.mk i))

/-- Maps from the actual scheme coproduct into a genuine all-test sheaf are
equal when their restrictions to the original summands are equal. -/
theorem maps_ext (Z : I → M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Space K)
    {r s : yoneda.obj (sumObject K Z) ⟶ F.obj}
    (h : ∀ i, yoneda.map (sumInclusion K Z i) ≫ r =
      yoneda.map (sumInclusion K Z i) ≫ s) : r = s := by
  have heq : (⟨r⟩ : (topology K).yoneda.obj (sumObject K Z) ⟶
      (⟨F.obj, F.isSheaf⟩ : Sheaf (topology K) (Type u))) = ⟨s⟩ := by
    apply (sumRepresentableIsColimit K Z).hom_ext
    rintro ⟨i⟩
    ext : 1
    exact h i
  exact congrArg (fun z => z.hom) heq

/-- The glued map preserves the original full-base projection when every
original chart does. The conclusion is equality of entire natural
transformations, not equality only on field-valued points. -/
theorem glueMaps_projection (Z : I → M9StandaloneDraft.Schemes K)
    (F : M9StandaloneDraft.Space K) {T : M9StandaloneDraft.Schemes K}
    (π : F.obj ⟶ yoneda.obj T) (r : ∀ i, yoneda.obj (Z i) ⟶ F.obj)
    (q : ∀ i, Z i ⟶ T) (h : ∀ i, r i ≫ π = yoneda.map (q i)) :
    glueMaps K Z F r ≫ π = yoneda.map (sumMap K Z q) := by
  apply maps_ext K Z (AllTestSchemeFamilies.standaloneSchemeSpace K T)
  intro i
  change yoneda.map (sumInclusion K Z i) ≫ (glueMaps K Z F r ≫ π) =
    yoneda.map (sumInclusion K Z i) ≫ yoneda.map (sumMap K Z q)
  rw [← Category.assoc, sumInclusion_glueMaps, h i,
    ← Functor.map_comp, sumInclusion_sumMap]

end M9StacksIntegration.AllTestSheafCoproducts
