module

public import M9StacksIntegration.AllTestClassifierSections
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Extending honest affine-family values to all original families

The input assigns values to every actual original family over every affine
original base, including families with nonschematic total algebraic space.
Its naturality is required for all actual Cartesian family arrows between
affine bases. The target is an actual fppf sheaf on the full original site.

The inclusion of affine bases is proved cover dense using actual affine open
covers. For each original family, the honest values on its actual pullbacks
give a map from restricted Yoneda into the target. The dense-site sheaf
extension constructs its section on the entire original base. No extension,
overlap compatibility, schematicity, or gluing witness is an input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9StacksIntegration.AllTestAffineClassifierExtension
open AllTestOriginalFamilyCategory AllTestFamilyPullback

universe u
variable (K : Type u) [Field K]

/-- Honest values and all Cartesian-arrow naturality on affine ORIGINAL bases. -/
structure AffineFamilyValues (g : ℕ) (M : M9StandaloneDraft.Presheaves K) where
  value : ∀ (T : M9StandaloneDraft.Schemes K) (_hT : IsAffine T.left),
    M9StandaloneDraft.Family K T g → M.obj (op T)
  naturality : ∀ (T U : M9StandaloneDraft.Schemes K)
    (hT : IsAffine T.left) (hU : IsAffine U.left) (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K T g) (G : M9StandaloneDraft.Family K U g)
    (r : G.total.obj ⟶ F.total.obj),
    IsPullback r G.projection F.projection (yoneda.map a) →
      M.map a.op (value T hT F) = value U hU G

/-- Affineness is a property, so the actual input values do not depend on its proof. -/
theorem value_proof_irrel {g : ℕ} {M : M9StandaloneDraft.Presheaves K}
    (d : AffineFamilyValues K g M) (T : M9StandaloneDraft.Schemes K)
    (hT hT' : IsAffine T.left) (F : M9StandaloneDraft.Family K T g) :
    d.value T hT F = d.value T hT' F := rfl

/-- The full subcategory of the original bases that are affine schemes. -/
def affineProperty : ObjectProperty (M9StandaloneDraft.Schemes K) :=
  fun T => IsAffine T.left

abbrev AffineBases := (affineProperty K).FullSubcategory

/-- The literal inclusion retains the original base schemes and their field maps. -/
abbrev affineInclusion : AffineBases K ⥤ M9StandaloneDraft.Schemes K :=
  (affineProperty K).ι

/-- Actual affine open covers prove cover density on the full original fppf site. -/
instance affineInclusion_isCoverDense :
    (affineInclusion K).IsCoverDense
      (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) where
  is_cover T := by
    let U : T.left.affineCover.I₀ → M9StandaloneDraft.Schemes K :=
      fun i => Over.mk (T.left.affineCover.f i ≫ T.hom)
    let v : ∀ i, U i ⟶ T := fun i => Over.homMk (T.left.affineCover.f i) rfl
    have hc : Sieve.ofArrows U v ∈
        (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) T := by
      rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      apply Precoverage.generate_mem_toGrothendieck
      exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ T.left.affineCover.mem₀
    apply (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)).superset_covering _ hc
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact Presieve.in_coverByImage (affineInclusion K)
      (Y := ⟨U i, by change IsAffine (T.left.affineCover.X i); infer_instance⟩) (v i)

variable (g : ℕ)

/-- The genuine Cartesian fill-in between two actual arrows to the same family. -/
def cartesianFactor {X Y Z : CurveObject K g} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : Z.base ⟶ Y.base) (ha : a ≫ φ.baseMap = ψ.baseMap) : Z ⟶ Y := by
  have hw : ψ.totalMap ≫ X.family.projection =
      (Z.family.projection ≫ yoneda.map a) ≫ yoneda.map φ.baseMap := by
    rw [Category.assoc, ← (yoneda (C := M9StandaloneDraft.Schemes K)).map_comp, ha]
    exact ψ.cartesian.w
  let r := φ.cartesian.lift ψ.totalMap (Z.family.projection ≫ yoneda.map a) hw
  have hr₁ : r ≫ φ.totalMap = ψ.totalMap := φ.cartesian.lift_fst _ _ _
  have hr₂ : r ≫ Y.family.projection = Z.family.projection ≫ yoneda.map a :=
    φ.cartesian.lift_snd _ _ _
  refine ⟨a, r, ?_⟩
  apply IsPullback.of_right ?_ hr₂ φ.cartesian
  rw [hr₁, ← (yoneda (C := M9StandaloneDraft.Schemes K)).map_comp, ha]
  exact ψ.cartesian

@[simp] theorem cartesianFactor_baseMap {X Y Z : CurveObject K g}
    (φ : Y ⟶ X) (ψ : Z ⟶ X) (a : Z.base ⟶ Y.base)
    (ha : a ≫ φ.baseMap = ψ.baseMap) :
    (cartesianFactor K g φ ψ a ha).baseMap = a := rfl

variable {g} {M : M9StandaloneDraft.Presheaves K}

/-- Actual affine pullbacks of one original family supply a restricted Yoneda map. -/
def affinePullbackValues (d : AffineFamilyValues K g M)
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g) :
    (affineInclusion K).op ⋙ yoneda.obj T ⟶ (affineInclusion K).op ⋙ M where
  app V := TypeCat.ofHom fun a =>
    d.value V.unop.obj V.unop.property (pullbackFamily K F a)
  naturality V W b := by
    ext a
    let φ := pullbackMap K g (⟨T, F⟩ : CurveObject K g) a
    let ψ := pullbackMap K g (⟨T, F⟩ : CurveObject K g) (b.unop.hom ≫ a)
    let χ := cartesianFactor K g φ ψ b.unop.hom rfl
    exact (d.naturality V.unop.obj W.unop.obj V.unop.property W.unop.property
      b.unop.hom (pullbackFamily K F a) (pullbackFamily K F (b.unop.hom ≫ a))
      χ.totalMap χ.cartesian).symm

/-- The target's actual sheaf property extends the restricted map on genuine affine bases. -/
def sectionMap (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g) :
    yoneda.obj T ⟶ M :=
  Functor.IsCoverDense.sheafHom
    (ℱ' := (⟨M, hM⟩ : Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u)))
    (affinePullbackValues K d T F)

/-- The constructed map restricts to the honest input on every actual affine test. -/
theorem sectionMap_restrict (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g) :
    Functor.whiskerLeft (affineInclusion K).op (sectionMap K d hM T F) =
      affinePullbackValues K d T F :=
  Functor.IsCoverDense.sheafHom_restrict_eq
    (G := affineInclusion K) (ℱ := yoneda.obj T)
    (ℱ' := (⟨M, hM⟩ : Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u)))
    (affinePullbackValues K d T F)

/-- The glued value is a section on the entire original base. -/
def extendedValue (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g) : M.obj (op T) :=
  yonedaEquiv (sectionMap K d hM T F)

/-- Every affine pullback of the glued section equals the input value of the
actual pullback family, with its literal original projection. -/
theorem extendedValue_pullback_affine (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T : M9StandaloneDraft.Schemes K) (F : M9StandaloneDraft.Family K T g)
    (U : M9StandaloneDraft.Schemes K) (hU : IsAffine U.left) (a : U ⟶ T) :
    M.map a.op (extendedValue K d hM T F) = d.value U hU (pullbackFamily K F a) := by
  rw [extendedValue, map_yonedaEquiv]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (sectionMap_restrict K d hM T F) (op ⟨U, hU⟩)) a

/-- The actual glued value agrees with every honest affine-family input. -/
theorem extendedValue_affine (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left)
    (F : M9StandaloneDraft.Family K T g) : extendedValue K d hM T F = d.value T hT F := by
  have h₁ : extendedValue K d hM T F = d.value T hT (pullbackFamily K F (𝟙 T)) := by
    simpa using extendedValue_pullback_affine K d hM T F T hT (𝟙 T)
  let φ := pullbackMap K g (⟨T, F⟩ : CurveObject K g) (𝟙 T)
  have h₂ : d.value T hT F = d.value T hT (pullbackFamily K F (𝟙 T)) := by
    simpa using d.naturality T T hT hT (𝟙 T) F (pullbackFamily K F (𝟙 T))
      φ.totalMap φ.cartesian
  exact h₁.trans h₂.symm

/-- Full naturality follows from genuine Cartesian fill-ins and separatedness
on affine covers. Both original totals and the entire base arrow are retained. -/
theorem extendedValue_naturality (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T U : M9StandaloneDraft.Schemes K) (a : U ⟶ T)
    (F : M9StandaloneDraft.Family K T g) (G : M9StandaloneDraft.Family K U g)
    (r : G.total.obj ⟶ F.total.obj)
    (hcart : IsPullback r G.projection F.projection (yoneda.map a)) :
    M.map a.op (extendedValue K d hM T F) = extendedValue K d hM U G := by
  apply Functor.IsCoverDense.ext (affineInclusion K)
    (⟨M, hM⟩ : Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u)) U
  intro V b
  change M.map b.op (M.map a.op (extendedValue K d hM T F)) =
    M.map b.op (extendedValue K d hM U G)
  let f : (⟨U, G⟩ : CurveObject K g) ⟶ ⟨T, F⟩ := ⟨a, r, hcart⟩
  let φ := pullbackMap K g (⟨T, F⟩ : CurveObject K g) (b ≫ a)
  let ψ := pullbackMap K g (⟨U, G⟩ : CurveObject K g) b ≫ f
  let χ := cartesianFactor K g φ ψ (𝟙 V.obj) (by
    change 𝟙 V.obj ≫ (b ≫ a) = b ≫ a
    exact Category.id_comp _)
  have hv : d.value V.obj V.property (pullbackFamily K F (b ≫ a)) =
      d.value V.obj V.property (pullbackFamily K G b) := by
    simpa using d.naturality V.obj V.obj V.property V.property (𝟙 V.obj)
      (pullbackFamily K F (b ≫ a)) (pullbackFamily K G b) χ.totalMap χ.cartesian
  calc
    M.map b.op (M.map a.op (extendedValue K d hM T F)) =
        M.map (b ≫ a).op (extendedValue K d hM T F) := by
      simp only [op_comp, Functor.map_comp_apply]
    _ = d.value V.obj V.property (pullbackFamily K F (b ≫ a)) :=
      extendedValue_pullback_affine K d hM T F V.obj V.property (b ≫ a)
    _ = d.value V.obj V.property (pullbackFamily K G b) := hv
    _ = M.map b.op (extendedValue K d hM U G) :=
      (extendedValue_pullback_affine K d hM U G V.obj V.property b).symm

/-- The full classifier on ALL original bases and ALL original total algebraic spaces. -/
def extend (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M) :
    M9StandaloneDraft.Classifier K g M where
  value := extendedValue K d hM
  naturality := extendedValue_naturality K d hM

theorem extend_value_affine (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left)
    (F : M9StandaloneDraft.Family K T g) :
    (extend K d hM).value T F = d.value T hT F :=
  extendedValue_affine K d hM T hT F

/-- Any full classifier agreeing with the honest affine values is the extension. -/
theorem extend_unique (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M)
    (c : M9StandaloneDraft.Classifier K g M)
    (hc : ∀ (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left)
      (F : M9StandaloneDraft.Family K T g), c.value T F = d.value T hT F) :
    c = extend K d hM := by
  apply AllTestClassifierSections.classifier_ext K g
  intro T F
  apply Functor.IsCoverDense.ext (affineInclusion K)
    (⟨M, hM⟩ : Sheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type u)) T
  intro V a
  change M.map a.op (c.value T F) = M.map a.op (extendedValue K d hM T F)
  let φ := pullbackMap K g (⟨T, F⟩ : CurveObject K g) a
  calc
    M.map a.op (c.value T F) = c.value V.obj (pullbackFamily K F a) :=
      c.naturality T V.obj a F (pullbackFamily K F a) φ.totalMap φ.cartesian
    _ = d.value V.obj V.property (pullbackFamily K F a) :=
      hc V.obj V.property (pullbackFamily K F a)
    _ = M.map a.op (extendedValue K d hM T F) :=
      (extendedValue_pullback_affine K d hM T F V.obj V.property a).symm

/-- Existence and uniqueness of a genuine full extension, with no supplied extension witness. -/
theorem existsUnique_extension (d : AffineFamilyValues K g M)
    (hM : Presheaf.IsSheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) M) :
    ∃! c : M9StandaloneDraft.Classifier K g M,
      ∀ (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left)
        (F : M9StandaloneDraft.Family K T g), c.value T F = d.value T hT F :=
  ⟨extend K d hM, extend_value_affine K d hM, fun c hc => extend_unique K d hM c hc⟩

end M9StacksIntegration.AllTestAffineClassifierExtension
