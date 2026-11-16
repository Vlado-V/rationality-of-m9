module

public import M9StacksIntegration.AllTestFamilyPullback

/-!
# The ACTUAL category of literal ORIGINAL all-test families

Objects are precisely a base scheme over the original field and a literal
Standalone Family, whose total is an actual full-test algebraic space.
Arrows are the actual base/total maps with their full original Cartesian
square. Pullbacks use the already-proved actual all-test family pullback.
No supplied classifier, category equivalence, atlas, or fibration is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestOriginalFamilyCategory
universe u
variable (K : Type u) [Field K] (g : ℕ)

/-- An actual original full-test family, with its original base. -/
structure CurveObject where
  base : M9StandaloneDraft.Schemes K
  family : M9StandaloneDraft.Family K base g

/-- Actual original Cartesian family arrows. -/
@[ext] structure CurveHom (F G : CurveObject K g) where
  baseMap : F.base ⟶ G.base
  totalMap : F.family.total.obj ⟶ G.family.total.obj
  cartesian : IsPullback totalMap F.family.projection G.family.projection (yoneda.map baseMap)

/-- The actual original-family category uses identity/pasting of the actual
Cartesian squares, without replacing the original objects or field maps. -/
instance : Category (CurveObject K g) where
  Hom := CurveHom K g
  id F :=
    { baseMap := 𝟙 F.base
      totalMap := 𝟙 F.family.total.obj
      cartesian := by
        rw [(yoneda (C := M9StandaloneDraft.Schemes K)).map_id]
        exact IsPullback.id_horiz F.family.projection }
  comp f h :=
    { baseMap := f.baseMap ≫ h.baseMap
      totalMap := f.totalMap ≫ h.totalMap
      cartesian := by
        rw [(yoneda (C := M9StandaloneDraft.Schemes K)).map_comp]
        exact f.cartesian.paste_horiz h.cartesian }
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp
  assoc := by intros; ext <;> simp [Category.assoc]

/-- The literal original base functor. -/
def projection : CurveObject K g ⥤ M9StandaloneDraft.Schemes K where
  obj F := F.base
  map f := f.baseMap

/-- The actual full-original-test total-space presheaf functor. -/
def totalFunctor : CurveObject K g ⥤ M9StandaloneDraft.Presheaves K where
  obj F := F.family.total.obj
  map f := f.totalMap

/-- The actual pullback object over every ORIGINAL base map. -/
def pullbackObject (F : CurveObject K g) {U : M9StandaloneDraft.Schemes K} (a : U ⟶ F.base) :
    CurveObject K g :=
  ⟨U, AllTestFamilyPullback.pullbackFamily K F.family a⟩

/-- The actual Cartesian arrow of the all-original family pullback. -/
def pullbackMap (F : CurveObject K g) {U : M9StandaloneDraft.Schemes K} (a : U ⟶ F.base) :
    pullbackObject K g F a ⟶ F := by
  let : HasPullback F.family.projection (yoneda.map a) :=
    AllTestFamilyPullback.originalPresheafPullback K F.family.projection (yoneda.map a)
  exact
    { baseMap := a
      totalMap := pullback.fst F.family.projection (yoneda.map a)
      cartesian := AllTestFamilyPullback.pullbackFamily_isPullback K F.family a }

/-- The actual family isomorphism of compatible base and total isomorphisms. -/
def isoMk {F G : CurveObject K g} (β : F.base ≅ G.base)
    (ε : F.family.total.obj ≅ G.family.total.obj)
    (w : ε.hom ≫ G.family.projection = F.family.projection ≫ yoneda.map β.hom) : F ≅ G where
  hom :=
    { baseMap := β.hom
      totalMap := ε.hom
      cartesian := IsPullback.of_horiz_isIso ⟨w⟩ }
  inv :=
    { baseMap := β.inv
      totalMap := ε.inv
      cartesian := by
        refine IsPullback.of_horiz_isIso ⟨?_⟩
        rw [Iso.inv_comp_eq, ← Category.assoc, w, Category.assoc,
          ← (yoneda (C := M9StandaloneDraft.Schemes K)).map_comp, β.hom_inv_id,
          (yoneda (C := M9StandaloneDraft.Schemes K)).map_id, Category.comp_id] }
  hom_inv_id := CurveHom.ext β.hom_inv_id ε.hom_inv_id
  inv_hom_id := CurveHom.ext β.inv_hom_id ε.inv_hom_id

/-- A Cartesian original-family arrow over a base isomorphism is actually
an isomorphism on its original total presheaf. -/
theorem isIso_totalMap_of_isIso_baseMap {F G : CurveObject K g} (f : F ⟶ G)
    [IsIso f.baseMap] : IsIso f.totalMap := by
  have : IsIso (yoneda.map f.baseMap) := Functor.map_isIso _ _
  exact f.cartesian.isIso_fst_of_isIso

/-- Every actual original-family arrow over a base isomorphism is invertible. -/
theorem isIso_of_isIso_baseMap {F G : CurveObject K g} (f : F ⟶ G)
    [IsIso f.baseMap] : IsIso f := by
  have : IsIso f.totalMap := isIso_totalMap_of_isIso_baseMap K g f
  let E := isoMk K g (asIso f.baseMap) (asIso f.totalMap) f.cartesian.w
  have h : E.hom = f := CurveHom.ext rfl rfl
  exact h ▸ (inferInstance : IsIso E.hom)

/-- Literal same-base family isomorphism is exactly isomorphism in the
actual original category over the IDENTITY original base map. -/
theorem familyIsomorphic_iff_iso_identity
    (T : M9StandaloneDraft.Schemes K) (F G : M9StandaloneDraft.Family K T g) :
    M9StandaloneDraft.FamilyIsomorphic K F G ↔
      ∃ e : (⟨T, F⟩ : CurveObject K g) ≅ ⟨T, G⟩, e.hom.baseMap = 𝟙 T := by
  constructor
  · rintro ⟨e, he⟩
    have hw : e.hom ≫ G.projection = F.projection ≫ yoneda.map (𝟙 T) := by
      rw [(yoneda (C := M9StandaloneDraft.Schemes K)).map_id, Category.comp_id]
      exact he
    exact ⟨isoMk K g (Iso.refl T) e hw, rfl⟩
  · rintro ⟨e, he⟩
    refine ⟨(totalFunctor K g).mapIso e, ?_⟩
    have hw := e.hom.cartesian.w
    rw [he, (yoneda (C := M9StandaloneDraft.Schemes K)).map_id, Category.comp_id] at hw
    exact hw

end M9StacksIntegration.AllTestOriginalFamilyCategory
