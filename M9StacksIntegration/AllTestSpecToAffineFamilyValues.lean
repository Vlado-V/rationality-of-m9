module

public import M9StacksIntegration.AllTestAffineClassifierExtension
public import M9StacksIntegration.AdjoinFinsetBaseMapFactorization

/-!
# From honest spectrum-family values to all affine original bases

Every commutative K-algebra is allowed, including the zero ring. The total
of a family is an arbitrary original algebraic space. The canonical
K-algebra on the sections of an affine original base is derived from its
actual structure map. Actual spectrum isomorphisms and Cartesian family
fill-ins derive all affine naturality and agreement on literal spectra.
-/

set_option autoImplicit false
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace M9StacksIntegration.AllTestSpecToAffineFamilyValues
open AllTestOriginalFamilyCategory AllTestFamilyPullback AllTestAffineClassifierExtension
open M9StacksIntegration.AdjoinFinsetBaseMapFactorization

universe u
variable (K : Type u) [Field K]

/-- The literal original spectrum over K, also used by the finite-stage API. -/
abbrev specOverK (A : Type u) [CommRing A] [Algebra K A] :
    M9StandaloneDraft.Schemes K :=
  (AdjoinFinset.specOverCone K A).pt

/-- Literal spectra are affine, including the spectrum of the zero algebra. -/
instance specOverK_isAffine (A : Type u) [CommRing A] [Algebra K A] :
    IsAffine (specOverK K A).left := by
  change IsAffine (Spec (CommRingCat.of A))
  infer_instance

/-- Every actual map of spectra over K comes from an actual K-algebra map. -/
def algebraHomOfSpecMap {A R : Type u} [CommRing A] [CommRing R]
    [Algebra K A] [Algebra K R] (a : specOverK K R ⟶ specOverK K A) : A →ₐ[K] R where
  __ := (Spec.preimage (R := CommRingCat.of A) (S := CommRingCat.of R) a.left).hom
  commutes' := by
    intro k
    have h : CommRingCat.ofHom (algebraMap K A) ≫
        Spec.preimage (R := CommRingCat.of A) (S := CommRingCat.of R) a.left =
        CommRingCat.ofHom (algebraMap K R) := by
      apply Spec.map_injective
      have hw := a.w
      change a.left ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)) =
        Spec.map (CommRingCat.ofHom (algebraMap K R)) at hw
      rw [Spec.map_comp]
      change Spec.map (Spec.preimage (R := CommRingCat.of A) (S := CommRingCat.of R) a.left) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K A)) =
          Spec.map (CommRingCat.ofHom (algebraMap K R))
      exact (congrArg (fun f : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A) =>
        f ≫ Spec.map (CommRingCat.ofHom (algebraMap K A)))
          (Spec.map_preimage (R := CommRingCat.of A) (S := CommRingCat.of R) a.left)).trans hw
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of R => f.hom k) h

/-- Extracting an algebra map recovers the original physical map over K. -/
theorem specOverMap_algebraHomOfSpecMap {A R : Type u} [CommRing A] [CommRing R]
    [Algebra K A] [Algebra K R] (a : specOverK K R ⟶ specOverK K A) :
    specOverMap (algebraHomOfSpecMap K a) = a := by
  apply Over.OverMorphism.ext
  change Spec.map (Spec.preimage a.left) = a.left
  exact Spec.map_preimage a.left

/-- The extraction also retains every original algebra homomorphism. -/
theorem algebraHomOfSpecMap_specOverMap {A R : Type u} [CommRing A] [CommRing R]
    [Algebra K A] [Algebra K R] (φ : A →ₐ[K] R) :
    algebraHomOfSpecMap K (specOverMap φ) = φ := by
  apply AlgHom.toRingHom_injective
  change (Spec.preimage (Spec.map (CommRingCat.ofHom φ.toRingHom))).hom = φ.toRingHom
  rw [Spec.preimage_map]
  rfl

/-- The K-algebra on actual global sections comes from the original structure map. -/
@[instance_reducible] def canonicalAlgebra
    (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left) :
    Algebra K Γ(T.left, ⊤) := by
  letI : IsAffine T.left := hT
  exact (Spec.preimage (T.left.isoSpec.inv ≫ T.hom)).hom.toAlgebra

/-- The actual affine spectrum isomorphism, with its derived original K-structure. -/
def canonicalSpecIso (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left) :
    letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
    specOverK K Γ(T.left, ⊤) ≅ T := by
  letI : IsAffine T.left := hT
  letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  refine Over.isoMk T.left.isoSpec.symm ?_
  change T.left.isoSpec.inv ≫ T.hom =
    Spec.map (Spec.preimage (T.left.isoSpec.inv ≫ T.hom))
  exact (Spec.map_preimage _).symm

/-- The physical canonical map is the inverse of the original affine spectrum map. -/
theorem canonicalSpecIso_hom_left (T : M9StandaloneDraft.Schemes K)
    (hT : IsAffine T.left) :
    letI : IsAffine T.left := hT
    letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
    (canonicalSpecIso K T hT).hom.left = T.left.isoSpec.inv := rfl

/-- Every original affine-base morphism induces a genuine map of the canonical K-algebras. -/
def canonicalAlgHom (T U : M9StandaloneDraft.Schemes K)
    (hT : IsAffine T.left) (hU : IsAffine U.left) (a : U ⟶ T) :
    letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
    letI : Algebra K Γ(U.left, ⊤) := canonicalAlgebra K U hU
    Γ(T.left, ⊤) →ₐ[K] Γ(U.left, ⊤) := by
  letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  letI : Algebra K Γ(U.left, ⊤) := canonicalAlgebra K U hU
  exact algebraHomOfSpecMap K
    ((canonicalSpecIso K U hU).hom ≫ a ≫ (canonicalSpecIso K T hT).inv)

/-- The actual canonical spectrum isomorphisms are natural for all affine-base maps. -/
theorem canonicalSpecIso_naturality (T U : M9StandaloneDraft.Schemes K)
    (hT : IsAffine T.left) (hU : IsAffine U.left) (a : U ⟶ T) :
    letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
    letI : Algebra K Γ(U.left, ⊤) := canonicalAlgebra K U hU
    specOverMap (canonicalAlgHom K T U hT hU a) ≫ (canonicalSpecIso K T hT).hom =
      (canonicalSpecIso K U hU).hom ≫ a := by
  let : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  let : Algebra K Γ(U.left, ⊤) := canonicalAlgebra K U hU
  rw [canonicalAlgHom, specOverMap_algebraHomOfSpecMap]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Honest values on ALL K-algebra spectra, with ALL actual Cartesian-arrow naturality. -/
structure SpecFamilyValues (g : ℕ) (M : M9StandaloneDraft.Presheaves K) where
  value : ∀ (A : Type u) [CommRing A] [Algebra K A],
    M9StandaloneDraft.Family K (specOverK K A) g → M.obj (op (specOverK K A))
  naturality : ∀ (A R : Type u) [CommRing A] [CommRing R] [Algebra K A] [Algebra K R]
    (φ : A →ₐ[K] R)
    (F : M9StandaloneDraft.Family K (specOverK K A) g)
    (G : M9StandaloneDraft.Family K (specOverK K R) g) (r : G.total.obj ⟶ F.total.obj),
    IsPullback r G.projection F.projection (yoneda.map (specOverMap φ)) →
      M.map (specOverMap φ).op (value A F) = value R G

variable {g : ℕ} {M : M9StandaloneDraft.Presheaves K}

/-- Pull back the actual family along the canonical affine spectrum isomorphism. -/
def affineValue (d : SpecFamilyValues K g M) (T : M9StandaloneDraft.Schemes K)
    (hT : IsAffine T.left) (F : M9StandaloneDraft.Family K T g) : M.obj (op T) := by
  letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  let e := canonicalSpecIso K T hT
  exact M.map e.inv.op (d.value Γ(T.left, ⊤) (pullbackFamily K F e.hom))

/-- Actual Cartesian fill-ins derive naturality for every original affine-base arrow. -/
theorem affineValue_naturality (d : SpecFamilyValues K g M)
    (T U : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left) (hU : IsAffine U.left)
    (a : U ⟶ T) (F : M9StandaloneDraft.Family K T g) (G : M9StandaloneDraft.Family K U g)
    (r : G.total.obj ⟶ F.total.obj)
    (hr : IsPullback r G.projection F.projection (yoneda.map a)) :
    M.map a.op (affineValue K d T hT F) = affineValue K d U hU G := by
  let : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  let : Algebra K Γ(U.left, ⊤) := canonicalAlgebra K U hU
  let eT := canonicalSpecIso K T hT
  let eU := canonicalSpecIso K U hU
  let φ := canonicalAlgHom K T U hT hU a
  have ha : specOverMap φ ≫ eT.hom = eU.hom ≫ a :=
    canonicalSpecIso_naturality K T U hT hU a
  let pF := pullbackMap K g (⟨T, F⟩ : CurveObject K g) eT.hom
  let pG := pullbackMap K g (⟨U, G⟩ : CurveObject K g) eU.hom
  let α : (⟨U, G⟩ : CurveObject K g) ⟶ ⟨T, F⟩ := ⟨a, r, hr⟩
  let χ := cartesianFactor K g pF (pG ≫ α) (specOverMap φ) ha
  have hφ := d.naturality Γ(T.left, ⊤) Γ(U.left, ⊤) φ
    (pullbackFamily K F eT.hom) (pullbackFamily K G eU.hom) χ.totalMap χ.cartesian
  have hi : a ≫ eT.inv = eU.inv ≫ specOverMap φ := by
    apply (cancel_mono eT.hom).mp
    simp only [Category.assoc, ha, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
  change M.map a.op (M.map eT.inv.op _) = M.map eU.inv.op _
  calc
    M.map a.op (M.map eT.inv.op _) = M.map (a ≫ eT.inv).op _ := by
      rw [op_comp, M.map_comp]
      rfl
    _ = M.map (eU.inv ≫ specOverMap φ).op _ := by rw [hi]
    _ = M.map eU.inv.op (M.map (specOverMap φ).op _) := by
      rw [op_comp, M.map_comp]
      rfl
    _ = M.map eU.inv.op _ := congrArg (M.map eU.inv.op) hφ

/-- The derived datum satisfies the FINAL all-affine interface without further premises. -/
def toAffineFamilyValues (d : SpecFamilyValues K g M) : AffineFamilyValues K g M where
  value := affineValue K d
  naturality := affineValue_naturality K d

/-- The genuine pullback formula on every actual affine original base. -/
theorem toAffine_value (d : SpecFamilyValues K g M) (T : M9StandaloneDraft.Schemes K)
    (hT : IsAffine T.left) (F : M9StandaloneDraft.Family K T g) :
    letI : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
    (toAffineFamilyValues K d).value T hT F =
      M.map (canonicalSpecIso K T hT).inv.op
        (d.value Γ(T.left, ⊤) (pullbackFamily K F (canonicalSpecIso K T hT).hom)) := rfl

/-- Normalization agrees exactly with the supplied datum on every literal spectrum. -/
theorem toAffine_value_spec (d : SpecFamilyValues K g M)
    (A : Type u) [CommRing A] [Algebra K A]
    (F : M9StandaloneDraft.Family K (specOverK K A) g) :
    (toAffineFamilyValues K d).value (specOverK K A) inferInstance F = d.value A F := by
  let T := specOverK K A
  let : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T inferInstance
  let e := canonicalSpecIso K T inferInstance
  let p := pullbackMap K g (⟨T, F⟩ : CurveObject K g) e.hom
  let χ := cartesianFactor K g p (𝟙 (⟨T, F⟩ : CurveObject K g)) e.inv
    (by change e.inv ≫ e.hom = 𝟙 T; exact e.inv_hom_id)
  let φ := algebraHomOfSpecMap K e.inv
  have hχ : IsPullback χ.totalMap F.projection (pullbackFamily K F e.hom).projection
      (yoneda.map (specOverMap φ)) := by
    rw [specOverMap_algebraHomOfSpecMap]
    exact χ.cartesian
  have h := d.naturality Γ(T.left, ⊤) A φ (pullbackFamily K F e.hom) F χ.totalMap hχ
  change M.map e.inv.op (d.value Γ(T.left, ⊤) (pullbackFamily K F e.hom)) = d.value A F
  simpa only [φ, specOverMap_algebraHomOfSpecMap] using h

/-- Agreement with any genuine original classifier follows from its literal-Spec agreement. -/
theorem toAffine_agreesClassifier (d : SpecFamilyValues K g M)
    (c : M9StandaloneDraft.Classifier K g M)
    (hc : ∀ (A : Type u) [CommRing A] [Algebra K A]
      (F : M9StandaloneDraft.Family K (specOverK K A) g),
      d.value A F = c.value (specOverK K A) F)
    (T : M9StandaloneDraft.Schemes K) (hT : IsAffine T.left)
    (F : M9StandaloneDraft.Family K T g) :
    (toAffineFamilyValues K d).value T hT F = c.value T F := by
  let : Algebra K Γ(T.left, ⊤) := canonicalAlgebra K T hT
  let e := canonicalSpecIso K T hT
  let p := pullbackMap K g (⟨T, F⟩ : CurveObject K g) e.hom
  have h := c.naturality T (specOverK K Γ(T.left, ⊤)) e.hom F
    (pullbackFamily K F e.hom) p.totalMap p.cartesian
  change M.map e.inv.op (d.value Γ(T.left, ⊤) (pullbackFamily K F e.hom)) = c.value T F
  rw [hc, ← h]
  change (M.map e.hom.op ≫ M.map e.inv.op) (c.value T F) = c.value T F
  rw [← M.map_comp, ← op_comp, e.inv_hom_id, op_id, M.map_id]
  rfl

end M9StacksIntegration.AllTestSpecToAffineFamilyValues
