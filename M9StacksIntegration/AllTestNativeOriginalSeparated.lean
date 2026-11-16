module

public import M9StacksIntegration.AllTestNativeOriginalOpenSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedClosedSubspace

/-!
# Actual separatedness on the original full test category

The product is the actual fibre product over the represented original
base. Its original image is a product because the actual comparison
preserves that pullback and the same represented base is terminal.
The native closed diagonal then transfers by genuine scheme fppf descent.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalSeparated
open AllTestBoundedCharts AllTestNativeOriginalFunctor AllTestNativeOriginalSchemes
  AllTestNativeOriginalSpace AllTestNativeOriginalPullbacks AllTestNativeOriginalOpenSpace
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

theorem nativePresheafPullbacks :
    HasPullbacks ((BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape (J := WalkingCospan) (C := Type u)
    (K := (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ)

/-- A genuine pullback over a terminal object is a genuine product. -/
def productIsLimitOfIsPullbackTerminal {C : Type*} [Category C]
    {P X Y T : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ T} {g : Y ⟶ T}
    (h : IsPullback a b f g) (ht : IsTerminal T) : IsLimit (BinaryFan.mk a b) :=
  BinaryFan.isLimitMk
    (fun s => h.lift s.fst s.snd (ht.hom_ext _ _))
    (fun _s => h.lift_fst _ _ _) (fun _s => h.lift_snd _ _ _)
    (fun _s _m hm₁ hm₂ => h.hom_ext (hm₁.trans (h.lift_fst _ _ _).symm)
      (hm₂.trans (h.lift_snd _ _ _).symm))

/-- The native represented base, with its actual identity structural map. -/
abbrev nativeBase : AlgebraicSpaces B (Spec (.of K)) hK :=
  schemeSpace (Over.mk (𝟙 (B.obj hK)))

/-- The original image of the same native represented base is terminal
on the entire original category of schemes. -/
def originalBase_isTerminal : IsTerminal
    ((originalPresheafFunctor K B hK).obj (nativeBase K B hK)) := by
  let e := originalSchemeIso K B hK (Over.mk (𝟙 (B.obj hK)))
  have h : IsTerminal
      (yoneda.obj ((boundedInclusion B K hK).obj (Over.mk (𝟙 (B.obj hK))))) :=
    Over.mkIdTerminal.isTerminalObj yoneda _
  exact h.ofIso e.symm

/-- The actual native structural morphism to the represented base. -/
def nativeProjection (X : AlgebraicSpaces B (Spec (.of K)) hK) : X ⟶ nativeBase K B hK :=
  ObjectProperty.homMk ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).from X.obj)

local instance nativeProjectionPullback (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    HasPullback (nativeProjection K B hK X).hom (nativeProjection K B hK X).hom :=
  (nativePresheafPullbacks K B hK).has_limit _

/-- The actual native product, constructed as a fibre product over the base. -/
def nativeProduct (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    AlgebraicSpaces B (Spec (.of K)) hK :=
  ⟨CategoryTheory.Limits.pullback (nativeProjection K B hK X).hom (nativeProjection K B hK X).hom,
    isAlgebraicSpace_of_isPullback X.property X.property
      (nativeBase K B hK).property.isSheaf (nativeBase K B hK).property.diagonal_representable
      (IsPullback.of_hasPullback _ _)⟩

/-- The first actual product projection. -/
def nativeFirst (X : AlgebraicSpaces B (Spec (.of K)) hK) : nativeProduct K B hK X ⟶ X :=
  ObjectProperty.homMk (pullback.fst (nativeProjection K B hK X).hom
    (nativeProjection K B hK X).hom)

/-- The second actual product projection. -/
def nativeSecond (X : AlgebraicSpaces B (Spec (.of K)) hK) : nativeProduct K B hK X ⟶ X :=
  ObjectProperty.homMk (pullback.snd (nativeProjection K B hK X).hom
    (nativeProjection K B hK X).hom)

/-- The actual native diagonal into that actual native product. -/
def nativeDiagonal (X : AlgebraicSpaces B (Spec (.of K)) hK) : X ⟶ nativeProduct K B hK X :=
  ObjectProperty.homMk (pullback.diagonal (nativeProjection K B hK X).hom)

/-- The canonical native product comparison retains the two original projections. -/
def nativeProductIso (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (nativeProduct K B hK X).obj ≅ X.obj ⨯ X.obj where
  hom := prod.lift (nativeFirst K B hK X).hom (nativeSecond K B hK X).hom
  inv := pullback.lift prod.fst prod.snd
    ((Space.isTerminal_yoneda_obj_base B (Spec (.of K)) hK).hom_ext _ _)
  hom_inv_id := by apply pullback.hom_ext <;> simp [nativeFirst, nativeSecond]
  inv_hom_id := by apply prod.hom_ext <;> simp [nativeFirst, nativeSecond]

/-- The actual original image of the actual native product is a product
of the SAME original-space images. -/
def originalProductIso (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (originalPresheafFunctor K B hK).obj (nativeProduct K B hK X) ≅
      (originalPresheafFunctor K B hK).obj X ⨯ (originalPresheafFunctor K B hK).obj X := by
  have h := original_isPullback K B hK
    (nativeFirst K B hK X) (nativeSecond K B hK X)
    (nativeProjection K B hK X) (nativeProjection K B hK X)
    (IsPullback.of_hasPullback (nativeProjection K B hK X).hom
      (nativeProjection K B hK X).hom)
  exact {
    hom := prod.lift ((originalPresheafFunctor K B hK).map (nativeFirst K B hK X))
      ((originalPresheafFunctor K B hK).map (nativeSecond K B hK X))
    inv := h.lift prod.fst prod.snd ((originalBase_isTerminal K B hK).hom_ext _ _)
    hom_inv_id := by
      apply h.hom_ext
      · rw [Category.assoc, h.lift_fst, prod.lift_fst, Category.id_comp]
      · rw [Category.assoc, h.lift_snd, prod.lift_snd, Category.id_comp]
    inv_hom_id := by
      apply prod.hom_ext
      · rw [Category.assoc, prod.lift_fst, h.lift_fst, Category.id_comp]
      · rw [Category.assoc, prod.lift_snd, h.lift_snd, Category.id_comp]
  }

/-- The native product comparison retains the actual first projection. -/
theorem nativeProductIso_hom_fst (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (nativeProductIso K B hK X).hom ≫ prod.fst = (nativeFirst K B hK X).hom := by
  exact prod.lift_fst (nativeFirst K B hK X).hom (nativeSecond K B hK X).hom

/-- The native product comparison retains the actual second projection. -/
theorem nativeProductIso_hom_snd (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (nativeProductIso K B hK X).hom ≫ prod.snd = (nativeSecond K B hK X).hom := by
  exact prod.lift_snd (nativeFirst K B hK X).hom (nativeSecond K B hK X).hom

/-- The original product comparison retains the actual first projection. -/
theorem originalProductIso_hom_fst (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (originalProductIso K B hK X).hom ≫ prod.fst =
      (originalPresheafFunctor K B hK).map (nativeFirst K B hK X) := by
  exact prod.lift_fst ((originalPresheafFunctor K B hK).map (nativeFirst K B hK X))
    ((originalPresheafFunctor K B hK).map (nativeSecond K B hK X))

/-- The original product comparison retains the actual second projection. -/
theorem originalProductIso_hom_snd (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (originalProductIso K B hK X).hom ≫ prod.snd =
      (originalPresheafFunctor K B hK).map (nativeSecond K B hK X) := by
  exact prod.lift_snd ((originalPresheafFunctor K B hK).map (nativeFirst K B hK X))
    ((originalPresheafFunctor K B hK).map (nativeSecond K B hK X))

/-- The native product comparison carries the actual native diagonal to
the literal presheaf diagonal. -/
theorem nativeDiagonal_comp_productIso (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (nativeDiagonal K B hK X).hom ≫ (nativeProductIso K B hK X).hom = diag X.obj := by
  apply prod.hom_ext
  · rw [Category.assoc, nativeProductIso_hom_fst]
    exact (pullback.diagonal_fst (nativeProjection K B hK X).hom).trans
      (prod.lift_fst (𝟙 X.obj) (𝟙 X.obj)).symm
  · rw [Category.assoc, nativeProductIso_hom_snd]
    exact (pullback.diagonal_snd (nativeProjection K B hK X).hom).trans
      (prod.lift_snd (𝟙 X.obj) (𝟙 X.obj)).symm

/-- The original product comparison carries the actual original image
of the diagonal to the literal original presheaf diagonal. -/
theorem originalDiagonal_comp_productIso (X : AlgebraicSpaces B (Spec (.of K)) hK) :
    (originalPresheafFunctor K B hK).map (nativeDiagonal K B hK X) ≫
      (originalProductIso K B hK X).hom = diag ((originalPresheafFunctor K B hK).obj X) := by
  let E := originalPresheafFunctor K B hK
  have hd₁ : nativeDiagonal K B hK X ≫ nativeFirst K B hK X = 𝟙 X := by
    apply ObjectProperty.hom_ext
    exact pullback.diagonal_fst (nativeProjection K B hK X).hom
  have hd₂ : nativeDiagonal K B hK X ≫ nativeSecond K B hK X = 𝟙 X := by
    apply ObjectProperty.hom_ext
    exact pullback.diagonal_snd (nativeProjection K B hK X).hom
  apply prod.hom_ext
  · rw [Category.assoc, originalProductIso_hom_fst, ← E.map_comp, hd₁, E.map_id]
    exact (prod.lift_fst _ _).symm
  · rw [Category.assoc, originalProductIso_hom_snd, ← E.map_comp, hd₂, E.map_id]
    exact (prod.lift_snd _ _).symm

/-- Actual native separatedness gives the genuine closed original diagonal
on EVERY original test. No original separatedness premise is supplied. -/
theorem originalSpace_diagonal_closed
    (X : AlgebraicSpaces B (Spec (.of K)) hK)
    (hs : Space.IsSeparatedOver B (Spec (.of K)) hK X.obj) :
    (MorphismProperty.inverseImage (@IsClosedImmersion.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf
      (diag (originalSpaceOfNative K B hK X.obj X.property).obj) := by
  let P : MorphismProperty Scheme.{u} := @IsClosedImmersion.{u}
  let Q := P.inverseImage (BigFppfOver.toScheme B (Spec (.of K)) hK)
  have hd : Q.presheaf (nativeDiagonal K B hK X).hom := by
    change Q.presheaf (diag X.obj) at hs
    rw [← nativeDiagonal_comp_productIso K B hK X] at hs
    exact (Q.presheaf.cancel_right_of_respectsIso _ _).mp hs
  let : P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    Stacks.Descent.isClosedImmersion_descendsAlong_fppf
  have hP : P ≤ MorphismProperty.monomorphisms Scheme.{u} ⊓ @LocallyOfFiniteType := by
    intro U V f hf
    have : IsClosedImmersion f := hf
    exact ⟨inferInstance, inferInstance⟩
  have h := presheafProperty_of_native_mono_lft K B hK P hP
    (nativeDiagonal K B hK X) hd
  let R := P.inverseImage (Over.forget (M9StandaloneDraft.Base K))
  change R.presheaf (diag ((originalPresheafFunctor K B hK).obj X))
  rw [← originalDiagonal_comp_productIso K B hK X]
  exact (R.presheaf.cancel_right_of_respectsIso _ _).mpr h

end M9StacksIntegration.AllTestNativeOriginalSeparated
