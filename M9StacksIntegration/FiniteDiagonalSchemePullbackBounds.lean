module

public import M9StacksIntegration.FiniteDiagonalSchemePullback
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Finite-type and quasi-compact bounds for the actual scheme pullback

The finite morphism produced from the actual stack diagonal supplies the
bounds on the same original representing scheme. No finite-type or
quasi-compactness assertion about that scheme is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.FiniteDiagonalSchemePullbackBounds

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local instance siteProducts : HasBinaryProducts (BigFppfOver B S hS) :=
  Stack.hasBinaryProducts_bigFppfOver B S hS

/-- The actual product of the original bases is quasi-compact and locally
of finite type over the same original ground scheme. -/
theorem product_structural_properties
    (Y V : BigFppfOver B S hS)
    [QuasiCompact (B.inclusion.map Y.hom)]
    [LocallyOfFiniteType (B.inclusion.map Y.hom)]
    [QuasiCompact (B.inclusion.map V.hom)]
    [LocallyOfFiniteType (B.inclusion.map V.hom)] :
    QuasiCompact (B.inclusion.map (Y ⨯ V).hom) ∧
      LocallyOfFiniteType (B.inclusion.map (Y ⨯ V).hom) := by
  have hp := (Over.isPullback_of_binaryFan_isLimit
    (BinaryFan.mk (prod.fst : Y ⨯ V ⟶ Y) (prod.snd : Y ⨯ V ⟶ V))
    (prodIsProd Y V)).map B.inclusion
  haveI : QuasiCompact (B.inclusion.map (prod.fst : Y ⨯ V ⟶ Y).left) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  haveI : LocallyOfFiniteType (B.inclusion.map (prod.fst : Y ⨯ V ⟶ Y).left) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp.flip inferInstance
  have hw : B.inclusion.map (Y ⨯ V).hom =
      B.inclusion.map (prod.fst : Y ⨯ V ⟶ Y).left ≫ B.inclusion.map Y.hom := by
    rw [← Functor.map_comp, Over.w]
  rw [hw]
  exact ⟨inferInstance, inferInstance⟩

/-- A scheme finite over this actual product inherits the original
finite-type and quasi-compact ground structure. -/
theorem finite_over_product_structural_properties
    (Y V P : BigFppfOver B S hS) (q : P ⟶ Y ⨯ V)
    (hq : IsFinite ((BigFppfOver.toScheme B S hS).map q))
    [QuasiCompact (B.inclusion.map Y.hom)]
    [LocallyOfFiniteType (B.inclusion.map Y.hom)]
    [QuasiCompact (B.inclusion.map V.hom)]
    [LocallyOfFiniteType (B.inclusion.map V.hom)] :
    QuasiCompact (B.inclusion.map P.hom) ∧
      LocallyOfFiniteType (B.inclusion.map P.hom) := by
  letI := hq
  haveI := (product_structural_properties B S hS Y V).1
  haveI := (product_structural_properties B S hS Y V).2
  have hw : B.inclusion.map P.hom =
      (BigFppfOver.toScheme B S hS).map q ≫ B.inclusion.map (Y ⨯ V).hom := by
    change B.inclusion.map P.hom = B.inclusion.map q.left ≫ _
    rw [← Functor.map_comp, Over.w]
  rw [hw]
  exact ⟨inferInstance, inferInstance⟩

/-- Every genuine morphism over a field from a finite-type quasi-compact
scheme is itself quasi-compact and locally of finite type. Quasi-compactness
uses the DERIVED Noetherian source; finite type uses the actual triangle. -/
theorem overField_morphism_properties
    (K : Type u) [Field K] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of K)) (sY : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    [QuasiCompact sX] [LocallyOfFiniteType sX] (hf : f ≫ sY = sX) :
    QuasiCompact f ∧ LocallyOfFiniteType f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have : LocallyOfFiniteType (f ≫ sY) := hf.symm ▸ inferInstance
  exact ⟨inferInstance, locallyOfFiniteType_of_comp f sY⟩

end M9Native.FiniteDiagonalSchemePullbackBounds
