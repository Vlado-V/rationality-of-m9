module

public import M9StacksIntegration.PrimitiveRadicalOrbitDominance
public import M9StacksIntegration.PrimitiveRadicalOrbitReducedPoints
public import M9StacksIntegration.NativeGenericPointNaturality

@[expose] public section

/-! Genuine generic-source embeddings and the actual geometric kernel pair of
the native dominant radical orbit family. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory Module
open scoped Classical Matrix

namespace M9Native.PrimitiveRadicalOrbitGenericPoints
open PrimitiveRadicalOrbitFamily PrimitiveRadicalOrbitRings PrimitiveRadicalOrbitPoints
open PrimitiveRadicalOrbitReducedPoints
open NativeFunctionFieldFunctor NativeGenericPullbackEvaluation

/-- The actual generic point of an affine integral scheme is the spectrum
of its actual coordinate inclusion into its generic stalk. -/
theorem affine_genericSpec (R : Type) [CommRing R] [IsDomain R] :
    genericSpec (Spec (.of R)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Spec (.of R)).functionField)) := by
  apply ext_of_isAffine
  let κ : CommRingCat.of R ⟶ (Spec (.of R)).functionField :=
    CommRingCat.ofHom (algebraMap R (Spec (.of R)).functionField)
  have hr : (Spec.map κ).appTop =
      (Scheme.ΓSpecIso (.of R)).hom ≫ κ ≫
        (Scheme.ΓSpecIso (Spec (.of R)).functionField).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of R)).inv).mp
    simpa only [← Category.assoc,Iso.inv_hom_id,Category.id_comp] using
      (Scheme.ΓSpecIso_inv_naturality κ).symm
  change (genericSpec (Spec (.of R))).appTop = (Spec.map κ).appTop
  rw [hr]
  simp only [genericSpec,Scheme.fromSpecStalk_appTop,homOfLE_refl,op_id]
  change (Spec (.of R)).presheaf.germ ⊤ (genericPoint (Spec (.of R))) (by trivial) ≫
      (Scheme.ΓSpecIso (Spec (.of R)).functionField).inv =
    (Scheme.ΓSpecIso (.of R)).hom ≫
      ((Scheme.ΓSpecIso (.of R)).inv ≫
        (Spec (.of R)).presheaf.germ ⊤ (genericPoint (Spec (.of R))) (by trivial)) ≫
      (Scheme.ΓSpecIso (Spec (.of R)).functionField).inv
  simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp]

/-- This algebra homomorphism retains the original coordinate-ring inclusion
and the actual structural complex algebra on the native generic stalk. -/
def coordinateEmbedding : coordinateRing →ₐ[ℂ] source.functionField where
  toRingHom := coordinateFunctionFieldMap
  commutes' c := by
    have h := DFunLike.congr_fun (GrassmannianCharts.affine_structureScalarMap ℂ coordinateRing) c
    exact h.symm

variable (K : Type) [Field K] [Algebra ℂ K]

/-- A source-function-field embedding gives its actual coordinate-valued source point. -/
def sourcePoint (s : source.functionField →ₐ[ℂ] K) : Point K := s.comp coordinateEmbedding

/-- The coordinate point above is literally the genuine generic-field point,
not a point chosen from an abstract rational field isomorphism. -/
theorem sourcePoint_spec (s : source.functionField →ₐ[ℂ] K) :
    Spec.map (CommRingCat.ofHom (sourcePoint K s).toRingHom) = point (X := source) s.toRingHom := by
  rw [point,affine_genericSpec,← Spec.map_comp]
  rfl

/-- Actual dominance identifies the image with the actual native target generic point. -/
theorem nativePoint_sourcePoint (s : source.functionField →ₐ[ℂ] K) :
    nativePoint K (sourcePoint K s) =
      point (X := GrassmannianCharts.space ℂ 9 14)
        (s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding).toRingHom := by
  rw [nativePoint,sourcePoint_spec]
  exact NativeGenericPointNaturality.point_comp_dominant PrimitiveRadicalOrbitFamily.map s.toRingHom

/-- Two embeddings agreeing on the actual native target field have the same
actual native nine-plane point. -/
theorem nativePoint_eq_of_target_embeddings_eq (s t : source.functionField →ₐ[ℂ] K)
    (h : s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
      t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding) :
    nativePoint K (sourcePoint K s) = nativePoint K (sourcePoint K t) := by
  rw [nativePoint_sourcePoint,nativePoint_sourcePoint,h]

local instance extensionCharZero : CharZero K := PrimitiveExtensionFieldBridge.charZero_extension K

/-- The genuine field-theoretic kernel pair is related by the actual stabilizer
action on the literal original graph columns. No orbit/fiber premise is supplied:
the only equality is agreement of the two actual target-field embeddings. -/
theorem exists_graph_relation_of_target_embeddings_eq
    (s t : source.functionField →ₐ[ℂ] K)
    (h : s.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding =
      t.comp PrimitiveRadicalOrbitDominance.functionFieldEmbedding) :
    ∃ w : ReducedGraphAction.Stabilizer K,
      (Matrix.toLin' (graphAt K (sourcePoint K t))).range =
        ((Matrix.toLin' (graphAt K (sourcePoint K s))).range).map
          (Matrix.toLin' (ReducedGraphAction.matrixRepresentation K w).val) := by
  let hh := nativePoint_eq_of_target_embeddings_eq K s t h
  exact ⟨collisionReducedElement K (sourcePoint K s) (sourcePoint K t) hh,
    collision_graph_ranges K (sourcePoint K s) (sourcePoint K t) hh⟩

end M9Native.PrimitiveRadicalOrbitGenericPoints
