/-
The native Proj naturality proof adapts the Apache-2.0 source
OAI.AlgebraicGeometry.SheafCohomology.Projective.ToSpecZero:
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.

Other reused algebraic proof patterns and their exact source SHA256 values
are recorded in audits/frame-projective-geometry/provenance.json.
-/
module

public import M9.FrameAction
public import M9.ProjectiveFunctionField
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The frame action on the native projective matrix scheme and its function field

The homogeneous substitutions are the literal linear matrix-coordinate
substitutions of the frozen frame representation. Native `Proj.map` supplies
scheme automorphisms. Their generic-stalk maps supply the function-field
action, with no separately postulated rational-coordinate action.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 250000
set_option Elab.async false
open scoped BigOperators

namespace M9.FrameProjectiveGeometry


open CategoryTheory AlgebraicGeometry MvPolynomial Matrix
open ProjectiveFunctionField ProjectiveGeometry

abbrev W := FrameAction.TetrahedralFrameGroup
abbrev CoordinateSpace := Fin 9 → ℂ
abbrev Matrix9 := Matrix (Fin 9) (Fin 9) ℂ
abbrev GL9 := Matrix.GeneralLinearGroup (Fin 9) ℂ
abbrev HomogeneousRing := ProjectiveSpace.homogeneousCoordinateRing 8
abbrev Grading := ProjectiveSpace.projectiveGrading 8

/-- The frozen actual matrix action, expressed in the nine matrix-entry
coordinates of the native projective scheme. -/
def coordinateRepresentation : W →* (CoordinateSpace ≃ₗ[ℂ] CoordinateSpace) where
  toFun w := matrixCoordinates.symm.trans
    ((FrameAction.tetrahedralRepresentation w).trans matrixCoordinates)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp

/-- Native identification of vector-space and invertible-matrix operators. -/
def coordinateGL : (CoordinateSpace ≃ₗ[ℂ] CoordinateSpace) ≃* GL9 :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv ℂ CoordinateSpace).symm.trans
    Matrix.GeneralLinearGroup.toLin.symm

def matrixRepresentation : W →* GL9 :=
  coordinateGL.toMonoidHom.comp coordinateRepresentation

theorem coordinateGL_mulVec (e : CoordinateSpace ≃ₗ[ℂ] CoordinateSpace) (v : CoordinateSpace) :
    (coordinateGL e : Matrix9) *ᵥ v = e v := by
  have h := Matrix.GeneralLinearGroup.toLin.apply_symm_apply
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  exact congrArg (fun f : LinearMap.GeneralLinearGroup ℂ CoordinateSpace =>
    (f : Module.End ℂ CoordinateSpace) v) h

@[simp] theorem matrixRepresentation_mulVec (w : W) (v : CoordinateSpace) :
    (matrixRepresentation w : Matrix9) *ᵥ v = coordinateRepresentation w v :=
  coordinateGL_mulVec _ _

theorem matrixRepresentation_matrixCoordinates (w : W) (M : FrameAction.Mat3 ℂ) :
    (matrixRepresentation w : Matrix9) *ᵥ matrixCoordinates M =
      matrixCoordinates (FrameAction.tetrahedralRepresentation w M) := by
  rw [matrixRepresentation_mulVec]
  simp [coordinateRepresentation]

/-- Actual homogeneous linear forms determined by a coefficient matrix. -/
def linearForms (B : Matrix9) (i : Fin 9) : HomogeneousRing :=
  ∑ j, C (B i j) * X j

/-- The literal graded substitution on the homogeneous coordinate ring. -/
def substitution (B : Matrix9) : Grading →+*ᵍ Grading where
  toRingHom := eval₂Hom C (linearForms B)
  map_mem hx := by
    apply (mem_homogeneousSubmodule _ _).mpr
    change IsHomogeneous (eval₂ C (linearForms B) _) _
    simpa only [one_mul] using
      ((mem_homogeneousSubmodule _ _).mp hx).eval₂ C (linearForms B)
        (fun c => isHomogeneous_C _ c)
        (fun i => IsHomogeneous.sum _ _ _
          (fun j _ => isHomogeneous_C_mul_X (B i j) j))

@[simp] theorem substitution_C (B : Matrix9) (c : ℂ) : substitution B (C c) = C c := by
  simp [substitution]

@[simp] theorem substitution_X (B : Matrix9) (i : Fin 9) :
    substitution B (X i) = linearForms B i := by simp [substitution]

@[simp] theorem substitution_one : substitution (1 : Matrix9) = GradedRingHom.id Grading := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · exact substitution_C 1
  · intro i
    simp [linearForms, Matrix.one_apply]

theorem substitution_linearForms (B D : Matrix9) (i : Fin 9) :
    substitution D (linearForms B i) = linearForms (B * D) i := by
  simp only [linearForms, map_sum, map_mul, substitution_C, substitution_X, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul, mul_assoc]

/-- Composition is contravariant on coordinate rings, as required by the
actual linear action on matrix-coordinate vectors. -/
theorem substitution_comp (B D : Matrix9) :
    (substitution D).comp (substitution B) = substitution (B * D) := by
  apply GradedRingHom.toRingHom_injective
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro i
    change substitution D (substitution B (X i)) = substitution (B*D) (X i)
    rw [substitution_X, substitution_X]
    exact substitution_linearForms B D i

/-- Evaluation recovers the original matrix-vector action, including every
coefficient and the transpose component. -/
theorem evaluation_substitution (B : Matrix9) (v : CoordinateSpace) (p : HomogeneousRing) :
    MvPolynomial.eval v (substitution B p) = MvPolynomial.eval (B *ᵥ v) p := by
  have h : (MvPolynomial.eval v).comp (substitution B).toRingHom =
      MvPolynomial.eval (B *ᵥ v) := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp
    · intro i
      simp [linearForms, Matrix.mulVec, dotProduct]
  exact RingHom.congr_fun h p

/-- Explicit graded inverses imply the irrelevant-ideal condition for native
`Proj.map`; it is not supplied as a hypothesis. -/
theorem irrelevant_le_map_of_inverse (f g : Grading →+*ᵍ Grading)
    (hfg : f.comp g = GradedRingHom.id Grading) :
    HomogeneousIdeal.irrelevant Grading ≤ (HomogeneousIdeal.irrelevant Grading).map f := by
  change (HomogeneousIdeal.irrelevant Grading).toIdeal ≤
    ((HomogeneousIdeal.irrelevant Grading).map f).toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le Grading).mpr
  intro d hd p hp
  have hg : g p ∈ HomogeneousIdeal.irrelevant Grading :=
    HomogeneousIdeal.mem_irrelevant_of_mem Grading hd (g.map_mem hp)
  have heq : f (g p) = p := congrArg (fun k : Grading →+*ᵍ Grading => k p) hfg
  exact heq ▸ Ideal.mem_map_of_mem f.toRingHom hg

theorem substitution_irrelevant_le (B : GL9) :
    HomogeneousIdeal.irrelevant Grading ≤
      (HomogeneousIdeal.irrelevant Grading).map (substitution (B : Matrix9)) := by
  apply irrelevant_le_map_of_inverse _ (substitution (↑B⁻¹ : Matrix9))
  rw [substitution_comp, Units.inv_mul, substitution_one]

/-- Genuine native `Proj` automorphisms induced by the original linear
coordinate substitution and its actual inverse. -/
def projectiveLinear (B : GL9) : Aut matrixSpace := Aut.of {
  hom := Proj.map (substitution (B : Matrix9)) (substitution_irrelevant_le B)
  inv := Proj.map (substitution (↑B⁻¹ : Matrix9)) (substitution_irrelevant_le B⁻¹)
  hom_inv_id := by
    rw [← Proj.map_comp]
    simp only [substitution_comp, Units.inv_mul, substitution_one, Proj.map_id]
  inv_hom_id := by
    rw [← Proj.map_comp]
    simp only [substitution_comp, Units.mul_inv, substitution_one, Proj.map_id]
 }
@[simp] theorem projectiveLinear_one : projectiveLinear 1 = 1 := by
  apply Aut.ext
  apply Iso.ext
  change Proj.map _ _ = 𝟙 _
  simp only [Units.val_one, substitution_one, Proj.map_id]

theorem projectiveLinear_mul (B D : GL9) :
    projectiveLinear (B*D) = projectiveLinear B * projectiveLinear D := by
  apply Aut.ext
  apply Iso.ext
  change Proj.map _ _ = Proj.map _ _ ≫ Proj.map _ _
  rw [← Proj.map_comp]
  simp only [substitution_comp]
  rfl

/-- The actual finite frame-group action on the native projective matrix scheme. -/
def schemeRepresentation : W →* Aut matrixSpace where
  toFun w := projectiveLinear (matrixRepresentation w)
  map_one' := by rw [map_one, projectiveLinear_one]
  map_mul' g h := by rw [map_mul, projectiveLinear_mul]

/-- The actual coefficient scalar is fixed in every homogeneous localization. -/
theorem awayMap_constants (B : Matrix9) (s : HomogeneousRing) (c : ℂ) :
    HomogeneousLocalization.Away.map (substitution B) s
      (HomogeneousLocalization.fromZeroRingHom Grading (Submonoid.powers s)
        (ProjectiveSpace.degreeZeroConstants 8 c)) =
      HomogeneousLocalization.fromZeroRingHom Grading
        (Submonoid.powers (substitution B s)) (ProjectiveSpace.degreeZeroConstants 8 c) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  congr 1
  · exact substitution_C B c
  · exact Subtype.ext (by simp)

def degreeZeroSubstitution (B : Matrix9) : Grading 0 →+* Grading 0 where
  toFun a := ⟨substitution B a, (substitution B).map_mem a.property⟩
  map_one' := Subtype.ext (map_one (substitution B))
  map_mul' a b := Subtype.ext (map_mul (substitution B) (a : HomogeneousRing) (b : HomogeneousRing))
  map_zero' := Subtype.ext (map_zero (substitution B))
  map_add' a b := Subtype.ext (map_add (substitution B) (a : HomogeneousRing) (b : HomogeneousRing))

theorem awayMap_fromZero (B : Matrix9) (s : HomogeneousRing) (a : Grading 0) :
    HomogeneousLocalization.Away.map (substitution B) s
      (HomogeneousLocalization.fromZeroRingHom Grading (Submonoid.powers s) a) =
      HomogeneousLocalization.fromZeroRingHom Grading
        (Submonoid.powers (substitution B s)) (degreeZeroSubstitution B a) := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk]
  congr 1
  exact Subtype.ext (by simp)

theorem projectiveLinear_toSpecZero (B : GL9) :
    (projectiveLinear B).asIso.hom ≫ Proj.toSpecZero Grading =
      Proj.toSpecZero Grading ≫ Spec.map (CommRingCat.ofHom (degreeZeroSubstitution (B : Matrix9))) := by
  refine (Proj.mapAffineOpenCover (substitution (B : Matrix9))
    (substitution_irrelevant_le B)).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  change Proj.awayι Grading ((substitution (B : Matrix9)) s.2) _ _ ≫
      Proj.map (substitution (B : Matrix9)) _ ≫ Proj.toSpecZero Grading = _
  rw [← Category.assoc,
    Proj.awayι_comp_map (substitution (B : Matrix9)) (substitution_irrelevant_le B)
      s.1.2 (s.2 : HomogeneousRing) s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext (awayMap_fromZero (B : Matrix9) s.2)

/-- Native projectivization preserves the original complex structure morphism. -/
theorem projectiveLinear_over (B : GL9) :
    (projectiveLinear B).asIso.hom ≫ projection 8 = projection 8 := by
  change (projectiveLinear B).asIso.hom ≫ (Proj.toSpecZero Grading ≫ _) = _
  rw [← Category.assoc, projectiveLinear_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact Subtype.ext (substitution_C (B : Matrix9) c)

theorem schemeRepresentation_over (w : W) :
    (schemeRepresentation w).asIso.hom ≫ projection 8 = projection 8 :=
  projectiveLinear_over _

/-- Actual chart functoriality allows the denominator chart to move under
the linear operator; no invariant affine chart is assumed. -/
theorem transformedChart_naturality (B : GL9) (i : Fin 9) :
    Proj.awayι Grading (substitution (B : Matrix9) (X i))
        ((substitution (B : Matrix9)).map_mem (isHomogeneous_X ℂ i)) Nat.zero_lt_one ≫
        (projectiveLinear B).asIso.hom =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map
        (substitution (B : Matrix9)) (X i))) ≫
        Proj.awayι Grading (X i) (isHomogeneous_X ℂ i) Nat.zero_lt_one :=
  Proj.awayι_comp_map _ _ Nat.zero_lt_one (X i) (isHomogeneous_X ℂ i)

/-- On these actual chart rings, the coordinate ratio is sent to the ratio
of the transformed homogeneous linear forms. -/
theorem transformedChart_ratio (B : GL9) (i j : Fin 9) :
    HomogeneousLocalization.Away.map (substitution (B : Matrix9)) (X i)
        (PolynomialToProjectiveChart.projectiveChartRatio 8 i j) =
      HomogeneousLocalization.Away.mk Grading
        ((substitution (B : Matrix9)).map_mem (isHomogeneous_X ℂ i)) 1
        (substitution (B : Matrix9) (X j))
        (by simpa using (substitution (B : Matrix9)).map_mem (isHomogeneous_X ℂ j)) := by
  simp only [PolynomialToProjectiveChart.projectiveChartRatio, HomogeneousLocalization.Away.map_mk]

/-- The actual generic-stalk pullback, with the automorphism carrier kept
explicit so its group operations do not require any reducibility change. -/
def nativePullback (f : Aut matrixSpace)
    (hf : f.asIso.hom ≫ projection 8 = projection 8) :
    matrixFunctionField ≃ₐ[ℂ] matrixFunctionField :=
  ProjectiveFunctionField.automorphismFunctionField 8 f.asIso hf

/-- The native generic-point morphism, used to compare actual stalk maps. -/
abbrev genericSpec : Spec (.of matrixFunctionField) ⟶ matrixSpace :=
  matrixSpace.fromSpecStalk (genericPoint matrixSpace)

/-- The actual generic-stalk pullback square, retaining the original scheme
automorphism rather than a separately declared rational substitution. -/
theorem automorphismFunctionField_square (f : Aut matrixSpace)
    (hf : f.asIso.hom ≫ projection 8 = projection 8) :
    Spec.map (CommRingCat.ofHom (nativePullback f hf).toRingHom) ≫ genericSpec =
      genericSpec ≫ f.asIso.hom := by
  change Spec.map
    ((matrixSpace.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion f.asIso.hom).symm)).hom ≫
        f.asIso.hom.stalkMap (genericPoint matrixSpace)) ≫ _ = _
  rw [Spec.map_comp, Category.assoc, TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Actual generic-stalk pullbacks compose contravariantly. -/
theorem automorphismFunctionField_mul (f g : Aut matrixSpace)
    (hf : f.asIso.hom ≫ projection 8 = projection 8)
    (hg : g.asIso.hom ≫ projection 8 = projection 8)
    (hfg : (f*g).asIso.hom ≫ projection 8 = projection 8) :
    nativePullback (f*g) hfg =
      nativePullback g hg * nativePullback f hf := by
  have h : CommRingCat.ofHom (nativePullback (f*g) hfg).toRingHom =
      CommRingCat.ofHom (nativePullback f hf).toRingHom ≫
        CommRingCat.ofHom (nativePullback g hg).toRingHom := by
    apply Spec.map_injective
    apply (cancel_mono genericSpec).mp
    rw [automorphismFunctionField_square, Spec.map_comp, Category.assoc,
      automorphismFunctionField_square, ← Category.assoc,
      automorphismFunctionField_square, Category.assoc]
    rfl
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun k : CommRingCat.of matrixFunctionField ⟶ CommRingCat.of matrixFunctionField => k z) h

theorem automorphismFunctionField_one
    (h : (1 : Aut matrixSpace).asIso.hom ≫ projection 8 = projection 8) :
    nativePullback (1 : Aut matrixSpace) h = 1 := by
  have heq : CommRingCat.ofHom (nativePullback (1 : Aut matrixSpace) h).toRingHom =
      𝟙 (CommRingCat.of matrixFunctionField) := by
    apply Spec.map_injective
    apply (cancel_mono genericSpec).mp
    rw [automorphismFunctionField_square]
    rw [Spec.map_id]
    change genericSpec ≫ 𝟙 matrixSpace = 𝟙 _ ≫ genericSpec
    simp only [Category.comp_id, Category.id_comp]
  apply AlgEquiv.ext
  intro z
  exact congrArg (fun k : CommRingCat.of matrixFunctionField ⟶ CommRingCat.of matrixFunctionField => k z) heq

/-- The actual left action on the native generic-stalk field is inverse
pullback of the original projective matrix action. -/
def fieldRepresentation : W →* (matrixFunctionField ≃ₐ[ℂ] matrixFunctionField) where
  toFun w := nativePullback (schemeRepresentation w⁻¹)
    (schemeRepresentation_over w⁻¹)
  map_one' := by
    simpa only [inv_one, map_one] using
      automorphismFunctionField_one (show (𝟙 matrixSpace) ≫ projection 8 = projection 8 from
        Category.id_comp _)
  map_mul' g h := by
    have hgh : (schemeRepresentation h⁻¹ * schemeRepresentation g⁻¹).asIso.hom ≫ projection 8 =
        projection 8 := by
      change ((schemeRepresentation g⁻¹).asIso.hom ≫ (schemeRepresentation h⁻¹).asIso.hom) ≫ projection 8 = _
      rw [Category.assoc, schemeRepresentation_over, schemeRepresentation_over]
    simpa only [_root_.mul_inv_rev, map_mul] using
      automorphismFunctionField_mul (schemeRepresentation h⁻¹) (schemeRepresentation g⁻¹)
        (schemeRepresentation_over h⁻¹) (schemeRepresentation_over g⁻¹) hgh

theorem fieldRepresentation_square (w : W) :
    Spec.map (CommRingCat.ofHom (fieldRepresentation w).toRingHom) ≫ genericSpec =
      genericSpec ≫ (schemeRepresentation w⁻¹).asIso.hom :=
  automorphismFunctionField_square _ (schemeRepresentation_over w⁻¹)

/-- The action is a genuine semiring action through complex algebra automorphisms. -/
@[instance_reducible] def fieldAction : MulSemiringAction W matrixFunctionField :=
  MulSemiringAction.compHom matrixFunctionField fieldRepresentation

@[simp] theorem fieldAction_smul (w : W) (x : matrixFunctionField) :
    let _ := fieldAction
    w • x = fieldRepresentation w x := rfl

theorem fieldScalarCommutes :
    let _ := fieldAction
    SMulCommClass W ℂ matrixFunctionField := by
  let _ := fieldAction
  refine ⟨fun w c x => ?_⟩
  exact map_smul (fieldRepresentation w).toLinearEquiv c x

/-- The genuine generic-point morphism is dominant. -/
instance genericSpec_isDominant : IsDominant genericSpec where
  denseRange := by
    intro x
    have hx : x ∈ closure ({genericPoint matrixSpace} : Set matrixSpace) := by
      rw [(genericPoint_spec matrixSpace).def]
      trivial
    apply closure_mono (Set.singleton_subset_iff.mpr ?_) hx
    exact ⟨IsLocalRing.closedPoint matrixFunctionField, Scheme.fromSpecStalk_closedPoint⟩

/-- A native scheme automorphism acting trivially on the actual generic stalk
is the identity; dominance and separatedness prove this scheme statement. -/
theorem scheme_eq_one_of_functionField_eq_one (f : Aut matrixSpace)
    (hf : f.asIso.hom ≫ projection 8 = projection 8)
    (h : nativePullback f hf = 1) : f = 1 := by
  apply Aut.ext
  apply Iso.ext
  change f.asIso.hom = 𝟙 matrixSpace
  apply ext_of_isDominant (ι := genericSpec)
  have hsquare := automorphismFunctionField_square f hf
  rw [h] at hsquare
  change Spec.map (𝟙 (CommRingCat.of matrixFunctionField)) ≫ genericSpec = genericSpec ≫ f.asIso.hom at hsquare
  simpa using hsquare.symm

/-- Literal evaluation of matrix coordinates as sections of `Spec ℂ`. -/
def vectorGlobalSections (v : CoordinateSpace) : HomogeneousRing →+* Γ(Spec (.of ℂ), ⊤) :=
  (Scheme.ΓSpecIso (.of ℂ)).inv.hom.comp (MvPolynomial.eval v)

theorem vectorGlobalSections_irrelevant (v : CoordinateSpace) (hv : v ≠ 0) :
    (HomogeneousIdeal.irrelevant Grading).toIdeal.map (vectorGlobalSections v) = ⊤ := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hx : (X i : HomogeneousRing) ∈ (HomogeneousIdeal.irrelevant Grading).toIdeal :=
    HomogeneousIdeal.mem_irrelevant_of_mem Grading Nat.zero_lt_one (isHomogeneous_X ℂ i)
  apply Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem (vectorGlobalSections v) hx)
  change IsUnit ((Scheme.ΓSpecIso (.of ℂ)).inv (MvPolynomial.eval v (X i)))
  rw [MvPolynomial.eval_X]
  exact (isUnit_iff_ne_zero.mpr hi).map (Scheme.ΓSpecIso (.of ℂ)).inv.hom

/-- A nonzero actual coordinate vector defines a point of the actual native
projective scheme. -/
def vectorPoint (v : CoordinateSpace) (hv : v ≠ 0) : Spec (.of ℂ) ⟶ matrixSpace :=
  Proj.fromOfGlobalSections Grading (vectorGlobalSections v) (vectorGlobalSections_irrelevant v hv)

theorem vectorPoint_mem_basicOpen (v : CoordinateSpace) (hv : v ≠ 0)
    (f : HomogeneousRing) (hf : f.IsHomogeneous 1) :
    vectorPoint v hv (default : Spec (.of ℂ)) ∈ Proj.basicOpen Grading f ↔
      MvPolynomial.eval v f ≠ 0 := by
  change (default : Spec (.of ℂ)) ∈ vectorPoint v hv ⁻¹ᵁ Proj.basicOpen Grading f ↔ _
  rw [vectorPoint, Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.zero_lt_one hf]
  change (default : Spec (.of ℂ)) ∈
    (Spec (.of ℂ)).basicOpen ((Scheme.ΓSpecIso (.of ℂ)).inv (MvPolynomial.eval v f)) ↔ _
  rw [basicOpen_eq_of_affine]
  change MvPolynomial.eval v f ∉ (default : Spec (.of ℂ)).asIdeal ↔ _
  rw [Scheme.default_asIdeal]
  rfl

/-- If native projectivization is the identity, its original linear
substitution preserves every homogeneous linear vanishing test. -/
theorem evaluation_ne_zero_iff_of_projectiveLinear_eq_one (B : GL9)
    (hB : projectiveLinear B = 1) (v : CoordinateSpace) (hv : v ≠ 0)
    (f : HomogeneousRing) (hf : f.IsHomogeneous 1) :
    MvPolynomial.eval ((B : Matrix9) *ᵥ v) f ≠ 0 ↔ MvPolynomial.eval v f ≠ 0 := by
  have hopen : Proj.basicOpen Grading (substitution (B : Matrix9) f) =
      Proj.basicOpen Grading f := by
    have h := congrArg (fun z : Aut matrixSpace => z.asIso.hom ⁻¹ᵁ Proj.basicOpen Grading f) hB
    exact h
  rw [← evaluation_substitution]
  exact (vectorPoint_mem_basicOpen v hv _ ((substitution (B : Matrix9)).map_mem hf)).symm.trans
    ((Iff.of_eq (congrArg (fun U => vectorPoint v hv (default : Spec (.of ℂ)) ∈ U) hopen)).trans
      (vectorPoint_mem_basicOpen v hv f hf))

/-- Identity of the actual projective scheme forces the original linear
operator to preserve every vector line. -/
theorem scalarMultiple_of_projectiveLinear_eq_one (B : GL9)
    (hB : projectiveLinear B = 1) (v : CoordinateSpace) (hv : v ≠ 0) :
    ∃ c : ℂ, (B : Matrix9) *ᵥ v = c • v := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let w := (B : Matrix9) *ᵥ v
  refine ⟨w i / v i, ?_⟩
  funext j
  let f : HomogeneousRing := C (v i) * X j - C (v j) * X i
  have hf : f.IsHomogeneous 1 :=
    (isHomogeneous_C_mul_X (v i) j).sub (isHomogeneous_C_mul_X (v j) i)
  have hvf : MvPolynomial.eval v f = 0 := by simp [f, mul_comm]
  have hwf : MvPolynomial.eval w f = 0 := by
    by_contra h
    exact (evaluation_ne_zero_iff_of_projectiveLinear_eq_one B hB v hv f hf).mp h hvf
  have hcross : v i * w j = v j * w i := by
    apply sub_eq_zero.mp
    simpa [f] using hwf
  change w j = (w i / v i) * v j
  calc
    w j = (v j * w i) / v i :=
      (eq_div_iff hi).mpr (by simpa only [mul_comm] using hcross)
    _ = (w i / v i) * v j := by ring

/-- Faithfulness on projective points now gives faithfulness of the actual
native projective scheme action. -/
theorem schemeRepresentation_injective : Function.Injective schemeRepresentation := by
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  apply FrameAction.tetrahedralProjectiveRepresentation_injective
  rw [map_one]
  apply Equiv.ext
  intro L
  change FrameAction.tetrahedralRepresentation w • L = L
  induction L using Projectivization.ind with
  | h M hM =>
    have hv : matrixCoordinates M ≠ 0 := by
      intro h
      exact hM (matrixCoordinates.injective (h.trans (map_zero matrixCoordinates).symm))
    obtain ⟨c,hc⟩ := scalarMultiple_of_projectiveLinear_eq_one (matrixRepresentation w) hw
      (matrixCoordinates M) hv
    have heq : FrameAction.tetrahedralRepresentation w M = c • M := by
      apply matrixCoordinates.injective
      simpa only [matrixRepresentation_matrixCoordinates, map_smul] using hc
    rw [Projectivization.smul_mk]
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,heq.symm⟩

/-- Faithfulness is proved on the actual native generic-stalk field. -/
theorem fieldRepresentation_injective : Function.Injective fieldRepresentation := by
  apply (injective_iff_map_eq_one _).mpr
  intro w hw
  have hscheme : schemeRepresentation w⁻¹ = 1 :=
    scheme_eq_one_of_functionField_eq_one _ (schemeRepresentation_over w⁻¹) hw
  have hinv : w⁻¹ = 1 :=
    (injective_iff_map_eq_one _).mp schemeRepresentation_injective _ hscheme
  exact inv_eq_one.mp hinv

theorem fieldAction_faithful :
    let _ := fieldAction
    FaithfulSMul W matrixFunctionField := by
  let _ := fieldAction
  refine ⟨fun {g h} heq => fieldRepresentation_injective ?_⟩
  apply AlgEquiv.ext
  exact heq

/-- Canonical identification with the permutation-frame group used in the
finite wreath-product invariant-field calculation. -/
def frameGroupCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    FrameAction.FrameGroup G ≃* FrameAction.FrameGroup H where
  toFun x := ⟨e x.first,e x.second,x.odd⟩
  invFun x := ⟨e.symm x.first,e.symm x.second,x.odd⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp
  map_mul' x y := by
    cases x with
    | mk a b o =>
      rcases y with ⟨c,d,p⟩
      cases o <;> simp only [FrameAction.FrameGroup.mul_even, FrameAction.FrameGroup.mul_odd,
        map_mul]

def permutationFrameGroupEquiv : W ≃* FrameAction.FrameGroup (Equiv.Perm (Fin 4)) :=
  frameGroupCongr TetrahedralGroup.framePermutation

end M9.FrameProjectiveGeometry
