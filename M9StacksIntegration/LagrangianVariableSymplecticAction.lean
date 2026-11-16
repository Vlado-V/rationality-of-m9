module

public import M9StacksIntegration.LagrangianSymplecticAction

/-!
# Variable symplectic matrices on actual LG-valued points

The symplectic matrix has coefficients in the actual global-section ring
of the test scheme, which may have nilpotents. Precomposing the original
quotient by its genuine free-sheaf automorphism and using the native
Grassmannian classifier produces an actual LG-valued point. The quotient
isomorphism retains the original map, and canonical pullback maps the
matrix coefficients through the actual map on global sections.

The quotient-classifier argument follows the frozen constant-action
construction in `LagrangianSymplecticAction`; no constant-field action is
substituted for the variable matrix action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Matrix

universe u

namespace M9Native.LagrangianVariableSymplecticAction

open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianGrassmannian M9Native.LagrangianMatrixChart
open M9Native.LagrangianTransitivity M9Native.LagrangianSigmaInvariance
open M9Native.LagrangianFreeMatrixPullback
open M9Native.LagrangianSymplecticAction

section Rings

variable (R : Type u) [CommRing R]

theorem matrixSix_one : matrixSix R (1 : Matrix.symplecticGroup (Fin 3) R) = 1 := by
  change (1 : Matrix SplitIndex SplitIndex R).submatrix splitIndex.symm splitIndex.symm = 1
  exact Matrix.submatrix_one_equiv splitIndex.symm

theorem matrixSix_mul (g h : Matrix.symplecticGroup (Fin 3) R) :
    matrixSix R (g * h) = matrixSix R g * matrixSix R h := by
  change ((g : Matrix SplitIndex SplitIndex R) * (h : Matrix SplitIndex SplitIndex R)).submatrix
    splitIndex.symm splitIndex.symm = _
  exact (Matrix.submatrix_mul_equiv _ _ splitIndex.symm splitIndex.symm splitIndex.symm).symm

end Rings

theorem freeSymplecticIso_one (T : Scheme.{u}) :
    (freeSymplecticIso T 1).hom = 𝟙 (freeOn T 6) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [freeSymplecticIso_matrix, Stacks.FreeSheafMatrix.toMatrix_id, matrixSix_one]

/-- Actual sheaf composition reverses the coefficient-matrix order. -/
theorem freeSymplecticIso_mul (T : Scheme.{u})
    (g h : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    (freeSymplecticIso T (g * h)).hom =
      (freeSymplecticIso T h).hom ≫ (freeSymplecticIso T g).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [Stacks.FreeSheafMatrix.toMatrix_comp, freeSymplecticIso_matrix,
    freeSymplecticIso_matrix, freeSymplecticIso_matrix, matrixSix_mul]

/-- The actual free-sheaf pullback changes every variable matrix coefficient. -/
theorem freeSymplecticIso_pullback {S T : Scheme.{u}} (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    pulledFreeEnd f (freeSymplecticIso S g).hom =
      (freeSymplecticIso T (mapSymplectic Γ(S, ⊤) f.appTop.hom g)).hom := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [pulledFreeEnd_matrix, freeSymplecticIso_matrix,
    freeSymplecticIso_matrix, matrixSix_map]

theorem freeSymplecticIso_pullback_inv {S T : Scheme.{u}} (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map (freeSymplecticIso S g).hom =
      (freeSymplecticIso T (mapSymplectic Γ(S, ⊤) f.appTop.hom g)).hom ≫
        (pullbackFreeIso f 6).inv := by
  have h := congrArg (fun a => a ≫ (pullbackFreeIso f 6).inv)
    (freeSymplecticIso_pullback f g)
  simp only [pulledFreeEnd, Category.assoc] at h
  rw [(pullbackFreeIso f 6).hom_inv_id, Category.comp_id] at h
  exact h

/-- Precompose an actual quotient by the variable symplectic automorphism. -/
def transform {T : Scheme.{u}} (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤))
    (q : QuotientPresentation T 3 6) : QuotientPresentation T 3 6 := by
  letI : Epi q.map := q.map_epi
  exact { target := q.target
          map := (freeSymplecticIso T g).hom ≫ q.map
          map_epi := inferInstance
          finiteLocallyFree := q.finiteLocallyFree }

theorem transform_respects_isomorphic {T : Scheme.{u}}
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) {q q' : QuotientPresentation T 3 6}
    (h : q.Isomorphic q') : (transform g q).Isomorphic (transform g q') := by
  obtain ⟨e, he⟩ := h
  refine ⟨e, ?_⟩
  change ((freeSymplecticIso T g).hom ≫ q.map) ≫ e.hom =
    (freeSymplecticIso T g).hom ≫ q'.map
  rw [Category.assoc, he]

theorem transform_one {T : Scheme.{u}} (q : QuotientPresentation T 3 6) :
    (transform 1 q).Isomorphic q := by
  refine ⟨Iso.refl _, ?_⟩
  change ((freeSymplecticIso T 1).hom ≫ q.map) ≫ 𝟙 _ = q.map
  rw [freeSymplecticIso_one, Category.id_comp, Category.comp_id]

theorem transform_mul {T : Scheme.{u}}
    (g h : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) (q : QuotientPresentation T 3 6) :
    (transform h (transform g q)).Isomorphic (transform (g * h) q) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((freeSymplecticIso T h).hom ≫ (freeSymplecticIso T g).hom ≫ q.map) ≫ 𝟙 _ =
    (freeSymplecticIso T (g * h)).hom ≫ q.map
  rw [Category.comp_id, freeSymplecticIso_mul, Category.assoc]

theorem pullback_transform {S T : Scheme.{u}} (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) (q : QuotientPresentation S 3 6) :
    (pullbackPresentation f (transform g q)).Isomorphic
      (transform (mapSymplectic Γ(S, ⊤) f.appTop.hom g) (pullbackPresentation f q)) := by
  refine ⟨Iso.refl _, ?_⟩
  change ((pullbackFreeIso f 6).inv ≫
    (Scheme.Modules.pullback f).map ((freeSymplecticIso S g).hom ≫ q.map)) ≫ 𝟙 _ =
      (freeSymplecticIso T (mapSymplectic Γ(S, ⊤) f.appTop.hom g)).hom ≫
        (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map q.map
  rw [Category.comp_id, Functor.map_comp, ← Category.assoc,
    freeSymplecticIso_pullback_inv, Category.assoc]

def transformPoints {T : Scheme.{u}} (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    Points T 3 6 → Points T 3 6 :=
  Quotient.lift (fun q => (⟦transform g q⟧ : Points T 3 6)) (by
    intro q q' h
    induction h with
    | rel _ _ h => exact Quotient.sound (.rel _ _ (transform_respects_isomorphic g h))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih ih' => exact ih.trans ih')

theorem transformPoints_one {T : Scheme.{u}} (x : Points T 3 6) :
    transformPoints 1 x = x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_one q))

theorem transformPoints_mul {T : Scheme.{u}}
    (g h : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) (x : Points T 3 6) :
    transformPoints h (transformPoints g x) = transformPoints (g * h) x := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (transform_mul g h q))

theorem transformPoints_natural {S T : Scheme.{u}} (f : T ⟶ S)
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) (x : Points S 3 6) :
    pullbackPointsMap f 3 6 (transformPoints g x) =
      transformPoints (mapSymplectic Γ(S, ⊤) f.appTop.hom g) (pullbackPointsMap f 3 6 x) := by
  refine Quotient.inductionOn x fun q => ?_
  exact Quotient.sound (.rel _ _ (pullback_transform f g q))

variable (K : Type u) [Field K]

/-- The original quotient on the given test scheme, with its original map. -/
def pointQuotient {T : Scheme.{u}} (p : T ⟶ space K) : QuotientPresentation T 3 6 :=
  pullbackPresentation (p ≫ inclusion K) (universalQuotient K)

theorem pointQuotient_annihilates {T : Scheme.{u}} (p : T ⟶ space K) :
    AnnihilatesSigma T (pointQuotient K p).map :=
  (factorsThrough_iff_pullbackQuotient_annihilates K (p ≫ inclusion K)).mp ⟨p, rfl⟩

def actedQuotient {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) : QuotientPresentation T 3 6 :=
  transform g (pointQuotient K p)

theorem actedQuotient_annihilates {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    AnnihilatesSigma T (actedQuotient K p g).map :=
  (annihilatesSigma_precomp_iff T (pointQuotient K p).map g).mpr
    (pointQuotient_annihilates K p)

def pointClassifying {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) : T ⟶ grassmannian K :=
  M9Native.MukaiLagrangianMap.classifying K (p ≫ projection K) (actedQuotient K p g)

theorem exists_actPoint {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    ∃ a : T ⟶ space K, a ≫ inclusion K = pointClassifying K p g := by
  obtain ⟨e, he⟩ := M9Native.MukaiLagrangianMap.classifying_pullback_isomorphic
    K (p ≫ projection K) (actedQuotient K p g)
  apply (factorsThrough_iff_pullbackQuotient_annihilates K (pointClassifying K p g)).mpr
  exact (annihilatesSigma_iff_of_iso T _ _ e he).mpr (actedQuotient_annihilates K p g)

/-- The actual LG-valued point for a matrix over the actual global-section ring. -/
def actPoint {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) : T ⟶ space K :=
  Classical.choose (exists_actPoint K p g)

@[reassoc] theorem actPoint_inclusion {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    actPoint K p g ≫ inclusion K = pointClassifying K p g :=
  Classical.choose_spec (exists_actPoint K p g)

@[reassoc (attr := simp)] theorem actPoint_projection {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    actPoint K p g ≫ projection K = p ≫ projection K := by
  change (actPoint K p g ≫ inclusion K) ≫ grassmannianProjection K = _
  rw [actPoint_inclusion]
  exact M9Native.MukaiLagrangianMap.classifying_projection K
    (p ≫ projection K) (actedQuotient K p g)

/-- The literal original quotient class of the constructed scheme morphism. -/
theorem pointClass_actPoint {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    pointClass K (actPoint K p g) = transformPoints g (pointClass K p) := by
  rw [pointClass, pullbackUniversal_class, actPoint_inclusion]
  exact M9Native.MukaiLagrangianMap.classifying_class K
    (p ≫ projection K) (actedQuotient K p g)

/-- This isomorphism retains the actual quotient map, not only its target. -/
theorem pullback_actPoint_isomorphic {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    (pointQuotient K (actPoint K p g)).Isomorphic (actedQuotient K p g) :=
  presentation_isomorphic_of_class_eq (pointClass_actPoint K p g)

theorem actPoint_one {T : Scheme.{u}} (p : T ⟶ space K) : actPoint K p 1 = p := by
  apply hom_ext K
  · exact actPoint_projection K p 1
  · rw [pointClass_actPoint, transformPoints_one]

/-- Quotient precomposition gives a genuine right action on each test scheme. -/
theorem actPoint_mul {T : Scheme.{u}} (p : T ⟶ space K)
    (g h : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    actPoint K (actPoint K p g) h = actPoint K p (g * h) := by
  apply hom_ext K
  · rw [actPoint_projection, actPoint_projection, actPoint_projection]
  · rw [pointClass_actPoint, pointClass_actPoint, pointClass_actPoint]
    exact transformPoints_mul g h (pointClass K p)

theorem actPoint_inv {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    actPoint K (actPoint K p g) g⁻¹ = p := by
  rw [actPoint_mul, mul_inv_cancel, actPoint_one]

theorem actPoint_inv_left {T : Scheme.{u}} (p : T ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(T, ⊤)) :
    actPoint K (actPoint K p g⁻¹) g = p := by
  rw [actPoint_mul, inv_mul_cancel, actPoint_one]

/-- Naturality uses the actual map on global functions of an arbitrary scheme morphism. -/
theorem actPoint_natural {S T : Scheme.{u}} (f : T ⟶ S) (p : S ⟶ space K)
    (g : Matrix.symplecticGroup (Fin 3) Γ(S, ⊤)) :
    f ≫ actPoint K p g =
      actPoint K (f ≫ p) (mapSymplectic Γ(S, ⊤) f.appTop.hom g) := by
  apply hom_ext K
  · rw [Category.assoc, actPoint_projection, actPoint_projection, Category.assoc]
  · rw [pointClass_comp, pointClass_actPoint, transformPoints_natural,
      pointClass_actPoint, pointClass_comp]

end M9Native.LagrangianVariableSymplecticAction

end
