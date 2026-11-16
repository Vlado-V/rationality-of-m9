module

public import M9StacksIntegration.MukaiLagrangianMap
public import M9StacksIntegration.MukaiPrimitiveDuality
public import M9StacksIntegration.LagrangianDeterminantSections
public import M9StacksIntegration.LagrangianPluckerQuotient
public import M9StacksIntegration.LagrangianPrimitiveSectionsPullback
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality

/-!
# Primitive determinant evaluation from the original complete evaluation

The third exterior evaluation factors through the dual of the actual
primitive exterior kernel.  The factor is obtained from the actual
exterior-square relation, rather than from a dimension or surjectivity
assumption.  The normalized classifying quotient retains its commuting
triangle with the original complete evaluation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open scoped BigOperators

universe u

namespace M9Native.MukaiPrimitiveCanonicalEvaluation

open MukaiLagrangianMap

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  MukaiLagrangianMap.lagrangianQuotient AlgebraicGeometry.Grassmannian.pullbackPresentation

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k)) (E : X.Modules)

abbrev DeterminantH0 := cohomologyOverField k f (Scheme.Modules.exteriorPower E (3 : ℤ)) 0

/-- Exterior evaluation in the actual complete H0 basis. -/
def lambdaThree (b : Basis (Fin 6) k (H0 k f E)) :
    LagrangianField.Third k →ₗ[k] DeterminantH0 k f E :=
  (ExteriorEvaluation.lambda k f E 3).comp
    (exteriorPower.map 3 b.equivFun.symm.toLinearMap)

theorem lambdaThree_ιMulti (b : Basis (Fin 6) k (H0 k f E))
    (v : Fin 3 → LagrangianField.V k) :
    lambdaThree k f E b (exteriorPower.ιMulti k 3 v) =
      ExteriorEvaluation.lambda k f E 3
        (exteriorPower.ιMulti k 3 (fun i => b.equivFun.symm (v i))) := by
  change ExteriorEvaluation.lambda k f E 3
    (exteriorPower.map 3 b.equivFun.symm.toLinearMap (exteriorPower.ιMulti k 3 v)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

/-- The actual degree-three global section is the product of the actual
degree-two section with the remaining original section. -/
theorem lambdaThree_global_product (a b c : H0 k f E) :
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
      (ExteriorEvaluation.lambda k f E 3 (exteriorPower.ιMulti k 3 ![a, b, c])) =
    ((Scheme.Modules.exteriorAlgebra E).mul 2 1).app (op ⊤)
      ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (2 : ℤ))).hom
        (ExteriorEvaluation.lambda k f E 2 (exteriorPower.ιMulti k 2 ![a, b])))
      ((Scheme.Modules.exteriorGenerator E).val.app (op ⊤)
        (ExteriorEvaluation.h0SectionsSemilinear k f E c)) := by
  let A := (Scheme.Modules.exteriorAlgebra E).toPresheafGradedAlgebra
  let gen := fun s : H0 k f E => (Scheme.Modules.exteriorGenerator E).val.app (op ⊤)
    (ExteriorEvaluation.h0SectionsSemilinear k f E s)
  have h₂ := (ExteriorEvaluation.lambda_ιMulti k f E 2 ![a, b]).trans
    (ExteriorEvaluation.sectionComparison_ιMulti E 2 ⊤ _)
  have h₃ := (ExteriorEvaluation.lambda_ιMulti k f E 3 ![a, b, c]).trans
    (ExteriorEvaluation.sectionComparison_ιMulti E 3 ⊤ _)
  calc
    _ = A.homogeneousProd (op ⊤) 3 (fun i => gen (![a, b, c] i)) := h₃
    _ = (A.mul 2 1).app (op ⊤)
        (A.homogeneousProd (op ⊤) 2 (fun i => gen (![a, b] i))) (gen c) := rfl
    _ = _ := congrArg (fun z => (A.mul 2 1).app (op ⊤) z (gen c)) h₂.symm

theorem lambdaThree_wedgeSigma_eq_zero (b : Basis (Fin 6) k (H0 k f E))
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (v : LagrangianField.V k) :
    lambdaThree k f E b (MukaiPrimitiveDuality.wedgeSigma k v) = 0 := by
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom).injective
  rw [map_zero, MukaiPrimitiveDuality.wedgeSigma_apply, map_sum, map_sum]
  have h : ∑ i : Fin 3,
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (2 : ℤ))).hom
        (ExteriorEvaluation.lambda k f E 2
          (exteriorPower.ιMulti k 2 ![b (i.castAdd 3), b (Fin.natAdd 3 i)])) = 0 := by
    simpa only [basisSigma, map_sum, hσ, map_zero] using congrArg
      (fun z => (cohomologyOverFieldZeroLinearIso k f
        (Scheme.Modules.exteriorPower E (2 : ℤ))).hom z) hσ
  calc
    _ = ∑ i : Fin 3, ((Scheme.Modules.exteriorAlgebra E).mul 2 1).app (op ⊤)
        ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (2 : ℤ))).hom
          (ExteriorEvaluation.lambda k f E 2
            (exteriorPower.ιMulti k 2 ![b (i.castAdd 3), b (Fin.natAdd 3 i)])))
        ((Scheme.Modules.exteriorGenerator E).val.app (op ⊤)
          (ExteriorEvaluation.h0SectionsSemilinear k f E (b.equivFun.symm v))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [LagrangianField.wedge3, lambdaThree_ιMulti]
      have hi : (fun j : Fin 3 => b.equivFun.symm
          (![LagrangianField.e k i, LagrangianField.f k i, v] j)) =
          ![b (i.castAdd 3), b (Fin.natAdd 3 i), b.equivFun.symm v] := by
        funext j
        fin_cases j <;> simp [LagrangianField.e, LagrangianField.f,
          LagrangianField.eIndex, LagrangianField.fIndex, LagrangianField.basisVector]
      rw [hi]
      exact lambdaThree_global_product k f E _ _ _
    _ = _ := by
      let mv := (((Scheme.Modules.exteriorAlgebra E).mul 2 1).app (op ⊤)).flip
        ((Scheme.Modules.exteriorGenerator E).val.app (op ⊤)
          (ExteriorEvaluation.h0SectionsSemilinear k f E (b.equivFun.symm v)))
      change (∑ i : Fin 3, mv
        ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (2 : ℤ))).hom
          (ExteriorEvaluation.lambda k f E 2
            (exteriorPower.ιMulti k 2 ![b (i.castAdd 3), b (Fin.natAdd 3 i)])))) = 0
      rw [← map_sum, h, map_zero]

variable [CharZero k]

/-- The primitive determinant evaluation has exactly the coordinate
module used by the native primitive Plucker morphism. -/
def primitiveEvaluation (b : Basis (Fin 6) k (H0 k f E)) :
    Module.Dual k (LagrangianField.Primitive k) →ₗ[k] DeterminantH0 k f E :=
  MukaiPrimitiveDuality.factor k (lambdaThree k f E b)

theorem primitiveEvaluation_restriction (b : Basis (Fin 6) k (H0 k f E))
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (ell : Module.Dual k (LagrangianField.Third k)) :
    primitiveEvaluation k f E b (MukaiPrimitiveDuality.restriction k ell) =
      lambdaThree k f E b ((MukaiPrimitiveDuality.coefficientDuality k).symm ell) :=
  MukaiPrimitiveDuality.factor_restriction k (lambdaThree k f E b)
    (lambdaThree_wedgeSigma_eq_zero k f E b hσ) ell

/-- Passing to primitive coordinates preserves the actual determinant
linear system, without assuming it is all determinant cohomology. -/
theorem range_primitiveEvaluation (b : Basis (Fin 6) k (H0 k f E))
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0) :
    LinearMap.range (primitiveEvaluation k f E b) = LinearMap.range (lambdaThree k f E b) := by
  apply Submodule.ext
  intro t
  constructor
  · rintro ⟨ell, rfl⟩
    exact ⟨(MukaiPrimitiveDuality.coefficientDuality k).symm
      (MukaiPrimitiveDuality.extension k ell), rfl⟩
  · rintro ⟨w, rfl⟩
    refine ⟨MukaiPrimitiveDuality.restriction k (MukaiPrimitiveDuality.coefficientDuality k w), ?_⟩
    rw [primitiveEvaluation_restriction k f E b hσ, LinearEquiv.symm_apply_apply]

/-- Every original ordered determinant section is recovered by restriction
to the actual primitive coordinate module. -/
theorem primitiveEvaluation_minor (b : Basis (Fin 6) k (H0 k f E))
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (c : LagrangianPluckerLinear.MinorIndex) :
    primitiveEvaluation k f E b
        (LagrangianPluckerLinear.primitiveLinearMap k (Pi.basisFun k _ c)) =
      ExteriorEvaluation.lambda k f E 3
        (exteriorPower.ιMulti k 3 (fun i => b (c i))) := by
  rw [LagrangianPluckerFactor.primitiveLinearMap_basis]
  change primitiveEvaluation k f E b
    (MukaiPrimitiveDuality.restriction k (LagrangianField.coordinate3 k c)) = _
  rw [primitiveEvaluation_restriction k f E b hσ,
    MukaiPrimitiveDuality.coefficientSharp_coordinate, lambdaThree_ιMulti]
  congr 2
  funext i
  exact Basis.equivFun_symm_single b (c i)

theorem primitiveEvaluation_basis (b : Basis (Fin 6) k (H0 k f E)) (j : Fin 14) :
    primitiveEvaluation k f E b
        ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j) =
      ∑ i : Fin 20, LagrangianField.projectionMatrix k j i •
        lambdaThree k f E b (LagrangianField.thirdBasis20 k i) :=
  MukaiPrimitiveDuality.factor_basis k (lambdaThree k f E b) j

omit [CharZero k] in
theorem lambdaThree_thirdBasis (b : Basis (Fin 6) k (H0 k f E)) (i : Fin 20) :
    lambdaThree k f E b (LagrangianField.thirdBasis20 k i) =
      ExteriorEvaluation.lambda k f E 3
        (exteriorPower.ιMulti k 3 (fun j => b (LagrangianRing.triple i j))) := by
  rw [← LagrangianRing.thirdBasis20_eq_field, LagrangianRing.thirdBasis20_apply,
    lambdaThree_ιMulti]
  congr 2
  funext j
  exact Basis.equivFun_symm_single b (LagrangianRing.triple i j)

omit [CharZero k] in
/-- The native quotient minor of the original complete evaluation is
the original global exterior-evaluation section, with no choice of a
determinant-line trivialization. -/
theorem evaluation_minorSection (b : Basis (Fin 6) k (H0 k f E))
    (c : LagrangianPluckerLinear.MinorIndex) :
    LagrangianDeterminantSections.minorSection X
        (MukaiSemiIrreducible.evaluation k f E b) c =
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
        (ExteriorEvaluation.lambda k f E 3
          (exteriorPower.ιMulti k 3 (fun i => b (c i)))) := by
  rw [LagrangianDeterminantSections.minorSection_eq_wedge]
  have hi : (fun i : Fin 3 =>
      (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation k f E b) ⊤)
        (LagrangianMatrixChart.freeBasisSection X 6 (c i))) =
      (fun i => ExteriorEvaluation.h0SectionsSemilinear k f E (b (c i))) := by
    funext i
    exact evaluation_freeVector k f E b (c i)
  rw [hi]
  exact (ExteriorEvaluation.lambda_ιMulti k f E 3 (fun i => b (c i))).symm

/-- In particular the fourteen actual sections are explicit fixed linear
combinations of the original determinant evaluation sections. -/
theorem primitiveEvaluation_basis_original (b : Basis (Fin 6) k (H0 k f E)) (j : Fin 14) :
    primitiveEvaluation k f E b
        ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j) =
      ∑ i : Fin 20, LagrangianField.projectionMatrix k j i •
        ExteriorEvaluation.lambda k f E 3
          (exteriorPower.ιMulti k 3 (fun a => b (LagrangianRing.triple i a))) := by
  rw [primitiveEvaluation_basis]
  simp only [lambdaThree_thirdBasis]

/-- The native fourteen primitive quotient sections of complete evaluation
are precisely the actual factored exterior-evaluation sections. -/
theorem evaluation_primitiveSection (b : Basis (Fin 6) k (H0 k f E)) (j : Fin 14) :
    LagrangianPluckerQuotient.primitiveSection X k (ExteriorEvaluation.baseRingMap k f)
        (MukaiSemiIrreducible.evaluation k f E b) j =
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
        (primitiveEvaluation k f E b
          ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j)) := by
  rw [primitiveEvaluation_basis_original, map_sum]
  simp only [LagrangianPluckerQuotient.primitiveSection, evaluation_minorSection]
  apply Finset.sum_congr rfl
  intro i _
  exact ((ExteriorEvaluation.h0SectionsSemilinear k f
    (Scheme.Modules.exteriorPower E (3 : ℤ))).map_smulₛₗ _ _).symm

/-- Transport uses an actual determinant-line isomorphism.  Taking the
target to be the native dualizing sheaf gives the canonical evaluation. -/
def transportedEvaluation (b : Basis (Fin 6) k (H0 k f E))
    {L : X.Modules} (d : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ L) :
    Module.Dual k (LagrangianField.Primitive k) →ₗ[k] cohomologyOverField k f L 0 :=
  (cohomologyOverFieldMap k f d.hom 0).hom.comp (primitiveEvaluation k f E b)

theorem transportedEvaluation_minor (b : Basis (Fin 6) k (H0 k f E))
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    {L : X.Modules} (d : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ L)
    (c : LagrangianPluckerLinear.MinorIndex) :
    transportedEvaluation k f E b d
        (LagrangianPluckerLinear.primitiveLinearMap k (Pi.basisFun k _ c)) =
      cohomologyOverFieldMap k f d.hom 0
        (ExteriorEvaluation.lambda k f E 3
          (exteriorPower.ιMulti k 3 (fun i => b (c i)))) := by
  change (cohomologyOverFieldMap k f d.hom 0).hom
    (primitiveEvaluation k f E b
      (LagrangianPluckerLinear.primitiveLinearMap k (Pi.basisFun k _ c))) = _
  rw [primitiveEvaluation_minor k f E b hσ]

/-- The canonical evaluation is obtained using the actual given
isomorphism with the native dualizing sheaf. -/
def canonicalEvaluation [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (d : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    Module.Dual k (LagrangianField.Primitive k) →ₗ[k]
      cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0 :=
  transportedEvaluation k f E b d

theorem canonicalEvaluation_minor [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (d : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (c : LagrangianPluckerLinear.MinorIndex) :
    canonicalEvaluation k f E b d
        (LagrangianPluckerLinear.primitiveLinearMap k (Pi.basisFun k _ c)) =
      cohomologyOverFieldMap k f d.hom 0
        (ExteriorEvaluation.lambda k f E 3
          (exteriorPower.ιMulti k 3 (fun i => b (c i)))) :=
  transportedEvaluation_minor k f E b hσ d c

/-- The fourteen actual global determinant sections of the image linear
system.  Linear independence or surjectivity onto all H0 is not required. -/
def determinantSections (b : Basis (Fin 6) k (H0 k f E)) :
    Fin 14 → Γ(Scheme.Modules.exteriorPower E (3 : ℤ), ⊤) :=
  fun j => (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
    (primitiveEvaluation k f E b ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j))

def canonicalSections [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    Fin 14 → Γ(Stacks.Duality.dualizingSheafOverField f, ⊤) :=
  fun j => (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
    (canonicalEvaluation k f E b c ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j))

def determinantSectionMap (b : Basis (Fin 6) k (H0 k f E)) :
    LagrangianMatrixChart.freeOn X 14 ⟶ Scheme.Modules.exteriorPower E (3 : ℤ) :=
  LagrangianPluckerQuotient.sectionMap X (Scheme.Modules.exteriorPower E (3 : ℤ))
    (determinantSections k f E b)

def canonicalSectionMap [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    LagrangianMatrixChart.freeOn X 14 ⟶ Stacks.Duality.dualizingSheafOverField f :=
  LagrangianPluckerQuotient.sectionMap X (Stacks.Duality.dualizingSheafOverField f)
    (canonicalSections k f E b c)

omit [CharZero k] in
/-- The native section/unit-Hom correspondence commutes with actual
changes of target. -/
theorem unitSection_postcomp {M N : X.Modules} (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    Scheme.Modules.unitHomEquivTop M s ≫ φ =
      Scheme.Modules.unitHomEquivTop N (φ.app ⊤ s) := by
  apply (SheafOfModules.unitHomEquiv N).injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, Scheme.Modules.unitHomEquiv_unitHomEquivTop,
    Scheme.Modules.unitHomEquiv_unitHomEquivTop]
  ext U
  rw [Scheme.Modules.sectionsMap_val, Scheme.Modules.sectionsTopEquiv_val,
    Scheme.Modules.sectionsTopEquiv_val, Scheme.Modules.Hom.app_presheaf_map]

omit [CharZero k] in
/-- The actual finite free evaluation determined by sections commutes
with every actual target morphism. -/
theorem sectionMap_postcomp {M N : X.Modules} {r : ℕ}
    (s : Fin r → Γ(M, ⊤)) (φ : M ⟶ N) :
    LagrangianPluckerQuotient.sectionMap X M s ≫ φ =
      LagrangianPluckerQuotient.sectionMap X N (fun i => φ.app ⊤ (s i)) := by
  apply (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin r))).hom_ext
  intro j
  rcases j with ⟨⟨j⟩⟩
  change SheafOfModules.ιFree (ULift.up j) ≫
    (LagrangianPluckerQuotient.sectionMap X M s ≫ φ) =
      SheafOfModules.ιFree (ULift.up j) ≫
        LagrangianPluckerQuotient.sectionMap X N (fun i => φ.app ⊤ (s i))
  rw [← Category.assoc, LagrangianPluckerQuotient.sectionMap_component,
    LagrangianPluckerQuotient.sectionMap_component]
  exact unitSection_postcomp φ (s j)

theorem canonicalSectionMap_eq [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    canonicalSectionMap k f E b c = determinantSectionMap k f E b ≫ c.hom := by
  symm
  refine (sectionMap_postcomp (determinantSections k f E b) c.hom).trans ?_
  apply congrArg (LagrangianPluckerQuotient.sectionMap X (Stacks.Duality.dualizingSheafOverField f))
  funext j
  exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f c.hom _).symm

open AlgebraicGeometry.Grassmannian

/-- The original quotient triangle is retained as data.  In particular,
the target isomorphism is not merely a dimension-based bundle choice. -/
structure EvaluationDiagram (b : Basis (Fin 6) k (H0 k f E)) where
  map : X ⟶ LagrangianGrassmannian.space k
  over_base : map ≫ LagrangianGrassmannian.projection k = f
  quotientIso : (pullbackPresentation (map ≫ LagrangianGrassmannian.inclusion k)
    (LagrangianGrassmannian.universalQuotient k)).target ≅ E
  triangle : (pullbackPresentation (map ≫ LagrangianGrassmannian.inclusion k)
      (LagrangianGrassmannian.universalQuotient k)).map ≫ quotientIso.hom =
    MukaiSemiIrreducible.evaluation k f E b

omit [CharZero k] in
/-- The native LG coefficient map is the original structural field map,
including the comparison between `appTop` and `appLE` at the top open. -/
theorem EvaluationDiagram.coefficients {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b) :
    LagrangianPlucker.coefficientMap k d.map = ExteriorEvaluation.baseRingMap k f := by
  change ((Scheme.ΓSpecIso (.of k)).inv ≫
    (d.map ≫ LagrangianGrassmannian.projection k).appTop).hom = _
  rw [d.over_base]
  have happ : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    have h : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op =
        𝟙 Γ(X, ⊤) := by
      change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) = _
      exact X.presheaf.map_id _
    rw [Scheme.Hom.appLE, h]
    exact Category.comp_id _
  change _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom
  rw [happ]

omit [CharZero k] in
theorem EvaluationDiagram.exists_restrictedIso {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b) :
    ∃ e : (pullbackPresentation d.map (lagrangianQuotient k)).target ≅ E,
      (pullbackPresentation d.map (lagrangianQuotient k)).map ≫ e.hom =
        MukaiSemiIrreducible.evaluation k f E b := by
  have hc : (⟦pullbackPresentation d.map (lagrangianQuotient k)⟧ : Points X 3 6) =
      ⟦pullbackPresentation (d.map ≫ LagrangianGrassmannian.inclusion k)
        (LagrangianGrassmannian.universalQuotient k)⟧ := by
    exact (congrFun (pullbackPointsMap_comp (LagrangianGrassmannian.inclusion k) d.map 3 6)
      (⟦LagrangianGrassmannian.universalQuotient k⟧ : Points _ 3 6)).symm
  obtain ⟨e, he⟩ := LagrangianGrassmannian.presentation_isomorphic_of_class_eq hc
  refine ⟨e ≪≫ d.quotientIso, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, he, d.triangle]

def EvaluationDiagram.restrictedIso {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b) :
    (pullbackPresentation d.map (lagrangianQuotient k)).target ≅ E :=
  Classical.choose (d.exists_restrictedIso k f E)

omit [CharZero k] in
theorem EvaluationDiagram.restrictedIso_triangle {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b) :
    (pullbackPresentation d.map (lagrangianQuotient k)).map ≫
      (d.restrictedIso k f E).hom = MukaiSemiIrreducible.evaluation k f E b :=
  Classical.choose_spec (d.exists_restrictedIso k f E)

/-- The determinant-line comparison is the actual exterior-power pullback
comparison followed by the actual third exterior power of the quotient
isomorphism. -/
def EvaluationDiagram.determinantIso {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b) :
    (Scheme.Modules.pullback d.map).obj (LagrangianPluckerQuotient.determinantLine k) ≅
      Scheme.Modules.exteriorPower E (3 : ℤ) :=
  LagrangianPullback.exteriorPullbackIso d.map (lagrangianQuotient k).target 3 ≪≫
    (Scheme.Modules.exteriorPowerFunctor X 3).mapIso (d.restrictedIso k f E)

/-- The primitive Plucker determinant coordinates, pulled back along the
actual normalized map and compared by the actual determinant-line
isomorphism, are the original factored exterior-evaluation sections. -/
theorem EvaluationDiagram.primitiveCoordinates {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b) (j : Fin 14) :
    (d.determinantIso k f E).hom.app ⊤
        (pullbackGlobalSections d.map (LagrangianPluckerQuotient.determinantLine k)
          (LagrangianPluckerQuotient.primitiveSections k j)) =
      (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (3 : ℤ))).hom
        (primitiveEvaluation k f E b
          ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j)) := by
  change (Scheme.Modules.exteriorPowerMap (d.restrictedIso k f E).hom 3).app ⊤
    ((LagrangianPullback.exteriorPullbackIso d.map (lagrangianQuotient k).target 3).hom.app ⊤
      (pullbackGlobalSections d.map (LagrangianPluckerQuotient.determinantLine k)
        (LagrangianPluckerQuotient.primitiveSections k j))) = _
  have hκ := d.coefficients k f E
  have hp : (LagrangianPullback.exteriorPullbackIso d.map (lagrangianQuotient k).target 3).hom.app ⊤
      (pullbackGlobalSections d.map (LagrangianPluckerQuotient.determinantLine k)
        (LagrangianPluckerQuotient.primitiveSections k j)) =
      LagrangianPluckerQuotient.primitiveSection X k (ExteriorEvaluation.baseRingMap k f)
        (pullbackPresentation d.map (lagrangianQuotient k)).map j := by
    refine (LagrangianPrimitiveSectionsPullback.primitiveSections_pullback k d.map j).trans ?_
    exact congrArg (fun κ => LagrangianPluckerQuotient.primitiveSection X k κ
      (pullbackPresentation d.map (lagrangianQuotient k)).map j) hκ
  have ht : LagrangianPluckerQuotient.primitiveSection X k (ExteriorEvaluation.baseRingMap k f)
      ((pullbackPresentation d.map (lagrangianQuotient k)).map ≫
        (d.restrictedIso k f E).hom) j =
      LagrangianPluckerQuotient.primitiveSection X k (ExteriorEvaluation.baseRingMap k f)
        (MukaiSemiIrreducible.evaluation k f E b) j :=
    congrArg (fun q => LagrangianPluckerQuotient.primitiveSection X k
      (ExteriorEvaluation.baseRingMap k f) q j) (d.restrictedIso_triangle k f E)
  exact (congrArg ((Scheme.Modules.exteriorPowerMap (d.restrictedIso k f E).hom 3).app ⊤) hp).trans
    ((LagrangianPluckerQuotient.primitiveSection_postcomp X k (ExteriorEvaluation.baseRingMap k f)
      (pullbackPresentation d.map (lagrangianQuotient k)).map (d.restrictedIso k f E).hom j).trans
      (ht.trans (evaluation_primitiveSection k f E b j)))

def EvaluationDiagram.canonicalIso [IsProper f] {b : Basis (Fin 6) k (H0 k f E)}
    (d : EvaluationDiagram k f E b)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    (Scheme.Modules.pullback d.map).obj (LagrangianPluckerQuotient.determinantLine k) ≅
      Stacks.Duality.dualizingSheafOverField f :=
  d.determinantIso k f E ≪≫ c

theorem EvaluationDiagram.canonicalCoordinates [IsProper f]
    {b : Basis (Fin 6) k (H0 k f E)} (d : EvaluationDiagram k f E b)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (j : Fin 14) :
    (d.canonicalIso k f E c).hom.app ⊤
        (pullbackGlobalSections d.map (LagrangianPluckerQuotient.determinantLine k)
          (LagrangianPluckerQuotient.primitiveSections k j)) =
      (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
        (canonicalEvaluation k f E b c
          ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis j)) := by
  change c.hom.app ⊤ ((d.determinantIso k f E).hom.app ⊤ _) = _
  rw [d.primitiveCoordinates k f E]
  exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f c.hom _).symm

section Diagram
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

omit [CharZero k] in
theorem nonempty_evaluationDiagram (b : Basis (Fin 6) k (H0 k f E))
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0) :
    Nonempty (EvaluationDiagram k f E b) := by
  let q := evaluationQuotient k f E b hgen
  obtain ⟨e, he⟩ := classifying_pullback_isomorphic k f q
  have hkill : LagrangianGrassmannian.AnnihilatesSigma X
      (pullbackPresentation (classifying k f q) (LagrangianGrassmannian.universalQuotient k)).map :=
    (LagrangianGrassmannian.annihilatesSigma_iff_of_iso X _ q.map e he).mpr
      ((evaluation_annihilatesSigma_iff k f E b).mpr hσ)
  obtain ⟨g, hg⟩ := (LagrangianGrassmannian.factorsThrough_iff_pullbackQuotient_annihilates
    k (classifying k f q)).mpr hkill
  have hq : (pullbackPresentation (g ≫ LagrangianGrassmannian.inclusion k)
      (LagrangianGrassmannian.universalQuotient k)).Isomorphic q := by
    rw [hg]
    exact ⟨e, he⟩
  obtain ⟨ei, hei⟩ := hq
  refine ⟨⟨g, ?_, ei, hei⟩⟩
  change (g ≫ LagrangianGrassmannian.inclusion k) ≫
    LagrangianGrassmannian.grassmannianProjection k = f
  rw [hg, classifying_projection]

def evaluationDiagram (b : Basis (Fin 6) k (H0 k f E))
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0) :
    EvaluationDiagram k f E b :=
  Classical.choice (nonempty_evaluationDiagram k f E b hgen hσ)

end Diagram

/-- A basis, its actual exterior-square relation, and the actual
classifying quotient triangle are chosen together. -/
structure NormalizedEvaluation where
  basis : Basis (Fin 6) k (H0 k f E)
  relation : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E basis) = 0
  diagram : EvaluationDiagram k f E basis

section Complete
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
  [IsIntegral X] [IsAlgClosed k] [LocallyOfFiniteType f]
  [FiniteDimensional k (H0 k f E)]
  [FiniteDimensional k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0)]

theorem nonempty_normalizedEvaluation
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    Nonempty (NormalizedEvaluation k f E) := by
  obtain ⟨b, hb⟩ := exists_kernel_basis k f E hgen h6 h14 hsemi
  exact ⟨⟨b, hb, evaluationDiagram k f E b hgen hb⟩⟩

def normalizedEvaluation
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : Module.finrank k (H0 k f E) = 6)
    (h14 : Module.finrank k (cohomologyOverField k f (Scheme.Modules.exteriorPower E 2) 0) = 14)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    NormalizedEvaluation k f E :=
  Classical.choice (nonempty_normalizedEvaluation k f E hgen h6 h14 hsemi)

end Complete


end M9Native.MukaiPrimitiveCanonicalEvaluation
