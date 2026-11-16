/-
This project module contains a modified thin replay of the sheafification-unit
proof from AxiomMath/Stacks at c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerWedgeDuality.lean.
That proof is specialized to a scheme's structure sheaf and the identity scalar
morphism; its original source, SHA256, and Apache-2.0 license are preserved in
audits/lagrangian-matrix-chart/upstream and provenance.json.
All remaining constructions and proofs in this module are project integration.
-/
module

public import M9StacksIntegration.GrassmannianCharts
public import M9StacksIntegration.LagrangianGrassmannian
public import M9StacksIntegration.SectionZeroIdealFactorization
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
public import M9StacksIntegration.ExteriorEvaluation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Tactic

/-!
# The symmetric matrix chart of the native Lagrangian Grassmannian

The first three pivot columns are the identity and the last three form
`A`. With the actual bivector convention `∑ e_k ∧ f_k`, the coefficient
on the ordered basis vector `e_i ∧ e_j` is `A_{ji} - A_{ij}`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianMatrixChart

abbrev Entry := Fin 3 × Fin 3
abbrev SymmetricEntry := {p : Entry // p.1 ≤ p.2}

@[simp] theorem card_symmetricEntry : Fintype.card SymmetricEntry = 6 := by decide

/-- The upper-triangular index of an arbitrary matrix entry. -/
def symmetricIndex (p : Entry) : SymmetricEntry :=
  if h : p.1 ≤ p.2 then ⟨p,h⟩ else ⟨(p.2,p.1),le_of_not_ge h⟩

@[simp] theorem symmetricIndex_of_le (p : SymmetricEntry) : symmetricIndex p.val = p := by
  simp [symmetricIndex,p.property]

theorem symmetricIndex_swap (i j : Fin 3) :
    symmetricIndex (i,j) = symmetricIndex (j,i) := by
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have h := le_antisymm hij hji
      subst j
      rfl
    · simp [symmetricIndex,hij,hji]
  · have hji : j ≤ i := le_of_not_ge hij
    simp [symmetricIndex,hij,hji]

variable (R : Type u) [CommRing R]

abbrev MatrixRing := MvPolynomial (ULift.{u} Entry) R
abbrev SymmetricRing := MvPolynomial (ULift.{u} SymmetricEntry) R

/-- The skew coefficient dictated by `∑ e_k ∧ f_k`. -/
def skewEntry (p : Entry) : MatrixRing R :=
  MvPolynomial.X (ULift.up (p.2,p.1)) - MvPolynomial.X (ULift.up p)

/-- The actual polynomial ideal imposing matrix symmetry. -/
def symmetryIdeal : Ideal (MatrixRing R) := Ideal.span (Set.range (skewEntry R))

/-- Its three independent ordered equations. -/
def threeEquations : Fin 3 → MatrixRing R :=
  ![skewEntry R (0,1),skewEntry R (0,2),skewEntry R (1,2)]

/-- Exactly three skew equations generate the symmetry ideal. -/
theorem symmetryIdeal_eq_three :
    symmetryIdeal R = Ideal.span (Set.range (threeEquations R)) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    fin_cases i <;> fin_cases j
    · simp [skewEntry]
    · exact Ideal.subset_span ⟨0,rfl⟩
    · exact Ideal.subset_span ⟨1,rfl⟩
    · simpa [threeEquations,skewEntry] using
        (Submodule.neg_mem (Ideal.span (Set.range (threeEquations R)))
          (Ideal.subset_span (show threeEquations R 0 ∈ Set.range (threeEquations R) from ⟨0,rfl⟩)))
    · simp [skewEntry]
    · exact Ideal.subset_span ⟨2,rfl⟩
    · simpa [threeEquations,skewEntry] using
        (Submodule.neg_mem (Ideal.span (Set.range (threeEquations R)))
          (Ideal.subset_span (show threeEquations R 1 ∈ Set.range (threeEquations R) from ⟨1,rfl⟩)))
    · simpa [threeEquations,skewEntry] using
        (Submodule.neg_mem (Ideal.span (Set.range (threeEquations R)))
          (Ideal.subset_span (show threeEquations R 2 ∈ Set.range (threeEquations R) from ⟨2,rfl⟩)))
    · simp [skewEntry]
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    all_goals exact Ideal.subset_span ⟨_,rfl⟩

/-- Send a matrix entry to the variable attached to its unordered pair. -/
def symmetrize : MatrixRing R →ₐ[R] SymmetricRing R :=
  MvPolynomial.aeval (fun p => MvPolynomial.X (ULift.up (symmetricIndex p.down)))

@[simp] theorem symmetrize_X (p : ULift.{u} Entry) :
    symmetrize R (MvPolynomial.X p) = MvPolynomial.X (ULift.up (symmetricIndex p.down)) :=
  MvPolynomial.aeval_X _ _

theorem symmetryIdeal_le_ker : symmetryIdeal R ≤ RingHom.ker (symmetrize R).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨i,j⟩,rfl⟩
  change symmetrize R (skewEntry R (i,j)) = 0
  rw [skewEntry,map_sub,symmetrize_X,symmetrize_X]
  rw [symmetricIndex_swap i j, sub_self]

/-- The homomorphism from the quotient by the literal three symmetry equations. -/
def quotientToSymmetric : MatrixRing R ⧸ symmetryIdeal R →ₐ[R] SymmetricRing R :=
  Ideal.Quotient.liftₐ (symmetryIdeal R) (symmetrize R) (fun _a ha => symmetryIdeal_le_ker R ha)

/-- The inverse sends each upper-triangular variable to its actual quotient class. -/
def symmetricToQuotient : SymmetricRing R →ₐ[R] MatrixRing R ⧸ symmetryIdeal R :=
  MvPolynomial.aeval (fun p => Ideal.Quotient.mk (symmetryIdeal R)
    (MvPolynomial.X (ULift.up p.down.val)))

@[simp] theorem quotientToSymmetric_mk (p : MatrixRing R) :
    quotientToSymmetric R (Ideal.Quotient.mk (symmetryIdeal R) p) = symmetrize R p := rfl

@[simp] theorem symmetricToQuotient_X (p : ULift.{u} SymmetricEntry) :
    symmetricToQuotient R (MvPolynomial.X p) =
      Ideal.Quotient.mk (symmetryIdeal R) (MvPolynomial.X (ULift.up p.down.val)) :=
  MvPolynomial.aeval_X _ _

/-- A lower-triangular variable has the same actual quotient class as its upper partner. -/
theorem mk_X_symmetricIndex (p : ULift.{u} Entry) :
    Ideal.Quotient.mk (symmetryIdeal R) (MvPolynomial.X (ULift.up (symmetricIndex p.down).val)) =
      Ideal.Quotient.mk (symmetryIdeal R) (MvPolynomial.X p) := by
  obtain ⟨⟨i,j⟩⟩ := p
  by_cases hij : i ≤ j
  · simp [symmetricIndex,hij]
  · simp only [symmetricIndex,dite_eq_right hij]
    apply Ideal.Quotient.eq.mpr
    exact Ideal.subset_span ⟨(i,j),rfl⟩

theorem quotientToSymmetric_comp_symmetricToQuotient :
    (quotientToSymmetric R).comp (symmetricToQuotient R) = AlgHom.id R (SymmetricRing R) := by
  apply MvPolynomial.algHom_ext
  intro p
  simp

theorem symmetricToQuotient_comp_quotientToSymmetric :
    (symmetricToQuotient R).comp (quotientToSymmetric R) =
      AlgHom.id R (MatrixRing R ⧸ symmetryIdeal R) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  change symmetricToQuotient R (symmetrize R (MvPolynomial.X p)) = _
  rw [symmetrize_X,symmetricToQuotient_X]
  exact mk_X_symmetricIndex R p

/-- The quotient by the actual symmetry equations is the six-variable polynomial ring. -/
def symmetricQuotientEquiv : (MatrixRing R ⧸ symmetryIdeal R) ≃ₐ[R] SymmetricRing R :=
  AlgEquiv.ofAlgHom (quotientToSymmetric R) (symmetricToQuotient R)
    (quotientToSymmetric_comp_symmetricToQuotient R)
    (symmetricToQuotient_comp_quotientToSymmetric R)

def symmetricEntryEquivFinSix : ULift.{u} SymmetricEntry ≃ Fin 6 :=
  Fintype.equivFinOfCardEq (by simp)

/-- The same ring isomorphism with the six independent variables numbered explicitly. -/
def quotientPolynomialSixEquiv :
    (MatrixRing R ⧸ symmetryIdeal R) ≃ₐ[R] MvPolynomial (Fin 6) R :=
  (symmetricQuotientEquiv R).trans (MvPolynomial.renameEquiv R symmetricEntryEquivFinSix)



/-! ## The genuine exterior square of the three-dimensional free module -/

abbrev OrderedPair := Set.powersetCard (Fin 3) 2

def orderedPairs : Fin 3 → Entry := ![(0,1),(0,2),(1,2)]

def pairOrderEmbedding : Fin 3 → (Fin 2 ↪o Fin 3) :=
  ![⟨⟨![0,1],by decide⟩,by decide⟩,
    ⟨⟨![0,2],by decide⟩,by decide⟩,
    ⟨⟨![1,2],by decide⟩,by decide⟩]

def pairIndex (i : Fin 3) : OrderedPair :=
  Set.powersetCard.ofFinEmbEquiv (pairOrderEmbedding i)

def pairIndexEquiv : Fin 3 ≃ OrderedPair := Equiv.ofBijective pairIndex (by
  apply (Fintype.bijective_iff_injective_and_card pairIndex).mpr
  constructor
  · intro i j hij
    have he := Set.powersetCard.ofFinEmbEquiv.injective hij
    have h0 := congrArg (fun e : Fin 2 ↪o Fin 3 => e 0) he
    have h1 := congrArg (fun e : Fin 2 ↪o Fin 3 => e 1) he
    fin_cases i <;> fin_cases j
    all_goals first | rfl | (simp_all [pairOrderEmbedding])
  · change 3 = Fintype.card OrderedPair
    rw [← Nat.card_eq_fintype_card,Set.powersetCard.card,Nat.card_fin]
    decide)

theorem pairIndex_enumeration (i : Fin 3) (j : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm (pairIndex i) j =
      if j=0 then (orderedPairs i).1 else (orderedPairs i).2 := by
  unfold pairIndex
  rw [Equiv.symm_apply_apply]
  fin_cases i <;> fin_cases j <;> rfl

/-- The actual exterior basis `(e₀∧e₁,e₀∧e₂,e₁∧e₂)` over any commutative ring. -/
def wedgeBasis : Module.Basis (Fin 3) R (⋀[R]^2 (Fin 3 → R)) :=
  ((Pi.basisFun R (Fin 3)).exteriorPower 2).reindex pairIndexEquiv.symm

/-- Its coordinates are the actual alternating two-by-two determinants. -/
theorem wedgeBasis_coord_ιMulti (i : Fin 3) (v w : Fin 3 → R) :
    (wedgeBasis R).coord i (exteriorPower.ιMulti R 2 ![v,w]) =
      v (orderedPairs i).1 * w (orderedPairs i).2 -
        v (orderedPairs i).2 * w (orderedPairs i).1 := by
  change (wedgeBasis R).repr (exteriorPower.ιMulti R 2 ![v,w]) i = _
  rw [wedgeBasis,Module.Basis.repr_reindex_apply]
  change ((Pi.basisFun R (Fin 3)).exteriorPower 2).repr
    (exteriorPower.ιMulti R 2 ![v,w]) (pairIndex i) = _
  rw [exteriorPower.basis_repr_apply,exteriorPower.ιMultiDual_apply_ιMulti]
  simp [Matrix.det_fin_two,Matrix.of_apply,Module.Basis.coord_apply,Pi.basisFun_repr,
    pairIndex_enumeration]

/-- The actual image of the standard bivector through `[I|A]`. -/
def matrixSigma (A : Matrix (Fin 3) (Fin 3) R) : ⋀[R]^2 (Fin 3 → R) :=
  ∑ i : Fin 3, exteriorPower.ιMulti R 2 ![Pi.single i 1,fun j => A j i]

/-- The three coordinates of the actual quotient bivector are precisely the three skew entries. -/
theorem wedgeBasis_coord_matrixSigma (A : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    (wedgeBasis R).coord i (matrixSigma R A) =
      A (orderedPairs i).2 (orderedPairs i).1 - A (orderedPairs i).1 (orderedPairs i).2 := by
  simp only [matrixSigma,map_sum,wedgeBasis_coord_ιMulti]
  fin_cases i <;> simp [orderedPairs,Pi.single_apply]

/-- The vanishing condition uses the actual exterior carrier and is exactly matrix symmetry. -/
theorem matrixSigma_eq_zero_iff (A : Matrix (Fin 3) (Fin 3) R) :
    matrixSigma R A = 0 ↔ A.transpose = A := by
  constructor
  · intro h
    have hc (i : Fin 3) :
        A (orderedPairs i).2 (orderedPairs i).1 = A (orderedPairs i).1 (orderedPairs i).2 := by
      have hh := wedgeBasis_coord_matrixSigma R A i
      rw [h,map_zero] at hh
      exact sub_eq_zero.mp hh.symm
    ext i j
    fin_cases i <;> fin_cases j
    all_goals first | rfl | exact hc 0 | exact hc 1 | exact hc 2 | exact (hc 0).symm | exact (hc 1).symm | exact (hc 2).symm
  · intro h
    apply (wedgeBasis R).repr.injective
    ext i
    change (wedgeBasis R).coord i (matrixSigma R A) = (wedgeBasis R).coord i 0
    rw [wedgeBasis_coord_matrixSigma,map_zero]
    have hh := congrFun (congrFun h (orderedPairs i).1) (orderedPairs i).2
    exact sub_eq_zero.mpr hh


abbrev freeOn (X : Scheme.{u}) (n : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))

/-- Specialized replay of the sheafification-unit argument in pinned
`ExteriorPowerWedgeDuality.lean`, `isIso_sheafifyUnit_of_iso` (Apache-2.0).
The exact source and license are preserved in this task's audit directory. -/
theorem sheafifyUnit_isIso_of_iso {X : Scheme.{u}}
    {P : PresheafOfModules X.ringCatSheaf.obj} {G : X.Modules}
    (e : P ≅ (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj G) :
    IsIso (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) P) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Rf := SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  have h1 : IsIso (adj.unit.app (Rf.obj G)) := by
    have h : IsIso (adj.unit.app (Rf.obj G) ≫ Rf.map (adj.counit.app G)) := by
      rw [adj.right_triangle_components G]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Rf.map (adj.counit.app G))
  have h3 := adj.unit.naturality e.inv
  rw [Functor.id_map] at h3
  have h4 : adj.unit.app P =
      e.hom ≫ adj.unit.app (Rf.obj G) ≫
        (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙ Rf).map e.inv := by
    rw [← h3,Iso.hom_inv_id_assoc]
  change IsIso (adj.unit.app P)
  rw [h4]
  infer_instance

/-- For a finite free sheaf the actual sectionwise exterior comparison is bijective. -/
theorem freeSectionComparison_bijective (X : Scheme.{u}) (n r : ℕ) :
    Function.Bijective (M9Native.ExteriorEvaluation.sectionComparison (freeOn X r) n ⊤) := by
  let F := freeOn X r
  let A := Scheme.Modules.exteriorAlgebra F
  let gen := Scheme.Modules.exteriorGenerator F
  let hA := Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F
  let c := A.extPowCmp gen hA.1 n
  have hunit : IsIso (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj)
      (PresheafOfModules.extPow n F.val)) :=
    sheafifyUnit_isIso_of_iso
      (G := SheafOfModules.free (R := X.ringCatSheaf) (Set.powersetCard (ULift.{u} (Fin r)) n))
      (Stacks.SheafOfModules.extPowFreeIso X.ringCatSheaf.property n)
  have : IsIso (PresheafOfModules.sheafifyUnit
      (CategoryTheory.Sheaf.toRingCatMap (Opens.grothendieckTopology X) (𝟙 X.sheaf.obj))
      (PresheafOfModules.extPow n F.val)) := hunit
  have hc : IsIso c := by
    dsimp only [c]
    rw [SheafOfModules.extPowCmp_eq_sheafifyUnit_comp F A gen hA.1 hA n]
    infer_instance
  have happ : IsIso (c.app (op ⊤)) :=
    Functor.map_isIso (PresheafOfModules.evaluation _ (op ⊤)) c
  change Function.Bijective (c.app (op ⊤))
  exact ConcreteCategory.bijective_of_isIso (c.app (op ⊤))

/-- Coordinates of actual finite free sheaf sections, with the standard `Fin` index. -/
def freeSectionCoordinates (X : Scheme.{u}) (r : ℕ) :
    Γ(freeOn X r, ⊤) ≃ₗ[Γ(X, ⊤)] (Fin r → Γ(X, ⊤)) := by
  let f : Γ(freeOn X r, ⊤) →ₗ[Γ(X, ⊤)] (Fin r → Γ(X, ⊤)) :=
    { toFun s i := Stacks.SheafOfModules.freeCoord (S := X.ringCatSheaf) (op ⊤) s (ULift.up i)
      map_add' s t := by
        funext i
        exact map_add _ s t
      map_smul' c s := by
        funext i
        exact ((Stacks.SheafOfModules.freeProj (S := X.ringCatSheaf)
          (ULift.up i)).val.app (op ⊤)).hom.map_smul c s }
  apply LinearEquiv.ofBijective f
  constructor
  · intro s t h
    apply (Stacks.SheafOfModules.freeCoord_bijective (S := X.ringCatSheaf)
      (ι := ULift.{u} (Fin r)) (op ⊤)).injective
    funext i
    obtain ⟨i⟩ := i
    exact congrFun h i
  · intro v
    refine ⟨Stacks.SheafOfModules.freeMk (S := X.ringCatSheaf) (op ⊤) (fun i => v i.down),?_⟩
    funext i
    exact congrFun (Stacks.SheafOfModules.freeCoord_freeMk (S := X.ringCatSheaf) (op ⊤)
      (fun j : ULift.{u} (Fin r) => v j.down)) (ULift.up i)

@[simp] theorem freeSectionCoordinates_apply (X : Scheme.{u}) (r : ℕ)
    (s : Γ(freeOn X r, ⊤)) (i : Fin r) :
    freeSectionCoordinates X r s i =
      (Stacks.SheafOfModules.freeProj (S := X.ringCatSheaf) (ULift.up i)).val.app (op ⊤) s := rfl

/-- The two native canonical constructions of a free coordinate projection agree. -/
theorem freeProj_eq_freeProjection (X : Scheme.{u}) (r : ℕ) (i : Fin r) :
    Stacks.SheafOfModules.freeProj (S := X.ringCatSheaf) (ULift.up.{u} i) =
      SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up.{u} i) := by
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (ULift.{u} (Fin r))) _ _ fun j => ?_
  change SheafOfModules.ιFree j ≫ Stacks.SheafOfModules.freeProj (ULift.up i) =
    SheafOfModules.ιFree j ≫ SheafOfModules.freeProjection (ULift.up i)
  rw [Stacks.SheafOfModules.ιFree_comp_freeProj,SheafOfModules.ιFree_comp_freeProjection]

/-- The exterior power of an actual module isomorphism. -/
def exteriorLinearEquiv {A B : Type u} {T : Type u} [CommRing T]
    [AddCommGroup A] [Module T A] [AddCommGroup B] [Module T B]
    (e : A ≃ₗ[T] B) (n : ℕ) : (⋀[T]^n A) ≃ₗ[T] (⋀[T]^n B) :=
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
    ⟨exteriorPower.map_injective (n := n) e.symm.toLinearMap (LinearMap.ext fun x => e.symm_apply_apply x),
      exteriorPower.map_surjective (n := n) e.surjective⟩

/-- The canonical sectionwise comparison, as the actual proved linear equivalence. -/
def freeSectionComparisonEquiv (X : Scheme.{u}) (n r : ℕ) :
    (⋀[Γ(X, ⊤)]^n Γ(freeOn X r, ⊤)) ≃ₗ[Γ(X, ⊤)]
      Γ(Scheme.Modules.exteriorPower (freeOn X r) (n : ℤ), ⊤) :=
  LinearEquiv.ofBijective (M9Native.ExteriorEvaluation.sectionComparison (freeOn X r) n ⊤)
    (freeSectionComparison_bijective X n r)

/-- The actual exterior sheaf sections identified with the exterior power of the actual
coordinate free module, through the canonical native comparison. -/
def freeExteriorSectionsEquiv (X : Scheme.{u}) (n r : ℕ) :
    (⋀[Γ(X, ⊤)]^n (Fin r → Γ(X, ⊤))) ≃ₗ[Γ(X, ⊤)]
      Γ(Scheme.Modules.exteriorPower (freeOn X r) (n : ℤ), ⊤) :=
  (exteriorLinearEquiv (freeSectionCoordinates X r).symm n).trans
    (freeSectionComparisonEquiv X n r)

theorem freeExteriorSectionsEquiv_ιMulti (X : Scheme.{u}) (n r : ℕ)
    (v : Fin n → Fin r → Γ(X, ⊤)) :
    freeExteriorSectionsEquiv X n r (exteriorPower.ιMulti Γ(X, ⊤) n v) =
      M9Native.ExteriorEvaluation.sectionComparison (freeOn X r) n ⊤
        (exteriorPower.ιMulti Γ(X, ⊤) n (fun i => (freeSectionCoordinates X r).symm (v i))) := by
  change M9Native.ExteriorEvaluation.sectionComparison (freeOn X r) n ⊤
    (exteriorPower.map n (freeSectionCoordinates X r).symm.toLinearMap
      (exteriorPower.ιMulti Γ(X, ⊤) n v)) = _
  rw [exteriorPower.map_apply_ιMulti]
  rfl

/-- An actual quotient map sends a standard basis section to the column of its native matrix. -/
theorem freeCoordinates_map_basis {X : Scheme.{u}} {r n : ℕ}
    (q : freeOn X n ⟶ freeOn X r) (i : Fin r) (j : Fin n) :
    freeSectionCoordinates X r
      (q.app ⊤ ((SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up j)).val.app (op ⊤)
        (1 : Γ(X, ⊤)))) i = Stacks.FreeSheafMatrix.toMatrix q i j := by
  rw [freeSectionCoordinates_apply,freeProj_eq_freeProjection]
  rfl

/-- The literal standard basis section of an actual finite free sheaf. -/
def freeBasisSection (X : Scheme.{u}) (r : ℕ) (i : Fin r) : Γ(freeOn X r, ⊤) :=
  (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i)).val.app (op ⊤) (1 : Γ(X, ⊤))

/-- The actual global exterior section of a normalized quotient, as the native
wedges of the images of the actual standard basis sections. -/
def quotientSigmaSheaf (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3) :
    Γ(Scheme.Modules.exteriorPower (freeOn X 3) 2, ⊤) :=
  ∑ i : Fin 3, M9Native.ExteriorEvaluation.sectionComparison (freeOn X 3) 2 ⊤
    (exteriorPower.ιMulti Γ(X, ⊤) 2
      ![q.app ⊤ (freeBasisSection X 6 (i.castAdd 3)),
        q.app ⊤ (freeBasisSection X 6 (Fin.natAdd 3 i))])

/-- The actual normalized quotient exterior section corresponds to its genuine module bivector. -/
theorem quotientSigmaSheaf_eq (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3)
    (A : Matrix (Fin 3) (Fin 3) Γ(X, ⊤))
    (hfirst : ∀ i j : Fin 3, Stacks.FreeSheafMatrix.toMatrix q i (j.castAdd 3) = if i=j then 1 else 0)
    (hlast : ∀ i j : Fin 3, Stacks.FreeSheafMatrix.toMatrix q i (Fin.natAdd 3 j) = A i j) :
    quotientSigmaSheaf X q = freeExteriorSectionsEquiv X 2 3 (matrixSigma Γ(X, ⊤) A) := by
  unfold quotientSigmaSheaf matrixSigma
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [freeExteriorSectionsEquiv_ιMulti]
  apply congrArg (M9Native.ExteriorEvaluation.sectionComparison (freeOn X 3) 2 ⊤)
  apply congrArg (exteriorPower.ιMulti Γ(X, ⊤) 2)
  funext j
  fin_cases j
  · apply (freeSectionCoordinates X 3).injective
    ext k
    rw [LinearEquiv.apply_symm_apply]
    change freeSectionCoordinates X 3
      (q.app ⊤ ((SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up (i.castAdd 3))).val.app (op ⊤)
        (1 : Γ(X, ⊤)))) k = (Pi.single i (1 : Γ(X, ⊤)) : Fin 3 → Γ(X, ⊤)) k
    rw [freeCoordinates_map_basis,hfirst]
    simp [Pi.single_apply,eq_comm]
  · apply (freeSectionCoordinates X 3).injective
    ext k
    rw [LinearEquiv.apply_symm_apply]
    exact (freeCoordinates_map_basis q k (Fin.natAdd 3 i)).trans (hlast k i)

/-- The three actual exterior sheaf sections form a basis of the actual global sections. -/
def nativeWedgeBasis (X : Scheme.{u}) : Module.Basis (Fin 3) Γ(X, ⊤)
    Γ(Scheme.Modules.exteriorPower (freeOn X 3) 2, ⊤) :=
  (wedgeBasis Γ(X, ⊤)).map (freeExteriorSectionsEquiv X 2 3)

/-- The actual sheaf-section coordinates are the three actual skew entries of the normalized matrix. -/
theorem nativeWedgeBasis_coord_quotientSigma (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3)
    (A : Matrix (Fin 3) (Fin 3) Γ(X, ⊤))
    (hfirst : ∀ i j : Fin 3, Stacks.FreeSheafMatrix.toMatrix q i (j.castAdd 3) = if i=j then 1 else 0)
    (hlast : ∀ i j : Fin 3, Stacks.FreeSheafMatrix.toMatrix q i (Fin.natAdd 3 j) = A i j)
    (i : Fin 3) :
    (nativeWedgeBasis X).coord i (quotientSigmaSheaf X q) =
      A (orderedPairs i).2 (orderedPairs i).1 - A (orderedPairs i).1 (orderedPairs i).2 := by
  rw [quotientSigmaSheaf_eq X q A hfirst hlast]
  change (wedgeBasis Γ(X, ⊤)).repr
    ((freeExteriorSectionsEquiv X 2 3).symm
      (freeExteriorSectionsEquiv X 2 3 (matrixSigma Γ(X, ⊤) A))) i = _
  rw [LinearEquiv.symm_apply_apply]
  exact wedgeBasis_coord_matrixSigma Γ(X, ⊤) A i

/-- The actual dual-evaluation ideal on an affine normalized matrix chart is
exactly the ideal of the three skew entries. -/
theorem quotientSigmaSheaf_zeroIdeal_top (X : Scheme.{u}) [IsAffine X]
    (q : freeOn X 6 ⟶ freeOn X 3) (A : Matrix (Fin 3) (Fin 3) Γ(X, ⊤))
    (hfirst : ∀ i j : Fin 3, Stacks.FreeSheafMatrix.toMatrix q i (j.castAdd 3) = if i=j then 1 else 0)
    (hlast : ∀ i j : Fin 3, Stacks.FreeSheafMatrix.toMatrix q i (Fin.natAdd 3 j) = A i j) :
    (M9Native.SectionZeroIdealFactorization.sectionZeroIdeal X
      (Scheme.Modules.exteriorPower (freeOn X 3) 2) (quotientSigmaSheaf X q)).ideal
        ⟨⊤,isAffineOpen_top X⟩ =
      Ideal.span (Set.range (fun i : Fin 3 =>
        A (orderedPairs i).2 (orderedPairs i).1 - A (orderedPairs i).1 (orderedPairs i).2)) := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (freeOn X 3) 3 :=
    AlgebraicGeometry.Grassmannian.free_isFiniteLocallyFreeOfRank X 3
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower (freeOn X 3) 2) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (freeOn X 3) 3 2
  have : SheafOfModules.IsFiniteLocallyFree.{u,u,u}
      (Scheme.Modules.exteriorPower (freeOn X 3) 2) :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 3
  rw [M9Native.SectionZeroIdealFactorization.sectionZeroIdeal_ideal]
  have hres : (Scheme.Modules.exteriorPower (freeOn X 3) 2).presheaf.map
      (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op (quotientSigmaSheaf X q) =
      quotientSigmaSheaf X q := by
    rw [show (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op = 𝟙 _ from rfl,CategoryTheory.Functor.map_id]
    rfl
  rw [hres]
  rw [M9Native.SectionZeroIdealFactorization.span_eval_eq_span_coord
    (nativeWedgeBasis X).coord (nativeWedgeBasis X)
    (fun m => (nativeWedgeBasis X).sum_repr m |>.symm)]
  congr 1
  apply congrArg Set.range
  funext i
  exact nativeWedgeBasis_coord_quotientSigma X q A hfirst hlast i

/-- An actual target isomorphism detects the vanishing of the actually pulled-back section. -/
theorem pullbackSection_eq_zero_iff_of_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    {E F : X.Modules} (e : E ≅ F) (s : Γ(E, ⊤)) :
    pullbackGlobalSections f E s = 0 ↔ pullbackGlobalSections f F (e.hom.app ⊤ s) = 0 := by
  rw [← M9Native.SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections f e.hom s]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullback f).map e.hom).app ⊤)).injective).symm

/-- The actual zero ideal is invariant under actual bundle isomorphisms, proved from the
already checked factorization theorem and actual closed-immersion kernels. -/
theorem sectionZeroIdeal_eq_of_iso {X : Scheme.{u}} {E F : X.Modules}
    (r : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} F r]
    (e : E ≅ F) (s : Γ(E, ⊤)) :
    M9Native.SectionZeroIdealFactorization.sectionZeroIdeal X E s =
      M9Native.SectionZeroIdealFactorization.sectionZeroIdeal X F (e.hom.app ⊤ s) := by
  let I := M9Native.SectionZeroIdealFactorization.sectionZeroIdeal X E s
  let J := M9Native.SectionZeroIdealFactorization.sectionZeroIdeal X F (e.hom.app ⊤ s)
  apply le_antisymm
  · have hs := (pullbackSection_eq_zero_iff_of_iso J.subschemeι e s).mpr
      (M9Native.SectionZeroIdealFactorization.pullbackGlobalSections_subschemeι_eq_zero F r (e.hom.app ⊤ s))
    have h := (AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker I J.subschemeι).mp
      ((M9Native.SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough E r s J.subschemeι).mp hs)
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using h
  · have hs := (pullbackSection_eq_zero_iff_of_iso I.subschemeι e s).mp
      (M9Native.SectionZeroIdealFactorization.pullbackGlobalSections_subschemeι_eq_zero E r s)
    have h := (AlgebraicGeometry.factorsThrough_ideal_iff_ideal_le_ker J I.subschemeι).mp
      ((M9Native.SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
        F r (e.hom.app ⊤ s) I.subschemeι).mp hs)
    simpa only [Scheme.IdealSheafData.ker_subschemeι] using h


/-! ## The actual native matrix chart -/

/-- The native Grassmannian chart whose first three columns are the pivots. -/
def firstPivot : Fin (6-3) ↪ Fin 6 where
  toFun i := i.castAdd 3
  inj' := by intro i j h; exact Fin.ext (congrArg (fun k : Fin 6 => k.val) h)

@[simp] theorem firstPivot_apply (i : Fin 3) : firstPivot i = i.castAdd 3 := rfl

theorem mem_range_firstPivot_iff (i : Fin 6) : i ∈ Set.range firstPivot ↔ i.val < 3 := by
  constructor
  · rintro ⟨j,rfl⟩
    exact j.isLt
  · intro hi
    exact ⟨⟨i.val,hi⟩,Fin.ext rfl⟩

/-- The three nonpivot columns are literally the final three columns. -/
def nonPivotEquiv : {j : Fin 6 // j ∉ Set.range firstPivot} ≃ Fin 3 where
  toFun j := ⟨j.val.val - 3, by
    have hj := j.val.isLt
    have hn := (mem_range_firstPivot_iff j.val).not.mp j.property
    omega⟩
  invFun j := ⟨Fin.natAdd 3 j, by
    rw [mem_range_firstPivot_iff]
    simp only [Fin.val_natAdd]
    omega⟩
  left_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have hn := (mem_range_firstPivot_iff j.val).not.mp j.property
    dsimp
    omega
  right_inv j := by
    apply Fin.ext
    simp

/-- Relabel native chart coordinates by `(row,column)` in the final matrix block. -/
def chartEntryEquiv : AlgebraicGeometry.Grassmannian.ChartIndex.{u} firstPivot ≃ ULift.{u} Entry where
  toFun a := ⟨(a.down.2,nonPivotEquiv a.down.1)⟩
  invFun p := ⟨(nonPivotEquiv.symm p.down.2,p.down.1)⟩
  left_inv a := by cases a; simp
  right_inv p := by cases p; simp

section NativeChart

variable (K : Type u) [Field K]

abbrev matrixAffineSpace : Scheme.{u} := AffineSpace (ULift.{u} Entry) (Spec (.of K))

/-- The coordinate relabelling is an actual isomorphism of affine spaces over the field. -/
def chartCoordinatesIso : matrixAffineSpace K ≅
    M9Native.GrassmannianCharts.chartSpace K 3 6 firstPivot where
  hom := AffineSpace.reindex chartEntryEquiv (Spec (.of K))
  inv := AffineSpace.reindex chartEntryEquiv.symm (Spec (.of K))
  hom_inv_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      simp
  inv_hom_id := by
    apply AffineSpace.hom_ext
    · simp
    · intro i
      simp

/-- The actual native `Gr(3,6)` matrix chart with quotient `[I|A]`. -/
def matrixChart : Spec (.of (MatrixRing K)) ⟶ M9Native.GrassmannianCharts.space K 3 6 :=
  (AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).inv ≫
    (chartCoordinatesIso K).hom ≫ M9Native.GrassmannianCharts.chartOver K 3 6 firstPivot

instance matrixChart_isOpenImmersion : IsOpenImmersion (matrixChart K) := by
  dsimp [matrixChart]
  infer_instance

@[reassoc (attr := simp)] theorem matrixChart_projection :
    matrixChart K ≫ M9Native.GrassmannianCharts.projection K 3 6 =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} Entry) (R := K))) := by
  simp only [matrixChart,Category.assoc,M9Native.GrassmannianCharts.chartOver_projection]
  change (AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).inv ≫
    AffineSpace.reindex chartEntryEquiv (Spec (.of K)) ≫
      (AffineSpace (AlgebraicGeometry.Grassmannian.ChartIndex.{u} firstPivot) (Spec (.of K)) ↘ Spec (.of K)) = _
  rw [AffineSpace.reindex_over,AffineSpace.SpecIso_inv_over]

/-- The actual map of this chart to the integral native chart. -/
def integralChartPoint : Spec (.of (MatrixRing K)) ⟶
    Spec (.of (MvPolynomial (AlgebraicGeometry.Grassmannian.ChartIndex.{u} firstPivot) (ULift.{u} ℤ))) :=
  (AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).inv ≫
    (chartCoordinatesIso K).hom ≫
      AffineSpace.toSpecMvPoly _ (Spec (.of K))

/-- Pulling the native chart coordinate back gives the actual polynomial matrix entry. -/
theorem integralChartPoint_coord (a : AlgebraicGeometry.Grassmannian.ChartIndex.{u} firstPivot) :
    AffineSpace.toSpecMvPolyIntEquiv _ (integralChartPoint K) a =
      (Scheme.ΓSpecIso (.of (MatrixRing K))).inv (MvPolynomial.X (chartEntryEquiv a)) := by
  change ((AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).inv ≫
    (chartCoordinatesIso K).hom).appTop (AffineSpace.coord (Spec (.of K)) a) = _
  change (AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).inv.appTop
    ((chartCoordinatesIso K).hom.appTop (AffineSpace.coord (Spec (.of K)) a)) = _
  change (AffineSpace.SpecIso (ULift.{u} Entry) (.of K)).inv.appTop
    ((AffineSpace.reindex chartEntryEquiv (Spec (.of K))).appTop
      (AffineSpace.coord (Spec (.of K)) a)) = _
  rw [AffineSpace.reindex_appTop_coord]
  exact AffineSpace.SpecIso_inv_appTop_coord (.of K) (chartEntryEquiv a)


/-- The actual native chart diagram commutes with projection to the integral Grassmannian. -/
@[reassoc] theorem matrixChart_toIntegral :
    matrixChart K ≫ M9Native.GrassmannianCharts.toIntegral K 3 6 =
      integralChartPoint K ≫ AlgebraicGeometry.Grassmannian.chart 3 6 firstPivot := by
  simp only [matrixChart,Category.assoc,M9Native.GrassmannianCharts.chartOver_toIntegral,
    integralChartPoint]
  rfl

/-- The actual polynomial entry as a global function on the actual affine matrix chart. -/
def matrixEntry (p : Entry) : Γ(Spec (.of (MatrixRing K)), ⊤) :=
  (Scheme.ΓSpecIso (.of (MatrixRing K))).inv (MvPolynomial.X (ULift.up p))

/-- The actual normalized quotient map on the native matrix chart. -/
def matrixQuotientMap :
    SheafOfModules.free (R := (Spec (.of (MatrixRing K))).ringCatSheaf) (ULift.{u} (Fin 6)) ⟶
      SheafOfModules.free (R := (Spec (.of (MatrixRing K))).ringCatSheaf) (ULift.{u} (Fin 3)) :=
  AlgebraicGeometry.Grassmannian.chartQuotientMap 3 6 firstPivot (integralChartPoint K)

/-- The first three columns of the actual normalized quotient are the identity. -/
theorem matrixQuotient_first (i j : Fin 3) :
    Stacks.FreeSheafMatrix.toMatrix (matrixQuotientMap K) i (j.castAdd 3) =
      if i=j then 1 else 0 := by
  change Stacks.FreeSheafMatrix.toMatrix
    (AlgebraicGeometry.Grassmannian.chartQuotientMap 3 6 firstPivot (integralChartPoint K)) i (firstPivot j) = _
  rw [AlgebraicGeometry.Grassmannian.toMatrix_chartQuotientMap,
    AlgebraicGeometry.Grassmannian.chartMatrix_apply_self]

/-- The last three columns of the actual quotient are exactly the nine matrix variables. -/
theorem matrixQuotient_last (i j : Fin 3) :
    Stacks.FreeSheafMatrix.toMatrix (matrixQuotientMap K) i (Fin.natAdd 3 j) =
      matrixEntry K (i,j) := by
  have hj : Fin.natAdd 3 j ∉ Set.range firstPivot := by
    rw [mem_range_firstPivot_iff]
    simp only [Fin.val_natAdd]
    omega
  change Stacks.FreeSheafMatrix.toMatrix
    (AlgebraicGeometry.Grassmannian.chartQuotientMap 3 6 firstPivot (integralChartPoint K)) i (Fin.natAdd 3 j) = _
  rw [AlgebraicGeometry.Grassmannian.toMatrix_chartQuotientMap,
    AlgebraicGeometry.Grassmannian.chartMatrix_apply_of_notMem firstPivot _ i hj,
    integralChartPoint_coord]
  apply congrArg (fun p => (Scheme.ΓSpecIso (.of (MatrixRing K))).inv (MvPolynomial.X p))
  apply ULift.ext
  change (i,nonPivotEquiv ⟨Fin.natAdd 3 j,hj⟩) = (i,j)
  congr 1
  apply Fin.ext
  simp [nonPivotEquiv]

/-- The affine scheme cut out by the literal three polynomial equations. -/
abbrev symmetryScheme : Scheme.{u} := Spec (.of (MatrixRing K ⧸ symmetryIdeal K))

/-- Its actual closed immersion into the nine-dimensional matrix chart. -/
def symmetryInclusion : symmetryScheme K ⟶ Spec (.of (MatrixRing K)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (symmetryIdeal K)))

instance symmetryInclusion_isClosedImmersion : IsClosedImmersion (symmetryInclusion K) := by
  exact IsClosedImmersion.spec_of_quotient_mk (R := .of (MatrixRing K)) (symmetryIdeal K)

/-- An explicit actual scheme isomorphism to affine six-space. -/
def symmetrySchemeIsoPolynomialSix :
    symmetryScheme K ≅ Spec (.of (MvPolynomial (Fin 6) K)) :=
  (Scheme.Spec.mapIso (quotientPolynomialSixEquiv K).toRingEquiv.toCommRingCatIso.op).symm


/-- The actual section-zero ideal of the actual normalized native quotient on affine nine-space. -/
def matrixZeroIdeal : (Spec (.of (MatrixRing K))).IdealSheafData :=
  M9Native.SectionZeroIdealFactorization.sectionZeroIdeal _
    (Scheme.Modules.exteriorPower (freeOn (Spec (.of (MatrixRing K))) 3) 2)
    (quotientSigmaSheaf _ (matrixQuotientMap K))

/-- On the actual matrix chart, the actual dual-evaluation ideal consists of the literal
three skew equations, read in the actual global section ring. -/
theorem matrixZeroIdeal_ideal_top :
    (matrixZeroIdeal K).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.map (Scheme.ΓSpecIso (.of (MatrixRing K))).inv.hom (symmetryIdeal K) := by
  rw [matrixZeroIdeal,quotientSigmaSheaf_zeroIdeal_top _ _
    (fun i j => matrixEntry K (i,j)) (matrixQuotient_first K) (matrixQuotient_last K)]
  rw [symmetryIdeal_eq_three,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  fin_cases i <;> simp [orderedPairs,threeEquations,skewEntry,matrixEntry,map_sub]

/-- The global kernel of the actual affine quotient immersion is the symmetry ideal
transported by the canonical `ΓSpec` isomorphism. -/
theorem symmetryInclusion_ker_appTop :
    RingHom.ker (symmetryInclusion K).appTop.hom =
      Ideal.map (Scheme.ΓSpecIso (.of (MatrixRing K))).inv.hom (symmetryIdeal K) := by
  let e : MatrixRing K ≃+* Γ(Spec (.of (MatrixRing K)), ⊤) :=
    (Scheme.ΓSpecIso (.of (MatrixRing K))).symm.commRingCatIsoToRingEquiv
  ext a
  obtain ⟨p,rfl⟩ := e.surjective a
  change (symmetryInclusion K).appTop (e p) = 0 ↔ e p ∈ Ideal.map e.toRingHom (symmetryIdeal K)
  have hm : e p ∈ Ideal.map e.toRingHom (symmetryIdeal K) ↔ p ∈ symmetryIdeal K :=
    Ideal.apply_mem_of_equiv_iff (f := e)
  rw [hm]
  have hn := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (Ideal.Quotient.mk (symmetryIdeal K)))) p
  change (Scheme.ΓSpecIso (.of (MatrixRing K ⧸ symmetryIdeal K))).inv
      (Ideal.Quotient.mk (symmetryIdeal K) p) = (symmetryInclusion K).appTop (e p) at hn
  rw [← hn]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (.of (MatrixRing K ⧸ symmetryIdeal K))).inv).injective).trans
      Ideal.Quotient.eq_zero_iff_mem

/-- Equality of actual quasi-coherent ideal sheaves, rather than equality only at field points. -/
theorem matrixZeroIdeal_eq_symmetryKer : matrixZeroIdeal K = (symmetryInclusion K).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [matrixZeroIdeal_ideal_top]
  simpa [Scheme.ker_of_isAffine,Scheme.IdealSheafData.ofIdealTop_ideal] using
    (symmetryInclusion_ker_appTop K).symm

/-- The actual native section-zero scheme on the actual matrix chart is affine six-space. -/
def matrixZeroSchemeIsoPolynomialSix :
    (matrixZeroIdeal K).subscheme ≅ Spec (.of (MvPolynomial (Fin 6) K)) :=
  eqToIso (congrArg (fun I : (Spec (.of (MatrixRing K))).IdealSheafData => I.subscheme)
      (matrixZeroIdeal_eq_symmetryKer K)) ≪≫
    (asIso (symmetryInclusion K).toImage).symm ≪≫ symmetrySchemeIsoPolynomialSix K

/-- The polynomial-quotient isomorphism commutes with the actual structural map to the field. -/
@[reassoc] theorem symmetrySchemeIsoPolynomialSix_over :
    (symmetrySchemeIsoPolynomialSix K).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 6) (R := K))) =
    symmetryInclusion K ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} Entry) (R := K))) := by
  change Spec.map (CommRingCat.ofHom (quotientPolynomialSixEquiv K).symm.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 6) (R := K))) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (symmetryIdeal K))) ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} Entry) (R := K)))
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  ext c
  exact (quotientPolynomialSixEquiv K).symm.commutes c


end NativeChart

open M9Native.LagrangianGrassmannian

/-- Equality with the actual bivector image in the actual native exterior sheaf. -/
theorem quotientSigmaSheaf_eq_native (X : Scheme.{u}) (q : freeOn X 6 ⟶ freeOn X 3) :
    quotientSigmaSheaf X q = (exteriorPowerMap X q 2).app ⊤ (sigmaSection X) := by
  unfold quotientSigmaSheaf sigmaSection
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [exteriorPowerMap_wedgeSection,M9Native.ExteriorEvaluation.sectionComparison_ιMulti]
  apply congrArg ((Scheme.Modules.exteriorAlgebra (freeOn X 3)).toPresheafGradedAlgebra.homogeneousProd (op ⊤) 2)
  funext j
  fin_cases j <;> rfl

/-- Equality of actual ideal sheaves gives the compatible equality isomorphism of subschemes. -/
@[reassoc] theorem eqToIso_subscheme_ι {X : Scheme.{u}} (I J : X.IdealSheafData) (h : I=J) :
    (eqToIso (congrArg (fun A : X.IdealSheafData => A.subscheme) h)).hom ≫ J.subschemeι =
      I.subschemeι := by
  subst J
  simp

/-- The inverse image isomorphism of an actual closed immersion preserves its inclusion. -/
@[reassoc] theorem asIso_toImage_inv_imageι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f.toImage] :
    (asIso f.toImage).inv ≫ f = f.imageι := by
  calc
    _ = (asIso f.toImage).inv ≫ (f.toImage ≫ f.imageι) :=
      congrArg (fun g => (asIso f.toImage).inv ≫ g) f.toImage_imageι.symm
    _ = _ := Iso.inv_hom_id_assoc (asIso f.toImage) _

variable (K : Type u) [Field K]

/-- The actual target isomorphism between the pulled-back chosen universal quotient and `[I|A]`. -/
def matrixQuotientIso :
    (AlgebraicGeometry.Grassmannian.pullbackPresentation (matrixChart K) (universalQuotient K)).target ≅
      freeOn (Spec (.of (MatrixRing K))) 3 :=
  Classical.choose (pullbackUniversal_chart_isomorphic K (matrixChart K) firstPivot
    (integralChartPoint K) (matrixChart_toIntegral K))

theorem matrixQuotientIso_fac :
    (AlgebraicGeometry.Grassmannian.pullbackPresentation (matrixChart K) (universalQuotient K)).map ≫
        (matrixQuotientIso K).hom = matrixQuotientMap K :=
  Classical.choose_spec (pullbackUniversal_chart_isomorphic K (matrixChart K) firstPivot
    (integralChartPoint K) (matrixChart_toIntegral K))

/-- The canonical exterior pullback comparison followed by the actual quotient trivialization. -/
def matrixEquationIso :
    (Scheme.Modules.pullback (matrixChart K)).obj (equationBundle K) ≅
      Scheme.Modules.exteriorPower (freeOn (Spec (.of (MatrixRing K))) 3) 2 :=
  M9Native.LagrangianPullback.exteriorPullbackIso (matrixChart K) (quotientBundle K) 2 ≪≫
    (Scheme.Modules.exteriorPowerFunctor (Spec (.of (MatrixRing K))) 2).mapIso (matrixQuotientIso K)

/-- The actual pulled-back LG equation is the actual normalized quotient bivector section. -/
theorem matrixEquationIso_section :
    (matrixEquationIso K).hom.app ⊤
      (pullbackGlobalSections (matrixChart K) (equationBundle K) (equationSection K)) =
        quotientSigmaSheaf _ (matrixQuotientMap K) := by
  change (Scheme.Modules.exteriorPowerMap (matrixQuotientIso K).hom 2).app ⊤
    ((M9Native.LagrangianPullback.exteriorPullbackIso (matrixChart K) (quotientBundle K) 2).hom.app ⊤
      (pullbackGlobalSections (matrixChart K) (equationBundle K) (equationSection K))) = _
  rw [pullback_equation_eq_quotientSigma]
  change (Scheme.Modules.exteriorPowerMap
      (AlgebraicGeometry.Grassmannian.pullbackPresentation (matrixChart K) (universalQuotient K)).map 2 ≫
      Scheme.Modules.exteriorPowerMap (matrixQuotientIso K).hom 2).app ⊤
        (sigmaSection _) = _
  rw [← Scheme.Modules.exteriorPowerMap_comp,matrixQuotientIso_fac]
  exact (quotientSigmaSheaf_eq_native _ (matrixQuotientMap K)).symm

/-- The scheme-theoretic pullback of the actual LG ideal is the actual symmetric-matrix ideal. -/
theorem lagrangianIdeal_comap_matrixChart :
    (M9Native.LagrangianGrassmannian.ideal K).comap (matrixChart K) = matrixZeroIdeal K := by
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      ((Scheme.Modules.pullback (matrixChart K)).obj (equationBundle K)) 3 :=
    AlgebraicGeometry.Grassmannian.isFiniteLocallyFreeOfRank_pullback
      (matrixChart K).base (matrixChart K).toRingCatSheafHom (equationBundle K) 3 inferInstance
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (freeOn (Spec (.of (MatrixRing K))) 3) 3 :=
    AlgebraicGeometry.Grassmannian.free_isFiniteLocallyFreeOfRank _ 3
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower (freeOn (Spec (.of (MatrixRing K))) 3) 2) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
      (freeOn (Spec (.of (MatrixRing K))) 3) 3 2
  rw [← ideal_baseChange K (matrixChart K)]
  have h := sectionZeroIdeal_eq_of_iso 3 (matrixEquationIso K)
    (pullbackGlobalSections (matrixChart K) (equationBundle K) (equationSection K))
  rw [matrixEquationIso_section] at h
  exact h

/-- The actual quasi-coherent ideal of the LG big cell is generated by the literal three skew equations. -/
theorem lagrangianIdeal_comap_eq_symmetryKer :
    (M9Native.LagrangianGrassmannian.ideal K).comap (matrixChart K) = (symmetryInclusion K).ker :=
  (lagrangianIdeal_comap_matrixChart K).trans (matrixZeroIdeal_eq_symmetryKer K)

/-- The actual scheme-theoretic intersection of LG with the native `[I|A]` Grassmannian chart. -/
abbrev lagrangianChart : Scheme.{u} := pullback (matrixChart K) (inclusion K)

def lagrangianChartMap : lagrangianChart K ⟶ space K := pullback.snd _ _

instance lagrangianChartMap_isOpenImmersion : IsOpenImmersion (lagrangianChartMap K) := by
  dsimp [lagrangianChartMap]
  infer_instance

/-- The actual open chart in the constructed LG is affine six-space. -/
def lagrangianChartIsoPolynomialSix :
    lagrangianChart K ≅ Spec (.of (MvPolynomial (Fin 6) K)) :=
  ((M9Native.LagrangianGrassmannian.ideal K).comapIso (matrixChart K)).symm ≪≫
    eqToIso (congrArg (fun I : (Spec (.of (MatrixRing K))).IdealSheafData => I.subscheme)
      (lagrangianIdeal_comap_matrixChart K)) ≪≫ matrixZeroSchemeIsoPolynomialSix K

/-- The actual affine-six big cell as an open immersion into the constructed LG. -/
def bigCell : Spec (.of (MvPolynomial (Fin 6) K)) ⟶ space K :=
  (lagrangianChartIsoPolynomialSix K).inv ≫ lagrangianChartMap K

instance bigCell_isOpenImmersion : IsOpenImmersion (bigCell K) := by
  dsimp [bigCell]
  infer_instance

/-- The native section-zero scheme's actual affine-six isomorphism is defined over the field. -/
@[reassoc] theorem matrixZeroSchemeIsoPolynomialSix_over :
    (matrixZeroSchemeIsoPolynomialSix K).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 6) (R := K))) =
    (matrixZeroIdeal K).subschemeι ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} Entry) (R := K))) := by
  simp only [matrixZeroSchemeIsoPolynomialSix,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    symmetrySchemeIsoPolynomialSix_over]
  rw [asIso_toImage_inv_imageι_assoc,
    eqToIso_subscheme_ι_assoc (matrixZeroIdeal K) ((symmetryInclusion K).ker)
      (matrixZeroIdeal_eq_symmetryKer K)]

/-- The actual LG chart isomorphism commutes with the actual structural morphism to the field. -/
@[reassoc] theorem lagrangianChartIsoPolynomialSix_over :
    (lagrangianChartIsoPolynomialSix K).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 6) (R := K))) =
    lagrangianChartMap K ≫ M9Native.LagrangianGrassmannian.projection K := by
  simp only [lagrangianChartIsoPolynomialSix,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    matrixZeroSchemeIsoPolynomialSix_over]
  rw [eqToIso_subscheme_ι_assoc
      ((M9Native.LagrangianGrassmannian.ideal K).comap (matrixChart K)) (matrixZeroIdeal K)
      (lagrangianIdeal_comap_matrixChart K),Scheme.IdealSheafData.comapIso_inv_subschemeι_assoc]
  rw [← matrixChart_projection,← Category.assoc,pullback.condition]
  exact Category.assoc _ _ _

/-- The affine-six big cell is an open immersion over the actual base field. -/
@[reassoc (attr := simp)] theorem bigCell_projection :
    bigCell K ≫ M9Native.LagrangianGrassmannian.projection K =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 6) (R := K))) := by
  rw [bigCell,Category.assoc,← lagrangianChartIsoPolynomialSix_over,Iso.inv_hom_id_assoc]

/-- The polynomial spectrum with six variables is the actual native affine six-space. -/
def polynomialSixIsoAffineSpace :
    Spec (.of (MvPolynomial (Fin 6) K)) ≅
      AffineSpace (ULift.{u} (Fin 6)) (Spec (.of K)) :=
  Scheme.Spec.mapIso (MvPolynomial.renameEquiv K
      (Equiv.ulift : ULift.{u} (Fin 6) ≃ Fin 6)).toRingEquiv.toCommRingCatIso.op ≪≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 6)) (.of K)).symm

@[reassoc] theorem polynomialSixIsoAffineSpace_over :
    (polynomialSixIsoAffineSpace K).hom ≫
      (AffineSpace (ULift.{u} (Fin 6)) (Spec (.of K)) ↘ Spec (.of K)) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := Fin 6) (R := K))) := by
  simp only [polynomialSixIsoAffineSpace,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    AffineSpace.SpecIso_inv_over]
  change Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv K
      (Equiv.ulift : ULift.{u} (Fin 6) ≃ Fin 6)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ := ULift.{u} (Fin 6)) (R := K))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact (MvPolynomial.renameEquiv K (Equiv.ulift : ULift.{u} (Fin 6) ≃ Fin 6)).commutes c

/-- The actual native Lagrangian Grassmannian big cell is the actual native affine six-space. -/
def lagrangianChartIsoAffineSix :
    lagrangianChart K ≅ AffineSpace (ULift.{u} (Fin 6)) (Spec (.of K)) :=
  lagrangianChartIsoPolynomialSix K ≪≫ polynomialSixIsoAffineSpace K

@[reassoc] theorem lagrangianChartIsoAffineSix_over :
    (lagrangianChartIsoAffineSix K).hom ≫
      (AffineSpace (ULift.{u} (Fin 6)) (Spec (.of K)) ↘ Spec (.of K)) =
    lagrangianChartMap K ≫ M9Native.LagrangianGrassmannian.projection K := by
  simp only [lagrangianChartIsoAffineSix,Iso.trans_hom,Category.assoc,
    polynomialSixIsoAffineSpace_over,lagrangianChartIsoPolynomialSix_over]

/-- An actual isomorphism in the category of schemes over the given field. -/
def lagrangianChartIsoOverAffineSix :
    Over.mk (lagrangianChartMap K ≫ M9Native.LagrangianGrassmannian.projection K) ≅
      Over.mk (AffineSpace (ULift.{u} (Fin 6)) (Spec (.of K)) ↘ Spec (.of K)) :=
  Over.isoMk (lagrangianChartIsoAffineSix K) (lagrangianChartIsoAffineSix_over K)


end M9Native.LagrangianMatrixChart

end
