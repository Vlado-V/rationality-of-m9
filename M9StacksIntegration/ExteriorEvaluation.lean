module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.AlgebraicGeometry.Modules.Stalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.LinearAlgebra.ExteriorPower.BaseChange

/-!
# Exterior evaluation of actual global sections

The source is the exterior power over the structural base field of actual
zeroth sheaf cohomology. The target is actual zeroth cohomology of the
chosen native sheaf exterior power. The construction passes through the
canonical sectionwise comparison; it does not identify global sections of
an exterior sheaf with the exterior power of global sections.

The map is natural under every sheaf morphism. Its stalk and fibre squares
use the canonical exterior-stalk and exterior-base-change isomorphisms.
For a genuine field-valued point `p : Spec L → X`, its fibre is the actual
tensor fibre over the local-ring map `Scheme.stalkClosedPointTo p`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.ExteriorEvaluation

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The actual scalar map on global functions induced by the structure morphism. -/
def baseRingMap : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom

/-- Actual global sections, with precisely the native restricted structural scalar action. -/
abbrev sectionsOverField (E : X.Modules) : ModuleCat.{u} k :=
  (restrictScalarsOverBase k f).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj E)

/-- The native H0/global-section isomorphism, viewed semilinearly over global functions. -/
def h0SectionsSemilinear (E : X.Modules) :
    cohomologyOverField k f E 0 →ₛₗ[baseRingMap k f] Γ(E, ⊤) where
  toFun := (cohomologyOverFieldZeroLinearIso k f E).hom
  map_add' := (cohomologyOverFieldZeroLinearIso k f E).hom.hom.map_add
  map_smul' c s := (cohomologyOverFieldZeroLinearIso k f E).hom.hom.map_smul c s

/-- The actual sectionwise exterior comparison into the chosen sheaf exterior power. -/
def sectionComparison (E : X.Modules) (n : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^n Γ(E, U)) →ₗ[Γ(X, U)] Γ(Scheme.Modules.exteriorPower E (n : ℤ), U) :=
  (Scheme.Modules.exteriorAlgebra E).toPresheafGradedAlgebra.extCmpSections
    (Scheme.Modules.exteriorGenerator E).val
    (fun V s => (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E).1 V s) n (op U)

/-- On local wedges the comparison is the actual product of the exterior generators. -/
theorem sectionComparison_ιMulti (E : X.Modules) (n : ℕ) (U : X.Opens)
    (s : Fin n → Γ(E, U)) :
    sectionComparison E n U (exteriorPower.ιMulti Γ(X, U) n s) =
      (Scheme.Modules.exteriorAlgebra E).toPresheafGradedAlgebra.homogeneousProd (op U) n
        (fun i => (Scheme.Modules.exteriorGenerator E).val.app (op U) (s i)) :=
  Stacks.GradedAlgebra.extCmpSections_ιMulti _ _ _ _ _ _

/-- Exterior powers of actual H0 sections, compared with actual global exterior-sheaf sections. -/
def lambdaSectionsSemilinear (E : X.Modules) (n : ℕ) :
    (⋀[k]^n (cohomologyOverField k f E 0)) →ₛₗ[baseRingMap k f]
      Γ(Scheme.Modules.exteriorPower E (n : ℤ), ⊤) :=
  (sectionComparison E n ⊤).comp
    (ExteriorAlgebra.powMapₛₗ n (baseRingMap k f) (h0SectionsSemilinear k f E))

/-- The same actual comparison with its structural `k`-linearity recorded. -/
def lambdaToSections (E : X.Modules) (n : ℕ) :
    (⋀[k]^n (cohomologyOverField k f E 0)) →ₗ[k]
      sectionsOverField k f (Scheme.Modules.exteriorPower E (n : ℤ)) where
  toFun := lambdaSectionsSemilinear k f E n
  map_add' := (lambdaSectionsSemilinear k f E n).map_add
  map_smul' c s := (lambdaSectionsSemilinear k f E n).map_smulₛₗ c s

/-- The genuine exterior evaluation map `λ_n`, for an arbitrary actual sheaf of modules. -/
def lambda (E : X.Modules) (n : ℕ) :
    (⋀[k]^n (cohomologyOverField k f E 0)) →ₗ[k]
      cohomologyOverField k f (Scheme.Modules.exteriorPower E (n : ℤ)) 0 :=
  (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (n : ℤ))).inv.hom.comp
    (lambdaToSections k f E n)

@[simp] theorem lambda_globalSection (E : X.Modules) (n : ℕ)
    (w : ⋀[k]^n (cohomologyOverField k f E 0)) :
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (n : ℤ))).hom
        (lambda k f E n w) = lambdaSectionsSemilinear k f E n w := by
  exact (cohomologyOverFieldZeroLinearIso k f
    (Scheme.Modules.exteriorPower E (n : ℤ))).inv_hom_id_apply _

/-- On decomposable wedges, the map is the canonical wedge of the actual sections. -/
theorem lambda_ιMulti (E : X.Modules) (n : ℕ)
    (s : Fin n → cohomologyOverField k f E 0) :
    (cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (n : ℤ))).hom
        (lambda k f E n (exteriorPower.ιMulti k n s)) =
      sectionComparison E n ⊤
        (exteriorPower.ιMulti Γ(X, ⊤) n (fun i => h0SectionsSemilinear k f E (s i))) := by
  rw [lambda_globalSection]
  change sectionComparison E n ⊤
    (ExteriorAlgebra.powMapₛₗ n (baseRingMap k f) (h0SectionsSemilinear k f E)
      (exteriorPower.ιMulti k n s)) = _
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti]

/-- The comparison is compatible with genuine restriction to every open subset. -/
theorem sectionComparison_restrict (E : X.Modules) (n : ℕ) (U : X.Opens)
    (s : Fin n → Γ(E, ⊤)) :
    (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        (sectionComparison E n ⊤ (exteriorPower.ιMulti Γ(X, ⊤) n s)) =
      sectionComparison E n U
        (exteriorPower.ιMulti Γ(X, U) n
          (fun i => E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (s i))) := by
  have h := Stacks.GradedAlgebra.extCmpSections_naturality
    (Scheme.Modules.exteriorAlgebra E).toPresheafGradedAlgebra
    (Scheme.Modules.exteriorGenerator E).val
    (fun V t => (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E).1 V t) n
    (homOfLE (show U ≤ ⊤ from le_top)).op (exteriorPower.ιMulti _ n s)
  exact h.trans (congrArg
    ((Scheme.Modules.exteriorAlgebra E).toPresheafGradedAlgebra.extCmpSections
      (Scheme.Modules.exteriorGenerator E).val
      (fun V t => (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E).1 V t) n (op U))
    (ExteriorAlgebra.powMapₛₗ_ιMulti (R := Γ(X, ⊤)) (S := Γ(X, U))
      (M := Γ(E, ⊤)) (N := Γ(E, U)) n _
      (E.val.restrictₛₗ (homOfLE (show U ≤ ⊤ from le_top)).op) s))

/-- The decomposable formula on every actual open uses the restrictions of the original sections. -/
theorem lambda_restrict_ιMulti (E : X.Modules) (n : ℕ) (U : X.Opens)
    (s : Fin n → cohomologyOverField k f E 0) :
    (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf.map
        (homOfLE (show U ≤ ⊤ from le_top)).op
        ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (n : ℤ))).hom
          (lambda k f E n (exteriorPower.ιMulti k n s))) =
      sectionComparison E n U
        (exteriorPower.ιMulti Γ(X, U) n (fun i =>
          E.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
            (h0SectionsSemilinear k f E (s i)))) := by
  rw [lambda_ιMulti]
  exact sectionComparison_restrict E n U _

/-- The actual stalk, with its canonical action of the actual local ring. -/
abbrev stalkSections (E : X.Modules) (x : X) : ModuleCat.{u} (X.presheaf.stalk x) :=
  ModuleCat.of _ (E.presheaf.stalk x)

/-- The canonical native identification of the stalk of the chosen exterior sheaf. -/
def stalkComparison (E : X.Modules) (n : ℕ) (x : X) :
    stalkSections (Scheme.Modules.exteriorPower E (n : ℤ)) x ≃ₗ[X.presheaf.stalk x]
      ⋀[X.presheaf.stalk x]^n (stalkSections E x) :=
  SheafOfModules.exteriorPowerStalkEquiv
    (Scheme.Modules.exteriorAlgebra E) (Scheme.Modules.exteriorGenerator E)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E) n x

/-- Evaluating the actual local wedge in a stalk gives the wedge of the actual germs. -/
theorem sectionComparison_germ_ιMulti (E : X.Modules) (n : ℕ) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Fin n → Γ(E, U)) :
    stalkComparison E n x
      (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf U x hx
        (sectionComparison E n U (exteriorPower.ιMulti Γ(X, U) n s))) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i => TopCat.Presheaf.germ E.presheaf U x hx (s i)) := by
  rw [sectionComparison_ιMulti]
  exact SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd
    (Scheme.Modules.exteriorAlgebra E) (Scheme.Modules.exteriorGenerator E)
    (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E) n x U hx s

/-- Stalk evaluation of `λ_n` is the wedge of the original sections evaluated in that stalk. -/
theorem lambda_germ_ιMulti (E : X.Modules) (n : ℕ) (x : X)
    (s : Fin n → cohomologyOverField k f E 0) :
    stalkComparison E n x
      (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf ⊤ x (by simp)
        ((cohomologyOverFieldZeroLinearIso k f (Scheme.Modules.exteriorPower E (n : ℤ))).hom
          (lambda k f E n (exteriorPower.ιMulti k n s)))) =
      exteriorPower.ιMulti (X.presheaf.stalk x) n
        (fun i => TopCat.Presheaf.germ E.presheaf ⊤ x (by simp)
          (h0SectionsSemilinear k f E (s i))) := by
  rw [lambda_ιMulti]
  exact sectionComparison_germ_ιMulti E n x ⊤ (by simp) _

/-- The actual scalar map from the structural field to a local ring. -/
abbrev stalkBaseRingMap (x : X) : k →+* X.presheaf.stalk x :=
  (X.presheaf.germ ⊤ x (by simp)).hom.comp (baseRingMap k f)

instance stalkBaseRingMap_compTriple (x : X) :
    RingHomCompTriple (baseRingMap k f) (X.presheaf.germ ⊤ x (by simp)).hom
      (stalkBaseRingMap k f x) := ⟨rfl⟩

/-- Evaluate an actual native H0 class in the actual stalk. -/
def h0StalkEvaluation (E : X.Modules) (x : X) :
    cohomologyOverField k f E 0 →ₛₗ[stalkBaseRingMap k f x] stalkSections E x :=
  (PresheafOfModules.germₛₗ (R := X.presheaf) E.val x ⊤ (by simp)).comp
    (h0SectionsSemilinear k f E)

/-- Evaluate the sectionwise exterior comparison in an actual stalk. -/
def lambdaStalkEvaluation (E : X.Modules) (n : ℕ) (x : X) :
    (⋀[k]^n (cohomologyOverField k f E 0)) →ₛₗ[stalkBaseRingMap k f x]
      stalkSections (Scheme.Modules.exteriorPower E (n : ℤ)) x :=
  (PresheafOfModules.germₛₗ (R := X.presheaf) (Scheme.Modules.exteriorPower E (n : ℤ)).val x ⊤
    (by simp)).comp (lambdaSectionsSemilinear k f E n)

/-- The entire stalk evaluation square commutes, for every exterior vector. -/
theorem lambda_stalk_naturality (E : X.Modules) (n : ℕ) (x : X) :
    (stalkComparison E n x).toLinearMap.comp (lambdaStalkEvaluation k f E n x) =
      ExteriorAlgebra.powMapₛₗ n (stalkBaseRingMap k f x) (h0StalkEvaluation k f E x) := by
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  change stalkComparison E n x
    (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf ⊤ x (by simp)
      (sectionComparison E n ⊤
        (ExteriorAlgebra.powMapₛₗ n (baseRingMap k f) (h0SectionsSemilinear k f E)
          (exteriorPower.ιMulti k n s)))) = _
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti, ExteriorAlgebra.powMapₛₗ_ιMulti]
  exact sectionComparison_germ_ιMulti E n x ⊤ (by simp) _

/-- A wedge killed by actual `λ_n` vanishes after evaluation in every actual stalk. -/
theorem wedge_germs_eq_zero_of_lambda_eq_zero (E : X.Modules) (n : ℕ) (x : X)
    (s : Fin n → cohomologyOverField k f E 0)
    (h_lambda : lambda k f E n (exteriorPower.ιMulti k n s) = 0) :
    exteriorPower.ιMulti (X.presheaf.stalk x) n
      (fun i => h0StalkEvaluation k f E x (s i)) = 0 := by
  have h := lambda_germ_ιMulti k f E n x s
  rw [h_lambda, map_zero, map_zero, map_zero] at h
  exact h.symm

/-- The chosen exterior-power sheaf map carries the canonical local wedge to the wedge of
the images of the original sections. -/
theorem sectionComparison_map_ιMulti {E F : X.Modules} (φ : E ⟶ F)
    (n : ℕ) (U : X.Opens) (s : Fin n → Γ(E, U)) :
    (Scheme.Modules.exteriorPowerMap φ (n : ℤ)).app U
        (sectionComparison E n U (exteriorPower.ιMulti Γ(X, U) n s)) =
      sectionComparison F n U
        (exteriorPower.ιMulti Γ(X, U) n (fun i => φ.app U (s i))) := by
  rw [sectionComparison_ιMulti, sectionComparison_ιMulti]
  refine (SheafOfModules.GradedAlgebra.UnitalHom.app_homogeneousProd
    ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E).map
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F) φ) (op U) n _).trans ?_
  refine congrArg
    ((Scheme.Modules.exteriorAlgebra F).toPresheafGradedAlgebra.homogeneousProd (op U) n)
    (funext fun i => ?_)
  exact SheafOfModules.hom_congr_app_apply
    ((Scheme.Modules.isExteriorAlgebra_exteriorAlgebra E).map_app_one
      (Scheme.Modules.isExteriorAlgebra_exteriorAlgebra F) φ) (op U) (s i)

/-- The genuine `λ_n` is natural under every actual morphism of sheaves of modules. -/
theorem lambda_naturality {E F : X.Modules} (φ : E ⟶ F) (n : ℕ) :
    (cohomologyOverFieldMap k f (Scheme.Modules.exteriorPowerMap φ (n : ℤ)) 0).hom.comp
        (lambda k f E n) =
      (lambda k f F n).comp
        (exteriorPower.map n (cohomologyOverFieldMap k f φ 0).hom) := by
  refine exteriorPower.linearMap_ext (AlternatingMap.ext fun s => ?_)
  change cohomologyOverFieldMap k f (Scheme.Modules.exteriorPowerMap φ (n : ℤ)) 0
    (lambda k f E n (exteriorPower.ιMulti k n s)) = _
  apply (cohomologyOverFieldZeroLinearIso k f
    (Scheme.Modules.exteriorPower F (n : ℤ))).toLinearEquiv.injective
  change (cohomologyOverFieldZeroLinearIso k f
    (Scheme.Modules.exteriorPower F (n : ℤ))).hom
      (cohomologyOverFieldMap k f (Scheme.Modules.exteriorPowerMap φ (n : ℤ)) 0
        (lambda k f E n (exteriorPower.ιMulti k n s))) =
    (cohomologyOverFieldZeroLinearIso k f
      (Scheme.Modules.exteriorPower F (n : ℤ))).hom
        (lambda k f F n
          (exteriorPower.map n (cohomologyOverFieldMap k f φ 0).hom
            (exteriorPower.ιMulti k n s)))
  rw [cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap, lambda_ιMulti]
  rw [sectionComparison_map_ιMulti, exteriorPower.map_apply_ιMulti, lambda_ιMulti]
  refine congrArg (sectionComparison F n ⊤) (congrArg (exteriorPower.ιMulti Γ(X, ⊤) n)
    (funext fun i => ?_))
  exact (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f φ (s i)).symm

/-- In particular `λ_n` is compatible with every actual bundle isomorphism. -/
theorem lambda_iso_naturality {E F : X.Modules} (e : E ≅ F) (n : ℕ) :
    (cohomologyOverFieldMap k f (Scheme.Modules.exteriorPowerMap e.hom (n : ℤ)) 0).hom.comp
        (lambda k f E n) =
      (lambda k f F n).comp
        (exteriorPower.map n (cohomologyOverFieldMap k f e.hom 0).hom) :=
  lambda_naturality k f e.hom n

section Fiber

variable (x : X) (A : Type u) [CommRing A] [Algebra (X.presheaf.stalk x) A]

/-- The genuine tensor fibre after any scalar extension of the actual local ring. -/
abbrev fiberSections (E : X.Modules) : ModuleCat.{u} A :=
  ModuleCat.of A (A ⊗[X.presheaf.stalk x] (stalkSections E x))

/-- The canonical exterior comparison for the genuine tensor fibre. -/
def fiberComparison (E : X.Modules) (n : ℕ) :
    fiberSections x A (Scheme.Modules.exteriorPower E (n : ℤ)) ≃ₗ[A]
      ⋀[A]^n (fiberSections x A E) :=
  ((stalkComparison E n x).baseChange (X.presheaf.stalk x) A _ _).trans
    (ExteriorAlgebra.exteriorPowerBaseChange (X.presheaf.stalk x) A (stalkSections E x) n)

/-- Actual passage from the stalk to its tensor fibre. -/
def stalkToFiber (E : X.Modules) :
    stalkSections E x →ₛₗ[algebraMap (X.presheaf.stalk x) A] fiberSections x A E where
  toFun s := (1 : A) ⊗ₜ[X.presheaf.stalk x] s
  map_add' s t := TensorProduct.tmul_add _ s t
  map_smul' r s := by simp only [TensorProduct.tmul_smul, algebraMap_smul]

/-- The structural scalar map into the tensor fibre's coefficient ring. -/
abbrev fiberBaseRingMap : k →+* A :=
  (algebraMap (X.presheaf.stalk x) A).comp (stalkBaseRingMap k f x)

instance fiberBaseRingMap_compTriple :
    RingHomCompTriple (stalkBaseRingMap k f x) (algebraMap (X.presheaf.stalk x) A)
      (fiberBaseRingMap k f x A) := ⟨rfl⟩

/-- Evaluate the actual H0 section in the genuine tensor fibre. -/
def h0FiberEvaluation (E : X.Modules) :
    cohomologyOverField k f E 0 →ₛₗ[fiberBaseRingMap k f x A] fiberSections x A E :=
  (stalkToFiber x A E).comp (h0StalkEvaluation k f E x)

/-- Evaluate the actual exterior H0 section in the genuine tensor fibre. -/
def lambdaFiberEvaluation (E : X.Modules) (n : ℕ) :
    (⋀[k]^n (cohomologyOverField k f E 0)) →ₛₗ[fiberBaseRingMap k f x A]
      fiberSections x A (Scheme.Modules.exteriorPower E (n : ℤ)) :=
  (h0FiberEvaluation k f x A (Scheme.Modules.exteriorPower E (n : ℤ))).comp (lambda k f E n)

/-- Fibre evaluation of the actual wedge is the wedge of the evaluated sections. -/
theorem lambda_fiber_ιMulti (E : X.Modules) (n : ℕ)
    (s : Fin n → cohomologyOverField k f E 0) :
    fiberComparison x A E n
      (h0FiberEvaluation k f x A (Scheme.Modules.exteriorPower E (n : ℤ))
        (lambda k f E n (exteriorPower.ιMulti k n s))) =
      exteriorPower.ιMulti A n (fun i => h0FiberEvaluation k f x A E (s i)) := by
  change ExteriorAlgebra.exteriorPowerBaseChange (X.presheaf.stalk x) A
    (stalkSections E x) n
      ((1 : A) ⊗ₜ[X.presheaf.stalk x]
        (stalkComparison E n x
          (TopCat.Presheaf.germ (Scheme.Modules.exteriorPower E (n : ℤ)).presheaf ⊤ x (by simp)
            ((cohomologyOverFieldZeroLinearIso k f
              (Scheme.Modules.exteriorPower E (n : ℤ))).hom
                (lambda k f E n (exteriorPower.ιMulti k n s)))))) = _
  rw [lambda_germ_ιMulti, ExteriorAlgebra.exteriorPowerBaseChange_tmul_ιMulti, one_smul]
  rfl

/-- The entire exterior evaluation square commutes in the genuine tensor fibre. -/
theorem lambda_fiber_naturality (E : X.Modules) (n : ℕ) :
    (fiberComparison x A E n).toLinearMap.comp (lambdaFiberEvaluation k f x A E n) =
      ExteriorAlgebra.powMapₛₗ n (fiberBaseRingMap k f x A) (h0FiberEvaluation k f x A E) := by
  refine ExteriorAlgebra.powExtₛₗ fun s => ?_
  change fiberComparison x A E n
    (h0FiberEvaluation k f x A (Scheme.Modules.exteriorPower E (n : ℤ))
      (lambda k f E n (exteriorPower.ιMulti k n s))) = _
  rw [ExteriorAlgebra.powMapₛₗ_ιMulti]
  exact lambda_fiber_ιMulti k f x A E n s

/-- An arbitrary exterior vector killed by actual `λ_n` vanishes in every genuine fibre. -/
theorem fiber_exterior_eq_zero_of_lambda_eq_zero (E : X.Modules) (n : ℕ)
    (w : ⋀[k]^n (cohomologyOverField k f E 0)) (h_lambda : lambda k f E n w = 0) :
    ExteriorAlgebra.powMapₛₗ n (fiberBaseRingMap k f x A) (h0FiberEvaluation k f x A E) w = 0 := by
  have h := DFunLike.congr_fun (lambda_fiber_naturality k f x A E n) w
  change fiberComparison x A E n
    (h0FiberEvaluation k f x A (Scheme.Modules.exteriorPower E (n : ℤ))
      (lambda k f E n w)) = _ at h
  rw [h_lambda, map_zero, map_zero] at h
  exact h.symm

/-- Actual `λ_n`-vanishing forces vanishing of the evaluated wedge in the genuine fibre. -/
theorem wedge_fiber_eq_zero_of_lambda_eq_zero (E : X.Modules) (n : ℕ)
    (s : Fin n → cohomologyOverField k f E 0)
    (h_lambda : lambda k f E n (exteriorPower.ιMulti k n s) = 0) :
    exteriorPower.ιMulti A n (fun i => h0FiberEvaluation k f x A E (s i)) = 0 := by
  have h := lambda_fiber_ιMulti k f x A E n s
  rw [h_lambda, map_zero, map_zero] at h
  exact h.symm

end Fiber

section FieldPoint

open IsLocalRing

variable (L : Type u) [Field L] (p : Spec (.of L) ⟶ X)

/-- The actual field-valued point gives its canonical local-ring algebra structure. -/
abbrev pointAlgebra : Algebra (X.presheaf.stalk (p (closedPoint L))) L :=
  (Scheme.stalkClosedPointTo p).hom.toAlgebra

/-- The actual fibre of `E` at the given field-valued point. -/
abbrev pointFiber (E : X.Modules) : ModuleCat.{u} L :=
  letI := pointAlgebra L p
  fiberSections (p (closedPoint L)) L E

/-- The canonical native exterior comparison on the actual field-point fibre. -/
def pointFiberComparison (E : X.Modules) (n : ℕ) :
    pointFiber L p (Scheme.Modules.exteriorPower E (n : ℤ)) ≃ₗ[L]
      ⋀[L]^n (pointFiber L p E) :=
  letI := pointAlgebra L p
  fiberComparison (p (closedPoint L)) L E n

/-- Actual section evaluation at the field-valued point. -/
abbrev pointBaseRingMap : k →+* L :=
  letI := pointAlgebra L p
  fiberBaseRingMap k f (p (closedPoint L)) L

/-- Actual section evaluation at the field-valued point, with its canonical semilinearity. -/
def pointEvaluation (E : X.Modules) :
    cohomologyOverField k f E 0 →ₛₗ[pointBaseRingMap k f L p] pointFiber L p E :=
  letI := pointAlgebra L p
  h0FiberEvaluation k f (p (closedPoint L)) L E

/-- The whole field-point evaluation square commutes for arbitrary exterior vectors. -/
theorem lambda_point_naturality (E : X.Modules) (n : ℕ) :
    (pointFiberComparison L p E n).toLinearMap.comp
        ((pointEvaluation k f L p (Scheme.Modules.exteriorPower E (n : ℤ))).comp
          (lambda k f E n)) =
      ExteriorAlgebra.powMapₛₗ n (pointBaseRingMap k f L p) (pointEvaluation k f L p E) := by
  let := pointAlgebra L p
  exact lambda_fiber_naturality k f (p (closedPoint L)) L E n

/-- The field-point evaluation square for the genuine native `λ_n`. -/
theorem lambda_point_ιMulti (E : X.Modules) (n : ℕ)
    (s : Fin n → cohomologyOverField k f E 0) :
    pointFiberComparison L p E n
      (pointEvaluation k f L p (Scheme.Modules.exteriorPower E (n : ℤ))
        (lambda k f E n (exteriorPower.ιMulti k n s))) =
      exteriorPower.ιMulti L n (fun i => pointEvaluation k f L p E (s i)) := by
  let := pointAlgebra L p
  exact lambda_fiber_ιMulti k f (p (closedPoint L)) L E n s

/-- Any vector in the actual kernel of `λ_n` vanishes at every actual field-valued point. -/
theorem point_exterior_eq_zero_of_lambda_eq_zero (E : X.Modules) (n : ℕ)
    (w : ⋀[k]^n (cohomologyOverField k f E 0)) (h_lambda : lambda k f E n w = 0) :
    ExteriorAlgebra.powMapₛₗ n (pointBaseRingMap k f L p) (pointEvaluation k f L p E) w = 0 := by
  let := pointAlgebra L p
  exact fiber_exterior_eq_zero_of_lambda_eq_zero k f (p (closedPoint L)) L E n w h_lambda

/-- A wedge killed by actual `λ_n` vanishes at every actual field-valued point. -/
theorem wedge_point_eq_zero_of_lambda_eq_zero (E : X.Modules) (n : ℕ)
    (s : Fin n → cohomologyOverField k f E 0)
    (h_lambda : lambda k f E n (exteriorPower.ιMulti k n s) = 0) :
    exteriorPower.ιMulti L n (fun i => pointEvaluation k f L p E (s i)) = 0 := by
  let := pointAlgebra L p
  exact wedge_fiber_eq_zero_of_lambda_eq_zero k f (p (closedPoint L)) L E n s h_lambda

end FieldPoint

end M9Native.ExteriorEvaluation
