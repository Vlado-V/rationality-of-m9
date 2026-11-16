module

public import M9StacksIntegration.ExteriorEvaluation
public import M9StacksIntegration.MukaiSemiIrreducible

/-!
# Actual fibre coordinates for finite tuples of native sections

The fibre is the actual residue-field tensor of the sheaf stalk. Finite
local freeness supplies an actual basis of the prescribed size. The finite
tuple map and its rank are compared with the original free-sheaf evaluation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.TupleEvaluationFiber

variable {X : Scheme.{u}}

/-- The actual local-to-residue-field algebra structure. -/
abbrev residueAlgebra (x : X) : Algebra (X.presheaf.stalk x) (X.residueField x) :=
  (X.residue x).hom.toAlgebra

/-- The original residue fibre, with its native vector-space structure bundled. -/
abbrev Fiber (E : X.Modules) (x : X) : ModuleCat.{u} (X.residueField x) :=
  letI := residueAlgebra x
  ExteriorEvaluation.fiberSections x (X.residueField x) E

/-- Finite local freeness of rank `r` supplies an actual `Fin r` basis of every fibre. -/
theorem nonempty_fiberBasis (E : X.Modules) (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]
    (x : X) : Nonempty (Module.Basis (Fin r) (X.residueField x) (Fiber E x)) := by
  classical
  obtain ⟨q, hq, hr⟩ := hE.exists_isFiniteLocallyFreeOfRankData
  have hcov : TopologicalSpace.IsOpenCover q.X := (Opens.coversTop_iff X q.X).mp q.coversTop
  obtain ⟨i, hxi⟩ := hcov.exists_mem x
  let t := LocallyFreeRank.trivializationOfLocalGenerators E q hq i
  obtain ⟨e⟩ := LocallyFreeRank.Trivialization.stalk_linearEquiv_finsupp
    X.toTopCat X.sheaf E x hxi t
  obtain ⟨ei⟩ := hr i
  let b : Module.Basis (Fin r) (X.presheaf.stalk x) (ExteriorEvaluation.stalkSections E x) :=
    ((Finsupp.basisSingleOne (ι := t.ι) (R := X.presheaf.stalk x)).map e.symm).reindex ei
  let := residueAlgebra x
  exact ⟨b.baseChange (X.residueField x)⟩

/-- A chosen actual fibre basis, with no coordinate-space identification premise. -/
def fiberBasis (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    Module.Basis (Fin r) (X.residueField x) (Fiber E x) :=
  Classical.choice (nonempty_fiberBasis E r x)

/-- Actual finiteness of the residue fibre follows from the proved finite basis. -/
theorem fiberFinite (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    Module.Finite (X.residueField x) (Fiber E x) :=
  Module.Finite.of_basis (fiberBasis E r x)

/-- The dimension of the actual residue fibre is the prescribed locally free rank. -/
theorem finrank_fiber (E : X.Modules) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    Module.finrank (X.residueField x) (Fiber E x) = r := by
  simpa using Module.finrank_eq_card_basis (fiberBasis E r x)

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- The actual structural field embedding into the residue field. -/
abbrev residueBaseRingMap (x : X) : k →+* X.residueField x :=
  letI := residueAlgebra x
  ExteriorEvaluation.fiberBaseRingMap k f x (X.residueField x)

/-- The original native H0 section evaluated in the actual residue fibre. -/
def sectionValue (E : X.Modules) (x : X) :
    cohomologyOverField k f E 0 →ₛₗ[residueBaseRingMap k f x] Fiber E x :=
  letI := residueAlgebra x
  ExteriorEvaluation.h0FiberEvaluation k f x (X.residueField x) E

/-- The actual residue-field linear map associated with a finite tuple of sections. -/
def tupleMap {r : ℕ} (E : X.Modules) (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    (Fin r → X.residueField x) →ₗ[X.residueField x] Fiber E x :=
  (Pi.basisFun (X.residueField x) (Fin r)).constr (X.residueField x)
    (fun i => sectionValue k f E x (s i))

/-- Each coordinate basis vector is sent to the actual value of the corresponding section. -/
theorem tupleMap_single {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) (i : Fin r) :
    tupleMap k f E s x (Pi.single i 1) = sectionValue k f E x (s i) := by
  change (Pi.basisFun (X.residueField x) (Fin r)).constr (X.residueField x)
    (fun j => sectionValue k f E x (s j)) (Pi.single i 1) = _
  rw [← Pi.basisFun_apply (X.residueField x) (Fin r) i, Module.Basis.constr_basis]

/-- The original native sheaf morphism on its actual residue fibres. -/
def inducedFiberMap {E F : X.Modules} (φ : E ⟶ F) (x : X) :
    Fiber E x →ₗ[X.residueField x] Fiber F x :=
  letI := residueAlgebra x
  MukaiSemiIrreducible.fiberMap φ x

/-- Taking the actual stalk map carries a germ to the germ of its sheaf-map image. -/
theorem stalkMap_germ {E F : X.Modules} (φ : E ⟶ F) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(E, U)) :
    Stacks.SheafOfModules.FlatShortExact.stalkLinearMap
        (X := X.toRingedSpace) φ x (TopCat.Presheaf.germ E.presheaf U x hx s) =
      TopCat.Presheaf.germ F.presheaf U x hx (φ.app U s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map φ.val) s

/-- The actual residue-fibre map is scalar extension of that exact germ formula. -/
theorem inducedFiberMap_tmul_germ {E F : X.Modules} (φ : E ⟶ F) (x : X)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(E, U)) (a : X.residueField x) :
    letI := residueAlgebra x
    inducedFiberMap φ x
        (a ⊗ₜ[X.presheaf.stalk x] TopCat.Presheaf.germ E.presheaf U x hx s) =
      a ⊗ₜ[X.presheaf.stalk x] TopCat.Presheaf.germ F.presheaf U x hx (φ.app U s) := by
  let := residueAlgebra x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) E x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule (X := X.toRingedSpace) F x
  change (Stacks.SheafOfModules.FlatShortExact.stalkLinearMap
    (X := X.toRingedSpace) φ x).baseChange (X.residueField x) _ = _
  rw [LinearMap.baseChange_tmul, stalkMap_germ]

/-- The original free-sheaf tuple evaluation has the prescribed actual section on generators. -/
theorem evaluation_freeSection_top {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (i : Fin r) :
    (MukaiSemiIrreducible.evaluation k f E s).val.app (op ⊤)
        ((_root_.SheafOfModules.freeSection (R := X.ringCatSheaf)
          (ULift.up i : ULift.{u} (Fin r))).eval (op ⊤)) =
      (cohomologyOverFieldZeroLinearIso k f E).hom (s i) := by
  have h := congrArg (fun a : E.sections => a.eval (op ⊤))
    (MukaiSemiIrreducible.evaluation_freeSection k f E s (ULift.up i))
  exact h.trans (MukaiSemiIrreducible.sectionOfH0_eval_top k f E (s i))

end M9Native.TupleEvaluationFiber
