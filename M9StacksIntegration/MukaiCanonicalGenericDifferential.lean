module

public import M9StacksIntegration.CanonicalMapNonconstant
public import M9StacksIntegration.CurveGenericDifferentialRank
public import M9StacksIntegration.MukaiPrimitiveCanonicalEvaluation
public import M9StacksIntegration.LagrangianPluckerClosed

/-!
# The original genus-nine Mukai map has generic differential rank one

The actual pullback of the actual universal LG determinant line is the
original canonical sheaf. Its native degree is calculated to be sixteen,
so the original map is nonconstant and finite. Characteristic zero and
the actual cotangent triangle then prove the rank of the original native
relative differential on its actual generic residue fibre.

The final specialization retains the actual EvaluationDiagram map and
its checked canonicalIso. No nonconstancy, differential rank, exterior
surjectivity, or first-jet premise is introduced.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.MukaiCanonicalGenericDifferential

open MukaiCanonicalExteriorCohomology MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation

section Intrinsic

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hg : genus f = 9)

include hg

theorem not_constant_of_canonicalIso
    (g : X ⟶ LagrangianGrassmannian.space k)
    (e : (Scheme.Modules.pullback g).obj (LagrangianPluckerQuotient.determinantLine k) ≅
      Stacks.Duality.dualizingSheafOverField f) :
    ¬ ∃ y : LagrangianGrassmannian.space k, ∀ x : X, g.base x = y :=
  CanonicalMapNonconstant.not_constant_of_canonical_line_pullback k f
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) hg g _ e

theorem isFinite_of_canonicalIso
    (g : X ⟶ LagrangianGrassmannian.space k)
    (hgf : g ≫ LagrangianGrassmannian.projection k = f)
    (e : (Scheme.Modules.pullback g).obj (LagrangianPluckerQuotient.determinantLine k) ≅
      Stacks.Duality.dualizingSheafOverField f) : IsFinite g := by
  have : IsProper (LagrangianGrassmannian.projection k) :=
    isProper_of_isProjectiveMorphism _ (LagrangianPluckerClosed.isProjectiveMorphism_projection k)
  exact CanonicalMapNonconstant.isFinite_of_canonical_line_pullback k f
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) hg
    (LagrangianGrassmannian.projection k) g hgf _ e

theorem differential_rank_one_of_canonicalIso
    (g : X ⟶ LagrangianGrassmannian.space k)
    (hgf : g ≫ LagrangianGrassmannian.projection k = f)
    (e : (Scheme.Modules.pullback g).obj (LagrangianPluckerQuotient.determinantLine k) ≅
      Stacks.Duality.dualizingSheafOverField f) :
    MukaiSemiIrreducible.mapRankAt
      (Scheme.Hom.relativeDifferentialsMap g (LagrangianGrassmannian.projection k) f (𝟙 _)
        (by simpa using hgf)) (genericPoint X) = 1 := by
  have : IsFinite g := isFinite_of_canonicalIso k f hg g hgf e
  exact CurveGenericDifferentialRank.relativeDifferentialsMap_rank_one_of_isFinite k
    (LagrangianGrassmannian.projection k) g f hgf

end Intrinsic

section Evaluation

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
    (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (c : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hg : genus f = 9)

include c hg

theorem evaluationDiagram_not_constant (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) :
    ¬ ∃ y : LagrangianGrassmannian.space k, ∀ x : X, d.map.base x = y :=
  not_constant_of_canonicalIso k f hg d.map (d.canonicalIso k f E c)

theorem evaluationDiagram_isFinite (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) : IsFinite d.map :=
  isFinite_of_canonicalIso k f hg d.map d.over_base (d.canonicalIso k f E c)

theorem evaluationDiagram_differential_rank_one (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) :
    MukaiSemiIrreducible.mapRankAt
      (Scheme.Hom.relativeDifferentialsMap d.map (LagrangianGrassmannian.projection k) f (𝟙 _)
        (by simpa using d.over_base)) (genericPoint X) = 1 :=
  differential_rank_one_of_canonicalIso k f hg d.map d.over_base (d.canonicalIso k f E c)

end Evaluation

end M9Native.MukaiCanonicalGenericDifferential
