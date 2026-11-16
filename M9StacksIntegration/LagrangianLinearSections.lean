module

public import M9StacksIntegration.LagrangianPluckerQuotient
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological

/-! The actual universal family of primitive linear sections. The parameter
is the native Grassmannian of nine-dimensional kernels in the fixed
fourteen coordinates. Its actual rank-five universal quotient is paired
with the actual fourteen determinant sections; the family is the genuine
zero scheme of this rank-five tensor-bundle section. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
namespace M9Native.LagrangianLinearSections
open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianPluckerQuotient M9Native.LagrangianMatrixChart
open M9Native.SectionZeroIdealFactorization
variable (K : Type u) [Field K]

/-- The actual native parameter of rank-nine kernels in the fourteen primitive coordinates. -/
abbrev parameter : Scheme.{u} := M9Native.GrassmannianCharts.space K 9 14
abbrev parameterProjection : parameter K ⟶ Spec (.of K) :=
  M9Native.GrassmannianCharts.projection K 9 14

def integralParameterClass : Points (AlgebraicGeometry.Grassmannian.scheme.{u} 9 14) 9 14 :=
  (functorData 9 14).objEquiv _ ((schemeRepresentableBy 9 14).homEquiv (𝟙 _))

def integralParameterQuotient : QuotientPresentation
    (AlgebraicGeometry.Grassmannian.scheme.{u} 9 14) 9 14 :=
  Quotient.out (integralParameterClass.{u})

/-- The actual universal quotient of rank five, chosen from its representing class. -/
def parameterQuotient : QuotientPresentation (parameter K) 9 14 :=
  pullbackPresentation (M9Native.GrassmannianCharts.toIntegral K 9 14) integralParameterQuotient

instance parameterQuotient_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (parameterQuotient K).target 5 := by
  simpa using (parameterQuotient K).finiteLocallyFree

/-- The actual product over the given field, before imposing the incidence equation. -/
abbrev ambient : Scheme.{u} :=
  pullback (M9Native.LagrangianGrassmannian.projection K) (parameterProjection K)
abbrev toLG : ambient K ⟶ M9Native.LagrangianGrassmannian.space K := pullback.fst _ _
abbrev toParameter : ambient K ⟶ parameter K := pullback.snd _ _

@[reassoc] theorem ambient_over :
    toLG K ≫ M9Native.LagrangianGrassmannian.projection K=toParameter K ≫ parameterProjection K :=
  pullback.condition

abbrev ambientQuotient : QuotientPresentation (ambient K) 9 14 :=
  pullbackPresentation (toParameter K) (parameterQuotient K)
abbrev quotientFive : (ambient K).Modules := (ambientQuotient K).target

instance quotientFive_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientFive K) 5 := by
  simpa using (ambientQuotient K).finiteLocallyFree

/-- The actual pulled-back determinant line, with its literal geometric source retained. -/
abbrev lineBundle : (ambient K).Modules :=
  (Scheme.Modules.pullback (toLG K)).obj (determinantLine K)

instance lineBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (lineBundle K) 1 :=
  isFiniteLocallyFreeOfRank_pullback (toLG K).base (toLG K).toRingCatSheafHom
    (determinantLine K) 1 (determinantLine_rank K)

/-- The genuine rank-five tensor bundle carrying the five universal linear equations. -/
abbrev equationBundle : (ambient K).Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor (ambient K).sheaf).obj (lineBundle K)).obj (quotientFive K))

instance equationBundle_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (equationBundle K) 5 := by
  exact AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf
    (ambient K) (lineBundle K) (quotientFive K) 1 5

def lineSection (i : Fin 14) : Γ(lineBundle K,⊤) :=
  pullbackGlobalSections (toLG K) (determinantLine K) (primitiveSections K i)

def quotientSection (i : Fin 14) : Γ(quotientFive K,⊤) :=
  Scheme.Modules.Hom.app (ambientQuotient K).map ⊤ (freeBasisSection (ambient K) 14 i)

/-- The actual pure tensor of local sections in the native sheaf tensor product. -/
def tensorSection (s : Γ(lineBundle K,⊤)) (t : Γ(quotientFive K,⊤)) :
    Γ(equationBundle K,⊤) :=
  Stacks.SheafOfModules.pairingApp
    (Stacks.SheafOfModules.Tensor.ringSheaf (ambient K).sheaf)
    (Stacks.SheafOfModules.tensorSectionPairing (O:=(ambient K).sheaf)
      (lineBundle K) (quotientFive K)) (op ⊤) s t

/-- The literal sum of the fourteen universal linear coefficient tensors. -/
def equationSection : Γ(equationBundle K,⊤) :=
  ∑ i : Fin 14,tensorSection K (lineSection K i) (quotientSection K i)

/-- The actual dual-evaluation zero ideal, on the actual product scheme. -/
def ideal : (ambient K).IdealSheafData :=
  sectionZeroIdeal (ambient K) (equationBundle K) (equationSection K)

abbrev family : Scheme.{u} := (ideal K).subscheme
abbrev inclusion : family K ⟶ ambient K := (ideal K).subschemeι

instance inclusion_isClosedImmersion : IsClosedImmersion (inclusion K) := inferInstance

abbrev familyProjection : family K ⟶ parameter K := inclusion K ≫ toParameter K
abbrev familyToLG : family K ⟶ M9Native.LagrangianGrassmannian.space K := inclusion K ≫ toLG K

/-- The family is the actual scheme-theoretic zero locus on every test scheme. -/
theorem factorsThrough_iff_equation_zero {T : Scheme.{u}} (f : T ⟶ ambient K) :
    (∃ g : T ⟶ family K,g ≫ inclusion K=f) ↔
      pullbackGlobalSections f (equationBundle K) (equationSection K)=0 :=
  (pullbackGlobalSections_eq_zero_iff_factorsThrough (equationBundle K) 5 (equationSection K) f).symm


@[reassoc] theorem family_over :
    familyToLG K ≫ M9Native.LagrangianGrassmannian.projection K=
      familyProjection K ≫ parameterProjection K := by
  exact Category.assoc _ _ _ |>.trans
    ((congrArg (fun h => inclusion K ≫ h) (ambient_over K)).trans (Category.assoc _ _ _).symm)

/-- The actual universal equation vanishes on the actual incidence subscheme. -/
theorem equation_zero_on_family :
    pullbackGlobalSections (inclusion K) (equationBundle K) (equationSection K)=0 :=
  (factorsThrough_iff_equation_zero K (inclusion K)).mp ⟨𝟙 _,by simp⟩

/-- The actual incidence ideal commutes with arbitrary scheme base change. -/
theorem ideal_baseChange {T : Scheme.{u}} (f : T ⟶ ambient K) :
    (ideal K).comap f=sectionZeroIdeal T
      ((Scheme.Modules.pullback f).obj (equationBundle K))
      (pullbackGlobalSections f (equationBundle K) (equationSection K)) :=
  (sectionZeroIdeal_pullback f (equationBundle K) 5 (equationSection K)).symm

/-- The actual family projection is proper. This uses the original native
Grassmannian projectivity and the actual closed inclusions, over every field. -/
instance familyProjection_isProper : IsProper (familyProjection K) := by
  have : IsProper (M9Native.LagrangianGrassmannian.grassmannianProjection K) :=
    AlgebraicGeometry.isProper_of_isProjectiveMorphism _
      (AlgebraicGeometry.Grassmannian.isProjectiveMorphism_schemeOver 3 6 (Spec (.of K)))
  have : IsProper (M9Native.LagrangianGrassmannian.projection K) := by
    change IsProper (M9Native.LagrangianGrassmannian.inclusion K ≫
      M9Native.LagrangianGrassmannian.grassmannianProjection K)
    infer_instance
  have : IsProper (toParameter K) :=
    inferInstanceAs (IsProper (pullback.snd
      (M9Native.LagrangianGrassmannian.projection K) (parameterProjection K)))
  exact inferInstanceAs (IsProper (inclusion K ≫ toParameter K))

end M9Native.LagrangianLinearSections
