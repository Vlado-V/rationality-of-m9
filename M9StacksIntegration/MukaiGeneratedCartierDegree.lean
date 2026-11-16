module

public import M9StacksIntegration.MukaiDivisorCokernel
public import M9StacksIntegration.MukaiGeneratedImageRank
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological

/-!
# Degree of the actual generated Cartier modification

Tensor-flatness proves that the original inclusion Q → Q(D) is a
monomorphism. The cokernel of Q in the literal generated image is a
quotient of O_D, so its contribution to the degree is at most length(D).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.BraidedCategory

universe u

namespace M9Native.MukaiGeneratedCartierImage

@[instance_reducible] local instance degreeModulesMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorMonoidal X.sheaf.obj X.ringCatSheaf.property

@[instance_reducible] local instance degreeModulesSymmetric (X : Scheme.{u}) :
    SymmetricCategory X.Modules :=
  Stacks.SheafOfModules.sheafTensorSymmetric X.sheaf.obj X.ringCatSheaf.property

variable {X : Scheme.{u}}

/-- A finite locally free left tensor factor preserves actual monomorphisms. -/
theorem mono_whiskerLeft (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q]
    {A B : X.Modules} (c : A ⟶ B) [Mono c] : Mono (Q ◁ c) := by
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj Q
  letI : T.PreservesMonomorphisms :=
    (SheafOfModules.sheafTensorRight_exact_iff_preservesMonomorphisms X.sheaf Q).mp
      (SheafOfModules.isFlat_of_isFiniteLocallyFree Q inferInstance)
  have hm : Mono (T.map c) := T.map_mono c
  haveI : Mono (c ▷ Q) := by
    exact hm
  haveI : Mono (Q ◁ c ≫ (β_ Q B).hom) := by
    rw [braiding_naturality_right]
    infer_instance
  exact mono_of_mono (Q ◁ c) (β_ Q B).hom

/-- The actual canonical inclusion of the bundle into its positive twist is mono. -/
theorem inclusion_mono (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u,u,u} Q] : Mono (inclusion D Q) := by
  letI : Mono (Stacks.Divisors.canonicalSectionHom D) :=
    Stacks.Divisors.canonicalSection_isRegular D
  letI := mono_whiskerLeft Q (Stacks.Divisors.canonicalSectionHom D)
  dsimp only [inclusion, MukaiGeneratedImage.twistInclusion]
  infer_instance

/-- The actual positive Cartier twist retains rank two. -/
theorem twist_rank_two (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) 2 := by
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.invertibleSheaf' D) := Stacks.Divisors.invertibleSheaf_isInvertible D
  letI := SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X
    (Stacks.Divisors.invertibleSheaf' D)
  exact SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf X Q
    (Stacks.Divisors.invertibleSheaf' D) 2 1

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
variable [IsProper f] [IsCurve k f] [Smooth f]
include f

/-- The literal generated image is rank two; no rank of the image is assumed. -/
theorem generatedImage_rank_two (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (a : MukaiBundle.structureModule X ⟶
      Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D)) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (MukaiGeneratedImage.generatedImage (inclusion D Q) a) 2 := by
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  letI := twist_rank_two D Q
  letI := inclusion_mono D Q
  exact MukaiGeneratedImage.rank_two_on_smooth_curve k f (inclusion D Q) a

/-- The degree increase of the actual image is bounded by the actual divisor length. -/
theorem degree_generated_le (D : X.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (Q : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} Q 2]
    (a : MukaiBundle.structureModule X ⟶
      Scheme.Modules.tensorObj Q (Stacks.Divisors.invertibleSheaf' D))
    (d : ℕ) (hlen : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = d) :
    letI := generatedImage_rank_two f D Q a
    curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le
      (MukaiGeneratedImage.generatedImage (inclusion D Q) a) 2 ≤
        curveDegree k f (IsCurve.topologicalKrullDim_eq_one f).le Q 2 + d := by
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree Q 2
  letI := inclusion_mono D Q
  letI := generatedImage_rank_two f D Q a
  letI := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    (MukaiGeneratedImage.generatedImage (inclusion D Q) a) 2
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : Q.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X Q
  letI : (MukaiBundle.structureModule X).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  letI : (MukaiGeneratedImage.generatedImage (inclusion D Q) a).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X _
  letI : (MukaiGeneratedImage.quotient (inclusion D Q) a).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel inferInstance inferInstance _
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.negativeTwist' D) := Stacks.Divisors.isInvertible_negativeTwist D
  letI : (Stacks.Divisors.negativeTwist' D).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X _
  letI : (MukaiDivisorCokernel.divisorCokernel D).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel inferInstance inferInstance _
  let j := MukaiGeneratedImage.subobjectMap (inclusion D Q) a
  letI : Mono j := by dsimp [j]; infer_instance
  letI : (cokernel j).IsCoherent :=
    Stacks.AlgebraicGeometry.ProperMapping.isCoherent_cokernel inferInstance inferInstance j
  have hS : (ShortComplex.cokernelSequence j).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact j
      mono_f := by dsimp [ShortComplex.cokernelSequence]; infer_instance }
  have hD := topologicalKrullDim_divisorSubscheme_le_zero
    (IsCurve.topologicalKrullDim_eq_one f).le D
  letI : Epi (divisorQuotientMap D Q a) := divisorQuotientMap_epi D Q a
  exact MukaiGeneratedImage.degree_le_of_quotient f
    (IsCurve.topologicalKrullDim_eq_one f).le hS (divisorQuotientMap D Q a)
    (MukaiDivisorCokernel.divisorCokernel_support D hD) d
    (le_of_eq ((MukaiDivisorCokernel.divisorCokernel_h0 f D hD).trans hlen))

end M9Native.MukaiGeneratedCartierImage
