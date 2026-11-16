module

public import M9StacksIntegration.MukaiPrimitiveCanonicalEvaluation
public import M9StacksIntegration.MukaiCanonicalExteriorCohomology
public import M9StacksIntegration.ProjectiveSectionIso
public import M9StacksIntegration.LagrangianPluckerEpimorphism
public import M9StacksIntegration.LagrangianPluckerGeneration
public import StacksFrontier.AlgebraicGeometry.ProjectiveFromSections.FreePresentation

/-!
# The actual primitive canonical linear system and its projective diagram

The primitive determinant sections are the image of the original third
exterior evaluation.  This leaf assembles their generation and actual
native projective comparison.  It makes no third-exterior surjectivity or
transversality assumption.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.MukaiPrimitiveCanonicalDiagram

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  MukaiLagrangianMap.lagrangianQuotient AlgebraicGeometry.Grassmannian.pullbackPresentation

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) (E : X.Modules)

theorem primitive_coordinate_finrank :
    finrank k (Module.Dual k (LagrangianField.Primitive k)) = 14 := by
  simpa only [Fintype.card_fin] using
    finrank_eq_card_basis (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis

/-- Rank-nullity gives the genuine lower bound on the actual kernel,
before any third-exterior surjectivity has been established. -/
theorem canonicalKernel_atLeast_five [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    [FiniteDimensional k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0)]
    (h9 : finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) = 9) :
    5 ≤ finrank k (LinearMap.ker (canonicalEvaluation k f E b c)) := by
  have h := (canonicalEvaluation k f E b c).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (canonicalEvaluation k f E b c))
  rw [primitive_coordinate_finrank k] at h
  rw [h9] at hr
  omega

/-- The all-test transported primitive quotient family is exactly the
original determinant evaluation family in the retained complete basis. -/
theorem determinantSections_eq_transported (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) :
    LagrangianPluckerQuotient.primitiveSection X k (LagrangianPlucker.coefficientMap k d.map)
        ((AlgebraicGeometry.Grassmannian.pullbackPresentation d.map (lagrangianQuotient k)).map ≫
          (d.restrictedIso k f E).hom) = determinantSections k f E b := by
  funext j
  refine (congrArg (fun κ => LagrangianPluckerQuotient.primitiveSection X k κ
    ((AlgebraicGeometry.Grassmannian.pullbackPresentation d.map (lagrangianQuotient k)).map ≫
      (d.restrictedIso k f E).hom) j) (d.coefficients k f E)).trans ?_
  refine (congrArg (fun q => LagrangianPluckerQuotient.primitiveSection X k
    (ExteriorEvaluation.baseRingMap k f) q j) (d.restrictedIso_triangle k f E)).trans ?_
  exact evaluation_primitiveSection k f E b j

/-- The image of the actual primitive third-exterior evaluation generates
the original determinant line.  No surjectivity onto determinant H0 is
used. -/
theorem determinantSectionMap_epi (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) : Epi (determinantSectionMap k f E b) := by
  change Epi (LagrangianPluckerQuotient.sectionMap X
    (Scheme.Modules.exteriorPower E (3 : ℤ)) (determinantSections k f E b))
  have hmap := congrArg (LagrangianPluckerQuotient.sectionMap X
    (Scheme.Modules.exteriorPower E (3 : ℤ)))
      (determinantSections_eq_transported k f E b d)
  exact (congrArg (fun q => Epi q) hmap).mp
    (LagrangianPluckerEpimorphism.primitiveSectionMap_epi k d.map (d.restrictedIso k f E))

theorem determinantSections_generatesStalks (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) :
    Stacks.ProjectiveFromSections.GeneratesStalks (determinantSections k f E b) :=
  LagrangianSectionGeneration.generatesStalks_of_sectionMap_epi X
    (Scheme.Modules.exteriorPower E (3 : ℤ)) (determinantSections k f E b)
    (determinantSectionMap_epi k f E b d)

theorem canonicalSectionMap_epi [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) : Epi (canonicalSectionMap k f E b c) := by
  let := determinantSectionMap_epi k f E b d
  have h : Epi (determinantSectionMap k f E b ≫ c.hom) := inferInstance
  exact (canonicalSectionMap_eq k f E b c).symm ▸ h

theorem canonicalSections_generatesStalks [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    Stacks.ProjectiveFromSections.GeneratesStalks (canonicalSections k f E b c) :=
  LagrangianSectionGeneration.generatesStalks_of_sectionMap_epi X
    (Stacks.Duality.dualizingSheafOverField f) (canonicalSections k f E b c)
    (canonicalSectionMap_epi k f E b c d)

omit [CharZero k] in
/-- Native rank three gives the actual invertibility needed by projective
evaluation of the determinant sections. -/
theorem determinantInvertible [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3] :
    Stacks.Ample.IsInvertibleModule X (Scheme.Modules.exteriorPower E (3 : ℤ)) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (3 : ℤ)) 1 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E 3 3
  exact Stacks.ProjectiveFromSections.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one _

omit [CharZero k] in
/-- The actual canonical determinant isomorphism transports actual
rank-one local freeness, hence actual invertibility, to the native
dualizing sheaf. -/
theorem canonicalInvertible [IsProper f] [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    Stacks.Ample.IsInvertibleModule X (Stacks.Duality.dualizingSheafOverField f) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (3 : ℤ)) 1 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E 3 3
  have h := Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso c
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff (Scheme.Modules.exteriorPower E (3 : ℤ)) 1).mpr
      inferInstance)
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff _ 1).mp h
  exact Stacks.ProjectiveFromSections.isInvertibleModule_of_isFiniteLocallyFreeOfRank_one _

/-- Transport to the actual canonical sheaf preserves the native
projective evaluation morphism; the generating proofs refer only to the
image linear system. -/
theorem canonicalProjectiveEvaluation_eq_determinant [IsProper f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hs : Stacks.ProjectiveFromSections.GeneratesStalks (determinantSections k f E b))
    (ht : Stacks.ProjectiveFromSections.GeneratesStalks (canonicalSections k f E b c)) :
    letI := determinantInvertible E
    letI := canonicalInvertible k f E c
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13)
        (determinantSections k f E b) hs f =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (X := X) (L := Stacks.Duality.dualizingSheafOverField f) (n := 13)
        (canonicalSections k f E b c) ht f := by
  let := determinantInvertible E
  let := canonicalInvertible k f E c
  exact ProjectiveSectionIso.toProjectiveSpaceOver_iso
    (X := X) (M := Scheme.Modules.exteriorPower E (3 : ℤ))
    (N := Stacks.Duality.dualizingSheafOverField f) (n := 13)
    (determinantSections k f E b) (canonicalSections k f E b c) hs ht c
    (fun j => (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f c.hom _).symm) f

section NativeProjectiveEvaluation
variable [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

/-- The actual projective morphism constructed from the now-proved
generating image linear system in the determinant line. -/
def determinantProjectiveMap (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) : X ⟶ projectiveSpaceOver 13 (Spec (.of k)) :=
  letI := determinantInvertible E
  Stacks.ProjectiveFromSections.toProjectiveSpaceOver
    (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13)
    (determinantSections k f E b) (determinantSections_generatesStalks k f E b d) f

@[reassoc (attr := simp)] theorem determinantProjectiveMap_over
    (b : Basis (Fin 6) k (H0 k f E)) (d : EvaluationDiagram k f E b) :
    determinantProjectiveMap k f E b d ≫ pullback.fst _ _ = f := by
  let := determinantInvertible E
  exact Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst
    (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13)
    (determinantSections k f E b) (determinantSections_generatesStalks k f E b d) f

/-- Canonical projective evaluation uses the original native dualizing
sheaf and the original canonical H0 sections transported by the given
actual determinant isomorphism. -/
def canonicalProjectiveMap [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) : X ⟶ projectiveSpaceOver 13 (Spec (.of k)) :=
  letI := canonicalInvertible k f E c
  Stacks.ProjectiveFromSections.toProjectiveSpaceOver
    (X := X) (L := Stacks.Duality.dualizingSheafOverField f) (n := 13)
    (canonicalSections k f E b c) (canonicalSections_generatesStalks k f E b c d) f

@[reassoc (attr := simp)] theorem canonicalProjectiveMap_over [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    canonicalProjectiveMap k f E b c d ≫ pullback.fst _ _ = f := by
  let := canonicalInvertible k f E c
  exact Stacks.ProjectiveFromSections.toProjectiveSpaceOver_fst
    (X := X) (L := Stacks.Duality.dualizingSheafOverField f) (n := 13)
    (canonicalSections k f E b c) (canonicalSections_generatesStalks k f E b c d) f

theorem canonicalProjectiveMap_eq_determinant [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    canonicalProjectiveMap k f E b c d = determinantProjectiveMap k f E b d := by
  exact (canonicalProjectiveEvaluation_eq_determinant k f E b c
    (determinantSections_generatesStalks k f E b d)
    (canonicalSections_generatesStalks k f E b c d)).symm

/-- The target is literally the projective space on the dual of the
actual primitive exterior kernel, as in the native primitive Plucker map. -/
def canonicalModuleProjectiveMap [IsProper f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    X ⟶ projectiveSpaceOfModule k (Module.Dual k (LagrangianField.Primitive k)) :=
  canonicalProjectiveMap k f E b c d ≫ (LagrangianPluckerLinear.primitiveProjectiveIso k).hom

/-- The actual normalized LG map followed by the actual primitive Plucker
map is precisely native projective evaluation of the original determinant
linear system. -/
theorem lagrangian_eq_determinantProjectiveMap (b : Basis (Fin 6) k (H0 k f E))
    (d : EvaluationDiagram k f E b) :
    d.map ≫ LagrangianPlucker.primitivePlucker k = determinantProjectiveMap k f E b d := by
  let := determinantInvertible E
  let s := LagrangianPluckerQuotient.primitiveSection X k (LagrangianPlucker.coefficientMap k d.map)
    ((AlgebraicGeometry.Grassmannian.pullbackPresentation d.map (lagrangianQuotient k)).map ≫
      (d.restrictedIso k f E).hom)
  have hs : Stacks.ProjectiveFromSections.GeneratesStalks s :=
    LagrangianPluckerEpimorphism.primitiveSection_generatesStalks k d.map (d.restrictedIso k f E)
  calc
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13)
        s hs (d.map ≫ LagrangianGrassmannian.projection k) :=
      LagrangianPluckerGeneration.comp_primitivePlucker_eq_toProjectiveSpaceOver k d.map
        (d.restrictedIso k f E)
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13) s hs f :=
      congrArg (fun base => Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13) s hs base) d.over_base
    _ = Stacks.ProjectiveFromSections.toProjectiveSpaceOver
        (X := X) (L := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13)
        (determinantSections k f E b) (determinantSections_generatesStalks k f E b d) f :=
      ProjectiveSectionIso.toProjectiveSpaceOver_iso
        (X := X) (M := Scheme.Modules.exteriorPower E (3 : ℤ))
        (N := Scheme.Modules.exteriorPower E (3 : ℤ)) (n := 13)
        s (determinantSections k f E b) hs (determinantSections_generatesStalks k f E b d)
        (Iso.refl _) (fun j => congrFun (determinantSections_eq_transported k f E b d) j) f
    _ = _ := rfl

theorem lagrangian_eq_canonicalProjectiveMap [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    d.map ≫ LagrangianPlucker.primitivePlucker k = canonicalProjectiveMap k f E b c d :=
  (lagrangian_eq_determinantProjectiveMap k f E b d).trans
    (canonicalProjectiveMap_eq_determinant k f E b c d).symm

/-- The commutative diagram has exactly the native primitive projective
coordinate module `Dual (ker contraction)`. -/
theorem lagrangian_eq_canonicalModuleProjectiveMap [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    d.map ≫ LagrangianPluckerLinear.primitivePlucker k =
      canonicalModuleProjectiveMap k f E b c d := by
  change d.map ≫ (LagrangianPlucker.primitivePlucker k ≫
    (LagrangianPluckerLinear.primitiveProjectiveIso k).hom) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun p => p ≫ (LagrangianPluckerLinear.primitiveProjectiveIso k).hom)
      (lagrangian_eq_canonicalProjectiveMap k f E b c d))

/-- The actual ambient hyperplane line restricts to the actual original
canonical sheaf, through the genuine universal determinant line. -/
def canonicalLagrangianO1Iso [IsProper f]
    (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) :
    (Scheme.Modules.pullback (d.map ≫ LagrangianPlucker.primitivePlucker k)).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (Spec (.of k))) ≅
        Stacks.Duality.dualizingSheafOverField f :=
  ((Scheme.Modules.pullbackComp d.map (LagrangianPlucker.primitivePlucker k)).app
    (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (Spec (.of k)))).symm ≪≫
      (Scheme.Modules.pullback d.map).mapIso (LagrangianPluckerGeneration.determinantLineO1Iso k) ≪≫
        d.canonicalIso k f E c

end NativeProjectiveEvaluation

section ActualCurve
variable [IsAlgClosed k] [IsProper f] [IsCurve k f]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

omit [IsAlgClosed k] [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3] in
/-- For the actual genus-nine canonical cohomology, the true kernel has
dimension at least five without any supplied section-count premise. -/
theorem curve_canonicalKernel_atLeast_five (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) :
    5 ≤ finrank k (LinearMap.ker (canonicalEvaluation k f E b c)) := by
  have h9 : finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) = 9 :=
    (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le).trans hg
  let : FiniteDimensional k
      (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  exact canonicalKernel_atLeast_five k f E b c h9

/-- The actual canonical exterior cohomology theorem discharges the
fourteen-section input for a proper genus-nine curve. -/
def normalizedEvaluation_of_canonical
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : finrank k (H0 k f E) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    NormalizedEvaluation k f E := by
  letI : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f E 3
  letI : FiniteDimensional k (H0 k f E) :=
    finiteDimensional_cohomologyOverField_of_isProper k f E 0
  letI : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (2 : ℤ)) 3 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower E 3 2
  letI : (Scheme.Modules.exteriorPower E (2 : ℤ)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
      (Scheme.Modules.exteriorPower E (2 : ℤ)) 3
  letI : FiniteDimensional k
      (cohomologyOverField k f (Scheme.Modules.exteriorPower E (2 : ℤ)) 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k f (Scheme.Modules.exteriorPower E (2 : ℤ)) 0
  exact normalizedEvaluation k f E hgen h6
    (MukaiCanonicalExteriorCohomology.curve_canonical_exterior_h0_fourteen k f E c hg h6) hsemi

/-- The complete application starts with the original canonical bundle
data.  The normalized basis, LG quotient, native projective diagram,
canonical hyperplane line and generating image system are all constructed.
There is no supplied classifier, third-exterior surjectivity or map
comparison premise. -/
theorem exists_canonicalPrimitiveDiagram
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : finrank k (H0 k f E) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    ∃ n : NormalizedEvaluation k f E,
      Epi (canonicalSectionMap k f E n.basis c) ∧
      n.diagram.map ≫ LagrangianPluckerLinear.primitivePlucker k =
        canonicalModuleProjectiveMap k f E n.basis c n.diagram ∧
      Nonempty ((Scheme.Modules.pullback
          (n.diagram.map ≫ LagrangianPlucker.primitivePlucker k)).obj
            (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (Spec (.of k))) ≅
              Stacks.Duality.dualizingSheafOverField f) ∧
      5 ≤ finrank k (LinearMap.ker (canonicalEvaluation k f E n.basis c)) := by
  let n := normalizedEvaluation_of_canonical k f E c hg hgen h6 hsemi
  exact ⟨n, canonicalSectionMap_epi k f E n.basis c n.diagram,
    lagrangian_eq_canonicalModuleProjectiveMap k f E n.basis c n.diagram,
    ⟨canonicalLagrangianO1Iso k f E n.basis c n.diagram⟩,
    curve_canonicalKernel_atLeast_five k f E n.basis c hg⟩

end ActualCurve

end M9Native.MukaiPrimitiveCanonicalDiagram
