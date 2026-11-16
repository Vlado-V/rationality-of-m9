module

public import M9StacksIntegration.LagrangianTransverseCanonical
public import M9StacksIntegration.LagrangianPluckerGeneration
public import M9StacksIntegration.LineFramePullback

/-!
# The original transverse cut has a genuine canonical projective embedding

The morphism is the original cut immersion followed by the original
primitive Plücker closed immersion. The native hyperplane line is
identified with the original canonical line through actual pullback
composition, the original section-pinned Plücker comparison, and actual
adjunction. No genus, canonical-embedding or pencil hypothesis is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.LagrangianTransverseProjectiveCanonical

open LagrangianTransverseRestriction LagrangianPluckerQuotient

private theorem iso_trans_coordinate {T : Scheme.{u}} {A B C : T.Modules}
    (e : A ≅ B) (c : B ≅ C) (s : Γ(A, ⊤)) (t : Γ(B, ⊤))
    (h : e.hom.app ⊤ s = t) : (e ≪≫ c).hom.app ⊤ s = c.hom.app ⊤ t :=
  congrArg (c.hom.app ⊤) h

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- The actual original projective morphism of the original cut. -/
def projectiveMap : curve K M ⟶ projectiveSpaceOver 13 (Spec (.of K)) :=
  inclusion K M ≫ LagrangianPlucker.primitivePlucker K

instance projectiveMap_isClosedImmersion : IsClosedImmersion (projectiveMap K M) := by
  let : IsClosedImmersion (inclusion K M) := IteratedLineSectionCuts.simultaneousCut_closed _ _
  let : IsClosedImmersion (LagrangianPlucker.primitivePlucker K) :=
    LagrangianPluckerClosed.primitivePlucker_isClosedImmersion K
  dsimp [projectiveMap]
  infer_instance

omit [IsAlgClosed K] [IsIntegral (curve K M)]
  [SmoothOfRelativeDimension 1 (curveProjection K M)] in
theorem projectiveMap_overBase :
    projectiveMap K M ≫ Stacks.Tag01VT.projectiveSpaceHom 13 (Spec (.of K)) =
      curveProjection K M := by
  exact congrArg (fun t => inclusion K M ≫ t) (LagrangianPlucker.primitivePlucker_projection K)

abbrev hyperplaneLine : (projectiveSpaceOver 13 (Spec (.of K))).Modules :=
  Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 13 (Spec (.of K))

def coordinateSection (j : Fin 14) : Γ(hyperplaneLine K, ⊤) :=
  pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse 13 (Spec (.of K)))
    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse.{u} 13)
    (Stacks.TwistPullbackPinned.coordGlobalSection.{u} 13 j)

/-- The original O(1) comparison before canonical transport. -/
def determinantO1Iso :
    (Scheme.Modules.pullback (projectiveMap K M)).obj (hyperplaneLine K) ≅
      LagrangianPrimitiveRestriction.restrictedLine K (inclusion K M) :=
  ((Scheme.Modules.pullbackComp (inclusion K M) (LagrangianPlucker.primitivePlucker K)).app
      (hyperplaneLine K)).symm ≪≫
    (Scheme.Modules.pullback (inclusion K M)).mapIso
      (LagrangianPluckerGeneration.determinantLineO1Iso K)

/-- Every original coordinate is retained before canonical transport. -/
theorem determinantO1Iso_coordinate (j : Fin 14) :
    (determinantO1Iso K M).hom.app ⊤
      (pullbackGlobalSections (projectiveMap K M) (hyperplaneLine K) (coordinateSection K j)) =
      LagrangianPrimitiveRestriction.restrictedSection K (inclusion K M) j := by
  change (((Scheme.Modules.pullback (inclusion K M)).map
      (LagrangianPluckerGeneration.determinantLineO1Iso K).hom).app ⊤
      (((Scheme.Modules.pullbackComp (inclusion K M)
        (LagrangianPlucker.primitivePlucker K)).inv.app (hyperplaneLine K)).app ⊤
        (pullbackGlobalSections (inclusion K M ≫ LagrangianPlucker.primitivePlucker K)
          (hyperplaneLine K) (coordinateSection K j)))) = _
  rw [LineFramePullback.pullbackComp_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  exact congrArg (fun s => pullbackGlobalSections (inclusion K M) (determinantLine K) s)
    (LagrangianPluckerGeneration.determinantLineO1Iso_coordinate K j)

/-- The genuine section-pinned O(1) comparison, with original native
canonical target. -/
def canonicalO1Iso (hM : Function.Surjective M.mulVec) :
    (Scheme.Modules.pullback (projectiveMap K M)).obj (hyperplaneLine K) ≅
      Stacks.Duality.dualizingSheafOverField (curveProjection K M) :=
  determinantO1Iso K M ≪≫ LagrangianTransverseCanonical.restrictedCanonicalIso K M hM

/-- Every original homogeneous coordinate is retained by the actual
canonical O(1) comparison. -/
theorem canonicalO1Iso_coordinate (hM : Function.Surjective M.mulVec) (j : Fin 14) :
    (canonicalO1Iso K M hM).hom.app ⊤
      (pullbackGlobalSections (projectiveMap K M) (hyperplaneLine K) (coordinateSection K j)) =
      (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM).hom.app ⊤
        (LagrangianPrimitiveRestriction.restrictedSection K (inclusion K M) j) :=
  iso_trans_coordinate (determinantO1Iso K M)
    (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM) _ _
      (determinantO1Iso_coordinate K M j)

/-- The actual fourteen-coordinate canonical restriction is complete
when the actual genus is nine; its surjectivity is the checked original
five-cut restriction theorem. -/
theorem canonicalRestriction_surjective (hM : Function.Surjective M.mulVec)
    (hg : genus (curveProjection K M) = 9) :
    Function.Surjective (LagrangianPrimitiveRestriction.canonicalRestriction K
      (curveProjection K M) (inclusion K M)
      (LagrangianTransverseCanonical.restrictedCanonicalIso K M hM)) :=
  LagrangianTransverseRestriction.canonicalRestriction_surjective K M hM _ hg

end M9Native.LagrangianTransverseProjectiveCanonical
