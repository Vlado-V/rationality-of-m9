module

public import M9StacksIntegration.SpecFieldStalkSections
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine

/-! Genuine field-point pullbacks of local sections, their naturality,
and their exact value under the actual pullback-stalk comparison. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u

namespace M9Native.SpecFieldPullbackSections

open SpecFieldStalkSections

variable (K : Type u) [Field K] {Y : Scheme.{u}} (p : space K ⟶ Y)

def scalarLinearEquiv : K ≃ₗ[K] localRing K :=
  ({ __ := scalarStalkEquiv K
     commutes' := scalarStalkEquiv_apply K } : K ≃ₐ[K] localRing K).toLinearEquiv

theorem stalkScalarTower (M : (space K).Modules) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule M (point K)
    letI := moduleStalk K M
    IsScalarTower K (localRing K) (M.presheaf.stalk (point K)) := by
  letI := Stacks.ModuleStalkSpecialization.stalkModule M (point K)
  letI := moduleStalk K M
  exact ⟨fun a b m => mul_smul (scalarStalkMap K a) b m⟩

def preimageTop (U : Y.Opens) (hp : p.base (point K) ∈ U) : ⊤ ≤ p ⁻¹ᵁ U := by
  intro z _
  change p.base z ∈ U
  have hz : z = point K := Subsingleton.elim _ _
  simpa only [hz] using hp

/-- The actual pullback unit on a section, restricted to the whole field spectrum. -/
def pulledSection (M : Y.Modules) (U : Y.Opens) (hp : p.base (point K) ∈ U)
    (s : Γ(M, U)) : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj M) :=
  Scheme.Modules.pullbackSection p M U ⊤ (preimageTop K p U hp) s

theorem pulledSection_naturality {M N : Y.Modules} (t : M ⟶ N) (U : Y.Opens)
    (hp : p.base (point K) ∈ U) (s : Γ(M, U)) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map t)).hom
        (pulledSection K p M U hp s) =
      pulledSection K p N U hp (t.app U s) :=
  Scheme.Modules.pullbackSection_naturality p t U ⊤ (preimageTop K p U hp) s

/-- The authentic comparison takes the actual pullback of a local section
to one tensor its original germ. -/
theorem baseChange_pulledSection (M : Y.Modules) (U : Y.Opens)
    (hp : p.base (point K) ∈ U) (s : Γ(M, U)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule M (p.base (point K))
    letI := Stacks.ModuleStalkSpecialization.stalkModule
      ((Scheme.Modules.pullback p).obj M) (point K)
    letI : Algebra (Y.presheaf.stalk (p.base (point K))) (localRing K) :=
      (p.stalkMap (point K)).hom.toAlgebra
    Stacks.Divisors.pullbackStalkBaseChange p M (point K)
      (sectionsStalkEquiv K ((Scheme.Modules.pullback p).obj M)
        (pulledSection K p M U hp s)) =
      (1 : localRing K) ⊗ₜ[Y.presheaf.stalk (p.base (point K))]
        (M.presheaf.germ U (p.base (point K)) hp s) := by
  letI := Stacks.ModuleStalkSpecialization.stalkModule M (p.base (point K))
  letI := Stacks.ModuleStalkSpecialization.stalkModule
    ((Scheme.Modules.pullback p).obj M) (point K)
  letI : Algebra (Y.presheaf.stalk (p.base (point K))) (localRing K) :=
    (p.stalkMap (point K)).hom.toAlgebra
  change Stacks.Divisors.pullbackStalkBaseChange p M (point K)
    (((Scheme.Modules.pullback p).obj M).presheaf.germ ⊤ (point K) trivial
      (((Scheme.Modules.pullback p).obj M).presheaf.map
        (homOfLE (preimageTop K p U hp)).op
        (Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections p M U s))) = _
  rw [((Scheme.Modules.pullback p).obj M).presheaf.germ_res_apply]
  exact Stacks.Divisors.pullbackStalkBaseChange_germ p M (point K) U hp s

end M9Native.SpecFieldPullbackSections
