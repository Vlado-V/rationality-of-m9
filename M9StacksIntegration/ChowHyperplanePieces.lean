module

public import M9StacksIntegration.ChowSplitLineProjectiveZero

/-! The actual hyperplane-zero isomorphism is independent of the proof
of quasi-coherence of the symmetric pieces. Naming that proof retains
the original Chow model on both sides of later section identities. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.RelativeProj
universe u
namespace M9Native.ChowHyperplanePieces

variable {X : Scheme.{u}} (F : X.Modules) (hqc : Stacks.SymGraded.IsQuasicoherentPieces F)

abbrev ambient := (Stacks.SymGraded.schemeProjectiveBundle F hqc).scheme
abbrev projection : ambient F hqc ⟶ X := Stacks.SymGraded.schemeProjectiveBundleToBase F hqc
abbrev twist : (ambient F hqc).Modules :=
  Stacks.ProjectiveBundleSplitting.tautologicalTwist F hqc
abbrev tautological : (Scheme.Modules.pullback (projection F hqc)).obj F ⟶ twist F hqc :=
  Stacks.ProjectiveBundleSplitting.tautologicalMap F hqc

def originalSection (σ : Scheme.unitModule X ⟶ F) : Γ(twist F hqc,⊤) :=
  (tautological F hqc).app ⊤
    (pullbackGlobalSections (projection F hqc) F (σ.app ⊤ (1 : Γ(X,⊤))))

def zeroIdeal (σ : Scheme.unitModule X ⟶ F) : (ambient F hqc).IdealSheafData :=
  SectionZeroIdealFactorization.sectionZeroIdeal (ambient F hqc) (twist F hqc)
    (originalSection F hqc σ)

variable {F} {G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
  (q : F ⟶ G) [Epi q] (S : UnitSplitting q)
  (hG : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 G)

/-- Only proof irrelevance of the actual quasi-coherence proposition is
used; the zero scheme and section are genuine throughout. -/
def zeroIsoBase (hqc : Stacks.SymGraded.IsQuasicoherentPieces F) :
    (zeroIdeal F hqc S.σ).subscheme ≅ X := by
  have he : Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F = hqc :=
    Subsingleton.elim _ _
  cases he
  exact ChowSplitLineProjectiveZero.zeroIsoBase q S hG

theorem zeroIsoBase_hom (hqc : Stacks.SymGraded.IsQuasicoherentPieces F) :
    (zeroIsoBase q S hG hqc).hom = (zeroIdeal F hqc S.σ).subschemeι ≫ projection F hqc := by
  have he : Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent F = hqc :=
    Subsingleton.elim _ _
  cases he
  exact ChowSplitLineProjectiveZero.zeroIsoBase_hom q S hG

include hG in
theorem zeroProjection_isIso (hqc : Stacks.SymGraded.IsQuasicoherentPieces F) :
    IsIso ((zeroIdeal F hqc S.σ).subschemeι ≫ projection F hqc) := by
  rw [← zeroIsoBase_hom q S hG hqc]
  infer_instance

end M9Native.ChowHyperplanePieces
