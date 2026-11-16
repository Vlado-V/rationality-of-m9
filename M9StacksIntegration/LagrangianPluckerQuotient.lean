module
public import M9StacksIntegration.LagrangianDeterminantSections
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
universe u
namespace M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianMatrixChart M9Native.LagrangianGrassmannian
open M9Native.LagrangianDeterminantSections

variable (X : Scheme.{u}) (K : Type u) [Field K]

/-- The actual determinant sections in the fixed primitive coordinate convention. -/
def primitiveSection (κ : K →+* Γ(X,⊤)) {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (j : Fin 14) :
    Γ(Scheme.Modules.exteriorPower Q 3,⊤) :=
  ∑ i : Fin 20, κ (M9Native.LagrangianField.projectionMatrix K j i) •
    minorSection X q (M9Native.LagrangianRing.triple i)

theorem primitiveSection_postcomp (κ : K →+* Γ(X,⊤)) {Q Q' : X.Modules}
    (q : freeOn X 6 ⟶ Q) (e : Q ⟶ Q') (j : Fin 14) :
    (exteriorPowerMap X e 3).app ⊤ (primitiveSection X K κ q j)=
      primitiveSection X K κ (q ≫ e) j := by
  simp only [primitiveSection,map_sum,Scheme.Modules.Hom.app_smul,minorSection_postcomp]


theorem primitiveSection_freeCoordinates (κ : K →+* Γ(X,⊤))
    (q : freeOn X 6 ⟶ freeOn X 3) (j : Fin 14) :
    freeDeterminantCoordinates X (primitiveSection X K κ q j)=
      M9Native.LagrangianRing.rowFourteen Γ(X,⊤) κ (Stacks.FreeSheafMatrix.toMatrix q) j := by
  simp only [primitiveSection,map_sum,map_smul,minorSection_freeCoordinates,
    M9Native.LagrangianRing.rowFourteen,Matrix.mulVec_apply_eq_sum,Matrix.map_apply,
    M9Native.LagrangianRing.rowTwenty_eq_minor,smul_eq_mul]


end M9Native.LagrangianPluckerQuotient

namespace M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianMatrixChart M9Native.LagrangianGrassmannian
open M9Native.LagrangianDeterminantSections
open AlgebraicGeometry.Grassmannian

/-- The actual morphism from a finite free sheaf defined by actual global sections.
This is the literal coproduct construction of native freeHomOfBasis. -/
def sectionMap (X : Scheme.{u}) (Q : X.Modules) {r : ℕ} (s : Fin r → Γ(Q,⊤)) :
    freeOn X r ⟶ Q :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin r)))
    (fun i => Scheme.Modules.unitHomEquivTop Q (s i.down))

theorem sectionMap_component (X : Scheme.{u}) (Q : X.Modules) {r : ℕ}
    (s : Fin r → Γ(Q,⊤)) (i : Fin r) :
    SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up i) ≫ sectionMap X Q s=
      Scheme.Modules.unitHomEquivTop Q (s i) :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin r))) _ (ULift.up i)

variable (K : Type u) [Field K]

/-- The actual quotient on LG, pulled back from the native universal quotient. -/
abbrev quotientOnLG : QuotientPresentation (space K) 3 6 :=
  pullbackPresentation (inclusion K) (universalQuotient K)

instance quotientOnLG_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (quotientOnLG K).target 3 := by
  simpa using (quotientOnLG K).finiteLocallyFree

/-- The actual determinant line of the universal quotient on LG. -/
abbrev determinantLine : (space K).Modules :=
  Scheme.Modules.exteriorPower (quotientOnLG K).target 3

instance determinantLine_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (determinantLine K) 1 := by
  simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower (quotientOnLG K).target 3 3

/-- Invertibility is proved from the actual rank-three quotient. -/
theorem determinantLine_invertible :
    Stacks.SheafOfModules.IsInvertible (space K).sheaf.obj (structureSheaf (space K).sheaf).property
      (determinantLine K) :=
  Scheme.Modules.isInvertible_exteriorPower_self (quotientOnLG K).target 3


/-- The fourteen actual global determinant sections, in the frozen primitive basis. -/
def primitiveSections : Fin 14 → Γ(determinantLine K,⊤) :=
  primitiveSection (space K) K (M9Native.LagrangianPlucker.coefficientMap K (𝟙 _)) (quotientOnLG K).map

/-- The actual morphism to the determinant line defined by these fourteen sections. -/
def primitiveDeterminantMap : freeOn (space K) 14 ⟶ determinantLine K :=
  sectionMap (space K) (determinantLine K) (primitiveSections K)

theorem primitiveDeterminantMap_component (j : Fin 14) :
    SheafOfModules.ιFree (R:=(space K).ringCatSheaf) (ULift.up j) ≫ primitiveDeterminantMap K=
      Scheme.Modules.unitHomEquivTop (determinantLine K) (primitiveSections K j) :=
  sectionMap_component (space K) (determinantLine K) (primitiveSections K) j

end M9Native.LagrangianPluckerQuotient
