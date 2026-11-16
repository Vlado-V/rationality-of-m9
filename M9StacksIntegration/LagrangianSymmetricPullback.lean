module

public import M9StacksIntegration.SymmetricSquareLocalSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackSymmetric
public import StacksFrontier.AlgebraicGeometry.Modules.ZariskiRingedToposHom

/-! Canonical symmetric powers commute with the original scheme pullback. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.LagrangianSymmetricPullback

variable {X Y : Scheme.{u}}

/-- The original native functorial morphism of symmetric powers. -/
def symmetricMap {F G : X.Modules} (φ : F ⟶ G) (n : ℤ) :
    (Scheme.Modules.symmetricAlgebra X F).piece n ⟶
      (Scheme.Modules.symmetricAlgebra X G).piece n :=
  (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).pieceMap
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X G) φ n

/-- An actual bundle isomorphism induces the canonical actual symmetric
power isomorphism, as a consequence of the universal property. -/
def symmetricMapIso {F G : X.Modules} (e : F ≅ G) (n : ℤ) :
    (Scheme.Modules.symmetricAlgebra X F).piece n ≅
      (Scheme.Modules.symmetricAlgebra X G).piece n := by
  letI : IsIso (symmetricMap e.hom n) :=
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X F).isIso_pieceMap
      (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X G) e.hom inferInstance n
  exact asIso (symmetricMap e.hom n)

/-- First use the genuine ringed-topos pullback and its actual graded
adjunction; every degree comparison is proved invertible by the native
symmetric-algebra universal property. -/
def fourFieldSymmetricPullbackIso (g : X ⟶ Y) (F : Y.Modules) (n : ℤ) :
    (Scheme.Modules.symmetricAlgebra X
      (g.zariskiRingedToposModulesHom.pullbackModules.obj F)).piece n ≅
    g.zariskiRingedToposModulesHom.pullbackModules.obj
      ((Scheme.Modules.symmetricAlgebra Y F).piece n) := by
  let f := g.zariskiRingedSiteHom.toRingedToposHom
  let M := g.zariskiRingedToposModulesHom.pullbackModules.obj F
  let ι := Scheme.Modules.symmetricAlgebraGen Y F
  let ι' := Scheme.Modules.symmetricAlgebraGen X M
  have hAc : ∀ V (x y : ((Scheme.Modules.symmetricAlgebra Y F).piece 1).val.obj V),
      ((Scheme.Modules.symmetricAlgebra Y F).mul 1 1).app V x y=
        ((Scheme.Modules.symmetricAlgebra Y F).mul 1 1).app V y x :=
    fun V x y => eq_of_heq (Scheme.Modules.symmetricAlgebra_mul_comm Y F 1 1 V x y)
  have hSc : ∀ V (x y : ((Scheme.Modules.symmetricAlgebra X M).piece 1).val.obj V),
      ((Scheme.Modules.symmetricAlgebra X M).mul 1 1).app V x y=
        ((Scheme.Modules.symmetricAlgebra X M).mul 1 1).app V y x :=
    fun V x y => eq_of_heq (Scheme.Modules.symmetricAlgebra_mul_comm X M 1 1 V x y)
  let c := Stacks.Sheaves.GradedAlgebraEssentiallySmall.symmetricPullbackHom f ι hAc ι'
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X M)
  letI : IsIso (c.app n) :=
    Stacks.Sheaves.GradedAlgebraEssentiallySmall.isIso_symmetricPullbackHom_app f ι
      (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra Y F) hAc ι'
      (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra X M) hSc n
  exact asIso (c.app n)

/-- The canonical actual symmetric-power pullback isomorphism for a
morphism of schemes. Both identifications with ringed-space pullback
are the proved native adjoint-comparison isomorphisms. -/
def symmetricPullbackIso (g : X ⟶ Y) (F : Y.Modules) (n : ℤ) :
    (Scheme.Modules.symmetricAlgebra X ((Scheme.Modules.pullback g).obj F)).piece n ≅
      (Scheme.Modules.pullback g).obj ((Scheme.Modules.symmetricAlgebra Y F).piece n) :=
  symmetricMapIso (g.zariskiPullbackModulesIso.app F).symm n ≪≫
    fourFieldSymmetricPullbackIso g F n ≪≫
      g.zariskiPullbackModulesIso.app ((Scheme.Modules.symmetricAlgebra Y F).piece n)

end M9Native.LagrangianSymmetricPullback
