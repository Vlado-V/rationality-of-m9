module

public import M9StacksIntegration.FormallySmoothDerivationExtension
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.TangentMapDual

/-!
# Surjectivity of the actual canonical tangent map at a smooth point

The native tangent map is defined through actual derivations of local
rings. A genuine formally smooth stalk map extends every such derivation.
Its extension still annihilates the actual base stalk, by the literal
commuting triangle. Thus the original native tangent map is surjective.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry

namespace M9Native.SmoothTangentMapSurjective
universe u
variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S)
  (h : f ≫ q = p) (x : X) [IsIso (f.residueFieldMap x)]

/-- A formally smooth actual stalk map makes the actual canonical map
on tangent derivations surjective, retaining the real base triangle. -/
theorem tangentDerivationMap_surjective
    (hsm : (f.stalkMap x).hom.FormallySmooth) :
    Function.Surjective (tangentDerivationMap f p q x h) := by
  subst h
  let B := ToType (Y.presheaf.stalk (f x))
  let C := ToType (X.presheaf.stalk x)
  let kB := ToType (Y.residueField (f x))
  let kC := ToType (X.residueField x)
  let : Module B kB := Module.compHom _ (Y.residue (f x)).hom
  let : Module C kC := Module.compHom _ (X.residue x).hom
  let : Algebra B C := (f.stalkMap x).hom.toAlgebra
  let : Module B kC := Module.compHom _ ((X.residue x).hom.comp (f.stalkMap x).hom)
  let : IsScalarTower B C kC := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Algebra.FormallySmooth B C := hsm.toAlgebra
  let v : kB →ₗ[B] kC :=
    { toFun := (f.residueFieldMap x).hom
      map_add' := (f.residueFieldMap x).hom.map_add
      map_smul' := fun b z => by
        change (f.residueFieldMap x).hom (Y.residue (f x) b * z) =
          X.residue x (f.stalkMap x b) * (f.residueFieldMap x).hom z
        rw [map_mul]
        exact congrArg (fun c => c * (f.residueFieldMap x).hom z)
          (congrArg (fun g : Y.presheaf.stalk (f x) ⟶ X.residueField x => g b)
            (Scheme.residue_residueFieldMap f x)) }
  intro D
  let D' : Derivation ℤ B kC := v.compDer D.val
  obtain ⟨E, hE⟩ := FormallySmoothDerivationExtension.exists_extension ℤ B C kC D'
  refine ⟨⟨E, ?_⟩, ?_⟩
  · intro s
    change E ((f ≫ q).stalkMap x s) = 0
    rw [Scheme.Hom.stalkMap_comp]
    change E (algebraMap B C (q.stalkMap (f x) s)) = 0
    rw [hE]
    change (f.residueFieldMap x).hom (D.val (q.stalkMap (f x) s)) = 0
    rw [D.property s, map_zero]
  · apply Subtype.ext
    apply Derivation.ext
    intro b
    change (inv (f.residueFieldMap x)).hom (E (algebraMap B C b)) = D.val b
    rw [hE]
    change (inv (f.residueFieldMap x)).hom ((f.residueFieldMap x).hom (D.val b)) = D.val b
    exact inv_residueFieldMap_apply f x _

/-- At an actual formally smooth point, the original native canonical
tangent map is surjective. No differential-rank or lifting premise is given. -/
theorem tangentMap_surjective (hsm : (f.stalkMap x).hom.FormallySmooth) :
    Function.Surjective (tangentMap f p q h x) := by
  intro θ
  obtain ⟨D, hD⟩ := tangentDerivationMap_surjective f p q h x hsm
    (dottedToDerivation q (f x) θ)
  refine ⟨derivationToDotted p x D, ?_⟩
  change derivationToDotted q (f x)
    (tangentDerivationMap f p q x h
      (dottedToDerivation p x (derivationToDotted p x D))) = θ
  rw [dottedToDerivation_derivationToDotted, hD, derivationToDotted_dottedToDerivation]

end M9Native.SmoothTangentMapSurjective
