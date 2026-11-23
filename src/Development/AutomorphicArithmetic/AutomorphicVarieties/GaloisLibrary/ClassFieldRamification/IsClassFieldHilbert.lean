module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import GroundTheory.GlobalFields.ClassFieldConsequences.HilbertClassField

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Kum

namespace UpperTheory.V.CF

section Art

variable (K H : Type) [Field K] [NumberField K] [Field H] [NumberField H] [Algebra K H]

end Art

section Tower

variable (k K H : Type) [Field k] [Field K] [Field H] [Algebra k K] [Algebra K H] [Algebra k H] [IsScalarTower k K H]

def relIncl : Gal(H/K) →* Gal(H/k) := AlgEquiv.restrictScalarsHom k

def resTo [Normal k K] : Gal(H/k) →* Gal(K/k) := AlgEquiv.restrictNormalHom K

theorem resTo_commutes [Normal k K] (σ : Gal(H/k)) (x : K) :
    algebraMap K H (resTo k K H σ x) = σ (algebraMap K H x) := AlgEquiv.restrictNormal_commutes σ K x

theorem resTo_surjective [Normal k K] [Normal k H] : Function.Surjective (resTo k K H) :=
  AlgEquiv.restrictNormalHom_surjective H

theorem range_relIncl [Normal k K] : (relIncl k K H).range = (resTo k K H).ker := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [MonoidHom.mem_ker]
    ext x
    apply (algebraMap K H).injective
    rw [resTo_commutes]
    simp [relIncl]
  · intro h
    rw [MonoidHom.mem_ker] at h
    have hc : ∀ x : K, σ (algebraMap K H x) = algebraMap K H x := by
      intro x
      rw [← resTo_commutes, h]
      rfl
    refine ⟨{ σ with commutes' := hc }, ?_⟩
    ext y
    rfl

end Tower

def UnramAt (L : Type) [Field L] [NumberField L] (p : ℕ) : Prop :=
  ∀ P : Ideal (𝓞 L), P.IsPrime → (p : 𝓞 L) ∈ P → P.ramificationIdx ℤ = 1

def phi (p : ℕ) (P : Type) [Group P] : Subgroup P := Subgroup.closure (Set.range fun g : P => g ^ p) ⊔ commutator P

def aug (R G : Type) [CommRing R] [Group G] : MonoidAlgebra R G →ₐ[R] R := MonoidAlgebra.lift R R G 1

theorem aug_single (R G : Type) [CommRing R] [Group G] (g : G) (r : R) : aug R G (MonoidAlgebra.single g r) = r := by
  simp [aug]

def augIdeal (R G : Type) [CommRing R] [CommGroup G] : Ideal (MonoidAlgebra R G) :=
  Ideal.span (Set.range fun g : G => MonoidAlgebra.of R G g - 1)

def pStar (p : ℕ) : ℤ := (-1) ^ (p / 2) * p

end UpperTheory.V.CF

end
