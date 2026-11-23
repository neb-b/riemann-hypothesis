module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Gcomm

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.AmitsurSub
section
open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.amitsurSub :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
    AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈
      Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)} := by
  intro n A G _ _ D m g β
  have h := UpperTheory.V.CA.d_coef_mem D.toDet (MonoidHom.mrange (MonoidAlgebra.of A G))
    (Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)})
    (by
      rintro x ⟨s, rfl⟩ i - h2
      rw [(UpperTheory.V.CA.d_toDet D _).2.1]
      exact Subring.subset_closure ⟨i, h2, s, rfl⟩)
    (fun j => MonoidAlgebra.single (g j) 1) (fun j => ⟨g j, rfl⟩) β
  have e : D.toDet.poly (fun j => MonoidAlgebra.single (g j) (1 : A)) =
      D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) := by
    change D.D _ (ofT A G _ (Det.gen _)) = _
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Det.gen, GDet.gen, map_sum, ofT_tmul, MvPolynomial.algebraMap_eq]
  rwa [e] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.KillsStar
section
open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsStar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), F.IsPolar O D → ∀ y, D.Kills y → D.Kills (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n D hP y hy B _ _ h
  letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨-, -, -, -, -, snat⟩ := AlgebraTools.Det.starApi F O R n
  obtain ⟨bmul, b1, badd, -, binv, -⟩ := AlgebraTools.Det.starApi F O B n
  have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) (F.star O R n y)
      = F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y) :=
    (snat B (IsScalarTower.toAlgHom O R B) y).symm
  rw [hm]
  have key : 1 + h * F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y)
      = F.star O B n (1 + MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y * F.star O B n h) := by
    rw [badd, bmul, b1, binv]
  rw [key, hP B, (AlgebraTools.Det.gcomm D).1 B]
  exact hy B (F.star O B n h)
end

