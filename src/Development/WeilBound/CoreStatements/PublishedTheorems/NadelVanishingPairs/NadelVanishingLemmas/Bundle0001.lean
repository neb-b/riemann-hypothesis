module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsIsoTermComparisonRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.AssociatedOfHeightOneAgree
section
theorem _root_.GlobalTheory.T.associated_of_height_one_agree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {n : ℕ} (π : Fin n → R) (J : Finset (Fin n)) (a b : R), a ≠ 0 → b ≠ 0 → (∀ j ∈ J, IsUnit (π j) ∨ Prime (π j)) → (∀ j ∈ J, Prime (π j) → ¬ π j ∣ a ∧ ¬ π j ∣ b) → (∀ Q : Ideal R, Q.IsPrime → Q.height = 1 → (∀ j ∈ J, π j ∉ Q) → ∃ c d : R, c ∉ Q ∧ d ∉ Q ∧ a * d = b * c) → ∃ u : Rˣ, a = u * b := by
  first | exact @_root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | exact _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding | (intros; apply _root_.GlobalTheory.exists_unit_eq_mul_of_height_one_avoiding <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechComplexDirectLimit
section
open CategoryTheory Limits Filter GlobalTheory
theorem _root_.GlobalTheory.T.cech_complex_direct_limit : ∀ {ι : Type} [LinearOrder ι] [Fintype ι] (A : ℕ → Cube.{0} ι ℤ) (B : Cube.{0} ι ℤ) (μ : ∀ (j c d : ℕ), c + j = d → (A c ⟶ A d)) (ρ : ∀ c, A c ⟶ B), (∀ j c d h, μ j c d h ≫ ρ d = ρ c) → (∀ (j j' c d e : ℕ) (h : c + j = d) (h' : d + j' = e) (h'' : c + (j + j') = e), μ j c d h ≫ μ j' d e h' = μ (j + j') c e h'') → (∀ s : Finset ι, s.Nonempty → ∀ b : B.obj s, ∃ c, ∃ a : (A c).obj s, (ρ c).app s a = b) → (∀ s : Finset ι, s.Nonempty → ∀ c (a : (A c).obj s), (ρ c).app s a = 0 → ∃ j, (μ j c (c + j) rfl).app s a = 0) → ∀ n : ℕ, (∀ᶠ c in atTop, IsZero ((cechComplex (A c)).homology n)) → IsZero ((cechComplex B).homology n) := by
  first | exact @_root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | exact _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit | (intros; apply _root_.GlobalTheory.cechComplex_homology_isZero_of_colimit <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.EtaleCoordinatesDifferentials
section
open scoped TensorProduct Polynomial
theorem _root_.GlobalTheory.T.etale_coordinates_differentials : ∀ (R B K : Type) [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra B K] (d : ℕ) (t : Fin d → B), (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale → Module.finrank K (K ⊗[B] Ω[B⁄R]) = d ∧ ∀ (ι : Type) (e : ι ↪ Fin d) (u : ι → Bˣ), (∀ i, algebraMap B K (t (e i)) = 0) → LinearIndependent K (fun i => (1 : K) ⊗ₜ[B] KaehlerDifferential.D R B ((u i : B) * t (e i))) := by
  first | exact @_root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | exact _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul | (intros; apply _root_.GlobalTheory.EtaleCoordRank.finrank_and_linearIndependent_D_unit_mul <;> assumption)
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsFrobeniusSplittingDatum
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isPhi : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  intro K _ V _ _ ι _ p _ _ d f h hD
  have lopAddV : ∀ (x x' : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (x + x') y = Lop f h x y + Lop f h x' y := by
    intro x x' y
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [map_add (f := _), add_mul, smul_add, add_smul, add_zero] <;> abel
  have lopAddY : ∀ (x : V) (y y' : Finset ι → ExteriorAlgebra K V),
      Lop f h x (y + y') = Lop f h x y + Lop f h x y' := by
    intro x y y'
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [mul_add, smul_add, add_zero] <;> abel
  have lopSmulV : ∀ (c : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (c • x) y = c ^ p • Lop f h x y := by
    intro c x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [hD.f_smul, hD.h_smul, map_smul, smul_mul_assoc, mul_smul, smul_add, smul_zero,
        smul_comm ((-1 : ℤ) ^ t.card) (c ^ p)]
  have lopSmulY : ∀ (k : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h x (k • y) = k • Lop f h x y := by
    intro k x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [mul_smul_comm, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) k, smul_comm _ k]
  have hcons : ∀ (x : V) (l : List V), prodL f h (x :: l) = Lop f h x (prodL f h l) := fun _ _ => rfl
  have hupd0 : ∀ {a : ℕ} (v : Fin (a + 1) → V) (z : V),
      (fun k : Fin a => Function.update v 0 z k.succ) = fun k => v k.succ := by
    intro a v z
    funext k
    exact Function.update_of_ne (Fin.succ_ne_zero k) _ _
  have hupds : ∀ {a : ℕ} (v : Fin (a + 1) → V) (j : Fin a) (z : V),
      (fun k : Fin a => Function.update v j.succ z k.succ) = Function.update (fun k => v k.succ) j z := by
    intro a v j z
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]
  have hPadd : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (x x' : V),
      prodL f h (List.ofFn (Function.update v i (x + x'))) =
        prodL f h (List.ofFn (Function.update v i x)) + prodL f h (List.ofFn (Function.update v i x')) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i x x'
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopAddV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopAddY]
  have hPsmul : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (c : K) (x : V),
      prodL f h (List.ofFn (Function.update v i (c • x))) =
        c ^ p • prodL f h (List.ofFn (Function.update v i x)) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i c x
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopSmulV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopSmulY]
  have key : ∃ Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V),
      (∀ (c : K) (x : ExteriorAlgebra K V), Φ (c • x) = c ^ p • Φ x) ∧
        ∀ (a : ℕ) (v : Fin a → V), Φ (ExteriorAlgebra.ιMulti K a v) = alt f h a v := by
    letI tw : Module K (Finset ι → ExteriorAlgebra K V) := Module.compHom _ (frobenius K p)
    let P : ∀ a : ℕ, (Fin a → V) →ₘₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      { toFun := fun v => prodL f h (List.ofFn v)
        map_update_add' := fun v i x x' => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPadd a v i x x'
        map_update_smul' := fun v i c x => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPsmul a v i c x }
    let A : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      MultilinearMap.alternatization (P a)
    let Φ0 := ExteriorAlgebra.liftAlternating (R := K) A
    refine ⟨Φ0.toAddMonoidHom, fun c x => ?_, fun a v => ?_⟩
    · exact Φ0.map_smul c x
    · show Φ0 (ExteriorAlgebra.ιMulti K a v) = _
      rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
      show (MultilinearMap.alternatization (P a)) v = alt f h a v
      rw [MultilinearMap.alternatization_apply]
      unfold alt
      apply Finset.sum_congr rfl
      intro σ _
      rw [Units.smul_def]
      rfl
  obtain ⟨Φ, h1, h2⟩ := key
  exact ⟨Φ, fun c a v => by rw [h1, h2]⟩

end GlobalTheory.DI
end

