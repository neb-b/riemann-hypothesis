module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemOfCharpolyCoeffMem
section
open scoped BigOperators

namespace GlobalTheory

namespace Amitsur

open Matrix Polynomial

theorem det_one_sub_smul_mem_of_nilpotent {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]
    (U : Subring A) (t : A) (N : ℕ) (ht : t ^ N = 0) (S : Set (Matrix ι ι A))
    (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hsm : ∀ a ∈ S, t • a ∈ S)
    (hdet : ∀ a ∈ S, (1 - a).det ∈ U) :
    ∀ B ∈ AddSubmonoid.closure S, (1 - t • B).det ∈ U := by
  have hpow : ∀ (k : ℕ), ∀ a ∈ S, t ^ k • a ∈ S := by
    intro k a ha
    induction k with
    | zero => simpa using ha
    | succ k ih => rw [pow_succ', mul_smul]; exact hsm _ ih
  have hM1 : ∀ a ∈ S, ∀ y ∈ AddSubmonoid.closure S, a * y ∈ AddSubmonoid.closure S := by
    intro a ha y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hmul a ha x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  have hM2 : ∀ y ∈ AddSubmonoid.closure S, t • y ∈ AddSubmonoid.closure S := by
    intro y hy
    induction hy using AddSubmonoid.closure_induction with
    | mem x hx => exact AddSubmonoid.subset_closure (hsm x hx)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  have hM3 : ∀ a ∈ S, ∀ (j : ℕ), ∀ y ∈ AddSubmonoid.closure S,
      a ^ j * y ∈ AddSubmonoid.closure S := by
    intro a ha j y hy
    induction j with
    | zero => simpa using hy
    | succ j ih => rw [pow_succ', mul_assoc]; exact hM1 a ha _ ih
  have step : ∀ e : ℕ, (∀ C ∈ AddSubmonoid.closure S, (1 - t ^ (e + 2) • C).det ∈ U) →
      ∀ B ∈ AddSubmonoid.closure S, (1 - t ^ (e + 1) • B).det ∈ U := by
    intro e ih
    have key : ∀ B ∈ AddSubmonoid.closure S, ∀ C ∈ AddSubmonoid.closure S,
        (1 - t ^ (e + 1) • (B + t • C)).det ∈ U := by
      intro B hB
      induction hB using AddSubmonoid.closure_induction_left with
      | zero =>
        intro C hC
        have := ih C hC
        rwa [zero_add, smul_smul, ← pow_succ]
      | add_left s hs B hB ihB =>
        intro C hC
        set a : Matrix ι ι A := t ^ (e + 1) • s with ha
        have haS : a ∈ S := hpow _ _ hs
        have haN : a ^ N = 0 := by
          rw [ha, _root_.smul_pow, ← pow_mul, add_mul, one_mul, pow_add, ht, mul_zero, zero_smul]
        set g : Matrix ι ι A := ∑ j ∈ Finset.range N, a ^ j with hg
        have hga : (1 - a) * g = 1 := by
          rw [hg, mul_neg_geom_sum, haN, sub_zero]
        set y : Matrix ι ι A := B + t • C with hy
        have hyM : y ∈ AddSubmonoid.closure S := add_mem hB (hM2 C hC)
        have hgy : g * y ∈ AddSubmonoid.closure S := by
          rw [hg, Finset.sum_mul]
          exact sum_mem fun j _ => hM3 a haS j y hyM
        have hC' : C + (t ^ e • s) * (g * y) ∈ AddSubmonoid.closure S :=
          add_mem hC (hM1 _ (hpow _ _ hs) _ hgy)
        have h1 := ihB _ hC'
        have e1 : B + t • (C + (t ^ e • s) * (g * y)) = g * y := by
          have h2 : t • ((t ^ e • s) * (g * y)) = a * (g * y) := by
            rw [← smul_mul_assoc, smul_smul, ← pow_succ']
          have h3 : g * y = (1 - a) * g * y + a * (g * y) := by noncomm_ring
          rw [smul_add, h2, ← add_assoc, ← hy]
          conv_rhs => rw [h3, hga, one_mul]
        rw [e1] at h1
        have e2 : 1 - t ^ (e + 1) • (s + B + t • C) = (1 - a) * (1 - t ^ (e + 1) • (g * y)) := by
          rw [mul_sub, mul_one, mul_smul_comm, ← mul_assoc, hga, one_mul, add_assoc, ← hy,
            smul_add, ← ha, sub_sub]
        rw [e2, det_mul]
        exact U.mul_mem (hdet a haS) h1
    intro B hB
    simpa using key B hB 0 (zero_mem _)
  have all : ∀ k e : ℕ, N ≤ e + k → ∀ B ∈ AddSubmonoid.closure S,
      (1 - t ^ (e + 1) • B).det ∈ U := by
    intro k
    induction k with
    | zero =>
      intro e he B _
      have : t ^ (e + 1) = 0 := pow_eq_zero_of_le (by omega) ht
      simp [this]
    | succ k ih =>
      intro e he
      exact step e (ih (e + 1) (by omega))
  intro B hB
  simpa using all N 0 (by omega) B hB

theorem eval₂_charpolyRev {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (u : A) (s : Matrix ι ι R) :
    (1 - u • s.map φ).det = s.charpolyRev.eval₂ φ u := by
  rw [← coe_eval₂RingHom, Matrix.charpolyRev, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply] <;> ring

theorem det_sum_smul_mem {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (T : Subring R) (S : Set (Matrix ι ι R)) (hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S)
    (hchar : ∀ a ∈ S, ∀ j, a.charpoly.coeff j ∈ T)
    (F : Finset κ) (c : κ → R) (s : κ → Matrix ι ι R) (hc : ∀ k, c k ∈ T) (hs : ∀ k, s k ∈ S) :
    (∑ k ∈ F, c k • s k).det ∈ T := by
  nontriviality R
  set n := Fintype.card ι with hn
  let I : Ideal R[X] := Ideal.span {X ^ (n + 1)}
  let π : R[X] →+* R[X] ⧸ I := Ideal.Quotient.mk I
  let φ : R →+* R[X] ⧸ I := π.comp C
  let U : Subring (R[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.subtype)).range
  have hφ : ∀ x ∈ T, φ x ∈ U := fun x hx => ⟨C ⟨x, hx⟩, by simp [φ]⟩
  have htU : π X ∈ U := ⟨X, by simp⟩
  have ht : π X ^ (n + 1) = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  let S' : Set (Matrix ι ι (R[X] ⧸ I)) := {a | ∃ u ∈ U, ∃ b ∈ S, a = u • b.map φ}
  have main := det_one_sub_smul_mem_of_nilpotent U (π X) (n + 1) ht S' (by
      rintro _ ⟨u, hu, a, ha, rfl⟩ _ ⟨v, hv, b, hb, rfl⟩
      refine ⟨u * v, U.mul_mem hu hv, a * b, hmul a ha b hb, ?_⟩
      rw [Matrix.map_mul, smul_mul_smul_comm]) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      exact ⟨π X * u, U.mul_mem htU hu, a, ha, by rw [smul_smul]⟩) (by
      rintro _ ⟨u, hu, a, ha, rfl⟩
      rw [eval₂_charpolyRev, eval₂_eq_sum, Polynomial.sum]
      refine U.sum_mem fun j _ => U.mul_mem (hφ _ ?_) (U.pow_mem hu _)
      rw [← reverse_charpoly, coeff_reverse]
      exact hchar a ha _)
    ((∑ k ∈ F, c k • s k).map φ) (by
      have : (∑ k ∈ F, c k • s k).map φ = ∑ k ∈ F, φ (c k) • (s k).map φ := by
        ext i j
        simp [Matrix.sum_apply]
      rw [this]
      exact sum_mem fun k _ => AddSubmonoid.subset_closure ⟨_, hφ _ (hc k), _, hs k, rfl⟩)
  set B := ∑ k ∈ F, c k • s k
  rw [eval₂_charpolyRev] at main
  have h1 : B.charpolyRev.eval₂ φ (π X) = π B.charpolyRev := by
    rw [← Polynomial.hom_eval₂, eval₂_C_X]
  rw [h1] at main
  obtain ⟨p, hp⟩ := main
  have h2 : X ^ (n + 1) ∣ p.map T.subtype - B.charpolyRev :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hp)
  have h3 := X_pow_dvd_iff.1 h2 n (by omega)
  rw [coeff_sub, sub_eq_zero, coeff_map, ← reverse_charpoly, coeff_reverse,
    charpoly_natDegree_eq_dim, ← hn, revAt_le le_rfl, Nat.sub_self] at h3
  rw [det_eq_sign_charpoly_coeff, ← h3]
  exact T.mul_mem (T.pow_mem (T.neg_mem T.one_mem) _) (p.coeff n).2

end Amitsur

theorem coeff_det_generic_sum_mem_of_charpoly_coeff_mem :
    ∀ {O X G : Type} [CommRing O] [Monoid G] (T : Subalgebra O (X → O)) (n : ℕ)
      (r : X → G →* Matrix (Fin n) (Fin n) O),
      (∀ g j, (fun x => (r x g).charpoly.coeff j) ∈ T) →
      ∀ (m : ℕ) (g : Fin m → G) (d : Fin m →₀ ℕ),
        (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k,
          (MvPolynomial.X k : MvPolynomial (Fin m) O) • (r x (g k)).map MvPolynomial.C)) d) ∈ T := by
  intro O X G _ _ T n r h m g d
  let ρ : G → Matrix (Fin n) (Fin n) (X → O) := fun a => Matrix.of fun i j x => r x a i j
  have hρx : ∀ a x, (ρ a).map (Pi.evalRingHom (fun _ : X => O) x) = r x a := by
    intro a x; ext i j; simp [ρ]
  have hρ : ∀ a b, ρ (a * b) = ρ a * ρ b := by
    intro a b
    ext i j x
    simp [ρ, Matrix.mul_apply]
  have hch : ∀ a j, (ρ a).charpoly.coeff j ∈ T := by
    intro a j
    convert h a j using 1
    funext x
    rw [← hρx, Matrix.charpoly_map, Polynomial.coeff_map]
    rfl
  let T' : Subring (MvPolynomial (Fin m) (X → O)) :=
    (MvPolynomial.map (σ := Fin m) T.toSubring.subtype).range
  have main := Amitsur.det_sum_smul_mem T'
    (Set.range fun a => (ρ a).map (MvPolynomial.C (σ := Fin m))) (by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact ⟨a * b, by simp only [hρ, Matrix.map_mul]⟩) (by
      rintro _ ⟨a, rfl⟩ j
      rw [Matrix.charpoly_map, Polynomial.coeff_map]
      exact ⟨MvPolynomial.C ⟨_, hch a j⟩, MvPolynomial.map_C _ _⟩)
    Finset.univ (fun k => MvPolynomial.X k) (fun k => (ρ (g k)).map MvPolynomial.C)
    (fun k => ⟨MvPolynomial.X k, by simp⟩) (fun k => ⟨g k, rfl⟩)
  obtain ⟨p, hp⟩ := main
  have h1 : AddMonoidAlgebra.coeff (MvPolynomial.map T.toSubring.subtype p) d ∈ T := by
    rw [MvPolynomial.coeff_map]
    exact (AddMonoidAlgebra.coeff p d).2
  rw [hp] at h1
  convert h1 using 1
  funext x
  change _ = Pi.evalRingHom (fun _ : X => O) x (AddMonoidAlgebra.coeff _ d)
  rw [← MvPolynomial.coeff_map, RingHom.map_det]
  have heq : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (r x (g k)).map (MvPolynomial.C (σ := Fin m))) =
      (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x)).mapMatrix
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (ρ (g k)).map (MvPolynomial.C (σ := Fin m))) := by
    ext i j
    simp [Matrix.sum_apply, ρ]
  rw [heq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommonEigenvector
section
universe u_1 u_2

namespace GlobalTheory.CommonEigenvector

private lemma exists_common_eigenspace_of_commuting {V : Type u_1} {ι : Type u_2} [AddCommGroup V] [Module ℂ V]
    (H : ι → Module.End ℂ V) (hc : ∀ (i j : ι), H i * H j = H j * H i)
    (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E] (hE : ∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E)
    (hne : E ≠ ⊥) :
    ∃ W : Submodule ℂ V, W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∃ c : ℂ, ∀ x ∈ W, (H i : V → V) x = c • x := by

  classical
  let P : Submodule ℂ V → Prop := fun W => W ≤ E ∧ W ≠ ⊥ ∧ ∀ i, ∀ x ∈ W, (H i : V → V) x ∈ W
  have hex : ∃ n, ∃ W, P W ∧ Module.finrank ℂ W = n := ⟨_, E, ⟨le_rfl, hne, hE⟩, rfl⟩
  obtain ⟨W, ⟨hWE, hW0, hWi⟩, hWn⟩ := Nat.find_spec hex
  have hmin : ∀ W', P W' → Module.finrank ℂ W ≤ Module.finrank ℂ W' := fun W' hW' => by
    rw [hWn]
    exact Nat.find_min' hex ⟨W', hW', rfl⟩
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWE
  have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  refine ⟨W, hWE, hW0, fun i => ?_⟩
  obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue ((H i).restrict (hWi i))
  obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
  have hwv : (H i : V → V) w = c • (w : V) := by
    have h1 := congrArg Subtype.val hw.apply_eq_smul
    simpa using h1
  let W' : Submodule ℂ V := W ⊓ LinearMap.ker (H i - c • LinearMap.id)
  have hmem : ∀ x, x ∈ W' ↔ x ∈ W ∧ (H i : V → V) x = c • x := by
    intro x
    simp [W', sub_eq_zero]
  have hW'le : W' ≤ W := inf_le_left
  have hW'P : P W' := by
    refine ⟨hW'le.trans hWE, ?_, ?_⟩
    · intro h
      have hw' : (w : V) ∈ W' := (hmem _).2 ⟨w.2, hwv⟩
      rw [h, Submodule.mem_bot] at hw'
      exact hw.2 (Subtype.ext hw')
    · intro j x hx
      obtain ⟨hxW, hxe⟩ := (hmem x).1 hx
      refine (hmem _).2 ⟨hWi j x hxW, ?_⟩
      have hcom := congrArg (fun f : Module.End ℂ V => f x) (hc i j)
      simp only [Module.End.mul_apply] at hcom
      rw [hcom, hxe, map_smul]
  have hle : Module.finrank ℂ W' ≤ Module.finrank ℂ W :=
    LinearMap.finrank_le_finrank_of_injective (Submodule.inclusion_injective hW'le)
  have hEq : W' = W := Submodule.eq_of_le_of_finrank_eq hW'le (le_antisymm hle (hmin W' hW'P))
  refine ⟨c, fun x hx => ?_⟩
  rw [← hEq] at hx
  exact ((hmem x).1 hx).2

theorem common_eigenvector : ∀ {V : Type u_1} {ι : Type u_2} [inst : AddCommGroup V] [inst_1 : Module ℂ V] [Fintype ι] (H : ι → Module.End ℂ V), (∀ (i j : ι), H i * H j = H j * H i) → ∀ (E : Submodule ℂ V) [FiniteDimensional ℂ ↥E], (∀ (i : ι), ∀ x ∈ E, (H i : V → V) x ∈ E) → E ≠ ⊥ → ∃ v ∈ E, v ≠ (0 : V) ∧ ∀ (i : ι), ∃ (c : ℂ), (H i : V → V) v = c • v := by
  intro V ι _ _ _ H hc E _ hE hne

  obtain ⟨W, hWE, hW0, hW⟩ := exists_common_eigenspace_of_commuting H hc E hE hne
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  refine ⟨v, hWE hv, hv0, fun i => ?_⟩
  obtain ⟨c, hc'⟩ := hW i
  exact ⟨c, hc' v hv⟩

end GlobalTheory.CommonEigenvector
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompOneAddPowMul
section
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.PsiBasis

variable {k : Type} [Field k]

noncomputable def comp (l : ℕ) (hl : 0 < l) (i : ℕ) : k⸨X⸩ →ₗ[k] k⸨X⸩ where
  toFun y :=
    { coeff := fun m => y.coeff (l * m + i)
      isPWO_support' := by
        apply Set.IsWF.isPWO
        apply BddBelow.isWF
        refine ⟨min 0 (y.order - i), fun m hm => ?_⟩
        by_contra h
        apply hm
        apply HahnSeries.coeff_eq_zero_of_lt_order
        have h1 : m < 0 := lt_of_lt_of_le (not_le.1 h) (min_le_left _ _)
        have h2 : m < y.order - i := lt_of_lt_of_le (not_le.1 h) (min_le_right _ _)
        have h3 : (1 : ℤ) ≤ l := by exact_mod_cast hl
        nlinarith }
  map_add' x y := by ext m; simp
  map_smul' c x := by ext m; simp

theorem comp_coeff (l : ℕ) (hl : 0 < l) (i : ℕ) (y : k⸨X⸩) (m : ℤ) :
    (comp l hl i y).coeff m = y.coeff (l * m + i) := rfl

theorem p_zpow (s : ℤ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single s 1 := by
  cases s with
  | ofNat n => simp [HahnSeries.single_pow]
  | negSucc n =>
    rw [zpow_negSucc, HahnSeries.single_pow, HahnSeries.inv_single]
    simp [Int.negSucc_eq]

theorem p_pow (s : ℕ) :
    (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s = HahnSeries.single (s : ℤ) 1 := by
  simp [HahnSeries.single_pow]

theorem mem_iff (s : ℤ) (x : k⸨X⸩) :
    (∃ b : k⟦X⟧, x = (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ s * (b : k⸨X⸩)) ↔
      ∀ m < s, x.coeff m = 0 := by
  rw [p_zpow]
  constructor
  · rintro ⟨b, rfl⟩ m hm
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, if_pos (by omega), mul_zero]
  · intro h
    refine ⟨PowerSeries.mk fun n => x.coeff (s + n), ?_⟩
    ext m
    rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe, one_mul]
    split_ifs with hm
    · exact h m (by omega)
    · rw [PowerSeries.coeff_mk]; congr 1; omega

section
variable (l : ℕ) (hl : 0 < l) (φ : k⸨X⸩ →+* k⸨X⸩)
  (hφ : ∀ (x : k⸨X⸩) (m : ℤ), (φ x).coeff m = if (l : ℤ) ∣ m then x.coeff (m / l) else 0)
include hl hφ

theorem comp_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ j * φ a)
      = if j = i then a else 0 := by
  ext m
  have hl' : (l : ℤ) ≠ 0 := by exact_mod_cast hl.ne'
  rw [comp_coeff, p_pow, HahnSeries.coeff_single_mul, one_mul, hφ]
  by_cases h : j = i
  · subst h
    simp [Int.mul_ediv_cancel_left _ hl']
  · rw [if_neg h, if_neg]
    · simp
    · intro hd
      have : (l : ℤ) ∣ (i : ℤ) - j := by
        have h2 := dvd_sub hd (dvd_mul_right (l : ℤ) m)
        have e : (l : ℤ) * m + i - j - l * m = i - j := by ring
        rwa [e] at h2
      have := Int.eq_zero_of_abs_lt_dvd this (by rw [abs_lt]; constructor <;> omega)
      omega

theorem comp_one_add_pow_mul {i j : ℕ} (hi : i < l) (hj : j < l) (a : k⸨X⸩) :
    comp l hl i ((1 + (HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩)) ^ j * φ a)
      = (j.choose i) • a := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [add_comm, add_pow, Finset.sum_mul, map_sum]
  have : ∀ m ∈ Finset.range (j + 1),
      comp l hl i ((HahnSeries.single (1 : ℤ) (1 : k) : k⸨X⸩) ^ m * 1 ^ (j - m) *
        (j.choose m : k⸨X⸩) * φ a) = if m = i then (j.choose i) • a else 0 := by
    intro m hm
    have hm' : m < l := by have := Finset.mem_range.1 hm; omega
    rw [one_pow, mul_one, mul_assoc, ← map_natCast φ, ← map_mul,
      comp_pow_mul l hl φ hφ hi hm']
    split_ifs with h
    · subst h; rw [nsmul_eq_mul]
    · rfl
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [Nat.choose_eq_zero_of_lt (by simpa using h), zero_smul]

end

noncomputable def psi (l : ℕ) (hl : 0 < l) : k⸨X⸩ →ₗ[k] k⸨X⸩ :=
  ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i

theorem psi_apply (l : ℕ) (hl : 0 < l) (y : k⸨X⸩) :
    psi l hl y = ∑ i ∈ Finset.range l, ((-1 : ℤ) ^ i) • comp l hl i y := by
  simp only [psi, LinearMap.sum_apply, LinearMap.smul_apply]

end GlobalTheory.PsiBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactDvrAdicCompleteSeparatedUniformizer
section
namespace GlobalTheory

theorem compact_dvr_complete_separated : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  intro O _ _ _ _ _ _ _ _ ϖ hϖ
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · set s : ℕ → O := fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j with hs
    let C : ℕ → Set O := fun n => Set.range (fun b : O => s n + ϖ ^ n * b)
    have hcpt : ∀ n, IsCompact (C n) := fun n =>
      isCompact_range (continuous_const.add (continuous_const.mul continuous_id))
    have hdec : ∀ n, C (n + 1) ⊆ C n := by
      intro n y ⟨b, hb⟩
      refine ⟨x n + ϖ * b, ?_⟩
      rw [← hb]
      simp only [hs, Finset.sum_range_succ, pow_succ]
      ring
    have hne : ∀ n, (C n).Nonempty := fun n => ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
      (hcpt 0) (fun n => (hcpt n).isClosed)
    refine ⟨a, fun n => ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iInter.mp ha n
    exact ⟨b, by rw [← hb]; simp [hs]⟩
  · have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O) := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hϖ.not_isUnit
    have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
    have : a ∈ ⨅ i, (Ideal.span {ϖ}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      obtain ⟨b, hb⟩ := ha i
      rw [Ideal.span_singleton_pow, hb]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Submodule.mem_bot O).mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementedSup
section
namespace GlobalTheory.ComplementedSup

theorem complemented_sup :
    (let d1 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (S : Submodule K V) ↦ ∀ (γ : Γ), ∀ v ∈ S, (f γ : V → V) v ∈ S); let d2 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (Y : Submodule K V) ↦ ∀ (W : Submodule K V), d1 f W → W ≤ Y → ∃ (C : Submodule K V), d1 f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y); ∀ {K : Type} [inst : Field K] {Γ V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module K V] {f : Γ → V →ₗ[K] V} {X U : Submodule K V}, d1 f X → d1 f U → d2 f X → d2 f U → d2 f (X ⊔ U)) := by
  intro d1 d2 K _ Γ V _ _ f X U hX hU hXc hUc

  have hsup : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊔ B) := by
    intro A B hA hB γ v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hA γ a ha) (hB γ b hb)
  have hinf : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊓ B) := by
    intro A B hA hB γ v hv
    exact Submodule.mem_inf.mpr ⟨hA γ v (Submodule.mem_inf.mp hv).1, hB γ v (Submodule.mem_inf.mp hv).2⟩
  intro W hW hWle

  obtain ⟨D, hD, hDX, hD1, hD2⟩ := hXc (W ⊓ X) (hinf W X hW hX) inf_le_right
  obtain ⟨B, hB, hBU, hB1, hB2⟩ := hUc ((W ⊔ X) ⊓ U) (hinf _ U (hsup W X hW hX) hU) inf_le_right
  refine ⟨D ⊔ B, hsup D B hD hB, sup_le_sup hDX hBU, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwDB⟩ := Submodule.mem_inf.mp hw
    obtain ⟨d, hd, b, hb, rfl⟩ := Submodule.mem_sup.mp hwDB
    have hbA : b ∈ (W ⊔ X) ⊓ U := by
      refine Submodule.mem_inf.mpr ⟨?_, hBU hb⟩
      have hbd : b = (d + b) - d := by abel
      rw [hbd]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hwW) (Submodule.mem_sup_right (hDX hd))
    have hb0 : b = 0 := by
      have hb' : b ∈ (W ⊔ X) ⊓ U ⊓ B := Submodule.mem_inf.mpr ⟨hbA, hb⟩
      rw [hB1] at hb'
      exact (Submodule.mem_bot K).mp hb'
    subst hb0
    rw [add_zero] at hwW ⊢
    have hd' : d ∈ W ⊓ X ⊓ D := Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hwW, hDX hd⟩, hd⟩
    rw [hD1] at hd'
    exact hd'
  · apply le_antisymm
    · exact sup_le hWle (sup_le_sup hDX hBU)
    · have hX' : X ≤ W ⊔ (D ⊔ B) := by
        rw [← hD2]
        exact sup_le (le_trans inf_le_left le_sup_left) (le_trans le_sup_left le_sup_right)
      have hU' : U ≤ W ⊔ (D ⊔ B) := by
        rw [← hB2]
        exact sup_le (le_trans inf_le_left (sup_le le_sup_left hX')) (le_trans le_sup_right le_sup_right)
      exact sup_le hX' hU'

end GlobalTheory.ComplementedSup
end

