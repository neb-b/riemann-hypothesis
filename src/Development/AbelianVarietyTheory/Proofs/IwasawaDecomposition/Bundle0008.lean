module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroSmulMemAlt
section
namespace GlobalTheory.NonzeroSmulMemIntegralSpan

theorem exists_ne_zero_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {M : Submodule (NumberField.RingOfIntegers K) V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : NumberField.RingOfIntegers K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hay
    · rw [mul_smul]; exact M.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj
      (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨a * q, mul_ne_zero ha (nonZeroDivisors.ne_zero q.2), ?_⟩
    have h1 : (q : NumberField.RingOfIntegers K) • c • y = p • y := by
      rw [← algebraMap_smul K (q : NumberField.RingOfIntegers K), smul_smul, mul_comm,
        ← algebraMap_smul K p y]
      exact congrArg (· • y) hpq
    rw [mul_smul, h1, smul_comm]
    exact M.smul_mem _ hay

end GlobalTheory.NonzeroSmulMemIntegralSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZero
section
open NumberField Matrix

namespace GlobalTheory

theorem det_one_add_smul_poly_eval {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Polynomial.eval z (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) = det (1 + z • M) := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp [Matrix.one_apply]
  split_ifs <;> simp [mul_comm]

theorem det_one_add_smul_poly_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C) ≠ 0 := by
  intro h
  have := det_one_add_smul_poly_eval M 0
  rw [h] at this
  simp at this

theorem finite_det_one_add_smul_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    {z : ℂ | det (1 + z • M) = 0}.Finite := by
  refine (Polynomial.rootSet_finite (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) ℂ).subset ?_
  intro z hz
  rw [Polynomial.mem_rootSet_of_ne (det_one_add_smul_poly_ne_zero M)]
  simp only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id]
  rw [det_one_add_smul_poly_eval]
  exact hz

theorem exists_normOne_det_one_add_ne_zero : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ),
    ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by
  intro L _ _ _ n X
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨μ, hμ⟩ := DFunLike.ne_iff.mp (IsCMField.complexConj_ne_one L)
  have hμ' : c μ ≠ μ := hμ
  have hne : ∀ t : ℚ, (t : L) + μ ≠ 0 := by
    intro t h
    apply hμ'
    have h1 : μ = -(t : L) := by linear_combination h
    rw [h1, map_neg, map_ratCast]
  have hne' : ∀ t : ℚ, (t : L) + c μ ≠ 0 := by
    intro t h
    apply hμ'
    have h1 : c μ = -(t : L) := by linear_combination h
    have h2 : μ = -(t : L) := by rw [← hcc μ, h1, map_neg, map_ratCast]
    rw [h1, h2]
  let a : ℚ → L := fun t => ((t : L) + μ) / ((t : L) + c μ)
  have hca : ∀ t, c (a t) = ((t : L) + c μ) / ((t : L) + μ) := by
    intro t
    simp only [a, map_div₀, map_add (f := _), map_ratCast, hcc]
  have hnorm : ∀ t, a t * c (a t) = 1 := by
    intro t
    rw [hca]
    simp only [a]
    field_simp [hne t, hne' t]
  have hinj : Function.Injective a := by
    intro t s h
    simp only [a] at h
    rw [div_eq_div_iff (hne' t) (hne' s)] at h
    have h3 : ((t : L) - s) * (c μ - μ) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact_mod_cast sub_eq_zero.mp h4
    · exact absurd (sub_eq_zero.mp h4) hμ'
  have hfin : (⋃ σ : L →+* ℂ, (fun t => σ (a t)) ⁻¹' {z : ℂ | det (1 + z • X σ) = 0}).Finite := by
    refine Set.finite_iUnion fun σ => ?_
    exact (finite_det_one_add_smul_eq_zero (X σ)).preimage
      (fun t _ s _ h => hinj (σ.injective h))
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hfin |>.nonempty
  refine ⟨a t, hnorm t, fun σ hσ => ht.2 ?_⟩
  exact Set.mem_iUnion.mpr ⟨σ, hσ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormOneCmFieldDetOneAddNeZeroCharZero
section
open NumberField

namespace GlobalTheory.CMScalar
open Matrix Polynomial

theorem eval_charpolyRev_neg {K : Type} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (w : K) :
    (-A).charpolyRev.eval w = (1 + w • A).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm w, sub_eq_add_neg]

theorem exists_unit_norm_one_det_ne_zero (L : Type) [Field L] [NumberField L] [IsCMField L] (K : Type) [Field K]
    [CharZero K] (n : ℕ) (M : (L →+* K) → Matrix (Fin n) (Fin n) K) :
    ∃ u : L, u * (IsCMField.complexConj L : L →+* L) u = 1 ∧ ∀ σ : L →+* K, (1 + σ u • M σ).det ≠ 0 := by
  classical
  set c : L →+* L := (IsCMField.complexConj L : L →+* L) with hc
  have hcc : ∀ x, c (c x) = x := fun x => IsCMField.complexConj_apply_apply L x
  obtain ⟨y, hy⟩ : ∃ y : L, c y ≠ y := by
    by_contra h
    push_neg at h
    apply IsCMField.complexConj_ne_one L
    ext x
    exact h x
  set i : L := y - c y with hi
  have hi0 : i ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  have hci : c i = -i := by rw [hi, map_sub, hcc]; ring
  have hden : ∀ t : ℚ, (1 : L) + (t : L) * i ≠ 0 := by
    intro t h
    have h1 : (t : L) * i = -1 := by linear_combination h
    have h2 := congrArg c h1
    rw [map_mul, map_ratCast, hci, map_neg, map_one] at h2
    have : (2 : L) = 0 := by linear_combination h1 + h2
    exact two_ne_zero this
  let f : ℚ → L := fun t => (1 - (t : L) * i) / (1 + (t : L) * i)
  have hfu : ∀ t, f t * c (f t) = 1 := by
    intro t
    have hd := hden t
    have hd' : (1 : L) - (t : L) * i ≠ 0 := by
      intro h; apply hden (-t); push_cast; linear_combination h
    have e : c (f t) = (1 + (t : L) * i) / (1 - (t : L) * i) := by
      simp only [f, map_div₀, map_sub, map_add (f := _), map_one, map_mul, map_ratCast, hci]
      congr 1 <;> ring
    rw [e, div_mul_div_comm]
    exact (div_eq_one_iff_eq (mul_ne_zero hd hd')).2 (by ring)
  have hfinj : Function.Injective f := by
    intro s t hst
    simp only [f] at hst
    rw [div_eq_div_iff (hden s) (hden t)] at hst
    have h2 : (2 : L) * ((t : L) - s) * i = 0 := by linear_combination hst
    have : ((t : L) - s) = 0 := by
      rcases mul_eq_zero.1 h2 with h | h
      · rcases mul_eq_zero.1 h with h | h
        · exact absurd h two_ne_zero
        · exact h
      · exact absurd h hi0
    have : ((t - s : ℚ) : L) = 0 := by push_cast; exact this
    exact (sub_eq_zero.1 (Rat.cast_eq_zero.1 this)).symm
  have hp : ∀ σ : L →+* K, (-(M σ)).charpolyRev ≠ 0 := by
    intro σ h
    have := Matrix.eval_charpolyRev (M := -(M σ))
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  let B : Set L := ⋃ σ : L →+* K, σ ⁻¹' ((-(M σ)).charpolyRev.roots.toFinset : Set K)
  have hB : B.Finite := by
    apply Set.finite_iUnion
    intro σ
    exact (Finset.finite_toSet _).preimage σ.injective.injOn
  have hS : (f ⁻¹' B).Finite := hB.preimage hfinj.injOn
  obtain ⟨t, ht⟩ := (Set.infinite_univ (α := ℚ)).diff hS |>.nonempty
  refine ⟨f t, hfu t, fun σ hσ => ht.2 ?_⟩
  simp only [Set.mem_preimage, B, Set.mem_iUnion]
  refine ⟨σ, ?_⟩
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots (hp σ), Polynomial.IsRoot, eval_charpolyRev_neg]
  exact hσ

end GlobalTheory.CMScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPermOfOfFnPerm
section
namespace GlobalTheory.FiberCardPermutation

theorem card_fiber_eq_count {α : Type} [DecidableEq α] {n : ℕ} (v : Fin n → α) (c : α) :
    Fintype.card {i : Fin n // v i = c} = Multiset.count c (List.ofFn v : Multiset α) := by
  rw [← Fin.univ_val_map, Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : List.Perm (List.ofFn v) (List.ofFn w)) :
    ∃ σ : Equiv.Perm (Fin n), v = w ∘ (⇑σ : Fin n → Fin n) := by
  classical
  have hm : (List.ofFn v : Multiset α) = (List.ofFn w : Multiset α) := Multiset.coe_eq_coe.mpr h
  have hc : ∀ c : α, Fintype.card {i : Fin n // v i = c} = Fintype.card {i : Fin n // w i = c} := by
    intro c
    have h1 := card_fiber_eq_count v c
    have h2 := card_fiber_eq_count w c
    rw [hm, ← h2] at h1
    convert h1
  refine ⟨Equiv.ofFiberEquiv (f := v) (g := w) (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map (f := v) (g := w) _ i).symm

end GlobalTheory.FiberCardPermutation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPosSmulEqOfLinearIndependentCone
section
open Finset

namespace GlobalTheory

theorem exists_pos_smul_eq_of_linearIndependent_cone {L : Type} [AddCommGroup L] {m m' : ℕ}
    (δ : Fin m → L) (γ : Fin m' → L) (i : Fin m) (k : ℕ)
    (a : Fin m' → ℕ) (hδ : LinearIndependent ℤ δ) (hk : 0 < k) (hsum : k • δ i = ∑ j, a j • γ j)
    (hγ : ∀ j, 0 < a j → ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ k' • γ j = ∑ l, b l • δ l) :
    ∃ (j : Fin m') (p r : ℕ), 0 < p ∧ 0 < r ∧ p • δ i = r • γ j := by
  classical
  have hγ' : ∀ j, ∃ (k' : ℕ) (b : Fin m → ℕ), 0 < k' ∧ (0 < a j → k' • γ j = ∑ l, b l • δ l) := by
    intro j
    by_cases hj : 0 < a j
    · obtain ⟨k', b, hk', h⟩ := hγ j hj
      exact ⟨k', b, hk', fun _ => h⟩
    · exact ⟨1, 0, one_pos, fun h => absurd h hj⟩
  choose kk b hkk hb using hγ'
  let c : Fin m' → ℕ := fun j => ∏ j' ∈ univ.erase j, kk j'
  let K : ℕ := ∏ j, kk j
  have hcK : ∀ j, c j * kk j = K := fun j => by
    rw [mul_comm]; exact Finset.mul_prod_erase _ _ (mem_univ j)
  have hcpos : ∀ j, 0 < c j := fun j => Finset.prod_pos (fun j' _ => hkk j')
  have hKpos : 0 < K := Finset.prod_pos (fun j _ => hkk j)
  have hterm : ∀ j, (K * a j) • γ j = (a j * c j) • ∑ l, b j l • δ l := by
    intro j
    by_cases hj : 0 < a j
    · rw [← hb j hj, smul_smul, ← hcK j]; congr 1; ring
    · have : a j = 0 := Nat.eq_zero_of_not_pos hj
      simp [this]
  have key : (K * k) • δ i = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
    calc (K * k) • δ i = K • (k • δ i) := mul_smul _ _ _
      _ = ∑ j, (K * a j) • γ j := by rw [hsum, Finset.smul_sum]; simp_rw [smul_smul]
      _ = ∑ j, (a j * c j) • ∑ l, b j l • δ l := Finset.sum_congr rfl (fun j _ => hterm j)
      _ = ∑ l, (∑ j, a j * c j * b j l) • δ l := by
          simp_rw [Finset.smul_sum, smul_smul, Finset.sum_smul]
          rw [Finset.sum_comm]
  let N : Fin m → ℕ := fun l => ∑ j, a j * c j * b j l
  let g : Fin m → ℤ := fun l => (N l : ℤ) - (if l = i then ((K * k : ℕ) : ℤ) else 0)
  have hg : ∑ l, g l • δ l = 0 := by
    simp only [g, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
      mem_univ, if_true, natCast_zsmul]
    rw [key]; exact sub_self _
  have hg0 := Fintype.linearIndependent_iff.mp hδ g hg
  have hN : ∀ l, N l = if l = i then K * k else 0 := by
    intro l
    have := hg0 l
    simp only [g] at this
    split_ifs at this ⊢ <;> omega
  have hNi : N i ≠ 0 := by rw [hN i, if_pos rfl]; exact (Nat.mul_pos hKpos hk).ne'
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hNi
  have haj : 0 < a j := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbji : 0 < b j i := Nat.pos_of_ne_zero (fun h => hj (by simp [h]))
  have hbjl : ∀ l, l ≠ i → b j l = 0 := by
    intro l hl
    have h0 : N l = 0 := by rw [hN l, if_neg hl]
    have := (Finset.sum_eq_zero_iff.mp h0) j (mem_univ j)
    rcases Nat.mul_eq_zero.mp this with h | h
    · rcases Nat.mul_eq_zero.mp h with h | h
      · omega
      · exact absurd h (hcpos j).ne'
    · exact h
  have hγj : kk j • γ j = b j i • δ i := by
    rw [hb j haj, Finset.sum_eq_single i]
    · intro l _ hl; rw [hbjl l hl, zero_smul]
    · intro h; exact absurd (mem_univ i) h
  exact ⟨j, b j i, kk j, hbji, hkk j, hγj.symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeDvdNatCastMem
section
namespace GlobalTheory.PrimeDvdNatCastMem

theorem exists_prime_dvd_natCast_mem {O : Type} [CommRing O] (P : Ideal O) [hP : Ideal.IsPrime P]
    (m : ℕ) : m ≠ (0 : ℕ) → (↑m : O) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ m ∧ (↑p : O) ∈ P := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hm
    by_cases h1 : m = 1
    · subst h1
      exact absurd ((Ideal.eq_top_iff_one P).2 (by simpa using hm)) hP.ne_top
    · obtain ⟨q, hq, k, hk⟩ := Nat.exists_prime_and_dvd h1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hm0 (by simpa using hk)
      have hmul : (q : O) * (k : O) ∈ P := by
        have := hm
        rw [hk, Nat.cast_mul] at this
        exact this
      rcases hP.mem_or_mem hmul with h | h
      · exact ⟨q, hq, ⟨k, hk⟩, h⟩
      · have hlt : k < m := by
          have h2 := hq.two_le
          have h3 : 0 < k := Nat.pos_of_ne_zero hk0
          rw [hk]
          nlinarith
        obtain ⟨p, hp, hpk, hpP⟩ := ih k hlt hk0 h
        exact ⟨p, hp, hk ▸ Dvd.dvd.mul_left hpk q, hpP⟩

end GlobalTheory.PrimeDvdNatCastMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeMemHeightOneSpectrum
section
namespace GlobalTheory.PrimeInHeightOneSpectrum

theorem exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have h1 : n ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr (by simpa using hmem))
    have hpr : Nat.Prime n.minFac := Nat.minFac_prime h1
    obtain ⟨m, hm⟩ := Nat.minFac_dvd n
    have hmul : ((n.minFac : R) * (m : R)) ∈ P := by
      rw [← Nat.cast_mul, ← hm]; exact hmem
    rcases hP.mem_or_mem hmul with h | h
    · exact ⟨_, hpr, h⟩
    · have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hn hm
      have hlt : m < n := by
        rw [hm]
        have := hpr.two_le
        calc m = 1 * m := (one_mul m).symm
          _ < n.minFac * m := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.pos_of_ne_zero hm0)
      exact ih m hlt hm0 h

theorem exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by
  haveI := v.isPrime
  exact exists_prime_natCast_mem v.asIdeal (Ideal.absNorm v.asIdeal)
    (Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot) (Ideal.absNorm_mem _)

theorem target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v :=
  fun v => exists_prime_mem_heightOneSpectrum v

end GlobalTheory.PrimeInHeightOneSpectrum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimitiveElementUnramified
section
open IsLocalRing Polynomial

namespace GlobalTheory

open IsLocalRing Polynomial in
private lemma residue_eval_map_eq {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    residue R ((P.map φ).eval x) =
      (P.map (residue A)).eval₂ (ResidueField.map φ) (residue R x) := by
  rw [eval_map, hom_eval₂, eval₂_map]
  congr 1


open IsLocalRing Polynomial in
theorem _root_.GlobalTheory.exists_hensel_generator_of_residue_finite_unramified : ∀ {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R] (φ : A →+* R) [IsLocalHom φ], ((residue R).comp φ).Finite → ((residue R).comp φ).FormallyUnramified → ∃ (θ : R) (q : Polynomial A), q.Monic ∧ (q.map φ).eval θ = 0 ∧ IsUnit ((q.derivative.map φ).eval θ) ∧ (∀ r : R, ∃ P : Polynomial A, r - (P.map φ).eval θ ∈ maximalIdeal R) ∧ ∀ P : Polynomial A, P.natDegree < q.natDegree → (P.map φ).eval θ ∈ maximalIdeal R → ∀ i, P.coeff i ∈ maximalIdeal A := by
  intro A R _ _ _ _ _ φ _ hfin hunr
  have hcomp : (residue R).comp φ = (ResidueField.map φ).comp (residue A) :=
    RingHom.ext fun a => (ResidueField.map_residue φ a).symm
  rw [hcomp] at hfin hunr
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hfin.of_comp_finite
  haveI : Algebra.FormallyUnramified (ResidueField A) (ResidueField R) := hunr.of_comp
  haveI : Algebra.IsSeparable (ResidueField A) (ResidueField R) :=
    Algebra.FormallyUnramified.isSeparable _ _
  set pb := Field.powerBasisOfFiniteOfSeparable (ResidueField A) (ResidueField R)
  set f := minpoly (ResidueField A) pb.gen with hf
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hfroot : aeval pb.gen f = 0 := minpoly.aeval _ _
  have hfder : aeval pb.gen (derivative f) ≠ 0 :=
    (Algebra.IsSeparable.isSeparable _ pb.gen).aeval_derivative_ne_zero hfroot
  obtain ⟨q, hqf, hqdeg, hqmonic⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts f).2 (map_surjective (residue A) residue_surjective f)) hfmonic
  obtain ⟨θ₀, hθ₀⟩ := residue_surjective pb.gen
  have key : ∀ (P : A[X]) (x : R), residue R x = pb.gen →
      residue R ((P.map φ).eval x) = aeval pb.gen (P.map (residue A)) := by
    intro P x hx
    rw [residue_eval_map_eq, hx]
    rfl
  obtain ⟨θ, hroot, hθ⟩ := HenselianRing.is_henselian (I := maximalIdeal R) (q.map φ)
    (hqmonic.map φ) θ₀
    (by rw [← residue_eq_zero_iff, key _ _ hθ₀, hqf, hfroot])
    (by
      rw [derivative_map]
      change IsUnit (residue R _)
      rw [key _ _ hθ₀, ← derivative_map, hqf]
      exact isUnit_iff_ne_zero.2 hfder)
  have hθres : residue R θ = pb.gen := by
    rw [← hθ₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    exact hθ
  refine ⟨θ, q, hqmonic, hroot, ?_, ?_, ?_⟩
  · rw [← residue_ne_zero_iff_isUnit, key _ _ hθres, ← derivative_map, hqf]
    exact hfder
  · intro r
    obtain ⟨g, hg⟩ := pb.exists_eq_aeval' (residue R r)
    obtain ⟨P, hP⟩ := map_surjective (residue A) residue_surjective g
    refine ⟨P, ?_⟩
    rw [← residue_eq_zero_iff, map_sub, key _ _ hθres, hP, hg, sub_self]
  · intro P hdeg hmem i
    rw [← residue_eq_zero_iff, key _ _ hθres] at hmem
    have hzero : P.map (residue A) = 0 := by
      by_contra hne
      have h1 := minpoly.degree_le_of_ne_zero (ResidueField A) pb.gen hne hmem
      have h2 := natDegree_le_natDegree h1
      have h3 : (P.map (residue A)).natDegree ≤ P.natDegree := natDegree_map_le
      rw [← hf, ← hqdeg] at h2
      omega
    rw [← residue_eq_zero_iff, ← coeff_map, hzero, coeff_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryMulUpperTriangular
section
namespace GlobalTheory.UnitaryUpperTriangular

open Module InnerProductSpace

theorem exists_unitary_mul_upperTriangular {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) :
    ∃ u ∈ Matrix.unitaryGroup (Fin n) ℂ, ∃ (t : Matrix (Fin n) (Fin n) ℂ),
      Matrix.BlockTriangular t id ∧ y = u * t := by
  classical
  let f : Fin n → EuclideanSpace ℂ (Fin n) := fun i => WithLp.toLp 2 (fun k => y k i)
  have h : finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n) := finrank_euclideanSpace
  let a := EuclideanSpace.basisFun (Fin n) ℂ
  let b := gramSchmidtOrthonormalBasis h f
  refine ⟨a.toBasis.toMatrix b, a.toMatrix_orthonormalBasis_mem_unitary b,
    b.toBasis.toMatrix f, gramSchmidtOrthonormalBasis_inv_isUpperTriangular h f, ?_⟩
  rw [← b.coe_toBasis, Basis.toMatrix_mul_toMatrix]
  ext k i
  simp [Basis.toMatrix_apply, a, f]

end GlobalTheory.UnitaryUpperTriangular
end

