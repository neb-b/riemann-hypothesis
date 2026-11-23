module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TorsionTotientBound
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.TorsionReduceInjective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.MassNumeric
section
namespace UpperTheory.Mu

theorem numeric_bound {ι : Type} [Fintype ι] {w : ℕ} (f n r : ℕ) (hcard : Fintype.card ι = f) (L' dmax mass dim idx nrm E dO dS : ℝ)
    (H dk J deg : ι → ℝ) (h8 : 8 ≤ n) (h2 : 2 * r ≤ n) (h1 : 1 ≤ r) (hf : 1 ≤ f) (hL : (5.5 : ℝ) ≤ L') (hn : Real.log n ≤ L')
    (hd0 : 0 ≤ dmax) (hd : Real.log (dmax + 2) ≤ 2 * L') (hw0 : 0 < w) (hw : w ≤ 8 * f ^ 2)
    (hm : 1 / ((w : ℝ) ^ n * (n.factorial : ℝ)) ≤ mass) (hdim : 1 ≤ dim)
    (hidx : idx * nrm = dS⁻¹) (hE : Real.exp (-(r * (2 * f))) ≤ E) (hO : 0 < dO ∧ dO ≤ Real.exp (2 * (r * (2 * f))))
    (hS : 0 < dS ∧ dS ≤ Real.exp (2 * (r * (2 * f)))) (hH : ∀ ρ, 0 < H ρ) (hk : ∀ ρ, 1 ≤ dk ρ) (hJ : ∀ ρ, 0 < J ρ)
    (hdeg : ∀ ρ, 0 ≤ deg ρ ∧ deg ρ ≤ dmax)
    (hJb : ∀ ρ, Real.log (J ρ)⁻¹ ≤ 2 + (r : ℝ) ^ 2 * Real.log (2 * Real.sqrt 2 * (r : ℝ) ^ 2 * n * (deg ρ + 2))) :
    0 < (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E ∧
      ∑ ρ, Real.log (H ρ) - 8 * f * (n : ℝ) ^ 2 * L' ≤
        Real.log ((∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E) := by
  obtain ⟨e⟩ : Nonempty (Fin f ≃ ι) := ⟨(Fintype.equivFinOfCardEq hcard).symm⟩
  have hw1 : (0 : ℝ) < w := by exact_mod_cast hw0
  have hc : 0 < ((w : ℝ) / 2) ^ n := by positivity
  have hm' : 1 / ((2 : ℝ) ^ n * (n.factorial : ℝ)) ≤ ((w : ℝ) / 2) ^ n * mass := by
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hm hc.le)
    have : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
    rw [div_pow]
    field_simp
  have hm0 : 0 < mass := lt_of_lt_of_le (by positivity) hm
  have hE0 : 0 < E := lt_of_lt_of_le (Real.exp_pos _) hE
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hn8 : (8 : ℝ) ≤ n := by exact_mod_cast h8
  have hrn : 2 * (r : ℝ) ≤ n := by exact_mod_cast h2
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hs : Real.sqrt 2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have key := GlobalTheory.lamLow_numerical_end f n r L' dmax (((w : ℝ) / 2) ^ n * mass * dim) 1 _ (fun a => H (e a)) (fun _ => 1) (fun a => dk (e a))
    (fun a => (J (e a))⁻¹) h8 h2 h1 hf hL hn hd0 hd (hm'.trans (le_mul_of_one_le_right (mul_pos hc hm0).le hdim)) one_pos
    (by rw [Real.log_one, abs_zero]; positivity)
    (fun a => ⟨hH _, le_rfl, hk _, inv_pos.2 (hJ _), (hJb _).trans (by
      have := (hdeg (e a)).1
      have := (hdeg (e a)).2
      gcongr
      linarith)⟩) rfl
  rw [e.sum_comp fun ρ => Real.log (H ρ), e.prod_comp fun ρ => H ρ * 1 * dk ρ / (J ρ)⁻¹] at key
  have hP : 0 < mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ := by
    refine mul_pos (by positivity) (Finset.prod_pos fun ρ _ => ?_)
    have := hH ρ; have := hk ρ; have := hJ ρ
    positivity
  have hlw : Real.log (((w : ℝ) / 2) ^ n) ≤ 4 * (n * f) := by
    have b0 : (w : ℝ) / 2 ≤ (2 * f) ^ 2 := by
      have : (w : ℝ) ≤ 8 * (f : ℝ) ^ 2 := by exact_mod_cast hw
      linarith
    have b1 := Real.log_le_log (by positivity) b0
    have b2 := Real.log_le_sub_one_of_pos (x := 2 * (f : ℝ)) (by positivity)
    rw [Real.log_pow] at b1 ⊢
    push_cast at b1
    have : Real.log ((w : ℝ) / 2) ≤ 4 * f := by linarith only [b1, b2]
    linarith only [mul_le_mul_of_nonneg_left this (Nat.cast_nonneg (α := ℝ) n)]
  rw [show ((w : ℝ) / 2) ^ n * mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹ =
    ((w : ℝ) / 2) ^ n * (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) by ring, Real.log_mul hc.ne' hP.ne'] at key
  have e1 : (∏ ρ, dk ρ) * dim * (idx * mass) * (∏ ρ, H ρ) * nrm / dO * (∏ ρ, J ρ) * E =
      (mass * dim * 1 * ∏ ρ, H ρ * 1 * dk ρ / (J ρ)⁻¹) * (E / (dO * dS)) := by
    simp only [div_inv_eq_mul, mul_one, Finset.prod_mul_distrib]
    have : idx * nrm * dS = 1 := by rw [hidx, inv_mul_cancel₀ hS.1.ne']
    have h3 := hO.1.ne'
    have h4 := hS.1.ne'
    field_simp
    linear_combination ((∏ ρ, dk ρ) * (∏ ρ, H ρ) * (∏ ρ, J ρ)) * this
  have hq : 0 < E / (dO * dS) := div_pos hE0 (mul_pos hO.1 hS.1)
  rw [e1]
  refine ⟨mul_pos hP hq, ?_⟩
  rw [Real.log_mul hP.ne' hq.ne', Real.log_div hE0.ne' (mul_pos hO.1 hS.1).ne', Real.log_mul hO.1.ne' hS.1.ne']
  have a1 := (Real.le_log_iff_exp_le hE0).2 hE
  have a2 := (Real.log_le_iff_le_exp hO.1).2 hO.2
  have a3 := (Real.log_le_iff_le_exp hS.1).2 hS.2
  have a4 : 10 * ((r : ℝ) * f) + 4 * (n * f) ≤ 6 * (f * (n : ℝ) ^ 2 * L') := by
    have b0 : (0 : ℝ) ≤ f := Nat.cast_nonneg _
    have b1 : (r : ℝ) * f ≤ n * f := mul_le_mul_of_nonneg_right (by linarith only [hrn, hr]) b0
    have b2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith only [hn8]
    have b3 : (n : ℝ) * f ≤ (n : ℝ) ^ 2 * f := mul_le_mul_of_nonneg_right b2 b0
    have b4 : (n : ℝ) ^ 2 * f * 5.5 ≤ (n : ℝ) ^ 2 * f * L' := mul_le_mul_of_nonneg_left hL (by positivity)
    have b5 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
    linarith only [b1, b3, b4, b5]
  linarith only [key, hlw, a1, a2, a3, a4]

end UpperTheory.Mu
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Monomial
section
open NumberField Matrix

namespace UpperTheory.Mu

variable {K : Type} [Field K] [NumberField K]

private theorem finrank_le_sum_sq_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    (Module.finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (GlobalTheory.finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast GlobalTheory.one_le_abs_norm_of_isIntegral hx h0
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow h1 (by positivity))

private theorem exists_single_of_sum_star_mul {n : ℕ} [Star K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (z : Fin n → K) (hz : ∀ i, IsIntegral ℤ (z i)) (h1 : ∑ i, star (z i) * z i = 1) :
    ∃ i, ∀ j, j ≠ i → z j = 0 := by
  have hφ : ∀ φ : K →+* ℂ, ∑ i, ‖φ (z i)‖ ^ 2 = 1 := by
    intro φ
    have h := congrArg φ h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one] at h
    have h2 : ∀ i, φ (star (z i) * z i) = ((‖φ (z i)‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [map_mul, hconj, Complex.conj_mul']
      push_cast
      rfl
    simp_rw [h2] at h
    exact_mod_cast h
  have htot : ∑ i, ∑ φ : K →+* ℂ, ‖φ (z i)‖ ^ 2 = (Module.finrank ℚ K : ℝ) := by
    rw [Finset.sum_comm]
    simp [hφ, Embeddings.card]
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
    by_contra hall
    push_neg at hall
    simp [hall] at h1
  refine ⟨i, fun j hji => ?_⟩
  by_contra hj
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ ∑ φ : K →+* ℂ, ‖φ (z k)‖ ^ 2 :=
    fun k _ => Finset.sum_nonneg fun _ _ => by positivity
  have hsub := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ {i, j})
    (fun k hk _ => hnn k hk)
  rw [Finset.sum_pair (Ne.symm hji), htot] at hsub
  have := finrank_le_sum_sq_of_isIntegral (hz i) hi
  have := finrank_le_sum_sq_of_isIntegral (hz j) hj
  linarith

theorem torsionOrder_le (K : Type) [Field K] [NumberField K] : Units.torsionOrder K ≤ 2 * Module.finrank ℚ K ^ 2 :=
  Formalism.L2.SG.NGCut.TorsionTotientBound.torsionOrder_le K

theorem pow_torsionOrder_eq_one {x : K} (hx : IsIntegral ℤ x) (h : ∀ φ : K →+* ℂ, ‖φ x‖ = 1) :
    x ^ Units.torsionOrder K = 1 := by
  obtain ⟨n, hn, hxn⟩ := Embeddings.pow_eq_one_of_norm_eq_one K ℂ hx h
  obtain ⟨y, rfl⟩ : ∃ y : 𝓞 K, (y : K) = x := ⟨⟨x, hx⟩, rfl⟩
  have hyn : y ^ n = 1 := by
    apply RingOfIntegers.coe_injective
    simpa using hxn
  have hmem : Units.ofPowEqOne y n hyn hn.ne' ∈ Units.torsion K := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨n, hn, Units.ext (by simpa using hyn)⟩
  rw [← Units.rootsOfUnity_eq_torsion, mem_rootsOfUnity] at hmem
  have := congrArg (fun v : (𝓞 K)ˣ => ((v : 𝓞 K) : K)) hmem
  simpa using this

theorem norm_eq_one_of_star_mul [Star K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    {z : K} (h1 : star z * z = 1) (φ : K →+* ℂ) : ‖φ z‖ = 1 := by
  have h3 := congrArg φ h1
  rw [map_mul, hconj, map_one, Complex.conj_mul'] at h3
  have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4

theorem exists_monomial [StarRing K] (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x))
    (n : ℕ) (g : Matrix (Fin n) (Fin n) K) (hg : gᴴ * g = 1) (hint : ∀ a b, IsIntegral ℤ (g a b)) :
    ∃ (t : Fin n → K) (σ : Equiv.Perm (Fin n)), (∀ b, t b ^ Units.torsionOrder K = 1) ∧
      g = Matrix.of fun a b => if a = σ b then t b else 0 := by
  have hcol : ∀ b, ∑ a, star (g a b) * g a b = 1 := by
    intro b
    have h := congrFun (congrFun hg b) b
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using h
  have horth : ∀ b b', b ≠ b' → ∑ a, star (g a b) * g a b' = 0 := by
    intro b b' hbb
    have h := congrFun (congrFun hg b) b'
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_ne hbb] using h
  choose f hf using fun b => exists_single_of_sum_star_mul hconj (fun a => g a b)
    (fun a => hint a b) (hcol b)
  have hdiag : ∀ b, star (g (f b) b) * g (f b) b = 1 := by
    intro b
    have h := hcol b
    rwa [Finset.sum_eq_single (f b) (fun j _ hj => by simp [hf b j hj]) (by simp)] at h
  have hne : ∀ b, g (f b) b ≠ 0 := by
    intro b h
    have h' := hdiag b
    simp [h] at h'
  have hinj : Function.Injective f := by
    intro b b' hbb
    by_contra hb
    have h := horth b b' hb
    rw [Finset.sum_eq_single (f b) (fun j _ hj => by simp [hf b j hj]) (by simp)] at h
    rcases mul_eq_zero.mp h with h | h
    · exact hne b (star_eq_zero.mp h)
    · rw [hbb] at h
      exact hne b' h
  refine ⟨fun b => g (f b) b, Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj),
    fun b => pow_torsionOrder_eq_one (hint _ _) (norm_eq_one_of_star_mul hconj (hdiag b)), ?_⟩
  ext a b
  simp only [Matrix.of_apply, Equiv.ofBijective_apply]
  split_ifs with h
  · rw [h]
  · exact hf b a h

theorem unitary_integral_finite_and_ncard_le [StarRing K]
    (hconj : ∀ (φ : K →+* ℂ) (x : K), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ) :
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.Finite ∧
    {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)}.ncard
      ≤ Units.torsionOrder K ^ n * n.factorial := by
  classical
  have hT : 0 < Units.torsionOrder K := Units.torsionOrder_pos K
  let R : Finset K := (Polynomial.nthRoots (Units.torsionOrder K) (1 : K)).toFinset
  let P : Finset ((Fin n → K) × Equiv.Perm (Fin n)) :=
    Fintype.piFinset (fun _ => R) ×ˢ Finset.univ
  let Φ : (Fin n → K) × Equiv.Perm (Fin n) → Matrix (Fin n) (Fin n) K :=
    fun p => Matrix.of fun a b => if a = p.2 b then p.1 b else 0
  have hsub : {g : Matrix (Fin n) (Fin n) K | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} ⊆
      ↑(P.image Φ) := by
    rintro g ⟨hg, hint⟩
    obtain ⟨t, σ, ht, rfl⟩ := exists_monomial hconj n g hg hint
    rw [Finset.coe_image]
    refine ⟨(t, σ), ?_, rfl⟩
    simp [P, R, Finset.mem_coe, Finset.mem_product, Fintype.mem_piFinset, Multiset.mem_toFinset,
      Polynomial.mem_nthRoots hT, ht]
  refine ⟨(P.image Φ).finite_toSet.subset hsub, ?_⟩
  calc _ ≤ (↑(P.image Φ) : Set (Matrix (Fin n) (Fin n) K)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (P.image Φ).card := Set.ncard_coe_finset _
    _ ≤ P.card := Finset.card_image_le
    _ = R.card ^ n * n.factorial := by
        simp [P, Fintype.card_piFinset, Fintype.card_perm]
    _ ≤ Units.torsionOrder K ^ n * n.factorial := by
        gcongr
        exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots _ _)

end UpperTheory.Mu
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.ResidueEisenstein
section
open NumberField IsDedekindDomain

namespace UpperTheory.Mu

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem tame_ext_prime {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    (ε : (𝓞 L)ˣ →* ℂˣ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) = ε ζ := by
  have hv' : v.asIdeal ≠ ⊤ := v.isPrime.ne_top
  have hpos := Units.torsionOrder_pos L
  have hn : ((Units.torsionOrder L : ℕ) : 𝓞 L) ∉ v.asIdeal := by
    intro hn
    have hcop : Nat.Coprime (Units.torsionOrder L) p := by
      rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
      intro hd
      have := Nat.le_of_dvd hpos hd
      omega
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have h1 : (1 : 𝓞 L) = (a : 𝓞 L) * ((Units.torsionOrder L : ℕ) : 𝓞 L) + (b : 𝓞 L) * ((p : ℕ) : 𝓞 L) := by
      have := congrArg (Int.cast : ℤ → 𝓞 L) hab
      push_cast at this
      exact this.symm
    apply hv'
    rw [Ideal.eq_top_iff_one, h1]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hn) (v.asIdeal.mul_mem_left _ hv)
  have hN : Units.torsionOrder L + 1 < Ideal.absNorm v.asIdeal := by
    have hd : Ideal.absNorm v.asIdeal ∣ p ^ Module.finrank ℤ (𝓞 L) := by
      have h1 := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hv)
      rwa [Ideal.absNorm_span_singleton, show ((p : ℕ) : 𝓞 L) = algebraMap ℤ (𝓞 L) (p : ℤ) by simp,
        Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast] at h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hd
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hv' (Ideal.absNorm_eq_one_iff.1 (by simpa using hk))
    rw [hk]
    exact lt_of_lt_of_le hw (Nat.le_self_pow hk0 p)
  obtain ⟨θ, hθ, hθε⟩ := tame_ext L v hn hN (ε.comp (Units.torsion L).subtype)
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  obtain ⟨m, hm, hζm⟩ := hζ
  have hmem : ζ ∈ Units.torsion L := by
    rw [Units.torsion, CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    refine ⟨m, hm, ?_⟩
    apply Units.ext
    apply RingOfIntegers.ext
    simpa using hζm
  exact hθε ⟨ζ, hmem⟩

theorem tame_par {p : ℕ} (hp : p.Prime) (hw : Units.torsionOrder L + 1 < p) (hv : (p : 𝓞 L) ∈ v.asIdeal)
    {I : Type} [Fintype I] (φ : I → L →+* ℂ) (e : I → ℤ) :
    ∃ θ : (𝓞 L ⧸ v.asIdeal)ˣ →* ℂˣ, θ ≠ 1 ∧ ∀ ζ : (𝓞 L)ˣ, (∃ m : ℕ, 0 < m ∧ ((ζ : 𝓞 L) : L) ^ m = 1) →
      (∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i) * ((θ (Units.map (Ideal.Quotient.mk v.asIdeal).toMonoidHom ζ) : ℂˣ) : ℂ) = 1 := by
  classical
  let f : I → (𝓞 L)ˣ →* ℂˣ := fun i =>
    (zpowGroupHom (e i)).comp (Units.map ((φ i).toMonoidHom.comp (algebraMap (𝓞 L) L).toMonoidHom))
  obtain ⟨θ, hθ, hθε⟩ := tame_ext_prime v hp hw hv (∏ i, f i)⁻¹
  refine ⟨θ, hθ, fun ζ hζ => ?_⟩
  have hf : (((∏ i, f i ζ : ℂˣ)) : ℂ) = ∏ i, φ i ((ζ : 𝓞 L) : L) ^ e i := by
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [f, Units.val_zpow_eq_zpow_val]
  rw [hθε ζ hζ, MonoidHom.inv_apply, MonoidHom.finsetProd_apply, ← hf]
  exact Units.mul_inv _

theorem exists_unit_of_root {z : L} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∃ ζ : (𝓞 L)ˣ, ((ζ : 𝓞 L) : L) = z := by
  obtain ⟨m, hm, hzm⟩ := hz
  have hint : IsIntegral ℤ z := by
    refine IsIntegral.of_pow hm ?_
    rw [hzm]
    exact isIntegral_one
  let y : 𝓞 L := ⟨z, hint⟩
  have hy : y ^ m = 1 := by
    apply RingOfIntegers.ext
    push_cast
    exact hzm
  exact ⟨(IsUnit.of_pow_eq_one hy hm.ne').unit, rfl⟩

end UpperTheory.Mu
end

