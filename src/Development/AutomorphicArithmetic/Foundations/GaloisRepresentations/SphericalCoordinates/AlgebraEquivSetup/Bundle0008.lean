module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.QuadraticExtensions

private lemma sq_in_Zq (q : ℕ) [Fact q.Prime] (d g d0 : ℕ) (hg : 0 < g) (hd : g ^ 2 * d0 = d)
    (h : IsSquare (-(d : ℚ_[q]))) : ∃ z : ℤ_[q], z ^ 2 = -(d0 : ℤ_[q]) := by
  obtain ⟨y, hy⟩ := h
  have hg0 : (g : ℚ_[q]) ≠ 0 := by exact_mod_cast hg.ne'
  have hd' : (d : ℚ_[q]) = (g : ℚ_[q]) ^ 2 * d0 := by rw [← hd]; push_cast; ring
  rw [hd'] at hy
  have hx : (y / g) ^ 2 = -(d0 : ℚ_[q]) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hg0)]
    linear_combination -hy
  have hxn : ‖y / (g : ℚ_[q])‖ ≤ 1 := by
    have h1 : ‖y / (g : ℚ_[q])‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hx, norm_neg]
      have : ‖((d0 : ℤ_[q]) : ℚ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      simpa using this
    by_contra hc
    push_neg at hc
    nlinarith
  let z : ℤ_[q] := ⟨y / g, hxn⟩
  have hzc : (z : ℚ_[q]) = y / g := rfl
  refine ⟨z, ?_⟩
  have hc : ((z ^ 2 : ℤ_[q]) : ℚ_[q]) = ((-(d0 : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) := by
    push_cast
    rw [hzc]
    exact hx
  first
    | exact PadicInt.ext hc
    | exact Subtype.ext hc
    | exact PadicInt.coe_injective hc

private lemma not_dvd (q : ℕ) [hq : Fact q.Prime] (d0 : ℕ) (hsq : Squarefree d0) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ¬ q ∣ d0 := by
  intro hdvd
  have hnorm : ‖z‖ ^ 2 = ‖((d0 : ℤ) : ℤ_[q])‖ := by
    rw [← norm_pow, hz, norm_neg, Int.cast_natCast]
  have hd1 : ‖((d0 : ℤ) : ℤ_[q])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
  have hz1 : ‖z‖ < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg z]
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp hz1
  have hle : ‖((d0 : ℤ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(2 : ℕ) : ℤ) := by
    rw [← hnorm, norm_mul, PadicInt.norm_p, mul_pow]
    have hw := PadicInt.norm_le_one w
    have he : (q : ℝ) ^ (-(2 : ℕ) : ℤ) = ((q : ℝ)⁻¹) ^ 2 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_pow]
    rw [he]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg w) hw)
  have h2 := PadicInt.norm_int_le_pow_iff_dvd.mp hle
  have h3 : q ^ 2 ∣ d0 := by exact_mod_cast h2
  rw [sq] at h3
  exact (Nat.Prime.one_lt hq.out).ne' (Nat.isUnit_iff.mp (hsq q h3))

private lemma root_mod (q : ℕ) [Fact q.Prime] (d0 : ℕ) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 + d0 := by
  refine ⟨((PadicInt.toZMod z).val : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  have h := congrArg (PadicInt.toZMod (p := q)) hz
  simp only [map_pow, map_neg, map_natCast] at h
  push_cast
  rw [ZMod.natCast_zmod_val, h]
  ring

private lemma two_case [Fact (Nat.Prime 2)] (d0 : ℕ) (hodd : ¬ 2 ∣ d0) (z : ℤ_[2])
    (hz : z ^ 2 = -(d0 : ℤ_[2])) : d0 % 8 = 7 := by
  have h := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) hz
  rw [map_pow, map_neg, map_natCast] at h
  generalize (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) z = a at h
  revert a
  show ∀ a : ZMod 8, a ^ 2 = -((d0 : ZMod 8)) → d0 % 8 = 7
  rw [← ZMod.natCast_mod d0 8]
  have hlt := Nat.mod_lt d0 (by norm_num : 8 > 0)
  have hodd : d0 % 2 = 1 := by omega
  interval_cases h8 : d0 % 8
  all_goals first | omega | decide

private lemma not_dvd_four (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : ¬ (q : ℤ) ∣ 4 := by
  intro h
  have h' : q ∣ 2 ^ 2 := by exact_mod_cast h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h'))

private lemma root_odd (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (d0 m : ℕ) (hm : d0 + 1 = 4 * m) (r0 : ℤ)
    (hr : (q : ℤ) ∣ r0 ^ 2 + d0) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - 1 * r + m := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q + 1 = 2 * k := by
    rcases hq.eq_two_or_odd' with h | ⟨j, hj⟩
    · exact absurd h h2
    · exact ⟨j + 1, by omega⟩
  refine ⟨(r0 + 1) * k, ?_⟩
  have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have h4 : (q : ℤ) ∣ 4 * (((r0 + 1) * k) ^ 2 - 1 * ((r0 + 1) * k) + m) := by
    obtain ⟨c, hc⟩ := hr
    have hk' : (2 * k : ℤ) = q + 1 := by exact_mod_cast hk.symm
    have hm' : (4 * m : ℤ) = d0 + 1 := by exact_mod_cast hm.symm
    refine ⟨c + (r0 + 1) * (2 * r0 + (r0 + 1) * q), ?_⟩
    linear_combination ((r0 + 1) ^ 2 * (2 * (k : ℤ) + q + 1) - 2 * (r0 + 1)) * hk' + hm' + hc
  rcases hpz.dvd_or_dvd h4 with h | h
  · exact absurd h (not_dvd_four q hq h2)
  · exact h

end UpperTheory.Gal.W2.Seed.QuadraticExtensions

open UpperTheory.Gal.W2.Seed.QuadraticExtensions in
theorem UpperTheory.Gal.W2.Seed.pQuadEx :
    QuadEx := by
  intro d hd
  obtain ⟨d0, g, hgd, hsq⟩ := Nat.sq_mul_squarefree d
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hd0 : 0 < d0 := by
    rcases Nat.eq_zero_or_pos d0 with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdq : (d : ℚ) = (g : ℚ) ^ 2 * d0 := by rw [← hgd]; push_cast; ring
  by_cases h43 : d0 % 4 = 3
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, d0 + 1 = 4 * m := ⟨(d0 + 1) / 4, by omega⟩
    have hdisc : (1 : ℤ) ^ 2 - 4 * (m : ℤ) = -(d0 : ℤ) := by
      have : ((d0 : ℤ) + 1) = 4 * (m : ℤ) := by exact_mod_cast hm
      linarith
    refine ⟨1, m, 1 / (g : ℚ), ?_, ?_, ?_⟩
    · rw [hdisc]; omega
    · rw [hdisc, hdq]; push_cast; field_simp
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · rw [hdisc, dvd_neg]
        intro h
        exact hnd (by exact_mod_cast h)
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          refine ⟨0, ?_⟩
          have : (m : ℤ) % 2 = 0 := by omega
          push_cast
          omega
        · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
          exact root_odd q (Fact.out) hq2 d0 m hm r0 hr0
  · refine ⟨0, d0, 2 / (g : ℚ), ?_, ?_, ?_⟩
    · omega
    · rw [hdq]; push_cast; field_simp; ring
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          omega
        · have hq : q.Prime := Fact.out
          have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
          intro h
          have h' : (q : ℤ) ∣ 4 * (d0 : ℤ) := by
            have : (0 : ℤ) ^ 2 - 4 * (d0 : ℤ) = -(4 * (d0 : ℤ)) := by ring
            rw [this, dvd_neg] at h
            exact h
          rcases hpz.dvd_or_dvd h' with h4 | h4
          · exact not_dvd_four q hq hq2 h4
          · exact hnd (by exact_mod_cast h4)
      · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
        exact ⟨r0, by simpa using hr0⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRealIso
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma realForm_eq_zero {E : Type} [Field E] [NumberField E] {P : Type} [Fintype P] (g : P → (E →+* ℂ))
    (hg : Function.Injective (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p))))
    (u v : P → ℝ) (h : ∀ x : 𝓞 E, ∑ p, (u p * (g p (x : E)).re + v p * (g p (x : E)).im) = 0) :
    ∀ p, u p = 0 ∧ v p = 0 := by
  classical
  let σ : P ⊕ P → (E →* ℂ) := fun k =>
    (Sum.elim g (fun p => ComplexEmbedding.conjugate (g p)) k).toMonoidHom
  have hσ : Function.Injective σ := by
    intro k l hkl
    apply hg
    ext x
    exact DFunLike.congr_fun hkl x
  have hli : LinearIndependent ℂ (fun k => (σ k : E → ℂ)) :=
    (linearIndependent_monoidHom E ℂ).comp σ hσ
  have hE : ∀ x : E, ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
    intro x
    obtain ⟨d, hd, hdx⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
    obtain ⟨w, hw⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hdx x (Finset.mem_singleton_self x))
    have h1 := h w
    have hw' : (w : E) = (d : E) * x := by
      rw [← zsmul_eq_mul, ← hw]
    rw [hw'] at h1
    simp only [map_mul, map_intCast, Complex.mul_re, Complex.mul_im, Complex.intCast_re,
      Complex.intCast_im, zero_mul, sub_zero, add_zero] at h1
    have h3 : (d : ℝ) * ∑ p, (u p * (g p x).re + v p * (g p x).im) = 0 := by
      rw [Finset.mul_sum, ← h1]
      exact Finset.sum_congr rfl fun p _ => by ring
    rcases mul_eq_zero.mp h3 with h2 | h2
    · exact absurd (Int.cast_eq_zero.mp h2) hd
    · exact h2
  let c : P ⊕ P → ℂ := Sum.elim (fun p => ((u p : ℂ) - Complex.I * v p) / 2)
    (fun p => ((u p : ℂ) + Complex.I * v p) / 2)
  have hterm : ∀ p (x : E), ((u p : ℂ) - Complex.I * v p) / 2 * g p x +
      ((u p : ℂ) + Complex.I * v p) / 2 * ComplexEmbedding.conjugate (g p) x =
      ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) := by
    intro p x
    rw [ComplexEmbedding.conjugate_coe_eq]
    apply Complex.ext <;> simp <;> ring
  have hsum : ∑ k, c k • (σ k : E → ℂ) = 0 := by
    funext x
    rw [Finset.sum_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    calc _ = ∑ p, ((u p * (g p x).re + v p * (g p x).im : ℝ) : ℂ) :=
          Finset.sum_congr rfl fun p _ => hterm p x
      _ = 0 := by rw [← Complex.ofReal_sum, hE x, Complex.ofReal_zero]
  have hc := (Fintype.linearIndependent_iff.mp hli) c hsum
  intro p
  have h1 : ((u p : ℂ) - Complex.I * v p) / 2 = 0 := hc (Sum.inl p)
  have h1' : (u p : ℂ) - Complex.I * v p = 0 := by
    rcases div_eq_zero_iff.mp h1 with h | h
    · exact h
    · norm_num at h
  constructor
  · have h4 := congrArg Complex.re h1'
    simpa using h4
  · have h4 := congrArg Complex.im h1'
    simpa using h4

theorem UpperTheory.Gal.W2.Seed.pRealIso :
    TraceType → RealIso := by
  intro hT E _ _ _ A n
  classical
  obtain ⟨-, -, hpl, him⟩ := hT E A
  have hcardPhi : Fintype.card (Phi A) = Fintype.card (InfinitePlace E) := by
    refine Fintype.card_congr (Equiv.ofBijective (fun τ : Phi A => InfinitePlace.mk τ.1) ⟨?_, ?_⟩)
    · intro a b hab
      exact (hpl (InfinitePlace.mk a.1)).unique rfl hab.symm
    · intro v
      obtain ⟨τ, hτ, -⟩ := hpl v
      exact ⟨τ, hτ⟩
  have hrank : 2 * Fintype.card (InfinitePlace E) = Module.finrank ℚ E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero E]
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E] at h1
    omega
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let b1 := Algebra.TensorProduct.basis ℝ bZ
  let F : (Fin n → 𝓞 E) →ₗ[ℤ] (Phi A × Fin n → ℂ) :=
    LinearMap.pi (fun p : Phi A × Fin n =>
      ((p.1.1.comp (algebraMap (𝓞 E) E)).toIntAlgHom.toLinearMap) ∘ₗ LinearMap.proj p.2)
  let L : ℝ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℝ] (Phi A × Fin n → ℂ) := b1.constr ℝ (fun k => F (bZ k))
  have hL : ∀ x, L (1 ⊗ₜ x) = F x := by
    have hcomp : (L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1 = F := by
      refine bZ.ext fun k => ?_
      have hk : ((L.restrictScalars ℤ) ∘ₗ TensorProduct.mk ℤ ℝ (Fin n → 𝓞 E) 1) (bZ k) =
          L (b1 k) := by
        rw [Algebra.TensorProduct.basis_apply]
        rfl
      rw [hk, Module.Basis.constr_basis]
    intro x
    exact LinearMap.congr_fun hcomp x
  have dec : ∀ (φ : Module.Dual ℝ (Phi A × Fin n → ℂ)) p (w : ℂ),
      φ (Pi.single p w) = w.re * φ (Pi.single p 1) + w.im * φ (Pi.single p Complex.I) := by
    intro φ p w
    have hw : (Pi.single p w : Phi A × Fin n → ℂ) =
        w.re • (Pi.single p (1 : ℂ) : Phi A × Fin n → ℂ) +
          w.im • (Pi.single p Complex.I : Phi A × Fin n → ℂ) := by
      ext q
      by_cases hq : q = p
      · subst hq
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
        apply Complex.ext <;> simp
      · simp [Pi.single_apply, hq]
    rw [hw, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hg : Function.Injective
      (Sum.elim (fun τ : Phi A => τ.1) (fun τ : Phi A => ComplexEmbedding.conjugate τ.1)) := by
    have hcross : ∀ a b : Phi A, a.1 ≠ ComplexEmbedding.conjugate b.1 := by
      intro a b h
      have h2 := RingHom.congr_fun h (A.ω : E)
      rw [ComplexEmbedding.conjugate_coe_eq, a.2, b.2] at h2
      have h3 := congrArg Complex.im h2
      rw [Complex.conj_im] at h3
      exact him (by linarith)
    rintro (a | a) (b | b) h
    · exact congrArg _ (Subtype.ext h)
    · exact absurd h (hcross a b)
    · exact absurd h.symm (hcross b a)
    · simp only [Sum.elim_inr] at h
      have h' : (a.1 : E →+* ℂ) = b.1 := by
        ext x
        have hx := RingHom.congr_fun h x
        rw [ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq] at hx
        simpa using congrArg (starRingEnd ℂ) hx
      exact congrArg _ (Subtype.ext h')
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    have hvan : ∀ y, φ (L y) = 0 := by
      intro y
      have hm : φ (L y) ∈ (LinearMap.range L).map φ := ⟨L y, ⟨y, rfl⟩, rfl⟩
      rw [hφ] at hm
      exact (Submodule.mem_bot ℝ).mp hm
    have huv : ∀ i : Fin n, ∀ τ : Phi A,
        φ (Pi.single (τ, i) 1) = 0 ∧ φ (Pi.single (τ, i) Complex.I) = 0 := by
      intro i
      refine realForm_eq_zero (fun τ : Phi A => τ.1) hg _ _ fun x => ?_
      have h1 := hvan (1 ⊗ₜ Pi.single i x)
      rw [hL] at h1
      have hFx : F (Pi.single i x) = ∑ τ : Phi A, Pi.single (τ, i) (τ.1 (x : E)) := by
        ext ⟨τ', i'⟩
        rw [Finset.sum_apply]
        by_cases hi : i' = i
        · subst hi
          rw [Finset.sum_eq_single τ']
          · simp [F]
          · intro τ _ hτ
            simp [Pi.single_apply, hτ]
          · simp
        · simp [F, Pi.single_apply, hi]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hFx, map_sum] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun τ _ => by rw [dec φ (τ, i) (τ.1 (x : E))]; ring
    apply hφ0
    refine LinearMap.ext fun z => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.zero_apply, ← Finset.univ_sum_single z, map_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    obtain ⟨τ, i⟩ := p
    rw [dec, (huv i τ).1, (huv i τ).2]
    simp
  have hdim : Module.finrank ℝ (ℝ ⊗[ℤ] (Fin n → 𝓞 E)) =
      Module.finrank ℝ (Phi A × Fin n → ℂ) := by
    rw [Module.finrank_eq_card_basis b1,
      Module.finrank_eq_card_basis (Pi.basis fun _ : Phi A × Fin n => Complex.basisOneI)]
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Fintype.card_fin, Fintype.card_prod]
    rw [← Module.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, ← hrank, hcardPhi]
    ring
  refine ⟨LinearEquiv.ofBijective L
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩, ?_⟩
  intro x τ i
  show L (1 ⊗ₜ x) (τ, i) = _
  rw [hL]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepAdj
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepAdj :
    RepAdj := by
  intro E _ _ _ A n rep hrep x a b
  obtain ⟨β, h1, h2⟩ := hrep
  have key : ∀ z w, LinearMap.BilinForm.baseChange ℚ (A.EF n) z w =
      Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * β z i * IsCMField.complexConj E (β w i)) := by
    have hσq : ∀ (q : ℚ) (b : E), IsCMField.complexConj E (q • b) = q • IsCMField.complexConj E b := by
      intro q b
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]
      simp
    have hEF : ∀ v u : Fin n → 𝓞 E, ((A.EF n v u : ℤ) : ℚ) =
        Algebra.trace ℚ E (A.δ * ∑ i, (A.hd n i : E) * v i * IsCMField.complexConj E (u i)) := by
      intro v u
      simp only [Arith.EF, LinearMap.mk₂_apply, A.trd_spec]
      push_cast
      simp only [A.bar_eq]
    intro z w
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp [ha, hb, add_mul, Finset.sum_add_distrib, mul_add]
    | tmul q v =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp [ha, hb, mul_add, Finset.sum_add_distrib]
      | tmul r u =>
        rw [LinearMap.BilinForm.baseChange_tmul]
        have e1 : q ⊗ₜ[ℤ] v = q • ((1:ℚ) ⊗ₜ[ℤ] v) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        have e2 : r ⊗ₜ[ℤ] u = r • ((1:ℚ) ⊗ₜ[ℤ] u) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [e1, e2, map_smul, map_smul]
        simp only [Pi.smul_apply, h1, hσq]
        have hS : ∑ x, (A.hd n x : E) * q • (v x : E) * r • IsCMField.complexConj E (u x : E) =
            (q * r) • ∑ x, (A.hd n x : E) * v x * IsCMField.complexConj E (u x : E) := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Algebra.smul_def, map_mul]
          ring
        rw [hS, mul_smul_comm, map_smul, ← hEF, zsmul_eq_mul, smul_eq_mul]
        ring
  have hreal : ∀ i, IsCMField.complexConj E (A.hd n i : E) = A.hd n i := by
    intro i
    have hc : IsCMField.complexConj E (A.c : E) = A.c := by
      rw [← A.bar_eq, A.c_real]
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  have hc0 : (A.c : E) ≠ 0 := by
    intro h
    have := A.c_neg
    rw [h, map_zero] at this
    simp at this
  have hne : ∀ i, (A.hd n i : E) ≠ 0 := by
    intro i
    simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc0]
  rw [key, key, h2, h2]
  congr 2
  generalize β a = p
  generalize β b = s
  have hD : ∀ d : Fin n → E, (∀ m, d m ≠ 0) → (diagonal d)⁻¹ = diagonal (fun m => (d m)⁻¹) := by
    intro d hd
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext m
    exact inv_mul_cancel₀ (hd m)
  have hx : ∀ j, (MulOpposite.unop ((hermStar (A.H n) (by
      simp only [Arith.H, Matrix.det_diagonal]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hne i)) x) *ᵥ s) j =
      (A.hd n j : E)⁻¹ * ∑ k, IsCMField.complexConj E (x k j) * A.hd n k * s k := by
    intro j
    simp only [hermStar, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, MulOpposite.unop_op, Arith.H]
    rw [Matrix.diagonal_map (map_zero _)]
    simp only [Function.comp_def, RingHom.coe_coe, hreal]
    rw [hD _ hne, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    rw [show ∀ d : Fin n → E, diagonal d *ᵥ s = fun m => d m * s m from fun d => funext (Matrix.mulVec_diagonal d s)]
    simp only [Matrix.mulVec, dotProduct, transpose_apply, map_apply, RingHom.coe_coe]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp only [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_inv₀, map_sum, hreal, IsCMField.complexConj_apply_apply, Matrix.mulVec, dotProduct]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  have := hne j
  field_simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pSetupBasic :
    SetupBasic := by
  intro E _ _ _ A n p _ S
  have key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀ := by
    intro v
    show sigPos (A.herm n) v.embedding = 1 ↔ _
    have h := S.sig v.embedding
    rw [InfinitePlace.mk_embedding] at h
    constructor
    · intro h1
      by_contra hne
      have h0 := (h.2 hne).1
      omega
    · intro hv
      exact (h.1 hv).1
  refine ⟨?_, (key _).2 rfl, fun h => ?_⟩
  · exact Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩,
      fun w => Subtype.ext ((key w.1).1 w.2)⟩
  · have h2 : 2 * 1 < Module.finrank ℚ E := by simpa using h
    exact ⟨Or.inl h2, Or.inl h2⟩
end

