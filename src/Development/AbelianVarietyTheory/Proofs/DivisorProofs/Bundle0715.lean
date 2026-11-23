module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0002
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.QuotientMetricDivisors.SixthReductionExplicit
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDegreeGapBound
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0703
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0685
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0699

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LossSumPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLossPrimes

theorem bound_one {D : D7} {L : SizeData₂ D} {c : ErrC}
    (hc : c.dig = 3) (P : ParameterChoice' D L) (hS : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| ≤ 2 * (9 * (1 / L.sc.eps + 1)) * L.B0 := by
  have hEg : ∀ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| = 2 * (Real.log (p : ℝ) * |(padicValNat p 1 : ℝ) +
    (if (p : ℝ) ≤ L.sc.X'' D.R.n then 3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
      (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1) else 0)|) := by
    intro p hp
    have e0 : padicValNat p 1 = 0 := by simp [_root_.Nat.padicValNat_def (n := 1)]
    rw [if_pos (hQ p hp).2, e0, Nat.cast_zero, zero_add]
    unfold EatC Formalism.MainNotions.G.Nm
    rw [hc, mul_assoc]
  rw [Finset.sum_congr rfl hEg]
  rw [← Finset.mul_sum, mul_assoc (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hL := HCEntries.one_le_scL L
  have hb := HCEntries.one_le_b L
  have hk := HCEntries.one_le_k D
  have ht := HCEntries.one_le_letterBlockLength D
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hx0 : 0 < L.sc.x := by linarith
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha1 : 1 ≤ L.sc.a := by rw [ha]; exact one_le_mul_of_one_le_of_one_le (by linarith) hb
  have hN2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := one_le_pow₀ hN
  have hw : (D.R.N D.R.m : ℝ) ^ 2 * L.sc.x ≤ L.sc.w'' D.R.n := by
    have a1 := P.teta
    rw [le_div_iff₀ hx0] at a1
    exact (mul_le_mul_of_nonneg_right (hNη.trans (le_mul_of_one_le_left hη0 ht)) hx0.le).trans a1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := (one_le_mul_of_one_le_of_one_le hN2 (by linarith)).trans hw
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by unfold Scale.X''; positivity
  have hXa : L.sc.X'' D.R.n ≤ L.sc.a := div_le_self (by linarith) hw1
  have hXN : L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2 ≤ L.sc.b := by
    unfold Scale.X''
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), ha]
    have := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ L.sc.b)
    linarith
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  have hwj := HCEntries.wj_bounds hS hx j hj1 hjm
  have hW0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ := Finset.sum_nonneg fun τ _ => (hwj τ).1
  have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  have hW : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => wj D j τ) _ fun τ _ => (hwj τ).2
    rwa [Finset.card_univ, hcard, nsmul_eq_mul] at this
  have hla0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have he := L.sc.eps_pos
  have hla : Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.sc.L := by
    rw [ha, Real.log_mul hx0.ne' (by linarith)]
    have a1 : Real.log L.sc.b = L.sc.L := Real.log_exp _
    have a2 : Real.log L.sc.x ≤ L.sc.L / L.sc.eps := Real.log_le_rpow_div hx0.le he
    rw [a1]
    calc _ ≤ L.sc.L / L.sc.eps + L.sc.L := by linarith
      _ = _ := by ring
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hfb : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    have : L.B0 = D.R.m * (D.R.f * L.sc.b * L.sc.L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hm
  have hfl : D.R.f * L.sc.b * Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.B0 := by
    calc _ ≤ D.R.f * L.sc.b * ((1 / L.sc.eps + 1) * L.sc.L) := mul_le_mul_of_nonneg_left hla hfb
      _ = (1 / L.sc.eps + 1) * (D.R.f * L.sc.b * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : L.sc.X'' D.R.n * (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.log L.sc.a) ≤
      3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ = 3 * (D.R.f * (L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2) * Real.log L.sc.a) := by ring
      _ ≤ _ := by gcongr
  have t3 : (∑ τ : D.what₂.Tau, wj D j τ) * Real.log L.sc.a ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ ≤ D.R.f * (3 * L.sc.b) * Real.log L.sc.a := mul_le_mul_of_nonneg_right hW hla0
      _ = _ := by ring
  have key := GlobalTheory.ConjLoss.sum_primes_le Q (fun p hp => (hQ p hp).1)
    1 (L.sc.X'' D.R.n) L.sc.a (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)
    (∑ τ : D.what₂.Tau, wj D j τ) hX0 hXa ha1 (by positivity) hW0
  refine key.trans ?_
  rw [Nat.cast_one, Real.log_one]
  linarith

theorem loss_sum_primes : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm h0 h1
  refine ⟨2 * (9 * (1 / eps + 1)), 2, by positivity, ?_⟩
  intro x hx0 hx i j hj Q hQ
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have := bound_one (c := Fm.cX.err) Fm.fixed.2.2.2.2.2.1 (Fm.params x hx i) (Fm.sizes x hx i)
    (by rw [hsx]; exact hx0) j hj Q hQ
  rwa [hse] at this

end GlobalTheory.ConjLossPrimes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeLoss

open IsDedekindDomain

theorem additiveValuation_mul_of_ne_zero {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) : vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((map_ne_zero _).2 hx) ((map_ne_zero _).2 hy)]
  ring

theorem additiveValuation_conj_place_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneIdeal_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conj (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneIdeal_iff_additiveValuation_pos _ y hy, mem_heightOneIdeal_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conj_place_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

theorem logWeight_conj (D : D7) (w : D.what₂.places.Pl) :
    SizeData₂.lwP (D.what₂.places.conj w) = SizeData₂.lwP w := by
  unfold SizeData₂.lwP
  rw [plEq_conj]
  exact Formalism.DivisionValues.ValuationRepresentative.lw_conjPl (D.plEq w)

theorem additiveValuation_residueChar_eq_ramIndex (D : D7) (w : D.what₂.places.Pl) :
    vAdd (D.plEq w) ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = (D.what₂.places.ramIdx w : ℤ) := by
  have h0 : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  have h1 := D.val_eq w _ h0
  rw [D.what₂.places.val_resChar] at h1
  exact_mod_cast h1.symm

theorem exists_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ S : Finset D.what₂.places.Pl, ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p := by
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  refine ⟨(T.map D.plEq.symm.toEmbedding).filter (fun w => D.what₂.places.resChar w = p), fun w => ?_⟩
  rw [Finset.mem_filter, Finset.mem_map_equiv, Equiv.symm_symm, hT]
  exact ⟨fun h => h.2, fun h => ⟨h ▸ resChar_mem D w, h⟩⟩

theorem sum_half (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w, w ∈ S ↔ D.what₂.places.resChar w = p) (y : D.what₂.LL) (hy : y * star y = (p : D.what₂.LL)) :
    ∑ w ∈ S, 2 * SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) = Real.log p := by
  have hp0 : (p : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hy0 : y ≠ 0 := fun h => hp0 (by rw [← hy, h, zero_mul])
  have hconj : ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) =
      ∑ w ∈ S, SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) := by
    refine Finset.sum_nbij' D.what₂.places.conj D.what₂.places.conj ?_ ?_ ?_ ?_ ?_
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w hw
      rw [hS] at hw ⊢
      rw [resChar_conj, hw]
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      exact D.what₂.places.conj_conj w
    · intro w _
      rw [logWeight_conj, additiveValuation_conj_place_eq_star]
  have hm := factEtaMean D p hp S hS
  rw [← hm]
  have : ∀ w ∈ S, lw D.what₂.LL (D.plEq w) * (D.what₂.places.ramIdx w : ℝ) =
      SizeData₂.lwP w * (vAdd (D.plEq w) y : ℝ) + SizeData₂.lwP w * (vAdd (D.plEq w) (star y) : ℝ) := by
    intro w hw
    have h1 := additiveValuation_residueChar_eq_ramIndex D w
    rw [(hS w).1 hw, ← hy, additiveValuation_mul_of_ne_zero _ hy0 (star_ne_zero.2 hy0)] at h1
    have h2 : (D.what₂.places.ramIdx w : ℝ) = (vAdd (D.plEq w) y : ℝ) + (vAdd (D.plEq w) (star y) : ℝ) := by
      exact_mod_cast h1.symm
    rw [h2, ← mul_add]
    rfl
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hconj, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

theorem conj_sigmaOf {R : Ranks} (H : Host R) (g : R.GG) (x : H.E) :
    H.conj (H.sigmaOf g x) = H.sigmaOf g (H.conj x) := by
  have h1 : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj :=
    map_mul (H.gal).symm g (R.cc)
  have h2 : H.sigmaOf (R.cc * g) = H.conj * H.sigmaOf g :=
    map_mul (H.gal).symm (R.cc) g
  have h3 : H.conj * H.sigmaOf g = H.sigmaOf g * H.conj := by rw [← h1, ← h2, mul_comm]
  exact congrArg (fun s : H.E ≃ₐ[ℚ] H.E => s x) h3

theorem tauPib_norm {D : D7} (X : ErrX D) (i : Fin 2) (τ : D.what₂.Tau) :
    tauPib X i τ * star (tauPib X i τ) = (D.host.g i : D.what₂.LL) := by
  unfold tauPib tauLL
  rw [← D.embE_conj, conj_sigmaOf, ← map_mul, ← map_mul, ← map_mul, X.piG_norm]
  simp

theorem padic_log_le (p n : ℕ) (hp : p.Prime) : (padicValNat p n : ℝ) * Real.log p ≤ Real.log n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.padicValNat_def]
  · have h : p ^ padicValNat p n ≤ n := Nat.le_of_dvd hn (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    rw [← Real.log_pow]
    apply Real.log_le_log
    · have := hp.pos
      positivity
    · exact_mod_cast h

theorem arith_bound (δ v e lg f m b L N η C₁ C₂ cg CY B : ℝ) (hB : B = f * m * b * L) (hf : 1 ≤ f) (hm : 1 ≤ m)
    (hL : 1 ≤ L) (hN : 1 ≤ N) (hCY : 0 ≤ CY) (hδ : |δ| ≤ C₁ * f * b) (hv0 : 0 ≤ v)
    (hv : v ≤ C₂ * f * N * Real.log (f * N)) (he : e = cg * f * (N ^ 2 + m ^ 2 * η)) (hlg0 : 0 ≤ lg)
    (hlg : lg ≤ (CY + 1) * L) (hη0 : 0 ≤ η) (hNη : N ^ 2 ≤ η) (hmf : m ≤ f) (hfη : f * η ≤ b) :
    |δ * lg + 2 * v + 2 * e * lg| ≤ (|C₁| * (CY + 1) + 2 * |C₂| + 4 * |cg| * (CY + 1)) * B := by
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hηb : η ≤ b := le_trans (le_mul_of_one_le_left hη0 hf) hfη
  have hb : 0 ≤ b := hη0.trans hηb
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb
  have hB1 : f * b * L ≤ B := by
    have : B = m * (f * b * L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (mul_nonneg hfb hL0) hm
  have hB2 : f * b ≤ B := le_trans (le_mul_of_one_le_right hfb hL) hB1
  have t1 : |δ * lg| ≤ |C₁| * (CY + 1) * B := by
    rw [abs_mul, abs_of_nonneg hlg0]
    have h1 : |δ| ≤ |C₁| * (f * b) := by
      refine hδ.trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hfb
    calc |δ| * lg ≤ |C₁| * (f * b) * ((CY + 1) * L) := mul_le_mul h1 hlg hlg0 (by positivity)
      _ = |C₁| * (CY + 1) * (f * b * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : v ≤ |C₂| * B := by
    have hfN : 1 ≤ f * N := one_le_mul_of_one_le_of_one_le hf hN
    have l0 : 0 ≤ Real.log (f * N) := Real.log_nonneg hfN
    have l1 : Real.log (f * N) ≤ f * N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have h1 : f * N * Real.log (f * N) ≤ B := by
      calc f * N * Real.log (f * N) ≤ f * N * (f * N) := mul_le_mul_of_nonneg_left l1 (by linarith)
        _ = f * (f * N ^ 2) := by ring
        _ ≤ f * b := mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left hNη hf0).trans hfη) hf0
        _ ≤ B := hB2
    calc v ≤ C₂ * (f * N * Real.log (f * N)) := by rw [← mul_assoc, ← mul_assoc]; exact hv
      _ ≤ |C₂| * (f * N * Real.log (f * N)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg (by linarith) l0)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have t3 : |2 * e * lg| ≤ 4 * |cg| * (CY + 1) * B := by
    have h0 : 0 ≤ N ^ 2 + m ^ 2 * η := by positivity
    have h1 : N ^ 2 + m ^ 2 * η ≤ 2 * (m * b) := by
      have a1 : m * η ≤ b := (mul_le_mul_of_nonneg_right hmf hη0).trans hfη
      have a2 : m * (m * η) ≤ m * b := mul_le_mul_of_nonneg_left a1 hm0
      have a3 : b ≤ m * b := le_mul_of_one_le_left hb hm
      nlinarith
    have h2 : |2 * e * lg| = 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) := by
      rw [he, abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hlg0, abs_of_nonneg h0, abs_of_nonneg hf0]
      simp only [abs_two]
      ring
    rw [h2]
    calc 2 * |cg| * f * ((N ^ 2 + m ^ 2 * η) * lg) ≤ 2 * |cg| * f * (2 * (m * b) * ((CY + 1) * L)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 hlg hlg0 (by positivity)) (by positivity)
      _ = _ := by rw [hB]; ring
  have tri : |δ * lg + 2 * v + 2 * e * lg| ≤ |δ * lg| + |2 * v| + |2 * e * lg| := abs_add_three _ _ _
  rw [abs_of_nonneg (by linarith : 0 ≤ 2 * v)] at tri
  nlinarith

end GlobalTheory.TypeLoss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChernClause

attribute [-instance] Formalism.BasicNotions.Examples₂.instIsEmptyClsEmptyColumnChain in
theorem pchern_of (hsep : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated)
 (hcharts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k))
 (hpull : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
 (hframe : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k))
 (hlift : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J))
 (halg : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg))
 (hcup : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc) (β : Λ → Λ → Hol F.V), (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) → ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg))
 (hsym : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : GlobalTheory.CatCoh.C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = GlobalTheory.CatCoh.mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = GlobalTheory.CatCoh.d0 K.Oc G T T' φ) → (∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → GlobalTheory.CatCoh.mp K.Oc φ (G T) = G T') → ∃ r : Hol F.V, ∀ T, G T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l)
 (hah : ∀ {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ), H.IsHermitian → ∀ x y : Fin g → ℂ, (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) = (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((x ⬝ᵥ H.mulVec (star y)).im : ℂ))
 (h1 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T))
 (h0 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p) : PChern (-1) := by
  intro A _ g hA L u P hP M u' hM hex H χ ψ hAH hψ x x'
  obtain ⟨n, a, b, hc, rfl⟩ := hψ
  obtain ⟨K, r, j, hR, hS, hF, hj⟩ := hcharts (fibUnif u) (hsep A hA) M.U hM.cover
  have hB : K.Based := by
    obtain ⟨k, hk⟩ := hR.1 (0, 0) trivial
    exact ⟨k, fun z _ ↦ by rwa [Subsingleton.elim z 0]⟩
  obtain ⟨i, uu, ℓ, hi, huu, hℓ, hz⟩ := hpull K r M j hj _ hc
  obtain ⟨fr, af, lg, f1, f2, a1, a2, a3, a4, a5⟩ := hframe A L u M u' hM hex H χ hAH K r hF j hj
  obtain ⟨e, he⟩ := hlift K r M hM j hj fr af f1 f2 i hi uu huu
  let β : u.Λ → u.Λ → ℂ := fun l m ↦ (Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))
  obtain ⟨c, hcc⟩ := halg K af lg (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) a1 a2 a3 a4 a5 e uu ℓ.1 he hℓ
  let pr : primDR A → (u.Λ →+ Hol (fibFam u).V) := fun c ↦
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by rw [map_add (f := _), LinearMap.add_apply, (algebraMap ℂ (Hol (fibFam u).V)).map_add] }
  have hpr : ∀ c : primDR A, r.coef.pull1 c.1 = K.perCl (pr c) := fun c ↦ hP c K r hF
  obtain ⟨c', hc'⟩ := hcup K (fun k ↦ pr (a k)) (fun k ↦ pr (b k)) ℓ c
    (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_cup, hpr, hpr]) hcc
  let δ : u.Λ → u.Λ → ℂ := fun l m ↦ ∑ k, P l (a k) * P m (b k) - β l m
  have d1 : ∀ l l' m, δ (l + l') m = δ l m + δ l' m := fun l l' m ↦ by
    simp only [δ, β, map_add (f := _), LinearMap.add_apply, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add,
      add_mul, Finset.sum_add_distrib]
    ring
  have d2 : ∀ l m m', δ l (m + m') = δ l m + δ l m' := fun l m m' ↦ by
    simp only [δ, β, map_add (f := _), LinearMap.add_apply, Submodule.coe_add, add_dotProduct,
      mul_add, Finset.sum_add_distrib]
    ring
  let β' : u.Λ →+ u.Λ →+ Hol (fibFam u).V := AddMonoidHom.mk'
    (fun l ↦ AddMonoidHom.mk' (fun m ↦ algebraMap ℂ (Hol (fibFam u).V) (δ l m)) fun m m' ↦ by rw [d2, (algebraMap ℂ (Hol (fibFam u).V)).map_add])
    fun l l' ↦ AddMonoidHom.ext fun m ↦ by
      change algebraMap ℂ (Hol (fibFam u).V) (δ (l + l') m) = algebraMap ℂ (Hol (fibFam u).V) (δ l m) + algebraMap ℂ (Hol (fibFam u).V) (δ l' m)
      rw [d1, (algebraMap ℂ (Hol (fibFam u).V)).map_add]
  have hs := hsym K (fun c hc ↦ h1 K hR hB c hc) (fun G hG ↦ h0 K hR G fun T T' φ h ↦ (hG T T' φ h).symm) hS hR β' c'
    (fun T T' T'' φ ψ ↦ by
      rw [hc']
      congr 1
      change _ = algebraMap ℂ (Hol (fibFam u).V) (δ φ.deg ψ.deg)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [δ, map_sub, map_sum, map_mul]
      rfl) x x'
  have hs' : δ x x' = δ x' x := by
    have := congrArg (Hol.ev (W := (fibFam u).V) 0 trivial) hs
    change Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x x')) = Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x' x)) at this
    simpa using this
  rw [wedgeForm_apply, ← hah H hAH.1 x x', Finset.sum_sub_distrib]
  simp only [δ, β] at hs'
  have e2 : ∑ k, P x (b k) * P x' (a k) = ∑ k, P x' (a k) * P x (b k) := Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  rw [e2]
  linear_combination hs'

theorem pchern : GlobalTheory.AnPer.PChern (-1) :=
  pchern_of @_root_.GlobalTheory.abelianScheme_left_isSeparated_of_affine @_root_.GlobalTheory.AnPer.exists_charts_subordinate @_root_.GlobalTheory.AnPer.isChern_real @_root_.GlobalTheory.AnPer.FrameFn.exists_frame_factor_log @_root_.GlobalTheory.LiftUnits.exists_units @_root_.GlobalTheory.AnPer.log_cocycle_cohomologous @_root_.GlobalTheory.T.cup_period_classes_sum_const @_root_.GlobalTheory.AnPer.const_biadditive_coboundary_symm @GlobalTheory.pi_mul_hermitian_alternation @_root_.GlobalTheory.AnPer.Charts.DegZero.exists_gauge @_root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible

end GlobalTheory.AnPer.ChernClause
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZalgEqAdjoinFiniteCapelli
section
open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspRep


open Finset in
theorem zalg_eq_adjoin_finite_caps : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (b : ℕ),
    ∃ T : Finset (Module.End ℂ (Sm E b)), (∀ t ∈ T, ∃ (τ : E →+* ℂ) (u : ℂ), t = cap τ u) ∧
      Zalg E b = Algebra.adjoin ℂ (T : Set (Module.End ℂ (Sm E b))) := by
  intro E _ _ _ b
  classical
  refine ⟨univ.image (fun p : (E →+* ℂ) × Fin (b + 1) => cap (a := b) p.1 ((p.2 : ℕ) : ℂ)), ?_, ?_⟩
  · intro t ht
    obtain ⟨p, -, rfl⟩ := mem_image.1 ht
    exact ⟨p.1, _, rfl⟩
  · apply le_antisymm
    · unfold Zalg
      rw [Algebra.adjoin_le_iff]
      rintro z ⟨τ, u, rfl⟩
      obtain ⟨w, hw⟩ := cap_eq_sum_nodes E b τ u
      rw [hw]
      refine Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin ?_) _
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range]
      exact ⟨(τ, j), rfl⟩
    · unfold Zalg
      apply Algebra.adjoin_mono
      intro t ht
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at ht
      obtain ⟨p, rfl⟩ := ht
      exact ⟨p.1, _, rfl⟩

end GlobalTheory.CuspRep

end
end

