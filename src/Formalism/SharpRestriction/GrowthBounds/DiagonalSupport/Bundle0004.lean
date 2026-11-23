module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
public import Formalism.SharpRestriction.GrowthBounds.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.BinomCombFOnFinset
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.Joints Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

theorem gamR_zero_zero (P : ℕ) : gamR P 0 0 = 1 := by
  unfold gamR
  simp

theorem gamR_one_zero (be : ℕ) : gamR 1 0 be = 1 := by
  unfold gamR
  have : ((be.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  simp [this]

theorem digQ (D : Formalism.BasicNotions.D7) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (σ : Type) [Fintype σ] (g rho : σ → ℕ)
    (hrho : ∀ v, rho v < p ^ g v) :
    (∀ be : σ → ℕ, (∏ v, gamR (p ^ g v) (rho v) (be v)) ≠ 0 ∧
      padicValRat p (∏ v, gamR (p ^ g v) (rho v) (be v)) = 0) ∧
    ∀ (inv : Bool) (c : ℕ), ∃ (T : Finset (σ → ℕ)) (q : (σ → ℕ) → ℚ),
      (∀ j ∈ T, ∑ k, j k ≤ 4 * c ∧ PadicGe p (q j) 0) ∧
      ∀ be : σ → ℕ, PadicGe p ((if inv then (∏ v, gamR (p ^ g v) (rho v) (be v))⁻¹
          else (∏ v, gamR (p ^ g v) (rho v) (be v))) - ∑ j ∈ T, q j * ∏ k, ((be k).choose (j k) : ℚ)) c := by
  obtain ⟨hA, hB⟩ := lemma_five_two_first_holds D p hp h5
  have hrho' : ∀ v, rho v < p ^ (g v - 1 + 1) := by
    intro v
    by_cases h : g v = 0
    · have h1 := hrho v
      rw [h, pow_zero] at h1
      have : rho v = 0 := by omega
      rw [this]
      exact pow_pos hp.pos _
    · have : g v - 1 + 1 = g v := by omega
      rw [this]
      exact hrho v
  obtain ⟨hU, _, hQ⟩ := hB σ (fun v => g v - 1) rho hrho'
  have hgam : ∀ (v : σ) (e' : ℕ), gamR (p ^ (g v - 1 + 1)) (rho v) e' =
      cUnit (p ^ (g v - 1 + 1)) e' * dUnit (p ^ (g v - 1 + 1)) e' (rho v) := by
    intro v e'
    unfold gamR
    have h1 : ((rho v).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h2 : (e'.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    have h3 : ((p ^ (g v - 1 + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
    rw [hA (g v - 1) (rho v) e' (hrho' v)]
    have hne : ((rho v).factorial : ℚ) * (e'.factorial : ℚ) * ((p ^ (g v - 1 + 1)).factorial : ℚ) ^ e' ≠ 0 :=
      mul_ne_zero (mul_ne_zero h1 h2) (pow_ne_zero _ h3)
    rw [mul_assoc _ (cUnit _ _) _, mul_div_cancel_left₀ _ hne]
  have hkey : ∀ (be : σ → ℕ) (v : σ), gamR (p ^ (g v - 1 + 1)) (rho v) (if g v = 0 then 0 else be v) =
      gamR (p ^ g v) (rho v) (be v) := by
    intro be v
    by_cases h : g v = 0
    · have h1 := hrho v
      rw [h, pow_zero] at h1
      have h2 : rho v = 0 := by omega
      rw [if_pos h, h2, gamR_zero_zero, h, pow_zero, gamR_one_zero]
    · have : g v - 1 + 1 = g v := by omega
      rw [if_neg h, this]
  have hratio : ∀ e' : σ → ℕ,
      ((∏ k, (((rho k + p ^ (g k - 1 + 1) * e' k).factorial : ℕ) : ℚ)) /
        (∏ k, ((rho k).factorial : ℚ) * ((e' k).factorial : ℚ) * ((p ^ (g k - 1 + 1)).factorial : ℚ) ^ (e' k))) =
      ∏ k, gamR (p ^ (g k - 1 + 1)) (rho k) (e' k) := by
    intro e'
    rw [← Finset.prod_div_distrib]
    rfl
  refine ⟨fun be => ?_, fun inv c => ?_⟩
  · have h := hU (fun v => if g v = 0 then 0 else be v)
    have e1 : (∏ k, cUnit (p ^ (g k - 1 + 1)) (if g k = 0 then 0 else be k) *
        dUnit (p ^ (g k - 1 + 1)) (if g k = 0 then 0 else be k) (rho k)) = ∏ v, gamR (p ^ g v) (rho v) (be v) :=
      Finset.prod_congr rfl fun v _ => by rw [← hgam, hkey]
    rw [e1] at h
    exact h
  · obtain ⟨T, q, hT, hq⟩ := hQ inv c
    refine ⟨T.filter (fun j => ∀ k, g k = 0 → j k = 0), q, fun j hj => hT j (Finset.mem_filter.1 hj).1, fun be => ?_⟩
    have h := hq (fun v => if g v = 0 then 0 else be v)
    simp only [hratio] at h
    have e1 : (∏ k, gamR (p ^ (g k - 1 + 1)) (rho k) (if g k = 0 then 0 else be k)) =
        ∏ v, gamR (p ^ g v) (rho v) (be v) := Finset.prod_congr rfl fun v _ => hkey be v
    rw [e1] at h
    have e2 : ∑ j ∈ T, q j * ∏ k, (((if g k = 0 then 0 else be k).choose (j k) : ℕ) : ℚ) =
        ∑ j ∈ T.filter (fun j => ∀ k, g k = 0 → j k = 0), q j * ∏ k, ((be k).choose (j k) : ℚ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · congr 1
        refine Finset.prod_congr rfl fun k _ => ?_
        by_cases hk : g k = 0
        · rw [if_pos hk, hj k hk]; simp
        · rw [if_neg hk]
      · push Not at hj
        obtain ⟨k, hk, hjk⟩ := hj
        have : ∏ k, (((if g k = 0 then 0 else be k).choose (j k) : ℕ) : ℚ) = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
          rw [if_pos hk]
          have : Nat.choose 0 (j k) = 0 := Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hjk)
          rw [this]; simp
        rw [this, mul_zero]
    rw [e2] at h
    exact h

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem binomCombF_onFinset {σ : Type} [Fintype σ] (T : Finset (σ → ℕ)) (o : (σ → ℕ) → O) :
    ∃ lam : (σ →₀ ℕ) →₀ O, (∀ m ∈ lam.support, (⇑m : σ → ℕ) ∈ T) ∧
      ∀ be : σ →₀ ℕ, binomCombF (K := KK O) lam be =
        ∑ j ∈ T, algebraMap O (KK O) (o j) * ∏ k, (((be k).choose (j k) : ℕ) : KK O) := by
  let em : (σ → ℕ) ↪ (σ →₀ ℕ) := (Finsupp.equivFunOnFinite (α := σ) (M := ℕ)).symm.toEmbedding
  have hem : ∀ j : σ → ℕ, (⇑(em j) : σ → ℕ) = j := fun j => by
    funext k
    rfl
  have hsub : ∀ m : σ →₀ ℕ, (if (⇑m : σ → ℕ) ∈ T then o ⇑m else 0) ≠ 0 → m ∈ T.map em := by
    intro m hm
    by_cases hT : (⇑m : σ → ℕ) ∈ T
    · refine Finset.mem_map.2 ⟨⇑m, hT, ?_⟩
      ext k
      rfl
    · simp [hT] at hm
  refine ⟨Finsupp.onFinset (T.map em) (fun m => if (⇑m : σ → ℕ) ∈ T then o ⇑m else 0) hsub, fun m hm => ?_, fun be => ?_⟩
  · have h1 := Finsupp.mem_support_iff.1 hm
    rw [Finsupp.onFinset_apply] at h1
    by_contra hT
    simp [hT] at h1
  · unfold binomCombF
    rw [Finset.sum_subset (Finsupp.support_onFinset_subset)]
    · rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finsupp.onFinset_apply, hem, if_pos hj]
      congr 1
      rw [← Finset.prod_subset (Finset.subset_univ (em j).support)]
      · intro k _ hk
        have h0 : j k = 0 := by
          have := Finsupp.notMem_support_iff.1 hk
          exact this
        rw [h0]; simp
    · intro m _ hm
      rw [Finsupp.notMem_support_iff.1 hm]
      simp

theorem digAbs (D : Formalism.BasicNotions.D7) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (S : UniformizedDVR p O) : DigAbs p O := by
  intro σ _ g rho hrho
  have hO : CharZero O := dvr_ring_charZero hp S
  have hK : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  obtain ⟨h1, h2⟩ := digQ D p hp h5 σ g rho hrho
  refine ⟨fun be => h1 be, fun inv c => ?_⟩
  obtain ⟨T, q, hT, hq⟩ := h2 inv c
  have hex : ∀ j, ∃ o : O, j ∈ T → ((q j : ℚ) : KK O) = algebraMap O (KK O) o := by
    intro j
    by_cases hj : j ∈ T
    · obtain ⟨o, ho⟩ := rat_padicGe_cast hp S (q j) 0 (by simpa using (hT j hj).2)
      exact ⟨o, fun _ => by simpa using ho⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose o ho using hex
  obtain ⟨lam, hsup, hlam⟩ := binomCombF_onFinset (O := O) T o
  refine ⟨lam, fun m hm => ?_, fun be => ?_⟩
  · rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
    exact (hT _ (hsup m hm)).1
  · obtain ⟨z, hz⟩ := rat_padicGe_cast hp S _ c (hq be)
    have hsum : binomCombF (K := KK O) lam be =
        ((∑ j ∈ T, q j * ∏ k, ((be k).choose (j k) : ℚ) : ℚ) : KK O) := by
      rw [hlam be]
      push_cast
      exact Finset.sum_congr rfl fun j hj => by rw [ho j hj]
    have heq : ((if inv = true then (((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O))⁻¹
          else ((∏ v, gamR (p ^ g v) (rho v) (be v) : ℚ) : KK O)) - binomCombF (K := KK O) lam be) =
        (p : KK O) ^ c * algebraMap O (KK O) z := by
      rw [← hz, hsum]
      cases inv <;> simp
    rw [heq]
    exact geQ_vK_pow_mul S c z

theorem exists_unit_of_rat (p : ℕ) (hp : p.Prime) (S : UniformizedDVR p O) (x : ℚ) (hx : x ≠ 0) (hv : padicValRat p x = 0) :
    ∃ u : O, IsUnit u ∧ algebraMap O (KK O) u = ((x : ℚ) : KK O) := by
  have hO : CharZero O := dvr_ring_charZero hp S
  have hK : CharZero (KK O) := dvr_fraction_field_char_zero hp S
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := rat_padicGe_cast hp S x 0 (Or.inr (by rw [hv]; simp))
  obtain ⟨b, hb⟩ := rat_padicGe_cast hp S x⁻¹ 0 (Or.inr (by rw [padicValRat.inv, hv]; simp))
  rw [pow_zero, one_mul] at ha hb
  refine ⟨a, ?_, ha.symm⟩
  have hab : a * b = 1 := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul, ← ha, ← hb, map_one]
    push_cast
    exact mul_inv_cancel₀ (by exact_mod_cast hx)
  exact IsUnit.of_mul_eq_one b hab

theorem gaAt (D : Formalism.BasicNotions.D7) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) (S : UniformizedDVR p O) {n' r K : ℕ} [NeZero n'] [NeZero r]
    [NeZero K] (Fr : Frames n' r) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) : GaAt (K := K) p O Fr nL := by
  intro rho hrho
  have hDA := digAbs (O := O) D p hp h5 S
  obtain ⟨hn1, _⟩ := hDA (TL J nL r × Fin K) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.natAdd r v.2)) (fun v => hrho v.1 _)
  obtain ⟨hp1, hp2⟩ := hDA (TL J nL r × Fin r) (fun v => Fr.dist (segZ v.1.1) (posTL Fr v.1))
    (fun v => rho (v.1, Fin.castAdd K v.2)) (fun v => hrho v.1 _)
  refine ⟨fun bn => hn1 bn, fun bp => hp1 bp, ?_⟩
  have hex : ∀ al : TL J nL r × Fin r →₀ ℕ, ∃ u : O, IsUnit u ∧
      algebraMap O (KK O) u = ((gamPl Fr p nL rho al : ℚ) : KK O) :=
    fun al => exists_unit_of_rat p hp S _ (hp1 al).1 (hp1 al).2
  choose ga hu hga using hex
  refine ⟨ga, hu, hga, fun k _ ε => ?_⟩
  obtain ⟨lam, hl1, hl2⟩ := hp2 (!ε) k
  refine ⟨lam, fun m hm => le_trans (hl1 m hm) (by omega), fun al => ?_⟩
  have h := hl2 al
  rw [hga al]
  have hdef : gamPl Fr p nL rho al =
      ∏ v : TL J nL r × Fin r, gamR (p ^ Fr.dist (segZ v.1.1) (posTL Fr v.1)) (rho (v.1, Fin.castAdd K v.2)) (al v) := rfl
  rw [hdef]
  cases ε
  · simpa using h
  · simpa using h

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LevImgCoeffBigM
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

section Up

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem upPl_monomial (bp : TL J nL r × Fin r →₀ ℕ) (c : KK O) :
    upPl Fr p O hk nL (monomial bp c) = monomial (mPl Fr p hk nL bp) c := by
  rw [show monomial (mPl Fr p hk nL bp) c = C c * monomial (mPl Fr p hk nL bp) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upPl, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mPl, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

theorem upNo_monomial (bn : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    upNo Fr p O hk nL (monomial bn c) = monomial (mNo Fr p hk nL bn) c := by
  rw [show monomial (mNo Fr p hk nL bn) c = C c * monomial (mNo Fr p hk nL bn) 1 by
      rw [C_mul_monomial, mul_one]]
  simp only [upNo, aeval_monomial, algebraMap_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mNo, MvPolynomial.monomial_sum_one]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  rw [← pow_mul, X_pow_eq_monomial]

theorem asm_eq_sum (rho : TL J nL r × Fin (r + K) → ℕ) (A : MvPolynomial (TL J nL r × Fin r) (KK O))
    (N : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    asm Fr p O hk nL rho A N = ∑ bp ∈ A.support, ∑ bn ∈ N.support,
      monomial (bigM Fr p hk nL rho bp bn) (A.coeff bp * N.coeff bn) := by
  conv_lhs => rw [asm, A.as_sum, N.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, upPl_monomial, upNo_monomial, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bp _
  apply Finset.sum_congr rfl
  intro bn _
  rw [monomial_mul, monomial_mul, one_mul, bigM_eq]

theorem levImg_coeff (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (G : MvPolynomial (TV n' (m + 1)) (KK O)) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn =
      ∑ mo ∈ G.support.filter (fun mo => InLow Fr p hk nL rho mo ∧ InBlock Fr p hk nL dPl dNo mo),
        if plMon Fr p hk nL mo = bp ∧ noMon Fr p hk nL mo = bn then G.coeff mo else 0 := by
  simp only [levImg, MvPolynomial.coeff_sum, coeff_monomial]
  apply Finset.sum_congr rfl
  intro mo _
  by_cases h1 : plMon Fr p hk nL mo = bp <;> by_cases h2 : noMon Fr p hk nL mo = bn <;> simp [h1, h2]

variable {Fr p O hk nL}

theorem levImg_coeff_bigM (hp : 0 < p) (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (G : MvPolynomial (TV n' (m + 1)) (KK O))
    (hz : ∀ mo ∈ G.support, ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0)
    (rho : TL J nL r × Fin (r + K) → ℕ) (hrho : ∀ x c, rho (x, c) < lowP Fr p x) (dPl dNo : TL J nL r → ℕ)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (h1 : ∀ x, multideg bp x = dPl x) (h2 : ∀ x, multideg bn x = dNo x) :
    ((levImg Fr p hk nL rho dPl dNo G).coeff bp).coeff bn = G.coeff (bigM Fr p hk nL rho bp bn) := by
  have hpl := bigM_plMon (hk := hk) hp hinj rho hrho bp bn
  have hno := bigM_noMon (hk := hk) hp hinj rho hrho bp bn
  rw [levImg_coeff]
  refine (Finset.sum_eq_single (bigM Fr p hk nL rho bp bn) ?_ ?_).trans ?_
  · intro mo hmo hne
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply hne
    obtain ⟨hmo1, hlow, -⟩ := Finset.mem_filter.mp hmo
    rw [eq_bigM hinj rho mo (hz mo hmo1) hlow, e1, e2]
  · intro hnot
    rw [if_pos ⟨hpl, hno⟩]
    by_contra hc
    exact hnot (Finset.mem_filter.mpr ⟨mem_support_iff.mpr hc, bigM_inLow (hk := hk) hinj rho hrho bp bn,
      bigM_inBlock (hk := hk) hp hinj rho hrho bp bn dPl dNo h1 h2⟩)
  · rw [if_pos ⟨hpl, hno⟩]

end Up

section Fact

theorem expFact_fintype {σ : Type} [Fintype σ] (b : σ →₀ ℕ) : expFact b = ∏ v, (b v).factorial := by
  unfold expFact
  exact Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)

theorem gamR_spec (P rho be : ℕ) :
    ((rho + P * be).factorial : ℚ) =
      gamR P rho be * ((rho.factorial : ℚ) * (be.factorial : ℚ) * (P.factorial : ℚ) ^ be) := by
  rw [gamR, div_mul_cancel₀]
  positivity

variable {n' r K m : ℕ} [NeZero n'] {Fr : Frames n' r} {p : ℕ} {hk : m + 1 = r + K} {J : ℕ} [NeZero J]
  {nL : ZMod J → ℕ}

theorem expFact_bigM (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ) :
    expFact (bigM Fr p hk nL rho bp bn) = ∏ v, (bigE Fr p nL rho bp bn v).factorial := by
  unfold expFact bigM
  rw [Finsupp.prod_mapDomain_index_inj (tvar_inj (hk := hk) hinj),
    Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
  simp

private theorem sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul {M : Type} [CommMonoid M] (f : TL J nL r × Fin (r + K) → M) :
    ∏ v, f v = (∏ v : TL J nL r × Fin r, f (v.1, Fin.castAdd K v.2)) *
      ∏ v : TL J nL r × Fin K, f (v.1, Fin.natAdd r v.2) := by
  simp only [Fintype.prod_prod_type, Fin.prod_univ_add, Finset.prod_mul_distrib]

theorem expFact_bigM_Q (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (dPl dNo : TL J nL r → ℕ)
    (bp : TL J nL r × Fin r →₀ ℕ) (bn : TL J nL r × Fin K →₀ ℕ)
    (h1 : ∀ x, multideg bp x = dPl x) (h2 : ∀ x, multideg bn x = dNo x) :
    ((expFact (bigM Fr p hk nL rho bp bn) : ℕ) : ℚ) = ((cstOf Fr p nL rho dPl dNo : ℕ) : ℚ) *
      ((expFact bp : ℕ) : ℚ) * ((expFact bn : ℕ) : ℚ) * gamPl Fr p nL rho bp * gamNo Fr p nL rho bn := by
  rw [expFact_bigM (hk := hk) hinj rho bp bn]
  push_cast
  unfold bigE
  rw [Finset.prod_congr rfl (fun v _ => gamR_spec (lowP Fr p v.1) (rho v) (joinE nL bp bn v))]
  simp only [Finset.prod_mul_distrib]
  rw [sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => gamR (lowP Fr p v.1) (rho v) (joinE nL bp bn v)),
    sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => ((joinE nL bp bn v).factorial : ℚ)),
    sum_cf_mul_sum_cf_mul_eq_sum_sum_toReal_mul (fun v => ((lowP Fr p v.1).factorial : ℚ) ^ (joinE nL bp bn v))]
  simp only [joinE, Fin.addCases_left, Fin.addCases_right, Prod.mk.eta]
  rw [cstOf, expFact_fintype, expFact_fintype, gamPl, gamNo]
  push_cast
  have hP : ∏ x : TL J nL r, ((lowP Fr p x).factorial : ℚ) ^ (dPl x + dNo x) =
      (∏ v : TL J nL r × Fin r, ((lowP Fr p v.1).factorial : ℚ) ^ bp v) *
        ∏ v : TL J nL r × Fin K, ((lowP Fr p v.1).factorial : ℚ) ^ bn v := by
    rw [Fintype.prod_prod_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro x _
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, ← pow_add, ← h1 x, ← h2 x]
    rfl
  rw [hP]
  ring

end Fact

section Main

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) (O : Type) [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem classOf_left (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (a : Fin r) :
    classOf Fr p hk nL mo (x, Fin.castAdd K a) = mo (plVar Fr hk nL x a) % lowP Fr p x := by
  simp [classOf, Fin.addCases_left]

theorem classOf_right (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) (b : Fin K) :
    classOf Fr p hk nL mo (x, Fin.natAdd r b) = mo (noVar Fr hk nL x b) % lowP Fr p x := by
  simp [classOf, Fin.addCases_right]

theorem sum_coords (mo : TV n' (m + 1) →₀ ℕ) (x : TL J nL r) :
    multideg mo (posOf n' (posTL Fr x)) =
      ∑ a : Fin r, mo (plVar Fr hk nL x a) + ∑ b : Fin K, mo (noVar Fr hk nL x b) := by
  unfold multideg
  rw [← Equiv.sum_comp (finCongr hk.symm) (fun c => mo (posOf n' (posTL Fr x), c)), Fin.sum_univ_add]
  rfl

theorem digFacts_of [CharZero (KK O)] (hp : 0 < p)
    (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (hsurj : ∀ s ∈ Fr.TT, ∃ x : TL J nL r, posOf n' (posTL Fr x) = s)
    (d : Fin n' → ℕ) (hd : ∀ s, s ∉ Fr.TT → d s = 0) : DigFacts Fr p O hk nL d := by
  intro G hG
  have hdeg : ∀ mo ∈ G.support, ∀ s, multideg mo s = d s := fun mo hmo =>
    (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hG hmo
  have hz : ∀ mo ∈ G.support, ∀ w, w ∉ Set.range (tvar Fr hk nL) → mo w = 0 := by
    rintro mo hmo ⟨s, c⟩ hw
    by_cases hs : s ∈ Fr.TT
    · obtain ⟨x, hx⟩ := hsurj s hs
      exact absurd ⟨(x, Fin.cast hk c), by simp [tvar, hx]⟩ hw
    · have h1 := hdeg mo hmo s
      rw [hd s hs] at h1
      exact (Finset.sum_eq_zero_iff.1 h1) c (Finset.mem_univ _)
  refine ⟨?_, ?_, ?_⟩
  · intro rho dPl dNo hrho A hA N hN
    rw [asm_eq_sum, fockR_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun bp hbp => ?_
    rw [fockR_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun bn hbn => ?_
    have h1 : ∀ x, multideg bp x = dPl x := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hA hbp
    have h2 : ∀ x, multideg bn x = dNo x := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hN hbn
    rw [fockR_monomial, levImg_coeff_bigM hp hinj G hz rho hrho dPl dNo bp bn h1 h2]
    have hc := congrArg (fun q : ℚ => (q : KK O)) (expFact_bigM_Q (p := p) (hk := hk) hinj rho dPl dNo bp bn h1 h2)
    simp only [Rat.cast_mul, Rat.cast_natCast] at hc
    rw [hc]
    ring
  · intro rho dPl dNo bp
    unfold levImg
    rw [coeff_sum]
    refine Submodule.sum_mem _ fun mo hmo => ?_
    rw [coeff_monomial]
    split_ifs
    · unfold Pol
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro b hb
      have hb' := MvPolynomial.support_monomial_subset hb
      rw [Finset.mem_singleton] at hb'
      subst hb'
      intro x
      exact (Finset.mem_filter.1 hmo).2.2.2 x
    · exact Submodule.zero_mem _
  · intro mo hmo
    have hlow : InLow Fr p hk nL (classOf Fr p hk nL mo) mo :=
      ⟨fun x a => (classOf_left Fr p hk nL mo x a).symm, fun x b => (classOf_right Fr p hk nL mo x b).symm⟩
    have hrho : ∀ x c, classOf Fr p hk nL mo (x, c) < lowP Fr p x := by
      intro x c
      refine Fin.addCases (fun a => ?_) (fun b => ?_) c
      · rw [classOf_left]; exact Nat.mod_lt _ (lowP_pos hp x)
      · rw [classOf_right]; exact Nat.mod_lt _ (lowP_pos hp x)
    have heq := eq_bigM hinj (classOf Fr p hk nL mo) mo (hz mo hmo) hlow
    refine ⟨⟨hrho, fun x => ?_⟩, ?_, fun x => rfl, fun x => rfl, ?_⟩
    · rw [← hdeg mo hmo, sum_coords Fr hk nL mo x, Fin.sum_univ_add]
      simp only [classOf_left, classOf_right]
      unfold blkPl blkNo
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      have e1 : ∑ a : Fin r, mo (plVar Fr hk nL x a) =
          ∑ a : Fin r, (mo (plVar Fr hk nL x a) % lowP Fr p x + lowP Fr p x * (mo (plVar Fr hk nL x a) / lowP Fr p x)) :=
        Finset.sum_congr rfl fun a _ => (Nat.mod_add_div _ _).symm
      have e2 : ∑ b : Fin K, mo (noVar Fr hk nL x b) =
          ∑ b : Fin K, (mo (noVar Fr hk nL x b) % lowP Fr p x + lowP Fr p x * (mo (noVar Fr hk nL x b) / lowP Fr p x)) :=
        Finset.sum_congr rfl fun b _ => (Nat.mod_add_div _ _).symm
      rw [e1, e2, Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring
    · have h := levImg_coeff_bigM hp hinj G hz (classOf Fr p hk nL mo) hrho (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo)
        (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) (fun x => rfl) (fun x => rfl)
      rw [← heq] at h
      exact h
    · have h := expFact_bigM_Q (p := p) (hk := hk) hinj (classOf Fr p hk nL mo) (blkPl Fr p hk nL mo) (blkNo Fr p hk nL mo)
        (plMon Fr p hk nL mo) (noMon Fr p hk nL mo) (fun x => rfl) (fun x => rfl)
      rw [← heq] at h
      exact h

end Main

end Formalism.MainNotions.Proposition5Numerics
end
end

