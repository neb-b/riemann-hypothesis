module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwistSliceCoeff

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.FactorLeProductSeven
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem lowest_weight_le_of_isotypic (D : Formalism.BasicNotions.D7) {R : Type} [Field R] [CharZero R] {ι : Type} [Fintype ι] (LL : Letters ι)
    {n : ℕ} [NeZero n] (S : Set ι) (lam : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R)
    (hF : F ∈ isoSub (glOps R n LL S) lam) : lam1S LL S F ≤ ((lam 0 : ℤ) : WithBot ℤ) := by
  obtain ⟨ee, hee, _⟩ := Formalism.MainNotions.G.Joints.polIsoDecompB_of D (weight_condition_from_integral_form D) R ι LL n S
  refine (((valuation_field D).2 R ι LL n S ee hee).2 F (lam 0)).2 fun mu hmu => ?_
  by_cases h : lam = mu
  · rw [h]
  · exact absurd ((hee mu).2 lam h F hF) hmu

section DD

variable {σ Kf : Type} [Field Kf]

theorem coeff_mon_divDer (m a : σ →₀ ℕ) (F : MvPolynomial σ Kf) :
    (monomial m (1 : Kf) * divDer m F).coeff a = (∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : Kf)) * F.coeff a := by
  rw [coeff_monomial_mul']
  split_ifs with hma
  · rw [one_mul]
    unfold divDer
    rw [coeff_sum]
    have hsingle : ∀ b ∈ F.support, b ≠ a →
        AddMonoidAlgebra.coeff (if m ≤ b then monomial (b - m) (F.coeff b * ((m.prod fun k j => (b k).choose j : ℕ) : Kf))
          else 0) (a - m) = 0 := by
      intro b _ hb
      split_ifs with hmb
      · rw [coeff_monomial, if_neg]
        intro h
        apply hb
        have h1 : b - m + m = a - m + m := by rw [h]
        rwa [tsub_add_cancel_of_le hmb, tsub_add_cancel_of_le hma] at h1
      · simp
    by_cases ha : a ∈ F.support
    · rw [Finset.sum_eq_single a hsingle (fun h => absurd ha h), if_pos hma, coeff_monomial, if_pos rfl]
      unfold Finsupp.prod
      push_cast
      ring
    · rw [Finset.sum_eq_zero (fun b hb => hsingle b hb (fun h => ha (h ▸ hb))), notMem_support_iff.1 ha, mul_zero]
  · have : ∃ v, a v < m v := by
      by_contra hcon
      push Not at hcon
      exact hma hcon
    obtain ⟨v, hv⟩ := this
    have hvs : v ∈ m.support := by
      rw [Finsupp.mem_support_iff]
      omega
    rw [Finset.prod_eq_zero hvs (by rw [Nat.choose_eq_zero_of_lt hv, Nat.cast_zero]), zero_mul]

end DD

section BC

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem diagK_binomCombF (lam : (σ →₀ ℕ) →₀ O) (F : MvPolynomial σ (KK O)) :
    diagK (fun a => binomCombF (K := KK O) lam a) F =
      ∑ m ∈ lam.support, (algebraMap O (KK O) (lam m)) • (monomial m (1 : KK O) * divDer m F) := by
  ext a
  rw [coeff_diagK, coeff_sum]
  unfold binomCombF
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, coeff_mon_divDer, smul_eq_mul]
  ring

theorem geQ_binomCombF (S : UniformizedDVR p O) (lam : (σ →₀ ℕ) →₀ O) (a : σ →₀ ℕ) :
    geQ (vK p (binomCombF (K := KK O) lam a)) 0 := by
  unfold binomCombF
  refine geQ_sum _ _ fun m _ => ?_
  have h : algebraMap O (KK O) (lam m) * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : KK O) =
      algebraMap O (KK O) (lam m * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : O)) := by
    rw [map_mul, map_prod]
    simp
  rw [h]
  exact geQ_alg S _

end BC

theorem padicVal_expFact_le' (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {k : ℕ} (d : ι → ℕ)
    (α : ι × Fin k →₀ ℕ) (hα : ∀ s, multideg α s = d s) :
    padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : ι, ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hMn0 hE0]
  omega

section St

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coefGe_of_inBB [hp : Fact p.Prime] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O)) {ι : Type} [Fintype ι]
    {k : ℕ} (d : ι → ℕ) (Z : MvPolynomial (ι × Fin k) (KK O)) (hZ : Z ∈ Pol (KK O) k d) (hBB : InBB (O := O) p Z) :
    CoefGe p (((algebraMap O (KK O) w) ^ (padicValNat p (∏ s, (d s).factorial))) • Z) 0 := by
  intro bn
  rw [coeff_smul, smul_eq_mul]
  by_cases hbn : bn ∈ Z.support
  · have hdeg : ∀ s, multideg bn s = d s := ((mem_restrictSupport_iff (KK O)).1 hZ) hbn
    have h1 := padicVal_expFact_le' p d bn hdeg
    have h2 : (0 : WithTop ℚ) ≤ vK p (Z.coeff bn) + (((padicValNat p (expFact bn) : ℚ) / 2 : ℚ) : WithTop ℚ) :=
      le_trans hBB (vBB_le_coeff Z bn)
    intro q hq
    rw [valuation_mul_alt, vK_w_pow hp.out S w hw2] at hq
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 hq
    rw [← hb, ← WithTop.coe_add] at h2
    have h3 : (0 : ℚ) ≤ b + (padicValNat p (expFact bn) : ℚ) / 2 := by exact_mod_cast h2
    have h4 : a = ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) / 2 := by exact_mod_cast ha
    have h5 : ((padicValNat p (expFact bn) : ℕ) : ℚ) ≤ ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) := by
      exact_mod_cast h1
    have h6 : (0 : ℚ) ≤ q := by rw [← hab, h4]; linarith
    exact_mod_cast h6
  · rw [notMem_support_iff.1 hbn, mul_zero]
    exact geQ_zero 0

end St

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ImportsAlt
section

end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.LeCubeMul
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem le_cube_mul (k N : ℝ) (hk : 1 ≤ k) (hN : 1 ≤ N) : k ≤ k ^ 3 * N := by
  have hk2 : 1 ≤ k ^ 2 := by nlinarith
  have h1 : k ≤ k ^ 3 := by nlinarith
  calc k ≤ k ^ 3 := h1
    _ = k ^ 3 * 1 := (mul_one _).symm
    _ ≤ k ^ 3 * N := mul_le_mul_of_nonneg_left hN (by positivity)

theorem k_le_a {C : ℝ} (hC1 : 1 ≤ C) {p n' m r : ℕ} {TT : Finset (Fin n')} {L₁ L₂ : ℕ} {de h x : ℝ}
    {lam0 : Fin n' → Fin (m + 1) → ℤ} {aT bT : Fin n' → ℤ} {a Y : ℝ} {cpp c0 Dp cStar : ℕ}
    (H : Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar) : ((m + 1 : ℕ) : ℝ) ≤ a := by
  have hB := hyps_basic hC1 H
  obtain ⟨h1, h2, _, _, _, _, _, _, _, _, h11, h12⟩ := H
  have hr1 : 1 ≤ r := by omega
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : 1 ≤ p)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  have hN1 : (1 : ℝ) ≤ (TT.card : ℝ) := by exact_mod_cast hB.N_pos
  have hrr : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hQ1 : (1 : ℝ) ≤ (p : ℝ) ^ goodG' r de h x := one_le_pow₀ hp1
  have hcc : (1 : ℝ) ≤ (cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp) := by
    have h8' : (1 : ℝ) ≤ (cStar : ℝ) := by exact_mod_cast (by omega : 1 ≤ cStar)
    have : (0 : ℝ) ≤ (r : ℝ) * TT.card * c0 + 2 * r * n' * cpp := by positivity
    linarith
  obtain ⟨z1, _, _⟩ := factor_le_product_seven C (((m + 1 : ℕ) : ℝ) ^ 3) ((r : ℝ) ^ 2) (TT.card : ℝ)
    (((p : ℝ) ^ goodG' r de h x) ^ 5) ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) Y hC1
    (one_le_pow₀ hk1) (one_le_pow₀ hrr) hN1 (one_le_pow₀ hQ1) hcc (by linarith [hB.two_le_Y])
  exact le_trans (le_cube_mul _ _ hk1 hN1) (le_trans z1 h12)

section Geo

variable {n' r : ℕ} [NeZero n'] {Fr : Frames n' r} {L₁ N₁ : ℕ}

theorem posU_mem' (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j : ℤ) (u : ℕ) (hu : u < (Fr.LLset j).card + r) :
    posU Fr (Fr.LLset j).card j u ∈ Fr.letters j ∧ ¬ Fr.IsW j (posU Fr (Fr.LLset j).card j u) := by
  unfold posU
  split_ifs with h
  · exact LL_sub_letters hV hr j _ (llPos_mem Fr j u h)
  · have hi : u - (Fr.LLset j).card < r := by omega
    have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    have h2 := frame_row_monotone Fr L₁ N₁ hV (j - 1) (r - 1) (by omega)
    have h3 := frame_row_monotone Fr L₁ N₁ hV j _ hi
    have h4 := frame_entry_le_last Fr L₁ N₁ hV j _ hi
    refine ⟨?_, ?_⟩
    · unfold Frames.letters
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, h4⟩, (hV.2.2.2.2.1 j _ hi).1⟩
    · unfold Frames.IsW
      omega

theorem sl_lt_Bo (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (p : ℕ) (hp : 1 ≤ p) (deg : Fin n' → ℕ) (a : ℝ) (ha : 0 < a)
    (hdeg : ∀ s ∈ Fr.TT, a ≤ (deg s : ℝ)) (Y : ℝ) (k : ℕ) (hY : 2 ≤ Y) (hk : 1 ≤ k) {J : ℕ} (nL : ZMod J → ℕ)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ) (hu : u < nL j + r) :
    3 / 8 * slU Fr p deg Y k nL j u < Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) / 2 := by
  have hu' : u < (Fr.LLset (segZ j)).card + r := by rw [← hnL j]; exact hu
  obtain ⟨hx1, hx2⟩ := posU_mem' hV hr (segZ j) u hu'
  rw [← hnL j] at hx1 hx2
  have hB := Bo_ge hV hr p hp deg a hdeg (segZ j) _ hx1 hx2
  have hp' : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpos : 0 < Bo p Fr deg (segZ j) (posU Fr (nL j) (segZ j) u) := lt_of_lt_of_le (by positivity) hB
  unfold slU
  exact sl_lt_real _ Y (k : ℝ) _ rfl hpos hY (by exact_mod_cast hk)

end Geo

section At

variable {p n' m r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {TT : Finset (Fin n')} {L₁ L₂ N₁ G' : ℕ} {F : Frames n' r}
  {lam0 : Fin n' → Fin (m + 1) → ℤ} {a : ℝ}

theorem sizeAt_of [hpF : Fact p.Prime] (hk : m + 1 = r + K) (hF : FramesOK TT L₁ L₂ N₁ G' F) (hr : 1 ≤ r)
    (hnb : NB p m r TT.card a) (hka : ((m + 1 : ℕ) : ℝ) ≤ a)
    (hfd : ∀ s ∈ TT, a ≤ (flatDeg lam0 s : ℝ) ∧ (flatDeg lam0 s : ℝ) ≤ 2 * a)
    {J : ℕ} [NeZero J] (nL : ZMod J → ℕ) (hJ : J = F.J) (hnL : ∀ j, nL j = (F.LLset (segZ j)).card) :
    SizeAt (K := K) p F nL (dT TT lam0) (9 * ((TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a)) := by
  have hV := hF.2.1
  have hp2 : 2 ≤ p := hpF.out.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have ha2 := hnb.two_le_a
  intro rho dPl dNo hBk bp bn hbp hbn
  have hsum : ∀ x, ((dPl x + dNo x : ℕ) : ℝ) ≤ 2 * a := by
    intro x
    have htop : posOf n' (posTL F x) ∈ TT := by
      have := (posTL_seg F hV hr hnL x).2.2
      rwa [hF.1] at this
    have e := hBk.2 x
    have e2 : dT TT lam0 (posOf n' (posTL F x)) = flatDeg lam0 (posOf n' (posTL F x)) := by
      unfold dT; rw [if_pos htop]
    rw [e2] at e
    have hl : 1 ≤ lowP F p x := Nat.one_le_pow _ _ (by omega)
    have e3 : dPl x + dNo x ≤ flatDeg lam0 (posOf n' (posTL F x)) := by
      have := Nat.mul_le_mul_right (dPl x + dNo x) hl
      omega
    have e4 : ((dPl x + dNo x : ℕ) : ℝ) ≤ (flatDeg lam0 (posOf n' (posTL F x)) : ℝ) := by exact_mod_cast e3
    have := (hfd _ htop).2
    linarith
  have hdp : ∀ x, (dPl x : ℝ) ≤ 2 * a := by
    intro x
    have := hsum x
    push_cast at this
    have h0 : (0 : ℝ) ≤ (dNo x : ℝ) := Nat.cast_nonneg _
    linarith
  have hdn : ∀ x, (dNo x : ℝ) ≤ 2 * a := by
    intro x
    have := hsum x
    push_cast at this
    have h0 : (0 : ℝ) ≤ (dPl x : ℝ) := Nat.cast_nonneg _
    linarith
  have hcard : Fintype.card (TL J nL r) ≤ TT.card := by
    have := card_TL_le F hV hr hJ hnL
    rwa [hF.1] at this
  have A := DnoOf_le (K := K) p hp2 nL dNo TT.card (m + 1) a hr (by omega) hcard hdn ha2 hnb.fourN hka
  have B := mult_level_real p dPl bp hbp TT.card a ha2 hcard hdp
  have Cc := mult_level_real p dNo bn hbn TT.card a ha2 hcard hdn
  have hrk : (r : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : r ≤ m + 1)
  have hKk : (K : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : K ≤ m + 1)
  have hk1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m + 1)
  exact size_fin (TT.card : ℝ) ((m + 1 : ℕ) : ℝ) (r : ℝ) (K : ℝ) (Real.logb p a) _ _ _ (Nat.cast_nonneg _)
    (by linarith [hnb.one_le_log]) hk1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) hrk hKk A B Cc

end At

end Formalism.MainNotions.Proposition5Numerics
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembLabF
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords
open Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

section Geo

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) {L₁ N₁ : ℕ}

theorem lf_fr_per (hV : Fr.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    Fr.fr (j + m * Fr.J) i = Fr.fr j i + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    rw [show j + ((k : ℤ) + 1) * (Fr.J : ℤ) = (j + (k : ℤ) * Fr.J) + Fr.J by ring, hV.2.1, ih]
    ring
  | pred k ih =>
    have h := hV.2.1 (j + (-(k : ℤ) - 1) * Fr.J) i
    rw [show j + (-(k : ℤ) - 1) * (Fr.J : ℤ) + Fr.J = j + -(k : ℤ) * Fr.J by ring, ih] at h
    linarith

private theorem fr_mono_of_valid (hV : Fr.Valid L₁ N₁) (j : ℤ) :
    ∀ i i' : ℕ, i ≤ i' → i' < r → Fr.fr j i ≤ Fr.fr j i' := by
  intro i i' hii' hi'
  induction i' with
  | zero => rw [Nat.le_zero.mp hii']
  | succ k ih =>
    rcases Nat.lt_or_ge i (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (hV.2.2.1 j k (by omega)).le
    · rw [le_antisymm hii' h]

private theorem fr_last_mono_in_index_of_valid (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (a : ℤ) :
    ∀ b : ℤ, a ≤ b → Fr.fr a (r - 1) ≤ Fr.fr b (r - 1) := by
  intro b hab
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
  clear hab
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := le_trans (hV.2.2.2.1 (a + n)).le
      (fr_mono_of_valid Fr hV (a + n + 1) 0 (r - 1) (Nat.zero_le _) (by omega))
    exact le_trans ih (by simpa [add_assoc] using hstep)

theorem lf_dist_eq (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (j j' x y : ℤ) (hx1 : Fr.fr (j - 1) (r - 1) < x)
    (hx2 : x ≤ Fr.fr j (r - 1)) (hy1 : Fr.fr (j' - 1) (r - 1) < y) (hy2 : y ≤ Fr.fr j' (r - 1))
    (h : posOf n' y = posOf n' x) : Fr.dist j x = Fr.dist j' y := by
  have hn0 : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hv : ((y % (n' : ℤ)).toNat % n') = ((x % (n' : ℤ)).toNat % n') := congrArg Fin.val h
  have ex1 : 0 ≤ x % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ex2 : x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have ey1 : 0 ≤ y % (n' : ℤ) := Int.emod_nonneg _ hn0.ne'
  have ey2 : y % (n' : ℤ) < n' := Int.emod_lt_of_pos _ hn0
  have hmod : y % (n' : ℤ) = x % (n' : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hv
    omega
  obtain ⟨k, hk⟩ : (n' : ℤ) ∣ y - x := Int.dvd_of_emod_eq_zero (Int.emod_emod_of_dvd _ (dvd_refl _) ▸ (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp hmod))
  have hJ1 := lf_fr_per Fr hV j (r - 1) k
  have hJ2 := lf_fr_per Fr hV (j - 1) (r - 1) k
  have hjj : j' = j + k * Fr.J := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := fr_last_mono_in_index_of_valid Fr hV hr j' (j - 1 + k * Fr.J) (by linarith)
      rw [hJ2] at this
      nlinarith
    · have := fr_last_mono_in_index_of_valid Fr hV hr (j + k * Fr.J) (j' - 1) (by linarith)
      rw [hJ1] at this
      nlinarith
  unfold Frames.dist
  rw [hjj, hJ1]
  congr 1
  linarith

end Geo

section Lab

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r) (K : ℕ) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem labO_apply (hinj : Function.Injective fun x : TL J nL r => posOf n' (posTL Fr x))
    (rho : TL J nL r × Fin (r + K) → ℕ) (y : TL J nL r) (c : Fin (r + K)) :
    labO Fr K nL rho (posOf n' (posTL Fr y), c) = rho (y, c) := by
  classical
  simp only [labO, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single c]
    · simp
    · intro c' _ hc'
      rw [if_neg]
      intro h
      exact hc' (Prod.ext_iff.mp h).2
    · intro h; exact absurd (Finset.mem_univ c) h
  · intro x _ hx
    apply Finset.sum_eq_zero
    intro c' _
    rw [if_neg]
    intro h
    exact hx (hinj (Prod.ext_iff.mp h).1)
  · intro h; exact absurd (Finset.mem_univ y) h

theorem labO_support (rho : TL J nL r × Fin (r + K) → ℕ) (v : Fin n' × Fin (r + K))
    (hv : v ∈ (labO Fr K nL rho).support) : ∃ x : TL J nL r, v.1 = posOf n' (posTL Fr x) := by
  classical
  by_contra hne
  push_neg at hne
  apply Finsupp.mem_support_iff.mp hv
  simp only [labO, Finsupp.finsetSum_apply, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro c _
  rw [if_neg]
  intro h
  exact hne x (Prod.ext_iff.mp h).1.symm

end Lab

theorem restLabG : RestLabG := by
  intro p _ n' r K _ _ _ O _ _ _ _S Fr TT L₁ L₂ N₁ G' deg d Y cP hMFH J _ Dt dPl dNo ka rho No Go hMH
  obtain ⟨hJ, hnL, -⟩ := hMH.1.1
  have hV : Fr.Valid L₁ N₁ := hMFH.frames.2.1
  have hr : 1 ≤ r := by have := hMFH.two_le_r; omega
  have hinj := posTL_inj Fr hV hr hJ hnL
  have hB := hMH.2.1
  unfold LabAt
  refine ⟨?_, ?_⟩
  · intro j x hx hW c
    by_cases hy : ∃ y : TL J Dt.nL r, posOf n' (posTL Fr y) = posOf n' x
    · obtain ⟨y, hy⟩ := hy
      rw [← hy, labO_apply Fr K Dt.nL hinj rho y c]
      have hlt := hB.1 y c
      have hseg := posTL_seg Fr hV hr hnL y
      have hxl := (Finset.mem_filter.mp hx).1
      rw [Finset.mem_Icc] at hxl
      have hd := lf_dist_eq Fr hV hr j (segZ y.1) x (posTL Fr y) (not_le.mp hW) hxl.2 hseg.1 hseg.2.1 hy
      rw [hd]
      exact hlt
    · push_neg at hy
      have h0 : labO Fr K Dt.nL rho (posOf n' x, c) = 0 := by
        by_contra hne
        obtain ⟨y, hy'⟩ := labO_support Fr K Dt.nL rho (posOf n' x, c) (Finsupp.mem_support_iff.mpr hne)
        exact hy y hy'.symm
      rw [h0]
      exact pow_pos (Fact.out : p.Prime).pos _
  · intro v hv
    obtain ⟨y, hy⟩ := labO_support Fr K Dt.nL rho v hv
    rw [hy]
    exact (posTL_seg Fr hV hr hnL y).2.2

end Formalism.MainNotions.Proposition5Numerics
end
end

