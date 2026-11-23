module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Mathlib
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedFDerivAlgebraicDirectionsJetTransport
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.JetTransport

section Formal

variable {σ : Type} [Fintype σ] [DecidableEq σ] {p : ℕ} [Fact p.Prime]

def factP (n : σ →₀ ℕ) : ℂ_[p] := ∏ i, ((n i).factorial : ℂ_[p])

theorem multiIndexFactorial_zero : (factP (0 : σ →₀ ℕ) : ℂ_[p]) = 1 := by simp [factP]

theorem multiIndexFactorial_add_single (n : σ →₀ ℕ) (k : σ) :
    (factP (n + Finsupp.single k 1) : ℂ_[p]) = factP n * ((n k : ℂ_[p]) + 1) := by
  unfold factP
  have h : ∀ i, (((n + Finsupp.single k 1 : σ →₀ ℕ) i).factorial : ℂ_[p]) =
      ((n i).factorial : ℂ_[p]) * (if i = k then (n k : ℂ_[p]) + 1 else 1) := by
    intro i
    by_cases hi : i = k
    · subst hi
      rw [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, if_pos rfl]
      push_cast; ring
    · rw [Finsupp.add_apply, if_neg hi]
      simp [Finsupp.single_apply, Ne.symm hi]
  rw [Finset.prod_congr rfl fun i _ => h i, Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k]
  simp

theorem coeff_pd (k : σ) (F : MvPowerSeries σ ℂ_[p]) (n : σ →₀ ℕ) :
    MvPowerSeries.coeff n (pd k F) = ((n k : ℂ_[p]) + 1) * MvPowerSeries.coeff (n + Finsupp.single k 1) F := rfl

def cntL (l : List σ) : σ →₀ ℕ := (l.map fun k => Finsupp.single k 1).sum

theorem coeff_foldr_pd (F : MvPowerSeries σ ℂ_[p]) : ∀ (l : List σ) (n : σ →₀ ℕ),
    factP n * MvPowerSeries.coeff n (l.foldr (fun k G => pd k G) F) =
      factP (n + cntL l) * MvPowerSeries.coeff (n + cntL l) F
  | [], n => by simp [cntL]
  | k :: l, n => by
    have hc : cntL (k :: l) = Finsupp.single k 1 + cntL l := by simp [cntL]
    rw [List.foldr_cons, coeff_pd, ← mul_assoc, ← multiIndexFactorial_add_single, coeff_foldr_pd F l, hc, add_assoc]

theorem pd_sum_smul {ι : Type} (s : Finset ι) (a : ι → ℂ_[p]) (P : ι → MvPowerSeries σ ℂ_[p]) (k : σ) :
    pd k (∑ i ∈ s, a i • P i) = ∑ i ∈ s, a i • pd k (P i) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coeff_pd, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem foldr_expand {β : Type} (c : β → σ → ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) : ∀ (m : ℕ) (y : Fin m → β),
    (List.ofFn y).foldr (fun b G => ∑ k, algebraMap ℂ_[p] (MvPowerSeries σ ℂ_[p]) (c b k) * pd k G) F =
      ∑ f : Fin m → σ, (∏ j, c (y j) (f j)) • (List.ofFn f).foldr (fun k G => pd k G) F
  | 0, y => by simp
  | m + 1, y => by
    rw [List.ofFn_succ, List.foldr_cons, foldr_expand c F m]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => σ)).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Algebra.smul_def, pd_sum_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    have e : (Fin.consEquiv (fun _ : Fin (m + 1) => σ)) (k, f) = Fin.cons k f := rfl
    rw [e, List.ofFn_cons, List.foldr_cons, Fin.prod_univ_succ, smul_smul]
    simp only [Fin.cons_zero, Fin.cons_succ]

theorem cntL_ofFn {m : ℕ} (f : Fin m → σ) : cntL (List.ofFn f) = ∑ j, Finsupp.single (f j) 1 := by
  simp [cntL, List.map_ofFn, List.sum_ofFn]

end Formal

section Cplx

variable {σ : Type} [Fintype σ]

def cnt {k : ℕ} (f : Fin k → σ) (i : σ) : ℕ := (Finset.univ.filter fun j => f j = i).card

theorem perm_of_cnt {k : ℕ} (f l : Fin k → σ) (h : ∀ i, cnt f i = cnt l i) :
    ∃ e : Equiv.Perm (Fin k), f = l ∘ e := by
  have e : ∀ c, {a // f a = c} ≃ {b // l b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact h c)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext a
  exact (Equiv.ofFiberEquiv_map e a).symm

theorem cnt_toList (α : σ →₀ ℕ) (i : σ) :
    cnt (fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩) i = α i := by
  set l := fun j : Fin (Multiset.card α.toMultiset) => α.toMultiset.toList.get ⟨j, by simpa using j.2⟩
  have hmap : Multiset.map l Finset.univ.val = α.toMultiset := by
    rw [Fin.univ_val_map]
    have : List.ofFn l = α.toMultiset.toList := by
      refine List.ext_get (by simp) ?_
      intro n h1 h2
      simp [l]
    rw [this, Multiset.coe_toList]
  have h := congrArg (Multiset.count i) hmap
  rw [Multiset.count_map, Finsupp.count_toMultiset] at h
  rw [← h]
  unfold cnt
  rw [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun j _ => eq_comm

def cntF {m : ℕ} (f : Fin m → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (f j) 1

theorem cntF_apply {m : ℕ} (f : Fin m → σ) (i : σ) : cntF f i = cnt f i := by
  rw [cntF, cnt, Finsupp.finsetSum_apply, Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : f j = i
  · rw [h, if_pos rfl, Finsupp.single_eq_same]
  · rw [if_neg h, Finsupp.single_apply, if_neg h]

theorem card_cntF {m : ℕ} (f : Fin m → σ) : Multiset.card (cntF f).toMultiset = m := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cntF, map_sum, Multiset.card_sum]
  simp

end Cplx

section Main

variable {D : D7} {N N' : ℕ}

theorem vec_eq (v : VC D N N') :
    v = ∑ k : D.what₂.Tau × Fin N' × Fin N, v k.1 k.2.1 k.2.2 • coordV D k := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, coordV, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (τ, i, j)]
  · simp
  · rintro ⟨a, b, c⟩ _ hb
    rw [if_neg]
    rintro ⟨rfl, rfl, rfl⟩
    exact hb rfl
  · simp

theorem mlin_expand {m : ℕ} (A : ContinuousMultilinearMap ℂ (fun _ : Fin m => VC D N N') ℂ) (v : Fin m → VC D N N') :
    A v = ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
      (∏ j, v j (f j).1 (f j).2.1 (f j).2.2) * A (fun j => coordV D (f j)) := by
  have hv : v = fun j => ∑ k : D.what₂.Tau × Fin N' × Fin N, v j k.1 k.2.1 k.2.2 • coordV D k :=
    funext fun j => vec_eq (v j)
  conv_lhs => rw [hv]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [A.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [A.map_smul_univ, smul_eq_mul]

theorem iFD_coord (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G) {m : ℕ} (f : Fin m → D.what₂.Tau × Fin N' × Fin N) :
    iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) =
      (∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f) := by
  have key : ∀ (k : ℕ) (hk : k = m) (l : Fin k → D.what₂.Tau × Fin N' × Fin N), (∀ i, cnt l i = cntF f i) →
      iteratedFDeriv ℂ k G 0 (fun j => coordV D (l j)) = iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) := by
    rintro k rfl l hl
    obtain ⟨e, he⟩ := perm_of_cnt f l (fun i => by rw [hl, cntF_apply])
    rw [he]
    exact (hG.contDiffAt.iteratedFDeriv_comp_perm (fun j => coordV D (l j)) e).symm
  have e1 : iteratedFDeriv ℂ (Multiset.card (cntF f).toMultiset) G 0
      (fun i => coordV D ((cntF f).toMultiset.toList.get ⟨i, by simpa using i.2⟩)) =
      iteratedFDeriv ℂ m G 0 (fun j => coordV D (f j)) :=
    key _ (card_cntF f) _ (cnt_toList (cntF f))
  have h0 : ((cntF f).prod fun _ n => (n.factorial : ℂ)) = ∏ i, ((cntF f i).factorial : ℂ) :=
    Finsupp.prod_fintype _ _ (by simp)
  have hne : (∏ i, ((cntF f i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  unfold taylor
  rw [e1, h0, mul_div_cancel₀ _ hne]

theorem embT_mem (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom)

theorem lam_mk {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : ℂ) (h : a ∈ Qbar) :
    lam ⟨a, h⟩ = lamC lam a := by
  unfold lamC; rw [dite_eq_left h]

end Main

end GlobalTheory.JetTransport

namespace GlobalTheory.JetTransport

theorem jet_pSer : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N N' : ℕ) (G : VC D N N' → ℂ), ContDiff ℂ ⊤ G → CoefIn D G Qbar → ∀ (m : ℕ) (y : Fin m → Matrix (Fin N') (Fin N) D.host.E), iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) ∈ Qbar ∧ jet D lam y (pSer D lam G) = lamC lam (iteratedFDeriv ℂ m G 0 fun j => embV D (tor0 D cc δ) (y j)) := by
  intro D cc δ p _ lam N N' G hG hco m y
  have hC : iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, embT D (f j).1 (y j (f j).2.1 (f j).2.2)) *
        ((∏ i, ((cntF f i).factorial : ℂ)) * taylor D G (cntF f)) := by
    rw [mlin_expand]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [iFD_coord G hG f]
    rfl
  have hP : jet D lam y (pSer D lam G) =
      ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N, (∏ j, lamC lam (embT D (f j).1 (y j (f j).2.1 (f j).2.2))) *
        ((∏ i, ((cntF f i).factorial : ℂ_[p])) * lamC lam (taylor D G (cntF f))) := by
    unfold jet
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hx := foldr_expand (fun (b : Matrix (Fin N') (Fin N) D.host.E) (k : D.what₂.Tau × Fin N' × Fin N) =>
      lamC lam (embT D k.1 (b k.2.1 k.2.2))) (pSer D lam G) m y
    erw [hx, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, smul_eq_mul]
    congr 1
    have h := coeff_foldr_pd (pSer D lam G) (List.ofFn f) 0
    rw [zero_add, cntL_ofFn, multiIndexFactorial_zero, one_mul] at h
    rw [h]
    rfl
  set z : Qbar := ∑ f : Fin m → D.what₂.Tau × Fin N' × Fin N,
    (∏ j, (⟨embT D (f j).1 (y j (f j).2.1 (f j).2.2), embT_mem _ _⟩ : Qbar)) *
      ((∏ i, ((cntF f i).factorial : Qbar)) * ⟨taylor D G (cntF f), hco _⟩) with hzdef
  have hz : (z : ℂ) = iteratedFDeriv ℂ m G 0 (fun j => embV D (tor0 D cc δ) (y j)) := by
    rw [hC, hzdef, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul, IntermediateField.coe_prod, IntermediateField.coe_prod]
    simp
  have hl : lam z = jet D lam y (pSer D lam G) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hP, hzdef, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [map_mul, map_prod, map_natCast, lam_mk]
  refine ⟨hz ▸ z.2, ?_⟩
  rw [← hz, ← hl]
  exact lam_mk lam _ z.2

end GlobalTheory.JetTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OneLeLetterBlockLength
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory.HCEntries

variable {D : D7} {L : SizeData₂ D}

theorem one_le_scL (L : SizeData₂ D) : 1 ≤ L.sc.L :=
  Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b (L : SizeData₂ D) : 1 ≤ L.sc.b :=
  Real.one_le_exp (by linarith [one_le_scL L])

theorem b'_pos (L : SizeData₂ D) : 0 < L.sc.b' := by
  have := L.sc.one_lt_alt
  have := one_le_b L
  unfold Scale.b' Scale.a Scale.X'
  positivity

theorem one_le_n (D : D7) : (1 : ℝ) ≤ D.R.n := by
  have : 1 ≤ D.R.n := by unfold Ranks.n; exact D.R.ord_pos
  exact_mod_cast this

theorem one_le_k (D : D7) : (1 : ℝ) ≤ D.R.k := by
  have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  exact_mod_cast this

theorem one_le_letterBlockLength (D : D7) : (1 : ℝ) ≤ D.R.t := by
  have : 1 ≤ D.R.t := by have := D.R.three_m_lt_t; omega
  exact_mod_cast this

theorem eta_k_le (h : SizeEta L) : L.etaSz ≤ L.sc.b ∧ (D.R.k : ℝ) ≤ L.sc.b := by
  obtain ⟨h1, h2, -⟩ := h
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hf : (1 : ℝ) ≤ D.R.f := by
    have := one_le_n D
    unfold Ranks.f
    push_cast
    linarith
  have hk3 : (D.R.k : ℝ) ≤ (D.R.k : ℝ) ^ 3 := le_self_pow₀ hk (by norm_num)
  have htf : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := one_le_mul_of_one_le_of_one_le (one_le_pow₀ ht) hf
  have hP : (D.R.k : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 :=
    hk3.trans (le_mul_of_one_le_left (by positivity) htf)
  rw [le_div_iff₀ (by linarith)] at h2
  constructor <;> nlinarith

theorem b'_Sc_le (h : SizeLstar L) : L.sc.b' + L.Sc ≤ L.sc.b := by
  have hk := one_le_k D
  have ht := one_le_letterBlockLength D
  have hn := one_le_n D
  have hL := one_le_scL L
  have hb := one_le_b L
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hN0 : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hmt : (D.R.m : ℝ) ≤ D.R.t := by
    have : D.R.m ≤ D.R.t := by have := D.R.three_m_lt_t; omega
    exact_mod_cast this
  have h0 : 0 ≤ szlStar L := by unfold szlStar; positivity
  have h1 : szlStar L ≤ L.sc.b := by
    unfold szlStar
    rw [div_le_iff₀ (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    have e1 : (1 : ℝ) ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 := one_le_mul_of_one_le_of_one_le hk (one_le_pow₀ hn)
    have e2 : L.Sc + D.R.t + L.sc.L ≤ (D.R.k : ℝ) * (D.R.n : ℝ) ^ 2 * (L.Sc + D.R.t + L.sc.L) :=
      le_mul_of_one_le_left (by positivity) e1
    have e3 : 0 ≤ (D.R.n : ℝ) * (D.R.t : ℝ) ^ 2 * ((D.R.N D.R.m : ℝ) + D.R.t) * L.sc.L ^ 2 := by positivity
    linarith
  have h2 : 0 ≤ L.sc.b / szlStar L := div_nonneg (by linarith) h0
  linarith [h.1]

theorem bT_le (hLa : SizeLa L) (hR : SizeRho L) (hB : SizeBot L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ 5 / 4 * L.sc.b' := by
  have hx := L.sc.one_lt_alt
  have hk := one_le_k D
  have hb := b'_pos L
  have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg (by linarith) _) hLa.1
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx.le
  have h1 : 0 ≤ L.sc.x ^ szTh L * Real.log L.sc.x * L.LaG / D.R.k := by positivity
  have h2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by norm_num)
  unfold SizeRho at hR
  have h3 : szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h4 := hB t
  have h5 : szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h6 := mul_le_mul_of_nonneg_right h3 hb.le
  linarith

theorem aT_le (L : SizeData₂ D) (t : D.host.TT) : (L.aT t : ℝ) ≤ 2 * L.sc.x * L.sc.b := by
  have hx := L.sc.one_lt_alt
  have hb := one_le_b L
  have h1 := (L.aT_win t).2
  have h2 : (1 : ℝ) ≤ (D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_k D) (Real.one_le_rpow hx.le (by unfold Scale.A; norm_num))
  have h3 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a :=
    div_le_self (by unfold Scale.a; positivity) h2
  have h4 : L.sc.a = L.sc.x * L.sc.b := rfl
  linarith

theorem exists_top {τ : D.what₂.Tau} (h : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces) :
    ∃ t : D.host.TT, (D.eTau τ : D.R.GG) = D.R.tau1 t := by
  unfold Host.topPlaces at h
  obtain ⟨t, ht, hte⟩ := Finset.mem_image.1 h
  exact ⟨⟨t, ht⟩, hte.symm⟩

theorem wj_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    0 ≤ wj D j τ ∧ wj D j τ ≤ 3 * L.sc.b := by
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hR, hB, -, -, hE, -, hS, -⟩ := h
  have hb := one_le_b L
  have hb' := b'_pos L
  have he := (eta_k_le hE).1
  have hbb : L.sc.b' ≤ L.sc.b := by linarith [b'_Sc_le hS, L.Sc_pos]
  by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht⟩ := exists_top ha
    obtain ⟨a1, a2⟩ := L.win_top j h1 h2 τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le hLa hR hB t
    have a5 : 0 ≤ L.sc.b' / L.sc.x := by positivity
    have a6 : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx
    constructor <;> linarith
  · by_cases hc : (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces
    · obtain ⟨a1, a2⟩ := L.win_thick j h1 h2 τ hc
      constructor <;> linarith
    · obtain ⟨a1, a2⟩ := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, ha, hc⟩
      have hn := one_le_n D
      have a5 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
      have a6 : L.sc.w'' D.R.n ≤ L.sc.b' :=
        div_le_self hb'.le (one_le_mul_of_one_le_of_one_le (by linarith) hn)
      constructor <;> linarith

theorem b_bounds (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (j : Fin D.R.m) :
    -L.sc.b ≤ (((D.hc τ).b j : ℚ) : ℝ) ∧ (((D.hc τ).b j : ℚ) : ℝ) ≤ 3 * L.sc.b := by
  obtain ⟨a1, a2⟩ := wj_bounds h hx (j.1 + 1) (by omega) j.2 τ
  have hw : wj D (j.1 + 1) τ = (((D.hc τ).e j : ℚ) : ℝ) := by
    unfold wj
    rw [dite_eq_left (by simp)]
    rfl
  rw [hw] at a1 a2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := h
  have he := (eta_k_le hE).1
  have a3 := abs_le.1 (L.be_close τ j j)
  have a4 : (D.hc τ).b j ≤ (D.hc τ).e j := by
    have := (D.hc τ).gap_be j
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have a5 : (((D.hc τ).b j : ℚ) : ℝ) ≤ (((D.hc τ).e j : ℚ) : ℝ) := by exact_mod_cast a4
  push_cast at a3
  constructor <;> linarith [a3.1]

theorem sigPar_bound (h : SizesAt L) (hx : 2 ≤ L.sc.x) (τ : D.what₂.Tau) (l : ℕ) :
    |((sigPar D τ l : ℚ) : ℝ)| ≤ 4 * L.sc.b := by
  have hb := one_le_b L
  have hS : L.Sc ≤ L.sc.b := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, -⟩ := h
    linarith [b'_Sc_le hS, b'_pos L]
  unfold sigPar
  split_ifs with h1 h2
  · obtain ⟨a1, a2⟩ := L.cloud_v τ ⟨l, h1⟩
    rw [abs_le]
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := b_bounds h hx τ ⟨_, h2⟩
    rw [abs_le]
    push_cast
    constructor <;> linarith
  · simp only [Rat.cast_zero, abs_zero]
    linarith

theorem u_bound (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (l : Fin D.R.k) : |(((D.hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * L.sc.x * L.sc.b := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hm := D.R.two_le_m
  have hb := one_le_b L
  have hxb : 2 * L.sc.b ≤ L.sc.x * L.sc.b := mul_le_mul_of_nonneg_right hx (by linarith)
  have hb1 := b_bounds h hx τ ⟨0, by omega⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hE, -, hS, -⟩ := h
  have hkb := (eta_k_le hE).2
  have hS : L.Sc ≤ L.sc.b := by linarith [b'_Sc_le hS, b'_pos L]
  obtain ⟨r, hr⟩ := l
  rw [abs_le]
  by_cases h0 : r = 0
  · subst h0
    rw [D.hcW_first u τ hr]
    have h2 := L.cloud_v τ ⟨0, by omega⟩
    have h3 : (((D.hc τ).v ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨0, hr⟩ : ℚ) : ℝ) := by
      exact_mod_cast (D.hc τ).u_gt_v ⟨0, by omega⟩
    refine ⟨by linarith [h2.1], ?_⟩
    by_cases ha : (D.eTau τ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht⟩ := exists_top ha
      rw [(L.top_u τ t hr ht).1]
      linarith [aT_le L t]
    · have h1 := P.cloud_place_bound τ (by omega) ha
      push_cast at h1
      linarith [h2.2]
  · by_cases hl : r + 1 < D.R.k
    · have := L.cloud_u u τ ⟨r, hr⟩ (by show 1 ≤ r; omega) hl
      constructor <;> linarith [this.1, this.2]
    · obtain rfl : r = D.R.k - 1 := by omega
      rw [D.hcW_last u τ (by omega)]
      have h2 := L.cloud_v τ ⟨D.R.k - 2, by omega⟩
      have h3 : -(((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) < (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) := by
        exact_mod_cast (D.hc τ).u_last_gt (by omega) (by omega)
      have h4 : (((D.hc τ).u ⟨D.R.k - 1, hr⟩ : ℚ) : ℝ) < (((D.hc τ).v ⟨D.R.k - 2, by omega⟩ : ℚ) : ℝ) := by
        have := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
        have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, hr⟩ :=
          Fin.ext (by show D.R.k - 2 + 1 = D.R.k - 1; omega)
        simp only at this
        rw [e] at this
        exact_mod_cast this
      constructor <;> linarith [h2.2, hb1.2]

theorem entries : ∀ (eps : ℝ) (Fm : FamP eps), (∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, (∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, 0 ≤ wj (Fm.D x i) j τ ∧ wj (Fm.D x i) j τ ≤ 3 * (Fm.L x i).sc.b ∧ wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ) ∧ (∀ u τ (l : Fin (Fm.D x i).R.k), |((((Fm.D x i).hcW u τ).u l : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b) ∧ (∀ τ l, |((sigPar (Fm.D x i) τ l : ℚ) : ℝ)| ≤ 4 * (Fm.L x i).sc.b)) := by
  intro eps Fm
  refine ⟨2, fun x hx2 hx i => ?_⟩
  have hS := Fm.sizes x hx i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have h2 : 2 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx2
  refine ⟨fun j hj τ => ?_, fun u τ l => ?_, fun τ l => sigPar_bound hS h2 τ l⟩
  · obtain ⟨h1, hm⟩ := Finset.mem_Icc.1 hj
    obtain ⟨a1, a2⟩ := wj_bounds hS h2 j h1 hm τ
    refine ⟨a1, a2, ?_⟩
    unfold wSz wj
    rw [dite_eq_left ⟨h1, hm⟩, dite_eq_left (by omega)]
  · have := u_bound hS (Fm.params x hx i) h2 u τ l
    rwa [hsx] at this

end GlobalTheory.HCEntries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScaleOneLeA
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem scale_one_le_a (s : Scale) : 1 ≤ s.a := by
  have hx : 1 < s.x := s.one_lt_alt
  have hL : 0 ≤ s.L := by
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ s.b := by
    unfold Scale.b
    exact Real.one_le_exp hL
  unfold Scale.a
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem famP_La_nonneg : ∀ (eps : ℝ) (Fm : FamP eps), ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x,
    0 ≤ (Fm.L x i).La := by
  intro eps Fm x hx i
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := Fm.sizes x hx i
  obtain ⟨-, -, -, -, -, -, hrd, -⟩ := hQD
  unfold SizeData₂.La
  exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (scale_one_le_a _) hrd)

end GlobalTheory
end

