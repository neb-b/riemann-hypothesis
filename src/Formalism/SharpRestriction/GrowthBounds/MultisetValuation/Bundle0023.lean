module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0021
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0022
public import Formalism.LocalRingCardinality.ColumnWeightSpreadOffTop
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.TheoremSFromKOneOf

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaApplyDScale
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem ea_applyD_scale {σ τ K : Type} [Field K] (q E : ℕ) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) f = ((q : K) ^ E) • applyD P f := by
  classical
  have hc : ∀ n, AddMonoidAlgebra.coeff ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P) n =
      (q : MvPolynomial τ ℤ) ^ E * AddMonoidAlgebra.coeff P n := by
    intro n
    have : (q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E = MvPolynomial.C ((q : MvPolynomial τ ℤ) ^ E) := by
      rw [map_pow, map_natCast]
    rw [this, MvPolynomial.coeff_C_mul]
  have hsub : ((q : MvPolynomial σ (MvPolynomial τ ℤ)) ^ E * P).support ⊆ P.support := by
    intro n hn
    rw [MvPolynomial.mem_support_iff, hc] at hn
    rw [MvPolynomial.mem_support_iff]
    intro h0
    rw [h0, mul_zero] at hn
    exact hn rfl
  unfold applyD
  rw [Finset.sum_subset hsub (fun n _ hn => by
    rw [MvPolynomial.notMem_support_iff.1 hn, map_zero, smul_zero]), Finset.smul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hc, map_mul, map_pow, map_natCast, smul_comm]
  congr 1
  rw [MvPolynomial.smul_eq_C_mul, map_pow, map_natCast]

theorem ea_applyD_zero {σ τ K : Type} [Field K] (f : MvPowerSeries σ K) :
    applyD (0 : MvPolynomial σ (MvPolynomial τ ℤ)) f = 0 := by
  unfold applyD
  rw [MvPolynomial.support_zero, Finset.sum_empty]

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_PIvS_eq (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^
      (∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I i0 v s c) * X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

theorem ea_colFac_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ)
    (h : ¬ Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) : X.colFac j I v s c = 0 := by
  unfold Function.Injective at h
  push Not at h
  obtain ⟨x, y, hxy, hne⟩ := h
  unfold Sys.colFac
  refine Matrix.det_zero_of_column_eq hne fun k => ?_
  show (∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c x.val)⟩ : X.ZA j)) =
    ∑ a : Fin (NN X.G.P.m X.t j), _ * MvPolynomial.X (⟨v, (s, a, I v s c y.val)⟩ : X.ZA j)
  have hxy' : I v s c x.val = I v s c y.val := hxy
  rw [hxy']

theorem ea_card_img {H N : ℕ} (g : Fin H → Fin N) (hg : Function.Injective g) (i : ℕ) :
    ((univ.image g) ∩ univ.filter (fun b : Fin N => b.val < i)).card =
      (univ.filter fun x : Fin H => (g x).val < i).card := by
  rw [← Finset.card_image_of_injective _ hg]
  congr 1
  ext b
  simp only [mem_inter, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨x, rfl⟩, hb⟩
    exact ⟨x, hb, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, rfl⟩, hx⟩

theorem ea_Exp_eq (v : X.Pl) (j i : ℕ) (I : X.ColCh j)
    (h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val) :
    ∑ s : Fin (X.G.P.n' v), ∑ c ∈ range (X.nuv v (j + 1) s 1).toNat, X.colExp j I (fun _ => i) v s c =
      ea_Exp X v j i I := by
  unfold ea_Exp
  refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
  rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 := ea_card_img (ea_Ic X v j I s' c) (h ((ea_e X v).symm s') c.val) i
  have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
    (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
  have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
      univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
      ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
        fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
  rw [e3]
  unfold Sys.colExp
  have hv : ((ea_e X v).symm s').val = s'.val := rfl
  by_cases hodd : s'.val % 2 = 0
  · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
    rfl
  · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]

theorem ea_brScale : ea_BrScale X := by
  intro v j i K' _ F I n
  by_cases h : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ), c ∈ range (X.nuv v (j + 1) s 1).toNat →
      X.colFac j I v s c ≠ 0
  · by_cases h2 : ∀ (s : Fin (X.G.P.n' v)) (c : ℕ),
        Function.Injective fun i' : Fin (X.colHt v (j + 1) s c) => I v s c i'.val
    · right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul, ea_Exp_eq X v j i I h2]
    ·
      right
      rw [ea_PIvS_eq, ea_applyD_scale, MvPolynomial.coeff_smul, smul_eq_mul]
      congr 2
      unfold ea_Exp
      refine (Fintype.sum_equiv (ea_e X v).symm _ _ fun s' => ?_).symm
      rw [← Fin.sum_univ_eq_sum_range (fun c => X.colExp j I (fun _ => i) v ((ea_e X v).symm s') c)]
      refine Finset.sum_congr rfl fun c _ => ?_
      have hinj : Function.Injective fun i' : Fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val) =>
          I v ((ea_e X v).symm s') c.val i'.val := by
        by_contra hni
        exact h _ c.val (mem_range.2 c.isLt) (ea_colFac_zero X j I v _ _ hni)
      have e1 := ea_card_img (ea_Ic X v j I s' c) hinj i
      have e2 := ea_card_fin (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)
        (fun x => (I v ((ea_e X v).symm s') c.val x).val < i)
      have e3 : ((univ.image (ea_Ic X v j I s' c)) ∩
          univ.filter (fun b : Fin (NN X.G.P.m X.t (j + 1)) => b.val < i)).card =
          ((range (X.colHt v (j + 1) ((ea_e X v).symm s') c.val)).filter
            fun x => (I v ((ea_e X v).symm s') c.val x).val < i).card := e1.trans e2
      rw [e3]
      unfold Sys.colExp
      have hv : ((ea_e X v).symm s').val = s'.val := rfl
      by_cases hodd : s'.val % 2 = 0
      · rw [if_pos hodd, if_neg (by unfold IsOddPos; rw [hv]; omega)]
        rfl
      · rw [if_neg hodd, if_pos (by unfold IsOddPos; rw [hv]; omega)]
  · left
    push Not at h
    obtain ⟨s, c, hc, h0⟩ := h
    have hz : PIvS X j I (fun _ => i) v = 0 := by
      unfold PIvS
      refine Finset.prod_eq_zero (Finset.mem_univ s) (Finset.prod_eq_zero hc ?_)
      rw [h0, mul_zero]
    rw [hz, ea_applyD_zero, MvPolynomial.coeff_zero]
    rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceBoundLargePrimes
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Fl

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem ne_lamI_last (s : Fin (G.P.n' v)) : lamI (G.P.lam0 v) s (G.P.m + 1) = G.P.lam0 v s (Fin.last G.P.m) := by
  unfold lamI
  rw [dite_eq_left ⟨by omega, le_rfl⟩]
  rfl

theorem ne_lamI_le (s : Fin (G.P.n' v)) (a : ℕ) (hm : 2 ≤ G.P.m) (hb : s ∈ Fl.TT v → 0 ≤ Fl.b v s) :
    lamI (G.P.lam0 v) s a ≤ (Fl.c : ℤ) + (if s ∈ Fl.TT v ∧ a = 1 then Fl.a v s else 0) := by
  have hc : (0 : ℤ) ≤ Fl.c := Int.natCast_nonneg _
  unfold lamI
  by_cases h : 1 ≤ a ∧ a ≤ G.P.m + 1
  · rw [dite_eq_left h]
    by_cases hs : s ∈ Fl.TT v
    · obtain ⟨h1, h2, h3⟩ := (Fl.base v s).1 hs
      by_cases ha : a = 1
      · subst ha
        rw [if_pos ⟨hs, rfl⟩]
        have : G.P.lam0 v s ⟨1 - 1, by omega⟩ = Fl.a v s := h1
        omega
      · rw [if_neg (fun h' => ha h'.2)]
        by_cases hl : a = G.P.m + 1
        · subst hl
          have : G.P.lam0 v s ⟨G.P.m + 1 - 1, by omega⟩ = -Fl.b v s := h2
          have := hb hs
          omega
        · have := (abs_le.1 (h3 ⟨a - 1, by omega⟩ (by show 0 < a - 1; omega) (by show a - 1 < G.P.m; omega))).2
          omega
    · rw [if_neg (fun h' => hs h'.1)]
      have := (abs_le.1 ((Fl.base v s).2 hs ⟨a - 1, by omega⟩)).2
      omega
  · rw [dite_eq_right h, if_neg (fun h' => h ⟨by omega, by omega⟩)]
    omega

end Fl

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem ne_kaJ_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ Formalism.MainNotions.G.kaJ D j := by
  unfold Formalism.MainNotions.G.kaJ
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have : 0 ≤ (2 * (j : ℝ) - 1) * ((D.R.t : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
  linarith

theorem ne_w''_nonneg : 0 ≤ L.sc.w'' D.R.n := by
  unfold Scale.w''
  exact div_nonneg L.sc.b'_pos.le (mul_nonneg L.sc.x_pos.le (Nat.cast_nonneg _))

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))


include hL ht0 in
theorem ne_w_non (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∉ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ L.sc.w'' D.R.n + L.etaSz := by
  obtain ⟨_, h2, _, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∉ D.host.TT := fun h => hs (h2.2 h)
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_neg (fun h => hn h.2)]
  have h5 := (X.off_thin j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))
    ⟨fun h => hn h.2, fun h => by simpa using h.1⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith


include hL ht0 in
theorem ne_w_top (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) + L.sc.b' / L.sc.x + L.etaSz := by
  obtain ⟨_, h2, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [h4 j hj, (h3 hs).2]
  have hn : t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ∈ D.host.TT := h2.1 hs
  unfold Formalism.MainNotions.G.fillG Formalism.MainNotions.G.fill
  rw [if_pos ⟨rfl, hn⟩]
  have h5 := (X.off_top j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) ⟨rfl, hn⟩).2
  have h6 := ne_kaJ_nonneg (D := D) j (Finset.mem_Icc.1 hj).1
  linarith

include hL ht0 in
theorem ne_nP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
  unfold Formalism.MainNotions.G.nP
  rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]

theorem ne_Nm (j : ℕ) (hj : j ∈ SizeData₂.lifts D) : (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 ≤ Formalism.MainNotions.G.Nm D := by
  unfold Formalism.MainNotions.G.Nm Ranks.N
  have h1 : (j : ℝ) ≤ D.R.m := by exact_mod_cast (Finset.mem_Icc.1 hj).2
  have h2 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have h3 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  push_cast
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1),
    mul_nonneg h4 (by linarith : (0 : ℝ) ≤ (D.R.t : ℝ) + 1)]

end Orbit


open Classical in
theorem price_bound_large_primes : PriceBoundLargePrimes 1 := by
  intro D L X Y K hK _ hT hL u w hg hp t0 ht0 j hj
  have hr : (D.gat u w hg).P.r = 1 := by rw [(hL u w hg).2.2.2.1, if_neg (not_lt.2 hp)]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hA : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L := by
    have := ne_w''_nonneg (L := L)
    have := L.etaSz_pos
    have := nc_cG_nonneg (L := L)
    linarith
  rw [hr]
  have h1 := price_sum_single_edge (Y.Fl u w hg).t j ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L)
    (fun s => ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) hA
    (fun s _ => by
      have e : (D.gat u w hg).P.m + 2 - 1 = (D.gat u w hg).P.m + 1 := rfl
      rw [e, Finset.Icc_self, Finset.sum_singleton, ne_lamI_last]
      split_ifs with hs
      · rw [((Y.Fl u w hg).base (Y.vOf u w hg t0) s).1 hs |>.2.1]
        push_cast
        linarith
      · have h2 := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h3 := (abs_le.1 (((Y.Fl u w hg).base (Y.vOf u w hg t0) s).2 hs (Fin.last _))).2
        have h4 : (((D.gat u w hg).P.lam0 (Y.vOf u w hg t0) s (Fin.last _) : ℤ) : ℝ) ≤ ((Y.Fl u w hg).c : ℝ) := by
          exact_mod_cast h3
        push_cast
        linarith)
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr
  rw [if_pos hp, nc_topsOn X Y hT hL u w hg t0 ht0, Finset.filter_image, Finset.sum_image (fun a _ b _ h => hinj h)]
  have hf : ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter
      (fun a => ¬ Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 a)) =
      ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos := by
    apply Finset.filter_congr
    intro s _
    rw [nc_isV X Y hT hL u w hg t0 ht0 s, not_not]
  rw [hf, ne_nP X Y hT hL u w hg t0 ht0, ht]
  have e1 : ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
      (((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) - ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ)) =
      ∑ s ∈ ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).filter IsOddPos,
        (Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, nc_iota Y u w hg t0 s) -
          (Formalism.MainNotions.G.bL L (nc_iota Y u w hg t0 s) : ℝ)) := by
    apply Finset.sum_congr rfl
    intro s hs
    obtain ⟨_, _, h3, h4⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
    rw [h4 j hj, (h3 (Finset.mem_filter.1 hs).1).2]
  rw [e1]
  have hN := ne_Nm (D := D) j hj
  have hn : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := Nat.cast_nonneg _
  have hNm : 0 ≤ Formalism.MainNotions.G.Nm D := le_trans (by positivity) hN
  have h5 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) ≤
      K.Pr1 * ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) *
        (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D) := by
    have := mul_le_mul_of_nonneg_right hK
      (mul_nonneg hn (by linarith : 0 ≤ L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L + Formalism.MainNotions.G.Nm D))
    linarith
  have h6 : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * ((1 : ℕ) : ℝ) * j * ((D.R.t : ℝ) + 1) / 2 ≤
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * Formalism.MainNotions.G.Nm D := by
    have := mul_le_mul_of_nonneg_left hN hn
    push_cast
    linarith
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThPosSubPosAdd
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lamF altF)

section CgCalc

variable {ι K : Type} [Field K] (R : Subring K) (pp : K)

def Cg (f g : MvPowerSeries ι K) : Prop := ∃ Y : MvPowerSeries ι K, IntR R Y ∧ f = g + MvPowerSeries.C pp * Y

variable {R pp}

theorem cg_refl (f : MvPowerSeries ι K) : Cg R pp f f := ⟨0, IntR_zero, by simp⟩

theorem cg_of_eq {f g : MvPowerSeries ι K} (h : f = g) : Cg R pp f g := h ▸ cg_refl f

theorem cg_trans {f g k : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp g k) : Cg R pp f k := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_add {f g f' g' : MvPowerSeries ι K} (h1 : Cg R pp f g) (h2 : Cg R pp f' g') :
    Cg R pp (f + f') (g + g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  exact ⟨Y + Y', IntR_add hY hY', by rw [e, e']; ring⟩

theorem cg_sum {α : Type} (s : Finset α) (F G : α → MvPowerSeries ι K) (h : ∀ a ∈ s, Cg R pp (F a) (G a)) :
    Cg R pp (∑ a ∈ s, F a) (∑ a ∈ s, G a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact cg_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact cg_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

theorem cg_mul {f g f' g' : MvPowerSeries ι K} (hf' : IntR R f') (hg : IntR R g) (h1 : Cg R pp f g)
    (h2 : Cg R pp f' g') : Cg R pp (f * f') (g * g') := by
  obtain ⟨Y, hY, e⟩ := h1
  obtain ⟨Y', hY', e'⟩ := h2
  refine ⟨g * Y' + Y * f', IntR_add (IntR_mul hg hY') (IntR_mul hY hf'), ?_⟩
  rw [e]
  conv_lhs => rw [add_mul, e']
  conv_rhs => rw [e']
  ring

theorem cg_pow {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) (h : Cg R pp f g) (k : ℕ) :
    Cg R pp (f ^ k) (g ^ k) := by
  induction k with
  | zero => exact cg_of_eq (by simp)
  | succ k ih => rw [pow_succ, pow_succ]; exact cg_mul hf (IntR_pow hg k) ih h

theorem cg_of_coeff {f g : MvPowerSeries ι K}
    (h : ∀ n, ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y) : Cg R pp f g := by
  choose y hy he using h
  let Y : MvPowerSeries ι K := fun n => y n
  have hYc : ∀ n, MvPowerSeries.coeff n Y = y n := fun _ => rfl
  refine ⟨Y, fun n => by rw [hYc]; exact hy n, ?_⟩
  ext n
  rw [map_add (f := _), MvPowerSeries.coeff_C_mul, he n, hYc]

theorem cg_coeff {f g : MvPowerSeries ι K} (h : Cg R pp f g) (n : ι →₀ ℕ) :
    ∃ y ∈ R, MvPowerSeries.coeff n f = MvPowerSeries.coeff n g + pp * y := by
  obtain ⟨Y, hY, e⟩ := h
  exact ⟨_, hY n, by rw [e, map_add (f := _), MvPowerSeries.coeff_C_mul]⟩

end CgCalc

section Pos

theorem th_posSub_posAdd {n' : ℕ} (s : Fin n') (d : ℕ) : posSub (posAdd s d) d = s := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := s.pos; omega⟩
  apply Fin.ext
  show ((s.val + d) % (m + 1) + (m + 1) * d - d) % (m + 1) = s.val
  have e : (s.val + d) % (m + 1) + (m + 1) * d - d = (s.val + d) % (m + 1) + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : s.val + d + m * d = s.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

theorem th_posAdd_posSub {n' : ℕ} (t : Fin n') (d : ℕ) : posAdd (posSub t d) d = t := by
  obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := ⟨n' - 1, by have := t.pos; omega⟩
  apply Fin.ext
  show ((t.val + (m + 1) * d - d) % (m + 1) + d) % (m + 1) = t.val
  have e : t.val + (m + 1) * d - d = t.val + m * d := by
    have : (m + 1) * d = m * d + d := by ring
    omega
  rw [e, Nat.mod_add_mod]
  have e2 : t.val + m * d + d = t.val + (m + 1) * d := by ring
  rw [e2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt t.isLt]

theorem th_odd_posAdd {n' : ℕ} (hev : Even n') (s : Fin n') (d : ℕ) :
    (posAdd s d).val % 2 = (s.val + d) % 2 := by
  show (s.val + d) % n' % 2 = _
  exact Nat.mod_mod_of_dvd _ hev.two_dvd

end Pos

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

