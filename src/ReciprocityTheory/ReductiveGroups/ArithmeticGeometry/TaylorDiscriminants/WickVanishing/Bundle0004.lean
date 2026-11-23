module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CcTMulQ
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.G2

variable {k : Type} [CommRing k] {d : ℕ}

section Q
variable {ι : Type} (c : ι → ι → k)

def ev2 : List ι → k
  | [x, y] => c x y
  | _ => 0

variable (F : Fin d → PS k 2 d) (u : ι → Fin d → k) (q : PS k 1 d)
  (hq0 : constantCoeff q = 0) (hq1 : ∀ l, constantCoeff (Dof F (u l) q) = 0)
  (hq2 : ∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l'))
include hq2

theorem T_q_long (w : List ι) (hw : 3 ≤ w.length) : T F u w q = 0 := by
  induction w with
  | nil => simp at hw
  | cons a w ih =>
    rw [T_cons]
    rcases w with _ | ⟨b, _ | ⟨e, _ | ⟨f, w⟩⟩⟩
    · simp at hw
    · simp at hw
    · rw [T_cons, T_cons]
      change Dof F (u a) (Dof F (u b) (Dof F (u e) q)) = 0
      rw [hq2, dof_C]
    · rw [ih (by simp)]
      exact dof_zero ..

include hq0 hq1

theorem cc_T_q (b : List ι) : constantCoeff (T F u b q) = ev2 c b := by
  rcases b with _ | ⟨x, _ | ⟨y, _ | ⟨z, b⟩⟩⟩
  · exact hq0
  · rw [T_cons]
    exact hq1 x
  · rw [T_cons, T_cons]
    change constantCoeff (Dof F (u x) (Dof F (u y) q)) = c x y
    rw [hq2, constantCoeff_C]
  · rw [T_q_long c F u q hq2 _ (by simp), map_zero]
    rfl

theorem cc_T_mul_q (w : List ι) (A : PS k 1 d) :
    constantCoeff (T F u w (A * q)) =
      ((splits w).map (fun p => constantCoeff (T F u p.1 A) * ev2 c p.2)).sum := by
  rw [T_mul, map_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp_apply, map_mul]
  rw [cc_T_q c F u q hq0 hq1 hq2]

end Q

end ReciprocityTheory.ChartRestriction.G.TB.G2
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Finsupp

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

section NabAux

variable {k : Type} [CommRing k] {d : ℕ}

theorem nt_ev_smul {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (r : k) (f : PS k m d) :
    ev a (r • f) = r • ev a f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
    | exact ⟨fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero, fun e => Set.toFinite _⟩
  unfold ev
  first
  | exact MvPowerSeries.subst_smul hs r f
  | (rw [← MvPowerSeries.coe_substAlgHom hs]; exact map_smul _ r f)

theorem nt_expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  have hdvd : (PowerSeries.X : PowerSeries k) ^ 1 ∣ PowerSeries.exp k - 1 := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    first
    | (simp [PowerSeries.coeff_exp]; done)
    | (simp only [map_sub, PowerSeries.coeff_exp, PowerSeries.coeff_one, if_true, Nat.factorial_zero,
        Nat.cast_one, div_one, map_one, sub_self]; done)
  obtain ⟨R, hR⟩ := hdvd
  have hexp : PowerSeries.exp k = 1 + PowerSeries.X ^ 1 * R := by
    rw [← hR]
    ring
  have hc : constantCoeff (0 : PS k n d) = 0 := map_zero _
  have hs : PowerSeries.HasSubst (0 : PS k n d) := by
    first
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero' hc
    | (show IsNilpotent _; rw [hc]; exact IsNilpotent.zero)
  have key : ∀ f : PowerSeries k, PowerSeries.subst (0 : PS k n d) f = PowerSeries.substAlgHom hs f := by
    intro f
    first
    | rw [PowerSeries.coe_substAlgHom]
    | rfl
  have hX : PowerSeries.substAlgHom hs (PowerSeries.X : PowerSeries k) = 0 := by
    first
    | exact PowerSeries.substAlgHom_X hs
    | (rw [← key]; exact PowerSeries.subst_X hs)
  unfold FB.expS
  rw [hexp, key]
  simp [hX]

theorem nt_const_smul {n : ℕ} (r : k) (f : PS k n d) : constantCoeff (r • f) = r * constantCoeff f := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_C]

end NabAux

theorem connection_translation_of_poly (hTP : TransPolySt) : NabTransSt := by
  intro k _ _ d O _ _ B B' φ φi lam hinv hl0 hl1 hF0 hF hA h hh w0 m f ι _ u P
  have hφ : GP φ := hinv.1
  have hp : ∀ {n : ℕ} (j : Fin n), GP (pt k (n := n) d j) := fun j => gp_pt j
  have hcφ : ∀ {n : ℕ} (a : Pt k n d), GP a → GP (comp1 φ a) := fun a ha => gp_comp1 φ a hφ ha
  have hBF : ∀ i, constantCoeff (B.G.F i) = 0 := B.G.const
  have fk : B.FK k = B.G.F := funext fun i => gt_map_id _
  have fk' : B'.FK k = transF B.G.F φ φi := funext fun i => (gt_map_id _).trans (hF i)
  have ak : ∀ a, B.actK k a = B.A.act a := fun a => funext fun i => gt_map_id _
  have ak' : ∀ a, B'.actK k a = B'.A.act a := fun a => funext fun i => gt_map_id _
  have hz0 : ∀ {n : ℕ}, GP (0 : Pt k n d) := gp_zero₂
  have hh0 : constantCoeff h = 0 := by
    have := congrArg constantCoeff hh
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hlam0 : constantCoeff lam = 0 := by
    have := congrArg constantCoeff hl0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant hz0 (hp 0)), map_zero] at this
  have hΦ2 : ∀ j, GP (![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] j) :=
    pair_points_zero_constant (hcφ _ (hp 0)) (hcφ _ (hp 1))
  have hBa : GP (B.A.act w0) := B.A.const w0
  have hB'a : GP (B'.A.act w0) := B'.A.const w0
  have hx' := gp_comp1 _ _ hB'a (hp (n := 1) 0)
  have hx := gp_comp1 _ _ hBa (hp (n := 1) 0)

  have Ha : comp1 φ (comp1 (B'.A.act w0) (pt k (n := 1) d 0)) = comp1 (B.A.act w0) φ := by
    rw [hA w0, gt_comp1_comp1 φi _ (gp_comp1 _ φ hBa hφ) _ (hp 0),
      gt_comp1_comp1 (B.A.act w0) φ hφ _ (hp 0), gt_comp_inv hinv _ (gp_comp1 _ _ hBa (hcφ _ (hp 0))),
      gt_comp1_pt_right]

  have hL : B'.hL k (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) w0 =
      ev ![φ] (B.hL k h w0) + ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam := by
    unfold FB.hL
    rw [ak', ak, gt_ev_add _ (pair_points_zero_constant (hp 0) hx'), gt_ev_ev' _ _ (pair_points_zero_constant (hp 0) hx') hΦ2, eval_pair_points,
      evP_comp1 _ (pair_points_zero_constant (hp 0) hx') φ _ (hp 0), evP_comp1 _ (pair_points_zero_constant (hp 0) hx') φ _ (hp 1),
      evP_pt _ (pair_points_zero_constant (hp 0) hx'), evP_pt _ (pair_points_zero_constant (hp 0) hx'),
      gt_ev_ev' _ _ (single_point_zero_constant hφ) (pair_points_zero_constant (hp 0) hx), eval_pair_points, evP_comp1 _ (single_point_zero_constant hφ) _ _ (hp 0),
      evP_pt _ (single_point_zero_constant hφ)]
    congr 2
    change ![comp1 φ (pt k (n := 1) d 0), comp1 φ (comp1 (B'.A.act w0) (pt k (n := 1) d 0))] =
      ![φ, comp1 (B.A.act w0) φ]
    rw [gt_comp1_pt_right, Ha]
  have cL : constantCoeff (ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam) = 0 :=
    gt_const_ev _ (pair_points_zero_constant (hp 0) hx') lam hlam0
  have chL : constantCoeff (B.hL k h w0) = 0 := by
    unfold FB.hL
    rw [ak]
    exact gt_const_ev _ (pair_points_zero_constant (hp 0) hx) h hh0

  have hG : ev ![φ] f * FB.expS k (-((m : k) •
        ev ![pt k (n := 1) d 0, comp1 (B'.actK k w0) (pt k (n := 1) d 0)] lam)) *
      FB.expS k ((m : k) • B'.hL k (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam) w0) =
      ev ![φ] (f * FB.expS k ((m : k) • B.hL k h w0)) := by
    rw [hL, ak', smul_add, gt_expS_add _ _ (by rw [nt_const_smul, gt_const_ev _ (single_point_zero_constant hφ) _ chL, mul_zero])
      (by rw [nt_const_smul, cL, mul_zero]), gt_ev_mul _ (single_point_zero_constant hφ),
      gt_ev_expS _ (single_point_zero_constant hφ) _ (by rw [nt_const_smul, chL, mul_zero]), nt_ev_smul _ (single_point_zero_constant hφ)]
    have e : FB.expS k (-((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam)) *
        FB.expS k ((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam) = 1 := by
      rw [← gt_expS_add _ _ (by rw [map_neg, nt_const_smul, cL, mul_zero, neg_zero]) (by rw [nt_const_smul, cL, mul_zero]),
        neg_add_cancel, nt_expS_zero]
    calc _ = ev ![φ] f * FB.expS k ((m : k) • ev ![φ] (B.hL k h w0)) *
          (FB.expS k (-((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam)) *
            FB.expS k ((m : k) • ev ![pt k (n := 1) d 0, comp1 (B'.A.act w0) (pt k (n := 1) d 0)] lam)) := by ring
      _ = _ := by rw [e, mul_one]
  unfold FB.nabVal
  rw [hG, fk', hTP k d B.G.F hBF (by intro i; rw [← fk]; exact hF0 i) φ φi hinv ι u P, fk,
    gt_const_ev_eq _ (single_point_zero_constant hφ)]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SecondColumnDegree
section
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree

variable {k : Type} [CommRing k]

section General

variable {σ : Type} [Fintype σ]

theorem so_def (c : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k c P = ∑ l, ∑ l', C (c l l') * pderiv l (pderiv l' P) := rfl

theorem so_zero (c : σ → σ → k) : secondOrder k c (0 : MvPolynomial σ k) = 0 := by
  simp [so_def]

theorem so_add (c : σ → σ → k) (P Q : MvPolynomial σ k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by
  simp only [so_def, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem so_smul (c : σ → σ → k) (r : k) (P : MvPolynomial σ k) :
    secondOrder k c (r • P) = r • secondOrder k c P := by
  first
  | (simp only [so_def, MvPolynomial.smul_eq_C_mul, Finset.mul_sum, Derivation.leibniz, smul_eq_mul,
      pderiv_C, mul_zero, add_zero]
     refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
     ring)
  | simp [so_def, Finset.smul_sum, mul_smul_comm]

private theorem mvPolynomial_pderiv_comm (a b : σ) (P : MvPolynomial σ k) :
    pderiv a (pderiv b P) = pderiv b (pderiv a P) := by
  classical
  induction P using MvPolynomial.induction_on
  · simp
  · simp [*]
  · rename_i p m hp
    simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), hp, pderiv_X]
    by_cases ha : a = m <;> by_cases hb : b = m <;> simp [Pi.single_apply, ha, hb] <;> ring

theorem pd4 (P : MvPolynomial σ k) (a b c d : σ) :
    pderiv a (pderiv b (pderiv c (pderiv d P))) = pderiv c (pderiv d (pderiv a (pderiv b P))) := by
  rw [mvPolynomial_pderiv_comm b c, mvPolynomial_pderiv_comm a c, mvPolynomial_pderiv_comm b d, mvPolynomial_pderiv_comm a d]

private theorem sum4_lemma {M : Type} [AddCommMonoid M] (f : σ → σ → σ → σ → M) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem so_comm (c1 c2 : σ → σ → k) (P : MvPolynomial σ k) :
    secondOrder k c1 (secondOrder k c2 P) = secondOrder k c2 (secondOrder k c1 P) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [so_def, map_sum, Finset.mul_sum, Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero,
    add_zero]
  rw [sum4_lemma]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun m' _ =>
    Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [pd4]
  ring

theorem totalDegree_pderiv_le (i : σ) (Q : MvPolynomial σ k) :
    (pderiv i Q).totalDegree ≤ Q.totalDegree - 1 := by
  classical
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [pderiv_monomial]
  by_cases h0 : s i = 0
  · simp [h0]
  · refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    have h1 := MvPolynomial.le_totalDegree hs
    have h2 : s = (s - Finsupp.single i 1) + Finsupp.single i 1 :=
      (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h0))).symm
    have h3 : (s.sum fun _ e => e) = ((s - Finsupp.single i 1).sum fun _ e => e) + 1 := by
      conv_lhs => rw [h2]
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have h4 : ((s - Finsupp.single i 1).sum fun _ => id) = ((s - Finsupp.single i 1).sum fun _ e => e) := rfl
    have h5 : (s.sum fun _ => id) = (s.sum fun _ e => e) := rfl
    omega

theorem pderiv_eq_zero_of_deg (i : σ) (Q : MvPolynomial σ k) (h : Q.totalDegree = 0) : pderiv i Q = 0 := by
  first
  | (rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h; rw [h, pderiv_C])
  | (have h' := (MvPolynomial.totalDegree_eq_zero_iff_eq_C).1 h; rw [h', pderiv_C])

theorem totalDegree_so_le (c : σ → σ → k) (Q : MvPolynomial σ k) :
    (secondOrder k c Q).totalDegree ≤ Q.totalDegree - 2 := by
  rw [so_def]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l' _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  have h1 := totalDegree_pderiv_le l (pderiv l' Q)
  have h2 := totalDegree_pderiv_le l' Q
  omega

theorem so_eq_zero_of_le_one (c : σ → σ → k) (Q : MvPolynomial σ k) (h : Q.totalDegree ≤ 1) :
    secondOrder k c Q = 0 := by
  rw [so_def]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_
  have h1 := totalDegree_pderiv_le l' Q
  rw [pderiv_eq_zero_of_deg l (pderiv l' Q) (by omega), mul_zero]

theorem so_iter_eq_zero (c : σ → σ → k) :
    ∀ (i : ℕ) (Q : MvPolynomial σ k), Q.totalDegree < i → (secondOrder k c)^[i] Q = 0
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | i + 1, Q, h => by
    rw [Function.iterate_succ_apply]
    by_cases h1 : Q.totalDegree ≤ 1
    · rw [so_eq_zero_of_le_one c Q h1]
      exact Function.iterate_fixed (so_zero c) i
    · apply so_iter_eq_zero c i
      have hdeg : (secondOrder k c Q).totalDegree ≤ Q.totalDegree - 2 :=
        totalDegree_so_le c Q
      omega

theorem so_iter_deg_le (c : σ → σ → k) :
    ∀ (i : ℕ) (Q : MvPolynomial σ k), ((secondOrder k c)^[i] Q).totalDegree ≤ Q.totalDegree
  | 0, _ => le_rfl
  | i + 1, Q => by
    rw [Function.iterate_succ_apply]
    exact (so_iter_deg_le c i _).trans ((totalDegree_so_le c Q).trans (Nat.sub_le _ _))

end General

section Columns

variable {ι : Type} [Fintype ι] {n : ℕ}

abbrev colE (b : Fin n) : MvPolynomial ι k →ₐ[k] MvPolynomial (ι × Fin n) k := rename fun l => (l, b)

def cB (c : ι → ι → k) (b : Fin n) : ι × Fin n → ι × Fin n → k :=
  fun p q => if p.2 = b ∧ q.2 = b then c p.1 q.1 else 0

theorem pderiv_colE (b : Fin n) (l : ι) (Q : MvPolynomial ι k) :
    pderiv (l, b) (colE b Q) = colE b (pderiv l Q) := by
  classical
  first
  | exact pderiv_rename (f := fun l => (l, b)) (fun x y h => by simpa using h) l Q
  | simpa using pderiv_rename (f := fun l : ι => (l, b)) (fun x y h => by simpa using h) l Q

private theorem pderiv_colE_eq_zero_of_ne (a b : Fin n) (hab : a ≠ b) (l : ι) (P : MvPolynomial ι k) :
    pderiv (l, b) (colE a P) = 0 := by
  classical
  induction P using MvPolynomial.induction_on
  · simp
  · simp [*]
  · rename_i p m hp
    simp [hp, pderiv_X, Pi.single_apply, hab]

theorem pderiv_prod_colE (b : Fin n) (s : Finset (Fin n)) (hb : b ∉ s) (Q : Fin n → MvPolynomial ι k)
    (l : ι) : pderiv (l, b) (∏ b' ∈ s, colE b' (Q b')) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Derivation.leibniz, ih (fun h => hb (Finset.mem_insert_of_mem h)),
      pderiv_colE_eq_zero_of_ne a b (by rintro rfl; exact hb (Finset.mem_insert_self _ _)) l (Q a)]
    simp

theorem so_colB (c : ι → ι → k) (b : Fin n) (Q : MvPolynomial ι k) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    secondOrder k (cB c b) (colE b Q * R) = colE b (secondOrder k c Q) * R := by
  classical
  have hd : ∀ l l' : ι, pderiv (l, b) (pderiv (l', b) (colE b Q * R)) =
      colE b (pderiv l (pderiv l' Q)) * R := by
    intro l l'
    rw [Derivation.leibniz, hR, smul_zero, zero_add, smul_eq_mul, pderiv_colE,
      Derivation.leibniz, hR, smul_zero, add_zero, smul_eq_mul, pderiv_colE, mul_comm]
  have key : ∀ p q : ι × Fin n, C (cB c b p q) * pderiv p (pderiv q (colE b Q * R)) =
      if p.2 = b ∧ q.2 = b then C (c p.1 q.1) * (colE b (pderiv p.1 (pderiv q.1 Q)) * R) else 0 := by
    rintro ⟨l, y⟩ ⟨l', y'⟩
    simp only [cB]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [hd]
    · simp
  rw [so_def, so_def]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [key, map_sum, Finset.sum_mul, map_mul, MvPolynomial.rename_C]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single b]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [mul_assoc]
    · intro y _ hy
      simp [hy]
    · simp
  · intro y _ hy
    simp [hy]
  · simp

theorem so_colB_iter (c : ι → ι → k) (b : Fin n) (R : MvPolynomial (ι × Fin n) k)
    (hR : ∀ l : ι, pderiv (l, b) R = 0) :
    ∀ (i : ℕ) (Q : MvPolynomial ι k),
      (secondOrder k (cB c b))^[i] (colE b Q * R) = colE b ((secondOrder k c)^[i] Q) * R
  | 0, _ => rfl
  | i + 1, Q => by
    rw [Function.iterate_succ_apply, so_colB c b Q R hR, so_colB_iter c b R hR i,
      ← Function.iterate_succ_apply]

end Columns

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.SecondColumnDegree
end
end

