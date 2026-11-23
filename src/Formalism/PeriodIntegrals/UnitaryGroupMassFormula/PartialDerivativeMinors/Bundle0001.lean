module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.CardCellsEqSumRowLen
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD Formalism.BasicNotions Formalism.MainNotions.G

theorem card_cells_eq_sum_rowLen (α : YoungDiagram) (n : ℕ) (h : ∀ r, n ≤ r → α.rowLen r = 0) :
    α.cells.card = ∑ r ∈ Finset.range n, α.rowLen r := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := Finset.range n)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [YoungDiagram.rowLen_eq_card]
    first
      | rfl
      | (simp only [YoungDiagram.row]; congr 1)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_range] at hx ⊢
    by_contra hc
    have h0 := h x.1 (not_lt.mp hc)
    have hx' : (x.1, x.2) ∈ α := hx
    rw [YoungDiagram.mem_iff_lt_rowLen] at hx'
    omega

theorem cPr_le_ctD (D : D7) (u : D.what₂.Word) (i : ℕ) (nu : Pl D → YoungDiagram)
    (hrow : ∀ z r, (((nu z).rowLen r : ℕ) : ℝ) =
      if r < D.R.N i then DV.nuRow D u (i + 1) (tauPl D z) r else 0)
    (hN : 2 ≤ D.R.N i) (t : HH D) :
    (cPr (nu (false, t)) (nu (true, t)) : ℝ) ≤ ctD D u (i + 1) t := by
  have hN0 : 0 < D.R.N i := by omega
  have hN1 : 1 < D.R.N i := by omega

  have hr : ∀ z r, r < D.R.N i → DV.nuRow D u (i + 1) (tauPl D z) r = ((nu z).rowLen r : ℝ) := by
    intro z r hr'
    rw [hrow z r, if_pos hr']
  have hz : ∀ z r, D.R.N i ≤ r → (nu z).rowLen r = 0 := by
    intro z r hr'
    have hz0 := hrow z r
    rw [if_neg (by omega)] at hz0
    exact_mod_cast hz0
  have hsum := card_cells_eq_sum_rowLen (nu (false, t)) (D.R.N i) (hz _)
  have habs : nuAbs D u (i + 1) (tauPl D (false, t)) = ((nu (false, t)).cells.card : ℝ) := by
    rw [hsum]
    unfold nuAbs
    rw [Nat.add_sub_cancel]
    push_cast
    refine Finset.sum_congr rfl fun r hr' => ?_
    exact hr _ r (Finset.mem_range.mp hr')
  have h0le : (nu (false, t)).rowLen 0 ≤ (nu (false, t)).cells.card := by
    rw [hsum]
    exact Finset.single_le_sum (f := fun r => (nu (false, t)).rowLen r)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hN0)
  unfold cPr ctD
  rw [habs, hr (false, t) 0 hN0, hr (false, t) 1 hN1, hr (true, t) 0 hN0]
  push_cast [Nat.cast_sub h0le]
  have hm1 := min_le_left ((nu (false, t)).rowLen 0 : ℝ) ((nu (true, t)).rowLen 0 : ℝ)
  have hm2 := min_le_right ((nu (false, t)).rowLen 0 : ℝ) ((nu (true, t)).rowLen 0 : ℝ)
  have ha1 : (0 : ℝ) ≤ ((nu (false, t)).rowLen 1 : ℝ) := Nat.cast_nonneg _
  split_ifs <;> linarith

theorem entAtD_of_core (h : CoreBound) : PI.EntAtD.EntAtD := by
  unfold PI.EntAtD.EntAtD
  intro D Dx nu hrow hcol Th hTh u μ w hLF hram i hi L L'
  have hS := hTh u μ w hLF hram i hi L L'
  have hc := h (HH D) (D.R.N i) (D.R.N (i + 1)) (D.what₂.places.resChar w) (nu u i)
    (Th u μ w i L L') hS
  have hN : 2 ≤ D.R.N i := by
    show 2 ≤ D.R.k + i * (D.R.t + 1)
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    exact le_trans (by omega : 2 ≤ D.R.k) (Nat.le_add_right _ _)

  have hle : ∑ t : HH D, (cPr (nu u i (false, t)) (nu u i (true, t)) : ℝ) ≤
      ∑ t : HH D, ctD D u (i + 1) t :=
    Finset.sum_le_sum fun t _ => cPr_le_ctD D u i (nu u i) (hrow u i hi) hN t
  have hp : (1 : ℝ) ≤ (D.what₂.places.resChar w : ℝ) := by
    have hpr : (D.what₂.places.resChar w).Prime := Fact.out
    exact_mod_cast hpr.one_lt.le
  unfold KvalGe at hc ⊢
  intro I m
  refine (hc I m).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le hp
  linarith

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.CoreTermLe
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem coreTerm_le {H : Type} [Fintype H] (p : ℕ) [Fact p.Prime] (S : ℂ_[p]) (ut : H → ℂ_[p])
    (hS : ‖S‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2)) (hut : ∀ t, ‖ut t‖ ≤ 1) (X : ℂ_[p]) (hX : ‖X‖ ≤ 1) (A : ℤ)
    (n c : H → ℕ) (hn : ∀ t, n t ≤ c t) :
    ‖X * (∏ t : H, (-(S * ut t)) ^ n t) * ((A : ℤ) : ℂ_[p])‖ ≤
      (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  have hq0 : (0 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hp0.le _
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 2) := Real.one_le_rpow hp1 (by norm_num)
  have hA : ‖((A : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one ℂ_[p] A
  have h2 : ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) := by
    calc ∏ t : H, ‖(-(S * ut t)) ^ n t‖ ≤ ∏ t : H, ((p : ℝ) ^ ((1 : ℝ) / 2)) ^ c t := by
          apply Finset.prod_le_prod₀ (fun t _ => norm_nonneg _)
          intro t _
          rw [norm_pow, norm_neg, norm_mul]
          calc (‖S‖ * ‖ut t‖) ^ n t ≤ ((p : ℝ) ^ ((1 : ℝ) / 2)) ^ n t := by
                apply pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
                calc ‖S‖ * ‖ut t‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2) * 1 :=
                      mul_le_mul hS (hut t) (norm_nonneg _) hq0
                  _ = _ := mul_one _
            _ ≤ _ := pow_le_pow_right₀ hq1 (hn t)
      _ = _ := by
          rw [Finset.sum_div, Real.rpow_sum_of_pos hp0]
          refine Finset.prod_congr rfl (fun t _ => ?_)
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
          congr 1
          ring
  rw [norm_mul, norm_mul, norm_prod]
  calc ‖X‖ * (∏ t : H, ‖(-(S * ut t)) ^ n t‖) * ‖((A : ℤ) : ℂ_[p])‖
      ≤ 1 * (p : ℝ) ^ ((∑ t : H, (c t : ℝ)) / 2) * 1 := by
        apply mul_le_mul (mul_le_mul hX h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one)
          hA (norm_nonneg _)
        exact mul_nonneg zero_le_one (Real.rpow_nonneg hp0.le _)
    _ = _ := by ring

theorem core_of (hE : PExpand) (hV : PVanish) : CoreBound := by
  intro H _ _ N0 N1 p _ nu Th hTh I m
  obtain ⟨S, hS, ut, hut, sg, hsg, rfl⟩ := hTh
  rw [hE H N0 N1 p S ut sg (Gxz N0 N1 nu I) m, neg_neg]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hB0 : (0 : ℝ) ≤ (p : ℝ) ^ ((∑ t : H, (cPr (nu (false, t)) (nu (true, t)) : ℝ)) / 2) :=
    Real.rpow_nonneg hp0.le _
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun κ2 _ => ?_)
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 (fun n _ => ?_)
  by_cases hn : ∃ t, cPr (nu (false, t)) (nu (true, t)) < n t
  · obtain ⟨t, ht⟩ := hn
    rw [hV H N0 N1 nu I m κ2 n t ht]
    simpa using hB0
  · simp only [not_exists, not_lt] at hn
    exact coreTerm_le p S ut hS hut _ (hsg κ2) _ n (fun t => cPr (nu (false, t)) (nu (true, t))) hn

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.ExpCoeff
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

namespace ExponentialCoefficients

variable {H : Type} [Fintype H] [DecidableEq H] {N0 N1 : ℕ}

abbrev JI (H : Type) (N0 N1 : ℕ) : Type := H × Fin N0 × Fin N1

def vX (s : Bool) (j : JI H N0 N1) : ZV H N0 N1 := ((s, j.1), j.2.1, j.2.2)

def eJ (j : JI H N0 N1) : ZV H N0 N1 →₀ ℕ :=
  Finsupp.single (vX false j) 1 + Finsupp.single (vX true j) 1

def eK (k : JI H N0 N1 → ℕ) : ZV H N0 N1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => k (v.1.2, v.2))

theorem eK_apply (k : JI H N0 N1 → ℕ) (s : Bool) (t : H) (a : Fin N0) (b : Fin N1) :
    eK k ((s, t), a, b) = k (t, a, b) := by
  first
  | rfl
  | simp [eK]

theorem sum_eJ (k : JI H N0 N1 → ℕ) : ∑ j, k j • eJ j = eK k := by
  ext ⟨⟨s, t⟩, a, b⟩
  rw [eK_apply, Finsupp.finsetSum_apply, Finset.sum_eq_single (t, a, b)]
  · cases s <;> simp [eJ, vX, Finsupp.single_apply]
  · rintro ⟨t', a', b'⟩ _ hne
    simp only [eJ, vX, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eK_eq_iff (k : JI H N0 N1 → ℕ) (κ : ZV H N0 N1 →₀ ℕ) :
    κ = eK k ↔ (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧ k = fun j => κ (vX true j) := by
  constructor
  · rintro rfl
    refine ⟨fun t a b => by rw [eK_apply, eK_apply], ?_⟩
    funext ⟨t, a, b⟩
    exact (eK_apply k true t a b).symm
  · rintro ⟨h1, rfl⟩
    ext ⟨⟨s, t⟩, a, b⟩
    rw [eK_apply]
    cases s
    · exact h1 t a b
    · rfl

theorem prod_monomial' {σ ι R : Type*} [CommSemiring R] (s : Finset ι) (f : ι → σ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, MvPowerSeries.monomial (f i) (a i) =
      MvPowerSeries.monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [MvPowerSeries.monomial_zero_one]
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPowerSeries.monomial_mul_monomial]

variable (p : ℕ) [Fact p.Prime]

theorem f_eq (S : ℂ_[p]) (ut : H → ℂ_[p]) :
    (-(S • ∑ t : H, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (ZV H N0 N1) ℂ_[p]))) =
      ∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1)) := by
  have key : ∀ (c : ℂ_[p]) (n : ZV H N0 N1 →₀ ℕ),
      c • (MvPowerSeries.monomial n (1 : ℂ_[p])) = MvPowerSeries.monomial n c := by
    intro c n
    rw [← map_smul, smul_eq_mul, mul_one]
  simp only [Finset.smul_sum, ← Finset.sum_neg_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, mul_one, smul_smul,
    ← neg_smul, key]
  rfl

theorem cc_zero (S : ℂ_[p]) (ut : H → ℂ_[p]) :
    MvPowerSeries.constantCoeff
      (∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1))) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_monomial, if_neg]
  intro h
  have h2 := DFunLike.congr_fun h (vX false j)
  simp [eJ, vX, Finsupp.single_apply] at h2

private theorem monomial_pow_lemma {σ R : Type*} [CommSemiring R] (n : σ →₀ ℕ) (a : R) (k : ℕ) :
    MvPowerSeries.monomial n a ^ k = MvPowerSeries.monomial (k • n) (a ^ k) := by
  induction k with
  | zero => simp [MvPowerSeries.monomial_zero_one]
  | succ k ih => rw [pow_succ, ih, MvPowerSeries.monomial_mul_monomial, succ_nsmul, pow_succ]

theorem coeff_pow (S : ℂ_[p]) (ut : H → ℂ_[p]) (κ : ZV H N0 N1 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff κ ((∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1))) ^ d) =
      if (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧ ∑ j, κ (vX true j) = d then
        ((Nat.multinomial Finset.univ fun j => κ (vX true j) : ℕ) : ℂ_[p]) *
          ∏ j, (-(S * ut j.1)) ^ κ (vX true j)
      else 0 := by
  classical
  have hn : ∀ (n : ℕ) (m : ZV H N0 N1 →₀ ℕ) (c : ℂ_[p]),
      (n : MvPowerSeries (ZV H N0 N1) ℂ_[p]) * MvPowerSeries.monomial m c =
        MvPowerSeries.monomial m ((n : ℂ_[p]) * c) := by
    intro n m c
    rw [← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
  have hterm : ∀ k : JI H N0 N1 → ℕ,
      (Nat.multinomial Finset.univ k : MvPowerSeries (ZV H N0 N1) ℂ_[p]) *
          ∏ j, MvPowerSeries.monomial (eJ j) (-(S * ut j.1)) ^ k j =
        MvPowerSeries.monomial (eK k)
          ((Nat.multinomial Finset.univ k : ℂ_[p]) * ∏ j, (-(S * ut j.1)) ^ k j) := by
    intro k
    simp only [monomial_pow_lemma]
    rw [prod_monomial', sum_eJ, hn]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
  simp only [hterm, MvPowerSeries.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single (fun j => κ (vX true j))]
    · rw [if_pos ((eK_eq_iff _ _).2 ⟨h.1, rfl⟩)]
    · intro k _ hk
      rw [if_neg]
      intro he
      exact hk ((eK_eq_iff k κ).1 he).2
    · intro hn'
      exfalso
      apply hn'
      rw [Finset.mem_piAntidiag]
      exact ⟨h.2, fun i _ => Finset.mem_univ i⟩
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg]
    intro he
    apply h
    obtain ⟨h1, h2⟩ := (eK_eq_iff k κ).1 he
    refine ⟨h1, ?_⟩
    rw [Finset.mem_piAntidiag] at hk
    subst h2
    exact hk.1

end ExponentialCoefficients

theorem pExpCoeff : PExpCoeff := by
  intro H _ _ N0 N1 p _ S ut κ
  have hs : PowerSeries.HasSubst (∑ j : ExponentialCoefficients.JI H N0 N1,
      MvPowerSeries.monomial (ExponentialCoefficients.eJ j) (-(S * ut j.1))) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (ExponentialCoefficients.cc_zero p S ut)
  rw [expS, ExponentialCoefficients.f_eq, PowerSeries.coeff_subst hs]
  simp only [ExponentialCoefficients.coeff_pow, PowerSeries.coeff_exp, smul_eq_mul]
  split_ifs with hbal
  · rw [finsum_eq_single _ (∑ j, κ (ExponentialCoefficients.vX true j)) ?_]
    · rw [if_pos ⟨hbal, rfl⟩]
      have hκ : (κ.prod fun _ k => (k.factorial : ℂ_[p])) =
          ∏ j : ExponentialCoefficients.JI H N0 N1, ((κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) ^ 2 := by
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
        let e : (Bool × ExponentialCoefficients.JI H N0 N1) ≃ ZV H N0 N1 :=
          { toFun := fun x => ExponentialCoefficients.vX x.1 x.2
            invFun := fun v => (v.1.1, v.1.2, v.2)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← e.prod_comp, Fintype.prod_prod_type, Fintype.prod_bool, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        obtain ⟨t, a, b⟩ := j
        simp only [e, Equiv.coe_fn_mk, ExponentialCoefficients.vX]
        rw [← hbal t a b, sq]
      have hR : (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)) =
          ∏ j : ExponentialCoefficients.JI H N0 N1, ((κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) *
            (-(S * ut j.1)) ^ κ (ExponentialCoefficients.vX true j) := by
        simp only [Fintype.prod_prod_type] <;> rfl
      have hM := congrArg (Nat.cast (R := ℂ_[p]))
        (Nat.multinomial_spec Finset.univ (fun j => κ (ExponentialCoefficients.vX true j)))
      push_cast at hM
      have hD : ((∑ j, κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [hκ, hR, Finset.prod_mul_distrib, Finset.prod_pow, map_div₀, map_one, map_natCast]
      rw [← hM] at hD ⊢
      have hMne := right_ne_zero_of_mul hD
      field_simp
    · intro d hd
      rw [if_neg, mul_zero]
      rintro ⟨_, h⟩
      exact hd h.symm
  · rw [finsum_eq_zero_of_forall_eq_zero, mul_zero]
    intro d
    rw [if_neg, mul_zero]
    rintro ⟨h, _⟩
    exact hbal h

end PI.EntAtD.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.HeartPderivMinor
section
noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

section Ker

variable {A : Type} [CommRing A] (D : Derivation ℤ A A)

end Ker

private theorem derivation_prod_eq_zero_of_forall' {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (s : Finset ι) (f : ι → A) (h : ∀ i ∈ s, D (f i) = 0) :
    D (∏ i ∈ s, f i) = 0 := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Derivation.leibniz, h i (Finset.mem_insert_self i s),
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj)), smul_zero, smul_zero, add_zero]

private theorem derivation_det_eq_zero_of_entries {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (h : ∀ i j, D (M i j) = 0) :
    D M.det = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.det_apply, map_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivation_prod_eq_zero_of_forall' D _ _ (fun i _ => h _ _), smul_zero]

theorem heart_pderiv_minor {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N0 N1 : ℕ) (s s' : Lt) (hs : s ≠ s')
    (k : ℕ) (I : Fin k ↪o Fin N1) (a : Fin N0) (b : Fin N1) :
    MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) (minorXZ N0 N1 s k I) = 0 := by
  simp only [minorXZ]
  apply derivation_det_eq_zero_of_entries
  intro i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.of_apply, map_sum]
  refine Finset.sum_eq_zero fun a0 _ => ?_
  rw [Derivation.leibniz, MvPolynomial.pderiv_X, MvPolynomial.pderiv_X]
  simp [Pi.single_apply, hs, Ne.symm hs]

private theorem derivation_finset_sum_apply' {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    (s : Finset ι) (D : ι → Derivation R A A) (x : A) : (∑ i ∈ s, D i) x = ∑ i ∈ s, D i x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Derivation.add_apply, ih]

theorem heart_dRow_zero {H : Type} {N0 N1 : ℕ} (t : H) (r : ℕ) (b : Fin N1) (f : PolyXZ H N0 N1)
    (h : ∀ a : Fin N0, MvPolynomial.pderiv (R := ℤ) (Sum.inr ((true, t), a, b)) f = 0) :
    dRow (N0 := N0) t r b f = 0 := by
  simp only [dRow]
  rw [derivation_finset_sum_apply']
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [Derivation.smul_apply, h a, smul_zero]

theorem heart_sdeg_prod (hS : PSDegMul) {A : Type} [CommRing A] {ι : Type} (d : ι → Derivation ℤ A A)
    {κ : Type} [DecidableEq κ] (s : Finset κ) (f : κ → A) (k : κ → ℕ) :
    (∀ i ∈ s, SDegD d (k i) (f i)) → SDegD d (∑ i ∈ s, k i) (∏ i ∈ s, f i) := by
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.prod_empty]
    intro j
    exact (d j).map_one_eq_zero
  · intro i s hi ih h
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact hS A ι d _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lapZero_of (hM : PMinorAff) (hS : PSDegMul) (hF : PLapForms) : PLapZero := by
  intro H _ inst N0 N1 nu I t n hn
  clear inst
  let P : Bool × H → PolyXZ H N0 N1 := fun s => ∏ c : Fin ((nu s).rowLen 0),
    minorXZ (Lt := Bool × H) N0 N1 s ((nu s).colLen c) (I s c)
  let R : PolyXZ H N0 N1 := ∏ s ∈ (Finset.univ.erase (false, t)).erase (true, t), P s
  have hne : (true, t) ≠ (false, t) := by simp
  have hmem : (true, t) ∈ Finset.univ.erase (false, t) := by simp
  have hG : Gxz N0 N1 nu I = P (false, t) * (P (true, t) * R) := by
    show (∏ s, P s) = _
    rw [← Finset.mul_prod_erase Finset.univ P (Finset.mem_univ (false, t)),
      ← Finset.mul_prod_erase (Finset.univ.erase (false, t)) P hmem]
  have hnoP : ∀ (s s' : Bool × H), s ≠ s' → ∀ (a : Fin N0) (b : Fin N1),
      MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) (P s) = 0 := by
    intro s s' hs a b
    apply derivation_prod_eq_zero_of_forall'
    intro c _
    convert heart_pderiv_minor N0 N1 s s' hs _ (I s c) a b
  have hnoR : ∀ (s' : Bool × H), s' = (false, t) ∨ s' = (true, t) → ∀ (a : Fin N0) (b : Fin N1),
      MvPolynomial.pderiv (R := ℤ) (Sum.inr (s', a, b)) R = 0 := by
    intro s' hs' a b
    apply derivation_prod_eq_zero_of_forall'
    intro s hs
    apply hnoP s s' _ a b
    rintro rfl
    rcases hs' with rfl | rfl
    · exact Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hs) rfl
    · exact Finset.ne_of_mem_erase hs rfl
  have h1 : ∀ (a : Fin N0) (b : Fin N1), pd (Sum.inr ((false, t), a, b)) (P (true, t) * R) = 0 := by
    intro a b
    show MvPolynomial.pderiv (R := ℤ) (Sum.inr ((false, t), a, b)) (P (true, t) * R) = 0
    rw [Derivation.leibniz, hnoP (true, t) (false, t) hne a b, hnoR (false, t) (Or.inl rfl) a b,
      smul_zero, smul_zero, add_zero]
  have hR0 : SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) 0 R := by
    intro b
    exact heart_dRow_zero t 0 b R (fun a => hnoR (true, t) (Or.inr rfl) a b)
  have hmin : ∀ c : Fin ((nu (true, t)).rowLen 0), SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) 1
      (minorXZ (Lt := Bool × H) N0 N1 (true, t) ((nu (true, t)).colLen c) (I (true, t) c)) := by
    intro c j j'
    exact hM H N0 N1 t _ _ j' j
  have hPT0 := heart_sdeg_prod hS (fun b : Fin N1 => dRow (N0 := N0) t 0 b) Finset.univ _ (fun _ => 1)
    (fun c _ => hmin c)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hPT0
  have hPT : SDegD (fun b : Fin N1 => dRow (N0 := N0) t 0 b) ((nu (true, t)).rowLen 0) (P (true, t)) :=
    hPT0
  have h2 := hS _ _ _ _ _ _ 0 hPT hR0
  rw [hG]
  exact hF H N0 N1 (nu (false, t)) (I (false, t)) t (P (true, t) * R) ((nu (true, t)).rowLen 0) n h1 h2 hn

end PI.EntAtD.W
end
end

