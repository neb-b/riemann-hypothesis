module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.Development
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.AddPreservesExpCongruence
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.HasseOrdBdW

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem kp_charZero (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : CharZero (Kp X la N) := by
  have := Kl_charZero X la
  exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

theorem isUnif_unifO (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (hfd : FiniteDimensional (Kp X la G.N) (OsK X la G.w)) :
    IsUnif (OsK X la G.w) (unifO X la G.N) := by
  have : Algebra.IsIntegral (Kp X la G.N) (OsK X la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp X la G.N)
    (Op.irreducible_map X la G.N (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))))

theorem isDVRAt_pt (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (hP : PublishedIntClos)
    (hfd : FiniteDimensional (Kp X la G.N) (OsK X la G.w)) (hred : IsReduced (OsK X la G.w))
    (ζ : PtsG G la) : IsDVRAt ζ := by
  have := kp_charZero (X := X) la G.N
  exact (hP (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).2 ζ

theorem addPreservesExpCongruence : S3 := by
  intro D B P j X ka wL wF G la Q hP hC ζ
  obtain ⟨hfd, hred, hgen⟩ := hC
  have hU := isUnif_unifO G la hfd
  have := isDVRAt_pt G la hP hfd hred ζ
  refine ⟨ordV_zero Q.c ζ hU hgen, fun m v => ?_⟩
  show ordV (unifO X la G.N) ζ Q.e Q.c v ≤ ordV (unifO X la G.N) ζ Q.e Q.c (m • v)
  rw [← Int.cast_smul_eq_zsmul (OsK X la G.w) m v, ordV_smul Q.c ζ hU hgen]
  exact le_add_of_nonneg_left (ord_nonneg ζ hU (intCast_mem _ m))

theorem expCongruenceExtendsToSum : S4 := by
  intro e vf vg d T n hvf h
  refine mul_le_mul_of_nonneg_left ?_ (by exact_mod_cast Nat.zero_le e)
  have e1 : (T : EReal) * (d : EReal) = ((T * d : ℝ) : EReal) := by rw [EReal.coe_mul]; rfl
  have e2 : ((T + n : ℕ) : EReal) * (d : EReal) = ((((T + n : ℕ) : ℝ) * d : ℝ) : EReal) := by
    rw [EReal.coe_mul]; rfl
  rw [e1, e2]
  induction vf using EReal.rec with
  | bot => exact absurd rfl hvf
  | top =>
    have hg : vg = ⊤ := by
      rw [EReal.top_add_coe] at h
      exact top_le_iff.mp h
    rw [hg, EReal.top_sub_coe, EReal.top_sub_coe]
  | coe a =>
    induction vg using EReal.rec with
    | bot =>
      rw [← EReal.coe_add] at h
      exact absurd (le_bot_iff.mp h) (EReal.coe_ne_bot _)
    | top =>
      rw [EReal.top_sub_coe]
      exact le_top
    | coe b =>
      have h' : a + n * d ≤ b := by
        rw [← EReal.coe_add] at h
        exact EReal.coe_le_coe_iff.mp h
      rw [← EReal.coe_sub, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      push_cast
      nlinarith

end PI.HasseOrdBdW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.CompositionalInverseSymm
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps MvPowerSeries

namespace PI.HasseOrdBdW

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def s0 : Lc X la w := algebraMap (Rp X la N) (Lc X la w) (sec X la w 0)

theorem section_mul_inverse : s0 X la w * wi X la w = 1 := section_mul_inverse_eq_one X la w

theorem hasse_apply (β : Idx D j N →₀ ℕ) (x : Lc X la w) :
    hasse X la w β x = MvPowerSeries.coeff β (tayLc X la w x) := rfl

def cS (p : Idx D j N) : Lc X la w := hasse X la w (Finsupp.single p 1) (s0 X la w)

theorem cS_eq (p : Idx D j N) : cS X la w p =
    if p.1 = 0 then algebraMap (Rp X la N) (Lc X la w) (emb X la N (X.inc wL (w p.2))) else 0 := by
  unfold cS s0
  rw [hasse_algebraMap, hasseRp_single, pdRp_sec]
  by_cases h : p.1 = 0 <;> simp [h]

theorem taySec : tayLc X la w (s0 X la w) =
    MvPowerSeries.C (s0 X la w) +
      (Finsupp.equivFunOnFinite.symm (cS X la w)).sum (fun p a => MvPowerSeries.C a * MvPowerSeries.X p) := by
  classical
  ext γ
  rw [Finsupp.sum_fintype _ _ (by intro p; simp)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, Finsupp.coe_equivFunOnFinite_symm, MvPowerSeries.coeff_C_mul,
    MvPowerSeries.coeff_X, MvPowerSeries.coeff_C]
  rw [← hasse_apply]
  have hne : ∀ p : Idx D j N, (0 : Idx D j N →₀ ℕ) ≠ Finsupp.single p 1 := fun p h => by
    simpa using h.symm
  by_cases h0 : γ = 0
  · subst h0
    rw [hasse_zero]
    simp [hne]
  · by_cases h1 : ∃ q, γ = Finsupp.single q 1
    · obtain ⟨q, rfl⟩ := h1
      have hq : hasse X la w (Finsupp.single q 1) (s0 X la w) = cS X la w q := rfl
      rw [hq]
      simp [Finsupp.single_left_inj one_ne_zero, h0]
    · push Not at h1
      unfold s0
      rw [hasse_algebraMap, hasseRp_sec_eq_zero X la w h0 h1 0, map_zero]
      simp [h0, h1]

end

theorem compositionalInverseSymm : S1 := by
  classical
  intro D B P j X la N wL w T β
  have hT := _root_.coeffInversePowerFacts (Idx D j N) (Lc X la w) (tayLc X la w) (s0 X la w) (wi X la w)
    (Finsupp.equivFunOnFinite.symm (cS X la w)) (section_mul_inverse X la w) (taySec X la w) T β
  rw [← hasse_apply] at hT
  have hprod : (β.prod fun p b => (Finsupp.equivFunOnFinite.symm (cS X la w)) p ^ b) =
      if (∀ i : Fin (WeightFamilies.dimY D j), ∀ k, β (i.succ, k) = 0) then
        algebraMap (Rp X la N) (Lc X la w) (∏ k, emb X la N (X.inc wL (w k)) ^ β (0, k)) else 0 := by
    rw [Finsupp.prod_fintype _ _ (by intro p; simp)]
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    rw [Fintype.prod_prod_type, Fin.prod_univ_succ]
    simp only [cS_eq, Fin.succ_ne_zero, if_false, if_true, map_prod, map_pow]
    split_ifs with h
    · simp [h]
    · push Not at h
      obtain ⟨i, k, hk⟩ := h
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      apply Finset.prod_eq_zero (Finset.mem_univ k)
      exact zero_pow hk
  refine ⟨if (∀ i : Fin (WeightFamilies.dimY D j), ∀ k, β (i.succ, k) = 0) then
      (-1) ^ (β.sum fun _ n => n) * (((T + (β.sum fun _ n => n) - 1).choose (β.sum fun _ n => n) : ℕ) : ℤ) *
        ((Nat.multinomial β.support β : ℕ) : ℤ) else 0, ?_, ?_⟩
  · intro hm
    split_ifs at hm with h
    · rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type, Fin.sum_univ_succ]
      simp [h]
    · exact absurd rfl hm
  · rw [hT, hprod]
    split_ifs with h
    · push_cast
      ring
    · simp

end PI.HasseOrdBdW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseOrderBound.OrthogonalSplitPolarizationVanishes
section
noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.HasseOrdBdW

section

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)

def Rep (u : WeightFamilies.Wt D j) (F : X.Forms) : Prop := ∃ g : B.Cusp j u, X.inc u g = F

variable {X}

theorem rep_mul {wL u : WeightFamilies.Wt D j} (x : B.Cusp j wL) {F : X.Forms} (hF : Rep X u F) :
    Rep X (wadd wL u) (X.inc wL x * F) := by
  obtain ⟨g, rfl⟩ := hF
  obtain ⟨H, hH⟩ := X.inc_mul wL u x g
  exact ⟨H, hH.symm⟩

theorem rep_pow (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) {wL wF : WeightFamilies.Wt D j} (x : B.Cusp j wL) (d : ℝ)
    (hd : (d : EReal) ≤ X.vAt la y (X.inc wL x)) :
    ∀ (a m : ℕ) (F : X.Forms), Rep X (addL wF wL m) F →
      Rep X (addL wF wL (m + a)) (X.inc wL x ^ a * F) ∧
      X.vAt la y F + (((a : ℝ) * d : ℝ) : EReal) ≤ X.vAt la y (X.inc wL x ^ a * F) := by
  intro a
  induction a with
  | zero =>
    intro m F hF
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, EReal.coe_zero, add_zero]
    exact ⟨hF, le_rfl⟩
  | succ a ih =>
    intro m F hF
    obtain ⟨hR, hv⟩ := ih m F hF
    have hR' := rep_mul x hR
    rw [wadd_addL] at hR'
    refine ⟨by rw [pow_succ', mul_assoc]; exact hR', ?_⟩
    obtain ⟨g, hg⟩ := hR
    rw [pow_succ', mul_assoc, ← hg, X.vAt_mul]
    rw [← hg] at hv
    have e1 : ((((a + 1 : ℕ) : ℝ) * d : ℝ)) = (a : ℝ) * d + d := by push_cast; ring
    rw [e1, EReal.coe_add]
    calc X.vAt la y F + ((((a : ℝ) * d : ℝ) : EReal) + (d : EReal))
        = (d : EReal) + (X.vAt la y F + (((a : ℝ) * d : ℝ) : EReal)) := by ac_rfl
      _ ≤ _ := add_le_add hd hv

theorem rep_prod (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) {N : ℕ} {wL wF : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (d : ℝ) (hd : ∀ k, (d : EReal) ≤ X.vAt la y (X.inc wL (w k))) (e : Fin N → ℕ) :
    ∀ (s : Finset (Fin N)) (m : ℕ) (F : X.Forms), Rep X (addL wF wL m) F →
      Rep X (addL wF wL (m + ∑ k ∈ s, e k)) ((∏ k ∈ s, X.inc wL (w k) ^ e k) * F) ∧
      X.vAt la y F + ((((∑ k ∈ s, e k : ℕ) : ℝ) * d : ℝ) : EReal) ≤
        X.vAt la y ((∏ k ∈ s, X.inc wL (w k) ^ e k) * F) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro m F hF
    simp only [Finset.prod_empty, Finset.sum_empty, one_mul, add_zero, Nat.cast_zero, zero_mul, EReal.coe_zero]
    exact ⟨hF, le_rfl⟩
  | @insert a s ha ih =>
    intro m F hF
    obtain ⟨hR, hv⟩ := ih m F hF
    obtain ⟨hR2, hv2⟩ := rep_pow la y (w a) d (hd a) (e a) _ _ hR
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_assoc]
    refine ⟨?_, ?_⟩
    · have h3 : m + (e a + ∑ k ∈ s, e k) = m + ∑ k ∈ s, e k + e a := by ring
      rw [h3]
      exact hR2
    · calc _ = X.vAt la y F + ((((∑ k ∈ s, e k : ℕ) : ℝ) * d : ℝ) : EReal) + (((e a : ℝ) * d : ℝ) : EReal) := by
            rw [add_assoc, ← EReal.coe_add]
            congr 2
            push_cast
            ring
        _ ≤ _ := le_trans (add_le_add hv le_rfl) hv2

end

theorem orthogonalSplitPolarizationVanishes : S2 := by
  intro D B P j X la y N wL wF w d hd m g e n hn
  subst hn
  obtain ⟨⟨g', hg'⟩, hv⟩ := rep_prod la y w d hd e Finset.univ m (X.inc _ g) ⟨g, rfl⟩
  refine ⟨g', by rw [mul_comm, hg'], ?_⟩
  rw [hg']
  exact hv

end PI.HasseOrdBdW
end
end

