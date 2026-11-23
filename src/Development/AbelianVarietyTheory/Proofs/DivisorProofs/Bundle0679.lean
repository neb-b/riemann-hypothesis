module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentOfQuasiLogarithm
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QLogTangent

theorem smodEq_iff' {O : Type} [CommRing O] (p : O) (n : ℕ) (x y : O) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule O O)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top, Ideal.mem_span_singleton]

theorem eq_zero_of_forall_dvd {O : Type} [CommRing O] (p : O) [IsHausdorff (Ideal.span {p}) O] (x : O)
    (h : ∀ n : ℕ, p ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' x fun n => (smodEq_iff' p n x 0).2 (by simpa using h n)

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ f : MvPowerSeries (Fin d) E, QL c.μ ⊤ f → ∃! l : G.dual.Lie, c.IsLie f l := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f hf
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hlift : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  have hser : ∀ {τ : Type} (F : MvPowerSeries τ E), In (⊤ : Ideal O) F →
      ∃ s : MvPowerSeries τ O, map (algebraMap O E) s = F := by
    intro τ F hF'
    choose b _ hb using hF'
    let S : MvPowerSeries τ O := fun α => b α
    exact ⟨S, by ext α; rw [coeff_map, hb α]; rfl⟩
  have hminj : ∀ (s s' : MvPowerSeries (Fin d) O),
      map (algebraMap O E) s = map (algebraMap O E) s' → s = s' := by
    intro s s' h
    ext α
    apply hinj
    have := congrArg (coeff α) h
    simpa [coeff_map] using this
  have hdef : ∀ k, ∃ s : MvPowerSeries (Fin d) O, map (algebraMap O E) s = defect c.μ k f :=
    fun k => hser _ (GlobalTheory.QLogDefect.main p O O E (RingHom.id O) hF d c.μ hlift ⊤ f hf k).1
  obtain ⟨g, hg⟩ := hser _ hf.2.2
  choose s hs using hdef
  let a : ∀ n, G.A n := fun n => c.ev n (s (p ^ n))
  have hprim : ∀ n, ∃ t : G.A n ⊗[O] G.A n,
      Coalgebra.comul (R := O) (a n) = a n ⊗ₜ[O] (1 : G.A n) + (1 : G.A n) ⊗ₜ[O] a n + ((p : O) ^ n) • t := by
    intro n
    obtain ⟨h1, h2⟩ := GlobalTheory.CobDefect.main O E d c.μ c.isLaw hinj f g (s (p ^ n)) (p ^ n) hf.1 hg (hs _)
    refine ⟨c.ev₂ n g, ?_⟩
    show Coalgebra.comul (R := O) (c.ev n (s (p ^ n))) = _
    rw [GlobalTheory.QLog.Chart.comul_ev p C v O hv G d c n, h1, map_sub, map_smul, GlobalTheory.EvTor.ev₂_at_nmul_pow_self p C v O hv G d c n, h2, map_zero, sub_zero,
      Nat.cast_pow]
  have hcomp : ∀ n, ∃ b : G.A (n + 1), a (n + 1) = G.mulP n (a n) + ((p : O) ^ n) • b := by
    intro n
    have h := GlobalTheory.DefectComp.main O E d c.μ c.isLaw hinj f hf.1 (p ^ n) p (s (p ^ n)) (s p) (s (p ^ n * p))
      (hs _) (hs _) (hs _)
    refine ⟨c.ev (n + 1) (s p), ?_⟩
    show c.ev (n + 1) (s (p ^ (n + 1))) = G.mulP n (c.ev n (s (p ^ n))) + _
    rw [pow_succ, h, map_add (f := _), map_smul, GlobalTheory.EvP.ev_subst_nmul_p p C v O hv G d c n, Nat.cast_pow]
  have key : ∀ n (φ ψ : CartierDual O (G.A n)), PDiv.dUnit (R := O) φ = PDiv.dUnit (R := O) ψ →
      (p : O) ^ n ∣ φ (a n) - ψ (a n) := by
    intro n φ ψ h
    obtain ⟨t, ht⟩ := hprim n
    exact GlobalTheory.CotDualLin.dvd_sub_of_dUnit_eq O (G.A n) (a n) _ t ht φ ψ h
  have dsurj : ∀ n (x : PDiv.Cot O (CartierDual O (G.A n))), ∃ φ : CartierDual O (G.A n),
      PDiv.dUnit (R := O) φ = x := fun n x => AugCot.d_surjective _ x
  have haus : ∀ x : O, (∀ n : ℕ, (p : O) ^ n ∣ x) → x = 0 := eq_zero_of_forall_dvd (p : O)
  let Good : G.dual.omega → O → Prop := fun w L => ∀ n (φ : CartierDual O (G.A n)),
    PDiv.dUnit (R := O) φ = w.1 n → (p : O) ^ n ∣ L - φ (a n)
  have good_unique : ∀ w L L', Good w L → Good w L' → L = L' := by
    intro w L L' h h'
    refine sub_eq_zero.1 (haus _ fun n => ?_)
    obtain ⟨φ, hφ⟩ := dsurj n (w.1 n)
    have := dvd_sub (h n φ hφ) (h' n φ hφ)
    rwa [sub_sub_sub_cancel_right] at this
  have good_exists : ∀ w, ∃ L, Good w L := by
    intro w
    choose φ hφ using fun n => dsurj n (w.1 n)
    have step : ∀ n, (p : O) ^ n ∣ φ (n + 1) (a (n + 1)) - φ n (a n) := by
      intro n
      obtain ⟨b, hb⟩ := hcomp n
      have h1 : PDiv.dUnit (R := O) (CartierDual.map (G.mulP n) (φ (n + 1))) = w.1 n := by
        rw [← w.2 n, ← hφ (n + 1)]
        exact (PDiv.cotMap_d (G.dual.res n) (φ (n + 1))).symm
      have h2 := key n _ _ (h1.trans (hφ n).symm)
      rw [CartierDual.map_apply] at h2
      rw [hb, map_add (f := _), map_smul, smul_eq_mul]
      have e : φ (n + 1) (G.mulP n (a n)) + (p : O) ^ n * φ (n + 1) b - φ n (a n) =
          (φ (n + 1) (G.mulP n (a n)) - φ n (a n)) + (p : O) ^ n * φ (n + 1) b := by ring
      rw [e]
      exact dvd_add h2 (dvd_mul_right _ _)
    have cauchy : ∀ m n, m ≤ n → (p : O) ^ m ∣ φ n (a n) - φ m (a m) := by
      intro m n hmn
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        have := dvd_add ih ((pow_dvd_pow (p : O) hmn).trans (step n))
        rwa [add_comm, sub_add_sub_cancel] at this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) (fun n => φ n (a n))
      (fun {m n} hmn => (smodEq_iff' _ _ _ _).2 (dvd_sub_comm.1 (cauchy m n hmn)))
    refine ⟨L, fun n ψ hψ => ?_⟩
    have h1 := (smodEq_iff' _ _ _ _).1 (hL n)
    have h2 := key n _ _ ((hφ n).trans hψ.symm)
    have := dvd_add (dvd_sub_comm.1 h1) h2
    rwa [sub_add_sub_cancel] at this
  choose Lf hLf using good_exists
  have hgood_add : ∀ w w', Good (w + w') (Lf w + Lf w') := by
    intro w w' n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    obtain ⟨φ2, h2⟩ := dsurj n (w'.1 n)
    have e : PDiv.dUnit (R := O) (φ1 + φ2) = PDiv.dUnit (R := O) φ := by
      have ea : PDiv.dUnit (R := O) (φ1 + φ2) = PDiv.dUnit (R := O) φ1 + PDiv.dUnit (R := O) φ2 := map_add (AugCot.d _) φ1 φ2
      rw [ea, h1, h2, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_add (hLf w n φ1 h1) (hLf w' n φ2 h2)) k
    have e2 : (φ1 + φ2) (a n) = φ1 (a n) + φ2 (a n) := rfl
    rw [e2] at this
    have e3 : Lf w - φ1 (a n) + (Lf w' - φ2 (a n)) + (φ1 (a n) + φ2 (a n) - φ (a n)) =
        Lf w + Lf w' - φ (a n) := by ring
    rwa [e3] at this
  have hgood_smul : ∀ (r : O) w, Good (r • w) (r * Lf w) := by
    intro r w n φ hφ
    obtain ⟨φ1, h1⟩ := dsurj n (w.1 n)
    have e : PDiv.dUnit (R := O) (r • φ1) = PDiv.dUnit (R := O) φ := by
      have ea : PDiv.dUnit (R := O) (r • φ1) = r • PDiv.dUnit (R := O) φ1 := map_smul (AugCot.d _) r φ1
      rw [ea, h1, hφ]; rfl
    have k := key n _ _ e
    have := dvd_add (dvd_mul_of_dvd_right (hLf w n φ1 h1) r) k
    have e2 : (r • φ1) (a n) = r * φ1 (a n) := rfl
    rw [e2] at this
    have e3 : r * (Lf w - φ1 (a n)) + (r * φ1 (a n) - φ (a n)) = r * Lf w - φ (a n) := by ring
    rwa [e3] at this
  let l : G.dual.Lie :=
    { toFun := Lf
      map_add' := fun w w' => good_unique _ _ _ (hLf (w + w')) (hgood_add w w')
      map_smul' := fun r w => good_unique _ _ _ (hLf (r • w)) (hgood_smul r w) }
  have hisLie : ∀ l' : G.dual.Lie, c.IsLie f l' ↔ ∀ w, Good w (l' w) := by
    intro l'
    constructor
    · intro h w n φ hφ
      exact h.2 n w φ (s (p ^ n)) hφ (hs _)
    · intro h
      refine ⟨fun n => In.top_iff.2 ⟨s (p ^ n), hs _⟩, fun n w φ s' hφ hs' => ?_⟩
      have : s' = s (p ^ n) := hminj _ _ (hs'.trans (hs _).symm)
      subst this
      exact h w n φ hφ
  refine ⟨l, (hisLie l).2 fun w => hLf w, fun l' hl' => ?_⟩
  exact LinearMap.ext fun w => good_unique _ _ _ ((hisLie l').1 hl' w) (hLf w)

end GlobalTheory.QLogTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorExponentLeOfIntegral
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.DenomBound

theorem cE_le_of_inZl : ∀ {F : Type} [Field F] [NumberField F] (z : ClassGroup (𝓞 F) → ℚ) (l a n : ℕ) [Fact l.Prime], 2 ≤ a → 1 ≤ n →
    (∀ C, InZl l (((a ^ n - 1 : ℕ) : ℚ) * z C)) → cE z l ≤ finrank ℚ F * padicValNat l 2 + padicValNat l (a ^ n - 1) := by
  intro F _ _ z l a n _ ha hn h
  unfold cE
  apply Finset.sup_le
  intro C _
  unfold denomExp
  by_cases hz : z C = 0
  · simp [hz]
  have hpow : 2 ≤ a ^ n := le_trans ha (Nat.le_self_pow (by omega) a)
  have hA : (a ^ n - 1 : ℕ) ≠ 0 := by omega
  have hAq : ((a ^ n - 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hA
  have h1 := h C
  rw [inZl_iff, padicValRat.mul hAq hz, padicValRat.of_nat] at h1
  rw [← Nat.padicValNat_def] at h1
  have h2 : (2 : ℚ) ^ finrank ℚ F ≠ 0 := pow_ne_zero _ two_ne_zero
  have h3 : padicValRat l (z C / 2 ^ finrank ℚ F) = padicValRat l (z C) - (finrank ℚ F : ℤ) * (padicValNat l 2 : ℤ) := by
    rw [padicValRat.div hz h2, padicValRat.pow (q := (2:ℚ))]
    have : padicValRat l (2 : ℚ) = padicValNat l 2 := by
      have := padicValRat.of_nat (p := l) (n := 2)
      simpa [Nat.padicValNat_def] using this
    rw [this]
  rw [h3]
  omega

end GlobalTheory.DenomBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionSmallFirstJetNormalFrame
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JetSmall

theorem ph_nsmul {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : La) (i : ι) (y : Y) (hy : y ∈ (A.chart i).source) (k : ℕ) :
    A.ph (k • H) i y = k * A.ph H i y := by
  induction k with
  | zero =>
    rw [zero_nsmul, Nat.cast_zero, zero_mul]
    have := A.ph_add 0 0 i y hy
    rw [add_zero] at this
    linarith
  | succ k ih =>
    rw [succ_nsmul, A.ph_add _ _ i y hy, ih]
    push_cast; ring

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  intro n Y _ _ _ _ _ ι La _ A H G i p r0 c Cq K q hr0 hc hsub hq hH ε hε

  set r : ℝ := min r0 (Real.sqrt (c / (2 * (|Cq| + 1)))) with hr
  have hCq1 : 0 < |Cq| + 1 := by positivity
  have hrpos : 0 < r := lt_min hr0 (Real.sqrt_pos.2 (by positivity))
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hr2 : r ^ 2 ≤ c / (2 * (|Cq| + 1)) := by
    have h1 : r ≤ Real.sqrt (c / (2 * (|Cq| + 1))) := min_le_right _ _
    have h2 := pow_le_pow_left₀ hrpos.le h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hsubr : closedBall p r ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall hrr0).trans hsub
  have hball : ball p r ⊆ (A.chart i).target := ball_subset_closedBall.trans hsubr
  have hquad : ∀ v ∈ closedBall p r, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ c / 2 := by
    intro v hv
    have h := hH v (closedBall_subset_closedBall hrr0 hv)
    have hd : ‖v - p‖ ≤ r := by rw [← dist_eq_norm]; exact hv
    have hd2 : ‖v - p‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
    have h3 : Cq * ‖v - p‖ ^ 2 ≤ |Cq| * ‖v - p‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have h4 : |Cq| * ‖v - p‖ ^ 2 ≤ |Cq| * (c / (2 * (|Cq| + 1))) :=
      mul_le_mul_of_nonneg_left (hd2.trans hr2) (abs_nonneg _)
    have h5 : |Cq| * (c / (2 * (|Cq| + 1))) ≤ c / 2 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [abs_nonneg Cq]
    linarith

  obtain ⟨M, hM⟩ := hyq_bdd (f := fun v => Real.exp (A.ph G i ((A.chart i).symm v))) (c := p) (r := r)
    ((A.smooth_ph G i).continuousOn.rexp.mono hsubr)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hM p (mem_closedBall_self hrpos.le))

  obtain ⟨C, hC0, hC⟩ := _root_.GlobalTheory.l2_value_deriv_ball n r hrpos

  have htend : Tendsto (fun k : ℕ => C * M * |K| * Real.exp (-(c / 2) * k)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => -(c / 2) * (k : ℝ)) atTop atBot :=
      (tendsto_natCast_atTop_atTop).const_mul_atTop_of_neg (by linarith)
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (C * M * |K|)
    simpa using h2
  obtain ⟨k0, hk0⟩ := eventually_atTop.1 ((tendsto_order.1 htend).2 (ε ^ 2) (by positivity))
  refine ⟨k0, fun k hk D hD hDd hn0 => ?_⟩
  set u : V n → ℂ := fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v)) with hu
  have hud : DifferentiableOn ℂ u (ball p r) :=
    (hDd.mono (ball_subset_ball hrr0)).mul
      ((Complex.differentiable_exp.comp ((hq.const_mul (k : ℂ)).neg)).differentiableOn)
  have hest := hC p u hud

  set la : La := G + k • H
  set f : Y → ℝ≥0∞ := fun y => ENNReal.ofReal (A.nsq (A.kap + la) D y) with hf
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp (A.aap_continuous_nsq _ D hD.2
      (fun j => (hD.1 j).continuousOn)).measurable

  have hpt : ∀ v ∈ ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
        (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) := by
    intro v hv
    set y := (A.chart i).symm v
    have hy : y ∈ (A.chart i).source := (A.chart i).map_target (hball hv)
    have hns := hyq_nsq_chart A (A.kap + la) D i y hy (hD.2 i (A.pick y) y hy (A.mem_pick y))
    have hph : A.ph (A.kap + la) i y = A.ph A.kap i y + (A.ph G i y + k * A.ph H i y) := by
      rw [A.ph_add _ _ i y hy, A.ph_add _ _ i y hy, ph_nsmul A H i y hy]
    simp only [hf]
    rw [hns, hph, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hnu : ‖u v‖ ^ 2 = ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re)) := by
      simp only [hu, norm_mul, Complex.norm_exp, mul_pow]
      congr 1
      rw [← Real.exp_nat_mul]
      congr 1
      simp [Complex.neg_re, Complex.mul_re]
      ring
    rw [hnu]
    have hq2 := hquad v (ball_subset_closedBall hv)
    have hMv := hM v (ball_subset_closedBall hv)
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have key : Real.exp (-(2 * k * (q v).re)) ≤
        M * Real.exp (k * (c / 2)) * (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
          Real.exp (A.ph A.kap i y)) := by
      calc Real.exp (-(2 * k * (q v).re))
          ≤ Real.exp (A.ph G i y) * Real.exp (k * (c / 2)) *
              (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) *
                Real.exp (A.ph A.kap i y)) := by
            rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_le_mul_of_nonneg_left hq2 hk0]
        _ ≤ _ := by gcongr
    calc ‖D i y‖ ^ 2 * Real.exp (-(2 * k * (q v).re))
        ≤ ‖D i y‖ ^ 2 * (M * Real.exp (k * (c / 2)) *
          (Real.exp (-(A.ph A.kap i y + (A.ph G i y + k * A.ph H i y))) * Real.exp (A.ph A.kap i y))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = _ := by ring
  have hint : ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) ≤
      ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
    calc ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2)
        ≤ ∫⁻ v in ball p r, ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            (f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v)))) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ = ENNReal.ofReal (M * Real.exp (k * (c / 2))) * ∫⁻ v in ball p r,
            f ((A.chart i).symm v) * ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (M * Real.exp (k * (c / 2))) * n0 A la D := by
          gcongr
          exact A.aap_lintegral_chart_le i f hfm _ hball

  have hall : ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
      ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
    calc ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal (M * Real.exp (k * (c / 2))) *
            ENNReal.ofReal (|K| * Real.exp (-c * k))) := by
          refine hest.trans ?_
          gcongr
          refine hint.trans ?_
          gcongr
          exact hn0.trans (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.exp_pos _).le))
      _ = ENNReal.ofReal (C * M * |K| * Real.exp (-(c / 2) * k)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC0]
          congr 1
          have : Real.exp (k * (c / 2)) * Real.exp (-c * k) = Real.exp (-(c / 2) * k) := by
            rw [← Real.exp_add]; congr 1; ring
          calc C * (M * Real.exp (k * (c / 2)) * (|K| * Real.exp (-c * k)))
              = C * M * |K| * (Real.exp (k * (c / 2)) * Real.exp (-c * k)) := by ring
            _ = _ := by rw [this]
  have hsq : ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by
    have hb := (hk0 k hk).le
    rcases (ENNReal.ofReal_le_ofReal_iff'.1 hall) with h | h
    · linarith
    · nlinarith [sq_nonneg ε]
  have h1 : ‖u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖fderiv ℂ u p‖]
  have h2 : ‖fderiv ℂ u p‖ ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg ‖u p‖]
  exact ⟨by nlinarith [norm_nonneg (u p)], by nlinarith [norm_nonneg (fderiv ℂ u p)]⟩

end GlobalTheory.JetSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionsFiniteWeightedAtlas
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem peakFin_exists_pos_le {Y : Type} (T : Finset Y) (f : Y → ℝ) (hf : ∀ P, 0 < f P) :
    ∃ r : ℝ, 0 < r ∧ ∀ P ∈ T, r ≤ f P := by
  first
  | exact @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
  | (apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset ..)

theorem peak_sections_finite : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A), ∀ (H : La), (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ T : Finset Y, ∃ (q : Y → V n → ℂ) (c Cq r0 : ℝ), 0 < c ∧ 0 < r0 ∧ (∀ P ∈ T, Differentiable ℂ (q P) ∧ closedBall (A.chart (A.pick P) P) r0 ⊆ (A.chart (A.pick P)).target ∧ ∀ v ∈ closedBall (A.chart (A.pick P) P) r0, A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q P v).re ≤ Cq * ‖v - (A.chart (A.pick P) P)‖ ^ 2) ∧ ∀ (G : La) (p : Y → V n → ℂ), (∀ P, Differentiable ℂ (p P)) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ P ∈ T, ∀ v ∈ ball (A.chart (A.pick P) P) r0, F0 (A.pick P) ((A.chart (A.pick P)).symm v) = p P v * Complex.exp (k * q P v)) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-c * k)) := by
  intro n Y _ _ _ _ _ ι La _ A C H hH T
  classical
  obtain ⟨U, hU, hdisj⟩ := T.finite_toSet.t2_separation
  have h7 : ∀ P : Y, ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧
      closedBall (A.chart (A.pick P) P) ρ ⊆
        (A.chart (A.pick P)).target ∩ (A.chart (A.pick P)).symm ⁻¹' U P ∧
      ∀ v ∈ closedBall (A.chart (A.pick P) P) ρ,
        c * ‖v - A.chart (A.pick P) P‖ ^ 2 ≤
          A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ∧
        A.ph H (A.pick P) ((A.chart (A.pick P)).symm v) - 2 * (q v).re ≤
          C * ‖v - A.chart (A.pick P) P‖ ^ 2 := by
    intro P
    refine _root_.GlobalTheory.psh_normal_frame n _ (fun v => A.ph H (A.pick P) ((A.chart (A.pick P)).symm v)) _
      ((A.chart (A.pick P)).isOpen_inter_preimage_symm (hU P).2) ?_
      ((A.smooth_ph H (A.pick P)).mono Set.inter_subset_left) ?_
    · refine ⟨(A.chart (A.pick P)).map_source (A.mem_pick P), ?_⟩
      rw [Set.mem_preimage, (A.chart (A.pick P)).left_inv (A.mem_pick P)]
      exact (hU P).1
    · intro ξ hξ
      exact hH (A.pick P) P (A.mem_pick P) ξ hξ
  choose q c Cc ρ hq hc hC hρ hsub hb using h7
  obtain ⟨r0, hr0, hr0le⟩ := peakFin_exists_pos_le T (fun P => ρ P / 2)
    (fun P => half_pos (hρ P))
  obtain ⟨c0, hc0, hc0le⟩ := peakFin_exists_pos_le T (fun P => c P * ρ P ^ 2 / 4)
    (fun P => by have := hc P; have := hρ P; positivity)
  have hrρ : ∀ P ∈ T, r0 ≤ ρ P := fun P hP => by
    have h1 : r0 ≤ ρ P / 2 := hr0le P hP
    have := hρ P
    linarith
  refine ⟨q, c0, ∑ P ∈ T, Cc P, r0, hc0, hr0, fun P hP => ⟨hq P, ?_, ?_⟩, ?_⟩
  · exact ((closedBall_subset_closedBall (hrρ P hP)).trans (hsub P)).trans Set.inter_subset_left
  · intro v hv
    refine (hb P v (closedBall_subset_closedBall (hrρ P hP) hv)).2.trans ?_
    exact mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (f := Cc) (fun Q _ => (hC Q).le) hP) (by positivity)
  · intro G p hp
    have h9 := fun P : Y => _root_.GlobalTheory.OTY.peak_section n Y ι La A C H G (A.pick P) (A.chart (A.pick P) P)
      (ρ P) (c P) (q P) (p P) (hρ P) (hc P) ((hsub P).trans Set.inter_subset_left) (hq P) (hp P)
      (fun v hv => (hb P v hv).1)
    choose K hK F hF using h9
    have hKs : 0 ≤ ∑ P ∈ T, K P := Finset.sum_nonneg fun P _ => hK P
    refine ⟨(T.card : ℝ) * ∑ P ∈ T, K P, by positivity, fun k => ?_⟩
    obtain ⟨hs, hn⟩ := GlobalTheory.T.finSum_smoothSection_dbarEnergy_le n Y ι La A C (G + k • H) T (fun P => F P k)
      (fun P _ => (hF P k).1)
    refine ⟨_, hs, fun P hP v hv => ?_, hn.trans ?_⟩
    · have hv' : v ∈ ball (A.chart (A.pick P) P) (ρ P / 2) := ball_subset_ball (hr0le P hP) hv
      have hvU : (A.chart (A.pick P)).symm v ∈ U P :=
        (hsub P (ball_subset_closedBall (ball_subset_ball (hrρ P hP) hv))).2
      rw [← (hF P k).2.1 v hv']
      refine Finset.sum_eq_single_of_mem P hP (fun Q hQ hQP => ?_)
      refine (hF Q k).2.2.1 _ _ (fun hm => ?_)
      have h1 := (hsub Q (ball_subset_closedBall hm.2)).2
      rw [Set.mem_preimage, (A.chart (A.pick Q)).left_inv hm.1] at h1
      exact Set.disjoint_left.1 (hdisj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hP) hQP) h1 hvU
    · have hle : ∑ P ∈ T, n1 C (G + k • H) (F P k) ≤
          ∑ P ∈ T, ENNReal.ofReal (K P * Real.exp (-c0 * k)) := by
        refine Finset.sum_le_sum fun P hP => (hF P k).2.2.2.trans ?_
        refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (hK P))
        refine Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg k))
        exact neg_le_neg (hc0le P hP)
      refine (mul_le_mul_right hle _).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_sum_of_nonneg
          (fun P _ => mul_nonneg (hK P) (Real.exp_pos _).le), ← Finset.sum_mul, mul_assoc,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end GlobalTheory.OTY
end

