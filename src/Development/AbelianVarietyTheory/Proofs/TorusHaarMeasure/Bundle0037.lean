module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalDecayHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.PublishedTheorems.DefiniteCompactness.ExistsCompactOfDefinite
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.WeightContDiffOn
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableIndicatorOfContOn
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsCompactOfLeSumPnormSq
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

namespace CuspCompact

theorem exists_sum_exp_lt {N : ℕ} (C c : Fin N → ℝ) (hc : ∀ k, 0 < c k) (c0 : ℝ) (h0 : 0 < c0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      ∑ k, C k * Real.exp (-2 * Real.pi * c k / s) < c0 := by
  have ht : Filter.Tendsto (fun s : ℝ => ∑ k, C k * Real.exp (-2 * Real.pi * c k / s))
      (𝓝[>] 0) (𝓝 (∑ k : Fin N, C k * 0)) := by
    refine tendsto_finsetSum _ fun k _ => Filter.Tendsto.const_mul _ ?_
    refine Real.tendsto_exp_atBot.comp ?_
    have hneg : -2 * Real.pi * c k < 0 := by
      have := mul_pos Real.pi_pos (hc k)
      linarith
    exact (Filter.Tendsto.const_mul_atTop_of_neg hneg (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))).congr
      fun s => (div_eq_mul_inv _ _).symm
  simp only [mul_zero, Finset.sum_const_zero] at ht
  have hev := ht.eventually (gt_mem_nhds h0)
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  exact ⟨δ, hδ, fun s hs hsδ => hsub ⟨hs, hsδ⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_compact_of_le_sum_pnorm_sq :
    LineBundleFirstBoundGlobalGeneration (E := E) → MahlerCompactnessCriterion (E := E) →
    ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (c0 : ℝ), 0 < c0 →
    ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C := by
  intro hLa hM2 r X Xa c0 h0
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨X.dom, Set.subsingleton_of_subsingleton.isCompact, subset_rfl, fun x hx _ => ?_⟩
    refine ⟨1, X.Γ.one_mem, x, fun τ => ⟨by simp, fun a => a.elim0⟩, ?_⟩
    rwa [Subsingleton.elim (lact 1 (rmul x x)) x]
  have hpos := (hLa r X hr).2.2
  choose c hc hcw using fun k => spectralGap_holds r X Xa.L (Xa.w k) (Xa.w_van k).1
  choose C hC using fun k => cuspidalDecay_holds r X Xa.L (Xa.w k) (c k) (hc k).le (hcw k)
  obtain ⟨δ, hδ, hlt⟩ := exists_sum_exp_lt C c hc c0 h0
  obtain ⟨K, hK, hKd, hKx⟩ := hM2 r X (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
  refine ⟨K, hK, hKd, fun x hx hle => hKx x hx ?_⟩
  have hs : 0 < X.firstMinimumSq x := Real.sqrt_pos.1 (hpos x hx)
  refine Real.sqrt_le_sqrt (not_lt.1 fun h => ?_)
  have h1 := hlt _ hs h
  have h2 : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤
      ∑ k, C k * Real.exp (-2 * Real.pi * c k / X.firstMinimumSq x) :=
    Finset.sum_le_sum fun k _ => hC k x hx
  linarith

end CuspCompact

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedFiniteMeasure

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finMu_of_covolume :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → (∀ (r : ℕ) (X : Data E r), FinMu X) := by
  intro hcov
  exact GlobalTheory.FiniteCovolume.finMu_of_finite_covolume hcov GlobalTheory.UnitaryFrames.unitary_group_frames
    (GlobalTheory.UnitaryInvMeasure.invMeas GlobalTheory.FrameMeasureClosed.measInv_holds
      GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt GlobalTheory.isOrth_rmul_iff_unitary_diagonal
      (GlobalTheory.SatFin.muF_sat_lt_top GlobalTheory.FrameMeasureClosed.measInv_holds)
      GlobalTheory.UnitaryFrames.unitary_group_frames.2)
    GlobalTheory.ClosedDiscontinuity.propDisc_closed

end GlobalTheory.ClosedFiniteMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.InterpWeight
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.InterpWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem core (hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E))
    (hExt : ExtFStatement (E := E)) (hMI : MeasInvStatement (E := E)) (hV : VanishAtSStatement (E := E))
    (hK : KapGGStatement (E := E)) {r : ℕ} (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa)
    (G : Wt X.Ψ r) (bb m η : ℝ) (hbb : 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb) (hbm : bb < m) (hη : 0 < η)
    (hmar : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ)
    (hstr : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) (j : Fin Fl.δ) :
    ∃ (x0 : Frame X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (F : V (nd X) → ℂ) (P : Frame X.Ψ r → ℂ),
      IsOrth X x0 ∧ IsMetricW X G W ∧ WLower X G W ∧
      DifferentiableOn ℂ F (OmF X x0) ∧ InAt X x0 W bb F ∧ IsBEq X G P ∧
      (∀ z ∈ OmF X x0, P (cpt X x0 z) = F z) ∧ P (lact 1 (Fl.xs j)) ≠ 0 ∧
      ∀ γ ∈ X.Γ, ∀ j', (γ ≠ 1 ∨ j' ≠ j) → P (lact γ (Fl.xs j')) = 0 := by
  have hCo := GlobalTheory.OrbitCoord.det_fderiv_ne_zero_orbit hK
  have hn : 0 < nd X := lt_of_lt_of_le (by norm_num) Xa.n_ge
  have hbb0 : 0 ≤ bb := le_trans (by positivity) hbb.le
  have hw0b : X.IsBddSec Xa.L Fl.w0 := Fl.weightForm_vanishes.1.1
  have hsb : ∀ k, X.IsBddSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1
  have hw0 : X.IsSec Xa.L Fl.w0 := hw0b.1
  have hs : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (hsb k).1
  have key : ∀ j', ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, ∀ x1, x1 = lact γ (rmul (Fl.xs j') b) →
      Fl.w0 x1 ≠ 0 ∧ (∀ k, Fl.s k x1 = 0) ∧
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        Fl.s k (cpt X x1 z) / Fl.w0 (cpt X x1 z) : V (nd X))) 0).det ≠ 0 := by
    rintro j' γ hγ b hb x1 rfl
    refine ⟨KronAssembly.sec_ne_zero X hw0 (Fl.xs_mem j') (Fl.w0_ne j') hγ hb, ?_,
      hCo r X Xa.L Fl.w0 Fl.s hw0 hs _ (Fl.xs_mem j') (Fl.w0_ne j') (Fl.coord j') γ hγ b hb⟩
    exact (Fl.S_eq _ (OntoS.dom_lact X hγ (OntoS.dom_rmul X (Fl.xs_mem j') hb))).2
      ⟨j', γ, hγ, b, hb, rfl⟩
  obtain ⟨x0, ho, b0, hb0, b0', hb0', hx0, hx0'⟩ :=
    KronAssembly.exists_orth X (Fl.xs_mem j) X.Γ.one_mem
  have hx0d : x0 ∈ X.dom := IW.orth_mem_dom X x0 ho
  obtain ⟨k1, k2, k3⟩ := key j 1 X.Γ.one_mem b0' hb0' x0 hx0'
  have hψb : ∃ C : ℝ, ∀ x ∈ X.dom, (fun _ : Frame X.Ψ r => (0 : ℝ)) x ≤ C := ⟨0, fun _ _ => le_rfl⟩
  obtain ⟨hψc, hMW, hWL⟩ := GlobalTheory.KronMetric.kronMetric hN r X G (fun _ => 0) (fun _ _ _ _ _ _ => rfl)
    (fun _ _ => contDiffOn_const) hψb
  obtain ⟨ε, χ, F, hε, hball, hiso, hχc, hχ1, hχ0, hF, hint⟩ :=
    GlobalTheory.kronSolve r X G Xa.L Fl.w0 Fl.s (fun _ => 0) x0 bb m η hn ho hw0 hs contDiffOn_const hbb0 hbm hη
      (fun z hz ξ => by rw [leviO_zero, add_zero]; exact hmar x0 ho z hz ξ)
      (fun z hz ξ => by rw [leviO_zero, add_zero]; exact hstr x0 ho z hz ξ)
      (fun z hz ξ hξ => Xa.posL x0 hx0d z hz ξ hξ) k1 k2 k3
  obtain ⟨hF0, hInAt, hloc⟩ :=
    GlobalTheory.KronValue.value_and_integrability hV r X G Xa.L Fl.w0 Fl.s (fun _ => 0) x0 bb ε (2 * ε) χ F hn
      ho hw0b hsb hψc hψb hbb0 hε hball hχc hχ1 hχ0 hF hint k1 k2 k3
  obtain ⟨P, hP, hPF⟩ := hExt r X x0 ho G F hF hloc
  have h0 : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [IW.cpt_zero]; exact hx0d
  have hP0 : P x0 = 1 := by
    have := hPF 0 h0
    rwa [IW.cpt_zero, hF0] at this
  refine ⟨x0, _, F, P, ho, hMW, hWL, hF, hInAt, hP, hPF, ?_, ?_⟩
  · rw [hx0, hP.2 x0 hx0d b0 hb0, hP0, mul_one]
    exact OntoE.bchar_ne X _ hb0
  · intro γ hγ j' hne
    obtain ⟨x1, ho1, b1, hb1, b1', hb1', hx1, hx1'⟩ := KronAssembly.exists_orth X (Fl.xs_mem j') hγ
    have hx1d : x1 ∈ X.dom := IW.orth_mem_dom X x1 ho1
    obtain ⟨l1, l2, l3⟩ := key j' γ hγ b1' hb1' x1 hx1'
    have hP1 : P x1 = 0 := by
      refine GlobalTheory.KronOff.vanish_off hMI hV hN r X G Xa.L Fl.w0 Fl.s (fun _ => 0) x0 x1 bb (2 * ε) χ F P
        hn ho ho1 hw0 hs hψc (fun _ _ _ _ => rfl) hbb0 hball hχ0 hP hPF hint ?_ l1 l2 l3
      intro z hz b hb hxz
      have hz0 : z = 0 := by
        refine hiso z hz fun k => ?_
        have h1 := l2 k
        rw [hxz, (hs k).2.1 _ (hball hz) b hb] at h1
        exact (mul_eq_zero.mp h1).resolve_left (OntoE.bchar_ne X _ hb)
      rw [hz0, IW.cpt_zero] at hxz
      rw [FundSetPf.lact_one] at hx0'
      have hc : rmul b0' (rmul b b1) ∈ Bor X.Ψ r := ExtFPf.mul_mem X hb0' (ExtFPf.mul_mem X hb hb1)
      have he : lact γ (Fl.xs j') = rmul (Fl.xs j) (rmul b0' (rmul b b1)) := by
        rw [hx1, hxz, ← ExtFPf.rmul_assoc X (Fl.xs j) b0', ← hx0', ExtFPf.rmul_assoc]
      have hjj : j = j' := by
        refine Fl.xs_inj j j' γ⁻¹ (X.Γ.inv_mem hγ) _ hc ?_
        rw [← he, FundSetPf.lact_inv]
      subst hjj
      have hγ1 : γ = 1 := X.Γ_free γ hγ _ (Fl.xs_mem j) _ hc he
      rcases hne with h | h
      · exact h hγ1
      · exact h rfl
    rw [hx1, hP.2 x1 hx1d b1 hb1, hP1, mul_zero]

theorem interp_weight : (NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) → PoinStatement (E := E) → ExtFStatement (E := E) → MeasInvStatement (E := E) → VanishAtSStatement (E := E) → KapGGStatement (E := E) →
    ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r), PropDisc X →
    (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
      ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
        m * leviRh X x0 z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
          (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∃ η : ℝ, 0 < η ∧ ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      2 * η * leviO X x0 (phla X Xa.L) z ξ ≤ leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ) →
    (∀ P, X.IsBddSec G P → P ∈ X.SS G) →
    ∀ v : Fin Fl.δ → ℂ, ∃ F ∈ X.SSgt G 0, ∀ j, F (Fl.xs j) = v j := by
  intro hN hPo hExt hMI hV hK r X Xa Fl G hPD ⟨bb, m, hbb, hbm, hmar⟩ ⟨η, hη, hstr⟩ hcusp
  apply interp_of_kron X G Fl.xs
  intro j
  obtain ⟨x0, W, F, P, hx0, hW, hWl, hF, hA, hBE, hPF, hne, hz⟩ :=
    core hN hExt hMI hV hK X Xa Fl G bb m η hbb hbm hη hmar hstr j
  obtain ⟨-, hQ, -⟩ := hPo r X x0 hx0 hPD G W bb hW hWl hbb F P hF hA hBE hPF
  have hQne : poin X G P (Fl.xs j) ≠ 0 := by
    rw [poin_single X G P _ X.Γ.one_mem fun γ hγ hne' => hz γ hγ j (Or.inl hne')]
    exact mul_ne_zero (inv_ne_zero (KronAssembly.chi_ne_zero X G X.Γ.one_mem)) hne
  have hQz : ∀ j', j' ≠ j → poin X G P (Fl.xs j') = 0 := fun j' hj' =>
    poin_zero X G P _ fun γ hγ => hz γ hγ j' (Or.inr hj')
  have hQs : poin X G P ∈ X.SSgt G 0 := ss_sub_ssgt0 X G (hcusp _ hQ)
  obtain ⟨-, -, ⟨-, -, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X G G 0
  refine ⟨(poin X G P (Fl.xs j))⁻¹ • poin X G P, hsmul _ _ hQs, fun j' => ?_⟩
  by_cases h : j' = j
  · subst h
    simp [hQne]
  · simp [h, hQz j' h]

end GlobalTheory.InterpWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LeMulPowOfExpDecay
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem le_mul_pow_of_exp_decay {c c₁ l φ K K' nF s : ℝ} (T : ℕ) (hc : 0 ≤ c₁) (hl : 0 ≤ l)
    (hnF : nF ≤ K * Real.exp (-2 * Real.pi * c₁ / l)) (hK' : Real.exp (-(2 * c * φ)) ≤ K' * s)
    (hp : (T : ℝ) * c * φ ≤ c₁ / l) : nF ≤ max K 0 * K' ^ T * s ^ T := by
  have hq : 0 ≤ c₁ / l := div_nonneg hc hl
  have h1 : Real.exp (-2 * Real.pi * c₁ / l) ≤ Real.exp (-(2 * c * φ)) ^ T := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have e : -2 * Real.pi * c₁ / l = -2 * Real.pi * (c₁ / l) := by ring
    rw [e]
    nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-(2 * c * φ)) ^ T ≤ (K' * s) ^ T :=
    pow_le_pow_left₀ (Real.exp_pos _).le hK' T
  calc nF ≤ K * Real.exp (-2 * Real.pi * c₁ / l) := hnF
    _ ≤ max K 0 * Real.exp (-2 * Real.pi * c₁ / l) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max K 0 * (K' * s) ^ T := mul_le_mul_of_nonneg_left (h1.trans h2) (le_max_right _ _)
    _ = max K 0 * K' ^ T * s ^ T := by rw [mul_pow, mul_assoc]

theorem sum_pnorm_w_sq_pos {r : ℕ} {X : Data E r} (Xa : ArchInM X) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
  obtain ⟨K, hK⟩ := Xa.p3
  have h0 : 0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rcases eq_or_lt_of_le h0 with h | h
  · have h1 := hK x hx
    rw [← h, mul_zero] at h1
    exact absurd h1 (not_le.mpr (Real.exp_pos _))
  · exact h

theorem highModes_le_pow_w : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X), ∀ F ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1,
    (∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (Xa.Fp + Xa.T • Xa.L) F x ^ 2 ≤ C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ Xa.T) ∧
    ∀ x0 FF, IsFundSet X x0 FF → muF X x0 FF < ⊤ →
      ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) F (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0 < ⊤ := by
  intro r X Xa F hF
  obtain ⟨K, hK⟩ := cuspidalDecay_holds r X _ F Xa.c1 Xa.frame_theta_const_pos.le hF
  obtain ⟨K', hK'⟩ := Xa.p3
  have hbd : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + Xa.T • Xa.L) F x ^ 2 ≤
      (max K 0 * K' ^ Xa.T) * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ Xa.T := by
    intro x hx
    have hl := MinimumGrowthBounds.minimumSq_nonneg X hx
    have hp := Xa.p2 x hx
    rw [Data.la1, Real.sq_sqrt hl] at hp
    exact le_mul_pow_of_exp_decay Xa.T Xa.frame_theta_const_pos.le hl (hK x hx) (hK' x hx) hp
  refine ⟨⟨_, hbd⟩, fun x0 FF hFF hfin => ?_⟩
  calc ∫⁻ z in FF, ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) F (cpt X x0 z) ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) (cpt X x0 z) ^ 2) ^ (-(Xa.T : ℝ))) ∂muF X x0
      ≤ ∫⁻ _ in FF, ENNReal.ofReal (max K 0 * K' ^ Xa.T) ∂muF X x0 := by
        refine setLIntegral_mono' hFF.1 fun z hz => ENNReal.ofReal_le_ofReal ?_
        have hx : cpt X x0 z ∈ X.dom := hFF.2.1 hz
        have hs := sum_pnorm_w_sq_pos Xa hx
        rw [Real.rpow_neg hs.le, Real.rpow_natCast, ← div_eq_mul_inv, div_le_iff₀ (pow_pos hs _)]
        exact hbd _ hx
    _ = ENNReal.ofReal (max K 0 * K' ^ Xa.T) * muF X x0 FF := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFSublevelLtTop
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.SublevelFin

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isClosed_isOrth {r : ℕ} (X : Data E r) : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
  have e : {x : Frame X.Ψ r | IsOrth X x} = ⋂ τ : X.Ψ, {x | gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)} := by
    ext x; simp [IsOrth]
  rw [e]
  refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
  have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
  simp only [FrameDegreeData.gram_eq]
  exact (hm.matrix_transpose.matrix_mul continuous_const).matrix_mul
    (hm.matrix_map Complex.continuous_conj)

theorem entry_sq_le {r : ℕ} (X : Data E r) {x0 x : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (τ : X.Ψ) (i j : Fin r) :
    ‖((mat x0 τ)⁻¹ * mat x τ) i j‖ ^ 2 ≤ ((r : ℝ) + 1) *
      ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 := by
  have h := sumBd_entry_bound (FrameSumBound.isUpq_frame X h0 hx τ)
    ((FrameSumBound.swapIdx X.p0_le).symm i) ((FrameSumBound.swapIdx X.p0_le).symm j)
  have hm : ∀ M : Matrix (Fin r) (Fin r) ℂ,
      lminor M (⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ : Fin (r + 1)) =
        (M.submatrix (FrameSumBound.swapIdx X.p0_le)
          (FrameSumBound.swapIdx X.p0_le)).toBlocks₂₂.det := fun M => by
    unfold lminor
    congr 1
  rw [Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Nat.sub_add_cancel X.p0_le, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ← hm] at h
  exact h

theorem minor_sq_le {r : ℕ} (X : Data E r) {x0 x b : Frame X.Ψ r} (h0 : IsOrth X x0)
    (hx : IsOrth X x) (hb : b ∈ Bor X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (he : cpt X x0 z = rmul x b) {a : ℝ} (ha : rhF X x0 z ≤ a) (τ : X.Ψ) :
    ‖lminor ((mat x0 τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ 2 ≤ Real.exp a := by
  classical
  have h := (FramePotential.frame_potential_basic r X x0 h0).2.2.2 z hz
  rw [he] at h
  simp only [FramePotential.factor_rmul X x0 x hb, FramePotential.norm_dmin_of_isOrth X hx,
    one_div, Finset.prod_inv_distrib, Real.exp_neg, inv_inj] at h
  refine le_trans ?_ (h.le.trans (Real.exp_le_exp.2 ha))
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  refine le_mul_of_one_le_right (by positivity) ?_
  exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun _ _ => one_le_mul_of_one_le_of_one_le)
    le_rfl fun σ _ => FramePotential.one_le_minor_of_isOrth X h0 hx σ

theorem muF_sublevel_lt_top : MeasInvStatement (E := E) → ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ a : ℝ,
    muF X x0 {z | rhF X x0 z ≤ a} < ⊤ := by
  intro hI r X x0 h0 a
  set M : ℝ := Real.sqrt (((r : ℝ) + 1) * Real.exp a) with hM
  have hc : Continuous fun g : Frame X.Ψ r => rmul x0 g := by
    refine continuous_pi fun τ => ?_
    have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact continuous_const.matrix_mul hm
  have hK : IsCompact ((fun g : Frame X.Ψ r => rmul x0 g) '' Metric.closedBall 0 M ∩
      {x | IsOrth X x}) :=
    ((isCompact_closedBall _ _).image hc).inter_right (isClosed_isOrth X)
  have hfin := SatFin.muF_sat_lt_top hI r X x0 h0 _ hK fun x hx => IW.orth_mem_dom X x hx.2
  have hnull : muF X x0 (OmF X x0)ᶜ = 0 := by
    unfold muF
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (OntoB.isOpen_OmF X x0).measurableSet.compl]
    simp
  refine lt_of_le_of_lt (measure_mono (t := sat X x0 _ ∪ (OmF X x0)ᶜ) fun z ha => ?_)
    (measure_union_lt_top hfin (by rw [hnull]; exact ENNReal.zero_lt_top))
  by_cases hz : z ∈ OmF X x0
  swap
  · exact Or.inr hz
  obtain ⟨x, hx, b, hb, he⟩ := ortho_holds r X _ hz
  refine Or.inl ⟨hz, x, ⟨⟨fun τ i j => ((mat x0 τ)⁻¹ * mat x τ : Matrix (Fin r) (Fin r) ℂ) i j, ?_, ?_⟩, hx⟩,
    b, hb, he⟩
  · have hM0 : 0 ≤ M := Real.sqrt_nonneg _
    refine mem_closedBall_zero_iff.2 ?_
    refine (pi_norm_le_iff_of_nonneg hM0).2 fun τ => (pi_norm_le_iff_of_nonneg hM0).2 fun i =>
      (pi_norm_le_iff_of_nonneg hM0).2 fun j => ?_
    refine Real.le_sqrt_of_sq_le ((entry_sq_le X h0 hx τ i j).trans ?_)
    exact mul_le_mul_of_nonneg_left (minor_sq_le X h0 hx hb hz he ha τ) (by positivity)
  · funext τ
    have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (ExF.det_ne_of_orth X h0 τ)
    exact Matrix.mul_nonsing_inv_cancel_left (mat x0 τ) (mat x τ) hu

end GlobalTheory.SublevelFin
end

