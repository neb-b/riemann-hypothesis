module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0007
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0008
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailInt
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Meas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem continuous_ac' : Continuous (ac E n) := by
  have hc : Continuous (splitCentre E n) := by
    have e : splitCentre E n = fun t : ℝ =>
        GeneralLinearGroup.scalar (Fin n) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
      funext GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar
    rw [e]
    refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
      (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
    change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin n => x
    exact (continuous_pi fun _ => continuous_id).matrix_diagonal
  exact (hc.comp (continuous_id.div_const _)).prodMk continuous_const

private theorem measurable_reduced_size : Measurable (r0 : H E n 0 → ℝ) := by
  have hc : Continuous fun x : H E n 0 => (ac E n (-ldet x) * x).1 :=
    continuous_fst.comp ((continuous_ac'.comp continuous_ldet.neg).mul continuous_id)
  haveI := borelSpace_H (E := E) (n := n)
  letI : MeasurableSpace (GA E n) := borel _
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact (redBasic E n).2.2.comp hc.measurable

private theorem measurable_cnt {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  set_option synthInstance.maxHeartbeats 200000 in
    have hm : MeasurableSet Ω := hΩ.measurableSet
    refine Measurable.tsum fun γ => ?_
    have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
      (continuous_inv.mul continuous_const).mul continuous_id
    exact (measurable_one.indicator hm).comp hc.measurable

end Meas

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailInt_of_bounds :
    GFac → GBound → Supp → DomInt → TailInt := by
  intro hF hB hS hD E _ _ _ n ι _ s
  haveI := borelSpace_H (E := E) (n := n)
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨Ω, hΩ, hC⟩ := hB E n ι s
  choose Cb hCb0 hCb using fun b => hC (p.x b)
  choose Nb hNb using fun b => hD E n s.pos s.D s.π s.fix (p.w b) (p.mem b) Ω hΩ
  refine ⟨Finset.univ.sup Nb, fun L hL => ?_⟩
  choose Db hDb0 hDb using fun b => hNb b L hL
  refine ⟨∑ b, Cb b * Db b, Finset.sum_nonneg fun b _ => mul_nonneg (hCb0 b) (hDb0 b),
    fun m R ρ hR hφ A hA => ?_⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R ∧ ρ ≤ r0 x} with hSdef
  have hSm : MeasurableSet S :=
    ((isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet).inter
      (measurableSet_le measurable_const measurable_reduced_size)
  set f : p.B → H E n 0 → ℝ≥0∞ := fun b =>
    S.indicator (fun x => ‖(p.w b).1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
  have hfm : ∀ b, Measurable (f b) := fun b => by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ (measurable_cnt hΩ)
    exact (((continuous_of_mem s.π (p.mem b)).comp continuous_fst).enorm).measurable
  have hpt : ∀ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ≤
      ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx : |ldet x| ≤ R
      · have hxS : x ∈ S := ⟨hx, hA x hxA hx⟩
        rw [hp m x x]
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [enorm_mul, hf]
        simp only [Set.indicator_of_mem hxS]
        calc ‖(p.w b).1 x.1‖ₑ * ‖m.G (ac E n (ldet x) * p.x b) x‖ₑ
            ≤ ‖(p.w b).1 x.1‖ₑ * (ENNReal.ofReal (Cb b * ‖m.U‖) * cnt (ratH E n 0) Ω x) := by
              gcongr; exact hCb b m _ x
          _ = _ := by ring
      · have h0 : m.G x x = 0 := by
          refine hS E n ι s m R hφ x x ?_
          have h1 : R < |ldet x| := not_le.mp hx
          have h2 : |ldet x + ldet x| = 2 * |ldet x| := by
            rw [← two_mul, abs_mul, abs_two]
          rw [h2]
          have := abs_nonneg (ldet x)
          linarith
        simp [h0]
    · rw [Set.indicator_of_notMem hxA]
      exact zero_le
  have h1R : (1 : ℝ) ≤ 1 + R := by linarith
  have hT : ∀ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν ≤
      ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
    intro b
    have hpow : (1 + R) ^ Nb b ≤ (1 + R) ^ (Finset.univ.sup Nb) :=
      pow_le_pow_right₀ h1R (Finset.le_sup (Finset.mem_univ b))
    have h2 : ∫⁻ x, f b x ∂s.D.ν ≤
        ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
      refine (hDb b R ρ hR).trans (ENNReal.ofReal_le_ofReal ?_)
      have := hDb0 b
      have he := (Real.exp_pos (-(L * ρ))).le
      gcongr
    calc _ ≤ ENNReal.ofReal (Cb b * ‖m.U‖) *
          ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (hCb0 b) (norm_nonneg _))]
        congr 1
        ring
  calc ∫⁻ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ∂s.D.ν
      ≤ ∫⁻ x, ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x ∂s.D.ν := lintegral_mono hpt
    _ = ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν := by
        rw [lintegral_finsetSum _ fun b _ => (hfm b).const_mul _]
        exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hfm b)
    _ ≤ ∑ b, ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) :=
        Finset.sum_le_sum fun b _ => hT b
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [Finset.sum_mul]
        · intro b _
          have := mul_nonneg (hCb0 b) (hDb0 b)
          have he := (Real.exp_pos (-(L * ρ))).le
          have hp1 : 0 ≤ (1 + R) ^ (Finset.univ.sup Nb) := by positivity
          positivity

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTailOf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

section SlopeTestRemainingChoices

open NumberField MeasureTheory GlobalTheory.CuspRep PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

private theorem mem_cut_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {τ : ℝ} (hτ : 0 ≤ τ)
    (x : GA E 0) : x ∈ cutSet E 0 τ := by
  have key : ∀ (k : ℕ), k = 0 → ∀ M : Matrix (Fin 0) (Fin k) E, degM x M = 0 := by
    intro k hk M
    subst hk
    exact degM_zero x M
  have hr : ∀ W : Submodule E (Fin 0 → E), Module.finrank E W = 0 := fun W =>
    Module.finrank_zero_of_subsingleton
  refine ⟨fun W => ?_, ?_⟩
  · rw [deg, key _ (hr W), hr W]
    simp [prof]
  · rw [deg, key _ (hr ⊤)]
    simpa using hτ

private theorem tail_num (c ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) (N k : ℕ) (ρ : ℝ) (hρ : 1 + (k : ℝ) ≤ ρ) :
    (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) ≤
      ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hρ0 : 0 ≤ ρ := by linarith
  set l := max 0 (-Real.log ε) with hl
  have hl0 : 0 ≤ l := le_max_left _ _
  have hl1 : -Real.log ε ≤ l := le_max_right _ _
  have h1 : 1 + c * ρ ≤ (1 + c) * (1 + ρ) := by nlinarith
  have h2 : (1 + ρ) ^ N ≤ N.factorial * Real.exp (1 + ρ) := by
    have := Real.pow_div_factorial_le_exp (1 + ρ) (by linarith) N
    rwa [div_le_iff₀' (by positivity)] at this
  have h3 : Real.exp (-(l * ρ)) ≤ ε ^ k := by
    have e : ε ^ k = Real.exp (k * Real.log ε) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log hε, Real.rpow_natCast]
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hl0 (by linarith : (0 : ℝ) ≤ ρ - k), mul_le_mul_of_nonneg_right hl1 hk]
  have h4 : Real.exp (-((1 + l) * ρ)) = Real.exp (-ρ) * Real.exp (-(l * ρ)) := by
    rw [← Real.exp_add]
    ring_nf
  have h5 : Real.exp (1 + ρ) * Real.exp (-ρ) = Real.exp 1 := by
    rw [← Real.exp_add]
    ring_nf
  calc (1 + c * ρ) ^ N * Real.exp (-((1 + l) * ρ))
      ≤ ((1 + c) * (1 + ρ)) ^ N * Real.exp (-((1 + l) * ρ)) := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) h1 N) (Real.exp_pos _).le
    _ = (1 + c) ^ N * ((1 + ρ) ^ N * Real.exp (-ρ)) * Real.exp (-(l * ρ)) := by
        rw [h4, mul_pow]
        ring
    _ ≤ (1 + c) ^ N * (N.factorial * Real.exp 1) * ε ^ k := by
        have h6 : (1 + ρ) ^ N * Real.exp (-ρ) ≤ N.factorial * Real.exp 1 := by
          calc (1 + ρ) ^ N * Real.exp (-ρ) ≤ (N.factorial * Real.exp (1 + ρ)) * Real.exp (-ρ) :=
                mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
            _ = N.factorial * Real.exp 1 := by rw [mul_assoc, h5]
        exact mul_le_mul (mul_le_mul_of_nonneg_left h6 (by positivity)) h3 (Real.exp_pos _).le (by positivity)

private theorem diff_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (f g : X → ℂ) (A : Set X)
    (hA : MeasurableSet A) (hf : Integrable f ν) (h : ∀ x, g x = f x - A.indicator f x) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∫⁻ x, A.indicator (fun x => ‖f x‖ₑ) x ∂ν ≤ ENNReal.ofReal B) :
    ‖∫ x, g x ∂ν - ∫ x, f x ∂ν‖ ≤ B := by
  have e : ∫ x, g x ∂ν - ∫ x, f x ∂ν = -∫ x, A.indicator f x ∂ν := by
    simp only [h]
    rw [integral_sub hf (hf.indicator hA)]
    ring
  rw [e, norm_neg]
  have h1 : ‖∫ x, A.indicator f x ∂ν‖ₑ ≤ ENNReal.ofReal B := by
    refine (enorm_integral_le_lintegral_enorm _).trans (le_trans (le_of_eq ?_) hb)
    refine lintegral_congr fun x => ?_
    exact enorm_indicator_eq_indicator_enorm ..
  rw [← ofReal_norm] at h1
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp h1

private theorem tail_main : UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Sizes → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.InCut → UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.TailInt →
    UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.DiagInt → DiscreteGroups.T1.G.CutTail2 := by
  intro hS hI hT hD E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  obtain ⟨c, hc, hsz⟩ := hS E n hn
  obtain ⟨c', hc', hcut⟩ := hI E n
  obtain ⟨N, hN⟩ := hT E n ι s
  obtain ⟨Ct, hCt, hbd⟩ := hN (1 + max 0 (-Real.log ε)) (by positivity)
  refine ⟨(c' + 1) * (2 + c + c ^ 2), fun C' hC' =>
    ⟨Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)), fun k U Uπ Φ t o pp ht => ?_⟩⟩
  let m : Mid s := ⟨U, Uπ, Φ, t, o, pp⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 + k) * (1 + r₀ + r₁) := ⟨_, rfl⟩
  have hρk : 1 + (k : ℝ) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hρ1 : 1 ≤ ρ := by linarith
  have hρr : 1 + (r₀ + k * r₁) ≤ ρ := by rw [hρdef]; nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = C' * ρ := ⟨_, rfl⟩
  have hτ0 : 0 ≤ τ := by rw [hτdef]; positivity
  have hR0 : 0 ≤ c * ρ := by positivity
  have hsupp : ∀ z, m.φ z ≠ 0 → |ldet z| ≤ c * ρ := fun z hz => by
    have h1 := (ht.toIsTest2.size z hz).1
    refine (hsz z).2.1.trans (mul_le_mul_of_nonneg_left ?_ hc)
    linarith
  let A : Set (H E n 0) := {x | x.1 ∉ cutSet E n τ}
  have hAm : MeasurableSet A := by
    have ho : IsOpen A := ((mahler_holds E n τ).1.preimage continuous_fst).isOpen_compl
    haveI : BorelSpace (H E n 0) := ⟨rfl⟩
    exact ho.measurableSet
  have hAρ : ∀ x ∈ A, |ldet x| ≤ c * ρ → ρ ≤ r0 x := fun x hx hl => by
    by_contra hlt
    refine hx (hcut τ x.1 ?_)
    have h1 := (hsz x).1
    have h2 : redSize x.1 ≤ ρ + c * (1 + c * ρ) := h1.trans (add_le_add (not_le.mp hlt).le
      (mul_le_mul_of_nonneg_left (by linarith) hc))
    have h3 : 1 + redSize x.1 ≤ (2 + c + c ^ 2) * ρ := by nlinarith [mul_nonneg hc (by linarith : (0 : ℝ) ≤ ρ - 1)]
    have hq : 0 ≤ (2 + c + c ^ 2) * ρ := by positivity
    calc c' * (1 + redSize x.1) ≤ c' * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_left h3 hc'
      _ ≤ (c' + 1) * ((2 + c + c ^ 2) * ρ) := mul_le_mul_of_nonneg_right (by linarith) hq
      _ = ((c' + 1) * (2 + c + c ^ 2)) * ρ := by ring
      _ ≤ C' * ρ := mul_le_mul_of_nonneg_right hC' (by linarith)
      _ = τ := hτdef.symm
  have hb := hbd m (c * ρ) ρ hR0 hsupp A hAρ
  have hB : 0 ≤ Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ)) := by positivity
  have hmain := diff_le D.ν (lInt0 D k₁ k₂ Uπ) (lInt D k₁ k₂ τ Uπ) A hAm (hD E n ι s m) (fun x => by
      have h2 : chiT τ x.2 = (1 : ℂ) := Set.indicator_of_mem (mem_cut_zero hτ0 x.2) _
      by_cases hx : x.1 ∈ cutSet E n τ
      · have h1 : chiT τ x.1 = (1 : ℂ) := Set.indicator_of_mem hx _
        have h3 : x ∉ A := fun h => h hx
        simp [lInt, lInt0, h1, h2, h3]
      · have h1 : chiT τ x.1 = (0 : ℂ) := Set.indicator_of_notMem hx _
        have h3 : x ∈ A := hx
        simp [lInt, lInt0, h1, h2, h3]) _ hB hb
  rw [← hρdef, ← hτdef]
  refine hmain.trans ?_
  have hn' := tail_num c ε hc hε N k ρ hρk
  calc Ct * ‖U‖ * (1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))
      = Ct * ‖U‖ * ((1 + c * ρ) ^ N * Real.exp (-((1 + max 0 (-Real.log ε)) * ρ))) := by ring
    _ ≤ Ct * ‖U‖ * (((1 + c) ^ N * (N.factorial * Real.exp 1)) * ε ^ k) :=
        mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = Ct * ((1 + c) ^ N * (N.factorial * Real.exp 1)) * ‖U‖ * ε ^ k := by ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailOf_pf :
    Basic → Sizes → InCut → TailInt → DiagInt → DiscreteGroups.T1.G.CutTail2 := fun _ => tail_main
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PThetaInt
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory

private theorem twist_general {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (fd : IsFundamentalDomain Γ F μ) (θ : G →* G) (hc : Continuous θ) (hi : ∀ x, θ (θ x) = x)
    (hΓ : ∀ γ ∈ Γ, θ γ ∈ Γ) (f : G → ℂ) (hf : ∀ (γ : Γ) x, f ((γ : G) * x) = f x)
    (hI : Integrable f (μ.restrict F)) :
    Integrable (fun x => f (θ x)) (μ.restrict F) ∧
      ∫ x, f (θ x) ∂(μ.restrict F) = ∫ x, f x ∂(μ.restrict F) :=
  _root_.UpperTheory.Reformulated.B.Qh1.twist_general μ Γ fd θ hc hi hΓ f hf hI

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.thetaInt_pf :
    Basic → ThetaInt := by
  intro _ E _ _ _ n D f hf hI
  have hb := PositivityTheory.Rg.BcB.E1.thetaBasic_holds E
  let θ : PositivityTheory.Rg.BcB.E.H E n 0 →* PositivityTheory.Rg.BcB.E.H E n 0 :=
    (PositivityTheory.Rg.BcB.thetaA E n).prodMap (PositivityTheory.Rg.BcB.thetaA E 0)
  have hc : Continuous θ :=
    ((hb n).1.comp continuous_fst).prodMk ((hb 0).1.comp continuous_snd)
  have hi : ∀ x, θ (θ x) = x := fun x => Prod.ext ((hb n).2.1 x.1) ((hb 0).2.1 x.2)
  have hΓ : ∀ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0, θ γ ∈ PositivityTheory.Rg.BcB.E.ratH E n 0 := by
    rintro _ ⟨g, rfl⟩
    exact ⟨(PositivityTheory.Rg.BcB.thetaE E n g.1, PositivityTheory.Rg.BcB.thetaE E 0 g.2),
      Prod.ext ((hb n).2.2 g.1).symm ((hb 0).2.2 g.2).symm⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E 0
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E 0
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E n).2.1
  haveI := (PositivityTheory.Rg.BcB.E1.ratProper_holds E 0).2.1
  letI := PositivityTheory.Rg.BcB.E.borelH E n 0
  haveI : BorelSpace (PositivityTheory.Rg.BcB.E.H E n 0) := ⟨rfl⟩
  haveI : D.μ.IsHaarMeasure :=
    { toIsFiniteMeasureOnCompacts :=
        @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure _ _ _ D.μ D.haar.2.2.2
      toIsMulLeftInvariant := D.haar.1
      toIsOpenPosMeasure := D.haar.2.2.1 }
  haveI : Countable (PositivityTheory.Rg.BcB.E.ratH E n 0) :=
    (((GlobalTheory.CuspRep.ratGL E n).prodMap (GlobalTheory.CuspRep.ratGL E 0)).rangeRestrict_surjective).countable
  exact twist_general D.μ _ D.fd θ hc hi hΓ f hf hI
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTrFin
section
namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem trFin_pf : TrFin := by
  intro V B _ _ _ L w e h
  classical
  have hr : ∀ r : LinearMap.range L, (r : V) = ∑ b, e b (r : V) • w b := by
    rintro ⟨_, v, rfl⟩
    exact h v
  let A : LinearMap.range L →ₗ[ℂ] (B → ℂ) :=
    LinearMap.pi fun b => (e b).comp (LinearMap.range L).subtype
  let c : (B → ℂ) →ₗ[ℂ] LinearMap.range L :=
    L.rangeRestrict.comp (Fintype.linearCombination ℂ w)
  have hA : Function.Injective A := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr0
    apply Subtype.ext
    rw [hr r]
    have hz : ∀ b, e b (r : V) = 0 := fun b => congrFun hr0 b
    simp [hz]
  haveI : FiniteDimensional ℂ (LinearMap.range L) := FiniteDimensional.of_injective A hA
  have hL : (L.restrict fun x _ => LinearMap.mem_range_self L x) = c ∘ₗ A := by
    ext r
    have h1 : (c (A r) : V) = L (∑ b, e b (r : V) • w b) := by
      simp [c, A, Fintype.linearCombination_apply]
    rw [LinearMap.comp_apply, h1, ← hr r]
    rfl
  rw [hL, LinearMap.trace_comp_comm', LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ B)]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp [c, A, Fintype.linearCombination_apply, Pi.single_apply, ite_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PUncutOf
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G
open MeasureTheory PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1 GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.uncutOf_pf :
    Basic → GFac → HalfTerm → RangeW → TrFin → DiscreteGroups.T1.G.UncutHalf := by
  intro hB hF hH hR hT E _ _ _ n hn D π hπ ι _ Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  let s : Su E n ι := ⟨D, π, Φ₁, Φ₂, T₁, T₂, M, k₁, k₂, hn, hπ, a1, a2, hfin, b1, b2, hv⟩
  let m : Mid s := ⟨U, Uπ, Φ, c1, c2, hpi⟩
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨hac, hmul, -⟩ := hB E n hn
  have hsum : lInt0 D k₁ k₂ Uπ = fun x => ∑ b, (p.w b).1 x.1 * m.G (ac E n (ldet x) * p.x b) x :=
    funext fun x => hp m x x
  have hterm := fun b => hH E n ι s m (p.w b) (p.mem b) (p.x b) (p.zero b)
  obtain ⟨L, hL, -, rfl⟩ := ht
  let w : p.B → π.V := fun b => ⟨p.w b, p.mem b⟩
  let e : p.B → (π.V →ₗ[ℂ] ℂ) := fun b =>
    { toFun := fun ψ => ψ.1.1 (p.x b).1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hcentre : ∀ (ψ : Sm E n), ψ ∈ π.V → ∀ g : GA E n,
      ψ.1 (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)).1 = ψ.1 g := by
    intro ψ hψ g
    exact hπ.1 ψ hψ _ g
  have hspan : ∀ v, L v = ∑ b, e b (L v) • w b := by
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    have h0 : ldet (ac E n (-ldet ((g, 1) : H E n 0)) * ((g, 1) : H E n 0)) = 0 := by
      rw [hmul, hac]; ring
    have h1 := hR E n ι s p hp m v.1 v.2 _ h0
    have h2 : (L v).1.1 g = ∑ b, (L v).1.1 (p.x b).1 * (p.w b).1 g := by
      rw [← hcentre (L v).1 (L v).2 g, hL v]
      refine h1.trans (Finset.sum_congr rfl fun b _ => ?_)
      rw [hcentre _ (p.mem b), hL v, mul_comm]
      rfl
    let ev : π.V →ₗ[ℂ] ℂ :=
      { toFun := fun ψ => ψ.1.1 g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have h3 : (∑ b, e b (L v) • w b).1.1 g = ev (∑ b, e b (L v) • w b) := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3, map_sum]
    exact h2
  have htr := hT π.V p.B L w e hspan
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum _ fun b _ => (hterm b).1
  · rw [hsum, integral_finsetSum _ fun b _ => (hterm b).1, htr, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(hterm b).2]
    congr 1
    exact (hL (w b) (p.x b).1).symm
end

