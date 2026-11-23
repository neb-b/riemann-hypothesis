module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingSetEtaleStein
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nzStein_germ {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    -Real.log (A.nsq Λ τ y) = (A.ph Λ i y + 0) + Real.log (‖(τ i y)⁻¹‖ ^ 2) := by
  rw [A.nsq_eq_chart hs hy]
  have h1 : ‖τ i y‖ ^ 2 ≠ 0 := by positivity
  rw [Real.log_mul h1 (Real.exp_pos _).ne', Real.log_exp, norm_inv, inv_pow, Real.log_inv]
  ring

theorem nzStein_smoothLog {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm) (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) := by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hlog := ((hτc.inv hne).norm_sq ℝ).log (by simpa using hne)
  simpa [Function.comp_def] using hlog

theorem nzStein_smooth {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    {Λ : La} {τ : ι → Y → ℂ} (hs : A.IsSec Λ τ) (i : ι) {y : Y}
    (hy : y ∈ (A.chart i).source) (hτ : τ i y ≠ 0) :
    ContDiffAt ℝ ∞ ((fun x => (A.ph Λ i x + 0) + Real.log (‖(τ i x)⁻¹‖ ^ 2)) ∘ (A.chart i).symm)
      (A.chart i y) := by
  have hT : (A.chart i).target ∈ 𝓝 (A.chart i y) :=
    (A.chart i).open_target.mem_nhds ((A.chart i).map_source hy)
  have hph : ContDiffAt ℝ ∞ (A.ph Λ i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph Λ i).contDiffAt hT
  have hd : DifferentiableOn ℂ (τ i ∘ (A.chart i).symm) (A.chart i).target := by
    simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 i
  have hτc : ContDiffAt ℝ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
    by
    have h : ContDiffAt ℂ ∞ (τ i ∘ (A.chart i).symm) (A.chart i y) :=
      (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.chart i).open_target hd).contDiffAt hT
    exact h.restrict_scalars ℝ
  have hne : (τ i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simpa [(A.chart i).left_inv hy] using hτ
  have hinv : ContDiffAt ℝ ∞ (fun v => ((τ i ∘ (A.chart i).symm) v)⁻¹) (A.chart i y) :=
    hτc.inv hne
  have hsq : ContDiffAt ℝ ∞ (fun v => ‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2) (A.chart i y) :=
    hinv.norm_sq ℝ
  have hlog : ContDiffAt ℝ ∞ (fun v => Real.log (‖((τ i ∘ (A.chart i).symm) v)⁻¹‖ ^ 2))
      (A.chart i y) :=
    hsq.log (by simpa using hne)
  exact (hph.add contDiffAt_const).add (by simpa [Function.comp_def] using hlog)

end GlobalTheory

namespace GlobalTheory

theorem nzEtaleStein : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n), A.IsSec Λ τ → A.Pos Λ (fun _ => 0) → Etale A (nz A τ) z → ∃ X : EtaleStein n (nz A τ), X.z = (fun y : nz A τ => z y) ∧ X.e = fun y : nz A τ => -Real.log (A.nsq Λ τ y) := by
  intro n Y _ _ _ _ _ _ ι La _ A Λ τ z hs hpos hE

  have hW : ∀ x ∈ nz A τ, ∀ᶠ y in 𝓝 x, (fun y => -Real.log (A.nsq Λ τ y)) y =
      (fun y => (A.ph Λ (A.pick x) y + 0) + Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) y := by
    intro x hx
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    filter_upwards [hO.mem_nhds ⟨A.mem_pick x, hx⟩] with y hy
    exact nzStein_germ A hs (A.pick x) hy.1 hy.2
  have hT : ∀ x, Tendsto (A.chart (A.pick x)).symm (𝓝 (A.chart (A.pick x) x)) (𝓝 x) := by
    intro x
    have := (A.chart (A.pick x)).continuousAt_symm ((A.chart (A.pick x)).map_source (A.mem_pick x))
    rwa [ContinuousAt, (A.chart (A.pick x)).left_inv (A.mem_pick x)] at this
  have hsm : ∀ x ∈ nz A τ, ContDiffAt ℝ ∞
      ((fun y => -Real.log (A.nsq Λ τ y)) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) := by
    intro x hx
    refine (nzStein_smooth A hs (A.pick x) (A.mem_pick x) hx).congr_of_eventuallyEq ?_
    filter_upwards [(hT x).eventually (hW x hx)] with v hv
    exact hv
  have hlev : ∀ x ∈ nz A τ, ∀ ξ : Fin n → ℂ,
      0 ≤ A.leviAt (A.pick x) (fun y => -Real.log (A.nsq Λ τ y)) x ξ := by
    intro x hx ξ
    have hxi : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
    rw [leviAt_congr A (A.pick x) _ _ x hxi (hW x hx) ξ]
    have hT' : (A.chart (A.pick x)).target ∈ 𝓝 (A.chart (A.pick x) x) :=
      (A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi)
    have hf : ContDiffAt ℝ 2 ((fun y => A.ph Λ (A.pick x) y + 0) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) := by
      have : ContDiffAt ℝ ∞ (A.ph Λ (A.pick x) ∘ (A.chart (A.pick x)).symm) (A.chart (A.pick x) x) :=
        (A.smooth_ph Λ (A.pick x)).contDiffAt hT'
      exact (this.add contDiffAt_const).of_le (WithTop.coe_le_coe.mpr le_top)
    have hg : ContDiffAt ℝ 2
        ((fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      (nzStein_smoothLog A hs (A.pick x) hxi hx).of_le (WithTop.coe_le_coe.mpr le_top)
    have hd : DifferentiableOn ℂ (τ (A.pick x) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x)).target := by
      simpa [WeightedAtlas.IsSec, WeightedAtlas.IsSecOn] using hs.1 (A.pick x)
    have hO : IsOpen ((A.chart (A.pick x)).source ∩ τ (A.pick x) ⁻¹' {0}ᶜ) :=
      (A.continuousOn_sec hs (A.pick x)).isOpen_inter_preimage (A.chart (A.pick x)).open_source
        isOpen_compl_singleton
    have hh : ∀ᶠ v in 𝓝 (A.chart (A.pick x) x),
        DifferentiableAt ℂ ((fun y => (τ (A.pick x) y)⁻¹) ∘ (A.chart (A.pick x)).symm) v := by
      filter_upwards [(A.chart (A.pick x)).open_target.mem_nhds ((A.chart (A.pick x)).map_source hxi),
        (hT x).eventually (hO.mem_nhds ⟨hxi, hx⟩)] with v hv1 hv2
      exact (hd.differentiableAt ((A.chart (A.pick x)).open_target.mem_nhds hv1)).inv hv2.2
    have E1 := leviAt_add A (A.pick x) (fun y => A.ph Λ (A.pick x) y + 0)
      (fun y => Real.log (‖(τ (A.pick x) y)⁻¹‖ ^ 2)) x hf hg ξ
    have E2 := leviAt_log_normSq A (A.pick x) (fun y => (τ (A.pick x) y)⁻¹) x hxi hh (inv_ne_zero hx) ξ
    have hp := hpos (A.pick x) x hxi ξ
    simp only at E1 E2 hp
    rw [E1, E2]
    linarith
  have hLH : IsLocalHomeomorph (fun y : nz A τ => z y) := _root_.GlobalTheory.OTY.etale_isLocalHomeomorph n Y ι La A _ z hE
  have hSm : SmoothR n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    (_root_.GlobalTheory.OTY.smooth_etale_of_smooth_in_charts n Y ι La A _ z hE).2 (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx⟩)
  have hLv : LeviNonneg n (fun y : nz A τ => z y) (fun y : nz A τ => -Real.log (A.nsq Λ τ y)) :=
    _root_.GlobalTheory.OTY.etale_leviNonneg n Y ι La A _ z hE (fun y => -Real.log (A.nsq Λ τ y))
      (fun x hx => ⟨A.pick x, A.mem_pick x, hsm x hx, hlev x hx⟩)
  have hC : ∀ a : ℝ, IsCompact {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} := by
    intro a
    have hK : IsCompact {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} :=
      (isClosed_le continuous_const (A.continuous_nsq hs)).isCompact
    have hsub : {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} ⊆ nz A τ := by
      intro y hy
      show τ (A.pick y) y ≠ 0
      intro h0
      have h1 : Real.exp (-a) ≤ A.nsq Λ τ y := hy
      have h2 : A.nsq Λ τ y = 0 := by simp [WeightedAtlas.nsq, h0]
      have := Real.exp_pos (-a)
      linarith
    have heq : {y : nz A τ | -Real.log (A.nsq Λ τ y) ≤ a} =
        Subtype.val ⁻¹' {y : Y | Real.exp (-a) ≤ A.nsq Λ τ y} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      have hne : τ (A.pick y) y ≠ 0 := hy
      have hp : 0 < A.nsq Λ τ y := by
        unfold WeightedAtlas.nsq
        positivity
      rw [neg_le, Real.le_log_iff_exp_le hp]
    rw [heq, Subtype.isCompact_iff, Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub)]
    exact hK
  exact ⟨⟨fun y => z y, hLH, fun y => -Real.log (A.nsq Λ τ y), hSm, hLv, hC⟩, rfl, rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupDualTangentLinearKillsIntegral
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O]

theorem eq_zero_of_forall_dvd [IsHausdorff (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ n : ℕ, (p : O) ^ n ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun n => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h n

variable {G : PDivGroup p O}

theorem exists_form (n : ℕ) (w : G.dual.omega) :
    ∃ φ : CartierDual O (G.A n), PDiv.dUnit (R := O) φ = w.1 n ∧ φ 1 = 0 := by
  obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 n)
  refine ⟨φ - algebraMap O _ (φ 1), ?_, ?_⟩
  · change AugCot.d _ (φ - algebraMap O _ (φ 1)) = _
    rw [map_sub, AugCot.d_algebraMap, sub_zero]
    exact hφ
  · have h1 : (algebraMap O (CartierDual O (G.A n)) (φ 1)) 1 = φ 1 := by
      rw [Algebra.algebraMap_eq_smul_one]
      change φ 1 * Coalgebra.counit (R := O) (1 : G.A n) = _
      rw [Bialgebra.counit_one, mul_one]
    change φ 1 - (algebraMap O (CartierDual O (G.A n)) (φ 1)) 1 = 0
    rw [h1, sub_self]

theorem lie_eq_zero [IsHausdorff (Ideal.span {(p : O)}) O] (l : G.dual.Lie)
    (h : ∀ (n : ℕ) (w : G.dual.omega) (φ : CartierDual O (G.A n)), PDiv.dUnit (R := O) φ = w.1 n →
      φ 1 = 0 → (p : O) ^ n ∣ l w) : l = 0 :=
  LinearMap.ext fun w => eq_zero_of_forall_dvd _ fun n => by
    obtain ⟨φ, hφ, h1⟩ := exists_form n w
    exact h n w φ hφ h1

variable {σ τ R : Type} [CommRing R] [Finite σ]

theorem constantCoeff_subst_of {a : σ → MvPowerSeries τ R} (ha0 : ∀ i, constantCoeff (a i) = 0)
    (f : MvPowerSeries σ R) : constantCoeff (subst a f) = constantCoeff f := by
  have hs := hasSubst_of_constantCoeff_zero ha0
  have hg : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  calc constantCoeff (subst a f)
      = constantCoeff (subst a (C (constantCoeff f) + (f - C (constantCoeff f)))) := by rw [← e]
    _ = constantCoeff f := by
      have hC : (C (constantCoeff f) : MvPowerSeries σ R) =
          algebraMap R (MvPowerSeries σ R) (constantCoeff f) := by
        rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha0 hg, add_zero,
        ← coe_substAlgHom hs, hC, AlgHom.commutes, MvPowerSeries.algebraMap_apply]
      simp

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_eq (n : ℕ) (a : Fin d → MvPowerSeries (Fin d) O)
    (ha0 : ∀ i, constantCoeff (a i) = 0) (hz : ∀ i, c.ev n (a i) = 0)
    (s : MvPowerSeries (Fin d) O) :
    ∃ y : G.A n, c.ev n (subst a s) = algebraMap O (G.A n) (constantCoeff s) + (p : O) ^ n • y := by
  have hs := hasSubst_of_constantCoeff_zero ha0
  obtain ⟨N, hN⟩ := (c.isEval n).2 n
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N) s with hP
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N →
      coeff α (subst a (s - (P : MvPowerSeries (Fin d) O))) = 0 := by
    have h1 : (N : ℕ∞) ≤ (s - (P : MvPowerSeries (Fin d) O)).order := by
      refine nat_le_order fun α hα => ?_
      rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
      intro i
      have : α i ≤ α.degree := Finsupp.le_degree i α
      have h' : (Finsupp.equivFunOnFinite.symm fun _ : Fin d => N) i = N := by simp
      rw [h']
      omega
    have h2 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
      le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha0 i)
    have h3 := le_order_subst hs (s - (P : MvPowerSeries (Fin d) O))
    intro α hα
    apply coeff_of_lt_order
    calc (α.degree : ℕ∞) < N := by exact_mod_cast hα
      _ = 1 * (N : ℕ∞) := (one_mul _).symm
      _ ≤ (⨅ i, (a i).order) * (s - (P : MvPowerSeries (Fin d) O)).order := mul_le_mul' h2 h1
      _ ≤ _ := h3
  obtain ⟨y, hy⟩ := hN _ hT
  refine ⟨y, ?_⟩
  have e : subst a s = subst a (P : MvPowerSeries (Fin d) O) +
      subst a (s - (P : MvPowerSeries (Fin d) O)) := by
    rw [← subst_add hs, add_sub_cancel]
  have hz' : (fun i => c.ev n (a i)) = 0 := funext hz
  rw [e, map_add (f := _), subst_coe, ← AlgHom.comp_apply, MvPolynomial.comp_aeval, hy, hz',
    MvPolynomial.aeval_zero, Algebra.smul_def, map_pow, map_natCast, MvPolynomial.constantCoeff_eq,
    hP, coeff_trunc', if_pos (by simp), coeff_zero_eq_constantCoeff_apply]

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)
  {E : Type} [CommRing E] [Algebra O E]

theorem lie_eq_zero_of_integral [IsHausdorff (Ideal.span {(p : O)}) O]
    (hz : ∀ n i, c.ev n (nmul c.μ (p ^ n) i) = 0) (s0 : MvPowerSeries (Fin d) O)
    (l : G.dual.Lie) (h : c.IsLie (map (algebraMap O E) s0) l) : l = 0 := by
  refine lie_eq_zero l fun n w φ hφ h1 => ?_
  have ha0 : ∀ i, constantCoeff (nmul c.μ (p ^ n) i) = 0 :=
    QLogDefect.constantCoeff_nmul c.isLaw.const _
  have hs := hasSubst_of_constantCoeff_zero ha0
  have hD : map (algebraMap O E) (((p ^ n : ℕ) : O) • s0 - subst (nmul c.μ (p ^ n)) s0) =
      defect c.μ (p ^ n) (map (algebraMap O E) s0) := by
    rw [defect, map_sub, map_subst hs]
    congr 1
    ext α
    simp [coeff_map]
  have h2 := h.2 n w φ _ hφ hD
  obtain ⟨y, hy⟩ := ev_subst_eq c n _ ha0 (hz n) s0
  have hφa : ∀ k : O, φ (algebraMap O (G.A n) k) = 0 := fun k => by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
  have e : φ (c.ev n (((p ^ n : ℕ) : O) • s0 - subst (nmul c.μ (p ^ n)) s0)) =
      (p : O) ^ n * (φ (c.ev n s0) - φ y) := by
    rw [map_sub, map_smul, hy, map_sub, map_smul, map_add (f := _), map_smul, hφa, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e] at h2
  have h3 := dvd_add h2 (dvd_mul_right ((p : O) ^ n) (φ (c.ev n s0) - φ y))
  rwa [sub_add_cancel] at h3

theorem quasiLogarithmDefect_eq_zero_of_coboundary (f : MvPowerSeries (Fin d) E) (hf : cob1 (up E c.μ) f = 0) (k : ℕ) :
    defect c.μ k f = 0 := by
  have hμ := c.isLaw.const
  have hM : ∀ j, constantCoeff (up E c.μ j) = 0 := fun j => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ j,
      map_zero]
  have hc : constantCoeff f = 0 := by
    have h := congrArg constantCoeff hf
    rw [cob1, inL, inR, map_sub, map_sub, constantCoeff_subst_of hM,
      constantCoeff_subst_of (fun _ => constantCoeff_X _),
      constantCoeff_subst_of (fun _ => constantCoeff_X _), map_zero] at h
    linear_combination -h
  induction k with
  | zero =>
    have h0 : up E (nmul c.μ 0) = 0 := by funext i; simp [up, nmul]
    rw [defect, h0, Nat.cast_zero, zero_smul, zero_sub, subst_zero_of_constantCoeff_zero hc,
      neg_zero]
  | succ k ih =>
    rw [QLogDefect.defect_succ c.μ hμ k f, ih, hf]
    have hE : ∀ j, constantCoeff (Sum.elim (up E (nmul c.μ k))
        (fun i => (X i : MvPowerSeries (Fin d) E)) j) = 0 := by
      rintro (j | j)
      · simp only [Sum.elim_inl, up]
        rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
          QLogDefect.constantCoeff_nmul hμ k j, map_zero]
      · simp
    rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero hE), map_zero, sub_zero]

theorem lie_eq_zero_of_cob1 [IsHausdorff (Ideal.span {(p : O)}) O] (f : MvPowerSeries (Fin d) E)
    (hf : cob1 (up E c.μ) f = 0) (l : G.dual.Lie) (h : c.IsLie f l) : l = 0 := by
  refine lie_eq_zero l fun n w φ hφ _ => ?_
  have h2 := h.2 n w φ 0 hφ (by rw [map_zero, quasiLogarithmDefect_eq_zero_of_coboundary c f hf])
  rwa [map_zero, map_zero, sub_zero] at h2

theorem exists_of_in {σ : Type} {f : MvPowerSeries σ E} (h : In (⊤ : Ideal O) f) :
    ∃ s : MvPowerSeries σ O, map (algebraMap O E) s = f := by
  choose b _ hb using h
  refine ⟨(show MvPowerSeries σ O from fun α => b α), ?_⟩
  ext α
  rw [coeff_map, hb α]
  rfl

theorem defect_add_smul (f g : MvPowerSeries (Fin d) E) (a : E) (k : ℕ) :
    defect c.μ k (f + a • g) = defect c.μ k f + a • defect c.μ k g := by
  have hU : ∀ j, constantCoeff (up E (nmul c.μ k) j) = 0 := fun j => by
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      QLogDefect.constantCoeff_nmul c.isLaw.const _ j, map_zero]
  have hsub := hasSubst_of_constantCoeff_zero hU
  simp only [defect]
  rw [subst_add hsub, subst_smul hsub, smul_add, smul_sub, smul_comm ((k : ℕ) : E) a g]
  abel

theorem isLie_add_smul (hinj : Function.Injective (algebraMap O E))
    {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (a : O)
    (hf : c.IsLie f l) (hg : c.IsLie g l') :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') := by
  have hmap : ∀ sf sg : MvPowerSeries (Fin d) O, map (algebraMap O E) (sf + a • sg) =
      map (algebraMap O E) sf + algebraMap O E a • map (algebraMap O E) sg := fun sf sg => by
    ext α
    simp [coeff_map]
    exact (Algebra.smul_def _ _).symm
  refine (c.isLie_iff hinj _ _).2 fun n => ?_
  obtain ⟨sf, hsf⟩ := exists_of_in (hf.1 n)
  obtain ⟨sg, hsg⟩ := exists_of_in (hg.1 n)
  refine ⟨sf + a • sg, by rw [hmap, defect_add_smul, hsf, hsg], fun w φ hφ => ?_⟩
  have h1 := hf.2 n w φ sf hφ hsf
  have h2 := hg.2 n w φ sg hφ hsg
  rw [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, map_add (f := _),
    map_smul, smul_eq_mul]
  have h3 := dvd_add h1 (dvd_mul_of_dvd_right h2 a)
  convert h3 using 1
  ring

theorem isLie_add [Fact p.Prime] (hF : IsFrame p E (RingHom.id O))
    (_hL : IsLift (RingHom.id O) c.μ) {f g : MvPowerSeries (Fin d) E} {l l' : G.dual.Lie} (a : O)
    (hf : c.IsLie f l) (hg : c.IsLie g l') (_qf : QL c.μ ⊤ f) (_qg : QL c.μ ⊤ g) :
    c.IsLie (f + algebraMap O E a • g) (l + a • l') :=
  isLie_add_smul c hF.inj a hf hg

end GlobalTheory.LieLin

namespace GlobalTheory.LieLin

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (f g : MvPowerSeries (Fin d) E) (l l' : G.dual.Lie) (a : O), c.IsLie f l → c.IsLie g l' → (QL c.μ ⊤ f → QL c.μ ⊤ g → c.IsLie (f + algebraMap O E a • g) (l + a • l')) ∧ ((∃ s : MvPowerSeries (Fin d) O, f = map (algebraMap O E) s) → l = 0) ∧ (cob1 (up E c.μ) f = 0 → l = 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF f g l l' a hf hg
  have hz : ∀ n i, c.ev n (nmul c.μ (p ^ n) i) = 0 := fun n i => GlobalTheory.chart_ev_nmul_pow_self p C v O hv G d c n i
  have hL : IsLift (RingHom.id O) c.μ :=
    ⟨c.isLaw.const, c.isLaw.unit, c.isLaw.comm, by simpa using c.isLaw⟩
  refine ⟨fun qf qg => isLie_add c hF hL a hf hg qf qg, ?_, fun h => lie_eq_zero_of_cob1 c f h l hf⟩
  rintro ⟨s, rfl⟩
  exact lie_eq_zero_of_integral c hz s l hf

end GlobalTheory.LieLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenomSumBoundOfLocalBounds
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds

theorem sumBound_of_local : ∀ {F : Type} [Field F] [NumberField F], Formalism.PairingDivisionLocalBalance.CESum → ∀ (k : ℕ) (z : ClassGroup (𝓞 F) → ℚ), 2 ≤ k → 16 ≤ finrank ℚ F * k →
    (∀ l : ℕ, l.Prime → cE z l ≤ finrank ℚ F * padicValNat l 2 + Formalism.PairingDivisionLocalBalance.mE l (finrank ℚ F * k)) → SumBound k z := by
  intro F _ _ hCE k z hk h16 hloc
  set f := finrank ℚ F with hf
  set X := f * k with hX
  have h2f : 2 * f ≤ X := by rw [hX, mul_comm 2 f]; exact Nat.mul_le_mul_left f hk

  have hvan : ∀ l : ℕ, l.Prime → X + 2 ≤ l → cE z l = 0 := by
    intro l hl hlX
    have hl2 : l ≠ 2 := by omega
    have hv : padicValNat l 2 = 0 := by
      rw [Nat.padicValNat_def]
      apply multiplicity_eq_zero_of_not_dvd
      intro h
      have := Nat.le_of_dvd (by norm_num : 0 < 2) h
      omega
    have hm : Formalism.PairingDivisionLocalBalance.mE l X = 0 := by
      unfold Formalism.PairingDivisionLocalBalance.mE
      rw [if_neg hl2, if_neg]
      intro hd
      have := Nat.le_of_dvd (by omega) hd
      omega
    have := hloc l hl
    rw [hv, hm] at this
    simpa using this
  set S : Finset Nat.Primes := (Finset.range (X + 2)).subtype Nat.Prime with hS
  have hsupp : (Function.support fun l : Nat.Primes => (cE z l : ℝ) * Real.log (l : ℕ)) ⊆ (S : Set Nat.Primes) := by
    intro l hl
    simp only [Function.mem_support] at hl
    rw [Finset.mem_coe, hS]
    refine (Finset.mem_subtype (p := Nat.Prime) (a := (l : {p : ℕ // p.Prime}))).2 (Finset.mem_range.2 ?_)
    by_contra hlt
    apply hl
    rw [hvan l l.2 (by omega)]
    simp
  refine ⟨S.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hsub : ∑ l ∈ S, (cE z l : ℝ) * Real.log (l : ℕ) =
      ∑ l ∈ (Finset.range (X + 2)).filter Nat.Prime, (cE z l : ℝ) * Real.log l :=
    Finset.sum_subtype_eq_sum_filter (f := fun l : ℕ => (cE z l : ℝ) * Real.log l) (s := Finset.range (X + 2))
  rw [hsub]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (hCE f X _ h16 h2f (fun l hl => (Finset.mem_filter.1 hl).2))
  have hlp := (Finset.mem_filter.1 hl).2
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hloc l hlp)
    (Real.log_nonneg (by exact_mod_cast hlp.one_lt.le))

end GlobalTheory.Proof.partialZetaDenomSumBound_of_local_bounds
end

