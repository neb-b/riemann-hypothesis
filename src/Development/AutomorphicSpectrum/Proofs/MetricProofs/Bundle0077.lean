module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithmeticVarietyGenericFibreProjective
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem varieties_over_rat_arith_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P :=
  @PositivityTheory.Xgp.t_contract

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BaseMetricVectorLogResolution
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens

def hline {Ψ : Type} {N : ℕ} (h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ) (s : ℂ) (τ' : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  (1 - s) • h₀ τ' + s • (1 : Matrix (Fin N) (Fin N) ℂ)

theorem finite_det_line {κ : Type} [Fintype κ] [DecidableEq κ] (A B : Matrix κ κ ℂ) (hB : B.det ≠ 0) :
    {s : ℂ | ((1 - s) • A + s • B).det = 0}.Finite := by
  let Q : Matrix κ κ (Polynomial ℂ) := fun a b =>
    (1 - Polynomial.X) * Polynomial.C (A a b) + Polynomial.X * Polynomial.C (B a b)
  have ev : ∀ s : ℂ, Q.det.eval s = ((1 - s) • A + s • B).det := by
    intro s
    have := RingHom.map_det (Polynomial.evalRingHom s) Q
    rw [Polynomial.coe_evalRingHom] at this
    rw [this]
    congr 1
    ext a b
    show Polynomial.eval s (Q a b) = _
    simp [Q]
    exact mul_comm _ _
  have hne : Q.det ≠ 0 := by
    intro h0
    have := ev 1
    rw [h0] at this
    simp at this
    exact hB this.symm
  refine (Q.det.roots.toFinset.finite_toSet).subset ?_
  intro s hs
  simp only [Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot.def, ev]
  exact hs

theorem minorIJ_self {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N)) :
    minorIJ h I I = (h.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)).det := by
  simp [minorIJ]

theorem det_submatrix_lowerUni {N : ℕ} {T : Matrix (Fin N) (Fin N) ℂ} (hT : IsLowerUni T) (I : Finset (Fin N)) :
    (T.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [hT.1]
  · intro a b hab
    exact hT.2 _ _ ((I.orderEmbOfFin rfl).strictMono hab)

theorem finite_minor_line {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (I : Finset (Fin N))
    (hB : (B.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)).det ≠ 0) :
    {s : ℂ | minorIJ ((1 - s) • A + s • B) I I = 0}.Finite := by
  refine (finite_det_line (A.submatrix (I.orderEmbOfFin rfl) (I.orderEmbOfFin rfl)) _ hB).subset ?_
  intro s hs
  simp only [Set.mem_setOf_eq, minorIJ_self] at hs ⊢
  rw [← hs]
  rfl

theorem exists_good_param {Ψ : Type} [Fintype Ψ] {N : ℕ} (h₀ T : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hT : ∀ τ', IsLowerUni (T τ')) (J : Fin N → Finset (Fin N)) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℂ, ‖s‖ < ε ∧ ∀ (τ' : Ψ) (i : Fin N), minorIJ (hline h₀ s τ') (J i) (J i) ≠ 0 ∧
      minorIJ (hline h₀ s τ' * T τ') (J i) (J i) ≠ 0 := by
  let bad : Set ℂ := ⋃ τ' : Ψ, ⋃ i : Fin N,
    ({s | minorIJ (hline h₀ s τ') (J i) (J i) = 0} ∪ {s | minorIJ (hline h₀ s τ' * T τ') (J i) (J i) = 0})
  have hfin : bad.Finite := by
    refine Set.finite_iUnion fun τ' => Set.finite_iUnion fun i => Set.Finite.union ?_ ?_
    · refine finite_minor_line (h₀ τ') 1 (J i) ?_
      rw [Matrix.submatrix_one _ ((J i).orderEmbOfFin rfl).injective, Matrix.det_one]
      exact one_ne_zero
    · have e : ∀ s : ℂ, hline h₀ s τ' * T τ' = (1 - s) • (h₀ τ' * T τ') + s • T τ' := by
        intro s
        simp [hline, add_mul]
      simp only [e]
      refine finite_minor_line (h₀ τ' * T τ') (T τ') (J i) ?_
      rw [det_submatrix_lowerUni (hT τ')]
      exact one_ne_zero
  have hd : Dense badᶜ := hfin.countable.dense_compl ℝ
  obtain ⟨s, hs, hsb⟩ := hd.inter_open_nonempty (Metric.ball 0 ε) Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self hε⟩
  refine ⟨s, by simpa using hs, fun τ' i => ?_⟩
  constructor
  · intro h0
    exact hsb (Set.mem_iUnion.2 ⟨τ', Set.mem_iUnion.2 ⟨i, Or.inl h0⟩⟩)
  · intro h0
    exact hsb (Set.mem_iUnion.2 ⟨τ', Set.mem_iUnion.2 ⟨i, Or.inr h0⟩⟩)

theorem exists_off_bdry {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
    {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j} {n : ℕ} (BM : BaseMetric M n)
    {O : Set BM.Rb.X} (hO : IsOpen O) (hne : O.Nonempty) : ∃ p ∈ O, p ∉ bdry BM.s := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨ψ, -, hxψ, hsub, σ, -, -, u, -, hu, hs⟩ := BM.snc x
  have hop : IsOpen (ψ '' (ψ.source ∩ O)) := ψ.isOpen_image_source_inter hO
  have hD : Dense (Set.pi Set.univ fun _ : Fin n => ({0}ᶜ : Set ℂ)) :=
    dense_pi _ fun _ _ => dense_compl_singleton 0
  obtain ⟨w, ⟨p, ⟨hp, hpO⟩, rfl⟩, hw⟩ := hD.inter_open_nonempty _ hop ⟨ψ x, x, ⟨hxψ, hx⟩, rfl⟩
  refine ⟨p, hpO, fun hb => ?_⟩
  have hpp : BM.s p p = 0 := hb
  have hsec := BM.sec.2 x p p ⟨hsub hp, BM.L.mem_U p⟩
  rw [hpp, norm_zero, zero_mul] at hsec
  have hz : BM.s x p = 0 := by
    have := (mul_eq_zero.1 hsec).resolve_right (Real.exp_pos _).ne'
    simpa using this
  rw [hs p hp] at hz
  rcases mul_eq_zero.1 hz with h | h
  · exact hu p hp h
  · obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.1 h
    cases hσ : σ k with
    | none => simp [hσ] at hk
    | some i =>
      simp only [hσ] at hk
      exact hw i (Set.mem_univ i) (by first | exact pow_eq_zero hk | exact eq_zero_of_pow_eq_zero hk)

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens


open GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens in
theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens.dens_core : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P' J' : Ideal (MRing ι')) (e : ℕ) (R' : AnLogRes P' J' e), J' = ⊤ → ∀ (l : Fin BM.q) (vec : BM.Rb.X → (Ψ → Matrix (Fin N) (Fin N) ℂ) → (Σ k, ι' k) → ℂ) (T : Ψ → Matrix (Fin N) (Fin N) ℂ), (∀ τ', IsLowerUni (T τ')) → (∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X) (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ), IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) → (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) → (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) → ∀ q, AnalyticOnNhd ℂ (fun u => vec (bp u) (fun τ' => hh τ' u) q) V) → (∀ b ∈ BM.O l, ∀ h : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0) → vec b h ∈ mcPts P') → ∀ (x : R'.X), ∀ b ∈ BM.O l, ∀ h₀ : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h₀ τ') ∧ (h₀ τ').det ≠ 0) → SameOrbit (R'.lift x x) (vec b h₀) → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, ∃ b' ∈ BM.O l \ bdry BM.s, ∃ h' : Ψ → Matrix (Fin N) (Fin N) ℂ, (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ SameOrbit (R'.lift x' x') (vec b' h') ∧ ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → minorIJ (h' τ') (stepCols N j i) (stepCols N j i) ≠ 0 ∧ minorIJ (h' τ' * T τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM K' _ ι' _ P' J' e R' hJ l vec T hT hAn hMem x b hb h₀ hh₀ hx V hV hxV
  subst hJ
  obtain ⟨kb, hkb⟩ := BM.Rb.A.cover b
  have hnot : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι')) := by
    intro z hz
    have := hz.2 1 trivial
    simp at this
  let tl : (Fin (n + 1) → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i.succ
  have htl : ∀ u, tl u = Fin.tail u := fun u => rfl
  let c := BM.Rb.A.chart kb
  let bp : (Fin (n + 1) → ℂ) → BM.Rb.X := fun u => c.symm (Fin.tail u)
  let hh : Ψ → (Fin (n + 1) → ℂ) → Matrix (Fin N) (Fin N) ℂ := fun τ' u => hline h₀ (u 0) τ'
  let V₀ : Set (Fin (n + 1) → ℂ) := {u | Fin.tail u ∈ c.target ∧ bp u ∈ BM.O l ∧ ∀ τ', (hh τ' u).det ≠ 0}
  have hc0 : Continuous fun u : Fin (n + 1) → ℂ => u 0 := continuous_apply 0
  have hV₀ : IsOpen V₀ := by
    have h1 : IsOpen (tl ⁻¹' (c.target ∩ c.symm ⁻¹' BM.O l)) :=
      (c.isOpen_inter_preimage_symm (BM.O_open l)).preimage tl.continuous
    have h2 : IsOpen (⋂ τ' : Ψ, {u : Fin (n + 1) → ℂ | (hh τ' u).det ≠ 0}) := by
      refine isOpen_iInter_of_finite fun τ' => ?_
      have hcm : Continuous fun u : Fin (n + 1) → ℂ => hh τ' u := by
        refine continuous_matrix fun r s => ?_
        show Continuous fun u : Fin (n + 1) → ℂ => ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        fun_prop
      exact isOpen_ne_fun hcm.matrix_det continuous_const
    convert h1.inter h2 using 1
    ext u
    simp only [V₀, bp, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, htl, and_assoc]
  have hbpc : ContinuousOn bp V₀ := by
    refine c.continuousOn_symm.comp tl.continuous.continuousOn fun u hu => hu.1
  have hchart : ∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V₀ ∩ bp ⁻¹' (BM.Rb.A.chart k).source) := by
    intro k u hu
    exact AnalyticAt.comp (g := BM.Rb.A.chart k ∘ c.symm) (f := tl)
      (BM.Rb.A.holo kb k _ ⟨hu.1.1, hu.2⟩) (tl.analyticAt u)
  have hentries : ∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V₀ := by
    intro τ' r s u _
    have hp : AnalyticAt ℂ (fun u : Fin (n + 1) → ℂ => u 0) u :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ) 0).analyticAt u
    show AnalyticAt ℂ (fun u : Fin (n + 1) → ℂ => ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s) u
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((analyticAt_const.sub hp).mul analyticAt_const).add (hp.mul analyticAt_const)
  have hbd : ∀ u ∈ V₀, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0 := by
    intro u hu τ'
    refine ⟨fun r s hrs => ?_, hu.2.2 τ'⟩
    have hne : r ≠ s := by
      rintro rfl
      exact hrs Iff.rfl
    show ((1 - u 0) • h₀ τ' + u 0 • (1 : Matrix (Fin N) (Fin N) ℂ)) r s = 0
    simp [Matrix.add_apply, Matrix.smul_apply, (hh₀ τ').1 r s hrs, Matrix.one_apply_ne hne]
  let μ : (Fin (n + 1) → ℂ) → (Σ k, ι' k) → ℂ := fun u => vec (bp u) fun τ' => hh τ' u
  have hμ : ∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V₀ :=
    hAn (n + 1) V₀ bp hh hV₀ hbpc hchart (fun u hu => hu.2.1) hentries hbd
  have hex : ∀ u, ∃ z : R'.X, u ∈ V₀ → SameOrbit (R'.lift z z) (μ u) := by
    intro u
    by_cases hu : u ∈ V₀
    · obtain ⟨z, hz⟩ := R'.surj (μ u) (hMem (bp u) hu.2.1 _ (hbd u hu)) (hnot _)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨x, fun h => absurd h hu⟩
  choose g hg using hex
  have hgc : ContinuousOn g V₀ :=
    (HoloLift.holo_of_analytic_lift K' ι' P' ⊤ e (n + 1) R' rfl V₀ μ g hV₀ hμ hg).1
  let u₀ : Fin (n + 1) → ℂ := Fin.cons 0 (c b)
  have ht₀ : Fin.tail u₀ = c b := Fin.tail_cons _ _
  have hz₀ : u₀ 0 = 0 := Fin.cons_zero _ _
  have hb₀ : bp u₀ = b := by
    show c.symm (Fin.tail u₀) = b
    rw [ht₀]
    exact c.left_inv hkb
  have hhh₀ : (fun τ' => hh τ' u₀) = h₀ := by
    funext τ'
    show hline h₀ (u₀ 0) τ' = h₀ τ'
    rw [hz₀]
    simp [hline]
  have hu₀ : u₀ ∈ V₀ := by
    refine ⟨?_, ?_, fun τ' => ?_⟩
    · rw [ht₀]
      exact c.map_source hkb
    · rw [hb₀]
      exact hb
    · have : hh τ' u₀ = h₀ τ' := congrFun hhh₀ τ'
      rw [this]
      exact (hh₀ τ').2
  have hgx : g u₀ = x := by
    refine R'.inj _ _ (hnot _) (orbit_trans (hg u₀ hu₀) ?_)
    have : μ u₀ = vec b h₀ := by
      show vec (bp u₀) (fun τ' => hh τ' u₀) = _
      rw [hb₀, hhh₀]
    rw [this]
    exact orbit_symm hx
  have hW : IsOpen (V₀ ∩ g ⁻¹' V) := hgc.isOpen_inter_preimage hV₀ hV
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW u₀ ⟨hu₀, by
    show g u₀ ∈ V
    rw [hgx]
    exact hxV⟩
  have hO' : IsOpen (c.source ∩ c ⁻¹' Metric.ball (c b) ε) := c.isOpen_inter_preimage Metric.isOpen_ball
  obtain ⟨p, ⟨hps, hpb⟩, hpoff⟩ := exists_off_bdry BM hO' ⟨b, hkb, Metric.mem_ball_self hε⟩
  obtain ⟨s, hs, hgood⟩ := exists_good_param h₀ T hT (fun i => stepCols N j i) hε
  let u : Fin (n + 1) → ℂ := Fin.cons s (c p)
  have htu : Fin.tail u = c p := Fin.tail_cons _ _
  have hzu : u 0 = s := Fin.cons_zero _ _
  have hbu : bp u = p := by
    show c.symm (Fin.tail u) = p
    rw [htu]
    exact c.left_inv hps
  have hmem : u ∈ Metric.ball u₀ ε := by
    refine Metric.mem_ball.2 ((dist_pi_lt_iff hε).2 fun i => ?_)
    refine Fin.cases ?_ (fun i => ?_) i
    · rw [hzu, hz₀, dist_zero_right]
      exact hs
    · have h1 : u i.succ = c p i := Fin.cons_succ _ _ _
      have h2 : u₀ i.succ = c b i := Fin.cons_succ _ _ _
      rw [h1, h2]
      exact lt_of_le_of_lt (dist_le_pi_dist _ _ i) (Metric.mem_ball.1 hpb)
  obtain ⟨huV, hugV⟩ := hball hmem
  refine ⟨g u, hugV, p, ⟨hbu ▸ huV.2.1, hpoff⟩, fun τ' => hh τ' u, hbd u huV, ?_, ?_⟩
  · have := hg u huV
    rw [show μ u = vec p (fun τ' => hh τ' u) from by
      show vec (bp u) _ = _
      rw [hbu]] at this
    exact this
  · intro τ' i _
    have := hgood τ' i
    rw [← hzu] at this
    exact this
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartYvEqAlgebraMapXbStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basePart_yv_eq_algebraMap_xb : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r, basePart (blkF Ψ p q K₀) (yv A x₀) r = algebraMap Ω (GenField Ω (rk Ψ p q)) (xb A x₀ r) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.YBase.basePart_yv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlkFProperStepInjectiveBlockDiagStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blkF_properStep_injective_blockDiag :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (K₀ : Type),
      (∀ r, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = none ↔ ¬ IsProperStep (p + q) p r.2) ∧
      (∀ r r' k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k →
        blkF (Ψ := Ψ) (p := p) (q := q) K₀ r' = some k → r = r') ∧
      ∀ τ : Ψ, IsBlockDiag p (gMat p q Ω τ) := by
  intro Ψ _ p q Ω _ K₀
  have stepOf_injective : Function.Injective (stepOf (Ψ := Ψ) (p := p) (q := q)) := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h
    have hi := i.2
    have hi' := i'.2
    by_cases h₁ : (i : ℕ) < p <;> by_cases h₂ : (i' : ℕ) < p
    · simp only [stepOf, dite_eq_left h₁, dite_eq_left h₂] at h
      have e₁ : τ = τ' := Sum.inl.inj (congrArg Sigma.fst h)
      have e₂ := congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext e₂)
    · simp only [stepOf, dite_eq_left h₁, dite_eq_right h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_left h₂] at h
      exact absurd (congrArg Sigma.fst h) (by simp)
    · simp only [stepOf, dite_eq_right h₁, dite_eq_right h₂] at h
      have e₁ : τ = τ' := Sum.inr.inj (congrArg Sigma.fst h)
      have e₂ : (i : ℕ) - p = (i' : ℕ) - p :=
        congrArg (fun t : StepIx Ψ p q => (t.2 : ℕ)) h
      exact Prod.ext e₁ (Fin.ext (by show (i : ℕ) = (i' : ℕ); omega))
  have fromBlocks_isBlockDiag {R : Type} [CommRing R] (A : Matrix (Fin q) (Fin q) R)
      (B : Matrix (Fin p) (Fin p) R) :
      IsBlockDiag p ((Matrix.fromBlocks A 0 0 B).submatrix
        (blockEquiv p q).symm (blockEquiv p q).symm) := by
    intro a b hab
    obtain ⟨x, rfl⟩ := (blockEquiv p q).surjective a
    obtain ⟨y, rfl⟩ := (blockEquiv p q).surjective b
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases x with x | x <;> rcases y with y | y
    · exfalso
      apply hab
      have hx := x.2
      have hy := y.2
      show ((x : ℕ) < _ ↔ (y : ℕ) < _)
      omega
    · rfl
    · rfl
    · exfalso
      apply hab
      show (q + (x : ℕ) < _ ↔ q + (y : ℕ) < _)
      omega
  refine ⟨?_, ?_, ?_⟩
  · intro r
    unfold blkF
    split_ifs with h <;> simp [h]
  · intro r r' k h h'
    unfold blkF at h h'
    split_ifs at h h'
    apply stepOf_injective
    have e := (Option.some.inj h).trans (Option.some.inj h').symm
    exact Sum.inr.inj e
  · intro τ
    exact fromBlocks_isBlockDiag
      (genU Ω (rk Ψ p q) (.inr τ)) (genU Ω (rk Ψ p q) (.inl τ))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagFrameAtGoodPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (w : (Σ k, ι k) → ℂ) (H : Ψ → Matrix (Fin N) (Fin N) ℂ), M.IsFrame F → basePart M.blk w ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (basePart M.blk w)) → (∀ τ, IsBlockDiag j (H τ) ∧ (H τ).det ≠ 0) → (∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, w ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M.blk w) p.2 ⟨k, m⟩ (H p.1)) → w ∈ mcPts (mCoordIdeal y) ∧ ∃ z₀, SameOrbit z₀ w ∧ SameOrbit (basePart M.blk z₀) (basePart M.blk w) ∧ M.IsFlagOf F z₀ H := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F w H hF hb hG hH hP
  have hne : ∀ k : NonPluckerBlocks M.blk, w ⟨k.1, F.c k⟩ ≠ 0 := fun k h0 => hG.1 k (by
    show mConeMap (basePart M.blk w) (X ⟨k, F.c k⟩) = 0
    have : basePart M.blk w ⟨k, F.c k⟩ = 0 := h0
    rw [mConeMap, aeval_X, this, map_zero, zero_mul])
  let c : K → ℂ := fun k => if hk : ∀ p, M.blk p ≠ some k then (w ⟨k, F.c ⟨k, hk⟩⟩)⁻¹ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases hk : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos hk]; exact inv_ne_zero (hne ⟨k, hk⟩)
    · simp only [c, dif_neg hk]; exact one_ne_zero
  let z₀ : (Σ k, ι k) → ℂ := fun q => c q.1 * w q
  let c' : NonPluckerBlocks M.blk → ℂ := fun k => c k.1
  have hc' : ∀ k, c' k ≠ 0 := fun k => hc k.1
  have eb : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k => c' q.1 * basePart M.blk w q := rfl
  obtain ⟨hI, hm⟩ := StepW.TorusAct.main _ _ M.Ω M.x (basePart M.blk w) c' hc'
  obtain ⟨hb₀, hval⟩ := hm hb
  rw [← eb] at hI hb₀ hval
  have hflag : M.IsFlagOf F z₀ H := by
    refine ⟨fun k => ?_, hH, fun p k hp => ?_⟩
    · show c k.1 * w ⟨k.1, F.c k⟩ = 1
      simp only [c, dif_pos k.2]
      exact inv_mul_cancel₀ (hne k)
    · obtain ⟨a, ha, hw⟩ := hP p k hp
      refine ⟨a, ha, fun m => ?_⟩
      have hk : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
      show c k * w ⟨k, m⟩ = _
      simp only [c, dif_neg hk, one_mul]
      rw [hw m, CovMap.LocImg.plk]
      simp only [hval]
  have hG₀ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [hI]; exact hG
  have hz₀ : z₀ ∈ mcPts (mCoordIdeal y) :=
    (((_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hF z₀ hb₀ hG₀ hflag.1).2 ⟨H, hflag⟩)
  have ho : SameOrbit z₀ w := ⟨c, hc, rfl⟩
  have ho' : SameOrbit w z₀ := ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), by
    funext q
    exact (inv_mul_cancel_left₀ (hc q.1) _).symm⟩
  exact ⟨mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) ho' hz₀, z₀, ho, ⟨c', hc', rfl⟩, hflag⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.FlagPt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.CompatibleChartProductProjectionTwisted
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.ChartSwap

theorem chart_swap_keep :
    ∀ (e n : ℕ) (X Z : Type) [TopologicalSpace X] [TopologicalSpace Z] (A : FinHolAtlas e X) (Ab : FinHolAtlas n Z) (pr : X → Z) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (kb : Fin Ab.n) (σ : Fin n ↪ Fin e) (ψb : OpenPartialHomeomorph Z (Fin n → ℂ)), IsCompatChart A ψ → IsCompatChart Ab ψb → (∀ x' ∈ ψ.source, pr x' ∈ (Ab.chart kb).source ∧ ∀ i, Ab.chart kb (pr x') i = ψ x' (σ i)) → ∃ ψ' : OpenPartialHomeomorph X (Fin e → ℂ), IsCompatChart A ψ' ∧ ψ'.source = ψ.source ∩ pr ⁻¹' ψb.source ∧ (∀ y ∈ ψ'.source, ∀ i, ψ' y (σ i) = ψb (pr y) i) ∧ ∀ y ∈ ψ'.source, ∀ i, (∀ l, σ l ≠ i) → ψ' y i = ψ y i := by
  intro e n X Z _ _ A Ab pr ψ kb σ ψb hψ hb hpr
  have h₁ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb)
      ((Ab.chart kb).symm.trans ψb).source := by
    intro y hy
    exact (hb kb).1 y hy
  have h₂ : AnalyticOnNhd ℂ ((Ab.chart kb).symm.trans ψb).symm
      ((Ab.chart kb).symm.trans ψb).target := by
    intro y hy
    exact (hb kb).2 y hy
  have hcomp : ∀ y ∈ ψ.source, ψ y ∘ σ = Ab.chart kb (pr y) := fun y hy =>
    funext fun i => ((hpr y hy).2 i).symm
  let T := extendHomeo σ ((Ab.chart kb).symm.trans ψb) h₁ h₂
  have hTan : ∀ w ∈ T.source, AnalyticAt ℂ T w := fun w hw =>
    analyticAt_extend_emb σ (h₁ _ hw)
  have hTsan : ∀ w ∈ T.target, AnalyticAt ℂ T.symm w := fun w hw =>
    analyticAt_extend_emb σ (h₂ _ hw)
  have hsrc : (ψ.trans T).source = ψ.source ∩ pr ⁻¹' ψb.source := by
    ext y
    rw [OpenPartialHomeomorph.trans_source]
    constructor
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      have h3 : ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source := hy'
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source] at h3
      have h4 := h3.2
      simp only [Set.mem_preimage] at h4
      rwa [(Ab.chart kb).left_inv (hpr y hy).1] at h4
    · rintro ⟨hy, hy'⟩
      refine ⟨hy, ?_⟩
      show ψ y ∘ σ ∈ ((Ab.chart kb).symm.trans ψb).source
      rw [hcomp y hy, OpenPartialHomeomorph.trans_source]
      refine ⟨(Ab.chart kb).map_source (hpr y hy).1, ?_⟩
      simp only [Set.mem_preimage]
      rwa [(Ab.chart kb).left_inv (hpr y hy).1]
  refine ⟨ψ.trans T, ?_, hsrc, ?_, ?_⟩
  · intro j
    refine ⟨?_, ?_⟩
    · rintro y ⟨hy1, hy2⟩
      rw [Set.mem_preimage, OpenPartialHomeomorph.trans_source] at hy2
      have h := (hψ j).1 y ⟨hy1, hy2.1⟩
      exact AnalyticAt.comp (g := T) (f := ψ ∘ (A.chart j).symm) (hTan _ hy2.2) h
    · rintro z ⟨hz1, hz2⟩
      rw [OpenPartialHomeomorph.trans_target] at hz1
      have h := (hψ j).2 (T.symm z) ⟨hz1.2, hz2⟩
      exact AnalyticAt.comp (g := A.chart j ∘ ψ.symm) (f := T.symm) h (hTsan z hz1.1)
  · intro y hy i
    rw [hsrc] at hy
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) (σ i) = ψb (pr y) i
    rw [σ.injective.extend_apply, hcomp y hy.1]
    show ψb ((Ab.chart kb).symm (Ab.chart kb (pr y))) i = ψb (pr y) i
    rw [(Ab.chart kb).left_inv (hpr y hy.1).1]
  · intro y _ i hi
    show Function.extend σ (((Ab.chart kb).symm.trans ψb) (ψ y ∘ σ)) (ψ y) i = ψ y i
    exact Function.extend_apply' _ _ _ (fun ⟨l, hl⟩ => hi l hl)

end GlobalTheory.CompanionTheory.Ar.PB.ChartSwap
end

