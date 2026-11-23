module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0520
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2699
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2705
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2725
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1383
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapSurjective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniform
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp.Morse

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem cmb_eq_frame (P : Pair p) (m : ℕ) {ι : Type} [Fintype ι] (f : ι → X.functionField)
    (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ) (i : P.L.B.ι) (j : P.A.B.ι)
    (hi : y ∈ ptsIn p σ (P.L.B.U i)) (hj : y ∈ ptsIn p σ (P.A.B.U j)) :
    cmb (vals P m 1 f) c σ y = ‖∑ l, c l * ratVal (P.loc m 1 (f l) i j) y‖ ^ 2 *
      Real.exp (-((m : ℝ) * (P.L.φ σ).φ i y)) * Real.exp (-(P.A.φ σ).φ j y) := by
  obtain ⟨θ, hθ, h⟩ := _root_.GlobalTheory.HSAmp.val_frame k X p P m 1 σ y i j hi hj
  have e : ∑ l, c l * vals P m 1 f σ y l = θ * ((∑ l, c l * ratVal (P.loc m 1 (f l) i j) y) *
      (Real.exp (-(((m : ℤ) : ℝ) * (P.L.φ σ).φ i y + ((1 : ℤ) : ℝ) * (P.A.φ σ).φ j y) / 2) : ℝ)) := by
    simp only [vals, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h _ (hf l)]
    ring
  rw [cmb, e, norm_mul, hθ, one_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    mul_pow, sq (Real.exp _), ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem continuous_cmb {D : ℕ} (hX : IsArithVar p D) (P : Pair p) (m : ℕ) {ι : Type} [Fintype ι]
    (f : ι → X.functionField) (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (σ : k →+* ℂ) :
    Continuous fun y => cmb (vals P m 1 f) c σ y := by
  have hp := (_root_.GlobalTheory.HSAmp.continuous_val_and_bounded k X p D hX P m 1).1 σ
  have e : (fun y => cmb (vals P m 1 f) c σ y) = fun y =>
      (∑ a, ∑ b, c a * (starRingEnd ℂ) (c b) *
        (val P m 1 σ y (f a) * (starRingEnd ℂ) (val P m 1 σ y (f b)))).re := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [cmb, ← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj, map_sum,
      Finset.sum_mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [vals, map_mul]
    ring
  rw [e]
  exact Complex.continuous_re.comp (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_const.mul (hp _ (hf a) _ (hf b)))

theorem integral_over_chart_le_l2 {D : ℕ} (hX : IsArithVar p D) (hs : GenSmooth p D) (P : Pair p) (m : ℕ) {ι : Type}
    [Fintype ι] (f : ι → X.functionField) (hf : ∀ l, f l ∈ P.H m 1) (c : ι → ℂ) (ω : ∀ σ, VolDens p σ D)
    (σ : k →+* ℂ) (C : AlgChart p σ D) (T : Set (ReciprocityTheory.L2DbarEstimates.V D)) (hT : IsOpen T) (hTt : T ⊆ C.e.target) :
    ∫ v in T, cmb (vals P m 1 f) c σ (C.e.symm v) * (ω σ).dens C (C.e.symm v) ≤
      l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  haveI := hX.compactSpace σ
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hX.isProjOver
  obtain ⟨hfin, -⟩ := _root_.GlobalTheory.HSAmp.volDens_meas_finite_openPos k X p D hX hs σ (ω σ)
  have hcont := continuous_cmb hX P m f hf c σ
  set S := C.e.source ∩ C.e ⁻¹' T with hSdef
  have hSo : IsOpen S := C.e.isOpen_inter_preimage hT
  have hSs : S ⊆ C.e.source := Set.inter_subset_left
  have hST : C.e '' S = T := by
    rw [hSdef, C.e.image_source_inter_eq']
    ext v
    refine ⟨fun hv => ?_, fun hv => ⟨hTt hv, ?_⟩⟩
    · have h := hv.2
      simp only [Set.mem_preimage, C.e.right_inv hv.1] at h
      exact h
    · simp only [Set.mem_preimage, C.e.right_inv (hTt hv)]
      exact hv
  have h1 := (_root_.GlobalTheory.HSAmp.VolDens.meas_integral_in_chart k X p D hX σ (ω σ) C S _ hSo.measurableSet hSs hcont).2
  rw [hST] at h1
  rw [← h1]
  have hnn : ∀ σ' (y : CxPts p σ'), 0 ≤ cmb (vals P m 1 f) c σ' y := fun _ _ => by unfold cmb; positivity
  have hint : Integrable (fun y => cmb (vals P m 1 f) c σ y) (ω σ).meas :=
    integrableOn_univ.1 (hcont.continuousOn.integrableOn_compact isCompact_univ)
  calc ∫ y in S, cmb (vals P m 1 f) c σ y ∂(ω σ).meas ≤ ∫ y, cmb (vals P m 1 f) c σ y ∂(ω σ).meas :=
        setIntegral_le_integral hint (Eventually.of_forall (hnn σ))
    _ ≤ l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
        unfold l2
        exact single_le_finsum (f := fun σ' => ∫ y, cmb (vals P m 1 f) c σ' y ∂(ω σ').meas) σ (Set.toFinite _)
          fun σ' => integral_nonneg (hnn σ')

theorem local_bound {D : ℕ} (hX : IsArithVar p D) (hs : GenSmooth p D) (P : Pair p) (hP : P.L.SemiPos D)
    (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ) (hρ : ∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) (ε : ℝ)
    (hε : 0 < ε) (σ : k →+* ℂ) (y₀ : CxPts p σ) :
    ∃ N ∈ 𝓝 y₀, ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField),
      (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ), ∀ y ∈ N,
        cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  obtain ⟨R⟩ := hs σ
  obtain ⟨a, ha⟩ := R.cover y₀
  set C := R.chart a with hC
  set i := pick (P.L.φ σ).isLB y₀ with hi
  set j := pick (P.A.φ σ).isLB y₀ with hj
  set O := C.e.source ∩ ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j) with hOdef
  have hO : IsOpen O := (C.e.open_source.inter (isOpen_ptsIn _)).inter (isOpen_ptsIn _)
  have hy₀O : y₀ ∈ O := ⟨⟨ha, mem_pick _ _⟩, mem_pick _ _⟩
  set U := C.e '' O with hUdef
  have hU : IsOpen U := C.e.isOpen_image_of_subset_source hO fun y hy => hy.1.1
  have hUO : ∀ v ∈ U, C.e.symm v ∈ O ∧ v ∈ C.e.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rwa [C.e.left_inv hy.1.1], C.e.map_source hy.1.1⟩
  obtain ⟨r, hr, hrU⟩ : ∃ r > 0, Metric.closedBall (C.e y₀) r ⊆ U :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds ⟨y₀, hy₀O, rfl⟩)
  set K := Metric.closedBall (C.e y₀) r with hK
  have hsymm : ContinuousOn C.e.symm U := C.e.continuousOn_symm.mono fun v hv => (hUO v hv).2
  have hdc : ContinuousOn (fun v => (ω σ).dens C (C.e.symm v)) U :=
    ((ω σ).cont C).comp hsymm fun v hv => (hUO v hv).1.1.1
  have hψc : ContinuousOn (fun v => (P.A.φ σ).φ j (C.e.symm v)) U :=
    ContinuousOn.comp (show ContinuousOn ((P.A.φ σ).φ j) (ptsIn p σ (P.A.B.U j)) from
      fun y hy => ((P.A.cInf σ) j y hy).continuousAt.continuousWithinAt) hsymm fun v hv => (hUO v hv).1.2
  have hφ' : ContDiffOn ℝ 2 (fun v => (P.L.φ σ).φ i (C.e.symm v)) U := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((P.L.cInf σ).contDiffAt C hy.1.1 hy.1.2).contDiffWithinAt
  have hlevi : ∀ z ∈ U, ∀ ξ : Fin D → ℂ,
      0 ≤ (ReciprocityTheory.L2DbarEstimates.leviV D (fun v => (((P.L.φ σ).φ i (C.e.symm v) : ℝ) : ℂ)) z ξ).re := by
    rintro _ ⟨y, hy, rfl⟩ ξ
    exact hP σ i C y ⟨hy.1.1, hy.1.2⟩ ξ
  have hgc : ContinuousOn (fun v => Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v)) U :=
    (Real.continuous_exp.comp_continuousOn hψc.neg).mul hdc
  have hgp : ∀ v ∈ U, 0 < Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v) := fun v hv =>
    mul_pos (Real.exp_pos _) ((ω σ).pos C _ (hUO v hv).1.1.1)
  obtain ⟨v₀, hv₀, hmin⟩ := (isCompact_closedBall (C.e y₀) r).exists_isMinOn
    ⟨C.e y₀, Metric.mem_closedBall_self hr.le⟩ (hdc.mono hrU)
  have hd₀ : 0 < (ω σ).dens C (C.e.symm v₀) := (ω σ).pos C _ (hUO v₀ (hrU hv₀)).1.1.1
  obtain ⟨δ, hδ, hball, hev⟩ := _root_.GlobalTheory.morse_local D U K (fun v => (P.L.φ σ).φ i (C.e.symm v))
    (fun v => Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v))
    (ε * (ω σ).dens C (C.e.symm v₀)) hU (isCompact_closedBall _ _) hrU hφ' hlevi hgc hgp (mul_pos hε hd₀)
  refine ⟨C.e.source ∩ C.e ⁻¹' K, inter_mem (C.e.open_source.mem_nhds ha)
    ((C.e.continuousAt ha).preimage_mem_nhds (Metric.closedBall_mem_nhds _ hr)), ?_⟩
  filter_upwards [hev] with m hm ι _ f hf c y hy
  have hyO : y ∈ O := by
    have := (hUO (C.e y) (hrU hy.2)).1
    rwa [C.e.left_inv hy.1] at this
  set F : ReciprocityTheory.L2DbarEstimates.V D → ℂ := fun v => ∑ l, c l * ratVal (P.loc m 1 (f l) i j) (C.e.symm v) with hF
  have hFd : DifferentiableOn ℂ F U := by
    refine DifferentiableOn.fun_sum (𝕜 := ℂ) (u := Finset.univ)
      (A := fun l v => c l * ratVal (P.loc m 1 (f l) i j) (C.e.symm v)) fun l _ => ?_
    exact (((GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P m 1 σ (f l) (hf l) i j).2 D C).mono fun v hv =>
      ⟨(hUO v hv).2, (hUO v hv).1.1.2, (hUO v hv).1.2⟩).const_mul (c l)
  have hid : ∀ v ∈ U, ‖F v‖ ^ 2 * Real.exp (-((m : ℝ) * (P.L.φ σ).φ i (C.e.symm v))) *
      (Real.exp (-(P.A.φ σ).φ j (C.e.symm v)) * (ω σ).dens C (C.e.symm v)) =
      cmb (vals P m 1 f) c σ (C.e.symm v) * (ω σ).dens C (C.e.symm v) := by
    intro v hv
    rw [cmb_eq_frame P m f hf c σ _ i j (hUO v hv).1.1.2 (hUO v hv).1.2]
    ring
  have hBU : ∀ w ∈ Metric.ball (C.e y) δ, w ∈ U := fun w hw =>
    hball _ hy.2 (Metric.ball_subset_closedBall hw)
  have hI : ∫ w in Metric.ball (C.e y) δ, ‖F w‖ ^ 2 * Real.exp (-((m : ℝ) * (P.L.φ σ).φ i (C.e.symm w))) *
      (Real.exp (-(P.A.φ σ).φ j (C.e.symm w)) * (ω σ).dens C (C.e.symm w)) =
      ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w) :=
    setIntegral_congr_fun Metric.isOpen_ball.measurableSet fun w hw => hid w (hBU w hw)
  have hle := integral_over_chart_le_l2 hX hs P m f hf c ω σ C _ Metric.isOpen_ball fun w hw => (hUO w (hBU w hw)).2
  have hInn : 0 ≤ ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w) :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet fun w hw =>
      mul_nonneg (by unfold cmb; positivity) ((ω σ).pos C _ (hUO w (hBU w hw)).1.1.1).le
  have hdy : 0 < (ω σ).dens C y := (ω σ).pos C y hy.1
  have hρ0 : 0 ≤ ρ σ y := by
    have h2 := C.chernDens_nonneg (P.L.cInf σ) (hP σ) hy.1
    rw [(hρ σ).2 C y hy.1] at h2
    exact (mul_nonneg_iff_of_pos_right hdy).1 h2
  have hdet : (ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (((P.L.φ σ).φ i (C.e.symm v) : ℝ) : ℂ)) (C.e y)).det.re /
      Real.pi ^ D = ρ σ y * (ω σ).dens C y / D.factorial := by
    have h1 := (hρ σ).2 C y hy.1
    rw [C.chernDens_eq (P.L.cInf σ) hy.1 hyO.1.2] at h1
    have hpi : 0 < Real.pi ^ D := by positivity
    have hfac : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
    rw [div_eq_div_iff hpi.ne' hfac.ne', ← h1]
    simp only [AlgChart.hess]
    field_simp
  have h0 := hm (C.e y) hy.2 F hFd
  beta_reduce at h0
  rw [hid _ (hrU hy.2), hI, hdet, C.e.left_inv hy.1] at h0
  have hmin' : (ω σ).dens C (C.e.symm v₀) ≤ (ω σ).dens C y := by
    have := hmin hy.2
    simp only [Set.mem_setOf_eq, C.e.left_inv hy.1] at this
    exact this
  set I := ∫ w in Metric.ball (C.e y) δ, cmb (vals P m 1 f) c σ (C.e.symm w) * (ω σ).dens C (C.e.symm w)
  have hM : 0 ≤ (m : ℝ) ^ D * I := mul_nonneg (by positivity) hInn
  have h3 : (ω σ).dens C y * cmb (vals P m 1 f) c σ y ≤
      (ω σ).dens C y * ((ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * I) := by
    rw [mul_comm]
    refine h0.trans ?_
    calc (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C (C.e.symm v₀)) * (m : ℝ) ^ D * I
        = (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C (C.e.symm v₀)) * ((m : ℝ) ^ D * I) := by ring
      _ ≤ (ρ σ y * (ω σ).dens C y / D.factorial + ε * (ω σ).dens C y) * ((m : ℝ) ^ D * I) := by gcongr
      _ = (ω σ).dens C y * ((ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * I) := by ring
  refine (le_of_mul_le_mul_left h3 hdy).trans (mul_le_mul_of_nonneg_left hle ?_)
  positivity

theorem cmb_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D →
    GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ),
    (∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι]
    (f : ι → X.functionField), (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ),
    cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  intro k _ X _ p D hX hs P hP ω ρ hρ ε hε
  haveI : Finite (k →+* ℂ) := hX.finite_emb
  choose N hN hev using fun σ (y₀ : CxPts p σ) => local_bound hX hs P hP ω ρ hρ ε hε σ y₀
  have hcov : ∀ σ : k →+* ℂ, ∃ t : Finset (CxPts p σ), ∀ y, ∃ y₀ ∈ t, y ∈ N σ y₀ := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨t, -, ht⟩ := (isCompact_univ (X := CxPts p σ)).elim_nhds_subcover (N σ) fun y _ => hN σ y
    exact ⟨t, fun y => by simpa using ht (Set.mem_univ y)⟩
  choose t ht using hcov
  have hall : ∀ᶠ m : ℕ in atTop, ∀ σ : k →+* ℂ, ∀ y₀ ∈ t σ, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField),
      (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ), ∀ y ∈ N σ y₀,
        cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c :=
    eventually_all.2 fun σ => (eventually_all_finset (t σ)).2 fun y₀ _ => hev σ y₀
  filter_upwards [hall] with m hm ι _ f hf c σ y
  obtain ⟨y₀, hy₀, hy⟩ := ht σ y
  exact hm σ y₀ hy₀ ι f hf c y hy

end GlobalTheory.HSAmp.Morse
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumber
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hCD F _ σ X κ _ Δ L r ψ hψ P hP
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hform : ∀ G : MvPolynomial κ ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (fun a => c1W (ψ a)) G) :=
    fun G => ((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 κ _ G
      (fun a => (_root_.GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero F σ X (L a) (ψ a) (hψ a).2).1)).1
  have Pw := GlobalTheory.LineForm.wInt_props (CxPts X.str σ) X.dim (atlas X σ)
  have hint : ∀ G : MvPolynomial κ ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((atlas X σ).part (evalF (atlas X σ) (fun a => c1W (ψ a)) G) ε) :=
    fun G ε => by
      haveI := Pw.1 _ (hform G) ε
      exact integrable_const _
  have eval_add (G₁ G₂ : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂) =
        evalF (atlas X σ) (fun a => c1W (ψ a)) G₁ + evalF (atlas X σ) (fun a => c1W (ψ a)) G₂ := by
    funext x
    simp [evalF, fld]
  have eval_smul (t : ℝ) (G : MvPolynomial κ ℝ) :
      evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G) =
        (t : ℂ) • evalF (atlas X σ) (fun a => c1W (ψ a)) G := by
    funext x
    simp [evalF, fld, MvPolynomial.smul_eq_C_mul, Algebra.smul_def]
  have hadd : ∀ G₁ G₂ : MvPolynomial κ ℝ,
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂)) =
        (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₁) +
          (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₂) := fun G₁ G₂ => by
    rw [← wInt_one, ← wInt_one, ← wInt_one, eval_add]
    exact (Pw.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  have hsmul : ∀ (t : ℝ) (G : MvPolynomial κ ℝ),
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G)) =
        t * (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G) := fun t G => by
    rw [← wInt_one, ← wInt_one, eval_smul]
    exact Pw.2.2.1 _ t _ (hform G)
  have hspan : P ∈ Submodule.span ℝ (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := by
    classical
    by_contra hnot
    obtain ⟨φ, hφF, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
    have hkill : ∀ n : κ → ℤ, φ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = 0 := by
      intro n
      have hm : GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim ∈ Submodule.span ℝ
          (Set.range fun n : κ → ℤ => GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) := Submodule.subset_span ⟨n, rfl⟩
      have h2 := Submodule.mem_map_of_mem (f := φ) hm
      rw [hφ] at h2
      exact (Submodule.mem_bot ℝ).mp h2
    have hQ : GlobalTheory.PowLinSpan.polOf φ X.dim = 0 := by
      refine eq_zero_of_eval_zero_at_prod_finset _
        (fun _ => (Finset.range (X.dim + 1)).image (fun k : ℕ => (k : ℝ))) ?_ ?_
      · intro x
        rw [Finset.card_image_of_injective _ Nat.cast_injective]
        simpa using Nat.lt_succ_of_le (GlobalTheory.PowLinSpan.degreeOf_polOf_le φ X.dim x)
      · intro v hv
        have hv' : ∀ i, ∃ k : ℕ, (k : ℝ) = v i := by
          intro i
          obtain ⟨k, -, hk⟩ := Finset.mem_image.mp (hv i)
          exact ⟨k, hk⟩
        choose k hk using hv'
        rw [GlobalTheory.PowLinSpan.eval_polOf]
        have he : (∑ x, C (v x) * MvPolynomial.X x : MvPolynomial κ ℝ) = GlobalTheory.ArInt.lin (fun i => (((k i : ℤ)) : ℝ)) := by
          simp only [GlobalTheory.ArInt.lin, Int.cast_natCast, hk]
        rw [he]
        exact hkill (fun i => (k i : ℤ))
    exact hφF (GlobalTheory.PowLinSpan.homog_kill φ X.dim hQ P hP)
  clear hP
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨L', r', ψ', hpr, hci, hc1⟩ := _root_.GlobalTheory.ChernCalc.exists_comb_smoothWeight F σ X κ Δ L r ψ hψ n
    have e1 : evalF (atlas X σ) (fun a => c1W (ψ a)) (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) =
        fld (atlas X σ) (c1W ψ' ^ X.dim) := by
      funext x
      rw [hc1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [evalF, fld, GlobalTheory.ArInt.lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply]
      congr 2
    have e2 : X.interPoly Δ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = (X.inter fun _ => ∑ a, n a • Δ a : ℝ) := by
      have := Var.interPoly_prod_sum X Δ (fun _ a => n a)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    rw [e1, e2, HolAtlas.integral, _root_.GlobalTheory.ChernCalc.TopPow.part_c1W_pow F σ X L' ψ' hci, _root_.GlobalTheory.ChernCalc.TopPow.part_c1W_pow F σ X L' ψ' hci,
      ← (hCD F X σ _ L' r' hpr ψ' hci).2]
    simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]
  | zero =>
    rw [map_zero]
    have := hsmul 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add (f := _), hadd, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, hsmul, hx, smul_eq_mul]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [HolAtlas.loc, dite_eq_left hw]
      exact Finset.sum_apply _ _ _
    · simp [HolAtlas.loc, hw]
  have hx := (A.e x.1.1).open_target.mem_nhds (x.ch.map_source x.2)
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt hx
  have hcoeff : ∀ S u,
      GlobalTheory.dbar (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
        ∑ j, GlobalTheory.dbar (fun w => (bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have hsum : (fun w => (bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j, (bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w
      rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [hsum, GlobalTheory.dbar_sum (fun j _ => hdiff j S), _root_.sum_apply]
  rw [Finset.sum_apply]
  simp only [HolAtlas.dbar, dbarAt, coefwise, hcoeff, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := _root_.GlobalTheory.exists_finite_smooth_partition_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    FormMul.isForm_mul A _ _ (A.isForm_fn (hs j)) hη
  have hdiff : ∀ j, A.IsForm (A.del (A.fn (χ j) * η)) ∧ A.IsForm (A.dbar (A.fn (χ j) * η)) :=
    fun j => _root_.GlobalTheory.CxForm.isForm_del_dbar M n A _ (hf j)
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).1)]
    exact Finset.sum_eq_zero fun j _ => _root_.GlobalTheory.CxForm.LocStokes.integral_del_fn_mul_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf,
      GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (hdiff j).2)]
    exact Finset.sum_eq_zero fun j _ => _root_.GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharpolyBcMapIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AV.AbVar

variable {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]

def bcAdd (A : AbVar K) : End A →+ End (baseChange L A) where
  toFun f := End.of (bcMap L f.asHom)
  map_zero' := by
    apply End.ext
    change bcMap L (0 : A ⟶ A) = 0
    have h := bcMap_add L (0 : A ⟶ A) 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  map_add' f g := End.ext (bcMap_add L f.asHom g.asHom)

theorem bcMap_intCast_sub (A : AbVar K) (n : ℤ) (f : End A) :
    End.of (bcMap L ((n : End A) - f).asHom) =
      (n : End (baseChange L A)) - End.of (bcMap L f.asHom) := by
  have h1 : bcAdd L A 1 = 1 := End.ext (bcMap_id L A)
  have hn : bcAdd L A (n : End A) = (n : End (baseChange L A)) := by
    simp only [← zsmul_one, map_zsmul, h1]
  change bcAdd L A ((n : End A) - f) = (n : End (baseChange L A)) - bcAdd L A f
  rw [map_sub, hn]

theorem isCharpoly_bcMap_iff (A : AbVar K) (f : End A) (P : Polynomial ℤ) :
    IsCharpoly (End.of (bcMap L f.asHom)) P ↔ IsCharpoly f P := by
  unfold IsCharpoly
  have hd : (baseChange L A).dim = A.dim := rfl
  refine and_congr Iff.rfl (and_congr (by rw [hd]) (forall_congr' fun n => ?_))
  rw [← bcMap_intCast_sub, (isIsogeny_bcMap_iff_and_deg_bcMap K L A A _).2]

theorem isCharpoly_unique {A : AbVar K} (f : End A) {P Q : Polynomial ℤ}
    (hP : IsCharpoly f P) (hQ : IsCharpoly f Q) : P = Q :=
  Polynomial.funext fun n => by rw [hP.2.2 n, hQ.2.2 n]

theorem charpoly_bcMap : ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (f : End A),
    charpoly (End.of (bcMap L f.asHom)) = charpoly f := by
  intro K _ L _ _ A f
  classical
  unfold charpoly
  by_cases h : ∃ P, IsCharpoly f P
  · have h' : ∃ P, IsCharpoly (End.of (bcMap L f.asHom)) P :=
      let ⟨P, hP⟩ := h; ⟨P, (isCharpoly_bcMap_iff L A f P).2 hP⟩
    rw [dite_eq_left h, dite_eq_left h']
    exact isCharpoly_unique f ((isCharpoly_bcMap_iff L A f _).1 h'.choose_spec) h.choose_spec
  · have h' : ¬ ∃ P, IsCharpoly (End.of (bcMap L f.asHom)) P :=
      fun ⟨P, hP⟩ => h ⟨P, (isCharpoly_bcMap_iff L A f P).1 hP⟩
    rw [dite_eq_right h, dite_eq_right h']

end GlobalTheory.AV.AbVar

end
end

