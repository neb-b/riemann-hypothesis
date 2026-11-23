module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ComplexMultiplicationJPremises
public import GroundTheory.GlobalFields.ComplexMultiplication.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0031
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ComplexMultiplicationJacquetShalika
section
open NumberField IsDedekindDomain IntermediateField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.Published

section

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem latticeCurve_eq_weierstrassCurve (L : PeriodPair) :
    GlobalTheory.latticeCurve L = weierstrassCurve L := by
  simp [GlobalTheory.latticeCurve, weierstrassCurve, neg_div]

theorem j_eq_of_eq {W W' : WeierstrassCurve ℂ} [W.IsElliptic] [W'.IsElliptic] (h : W = W') :
    W.j = W'.j := by
  subst h
  rfl

theorem latticeCurve_j (L : PeriodPair) : (GlobalTheory.latticeCurve L).j = (weierstrassCurve L).j :=
  j_eq_of_eq (latticeCurve_eq_weierstrassCurve L)

theorem under_ne_bot (M : IntermediateField K ℂ) [NumberField M] {P : Ideal (𝓞 M)} (hP : P ≠ ⊥) :
    P.under (𝓞 K) ≠ ⊥ :=
  fun h => hP (Ideal.eq_bot_of_comap_eq_bot h)

theorem isUnramifiedAbelian_hilbertClassField :
    GlobalTheory.Published.IsUnramifiedAbelian (hilbertClassField K ℂ) := by
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  refine ⟨inferInstance, inferInstance, fun P hp hP => ?_⟩
  let v : HeightOneSpectrum (𝓞 K) := ⟨P.under (𝓞 K), inferInstance, under_ne_bot _ hP⟩
  exact (isUnramifiedEverywhere_hilbertClassField K ℂ).1 v P hp ⟨rfl⟩

theorem isUnramifiedEverywhere_of_isUnramifiedAbelian [_root_.NumberField.IsTotallyComplex K]
    {M : IntermediateField K ℂ} [NumberField M] (h : GlobalTheory.Published.IsUnramifiedAbelian M) :
    IsUnramifiedEverywhere K M := by
  refine ⟨fun v P hp hv => ?_, fun v w hw => ?_⟩
  · exact h.2.2 P (Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P)
  · exact InfinitePlace.isUnramified_iff.2 (Or.inr (hw ▸ IsTotallyComplex.isComplex v))

theorem isHilbertClassField_hilbertClassField [_root_.NumberField.IsTotallyComplex K] :
    GlobalTheory.Published.IsHilbertClassField (hilbertClassField K ℂ) := by
  refine ⟨isUnramifiedAbelian_hilbertClassField, fun M hM => ?_⟩
  have := hM.1
  have := hM.2.1
  have : NumberField M := NumberField.of_module_finite K _
  exact (le_hilbertClassField_iff K ℂ M).2 (isUnramifiedEverywhere_of_isUnramifiedAbelian hM)

theorem isArtinMap_hilbertClassFieldArtinEquiv :
    GlobalTheory.Published.IsArtinMap (hilbertClassFieldArtinEquiv K ℂ).toMonoidHom := by
  intro 𝔭 𝔓 hP hO
  have : NumberField (hilbertClassField K ℂ) := NumberField.of_module_finite K _
  have hne : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.1 𝔭.2
  have hpp : (𝔭 : Ideal (𝓞 K)).IsPrime := by
    rw [hO.over]
    exact Ideal.IsPrime.under _ _
  let v : HeightOneSpectrum (𝓞 K) := ⟨𝔭, hpp, hne⟩
  let w : HeightOneSpectrum (𝓞 (hilbertClassField K ℂ)) :=
    ⟨𝔓, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hne 𝔓⟩
  have hwv : w.asIdeal.LiesOver v.asIdeal := hO
  have : Finite (𝓞 (hilbertClassField K ℂ) ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have e : hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭) = _ :=
    hilbertClassFieldArtinEquiv_mk0 K ℂ v w
  change IsArithFrobAt (𝓞 K) (hilbertClassFieldArtinEquiv K ℂ (ClassGroup.mk0 𝔭)) w.asIdeal
  rw [e]
  exact IsArithFrobAt.arithFrobAt _ _ _

theorem lattice_eq_idealLattice {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair}
    (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) : L.lattice = idealLattice (algebraMap K ℂ) 𝔞.1 :=
  SetLike.coe_injective h

theorem latticeEnd_eq_cmRing [_root_.NumberField.IsTotallyComplex K] (hK : Module.finrank ℚ K = 2)
    {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair} (h : GlobalTheory.Published.IsIdealLattice 𝔞 L) :
    GroundTheory.Global.Elliptic.periodLatticeEnd L = cmRingOfEmbedding (algebraMap K ℂ) := by
  rw [← latticeEnd_ideal (algebraMap K ℂ) hK 𝔞]
  ext α
  show (∀ l ∈ L.lattice, α * l ∈ L.lattice) ↔
    ∀ l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice,
      α * l ∈ (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice
  have e : (idealPeriodPair (algebraMap K ℂ) hK 𝔞).lattice = L.lattice := by
    rw [lattice_eq_idealLattice h]
    exact lattice_idealPeriodPair (algebraMap K ℂ) hK 𝔞
  rw [e]

end

theorem complexMultiplicationJ : GlobalTheory.Published.ComplexMultiplicationJSt := by
  intro K _ _ _ _ hK
  refine ⟨hilbertClassField K ℂ, hilbertClassFieldArtinEquiv K ℂ,
    isHilbertClassField_hilbertClassField, isArtinMap_hilbertClassFieldArtinEquiv, ?_, ?_⟩
  · intro 𝔞 L hL
    rw [latticeCurve_j]
    exact adjoin_j_curve_eq_hilbertClassField hK
      (CMCurve.ofLattice (algebraMap K ℂ) L (latticeEnd_eq_cmRing hK hL))
  · intro 𝔞 𝔟 L L' hL hL' x hx
    have hE := latticeEnd_eq_cmRing hK hL
    have hlat : L'.lattice = idealLattice (algebraMap K ℂ) ↑𝔟⁻¹ * L.lattice := by
      rw [lattice_eq_idealLattice hL', lattice_eq_idealLattice hL, Units.val_mul, idealLattice_mul]
    rw [latticeCurve_j] at hx ⊢
    have hx' : x = ⟨(weierstrassCurve L).j, j_weierstrassCurve_mem_hilbertClassField hK L hE⟩ :=
      Subtype.ext hx
    rw [hx']
    exact hilbertClassFieldArtinEquiv_apply_j_weierstrassCurve hK L L' hE 𝔟 hlat

end GlobalTheory.CompanionTheory.Published
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsUnitaryIwasawaLeviOne
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

theorem exists_unitary_iwasawa_leviOne : ∀ {n a : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a}
    (hW : IsIsoFlag ε j W) (hj : ∀ i, 1 ≤ j i), ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ,
      ∀ g ∈ mats (leviOne ε W), ∃ k ∈ maxCpt (mats (leviOne ε W)), ∃ s ∈ mats (leviOne ε W),
        g = k * s ∧ (Uᴴ * s * U).BlockTriangular id :=
  fun {_ _ ε j W} hW hj => GlobalTheory.CompanionTheory.LeviIwa.iwaOn_leviOne ε j W hW hj

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.IwaLevi

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicSectionModerateGrowth
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.CompanionTheory.Gaga

theorem continuous_section_polynomial_growth_of_isProper : ∀ (Y : Scheme.{0}) (p : Y ⟶ Sp ℂ), IsProper p → ∀ (B : LB Y), B.IsLB → ∀ s ∈ fibSec p (RingHom.id ℂ) B, (∀ j, ContinuousOn (s j) (ptsIn p (RingHom.id ℂ) (B.U j))) → ∀ (i : B.ι) (V : Y.Opens), IsAffineOpen V → V ≤ B.U i → ∃ (n : ℕ) (u : Fin n → Γ(Y, V)) (C : ℝ) (m : ℕ), ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ‖s i y‖ ≤ C * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by
  intro Y p hp B hB s hs hc i V hVa hV
  have := compactSpace_cxPts_of_isProper Y p hp
  obtain ⟨n, u, hu⟩ := _root_.GlobalTheory.CompanionTheory.Gaga.exists_gens_bound Y p inferInstance inferInstance V hVa
  refine ⟨n, u, ?_⟩
  have h0 (y) : 0 ≤ ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine SectionGrowth.global_bound _ (fun y => ‖s i y‖) _ (fun y => le_add_of_nonneg_right (h0 y)) fun y₀ => ?_
  obtain ⟨j, hj⟩ := exists_mem_ptsIn hB.cover y₀
  obtain ⟨W, hW, hxW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := B.U j) (mem_ptsIn.1 hj)
  have h2 : W ≤ B.U j := hle
  have hW₀ : y₀ ∈ ptsIn p (RingHom.id ℂ) W := mem_ptsIn.2 hxW
  have h3 : V ⊓ W ≤ B.U i ⊓ B.U j := inf_le_inf hV h2
  obtain ⟨r, m, w, hb⟩ := hu W hW (resG Y h3 (B.g i j).val)
  have hn := (isOpen_ptsIn W).mem_nhds hW₀
  let F : CxPts p (RingHom.id ℂ) → ℝ := fun y => (∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * ‖s j y‖
  have hF : ContinuousAt F y₀ :=
    (tendsto_finsetSum _ fun k _ => ((continuousOn_ev (w k)).continuousAt hn).norm).mul
      ((hc j).continuousAt ((isOpen_ptsIn _).mem_nhds hj)).norm
  refine ⟨|F y₀| + 1, m, by positivity, ?_⟩
  filter_upwards [hn, hF.eventually (eventually_le_nhds (lt_of_le_of_lt (le_abs_self _) (lt_add_one |F y₀|)))]
    with y hy hFy hyV
  have hVW : y ∈ ptsIn p (RingHom.id ℂ) (V ⊓ W) := mem_ptsIn_inf.2 ⟨hyV, hy⟩
  have hb' := hb y hVW
  have hij : y ∈ ptsIn p (RingHom.id ℂ) (B.U i ⊓ B.U j) := ptsIn_mono h3 hVW
  have e : ev p (RingHom.id ℂ) (V ⊓ W) (resG Y h3 (B.g i j).val) y = ev p (RingHom.id ℂ) (B.U i ⊓ B.U j) (B.g i j).val y :=
    ev_res _ hVW _
  rw [e] at hb'
  rw [hs.1 i j y (ptsIn_mono hV hyV) (ptsIn_mono h2 hy), CxPts.gv, norm_mul]
  have hT : 0 ≤ (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := pow_nonneg (add_nonneg zero_le_one (h0 y)) _
  calc _ ≤ ((∑ k, ‖ev p (RingHom.id ℂ) W (w k) y‖) * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m) * ‖s j y‖ :=
        mul_le_mul_of_nonneg_right hb' (norm_nonneg _)
    _ = F y * (1 + ∑ l, ‖ev p (RingHom.id ℂ) V (u l) y‖) ^ m := by simp only [F]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hFy hT

end GlobalTheory.CompanionTheory.Gaga
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IterateRealSmul
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mnorm_real_smul (s : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : mnorm (s • X) = |s| * mnorm X := by
  unfold mnorm
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, Finset.mul_sum]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem iterate_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => simpa using hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep ih hX).2

theorem iterate_real_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) (m : ℕ) :
    (dRep π (s • X))^[m] v = ((s : ℂ) ^ m) • (dRep π X)^[m] v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsm := iterate_smooth hG hrep hs hX m
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', GlobalTheory.GKLie.dRep_smul,
      (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep hsm hsm hX hX).2.2, ← Complex.coe_smul, smul_smul, pow_succ']

theorem analytic_coeff : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H),
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ := by
  intro n G H _ _ _ π hG hU v hs hw X hX w t₀ _
  obtain ⟨r, hr, hsum⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasSum_orbit_of_wordBound hG hU.1 hU.2.2 hs hw
  have hrep := hU.1
  let L : H →L[ℂ] ℂ := (innerSL ℂ w).comp (π (NormedSpace.exp (t₀ • X)))
  let a : ℕ → ℂ := fun m => ((m.factorial : ℂ)⁻¹) * L ((dRep π X)^[m] v)
  have key : ∀ s : ℝ, |s| * mnorm X < r → HasSum (fun m : ℕ => (s : ℂ) ^ m * a m)
      (⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ) := by
    intro s hs'
    have h1 := hsum (s • X) ((_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG).2.1 s X hX) (by rwa [mnorm_real_smul])
    have h2 := L.hasSum h1
    have e : ⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ = L (π (NormedSpace.exp (s • X)) v) := by
      have hc : Commute (t₀ • X) (s • X) := ((Commute.refl X).smul_left t₀).smul_right s
      rw [add_smul, Matrix.exp_add_of_commute _ _ hc, hrep.2 _ (hX t₀) _ (hX s)]
      rfl
    rw [e]
    convert h2 using 2 with m
    rw [iterate_real_smul hG hrep hs hX s m]
    simp only [a, map_smul, smul_eq_mul]
    ring
  let p : FormalMultilinearSeries ℝ ℝ ℂ := fun m => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (a m)
  have hpa : ∀ (m : ℕ) (s : ℝ), p m (fun _ => s) = (s : ℂ) ^ m * a m := by
    intro m s
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hM : 0 < mnorm X + 1 := by linarith [mnorm_nonneg X]
  have hsmall : ∀ s : ℝ, |s| < r / (mnorm X + 1) → |s| * mnorm X < r := by
    intro s h
    rw [lt_div_iff₀ hM] at h
    nlinarith [abs_nonneg s]
  set ε : ℝ := r / (mnorm X + 1) with hε
  have hεpos : 0 < ε := div_pos hr hM
  have hrad : 0 < p.radius := by
    have hs0 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
    have hS := (key (ε / 2) (hsmall _ hs0)).summable.norm
    let ρ : NNReal := ⟨ε / 2, by linarith⟩
    have hρ : (0 : NNReal) < ρ := by
      change (0 : ℝ) < ε / 2
      linarith
    have : (ρ : ENNReal) ≤ p.radius := by
      refine p.le_radius_of_summable_norm ?_
      refine hS.congr fun m => ?_
      have hρc : ((ρ : NNReal) : ℝ) = ε / 2 := rfl
      simp [p, hρc, ContinuousMultilinearMap.norm_mkPiRing, abs_of_pos hεpos, mul_comm]
    exact lt_of_lt_of_le (by exact_mod_cast hρ) this
  have han : AnalyticAt ℝ p.sum 0 := (p.hasFPowerSeriesOnBall hrad).analyticAt
  have han2 : AnalyticAt ℝ (fun t : ℝ => p.sum (t - t₀)) t₀ :=
    AnalyticAt.comp_of_eq (g := p.sum) (f := fun t : ℝ => t - t₀) han
      (analyticAt_id.sub analyticAt_const) (by simp)
  refine han2.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ hεpos] with t ht
  have hd : |t - t₀| < ε := by simpa [Real.dist_eq] using ht
  have h3 := key (t - t₀) (hsmall _ hd)
  rw [show t₀ + (t - t₀) = t by ring] at h3
  simp only [FormalMultilinearSeries.sum, hpa]
  exact h3.tsum_eq

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SumSquaresComm
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem dRep_realSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H} (hu : IsSmoothVec G π u) {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (a : ι → Matrix (Fin n) (Fin n) ℂ) (ha : ∀ l, a l ∈ HCSS.lieOf G)
    (h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G) :
    (∑ l ∈ s, c l • a l) ∈ HCSS.lieOf G ∧
      dRep π (∑ l ∈ s, c l • a l) u = ∑ l ∈ s, c l • dRep π (a l) u := by
  classical
  obtain ⟨hadd, hsm, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, GlobalTheory.GKLie.dRep_zero π u⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 := hsm (c x) _ (ha x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep hu hu h1 ih.1).1, ih.2, GlobalTheory.GKLie.dRep_smul]

theorem dRep_vecSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G)
    {ι : Type} (s : Finset ι) (c : ι → ℝ) (u : ι → H) (hu : ∀ l, IsSmoothVec G π (u l)) :
    IsSmoothVec G π (∑ l ∈ s, c l • u l) ∧
      dRep π X (∑ l ∈ s, c l • u l) = ∑ l ∈ s, c l • dRep π X (u l) := by
  classical
  obtain ⟨hadd, hsm, -⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed hG hrep
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [dRep]⟩
    exact ⟨fun _ => 0, contDiff_const, fun z _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : IsSmoothVec G π (c x • u x) := by
      rw [← Complex.coe_smul]
      exact hsm _ _ (hu x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep h1 ih.1 hX hX).2.1, ih.2, ← Complex.coe_smul,
      (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.SmoothLin.dRep_linear hG hrep (hu x) (hu x) hX hX).2.2, Complex.coe_smul]

theorem sumSquares_comm {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G)
    (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l)
    {v : H} (hv : IsSmoothVec G π v) :
    π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
  · simp [Finset.univ_eq_empty]
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G := by
    simpa using (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.lieOf_isLieSubalgebra hG).2.1 0 _ (hb i0)
  have hw : IsSmoothVec G π (π k v) := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.smooth_closed hG hrep).2.2 k hk v hv
  have hT : ∀ m, IsSmoothVec G π (dRep π (b m) (π k v)) := fun m =>
    (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hw (hb m)).2
  have step : ∀ i, π k (dRep π (b i) (dRep π (b i) v)) =
      ∑ l, ∑ m, (O l i * O m i) • dRep π (b l) (dRep π (b m) (π k v)) := by
    intro i
    have hsm := (_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.hasDerivAt_dRep_and_isSmoothVec hG hrep hv (hb i)).2
    rw [_root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant hG hrep hsm (hb i) hk, _root_.GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant hG hrep hv (hb i) hk, hkb i,
      (dRep_realSum hG hrep hw Finset.univ (fun m => O m i) b hb h0).2,
      (dRep_realSum hG hrep
        (dRep_vecSum hG hrep (hb i0) Finset.univ (fun m => O m i) _ hT).1
        Finset.univ (fun l => O l i) b hb h0).2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(dRep_vecSum hG hrep (hb l) Finset.univ (fun m => O m i) _ hT).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
  have hdelta : ∀ l m, ∑ i, O l i * O m i = (1 : Matrix (Fin d) (Fin d) ℝ) l m := fun l m => by
    rw [← hOO]
    simp [Matrix.mul_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hdelta, Matrix.one_apply]
  simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

