module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullCOfInvM
section
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RswCell.NullCompl

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G]

theorem rp_mk_inv (P : Subgroup G) (g : G) : ∃ p ∈ P, rp (P := P) (((g⁻¹ : G)) : G ⧸ P) = p * g := by
  refine ⟨(Quotient.out ((g⁻¹ : G) : G ⧸ P))⁻¹ * g⁻¹, ?_, ?_⟩
  · exact QuotientGroup.eq.mp (QuotientGroup.out_eq' ((g⁻¹ : G) : G ⧸ P))
  · simp [rp]

theorem rp_smul (P : Subgroup G) (x : G) (q : G ⧸ P) : ∃ p ∈ P, rp (x⁻¹ • q) = p * (rp q * x) := by
  refine ⟨(Quotient.out (x⁻¹ • q))⁻¹ * (x⁻¹ * Quotient.out q), ?_, ?_⟩
  · rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_coe,
      QuotientGroup.out_eq']
  · simp [rp, mul_assoc]

variable [TopologicalSpace G]

theorem isOpen_rp [IsTopologicalGroup G] (P : Subgroup G) {Ω : Set G} (hΩ : IsOpen Ω)
    (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) : IsOpen {q : G ⧸ P | rp q ∈ Ω} := by
  have hset : {q : G ⧸ P | rp q ∈ Ω} = ((↑) : G → G ⧸ P) '' {g | g⁻¹ ∈ Ω} := by
    ext q
    constructor
    · intro hq
      refine ⟨(rp q)⁻¹, by simpa using hq, ?_⟩
      simp only [rp, inv_inv]
      exact QuotientGroup.out_eq' q
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨p, hp, hrp⟩ := rp_mk_inv P g⁻¹
      simp only [inv_inv] at hrp
      show rp (g : G ⧸ P) ∈ Ω
      rw [hrp]
      exact hP p hp _ hg
  rw [hset]
  exact QuotientGroup.isOpenMap_coe _ (hΩ.preimage continuous_inv)

theorem ratio_bound {P : Subgroup G} {h : G → ℝ} {mu : (G → ℂ) → ℂ} [IsTopologicalGroup G]
    (hS : Setup P h mu) {V : Set G} (hV : IsCompact V) :
    ∃ B : ℝ, ∀ g, ∀ x ∈ V, h (g * x) / h g ≤ B := by
  obtain ⟨C, hC, hcov⟩ := hS.cocpt
  have hcont : Continuous (fun z : G × G => h (z.1 * z.2) / h z.1) :=
    (hS.cont.comp continuous_mul).div (hS.cont.comp continuous_fst) (fun z => (hS.pos _).ne')
  obtain ⟨B, hB⟩ := (hC.prod hV).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨B, fun g x hx => ?_⟩
  obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
  have hlaw := hS.law q hq c (c * x)
  have heq : h (q * c * x) / h (q * c) = h (c * x) / h c := by
    rw [div_eq_div_iff (hS.pos _).ne' (hS.pos _).ne', mul_assoc]
    linear_combination (-1 : ℝ) * hlaw
  rw [heq]
  have hb := hB (c, x) ⟨hc, hx⟩
  simp only [Real.norm_eq_abs] at hb
  exact le_trans (le_abs_self _) hb

theorem local_null [IsTopologicalGroup G] [LocallyCompactSpace G] {P : Subgroup G}
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] {h : G → ℝ} {mu : (G → ℂ) → ℂ}
    (hS : Setup P h mu) {ν : Measure (G ⧸ P)} [IsFiniteMeasure ν]
    (hInv : ∀ x, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν)
    {Ω : Set G} (hΩ : IsOpen Ω) (hP : ∀ p ∈ P, ∀ x ∈ Ω, p * x ∈ Ω) (hF : Few P h mu Ω) (q0 : G ⧸ P) :
    ∃ W : Set (G ⧸ P), IsOpen W ∧ q0 ∈ W ∧ ν ({q | rp q ∉ Ω} ∩ W) = 0 := by
  classical
  obtain ⟨U, d, hUo, hgU, hUP, hfew⟩ := hF (rp q0)
  have hφ : Continuous (fun z : G × G => rp q0 * z.1 * z.2⁻¹) :=
    (continuous_const.mul continuous_fst).mul continuous_snd.inv
  have hmem : (fun z : G × G => rp q0 * z.1 * z.2⁻¹) ⁻¹' U ∈ 𝓝 ((1 : G), (1 : G)) :=
    hφ.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by simpa using hgU))
  obtain ⟨N0, hN0, N1, hN1, hsub⟩ := mem_nhds_prod_iff.mp hmem
  obtain ⟨V, hV1, hVN1, hVc⟩ := local_compact_nhds hN1
  obtain ⟨B, hB⟩ := ratio_bound hS hVc
  have hNo : IsOpen (interior N0) := isOpen_interior
  have h1N : (1 : G) ∈ interior N0 := mem_interior_iff_mem_nhds.mpr hN0
  let U' : Set G := {y | ∃ p ∈ P, ∃ n ∈ interior N0, y = p * (rp q0 * n)}
  have hU'o : IsOpen U' := by
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨p, hp, n, hn, rfl⟩
    refine ⟨(fun z => (p * rp q0)⁻¹ * z) ⁻¹' interior N0, ?_, ?_, ?_⟩
    · intro z hz
      exact ⟨p, hp, (p * rp q0)⁻¹ * z, hz, by group⟩
    · exact hNo.preimage (continuous_const.mul continuous_id)
    · show (p * rp q0)⁻¹ * (p * (rp q0 * n)) ∈ interior N0
      simpa [mul_assoc] using hn
  have hU'P : ∀ p ∈ P, ∀ x ∈ U', p * x ∈ U' := by
    rintro p hp x ⟨p', hp', n, hn, rfl⟩
    exact ⟨p * p', P.mul_mem hp hp', n, hn, (mul_assoc _ _ _).symm⟩
  have hgU' : rp q0 ∈ U' := ⟨1, P.one_mem, 1, h1N, by simp⟩
  have hshift : ∀ y ∈ U', ∀ γ ∈ V, y * γ⁻¹ ∈ U := by
    rintro y ⟨p, hp, n, hn, rfl⟩ γ hγ
    have h1 := hsub (Set.mk_mem_prod (interior_subset hn) (hVN1 hγ))
    simp only [Set.mem_preimage] at h1
    have h2 := hUP p hp _ h1
    simpa [mul_assoc] using h2
  refine ⟨{q | rp q ∈ U'}, isOpen_rp P hU'o hU'P, hgU', ?_⟩
  have hopenU : IsOpen {q : G ⧸ P | rp q ∈ U} := isOpen_rp P hUo hUP
  have hopenΩ0 : IsOpen {q : G ⧸ P | rp q ∈ Ω} := isOpen_rp P hΩ hP
  have hopenR : ∀ (S : Set G), IsOpen S → (∀ p ∈ P, ∀ x ∈ S, p * x ∈ S) → ∀ γ : G,
      IsOpen {q : G ⧸ P | rp q * γ ∈ S} := fun S hSo hSP γ =>
    isOpen_rp P (hSo.preimage (continuous_mul_const γ)) (fun p hp x hx => by
      show p * x * γ ∈ S
      rw [mul_assoc]
      exact hSP p hp _ hx)
  let A : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ U} ∩ {q | rp q * γ ∈ Ω}ᶜ
  let E' : G → Set (G ⧸ P) := fun γ => {q | rp q ∈ Ω}ᶜ ∩ {q | rp q * γ⁻¹ ∈ U}
  have hAm : ∀ γ, MeasurableSet (A γ) := fun γ =>
    hopenU.measurableSet.inter (hopenR Ω hΩ hP γ).measurableSet.compl
  have hE'm : ∀ γ, MeasurableSet (E' γ) := fun γ =>
    hopenΩ0.measurableSet.compl.inter (hopenR U hUo hUP γ⁻¹).measurableSet
  have hEsub : ∀ γ ∈ V, {q | rp q ∉ Ω} ∩ {q | rp q ∈ U'} ⊆ E' γ := by
    rintro γ hγ q ⟨hq1, hq2⟩
    exact ⟨hq1, hshift _ hq2 γ hγ⟩
  have htrans : ∀ γ q, γ⁻¹ • q ∈ E' γ → q ∈ A γ := by
    rintro γ q ⟨h1, h2⟩
    obtain ⟨p, hp, hrp⟩ := rp_smul P γ q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at h1 h2
    rw [hrp] at h1 h2
    refine ⟨?_, ?_⟩
    · have h3 := hUP p⁻¹ (P.inv_mem hp) _ h2
      show rp q ∈ U
      simpa [mul_assoc] using h3
    · show ¬ (rp q * γ ∈ Ω)
      intro h4
      exact h1 (hP p hp _ h4)
  have hfin : ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (measure_ne_top ν univ))
  by_contra hne
  obtain ⟨M, hM⟩ := ENNReal.exists_nat_mul_gt hne hfin
  obtain ⟨γ, hγ, hcnt⟩ := hfew V hV1 M
  have hstep : ∀ j, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ENNReal.ofReal B * ν (A (γ j)) := by
    intro j
    have hI := hInv (γ j) (hγ j).2 ((E' (γ j)).indicator 1) (measurable_one.indicator (hE'm _))
    calc ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) ≤ ν (E' (γ j)) := measure_mono (hEsub _ (hγ j).1)
      _ = ∫⁻ q, (E' (γ j)).indicator 1 q ∂ν := (lintegral_indicator_one (hE'm _)).symm
      _ = ∫⁻ q, (E' (γ j)).indicator 1 ((γ j)⁻¹ • q) *
            ENNReal.ofReal (h (rp q * γ j) / h (rp q)) ∂ν := hI.symm
      _ ≤ ∫⁻ q, (A (γ j)).indicator 1 q * ENNReal.ofReal B ∂ν := by
          apply lintegral_mono
          intro q
          apply mul_le_mul'
          · simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;>
              first | exact le_rfl | exact zero_le | exact absurd (htrans _ _ h1) h2
          · exact ENNReal.ofReal_le_ofReal (hB _ _ (hγ j).1)
      _ = ν (A (γ j)) * ENNReal.ofReal B := by
          rw [lintegral_mul_const _ (measurable_one.indicator (hAm _)), lintegral_indicator_one (hAm _)]
      _ = ENNReal.ofReal B * ν (A (γ j)) := mul_comm _ _
  have hpt : ∀ q, ∑ j, (A (γ j)).indicator 1 q ≤ (d : ℝ≥0∞) := by
    intro q
    by_cases hq : rp q ∈ U
    · have hc := hcnt (rp q) hq
      have e : (↑(Finset.univ.filter (fun j => rp q * γ j ∉ Ω)) : Set (Fin M))
          = {j | rp q * γ j ∉ Ω} := by
        ext j
        simp
      rw [← e, Set.ncard_coe_finset] at hc
      calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q
          ≤ ∑ j, (if rp q * γ j ∉ Ω then (1 : ℝ≥0∞) else 0) := by
            apply Finset.sum_le_sum
            intro j _
            simp only [Set.indicator_apply, Pi.one_apply]
            split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd h2 h1.2
        _ = ((Finset.univ.filter (fun j => rp q * γ j ∉ Ω)).card : ℝ≥0∞) := by
            rw [Finset.sum_boole]
        _ ≤ d := by exact_mod_cast hc
    · calc ∑ j, (A (γ j)).indicator (1 : G ⧸ P → ℝ≥0∞) q = 0 :=
            Finset.sum_eq_zero (fun j _ => Set.indicator_of_notMem (by exact fun h => hq h.1) _)
        _ ≤ d := zero_le
  have hsumA : ∑ j, ν (A (γ j)) ≤ (d : ℝ≥0∞) * ν univ := by
    calc ∑ j, ν (A (γ j)) = ∑ j, ∫⁻ q, (A (γ j)).indicator 1 q ∂ν :=
          Finset.sum_congr rfl (fun j _ => (lintegral_indicator_one (hAm _)).symm)
      _ = ∫⁻ q, ∑ j, (A (γ j)).indicator 1 q ∂ν :=
          (lintegral_finsetSum _ (fun j _ => measurable_one.indicator (hAm _))).symm
      _ ≤ ∫⁻ _q, (d : ℝ≥0∞) ∂ν := lintegral_mono hpt
      _ = (d : ℝ≥0∞) * ν univ := lintegral_const _
  have hMle : (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
      ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by
    calc (M : ℝ≥0∞) * ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'})
        = ∑ _j : Fin M, ν ({q | rp q ∉ Ω} ∩ {q | rp q ∈ U'}) := by simp
      _ ≤ ∑ j, ENNReal.ofReal B * ν (A (γ j)) := Finset.sum_le_sum (fun j _ => hstep j)
      _ = ENNReal.ofReal B * ∑ j, ν (A (γ j)) := (Finset.mul_sum _ _ _).symm
      _ ≤ ENNReal.ofReal B * ((d : ℝ≥0∞) * ν univ) := by gcongr
  exact absurd hM (not_lt.mpr hMle)

theorem nullC_of_invM : InvM → NullC := by
  intro hInvM
  unfold NullC ForSet
  intro G _ _ _ _ _ _ P _ _ h mu hS ν hRepr Ω hΩ hP hF
  have : IsFiniteMeasure ν := hRepr.1
  have hInv : ∀ x : G, Inv P h mu x → ∀ F : G ⧸ P → ℝ≥0∞, Measurable F →
      ∫⁻ q, F (x⁻¹ • q) * ENNReal.ofReal (h (rp q * x) / h (rp q)) ∂ν = ∫⁻ q, F q ∂ν :=
    fun x hx => (hInvM G P h mu hS ν hRepr x hx).2
  apply measure_null_of_locally_null
  intro q0 _
  obtain ⟨W, hWo, hq0W, hWnull⟩ := local_null hS hInv hΩ hP hF q0
  exact ⟨{q | rp q ∉ Ω} ∩ W, inter_mem_nhdsWithin _ (hWo.mem_nhds hq0W), hWnull⟩

end GlobalTheory.CompanionTheory.RswCell.NullCompl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
section
open Matrix PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.Wedge


open ComplexOrder in
theorem pairI_of_detMono : DetMono → PairI := by
  open scoped ComplexOrder in
  intro hD ι κ _ _ _ U W
  have hG : (Uᴴ * U).PosSemidef := posSemidef_conjTranspose_mul_self U
  have hH : (Wᴴ * W).PosSemidef := posSemidef_conjTranspose_mul_self W
  have hHn : 0 ≤ ((Wᴴ * W).det).re := (Complex.le_def.1 hH.det_nonneg).1
  have hGn : 0 ≤ ((Uᴴ * U).det).re := (Complex.le_def.1 hG.det_nonneg).1
  have hGim : ((Uᴴ * U).det).im = 0 := ((Complex.le_def.1 hG.det_nonneg).2).symm
  unfold nI
  by_cases hdet : (Uᴴ * U).det = 0
  ·
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hUv : U *ᵥ v = 0 := by
      have := (Matrix.conjTranspose_mul_self_mulVec_eq_zero U v).1 hv
      exact this
    have hM : ((Uᴴ * W)ᴴ) *ᵥ v = 0 := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, ← Matrix.mulVec_mulVec, hUv,
        Matrix.mulVec_zero]
    have hd : ((Uᴴ * W)ᴴ).det = 0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, hM⟩
    have hd' : (Uᴴ * W).det = 0 := by
      rw [det_conjTranspose] at hd
      simpa using hd
    rw [hd', norm_zero]
    have : ((Uᴴ * U).det).re * ((Wᴴ * W).det).re ≥ 0 := mul_nonneg hGn hHn
    simpa using this
  · set G := Uᴴ * U with hGdef
    set M := Uᴴ * W with hMdef
    have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
    have hGi : G * G⁻¹ = 1 := mul_nonsing_inv _ hu
    have hiG : G⁻¹ * G = 1 := nonsing_inv_mul _ hu
    have hGh : Gᴴ = G := hG.isHermitian
    have hih : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hGh]
    have hMh : Mᴴ = Wᴴ * U := by
      rw [hMdef, conjTranspose_mul, conjTranspose_conjTranspose]
    set T := G⁻¹ * M with hT
    have hTh : Tᴴ = Mᴴ * G⁻¹ := by rw [hT, conjTranspose_mul, hih]
    have hGT : G * T = M := by rw [hT, ← Matrix.mul_assoc, hGi, Matrix.one_mul]
    have hX : (Tᴴ * G * T).PosSemidef := hG.conjTranspose_mul_mul_same T
    have hXe : Tᴴ * G * T = Mᴴ * T := by
      rw [Matrix.mul_assoc, hGT, hTh, Matrix.mul_assoc, ← hT]
    have hXp : (Mᴴ * T).PosSemidef := hXe ▸ hX
    have e1 : Wᴴ * (U * T) = Mᴴ * T := by rw [hMh, Matrix.mul_assoc]
    have e2 : Tᴴ * Uᴴ * W = Mᴴ * T := by
      rw [Matrix.mul_assoc, ← hMdef, hTh, Matrix.mul_assoc, ← hT]
    have e3 : Tᴴ * Uᴴ * (U * T) = Mᴴ * T := by
      rw [← hXe, hGdef]
      simp only [Matrix.mul_assoc]

    have hZ : (W - U * T)ᴴ * (W - U * T) = Wᴴ * W - Mᴴ * T := by
      rw [conjTranspose_sub, conjTranspose_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
        e1, e2, e3]
      abel
    have hmono : ((Mᴴ * T).det).re ≤ ((Wᴴ * W).det).re :=
      hD κ _ _ hXp (hZ ▸ posSemidef_conjTranspose_mul_self (W - U * T))
    have hiGd : (G⁻¹).det * G.det = 1 := by rw [← det_mul, hiG, det_one]
    have hdX : (Mᴴ * T).det * G.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
      have hc : (starRingEnd ℂ) M.det * M.det = ((‖M.det‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.conj_mul']
        push_cast
        rfl
      rw [det_mul, hT, det_mul, det_conjTranspose, ← hc, Complex.star_def]
      linear_combination ((starRingEnd ℂ) M.det * M.det) * hiGd
    have hre : ((Mᴴ * T).det).re * G.det.re = ‖M.det‖ ^ 2 := by
      have := congrArg Complex.re hdX
      rw [Complex.mul_re, hGim, mul_zero, sub_zero, Complex.ofReal_re] at this
      exact this
    rw [← hre, mul_comm]
    exact mul_le_mul_of_nonneg_left hmono hGn

end GlobalTheory.CompanionTheory.Wedge
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicFundamentalDomainSplit
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem exists_borel_section_ker :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) [Countable Γ], (∃ U ∈ 𝓝 (1 : P), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∃ K : Set P, IsCompact K ∧ ∀ m ∈ π.ker, ∃ γ ∈ Γ, π γ = 1 ∧ γ * m ∈ K) → ∃ D : Set π.ker, MeasurableSet D ∧ (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) ∧ ∀ (ν : Measure π.ker) [ν.IsHaarMeasure], IsFundamentalDomain (Γ.subgroupOf π.ker) D ν ∧ ν D ≠ 0 ∧ ν D < ⊤ := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ _ hU hK
  obtain ⟨U, hU, hU1⟩ := hU
  obtain ⟨K, hKc, hK⟩ := hK
  have hcl : IsClosed (π.ker : Set P) := by
    have : (π.ker : Set P) = π ⁻¹' {1} := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [this]
    exact isClosed_singleton.preimage hπ
  have hemb : IsClosedEmbedding (Subtype.val : π.ker → P) := hcl.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace π.ker := hemb.locallyCompactSpace
  haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : BorelSpace π.ker := Subtype.borelSpace _
  haveI : Countable (Γ.subgroupOf π.ker) :=
    Function.Injective.countable (f := fun h : Γ.subgroupOf π.ker =>
      (⟨((h : π.ker) : P), h.2⟩ : Γ)) (fun a b hab => by
        have h1 : ((a : π.ker) : P) = ((b : π.ker) : P) := congrArg (fun x : Γ => (x : P)) hab
        exact Subtype.ext (Subtype.ext h1))
  haveI : DiscreteTopology (Γ.subgroupOf π.ker) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hc : Continuous fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P) :=
      continuous_subtype_val.comp continuous_subtype_val
    have : ({1} : Set (Γ.subgroupOf π.ker)) =
        (fun h : Γ.subgroupOf π.ker => ((h : π.ker) : P)) ⁻¹' interior U := by
      ext h
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact mem_interior_iff_mem_nhds.2 hU
      · intro hh
        have h1 : ((h : π.ker) : P) = 1 :=
          hU1 _ (Subgroup.mem_subgroupOf.1 h.2) (interior_subset hh)
        exact Subtype.ext (Subtype.ext h1)
    rw [this]
    exact isOpen_interior.preimage hc
  obtain ⟨D, hDm, hDu, hDf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Γ.subgroupOf π.ker)
  refine ⟨D, hDm, hDu, fun ν _ => ⟨hDf ν, (hDf ν).measure_ne_zero (NeZero.ne ν), ?_⟩⟩
  have hKc' : IsCompact ((Subtype.val : π.ker → P) ⁻¹' K) := hemb.isCompact_preimage hKc
  refine lt_of_le_of_lt
    (GlobalTheory.measure_le_of_isFundamentalDomain_of_ae_covers (hDf ν)
      (D' := (Subtype.val : π.ker → P) ⁻¹' K) (.of_forall fun m => ?_)) hKc'.measure_lt_top
  obtain ⟨γ, hγ, hπγ, hmem⟩ := hK m m.2
  have hγk : γ ∈ π.ker := hπγ
  refine ⟨⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 hγ⟩, ?_⟩
  exact hmem

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicIntegralUnfolding
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem aedisjoint_smul_image_prod : ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ₁], (∀ γ ∈ Γ, π γ ∈ Γ₁) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁), (∀ x : π.ker, ∃! g : Γ.subgroupOf π.ker, g • x ∈ D) → IsFundamentalDomain Γ₁ 𝓕₁ μ₁ → ∀ γ : Γ, γ ≠ 1 → AEDisjoint (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) (γ • (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))) (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)) := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ hΓ ν _ μ₁ _ D 𝓕₁ hD h𝓕 γ hγ
  have hker : ∀ z : π.ker, π (z : P) = 1 := fun z => MonoidHom.mem_ker.1 z.2
  have hfa : ∀ z : π.ker × G₁, GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι z = (z.1 : P) * ι z.2 :=
    GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo_apply ι π hι hπ hπι
  set f := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with hf
  have hπx : ∀ z : π.ker × G₁, π (f z) = z.2 := by
    intro z
    rw [hfa, map_mul, hker, one_mul, hπι]
  let g : Γ₁ := ⟨π γ, hΓ γ γ.2⟩
  have hsub : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) ⊆ π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁) := by
    rintro x ⟨⟨y, ⟨z, ⟨-, hz⟩, rfl⟩, rfl⟩, ⟨z', ⟨-, hz'⟩, hzx⟩⟩
    dsimp only at hzx ⊢
    have hγπ : π (γ • f z) = π γ * z.2 := by
      rw [Subgroup.smul_def, smul_eq_mul, map_mul, hπx]
    refine ⟨⟨z.2, hz, ?_⟩, ?_⟩
    · dsimp only
      rw [hγπ, Subgroup.smul_def, smul_eq_mul]
    · rw [← hzx, hπx]
      exact hz'
  by_cases hg : g = 1
  · have hγk : (γ : P) ∈ π.ker := MonoidHom.mem_ker.2 (congrArg Subtype.val hg)
    suffices hempty : γ • (f '' (D ×ˢ 𝓕₁)) ∩ f '' (D ×ˢ 𝓕₁) = ∅ by
      show Measure.map f (ν.prod μ₁) _ = 0
      rw [hempty, measure_empty]
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨⟨y, ⟨z, ⟨hz1, hz2⟩, rfl⟩, rfl⟩, ⟨z', ⟨hz1', hz2'⟩, hzx⟩⟩
    dsimp only at hzx
    have h2 : z'.2 = z.2 := by
      have := congrArg π hzx
      rw [hπx, Subgroup.smul_def, smul_eq_mul, map_mul, hπx, MonoidHom.mem_ker.1 hγk, one_mul] at this
      exact this
    have h1 : (z'.1 : P) = (γ : P) * z.1 := by
      have := hzx
      rw [hfa, Subgroup.smul_def, smul_eq_mul, hfa, h2, ← mul_assoc] at this
      exact mul_right_cancel this
    let γk : Γ.subgroupOf π.ker := ⟨⟨γ, hγk⟩, Subgroup.mem_subgroupOf.2 γ.2⟩
    obtain ⟨g₀, -, huniq⟩ := hD z.1
    have e1 : (1 : Γ.subgroupOf π.ker) = g₀ := huniq 1 (by show (1 : Γ.subgroupOf π.ker) • z.1 ∈ D; rw [one_smul]; exact hz1)
    have e2 : γk = g₀ := huniq γk (by
      show γk • z.1 ∈ D
      have : γk • z.1 = z'.1 := Subtype.ext (by rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]; exact h1.symm)
      rw [this]
      exact hz1')
    apply hγ
    have := congrArg (fun t : Γ.subgroupOf π.ker => ((t : π.ker) : P)) (e2.trans e1.symm)
    exact Subtype.ext this
  · have hN : μ₁ (g • 𝓕₁ ∩ 𝓕₁) = 0 := by
      have := h𝓕.aedisjoint hg
      simp only [Function.onFun, one_smul] at this
      exact this
    have hpre : f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = Set.univ ×ˢ (g • 𝓕₁ ∩ 𝓕₁) := by
      ext z
      simp only [Set.mem_preimage, hπx, Set.mem_prod, Set.mem_univ, true_and]
    have hmap : Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = 0 := by
      rw [show Measure.map f (ν.prod μ₁) (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁)) = (ν.prod μ₁) (f ⁻¹' (π ⁻¹' (g • 𝓕₁ ∩ 𝓕₁))) from
        f.toMeasurableEquiv.map_apply _, hpre, Measure.prod_prod, hN, mul_zero]
    exact measure_mono_null hsub hmap

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicLeviIntegralFormula
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

theorem setLIntegral_splitHomeo_image_prod
    (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P]
    [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P]
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (hπι : ∀ u, π (ι u) = u) (ν : Measure π.ker) [ν.IsHaarMeasure]
    (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] (D : Set π.ker) (𝓕₁ : Set G₁) :
    MeasurableSet D → NullMeasurableSet 𝓕₁ μ₁ →
      NullMeasurableSet (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁))
        (Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) ∧
      ∀ f : P → ℝ≥0∞, Measurable f →
        ∫⁻ p in (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι '' (D ×ˢ 𝓕₁)), f p
            ∂(Measure.map (GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι) (ν.prod μ₁)) =
          ∫⁻ u in 𝓕₁, ∫⁻ m in D, f ((m : P) * ι u) ∂ν ∂μ₁ := by
  intro hD h𝓕
  have hker : IsClosed ((π.ker : Set P)) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  have hsc : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hlc : LocallyCompactSpace π.ker := hker.locallyCompactSpace
  have hσc : SigmaCompactSpace π.ker := sigmaCompactSpace_of_locallyCompact_secondCountable
  have hνσ : SigmaFinite ν := Measure.IsHaarMeasure.sigmaFinite ν
  set e := GlobalTheory.CompanionTheory.SplitExtLat.splitHomeo ι π hι hπ hπι with he
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  refine ⟨?_, ?_⟩
  · rw [e.image_eq_preimage_symm]
    exact (hD.nullMeasurableSet.prod h𝓕).preimage
      (MeasurableEquiv.quasiMeasurePreserving_symm (ν.prod μ₁) e.toMeasurableEquiv)
  · intro f hf
    rw [hemb.restrict_map, Set.preimage_image_eq _ e.injective, hemb.lintegral_map,
      ← Measure.prod_restrict, lintegral_prod_symm']
    · rfl
    · exact hf.comp hemb.measurable

end GlobalTheory.CompanionTheory.SplitExtLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorPrimeOverIdealCompletionStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_prime_over_ideal_completion : ∀ {B R C M : Type} [CommRing B] [CommRing R] [CommRing C] [Algebra B R] [Algebra B C] [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower B R M] [Module.Finite R M] [IsNoetherianRing (R ⊗[B] C)] (I : Ideal B) (y : M), (∀ n : ℕ, y ⊗ₜ[B] (1 : C) ∈ LinearMap.range ((I ^ (n + 1) • ⊤ : Submodule B M).subtype.rTensor C)) → ∀ Q₁ : Ideal (R ⊗[B] C), Q₁.IsPrime → I.map (algebraMap B R) ≤ Q₁.comap (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[B] C) → ∃ w : R ⊗[B] C, w ∉ Q₁ ∧ w • ((1 : R ⊗[B] C) ⊗ₜ[R] y) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | exact GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change | (intros; apply GlobalTheory.CompanionTheory.KrullBaseChange.krull_after_base_change <;> assumption)
end

