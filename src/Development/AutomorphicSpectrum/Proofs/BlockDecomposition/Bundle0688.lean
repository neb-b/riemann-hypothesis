module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.BoxIntegrals.MeanBlocks
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0682
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0683
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0685
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0096
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneProduct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneGramMeasurableSection
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import Development.WeilBound.CoreStatements.ThetaDilations.Bundle0001
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0316
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0317

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficient
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : IsPer (chn ψ β) := fun γ hγ x => by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem trace_bl_mul {R : Type} [CommRing R] (hn : ρ + p = n) (a z : Matrix (Fin ρ) (Fin ρ) R) (d y : Matrix (Fin p) (Fin p) R)
    (x : Matrix (Fin ρ) (Fin p) R) (c : Matrix (Fin p) (Fin ρ) R) :
    Matrix.trace (bl hn a 0 0 d * bl hn z x c y) = Matrix.trace (a * z) + Matrix.trace (d * y) := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have h : ∀ M : Matrix (Fin ρ ⊕ Fin p) (Fin ρ ⊕ Fin p) R,
      Matrix.trace (M.submatrix (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm) = Matrix.trace M :=
    fun M => Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun j => M j j)
  rw [h]
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem map_dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) :
    (dsum hn b₀ β').1.map (incA D) = bl hn (b₀.1.map (incA D)) 0 0 (β'.1.map (incA D)) := by
  refine Matrix.ext fun i j => ?_
  simp only [dsum, bl, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> simp

theorem pr_split (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    GlobalTheory.CompanionTheory.FourierN.pr (dsum hn b₀ β').1 (bT hn z x y).1 = GlobalTheory.CompanionTheory.FourierN.pr b₀.1 z.1 + GlobalTheory.CompanionTheory.FourierN.pr β'.1 y.1 := by
  simp only [GlobalTheory.CompanionTheory.FourierN.pr, ← GlobalTheory.CompanionTheory.FourierN.halfTr_add]
  congr 1
  rw [map_dsum]
  exact trace_bl_mul hn _ _ _ _ _ _

theorem chn_split {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p)
    (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    chn ψ (dsum hn b₀ β') (bT hn z x y) = conj (chz ψ b₀ z) * chn ψ β' y := by
  rw [chn_eq, pr_split, neg_add, AddChar.map_add_eq_mul, chn_eq]
  congr 1
  exact (conj_psi hψ _).symm

theorem coef_pm (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖)
    {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)} (hp : IsCovolOneH lp 𝓖p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (β' : HermE D p) (Φ : hermA D n → ℂ) (hc : Continuous Φ) (hper : IsPer Φ) :
    ∫ b in 𝓖, Φ b * chn ψ (dsum hn b₀ β') b ∂lam = ∫ y in 𝓖p, pm hn m ψ b₀ Φ y * chn ψ β' y ∂lp := by
  have hd := _root_.GlobalTheory.CompanionTheory.PcFc.mean_blocks hn m h hp (fun b => Φ b * chn ψ (dsum hn b₀ β') b) (hc.mul (chn_cont hψ _))
    (fun γ hγ x => by
      show Φ (γ + x) * chn ψ (dsum hn b₀ β') (γ + x) = _
      rw [hper γ hγ x, chn_per hψ _ γ hγ x])
  rw [hd]
  refine integral_congr_ae (.of_forall fun y => ?_)
  show ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * chn ψ (dsum hn b₀ β') (bT hn z x y) ∂m.lz ∂m.μ = pm hn m ψ b₀ Φ y * chn ψ β' y
  simp only [chn_split hψ, ← mul_assoc]
  simp only [integral_mul_const, pm]

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem per_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    IsPer (fun b => F (nb b * g)) := fun γ hγ x => by
  show F (nb (γ + x) * g) = F (nb x * g)
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

def zH (D : D7) (p : ℕ) : HermE D p := ⟨0, by
  rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]⟩

theorem chn_zero {D : D7} {p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (y : hermA D p) : chn ψ (zH D p) y = 1 := by
  have h := GlobalTheory.CompanionTheory.FourierN.pr_zero_left (D := D) (n := p) y.1
  simp only [GlobalTheory.CompanionTheory.FourierN.pr] at h
  simp only [chn, zH, h, neg_zero, AddChar.map_zero_eq_one]

theorem pcFc : PcFc := by
  intro D n ρ p hn M m ψ hψ F hF hinv
  obtain ⟨lp, 𝓖p, hp⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D p
  refine ⟨?_, ?_⟩
  · intro h nb lam 𝓖 hC β hr g
    obtain ⟨a, b₀, β', hd, he⟩ := GlobalTheory.T.hermitian_block_diagonal_normal_form hn β hr
    obtain ⟨q, hq⟩ := GlobalTheory.T.fourier_coefficient_conjugation hψ F hF hinv hC a β
    have h1 := hq (q⁻¹ * g)
    rw [mul_inv_cancel_left] at h1
    rw [h1, he]
    have h2 := coef_pm hn m hC.2 hp hψ b₀ β' _ (cont_nb hF hC.1 (q⁻¹ * g)) (per_nb hinv hC.1 (q⁻¹ * g))
    refine h2.trans ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
    rw [← _root_.GlobalTheory.CompanionTheory.PcNb.pc_nb M m ψ b₀ F hC.1, h b₀ hd, zero_mul]
  · intro hR b₀ hb β hβ nb lam 𝓖 hC g
    have hc := cont_nb hF hC.1 g
    have hpr := per_nb hinv hC.1 g
    have key := _root_.GlobalTheory.CompanionTheory.PcFc.const_of_coeff hp hψ (pm hn m ψ b₀ (fun b => F (nb b * g))) (GlobalTheory.T.continuous_partial_fourier_mean hn m hψ b₀ _ hc hpr)
      (GlobalTheory.T.periodic_partial_fourier_mean hn m ψ b₀ _ hpr)
      (fun a ha => by
        rw [← coef_pm hn m hC.2 hp hψ b₀ a _ hc hpr]
        exact hR nb lam 𝓖 hC _ (_root_.GlobalTheory.CompanionTheory.PcFc.rank_dsum_ge hn b₀ hb a ha) g)
    have e0 : β = dsum hn b₀ (zH D p) := Subtype.ext hβ
    have e1 : fc ψ lam 𝓖 nb F β g = ∫ y in 𝓖p, pm hn m ψ b₀ (fun b => F (nb b * g)) y * chn ψ (zH D p) y ∂lp := by
      rw [e0]
      exact coef_pm hn m hC.2 hp hψ b₀ _ _ hc hpr
    have e2 : pc M m ψ b₀ F g = pm hn m ψ b₀ (fun b => F (nb b * g)) 0 := by
      have := _root_.GlobalTheory.CompanionTheory.PcNb.pc_nb M m ψ b₀ F hC.1 g 0
      have hz : bT hn (0 : hermA D ρ) 0 (0 : hermA D p) = 0 := by
        apply Subtype.ext
        show (bl hn (0 : Mx D ρ ρ) 0 (adj (0 : Mx D ρ p)) 0 : Mx D n n) = 0
        rw [adj_zero, bl, Matrix.fromBlocks_zero]
        rfl
      rw [hz, GlobalTheory.CompanionTheory.FourierN.nb_zero hC.1, one_mul] at this
      exact this
    rw [e1, e2]
    simp only [chn_zero, mul_one]
    rw [show (fun y => pm hn m ψ b₀ (fun b => F (nb b * g)) y) = fun _ => pm hn m ψ b₀ (fun b => F (nb b * g)) 0 from funext key]
    rw [setIntegral_const, measureReal_def, hp.2.2]
    simp

theorem target : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := fun _ _ => pcFc

end GlobalTheory.CompanionTheory.PcFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

theorem sigmaFinite_of_integrable {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] {U : Set V} (hU : IsOpen U)
    {μ : Measure V} (h0 : μ Uᶜ = 0)
    (hint : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U → Integrable φ μ) :
    SigmaFinite μ := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  have hfin : ∀ n, μ (Subtype.val '' K n) < ∞ := by
    intro n
    have hLc : IsCompact (Subtype.val '' K n) := (K.isCompact n).image continuous_subtype_val
    have hLU : Subtype.val '' K n ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hLc hU hLU
    have hi := hint f f.continuous hfc hfs
    have hle : μ (Subtype.val '' K n) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
      calc μ (Subtype.val '' K n) = ∫⁻ x in Subtype.val '' K n, 1 ∂μ := by simp
        _ = ∫⁻ x in Subtype.val '' K n, ENNReal.ofReal (f x) ∂μ :=
            setLIntegral_congr_fun hLc.measurableSet fun x hx => by simp [hf1 hx]
        _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := setLIntegral_le_lintegral _ _
    exact hle.trans_lt hi.lintegral_lt_top
  refine ⟨⟨⟨fun n => Subtype.val '' K n ∪ Uᶜ, fun _ => Set.mem_univ _, fun n => ?_, ?_⟩⟩⟩
  · exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hfin n, by simp [h0]⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.2 ⟨K.find ⟨x, hx⟩, Or.inl ⟨⟨x, hx⟩, K.mem_find _, rfl⟩⟩
    · exact Set.mem_iUnion.2 ⟨0, Or.inr hx⟩

end GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeStage


open GlobalTheory.CompanionTheory.SW.StageMeasure in
set_option maxHeartbeats 4000000 in
theorem fibre_block_stages_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  obtain ⟨-, hW, hH⟩ := _root_.GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J hJ t ht
  obtain ⟨g₁, g₂, g₃, g₄, g₅, gAct⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM (M + 1) _ hJ' R
  obtain ⟨u₁, u₂, u₃, u₄, u₅, uAct⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ R
  have hgram : gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    rw [gram_first, inclR_algebraMap]
    rfl
  have hunit : IsUnit (gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))).det := by
    rw [gram_first]
    have e := Matrix.det_fin_one (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t))
    show IsUnit (Matrix.det (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t)))
    rw [e]
    exact ((isUnit_iff_ne_zero.2 (by simpa using ht)).map (inclR (F := F) R))
  obtain ⟨s, hsm, hs₁, hs₂⟩ := _root_.GlobalTheory.CompanionTheory.SW.OrbitSection.orbit_section F E σ hCM (M + 1) _ hJ' R hR _ hunit
  have hs₁' := fun y (hy : gramR R σ (blockOne (algebraMap F E t) J) y =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1)) => hs₁ y (hy.trans hgram.symm)
  have hs₂' : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
      ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
        gramR R σ (blockOne (algebraMap F E t) J) y =
          (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C' := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hs₂ C hC
    exact ⟨C', hC', fun y hy hg => h y hy (hg.trans hgram.symm)⟩
  obtain ⟨B, hBo, hTB, fib, hfib, hfibT⟩ := _root_.GlobalTheory.CompanionTheory.SW.StageF.fibre_family_free_near_block F E σ hCM M J hJ t ht n T hT hT' R hR
    d b lam hlam m₁ m' hm₁ hm' c hc s hsm hs₁' hs₂'
  obtain ⟨h₁, h₂, h₃, h₄, hlift⟩ := _root_.GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hlift (M + 1) _ hJ'
  have hWn := hW (n + 1) (M + 1)
  have hHn := hH (n + 1)
  have hBn := hBorel (n + 1) (M + 1)
  have hU' : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) = g ⁻¹' B := by
    ext X
    simp [hg X]
  have hfree := _root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR (n + 1) (M + 1)
  have hm₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val
      (g ⁻¹' Set.univ ∩ {X | LinearIndependent (R ⊗[F] E) X})
      (coordHerm R σ b lam (n + 1)) Set.univ m := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact hm
  rw [hU'] at hfib
  have hmT : fib (hermOf R σ _ hT') = m (hermOf R σ _ hT') :=
    GlobalTheory.T.measurable_embedding_of_injective_proper _ _ _ (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) g Subtype.val Subtype.val_injective hgc hg _ hfree
      Set.univ B isOpen_univ hBo (Set.subset_univ _) m fib hm₀ hfib _ hTB
  have hBa := hBorel (n + 1) (M + 1)
  have hBb := hBorel n M
  have hBc := hBorel 1 (M + 1)
  have hact : Measurable fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ p.1 p.2 := (gAct (n + 1)).1.measurable
  have hactu : ∀ u : HA R σ J, Measurable (actW R σ J u : (Fin n → Fin M → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E) :=
    fun u => ((uAct n).1.comp (Continuous.prodMk_right u)).measurable
  have hframe : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      actW R σ _ (s p.1) (consTup p.2) :=
    hact.comp ((hsm.comp measurable_fst).prodMk (measurable_consTup.comp measurable_snd))
  have hF : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      φ (actW R σ _ (s p.1) (consTup p.2)) := hφ.comp hframe
  haveI hσ : SigmaFinite (m' (hermOf R σ T hT)) := by
    refine sigmaFinite_of_integrable (_root_.GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM R hR n M) ?_ ?_
    · exact measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (hm'.1 _)
    · intro f hfc hfs hft
      exact (hm'.2.2 f hfc hfs hft).1 _ (Set.mem_univ _)
  refine ⟨fun y => ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT)),
    hF.lintegral_prod_right', ?_, ?_⟩
  · intro h
    obtain ⟨ι, -, hιm, hιr, -, hιa⟩ := GlobalTheory.CompanionTheory.SW.StabFirst.stab_first F E σ hCM M J hJ t ht R
    have hy := hs₁' (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0)))
      (((gAct 1).2.2.2 h _).trans hgram)
    set y := actW R σ _ h (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) with hydef
    have hfix : actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      calc actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))
          = actW R σ _ (s y)⁻¹ y := (gAct 1).2.2.1 _ _ _
        _ = actW R σ _ (s y)⁻¹ (actW R σ _ (s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))) := by
            rw [hy]
        _ = actW R σ _ ((s y)⁻¹ * s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) :=
            ((gAct 1).2.2.1 _ _ _).symm
        _ = _ := by rw [inv_mul_cancel, (gAct 1).2.1]
    obtain ⟨u, hu⟩ := (hιr _).2 hfix
    have hh : h = s y * ι u := by rw [hu, mul_inv_cancel_left]
    have hX : ∀ X : Fin n → Fin M → R ⊗[F] E,
        actW R σ _ h (consTup X) = actW R σ _ (s y) (consTup (actW R σ J u X)) := by
      intro X
      rw [hh, (gAct (n + 1)).2.2.1, hιa]
    have hinv := _root_.GlobalTheory.CompanionTheory.WeilSiegel.Free.FibreInv.map_actW_fibre_free F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' u (hermOf R σ T hT)
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => φ (actW R σ _ (s y) (consTup X)) :=
      hφ.comp (hact.comp ((measurable_const (a := s y)).prodMk measurable_consTup))
    calc ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT))
        = ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂((m' (hermOf R σ T hT)).map (actW R σ J u)) := by rw [hinv]
      _ = ∫⁻ X, φ (actW R σ _ (s y) (consTup (actW R σ J u X))) ∂(m' (hermOf R σ T hT)) :=
          lintegral_map hmeas (hactu u)
      _ = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT)) := by simp only [hX]
  · rw [← hmT, hfibT, lintegral_smul_measure, lintegral_map hφ hframe, lintegral_prod _ hF.aemeasurable]
    simp [ENNReal.smul_def]

end GlobalTheory.CompanionTheory.WeilSiegel.FreeStage
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BaseSimil

open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def g1 (x : E) (hx : x ≠ 0) : GL (Fin 1) E :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.of fun _ _ => x) (by rw [Matrix.det_fin_one]; exact hx)

theorem scalar_matrix_apply (x : E) (hx : x ≠ 0) (i j : Fin 1) :
    ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) i j = x := rfl

theorem tuple_action_scalar_eq_mul (R : Type) [CommRing R] [Algebra F R] (x : E) (hx : x ≠ 0) :
    actTup R (bc (inclR R) (g1 x hx)) =
      fun (X : Fin 1 → Fin 1 → R ⊗[F] E) a i => inclR R x * X a i := by
  funext X a i
  have hi : ∀ j : Fin 1, j = i := fun j => Subsingleton.elim _ _
  have h1 : ((bc (inclR R) (g1 x hx) : GL (Fin 1) (R ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i 0 = inclR R x := rfl
  change ∑ j, ((bc (inclR R) (g1 x hx) : GL (Fin 1) (R ⊗[F] E)) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) i j * X a j = _
  rw [Fin.sum_univ_one, h1, Subsingleton.elim i 0]

end Alg

theorem map_fib (hS : Scal) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Nontrivial R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hL : IsLocR R) (μ : Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (ν : Measure (HermR R σ 1))
    (m : HermR R σ 1 → Measure (Fin 1 → Fin 1 → R ⊗[F] E)) (hμ : μ.IsAddHaarMeasure) (hν : ν.IsAddHaarMeasure)
    (hm : IsGramFib R σ J 1 μ ν m) (x : E) (hx : x ≠ 0) (l β : F) (hl : σ x * x = algebraMap F E l) (hβ : β ≠ 0) :
    (m (hermScal R σ (algebraMap F R β))).map (actTup R (bc (inclR R) (g1 x hx))) =
      m (hermScal R σ (algebraMap F R (l * β))) := by
  have hn : algebraMap F R l ⊗ₜ[F] (1 : E) =
      sigR R σ ((Units.map (inclR (F := F) (E := E) R : E →* R ⊗[F] E) (Units.mk0 x hx) : (R ⊗[F] E)ˣ) : R ⊗[F] E) *
        ((Units.map (inclR (F := F) (E := E) R : E →* R ⊗[F] E) (Units.mk0 x hx) : (R ⊗[F] E)ˣ) : R ⊗[F] E) := by
    change _ = sigR R σ (inclR R x) * inclR R x
    have h1 : sigR R σ (inclR R x) = inclR R (σ x) := by simp [sigR, inclR]
    rw [h1, ← map_mul, hl]
    have := (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
    change _ = (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) (algebraMap F E l)
    rw [this]
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hu : IsUnit (algebraMap F R β) := (IsUnit.mk0 _ hβ).map _
  have := hS F E σ hcm J hJ R hL μ ν m hμ hν hm _ _ _ hn hu
  rw [tuple_action_scalar_eq_mul, map_mul]
  exact this

theorem hermitian_similitude_scalar {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E)
    (x : E) (hx : x ≠ 0) (l : F) (hl : σ x * x = algebraMap F E l) :
    cT (σ : E →+* E) ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) * J *
        ((g1 x hx : GL (Fin 1) E) : Matrix (Fin 1) (Fin 1) E) = (algebraMap F E l) • J := by
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, smul_eq_mul, cT, Matrix.transpose_apply,
    Matrix.map_apply, scalar_matrix_apply]
  rw [← hl]
  change σ x * J 0 0 * x = σ x * x * J 0 0
  ring

theorem exists_norm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (hJ : IsHermND σ J) (β β' : F) (hβ : β ≠ 0)
    (hs : (sph σ J β).Nonempty) (hs' : (sph σ J β').Nonempty) (hβ' : β' ≠ 0) :
    ∃ x : E, x ≠ 0 ∧ σ x * x = algebraMap F E (β' / β) := by
  obtain ⟨X, hX⟩ := hs
  obtain ⟨Y, hY⟩ := hs'
  have hJ0 : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have e : ∀ (Z : Fin 1 → Fin 1 → E) (t : F), Z ∈ sph σ J t → σ (Z 0 0) * J 0 0 * Z 0 0 = algebraMap F E t := by
    intro Z t hZ
    have h0 := congrFun (congrFun hZ 0) 0
    simpa [gramE, hE, hform] using h0
  have eX := e X β hX
  have eY := e Y β' hY
  have hb : algebraMap F E β ≠ 0 := by simpa using hβ
  have hx : X 0 0 ≠ 0 := by
    intro h
    rw [h] at eX
    exact hb (by simpa using eX.symm)
  have hsx : σ (X 0 0) ≠ 0 := by simpa using hx
  refine ⟨Y 0 0 / X 0 0, ?_, ?_⟩
  · refine div_ne_zero ?_ hx
    intro h
    rw [h] at eY
    exact (by simpa using hβ' : algebraMap F E β' ≠ 0) (by simpa using eY.symm)
  · rw [map_div₀, map_div₀, ← eX, ← eY]
    field_simp

theorem simil : Scal → Simil := by
  intro hScal F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm β β' hβ hβ' hs hs' c hc
  have hl0 : β' / β ≠ 0 := div_ne_zero hβ' hβ
  obtain ⟨x, hx, hxl⟩ := exists_norm σ J hJ β β' hβ hs hs' hβ'
  have hγ := hermitian_similitude_scalar σ J x hx (β' / β) hxl
  obtain ⟨μ', 𝓕', hμ', h𝓕', hth⟩ := GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 (g1 x hx) (β' / β) hl0 hγ
  have hT : (fun _ _ => algebraMap F E β' : Matrix (Fin 1) (Fin 1) E) =
      (algebraMap F E (β' / β)) • (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) := by
    funext a b'
    change algebraMap F E β' = algebraMap F E (β' / β) * algebraMap F E β
    rw [← map_mul, div_mul_cancel₀ _ hβ]
  have hth1 := hth 1 _ _ hT
  have hind := GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep F E σ hcm 1 J hJ μ μ' 𝓕 𝓕' hμ h𝓕 hμ' h𝓕' 1 (fun _ _ => algebraMap F E β)
  change (thetaMeas σ J μ' 𝓕' (sph σ J β)).map _ = thetaMeas σ J μ 𝓕 (sph σ J β') at hth1
  change thetaMeas σ J μ 𝓕 (sph σ J β) = thetaMeas σ J μ' 𝓕' (sph σ J β) at hind
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  have : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := SWIsom.haar_of_loc σ hcm (Ainf F) hLi b li hli.1 1 1
  have hWv := fun v => SWIsom.haar_of_loc σ hcm (Fv F v) (hLv v) b (lam v) (hlam v).1 1 1
  have hβ'' : β' / β * β = β' := div_mul_cancel₀ _ hβ
  have sInf := map_fib hScal σ hcm J hJ (Ainf F) hLi _ _ mi hWi.1 hWi.2 hmi x hx (β' / β) β hxl hβ
  have sV := fun v => map_fib hScal σ hcm J hJ (Fv F v) (hLv v) _ _ (m v) (hWv v).1 (hWv v).2 (hm v) x hx (β' / β) β hxl hβ
  rw [hβ''] at sInf
  simp only [hβ''] at sV
  have hproj : ∀ X : Fin 1 → Fin 1 → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) (g1 x hx)) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) (g1 x hx)) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact SWIsom.map_actTup (fstA F) (g1 x hx) X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)) X) =
          actTup (Af F) (bc (inclR (Af F)) (g1 x hx)) (projFin X) := by
        funext a i
        exact SWIsom.map_actTup (sndA F) (g1 x hx) X a i
      rw [h1]
      funext a i
      exact SWIsom.map_actTup (evalV F v) (g1 x hx) (projFin X) a i
  have hfin : ∀ v, (cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β'))) (latV b v) < ⊤ := by
    intro v
    have := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hcm 1 J hJ (Fv F v) (hLv v) 1 _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermScal (Fv F v) σ (algebraMap F _ β'))).1
    have h2 := ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b 1 1).2.2.2.1 v).1.measure_lt_top
      (μ := m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    rw [Measure.smul_apply]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h2
  have hu : IsUnitProd (1 : ℝ≥0) (fun _ : HeightOneSpectrum (𝓞 F) => (1 : ℝ≥0)) :=
    ⟨Filter.Eventually.of_forall fun _ => rfl, by simp⟩
  have key := GlobalTheory.CompanionTheory.SW.MassSimil.euler_move_c F E σ hcm d b 1 1 (thetaMeas σ J μ' 𝓕' (sph σ J β))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β)))
    (mi (hermScal (Ainf F) σ (algebraMap F _ β')))
    (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β)))
    (fun v => cfac E v • m v (hermScal (Fv F v) σ (algebraMap F _ β')))
    (actTup (AF F) (bc (inclR (AF F)) (g1 x hx)))
    (actTup (Ainf F) (bc (inclR (Ainf F)) (g1 x hx))) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) (g1 x hx)))
    (SWIsom.measurable_actTup σ hcm (AF F) _) (SWIsom.measurable_of_loc σ hcm (Ainf F) hLi _)
    (fun v => SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hcm d b 1 1).2.1 (g1 x hx)) 1 (fun _ => 1) hu
    (by rw [sInf, one_smul]) (fun v => by
      rw [Measure.map_smul, sV v, one_smul]
      exact (SWIsom.measurable_of_loc σ hcm (Fv F v) (hLv v) _).aemeasurable) hfin c
  unfold EP at hc ⊢
  rw [hind] at hc
  rw [← hth1]
  exact key hc

end GlobalTheory.CompanionTheory.SW.BaseSimil
end
end

