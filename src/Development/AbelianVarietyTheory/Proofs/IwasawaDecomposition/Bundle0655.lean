module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0519
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0551
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0636
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0648
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0377
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0616
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodFrameOfHolomorphicLatticeFamily
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PeriodFrame.exists_frame_of_latFam : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), IsLatFam (Metric.ball 0 1) K → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, LinearIndependent ℝ (ζ z)) → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, ζ z i ∈ K z) → IsLatBasis (K 0) (ζ 0) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → ContinuousOn lam (logDom n a) → (∀ s ∈ logDom n a, LinearIndependent ℤ (lam s) ∧ Submodule.span ℝ (Set.range (lam s)) = ⊤ ∧ ∀ w, w ∈ K (logExp a s) ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • lam s j) → (∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) ∧ ∀ s' ∈ logDom n a, logExp a s' = logExp a s → ∀ i j, (hermForm Hm (lam s' i) (lam s' j)).im = M i j) → (∀ N : ℕ, 0 < N → ∃ S : Set (Fin r₀ → ZMod N), N ^ r₀ * Nat.card S = N ^ (2 * g) ∧ ∀ u u' : Fin r₀ → ℤ, (fun j => (u j : ZMod N)) ∈ S → ∀ s ∈ logDom n a, ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → ∃ m : ℤ, (hermForm Hm (∑ i, u i • ζ (logExp a s) i) (∑ j, u' j • ζ (logExp a s) j)).im = N * m) → ∃ (rk : ℕ) (d ρ₁ : ℝ) (P τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (Δ : (Fin n → ℂ) → Matrix {j : Fin g // rk ≤ j.val} {j : Fin g // rk ≤ j.val} ℂ), 0 < ρ₁ ∧ ρ₁ ≤ 1 ∧ 0 < d ∧ rk ≤ g ∧ (∀ i j, DifferentiableOn ℂ (fun z => P z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, IsUnit (P z).det) ∧ (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) ∧ (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) → (P (logExp a s))ᵀ * Hm * (P (logExp a s))ᵀᴴ = ((d : ℝ) : ℂ) • (((τ s).map Complex.im).map Complex.ofReal)⁻¹) ∧ ContinuousOn Δ (Metric.ball 0 ρ₁) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, ((Δ z).map Complex.im).PosDef) ∧ (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).submatrix Subtype.val Subtype.val = Δ (logExp a s)) ∧ (∀ v : Fin g → ℤ, v ≠ 0 → (∀ j : Fin g, rk ≤ j.val → v j = 0) → ∀ F : (Fin n → ℂ) → Fin g → ℂ, ContinuousOn F (Metric.ball 0 ρ₁) → ¬ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).mulVec (fun j => (v j : ℂ)) = F (logExp a s)) := by
  intro n a g r₀ r ha K ζ lam M hK hζ hζi hζK hζ0 hstd hlamc hlam hH htor
  obtain ⟨hDo, hDc, hDan, hDmaps⟩ := GlobalTheory.logDom_chart_props n a
  have hlogc : Continuous (logExp a : (Fin n → ℂ) → Fin n → ℂ) :=
    continuous_iff_continuousAt.2 fun s => (hDan s).continuousAt
  set s₀ : Fin n → ℂ := fun k => if (k : ℕ) < a then -1 else 0 with hs₀def
  have hs₀ : s₀ ∈ logDom n a := by
    simp only [logDom, Set.mem_ofPred_eq]
    intro k
    by_cases h : (k : ℕ) < a <;> simp [s₀, h]
  obtain ⟨hr, hlamR, hlamD⟩ := _root_.GlobalTheory.ShFam.Hor.LogCh.latBasis_logCover_real_holo n a g r K lam hK hlamc hlam
  have hlB : ∀ b ∈ logDom n a, IsLatBasis (K (logExp a b)) (lam b) := fun b hb => ⟨hlamR b hb, (hlam b hb).2.2⟩
  have hmemL : ∀ b ∈ logDom n a, ∀ i, lam b i ∈ K (logExp a b) := fun b hb i =>
    ((hlam b hb).2.2 _).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
  have hpre : _root_.IsPreconnected (logDom n a) := hDc.isPreconnected
  have hζc : ContinuousOn (fun s => ζ (logExp a s)) (logDom n a) := hζ.continuousOn.comp hlogc.continuousOn hDmaps
  have hcex' : ∀ i : Fin r₀, ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, m j • lam b j := fun i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => ζ (logExp a b) i) s₀ hpre hlamc ((continuous_apply i).comp_continuousOn hζc) hlB
      (fun b hb => hζK _ (hDmaps hb) i) hs₀
  have hcex : ∃ c : Matrix (Fin r₀) (Fin r) ℤ, ∀ i, ∀ b ∈ logDom n a, ζ (logExp a b) i = ∑ j, c i j • lam b j := by
    choose c hc using hcex'
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hcex
  have hsh := fun (k : Fin a) (s : Fin n → ℂ) (hs : s ∈ logDom n a) => GlobalTheory.PeriodFrame.shift_mem ha k hs
  have hTex' : ∀ (k : Fin a) (i : Fin r), ∃ m : Fin r → ℤ, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, m j • lam b j := fun k i =>
    GlobalTheory.ShFam.Hor.LogCh.exists_const_coords n g r (logDom n a) (fun b => K (logExp a b)) lam
      (fun b => lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i) s₀ hpre hlamc
      ((continuous_apply i).comp_continuousOn
        (hlamc.comp (continuous_id.add continuous_const).continuousOn fun b hb => (hsh k b hb).1))
      hlB (fun b hb => by rw [← (hsh k b hb).2]; exact hmemL _ (hsh k b hb).1 i) hs₀
  have hTex : ∃ T : Fin a → Matrix (Fin r) (Fin r) ℤ, ∀ k i, ∀ b ∈ logDom n a,
      lam (b + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) i = ∑ j, T k i j • lam b j := by
    choose T hT using hTex'
    exact ⟨T, hT⟩
  obtain ⟨T, hT⟩ := hTex
  obtain ⟨Hm₀, hH₀h, hH₀p, hH₀l⟩ := hH s₀ hs₀
  have hM₀ := hH₀l s₀ hs₀ rfl
  have hMa : Mᵀ = -M := _root_.GlobalTheory.hermForm_im_antisymm g r Hm₀ (lam s₀) M hH₀h hM₀
  have hMd : M.det ≠ 0 :=
    GlobalTheory.det_ne_zero_of_im_hermForm_eq_int g r Hm₀ (lam s₀) M hH₀p (hlamR s₀ hs₀) (hlam s₀ hs₀).2.1 hM₀
  have hTM : ∀ k, T k * M * (T k)ᵀ = M := by
    intro k
    have h1 := _root_.GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb g r r Hm₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (T k) M (fun i => hT k i s₀ hs₀) hM₀
    have h2 := hH₀l _ (hsh k s₀ hs₀).1 (hsh k s₀ hs₀).2
    ext i j
    have h3 := (h1 i j).symm.trans (h2 i j)
    exact_mod_cast h3
  have hcT : ∀ k, c * T k = c := fun k =>
    _root_.GlobalTheory.FrameFix.coeff_mul_eq_of_same_combinations g r r₀ (lam s₀) (lam (s₀ + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)))
      (ζ (logExp a s₀)) c (T k) (hlam s₀ hs₀).1 (fun i => hT k i s₀ hs₀) (fun i => hc i s₀ hs₀)
      (fun i => by rw [← (hsh k s₀ hs₀).2]; exact hc i _ (hsh k s₀ hs₀).1)
  have hcLI : LinearIndependent ℚ (fun i j => (c i j : ℚ)) :=
    GlobalTheory.rowsInd_rat_of_real g r r₀ (lam s₀) (ζ (logExp a s₀)) c (hζi _ (hDmaps hs₀)) (fun i => hc i s₀ hs₀)
  have hco := GlobalTheory.CoisoCount.coisotropic_of_torsion_count r r₀ M c hMd hcLI (by
    intro N hN
    obtain ⟨S, hcard, hS⟩ := htor N hN
    refine ⟨S, by rw [hr]; exact hcard, fun u u' hu => ?_⟩
    obtain ⟨m, hm⟩ := hS u u' hu s₀ hs₀ Hm₀ hM₀
    rw [_root_.GlobalTheory.ShFam.Hor.LogCh.Core.hermForm_im_intComb_dotProduct g r r₀ Hm₀ (lam s₀) (ζ (logExp a s₀)) c M (fun i => hc i s₀ hs₀) hM₀ u u'] at hm
    exact ⟨m, by exact_mod_cast hm⟩)
  obtain ⟨rk, α, φ, β, gm, dl, hrk, hN1, hN2, hN3, hN4, hN5, hN6, hN7⟩ := _root_.GlobalTheory.SymplecticNormalForm.exists_adapted_rational_symplectic_basis g r r₀ M c hr hMa hMd hcLI hco
  choose b hb using fun k => _root_.GlobalTheory.isometry_fixing_rowSpace_shift g r r₀ rk M (T k) c α φ β hr hMa (hTM k) (hcT k) hN1 hN2 hN3 hN5
  obtain ⟨D, Bz, hD, hBz⟩ := _root_.GlobalTheory.rat_matrix_common_denom a g b
  have hBzs : ∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → Bz k j l = 0 := by
    intro k j l h
    have h1 := hBz k j l
    rw [(hb k).1 j l h, mul_zero] at h1
    exact_mod_cast h1
  have hPeq : ∀ s ∈ logDom n a, GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α =
      GlobalTheory.PeriodFrame.combMat (lam s) (α * c.map (Int.cast : ℤ → ℚ)) :=
    fun s hs => GlobalTheory.PeriodFrame.combMat_comb _ _ c α (fun i => hc i s hs)
  have hRie : ∀ s ∈ logDom n a, ∃ Hm : Matrix (Fin g) (Fin g) ℂ,
      (∀ i j, (hermForm Hm (lam s i) (lam s j)).im = M i j) ∧
      IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det ∧ (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef ∧
      (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α)ᵀᴴ =
        ((D : ℝ) : ℂ) • (((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).map Complex.ofReal)⁻¹ := by
    intro s hs
    obtain ⟨Hm, h1, h2, h3⟩ := hH s hs
    refine ⟨Hm, h3 s hs rfl, ?_⟩
    unfold GlobalTheory.PeriodFrame.perTau
    rw [hPeq s hs]
    exact _root_.GlobalTheory.PeriodFrame.riemann_relations_frame g r Hm M (lam s) _ φ D hD h1 h2 (hlamR s hs) (h3 s hs rfl) hN1 hN2 hN3
  have hdet : ∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det := fun s hs => by
    obtain ⟨_, _, h, _⟩ := hRie s hs
    exact h
  obtain ⟨hPd, hτd⟩ := _root_.GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau n a g r₀ r ζ lam α φ D hζ hlamD hdet
  have hτsm : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).IsSymm ∧
      ((GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).map Complex.im).PosDef := fun s hs _ => by
    obtain ⟨_, _, _, h1, h2, _⟩ := hRie s hs
    exact ⟨h1, h2⟩
  have hmono : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → ∀ k : Fin a,
      GlobalTheory.PeriodFrame.perTau a ζ lam α φ D (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) =
        GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s + (Bz k).map (Int.cast : ℤ → ℂ) := by
    intro s hs _ k
    unfold GlobalTheory.PeriodFrame.perTau
    rw [(hsh k s hs).2, hPeq s hs,
      GlobalTheory.PeriodFrame.combMat_comb (lam (s + _)) (lam s) (T k) φ (fun i => hT k i s hs), (hb k).2]
    exact GlobalTheory.PeriodFrame.combMat_shift (lam s) _ φ (b k) D (Bz k) (hPeq s hs ▸ hdet s hs) (hBz k)
  obtain ⟨hpsd, τ₀, hτ₀d, hτ₀s, hτ₀e⟩ :=
    _root_.GlobalTheory.ShFam.Hor.LogCh.PerExt.periodMatrix_extension n a g ha 1 (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D) Bz one_pos le_rfl hτd hτsm hmono
  have hPu : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det :=
    _root_.GlobalTheory.PeriodFrame.isUnit_det_combMat_on_ball n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ Bz hD hζ hstd (fun s hs i => hc i s hs) hN7 hN6 hdet hτ₀d
      hBzs hτ₀e
  have hcont : ∀ j l, ContinuousOn (fun z => τ₀ z j l) (Metric.ball 0 1) := fun j l => (hτ₀d j l).continuousOn
  have hagree : ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 →
      (GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
        (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) =
        (τ₀ (logExp a s)).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
          (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g) := by
    intro s hs hz
    rw [hτ₀e s hs hz]
    ext ⟨j, hj⟩ ⟨l, hl⟩
    simp [Matrix.sum_apply, hBzs _ j l (Or.inl hj)]
  refine ⟨rk, (D : ℝ), 1, fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α, GlobalTheory.PeriodFrame.perTau a ζ lam α φ D, Bz,
    fun z => (τ₀ z).submatrix Subtype.val Subtype.val, one_pos, le_rfl, by exact_mod_cast hD, hrk, hPd, hPu, hτd,
    hτsm, hmono, hBzs, ?_, ?_, ?_, hagree, ?_⟩
  · intro s hs hz Hm hHm
    obtain ⟨Hm', h1, _, _, _, h5⟩ := hRie s hs
    have hHH : Hm = Hm' :=
      _root_.GlobalTheory.hermForm_eq_of_im_eq_on_span g r Hm Hm' (lam s) (hlam s hs).2.1 (fun i j => (hHm i j).trans (h1 i j).symm)
    subst hHH
    exact h5
  · exact continuousOn_pi.2 fun j => continuousOn_pi.2 fun l => hcont j.1 l.1
  · refine _root_.GlobalTheory.posDef_im_on_ball_of_logExp n a {j : Fin g // rk ≤ j.val} (fun z => (τ₀ z).submatrix (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g)
      (Subtype.val : {j : Fin g // rk ≤ j.val} → Fin g))
      (fun j l => hτ₀d j.1 l.1) ?_
    intro s hs
    rw [← hagree s hs (hDmaps hs)]
    exact (hτsm s hs (hDmaps hs)).2.submatrix Subtype.val_injective
  · exact _root_.GlobalTheory.PeriodFrame.not_perTau_mulVec_eq_continuous n a g r₀ r K ζ lam M c α φ rk D hK hζ hζK hζ0 (fun s hs => ⟨hlamR s hs, (hlam s hs).2.2⟩)
      (fun s hs i => hc i s hs) hMa hN3 hN4 hD hdet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.BlockLiftFrame

open ReciprocityTheory.Aut GlobalTheory.CenFrame

section Local

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_isCompOf (s : SplitPlace L) {κ : Formalism.AUTREP.GAf L n} (hκ : κ ∈ Umax L n) :
    ∃ y : GL (Fin n) (Os s), IsCompOf s κ y := by
  obtain ⟨y, hy⟩ := GlobalTheory.TSetDoubleCoset.loc_mem_GLint s hκ
  refine ⟨y, fun a c => ?_⟩
  rw [← hy]
  rfl

theorem isCompOf_one_of_not_mem (s : SplitPlace L) {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    (h : s.v ∉ T) {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : IsCompOf s x 1 := by
  have e : s.loc n x = 1 := by
    apply Units.ext
    refine Matrix.ext fun a b => ?_
    have hc : compAt L s.v (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b - (1 : Matrix (Fin n) (Fin n) (AL L)) a b) = 0 := by
      have := congrFun (congrFun (hx s.v h) a) b
      rw [Matrix.map_apply] at this
      rw [map_sub, this, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s _ hc
    rw [map_sub, sub_eq_zero] at h0
    show s.proj (((x : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) a b) =
      (1 : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b
    rw [h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  intro a c
  rw [e]
  by_cases hac : a = c <;> simp [Matrix.one_apply, hac]

theorem isBlockDiagonal_reduction_of_blockLift_splitPlace (s : SplitPlace L) {r p : ℕ} [NeZero p] (γ : GL (Fin r) (ZMod p)) {κ : Formalism.AUTREP.GAf L n}
    {y : GL (Fin n) (Os s)} (hy : IsCompOf s κ y) (hl : GlobalTheory.PendOf.IsLiftAt s r p γ (s.loc n κ)) {k : Type} [CommRing k]
    (φ : Os s →+* k) (hφ : IsResidue s φ) (i : ZMod p →+* k) :
    GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (Formalism.UG.bc i γ) (Matrix.GeneralLinearGroup.map φ y) := by
  intro a b
  have hl' := hl a b
  have hyab := hy a b
  show φ (y.val a b) = _
  by_cases hab : a.val < r ∧ b.val < r
  · rw [dite_eq_left hab] at hl' ⊢
    show φ (y.val a b) = i ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩)
    set m : ℕ := ((γ : Matrix (Fin r) (Fin r) (ZMod p)) ⟨a.val, hab.1⟩ ⟨b.val, hab.2⟩).val with hm
    have h0 : φ (y.val a b - (m : Os s)) = 0 := by
      rw [hφ.ker]
      push_cast
      rw [hyab]
      exact hl'
    rw [map_sub, sub_eq_zero, map_natCast] at h0
    rw [h0, ← map_natCast i m, hm, ZMod.natCast_zmod_val]
  · rw [dite_eq_right hab] at hl' ⊢
    have h1 : ((y.val a b : Os s) : s.v.adicCompletion (maximalRealSubfield L)) = if a = b then 1 else 0 := by
      rw [hyab]; exact hl'
    split_ifs at h1 ⊢ with hab'
    · have h2 : y.val a b = 1 := Subtype.ext (by simpa using h1)
      rw [h2, map_one]
    · have h2 : y.val a b = 0 := Subtype.ext (by simpa using h1)
      rw [h2, map_zero]

end Local

theorem not_mem_gPl_of_twist (D : D7) {Q : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) (s : SplitPlace D.host.E)
    (hs : s.w ∈ Q) : s.v ∉ GlobalTheory.PendOf.gPl D := by
  rintro ⟨kv, hov⟩
  obtain ⟨q, hq, hcard, -, hqg⟩ := (hQ s.w hs).1
  have hg : (D.host.g kv.1 : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    have h0 : (D.host.g kv.1 : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal := D.naut.plGw_over kv.1 kv.2
    have h1 : ((D.host.g kv.1 : ℕ) : 𝓞 (maximalRealSubfield D.host.E)) ∈ s.v.asIdeal := by
      rw [← hov, Ideal.mem_comap, map_natCast]; exact h0
    rw [← s.w_under, Ideal.mem_comap, map_natCast] at h1
    exact h1
  exact GlobalTheory.LevelTypePlace.not_two_primes s.w.asIdeal (D.host.g_prime kv.1) hq (hqg kv.1).symm hg
    (GlobalTheory.LevelTypePlace.natCast_mem_of_card s.w hcard hq.ne_zero)

theorem exists_blockLift (D : D7) {Q Pg : Finset (Pl D.host.E)} (hQ : IsTwistPlaces D.host.g Q) {G : Type} [Group G]
    (eG : G ≃* G0 Pg D.R.r) (cG : G0 Pg D.R.r ≃* G0g D.nd)
    (hgrp : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((eG.trans cG) g kv)) :
    ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV,
      GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧ (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ∧
      ∀ g (s' : SplitPlace D.host.E) (φ : Os s' →+* kP s'.w), IsResidue s' φ →
        (s'.w ∈ Q → ∃ y, IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
        ∀ hP : s'.w ∈ Pg, ∃ y, IsCompOf s' (L g) y ∧
          GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (eG ((eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y) := by
  obtain ⟨plg, iso, hpl, hg⟩ := hgrp
  obtain ⟨L, hL, hU⟩ := GlobalTheory.LiftStandardGroup.main D D.R.nV (by unfold Ranks.nV; omega)
  refine ⟨L, hL, hU, fun g s' φ hφ => ⟨fun hs => ?_, fun hP => ?_⟩⟩
  · exact ⟨1, isCompOf_one_of_not_mem s' (not_mem_gPl_of_twist D hQ s' hs) (hL g).1, map_one _⟩
  · obtain ⟨y, hy⟩ := exists_isCompOf s' (hU g)
    refine ⟨y, hy, ?_⟩
    have hkv : plg (plg.symm ⟨s'.w, hP⟩) = ⟨s'.w, hP⟩ := plg.apply_symm_apply _
    have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : Pg), plg kv = PP →
        ∃ i : ZMod (D.host.g kv.1) →+* kP PP.1, eG ((eG.trans cG).symm g) PP = Formalism.UG.bc i (g kv) := by
      intro kv PP hPP
      subst hPP
      exact ⟨iso kv, by rw [hg, MulEquiv.apply_symm_apply]⟩
    obtain ⟨i, hi⟩ := key _ _ hkv
    rw [hi]
    have hw : s'.w = D.naut.plGw (plg.symm ⟨s'.w, hP⟩).1 (plg.symm ⟨s'.w, hP⟩).2 := by
      rw [← hpl, hkv]
    haveI : NeZero (D.host.g (plg.symm ⟨s'.w, hP⟩).1) := ⟨(D.host.g_prime _).ne_zero⟩
    exact isBlockDiagonal_reduction_of_blockLift_splitPlace s' (g _) hy ((hL g).2 _ s' hw) φ hφ i

end GlobalTheory.BlockLiftFrame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralPointClassEqOne
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

noncomputable section

namespace GlobalTheory.GrassTop

theorem intGr_pointPoly : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    intGr H Dw (pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  unfold intGr
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    exact prod_Ioi_rev v

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold GlobalTheory.GoodMetric.rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  have h : antisymm (chernRoots Dw.mult (pointPoly H Dw) * fibrePoint Dw.mult) =
      chernRoots Dw.mult (pointPoly H Dw) * rootDiscr Dw.mult := by
    rw [antisymm_chernRoots_mul, antisymm_fibrePoint]
  rw [← h, degFl_rho_antisymm, prod_factorial_mult,
    rho_eq_flagMap, ← GlobalTheory.Schubert.schubGam_apply, GlobalTheory.SchubertPoint.schubGam_pointPoly, mul_one]
  have hne : ((Dw.p.factorial * Dw.q.factorial : ℝ) ^ Fintype.card (GlobalTheory.AllWt.Psi H)) ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero _) (by exact_mod_cast Nat.factorial_ne_zero _)
  exact div_self hne

end GlobalTheory.GrassTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernDensityLieGramRelation
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.HodgeRelation

theorem chernTop_lieGram_rel_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk
  obtain ⟨-, hXd⟩ := _root_.GlobalTheory.FlagBaseDim.dims E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have hcard : Fintype.card (Fin X.dim) = Fintype.card (GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) := by
    simp [hXd, Fintype.card_prod]
  let ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q := Fintype.equivOfCardEq hcard
  obtain ⟨φ, g, cc, hcc, hφ, hg, hgu, hdom, hev⟩ :=
    _root_.GlobalTheory.PointChern.lieGram_local_model E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA ix
  set v := c'.e y
  set M : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => modelGram H Dw (coordOf ix u) with hM
  have hsm := _root_.GlobalTheory.PointChern.modelGram_smooth_isUnit E H Dw ix (φ v) hdom
  have hφr : ContDiffAt ℝ 2 φ v := (hφ.contDiffAt (n := 2)).restrict_scalars ℝ
  have hK2 : ∀ τ, MContDiffAt 2 (fun w => M (φ w) τ) v := fun τ a b => ((hsm τ).1 a b).comp v hφr
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.PointChern.chernTop_model_eq_mul E H Dw ix (φ v) hdom
  change chernTop (relPoly τ k' * Q) _ v = 0
  rw [_root_.GlobalTheory.PointChern.chernTop_changeFrame _ _ (fun w => M (φ w)) g cc v hcc hg hgu hK2 (fun τ => (hsm τ).2) hev,
    _root_.GlobalTheory.ChernPull.chernTop_comp _ M φ v hφ (fun τ => (hsm τ).1) (fun τ => (hsm τ).2), hκ, _root_.GlobalTheory.PointChernRel.relation_top_zero E H Dw ix τ k' hk Q,
    mul_zero, mul_zero]

end GlobalTheory.HodgeRelation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PartsPositiveScalarsWithoutCongruenceLengthsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_scalars_without_congruence_lengths : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : GlobalTheory.Mem.R3.Rw.RationalReadingWithoutCongruence R F X0 Y), Pins R F cG → Holds R F → HostHyp D → (Formalism.BasicNotions.Rows.IsotRank D.what₂ → Formalism.MainNotions.SumRepresentations.adm8 D) ∧ GlobalTheory.NRows.LamUsed D := by
  first | exact @GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths | exact GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths | (intros; apply GlobalTheory.NRows.L0.parts_positive_scalars_without_congruence_lengths <;> assumption)
end

