module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0176
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0184

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselCoefficientSmulEquivariant
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.AbsConv

variable {k r : ℕ}

theorem measurable_lmul : Measurable (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1) := by
  apply Continuous.measurable
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem lintegral_lt_top {μG μS ν : Measure (Mt k r)} [SFinite μG] [SFinite μS] [SFinite ν]
    {S : Set (Mat k r)} (hq : IsQuotMeas μG μS ν)
    (hmap : μG = (ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1))
    (hS : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ S)
    (hR : ∀ s ∈ S, μS.map (rmulM s) = μS)
    {φ : Mt k r → ENNReal} (hφ : Measurable φ)
    (hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤)
    {Wn : Mt k r → ENNReal} (hWG : AEMeasurable Wn μG) (hWν : AEMeasurable Wn ν)
    (hinv : ∀ᵐ x ∂ν, ∀ s ∈ S, Wn (lmulM s x) = Wn x)
    (hl2 : ∫⁻ x, Wn x ^ 2 ∂ν < ⊤) :
    ∫⁻ g, φ g * Wn g ∂μG < ⊤ := by
  have hmeas2 : Measurable (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1)) :=
    hφ.comp GlobalTheory.SgInf.AbsConv.measurable_lmul
  have hsec : ∀ x : Mt k r, Measurable (fun t : Mt k r => φ (lmulM (Matrix.of t : Mat k r) x)) :=
    fun x => hmeas2.comp measurable_prodMk_left
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : Mt k r → ENNReal,
      Φ = fun x => ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := ⟨_, rfl⟩
  have hΦx : ∀ x, Φ x = ∫⁻ t, φ (lmulM (Matrix.of t : Mat k r) x) ∂μS := fun x => by rw [hΦdef]
  have hΦm : Measurable Φ := by rw [hΦdef]; exact hmeas2.lintegral_prod_right'

  have hΦinv : ∀ s ∈ S, ∀ x, Φ (lmulM s x) = Φ x := by
    intro s hs x
    have hrm : Measurable (rmulM s : Mt k r → Mt k r) := (continuous_rmulM s).measurable
    rw [hΦx, hΦx]
    conv_rhs => rw [← hR s hs]
    rw [lintegral_map (hsec x) hrm]
    refine lintegral_congr fun t => ?_
    congr 1
    change (Matrix.of t * (s * Matrix.of x) : Mat k r) = Matrix.of t * s * Matrix.of x
    rw [Matrix.mul_assoc]

  have hΦ2 : ∫⁻ x, Φ x * Φ x ∂ν < ⊤ := by
    have hF : Measurable (fun g : Mt k r => φ g * Φ g) := hφ.mul hΦm
    have e1 : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG
        = ∫⁻ g, φ g * Φ g ∂μG := by
      refine lintegral_congr fun g => ?_
      rw [lintegral_const_mul _ (hsec g), hΦx]
    have e2 : ∫⁻ g, φ g * Φ g ∂μG = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) *
        Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν := hq _ hF
    have e3 : ∀ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS
        = Φ x * Φ x := by
      intro x
      rw [lintegral_congr_ae (g := fun s => φ (lmulM (Matrix.of s : Mat k r) x) * Φ x) ?_]
      · rw [lintegral_mul_const _ (hsec x), ← hΦx]
      · filter_upwards [hS] with s hs
        rw [hΦinv _ hs x]
    calc ∫⁻ x, Φ x * Φ x ∂ν
        = ∫⁻ x, ∫⁻ s, φ (lmulM (Matrix.of s : Mat k r) x) * Φ (lmulM (Matrix.of s : Mat k r) x) ∂μS ∂ν :=
          lintegral_congr fun x => (e3 x).symm
      _ = ∫⁻ g, φ g * Φ g ∂μG := e2.symm
      _ = _ := e1.symm
      _ < ⊤ := hfin

  have hWmm : Measurable (hWν.mk Wn) := hWν.measurable_mk
  have h1 : ∀ᵐ x ∂ν, (∀ s ∈ S, Wn (lmulM s x) = Wn x) ∧ Wn x = hWν.mk Wn x :=
    hinv.and hWν.ae_eq_mk
  have h1' : ∀ᵐ p ∂(ν.prod μS), (∀ s ∈ S, Wn (lmulM s p.1) = Wn p.1) ∧ Wn p.1 = hWν.mk Wn p.1 :=
    Measure.quasiMeasurePreserving_fst.ae h1
  have h2 : ∀ᵐ p ∂(ν.prod μS), (Matrix.of p.2 : Mat k r) ∈ S :=
    Measure.quasiMeasurePreserving_snd.ae hS
  have hA : AEMeasurable (fun g => φ g * Wn g)
      ((ν.prod μS).map (fun p : Mt k r × Mt k r => lmulM (Matrix.of p.2 : Mat k r) p.1)) := by
    rw [← hmap]; exact hφ.aemeasurable.mul hWG
  have hmain : ∫⁻ g, φ g * Wn g ∂μG = ∫⁻ x, Φ x * hWν.mk Wn x ∂ν := by
    rw [hmap, lintegral_map' hA GlobalTheory.SgInf.AbsConv.measurable_lmul.aemeasurable]
    rw [lintegral_congr_ae (g := fun p : Mt k r × Mt k r =>
      φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1) ?_]
    · rw [lintegral_prod (fun p : Mt k r × Mt k r => φ (lmulM (Matrix.of p.2 : Mat k r) p.1) * hWν.mk Wn p.1)
        (hmeas2.mul (hWmm.comp measurable_fst)).aemeasurable]
      refine lintegral_congr fun x => ?_
      dsimp only
      rw [lintegral_mul_const _ (hsec x), ← hΦx]
    · filter_upwards [h1', h2] with p hp1 hp2
      simp only [hp1.1 _ hp2, hp1.2]

  have hpt : ∀ x, Φ x * hWν.mk Wn x ≤ hWν.mk Wn x ^ 2 + Φ x * Φ x := by
    intro x
    rcases le_total (Φ x) (hWν.mk Wn x) with h | h
    · calc Φ x * hWν.mk Wn x ≤ hWν.mk Wn x * hWν.mk Wn x := by gcongr
        _ = hWν.mk Wn x ^ 2 := (sq _).symm
        _ ≤ _ := le_self_add
    · calc Φ x * hWν.mk Wn x ≤ Φ x * Φ x := by gcongr
        _ ≤ _ := le_add_self
  have hW2 : ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν = ∫⁻ x, Wn x ^ 2 ∂ν :=
    lintegral_congr_ae (hWν.ae_eq_mk.symm.fun_comp (· ^ 2))
  rw [hmain]
  calc ∫⁻ x, Φ x * hWν.mk Wn x ∂ν ≤ ∫⁻ x, hWν.mk Wn x ^ 2 + Φ x * Φ x ∂ν := lintegral_mono hpt
    _ = ∫⁻ x, hWν.mk Wn x ^ 2 ∂ν + ∫⁻ x, Φ x * Φ x ∂ν := lintegral_add_left (hWmm.pow_const 2) _
    _ < ⊤ := by rw [hW2]; exact ENNReal.add_lt_top.2 ⟨hl2, hΦ2⟩

theorem enorm_star' (a : ℂ) : ‖star a‖ₑ = ‖a‖ₑ := by
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm, nnnorm_star]

theorem coef_inv_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) (w : H) {y g : Mat k r}
    (hy : y ∈ GG k r) (hyi : y⁻¹ ∈ GG k r) (hg : g ∈ GG k r) :
    coef σ w w (y⁻¹ * g) = coef σ w (σ y w) g := by
  obtain ⟨⟨h1, hmul⟩, hiso, -⟩ := hσ
  have hyy : y * y⁻¹ = 1 := Matrix.mul_nonsing_inv y (isUnit_det_of_mem_GG hy)
  have key : ∀ v : H, σ y (σ y⁻¹ v) = v := by
    intro v
    have := congrArg (fun T : H →L[ℂ] H => T v) (hmul y hy y⁻¹ hyi)
    simp only [hyy, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  have hinner : ∀ u v : H, ⟪σ y u, σ y v⟫_ℂ = ⟪u, v⟫_ℂ := by
    intro u v
    let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ y).toLinearMap, norm_map' := hiso y hy }
    exact L.inner_map_map u v
  simp only [coef]
  rw [hmul y⁻¹ hyi g hg, ContinuousLinearMap.comp_apply, ← hinner w (σ y⁻¹ (σ g w)), key]

theorem norm_equiv {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    (hπ : IsURepOn (UWset k r z) π) {W : Mat k r → Wp} (hW : IsSPsiEquiv z (psiGen k r z c) π W)
    {s x : Mat k r} (hs : s ∈ Sset k r z) (hx : x ∈ GG k r) : ‖W (s * x)‖ₑ = ‖W x‖ₑ := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hx' : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := hx
  rw [hW h hh m hm x hx']
  obtain ⟨-, hiso, -⟩ := hπ
  have hψ : ‖psiGen k r z c m‖ = 1 := by simp [psiGen, Complex.norm_exp]
  have hn : ‖psiGen k r z c m • π h (W x)‖ = ‖W x‖ := by rw [norm_smul, hψ, one_mul, hiso h hh]
  simp only [enorm_eq_nnnorm]
  congr 1
  exact NNReal.eq hn

theorem integrable_coef_smul : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, Integrable (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g)) μG := by
  classical
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq W hWG hWν hW hl2 y hy
  have hint := _root_.GlobalTheory.SgInf.fubini_bound k r σ w a μG d z c π μS hStd hSide
  obtain ⟨-, hσ, -, -, hHG, -, -, -, -⟩ := hStd
  obtain ⟨hz, hT, hπ, hHS, -⟩ := hSide
  have hcl := _root_.GlobalTheory.SgInf.closedSub_groups k r z hz hT
  have hUS : IsUnimod (Sset k r z) μS := (_root_.GlobalTheory.SgInf.unimodular_S_N_UW k r z hz hT μS).1 hHS
  obtain ⟨hνσ, hνG, hmap, -, -⟩ := _root_.GlobalTheory.SgInf.weil_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHG hHS hUS hq
  have : SigmaFinite μG := hHG.1
  have : SigmaFinite μS := hHS.1
  have : SigmaFinite ν := hνσ
  have hyi : y⁻¹ ∈ GG k r := hcl.1.2.2.2.2 y hy
  have hone : (1 : Mat k r) ∈ GG k r := hcl.1.2.2.1
  have hwD : w ∈ DD σ w := by
    have := mem_DD σ w hone
    rwa [hσ.1.1, ContinuousLinearMap.one_apply] at this
  have hyD : σ y w ∈ DD σ w := mem_DD σ w hy
  have hint2 := hint w hwD w hwD (σ y w) hyD (σ y w) hyD

  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  set GGset : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∈ GG k r} with hGGdef
  have hGGmeas : MeasurableSet GGset := (hcl.1.2.1.preimage hof).measurableSet
  have hGae : ∀ᵐ x ∂μG, x ∈ GGset := ae_iff.2 hHG.2.2.1
  have hc0 : ContinuousOn (fun g : Mt k r => σ (Matrix.of g) w) GGset :=
    (hσ.2.2 w).comp hof.continuousOn (fun x hx => hx)
  have hcc : ContinuousOn (fun g : Mt k r => coef σ w (σ y w) (Matrix.of g)) GGset := by
    simp only [coef]
    exact continuousOn_const.inner hc0

  obtain ⟨φ, hφdef⟩ : ∃ φ : Mt k r → ENNReal,
      φ = GGset.piecewise (fun g => ‖coef σ w (σ y w) (Matrix.of g)‖ₑ) 0 := ⟨_, rfl⟩
  have hφm : Measurable φ := by
    rw [hφdef]
    exact ContinuousOn.measurable_piecewise (continuous_enorm.comp_continuousOn hcc)
      continuousOn_const hGGmeas
  have hφle : ∀ g, φ g ≤ ‖coef σ w (σ y w) (Matrix.of g)‖ₑ := by
    intro g
    rw [hφdef]
    by_cases hg : g ∈ GGset
    · simp [Set.piecewise, hg]
    · simp [Set.piecewise, hg]
  have hfin : ∫⁻ g, ∫⁻ t, φ g * φ (lmulM (Matrix.of t : Mat k r) g) ∂μS ∂μG < ⊤ := by
    have hfi := hint2.hasFiniteIntegral
    unfold HasFiniteIntegral at hfi
    refine lt_of_le_of_lt ?_ hfi
    refine le_trans (lintegral_mono fun g => lintegral_mono fun t => ?_) (lintegral_prod _ hint2.aestronglyMeasurable.enorm).symm.le
    dsimp only
    rw [enorm_mul, GlobalTheory.SgInf.AbsConv.enorm_star']
    exact mul_le_mul' (hφle g) (hφle _)
  have hinv : ∀ᵐ x ∂ν, ∀ s ∈ Sset k r z,
      ‖W (Matrix.of (lmulM s x))‖ₑ = ‖W (Matrix.of x)‖ₑ := by
    have : ∀ᵐ x ∂ν, x ∈ GGset := ae_iff.2 hνG
    filter_upwards [this] with x hx s hs
    exact GlobalTheory.SgInf.AbsConv.norm_equiv hπ hW hs hx
  have hl2' : ∫⁻ x, ‖W (Matrix.of x)‖ₑ ^ 2 ∂ν < ⊤ := by
    simpa only [l2SG, enorm_eq_nnnorm] using hl2
  have hbound := GlobalTheory.SgInf.AbsConv.lintegral_lt_top (S := Sset k r z) hq hmap (ae_iff.2 hHS.2.2.1)
    hUS.1 hφm hfin hWG.enorm hWν.enorm hinv hl2'

  have hcm : AEStronglyMeasurable (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g))) μG := by
    rw [← Measure.restrict_eq_self_of_ae_mem hGae]
    exact hcc.star.aestronglyMeasurable hGGmeas
  have hsm : AEStronglyMeasurable
      (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) μG := hcm.smul hWG
  have hae : (fun g : Mt k r => star (coef σ w w (y⁻¹ * Matrix.of g)) • W (Matrix.of g))
      =ᵐ[μG] (fun g : Mt k r => star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)) := by
    filter_upwards [hGae] with g hg
    rw [GlobalTheory.SgInf.AbsConv.coef_inv_mul (g := Matrix.of g) hσ w hy hyi hg]
  refine Integrable.congr ⟨hsm, ?_⟩ hae.symm
  show ∫⁻ g, ‖star (coef σ w (σ y w) (Matrix.of g)) • W (Matrix.of g)‖ₑ ∂μG < ⊤
  refine lt_of_eq_of_lt (lintegral_congr_ae ?_) hbound
  filter_upwards [hGae] with g hg
  rw [enorm_smul, GlobalTheory.SgInf.AbsConv.enorm_star', hφdef, Set.piecewise_eq_of_mem _ _ _ hg]

end GlobalTheory.SgInf.AbsConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvLeSizeQAboveOrthogonalSaturated
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

namespace GlobalTheory.Count.PerpSize

open GlobalTheory.Count.PerpStep

theorem inv_le_sizeQ_perp : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (hi : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → ∀ N, perpIn I x R < N → N ≤ lamX I x → hi⁻¹ ≤ sizeQ (bas I) (frm I x) N (perpIn I x R) := by
  intro I x R hi hR hhi hL N hPN hNA
  obtain ⟨-, hA, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨htc, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hm⟩ := GlobalTheory.Count.PerpStep.main I x
  obtain ⟨N', n1, n2, n3, n4⟩ := nd_sat (bas I) (frm I x) hX hA hNA
  obtain ⟨sP, rP, ppR, -, -⟩ := hm R R hR hR le_rfl
  obtain ⟨sS, rS, ppN, -, -⟩ := hm N' N' n2 n2 le_rfl
  have hPN' : perpIn I x R ≤ N' := hPN.le.trans n1
  obtain ⟨-, -, -, hle, hq⟩ := hm _ N' sP n2 hPN'
  rw [ppR] at hle hq
  have hfg : ∀ {M}, M ≤ lamX I x → M.FG := fun h => Submodule.FG.of_le hA h
  have hR0 : R ≠ ⊥ := by
    intro e
    have h1 : perpIn I x N' = R := by
      rw [e] at hle ⊢
      exact le_bot_iff.1 hle
    rw [h1] at ppN
    exact (lt_of_lt_of_le hPN n1).ne ppN
  rw [htQ_eq _ _ hX _ _ (hfg hR.1) (sat_mono _ _ sS hle hR.1),
    htQ_eq _ _ hX _ _ (hfg n2.1) (sat_mono _ _ sP hPN' n2.1), ← Real.exp_neg] at hq
  have hq' := Real.exp_injective hq
  obtain ⟨l0, lb⟩ := largest_bound (bas I) (frm I x) hX (hfg hR.1) hR0 hle
  have hd := rk_lt (bas I) (frm I x) hX hA sP hPN hNA
  have r1 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg hR.1)).2.1
  have r2 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sP.1)).2.1
  have r3 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg sS.1)).2.1
  have r4 := (plLat _ _ _ (bas I) (frm I x) hX _ (hfg n2.1)).2.1
  have hrk : rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R =
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') +
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N := by
    rw [← n3, r1, r2, r3, r4, ← mul_add, ← mul_add, rP, rS]
  have hrk' : (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) R : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x N') =
      (rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) N : ℝ) -
      rk (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hrk
    push_cast at h
    linarith
  rw [hrk'] at lb
  rw [log_sizeQ (bas I) (frm I x) hX hA sP hPN hNA, ← Real.log_le_iff_le_exp (inv_pos.2 hhi),
    le_div_iff₀ (sub_pos.2 hd), Real.log_inv]
  have h4 := Real.log_le_log l0 hL
  have h5 := mul_le_mul_of_nonneg_right h4 (sub_pos.2 hd).le
  linarith

end GlobalTheory.Count.PerpSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeTraceDualAndTraceDualTraceDual
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

noncomputable section

namespace GlobalTheory.MeanDual.Alg

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def halfTraceForm : LinearMap.BilinForm ℚ (Fin j → E) :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (x ⬝ᵥ y) / 2)
    (fun x x' y => by rw [add_dotProduct, map_add (f := _), add_div])
    (fun c x y => by rw [smul_dotProduct, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])
    (fun x y y' => by rw [dotProduct_add, map_add (f := _), add_div])
    (fun c x y => by rw [dotProduct_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_div_assoc])

theorem halfTraceForm_apply (x y : Fin j → E) :
    halfTraceForm E j x y = Algebra.trace ℚ E (x ⬝ᵥ y) / 2 := rfl

theorem halfTraceForm_symm : (halfTraceForm E j).IsSymm := by
  refine ⟨fun x y => ?_⟩
  rw [halfTraceForm_apply, halfTraceForm_apply, dotProduct_comm]

theorem halfTraceForm_left (x : Fin j → E) (h : ∀ y, halfTraceForm E j x y = 0) : x = 0 := by
  ext i
  rw [Pi.zero_apply]
  by_contra hx

  have h1 := h (Pi.single i (x i)⁻¹)
  rw [halfTraceForm_apply, dotProduct_single, mul_inv_cancel₀ hx, ← map_one (algebraMap ℚ E),
    Algebra.trace_algebraMap, nsmul_eq_mul, mul_one] at h1
  have h2 : (0 : ℚ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  linarith

theorem halfTraceForm_nondegenerate : (halfTraceForm E j).Nondegenerate := by
  refine ⟨halfTraceForm_left E j, fun y hy => halfTraceForm_left E j y fun x => ?_⟩
  rw [(halfTraceForm_symm E j).eq]
  exact hy x

theorem restrict_trDual (Λ : Submodule (𝓞 E) (Fin j → E)) :
    (trDual E j Λ).restrictScalars ℤ =
      (halfTraceForm E j).dualSubmodule (Λ.restrictScalars ℤ) := by
  ext y
  simp only [Submodule.restrictScalars_mem, mem_trDual, LinearMap.BilinForm.mem_dualSubmodule,
    Submodule.mem_one, halfTraceForm_apply, eq_intCast]
  constructor
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm, hz]
    ring
  · intro hy x hx
    obtain ⟨z, hz⟩ := hy x hx
    refine ⟨z, ?_⟩
    rw [dotProduct_comm]
    linarith

private theorem smul_mem_span_rat_restrictScalars (Λ : Submodule (𝓞 E) (Fin j → E)) (a : E) {x : Fin j → E}
    (hx : x ∈ Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin j → E)) : Set (Fin j → E))) :
    a • x ∈ Submodule.span ℚ ((Λ.restrictScalars ℤ : Submodule ℤ (Fin j → E)) : Set (Fin j → E)) := by
  obtain ⟨m, s, hm, hms⟩ :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)).exists_nsmul_eq (𝓞 E)
  induction hx using Submodule.span_induction with
  | mem y hy =>
    have hsy : s • y ∈ Λ := Λ.smul_mem s hy
    have key : a • y = (m : ℚ)⁻¹ • (s • y) := by
      rw [← algebraMap_smul E s y, ← hms, smul_assoc, ← Nat.cast_smul_eq_nsmul ℚ,
        inv_smul_smul₀ (by exact_mod_cast hm)]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [smul_add]
    exact add_mem hy hz
  | smul q y _ hy =>
    rw [smul_comm]
    exact Submodule.smul_mem _ _ hy

theorem isLattice_restrict (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsFullLattice E Λ) :
    Submodule.IsFullLattice ℚ (Λ.restrictScalars ℤ) := by
  refine { toIsLattice := Submodule.IsLattice.of_fg ℚ
             (Submodule.FG.restrictScalars (Submodule.IsLattice.fg E Λ)),
           span_eq_top := ?_ }
  refine Submodule.eq_top_iff'.mpr fun v => ?_
  have hv : v ∈ Submodule.span E (Λ : Set (Fin j → E)) := by
    rw [h.span_eq_top]
    trivial
  induction hv using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add y z _ _ hy hz => exact add_mem hy hz
  | smul a y _ hy => exact smul_mem_span_rat_restrictScalars E j Λ a hy

theorem exists_basis (Λ : Submodule (𝓞 E) (Fin j → E)) (h : Submodule.IsFullLattice E Λ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℚ (Fin j → E)),
      Λ.restrictScalars ℤ = Submodule.span ℤ (Set.range b) := by

  have := isLattice_restrict E j Λ h
  have := Submodule.IsLattice.free ℚ (Λ.restrictScalars ℤ)
  have := Submodule.IsLattice.finite ℚ (Λ.restrictScalars ℤ)
  let bF := Module.finBasis ℤ (Λ.restrictScalars ℤ)
  refine ⟨_, bF.extendOfIsFullLattice ℚ, ?_⟩
  have hb : ⇑(bF.extendOfIsFullLattice ℚ) = (Λ.restrictScalars ℤ).subtype ∘ bF :=
    funext fun k => bF.extendOfIsFullLattice_apply ℚ k
  rw [hb, Set.range_comp, ← Submodule.map_span, bF.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem isLattice_trDual_and_trDual_trDual :
    ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)),
      Submodule.IsFullLattice E Λ →
        Submodule.IsFullLattice E (trDual E j Λ) ∧ trDual E j (trDual E j Λ) = Λ := by
  intro E _ _ j Λ h
  obtain ⟨n, b, hb⟩ := exists_basis E j Λ h
  have hB := halfTraceForm_nondegenerate E j
  have hS := halfTraceForm_symm E j

  have hD : (trDual E j Λ).restrictScalars ℤ =
      Submodule.span ℤ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
    rw [restrict_trDual, hb, LinearMap.BilinForm.dualSubmodule_span_of_basis _ hB]
  refine ⟨{ toIsLattice := ?_, span_eq_top := ?_ }, ?_⟩
  · apply Submodule.IsLattice.of_fg E
    apply Submodule.FG.of_restrictScalars ℤ
    rw [hD]
    exact Submodule.fg_span (Set.finite_range _)
  · refine eq_top_iff.mpr fun v _ => ?_
    have hv : v ∈ Submodule.span ℚ (Set.range ((halfTraceForm E j).dualBasis hB b)) := by
      rw [((halfTraceForm E j).dualBasis hB b).span_eq]
      trivial
    have h1 : Set.range ((halfTraceForm E j).dualBasis hB b) ⊆ (trDual E j Λ : Set (Fin j → E)) := by
      rintro _ ⟨k, rfl⟩
      have hk : (halfTraceForm E j).dualBasis hB b k ∈ (trDual E j Λ).restrictScalars ℤ := by
        rw [hD]
        exact Submodule.subset_span ⟨k, rfl⟩
      exact hk
    exact Submodule.span_le_restrictScalars ℚ E _ (Submodule.span_mono h1 hv)
  · apply Submodule.restrictScalars_injective ℤ _ _
    rw [restrict_trDual, restrict_trDual, hb,
      LinearMap.BilinForm.dualSubmodule_dualSubmodule_of_basis _ hB hS]

end GlobalTheory.MeanDual.Alg
end
end

