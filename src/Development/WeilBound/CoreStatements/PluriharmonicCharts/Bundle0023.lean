module

public import Mathlib
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0051
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialBlockDecomposition
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0105
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0121
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0117
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChartImmersion
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.AnalyticAtDetFac
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace PositivityTheory.Xgp.c_unif

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ} {BM : BaseMetric M n}

theorem analyticAt_detFac {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (i : Fin N)
    {H : E → Matrix (Fin N) (Fin N) ℂ} {w : E} (h : ∀ r s, AnalyticAt ℂ (fun u => H u r s) w) :
    AnalyticAt ℂ (fun u => detFac j i (H u)) w := by
  unfold detFac
  refine AnalyticAt.mul ?_ ?_
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const
  · split_ifs
    · exact Fib.analyticAt_minorIJ_of_entries _ w h _ _
    · exact analyticAt_const

theorem holoOn_mul {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {W : Set X}
    {P Q : X → Matrix (Fin N) (Fin N) ℂ} (hP : ∀ a b, A.HoloOn W fun x => P x a b)
    (hQ : ∀ a b, A.HoloOn W fun x => Q x a b) (a b : Fin N) : A.HoloOn W fun x => (P x * Q x) a b := by
  intro k t ht
  show AnalyticAt ℂ (fun w => (P ((A.chart k).symm w) * Q ((A.chart k).symm w)) a b) t
  simp only [Matrix.mul_apply]
  exact Finset.analyticAt_fun_sum _ fun c _ => (hP a c k t ht).mul (hQ c b k t ht)

theorem period_chart (FA : FlagAn BM d) (hsurj : Function.Surjective FA.Re.π) {l : Fin BM.q} {Vb : Set BM.Rb.X}
    {Pi : Ψ → BM.Rb.X → Matrix (Fin N) (Fin N) ℂ} (hPi : IsPeriodOn BM.Rb.A j Vb Pi (BM.G l)) {W : Set FA.S.X}
    (hW : IsOpen W) {x : FA.S.X} (hx : x ∈ W) (hl : ∀ x' ∈ W, FA.pr x' ∈ BM.O l \ bdry BM.s ∧ FA.pr x' ∈ Vb)
    {H : Ψ → FA.S.X → Matrix (Fin N) (Fin N) ℂ} (hH : ∀ τ a b, FA.S.A.HoloOn W fun x' => H τ x' a b)
    (hHb : ∀ τ, ∀ x' ∈ W, IsBlockDiag j (H τ x') ∧ (H τ x').det ≠ 0)
    (ho : ∀ x' ∈ W, ∀ x₀, FA.Re.π x₀ = x' →
      SameOrbit (FA.Re.R.lift x₀ x₀) (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr x')) fun τ => H τ x')) :
    ∃ V, IsPeriodChart (FA.S.comap some).A j (FA.S.comap some).potH x V fun τ x' => Pi τ (FA.pr x') * H τ x' := by
  have hj := M.j_le
  have hg := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l
  have hl1 : ∀ x' ∈ W, FA.pr x' ∈ BM.O l := fun x' h => (hl x' h).1.1
  have hbv := bvec_holo BM FA.pr_holo hW hl1
  have hst := fun (p : Ψ × Fin N) x' (hx' : x' ∈ W) => _root_.GlobalTheory.CompanionTheory.Ar.PB.stepPot_mul_eq_blockPot N j p.2 (Pi p.1 (FA.pr x'))
    (BM.G l p.1 (FA.pr x')) (H p.1 x') hj (hPi.2.2 p.1 _ (hl x' hx').2) (BM.G_pos l p.1 _ (hl x' hx').1).1
    (BM.G_pos l p.1 _ (hl x' hx').1).2 (hHb p.1 x' hx').1 (hHb p.1 x' hx').2
  obtain ⟨k, hk⟩ := FA.S.A.cover x
  set c := FA.S.A.chart k with hc
  have hO : IsOpen (c.target ∩ c.symm ⁻¹' W) := c.isOpen_inter_preimage_symm hW
  have hxO : c x ∈ c.target ∩ c.symm ⁻¹' W := ⟨c.map_source hk, by simpa [c.left_inv hk] using hx⟩
  have hsx : c.symm (c x) = x := c.left_inv hk
  have key : ∀ p : Ψ × Fin N, ∃ V : Set FA.S.X, IsOpen V ∧ x ∈ V ∧ ∃ G : FA.S.X → ℂ, FA.S.A.HoloOn V G ∧
      ∀ x' ∈ V, ((FA.S.comap some).potH p).φ x x' - stepPot N j p.2 (Pi p.1 (FA.pr x') * H p.1 x') = (G x').re := by
    intro p
    obtain ⟨H1, hH1, he1⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.ref_pot_along_exact_family K ι (d + 1) _ FA.S (mCoordIdeal y) FA.Re (some p) (d + 1)
      (c.target ∩ c.symm ⁻¹' W) c.symm
      (fun u => FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (c.symm u))) fun τ => H τ (c.symm u)) (c x)
      FA.J_top FA.deg_one FA.br_empty hO hxO
      (fun q u hu => analyticAt_flagPt (BM.F l) (fun q => hbv.1 q k u hu)
        (fun q I => hbv.2 _ (fun b hb => ((hg b hb).2.1.2.1 q I).1) k u hu) (fun τ r s => hH τ r s k u hu) q)
      (fun u hu => _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.flagPt_mem_mcPts K ι Φ y Ψ N j M n BM l _ (hl1 _ hu.2) _ fun τ => hHb τ _ hu.2)
      (fun u hu x₀ h => ho _ hu.2 x₀ h)
    obtain ⟨H2, hH2, he2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt (d + 1) (fun u => detFac j p.2 (H p.1 (c.symm u))) (c x)
      (analyticAt_detFac p.2 fun r s => hH p.1 r s k _ hxO)
      (CPts.detFac_ne_zero hj p.2 (hHb p.1 _ hxO.2).1 (hHb p.1 _ hxO.2).2)
    obtain ⟨H3, hH3, he3⟩ : ∃ H3 : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ H3 (c x) ∧
        ∀ᶠ u in 𝓝 (c x), Fib.upsLogAt BM l p (FA.pr (c.symm u)) = (H3 u).re := by
      by_cases hp : M.blk p = none
      · simp only [Fib.upsLogAt, if_pos hp]
        refine _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_norm_eventually_eq_re_analyticAt (d + 1) (fun u => Fib.upsVal BM l p (FA.pr (c.symm u))) (c x) ?_
          (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.UpsNe.upsVal_ne_zero K ι Φ y Ψ N j M n d BM l p _ (hl1 _ hxO.2) hp)
        exact _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.analyticAt_valAt_lift_family _ _ M.Ω M.x ((BM.F l).υ p) (d + 1) n BM.Rb (c.target ∩ c.symm ⁻¹' W) (FA.pr ∘ c.symm) (c x)
          hO hxO (FA.pr_holo.1.comp_continuousOn (c.continuousOn_symm.mono Set.inter_subset_left))
          (fun m => (FA.pr_holo.2 k m).mono fun t ht => ⟨ht.1.1, ht.2⟩)
          ((BM.good l _ (hl1 _ hxO.2)).2.2 p hp).2.1
      · exact ⟨fun _ => 0, analyticAt_const, Eventually.of_forall fun u => by simp [Fib.upsLogAt, hp]⟩
    refine exists_holoOn_of_germ FA.S.A hk (H := fun u => H1 u - H2 u - H3 u) ((hH1.sub hH2).sub hH3) ?_
    filter_upwards [he1, he2, he3, hO.mem_nhds hxO] with u h1 h2 h3 hu
    obtain ⟨x₀, hx₀⟩ := hsurj (c.symm u)
    have hline := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.log_fsHerm_add_ph_eq_potAt K ι Φ y Ψ N j M n d BM FA l x₀ _ (FA.pr (c.symm u)) p (H p.1 (c.symm u))
      (hl _ hu.2).1 (ho _ hu.2 x₀ hx₀) (by rw [FC.basePart_flagPt]; exact (hg _ (hl1 _ hu.2)).2.2.2)
      (FC.exactAt_flagPt M (BM.F l) (hg _ (hl1 _ hu.2)).2.2.1 (fun τ => H τ (c.symm u)) p)
      (hHb _ _ hu.2).1 (hHb _ _ hu.2).2
    have hphi : ((FA.S.comap some).potH p).φ x (c.symm u) =
      (FA.S.th (some p)).φ x (c.symm u) + FA.S.ph (some p) (c.symm u) := rfl
    rw [hsx, FA.ref_some] at h1
    rw [hx₀, Fib.potAt] at hline
    rw [hphi, h1, (hst p _ hu.2).2, Complex.sub_re, Complex.sub_re, ← h2, ← h3]
    linarith
  choose V hVo hxV G hG hGe using key
  refine ⟨W ∩ ⋂ p, V p, hW.inter (isOpen_iInter_of_finite hVo), ⟨hx, Set.mem_iInter.2 hxV⟩, fun τ a b => ?_,
    fun τ x' hx' => ?_, fun p => ⟨G p, holoOn_mono (hG p) fun x' hx' => Set.mem_iInter.1 hx'.2 p, fun x' hx' => ?_⟩⟩
  · refine holoOn_mono (holoOn_mul (W := W) (fun a b => ?_) (hH τ) a b) Set.inter_subset_left
    exact holoOn_mono (holoOn_comp FA.pr_holo (hPi.2.1 τ a b)) fun x' hx' => (hl x' hx').2
  · exact StepBlock.inFlagDomain_mul (hPi.2.2 τ _ (hl x' hx'.1).2).1 (hHb τ x' hx'.1).1 (hHb τ x' hx'.1).2
  · have := hGe p x' (Set.mem_iInter.1 hx'.2 p)
    linarith

end PositivityTheory.Xgp.c_unif
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.NotMemTop
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl
open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

noncomputable section

namespace PositivityTheory.Xgp.c_smooth

theorem exists_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsMultiHomogIdeal P) (hnd : ¬ (⊤ : Ideal (MRing ι)) ≤ P)
    (hcov : ∀ z ∈ mcPts P, ∃ C : OrbitChart P e, z ∈ C.O) :
    ∃ R : AnLogRes P ⊤ e, ∀ C : OrbitChart P e, (mcPts P).Nonempty → ∃ ψ : OpenPartialHomeomorph R.X (Fin e → ℂ),
      IsCompatChart R.A ψ ∧ ψ.target = C.D ∧ (∀ x, x ∈ ψ.source ↔ R.lift x x ∈ C.O) ∧
        ∀ x ∈ ψ.source, SameOrbit (C.φ (ψ x)) (R.lift x x) := by
  have h' : ∀ x : PtsOf P, ∃ C : OrbitChart P e, x ∈ srcOf C := fun x => hcov _ (rep_mem_mcPts x)
  choose Cx hCx using h'
  haveI : CompactSpace (PtsOf P) := Top.compactSpace_pts (isMultiHomogIdeal_pC hP)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_nhds_subcover (fun x => srcOf (Cx x))
    (fun x _ => (isOpen_srcOf hP _).mem_nhds (hCx x))
  have hc : ∀ x, ∃ y ∈ t, x ∈ srcOf (Cx y) := fun x => by
    simpa using ht.2 (Set.mem_univ x)
  refine ⟨resOf hP hnd Cx hCx t hc, fun C hne => ?_⟩
  obtain ⟨z, hz⟩ := hne
  have ho : ∀ x : PtsOf P, SameOrbit ((Cx x).φ ((Cx x).ρ (rep x))) (rep x) := fun x => (Cx x).φ_ρ _ (hCx x)
  have hm : ∀ x : PtsOf P, (Cx x).φ ((Cx x).ρ (rep x)) ∈ mcPts P := fun x => (Cx x).mem _ ((Cx x).ρ_mem _ (hCx x))
  refine ⟨orbChart hP C (cls z hz), isCompat_orbChart hP Cx t hc C _, rfl, fun x => ?_, fun x hx => ?_⟩
  · exact ⟨fun h => mem_O_of_orbit C hP h (ho x) (rep_mem_mcPts x),
      fun h => mem_O_of_orbit C hP h (Proj.orbit_symm (ho x)) (hm x)⟩
  · exact Proj.orbit_trans (C.φ_ρ _ hx) (Proj.orbit_symm (ho x))

theorem not_mem_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (z : (Σ k, ι k) → ℂ) :
    z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n), d = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) → ∀ (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∃ (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e), ((∀ p, keep p) → e = d) ∧ ∃ pr : R.X → Rb.X, HoloMap R.A Rb.A pr ∧ (∀ x, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = R.lift x x ∧ SameOrbit (basePart M.blk z) (Rb.lift (pr x) (pr x))) ∧ ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧ ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb hd keep Kk _ ιk _ κ v hb hrng
  obtain ⟨e, he, ⟨ε⟩⟩ : ∃ e, e = n + Nat.card (PIdx j keep) ∧ Nonempty (Fin n ⊕ PIdx j keep ≃ Fin e) :=
    ⟨_, rfl, ⟨(Equiv.sumCongr (Equiv.refl _) (Finite.equivFin _)).trans finSumFinEquiv⟩⟩
  have hP : IsMultiHomogIdeal (mCoordIdeal (y ∘ v)) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
  have hnd : ¬ (⊤ : Ideal (MRing ιk)) ≤ mCoordIdeal (y ∘ v) := fun h =>
    (RingHom.ker_isPrime _ : (mCoordIdeal (y ∘ v)).IsPrime).ne_top (top_le_iff.mp h)
  have hcov := GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover.main K ι Φ y Ψ N j M n Rb keep Kk ιk κ v hb hrng
  have mk : ∀ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h →
      ∃ C : OrbitChart (mCoordIdeal (y ∘ v)) e, C.D = pD ε V ∧ C.φ = pPhi M F keep v bl h ε ∧
        C.O = pO M Rb keep v F kb V r h := by
    intro F kb V bl r h hc
    have hV : IsOpen V := hc.2.2.2.1.1
    have hh := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Holo.pPhi_holo K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hr := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.ChartRead.chart_reads K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ho := GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hO := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.POpn.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hb' := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have ht := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.PCont.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    have hi := GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm.chart_immersion K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
    exact ⟨{ D := pD ε V
             isOpen_D := hV.preimage (continuous_pi fun i => continuous_apply _)
             φ := pPhi M F keep v bl h ε
             holo := hh
             mem := fun w hw => (hr w hw).1.1
             O := pO M Rb keep v F kb V r h
             O_open := hO
             O_orbit := fun z hz z' hz' e => (hb' z hz z' hz' e).1
             ρ := pRho M Rb keep v F kb r h ε
             ρ_cont := ht
             ρ_orbit := fun z hz z' hz' e => (hb' z hz z' hz'.1 e).2
             φ_mem_O := fun w hw => (hr w hw).1
             ρ_φ := fun w hw => (hr w hw).2
             ρ_mem := fun z hz => (ho z hz).1
             φ_ρ := fun z hz => (ho z hz).2
             immersion := hi }, rfl, rfl, rfl⟩
  obtain ⟨R, hR⟩ := exists_res (e := e) hP hnd (fun z hz => by
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov z hz
    obtain ⟨C, -, -, hO⟩ := mk F kb V bl r h hc
    exact ⟨C, hO ▸ hzO⟩)

  have key : ∀ x : R.X, ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h ∧ IsCompatChart R.A ψ ∧ ψ.target = pD ε V ∧ x ∈ ψ.source ∧
        ∀ x' ∈ ψ.source, SameOrbit (pPhi M F keep v bl h ε (ψ x')) (R.lift x' x') := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, hc, hzO⟩ := hcov _ (R.mem x x (R.mem_U x))
    obtain ⟨C, hD, hφ, hO⟩ := mk F kb V bl r h hc
    obtain ⟨ψ, h1, h2, h3, h4⟩ := hR C ⟨_, R.mem x x (R.mem_U x)⟩
    exact ⟨F, kb, V, bl, r, h, ψ, hc, h1, h2.trans hD, (h3 x).2 (hO ▸ hzO), fun x' hx' => hφ ▸ h4 x' hx'⟩
  have hob := (_root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hb hrng).2

  have hbase : ∀ x : R.X, ∃ x' : Rb.X, SameOrbit (Rb.lift x' x') (pBase M v (R.lift x x)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    refine ⟨(Rb.A.chart kb).symm (pB ε (ψ x)), orbit_trans (hB.2.2.2.2 _ hw).2.2.2 ?_⟩
    have := hob _ _ (hs x hx)
    rwa [hE.2.1] at this
  choose pr hpr using hbase
  have hcoord : ∀ (x : R.X) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
      (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
      (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)),
      IsPCtx M Rb keep κ v F kb V bl r h → ψ.target = pD ε V → x ∈ ψ.source →
      SameOrbit (pPhi M F keep v bl h ε (ψ x)) (R.lift x x) →
      pr x = (Rb.A.chart kb).symm (pB ε (ψ x)) ∧ pr x ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x) i = ψ x (ε (Sum.inl i)) := by
    intro x F kb V bl r h ψ hc hT hx hs
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    have hE := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    have h1 : SameOrbit (bl (pB ε (ψ x))) (pBase M v (R.lift x x)) := by
      have := hob _ _ hs
      rwa [hE.2.1] at this
    have h2 := orbit_trans (hB.2.2.2.2 _ hw).2.2.2 (orbit_trans h1 (orbit_symm (hpr x)))
    have h3 : (Rb.A.chart kb).symm (pB ε (ψ x)) = pr x := Rb.inj _ _ (not_mem_top _) h2
    have hwt : pB ε (ψ x) ∈ (Rb.A.chart kb).target := hB.2.1 hw
    rw [← h3]
    exact ⟨rfl, (Rb.A.chart kb).map_target hwt, fun i => by
      rw [(Rb.A.chart kb).right_inv hwt]
      rfl⟩
  have hlast : ∀ x, ∃ (ψ : OpenPartialHomeomorph R.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e),
      IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ (∀ x' ∈ ψ.source, pr x' ∈ (Rb.A.chart kb).source ∧
        ∀ i, Rb.A.chart kb (pr x') i = ψ x' (σ i)) := by
    intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, hψ, hT, hx, hs⟩ := key x
    refine ⟨ψ, kb, ⟨fun i => ε (Sum.inl i), fun a b e' => Sum.inl_injective (ε.injective e')⟩, hψ, hx, fun x' hx' => ?_⟩
    obtain ⟨-, h1, h2⟩ := hcoord x' F kb V bl r h ψ hc hT hx' (hs x' hx')
    exact ⟨h1, h2⟩
  refine ⟨e, R, ?_, pr, ?_, ?_, hlast⟩
  · intro hall
    rw [he, _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.AllKept.card_pIdx_of_all Ψ N j keep M.j_le hall, hd]
  · refine GlobalTheory.CompanionTheory.Ar.PB.WMan.Coord.holoMap_of_coord e n R.X Rb.X R.A Rb.A pr fun x => ?_
    obtain ⟨ψ, kb, σ, h1, h2, h3⟩ := hlast x
    exact ⟨ψ, kb, σ, h1, h2, h3⟩
  · intro x
    obtain ⟨F, kb, V, bl, r, h, ψ, hc, -, hT, hx, hs⟩ := key x
    have hB : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
    have hw : ψ x ∈ pD ε V := hT ▸ ψ.map_source hx
    obtain ⟨z₀, hz₀, hzv, hzb⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext.main K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc _ hw
    obtain ⟨hpe, -, -⟩ := hcoord x F kb V bl r h ψ hc hT hx (hs x hx)
    obtain ⟨c, hc0, hce⟩ := orbit_symm (hs x hx)
    let c' : K → ℂ := fun k => if hk : ∃ k', κ k' = k then c hk.choose else 1
    have hc'0 : ∀ k, c' k ≠ 0 := fun k => by
      simp only [c']
      split_ifs
      · exact hc0 _
      · exact one_ne_zero
    have hc'κ : ∀ k', c' (κ k') = c k' := fun k' => by
      have hk : ∃ k'', κ k'' = κ k' := ⟨k', rfl⟩
      simp only [c']
      rw [dite_eq_left hk, hb.1 hk.choose_spec]
    have hyP : IsMultiHomogIdeal (mCoordIdeal y) := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _
    refine ⟨fun p => c' p.1 * z₀ p, mcPts_smul hyP c' hc'0 hz₀, ?_, ?_⟩
    · funext q
      have e1 : z₀ (v q) = pPhi M F keep v bl h ε (ψ x) q := congrFun hzv q
      have e2 := congrFun hce q
      show c' (v q).1 * z₀ (v q) = _
      rw [e2, e1, hb.2.2.1 q, hc'κ]
    · have h1 : SameOrbit (fun q => c' q.1.1 * basePart M.blk z₀ q) (bl (pB ε (ψ x))) := by
        rw [hzb]
        exact ⟨fun k => c' k.1, fun k => hc'0 _, rfl⟩
      have h2 : (basePart M.blk fun p => c' p.1 * z₀ p) = fun q => c' q.1.1 * basePart M.blk z₀ q := rfl
      rw [h2, hpe]
      exact orbit_trans h1 (orbit_symm (hB.2.2.2.2 _ hw).2.2.2)

end PositivityTheory.Xgp.c_smooth
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XReBridge
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_bridge

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem isNull_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {N N' : Set X}
    (h : IsNull A N) (h' : IsNull A N') : IsNull A (N ∪ N') := by
  intro j
  rw [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (h j) (h' j)

theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

end PositivityTheory.Xgp.re_bridge

theorem PositivityTheory.Xgp.t_re_bridge : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u := by
  intro hE K _ ι _ P J D R X _ _ _ A π hπ dg br hP hdeg L Φ hL hΦ hS Am f g u N hAm hfg hN hu hI
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hAm hB
  have hsf : IsSectionOn P (Am.tensor (HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show Am.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hsg : IsSectionOn P (HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hQ : ∀ j, IsPotential R.A (potOf R (L j)) := fun j => isPotential_potOf R (hL j)
  rw [GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.ptsIntegral_logNormRat
      (GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hE) hP hL hAm hB hsf hsg,
    ptsIntegral_eq_mInt' hE resBridge R hP hL hAB hsf, ptsIntegral_eq_mInt' hE resBridge R hP hL hB hsg,
    ← (degreeFormulaInt A R.A π hπ dg br hdeg Φ hΦ u hI).2]
  have hlin := mIntLinear R.A _ hQ (-1) _ _ (brIntegrable R L _ g hP hL hB hsg)
    (brIntegrable R L _ f hP hL hAB hsf)
  have hnull := PositivityTheory.Xgp.re_bridge.isNull_union hN (PositivityTheory.Xgp.re_bridge.isNull_union
    (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hf hfP) (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hg hgP))
  have key := (mInt_congr_samePot D R.X R.A
    (N ∪ ({x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}))ᶜ
    (fun j => potOf R (L j)) (fun j => (Φ j).pullback π hπ.1)
    (fun x => -1 * logNorm (HermLine.sqMetric β) g (R.lift x x) +
      logNorm (Am.tensor (HermLine.sqMetric β)) f (R.lift x x)) (u ∘ π)
    (by rwa [compl_compl]) (fun j x _ => hS j x (Set.mem_univ x))
    (fun j x _ => PositivityTheory.Xgp.re_bridge.isC2At_of_isPotential R.A
      (isPotentialPullback A R.A π hπ _ (hΦ j)) x) ?_).1
  · rw [← key, hlin]
    ring
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
    obtain ⟨hxN, hxf, hxg⟩ := hx
    have hz := (R.mem x x (R.mem_U x)).1
    have hf0 := norm_pos_iff.mpr hxf
    have hg0 := norm_pos_iff.mpr hxg
    have hA0 := Am.pos _ hz
    have hB0 := (HermLine.sqMetric (ι := ι) β).pos _ hz
    show _ = u (π x)
    rw [← hu x hxN]
    show -1 * Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h (R.lift x x)) +
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        (Am.h (R.lift x x) * (HermLine.sqMetric β).h (R.lift x x))) =
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / Am.h (R.lift x x))
    rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
      Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
      Real.log_div hf0.ne' hg0.ne']
    ring
end

