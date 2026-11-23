module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0050
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenNearCover
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0053

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticOrbitOffBoundary
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem log_h_sub_eq_of_sameOrbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (ho : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hP : (∏ k, ‖c k‖ ^ A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc k))
  rw [A.smul c z' hc, B.smul c z' hc, ← hab, Real.log_mul hP (A.pos z' hz').ne',
    Real.log_mul hP (B.pos z' hz').ne']
  ring

theorem exactLine_not_mem_mcPts_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  simp only [mcPts, Set.mem_ofPred_eq] at hz
  have h1 := hz.2 1 Submodule.mem_top
  simp at h1

theorem exactLine_basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (ho : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := ho
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

end SlopeTestRemainingChoices

theorem log_fsHerm_add_ph_eq_potAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (l : Fin BM.q) (x₀ : FA.Re.R.X) (z₀ : (Σ k, ι k) → ℂ) (b : BM.Rb.X) (p : Ψ × Fin N) (hm : Matrix (Fin N) (Fin N) ℂ), b ∈ BM.O l \ bdry BM.s → SameOrbit (FA.Re.R.lift x₀ x₀) z₀ → SameOrbit (basePart M.blk z₀) (BM.Rb.lift b b) → ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) (BM.F l) p z₀ hm → IsBlockDiag j hm → hm.det ≠ 0 → Real.log ((fsHerm ι (M.dy p)).h z₀) + FA.S.ph (some p) (FA.Re.π x₀) = potAt BM l p b hm := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA l x₀ z₀ b p hm hb hx hbase hex hbd hdet
  have hsymm : ∀ {K' : Type} {ι' : K' → Type} {u v : (Σ k, ι' k) → ℂ}, SameOrbit u v → SameOrbit v u := by
    intro K' ι' u v h
    obtain ⟨c, hc, rfl⟩ := h
    exact ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k),
      funext fun q => (inv_mul_cancel_left₀ (hc q.1) (v q)).symm⟩
  have htrans : ∀ {K' : Type} {ι' : K' → Type} {u v w : (Σ k, ι' k) → ℂ},
      SameOrbit u v → SameOrbit v w → SameOrbit u w := by
    intro K' ι' u v w h h'
    obtain ⟨c, hc, rfl⟩ := h
    obtain ⟨e, he, rfl⟩ := h'
    exact ⟨fun k => c k * e k, fun k => mul_ne_zero (hc k) (he k),
      funext fun q => (mul_assoc _ _ _).symm⟩
  have hmemx : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  have hmem : z₀ ∈ mcPts (mCoordIdeal y) :=
    ReciprocityTheory.ChartRestriction.G.Geo.mem_mcPts_of_sameOrbit
      (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal y) (hsymm hx) hmemx
  have hpr : FA.pr (FA.Re.π x₀) = b := by
    apply BM.Rb.inj
    · exact exactLine_not_mem_mcPts_top _
    · exact htrans (hsymm (FA.pr_eq x₀)) (htrans (exactLine_basePart_orbit M.blk hx) hbase)
  have hopen : FA.Re.π x₀ ∈ FA.S.open' := by
    show FA.Re.π x₀ ∈ (bdry FA.S.s)ᶜ
    rw [Set.mem_compl_iff]
    intro h
    apply hb.2
    have h' : FA.S.s (FA.Re.π x₀) (FA.Re.π x₀) = 0 := h
    simp only [FA.s_eq, hpr] at h'
    show BM.s b b = 0
    exact h'
  have hhom := FA.hom_eq p x₀ hopen
  rw [FA.ref_some p] at hhom
  have hz0 : ∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0 := hmem.1
  have hsub := log_h_sub_eq_of_sameOrbit (BM.hom p) (fsHerm ι (M.dy p)) (BM.hom_deg p) hz0 hx
  have hind := BM.induced l b hb p z₀ hmem hbase hex.1 hm hbd hdet
  have hval : valAt M.x ((BM.F l).υ p) (BM.Rb.lift b b) = valAt M.x ((BM.F l).υ p) (basePart M.blk z₀) :=
    valAt_eq_of_sameOrbit _ _ _ M.x _ _ _ (BM.Rb.mem b b (BM.Rb.mem_U b)) (hsymm hbase)
  unfold potAt upsLogAt upsVal
  by_cases hblk : M.blk p = none
  · have h1 := hind.2 hblk
    rw [if_pos hblk, hval]
    linarith
  · obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp hblk
    have h1 := hind.1 k hk (hex.2 k hk)
    rw [if_neg hblk, sub_zero]
    linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalDegreeEstimate
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∃ z ∈ mcPts (mCoordIdeal y), z ∘ v = pPhi M F keep v bl h ε w ∧ basePart M.blk z = bl (pB ε w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hctx w hw
  have hT := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hctx w hw
  have hc2 := hctx
  unfold GlobalTheory.CompanionTheory.Ar.PB.PFl.IsPCtx at hc2
  obtain ⟨-, -, hframe, hchart, -⟩ := hc2
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.IsBaseChart at hchart
  have hwV : pB ε w ∈ V := hw
  obtain ⟨hmem, hnorm, hgood, -⟩ := hchart.2.2.2.2 (pB ε w) hwV
  have hbase : basePart M.blk (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w)) =
      bl (pB ε w) := by
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    unfold GlobalTheory.CompanionTheory.Ar.PB.basePart GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
    split
    next hex => exact absurd hex (fun ⟨p, hp⟩ => hk p hp)
    next hex => rfl
  refine ⟨GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w), ?_, rfl, hbase⟩
  have hmain := (GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.2 F hframe
    (GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w))
    (by rw [hbase]; exact hmem) (by rw [hbase]; exact hgood) (by rw [hbase]; exact hnorm)
  refine hmain.2 ⟨fun τ => pH keep h ε τ w, ?_⟩
  refine ⟨fun k => by rw [hbase]; exact hnorm k, fun τ => hT.1 τ, ?_⟩
  intro p k hp
  refine ⟨1, one_ne_zero, fun m => ?_⟩
  rw [one_mul, hbase]
  unfold GlobalTheory.CompanionTheory.Ar.PB.WMan.flagZ
  split
  next hex =>
    have hc : hex.choose = p := M.blk_inj _ _ k hex.choose_spec hp
    rw [hc]
  next hex => exact absurd ⟨p, hp⟩ hex

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Ext
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalNormComparison
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_scale {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (z : (Σ k, ιk k) → ℂ) (c : Kk → ℂ)
    (k₀ : Kk) (m : ι (κ k₀)) :
    upV v (fun p => c p.1 * z p) ⟨κ k₀, m⟩ = c k₀ * upV v z ⟨κ k₀, m⟩ := by
  obtain ⟨q, hq⟩ := hb.2.2.2 ⟨κ k₀, m⟩ ⟨k₀, rfl⟩
  have hk : q.1 = k₀ := hb.1 (by rw [← hb.2.2.1 q, hq])
  rw [← hq, upV_apply hb.2.1, upV_apply hb.2.1, hk]

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem pRead_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ} (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {u u' : (Σ k, ι k) → ℂ} (τ : Ψ) (a b : Fin N)
    (hu : ∀ k, M.blk (τ, pStep j keep τ b) = some k → ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) :
    pRead M F keep zb' h u' τ a b = pRead M F keep zb h u τ a b := by
  unfold pRead
  obtain hk | ⟨k, hk⟩ : M.blk (τ, pStep j keep τ b) = none ∨ ∃ k, M.blk (τ, pStep j keep τ b) = some k := by
    cases M.blk (τ, pStep j keep τ b) <;> simp
  · simp only [hk, Option.elim_none]
  · obtain ⟨t, ht, hu⟩ := hu k hk
    simp only [hk, Option.elim_some]
    rw [WMan.Orb.twMinor_scale M F hv _ k _ hu, WMan.Orb.twMinor_scale M F hv _ k _ hu,
      mul_left_comm (pSgn _ _ _) t, mul_div_mul_left _ _ ht]

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, ∀ z' ∈ mcPts (mCoordIdeal (y ∘ v)), SameOrbit z' z → z' ∈ pO M Rb keep v F kb V r h ∧ pRho M Rb keep v F kb r h ε z' = pRho M Rb keep v F kb r h ε z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε ctx z hz z' hz' ho
  obtain ⟨hbm, hrange, -, -, hr, -, -⟩ := ctx
  obtain ⟨hzP, hs, hV, hm⟩ := hz
  have hI := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  have hb := hI.1 z hzP
  have hb' := hI.1 z' hz'
  have hob : SameOrbit (pBase M v z') (pBase M v z) := hI.2 z' z ho
  have hnot : ∀ x : Rb.X, Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun x hx => by
    have := hx.2 1 Submodule.mem_top
    simp at this
  have hrr : r (pBase M v z') = r (pBase M v z) :=
    Rb.inj _ _ (hnot _) (orbit_trans (hr _ hb') (orbit_trans hob (orbit_symm (hr _ hb))))
  have hv : ∀ s, valAt M.x s (pBase M v z') = valAt M.x s (pBase M v z) := fun s => by
    obtain ⟨t, ht, et⟩ := hob
    have := StepW.TorusAct.valAt_torus (x := M.x) t ht hb (et ▸ hb') s
    rw [et]
    exact this
  obtain ⟨c, hc, rfl⟩ := ho

  have hkept : ∀ {p : Ψ × Fin N} {k : K}, keep p → M.blk p = some k →
      ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ι k, upV v (fun p => c p.1 * z p) ⟨k, m⟩ = t * upV v z ⟨k, m⟩ := by
    intro p k hp hk
    obtain ⟨k₀, rfl⟩ := (hrange k).2 (Or.inr ⟨p, hp, hk⟩)
    exact ⟨c k₀, hc k₀, upV_scale hbm z c k₀⟩
  refine ⟨⟨hz', ?_, ?_, fun p k hp hk => ?_⟩, ?_⟩
  · rw [hrr]; exact hs
  · rw [hrr]; exact hV
  · obtain ⟨t, ht, hu⟩ := hkept hp hk
    rw [WMan.Orb.twMinor_scale M F hv _ k _ hu]
    exact mul_ne_zero ht (hm p k hp hk)
  · funext i
    unfold pRho
    rcases ε.symm i with l | q
    · show Rb.A.chart kb (r (pBase M v _)) l = Rb.A.chart kb (r (pBase M v z)) l
      rw [hrr]
    · exact pRead_scale M F keep hv h _ _ _ fun k hk =>
        hkept (SmallStep.pStep_reads Ψ N j keep q M.j_le).1 hk

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Orb
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionLocConstTrivial
section
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem intersection_locConst_trivial : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (B : HermLine ι) (Λ : (F →+* ℂ) → ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → B.a = 0 → IsSmoothHerm B → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) → II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) = ∑ sg : F →+* ℂ, Real.log (Λ sg) * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hInt K _ ι _ Ω _ F _ _ _ y D L B Λ II hII hP hL hB0 hB hex hloc
  classical
  let S : (F →+* ℂ) → Set ((Σ k, ι k) → ℂ) := fun sg => {z | LiesOver y sg z}
  have hSc : ∀ sg, IsClosed (S sg) := fun sg =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.isClosed_liesOver y sg
  have hSs : ∀ sg (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S sg →
      (fun p => t p.1 * z p) ∈ S sg :=
    fun _ t _ _ hz => GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.liesOver_smul hz t
  have hex' : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg, z ∈ S sg := hex
  have hR := (hII K ι).2.2 (mCoordIdeal y) D L B 1 0 hP hL hB (fun k => by simp [hB0])
    tele_one_homog (fun h1 => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1))
  have hnum : II K ι (mCoordIdeal y) (D + 1) (Fin.snoc L B) =
      ptsIntegral (mCoordIdeal y) (pot L) fun z => Real.log (B.h z) := by
    rw [hR]
    unfold recR
    rw [tele_divSupp_one, finsum_mem_empty, zero_sub]
    unfold arInt
    have hl : logNorm B 1 = fun z => - Real.log (B.h z) := by
      funext z
      simp [logNorm, Real.log_inv]
    rw [hl, tele_ptsIntegral_neg, neg_neg]
    rfl
  have hw : ptsIntegral (mCoordIdeal y) (pot L) (fun z => Real.log (B.h z)) =
      ptsIntegral (mCoordIdeal y) (pot L)
        (fun z => ∑ s, Real.log (Λ s) * (S s).indicator (fun _ => (1 : ℝ)) z) := by
    refine GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) ?_
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = Λ sg := (hloc z hz sg hsg).self_of_nhds
    rw [Finset.sum_eq_single sg]
    · rw [Set.indicator_of_mem (show z ∈ S sg from hsg), mul_one, hval]
    · intro s _ hs
      have hns : z ∉ S s := fun h => hs ((hex z hz).unique h hsg)
      rw [Set.indicator_of_notMem hns, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ sg) h
  rw [hnum, hw]
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.PiecesAdditive.proof hInt K ι _ D L (F →+* ℂ) S
    (fun s => Real.log (Λ s)) hP hL hSc hSs hex'

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsCxVarOfMemMinimalPrimesCxIdeal
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxComp

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Pub.CxInt Filter Topology
open ReciprocityTheory.AnForm.R (conePts)

theorem isCxVar_of_mem_minimalPrimes_cxIdeal :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P (d + 1) →
    ∀ Q ∈ (cxIdeal P).minimalPrimes, IsCxVar Q d ∧
      Q.comap (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P := by
  classical
  intro K _ ι _ P d hP Q hQ
  obtain ⟨hK, ⟨hPp, hPm, hPr⟩, hPh, hdim⟩ := hP
  have hc : Q.comap (MvPolynomial.map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι) = P :=
    GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.comap_of_minimal P hPh Q hQ
  have hCm : IsMultiHomogIdeal (cxIdeal P) := by
    obtain ⟨T, hT, hPT⟩ := hPm
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [cxIdeal, hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun m hm k => ha m (support_map_subset _ _ hm) k⟩
  have hQm : IsMultiHomogIdeal Q :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.GenNearCover.isMultiHomogIdeal_of_mem_minimalPrimes hCm hQ
  have hQr : IsRelevant Q := fun k => by
    obtain ⟨i, hi⟩ := hPr k
    refine ⟨i, fun hX => hi ?_⟩
    rw [← hc, Ideal.mem_comap, MvPolynomial.map_X]
    exact hX
  have hP' : ∀ m : ℤ, (C m : MRing ι) ∈ P → m = 0 := fun m hm => by
    have : m ∈ P.comap (C : ℤ →+* MRing ι) := hm
    rw [hPh] at this
    exact this
  obtain ⟨hQp, -, hQdim⟩ := ReciprocityTheory.AnForm.R.extQ_spec P hP'
  have hmapP : cxIdeal P =
      (ReciprocityTheory.AnForm.R.extQ P).map (MvPolynomial.map (algebraMap ℚ ℂ)) := by
    rw [cxIdeal, GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.map_int_complex_eq, ← Ideal.map_map]
    rfl
  have hQ' := hQ
  rw [hmapP] at hQ'
  refine ⟨⟨hK, ⟨hQ.1.1, hQm, hQr⟩, ?_⟩, hc⟩
  rw [ReciprocityTheory.AnForm.R.BaseChangeC.ringKrullDim_of_mem_minimalPrimes_map _ Q hQ']
  rw [hdim, show d + 1 + Fintype.card K = (d + Fintype.card K) + 1 by omega] at hQdim
  exact GroundTheory.Heights₂.Heights.Targets.ConeComplexBaseChange.dim_cancel_one hQdim

end GlobalTheory.CompanionTheory.Ar.Pub.CxComp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mixedDisc_eq_zero_of_eq_zero {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (j : Fin D)
    (hA : A j = 0) : mixedDisc A = 0 := by
  classical
  have pair : ∀ T : Finset (Fin D), j ∉ T →
      (-1 : ℂ) ^ (D - T.card) * (∑ k ∈ T, A k).det +
        (-1 : ℂ) ^ (D - (insert j T).card) * (∑ k ∈ insert j T, A k).det = 0 := by
    intro T hj
    rw [Finset.sum_insert hj, hA, zero_add, Finset.card_insert_of_notMem hj]
    have hlt : T.card < D := by simpa using Finset.card_lt_univ_of_notMem hj
    obtain ⟨m, hm⟩ : ∃ m, D - T.card = m + 1 := ⟨D - T.card - 1, by omega⟩
    have hm' : D - (T.card + 1) = m := by omega
    rw [hm, hm', pow_succ]
    ring
  unfold mixedDisc
  rw [Finset.sum_involution (fun S _ => if j ∈ S then S.erase j else insert j S), mul_zero]
  · intro S _
    split_ifs with h
    · have := pair (S.erase j) (Finset.notMem_erase j S)
      rw [Finset.insert_erase h] at this
      rw [add_comm]
      exact this
    · exact pair S h
  · intro S _ _
    split_ifs with h
    · intro e
      have hmem : j ∈ S.erase j := by
        rw [e]
        exact h
      exact Finset.notMem_erase j S hmem
    · exact fun e => h (e ▸ Finset.mem_insert_self j S)
  · intro S _
    exact Finset.mem_univ _
  · intro S _
    by_cases h : j ∈ S
    · simp [h, Finset.insert_erase]
    · simp [h, Finset.erase_insert]

theorem cxHessian_zero {D : ℕ} (z : Fin D → ℂ) : cxHessian (fun _ => (0 : ℝ)) z = 0 := by
  have h : fderiv ℝ (fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ))) z = 0 := by
    have h1 : fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) = fun _ => 0 := by
      funext x
      exact fderiv_const_apply 0
    rw [h1]
    exact fderiv_const_apply 0
  ext a b
  simp [cxHessian, h]

theorem sheetDensity_update_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ (Function.update φ j 0) g y w = 0 := by
  unfold sheetDensity
  split_ifs with hγ
  · have hm : mixedDisc (fun k => cxHessian
        (fun y' => Function.update φ j 0 k (hγ.choose y')) y) = 0 := by
      refine mixedDisc_eq_zero_of_eq_zero _ j ?_
      simpa using cxHessian_zero y
    simp [maDensity, hm]
  · rfl

theorem ptsIntegral_eq_zero_of_locConst :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
      (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e),
      (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  intro K _ ι _ P e φ g j hj
  have hshift : ∀ i, ∀ z ∈ mcPts P, ∃ c : ℝ,
      ∀ᶠ u in 𝓝 z, φ i u = Function.update φ j 0 i u + c := by
    intro i z hz
    by_cases hi : i = j
    · subst hi
      obtain ⟨c, hc⟩ := hj z hz
      refine ⟨c, hc.mono fun u hu => ?_⟩
      simpa using hu
    · exact ⟨0, Eventually.of_forall fun u => by simp [Function.update_of_ne hi]⟩
  rw [GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersection.ptsIntegral_add_locConst P hshift g]
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity_update_zero]
  · rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

