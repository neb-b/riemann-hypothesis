module

public import Mathlib
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.Bundle0001
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.SheetDensityEqSetSheetDensity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDim
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0113
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0055
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SetSegreConeSmul
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Pub.CxChart

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver segre scaleBlock)
open ReciprocityTheory.AnForm.R (conePts)

open GoodChartDim SegreChartDim

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem segChart_dim {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) (hPCh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    {e : ℕ} (hdim : ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) {m : ℕ}
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) {J : Ideal (MvPolynomial (Fin m) ℂ)}
    (hJ : J ∈ (setSegChartIdeal (conePts Q) σ i).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  classical
  have hdim' : ∀ Q' ∈ Q.minimalPrimes,
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ Q') = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    intro Q' hQ'
    rw [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff] at hQ'
    rw [hQ']
    exact hdim

  set T : Set ((Σ k, ι k) → ℂ) := MvPolynomial.zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal Q i) with hT
  set S := setSegChartSet (conePts Q) σ i with hS
  have hTmem : ∀ y, y ∈ T ↔ ∀ h ∈ ReciprocityTheory.AnForm.R.chartIdeal Q i, eval y h = 0 := fun y => by
    simp [hT, MvPolynomial.mem_zeroLocus_iff]
  have hsegT : ∀ y ∈ T, (fun a => segre y (σ a)) ∈ S := by
    intro y hy
    obtain ⟨hc, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    exact ⟨y, hc, by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1], rfl⟩
  have hlift_apply : ∀ z : (Σ k, ι k) → ℂ, segre z i = 1 →
      chartLift σ i (fun a => segre z (σ a)) = ReciprocityTheory.AnForm.R.affCoord i z := by
    intro z hz
    funext q
    rw [chartLift_segre_apply σ i z hz q.1 q.2]
    simp [ReciprocityTheory.AnForm.R.affCoord, div_eq_mul_inv]
  have hliftS : ∀ x ∈ S, chartLift σ i x ∈ T := by
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := fun k h0 => by
      have : segre z i = 0 := Finset.prod_eq_zero (Finset.mem_univ k) h0
      rw [hzi] at this
      exact one_ne_zero this
    rw [hTmem, hlift_apply z hzi]
    exact (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hPCh i z hne).1 hz
  have hsegLift : ∀ x ∈ S, (fun a => segre (chartLift σ i x) (σ a)) = x := by
    rintro _ ⟨z, -, hzi, rfl⟩
    rw [segre_chartLift σ i z hzi]
  have hliftSeg : ∀ y ∈ T, chartLift σ i (fun a => segre y (σ a)) = y := by
    intro y hy
    obtain ⟨-, h1, -⟩ := ReciprocityTheory.AnForm.R.conePts_of_chartIdeal hPCh i y ((hTmem y).1 hy)
    have hyi : segre y i = 1 := by simp [ReciprocityTheory.ChartRestriction.G.Geo.segre, h1]
    funext q
    rw [chartLift_segre_apply σ i y hyi q.1 q.2, h1, inv_one, mul_one]

  let α : MvPolynomial (Fin m) ℂ →ₐ[ℂ] MvPolynomial (Σ k, ι k) ℂ :=
    aeval fun a => ∏ k, X ⟨k, σ a k⟩
  let β : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] MvPolynomial (Fin m) ℂ :=
    aeval fun q => X (σ.symm (Function.update i q.1 q.2))
  have hα : ∀ (y : (Σ k, ι k) → ℂ) f, eval y (α f) = eval (fun a => segre y (σ a)) f := by
    intro y f
    induction f using MvPolynomial.induction_on with
    | C c => simp [α]
    | add f g hf hg => simp [hf, hg]
    | mul_X f a hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [α, ReciprocityTheory.ChartRestriction.G.Geo.segre, map_prod]
  have hβ : ∀ (x : Fin m → ℂ) g, eval x (β g) = eval (chartLift σ i x) g := by
    intro x g
    induction g using MvPolynomial.induction_on with
    | C c => simp [β]
    | add f g hf hg => simp [hf, hg]
    | mul_X f q hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [β, chartLift]
  have hvanS : ∀ f, f ∈ setSegChartIdeal (conePts Q) σ i ↔ ∀ x ∈ S, eval x f = 0 := fun f => by
    simp [setSegChartIdeal, hS, MvPolynomial.mem_vanishingIdeal_iff]
  have hvanT : ∀ g, g ∈ MvPolynomial.vanishingIdeal ℂ T ↔ ∀ y ∈ T, eval y g = 0 := fun g => by
    simp [MvPolynomial.mem_vanishingIdeal_iff]
  have htr := minimalPrimes_transfer α.toRingHom β.toRingHom (setSegChartIdeal (conePts Q) σ i)
    (MvPolynomial.vanishingIdeal ℂ T)
    (fun f hf => by
      rw [Ideal.mem_comap, hvanT]
      intro y hy
      show eval y (α f) = 0
      rw [hα]
      exact (hvanS f).1 hf _ (hsegT y hy))
    (fun g hg => by
      rw [Ideal.mem_comap, hvanS]
      intro x hx
      show eval x (β g) = 0
      rw [hβ]
      exact (hvanT g).1 hg _ (hliftS x hx))
    (fun f => by
      rw [hvanS]
      intro x hx
      show eval x (β (α f) - f) = 0
      rw [map_sub, hβ, hα, hsegLift x hx, sub_self])
    (fun g => by
      rw [hvanT]
      intro y hy
      show eval y (α (β g) - g) = 0
      rw [map_sub, hα, hβ, hliftSeg y hy, sub_self])
    J hJ
  obtain ⟨hmin, hd⟩ := htr
  rw [hd]
  rw [hT, MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, Ideal.radical_minimalPrimes] at hmin
  exact ringKrullDim_of_mem_minimalPrimes_chartIdeal hPCh e hdim' i hmin

theorem setSegreCone_smul {Q : Ideal (MRingOver ℂ ι)} (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q) [Nonempty K]
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) :
    ∀ c ∈ setSegreCone (conePts Q) σ, ∀ a : ℂ, a ≠ 0 → a • c ∈ setSegreCone (conePts Q) σ := by
  rintro _ ⟨z, hz, rfl⟩ a ha
  obtain ⟨z', hz', hseg⟩ := exists_segre_smul hQ hz ha
  exact ⟨z', hz', funext fun b => by simp [hseg]⟩

theorem chart_eq (S : Set ((Σ k, ι k) → ℂ)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    setChartSet S σ Ψ = {x | x ∈ setSegreCone S σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm (psiCoeffs σ Ψ)) = 1} := by
  have hl : ∀ z : (Σ k, ι k) → ℂ,
      eval (fun a => segre z (σ a)) (GroundTheory.Heights₂.Heights.linForm (psiCoeffs σ Ψ)) = Ψ (segre z) 0 := fun z => by
    rw [show GroundTheory.Heights₂.Heights.linForm (psiCoeffs σ Ψ) = GoodChartZeroSet.linForm σ Ψ from rfl, GoodChartZeroSet.eval_linForm]
    simp
  ext x
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, (hl z).trans h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, (hl z).symm.trans h1, rfl⟩


omit [∀ k, Fintype (ι k)] in
theorem segChart_eq (S : Set ((Σ k, ι k) → ℂ)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (a : Fin m) :
    setSegChartSet S σ (σ a) = {x | x ∈ setSegreCone S σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm (Pi.single a (1 : ℂ))) = 1} := by
  ext x
  simp only [setSegChartSet, setSegreCone, Set.mem_ofPred_eq, linForm_single', eval_X]
  constructor
  · rintro ⟨z, hz, h1, rfl⟩
    exact ⟨⟨z, hz, rfl⟩, h1⟩
  · rintro ⟨⟨z, hz, rfl⟩, h1⟩
    exact ⟨z, hz, h1, rfl⟩

theorem chart_dim {Q : Ideal (MRingOver ℂ ι)} (hQp : Q.IsPrime) (hQ : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal Q)
    [Nonempty K] {e : ℕ} (hdim : ringKrullDim (MRingOver ℂ ι ⧸ Q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞))
    {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ (setChartIdeal (conePts Q) σ Ψ).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) := by
  classical
  have hC := setSegreCone_smul hQ σ
  set t := psiCoeffs σ Ψ
  have hS : setChartSet (conePts Q) σ Ψ = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm t) = 1} := chart_eq _ σ Ψ
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : setChartIdeal (conePts Q) σ Ψ ≤ J := hJ.1.2
  set H := vanishingIdeal ℂ (setSegreCone (conePts Q) σ)
  have hH : IsHomogIdeal H := ConeVanishingHomog.proof m _ hC
  have hHI : H ≤ setChartIdeal (conePts Q) σ Ψ := by
    rw [setChartIdeal, hS]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  have hℓ1 : GroundTheory.Heights₂.Heights.linForm t - 1 ∈ setChartIdeal (conePts Q) σ Ψ := by
    rw [setChartIdeal, hS, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]

  obtain ⟨W, hW, hℓW, hWJ, hWcore⟩ := ChartHomogenise.proof ℂ m J t hJp (hIJ hℓ1)
  have hHW : H ≤ W := hWcore H hH (hHI.trans hIJ)
  obtain ⟨a, ha⟩ := exists_X_not_mem hℓW
  set u : Fin m → ℂ := Pi.single a 1
  have huW : GroundTheory.Heights₂.Heights.linForm u ∉ W := by rw [linForm_single']; exact ha
  have hT : setSegChartSet (conePts Q) σ (σ a) = {x | x ∈ setSegreCone (conePts Q) σ ∧ eval x (GroundTheory.Heights₂.Heights.linForm u) = 1} :=
    segChart_eq _ σ a

  have := ChartDehomogPrime.proof ℂ m W u hW huW
  have hTJ' : setSegChartIdeal (conePts Q) σ (σ a) ≤ W ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u - 1} := by
    rw [setSegChartIdeal, hT]; exact ConeSliceIdeal.proof m _ u W hC hHW
  obtain ⟨Q₀, hQ₀, hQ₀J'⟩ := Ideal.exists_minimalPrimes_le hTJ'
  have hdimQ₀ := segChart_dim hQp hQ hdim σ (σ a) hQ₀
  have hu1 : GroundTheory.Heights₂.Heights.linForm u - 1 ∈ setSegChartIdeal (conePts Q) σ (σ a) := by
    rw [setSegChartIdeal, hT, mem_vanishingIdeal_iff]
    intro x hx
    simp [hx.2]
  have hHT : H ≤ setSegChartIdeal (conePts Q) σ (σ a) := by
    rw [setSegChartIdeal, hT]; exact vanishingIdeal_anti_mono fun x hx => hx.1
  obtain ⟨V, hV, huV, hVQ₀, hVcore⟩ := ChartHomogenise.proof ℂ m Q₀ u hQ₀.1.1 (hQ₀.1.2 hu1)
  have hHV : H ≤ V := hVcore H hH (hHT.trans hQ₀.1.2)
  have hVW : V ≤ W := le_of_homog_le_sup hV.isHomog hW.isPrime hW.isHomog huW
    ((le_sup_left.trans hVQ₀.le).trans hQ₀J')

  have hIV : setChartIdeal (conePts Q) σ Ψ ≤ V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm t - 1} := by
    rw [setChartIdeal, hS]; exact ConeSliceIdeal.proof m _ t V hC hHV
  have hVJ : V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm t - 1} ≤ J :=
    sup_le (hVW.trans (le_sup_left.trans hWJ.le)) ((Ideal.span_singleton_le_iff_mem _).2 (hIJ hℓ1))
  have hJmin : J ∈ (V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm t - 1}).minimalPrimes :=
    ⟨⟨hJp, hVJ⟩, fun Z hZ hZJ => hJ.2 ⟨hZ.1, hIV.trans hZ.2⟩ hZJ⟩
  have hQ₀min : Q₀ ∈ (V ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u - 1}).minimalPrimes := by
    have := hQ₀.1.1
    rw [hVQ₀, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl

  have d₁ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V J (GroundTheory.Heights₂.Heights.linForm t - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top t) hJmin
  have d₂ := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.dimPIT ℂ (Fin m) V Q₀ (GroundTheory.Heights₂.Heights.linForm u - 1) hV.isPrime
    (linForm_sub_one_not_mem hV.isHomog hV.isPrime.ne_top u) hQ₀min
  rw [← d₂, hdimQ₀] at d₁
  exact eq_of_add_one_eq d₁

end Dim

end GlobalTheory.CompanionTheory.Ar.Pub.CxChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVSmul
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Cover GlobalTheory.CompanionTheory.Ar.PB.ValRing

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_smul {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (c : K → ℂ)
    (z : (Σ k, ιk k) → ℂ) (q : Σ k, ι k) :
    upV v (fun p => c (κ p.1) * z p) q = c q.1 * upV v z q := by
  unfold upV
  by_cases h : ∃ q', v q' = q
  · rw [dif_pos h, dif_pos h]
    have e : κ h.choose.1 = q.1 := by
      rw [← hb.2.2.1, h.choose_spec]
    show c (κ h.choose.1) * z h.choose = _
    rw [e]
  · rw [dif_neg h, dif_neg h, mul_zero]

end Scale

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)), IsBlockMap κ v → (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) → ∀ z ∈ mcPts (mCoordIdeal (y ∘ v)), ∃ (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsPCtx M Rb keep κ v F kb V bl r h ∧ z ∈ pO M Rb keep v F kb V r h := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n Rb keep Kk _ ιk _ κ v hbm hrange z hz
  obtain ⟨bs, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange
  obtain ⟨-, fr, -⟩ := CPts.main K ι Φ y Ψ N j M
  have hzb : pBase M v z ∈ mcPts (mCoordIdeal M.x) := bs z hz
  obtain ⟨F, hF, hG⟩ := fr _ hzb
  have hnon : Nonempty Rb.X := by
    obtain ⟨x, -⟩ := Rb.surj _ hzb fun h => by
      have := h.2 1 Submodule.mem_top
      simp at this
    exact ⟨x⟩
  obtain ⟨r, hr1, hr2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.exists_continuousOn_inv_pts _ _ _ n Rb hnon
  have hx0 := hr1 _ hzb
  obtain ⟨kb, V, bl, hsrc, hV, hBC⟩ := GlobalTheory.T.exists_base_chart_at_good_point K ι Φ y Ψ N j M n Rb F (r (pBase M v z))
    (by rw [CovMap.mCoordIdeal_eq_of_sameOrbit hx0]; exact hG)
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hsrc] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (pBase M v z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (pBase M v z) := orbit_trans (orbit_symm hblorb) hx0
  have hval : ∀ s, (∃ u, IsValueAt M.x s zc u) → valAt M.x s (pBase M v z) = valAt M.x s zc :=
    fun s hs => valAt_eq_of_orbit hblm hzb (orbit_symm horb) hs
  obtain ⟨c₀, hc₀, he⟩ := horb
  let c : K → ℂ := fun k => if h : ∀ p, M.blk p ≠ some k then c₀ ⟨k, h⟩ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases h : ∀ p, M.blk p ≠ some k
    · simp only [c, dif_pos h]
      exact hc₀ _
    · simp only [c, dif_neg h]
      exact one_ne_zero
  let z' : (Σ k, ιk k) → ℂ := fun p => c (κ p.1) * z p
  have hz' : z' ∈ mcPts (mCoordIdeal (y ∘ v)) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) (fun k => c (κ k)) (fun k => hc _) hz
  have hbp : pBase M v z' = zc := by
    rw [he]
    funext q
    obtain ⟨⟨k, hk⟩, m⟩ := q
    show upV v z' ⟨k, m⟩ = c₀ ⟨k, hk⟩ * upV v z ⟨k, m⟩
    rw [upV_smul hbm c z ⟨k, m⟩]
    simp only [c, dif_pos hk]
  obtain ⟨h, hh, H⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.PFl.Fwd.main K ι Φ y Ψ N j M keep Kk ιk κ v hbm hrange F z' hF hz'
    (hbp ▸ hblgood) (hbp ▸ hblnorm)
  refine ⟨F, kb, V, bl, r, h, ⟨hbm, hrange, hF, hBC, hr1, hr2, hh⟩, hz, hsrc, ?_, ?_⟩
  · rw [hzc] at *
    exact hV
  · intro p k hkeep hp
    obtain ⟨A, hA0, hA'⟩ := H p k hkeep hp
    have hk : c k = 1 := dif_neg fun e => e p hp
    have hw : ∀ m : ι k, upV v z ⟨k, m⟩ =
        A * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (pBase M v z) * minorIJ (h p.1) I (stepCols N j p.2) := fun m => by
      have e : upV v z' ⟨k, m⟩ = upV v z ⟨k, m⟩ := by
        rw [upV_smul hbm c z ⟨k, m⟩]
        show c k * _ = _
        rw [hk, one_mul]
      rw [← e, hA' m, hbp]
      refine congrArg (fun s => A * s) (Finset.sum_congr rfl fun I _ => ?_)
      rw [hval _ (exists_isValueAt hblm (hblgood.2.1 _ I).1)]
    rw [twMinor_of_flag M hF hzb hG hp (hh p.1).1 hw, Matrix.nonsing_inv_mul _ (hh p.1).2.isUnit, CPts.minorIJ_one,
      mul_one]
    exact hA0

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Cover
end
end

