module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminant

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBaseBlockValue
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem transPt_block_base : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z₁ : (Σ k, ι' k) → ℂ) (z₀ : (Σ k, ι k) → ℂ) (kb : NonPluckerBlocks M.blk), z₁ ∈ mcPts (mCoordIdeal y') → SameOrbit (basePart M.blk z₀) (basePart M'.blk z₁ ∘ Cv.v) → ∃ (e : Φ') (s : ι kb.1 → Φ') (t : ℂ), e ≠ 0 ∧ t ≠ 0 ∧ ∀ i, transPt Cv ⟨kb.1, i⟩ = e * s i ∧ IsValueAt y' (s i) z₁ (t * z₀ ⟨kb.1, i⟩) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z₁ z₀ kb hz hO
  obtain ⟨c₀, hc₀, e₀⟩ := hO
  obtain ⟨c, hc⟩ := hz.1 (Cv.κ kb).1
  obtain ⟨hy, hv⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.isValueAt_coord_ratio K' ι' Φ' y' z₁ (Cv.κ kb).1 c hz hc
  have hw : ∀ i : ι kb.1, ∃ m : ι' (Cv.κ kb).1, Cv.v ⟨kb, i⟩ = ⟨Cv.κ kb, m⟩ := fun i => by
    have h1 := Cv.block.2.2.1 ⟨kb, i⟩
    rcases hq : Cv.v ⟨kb, i⟩ with ⟨k, m⟩
    rw [hq] at h1
    obtain rfl : k = Cv.κ kb := h1
    exact ⟨m, rfl⟩
  choose w hw using hw
  refine ⟨y' ⟨(Cv.κ kb).1, c⟩, fun i => y' ⟨(Cv.κ kb).1, w i⟩ / y' ⟨(Cv.κ kb).1, c⟩,
    (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹, hy, inv_ne_zero (mul_ne_zero (hc₀ kb) hc), fun i => ⟨?_, ?_⟩⟩
  · rw [mul_div_cancel₀ _ hy]
    have h1 := transPt_base Cv (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
    rw [← Cv.x_eq, hw i, ← M'.y_base] at h1
    exact h1
  · have h2 : z₀ ⟨kb.1, i⟩ = c₀ kb * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      have h3 := congrFun e₀ (⟨kb, i⟩ : Σ k, baseIdx ι M.blk k)
      simp only [Function.comp, hw i] at h3
      exact h3
    have h4 : (c₀ kb * z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₀ ⟨kb.1, i⟩ =
        (z₁ ⟨(Cv.κ kb).1, c⟩)⁻¹ * z₁ ⟨(Cv.κ kb).1, w i⟩ := by
      rw [h2]
      have := hc₀ kb
      field_simp
    rw [h4]
    exact hv (w i)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointInPoints
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}

theorem mConeMap_rename {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv.2.2.1 n]

theorem rename_mem_iff {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    rename v g ∈ mCoordIdeal y ↔ g ∈ mCoordIdeal (y ∘ v) := by
  change mConeMap y (rename v g) = 0 ↔ mConeMap (y ∘ v) g = 0
  rw [mConeMap_rename hv]
  exact map_eq_zero_iff _ (rename_injective κ hv.1)

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

theorem mCoordIdeal_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) :
    mCoordIdeal (φ ∘ x) = mCoordIdeal x := by
  ext g
  change mConeMap (φ ∘ x) g = 0 ↔ mConeMap x g = 0
  rw [mConeMap_comp]
  exact map_eq_zero_iff _ (map_injective φ φ.injective)

theorem eval_rename_eq (z : (Σ k, ι' k) → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v g)) = eval (z ∘ v) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]

theorem sum_mapDomain_block (hv : ∀ p, (v p).1 = κ p.1) [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename_block (hb : IsBlockMap κ v) {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  classical
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨⟨k₀, i⟩, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hv.1 ((hv.2.2.1 ⟨k₀, i⟩).symm.trans (congrArg Sigma.fst hp))
    subst hk
    exact ⟨i, by simpa [hp] using hi'⟩
  · have h1 : rename v f ∈ mCoordIdeal x' := by
      rw [rename_mem_iff hv, show x' ∘ v = φ ∘ x from funext hx, mCoordIdeal_comp]
      exact hf
    rw [← eval_rename_eq]
    exact hz.2 _ h1

theorem aeval_rename_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'}
    (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q)) (f : MRing ι) :
    aeval x' (rename v f) = φ (aeval x f) := by
  rw [aeval_rename, show x' ∘ v = φ ∘ x from funext hx, aeval_def, aeval_def, algebraMap_int_eq,
    algebraMap_int_eq, eval₂_comp_left φ, RingHom.ext_int (φ.comp (Int.castRingHom Ω)) (Int.castRingHom Ω')]

theorem regAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal (z ∘ v)) s) :
    RegAt x' (mCoordIdeal z) (φ s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh,
    fun hm => hn ((rename_mem_iff hv z h).1 hm), ?_⟩
  rw [aeval_rename_pull φ hx, aeval_rename_pull φ hx, heq, map_mul]

theorem isValueAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} {w : ℂ} (hs : IsValueAt x s (z ∘ v) w) : IsValueAt x' (φ s) z w := by
  obtain ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩ := hs
  have hpull := aeval_rename_pull (v := v) φ hx
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh, ?_, ?_, ?_, ?_⟩
  · rw [hpull]; exact (map_ne_zero φ).2 hy
  · rw [hpull, hpull, heq, map_mul]
  · rwa [eval_rename_eq]
  · rw [eval_rename_eq, eval_rename_eq]

end General

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) ∧ ∀ s : M.Ω, RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hzb
  have hz := comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hzb
  refine ⟨hz, fun s hs => ?_⟩
  obtain ⟨w, hw⟩ := ValRing.exists_isValueAt hz hs
  have hw' := isValueAt_pull Cv.block Cv.φ Cv.x_eq hw
  exact ⟨regAt_pull Cv.block Cv.φ Cv.x_eq hs, by rw [valAt_eq hzb hw', valAt_eq hz hw]⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFrameCompatibility
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem trans_blockDiag_det : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (b : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), b ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal b) → M.GoodAt F (mCoordIdeal (b ∘ Cv.v)) → ∀ τ, IsBlockDiag j (Cv.trans F' F b τ) ∧ (Cv.trans F' F b τ).det ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv b F' F hb hF' hF hG' hG τ
  have hT := hF.1 τ
  have hT' := hF'.1 τ
  have hdet : ((F.T τ).map Cv.φ).det ≠ 0 := by
    have e : ((F.T τ).map Cv.φ).det = Cv.φ (F.T τ).det := by
      rw [RingHom.map_det]; rfl
    rw [e]
    exact (map_ne_zero Cv.φ).2 hT.2
  have hu : IsUnit ((F.T τ).map Cv.φ).det := isUnit_iff_ne_zero.2 hdet
  have hu' : IsUnit (F'.T τ).det := isUnit_iff_ne_zero.2 hT'.2
  have hA : IsBlockDiag j (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) :=
    ((hT.1.map Cv.φ).inv hu).mul hT'.1
  have hreg := Cv.agree b hb F' F hF' hF hG' hG τ
  have hz : valMat M'.x b (1 : Matrix (Fin N) (Fin N) M'.Ω) = 1 := by
    have hring := ValRing.regAt_valAt_ring _ _ _ M'.x b hb
    ext a c
    by_cases e : a = c
    · subst e
      show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a a) b = _
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact hring.2.2.2.1
    · show valAt M'.x ((1 : Matrix (Fin N) (Fin N) M'.Ω) a c) b = _
      rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e]
      exact hring.2.2.1
  have hAB : (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) * ((F'.T τ)⁻¹ * (F.T τ).map Cv.φ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu', Matrix.nonsing_inv_mul _ hu]
  have hmul := (regMat_mul hb (fun a c => (hreg a c).1) (fun a c => (hreg a c).2)).2
  rw [hAB, hz] at hmul
  have htr : Cv.trans F' F b τ = valMat M'.x b (((F.T τ).map Cv.φ)⁻¹ * F'.T τ) := rfl
  refine ⟨fun a c h => ?_, ?_⟩
  · show valAt M'.x ((((F.T τ).map Cv.φ)⁻¹ * F'.T τ) a c) b = 0
    rw [hA a c h]
    exact (ValRing.regAt_valAt_ring _ _ _ M'.x b hb).2.2.1
  · rw [htr]
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact one_ne_zero this

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesPullback
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr

section Minors

variable {R S : Type} [CommRing R] [CommRing S] {N : ℕ}

theorem minor_map (f : R →+* S) (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · rw [map_zero]

theorem minor_one_self (I : Finset (Fin N)) : minorIJ (1 : Matrix (Fin N) (Fin N) R) I I = 1 := by
  unfold minorIJ
  rw [dite_eq_left rfl, Matrix.submatrix_one _ (I.orderEmbOfFin rfl).injective, Matrix.det_one]

theorem detFac_one' (j : ℕ) (i : Fin N) : detFac j i (1 : Matrix (Fin N) (Fin N) R) = 1 := by
  simp [detFac, minor_one_self]

theorem stepCols_ne_empty (j : ℕ) (i : Fin N) : stepCols N j i ≠ ∅ := by
  have hi := i.2
  apply Finset.Nonempty.ne_empty
  by_cases h : (i : ℕ) + 1 ≤ j
  · exact ⟨⟨N - j, by omega⟩, by simp [stepCols, h]; omega⟩
  · exact ⟨⟨0, by omega⟩, by simp [stepCols, h]; omega⟩

theorem detFac_ne_zero' {E : Type} [Field E] {j : ℕ} (hj : j ≤ N) (i : Fin N) {T : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) : detFac j i T ≠ 0 := by
  have h := ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main E N j i hj).2.2.2 T T⁻¹ hT (hT.inv (isUnit_iff_ne_zero.2 hd))).2
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd), detFac_one'] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h

theorem det_map_ne {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T.map f).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero f).2 hd

theorem inv_map' {A B : Type} [Field A] [Field B] (f : A →+* B) {T : Matrix (Fin N) (Fin N) A} (hd : T.det ≠ 0) :
    (T⁻¹).map f = (T.map f)⁻¹ := by
  refine (Matrix.inv_eq_right_inv ?_).symm
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd)]
  exact Matrix.map_one _ (map_zero f) (map_one f)

end Minors

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem flag_in_frame_blockDiag {E : Type} [Field E] {T g : Matrix (Fin N) (Fin N) E}
    (hT : IsBlockDiag j T) (hd : T.det ≠ 0) (hg : IsBlockDiag j g) : IsBlockDiag j (T⁻¹ * g) :=
  (hT.inv (isUnit_iff_ne_zero.2 hd)).mul hg

theorem read_minor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (hF : M.IsFrame F)
    (p : Ψ × Fin N) (k : K) (hk : M.blk p = some k) (I' : Finset (Fin N)) (hI' : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1).map (algebraMap M.Ω Φ)) *
        ∑ m : ι k, algebraMap M.Ω Φ (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩ =
      algebraMap M.Ω Φ (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
        minorIJ (((F.T p.1).map (algebraMap M.Ω Φ))⁻¹ * M.g p.1) I' (stepCols N j p.2) := by
  set α : M.Ω →+* Φ := algebraMap M.Ω Φ with hα
  set T := (F.T p.1).map α with hTdef
  have hdet : T.det ≠ 0 := det_map_ne α (hF.1 p.1).2
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map α
  set h := T⁻¹ * M.g p.1 with hh
  have hb : IsBlockDiag j h := flag_in_frame_blockDiag hTb hdet (M.g_block p.1)
  have hTh : T * h = M.g p.1 := by
    rw [hh, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hy : ∀ m : ι k, detFac j p.2 T * y ⟨k, m⟩ =
      α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, α (F.u ⟨k, m⟩ I) * minorIJ h I (stepCols N j p.2) := fun m => by
    have := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map K ι Φ y Ψ N j M Φ α F hF p k hk m h hb
    rw [← hTdef, hTh] at this
    rw [M.y_step p k hk m]
    exact this
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h I (stepCols N j p.2) = 0 := fun I hI =>
    ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main Φ N j p.2 M.j_le).2.1 h I hb hI).resolve_right (stepCols_ne_empty j p.2)
  calc detFac j p.2 T * ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * y ⟨k, m⟩
      = ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * (detFac j p.2 T * y ⟨k, m⟩) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun m _ => by ring
    _ = α (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * ∑ I, (∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I)) *
          minorIJ h I (stepCols N j p.2) := by
        simp only [hy, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun m _ => by ring
    _ = _ := by
        congr 1
        have hs : ∀ I, IsStepRows N j p.2 I → ∑ m : ι k, α (F.u' I' ⟨k, m⟩) * α (F.u ⟨k, m⟩ I) = if I' = I then 1 else 0 := fun I hI => by
          have := hF.2.2.1 p k hk I' I hI' hI
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [← map_mul, ← map_sum, this]
          split_ifs <;> simp
        rw [Finset.sum_eq_single I' (fun I _ hne => ?_) (by simp), hs I' hI', if_pos rfl, one_mul]
        by_cases hI : IsStepRows N j p.2 I
        · rw [hs I hI, if_neg (Ne.symm hne), zero_mul]
        · rw [hv I hI, mul_zero]

theorem transPt_eq_smul_sum : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), M'.IsFrame F' → M.IsFrame F → (∀ k, M'.x ⟨k, F'.c k⟩ ≠ 0) → (∀ k, M.x ⟨k, F.c k⟩ ≠ 0) → ∀ (p : Ψ × Fin N) (k : K) (k' : K'), M.blk p = some k → M'.blk p = some k' → ∃ c : Φ', c ≠ 0 ∧ ∀ m : ι k, transPt Cv ⟨k, m⟩ = c * ∑ m' : ι' k', algebraMap M'.Ω Φ' (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv F' F hF' hF hc' hc p k k' hk hk'
  set α : M'.Ω →+* Φ' := algebraMap M'.Ω Φ' with hα
  set ρ : M.Ω →+* Φ' := α.comp Cv.φ with hρ
  set T' := (F'.T p.1).map α with hT'
  set T := (F.T p.1).map ρ with hT
  have hdetφ : ((F.T p.1).map Cv.φ).det ≠ 0 := det_map_ne Cv.φ (hF.1 p.1).2
  have hdet' : T'.det ≠ 0 := det_map_ne α (hF'.1 p.1).2
  have hdet : T.det ≠ 0 := det_map_ne ρ (hF.1 p.1).2
  have hTb' : IsBlockDiag j T' := (hF'.1 p.1).1.map α
  have hTb : IsBlockDiag j T := (hF.1 p.1).1.map ρ
  set h' := T'⁻¹ * M'.g p.1 with hh'
  set h₀ := T⁻¹ * M'.g p.1 with hh₀
  have hb' : IsBlockDiag j h' := flag_in_frame_blockDiag hTb' hdet' (M'.g_block p.1)
  have hb₀ : IsBlockDiag j h₀ := flag_in_frame_blockDiag hTb hdet (M'.g_block p.1)
  have hTh₀ : T * h₀ = M'.g p.1 := by
    rw [hh₀, Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet)]
  have hμ' : α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') ≠ 0 :=
    (map_ne_zero α).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc' k''))
  have hμ : ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') ≠ 0 :=
    (map_ne_zero ρ).2 (Finset.prod_ne_zero_iff.2 fun k'' _ => zpow_ne_zero _ (hc k''))
  have hd' : detFac j p.2 T' ≠ 0 := detFac_ne_zero' M'.j_le p.2 hTb' hdet'
  have hd : detFac j p.2 T ≠ 0 := detFac_ne_zero' M.j_le p.2 hTb hdet
  set μ' := α (∏ k'', M'.x ⟨k'', F'.c k''⟩ ^ M'.b p k'') with hμ'def
  set μ := ρ (∏ k'', M.x ⟨k'', F.c k''⟩ ^ M.b p k'') with hμdef
  set d' := detFac j p.2 T' with hd'def
  set d := detFac j p.2 T with hddef
  have hread : ∀ I', IsStepRows N j p.2 I' → minorIJ h' I' (stepCols N j p.2) =
      d' / μ' * ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := fun I' hI' => by
    have := read_minor M' F' hF' p k' hk' I' hI'
    rw [div_mul_eq_mul_div, eq_div_iff hμ', mul_comm]
    exact this.symm
  have hv : ∀ I, ¬ IsStepRows N j p.2 I → minorIJ h' I (stepCols N j p.2) = 0 := fun I hI =>
    ((_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main Φ' N j p.2 M'.j_le).2.1 h' I hb' hI).resolve_right (stepCols_ne_empty j p.2)
  have hmat : h₀ = (trMat Cv F' F p.1).map α * h' := by
    have e : ((F.T p.1).map Cv.φ).map α = T := Matrix.ext fun _ _ => rfl
    rw [trMat, Matrix.map_mul, inv_map' α hdetφ, e, ← hT', hh', Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 hdet')]
  have e3 : ∀ I, minorIJ h₀ I (stepCols N j p.2) =
      ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (minorIJ (trMat Cv F' F p.1) I I') * minorIJ h' I' (stepCols N j p.2) := fun I => by
    rw [hmat, (_root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main Φ' N j p.2 M'.j_le).1]
    simp only [minor_map]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun I' _ hI' => ?_).symm
    rw [hv I' (by simpa using hI'), mul_zero]
  have e1 : ∀ m : ι k, d * transPt Cv ⟨k, m⟩ =
      μ * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := fun m => by
    have := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovGraph.FrameExt.frame_identity_map K ι Φ y Ψ N j M Φ' ρ F hF p k hk m h₀ hb₀
    rw [← hT, hTh₀] at this
    rw [transPt_step Cv p k hk m]
    exact this
  refine ⟨μ / d * (d' / μ'), mul_ne_zero (div_ne_zero hμ hd) (div_ne_zero hd' hμ'), fun m => ?_⟩
  have htr : transPt Cv ⟨k, m⟩ = μ / d * ∑ I, α (Cv.φ (F.u ⟨k, m⟩ I)) * minorIJ h₀ I (stepCols N j p.2) := by
    rw [div_mul_eq_mul_div, eq_div_iff hd, mul_comm]
    exact e1 m
  have hR : ∑ m' : ι' k', α (coE Cv F' F p ⟨k, m⟩ ⟨k', m'⟩) * y' ⟨k', m'⟩ =
      ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2),
        α (Cv.φ (F.u ⟨k, m⟩ I)) * α (minorIJ (trMat Cv F' F p.1) I I') *
          ∑ m' : ι' k', α (F'.u' I' ⟨k', m'⟩) * y' ⟨k', m'⟩ := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [coE, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun I' _ => Finset.sum_congr rfl fun m' _ => by ring
  rw [htr, mul_assoc, hR]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [e3 I, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' hI' => ?_
  rw [hread I' (Finset.mem_filter.1 hI').2]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.StepExpr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GMatIsGenericFlagStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenericFlag_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω], GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag Ω p (gMat (Ψ := Ψ) p q Ω) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenMat.gMat_isGenericFlag <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminantStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base <;> assumption)
end

