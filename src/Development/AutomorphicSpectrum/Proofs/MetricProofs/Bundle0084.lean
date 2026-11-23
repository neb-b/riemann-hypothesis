module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsAntisym
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ModelMonomialWeightProduct
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial

theorem step_monomial : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ) (h : ModelOK A x₀ m) (Φ : Type) [Field Φ] (y : K₀ ⊕ StepIx Ψ p q → Φ), (∀ k, y k ≠ 0) → ∀ (τ : Ψ) (i : Fin (p + q)), (∀ h1 : (i : ℕ) < p, ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (((i : ℕ) + 1) * m (.inl τ)) / y (.inr ⟨.inl τ, ⟨i, h1⟩⟩)) ∧ (∀ h1 : p ≤ (i : ℕ), ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) = (∏ k, y (.inl k)) ^ (p * m (.inl τ) + ((i : ℕ) - p + 1) * m (.inr τ)) / ((if h0 : 0 < p then y (.inr ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩) else 1) * y (.inr ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩))) := by
  classical
  intro Ψ _ p q Ω _ _ n A K₀ _ J₀ _ x₀ m h Φ _ y hy τ i
  obtain ⟨hbase, hstep⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.FMX.Dy.dy_flag Ψ p q Ω n A K₀ J₀ x₀ m h τ i
  have hsplit : ∏ k, y k ^ (-((model A x₀ m h).dy (τ, i) k)) =
      (∏ k, y (.inl k)) ^ (rkW i * m (.inl τ) + rkO i * m (.inr τ)) *
        ∏ t, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) := by
    rw [Fintype.prod_sum_type, ← Finset.prod_pow]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hbase k, neg_neg, zpow_natCast]
  have hval : ∀ t : StepIx Ψ p q, y (.inr t) ^ (-((model A x₀ m h).dy (τ, i) (.inr t))) =
      if (t = stepOf Ψ p q (τ, i) ∨ (t.1 = .inl τ ∧ (t.2 : ℕ) + 1 = p ∧ p ≤ (i : ℕ))) then (y (.inr t))⁻¹
      else 1 := by
    intro t
    split_ifs with hc
    · rw [(hstep t).1 hc, _root_.zpow_neg, zpow_one]
    · rw [(hstep t).2 hc, neg_zero, zpow_zero]
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inl τ, ⟨i, h1⟩⟩ := by
      unfold stepOf
      exact dif_pos h1
    have hW : rkW i = (i : ℕ) + 1 := by unfold rkW; omega
    have hO : rkO i = 0 := by unfold rkO; omega
    rw [hsplit, hW, hO, zero_mul, add_zero, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval,
      if_pos (Or.inl rfl), hso, div_eq_mul_inv]
    intro t ht
    rw [hval, if_neg]
    rintro (h' | ⟨-, -, hp⟩)
    · exact ht h'
    · omega
  · have hso : stepOf Ψ p q (τ, i) = ⟨.inr τ, ⟨(i : ℕ) - p, by have := i.2; show _ < q; omega⟩⟩ := by
      unfold stepOf
      exact dif_neg (not_lt.2 h1)
    have hW : rkW i = p := by unfold rkW; omega
    have hO : rkO i = (i : ℕ) - p + 1 := by unfold rkO; omega
    rw [hsplit, hW, hO]
    by_cases hp0 : 0 < p
    · rw [dif_pos hp0]
      have hne : stepOf Ψ p q (τ, i) ≠ ⟨.inl τ, ⟨p - 1, by show _ < p; omega⟩⟩ := by
        rw [hso]
        intro he
        exact Sum.inr_ne_inl (congrArg Sigma.fst he)
      rw [Fintype.prod_eq_mul _ _ hne, hval, hval, if_pos (Or.inl rfl),
        if_pos (Or.inr ⟨rfl, show p - 1 + 1 = p by omega, h1⟩), hso]
      · rw [div_eq_mul_inv, mul_inv]
        ring
      · rintro x ⟨hx1, hx2⟩
        rw [hval, if_neg]
        rintro (h' | ⟨hs, hj, -⟩)
        · exact hx1 h'
        · apply hx2
          obtain ⟨s, j⟩ := x
          dsimp only at hs hj
          subst hs
          exact Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp; omega)))
    · rw [dif_neg hp0, one_mul, Fintype.prod_eq_single (stepOf Ψ p q (τ, i)), hval, if_pos (Or.inl rfl), hso,
        div_eq_mul_inv]
      intro t ht
      rw [hval, if_neg]
      rintro (h' | ⟨-, hj, -⟩)
      · exact ht h'
      · omega

end GlobalTheory.CompanionTheory.Ar.PB.FMX.StepMonomial
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SumOverEmbeddingsUnitInvariance
section
set_option maxSynthPendingDepth 1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem sum_log_unit_mul_mass_eq_zero : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  intro hSys hInt K _ ι _ Ω _ F _ _ _ y D L θ hP hbir hL hex
  classical
  obtain ⟨II, hII, -⟩ := hSys
  obtain ⟨x, hx⟩ : ∃ x : F, x = ((θ : 𝓞 F) : F) := ⟨_, rfl⟩
  have hmul : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) * x = 1 := by
    rw [hx]
    have h1 : (((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (θ : 𝓞 F)) = 1 := by simp
    exact_mod_cast congrArg (fun u : 𝓞 F => (u : F)) h1
  have hxinv : ((((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F)) = x⁻¹ := eq_inv_of_mul_eq_one_left hmul
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    exact zero_ne_one hmul
  have hxI : IsIntegral ℤ x := hx ▸ RingOfIntegers.isIntegral_coe (θ : 𝓞 F)
  have hxI' : IsIntegral ℤ x⁻¹ := hxinv ▸ RingOfIntegers.isIntegral_coe ((θ⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  rw [← hx]
  have ht0 : algebraMap F Ω x ≠ 0 := (map_ne_zero _).mpr hx0
  have htI : IsIntegral ℤ (algebraMap F Ω x) := hxI.map (algebraMap F Ω).toIntAlgHom
  have htI' : IsIntegral ℤ (algebraMap F Ω x)⁻¹ := by
    rw [← map_inv₀]
    exact hxI'.map (algebraMap F Ω).toIntAlgHom
  obtain ⟨d, f, g, hf, hg, hg0, hfg⟩ := hbir (algebraMap F Ω x)
  have hf0 : aeval y f ≠ 0 := by
    rw [hfg]
    exact mul_ne_zero ht0 hg0
  have hgP : g ∉ mCoordIdeal y := fun h => hg0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hg).mp h)
  have hfP : f ∉ mCoordIdeal y := fun h => hf0
    ((GroundTheory.Heights₂.Heights.Targets.BoundedSectionTransfer.mem_mCoordIdeal_iff y hf).mp h)
  obtain ⟨B, hB0, hBs, hBl⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun sg => ‖sg x‖) (fun sg => norm_pos_iff.mpr ((map_ne_zero sg).mpr hx0)) hex
  obtain ⟨A, hAa, hA⟩ : ∃ A : HermLine ι, (∀ k, A.a k = d k) ∧ IsSmoothHerm A :=
    ⟨HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (d k : ℤ)), fun _ => rfl,
      GroundTheory.Heights₂.Heights.Inter.isSmoothHerm_ofMetrics_fs _⟩
  have hAB : IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hBs
  have hABa : ∀ k, (A.tensor B).a k = d k := fun k => by
    simp [HermLine.tensor, hB0, hAa k]
  have hRA := (hII K ι).2.2 (mCoordIdeal y) D L A g d hP hL hA hAa hg hgP
  have hRB := (hII K ι).2.2 (mCoordIdeal y) D L (A.tensor B) f d hP hL hAB hABa hf hfP
  have hadd := (hII K ι).2.1 (mCoordIdeal y) D L A B hP hL hA hBs
  obtain ⟨hsupp, hmult⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.divCycle_eq_of_unit_ratio K ι Ω y D d f g (algebraMap F Ω x) hP hf hg hg0 ht0 htI htI' hfg
  have hlog : ∀ z ∈ mcPts (mCoordIdeal y), logNorm (A.tensor B) f z = logNorm A g z := by
    intro z hz
    obtain ⟨sg, hsg, -⟩ := hex z hz
    have hval : B.h z = ‖sg x‖ := (hBl z hz sg hsg).self_of_nhds
    have hfz := hsg d f g x hf hg hfg
    have hs0 : ‖sg x‖ ≠ 0 := norm_ne_zero_iff.mpr ((map_ne_zero sg).mpr hx0)
    have hAz : A.h z ≠ 0 := (A.pos z hz.1).ne'
    unfold logNorm
    congr 1
    show ‖eval z (map (Int.castRingHom ℂ) f)‖ / (A.h z * B.h z) = _
    rw [hfz, hval, norm_mul]
    field_simp
  have hrec : recR (II K ι) (mCoordIdeal y) L (A.tensor B) f = recR (II K ι) (mCoordIdeal y) L A g := by
    unfold recR
    rw [hsupp]
    congr 1
    · exact finsum_mem_congr rfl fun W hW => by rw [hmult W hW]
    · exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts _ (fun _ _ _ => rfl) hlog
  rw [← intersection_locConst_trivial hInt K ι Ω F y D L B (fun sg => ‖sg x‖) II hII hP hL hB0 hBs hex hBl]
  linarith [hRA, hRB, hadd, hrec]

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibility
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := h' k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem fstPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0 := fun k => h (some k)

theorem sndPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0 := by
  intro k
  by_cases e : k = k₀
  · subst e
    obtain ⟨i, hi⟩ := h none
    refine ⟨i, ?_⟩
    change z (v₁ k ⟨k, i⟩) ≠ 0
    rw [v₁_self]
    exact hi
  · obtain ⟨i, hi⟩ := h (some k)
    refine ⟨i, ?_⟩
    change z (v₁ k₀ ⟨k, i⟩) ≠ 0
    rw [v₁_ne (p := ⟨k, i⟩) e]
    exact hi

theorem basePart_snd_eq_fst {σ : Type} (blk : σ → Option K) {k₀ : K} (p : σ) (hp : blk p = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext q
  obtain ⟨⟨k, hk⟩, i⟩ := q
  have e : k ≠ k₀ := by
    rintro rfl
    exact hk p hp
  change z (v₁ k₀ ⟨k, i⟩) = z (v₀ k₀ ⟨k, i⟩)
  rw [v₁_ne (p := ⟨k, i⟩) e]
  rfl

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr hb hW x z₀ z₁ h₀ h₁
  have hL : ∀ o, ∃ i, RW.lift x x ⟨o, i⟩ ≠ 0 := (RW.mem x x (RW.mem_U x)).1
  have hbase : SameOrbit (basePart M.blk z₀) (Rb.lift (pr x) (pr x)) :=
    orbit_trans (basePart_orbit M.blk h₀) (orbit_symm (hW.2.1 x))
  refine ⟨?_, ?_, blocks_of_orbit h₀ (fstPt_blocks hL), blocks_of_orbit h₁ (sndPt_blocks hL)⟩
  · obtain ⟨c, hc, e⟩ := hbase
    rw [e]
    exact ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x _ c hc).2 (Rb.mem (pr x) (pr x) (Rb.mem_U _))).1
  · have h₁' := basePart_orbit M.blk h₁
    rw [basePart_snd_eq_fst M.blk (τ, a) hb] at h₁'
    exact orbit_trans h₁' (orbit_symm (basePart_orbit M.blk h₀))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

private theorem isPotential_secPot_of_isSmoothHerm {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)]
    {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ρ)} {e : ℕ} (R : ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes P J e)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ρ) (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A)
    (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (hVU : ∀ x, V x ⊆ R.U x)
    (c : ℝ) : ReciprocityTheory.AnForm.M.IsPotential R.A (secPot R A V hV hm c) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have hol : ∀ (x : R.X) (p : (k : κ) × ρ k) (j : Fin R.A.n) (t : Fin e → ℂ),
      t ∈ (R.A.chart j).target → (R.A.chart j).symm t ∈ R.U x →
      AnalyticAt ℂ (fun s => R.lift x ((R.A.chart j).symm s) p) t :=
    fun x p j t ht hu => R.holo x p j t ⟨ht, hu⟩
  have memNZ : ∀ (z0 y0 : R.X), y0 ∈ R.U z0 → ∀ k, ∃ i, R.lift z0 y0 ⟨k, i⟩ ≠ 0 := by
    intro z0 y0 h
    have h' := R.mem z0 y0 h
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.mcPts, Set.mem_ofPred_eq] at h'
    exact h'.1
  unfold ReciprocityTheory.AnForm.M.IsPotential ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn
    ReciprocityTheory.AnForm.M.FinHolAtlas.HoloOn
  dsimp only [secPot]
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t))
        ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) := by
      rw [contDiffOn_pi]
      intro p
      have h1 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t) p)
          ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) :=
        fun t ht => (hol x p j t ht.1 (hVU x ht.2)).contDiffAt.contDiffWithinAt
      exact h1.restrict_scalars ℝ
    have hmem : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        (∀ k, ∃ i, R.lift x ((R.A.chart j).symm t) ⟨k, i⟩ ≠ 0) :=
      fun t ht => memNZ x _ (hVU x ht.2)
    have hh := hA'.comp hlift (fun t ht => hmem t ht)
    have hne : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        A.h (R.lift x ((R.A.chart j).symm t)) ≠ 0 :=
      fun t ht => (A.pos _ (hmem t ht)).ne'
    exact (hh.log hne).add contDiffOn_const
  · obtain ⟨hyx, hyx'⟩ := hy
    have hyU : y ∈ R.U x := hVU x hyx
    have hyU' : y ∈ R.U x' := hVU x' hyx'
    choose i hi using memNZ x' y hyU'
    obtain ⟨r, hr⟩ : ∃ r : κ → R.X → ℂ,
        ∀ k z, r k z = R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ :=
      ⟨fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩, fun _ _ => rfl⟩
    have hry : ∀ k, r k y ≠ 0 := by
      intro k
      obtain ⟨cy, hcy, hly⟩ := R.compat x x' y ⟨hyU, hyU'⟩
      have h1 := congrFun hly ⟨k, i k⟩
      rw [hr, h1]
      exact div_ne_zero (mul_ne_zero (hcy k) (hi k)) (hi k)
    obtain ⟨j, hj⟩ := R.A.cover y
    have hD : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x')) :=
      (R.A.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x).inter (R.isOpen_U x'))
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Fin e → ℂ), O = {t | t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane} := ⟨_, rfl⟩
    have memO : ∀ t, t ∈ O ↔ (t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane) := by
      intro t; rw [hOdef]; rfl
    have hO : IsOpen O := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      obtain ⟨htT, htU, htne, htsl⟩ := (memO t).1 ht
      have hDn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x') ∈ 𝓝 t :=
        hD.mem_nhds ⟨htT, htU⟩
      have hca : ∀ (z0 : R.X) (p : (k : κ) × ρ k), (R.A.chart j).symm t ∈ R.U z0 →
          ContinuousAt (fun s => R.lift z0 ((R.A.chart j).symm s) p) t :=
        fun z0 p hz => (hol z0 p j t htT hz).continuousAt
      have e1 : ∀ᶠ s in 𝓝 t, ∀ k, R.lift x' ((R.A.chart j).symm s) ⟨k, i k⟩ ≠ 0 := by
        rw [Filter.eventually_all]
        intro k
        exact (hca x' _ htU.2).eventually_ne (htne k)
      have e2 : ∀ᶠ s in 𝓝 t, ∀ k, r k ((R.A.chart j).symm s) / r k y ∈ Complex.slitPlane := by
        rw [Filter.eventually_all]
        intro k
        have hc0 : ContinuousAt (fun s => r k ((R.A.chart j).symm s)) t := by
          simp only [hr]
          exact (hca x _ htU.1).div (hca x' _ htU.2) (htne k)
        have hc : ContinuousAt (fun s => r k ((R.A.chart j).symm s) / r k y) t :=
          hc0.div_const _
        exact hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (htsl k))
      filter_upwards [hDn, e1, e2] with s hs1 hs2 hs3
      exact (memO s).2 ⟨hs1.1, hs1.2, hs2, hs3⟩
    have hWopen : IsOpen ((R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O) :=
      (R.A.chart j).isOpen_inter_preimage hO
    have hsy : (R.A.chart j).symm ((R.A.chart j) y) = y := (R.A.chart j).left_inv hj
    have hyW : y ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O := by
      refine ⟨hj, (memO _).2 ?_⟩
      rw [hsy]
      refine ⟨(R.A.chart j).map_source hj, ⟨hyU, hyU'⟩, hi, fun k => ?_⟩
      rw [div_self (hry k)]
      exact Complex.one_mem_slitPlane
    have condW : ∀ z ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, z ∈ R.U x ∧ z ∈ R.U x' ∧
        (∀ k, R.lift x' z ⟨k, i k⟩ ≠ 0) ∧ ∀ k, r k z / r k y ∈ Complex.slitPlane := by
      intro z hz
      have h2 := (memO ((R.A.chart j) z)).1 hz.2
      rw [(R.A.chart j).left_inv hz.1] at h2
      exact ⟨h2.2.1.1, h2.2.1.2, h2.2.2.1, h2.2.2.2⟩
    refine ⟨(R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, hWopen, hyW,
      fun z => (∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ), ?_, ?_⟩
    · intro j' t ht
      obtain ⟨hUx, hUx', hne, hsl⟩ := condW _ ht.2
      have hra : ∀ k, AnalyticAt ℂ (fun s => r k ((R.A.chart j').symm s)) t := by
        intro k
        simp only [hr]
        exact (hol x _ j' t ht.1 hUx).div (hol x' _ j' t ht.1 hUx') (hne k)
      show AnalyticAt ℂ (fun s => (∑ k, ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)) t
      refine AnalyticAt.add ?_ analyticAt_const
      have hs : ∀ k ∈ (Finset.univ : Finset κ), AnalyticAt ℂ (fun s => ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) t :=
        fun k _ => analyticAt_const.mul (((hra k).div analyticAt_const (hry k)).clog (hsl k))
      have h3 := Finset.analyticAt_sum Finset.univ hs
      rw [Finset.sum_fn] at h3
      exact h3
    · intro z hz
      obtain ⟨hUx, hUx', hne, -⟩ := condW z hz.1.1
      obtain ⟨cz, hcz, hlz⟩ := R.compat x x' z ⟨hUx, hUx'⟩
      have hrz : ∀ k, r k z = cz k := by
        intro k
        rw [hr]
        have h1 := congrFun hlz ⟨k, i k⟩
        rw [h1]
        exact mul_div_cancel_right₀ _ (hne k)
      have hhz : A.h (R.lift x z) = (∏ k, ‖cz k‖ ^ A.a k) * A.h (R.lift x' z) := by
        rw [hlz]; exact A.smul cz _ hcz
      have hhpos : 0 < A.h (R.lift x' z) := A.pos _ (memNZ x' z hUx')
      have hczn : ∀ k, ‖cz k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hcz k)
      have hryn : ∀ k, ‖r k y‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hry k)
      have lhs : (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
          ∑ k, (A.a k : ℝ) * Real.log ‖cz k‖ := by
        rw [hhz, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hczn k))
          hhpos.ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hczn k))]
        simp only [Real.log_zpow]
        ring
      show (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
        ((∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
          ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)).re
      rw [lhs]
      simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re,
        Complex.log_re, norm_div, hrz]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.log_div (hczn k) (hryn k)]
      ring

theorem isPotential_secPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (potA M τ a k₀) := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA
    exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _
  exact isPotential_secPot_of_isSmoothHerm RW (potA M τ a k₀) hS V _ _ (fun x => (hL x).2.2.2.2.1) c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem locSec_norm_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr x x' ψ ψ' kb kb' σ σ' i₀ i₀' V V' u u' _ _ hs hs' w hw
  obtain ⟨⟨F, H, hc⟩, -, -, hVs, hVU, -, hu, hd, hn⟩ := hs
  obtain ⟨-, -, -, -, hVU', -, hu', hd', hn'⟩ := hs'
  by_cases h0 : ψ w i₀ = 0
  · have h0' : ψ' w i₀' = 0 := (hd' w hw.2).2 ((hd w hw.1).1 h0)
    simp [h0, h0']
  have h0' : ψ' w i₀' ≠ 0 := fun h => h0 ((hd w hw.1).2 ((hd' w hw.2).1 h))
  obtain ⟨-, hF, -, -, -, hp⟩ := hc
  obtain ⟨hH, hG, z₀, z₁, hz₀, hz₁, hex⟩ := hp w (hVs hw.1)
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    obtain ⟨c, hc0, hzc⟩ := hz₀
    have e₀ : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k =>
        (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk (fstPt k₀ (RW.lift w w)) q := by
      rw [hzc]; rfl
    rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
      (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk (fstPt k₀ (RW.lift w w)))]
    exact hG
  have hD : IsPtData M τ a k₀ ca cb RW w z₀ z₁ F (H τ (ψ w)) (ψ w i₀) :=
    ⟨hF, hG', hz₀, hz₁, (hH τ).1, (hH τ).2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  have e₁ := hn w hw.1 h0 z₀ z₁ F _ _ hD
  have e₂ := hn' w hw.2 h0' z₀ z₁ F _ _ hD
  have hA : 0 < (potA M τ a k₀).h (RW.lift x w) := (potA M τ a k₀).pos _ (RW.mem x w (hVU hw.1)).1
  have hA' : 0 < (potA M τ a k₀).h (RW.lift x' w) := (potA M τ a k₀).pos _ (RW.mem x' w (hVU' hw.2)).1
  have hN : 0 < ‖u w * ψ w i₀‖ := norm_pos_iff.2 (mul_ne_zero (hu w hw.1) h0)
  have hN' : 0 < ‖u' w * ψ' w i₀'‖ := norm_pos_iff.2 (mul_ne_zero (hu' w hw.2) h0')
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hN hA)) (Set.mem_Ioi.2 (div_pos hN' hA')) ?_
  rw [Real.log_div hN.ne' hA.ne', Real.log_div hN'.ne' hA'.ne', e₁, e₂]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMatStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.yv_eq_sum_minors_gMat :
    ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ)
      (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀]
      (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω),
    ∀ r k, blkF (Ψ := Ψ) (p := p) (q := q) K₀ r = some k → ∀ i : idx J₀ n k,
      yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) *
        minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  intro Ψ _ p q Ω _ n A K₀ _ J₀ _ x₀ r k hk i
  unfold blkF at hk
  split_ifs at hk
  obtain rfl := Option.some.inj hk
  exact BlockEmbeddings.det_fMat_eq A r.1 (stepOf Ψ p q r)
    (BlockEmbeddings.stepOf_fst r) _ (BlockEmbeddings.mem_stepCols_iff r) i
end

