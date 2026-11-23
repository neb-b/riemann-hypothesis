module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0078
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem continuousWithinAt_valAt {x : (Σ k, ι k) → Ω} {b₀ : (Σ k, ι k) → ℂ} (hb : b₀ ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal b₀) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) b₀ := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hx := ValRing.aeval_ne_zero_of_notMem hb hh hn
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hne : ∀ᶠ b in 𝓝 b₀, eval b (map (Int.castRingHom ℂ) h) ≠ 0 := ch.continuousAt.eventually_ne h0
  have key : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] b₀]
      fun b => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hne] with b hbm hbn
    exact valAt_eq hbm ⟨d, g, h, hg, hh, hx, heq, hbn, rfl⟩
  have hq : ContinuousWithinAt
      (fun b : (Σ k, ι k) → ℂ => eval b (map (Int.castRingHom ℂ) g) / eval b (map (Int.castRingHom ℂ) h))
      (mcPts (mCoordIdeal x)) b₀ := (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt
  exact hq.congr_of_eventuallyEq key (key.self_of_nhdsWithin hb)

end Values

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem continuousWithinAt_twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {A : Set Z} {z₀ : Z} {bs : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {pt : Z → (Σ k, ι k) → ℂ}
    (hbs : Continuous bs) (hpt : Continuous pt) (hA : Set.MapsTo bs A (mcPts (mCoordIdeal M.x))) (hz₀ : z₀ ∈ A)
    (hG : M.GoodAt F (mCoordIdeal (bs z₀))) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    (J : Finset (Fin N)) : ContinuousWithinAt (fun z => twMinor M F (bs z) i k g (pt z) J) A z₀ := by
  unfold twMinor pluck
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact (continuousWithinAt_valAt (hA hz₀) (hG.2.1 _ _).2).comp hbs.continuousWithinAt hA
  · exact ((continuous_apply _).comp hpt).continuousWithinAt

theorem isBlockMap_v₀ (k₀ : K) : IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ e
    simp only [v₀] at e
    obtain ⟨e1, e2⟩ := Sigma.mk.inj_iff.1 e
    obtain rfl := Option.some_injective _ e1
    rw [eq_of_heq e2]
  · rintro ⟨_, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

theorem continuous_fstPt (k₀ : K) : Continuous (fstPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₀ k₀ p)

theorem continuous_sndPt (k₀ : K) : Continuous (sndPt (ι := ι) k₀) :=
  continuous_pi fun p => continuous_apply (v₁ k₀ p)

theorem continuous_baseOf (M : FlagModel y Ψ N j) (k₀ : K) : Continuous (baseOf M k₀) :=
  continuous_pi fun q => continuous_apply (v₀ k₀ ⟨q.1.1, q.2⟩)

theorem fstPt_mem (M : FlagModel y Ψ N j) {d : ℕ} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}
    (hb : (b : ℕ) = a + 1) (hba : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hk : M.blk (τ, a) = some k₀)
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hV : IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    fstPt k₀ z ∈ mcPts (mCoordIdeal y) := by
  have hI := (_root_.PositivityTheory.Xgp.t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk hca hcb hV).2.2.2.1
  exact GlobalTheory.CompanionTheory.Ar.Chg.mem_mcPts_restr (isBlockMap_v₀ k₀) hI.ge hz

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∃ O' : Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen O' ∧ wO M Rb τ a k₀ ca cb F kb V r h = O' ∩ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hc
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, -, hBC, hr, hrc, -⟩ := hc
  have hmaps : Set.MapsTo (baseOf M k₀) (mcPts (wP M τ a k₀ ca cb)) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    CPts.base_mem M (fstPt_mem M hb hba hk₀ hca hcb hAV hz)
  have key : ∀ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h,
      wO M Rb τ a k₀ ca cb F kb V r h ∈ 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀ := by
    rintro z₀ ⟨hz₀, hsrc, hV₀, hm₁, hm₂⟩
    have hbm := hmaps hz₀
    have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z₀)) := by
      obtain ⟨-, -, hgood, horb⟩ := hBC.2.2.2.2 _ hV₀
      rw [(Rb.A.chart kb).left_inv hsrc] at horb
      rwa [CovMap.mCoordIdeal_eq_of_sameOrbit (orbit_trans (orbit_symm (hr _ hbm)) horb)]
    have hrb : ContinuousWithinAt (fun z => r (baseOf M k₀ z)) (mcPts (wP M τ a k₀ ca cb)) z₀ :=
      (hrc _ hbm).comp (continuous_baseOf M k₀).continuousWithinAt hmaps
    have e₁ := hrb.tendsto.eventually_mem ((Rb.A.chart kb).open_source.mem_nhds hsrc)
    have e₂ := (((Rb.A.chart kb).continuousAt hsrc).tendsto.comp hrb.tendsto).eventually_mem (hBC.1.mem_nhds hV₀)
    have tw := fun (pt : _ → (Σ k, ι k) → ℂ) (hpt : Continuous pt) =>
      continuousWithinAt_twMinor M F (continuous_baseOf M k₀) hpt hmaps hz₀ hG
    have e₃ : ∀ᶠ z in 𝓝[mcPts (wP M τ a k₀ ca cb)] z₀, ∀ p k, M.blk p = some k →
        twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := by
      refine eventually_all.2 fun p => eventually_all.2 fun k => ?_
      by_cases hp : M.blk p = some k
      · exact ((tw _ (continuous_fstPt k₀) p.2 k (h p.1)⁻¹ (stepCols N j p.2)).tendsto.eventually_ne
          (hm₁ p k hp)).mono fun _ hz _ => hz
      · exact Eventually.of_forall fun _ hp' => absurd hp' hp
    have e₄ := (tw _ (continuous_sndPt k₀) a k₀ (h τ)⁻¹ (stepCols N j a)).tendsto.eventually_ne hm₂
    filter_upwards [self_mem_nhdsWithin, e₁, e₂, e₃, e₄] with z h₀ h₁ h₂ h₃ h₄
    exact ⟨h₀, h₁, h₂, h₃, h₄⟩
  choose! U hU hmem hsub using fun z₀ (hz : z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h) =>
    mem_nhdsWithin.1 (key z₀ hz)
  refine ⟨⋃ z₀ ∈ wO M Rb τ a k₀ ca cb F kb V r h, U z₀, isOpen_biUnion hU, Set.Subset.antisymm ?_ ?_⟩
  · intro z hz
    exact ⟨Set.mem_biUnion hz (hmem z hz), hz.1⟩
  · rintro z ⟨hz, hzA⟩
    obtain ⟨z₀, h₀, hz₀⟩ := Set.mem_iUnion₂.1 hz
    exact hsub z₀ h₀ ⟨hz₀, hzA⟩

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Opn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentRowsAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr

theorem holoMap_comp' {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X}
    {g : Z → Y} {f : Y → X} (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm)
      ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

theorem injective_of_degree_one {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hd : IsDegreeOff A B π 1 ∅) :
    Function.Injective π := by
  intro u w huw
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 (π u) (Set.notMem_empty _))
  have hu : u ∈ π ⁻¹' {π u} := rfl
  have hw : w ∈ π ⁻¹' {π u} := huw.symm
  rw [hc] at hu hw
  exact hu.trans hw.symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_holo_of_centre {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k, ι' k)) {P : Ideal (MRing ι)} {J : Ideal (MRing ι)}
    {P' J' : Ideal (MRing ι')} {D D' : ℕ} (hJ : J = ⊤) (R : AnLogRes P J D)
    (R' : AnLogRes P' J' D') (hb : IsBlockMap κ v) (hP : P ≤ imageZ v P') :
    ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x ∘ v) := by
  subst hJ
  exact Proj.holoMap_of_blockProj K ι K' ι' κ v P P' J' D D' R R' hb hP

theorem isBlockMap_v₀ (k₀ : K) :
    IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
    subst h1
    have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
    rw [h2]
  · rintro ⟨o, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

def κ₁ (k₀ k : K) : Option K := if k = k₀ then none else some k

theorem isBlockMap_v₁ (k₀ : K) : IsBlockMap (κ₁ k₀) (v₁ (ι := ι) k₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u w h
    by_cases hu : u = k₀ <;> by_cases hw : w = k₀ <;> simp_all [κ₁]
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    by_cases hk : k = k₀
    · subst hk
      by_cases hk' : k' = k
      · subst hk'
        rw [v₁_self, v₁_self] at h
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
      · rw [v₁_self, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
    · by_cases hk' : k' = k₀
      · subst hk'
        rw [v₁_self, v₁_ne (p := ⟨k, m⟩) hk] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
      · rw [v₁_ne (p := ⟨k, m⟩) hk, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
        subst h1
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
  · rintro ⟨k, m⟩
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      simp [κ₁]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      simp [κ₁, hk]
  · rintro ⟨o, m⟩ ⟨k, hk⟩
    by_cases e : k = k₀
    · subst e
      have ho : o = none := by
        have hk' : κ₁ k k = o := hk
        rw [← hk']; simp [κ₁]
      subst ho
      exact ⟨⟨k, m⟩, v₁_self k m⟩
    · have ho : o = some k := by
        have hk' : κ₁ k₀ k = o := hk
        rw [← hk']; simp [κ₁, e]
      subst ho
      exact ⟨⟨k, m⟩, v₁_ne (p := ⟨k, m⟩) e⟩

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc _, rfl⟩

theorem basePart_snd {σ : Type} {blk : σ → Option K} {k₀ : K} {s : σ} (hs : blk s = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext ⟨k, m⟩
  have hk : k.1 ≠ k₀ := fun e => k.2 s (by rw [hs, e])
  change z (v₁ k₀ ⟨k.1, m⟩) = z (v₀ k₀ ⟨k.1, m⟩)
  rw [v₁_ne (p := ⟨k.1, m⟩) hk]
  rfl

theorem orbit_of_two {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : SameOrbit (fstPt k₀ z) (fstPt k₀ z')) (h₁ : SameOrbit (sndPt k₀ z) (sndPt k₀ z')) :
    SameOrbit z z' := by
  obtain ⟨c₀, hc₀, e₀⟩ := h₀
  obtain ⟨c₁, hc₁, e₁⟩ := h₁
  refine ⟨fun o => o.elim (c₁ k₀) c₀, ?_, ?_⟩
  · rintro (_ | k)
    · exact hc₁ k₀
    · exact hc₀ k
  · funext ⟨o, m⟩
    cases o with
    | none =>
      have := congrFun e₁ ⟨k₀, m⟩
      simpa [sndPt, v₁_self] using this
    | some k =>
      have := congrFun e₀ ⟨k, m⟩
      simpa [fstPt, v₀] using this

theorem two_projections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk ha hcb hy RW pr hpr hbase
  obtain ⟨-, -, -, hi₀, hi₁⟩ := _root_.PositivityTheory.Xgp.t_c_w_arith K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk ha hcb hy
  have hi₁' := hi₁ (v₁ k₀) (fun p hp => v₁_ne hp) (fun m => v₁_self k₀ m)
  obtain ⟨h₀, hh₀, ho₀⟩ := exists_holo_of_centre some (v₀ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₀ k₀) hi₀.ge
  obtain ⟨h₁, hh₁, ho₁⟩ := exists_holo_of_centre (κ₁ k₀) (v₁ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₁ k₀) hi₁'.ge
  have hdeg := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hdeg
  have hπ : Function.Injective FA.Re.π := injective_of_degree_one hdeg
  have hpr' : ∀ (x₁ : FA.Re.R.X) (w : RW.X) (zz : (Σ k, ι k) → ℂ),
      SameOrbit (FA.Re.R.lift x₁ x₁) zz →
      basePart M.blk zz = basePart M.blk (fstPt k₀ (RW.lift w w)) → FA.pr (FA.Re.π x₁) = pr w := by
    intro x₁ w zz h1 h2
    refine BM.Rb.inj _ _ (Proj.not_mem_mcPts_top _) ?_
    have h3 := basePart_orbit M.blk h1
    rw [h2] at h3
    exact orbit_trans (orbit_symm (FA.pr_eq x₁)) (orbit_trans h3 (orbit_symm (hbase w)))
  have hb₀ : ∀ w, FA.pr (FA.Re.π (h₀ w)) = pr w := fun w => hpr' _ w _ (ho₀ w) rfl
  have hb₁ : ∀ w, FA.pr (FA.Re.π (h₁ w)) = pr w := fun w =>
    hpr' _ w _ (ho₁ w) (basePart_snd hk (RW.lift w w))
  refine ⟨![FA.Re.π ∘ h₀, FA.Re.π ∘ h₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c₀ := holoMap_comp' hh₀ FA.Re.holo
    have c₁ := holoMap_comp' hh₁ FA.Re.holo
    exact Fin.forall_fin_two.2 ⟨c₀, c₁⟩
  · exact Fin.forall_fin_two.2 ⟨funext hb₀, funext hb₁⟩
  · intro x x₀ e
    have : x₀ = h₀ x := hπ e
    subst this
    exact ho₀ x
  · intro x x₀ e
    have : x₀ = h₁ x := hπ e
    subst this
    exact ho₁ x
  · intro w w' e
    have e₀ : FA.Re.π (h₀ w) = FA.Re.π (h₀ w') := congrArg Prod.fst e
    have e₁ : FA.Re.π (h₁ w) = FA.Re.π (h₁ w') := congrArg Prod.snd e
    have f₀ := hπ e₀
    have f₁ := hπ e₁
    have g₀ : SameOrbit (fstPt k₀ (RW.lift w w)) (fstPt k₀ (RW.lift w' w')) := by
      have := ho₀ w'
      rw [← f₀] at this
      exact orbit_trans (orbit_symm (ho₀ w)) this
    have g₁ : SameOrbit (sndPt k₀ (RW.lift w w)) (sndPt k₀ (RW.lift w' w')) := by
      have := ho₁ w'
      rw [← f₁] at this
      exact orbit_trans (orbit_symm (ho₁ w)) this
    exact RW.inj w w' (Proj.not_mem_mcPts_top _) (orbit_of_two g₀ g₁)
  · intro p hp
    have key : ∀ w, FA.S.ph (some p) (FA.Re.π (h₀ w)) = FA.S.ph (some p) (FA.Re.π (h₁ w)) ∧
        ∀ t, FA.S.phT (some p) t (FA.Re.π (h₀ w)) = FA.S.phT (some p) t (FA.Re.π (h₁ w)) := by
      intro w
      refine FA.step_ph p (h₀ w) (h₁ w) ((hb₀ w).trans (hb₁ w).symm) ?_
      intro k hkp
      have hne : k ≠ k₀ := fun e => hp (M.blk_inj p (τ, a) k₀ (e ▸ hkp) hk)
      obtain ⟨c₀, -, e₀⟩ := ho₀ w
      obtain ⟨c₁, hc₁, e₁⟩ := ho₁ w
      refine ⟨c₀ k / c₁ k, fun m => ?_⟩
      have a₀ := congrFun e₀ ⟨k, m⟩
      have a₁ := congrFun e₁ ⟨k, m⟩
      simp only [Function.comp] at a₀ a₁
      rw [v₁_ne (p := ⟨k, m⟩) hne] at a₁
      rw [a₀, a₁]
      have := hc₁ k
      simp only [v₀]
      field_simp
    exact ⟨funext fun w => (key w).1, fun t => funext fun w => (key w).2 t⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem base_orbit {σ : Type} {blk : σ → Option K} {z₁ z : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (basePart blk z₁) (basePart blk z) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem comp_orbit {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {κ : K → K'}
    {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {b₁ b : (Σ k, ι' k) → ℂ} (h : SameOrbit b₁ b) :
    SameOrbit (b₁ ∘ v) (b ∘ v) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => c (κ k), fun k => hc _, ?_⟩
  funext q
  simp only [Function.comp]
  rw [hv.2.2.1 q]

theorem ideal_orbit {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b) : mCoordIdeal b₁ = mCoordIdeal b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact StepW.TorusAct.mCoordIdeal_torus c hc b

theorem valAt_orbit {x : (Σ k, ι k) → Ω} {b₁ b : (Σ k, ι k) → ℂ} (h : SameOrbit b₁ b)
    (hb : b ∈ mcPts (mCoordIdeal x)) (s : Ω) : valAt x s b₁ = valAt x s b := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ((StepW.TorusAct.main K ι Ω x b c hc).2 hb).2 s

end Orbit

theorem img_spec (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ)
    (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K']
    (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j)
    (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F₀' : FrameData ι' Ψ N M'.Ω M'.blk)
    (F₀ : FrameData ι Ψ N M.Ω M.blk) (hz : z ∈ mcPts (mCoordIdeal y')) (hF' : M'.IsFrame F₀') (hF : M.IsFrame F₀)
    (hg' : M'.GoodAt F₀' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F₀ (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) :
    img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) ∧ IsImg Cv z (img Cv F₀' F₀ z) := by
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt.main K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨h₀, hh₀, hz₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.exists_flags_good K' ι' Φ' y' Ψ N j M' F₀' z hz hF' hg'
  have hT₀ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.trans_blockDiag_det K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F₀' F₀ hb hF' hF hg' hg
  have hH₀ : ∀ τ, IsBlockDiag j (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ) ∧
      (Cv.trans F₀' F₀ (basePart M'.blk z) τ * h₀ τ).det ≠ 0 := fun τ =>
    ⟨(hT₀ τ).1.mul (hh₀ τ).1, by rw [det_mul]; exact mul_ne_zero (hT₀ τ).2 (hh₀ τ).2⟩
  have hform := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.img_form K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F₀' F₀ h₀ hb hF' hF hg' hg
    (fun τ => (hh₀ τ).1) hz₀
  have hwb : basePart M.blk (img Cv F₀' F₀ z) = basePart M'.blk z ∘ Cv.v := img_base Cv F₀' F₀ z
  have hw : img Cv F₀' F₀ z ∈ mcPts (mCoordIdeal y) :=
    (GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F₀ (img Cv F₀' F₀ z) _ hF (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg) hH₀
      (by rw [hwb]; exact hform)).1
  refine ⟨hw, ?_⟩
  intro z₁ h1 F' F hF1' hF1 hg1' hg1 h hfl
  have hbo : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z) := base_orbit h1
  have hbov := comp_orbit Cv.block hbo
  rw [ideal_orbit hbo] at hg1'
  rw [ideal_orbit hbov] at hg1
  have htrans : ∀ τ, Cv.trans F' F (basePart M'.blk z₁) τ = Cv.trans F' F (basePart M'.blk z) τ := fun τ => by
    ext a c
    exact valAt_orbit hbo hb _
  obtain ⟨-, hhinv, hflag⟩ := hfl
  have hpl : ∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k',
      plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) =
        a * plk M' F₀' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h₀ p.1) := fun p k' hp => by
    obtain ⟨a, ha, e⟩ := hflag p k' hp
    obtain ⟨a₀, ha₀, e₀⟩ := hz₀ p k' hp
    obtain ⟨c, hc, rfl⟩ := h1
    refine ⟨a⁻¹ * c k' * a₀, mul_ne_zero (mul_ne_zero (inv_ne_zero ha) (hc k')) ha₀, fun m' => ?_⟩
    have e1 := e m'
    have e2 := e₀ m'
    have e3 : ∑ I, valAt M'.x (F'.u ⟨k', m'⟩ I) (basePart M'.blk fun p => c p.1 * z p) *
        minorIJ (h p.1) I (stepCols N j p.2) = plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1) :=
      Finset.sum_congr rfl fun I _ => by rw [valAt_orbit hbo hb]
    rw [e3] at e1
    simp only at e1
    rw [e2] at e1
    field_simp
    linear_combination -e1
  have hind := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Ind.plk_moved_indep K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F₀' F F₀ h h₀ hb hF1' hF' hF1 hF hg1' hg' hg1 hg
    (fun τ => (hhinv τ).1) (fun τ => (hh₀ τ).1) hpl
  have hT := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.trans_blockDiag_det K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hb hF1' hF1 hg1' hg1
  obtain ⟨-, z₀, o1, o2, fl⟩ := GlobalTheory.T.block_diag_frame_at_good_point K ι Φ y Ψ N j M F (img Cv F₀' F₀ z)
    (fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ) hF1 (by rw [hwb]; exact hbv) (by rw [hwb]; exact hg1)
    (fun τ => ⟨(hT τ).1.mul (hhinv τ).1, by rw [det_mul]; exact mul_ne_zero (hT τ).2 (hhinv τ).2⟩)
    (fun p k hp => by
      obtain ⟨a₁, ha₁, e₁⟩ := hform p k hp
      obtain ⟨a₂, ha₂, e₂⟩ := hind p k hp
      refine ⟨a₁ * a₂⁻¹, mul_ne_zero ha₁ (inv_ne_zero ha₂), fun m => ?_⟩
      rw [e₁ m, hwb, e₂ m]
      field_simp)
  refine ⟨z₀, o1, Cj.sameOrbit_trans (hwb ▸ o2) (Cj.sameOrbit_symm hbov), ?_⟩
  simp only [htrans]
  exact fl

theorem local_img : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), f z' ∈ mcPts (mCoordIdeal y) ∧ CovMap.IsImg Cv z' (f z') := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _ z hz
  have hb : basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').1 z hz
  have hbv := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt.main K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K ι Φ y Ψ N j M).2.1 _ hbv
  obtain ⟨V, f, hV, hzV, hf, hs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An.main K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z F' F hz hF' hF hg' hg
  refine ⟨V, f, hV, hzV, hf, fun z' hz' => ?_⟩
  obtain ⟨g1, g2, e⟩ := hs z' hz'
  rw [e]
  exact img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv z' F' F hz'.2 hF' hF g1 g2

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerInAffineChartStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symbolic_power_in_affine_chart : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ) (n : ℕ) (s' : MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), IsMultiHomogIdeal P → IsMultiHomogIdeal Q → Q.IsPrime → (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) → IsMultiHomog f a → s' ∉ SncRes.ideal Q p → s' * bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ^ n ⊔ SncRes.ideal P p → ∃ s ∉ Q, s * f ∈ Q ^ n ⊔ P := by
  exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises
end

