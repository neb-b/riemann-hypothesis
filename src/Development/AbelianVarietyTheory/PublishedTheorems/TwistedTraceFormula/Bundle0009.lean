module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAuxiliaryPlaceNotMemFinset
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.Published

def AdmissibleCoefficientsAnalytic : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε π →
    ∀ v w : H, IsKFin ε π v → IsKFin ε π w → AnalyticOnUJ ε fun g => ⟪w, π g v⟫_ℂ

def LeviSubmoduleDense : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Flag n a), IsIsoFlag ε j W → (∀ i, 1 ≤ j i) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsURepOn (mats (leviOne ε W)) σ → IsIrredOn (mats (leviOne ε W)) σ →
      ∀ S : Submodule ℂ V, S ≠ ⊥ → (∀ v ∈ S, IsKFinIn (leviOne ε W) σ v) →
        (∀ X : Matrix (Fin n) (Fin n) ℂ, (∀ t : ℝ, NormedSpace.exp (t • X) ∈ mats (leviOne ε W)) →
          ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) v) v' 0) →
        Dense (S : Set V)

def HarishChandraAnalyticity : Prop := AdmissibleCoefficientsAnalytic ∧ LeviSubmoduleDense

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace
open scoped ENNReal NNReal Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

def CuspDecaySobolev : Prop :=
  ∀ (D : D7) (θ : InfFam D), IsInfFam θ →
    ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ N M : ℕ,
      ∃ (d : ℕ) (C : ℝ≥0), ∀ φ : GA D V → ℂ, IsAutFun V φ → (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) →
        φ ∈ SmFun θ V → (∀ k, growthSob θ V k N φ ≠ ∞) → IsCuspFun V φ →
          decaySize V M φ ≤ C * growthSob θ V d N φ

end GlobalTheory.Published

namespace GlobalTheory.Size

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ}

theorem integrableOn_inv_quotHeight_pow (A : ℕ) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) : IntegrableOn (fun g => (quotHeight V g ^ A)⁻¹) 𝓕 μ := by
  refine Measure.integrableOn_of_bounded (M := 1)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V μ 𝓕 hμ h𝓕).ne
    (((continuous_quotHeight V).pow A).inv₀ fun g => (pow_pos (quotHeight_pos V g) A).ne').aestronglyMeasurable
    (.of_forall fun g => ?_)
  rw [Real.norm_of_nonneg (inv_pos.2 (pow_pos (quotHeight_pos V g) A)).le]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (one_le_quotHeight V g))

theorem exists_finset_doubleCosets (V : HSp D) (U : Subgroup (GA D V)) (hU : IsOpen (U : Set (GA D V))) :
    ∃ S : Finset (GA D V), (∀ x ∈ S, x ∈ GfC V) ∧
      ∀ g, ∃ γ ∈ GQ V, ∃ x ∈ S, ∃ a ∈ GinfC V, ∃ k ∈ U, k ∈ GfC V ∧ g = γ * x * a * k := by
  classical
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  have R := (_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
  obtain ⟨S, _, _, hS⟩ := GlobalTheory.SmoothForms.reduction hθ R U hU
  choose p hp q hq e using R.2.2.2.2.2.2.1
  refine ⟨S.image p, fun x hx => ?_, fun g => ?_⟩
  · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hp y
  · obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', h, -⟩ := hS g
    refine ⟨γ⁻¹, inv_mem hγ, p x, Finset.mem_image_of_mem p hx, q x * a, mul_mem (hq x) ha, k, hk, hk', ?_⟩
    rw [mul_assoc γ⁻¹, mul_assoc γ⁻¹, ← mul_assoc (p x), ← e x, ← h, inv_mul_cancel_left]

theorem growthSize_sum_le {T : (GA D V → ℂ) → GA D V → ℂ} (hT : LinOnSm θ V T) {ι : Type} (s : Finset ι) (c : ι → ℂ)
    {f : ι → GA D V → ℂ} (hf : ∀ a, f a ∈ SmFun θ V) (N : ℕ) :
    growthSize V N (T (∑ a ∈ s, c a • f a)) ≤ ∑ a ∈ s, ‖c a‖ₑ * growthSize V N (T (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hT.smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [Finset.sum_empty, Finset.sum_empty, this]
    exact ((growthSize_const (0 : ℂ)).trans eNorm_zero).le
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hT.add _ (Submodule.smul_mem _ _ (hf a)) _
      (sum_mem fun b _ => Submodule.smul_mem _ _ (hf b)), hT.smul, ← growthSize_smul]
    exact growthSize_add_le.trans (add_le_add le_rfl ih)

theorem exists_growthSize_rWord_le (hθ : IsInfFam θ)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∃ c : ℝ≥0, ∀ φ ∈ SmFun θ V, ∀ (N d : ℕ) (l' : List (D.what₂.Tau × Fin V.rank × Fin V.rank)),
      l'.length + l.length ≤ d →
        growthSize V N (wordAct (glDer θ V) l' (rWord θ V l φ)) ≤ c * growthSob θ V d N φ := by
  induction l with
  | nil => exact ⟨1, fun φ _ N d l' hd => by
      rw [ENNReal.coe_one, one_mul]
      exact le_wordSum (p := growthSize V N) (l := l') hd φ⟩
  | cons p l ih =>
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    obtain ⟨c, hc⟩ := ih hl'
    refine ⟨(∑ a : Fin V.rank × Fin V.rank, ‖p.2 a.1 a.2‖₊) * c, fun φ hs N d l' hd => ?_⟩
    have hm := (linOnSm_rWord hl').mem φ hs
    have e : rWord θ V (p :: l) φ = Rder θ V p.1 p.2 (rWord θ V l φ) := rfl
    rw [e, Rder_eq_sum_glDer hθ hm (hl p List.mem_cons_self)]
    refine (growthSize_sum_le (linOnSm_glWord l') _ _ (fun a => (linOnSm_RderC p.1 _).mem _ hm) N).trans ?_
    push_cast
    rw [mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl ?_
    have := hc φ hs N d (l' ++ [(p.1, a)])
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hd ⊢; omega)
    rwa [wordAct_append] at this

theorem cuspDecaySobolev_of_bound (hP : GlobalTheory.Published.CuspDecayBound) : GlobalTheory.Published.CuspDecaySobolev := by
  intro D θ hθ V U hU N M
  obtain ⟨L, C, hL, h⟩ := hP D θ hθ V U hU N M
  choose! c hc using fun l hl => exists_growthSize_rWord_le (V := V) hθ l hl
  refine ⟨L.sup List.length, C.toNNReal * ∑ l ∈ L, c l, fun φ ha hk hs hg hcu => ?_⟩
  lift growthSob θ V (L.sup List.length) N φ to ℝ≥0 using hg _ with s hs'
  have h1 := h φ ha hk hs (fun l hl => modGrowthExp_iff.2 (growthSize_rWord_ne_top hθ hs hg l hl)) hcu
    (fun l => (c l * s : ℝ≥0)) fun l hl => (growthSize_le_iff (NNReal.coe_nonneg _)).1 (by
      rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, hs']
      exact hc l (hL l hl) φ hs N _ [] (by simpa using Finset.le_sup (f := List.length) hl))
  rw [← ENNReal.coe_mul, ← ENNReal.ofReal_coe_nnreal]
  refine (decaySize_le_iff (NNReal.coe_nonneg _)).2 fun g => (h1 g).trans ?_
  rw [← NNReal.coe_sum, ← Finset.sum_mul, mul_assoc, NNReal.coe_mul C.toNNReal]
  exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C) (NNReal.coe_nonneg _)

theorem rapidDec_of_cuspDecaySobolev (hP : GlobalTheory.Published.CuspDecaySobolev) (hθ : IsInfFam θ) (ha : IsAutFun V φ)
    (hs : φ ∈ SmFun θ V) (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDec V φ := by
  obtain ⟨U, hU, hk⟩ := ha.level
  obtain ⟨N, hN⟩ := exists_growthSob_ne_top hs hg
  refine rapidDec_iff_decaySize.2 ⟨ha.left, ha.cont, fun M => ?_⟩
  obtain ⟨d, C, h⟩ := hP D θ hθ V U hU N M
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (hN d)) (h φ ha hk hs hN hc)

theorem continuous_Rder_of_growth (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (hc : Continuous φ) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) {A : ℕ}
    (hg : ModGrowthExp V A (Rder θ V τ X (Rder θ V τ X φ))) : Continuous (Rder θ V τ X φ) := by
  obtain ⟨B, hB⟩ := hg
  have hB0 := nonneg_of_growth hB
  obtain ⟨c, hc'⟩ := exists_height_le_of_isCompact V
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).image (GlobalTheory.Mem.Lift.continuous_oneP hθ hX))
  have key : ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ g, ‖Rder θ V τ X φ g - h⁻¹ • (φ (g * oneP θ V τ X h) - φ g)‖ ≤
      B * (height V g * c) ^ A * h := fun h h0 h1 g => by
    set q := h⁻¹ • (φ (g * oneP θ V τ X h) - φ g) with hq
    have d1 := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX) g
    have d2 := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (GlobalTheory.Mem.Lift.hasDerivAt_Rder (Rder_mem hs hX) hX) g
    have := GlobalTheory.CuspDecay.mul_norm_deriv_le (f := fun t => φ (g * oneP θ V τ X t) - φ g - t • q)
      (f₁ := fun t => Rder θ V τ X φ (g * oneP θ V τ X t) - q)
      (fun t => by simpa using ((d1 t).sub_const (φ g)).fun_sub ((hasDerivAt_id t).smul_const q))
      (fun t => (d2 t).sub_const q) h0.le (B := B * (height V g * c) ^ A) fun t ht => (hB _).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ((height_mul_le V _ _).trans
          (mul_le_mul_of_nonneg_left (hc' _ ⟨t, ⟨ht.1, ht.2.trans h1⟩, rfl⟩) (height_pos V g).le)) A) hB0)
    rw [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one, hq, smul_inv_smul₀ h0.ne', sub_self, sub_self, zero_smul, sub_self,
      norm_zero, zero_add, zero_add, mul_comm _ h] at this
    exact le_of_mul_le_mul_left this h0
  refine continuous_of_locally_uniform_approx_of_continuousAt fun x u hu => ?_
  obtain ⟨ε, hε, hu⟩ := Metric.mem_uniformity_dist.1 hu
  have hb : Continuous fun g => B * (height V g * c) ^ A :=
    continuous_const.mul (((continuous_height V).mul continuous_const).pow A)
  obtain ⟨h, h0, h1, h2⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧ B * (height V x * c) ^ A * h < ε := by
    have : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h ≤ 1 ∧ B * (height V x * c) ^ A * h < ε :=
      eventually_mem_nhdsWithin.and (Filter.Eventually.filter_mono nhdsWithin_le_nhds
        ((eventually_le_nhds zero_lt_one).and
          ((continuous_const.mul continuous_id).continuousAt.eventually_lt continuousAt_const (by simpa using hε))))
    exact this.exists
  refine ⟨_, (isOpen_lt (hb.mul (continuous_const (y := h))) (continuous_const (y := ε))).mem_nhds h2,
    fun g => h⁻¹ • (φ (g * oneP θ V τ X h) - φ g),
    (((hc.comp (continuous_mul_const _)).sub hc).const_smul h⁻¹).continuousAt, fun y hy => hu ?_⟩
  rw [dist_eq_norm]
  exact (key h h0 h1 y).trans_lt hy

theorem continuous_rWord (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (hc : Continuous φ) (hg : UnifModGrowth V θ φ)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) : Continuous (rWord θ V l φ) := by
  obtain ⟨A, hA⟩ := hg
  induction l with
  | nil => exact hc
  | cons p l ih =>
    have hl' : IsLieWord V l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    exact continuous_Rder_of_growth hθ ((linOnSm_rWord hl').mem φ hs) (ih hl') (hl p List.mem_cons_self)
      (hA (p :: p :: l) fun q hq => (List.mem_cons.1 hq).elim (fun e => e ▸ hl p List.mem_cons_self) (hl q))

theorem rWord_left {γ : GA D V} (h : ∀ g, φ (γ * g) = φ g)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) : ∀ g, rWord θ V l φ (γ * g) = rWord θ V l φ g := by
  induction l with
  | nil => exact h
  | cons p l ih =>
    intro g
    change Rder θ V p.1 p.2 (rWord θ V l φ) _ = Rder θ V p.1 p.2 (rWord θ V l φ) _
    simp only [Rder, mul_assoc, ih]

theorem rapidDecSm_of_unifModGrowth (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (ha : IsAutFun V φ)
    (hs : φ ∈ SmFun θ V) (hg : UnifModGrowth V θ φ) (hc : IsCuspFun V φ) : RapidDecSm θ V φ :=
  ⟨ha, hs, fun l hl => (rapidDec_iff_isRapidDecay hθ).2 ⟨fun γ hγ => rWord_left (ha.left γ hγ) l,
    continuous_rWord hθ hs ha.cont hg hl,
    GlobalTheory.CuspDecay.isRapidDecay_foldr_Rder hP hθ ha hs (hg.growth hθ) hc l hl⟩⟩

theorem rapidDecSm_of_cuspForm (hP : GlobalTheory.Published.CuspRapidDecay) (hθ : IsInfFam θ) (h : IsAutFunSm θ V φ)
    (hc : IsCuspFun V φ) : RapidDecSm θ V φ :=
  rapidDecSm_of_unifModGrowth hP hθ h.toIsAutFun h.smooth (unifModGrowth_of_isAutFunSm hθ h) hc

end GlobalTheory.Size

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsGlobalCharDetPow
section
open MeasureTheory Set Filter Matrix Polynomial GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.HCChar
open Formalism.REAL (UJ KG muK Jm)
open Formalism.QuantumDeterminants (IsHCParam IsCRepOn)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsDS UJset)
open GlobalTheory.FlagMeas (IsIsoFlag flagM)
open scoped ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.HCChar.Model

end GlobalTheory.HCChar.Model
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LinearIndependentE
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.Chamber GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (perp extSub coordR act parab)
open scoped TensorProduct NNReal Classical

namespace GlobalTheory.TruncKer

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def subFlag {V : HSpace E} (𝔉 : IsoFlag V) (J : Finset (Fin 𝔉.k)) : IsoFlag V where
  k := J.card
  X i := 𝔉.X (Fin.cases (motive := fun _ => Fin (𝔉.k + 1)) 0 (fun i => (J.orderEmbOfFin rfl i).succ) i)
  zero := 𝔉.zero
  strictMono := 𝔉.strictMono.comp fun a b h => by
    induction b using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ b =>
      induction a using Fin.cases with
      | zero => exact Fin.succ_pos _
      | succ a => exact Fin.succ_lt_succ_iff.2 ((J.orderEmbOfFin rfl).strictMono (Fin.succ_lt_succ_iff.1 h))
  iso := 𝔉.le_perp _ _

structure WittFrame (V : HSpace E) where

  e : Fin (wittIndex V) → V.V

  f : Fin (wittIndex V) → V.V
  ee : ∀ i j, V.hD (e i) (e j) = 0
  ff : ∀ i j, V.hD (f i) (f j) = 0
  ef : ∀ i j, V.hD (e i) (f j) = if i = j then 1 else 0

namespace WittFrame

variable {V : HSpace E} (Φ : WittFrame V)

theorem linearIndependent_e : LinearIndependent E Φ.e :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun j => V.hT (Φ.f j))
    (fun j i h => (Φ.ef i j).trans (if_neg h.symm)) fun i => (Φ.ef i i).trans (if_pos rfl)

def flag0 : IsoFlag V := .ofVectors Φ.e Φ.linearIndependent_e Φ.ee

def stdFlag (J : Finset (Fin (wittIndex V))) : IsoFlag V := subFlag Φ.flag0 J

def sub (u : SV (wittIndex V)) : Submodule E V.V := Submodule.span E (Φ.e '' {i | u i = 1} ∪ Φ.f '' {i | u i = -1})

variable (hc : CMData F E) (R : Type) [CommRing R] [Algebra F R]

def levi (P : Finset (SV (wittIndex V))) : Subgroup (HA R hc.sig V.gram) :=
  ⨅ u ∈ P, parab hc V R (Φ.sub u) ⊓ parab hc V R (Φ.sub (-u))

def coef (i : Fin (wittIndex V)) : (Fin V.rank → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hLin hc.sig V.gram R y (coordR V R (Φ.f i))
  map_add' y y' := hLin_add_left _ _ _ y y' _
  map_smul' c y := hLin_smul_left _ _ _ c y _

theorem coef_coordR (i : Fin (wittIndex V)) (x : V.V) : Φ.coef hc R i (coordR V R x) = inclR R (V.hD x (Φ.f i)) := by
  change hR R hc.sig V.gram _ _ = inclR R (V.hT _ _)
  rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.hT_coord]
  simp [hR, Formalism.UG.hform, coordR, JR, inclR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, CMData.sig, TensorProduct.tmul_sum, starRingEnd_apply]

theorem coef_eq_zero (i : Fin (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R (Φ.flag0.X i.castSucc)) : Φ.coef hc R i y = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (Φ.coef hc R i))).2 ?_ hy
  rintro _ ⟨x, hx, rfl⟩
  have : V.hT (Φ.f i) x = 0 := (Submodule.span_le (p := LinearMap.ker (V.hT (Φ.f i)))).2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (Φ.ef j i).trans (if_neg (Fin.ne_of_val_ne (ne_of_lt hj)))) hx
  exact (Φ.coef_coordR hc R i x).trans (by rw [HSpace.hD, this, map_zero])

theorem sub_coef_mem (i : Fin (wittIndex V)) {y : Fin V.rank → R ⊗[F] E}
    (hy : y ∈ extSub (F := F) V R (Φ.flag0.X i.succ)) :
    y - Φ.coef hc R i y • coordR V R (Φ.e i) ∈ extSub (F := F) V R (Φ.flag0.X i.castSucc) := by
  have h1 : ∀ x ∈ Φ.flag0.X i.succ, x - V.hT (Φ.f i) x • Φ.e i ∈ Φ.flag0.X i.castSucc := fun x hx => by
    have := (Submodule.span_le (p := (Φ.flag0.X i.castSucc).comap (LinearMap.id - (V.hT (Φ.f i)).smulRight (Φ.e i)))).2 (by
      rintro _ ⟨j, hj, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
      rw [show V.hT (Φ.f i) (Φ.e j) = _ from Φ.ef j i]
      split_ifs with e
      · rw [e, one_smul, sub_self]; exact zero_mem _
      · rw [zero_smul, sub_zero]
        exact Submodule.subset_span ⟨j, lt_of_le_of_ne (Nat.lt_succ_iff.1 hj) (Fin.val_ne_of_ne e), rfl⟩) hx
    simpa using this
  suffices h : extSub (F := F) V R (Φ.flag0.X i.succ) ≤ (extSub (F := F) V R (Φ.flag0.X i.castSucc)).comap
    (LinearMap.id - (Φ.coef hc R i).smulRight (coordR V R (Φ.e i))) by simpa using h hy
  refine Submodule.span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  have := h1 x hx
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply]
  rw [coef_coordR]
  convert coordR_mem (F := F) V R this using 1
  funext a; simp [coordR, HSpace.hD]

def chi (i : Fin (wittIndex V)) : Φ.flag0.par hc R →* R ⊗[F] E where
  toFun p := Φ.coef hc R i (act hc V p.1 (coordR V R (Φ.e i)))
  map_one' := by rw [OneMemClass.coe_one, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_one, coef_coordR, Φ.ef, if_pos rfl, map_one]
  map_mul' p q := by
    have he : coordR (F := F) V R (Φ.e i) ∈ extSub (F := F) V R (Φ.flag0.X i.succ) :=
      coordR_mem V R (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
    have h1 := Φ.coef_eq_zero hc R i (mem_parab_iff_maps.1 (IsoFlag.mem_par.1 p.2 i.castSucc) _
      (Φ.sub_coef_mem hc R i (mem_parab_iff_maps.1 (IsoFlag.mem_par.1 q.2 i.succ) _ he)))
    rw [IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_sub, map_sub, sub_eq_zero, act, act, act, Matrix.mulVec_smul, map_smul, smul_eq_mul] at h1
    rw [MulMemClass.coe_mul, IndefiniteRowSideFullHecke.AdelicUnitaryGroups.act_mul, mul_comm]
    exact h1

def IsWeylRep (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GRat hc.sig V.gram) : Prop :=
  ∀ u, ∀ x ∈ Φ.sub (invSV π ε u), ratAct hc V w x ∈ Φ.sub u

def IsGood (L : Submodule (𝓞 E) (Fin V.rank → E)) (a : GL (Fin V.rank) (AF F ⊗[F] E)) : Prop :=
  Submodule.IsLattice E L ∧ (∀ v, IsSelfDualAt hc.sig V.gram L v) ∧
  (∀ i, V.frame.equivFun (Φ.e i) ∈ L ∧ V.frame.equivFun (Φ.f i) ∈ L) ∧ IsMajorantFrame hc.sig V.gram a ∧
  ∀ (w : InfinitePlace F) (i : Fin (wittIndex V)),
    (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ hc.sig) (Formalism.UG.bc (compInf F E w) a⁻¹).1 * (Formalism.UG.bc (compInf F E w) a⁻¹).1) *ᵥ
      coordR V w.Completion (Φ.e i) = JR w.Completion V.gram *ᵥ coordR V w.Completion (Φ.f i)

end WittFrame

def IsSSPart {n : ℕ} (γ s : Matrix (Fin n) (Fin n) E) : Prop :=
  Module.End.IsSemisimple (Matrix.toLin' s) ∧ Commute γ s ∧ IsNilpotent (γ - s)

def IsSSClass {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (𝔬 : Set (GRat σ J)) : Prop :=
  ∃ δ : GRat σ J, Module.End.IsSemisimple (Matrix.toLin' δ.1.1) ∧
    𝔬 = {γ | ∃ s : GRat σ J, IsSSPart γ.1.1 s.1.1 ∧ IsConj δ s}

end General

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (Φ : WittFrame V) (K : Subgroup (GA D V))

abbrev GF (V : HSp D) : Type := GRat D.sp.cm.sig V.gram

abbrev rat (V : HSp D) : GF V →* GA D V := ratEmb D.sp.cm.sig V.gram

def absChi (i : Fin (wittIndex V)) : PA Φ.flag0 →* ℝ≥0 :=
  (Doubling.absE D.host.F D.host.E).comp (Φ.chi D.sp.cm (AF D.host.F) i).toHomUnits

def H0 (x : GA D V) : A0 (wittIndex V) := WithLp.toLp 2 fun i => Real.log (Doubling.iwAbs (absChi Φ i) K x)

def unipMeas (𝔉 : IsoFlag V) : Measure (NA 𝔉) := (quotMeasure (NQ 𝔉) Measure.haar Set.univ)⁻¹ • Measure.haar

def kerP (J : Finset (Fin (wittIndex V))) (𝔬 : Set (GF V)) (f : GA D V → ℂ) (x y : GA D V) : ℂ :=
  ∑' δ : {δ : GF V // δ ∈ 𝔬 ∧ rat V δ ∈ Φ.levi D.sp.cm (AF D.host.F) (stdPar J)},
    ∫ n : NA (Φ.stdFlag J), f (x⁻¹ * rat V δ * n * y) ∂unipMeas (Φ.stdFlag J)

def kT (𝔬 : Set (GF V)) (f : GA D V → ℂ) (T : A0 (wittIndex V)) (x : GA D V) : ℂ :=
  ∑ J : Finset (Fin (wittIndex V)), (-1) ^ J.card * ∑' ξ : Quot ((Φ.stdFlag J).parRat D.sp.cm),
    tauHat (stdPar J) ∅ (H0 Φ K (rat V ξ.out * x) - T) * kerP Φ J 𝔬 f (rat V ξ.out * x) (rat V ξ.out * x)

def Ys (π : Equiv.Perm (Fin (wittIndex V))) (ε : Fin (wittIndex V) → SignTypeˣ) (w : GF V) (x : GA D V)
    (T : A0 (wittIndex V)) : A0 (wittIndex V) := inverseChamberMap π ε (T - H0 Φ K (rat V w * x))

def Yfam (x : GA D V) (T : A0 (wittIndex V)) (Q : Finset (SV (wittIndex V))) : A0 (wittIndex V) :=
  if h : ∃ s : Equiv.Perm (Fin (wittIndex V)) × (Fin (wittIndex V) → SignTypeˣ) × GF V,
      Φ.IsWeylRep D.sp.cm s.1 s.2.1 s.2.2 ∧ Q ⊆ weylPar s.1 s.2.1 then
    pr Q (Ys Φ K h.choose.1 h.choose.2.1 h.choose.2.2 x T) else 0

def weight (𝔞 : Submodule ℝ (A0 (wittIndex V))) (T : A0 (wittIndex V)) (x : GA D V) : ℝ :=
  ∫ H : aMQ 𝔞 ∅, gamM 𝔞 ∅ (Yfam Φ K x T) H

def volA (𝔞 : Submodule ℝ (A0 (wittIndex V))) (I : Subgroup (GA D V)) (dt : Measure I) : ℝ :=
  (quotMeasure ((GQ V).subgroupOf I) dt).real {q | ‖𝔞.starProjection (H0 Φ K (q.out : I))‖ < 1} /
    (volume : Measure (aMQ 𝔞 ∅)).real (Metric.ball 0 1)

def IsMinLevi (γ : GF V) (P : Finset (SV (wittIndex V))) : Prop :=
  IsPar P ∧ rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) P ∧
    ∀ (g : GF V) P', IsPar P' → rat V (g * γ * g⁻¹) ∈ Φ.levi D.sp.cm (AF D.host.F) P' → P'.card ≤ P.card

end GlobalTheory.TruncKer

end
end

