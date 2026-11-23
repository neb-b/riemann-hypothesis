module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1138
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairData

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemULOfSplit
section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_UL_of_split {n : ℕ} {w : Pl E} (hw : IsSplitAt w) (x : GLw n w) : x ∈ UL n w := by
  rw [UL, if_pos hw]; exact Subgroup.mem_top x

theorem toSub_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (hg : g ∈ H) : toSub H g = ⟨g, hg⟩ := by
  simp [toSub, hg]

theorem ct_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (N : Subgroup (GLw n w)) (F : GLw n w → ℂ)
    (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (hF : ∀ y ∈ N, ∀ x, F (y * x) = F x ∧ F (x * y) = F x)
    (k : GLw a w × GLw b w) (hk1 : k.1 ∈ GlobalTheory.LFun.KGL w (n := a)) (hk2 : k.2 ∈ GlobalTheory.LFun.KGL w (n := b)) (hkN : dgM h w k ∈ N)
    (m : GLw a w × GLw b w) : ct h w F (k * m) = ct h w F m ∧ ct h w F (m * k) = ct h w F m := by
  have hab := GlobalTheory.T.absHalf_blockDet_integralGL_invariant E a b w m k hk1 hk2
  constructor
  · unfold ct
    rw [hab.1]
    congr 2
    funext X
    congr 1
    funext κ
    rw [(_root_.GlobalTheory.BCT.CtLevel.blk_mul_dgM E a b n h w m k _).1]
    have e : (κ : GLw n w)⁻¹ * (dgM h w k * blk h w m (Multiplicative.toAdd X)) * κ =
        ((κ : GLw n w)⁻¹ * dgM h w k * κ) * ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * κ) := by group
    rw [e, (hF _ (hNn _ κ.2 _ hkN) _).1]
  · unfold ct
    have e : (fun X : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) =>
        avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ * blk h w (m * k) (Multiplicative.toAdd X) * κ)) =
        fun X => avg fun κ : GlobalTheory.LFun.KGL w (n := n) => F ((κ : GLw n w)⁻¹ *
          blk h w m (Multiplicative.toAdd (Multiplicative.ofAdd (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val))) * κ) := by
      funext X
      congr 1
      funext κ
      rw [(_root_.GlobalTheory.BCT.CtLevel.blk_mul_dgM E a b n h w m k _).2]
      have e : (κ : GLw n w)⁻¹ * (blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * dgM h w k) * κ =
          ((κ : GLw n w)⁻¹ * blk h w m (k.1.val * Multiplicative.toAdd X * (k.2⁻¹).val) * κ) *
            ((κ : GLw n w)⁻¹ * dgM h w k * κ) := by group
      rw [e, (hF _ (hNn _ κ.2 _ hkN) _).2]
      rfl
    have hh := GlobalTheory.T.haarIntegralNormalized_integralMatrices_twoSidedMul E a b w (fun Y => avg fun κ : GlobalTheory.LFun.KGL w (n := n) =>
      F ((κ : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd Y) * κ)) k.1 k.2⁻¹ hk1 (inv_mem hk2)
    rw [hab.2, e, hh]

theorem ctMu_inv {a b n : ℕ} (h : a + b = n) (w : Pl E) (hw : IsSplitAt w) (N : Subgroup (GLw n w))
    (K' : Subgroup (UL n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ) (hf : IsHecke K' f)
    (hNK : N ≤ K'.map (UL n w).subtype) (hNn : ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N)
    (k : GLw a w × GLw b w) (hk : k ∈ (lev₁ h w N μ).prod (lev₂ h w N μ)) (m : GLw a w × GLw b w) :
    ctMu h w μ f (k * m) = ctMu h w μ f m ∧ ctMu h w μ f (m * k) = ctMu h w μ f m := by
  obtain ⟨⟨⟨hk1, hkN1⟩, hkμ1⟩, ⟨⟨hk2, hkN2⟩, hkμ2⟩⟩ := hk
  have hkN : dgM h w k ∈ N := by
    have e : k = (k.1, 1) * (1, k.2) := by ext <;> simp
    rw [e, map_mul]
    exact N.mul_mem hkN1 hkN2
  have hF : ∀ y ∈ N, ∀ x, (fun y => f (toSub (UL n w) y)) (y * x) = (fun y => f (toSub (UL n w) y)) x ∧
      (fun y => f (toSub (UL n w) y)) (x * y) = (fun y => f (toSub (UL n w) y)) x := by
    intro y hy x
    obtain ⟨y', hy', rfl⟩ := hNK hy
    have e1 : toSub (UL n w) ((UL n w).subtype y' * x) = y' * toSub (UL n w) x := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    have e2 : toSub (UL n w) (x * (UL n w).subtype y') = toSub (UL n w) x * y' := by
      rw [toSub_eq _ _ (mem_UL_of_split hw _), toSub_eq _ _ (mem_UL_of_split hw x)]; rfl
    exact ⟨by simp only; rw [e1]; exact (hf.2 y' hy' _).1, by simp only; rw [e2]; exact (hf.2 y' hy' _).2⟩
  have hc := ct_inv h w N (fun y => f (toSub (UL n w) y)) hNn hF k hk1 hk2 hkN m
  have hμ1 : μ (GeneralLinearGroup.det k.1) = 1 := hkμ1
  have hμ2 : μ (GeneralLinearGroup.det k.2) = 1 := hkμ2
  unfold ctMu
  rw [hc.1, hc.2]
  simp only [Prod.fst_mul, Prod.snd_mul, map_mul, mul_pow, map_pow, hμ1, hμ2, one_pow, mul_one, one_mul]
  constructor <;> trivial

theorem ctMu_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsOpen {x | μ x = 1} → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → ∃ (K₁ : Subgroup (GLw a w)) (K₂ : Subgroup (GLw (n - a) w)), IsLevel (thL a w) (GlobalTheory.LFun.KGL w (n := a)) K₁ ∧ IsLevel (thL (n - a) w) (GlobalTheory.LFun.KGL w (n := (n - a))) K₂ ∧ ((K' = KL n w ∧ ∀ u ∈ (GlobalTheory.LFun.KGL w (n := 1)), μ (GeneralLinearGroup.det u) = 1) → K₁ = GlobalTheory.LFun.KGL w (n := a) ∧ K₂ = GlobalTheory.LFun.KGL w (n := (n - a))) ∧ ∀ f, IsHecke K' f → IsHecke (K₁.prod K₂) (ctMu (Nat.add_sub_cancel' ha) w μ f) ∧ ((∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a (n - a) w (ctMu (Nat.add_sub_cancel' ha) w μ f)) := by
  intro E _ _ _ _ n a ha w hw μ hμ K' hK'
  obtain ⟨N, hNo, hNK, hNn, hNf⟩ := GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel E n w K' hw hK'
  have hlev := GlobalTheory.T.isLevel_blockLevels_splitPlace E a (n - a) n (Nat.add_sub_cancel' ha) w N μ hw hNo hμ
  refine ⟨lev₁ (Nat.add_sub_cancel' ha) w N μ, lev₂ (Nat.add_sub_cancel' ha) w N μ, hlev.1, hlev.2, ?_,
    fun f hf => ⟨⟨_root_.GlobalTheory.BCT.CtLevel.hasCompactSupport_ctMu_split E a (n - a) n _ w μ f hw hf.1, fun k hk m =>
      ctMu_inv _ w hw N K' μ f hf hNK hNn k hk m⟩, _root_.GlobalTheory.BCT.CtReg.ctMu_regAt2 E a (n - a) n _ w μ f hw⟩⟩
  rintro ⟨hK'e, hμ1⟩
  rw [hNf hK'e]
  exact GlobalTheory.T.blockLevels_eq_integralGL_of_unramified E a (n - a) n _ w μ hμ1

end GlobalTheory.BCT.CtLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBound
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_mixTop_le_of_weighted : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  intro n r _ _ K w c hw hK
  set D : ℝ := (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 with hD
  have hs : ∀ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hterm : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      ‖((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤ D := by
    intro p π u
    rw [norm_mul, norm_mul, hs, hs, one_mul, one_mul]
    exact GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u w c hw (fun i b => by simpa using hK i (u i) b (p i) (p (π i)))
  have hsum : ‖∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤
      (Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun π _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun u _ => hterm p π u))).trans ?_
    simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fun]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold mixTop
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖_‖ ≤ (n.factorial : ℝ)⁻¹ *
        ((Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hf.le)
    _ = _ := by rw [hD]; field_simp

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotKltAtSubOfNotLcAt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_kltAt_sub_of_not_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ LcAt p n (Δ + D) x →
    ∃ δ₀ : ℚ, 0 < δ₀ ∧ ∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ¬ KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D x hD hk hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, hd⟩ := hk
  obtain ⟨m', f, hm', hf, hDf⟩ := _root_.GlobalTheory.PairStep.exists_localEqn_of_isQCart X p D hD x
  obtain ⟨m₁, g₁, hm₁, hg₁, hd₁⟩ := _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n Δ D η x m m' g f 1 hm hm' hg hDf
  rw [one_smul] at hg₁
  have hnl := (_root_.GlobalTheory.PairStep.lcAt_iff_of_isLogEqn X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ hg₁).not.1 hlc
  push_neg at hnl
  obtain ⟨E, hE, hlt⟩ := hnl
  rw [hd₁, one_mul] at hlt
  set a := discrep E η m g with ha
  set t : ℚ := (E.ord f : ℚ) / m' with ht
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have ht0 : 0 ≤ t := div_nonneg (by exact_mod_cast (E.ord_nonneg_iff f).2 (hE _ hf)) hm'q.le
  have ha1 := hd E hE
  refine ⟨(-1 - a + t) / (t + 1), div_pos (by linarith) (by linarith), fun δ hδ0 hδ hk' => ?_⟩
  obtain ⟨m₂, g₂, hm₂, hg₂, hd₂⟩ := _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n Δ D η x m m' g f (1 - δ) hm hm' hg hDf
  have := ((hg₂.kltAt_iff hn hη hm₂).1 hk') E hE
  rw [hd₂] at this
  have h1 : δ * (t + 1) ≤ -1 - a + t := (le_div_iff₀ (by linarith)).1 hδ
  nlinarith
end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotLcAtAddOfIsNkltCentre
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem not_lcAt_add_of_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Γ A : X → ℚ) (z x : X), IsNkltCentre p n Γ z → IsQCart A → ¬ Off A z → z ⤳ x → ¬ LcAt p n (Γ + A) x := by
  intro X _ _ _ p n hp hn Γ A z x hN hA hoff hzx hlc
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  have hlcz := ((_root_.GlobalTheory.Discrepancy.kltAt_lcAt_generisation X p n (Γ + A) x z hzx).2 hlc)
  obtain ⟨E, η, m, g, hη, hm, hlog, hC, hd⟩ := hN
  obtain ⟨m₀, D₀, hm₀, hEff, rfl⟩ := hA
  obtain ⟨m', f, hm', hreg, heq⟩ := _root_.GlobalTheory.PairStep.exists_localEqn_of_isQCart X p (qWeil D₀ m₀) ⟨m₀, D₀, hm₀, hEff, rfl⟩ z
  obtain ⟨m'', g'', hm'', hlog'', hdisc⟩ :=
    _root_.GlobalTheory.PairStep.isLogEqn_add_smul X p n Γ (qWeil D₀ m₀) η z m m' g f 1 hm hm' hlog heq
  rw [one_smul] at hlog''
  have h1 := ((_root_.GlobalTheory.PairStep.lcAt_iff_of_isLogEqn X p n hp hn (Γ + qWeil D₀ m₀) η z m'' g'' hη hm'' hlog'').1 hlcz) E hC.1
  rw [hdisc E, one_mul] at h1
  have hf0 : 0 ≤ E.ord f := (E.ord_nonneg_iff f).2 (hC.1 _ hreg)
  have hm'q : (0 : ℚ) < m' := by exact_mod_cast hm'
  have hfle : (E.ord f : ℚ) / m' ≤ 0 := by linarith
  have hfle' : (E.ord f : ℚ) ≤ 0 := by
    rwa [div_le_iff₀ hm'q, zero_mul] at hfle
  have hord : E.ord f = 0 := by
    have : E.ord f ≤ 0 := by exact_mod_cast hfle'
    omega
  have hreg' := hC.2 f hreg hord
  apply hoff
  intro w hw
  by_cases hc : Order.coheight w = 1
  · obtain ⟨F, hF⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := p) hc
    rw [heq w hw F hF]
    have a : 0 ≤ F.ord f :=
      (F.ord_nonneg_iff f).2 ((hF _).2 (regAt_of_specializes hw hreg))
    have b : 0 ≤ F.ord f⁻¹ :=
      (F.ord_nonneg_iff _).2 ((hF _).2 (regAt_of_specializes hw hreg'))
    rw [F.ord_inv] at b
    have : F.ord f = 0 := by omega
    simp [this]
  · have : D₀.mult w = 0 := by
      by_contra h
      exact hc (CartierDiv.coheight_eq_one_of_mult_ne_zero h)
    simp [qWeil, this]

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdQMapDomainResiduePlaceTransportStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordQ_mapDomain_residuePlace_transport : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (Q : Subring L) (u : Q)
  (S E : Place cL) (ψ : S.ring →+* K) (F : Place cK),
  S.Contains Q → S.ord (u : L) = 0 → (u : L) ≠ 0 → Function.Surjective ψ →
  (∀ a : K, a ∈ F.ring ↔ ∃ q : S.ring, (q : L) ∈ Q ∧ ψ q = a) →
  (∀ us : S.ring, (us : L) = u → F.ord (ψ us) = 1) →
  (∀ G : L, G ≠ 0 → (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ E.ring → P.ord G = 0) →
    ∃ q : Q, IsUnit q ∧ G = (q : L) * (u : L) ^ E.ord G) →
  ∀ φ : S.ring →₀ ℚ, (∀ g ∈ φ.support, ψ g ≠ 0) →
  (∀ P : Place cL, P.IsPrimeOf Q → P.ring ≠ S.ring → P.ring ≠ E.ring →
    P.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) = 0) →
  F.ordQ (Finsupp.mapDomain ψ φ) = E.ordQ (Finsupp.mapDomain (fun g : S.ring => (g : L)) φ) := by
  first | exact @GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq | exact GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq | (intros; apply GlobalTheory.FieldPair.ordQ_mapDomain_residue_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicArchimedeanEigenvector
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

namespace GlobalTheory.LineGlue

theorem map_mul_eq_of_local {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (U : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin 1) R) (P : Matrix (Fin 1) (Fin n) R)
    (hPX : P * X = 1) (β : Matrix (Fin 1) (Fin 1) S) (h : U.map φ * X.map φ = X.map φ * β) :
    (U * X).map φ = (X * (P * U * X)).map φ := by
  have hβ : (P * U * X).map φ = β := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ← Matrix.map_mul, hPX,
      Matrix.map_one _ φ.map_zero φ.map_one, Matrix.one_mul]
  rw [Matrix.map_mul, h, ← hβ, ← Matrix.map_mul]

end GlobalTheory.LineGlue

theorem GlobalTheory.LineGlue.exists_idele_smul_of_local_lines : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) (pL : Matrix (Fin 1) (Fin n) E), pL * x = 1 → ∀ q : GAd σ J, (∀ w : InfinitePlace F, ∃ β : GL (Fin 1) (w.Completion ⊗[F] E), (matHom _ σ J (projArch σ J w q)).1 * x.map (inclR (F := F) w.Completion) = x.map (inclR (F := F) w.Completion) * β.1) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J (proj σ J v q)).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1) → ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J q).1 * adMat F x = l.1 • adMat F x := by
  intro F E _ _ _ _ _ σ n J x pL hpx q hInf hFin
  set U := matHom (AF F) σ J q with hU
  set X := adMat F x with hX
  set P := pL.map (inclR (F := F) (AF F)) with hP
  have hPX : P * X = 1 := by
    rw [hP, hX, adMat, ← Matrix.map_mul, hpx, Matrix.map_one _ (map_zero _) (map_one _)]
  have hinclFin : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      x.map (inclR (F := F) (Fv F v)) = X.map (compFin F E v) := by
    intro v
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compFin, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hinclInf : ∀ w : InfinitePlace F,
      x.map (inclR (F := F) w.Completion) = X.map (compInf F E w) := by
    intro w
    rw [hX, adMat, Matrix.map_map]
    congr 1
    try funext e; simp [compInf, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hMX : U.1 * X = X * (P * U.1 * X) := by
    ext i j
    refine GlobalTheory.Doubling.adele_ext (fun w => ?_) (fun v => ?_)
    · obtain ⟨β, hβ⟩ := hInf w
      rw [matHom_projArch, hinclInf] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compInf F E w) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
    · obtain ⟨β, hβ⟩ := hFin v
      rw [matHom_proj, hinclFin] at hβ
      have := GlobalTheory.LineGlue.map_mul_eq_of_local (compFin F E v) U.1 X P hPX β.1 hβ
      exact congrFun (congrFun this i) j
  obtain ⟨c', hc'⟩ : ∃ c' : AF F ⊗[F] E, c' * (P * U.1 * X) 0 0 = 1 := by
    refine ⟨(P * (U⁻¹).1 * X) 0 0, ?_⟩
    have h1 : X = (U⁻¹).1 * X * (P * U.1 * X) := by
      rw [Matrix.mul_assoc, ← hMX, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    have h2 : P * (U⁻¹).1 * X * (P * U.1 * X) = 1 := by
      rw [show P * (U⁻¹).1 * X * (P * U.1 * X) = P * ((U⁻¹).1 * X * (P * U.1 * X)) by
        simp only [Matrix.mul_assoc], ← h1, hPX]
    have := congrFun (congrFun h2 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_one] using this
  refine ⟨Units.mkOfMulEqOne _ _ (by rw [mul_comm]; exact hc'), ?_⟩
  rw [hMX]
  ext i j
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_one, mul_comm]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydi
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_poinVol {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)) (hK : IsCompact K)
    (hS : ∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) :
    IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  classical
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  let g : Fin n → ℂ → ℝ := fun a =>
    if a ∈ S then (Metric.closedBall (0 : ℂ) (1 / 2)).indicator (fun z : ℂ => (‖z‖ * |Real.log ‖z‖|)⁻¹ ^ 2)
    else (Metric.closedBall (0 : ℂ) R).indicator (fun _ => 1)
  have hg : ∀ a, Integrable (g a) := by
    intro a
    by_cases h : a ∈ S
    · simp only [g, h, if_true]
      exact (integrable_indicator_iff measurableSet_closedBall).2 _root_.GlobalTheory.GoodTop.integrableOn_poincare_disc
    · simp only [g, h, if_false]
      exact (integrable_indicator_iff measurableSet_closedBall).2
        (continuousOn_const.integrableOn_compact (isCompact_closedBall _ _))
  have h1 : Integrable (fun x : Fin n → ℂ => ∏ a, g a (x a)) := Integrable.fintype_prod hg
  have h2 := (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).integrable_comp_of_integrable h1
  refine (h2.integrableOn (s := K)).congr_fun ?_ hK.measurableSet
  intro v hv
  simp only [Function.comp]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases h : a ∈ S
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
      simpa using hS v hv a h
    simp only [g, h, if_true, poinWt]
    exact Set.indicator_of_mem this _
  · have : v.ofLp a ∈ Metric.closedBall (0 : ℂ) R := by
      simpa using (PiLp.norm_apply_le v a).trans (hR v hv)
    simp only [g, h, if_false, poinWt, inv_one, one_pow]
    exact Set.indicator_of_mem this _

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFnFamilySmallPullbackBirationalModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

namespace GlobalTheory.HSNef

theorem smallFam_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (π : Y ⟶ X) (hπ : π ≫ p = q) (φ : X.functionField →+* Y.functionField), IsModel π φ → ∀ (B : HermLB p) (J : Type) (f : J → X.functionField) (w : J → ℝ), SmallFam B f w → SmallFam (B.pull π hπ) (fun j => φ (f j)) w := by
  intro k _ X Y _ _ p q π hπ φ hM B J f w hs
  obtain ⟨β, hβ, hreg, hnorm⟩ := hs
  obtain ⟨hR, -, hF, hV⟩ := _root_.GlobalTheory.HSNef.model_regAt_unitAt_values k X Y p q π hπ φ hM
  refine ⟨fun c => Units.map φ.toMonoidHom (β (c PUnit.unit)), ?_, ?_, ?_⟩
  · intro i j h
    have hi : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (i PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit h.1
    have hj : genericPoint Y ∈ π ⁻¹ᵁ B.B.U (j PUnit.unit) :=
      LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit h.2
    have hX : genericPoint X ∈ B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit) := by
      rw [← hM.gen]; exact ⟨hi, hj⟩
    have eg : ((B.B.pull π).g i j).val = resG Y (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit)))
        (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val) := by
      dsimp only [LB.pull, LB.LinComb]
      simp only [Fintype.prod_unique, zpow_one, LB.val_res, pullU, Units.coe_map]
      rfl
    show φ (β (i PUnit.unit)) = fnOf _ h ((B.B.pull π).g i j).val * φ (β (j PUnit.unit))
    rw [hβ (i PUnit.unit) (j PUnit.unit) hX, map_mul, hF _ hX ⟨hi, hj⟩, eg]
    exact congrArg (· * φ (β (j PUnit.unit))) (fnOf_resG (X := Y) (U := π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) (fun _ hy => ⟨LB.wchart_le B.B (fun _ : PUnit => π) i PUnit.unit hy.1, LB.wchart_le B.B (fun _ : PUnit => π) j PUnit.unit hy.2⟩ : (B.B.pull π).U i ⊓ (B.B.pull π).U j ≤ π ⁻¹ᵁ (B.B.U (i PUnit.unit) ⊓ B.B.U (j PUnit.unit))) h (π.app _ (B.B.g (i PUnit.unit) (j PUnit.unit)).val)).symm
  · intro y c hy j
    show RegAt y (φ (f j) * φ (β (c PUnit.unit)))
    rw [← map_mul]
    exact hR y _ (hreg (π y) (c PUnit.unit) (LB.wchart_le B.B (fun _ : PUnit => π) c PUnit.unit hy) j)
  · intro σ z c hz j
    have hm := mem_of_mem_linComb (m := fun _ => GlobalTheory.Points.PtsOver.map π hπ _ z) (fun _ => rfl) hz
      PUnit.unit
    have hr := hreg (π (under z)) (c PUnit.unit) (mem_ptsIn.1 hm) j
    have e2 : ((B.φ σ).pull π hπ).φ c z = (B.φ σ).φ (c PUnit.unit) (GlobalTheory.Points.PtsOver.map π hπ _ z) :=
      (B.φ σ).pull_φ π hπ c z
    show ‖ratVal (φ (f j) * φ (β (c PUnit.unit))) z‖ * Real.exp (-((B.φ σ).pull π hπ).φ c z / 2) ≤ _
    rw [← map_mul, hV σ z _ hr, e2]
    exact hnorm σ _ (c PUnit.unit) hm j

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingEquivTransportsVarietyPairDataStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringEquiv_transports_varietyPair_data : ∀ {k K K' : Type} [Field k] [CharZero k] [Field K] [Field K'] (c : k →+* K) (c' : k →+* K') (e : K ≃+* K'),
  (∀ a, e (c a) = c' a) → ∀ (n : ℕ) (x : Fin n → K) (R : Subring K) (φ : K →₀ ℚ), TrBasis c x →
  TrBasis c' (e ∘ x) ∧
  (IsLocModel c R ↔ IsLocModel c' (R.map e.toRingHom)) ∧
  (Klt c n R (dForm c x) φ ↔ Klt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) ∧
  (EffAt c n R (dForm c x) φ ↔ EffAt c' n (R.map e.toRingHom) (dForm c' (e ∘ x)) (Finsupp.mapDomain e φ)) := by
  first | exact @GlobalTheory.FieldPair.transport_ringEquiv | exact GlobalTheory.FieldPair.transport_ringEquiv | (intros; apply GlobalTheory.FieldPair.transport_ringEquiv <;> assumption)
end

