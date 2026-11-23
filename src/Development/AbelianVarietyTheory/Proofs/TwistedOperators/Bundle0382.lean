module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdSpan.BddForms

theorem fg_of_mem_lats {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
    (Lv : SW.Level X) {L : Lt E r} (hL : L ∈ Lv.lats) : L.FG := by
  obtain ⟨-, s, hcop, hs, -⟩ := hL
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl, Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hcop
    have hle := Ideal.mul_le_left (I := Lv.𝔪) (J := conjI Lv.𝔪)
    rw [hcop] at hle
    exact Lv.proper (top_le_iff.1 hle)
  let f : (Fin r → E) →ₗ[𝓞 E] (Fin r → E) := s • LinearMap.id
  have hinj : Function.Injective f := fun v w h => smul_right_injective _ hs0 h
  have hle : L.map f ≤ X.Λ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hs v hv
  have : IsNoetherian (𝓞 E) X.Λ := isNoetherian_of_fg_of_noetherian X.Λ X.Λ_fg
  exact Submodule.fg_of_fg_map_injective f hinj (isNoetherian_submodule.1 this _ hle)

theorem zpow_mul_rpow_sq (t : ℝ) (ht : 0 < t) (l : ℤ) : t ^ l * (t ^ 2) ^ (-(l : ℝ) / 2) = 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
  rw [show ((2 : ℕ) : ℝ) * (-(l : ℝ) / 2) = -(l : ℝ) by push_cast; ring, Real.rpow_neg ht.le,
    Real.rpow_intCast]
  exact mul_inv_cancel₀ (zpow_ne_zero _ ht.ne')

theorem diag_ne_zero {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} {b : Frame Ψ r}
    (hb : b ∈ Bor Ψ r) (τ : Ψ) (i : Fin r) : b τ i i ≠ 0 := by
  obtain ⟨hdet, hlow⟩ := hb τ
  have htri : (mat b τ).BlockTriangular id := fun a c hca => hlow a c hca
  rw [Matrix.det_of_isUpperTriangular htri, Finset.prod_ne_zero_iff] at hdet
  exact hdet i (Finset.mem_univ _)

theorem exists_isSB_ne (n g : ℕ) : ∃ φ : TF n g, SW.IsSB φ ∧ φ ≠ 0 := by
  have key : ∀ x y : Matrix (Fin n) (Fin g) ℚ, SW.IntM y → (SW.IntM (x + y) ↔ SW.IntM x) := by
    intro x y hy
    constructor
    · intro h k i
      simpa using (h k i).sub (hy k i)
    · intro h k i
      simpa using (h k i).add (hy k i)
  have h0 : SW.IntM (0 : Matrix (Fin n) (Fin g) ℚ) := fun k i => by
    simpa using (isIntegral_zero : IsIntegral ℤ (0 : ℚ))
  refine ⟨fun x => if SW.IntM x then 1 else 0, ⟨1, one_pos, ?_, ?_⟩, ?_⟩
  · intro x hx
    by_cases h : SW.IntM x
    · simpa using h
    · simp [h] at hx
  · intro x y hy
    simp only [Nat.cast_one, one_smul, key x y hy]
  · intro h
    have := congrFun h 0
    simp [h0] at this

end GlobalTheory.AdSpan.BddForms

namespace GlobalTheory.AdSpan.BddForms

theorem pnorm_le_of_bdd : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → ∃ K : ℝ, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, C.X.pnorm (wtOf C.X C.hr c c' S.rank) (F L) x ≤ K := by
  intro D S T C om hW Lv hn M hw hM hMm B hB f' _hbase c c' z φ hz _hγ _hk v₀ μ _hvac _hμ ep cf hepcf gL hgL F
    _hFd hFb hFφ hφb
  obtain ⟨K, hKφ⟩ := hφb
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hmv : ∀ a, C.IsB (C.mvB a B) := fun a => ((hJ B hB).2.2.2.2.2 a).1
  have hdom : ∀ a, C.xB (C.mvB a B) ∈ C.X.dom := fun a => (hJ _ (hmv a)).2.1
  obtain ⟨φ₀, hφ₀, hφ₀ne⟩ := exists_isSB_ne S.rank C.g

  have hz1 : ∀ a ∈ GinfC T, ‖z a‖ = 1 := by
    intro a ha
    obtain ⟨c0, hc0, hc0'⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hW 1 (one_mem _) a ha B hB
    have e1 : om (1, a) (C.Th (C.xB B) φ₀) = z a • C.Th (C.xB (C.mvB a B)) φ₀ := hz a ha φ₀ hφ₀
    have e2 := hc0' φ₀ hφ₀
    have : z a = c0 := RealChar.smul_cancel (RealChar.th_ne C (hdom a) hφ₀ hφ₀ne) (e1.symm.trans e2)
    rw [this, hc0]

  have hstdFG : (stdL D.host.E S.rank).FG := Submodule.fg_span (Set.finite_range _)
  have hec : ∀ L ∈ Lv.lats, ‖ep 1 * cf (gL L)‖ = 1 := by
    intro L hL
    obtain ⟨h1, h2, h3⟩ := hgL L hL
    obtain ⟨e1, e2, -⟩ := hepcf 1 (stdL _ _) (gL L) L (one_mem _) (Red.trivAt_one _ _) hstdFG
      (by rw [Red.fmtC_one]; exact Red.isMov_one _) h1 h2 (fg_of_mem_lats Lv hL) h3
    rw [norm_mul, e1, e2, one_mul]

  have hFa : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, ‖F L (C.xB (C.mvB a B))‖ ≤ K := by
    intro L hL a ha
    have h := hKφ (gL L * a)
    rw [hFφ L hL a ha, norm_mul, norm_mul, hz1 a ha, hec L hL, one_mul, one_mul] at h
    exact h
  refine ⟨K, fun L hL x hx => ?_⟩
  obtain ⟨hON, hbB, hxe, hdm, -⟩ := hob x hx
  obtain ⟨a, ha, hax⟩ := (GlobalTheory.AdSpan.ConjHol.unitFr_conj_moved D S T C B hB).2.1 (o x) hON
  have hox : o x ∈ C.X.dom := hax ▸ hdom a
  have hFo : ‖F L (o x)‖ ≤ K := hax ▸ hFa L hL a ha
  set la := wtOf C.X C.hr c c' S.rank with hla
  have hval : F L x = bchar la (b x) * F L (o x) := by
    have := hFb L hL (o x) hox (b x) hbB
    rw [← hxe] at this
    exact this
  have hprod : ‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2) = 1 := by
    unfold bchar
    simp_rw [norm_prod, norm_zpow]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    exact zpow_mul_rpow_sq _ (norm_pos_iff.2 (diag_ne_zero hbB τ i)) _
  simp only [Data.pnorm]
  simp only [← hdm]
  rw [hval, norm_mul]
  calc ‖bchar la (b x)‖ * ‖F L (o x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)
      = ‖F L (o x)‖ * (‖bchar la (b x)‖ * ∏ τ, ∏ i, (‖b x τ i i‖ ^ 2) ^ (-(la τ i : ℝ) / 2)) := by ring
    _ = ‖F L (o x)‖ := by rw [hprod, mul_one]
    _ ≤ K := hFo

end GlobalTheory.AdSpan.BddForms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.PerAllTame

variable {D : D7}

theorem tame_congr {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {ℓ ℓ' : (WO S T → ℂ) → ℂ}
    (h : Tame ψ S T ℓ) (e : ∀ f, IsThetaFunO ψ S T f → ℓ' f = ℓ f) : Tame ψ S T ℓ' := by
  have hθ : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    fun w f hf => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, fun f hf => ?_, fun f hf m _ α hα hs => ?_⟩
  · rw [e _ (GlobalTheory.OrientedHeis.theta_add hf hf'), e _ hf, e _ hf', h.add f f' hf hf']
  · rw [e _ (GlobalTheory.OrientedHeis.theta_smul c hf), e _ hf, h.smul c f hf]
  · have hfun : (fun w => ℓ' (heisO ψ S T w f)) = fun w => ℓ (heisO ψ S T w f) :=
      funext fun w => e _ (hθ w f hf)
    rw [hfun]
    exact h.cont f hf
  · obtain ⟨C, hC⟩ := h.bdd f hf
    exact ⟨C, fun w => (e _ (hθ w f hf)).symm ▸ hC w⟩
  · have hfun : (fun w => α w * ℓ' (heisO ψ S T w f)) = fun w => α w * ℓ (heisO ψ S T w f) :=
      funext fun w => by rw [e _ (hθ w f hf)]
    rw [hfun, e _ hs]
    exact h.sup f hf m α hα hs

theorem decay_of_le {V : HSp D} {F : GA D V → ℂ} (hF : RapidDec V F) (C : ℝ) (a k : ℕ) :
    ∃ C' : ℝ, ∀ (g : GA D V) (t : ℝ), 0 ≤ t → t ≤ C * quotHeight V g ^ a → ‖F g‖ * t ^ k ≤ C' := by
  obtain ⟨-, -, hd⟩ := hF
  obtain ⟨C₀, hC₀⟩ := hd (a * k)
  refine ⟨|C| ^ k * max C₀ 0, fun g t ht0 htle => ?_⟩
  have hq : (0 : ℝ) ≤ quotHeight V g ^ a := pow_nonneg (le_trans zero_le_one (one_le_quotHeight V g)) a
  have ht : t ≤ |C| * quotHeight V g ^ a := htle.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hq)
  calc ‖F g‖ * t ^ k ≤ ‖F g‖ * (|C| * quotHeight V g ^ a) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht0 ht k) (norm_nonneg _)
    _ = |C| ^ k * (‖F g‖ * quotHeight V g ^ (a * k)) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ |C| ^ k * max C₀ 0 :=
        mul_le_mul_of_nonneg_left ((hC₀ g).trans (le_max_left _ _)) (pow_nonneg (abs_nonneg _) _)

theorem perAll_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  intro D ψ ρ σ B J χ χ' om₀ hW φ G hφ hG
  have hψ : IsStdChar D ψ (-1) := hW.std
  have hψc : Continuous ψ := hψ.1.1
  have hψn : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hGc : Continuous G := hG.2.1
  have hφc : Continuous φ := hφ.2.1
  haveI : SecondCountableTopology (flagN J.d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hF : J.v0.μ J.v0.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol J.W₀ J.v0.μ J.v0.𝓕 J.v0.haar J.v0.fund
  have hFA : B.vA.μ B.vA.𝓕 < ⊤ :=
    GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B.A B.vA.μ B.vA.𝓕 B.vA.haar B.vA.fund
  have hN : J.vN.ν J.vN.𝓝 = 1 := J.vN.unit.2.2
  haveI : IsFiniteMeasure (J.v0.μ.restrict J.v0.𝓕) := isFiniteMeasure_restrict.mpr hF.ne
  haveI : IsFiniteMeasure (B.vA.μ.restrict B.vA.𝓕) := isFiniteMeasure_restrict.mpr hFA.ne
  haveI : IsFiniteMeasure (J.vN.ν.restrict J.vN.𝓝) :=
    isFiniteMeasure_restrict.mpr (by rw [hN]; exact ENNReal.one_ne_top)
  have hpf : Continuous (psiFlag ψ J.d) := GlobalTheory.Unf.EvalCont.continuous_psiFlag hψc J.d
  have hcen : Continuous (cenT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_cenT J.d B.L _
  have hpt : Continuous (ptT J.d B.L (yZero B.L ρ B.ζ)) := GlobalTheory.Unf.EvalCont.continuous_ptT J.d B.L _
  have hn : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hh1 : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => y.1.1 :=
    continuous_fst.comp continuous_fst
  have hx : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => (y.1.2 : GA D J.W) * J.d.emb0 y.1.1 :=
    hn.mul (J.d.continuous_embed.comp hh1)
  have hgg : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A => B.o.emb (y.2, 1) :=
    B.o.continuous_emb.comp (continuous_snd.prodMk continuous_const)
  have hww : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (B.o.continuous_resS_symm J.W₀).comp (continuous_const.prodMk (hpt.comp hn))
  have hcc : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)) :=
    (((hGc.comp hx).mul (hpf.comp hn).star).mul (hφc.comp continuous_snd)).mul (hψc.comp (hcen.comp hn))
  obtain ⟨C₁, a₁, hC₁⟩ := _root_.GlobalTheory.HtOrth.quotHeight_orthDec_cmp D B.V₀ B.A B.L B.o
  obtain ⟨C₂, a₂, hC₂⟩ := _root_.GlobalTheory.HtWitt.quotHeight_witt D J.W J.W₀ ρ J.d
  have key : ∀ k : ℕ, Integrable (fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
      ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W))‖ *
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k)
      (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕)) := by
    intro k
    obtain ⟨K₁, hK₁⟩ := decay_of_le hφ C₁ a₁ k
    obtain ⟨K₂, hK₂⟩ := decay_of_le hG C₂ a₂ k
    have hq : Continuous fun y : (GA D J.W₀ × flagN J.d) × GA D B.A =>
        (quotHeight B.V₀ (B.o.emb (y.2, 1)) * quotHeight J.W₀ y.1.1) ^ k :=
      (((continuous_quotHeight B.V₀).comp hgg).mul ((continuous_quotHeight J.W₀).comp hh1)).pow k
    refine Integrable.mono' (integrable_const (K₁ * K₂)) (hcc.norm.mul hq).aestronglyMeasurable
      (ae_of_all _ fun y => ?_)
    have q1 : 0 ≤ quotHeight B.V₀ (B.o.emb (y.2, 1)) := zero_le_one.trans (one_le_quotHeight _ _)
    have q2 : 0 ≤ quotHeight J.W₀ y.1.1 := zero_le_one.trans (one_le_quotHeight _ _)
    have b1 := hK₁ y.2 _ q1 (hC₁ y.2).2
    have b2 := hK₂ _ _ q2 (hC₂ y.1.2 y.1.2.2 y.1.1).1
    have n1 : ‖star (psiFlag ψ J.d (y.1.2 : GA D J.W))‖ = 1 := by
      rw [norm_star]; unfold psiFlag psiE; exact hψn _
    have p1 : 0 ≤ ‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k := by positivity
    have p2 : 0 ≤ ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k := by positivity
    rw [Real.norm_of_nonneg (by positivity), norm_mul, norm_mul, norm_mul, n1, hψn, mul_pow]
    calc ‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * 1 * ‖φ y.2‖ * 1 *
          (quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k * quotHeight J.W₀ y.1.1 ^ k)
        = (‖φ y.2‖ * quotHeight B.V₀ (B.o.emb (y.2, 1)) ^ k) *
          (‖G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1)‖ * quotHeight J.W₀ y.1.1 ^ k) := by ring
      _ ≤ K₁ * K₂ := mul_le_mul b1 b2 p2 (p1.trans b1)
  obtain ⟨hint, htame⟩ := _root_.GlobalTheory.KerTame.kernel_tame D ψ B.V₀ J.W₀ χ χ' om₀ hW ((GA D J.W₀ × flagN J.d) × GA D B.A)
    (((J.v0.μ.restrict J.v0.𝓕).prod (J.vN.ν.restrict J.vN.𝓝)).prod (B.vA.μ.restrict B.vA.𝓕))
    (fun y => G ((y.1.2 : GA D J.W) * J.d.emb0 y.1.1) * star (psiFlag ψ J.d (y.1.2 : GA D J.W)) * φ y.2 *
        ψ (cenT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    (fun y => B.o.emb (y.2, 1)) (fun y => y.1.1)
    (fun y => (B.o.resS J.W₀).symm (0, ptT J.d B.L (yZero B.L ρ B.ζ) (y.1.2 : GA D J.W)))
    hcc.measurable hgg hh1 hww key
  refine tame_congr hψ htame fun Ξ hΞ => ?_
  have hI := hint Ξ hΞ
  rw [MeasureTheory.integral_prod _ hI, MeasureTheory.integral_prod _ hI.integral_prod_left]
  simp only [JacL.perAll, fjAll, fjAllFun,
    GlobalTheory.Unf.fjKer_eq_om_apply D ψ J.W J.W₀ B.V₀ B.A B.L ρ J.d B.o B.ζ χ χ' om₀ hW Ξ hΞ,
    ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun n => ?_)
  refine MeasureTheory.integral_congr_ae (ae_of_all _ fun h₀ => ?_)
  dsimp only
  ring

end GlobalTheory.PerAllTame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessRealComponentsAdelicHom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.FourierRealPart

variable {D : D7}

theorem exists_section (θ : InfFam D) (hθ : IsInfFam θ) :
    ∃ s : (D.what₂.Tau → ℂ) → AE D, Continuous s ∧ (∀ w, finPart D (s w) = 0) ∧
      (∀ w τ, θ τ (infPart D (s w)) = w τ) ∧ (∀ a, infPart D (s fun τ => θ τ (infPart D a)) = infPart D a) ∧
      ∀ τ, Continuous fun a : AE D => θ τ (infPart D a) := by
  obtain ⟨e, he, hc, hc', -⟩ := GlobalTheory.Mem.VolInfIso.exists_infAdele_equiv D.host.F D.host.E D.sp.cm.sig D.what₂.Tau
    (tauE D) θ (Formalism.MainNotions.UnusedSlot34.isCMExt_D D) (GlobalTheory.CMTypePlaces.mk_tauE_bijective D) hθ
  obtain ⟨e1, he1, hc1, hc1'⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hinf : ∀ a : AE D, (e1 a).1 = infPart D a := fun a => (he1 a).1
  have hfin : ∀ a : AE D, (e1 a).2 = finPart D a := fun a => (he1 a).2
  refine ⟨fun w => e1.symm (e.symm w, 0), hc1'.comp (hc'.prodMk continuous_const), fun w => ?_, fun w τ => ?_,
    fun a => ?_, fun τ => ?_⟩
  · rw [← hfin, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply, ← he, RingEquiv.apply_symm_apply]
  · rw [← hinf, RingEquiv.apply_symm_apply]
    apply e.injective
    funext τ
    rw [RingEquiv.apply_symm_apply, he]
  · have h : (fun a : AE D => θ τ (infPart D a)) = fun a => e (e1 a).1 τ := by
      funext a
      rw [he, hinf]
    rw [h]
    exact (continuous_apply τ).comp (hc.comp (continuous_fst.comp hc1))

theorem dualPt_finPart {T : HSp D} {ρ : ℕ} {b : Mx D ρ T.rank} (hb : b.map (finPart D) = 0) :
    (GlobalTheory.Unf.DoubleSum.dualPt T ρ b).map (finPart D) = 0 := by
  have h : (b ⬝ giA T).map (finPart D) = 0 := by rw [Matrix.map_mul, hb, Matrix.zero_mul]
  funext i j
  refine GlobalTheory.OrientedChar.finPart_cA_eq_zero (z := incA D D.host.xi0⁻¹ * (b ⬝ giA T) j i) ?_
  rw [map_mul, show finPart D ((b ⬝ giA T) j i) = 0 from congrFun (congrFun h j) i, mul_zero]


set_option synthInstance.maxHeartbeats 400000 in
theorem psi_dualPt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (z : Mx D W.rank ρ) {b : Mx D ρ W.rank}
    (hb : b.map (finPart D) = 0) :
    ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * ∑ τ, ((2 * (∑ i, ∑ j,
        θ τ (infPart D (z i j)) * θ τ (infPart D (b j i))).re : ℝ) : ℂ)) := by
  rw [GlobalTheory.Unf.DoubleSum.symplO_dualPt]
  have hfin : finPart D (z * b).trace = 0 := GlobalTheory.PhaseReal.finPart_trace z b hb
  have hT := GlobalTheory.PhaseReal.trace_real hfin
  have h1 : ψ (Algebra.trace (AF D.host.F) (AE D) (z * b).trace) =
      psiInf D.host.F ψ (fstA D.host.F (Algebra.trace (AF D.host.F) (AE D) (z * b).trace)) := congrArg ψ hT
  rw [h1, hψ.2.2 θ hθ]
  congr 2
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [GlobalTheory.PhaseReal.theta_trace θ hθ τ]
  congr 3
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, map_sum, map_mul]

theorem linear_expand {K : Type} [Fintype K] [DecidableEq K] (l : (K → ℂ) →L[ℝ] ℝ) (Z : K → ℂ) :
    l Z = ∑ k, ((Z k).re * l (Pi.single k 1) + (Z k).im * l (Pi.single k Complex.I)) := by
  conv_lhs => rw [← Finset.univ_sum_single Z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : Pi.single k (Z k) = (Z k).re • (Pi.single k (1 : ℂ) : K → ℂ) + (Z k).im • (Pi.single k Complex.I : K → ℂ) := by
    ext k'
    by_cases h : k' = k
    · subst h
      simp [Complex.ext_iff]
    · simp [h]
  rw [e, map_add (f := _), map_smul, map_smul, smul_eq_mul, smul_eq_mul]

end GlobalTheory.FourierRealPart


open GlobalTheory.FourierRealPart in
theorem GlobalTheory.FourierRealPart.integral_preimage_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (Y : Type) [MeasurableSpace Y] (m : Measure Y) (F : Y → ℂ), Integrable F m → ∀ x : Y → Mx D W.rank ρ, Measurable x → (∀ c : Mx D W.rank ρ, c.map (finPart D) = 0 → ∫ y, ψ (symplO V W (d.extX W (x y)) (d.extY W c)) * F y ∂m = 0) → ∀ S : Set (Mx D W.rank ρ), MeasurableSet S → (∀ z z' : Mx D W.rank ρ, z.map (infPart D) = z'.map (infPart D) → (z ∈ S ↔ z' ∈ S)) → ∫ y in x ⁻¹' S, F y ∂m = 0 := by
  intro D ψ hψ V V₀ W ρ d Y _ m F hF x hx hc S hS hsat
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨s, hsc, hsf, hsθ, hsinf, hcθ⟩ := exists_section θ hθ
  haveI : BorelSpace (Mx D W.rank ρ) := ⟨rfl⟩
  classical
  let P : Mx D W.rank ρ → (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) := fun z k => θ k.2.2 (infPart D (z k.1 k.2.1))
  let sec : (Fin W.rank × Fin ρ × D.what₂.Tau → ℂ) → Mx D W.rank ρ := fun w i j => s fun τ => w (i, j, τ)
  have hP : Continuous P :=
    continuous_pi fun k => (hcθ k.2.2).comp ((continuous_apply k.2.1).comp (continuous_apply k.1))
  have hsec : Continuous sec :=
    continuous_pi fun i => continuous_pi fun j => hsc.comp (continuous_pi fun τ => continuous_apply _)
  have hmem : ∀ z, z ∈ S ↔ sec (P z) ∈ S := fun z => hsat _ _ (by
    funext i j
    exact (hsinf (z i j)).symm)
  have hpre : x ⁻¹' S = (P ∘ x) ⁻¹' (sec ⁻¹' S) := by
    ext y
    exact hmem (x y)
  rw [hpre]
  refine GlobalTheory.T.setIntegral_preimage_eq_zero_of_fourier_eq_zero Y m F hF _ (P ∘ x) (hP.measurable.comp hx) ?_ _ (hsec.measurable hS)
  intro l
  let B : Fin W.rank × Fin ρ × D.what₂.Tau → ℂ := fun k =>
    ((-(1 / (4 * Real.pi)) : ℝ) : ℂ) * ((l (Pi.single k 1) : ℂ) - (l (Pi.single k Complex.I) : ℂ) * Complex.I)
  let b : Mx D ρ W.rank := fun j i => s fun τ => B (i, j, τ)
  have hb : b.map (finPart D) = 0 := by
    funext j i
    exact hsf _
  have key := hc (GlobalTheory.Unf.DoubleSum.dualPt W ρ b) (dualPt_finPart hb)
  have hpt : ∀ z : Mx D W.rank ρ, Complex.exp ((l (P z) : ℂ) * Complex.I) =
      ψ (symplO V W (d.extX W z) (d.extY W (GlobalTheory.Unf.DoubleSum.dualPt W ρ b))) := by
    intro z
    rw [psi_dualPt hψ θ hθ d z hb]
    congr 1
    have hbθ : ∀ i j τ, θ τ (infPart D (b j i)) = B (i, j, τ) := fun i j τ => hsθ _ τ
    simp only [hbθ]
    have hterm : ∀ k, (P z k).re * l (Pi.single k 1) + (P z k).im * l (Pi.single k Complex.I) =
        -(4 * Real.pi) * (P z k * B k).re := by
      intro k
      have hπ := Real.pi_ne_zero
      simp only [B, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
        Complex.sub_im, Complex.I_re, Complex.I_im]
      field_simp
      ring
    have h1 : l (P z) = ∑ i, ∑ j, ∑ τ, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [linear_expand l (P z), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun τ _ => hterm _
    have h2 : -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re =
        ∑ τ, ∑ i, ∑ j, -(4 * Real.pi) * (θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      simp only [Complex.re_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have hr : l (P z) = -(2 * Real.pi) * ∑ τ, 2 * (∑ i, ∑ j, θ τ (infPart D (z i j)) * B (i, j, τ)).re := by
      rw [h1, h2]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
    rw [hr]
    push_cast
    ring
  simp only [Function.comp_apply, hpt]
  exact key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
section
namespace GlobalTheory

theorem geometricLemma_of_filtration :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration →
      GlobalTheory.Published.GeometricLemma := by
  intro hB hF k _ _ _ _
  exact ⟨hF k, _root_.GlobalTheory.SmGL.CellSemis.cellSemisimplification hB k⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergTranslateFockVacuumCauchyRiemannStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_fockVacuum_cauchyRiemann : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (f : WO S T → ℂ), GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ y : WO S T, Differentiable ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) ∧ ∀ w z : GlobalTheory.FockCompare.RW T S, fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w z + Complex.I * fderiv ℝ (fun w : GlobalTheory.FockCompare.RW T S => heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y) w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) = (Real.pi : ℂ) * Complex.I * ((GlobalTheory.VacUnique.omO S T w z : ℂ) + Complex.I * (GlobalTheory.VacUnique.omO S T w (GlobalTheory.VacUnique.jO S T A.cart B.cart z) : ℂ)) * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S w) f y := by
  first | exact @GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | exact GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann | (intros; apply GlobalTheory.HeisTranslCR.heis_translate_cauchy_riemann <;> assumption)
end

