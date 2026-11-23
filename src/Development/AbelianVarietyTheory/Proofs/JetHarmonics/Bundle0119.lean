module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0118
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0111
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumSupportRename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartLocalDepthLeOfValuedExtensionBoundStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_local_depth_le_of_valuedExtension_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (B : FB X.O (chD Ch.ch) (𝓞 E)), B.G.F = (fun i => MvPowerSeries.map X.ι (Ch.FT i)) → (∀ a, B.A.act a = fun i => MvPowerSeries.map X.ι (Ch.actT a i)) → ∀ (e k n : ℕ) (a : (E →+* ℂ) × ℕ → ℕ), 0 < e → ∀ (P : MvPolynomial (LtN Dw n) X.O), MvPolynomial.map (algebraMap X.O X.C) P ∈ HHa Dw.mult n X.C ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (f : PS X.O n (chD Ch.ch)) (A : ℝ), (X.v (p : X.C) : ℝ) ^ A ≤ (X.v (nabValN B X.C (letI := io.toAlgebra; MvPowerSeries.map X.ιF Ch.ch.h) H.w0 k (MvPowerSeries.map (algebraMap X.O X.C) f) (fun ℓ : LtN Dw n => ℓ.2.2) (fun (ℓ : LtN Dw n) i => algebraMap X.O X.C (X.ι (Ch.uvecT ⟨ℓ.1, ℓ.2.1⟩ i))) (MvPolynomial.map (algebraMap X.O X.C) P)) : ℝ) → nuLocC Ch e k a n ≤ (((vV T.V (p : T.Fr) : ℝ) / (e : ℝ) * A : ℝ) : EReal) := by
  first | exact @GlobalTheory.CharDepth.nuLocC_le_of_value_extension | exact GlobalTheory.CharDepth.nuLocC_le_of_value_extension | (intros; apply GlobalTheory.CharDepth.nuLocC_le_of_value_extension <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegral
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem theta_series_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 →
    Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  intro d q hq M ω θ hd h16 hs hL hM hθ
  obtain ⟨-, h2, -, h4, -⟩ := GlobalTheory.MomOne.okArith d q M.ι hd h16 hs
  obtain ⟨α, hα, hα1, hα2⟩ := h4 1 1 (Nat.coprime_one_left q)
  obtain ⟨⟨a, ha⟩, ⟨m, hm⟩, -⟩ := h2 α hα
  have hq1 : (q : ℝ) ^ (-((1 : ℕ) : ℤ)) < 1 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
    exact zpow_lt_one_of_neg₀ this (by norm_num)
  have hα1' : ‖M.ι α - 1‖ < 1 := by
    have := hα1.trans_lt hq1
    simpa using this
  have hn : ‖M.ι α‖ = 1 := by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := M.ι α - 1) (y := (1 : ℂ_[q]))
      (by rw [norm_one]; exact hα1'.ne)
    rw [sub_add_cancel, norm_one, max_eq_right hα1'.le] at h
    exact h
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hn
  have hmn : ‖(m : ℂ_[q])‖ < 1 := by
    have : (m : ℂ_[q]) = M.ι α * M.ι (conj α) := by
      rw [← map_mul, ← hm, map_natCast]
    rw [this, norm_mul, hn, one_mul]
    exact hα2.trans_lt hq1
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · exfalso
      have : α * conj α = 0 := by rw [← hm]; simp
      rcases mul_eq_zero.1 this with h | h
      · exact hα0 h
      · exact hα0 (by simpa using h)
    · simp at hmn
    · omega
  obtain ⟨ε, -, hεa, -, hεb, hfe, -⟩ := _root_.GlobalTheory.MomOne.ThetaQuot.theta_quot d q M ω θ hd h16 hs hL hM hθ α m hα hα0 hm
  obtain ⟨hmul, -⟩ := GlobalTheory.MomOne.MulSeries.mulS_laws q
  obtain ⟨hb, hc0, hc1, -⟩ := hmul a
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [map_mul]
    have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]; simp [logS]
    rw [this, mul_zero]
  obtain ⟨hring, hconst, -, hcc, -⟩ := GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  have hθa : ∀ z, AnalyticAt ℂ θ z := fun z => hθ.1.analyticAt z
  have hpow : ∀ k : ℕ, hat M.ι (C ω * logS) (fun z => θ z ^ k) = hat M.ι (C ω * logS) θ ^ k := by
    intro k
    induction k with
    | zero => simpa using hconst 1
    | succ k ih =>
      have := (hring (fun z => θ z ^ k) θ ((hθa 0).pow k) (hθa 0)).2.1
      simp only [pow_succ]
      rw [this, ih]
  have hsub := (GlobalTheory.MomOne.hat_multiplicative_chart q M.ι ω θ (hθa 0)).2.2.1 α a ha
  have hne : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 :=
    (hθa 0).continuousAt.eventually_ne (by rw [hθ.2.1]; exact one_ne_zero)
  have hαa : AnalyticAt ℂ (fun z => θ (α * z)) 0 :=
    (hθ.1.comp (by fun_prop : Differentiable ℂ (fun z : ℂ => α * z))).analyticAt 0
  have heq := (hring (fun z => θ (α * z)) (fun z => θ z ^ m * ε z) hαa (((hθa 0).pow m).mul hεa)).2.2.1
    ((hne.mono fun z hz => hfe z hz).filter_mono nhdsWithin_le_nhds)
  rw [hsub, (hring (fun z => θ z ^ m) ε ((hθa 0).pow m) hεa).2.1, hpow] at heq
  refine (GlobalTheory.MomOne.FeUniq.funEq_unique q (mulS a) m hc0 (by rw [hc1, ← ha, hn]) hmn hm2).2 _ _ hb hεb ?_ heq
  rw [hcc, hθ.2.1, map_one]

end GlobalTheory.MomOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundOfTwoSteps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

noncomputable section

namespace GlobalTheory.DepthLink

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem finrank_host (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

end GlobalTheory.DepthLink
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ErealLeMulOfForallLe
section
set_option autoImplicit false

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GoodDepth

theorem ramOverZ_ne_zero' {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) :
    ramOverZ la ≠ 0 := by
  have hl := Formalism.L2.Pj.Crude.resCharOf_prime la
  have hne0 : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ la.asIdeal.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 K) ((resCharOf la : ℕ) : ℤ) ∈ la.asIdeal
    rw [map_natCast]
    exact Formalism.L2.Pj.Crude.crv_char_mem la
  have hne : la.asIdeal.under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ la.asIdeal.under ℤ := by rw [h]; trivial
    change algebraMap ℤ (𝓞 K) 1 ∈ la.asIdeal at h1
    rwa [map_one] at h1
  have : la.asIdeal.LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := ⟨hmax.eq_of_le hne hle⟩
  exact Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver la.asIdeal hne0

theorem ereal_le_mul_of_forall_le {x : EReal} {e B : ℝ} (he : 0 < e)
    (h : ∀ ν : ℝ, ((e * ν : ℝ) : EReal) ≤ x → ν ≤ B) : x ≤ ((e * B : ℝ) : EReal) := by
  by_contra hx
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 (not_le.1 hx)
  have h1 : r / e ≤ B := h (r / e) (by rw [mul_div_cancel₀ _ he.ne']; exact hr2.le)
  have h2 : e * B < r := by exact_mod_cast hr1
  rw [div_le_iff₀ he] at h1
  linarith [mul_comm e B]

theorem nuW_bound_of_charts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (lv : Level H) (Xo : Moduli Dw lv) (c : Coeff lv) [StarRing (𝓞 E)], IntChartEx Xo c →
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (B : ℝ), 0 ≤ B →
  (∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg → ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e k a n → ν ≤ B) →
  nuW Xo c la k a n ≠ ⊤ ∧ (nuW Xo c la k a n).toReal / (ramOverZ la : ℝ) ≤ B ∧ (B = 0 → nuW Xo c la k a n = 0) := by
  intro E _ _ _ H Dw lv Xo c _ hEx la k a n B hB h
  have he : (0 : ℝ) < (ramOverZ la : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (ramOverZ_ne_zero' la)
  have hsup : nuSup Xo c la k a n ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal) := by
    unfold nuSup
    refine iSup_le fun T => iSup_le fun io => iSup_le fun e => iSup_le fun hO => iSup_le fun y =>
      iSup_le fun hy => ?_
    obtain ⟨C⟩ := hEx T io y hy
    exact (iInf_le (fun C : IntChart T io y => nuLocC C e k a n) C).trans
      (ereal_le_mul_of_forall_le he (h T io e hO y hy C))
  have h0 : (0 : ℝ) ≤ (ramOverZ la : ℝ) * B := mul_nonneg he.le hB
  have hW : nuW Xo c la k a n ≤ (((ramOverZ la : ℝ) * B : ℝ) : EReal) :=
    max_le (by exact_mod_cast h0) hsup
  have hW0 : 0 ≤ nuW Xo c la k a n := le_max_left _ _
  refine ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _) hW, ?_, fun hB0 => ?_⟩
  · rw [div_le_iff₀ he, mul_comm]
    have := EReal.toReal_le_toReal hW (ne_bot_of_le_ne_bot EReal.zero_ne_bot hW0) (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  · rw [hB0, mul_zero, EReal.coe_zero] at hW
    exact le_antisymm hW hW0

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicElementOfMarkedComponentLattice
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open scoped Matrix nonZeroDivisors
open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_marked_of_component : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (D.host.E →+* ℂ)) (F : FamilyUnif Xo σ' ty), IsTypeFn H Dw.p Dw.q ty → ∀ (r : ℕ) (hr : V.rank = r) (X : Data D.host.E r) (i : Fin F.n) (φ : (F.Di i).La ≃ₗ[𝓞 D.host.E] X.Λ) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), ModelW V hr X → (∀ a b, (((F.Di i).EF a b : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-X.ξ0 * herm X.Gm (φ a : Fin r → D.host.E) (φ b))) → LatEmb V io → FormPlus V io → ∃ h : GA D V, Marked V hr io l X.Λ (fun a => (φ (F.t i a) : Fin r → D.host.E)) h := by
  intro D V H Dw l Xo σ' g ty F hty r hr X k φ io hW hef hemb hform
  subst hr
  obtain ⟨hinj, hrange⟩ := hemb
  have hEF : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) *
      herm (gmW V rfl) (io x) (io y)) := by
    intro x y
    have h := trace_herm_gmW V rfl (V.frame.equivFun.symm (io x)) (V.frame.equivFun.symm (io y))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    rw [hform, neg_neg, ← h]
    rfl
  obtain ⟨-, P, hP⟩ := (PeriodExists.typeFn_period_exist _ H (F.Di k)).2.1 g ty
    (by rw [(F.sig k).1, (F.sig k).2]; exact hty)
  obtain ⟨f, h1, h2, h3, h4⟩ := familyUnif_lattice_genus _ H Dw l Xo σ' g ty F k P hP
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : -(-D.host.xi0) ≠ 0 := by
    rw [← hW.2]
    exact neg_ne_zero.2 X.ξ0_ne
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    (-(-D.host.xi0)) hξ Dw.La (F.Di k).La (fun x y => Dw.EF x y) (fun x y => (F.Di k).EF x y) io hinj
    X.Λ φ hfg hsp X.Λ_fg X.Λ_span hEF
    (fun x y => by
      have := hef x y
      rw [hW.1, hW.2] at this
      exact this) f h1 h2 h3
  obtain ⟨u, hu, hug⟩ := (_root_.GlobalTheory.UnitaryGlue.adelic_glue D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have hc := (AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank X.Λ X.Λ_fg
    X.Λ_span).1
  refine ⟨u, ?_, fun a ha => ?_⟩
  · rw [(hlat u).1, hug]
    refine Eq.trans ?_ (Set.image_id _).symm
    ext v
    rw [AdLat.latOf, hg1]
    exact (hc v).symm
  · obtain ⟨e, he⟩ := h4 a ha
    obtain ⟨w, hw, hgw⟩ := hg2 l.M (lt_of_lt_of_le (by norm_num) l.three_le) a
    have hmem : ∀ z, z ∈ latGHat V u ↔ z ∈ AdLat.hat D.host.F (X.Λ : Set (Fin V.rank → D.host.E)) := by
      intro z
      rw [← SetLike.mem_coe, (hlat u).2, hug, hg1, SetLike.mem_coe]
    rw [hug]
    refine ⟨-(AdLat.fv D.host.F (φ e : Fin V.rank → D.host.E) + w),
      (hmem _).2 (neg_mem (add_mem ((hc _).2 (φ e).2) hw)), ?_⟩
    change AdLat.fv D.host.F (φ (F.t k a) : Fin V.rank → D.host.E) - gf.1 *ᵥ AdLat.fv D.host.F (io a) = _
    rw [hgw, he, map_add (f := _), map_nsmul, Submodule.coe_add, Submodule.coe_smul_of_tower, AdLat.cap_fv_add,
      AdLat.cap_fv_nsmul]
    exact comp_sub_eq _ _ _ _

end GlobalTheory.ShortMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAdelicUnitaryOfLatticeIsometries
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open GlobalTheory.ShortMove

namespace GlobalTheory.ShortMove

open GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_adelic_of_isometry : ∀ (D : D7) (V : HSp D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), LatEmb V io → FormPlus V io → ∀ s : Sim Dw, (∀ n, s.ν n = 1) → ∃ κ : GA D V, latGHat V κ = latGHat V 1 ∧ ∀ N : ℕ, 0 < N → ∀ a, ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (io a)) = finVec V (io (s.f N a)) + N • w := by
  intro D V H Dw io hio hEF s hν
  obtain ⟨hinj, hrange⟩ := hio
  let c : D.host.E ≃ₐ[D.host.F] D.host.E :=
    AlgEquiv.ofAlgHom D.sp.cm.sig D.sp.cm.sig (AlgHom.ext fun x => star_star x) (AlgHom.ext fun x => star_star x)
  obtain ⟨hfg, hsp, hlat⟩ := comp_latG D V
  rw [← hrange] at hfg hsp hlat
  have hξ : D.host.xi0 ≠ 0 := by
    have h1 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 D.host.ccK_ne_bot)
    have h2 : D.host.sqrtMinusD ≠ 0 := by
      intro h
      have := D.host.sqrtMinusD_sq
      rw [h] at this
      have hd : (D.host.d : D.host.E) ≠ 0 := by
        have := D.host.qd_big.2
        exact_mod_cast (by omega : D.host.d ≠ 0)
      apply hd
      linear_combination this
    exact div_ne_zero (by norm_num) (mul_ne_zero h1 h2)
  have hA : ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 *
      ∑ a, ∑ b, io x a * (-V.gram.transpose) a b * c (io y b)) := by
    intro x y
    rw [hEF, ← trace_herm_gmW V rfl, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    rfl
  obtain ⟨gf, hg1, hg2, hg3⟩ := comp_adelic_of_tower D.host.F D.host.E V.rank c (-V.gram.transpose)
    D.host.xi0 hξ Dw.La Dw.La (fun x y => Dw.EF x y) (fun x y => Dw.EF x y) io hinj
    (LinearMap.range io) (LinearEquiv.ofInjective io hinj) hfg hsp hfg hsp hA hA s.f
    (fun n m hn hm a => by
      obtain ⟨e, he⟩ := s.tower n m hn hm a
      exact ⟨e, by rw [← he, add_sub_cancel]⟩)
    (fun n hn => by
      obtain ⟨g, hg⟩ := s.inv n hn
      refine ⟨fun a => ⟨?_, ?_⟩, fun a' => ?_⟩
      · rintro ⟨e, he⟩
        obtain ⟨b, hb⟩ := (hg a).1
        exact ⟨g e - b, by rw [smul_sub, ← hb, he, map_nsmul, sub_sub_cancel]⟩
      · rintro ⟨e, he⟩
        exact ⟨s.f n e, by rw [he, map_nsmul]⟩
      · obtain ⟨b, hb⟩ := (hg a').2
        exact ⟨g a', -b, by rw [smul_neg, ← hb, neg_sub, add_sub_cancel]⟩)
    (fun n hn a a' => by
      have := s.mult n hn a a'
      rwa [hν, one_mul] at this)
  obtain ⟨u, -, hug⟩ := (_root_.GlobalTheory.UnitaryGlue.adelic_glue D V).1 gf (comp_mem_HR _ _ _ c _ (fun _ => rfl) _ gf hg3)
  have h1 : (latGHat V 1 : Set (Fin V.rank → AdLat.RA D.host.F D.host.E)) =
      AdLat.hat D.host.F (LinearMap.range io : Set (Fin V.rank → D.host.E)) := by
    rw [(hlat 1).2, map_one, Units.val_one]
    ext z
    simp
  refine ⟨u, SetLike.coe_injective ?_, fun N hN a => ?_⟩
  · rw [(hlat u).2, hug, hg1, h1]
  · obtain ⟨w, hw, hgw⟩ := hg2 N hN a
    refine ⟨w, ?_, ?_⟩
    · rw [← SetLike.mem_coe, h1]
      exact hw
    · rw [hug]
      exact hgw

end GlobalTheory.ShortMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharacterGermValuationEqColumnTyped
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharValue

local notation "linPart" => _root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart

def ballIdeal {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) (t : NNReal) (ht : 0 < t) : Ideal O where
  carrier := {y | v (algebraMap O C y) < t}
  zero_mem' := by simpa using ht
  add_mem' := by
    intro a b ha hb
    show v (algebraMap O C (a + b)) < t
    rw [map_add (f := _)]
    exact v.map_add_lt ha hb
  smul_mem' := by
    intro c a ha
    show v (algebraMap O C (c * a)) < t
    rw [map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) ha

def letterEquiv (Ty : Type) (r : Ty → ℕ) (n : ℕ) : (Σ τ : Ty, Fin (r τ)) × Fin n ≃ Letter Ty r n where
  toFun p := ⟨p.1.1, (p.1.2, p.2)⟩
  invFun l := (⟨l.1, l.2.1⟩, l.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem dAct_mulVec {R : Type} [CommRing R] {d : ℕ} {OE : Type} [CommRing OE] [StarRing OE] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d OE) (a : OE) (u : Fin d → R) (s : R)
    (hu : (linPart (B.A.act a)).mulVec u = s • u) :
    (TB.dAct k B a).mulVec (fun i => algebraMap R k (u i)) = algebraMap R k s • (fun i => algebraMap R k (u i)) := by
  funext i
  have h := congrArg (algebraMap R k) (congrFun hu i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.linPart, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply,
    smul_eq_mul] at h
  simp only [Matrix.mulVec, dotProduct, TB.dAct, FB.actK, MvPowerSeries.coeff_map, Pi.smul_apply, smul_eq_mul]
  exact h

theorem map_boxSer {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {n d : ℕ} (g : Fin n → PS R 1 d) :
    MvPowerSeries.map φ (PowGerm.boxSer g) = PowGerm.boxSer (fun b => MvPowerSeries.map φ (g b)) := by
  unfold PowGerm.boxSer
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ => (MvPowerSeries.rename_map _ φ (g b)).symm

theorem exists_germ_valuation_eq : ∀ (C : Type) [Field C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d : ℕ) (OE : Type) [CommRing OE] [StarRing OE] (B : FB O d OE) (h : PS C 2 d), B.IsCanonGauge C h → ∀ (w0 : OE) (k n : ℕ) (Ty : Type) [Fintype Ty] (r : Ty → ℕ) [Fintype (Letter Ty r n)] (σ : Ty → (OE →+* O)) (u : (Σ τ : Ty, Fin (r τ)) → Fin d → O), (∀ ℓ a, (linPart (B.A.act a)).mulVec (u ℓ) = σ ℓ.1 a • u ℓ) → (∀ τ, ∃ a0, IsUnit (σ τ a0 - σ τ (star a0))) → (∀ x : O, x ≠ 0 → ∃ N : ℕ, v (N : C) < v (algebraMap O C x) ∧ ∀ τ, ∃ a : OE, star a * a = (N : OE) ∧ v (algebraMap O C (σ τ a - 1)) < v (algebraMap O C x)) → ∀ (ty : Fin n → Ty) (P : MvPolynomial (Letter Ty r n) O), (∀ mo ∈ P.support, ∀ ℓ, mo ℓ ≠ 0 → ℓ.1 = ty ℓ.2.2) → ∀ χ : Fin n → PS O 1 d, (∀ b, IsCh B.G.F (χ b)) → MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P ≠ 0 → ∃ f : PS O n d, v (nabValN B C h w0 k (MvPowerSeries.map (algebraMap O C) f) (fun ℓ : Letter Ty r n => ℓ.2.2) (fun (ℓ : Letter Ty r n) i => algebraMap O C (u ⟨ℓ.1, ℓ.2.1⟩ i)) (MvPolynomial.map (algebraMap O C) P)) = v (algebraMap O C (MvPolynomial.eval (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) P)) := by
  intro C _ _ v O _ _ hv d OE _ _ B h hg w0 k n Ty _ r _ σ u hu h0 hN ty P hP χ hχ hx
  classical
  obtain ⟨P', rfl⟩ : ∃ P', P = MvPolynomial.rename (letterEquiv Ty r n) P' :=
    ⟨MvPolynomial.rename (letterEquiv Ty r n).symm P, by simp [MvPolynomial.rename_rename]⟩
  rw [MvPolynomial.eval_rename] at hx ⊢
  set y : (Σ τ : Ty, Fin (r τ)) × Fin n → O :=
    (fun ℓ : Letter Ty r n => ∑ j, u ⟨ℓ.1, ℓ.2.1⟩ j * dl (χ ℓ.2.2) j) ∘ (letterEquiv Ty r n) with hy
  set x : O := MvPolynomial.eval y P' with hxdef
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hx0 : 0 < v (algebraMap O C x) := by
    rw [pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact fun e => hx (hinj (by rw [e, map_zero]))
  obtain ⟨N, hNlt, ha⟩ := hN x hx
  choose a ha1 ha2 using ha
  have hh : MvPowerSeries.constantCoeff h = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [TB.WickVanishing.gt_const_ev_eq _ (TB.WickVanishing.pair_points_zero_constant TB.WickVanishing.gp_zero₂ (TB.WickVanishing.gp_pt 0)), map_zero] at this
  obtain ⟨g, ρ, hρ, hsum⟩ := _root_.GlobalTheory.nabVal_character_columns_of_canonGauge O d OE C B h hg hinj w0 N k n (ballIdeal hv _ hx0)
    (by show v (algebraMap O C (N : O)) < _; rwa [map_natCast]) (fun b => a (ty b)) (fun _ => 1)
    (fun b => by rw [ha1, mul_one]) (Σ τ : Ty, Fin (r τ)) u (fun b => {l | l.1 = ty b})
    (fun b l => σ l.1 (a (ty b)))
    (fun b l hl => by
      have hl' : l.1 = ty b := hl
      have h2 : v (algebraMap O C (σ l.1 (a (ty b)) - 1)) < v (algebraMap O C x) := by
        rw [hl']; exact ha2 _
      refine ⟨h2, ?_, dAct_mulVec C B _ _ _ (hu l _)⟩
      apply hv.isUnit_of_one'
      have h3 := v.map_one_add_of_lt (lt_of_lt_of_le h2 (hv.map_le_one x))
      rwa [map_sub, map_one, add_sub_cancel] at h3)
    (fun b l hl l' hl' => by
      have e1 : l.1 = ty b := hl
      have e2 : l'.1 = ty b := hl'
      obtain ⟨a0, ha0⟩ := h0 (ty b)
      exact _root_.GlobalTheory.CharDepth.eigen_pair_mem_range O d OE C B h hg (σ (ty b)) a0 ha0 (u l) (u l') (fun c => e1 ▸ hu l c)
        (fun c => e2 ▸ hu l' c) _)
    χ y (fun b => (hχ b).1)
    (fun b l _ => GlobalTheory.MultiplicativeSeries.main O d B.G (χ b) (hχ b).2 (u l))
    P' (fun mo hmo l b hne => by
      have hmem : Finsupp.mapDomain (letterEquiv Ty r n) mo ∈
          (MvPolynomial.rename (letterEquiv Ty r n) P').support := by
        rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_rename_mapDomain _ (letterEquiv Ty r n).injective]
        exact MvPolynomial.mem_support_iff.1 hmo
      exact hP _ hmem (letterEquiv Ty r n (l, b))
        (by rwa [Finsupp.mapDomain_apply_of_injective (letterEquiv Ty r n).injective]))
  refine ⟨PowGerm.boxSer g, ?_⟩
  rw [map_boxSer, MvPolynomial.map_rename,
    GlobalTheory.nabValN_boxSer O d OE B C h w0 hh k n _ (Σ τ : Ty, Fin (r τ)) (Letter Ty r n) (letterEquiv Ty r n) _
      (fun l i => algebraMap O C (u l i)) _ (fun _ => rfl) (fun _ => rfl),
    MvPolynomial.support_map_of_injective _ hinj]
  simp only [MvPolynomial.coeff_map]
  rw [hsum, map_add (f := _)]
  exact v.map_add_eq_of_lt_left hρ

end GlobalTheory.CharValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFlagCharactersLeadingMinorsColengthStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_characters_leading_minors_colength : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ (d s : ℕ) (F : Fin d → PS O 2 d) (w : Fin s → Fin d → O) (x : NNReal), HasAF v F w x → x ≠ 0 → x ≤ 1 ∧ ∃ χ : Fin s → PS O 1 d, (∀ b, IsCh F (χ b)) ∧ ∀ i : Fin s, x ≤ v (algebraMap O C (Matrix.of fun a b : Fin (i.val + 1) => ∑ j, w (Fin.castLE i.isLt a) j * dl (χ (Fin.castLE i.isLt b)) j).det) := by
  first | exact @GlobalTheory.CharDepth.exists_flag_characters | exact GlobalTheory.CharDepth.exists_flag_characters | (intros; apply GlobalTheory.CharDepth.exists_flag_characters <;> assumption)
end

