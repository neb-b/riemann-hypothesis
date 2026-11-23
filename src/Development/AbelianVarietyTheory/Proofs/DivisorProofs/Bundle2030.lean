module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1974
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFundamentalSetConjFiniteIndexSubgroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1987
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsBoundedOutsideCmTypeOfDefiniteArcLift
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.PerLim

theorem tendsto_of_inv_mulVec_span {α : Type} {l : Filter α} {N n : ℕ} (M : α → Matrix (Fin N) (Fin N) ℂ)
    (u : Fin n → Fin N → ℂ) (L : Fin n → Fin N → ℂ) (hdet : ∀ᶠ w in l, (M w).det ≠ 0)
    (ht : ∀ j, Tendsto (fun w => Matrix.mulVec (M w)⁻¹ (u j)) l (𝓝 (L j)))
    (hs : Submodule.span ℂ (Set.range L) = ⊤) : ∃ L0, Tendsto M l (𝓝 L0) := by
  have hc : ∀ a : Fin N, ∃ c : Fin n → ℂ, ∑ j, c j • L j = Pi.single a 1 := fun a =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hs ▸ Submodule.mem_top)
  choose c hc using hc
  let W : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun b a => ∑ j, c a j * u j b
  have hR : Tendsto (fun w => (M w)⁻¹ * W) l (𝓝 1) := by
    refine tendsto_pi_nhds.2 fun a' => tendsto_pi_nhds.2 fun a => ?_
    have e : ∀ w, ((M w)⁻¹ * W) a' a = ∑ j, c a j * (Matrix.mulVec (M w)⁻¹ (u j)) a' := by
      intro w
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, W, Matrix.of_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => by ring
    have lim : (1 : Matrix (Fin N) (Fin N) ℂ) a' a = ∑ j, c a j * L j a' := by
      have := congrFun (hc a) a'
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, Pi.single_apply, Matrix.one_apply]
    simp only [e]
    rw [lim]
    exact tendsto_finsetSum _ fun j _ => ((ht j).apply_nhds a').const_mul _
  have hRi : Tendsto (fun w => ((M w)⁻¹ * W)⁻¹) l (𝓝 1) := by
    have h0 : ContinuousAt Ring.inverse (1 : Matrix (Fin N) (Fin N) ℂ).det := by
      rw [Matrix.det_one, Ring.inverse_eq_inv']
      exact continuousAt_inv₀ one_ne_zero
    have h1 := ((continuousAt_matrix_inv (1 : Matrix (Fin N) (Fin N) ℂ) h0).tendsto).comp hR
    rw [inv_one] at h1
    exact h1
  have hRd : ∀ᶠ w in l, ((M w)⁻¹ * W).det ≠ 0 := by
    have h1 : Tendsto (fun w => ((M w)⁻¹ * W).det) l (𝓝 (1 : Matrix (Fin N) (Fin N) ℂ).det) :=
      ((Continuous.matrix_det continuous_id).tendsto (1 : Matrix (Fin N) (Fin N) ℂ)).comp hR
    rw [Matrix.det_one] at h1
    exact h1.eventually_ne one_ne_zero
  refine ⟨W, ?_⟩
  have hlim : Tendsto (fun w => W * ((M w)⁻¹ * W)⁻¹) l (𝓝 (W * 1)) :=
    ((continuous_const.matrix_mul continuous_id).tendsto _).comp hRi
  rw [Matrix.mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [hdet, hRd] with w h1 h2
  have e1 : M w * ((M w)⁻¹ * W) = W := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.one_mul]
  calc W * ((M w)⁻¹ * W)⁻¹ = M w * ((M w)⁻¹ * W) * ((M w)⁻¹ * W)⁻¹ := by rw [e1]
    _ = M w := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h2), Matrix.mul_one]

theorem periods_bounded_outside_cmType_of_definite_arc_lift_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (N : ℕ) (U : Unf Xo c σ N) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)) (k : U.Comp) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (xx : ℂ → Frame (U.X k).Ψ N), GoodEmb c σ → IsUnf U → IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → IsOrbit (U.X k) T M γ xx → IsLift U k y T xx → (U.X k).p0 = 0 → ∀ v : Fin N → E, ∃ C : ℝ, ∀ᶠ w in imTop, ∀ (τ : E →+* ℂ) (i : ℕ), τ ∉ (U.X k).Ψ → ‖perFr (U.X k) (xx w) v τ i‖ ≤ C := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ N U A _ φ x fr ψ r y k T M γ xx hσ hU harc hm horb hlift hp0 v
  obtain ⟨n, vv, Lp, Lm, hLp, -, hsp⟩ := GlobalTheory.ShFam.PerLim.exists_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x
    fr ψ r y k T M γ xx hσ hU harc hm horb hlift
  have hdom : ∀ᶠ w in imTop, xx w ∈ (U.X k).dom := by
    filter_upwards [(tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)] with w hw
    exact horb.2.2.2.1 w hw
  have hmat : ∀ τ' : (U.X k).Ψ, ∃ L0, Tendsto (fun w => mat (xx w) τ') imTop (𝓝 L0) := by
    intro τ'
    refine tendsto_of_inv_mulVec_span (fun w => mat (xx w) τ') (fun j => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 (vv j))
      (fun j i => Lp j τ' ⟨i, by omega⟩) ?_ ?_ ?_
    · filter_upwards [hdom] with w hw
      exact (hw τ').1
    · intro j
      refine tendsto_pi_nhds.2 fun i => ?_
      have hi : (i : ℕ) < N - (U.X k).p0 := by omega
      refine (hLp j τ' ⟨i, hi⟩).congr fun w => ?_
      unfold perFr
      rw [dite_eq_left τ'.2, dite_eq_left (by simp only [hp0]; omega)]
      congr 1
      ext
      simp [hp0]
    · exact span_proj (fun j => Lp j τ') (hsp τ').1 (fun i => ⟨i, by omega⟩)
        (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  choose L0 hL0 using hmat
  let F : ℂ → ((U.X k).Ψ → Fin N → ℂ) := fun w τ' a =>
    ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (mat (xx w) τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v)
  have hF : Tendsto F imTop (𝓝 (fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v))) := by
    refine tendsto_pi_nhds.2 fun τ' => tendsto_pi_nhds.2 fun a => ?_
    have hc : Continuous fun Mx : Matrix (Fin N) (Fin N) ℂ =>
        ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col Mx a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.hermC col
      fun_prop
    exact (hc.tendsto _).comp (hL0 τ')
  refine ⟨‖(fun τ' a =>
      ReciprocityTheory.ChartRestriction.G.FD.hermC τ'.1 (U.X k).Gm (col (L0 τ') a) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ'.1 v) :
      (U.X k).Ψ → Fin N → ℂ)‖ + 1, ?_⟩
  filter_upwards [hF.norm.eventually (gt_mem_nhds (lt_add_one _))] with w hw
  intro τ i hτ
  unfold perFr
  rw [dite_eq_right hτ]
  split_ifs with h' hj
  · exact ((norm_le_pi_norm (F w ⟨_, h'⟩) ⟨_, hj⟩).trans (norm_le_pi_norm (F w) ⟨_, h'⟩)).trans hw.le
  · simp only [norm_zero]; positivity
  · simp only [norm_zero]; positivity

end GlobalTheory.ShFam.PerLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonLevelCoverPullbackProbability
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

noncomputable section

namespace GlobalTheory.LevPullNorm

theorem sum_mul_fibre {ι κ : Type} [Fintype ι] [Fintype κ] (π : ι → κ) (w : ι → ℕ) (N : ℕ) (I : κ → ℝ≥0∞)
    (h : ∀ k, ∑ᶠ i : {i // π i = k}, w i.1 = N) : ∑ i, (w i : ℝ≥0∞) * I (π i) = N * ∑ k, I k := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ π, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := h k
  rw [finsum_eq_sum_of_fintype] at hk
  rw [← hk, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_subtype _ (p := fun i => π i = k) (by simp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [i.2]

theorem goodEmb_comp_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) :
    GoodEmb c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) ↔ GoodEmb d.c₂ σ₂ := by
  unfold GoodEmb
  rfl

theorem frame_tr {E : Type} [Field E] {r : ℕ} {A B : Finset (E →+* ℂ)} (h : A = B) (x : Frame A r) (ρ : E →+* ℂ)
    (h₁ : ρ ∈ B) (h₂ : ρ ∈ A) : (h ▸ x : Frame B r) ⟨ρ, h₁⟩ = x ⟨ρ, h₂⟩ := by
  subst h; rfl

theorem relab_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (τ : d.c₂.F →+* ℂ) :
    relab c (τ.comp (d.eF : c.F →+* d.c₂.F)) = relab d.c₂ τ := by
  funext ρ
  ext a
  rfl

theorem goodOf_eF (D : D7) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (d : DeltaDat Xo c 0) (σ₂ : d.c₂.F →+* ℂ) :
    goodOf c (σ₂.comp (d.eF : c.F →+* d.c₂.F)) = (goodOf d.c₂ σ₂).comp (d.eF : c.F →+* d.c₂.F) := by
  unfold goodOf
  by_cases h : GoodEmb d.c₂ σ₂
  · rw [if_pos ((goodEmb_comp_eF D d σ₂).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((goodEmb_comp_eF D d σ₂).1 h')), if_neg h]
    rfl

theorem pnorm_lact_transport : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (δ : GL (Fin r) E) (la : Wt X.Ψ r) (la' : Wt X'.Ψ r) (P : Frame X.Ψ r → ℂ) (P' : Frame X'.Ψ r → ℂ) (t : ℂ) (n : ℕ), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ v w, herm X.Gm ((δ : Matrix (Fin r) (Fin r) E).mulVec v) ((δ : Matrix (Fin r) (Fin r) E).mulVec w) = herm X.Gm v w) → (∀ (τ : E →+* ℂ) (h : τ ∈ X'.Ψ) (i : Fin r), la' ⟨τ, h⟩ i = la ⟨τ, hΨ ▸ h⟩ i) → ‖t‖ = 1 → (∀ x ∉ X'.dom, P' x = 0) → (∀ x ∉ X.dom, P x = 0) → (∀ x ∈ X'.dom, P' x = t ^ n * P (lact δ (hΨ ▸ x))) → ∀ y : Frame X'.Ψ r, X'.pnorm la' P' y = X.pnorm la P (lact δ (hΨ ▸ y)) := by
  intro E _ _ _ r X X' hΨ δ la la' P P' t n hG hp hu hla ht h0' h0 hrel y
  cases X'
  cases hΨ
  cases hG
  cases hp
  have hla' : la' = la := funext fun τ => funext fun i => hla τ.1 τ.2 i
  subst hla'
  have hun : GlobalTheory.SW.IsUn X δ := hu
  have hd : ∀ (z : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)), dmin X.Gm (lact δ z) τ i = dmin X.Gm z τ i :=
    fun z τ i => GlobalTheory.Dict.Extend.dmin_lact hun z τ i
  have hdom : ∀ z : Frame X.Ψ r, lact δ z ∈ X.dom → z ∈ X.dom := by
    intro z hz τ
    refine ⟨fun h => (hz τ).1 ?_, fun i => by rw [← hd z τ i]; exact (hz τ).2 i⟩
    show ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat z τ).det = 0
    rw [Matrix.det_mul, h, mul_zero]
  show _ = X.pnorm _ P (lact δ y)
  unfold Data.pnorm
  by_cases hy : y ∈ X.dom
  · rw [hrel y hy, norm_mul, norm_pow, ht, one_pow, one_mul]
    refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun i _ => ?_)
    rw [hd, hd]
  · have hy' : lact δ y ∉ X.dom := fun h => hy (hdom y h)
    rw [h0' y hy, h0 _ hy', norm_zero, zero_mul, zero_mul]

theorem petE_sq_mul_vol : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r), Laws D j Xo c U dict → ∀ σ, GoodEmb c σ → ∀ (G : WTZ D.host.E) (f : Rul Xo c), f ∈ cuspW Xo c U G → ∀ (x0 : ∀ k, Frame ((U σ).X k).Ψ D.R.r) (FF : ∀ k, Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), (∀ k, IsOrth ((U σ).X k) (x0 k) ∧ IsFundSet ((U σ).X k) (x0 k) (FF k)) → (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ 0 ∧ (∑ k, muF ((U σ).X k) (x0 k) (FF k)) ≠ ⊤ ∧ petE (D.sp.W j) (dict σ) (muQ1 (D.sp.W j)) (modelWt (U σ) G) (rdU (U σ) f) ^ 2 * ∑ k, muF ((U σ).X k) (x0 k) (FF k) = ∑ k, ∫⁻ z in FF k, ENNReal.ofReal (((U σ).X k).pnorm (modelWt (U σ) G k) (rdU (U σ) f k) (cpt ((U σ).X k) (x0 k) z) ^ 2) ∂(muF ((U σ).X k) (x0 k)) := by
  intro D j H Dw l Xo c U dict hL σ hσ G f hf x0 FF hx
  have hsf : ∀ k, ((U σ).X k).IsSec (modelWt (U σ) G k) (rdU (U σ) f k) := fun k =>
    GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ ((mem_cuspW.1 hf).2 σ hσ) k
  obtain ⟨h0, hT, hI⟩ := _root_.GlobalTheory.LevGeo.adelicProb_mul_volFund D j H Dw l Xo c U dict hL σ hσ x0 FF hx
  refine ⟨h0, hT, ?_⟩
  have := hI (fun k y => ENNReal.ofReal (((U σ).X k).pnorm (modelWt (U σ) G k) (rdU (U σ) f k) y ^ 2))
    (fun k => ENNReal.measurable_ofReal.comp ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _
      (hsf k).1.continuousOn (fun y hy => dif_neg hy)).pow_const 2))
    (fun k γ hγ y hy => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf k) hγ hy])
    (fun k b hb y hy => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf k).2.1 y hy b hb])
  rw [← this]
  congr 1
  unfold petE
  have e : eLpNorm' (fun q => ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))) 2 (muQ1 (D.sp.W j)) ^ 2 =
      ∫⁻ q, ‖ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))‖ₑ ^ 2 ∂(muQ1 (D.sp.W j)) := by
    have := lintegral_rpow_eNorm_eq_rpow_eLpNorm' (μ := muQ1 (D.sp.W j))
      (f := fun q => ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q))) (q := 2) (by norm_num)
    simpa using this.symm
  rw [e]
  refine lintegral_congr fun q => ?_
  have hnn : 0 ≤ ptN (modelWt (U σ) G) (rdU (U σ) f) (dict σ (Quotient.out q)) := by
    unfold ptN Data.pnorm
    positivity
  rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg hnn, ← ENNReal.ofReal_pow hnn]
  rfl


set_option maxHeartbeats 1600000 in
theorem petE_pull_good : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f g : _), f ∈ cuspW Xo c U (wtZ a n) → g ∈ cuspW d.Xo₂ d.c₂ U₂ (wtZ a n) → Pull d f g → ∀ τ : d.c₂.F →+* ℂ, GoodEmb d.c₂ τ →
    petE (D.sp.W j) (dict₂ τ) (muQ1 (D.sp.W j)) (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) =
    petE (D.sp.W j) (dict (τ.comp (d.eF : c.F →+* d.c₂.F))) (muQ1 (D.sp.W j)) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n)) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn f g hf hg hp τ hτ
  have hσ : GoodEmb c (τ.comp (d.eF : c.F →+* d.c₂.F)) := (goodEmb_comp_eF D d τ).2 hτ
  obtain ⟨π, δ, N, hN, hcomp, hfib, t, ht1, hrel⟩ := _root_.GlobalTheory.LevModel.levCover_model D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd τ hτ
  have hex : ∀ (X : Data D.host.E D.R.r), ∃ x0, IsOrth X x0 ∧ ∃ FF, IsFundSet X x0 FF := fun X => by
    choose P _ hG using X.signature
    exact ⟨fun τ => P τ, fun τ => hG τ, GlobalTheory.MetricWeightTest.exists_fundSet_orth X (fun τ => hG τ)⟩
  choose x0 hx0 FF hFF using fun k => hex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k)
  choose x0₂ hx0₂ FF₂ hFF₂ using fun k => hex ((U₂ τ).X k)
  obtain ⟨hS0, hST, h1⟩ := petE_sq_mul_vol D j H Dw l Xo c U dict hL (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ (wtZ a n) f hf x0 FF (fun k => ⟨hx0 k, hFF k⟩)
  obtain ⟨hS0₂, hST₂, h2⟩ := petE_sq_mul_vol D j H Dw d.l₂ d.Xo₂ d.c₂ U₂ dict₂ hL₂ τ hτ (wtZ a n) g hg x0₂ FF₂
    (fun k => ⟨hx0₂ k, hFF₂ k⟩)
  have hΨ : ∀ k₂, ((U₂ τ).X k₂).Ψ = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Ψ := fun k₂ => Finset.ext fun ρ =>
    (((hL₂.unf τ hτ).2.1 k₂).2 ρ).trans (((hL.unf (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ).2.1 (π k₂)).2 ρ).symm
  have hp0 : ∀ k₂, ((U₂ τ).X k₂).p0 = ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).p0 := fun k₂ =>
    ((hL₂.unf τ hτ).2.1 k₂).1.trans ((hL.unf (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ).2.1 (π k₂)).1.symm
  have hsf : ∀ k, ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).IsSec (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) := fun k =>
    GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ ((mem_cuspW.1 hf).2 (τ.comp (d.eF : c.F →+* d.c₂.F)) hσ) k
  have h0f : ∀ k, ∀ x ∉ ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).dom, rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k x = 0 := fun k x hx => dif_neg hx
  have h0g : ∀ k, ∀ x ∉ ((U₂ τ).X k).dom, rdU (U₂ τ) g k x = 0 := fun k x hx => dif_neg hx
  have hsecf : f ∈ sec Xo c a n := by
    have := cuspW_le_secZ (wtZ a n) hf
    rwa [GlobalTheory.AllWt.exZ_wtZ, secZ_nat] at this
  have hsecg : g ∈ sec d.Xo₂ d.c₂ a n := by
    have := cuspW_le_secZ (wtZ a n) hg
    rwa [GlobalTheory.AllWt.exZ_wtZ, secZ_nat] at this
  have hmeas : ∀ k, Measurable fun x => ENNReal.ofReal
      (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) x ^ 2) := fun k =>
    ENNReal.measurable_ofReal.comp
      ((GlobalTheory.PeterssonCompare.measurable_pnorm _ _ (hsf k).1.continuousOn (h0f k)).pow_const 2)
  have hcint : ∀ k₂, ∫⁻ z in FF₂ k₂, ENNReal.ofReal (((U₂ τ).X k₂).pnorm (modelWt (U₂ τ) (wtZ a n) k₂)
        (rdU (U₂ τ) g k₂) (cpt ((U₂ τ).X k₂) (x0₂ k₂) z) ^ 2) ∂(muF ((U₂ τ).X k₂) (x0₂ k₂)) =
      ((((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ : ℝ≥0∞) *
        ∫⁻ z in FF (π k₂), ENNReal.ofReal (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) (π k₂))
        (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂)) (cpt ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂)) z) ^ 2) ∂(muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂))) ∧
      muF ((U₂ τ).X k₂) (x0₂ k₂) (FF₂ k₂) =
      ((((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ : ℝ≥0∞) *
        muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) (x0 (π k₂)) (FF (π k₂)) := by
    intro k₂
    have hGm := (hcomp k₂).1
    have hu := (hcomp k₂).2.1
    have hle := (hcomp k₂).2.2.1
    have hidx := (hcomp k₂).2.2.2
    have hu' : ∀ v w, herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v)
        ((δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Gm v w := by
      rw [← hGm]; exact hu
    have hP := pnorm_lact_transport D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) (π k₂))
        (modelWt (U₂ τ) (wtZ a n) k₂) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f (π k₂)) (rdU (U₂ τ) g k₂) (t k₂) n hGm (hp0 k₂) hu'
        (fun ρ h i => by simp only [modelWt, hp0 k₂, relab_eF])
        (ht1 k₂) (h0g k₂) (h0f (π k₂)) (fun x hx => by
          refine hrel a n ha f hsecf g hsecg hp k₂ x _ hx (fun ρ h₂ h₁ => ?_) hn
          show (δ k₂ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map ρ * mat (hΨ k₂ ▸ x) ⟨ρ, h₁⟩ = _
          congr 1
          unfold mat
          rw [frame_tr (hΨ k₂) x ρ h₁ h₂])
    refine ⟨?_, ?_⟩
    · simp_rw [hP]
      exact _root_.GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (x0 (π k₂)) (x0₂ k₂)
        (FF (π k₂)) (FF₂ k₂) _ hGm (hp0 k₂) hu' hle hidx (hx0 _) (hx0₂ _) (hFF _) (hFF₂ _) (hmeas _)
        (fun γ hγ x hx => by simp only [GlobalTheory.PeterssonCompare.pnorm_lact _ (hsf _) hγ hx])
        (fun b hb x hx => by simp only [FrameDegreeData.pnorm_rmul _ _ _ (hsf _).2.1 x hx b hb])
    · have := _root_.GlobalTheory.SubgroupUnfold.lintegral_fundSet_conj_subgroup D.host.E D.R.r ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)) ((U₂ τ).X k₂) (hΨ k₂) (δ k₂) (x0 (π k₂)) (x0₂ k₂)
        (FF (π k₂)) (FF₂ k₂) (fun _ => 1) hGm (hp0 k₂) hu' hle hidx (hx0 _) (hx0₂ _) (hFF _) (hFF₂ _)
        measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      simpa only [setLIntegral_one] using this
  set w : (U₂ τ).Comp → ℕ := fun k₂ =>
    (((U₂ τ).X k₂).Γ.map (MulAut.conj (δ k₂)).toMonoidHom).relIndex ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X (π k₂)).Γ with hw
  have hfib' : ∀ k, ∑ᶠ i : {i // π i = k}, w i.1 = N := fun k => by
    rw [← hfib k]
    exact finsum_congr fun i => by simp only [hw, i.2]
  have hA := sum_mul_fibre π w N (fun k => ∫⁻ z in FF k, ENNReal.ofReal (((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k).pnorm (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n) k)
        (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f k) (cpt ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) z) ^ 2) ∂(muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k))) hfib'
  have hB := sum_mul_fibre π w N (fun k => muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k)) hfib'
  simp only [hw] at hA hB
  have e1 := h2
  simp only [fun k₂ => (hcint k₂).1, fun k₂ => (hcint k₂).2] at e1
  rw [hA, hB, ← h1] at e1
  have hNS0 : (N : ℝ≥0∞) * ∑ k, muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hN.ne') hS0
  have hNST : (N : ℝ≥0∞) * ∑ k, muF ((U (τ.comp (d.eF : c.F →+* d.c₂.F))).X k) (x0 k) (FF k) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top N) hST
  have e2 : petE (D.sp.W j) (dict₂ τ) (muQ1 (D.sp.W j)) (modelWt (U₂ τ) (wtZ a n)) (rdU (U₂ τ) g) ^ 2 =
      petE (D.sp.W j) (dict (τ.comp (d.eF : c.F →+* d.c₂.F))) (muQ1 (D.sp.W j)) (modelWt (U (τ.comp (d.eF : c.F →+* d.c₂.F))) (wtZ a n)) (rdU (U (τ.comp (d.eF : c.F →+* d.c₂.F))) f) ^ 2 := by
    rw [← ENNReal.mul_left_inj hNS0 hNST, e1]
    ring
  have e3 : ∀ x y : ℝ≥0∞, x ^ 2 = y ^ 2 → x = y := fun x y h => by
    have h' : x ^ (2:ℝ) = y ^ (2:ℝ) := by
      rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast, ENNReal.rpow_natCast]; exact h
    exact ENNReal.rpow_left_injective two_ne_zero h'
  exact e3 _ _ e2

theorem levPull_normW : ∀ (D : D7) (j : ℕ) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) (d : DeltaDat Xo c 0) (U₂ : ∀ σ : d.c₂.F →+* ℂ, Unf d.Xo₂ d.c₂ σ D.R.r) (dict₂ : ∀ σ : d.c₂.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U₂ σ).X k).Ψ D.R.r), Laws D j Xo c U dict → Laws D j d.Xo₂ d.c₂ U₂ dict₂ → d.IsLev → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → Even n → ∀ (f : cuspW Xo c U (wtZ a n)) (g : cuspW d.Xo₂ d.c₂ U₂ (wtZ a n)), Pull d (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) → ∀ σ₂ : d.c₂.F →+* ℂ, normW U₂ (xiR D) (fun _ => D.sp.W j) dict₂ (wtZ a n) σ₂ g = normW U (xiR D) (fun _ => D.sp.W j) dict (wtZ a n) (σ₂.comp (d.eF : c.F →+* d.c₂.F)) f := by
  intro D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn f g hp σ₂
  simp only [normW, petW, petAt]
  rw [goodOf_eF D d σ₂, petE_pull_good D j H Dw l Xo c U dict d U₂ dict₂ hL hL₂ hd a n ha hn _ _ f.2 g.2 hp _
    (goodEmb_goodOf _ _)]

end GlobalTheory.LevPullNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem surjective_to_spec_field {T : Scheme.{0}} (K : Type) [Field K] (h : T ⟶ Spec (CommRingCat.of K))
    (t : T) : Surjective h := by
  refine ⟨fun x ↦ ⟨t, ?_⟩⟩
  have : Subsingleton (PrimeSpectrum K) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum K) _ _

theorem geometricallyConnected_of_isPullback {X X' Y Y' : Scheme.{0}} {f : X ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X}
    {q : Y' ⟶ Y} (hsq : IsPullback p f' f q) [Surjective q] [GeometricallyConnected f'] :
    GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd hz ↦ ?_⟩
  have hb : Surjective (pullback.snd q y) :=
    MorphismProperty.of_isPullback (P := @Surjective) (IsPullback.of_hasPullback q y) inferInstance
  have k : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨z, -⟩ := (pullback.snd q y).surjective k
  let t := (pullback q y).fromSpecResidueField z
  let L := (pullback q y).residueField z
  let W := pullback f' (t ≫ pullback.fst q y)
  have hW : ConnectedSpace W :=
    GeometricallyConnected.geometrically_connectedSpace (f := f') (t ≫ pullback.fst q y)
      (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hbig : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.fst q y) ≫ q) := (IsPullback.of_hasPullback _ _).paste_horiz hsq
  have hbig' : IsPullback (pullback.fst f' (t ≫ pullback.fst q y) ≫ p) (pullback.snd _ _) f
      ((t ≫ pullback.snd q y) ≫ y) := by
    convert hbig using 1
    simp [pullback.condition]
  let w : W ⟶ Z := hz.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _ ≫ t ≫ pullback.snd q y) (by
    simpa using hbig'.w)
  have hw : IsPullback w (pullback.snd f' (t ≫ pullback.fst q y)) snd (t ≫ pullback.snd q y) := by
    refine IsPullback.of_right (h₁₂ := fst) (v₁₃ := f) (h₂₂ := y) ?_ (by simp [w]) hz
    convert hbig' using 1
    simp [w]
  have hs : Surjective (t ≫ pullback.snd q y) := surjective_to_spec_field K _ (IsLocalRing.closedPoint L)
  have : Surjective w := MorphismProperty.of_isPullback (P := @Surjective) hw.flip hs
  exact w.surjective.connectedSpace w.continuous

theorem good_of_isPullback_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X)
    (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f →
    GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  intro X X' Y Y' f f' p q g hsq hq hqs hf hf'
  have := hf'.proper
  have := hf'.conn
  have : Surjective p := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hqs
  have : IsFinite p := MorphismProperty.of_isPullback (P := @IsFinite) hsq.flip hq
  have : IsProper (p ≫ f) := by rw [hsq.w]; infer_instance
  have : UniversallyClosed f := UniversallyClosed.of_comp_surjective p f
  have : IsSeparated f := GlobalTheory.NilProper.isSeparated_of_comp_surjective p f
  have : Smooth f := hf.smooth
  have : LocallyOfFiniteType f := inferInstance
  exact ⟨{}, hf, geometricallyConnected_of_isPullback hsq⟩

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

theorem of_isPullback_opens_cover (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q]
    {S X : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) {Z : I → Scheme.{0}} {p : X ⟶ S}
    {q : ∀ i, Z i ⟶ (U i).toScheme} {ψ : ∀ i, Z i ⟶ X} (h : ∀ i, IsPullback (ψ i) (q i) p (U i).ι)
    (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U hU fun i => ?_
  have e := (isPullback_morphismRestrict p (U i)).flip
  rw [← IsPullback.isoIsPullback_hom_snd _ _ e (h i), MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem isPullback_sigmaι_desc {X : Scheme.{0}} {κ : Type} (V : κ → X.Opens)
    (hd : Pairwise fun i i' => Disjoint (V i) (V i')) {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme)
    (i : κ) : IsPullback (Sigma.ι B i) (f i) (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι := by
  have : IsOpenImmersion (Sigma.ι B i) := inferInstance
  have hr : ∀ s : PullbackCone (Sigma.desc fun j => f j ≫ (V j).ι) (V i).ι,
      Set.range s.fst ⊆ Set.range (Sigma.ι B i) := by
    rintro s _ ⟨t, rfl⟩
    obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk B).surjective (s.fst t)
    rw [sigmaMk_mk] at hy
    have e1 : (Sigma.desc fun j => f j ≫ (V j).ι) (s.fst t) = (V i).ι (s.snd t) := congr($(s.condition) t)
    rw [← hy, ← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply] at e1
    by_cases hji : j = i
    · subst hji
      exact ⟨y, hy⟩
    · exfalso
      have h1 : (V j).ι (f j y) ∈ V j := ((V j).ι_apply _ ▸ ((f j y).2))
      have h2 : (V i).ι (s.snd t) ∈ V i := ((V i).ι_apply _ ▸ ((s.snd t).2))
      rw [e1] at h1
      have h3 := (hd hji).le_bot (show (V i).ι (s.snd t) ∈ V j ⊓ V i from ⟨h1, h2⟩)
      simp at h3
  refine ⟨⟨Sigma.ι_desc _ _⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => IsOpenImmersion.lift (Sigma.ι B i) s.fst (hr s)) ?_ ?_ ?_⟩⟩
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono (V i).ι, Category.assoc, ← Sigma.ι_desc (fun j => f j ≫ (V j).ι) i,
      IsOpenImmersion.lift_fac_assoc, s.condition]
  · intro s m h1 _
    rw [← cancel_mono (Sigma.ι B i), IsOpenImmersion.lift_fac, h1]

theorem good_sigmaDesc_of_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  intro X κ _ V hU hd B f g hf
  have sq := isPullback_sigmaι_desc V hd f
  have hc : IsZariskiLocalAtTarget (@GeometricallyConnected.{0}) := by
    rw [GeometricallyConnected.eq_geometrically]; infer_instance
  have hs : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  exact
    { proper := of_isPullback_opens_cover @IsProper hU sq fun i => (hf i).proper
      smooth := of_isPullback_opens_cover (@SmoothOfRelativeDimension.{0} g) hU sq fun i => (hf i).smooth
      conn := of_isPullback_opens_cover @GeometricallyConnected hU sq fun i => (hf i).conn }

end GlobalTheory.DualCon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormOrderRationalPullbackOfEssentiallyEtaleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [LocallyOfFiniteType p], topologicalKrullDim W = n → ∀ (E : DivOver p) (E' : DivOver (f ≫ p)) (h : ∀ x ∈ E.ring, functionFieldMap f x ∈ E'.ring), ((functionFieldMap f).restrict E.ring E'.ring h).FormallyEtale → (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) → ∀ η : RatForms p n, η ≠ 0 → (fun ω => @dite ℤ (∃ a, E'.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (GlobalTheory.EtaleKlt.ratPull p f n η) = (fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) η := by
  first | exact @GlobalTheory.EtaleKlt.formOrd_ratPull | exact GlobalTheory.EtaleKlt.formOrd_ratPull | (intros; apply GlobalTheory.EtaleKlt.formOrd_ratPull <;> assumption)
end

