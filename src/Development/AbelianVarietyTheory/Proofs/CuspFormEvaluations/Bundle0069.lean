module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0065
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0034
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.UpperRecord

theorem finrank_le_of_parts {Y ι : Type} {Z : ι → Type} (V : Submodule ℂ (Y → ℂ)) (e : Y ≃ Σ k, Z k)
    (d : ι → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (hb : ∀ (k : ι) (m : ℕ) (g : Fin m → V),
      LinearIndependent ℂ (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) → m ≤ d k * C) :
    Module.finrank ℂ V ≤ δ * C := by
  classical
  let ρ : ∀ k, V →ₗ[ℂ] (Z k → ℂ) := fun k =>
    (LinearMap.funLeft ℂ ℂ fun z : Z k => e.symm ⟨k, z⟩).comp V.subtype
  have hr : ∀ k, Module.rank ℂ (LinearMap.range (ρ k)) ≤ (d k * C : ℕ) := fun k => by
    refine rank_le fun s hs => ?_
    have hs' := (hs.comp s.equivFin.symm s.equivFin.symm.injective).map' (LinearMap.range (ρ k)).subtype
      (Submodule.ker_subtype _)
    choose g hg using fun q : Fin s.card => (s.equivFin.symm q).1.2
    refine hb k s.card g ?_
    have heq : (fun q (z : Z k) => (g q).1 (e.symm ⟨k, z⟩)) = _ := funext hg
    rw [heq]
    exact hs'
  have hfin : ∀ k, Module.Finite ℂ (LinearMap.range (ρ k)) := fun k =>
    Module.rank_lt_aleph0_iff.1 ((hr k).trans_lt (Cardinal.natCast_lt_aleph0))
  have hfr : ∀ k, Module.finrank ℂ (LinearMap.range (ρ k)) ≤ d k * C := fun k =>
    Module.finrank_le_of_rank_le (hr k)
  let s : Finset ι := Finset.univ.image fun q => (en q).1
  have hs : ∀ k, k ∉ s → d k = 0 := fun k hk => by
    by_contra h0
    exact hk (Finset.mem_image.2 ⟨en.symm ⟨k, ⟨0, Nat.pos_of_ne_zero h0⟩⟩, Finset.mem_univ _, by simp⟩)
  let Φ : V →ₗ[ℂ] (∀ k : s, LinearMap.range (ρ k)) := LinearMap.pi fun k => (ρ k).rangeRestrict
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hk : ∀ k, ρ k g = 0 := fun k => by
      by_cases hk : k ∈ s
      · exact congrArg Subtype.val (congrFun hg ⟨k, hk⟩)
      · have h0 : Module.finrank ℂ (LinearMap.range (ρ k)) = 0 := by
          have := hfr k
          rw [hs k hk] at this
          omega
        have := Submodule.finrank_eq_zero.1 h0
        exact (Submodule.eq_bot_iff _).1 this _ ⟨g, rfl⟩
    ext y
    have := congrFun (hk (e y).1) (e y).2
    simpa [ρ, LinearMap.funLeft_apply] using this
  have hsum : ∑ k : s, d k ≤ δ := by
    have hinj : Function.Injective fun p : Σ k : s, Fin (d k) => en.symm ⟨p.1.1, p.2⟩ := by
      rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, a'⟩ hp
      have := en.symm.injective hp
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 this
      obtain rfl := eq_of_heq h2
      rfl
    simpa using Fintype.card_le_of_injective _ hinj
  calc Module.finrank ℂ V ≤ Module.finrank ℂ (∀ k : s, LinearMap.range (ρ k)) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = ∑ k : s, Module.finrank ℂ (LinearMap.range (ρ k)) := Module.finrank_pi_fintype ℂ
    _ ≤ ∑ k : s, d k * C := Finset.sum_le_sum fun k _ => hfr k
    _ = (∑ k : s, d k) * C := (Finset.sum_mul _ _ _).symm
    _ ≤ δ * C := Nat.mul_le_mul_right _ hsum

theorem upper : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → Module.finrank ℂ (R.sp (addL wF wL Tn) Set.univ) ≤ δ * (Tn + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j) := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _
  refine finrank_le_of_parts _ e (fun k => (Fl.Fl k).δ) _ δ en fun k m g hg => ?_
  choose f hf hgf using fun q => (_root_.GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL Tn)).1 (g q).1 (g q).2
  have hw := (_root_.GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj k).2.2.1 wF wL Tn
  have := GlobalTheory.UpperModel.upper _ _ _ (A.Xa k) (Fl.Fl k) m (fun q => f q k) (fun q => by
    rw [A.hF, A.hL, A.hT, ← hw]
    exact (hf q k).1.1) (fun u hu => by
    funext q
    refine Fintype.linearIndependent_iff.1 hg u ?_ q
    funext z
    have := hu z.1 z.2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← this]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hgf q, e.apply_symm_apply])
  rwa [A.hT, A.dim] at this

end GlobalTheory.UpperRecord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjCmHalfIntegralGeneratorEqOneSub
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_multiple_mem (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ (c : E) • v ∈ X.Λ :=
  _root_.GlobalTheory.SmulMemOfSpan.exists_smul_mem_lattice X v

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (a b : E) (x y : Fin r → E) :
    herm G (a • x) (b • y) = a * ReciprocityTheory.ChartRestriction.G.FD.cc b * herm G x y := by
  simp only [herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_isIso (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {ρ : ℕ} (cu : FJ.CuspFD X ρ) (hρ : 0 < ρ) :
    ∃ ξ : Fin r → E, X.IsIso ξ := by
  obtain ⟨c, hc, hm⟩ := exists_multiple_mem X (cu.e ⟨0, hρ⟩)
  refine ⟨_, hm, by rw [herm_smul_smul, cu.iso, mul_zero], ?_⟩
  exact smul_ne_zero (by simpa using hc) (cu.ind.ne_zero _)

theorem conj_cmHalfIntegralGenerator_eq_one_sub (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ReciprocityTheory.ChartRestriction.G.FD.cc (H.w0 : E) = 1 - (H.w0 : E) :=
  _root_.GlobalTheory.CMConjugationOfSquareRoot.main H

theorem even_im_hermitian_sub (X : DataX E r) (w0 : 𝓞 E) (hw : ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) = 1 - (w0 : E)) :
    ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k :=
  _root_.UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub X w0 hw

end General

theorem extra_weight_exists : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), GamAt T.toCore → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → j < D.R.m → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE → 16 ≤ D.host.rdE → D.R.m ^ 4 ≤ D.R.f → ∀ k : (T.U j T.σ₀).Comp, BasePotentialExistence ((T.U j T.σ₀).X k) (de2W ((T.U j T.σ₀).X k)) D.R.r (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f))) := by
  intro D T h j hj large₂ w hG hP hL hrn hjm hf2 hrd hm4 k
  obtain ⟨e, -⟩ := GlobalTheory.CuspDataBounds.cusp_data_bounds D T h hG large₂ j hj w hP hL hrn T.σ₀ T.good_σ₀
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hcard : ((T.U j T.σ₀).X k).Ψ.card = D.R.f := by
    have h2c := Formalism.L2.Pj.DatLin.two_card ((T.U j T.σ₀).X k).cmType
    rw [hfr] at h2c
    omega
  have hPf : ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    omega
  have hPr : ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E = D.host.rdE := rfl
  have hp0 : ((T.U j T.σ₀).X k).p0 = D.R.m - j :=
    ((h.unf j hj T.σ₀ T.good_σ₀).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by
      have hp : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
      omega
    exact_mod_cast this
  obtain ⟨cu⟩ := h.cuNe j hj k
  have hρ : 0 < WeightFamilies.rho D j := by
    show 0 < D.R.m - j
    omega
  have key := GlobalTheory.ThetaWeight.exists_weight GlobalTheory.theta_bound_tStatement D.host.E D.R.r (e k).toX
    (exists_isIso _ cu hρ)
    ⟨⟨T.Q.H.w0, even_im_hermitian_sub _ _ (conj_cmHalfIntegralGenerator_eq_one_sub T.Q.H)⟩, by rw [hPf, hPr]; nlinarith, by rw [hPf, hPr]; exact hf2,
      by rw [hPr]; exact hrd, D.R.m, by omega, by rw [hPf]; exact hm4,
      Or.inl (by show ((T.U j T.σ₀).X k).p0 ≤ _; omega)⟩
  rw [← hcard]
  exact key

end GlobalTheory.ExtraWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
section
namespace GlobalTheory.Shares.VanDiv

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem leviO_phla_add_nsmul (x0 : Frame X.Ψ r) (F L : Wt X.Ψ r) (k : ℕ) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (phla X (F + k • L)) z ξ = leviO X x0 (phla X F) z ξ + k * leviO X x0 (phla X L) z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz F).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have e : (fun w => ((phla X (F + k • L) (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun w => ((phla X F (cpt X x0 w) + (k : ℝ) * phla X L (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [OW.phla_add_nsmul X hw]
  unfold leviO leviM
  rw [Y.fc_leviV_congr _ _ _ _ e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h3),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

theorem pnorm_mul_pow_sq (F L : Wt X.Ψ r) (m : ℕ) (g w : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm (F + m • L) (fun x => g x * w x ^ m) x ^ 2 = X.pnorm F g x ^ 2 * (X.pnorm L w x ^ 2) ^ m := by
  rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.phla_add_nsmul X hx, neg_add,
    Real.exp_add, ← mul_neg, Real.exp_nat_mul, map_mul, map_pow]
  ring

theorem model_division (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) (k : ℕ)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + (k + (nd X + 1)) • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    (g : Frame X.Ψ r → ℂ) (hg : X.IsBddSec (Xa.Fp + k • Xa.L) g) (hv : ∀ j, g (Fl.xs j) = 0) :
    ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ i, h i ∈ X.SS (Xa.Fp + (k + nd X) • Xa.L)) ∧
      ∀ x ∈ X.dom, g x * Fl.w0 x ^ (nd X + 1) = ∑ i, Fl.s i x * h i x := by
  obtain ⟨-, ⟨bb, m, hbb, hbm, hmar⟩, hL, -, hcusp⟩ := hm
  have e : ∀ a : ℕ, Xa.Fp + k • Xa.L + a • Xa.L = Xa.Fp + (k + a) • Xa.L := fun a => by
    rw [add_nsmul, add_assoc]
  obtain ⟨C, hC⟩ := hg.2
  have hC2 : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + k • Xa.L) g x ^ 2 ≤ C ^ 2 := fun x hx =>
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hC x hx) 2
  obtain ⟨B, hB⟩ := Fl.weightForm_vanishes.1.1.2
  obtain ⟨K, hK⟩ := Fl.denom_le_family
  obtain ⟨h, hh, hs⟩ := GlobalTheory.DivFreeWeight.division_order_one E r X Xa Fl (Xa.Fp + k • Xa.L)
    ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => by
      have h1 := hmar x0 ho z hz ξ
      have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hL x0 ho z hz ξ)
      rw [leviO_phla_add_nsmul x0 _ _ k hz]
      linarith⟩
    (by rw [e]; exact hcusp _) (by rw [e]; exact hfin)
    (fun x => g x * Fl.w0 x ^ (nd X + 1))
    ⟨GlobalTheory.Up.DivCorePf.isSec_mul hg.1 (GlobalTheory.Up.DivCorePf.isSec_pow Fl.weightForm_vanishes.1.1.1 _),
      √(C ^ 2 * (B ^ 2) ^ (nd X + 1)), fun x hx => by
        refine Real.le_sqrt_of_sq_le ?_
        rw [pnorm_mul_pow_sq _ _ _ _ _ hx]
        exact mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _)
          (pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2) _) (by positivity) (by positivity)⟩
    ⟨C ^ 2 * |K| ^ (nd X + 1), fun x hx => by
      rw [pnorm_mul_pow_sq _ _ _ _ _ hx, mul_assoc, ← mul_pow]
      refine mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) ((hK x hx).trans ?_) _)
        (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)⟩
    (fun j => by simp [hv j])
  exact ⟨h, fun i => hcusp _ _ (e _ ▸ hh i), hs⟩

end Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (K : ℕ) (b : Fin K → B.Cusp j u),
      R.sp u Set.univ ≤ Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i))) := by
  obtain ⟨K, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨K, b, Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ _)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, R.ev_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem vanishing_division : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hen honto k g hg hv
  classical
  have hwt : ∀ (a : ℕ) c, laR T j (addL wF wL a) c = (A.Xa c).Fp + a • (A.Xa c).L := fun a c => by
    rw [(GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj c).2.2.1, A.hF, A.hL]
  obtain ⟨f, hf, hgf⟩ := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL k)).1 g hg
  have hfin : ∀ (a : ℕ) (c : (T.U j T.σ₀).Comp), ∃ (K : ℕ) (b : Fin K → Frame ((T.U j T.σ₀).X c).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X c).SS ((A.Xa c).Fp + a • (A.Xa c).L),
      ∃ cc : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X c).dom, f x = ∑ i, cc i * b i x := by
    intro a c
    obtain ⟨K, b, hb⟩ := sp_le_span R (addL wF wL a)
    refine ⟨K, fun i => rdR h j (b i) c, fun p hp => ?_⟩
    have h1 := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto a)
      (Function.update (fun _ => 0) c p) (fun c' => by
        by_cases hc : c' = c
        · subst hc
          rw [Function.update_self, hwt]
          exact hp
        · rw [Function.update_of_ne hc]
          exact (siegelSpaceAlgebra_holds _ _ _ 0 0).2.2.1.1.1)
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hb h1)
    refine ⟨cc, fun x hx => ?_⟩
    have h2 := congrFun hcc (e.symm ⟨c, ⟨x, hx⟩⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2] at h2
    rw [Equiv.apply_symm_apply] at h2
    simpa using h2.symm
  have hdiv := fun c => model_division (A.Xa c) (Fl.Fl c) (A.mar c) k (hfin _ c) (f c)
    (hwt k c ▸ (hf c).1.1) (fun i => by
      have h1 := hv (en.symm ⟨c, i⟩)
      rw [hgf, hen, Equiv.apply_symm_apply] at h1
      exact h1)
  choose H hH hsum using hdiv
  refine ⟨WeightFamilies.dimY D j, ?_⟩
  have hs : ∀ i y, R.s w t i y = ∑ a, t (i, a) * rdR h j (w a) (e y).1 (e y).2.1 := fun i y => by
    simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  have hmem : ∀ i : Fin (WeightFamilies.dimY D j),
      (fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1) ∈ R.sp (addL wF wL (k + WeightFamilies.dimY D j)) Set.univ :=
    fun i => (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto _) (fun c => H c (Fin.cast (A.dim c).symm i))
      (fun c => by
        rw [hwt]
        have h1 := hH c (Fin.cast (A.dim c).symm i)
        rwa [show k + nd ((T.U j T.σ₀).X c) = k + WeightFamilies.dimY D j by rw [A.dim c]] at h1)
  have heq : R.s w t 0 ^ (WeightFamilies.dimY D j + 1) * g =
      ∑ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) * fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1 := by
    have hmon : ∀ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) = R.s w t i.succ := fun i => by
      unfold Rdg.mon
      rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp
    funext y
    simp only [hmon, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hs]
    have h1 := hsum _ _ (e y).2.2
    rw [show nd ((T.U j T.σ₀).X (e y).1) + 1 = WeightFamilies.dimY D j + 1 by rw [A.dim]] at h1
    rw [← Fl.h0, hgf, mul_comm, h1]
    refine Fintype.sum_equiv (finCongr (A.dim (e y).1)) _ _ fun a => ?_
    rw [Fl.hs]
    rfl
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Pi.single i 1, _, by simp, hmem i, rfl⟩

end GlobalTheory.Shares.VanDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningFormsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valueBasis_in_spanning_forms : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) (N : ℕ) (w : Fin N → B.Cusp j wL) (R : Rdg X) (t : Idx D j N → ℂ) (T : ℕ) (Mg : Submodule B.KO (B.Cusp j ka)) (δ : ℕ) (xs : Fin δ → R.Y), AnFacts R w t ka wF T Mg xs → ∀ Sh : Set (B.Cusp j wF), Submodule.span B.KO Sh = ⊤ → ∃ θ : Fin δ → B.Cusp j wF, (∀ i, θ i ∈ Sh) ∧ LinearIndependent ℂ (vals xs fun i => R.ev (X.inc wF (θ i))) := by
  first | exact @GlobalTheory.Shares.exists_valueBasis_in_spanning | exact GlobalTheory.Shares.exists_valueBasis_in_spanning | (intros; apply GlobalTheory.Shares.exists_valueBasis_in_spanning <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.LowerBound

theorem le_finrank_of_pieces {K Z : Type} [Fintype K] [DecidableEq K] {Y : K → Type} (dom : ∀ k, Set (Y k))
    (e : Z ≃ Σ k, dom k) (d : K → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (f : ∀ k, Fin (d k * C) → Y k → ℂ)
    (hf : ∀ k (u : Fin (d k * C) → ℂ), (∀ x ∈ dom k, ∑ q, u q * f k q x = 0) → u = 0)
    (S : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k q, (fun z => (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e z).1 (e z).2.1) ∈ S) :
    δ * C ≤ Module.finrank ℂ S := by
  let v : (Σ k, Fin (d k * C)) → S := fun p => ⟨_, hS p.1 p.2⟩
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have key := hf p.1 (fun q => g ⟨p.1, q⟩) fun x hx => by
      have h1 := congrFun (congrArg Subtype.val hg) (e.symm ⟨p.1, x, hx⟩)
      rw [Submodule.coe_sum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single p.1] at h1
      · refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h1
        show _ = g _ * (Pi.single p.1 (f p.1 q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1
        rw [e.apply_symm_apply]
        simp
      · intro k _ hk
        refine Finset.sum_eq_zero fun q _ => ?_
        show g _ * (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1 = 0
        rw [e.apply_symm_apply]
        simp [Pi.single_eq_of_ne hk.symm]
      · simp
    exact congrFun key p.2
  have h1 := hv.fintype_card_le_finrank
  have h2 := Fintype.card_congr en
  simp only [Fintype.card_sigma, Fintype.card_fin] at h1 h2
  rwa [← Finset.sum_mul, ← h2] at h1

variable {D : D7}

theorem laR_wadd (T : Top D) (j : ℕ) (u v : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wadd u v) k = laR T j u k + laR T j v k := by
  unfold laR
  rw [wtA_wadd]
  exact laU_add (T.U j T.σ₀) (wtA u) (wtA v) u.n v.n u.n_even v.n_even k

theorem laR_wsmul (T : Top D) (j : ℕ) (m : ℕ) (u : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  induction m with
  | zero =>
    funext τ a
    simp [laR, laU, wtA, wsmul, Formalism.L2.Pj.ext0]
  | succ m ih =>
    have e : wsmul (m + 1) u = wadd (wsmul m u) u := by
      simp only [wsmul, wadd, add_mul, one_mul]
    rw [e, laR_wadd, ih, succ_nsmul]

theorem lower_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _ CR c hc hM
  have hex : ∀ k : (T.U j T.σ₀).Comp,
      ∃ f : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ,
        (∀ q, f q ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) ∧
        ∀ u : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → ℂ,
          (∀ x ∈ ((T.U j T.σ₀).X k).dom, ∑ q, u q * f q x = 0) → u = 0 := by
    intro k
    obtain ⟨⟨bb, m, h1, h2, h3⟩, -, h4, h5, h6⟩ := A.mar k
    have hint := interpCStatement_holds _ _ (A.Xa k) (Fl.Fl k) (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
      ⟨bb, m, h1, h2, h3 _ (by simp)⟩ h4 h5 (by simpa using h6 0) (GlobalTheory.ClosedModes.modeHalf_closed _ _)
    have hmany := GlobalTheory.ManyForms.exists_indep_forms _ _ (A.Xa k) (Fl.Fl k) (A.Xa k).Fp Tn (A.Xa k).c1
      (A.Xa k).frame_theta_const_pos.le hint
    rw [A.hF k, A.hL k, A.hc k] at hmany
    rw [← A.dim k, addL, laR_wadd, laR_wsmul]
    exact hmany
  choose f hfm hfi using hex
  haveI := (GlobalTheory.Shares.PolyDict.sp_finrank R (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))).1
  refine le_finrank_of_pieces (fun k => ((T.U j T.σ₀).X k).dom) e (fun k => (Fl.Fl k).δ) _ δ en f hfi _ fun k q => ?_
  obtain ⟨m, a, F, hF, hsum⟩ := hM (Pi.single k (f k q)) fun k' => by
    rw [← hc]
    by_cases hk : k' = k
    · subst hk
      rw [Pi.single_eq_same]
      exact hfm _ q
    · rw [Pi.single_eq_of_ne hk]
      exact (siegelSpaceAlgebra_holds _ _ _ (laR T j (addL wF wL Tn) k') c1).2.2.1.1
  have hE : (fun z => (Pi.single k (f k q) : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (e z).1 (e z).2.1) =
      ∑ i, a i • R.ev ((recPlusN h j hj n).inc _ (F i)) := by
    funext z
    rw [hsum _ _ (e z).2.2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hE]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.LowerBound
end

