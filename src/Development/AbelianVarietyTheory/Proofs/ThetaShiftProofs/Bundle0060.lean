module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionary
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataDescentNumberFieldStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmArcData_descent_numberField : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (σ₁ : K →+* ℂ) (σ : c.F →+* ℂ) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (aC : ArcIn Dw l (RingHom.id c.F) ℂ σ) (φ : aC.D₀.P.A.left ⟶ B.pol.A.left) (n : ℕ), letI := H.starRing; σ₁.comp (algebraMap c.F K) = σ → 0 < n → IsPolFibre (σ₁.comp (algebraMap (𝓞 K) K)) B.pol aC.D₀.P φ → (∀ x, (aC.oa.onB.act x).left ≫ φ = φ ≫ (B.t.act.act x).left) → TauCan aC.D₀ n → ∃ (K₂ : Type) (_ : Field K₂) (_ : NumberField K₂) (_ : Algebra c.F K₂) (i : K →ₐ[c.F] K₂) (σ₂ : K₂ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₂ (algebraMap c.F K₂)) (p : Out.IsPullDeg σ₂ a.D₀ aC.D₀) (ψ : a.D₀.P.A.left ⟶ B.pol.A.left), σ₂.comp (i : K →+* K₂) = σ₁ ∧ InBC σ₂ a aC p ∧ TauCan a.D₀ n ∧ IsPolFibre ((i : K →+* K₂).comp (algebraMap (𝓞 K) K)) B.pol a.D₀.P ψ ∧ ∀ x, (a.oa.onB.act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left := by
  first | exact @GlobalTheory.ArcCM.exists_arcIn_numberField | exact GlobalTheory.ArcCM.exists_arcIn_numberField | (intros; apply GlobalTheory.ArcCM.exists_arcIn_numberField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsKeyIntegral
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcGamma

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {v : Fin n → (epsR R ⟶ G)} (h : IsLieBasis v) : IsLieBasis fun i : Fin m => v (i.cast e) := by
  subst e
  exact h

theorem isLieComb_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {m n : ℕ} (e : m = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb (fun i : Fin m => c (i.cast e)) (fun i : Fin m => v (i.cast e)) w := by
  subst e
  exact h

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (Chart.dualMapR g) ≫ spMap (Chart.dualMapR f) = spMap (Chart.dualMapR (g.comp f)) := by
  rw [spMap_comp_spMap]
  refine congrArg spMap (RingHom.ext fun x => ?_)
  ext <;> simp [Chart.dualMapR]

section Pull

variable {A A' : Type} [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A'] {f : A →+* A'} {D₀ : Out.DegPre A}
  {D₁ : Out.DegPre A'} (p : Out.IsPullDeg f D₀ D₁)
include p

theorem g_eq : D₁.P.g = D₀.P.g :=
  H1.dim_unique _ D₁.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp p).1 D₀.P.smoothDim)
    (eSec D₁.P.A (Classical.arbitrary (PrimeSpectrum A')))

theorem keyPB_of_pull {th : D₀.P.L.Sec} {th₁ : D₁.P.L.Sec} (h : ThBC p th th₁) {g₀ n₀ g₁ n₁ v hv v₁ hv₁}
    (hvv : ∀ i, (v₁ i).left ≫ prj p = spMap (Chart.dualMapR f) ≫ (v (i.cast (g_eq p))).left) :
    KeyPB ⟨D₁.P, g₁, D₁.rig, D₁.rig_gen, th₁, n₁, v₁, hv₁⟩ ⟨D₀.P, g₀, D₀.rig, D₀.rig_gen, th, n₀, v, hv⟩ f := by
  refine ⟨prj p, p.he, p.w, g_eq p, Chart.dualMapR f, pull_grp p, p.w_gen, p.w_rig,
    KeyPow.appLE_eq_of_stalk _ th th₁ ((ArcQBC.through_iff _ _).1 h), fun a => ?_, ?_, hvv⟩
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end Pull

section Val

variable {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {V Fr : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field Fr] [Algebra V Fr] [IsFractionRing V Fr] {io : K →+* Fr}

theorem mem_range_iff (h : OverLa w V io 1) (y : K) :
    io y ∈ Set.range (algebraMap V Fr) ↔ w.valuation K y ≤ 1 := by
  have e : io y ∈ Set.range (algebraMap V Fr) ↔ valV V (io y) ≤ 1 :=
    ⟨fun ⟨r, hr⟩ => hr ▸ HeightOneSpectrum.valuation_le_one _ r,
      fun hy => IsDiscreteValuationRing.exists_lift_of_le_one hy⟩
  rw [e]
  by_cases hy : y = 0
  · simp [hy]
  have h1 := h.2 y
  simp only [vV, vLa, Nat.cast_one, _root_.one_mul, neg_inj] at h1
  have a : valV V (io y) ≠ 0 := valV_ne_zero ((map_ne_zero io).2 hy)
  have b : w.valuation K y ≠ 0 := ((w.valuation K).ne_zero_iff).2 hy
  rw [← WithZero.log_le_log a one_ne_zero, ← WithZero.log_le_log b one_ne_zero, h1]

theorem vV_eq_neg_count (h : OverLa w V io 1) {gm : Fr} {ca : K} {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K}
    (hc : IsLocGen w ca I) (u : Vˣ) (e : gm⁻¹ = io ca * algebraMap V Fr u) : vV V gm = -FractionalIdeal.count K w I := by
  have hu : valV V (algebraMap V Fr u) = 1 := by
    refine eq_one_of_one_le_mul_left (HeightOneSpectrum.valuation_le_one _ (u : V))
      (HeightOneSpectrum.valuation_le_one (K := Fr) (IsDiscreteValuationRing.maximalIdeal V) ((u⁻¹ : Vˣ) : V)) ?_
    rw [valV, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h1 := h.2 ca
  have h2 := congrArg (valV V) e
  rw [map_mul, hu, _root_.mul_one, map_inv₀, inv_eq_iff_eq_inv] at h2
  simp only [vV, vLa, Nat.cast_one, _root_.one_mul, neg_inj] at h1
  rw [vV, h2, WithZero.log_inv, h1, valuation_eq_exp_count w hc.1, hc.2]
  simp

end Val

theorem exists_ringHom {K R V Fr : Type} [Field K] [CommRing R] [Algebra R K] [CommRing V] [Field Fr] [Algebra V Fr]
    (hi : Function.Injective (algebraMap V Fr)) (io : K →+* Fr)
    (h : ∀ r : R, io (algebraMap R K r) ∈ Set.range (algebraMap V Fr)) :
    ∃ j : R →+* V, (algebraMap V Fr).comp j = io.comp (algebraMap R K) := by
  choose j hj using h
  exact ⟨⟨⟨⟨j, hi (by simp [hj])⟩, fun a b => hi (by simp [hj])⟩, hi (by simp [hj]), fun a b => hi (by simp [hj])⟩,
    RingHom.ext hj⟩

theorem exists_keyIntegral {K : Type} [Field K] [NumberField K] {w : HeightOneSpectrum (𝓞 K)} {V Fr : Type} [CommRing V]
    [IsDomain V] [Field Fr] [Algebra V Fr] (hi : Function.Injective (algebraMap V Fr)) {io : K →+* Fr}
    (hval : ∀ y : K, io y ∈ Set.range (algebraMap V Fr) ↔ w.valuation K y ≤ 1)
    {D : Out.DegPre K} {DV : Out.DegPre V} {DF : Out.DegPre Fr} (pw : Out.IsPullDeg (algebraMap V Fr) DV DF)
    (pK : Out.IsPullDeg io D DF) {th : D.P.L.Sec} {thw : DV.P.L.Sec} {th₁ th₂ : DF.P.L.Sec} {gm : Fr} (hgm : gm ≠ 0)
    (nw : ThNZ thw) (h₁ : ThBC pw thw th₁) (h₂ : ThBC pK th th₂) (hm : ThMul gm th₁ th₂) {g₀ n₀ v hv}
    {B : Out.PolAV (Sp (𝓞 K))} {φ : D.P.A.left ⟶ B.A.left}
    (hφ : IsGrpPullback D.P.A B.A (spMap (algebraMap (𝓞 K) K)) φ) {ρ : 𝓞 K →+* V} {ψ : DV.P.A.left ⟶ B.A.left}
    (hρ : ∀ x, algebraMap V Fr (ρ x) = io (x : K)) (hψ : IsGrpPullback DV.P.A B.A (spMap ρ) ψ)
    (hc : prj pw ≫ ψ = prj pK ≫ φ) {M : Matrix (Fin D.P.g) (Fin D.P.g) K}
    (hM : IsModelAt B ⟨D.P, g₀, D.rig, D.rig_gen, th, n₀, v, hv⟩ φ w M) :
    ∃ x' : KeyIn Fr, KeyPB x' ⟨D.P, g₀, D.rig, D.rig_gen, th, n₀, v, hv⟩ io ∧ KeyIntegral V x' gm⁻¹ (io M.det) := by
  obtain ⟨R, _, _, _, _, _, ρR, xR, φR, hg, hρR, hvalR, hfib, -, hw⟩ := hM
  obtain ⟨j, hj⟩ := exists_ringHom hi io fun r : R => (hval _).2 ((hvalR _).1 ⟨r, rfl⟩)
  have hjρ : j.comp ρR = ρ := RingHom.ext fun x => hi (by
    rw [hρ, RingHom.comp_apply, ← RingHom.comp_apply (algebraMap V Fr), hj, RingHom.comp_apply,
      ← RingHom.comp_apply (algebraMap R K), hρR])
  have hG : IsGrpPullback xR.P.A B.A (spMap ρR) φR := hfib.1
  have n : IsGrpPullback DV.P.A B.A (spMap j ≫ spMap ρR) ψ :=
    hψ.congr (by rw [spMap_comp_spMap]; exact congrArg spMap hjρ.symm) rfl
  have sq : ψ ≫ B.A.hom = (DV.P.A.hom ≫ spMap j) ≫ spMap ρR := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := hG.1.lift_fst _ _ sq
  have e₂ := hG.1.lift_snd _ _ sq
  generalize hG.1.lift _ _ sq = ψ' at e₁ e₂
  have hψ' : IsGrpPullback DV.P.A xR.P.A (spMap j) ψ' := hG.cancel (e₁ ▸ n) e₂
  have eK : DF.P.g = D.P.g := g_eq pK
  have eV : DF.P.g = DV.P.g := g_eq pw
  have eR : DV.P.g = xR.P.g := eV.symm.trans (eK.trans hg.symm)
  have := D.P.isAb.comm
  have := DV.P.isAb.comm
  have := DF.P.isAb.comm
  have := xR.P.isAb.comm
  obtain ⟨vV, hvV, eVv⟩ := exists_isLieBasis_baseChange R V j _ _ ψ' hψ' xR.P.isAb.smooth _ _ (isLieBasis_cast eR xR.basis)
  obtain ⟨v₁, hv₁, ev₁⟩ := exists_isLieBasis_baseChange V Fr _ _ _ (prj pw) (pull_grp pw) DV.P.isAb.smooth _ _
    (isLieBasis_cast eV hvV)
  obtain ⟨v₂, hv₂, ev₂⟩ := exists_isLieBasis_baseChange K Fr _ _ _ (prj pK) (pull_grp pK) D.P.isAb.smooth _ _
    (isLieBasis_cast eK hv)
  have gF : 1 ≤ DF.P.g := eK ▸ g₀
  refine ⟨⟨DF.P, gF, DF.rig, DF.rig_gen, th₂, ArcQBC.thNZ_of_thBC pK h₂ n₀, v₂, hv₂⟩, keyPB_of_pull pK h₂ ev₂,
    th₁, ArcQBC.thNZ_of_thBC pw h₁ nw, v₁, hv₁, (M.submatrix (Fin.cast eK) (Fin.cast eK)).map io,
    ⟨DV.P, eV ▸ gF, DV.rig, DV.rig_gen, thw, nw, vV, hvV⟩, fun i => ?_, fun i => ?_, ?_, keyPB_of_pull pw h₁ ev₁⟩
  · show th₁.f i = constFn DF.P.A.hom _ gm⁻¹ * th₂.f i
    rw [hm i, ← _root_.mul_assoc, ← KeyPow.constFn_mul, inv_mul_cancel₀ hgm, KeyPow.constFn_one, _root_.one_mul]
  · obtain ⟨wK, hwK, hwK'⟩ := hw (i.cast eK)
    refine (lieComb_baseChange K Fr io _ _ (prj pK) (pull_grp pK) _ _ wK _ v₂ (v₁ i) ev₂ (isLieComb_cast eK hwK)).1
      (hφ.1.hom_ext ?_ ?_)
    · have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := rfl
      rw [Category.assoc, ← hc, ← Category.assoc, ev₁, ← e₁, Category.assoc, ← Category.assoc (vV _).left, eVv,
        Category.assoc, Category.assoc, hwK', hd, ← Category.assoc, ← Category.assoc (spMap (Chart.dualMapR io)),
        dual_comp, dual_comp, hj]
      rfl
    · rw [Category.assoc, (pull_grp pK).1.w, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (LieCombBaseChange.dualMap_over io).symm
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact congrArg io (Matrix.det_submatrix_equiv_self (finCongr eK) M)

theorem vV_gamma : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (w : HeightOneSpectrum (𝓞 K₁)) (Tv : CDVR) (io : K₁ →+* Tv.Fr) (Wl : ValuationSubring ℂ) (M : IntModel d Tv io Wl) (ρ : 𝓞 K₁ →+* Tv.V) (ψ : M.aw.D₀.P.A.left ⟶ s.B.A.left), OverLa w Tv.V io 1 → (∀ x, algebraMap Tv.V Tv.Fr (ρ x) = io (x : K₁)) → IsPolFibre ρ s.B M.aw.D₀.P ψ → prj M.pw ≫ ψ = prj M.pK ≫ s.φB → TauCan M.aw.D₀ n' → M.γ ≠ 0 → vV Tv.V M.γ = -FractionalIdeal.count K₁ w s.Tl.I := by
  intro _ E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s w Tv io Wl M ρ ψ hO hρ hψ hc _ hgm
  obtain ⟨-, -, -, hB, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hloc, -, hmod⟩ := s.good
  obtain ⟨N, hN, hL⟩ := hmod w
  obtain ⟨th₁, th₂, h₁, h₂, hm⟩ := M.th_tie
  have hval := mem_range_iff hO
  obtain ⟨x', hPB, hInt⟩ := exists_keyIntegral (IsFractionRing.injective Tv.V Tv.Fr) hval M.pw M.pK hgm M.thw_nz h₁ h₂ hm
    hB.1 hρ hψ.2.1 hc hN
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ca, _, _, _, -, -, -, -, -, hca, -⟩ := hloc w
  obtain ⟨u, hu⟩ := KeyVal.integral_section_unit K₁ _ _ _ w (hloc w) Tv.V Tv.Fr io x' _ _ ca N.det 1 hval hPB hInt hL
    (by simp) hca
  exact vV_eq_neg_count hO hca u hu

end GlobalTheory.ArcGamma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicArcAgreesAnalyticDictionaryStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicArc_agrees_analyticDictionary : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (σ : c.F →+* ℂ) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (a : ArcIn Dw l β ℂ (σ.comp β)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (Λ : GtAn₀ a), letI := H.starRing; ∃ (gam : (Fu.Di Ha.i).La ≃ₗ[𝓞 E] Λ.A.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] Λ.A.V), (∀ z, Λ.ex₀ (h z) = Ha.ex₀ z) ∧ (∀ v, Λ.y (gam v) = Ha.y v) ∧ (∀ w v, h (Ha.Pw w v) = Λ.A.Pw w (gam v)) ∧ ∀ v v', Λ.A.EF (gam v) (gam v') = (Fu.Di Ha.i).EF v v' := by
  first | exact @GlobalTheory.ArcCompare.holArc_agrees | exact GlobalTheory.ArcCompare.holArc_agrees | (intros; apply GlobalTheory.ArcCompare.holArc_agrees <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ReadingsCuspAndIndependent
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ArcRead


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem readings_cusp_and_independent :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → TieReadSt h j := by
  intro D T h j hj
  refine ⟨fun u F k => ?_, fun u => GlobalTheory.Dict.readings_independent D T h.toLawsM j hj _ _⟩
  have hFC : F.1 ∈ T.C j u := cutR_le T.C j u F.2
  have hhol : rdU (T.U j T.σ₀) F.1 ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) :=
    ((mem_cusp _ _ _ _ _ F.1).1 hFC).2 T.σ₀ T.good_σ₀
  exact Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) hhol k

end GlobalTheory.ArcRead
end

