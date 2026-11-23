module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0065
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CuspFormBoundedBySupNormAtGoodEmbeddingAllEmbedd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem cusp_bound_allEmb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → (∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ) → 1 ≤ Dw.p + Dw.q → ∀ a n, Dom a n → ∀ F ∈ cusp Xo c U a n, ∀ (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (N : ℝ), IsMetric y N (fun _ => 1) → cabs (evR Xo c F y) ≤ Real.sqrt N ^ n * supC Xo c U ξ (goodOf c σ) a n F := by
  intro E _ _ _ H Dw l Xo c r U ξ hU hξ hpq a n hd F hF σ y N hm
  by_cases hσ : GoodEmb c σ
  · have e : goodOf c σ = σ := if_pos hσ
    rw [e]
    exact _root_.GlobalTheory.LamT.OrthoBound.cabs_evR_le_supC E H Dw l Xo c r U ξ hU hξ hpq a n hd F hF σ hσ y N hm
  · have e : goodOf c σ = (starRingEnd ℂ).comp σ := if_neg hσ
    have hg : GoodEmb c ((starRingEnd ℂ).comp σ) := e ▸ goodEmb_goodOf c σ
    rw [e]
    have hB : Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
    obtain ⟨y', hy'⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hB E H Dw l Xo c (CAt σ)
      (CAt ((starRingEnd ℂ).comp σ)) (FrameNorm.conjAlg σ) y
    have hm' := _root_.GlobalTheory.LamT.isMetric_conj E H Dw l Xo c σ y y' N (fun _ => 1) hpq hy' hm
    have h1 : (fun b : E →+* ℂ => ((1 : Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)).map (starRingEnd ℂ)) =
        fun _ => 1 := funext fun b => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1] at hm'
    have hb := _root_.GlobalTheory.LamT.OrthoBound.cabs_evR_le_supC E H Dw l Xo c r U ξ hU hξ hpq a n hd F hF _ hg y' N hm'
    haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    have hev := evR_frMap (GlobalTheory.Frames.algebraic_laws hB E H Dw l Xo c).2.2.1 F (cusp_le_sec Xo c U a n hF).1
      (FrameNorm.conjAlg σ) y (GlobalTheory.Frames.allTest_of_secBaseChange hB E H Dw l Xo c (CAt σ) y) y' hy'
    rw [hev] at hb
    refine le_trans (le_of_eq ?_) hb
    exact (Complex.norm_conj _).symm

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocalLowerBoundCmPointFramePolynomialEveryPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LocClause

theorem exists_isLocGen {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ∃ c : K, IsLocGen p c I := by
  obtain ⟨π, hπ⟩ := p.valuation_exists_uniformizer K
  refine ⟨π ^ FractionalIdeal.count K p I, (GlobalTheory.LamF.isLocGen_iff_valuation_eq p _ _).2 ?_⟩
  rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
  simp

theorem map_evalFr {B : Type} {m : B → ℕ} {R S : Type} [CommRing R] [CommRing S] (κ : R →+* S)
    (P : MvPolynomial (FrVar m) R) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) :
    κ (evalFr P Y) = evalFr (MvPolynomial.map κ P) (fun b => (Y b).map κ) := by
  unfold evalFr
  induction P using MvPolynomial.induction_on <;> simp_all

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem secBC_one_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {y : FrPt Xo c S} {y' : FrPt Xo c T} (h : FrMap φ y y') : SecBC φ.toRingHom 1 y.x y'.x y.s y'.s := by
  obtain ⟨-, -, pm, h₁, h₂, h₃⟩ := h
  refine ⟨pm, h₁, h₂, fun i hi => Eq.trans (congrArg _ ?_) (h₃ i hi)⟩
  have h1 := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x
    (by simp [spMap]) (by simp [spMap])).2.2.2 1 1 i).2.2
  rw [h1, _root_.one_mul]

theorem evR_scale {S : Type} [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {F : Rul Xo c}
    (hF : F ∈ sec Xo c a n) (s : Sˣ) {y y' : FrPt Xo c S} (h : FrChg (fun _ => 1) (s : S) y y') :
    evR Xo c F y' = (s : S) ^ n * evR Xo c F y := by
  let t : Ix Dw → Sˣ := fun i => i.elim s (fun _ => 1)
  have hb : FrBor t y y' := ((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2
    ⟨fun _ => 1, fun τ i j hij => Matrix.one_apply_ne hij.ne, fun τ i => by simp [t], h⟩
  rw [(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S inferInstance a n F hF t y y' hb]
  congr 1
  simp [wchar, Fintype.prod_option, t, ex]

theorem integral_of_eq (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    y.x = x → ∀ (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro h
  subst h
  exact integral_of T io y

theorem secInt_baseChange (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr))
    {x x₁ : Sp T.Fr ⟶ Xo.X} {x' x₁' : Sp T'.Fr ⟶ Xo.X} {G : PAT H (Sp T.V)} {G' : PAT H (Sp T'.V)}
    {t : SAB H (Sp T.Fr)} {t' : SAB H (Sp T'.Fr)} (m1 : SABMap t Xo.univ.t x)
    (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x')
    (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ))
    (n' : SABMap t' t (spMap i)) (hx : x' = spMap i ≫ x) (h1 : m1'.φ = n'.φ ≫ m1.φ)
    (h2 : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (e : x₁ = x) (e' : x₁' = x') (s : LB.Sec (PPx x₁)) (s' : LB.Sec (PPx x₁'))
    (hs : SecBC i 1 x₁ x₁' s s') (h : SecInt T m1 m2 s) : SecInt T' m1' m2' s' := by
  subst e e'
  exact _root_.GlobalTheory.LamT.secInt_baseChange E H Dw l Xo T T' ψ i hψ _ _ G G' t t' m1 m2 m1' m2' n n' hx h1 h2 s s' hs h

theorem integral_baseChange_chg [StarRing (𝓞 E)] (z : CMPt Xo c) (T T' : CDVR) (iK : z.K →+* T.Fr)
    (M : LocMod z T iK) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr)
    (hψ : (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr)) (io : c.F →+* T.Fr) :
    letI := io.toAlgebra
    letI := (i.comp io).toAlgebra
    ∀ (iA : T.Fr →ₐ[c.F] T'.Fr) (y : FrPt Xo c T.Fr) (y' w : FrPt Xo c T'.Fr)
      (X : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) T'.V),
      iA.toRingHom = i → y.x = spMap iK ≫ z.x → LieInt T io M.m1 M.m2 y.u → SecInt T M.m1 M.m2 y.s →
      FrMap iA y y' → (∀ b, IsUnit (X b).det) → FrChg (fun b => (X b).map (algebraMap T'.V T'.Fr)) 1 y' w →
      Integral T' (i.comp io) w := by
  letI := io.toAlgebra
  letI := (i.comp io).toAlgebra
  intro iA y y' w X hi hy hL hS hm hX hw
  obtain ⟨M', n, n', h1, h2⟩ := (_root_.GlobalTheory.LamT.locMod_exists E H Dw l Xo c z T iK).2 M T' ψ i hψ
  have hx : spMap (i.comp iK) ≫ z.x = spMap i ≫ spMap iK ≫ z.x := by
    rw [ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp, Category.assoc]
  have hy' : y'.x = spMap (i.comp iK) ≫ z.x := by rw [hm.1, hi, hy, hx]
  have hL' : LieInt T' (i.comp io) M'.m1 M'.m2 y'.u := by
    have := _root_.GlobalTheory.LamT.lieInt_baseChange E H Dw l Xo c T T' ψ i hψ _ _ M.G M'.G M.t'.t M'.t'.t M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2
      io y.u hL
    have hu : y'.u = fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ y.u τ k := by
      funext τ k
      rw [hm.2.1 τ k, hi]
    rw [hu]
    exact this
  have hLw : LieInt T' (i.comp io) M'.m1 M'.m2 w.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T' (i.comp io) M'.G.t M'.t'.t _ M'.m1 M'.m2 y' hy').2 hL' X 1 w hX hw
  have hs1 : SecBC i 1 y.x y'.x y.s y'.s := by
    have := secBC_one_of_frMap hm
    rwa [hi] at this
  have hs2 : SecBC i 1 y.x w.x y.s w.s := by
    have := ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo _ _ _ i (RingHom.id _) y.x y'.x w.x
      (by rw [hm.1, hi]) (by rw [hw.1]; simp [spMap])).1 1 _ _ _ hs1).1 hw.2.2
    rwa [RingHom.id_comp] at this
  have hwx : w.x = spMap (i.comp iK) ≫ z.x := hw.1.trans hy'
  exact integral_of_eq T' (i.comp io) w hwx M'.m1 M'.m2 hLw
    (secInt_baseChange T T' ψ i hψ M.m1 M.m2 M'.m1 M'.m2 n n' hx h1 h2 hy hwx _ _ hs2 hS)

theorem evR_chg {K S : Type} [Field K] [Algebra c.F K] [Field S] [Algebra c.F S] {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {y₀ : FrPt Xo c K} {G : MvPolynomial (FrVar Dw.mult) K}
    (hG : IsFrPoly F y₀ G) (φ : K →ₐ[c.F] S) {y y' w : FrPt Xo c S} (hy : FrMap φ y₀ y)
    {g X Y : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) S} {s : S} (hs : s ≠ 0)
    (hY : ∀ b, IsUnit (Y b).det) (hXY : ∀ b, (Y b).transpose = X b * g b)
    (h : FrChg g s y y') (hw : FrChg X 1 y' w) :
    evR Xo c F w = s ^ n * evalFr (MvPolynomial.map φ.toRingHom G) Y := by
  have hYt : ∀ b, IsUnit ((Y b).transpose).det := fun b => by rw [Matrix.det_transpose]; exact hY b
  obtain ⟨w₀, hw₀, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) 1 hYt
  obtain ⟨w₁, hw₁, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S w₀ (fun _ => 1) (Units.mk0 s hs)
    (fun _ => by simp)
  have c1 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y w₀ w₁).2 _ _ _ _ hw₀ hw₁
  have c2 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S y y' w).2 _ _ _ _ h hw
  have e : w₁ = w := by
    refine (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y (fun b => (Y b).transpose) (Units.mk0 s hs) hYt).unique
      ?_ ?_
    · simpa using c1
    · simpa [hXY] using c2
  rw [← e, evR_scale hF _ hw₁, hG S φ y w₀ Y hY hy hw₀]
  rfl

theorem step5Loc_cmPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ G : MvPolynomial (FrVar Dw.mult) z.K, IsFrPoly F z.y G → ∀ p, Step5Loc z.e z.Tl.dual z.LamL z.ℓ z.U G n p := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F hF hv G hG p
  obtain ⟨ca, hca⟩ := exists_isLocGen p z.Tl.I
  obtain ⟨cd, hcd⟩ := exists_isLocGen p z.LamL.I
  choose cl hcl using fun j => exists_isLocGen p (z.ℓ j).I
  refine ⟨ca⁻¹, cd, cl, isLocGen_inv hca, hcd, hcl,
    GlobalTheory.LamF.letters_det_valuation_le E H l c _ _ f z.obj La hz.1 z.letters hz.2.1 p cd cl hcd hcl, ?_⟩
  obtain ⟨T, iK, hT, hiK⟩ := _root_.GlobalTheory.exists_cdvr_completion_integral_iff z.K p
  obtain ⟨M⟩ := (_root_.GlobalTheory.LamT.locMod_exists E H Dw l Xo c z T iK).1 fun a => (hiK _).2 (p.valuation_le_one a)
  let io : c.F →+* T.Fr := iK.comp (algebraMap c.F z.K)
  letI := io.toAlgebra
  let φ : z.K →ₐ[c.F] T.Fr := { iK with commutes' := fun _ => rfl }
  obtain ⟨yT, hyT⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ φ z.y
  have hyx : yT.x = spMap iK ≫ z.x := by rw [hyT.1, hz.2.2.2.1]
  obtain ⟨g, hg, hgL⟩ := (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T io M.G.t M.t'.t _ M.m1 M.m2 yT hyx).1
  obtain ⟨s, hsS⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T io M.G M.t'.t _ M.m1 M.m2 yT hyx
  obtain ⟨y', hy', -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T.Fr yT g s hg
  have hL := hgL _ _ hy'
  have hS := hsS _ _ hy'
  obtain ⟨u, hu⟩ := GlobalTheory.T.integralGenerator_associated_localGenerator_CM_line E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hS ca hca
  refine ⟨T.V, T.Fr, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, iK,
    fun b => (g b)⁻¹, inferInstance, hT, hiK, fun b => (Matrix.isUnit_nonsing_inv_det _ (hg b)).ne_zero,
    fun b j k => GlobalTheory.T.lieLetter_integral_in_integral_eigenbasis E H Dw l Xo c z f La hz p T iK M hiK φ yT y' g s rfl hyT hy' hg hL b j k _ (hcl _), ?_⟩
  intro W KW _ _ _ _ _ _ _ fW hW hWf _ hfW Y X hX hXY
  have hinj : Function.Injective (algebraMap T.V W) := by
    intro x y h
    apply IsFractionRing.injective T.V T.Fr
    apply fW.injective
    rw [hfW, hfW, h]
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  let T' : CDVR := ⟨W⟩
  let κ : KW →+* T'.Fr := ((FractionRing.algEquiv W KW).symm : KW ≃ₐ[W] FractionRing W).toRingEquiv.toRingHom
  have hκ : ∀ w : W, κ (algebraMap W KW w) = algebraMap T'.V T'.Fr w := fun w =>
    (FractionRing.algEquiv W KW).symm.commutes w
  let i : T.Fr →+* T'.Fr := κ.comp fW
  have hψ : (algebraMap T'.V T'.Fr).comp (algebraMap T.V W) = i.comp (algebraMap T.V T.Fr) := by
    ext x
    show _ = κ (fW _)
    rw [hfW, hκ]
    rfl
  letI := (i.comp io).toAlgebra
  let iA : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨yW, hyW⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA yT
  obtain ⟨y'', hy''⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c _ _ iA y'
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c _ _ iA yT y' yW y'' g s hy' hyW).1 hy''
  have hXt : ∀ b, IsUnit ((X b).transpose : Matrix _ _ T'.V).det := fun b => by
    rw [Matrix.det_transpose]; exact hX b
  have hXu : ∀ b, IsUnit (((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr)).det := fun b => by
    have := (hXt b).map (algebraMap T'.V T'.Fr)
    rwa [RingHom.map_det] at this
  obtain ⟨w, hw, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c T'.Fr y'' _ 1 hXu
  have hint := integral_baseChange_chg z T T' iK M (algebraMap T.V W) i hψ io iA y' y'' w
    (fun b => (X b).transpose) rfl (hy'.1.trans hyx) hL hS hy'' hXt hw
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.ruleValue_integral_of_supLattice_values_nonneg E H Dw l Xo c F hv T' (i.comp io) hWf w hint
  have hYX : ∀ b, (Y b).transpose = ((X b).map (algebraMap W KW)).transpose * (g b).map fW := fun b => by
    rw [← hXY b, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc, ← Matrix.map_mul,
      Matrix.nonsing_inv_mul _ (hg b)]
    simp
  have hYX' : ∀ b, ((Y b).map κ).transpose =
      ((X b).transpose : Matrix _ _ T'.V).map (algebraMap T'.V T'.Fr) * (g b).map iA := fun b => by
    rw [← Matrix.transpose_map, hYX b, Matrix.map_mul]
    congr 1
    ext j k
    exact hκ _
  have hYu : ∀ b, IsUnit ((Y b).map κ).det := fun b => by
    rw [← Matrix.det_transpose, hYX' b, Matrix.det_mul]
    refine (hXu b).mul ?_
    have := (hg b).map i
    rwa [RingHom.map_det] at this
  have hval := evR_chg hF hG (iA.comp φ) (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans φ iA hyT hyW)
    ((map_ne_zero iA).2 s.ne_zero) hYu hYX' hc hw
  refine ⟨algebraMap T.V W ↑u⁻¹ ^ n * w₀, κ.injective ?_⟩
  have hP : MvPolynomial.map κ (MvPolynomial.map fW (MvPolynomial.map iK G)) =
      MvPolynomial.map (iA.comp φ).toRingHom G := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    rfl
  have hsn : (iA s : T'.Fr) ≠ 0 := (map_ne_zero iA).2 s.ne_zero
  have hu' : κ (fW (iK ca⁻¹)) * κ (algebraMap W KW (algebraMap T.V W ↑u⁻¹)) * iA s = 1 := by
    rw [← hfW]
    show i _ * i _ * i _ = 1
    rw [← map_mul, ← map_mul, hu, map_inv₀, _root_.mul_mul_mul_comm, inv_mul_cancel₀ ((map_ne_zero iK).2 hca.1),
      ← map_mul, Units.inv_mul, map_one, _root_.one_mul, map_one]
  rw [map_evalFr, hP]
  simp only [map_mul, map_pow]
  rw [hκ w₀, hw₀, hval, ← _root_.mul_assoc, ← _root_.mul_assoc, ← mul_pow, ← mul_pow, hu', one_pow, _root_.one_mul]

end GlobalTheory.LamT.LocClause
end

