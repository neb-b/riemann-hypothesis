module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1172
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2233
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqZeroOfValR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1785
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1827
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedLcCentreOfZeroLcThreshold
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

theorem GlobalTheory.PairStep.exists_isolated_of_lcCut_zero : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e ≤ 1 →
      ∀ (A : CartierDiv X) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X), IsAmpleLB (toLB A) → 0 < m' → D₀.Eff → 0 < μ →
        (lam : ℝ) < ∑ e ∈ Finset.Icc 1 n, (e : ℝ) / c e →
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) →
        LcCut p n (Δ + qWeil D₀ m') x 0 →
      ∃ (m : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m ∧ D₀.Eff ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C →
          (interNumRed ℂ C ![toLB D₀] : ℚ) / m = interNumRed ℂ C ![N₀] / r) ∧
        x ∈ U ∧ (∀ y ∈ U, LcAt p n (Δ + qWeil D₀ m) y) ∧
        (∀ y ∈ U, y ≠ x → KltAt p n (Δ + qWeil D₀ m) y) ∧ ¬ KltAt p n (Δ + qWeil D₀ m) x := by
  intro hPr X _ _ _ p n hp hn hn1
  letI := algebraΓOfHom p
  intro Δ r N₀ x c hΔ hklt hr hN₀ hnef hbig hx hc hcZ hsum A lam μ m' D₀ hA hm' hD₀ hμ hlam hnum hcut
  obtain ⟨m, G, hm, hG⟩ := _root_.GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt X p n hp hn Δ hΔ hklt
  have hG' := GlobalTheory.isLogCanonicalMultiple_add_qWeil X p n Δ m m' G D₀ hm hm' hG
  obtain ⟨U, hxU, hlc, hkl⟩ := _root_.GlobalTheory.PairStep.exists_open_lc_klt_off_point hPr X p n hp hn (Δ + qWeil D₀ m') (m * m') (m' • G + m • D₀) x
    (Nat.mul_pos hm hm') hG' hx hcut
  have hlam1 : lam ≤ 1 := by
    have : (lam : ℝ) ≤ 1 := (hlam.trans_le hsum).le
    exact_mod_cast this
  obtain ⟨M, E, hM, hE, hxE, hEnum⟩ := GlobalTheory.T.exists_effective_QDivisor_offPoint_ampleClass X p hp N₀ A x r lam μ hN₀ hnef hA hr hlam1 hμ
  obtain ⟨hD, hqW, hDnum⟩ := GlobalTheory.T.cartierDivToWeilQDivisor_add_of_effective X p hp D₀ E m' M hm' hM hD₀ hE
  have hoff : ∀ y, y ∉ E.supp → Off (qWeil E M) y := fun y hy =>
    (_root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp X E M y hE hM).2 hy
  have heq : Δ + qWeil (M • D₀ + m' • E) (m' * M) = (Δ + qWeil D₀ m') + (1 : ℚ) • qWeil E M := by
    rw [hqW, one_smul, add_assoc]
  let V : X.Opens := ⟨(E.supp : Set X)ᶜ, E.supp.isClosed.isOpen_compl⟩
  refine ⟨m' * M, M • D₀ + m' • E, U ⊓ V, Nat.mul_pos hm' hM, hD, ?_, ⟨hxU, hxE⟩, ?_, ?_, ?_⟩
  · intro C hC
    have h1 := hDnum C hC
    have h2 := hnum C hC
    have h3 := hEnum C hC
    push_cast at h1 ⊢
    rw [h1, h2, h3]
    ring
  · intro y hy
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).2.1).2 (hlc y hy.1)
  · intro y hy hyx
    rw [heq]
    exact ((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 y (hoff y hy.2)).1).2 (hkl y hy.1 hyx)
  · rw [heq]
    exact fun h => hcut.2.1 (((GlobalTheory.PairStep.off_add_smul X p n _ _ 1 x (hoff x hxE)).1).1 h)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifDvrBaseChange

theorem exists_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  intro E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨⟨hWN, -, hWI, hWc⟩, hW0⟩ := hW
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hfi
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have eg : jK W ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpW : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW

  have := t.semi.separated
  have := t.semi.smooth
  let p₀ : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G := by
    rw [← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]
    exact (GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2
      (GlobalTheory.DatUniq.polAt_of_unif P).1

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let Wv : Set (Sp V) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Wv :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hne : Wv ≠ Set.univ := fun h => by
    have : closedPoint V ∈ Wv := h ▸ Set.mem_univ _
    exact this.2 hϖ.not_isUnit
  have hψ : ∀ y, PsiUnitOn P.D.toPre y Wv := fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne
  have hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv := by
    have hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)
    rw [hk]
    exact ⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩
  have hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  obtain ⟨PW, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance
    hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩
  refine ⟨PW, e.symm, fun y r hr => ?_⟩
  obtain ⟨u, hu⟩ := he _ r hr
  exact ⟨u, by simpa using hu⟩

end GlobalTheory.UnifDvrBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocDerKDesc
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConst

open GlobalTheory.KS.GlueDer

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem desc_agree (hdd : ∀ a, IsField ⊤ (dd a)) {K : Type} [Field K] [CharZero K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (V : h.J → Q.P.A.left.Opens) (hV : ∀ i, h.W i = Y.q.left ⁻¹ᵁ V i)
    (e : h.J → Fld Q.P.A.left)
    (hq : ∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (e i V' f) = h.d i _ ((Y.q.left.app V').hom f))
    (i i' : h.J) (W : Q.P.A.left.Opens) (hW : W ≤ V i ⊓ V i') (f : Γ(Q.P.A.left, W)) :
    (m.app W).hom (e i W f) = (m.app W).hom (e i' W f) := by
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  refine FunDescent.app_injective b _ ?_
  show (b.app _).hom ((m.app W).hom _) = (b.app _).hom ((m.app W).hom _)
  rw [key, key, hq i W (hW.trans inf_le_left), hq i' W (hW.trans inf_le_right)]
  refine lift_agree h hdd i i' _ (le_inf ((pre_mono _ (hW.trans inf_le_left)).trans (hV i).ge)
    ((pre_mono _ (hW.trans inf_le_right)).trans (hV i').ge)) π ?_ (fun a b => ?_) _
  · have := (two_ne_zero (α := K)).isUnit.map ((((b ≫ p).appLE ⊤ (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (fun _ _ => trivial)).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    rwa [map_ofNat] at this
  · rw [hc, hΘ, constFn, map_zero, map_zero]

end Ray

theorem exists_locDerK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a, IsField ⊤ (dd a)) → IsBasic Y h → ∀ {K : Type} [Field K] [CharZero K] (φ : R →+* K), (∀ a b, φ (h.Θ a b) = 0) → ∀ {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left), m ≫ Q.P.A.hom = p ≫ spMap φ → ∃ dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W), GlobalTheory.KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) ⊤ dl ∧ (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m → ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB K _ _ φ hΘ Z p m hm
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  choose V hV using fun i => (hB i).1
  choose e he hq using fun i => exists_desc Y (V i) (h.d i) D (hV i ▸ h.lift i)
    fun V' hV' => (hB i).2.2.2 0 V' ((pre_mono _ hV').trans (hV i).ge)
  have hc := fun i i' W hW f => desc_agree Y h hdd φ hΘ p m hm V hV e hq i i' W hW f
  have hcov : ∀ y, ∃ i, m y ∈ V i := fun y => by
    obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact ⟨i, hx ▸ hi⟩
  have hloc : ∀ i, KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) (V i) (fun W f => (m.app W).hom (e i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(he i).1.1 W hW, map_add (f := _)]
    · rw [(he i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(he i).1.2.2 W W' h' hW, rsT_eq (pre_mono m h'), res_app m h']
    · rw [(he i).2 W hW, app_const φ _ p m hm]
  obtain ⟨dl, hdl, hu⟩ := InteriorKS.glue_along p Q.P.A.hom m _ V hcov (fun i W f => (m.app W).hom (e i W f)) hloc hc
  refine ⟨dl, hdl, fun Z' a b w i W hWi f => ?_⟩
  have hWV : W ≤ V i := fun x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    exact (hWi.trans (hV i).le) hx
  have e1 : dl W f = (m.app W).hom (e i W f) := by
    refine hu W f _ fun j => ?_
    rw [res_app m inf_le_left, ← (he i).1.2.2 W (W ⊓ V j) inf_le_left hWV f]
    exact hc i j _ (le_inf (inf_le_left.trans hWV) inf_le_right) _
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  rw [e1, pbT, pbT, dite_eq_left (le_refl _), dite_eq_left hle, ← hq i W hWV]
  have k : ∀ (c : Z' ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W) x,
      (b.appLE (m ⁻¹ᵁ W) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (le_refl _)).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
    rintro _ rfl hc x
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [k (a ≫ Y.q.left) w (by rw [Scheme.Hom.comp_preimage]; exact hle)]
  exact congrArg (fun ψ => ψ.hom (e i W f)) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)

end GlobalTheory.Heat.AbConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatchedFlipThetaIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BigNZ

theorem blkU_mul {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (h : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (x y : GA D A × GA D B) : blkU A B e h x * blkU A B e h y = blkU A B e h (x * y) := by
  refine Subtype.ext (Units.ext ?_)
  exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul e _ _ _ _

theorem exists_integral_ne_zero (hSA : GlobalTheory.Published.StrongApproxSU) (hK : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree)
    (hLM : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching) {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (hst : SquareStanding G t) :
    ∃ M : Vol G, M.Is t ∧ ∃ a τ τ' n Φ,
      (∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip B t ρ i j n Φ τ τ' ∧
      ∃ g g₁, ∫ u in M.fd _, kerBig W (tensT W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  classical
  obtain ⟨M, hM⟩ := exists_vol G hL t
  obtain ⟨e, Bs, Γ, X, om, om', h, hT, hti⟩ := _root_.GlobalTheory.BigNZ.Tied.squareTriple_tied hL W t i j hst M hM
  obtain ⟨R, Rf, hm⟩ := hLM _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨dec, hk⟩ := hK.1 _ _ _ Bs _ _ Γ X om om' hT
  obtain ⟨hc, hco⟩ := hk R Rf hm
  obtain ⟨l, hla, hl⟩ := _root_.GlobalTheory.ThetaIntAdm.exists_admissible_form_convergent_thetaIntegral Γ.M Bs.ψ _ _ om hT.weil dec.1
  have hw0 : G.pl.w G.pl.v0 ∈ locPl G t :=
    Finset.mem_union_left _ (by
      have : G.pl.v0 ∈ G.pl.S0 := by unfold Places.S0; convert Finset.mem_insert_self _ _
      unfold Places.W0; convert Finset.mem_image_of_mem _ this)
  have hv0 := (hti.2.2.1 _).2 ⟨_, hw0, rfl⟩
  have hd : 0 < (spW G i j).rank + (spW₁ G i j).rank := by have := hT.geo.aBig; omega
  obtain ⟨f, hf, h0⟩ := exists_I_ne_zero_at hm hc hco hla hl (_root_.GlobalTheory.RatInvTheta.thetaSum_rat_inv Bs Γ X om om' hT 1 (one_mem _)) hv0
    (GlobalTheory.T.weilRepresentationLocality_tensorModelVW Bs Γ X om om' hT _) (_root_.GlobalTheory.SplitApprox.strongApprox_split hSA Bs Γ X om om' hT ⟨_, hT.chars.sub hv0⟩)
    (H := Set.range (blkU _ _ e h.JWW)) fun x => by
      obtain ⟨s, g, h1, h2⟩ := _root_.GlobalTheory.DetDecomp.exists_detOne_mul_blkU _ _ e h.JWW hd x
      exact ⟨s, _, ⟨g, rfl⟩, h1, h2⟩
  obtain ⟨φ, hφ, hP, _, ⟨g, rfl⟩, hne⟩ := exists_I_ne_zero_kind hm hc hco (H := Set.range (blkU _ _ e h.JWW))
    (by rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩; exact ⟨x * y, (blkU_mul _ _ e h.JWW x y).symm⟩)
    (fun v χ => ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → ∃ n Φ, depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w v (flipAt W t i j w n Φ) χ)
    (fun v hv φ₀ hφ₀ => by
      obtain ⟨w, hw, ew⟩ := (hti.2.2.1 v).1 hv
      obtain ⟨n, Φ, φ₂, k, φ₃, h1, h2, h3, h4, h5, h6⟩ := _root_.GlobalTheory.SquareFlipReach.flip_reach hL W B t i j M hst e Bs Γ X om om' h R Rf hm hti w hw v ew φ₀ hφ₀
      refine ⟨φ₂, h3.1, fun w' hw' ew' => ?_, _, ⟨k, rfl⟩, φ₃, h4, h5, h6⟩
      obtain rfl : w = w' := (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w hw ew).symm.trans (hti.2.2.2 ⟨v, hT.chars.sub hv⟩ w' hw' ew')
      exact ⟨n, Φ, h1, h2, h3⟩) hf h0
  have H : ∀ w, ∃ n Φ, w ∈ locPl G t → depthAt G w ≤ n ∧ IsNatDatum (unifAt w) n Φ ∧
      IsLocFn W B t e Γ w (w.under (𝓞 D.host.F)) (flipAt W t i j w n Φ) (φ (w.under (𝓞 D.host.F))) := fun w => by
    by_cases hw : w ∈ locPl G t
    · obtain ⟨n, Φ, H⟩ := hP _ ((hti.2.2.1 _).2 ⟨w, hw, rfl⟩) w hw rfl
      exact ⟨n, Φ, fun _ => H⟩
    · exact ⟨0, 0, fun h => absurd h hw⟩
  choose n Φ H using H
  have hnat : ∀ w ∈ locPl G t, depthAt G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w) := fun w hw => ⟨(H w hw).1, (H w hw).2.1⟩
  obtain ⟨τ, τ', hF, -⟩ := (LocTensor.local_tensors hL B ρ t i j).2.2.2 (fun w hw hmem => hst.2 w hw (by
    have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
        (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
    rw [e]; exact Ideal.mul_mem_left _ _ hmem)) n Φ hnat
  obtain ⟨f₀, h1, h2, h3⟩ := GlobalTheory.T.exists_gaussianDatum_flippedFiniteTensor_bigRoute hL W B ρ t i j M hst e Bs Γ X om om' h hT hti n Φ τ τ' hnat hF φ hφ
    fun w hw => (H w hw).2.2
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.BigNZ.DatReal.datum_real hL W B ρ t i j M e Bs Γ X om om' h hT n Φ τ τ' hF φ hφ f₀ h1 h2 h3 f hf
  obtain ⟨b', hb'⟩ := ρ.onto_big i j (toTens a)
  obtain ⟨b, rfl⟩ := toTens_surjective b'
  have hΘ : IsMatched B t ρ i j (tensT W a τ) (tensT W b τ') := ⟨a, b, τ, τ', n, Φ, hb', hnat, hF, rfl, rfl⟩
  obtain ⟨ξ, hξ, hker⟩ := _root_.GlobalTheory.BigKernel.kerBig_eq_theta hL W B ρ t i j M _ _ hΘ e Bs Γ X om om' h hT _ ha g.1 g.2
  refine ⟨M, hM, a, τ, τ', n, Φ, hnat, hF, g.1, g.2, ?_⟩
  have hfd := (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund
  simp only [hker]
  rw [integral_const_mul, _root_.GlobalTheory.ConjUIntegral.setIntegral_conjU_eq _ 1 one_ne_zero h.JW _ _ hfd.1 hfd.2 Γ.M.dom (h.μW ▸ hT.geo.hM.dom)
    (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om _ x _) fun γ hγ x => ?_, ← h.μW]
  · exact mul_ne_zero hξ hne
  · have e3 : ((γ * x, blkU _ _ e h.JWW (g.1, g.2)) : UB Γ.V.J × UB Γ.W.J) = (γ, 1) * (x, blkU _ _ e h.JWW (g.1, g.2)) := by
      simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta]
    rw [e3, map_mul, Module.End.mul_apply,
      _root_.GlobalTheory.RatInvTheta.thetaSum_rat_inv Bs Γ X om om' hT γ hγ 1 (one_mem _) _ (hT.weil.isUSplitting.pres _ _ ha.1)]

open Formalism.IndefR GlobalTheory.RowTest GlobalTheory.RowClaim

theorem splitBound_ge : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ _ => 11 ≤ D.host.splitBound :=
  ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS _ _ _ => hS.size.2.1.eleven_le⟩⟩

theorem standing : Big fun ch => ∀ t, SquareStanding ch.G t := by
  obtain ⟨CF0, hH⟩ := splitBound_ge.and GlobalTheory.PlacesPrime.places_prime_to_level
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc t => ?_⟩
  obtain ⟨h11, hW⟩ := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc
  refine ⟨h11, fun w hw => ?_⟩
  classical
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with hw | hw
  · exact hW w hw
  · intro hmem
    have h1 := (hS.core.lev.Q_off t w hw).1
    have h2 := hS.guard.2 t w hw
    push_cast at hmem h1 h2
    rcases w.isPrime.mem_or_mem hmem with h | h
    · exact h1 (Ideal.mul_mem_right _ _ h)
    · exact h2 (Ideal.mul_mem_left _ _ h)

end GlobalTheory.BigNZ

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBl
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.NormBlowupField

theorem exists_normBl : ∀ (K : Type) [Field K] [CharZero K] (Z : Scheme.{0}) (z : Z ⟶ Sp K),
    IsProjOver z → GlobalTheory.IsNormalScheme Z → ∀ (J : Z.IdealSheafData) (W : Z.Opens),
    Dense (W : Set Z) → (∀ x ∈ J.support, x ∉ W) → ∃ (S : Scheme.{0}) (π : S ⟶ Z)
    (BD : EffCartierData S), GlobalTheory.Poinc.IsNormBl π J ∧ IsProjOver (π ≫ z) ∧ IsProper π ∧
    BD.idealSheaf = J.comap π ∧ IsIso (π ∣_ W) ∧ Dense (π ⁻¹' W : Set S) := by
  intro K _ _ Z z hz hZ J W hWd hWJ
  obtain ⟨X', b, hb, hbs, hiso⟩ := GlobalTheory.ProjBlowup.exists_blowup z hz J
  haveI : LocallyOfFiniteType (b ≫ z) := by
    obtain ⟨m, i, hi, e⟩ := hbs
    have := isProper_str K m
    rw [← e]; infer_instance
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian (b ≫ z)
  let V : X'.Opens := b ⁻¹ᵁ W
  haveI hbW : IsIso (b ∣_ W) := hiso W fun x hx hJ => hWJ x hJ hx
  haveI hoi : IsOpenImmersion (V.ι ≫ b) := by
    rw [← morphismRestrict_ι]; infer_instance
  haveI hN : GlobalTheory.IsNormalScheme V.toScheme := .of_isOpenImmersion (V.ι ≫ b)
  haveI : IsReduced V.toScheme := by
    exact inferInstance
  haveI hfin : IsFinite V.ι.fromNormalization :=
    isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of K) V.ι (b ≫ z)
      (fun x _ => charZero_of_injective_ringHom (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (V.ι ≫ b ≫ z).appTop ≫ V.toScheme.presheaf.germ ⊤ x trivial ≫ V.toScheme.residue x).hom)
        (RingHom.injective _))
      fun x _ => (LocallyOfFiniteType.stalkMap V.ι x).residueFieldMap
  let ν := V.ι.fromNormalization
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V.ι.normalization := IsNormalScheme.pred _
  have hν : IsIso (ν ∣_ V) := by
    have H := isPullback_toNormalization_of_mono (𝟙 _) V.ι V.ι (Category.id_comp _).symm
    have e := IsPullback.isoIsPullback_hom_fst _ _ (isPullback_morphismRestrict V.ι.fromNormalization V) H.flip
    rw [← e]
    infer_instance
  have hd : Dense ((ν ⁻¹ᵁ V : V.ι.normalization.Opens) : Set V.ι.normalization) := by
    refine V.ι.toNormalization.denseRange.mono ?_
    rintro _ ⟨x, rfl⟩
    change V.ι.fromNormalization (V.ι.toNormalization x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization]
    exact x.2
  have hVd : Dense (V : Set X') := GlobalTheory.NormBlowupInt.dense_preimage_of_blowup J b hb hiso W hWd
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hb.1
  have hK : D.KeepsRegular ν := by
    refine D.keepsRegular_of_dense ν (fun y => (hS y).1) (hd.mono fun t ht => ?_)
    show ν t ∉ D.idealSheaf.support
    rw [hD, GlobalTheory.ProjBlowup.mem_support_comap]
    exact fun h => hWJ _ h ht
  have hproj : IsProjOver ((ν ≫ b) ≫ z) := by
    rw [Category.assoc]; exact isProjOver_comp_of_isFinite ν hbs
  have hprop : IsProper (ν ≫ b) := by
    haveI : IsProper z := by
      obtain ⟨m, i, hi, e⟩ := hz
      have := isProper_str K m
      rw [← e]; infer_instance
    haveI : IsProper ((ν ≫ b) ≫ z) := by
      obtain ⟨m, i, hi, e⟩ := hproj
      have := isProper_str K m
      rw [← e]; infer_instance
    exact IsProper.of_comp (ν ≫ b) z
  refine ⟨V.ι.normalization, ν ≫ b, D.pull ν hK,
    ⟨inferInstance, X', b, ν, V, hb, rfl, hfin, hVd, hd, hν⟩, hproj, hprop, ?_, ?_, ?_⟩
  · rw [EffCartierData.idealSheaf_pull, hD, Scheme.IdealSheafData.comap_comp]
  · rw [morphismRestrict_comp]; exact IsIso.comp_isIso' hν hbW
  · convert hd using 1
    ext t
    simp [V]

end GlobalTheory.NormBlowupField
end
end

