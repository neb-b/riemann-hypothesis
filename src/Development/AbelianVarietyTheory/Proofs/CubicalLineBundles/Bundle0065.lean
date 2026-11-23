module

public import Mathlib
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsMetricConjugateFramedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem isLieComb_of_two_pullbacks {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {X : Scheme.{0}}
    {x : Sp R ⟶ X} {x' : Sp S ⟶ X} (hx : x' = spMap f ≫ x) {G : Over X} [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀]
    {G' : Over (Sp S)} [GrpObj G'] {φ : G₀.left ⟶ G.left} {φ' : G'.left ⟶ G.left}
    (h : IsGrpPullback G₀ G x φ) (h' : IsGrpPullback G' G x' φ') {n n' : ℕ} (hn : n' = n)
    {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀} (hc : IsLieComb c v w)
    {v' : Fin n' → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ (v (i.cast hn)).left ≫ φ)
    (hw : w'.left ≫ φ' = spMap (Formalism.L2.Pj.dualMap f) ≫ w.left ≫ φ) :
    IsLieComb (fun i => f (c (i.cast hn))) v' w' := by
  subst hn
  subst hx
  have hw0 : φ' ≫ G.hom = (G'.hom ≫ spMap f) ≫ x := by rw [Category.assoc]; exact h'.1.w
  have hψ1 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ φ = φ' := h.1.lift_fst _ _ _
  have hψ2 : h.1.lift φ' (G'.hom ≫ spMap f) hw0 ≫ G₀.hom = G'.hom ≫ spMap f := h.1.lift_snd _ _ _
  have hG : IsGrpPullback G' G₀ (spMap f) (h.1.lift φ' (G'.hom ≫ spMap f) hw0) :=
    IsGrpPullback.cancel h (IsGrpPullback.congr h' rfl hψ1.symm) hψ2
  have he : (algebraMap S (DualNumber S)).comp f = (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) := by
    clear h h' hv hw hc hG hψ1 hψ2 hw0
    first
    | exact RingHom.ext fun r => rfl
    | (ext r <;> simp [Chart.dualMapR] <;> rfl)
    | (ext r <;> simp [Chart.dualMapR] <;> erw [TrivSqZeroExt.algebraMap_eq_inl] <;> simp <;> done)
    | (ext r <;> simp [Chart.dualMapR] <;> simp [Algebra.algebraMap_eq_smul_one] <;> done)
    | (ext r
       · simp [Chart.dualMapR]
         show f r = f r
         rfl
       · simp [Chart.dualMapR]
         show (0 : S) = f 0
         simp)
  refine ReciprocityTheory.ChartRestriction.G.Chart.comb_baseChange f hG hc (fun i => ?_) ?_
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hv i, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w (v' i), Category.assoc, Over.w (v i)]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])
  · apply h.1.hom_ext
    · rw [Category.assoc, hψ1, hw, Category.assoc]
      rfl
    · rw [Category.assoc, hψ2, ← Category.assoc, Over.w w', Category.assoc, Over.w w]
      first
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← spMap_comp, ← spMap_comp, he])
      | (show spMap _ ≫ spMap f = spMap _ ≫ spMap _
         rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, he])
      | (unfold epsR; simp only [Over.mk_hom, ← spMap_comp, he])
      | (show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
         rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, he])

theorem hermForm_map_conj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.map (starRingEnd ℂ)) (fun i => starRingEnd ℂ (z i)) (fun i => starRingEnd ℂ (w i)) =
      starRingEnd ℂ (hermForm Hm z w) := by
  unfold hermForm
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply]

theorem isMetricAt_of_dim {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (x : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x))
    (uu : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (Φ : FibKey Xo ℂ x) (g : ℕ) (hg : Φ.key.P.g = g) (u : HolUnif Φ.key.P.A Φ.key.P.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
    (χ : u.Λ → ℂ) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ))
    (w : ∀ b : E →+* ℂ, Fin (Dw.mult b) → (epsR ℂ ⟶ Φ.key.P.A))
    (W : ∀ b : E →+* ℂ, Fin (Dw.mult b) → Fin g → ℂ)
    (h : SecTie Φ.m Φ.th s ∧ u.IsAH Hm χ ∧ u.IsRig Φ.key.rig ∧ u.IsFn Φ.key.th θ ∧
      IsAddFundamentalDomain u.Λ Fd volume ∧
      N = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal ∧
      (∀ b i, (w b i).left ≫ Φ.m.φ = uu b i ∧ u.IsDiff (W b i) (w b i)) ∧
      ∀ b i k, Gr b i k = Real.pi * hermForm Hm (W b k) (W b i)) : IsMetricAt x s uu N Gr := by
  subst hg
  exact ⟨Φ, u, Hm, χ, θ, Fd, w, W, h⟩

theorem isMetricAt_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} (hpq : 1 ≤ Dw.p + Dw.q) (x x' : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x'))
    (uu uu' : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (N : ℝ)
    (Gr : ∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)
    (hx : x' = spMap (starRingEnd ℂ) ≫ x) (hs : SecBC (starRingEnd ℂ) 1 x x' s s') (hgen : SecGen x' s')
    (ht : ∀ τ i, IsTanAt x (uu τ i)) (ht' : ∀ τ i, IsTanAt x' (uu' τ i))
    (hu : ∀ τ i, uu' τ i = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ uu τ i)
    (h : IsMetricAt x s uu N Gr) : IsMetricAt x' s' uu' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  obtain ⟨Φ, u, Hm, χ, θ, Fd, w, W, hT, hAH, hRig, hFn, hFd, hN, hw, hGr⟩ := h
  obtain ⟨Φ0⟩ := _root_.GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo ℂ x' hpq
  have hNZ : SecNZ x' s' := GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo ℂ x' s' hgen
  obtain ⟨-, hex, huniq⟩ := _root_.GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo ℂ x' Φ0.T.t Φ0.m
  obtain ⟨th, hth⟩ := hex s'
  have hne := ((huniq th s' hth).2).1 hNZ
  obtain ⟨hg, v', hv', hKey, hvrel⟩ := GlobalTheory.T.universalTripleFibreKeyData_baseChange_keyPullback E H Dw l Xo ℂ ℂ (starRingEnd ℂ) x x' Φ
    { Φ0 with th := th, th_ne := hne } s s' hx hT hth hs
  obtain ⟨u', χ', θ', Fd', hAH', hRig', hFn', hFd', hNeq, hdiff⟩ :=
    _root_.GlobalTheory.ConjUnif.exists_conj_unif Φ.key _ hKey hg _ u Hm χ θ Fd ⟨hAH, hRig, hFn, hFd⟩
  have hpb : ∀ (Ψ : FibKey Xo ℂ x'), IsGrpPullback Ψ.T.t.G Xo.univ.t.G x' Ψ.m.φ := by
    intro Ψ
    exact Ψ.m.cart
  have hpb0 : IsGrpPullback Φ.T.t.G Xo.univ.t.G x Φ.m.φ := Φ.m.cart
  have hcomb : ∀ b i, ∃ cf : Fin Φ.T.g → ℂ, IsLieComb cf Φ.v (w b i) := by
    intro b i
    have hTB := ((GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x _ Φ.m.φ hpb0).2 _ Φ.v).1 Φ.basis
    obtain ⟨a, ha, -⟩ := hTB.2 _ (ht b i)
    refine ⟨a, (ReciprocityTheory.ChartRestriction.G.Chart.comb_push hpb0 a Φ.v (w b i)).2 ?_⟩
    rw [← (hw b i).1] at ha
    exact ha
  choose cf hcf using hcomb
  have hw' : ∀ b i, ∃ w' : epsR ℂ ⟶ Φ0.T.t.G, w'.left ≫ Φ0.m.φ = uu' b i :=
    fun b i => (GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo ℂ x' Φ0.T.t.G Φ0.m.φ (hpb Φ0)).1 _ (ht' b i)
  choose w' hw'e using hw'
  refine isMetricAt_of_dim x' s' uu' N _ _ _ hg u' (Hm.map (starRingEnd ℂ)) χ' θ' Fd' w'
    (fun b i k => starRingEnd ℂ (W b i k)) ⟨hth, hAH', hRig', hFn', hFd', ?_, fun b i => ⟨hw'e b i, ?_⟩, fun b i k => ?_⟩
  · rw [hN, hNeq]
  · exact hdiff (cf b i) (w b i) (w' b i) (W b i) (hcf b i)
      (isLieComb_of_two_pullbacks (starRingEnd ℂ) hx hpb0 (hpb _) hg (hcf b i) hvrel
        (by rw [hw'e, hu, (hw b i).1])) (hw b i).2
  · rw [Matrix.map_apply, hGr, map_mul, hermForm_map_conj]
    simp

theorem scal_one_mul_sec {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s : LB.Sec (PPx x)) (i : (PPx x).ι) :
    scal x 1 i * s.f i = s.f i := by
  simp only [scal]
  first
  | rw [map_one, one_mul]
  | simp [Out.liftFun]

theorem isMetric_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((starRingEnd ℂ).comp σ))) (N : ℝ) (Gr : (∀ b : E →+* ℂ, Matrix (Fin (Dw.mult b)) (Fin (Dw.mult b)) ℂ)), 1 ≤ Dw.p + Dw.q → FrMap (FrameNorm.conjAlg σ) y y' → IsMetric y N Gr → IsMetric y' N (fun b => (Gr b).map (starRingEnd ℂ)) := by
  intro E _ _ _ H Dw l Xo c σ y y' N Gr hpq hF hM
  obtain ⟨hx, hu, pm, h1, h2, h3⟩ := hF
  unfold IsMetric at hM ⊢
  refine isMetricAt_conj hpq y.x y'.x y.s y'.s y.u y'.u N Gr hx ?_ y'.gen y.tan y'.tan hu hM
  refine ⟨pm, h1, h2, fun i h => ?_⟩
  have h4 := h3 i h
  first
  | exact (congrArg _ (scal_one_mul_sec (S := ℂ) y.x y.s i)).trans h4
  | exact (congrArg _ (scal_one_mul_sec y.x y.s i)).trans h4
  | (convert h4 using 2; exact scal_one_mul_sec (S := ℂ) y.x y.s i)
  | (convert h4 using 2; simp only [scal]; first | rw [map_one, one_mul] | simp [Out.liftFun])
  | (erw [scal_one_mul_sec]; exact h4)

end GlobalTheory.LamT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaLineDegreeAndHeightLowerBound
section
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem thetaDegree_and_lowerBound : (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi)) ∧ (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) :=
  have hdeg := _root_.GlobalTheory.thetaLine_dual_deg_of_keyFormulaPow GlobalTheory.keyFormulaPow_and_keyDegree.1
  ⟨hdeg, _root_.GlobalTheory.thetaLine_lower_bound_of_degree hdeg⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ThetaSectionNormAndHermitianFormIndepUniformisat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyUniq

theorem volume_image {g : ℕ} (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (s : Set (Fin g → ℂ)) :
    (volume (F '' s)).toReal = ‖LinearMap.det F‖ ^ 2 * (volume s).toReal := by
  have h := Measure.addHaar_image_linearMap volume (F.restrictScalars ℝ) s
  rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, abs_of_nonneg (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq] at h
  rw [show (F '' s) = (F.restrictScalars ℝ) '' s from rfl, h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volume_fund {g : ℕ} (Λ Λ' : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ']
    (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hF : ∀ z, F z ∈ Λ' ↔ z ∈ Λ) {s s' : Set (Fin g → ℂ)}
    (hs : IsAddFundamentalDomain Λ s volume) (hs' : IsAddFundamentalDomain Λ' s' volume) :
    (volume s').toReal = ‖LinearMap.det F.toLinearMap‖ ^ 2 * (volume s).toReal := by
  let φ : Λ' ≃ Λ :=
    { toFun := fun b => ⟨F.symm b, (hF _).1 (by rw [F.apply_symm_apply]; exact b.2)⟩
      invFun := fun a => ⟨F a, (hF a).2 a.2⟩
      left_inv := fun b => Subtype.ext (F.apply_symm_apply b.1)
      right_inv := fun a => Subtype.ext (F.symm_apply_apply a.1) }
  have hq : Measure.QuasiMeasurePreserving F.toEquiv.symm volume volume :=
    Measure.LinearMap.quasiMeasurePreserving volume (F.symm.restrictScalars ℝ).toLinearMap
      (F.symm.restrictScalars ℝ).isUnit_det'.ne_zero
  have h1 : IsAddFundamentalDomain Λ' (F.toEquiv '' s) volume :=
    hs.image_of_equiv F.toEquiv hq φ fun b z => by
      change F (F.symm b + z) = b + F z
      rw [map_add (f := _), F.apply_symm_apply]
  have : Countable Λ' := countable_of_Lindelof_of_discrete
  have : MeasurableConstVAdd Λ' (Fin g → ℂ) := ⟨fun c => measurable_const_add (c : Fin g → ℂ)⟩
  have : VAddInvariantMeasure Λ' (Fin g → ℂ) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : Fin g → ℂ) s⟩
  rw [hs'.measure_eq h1]
  exact volume_image F.toLinearMap s

theorem norm_eq_and_hermForm_eq : ∀ (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L x.P.g) (Hm : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin x.P.g → ℂ) → ℂ) (Fd : Set (Fin x.P.g → ℂ)) (u' : HolUnif x.P.A x.P.L x.P.g) (Hm' : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (χ' : u'.Λ → ℂ) (θ' : (Fin x.P.g → ℂ) → ℂ) (Fd' : Set (Fin x.P.g → ℂ)), u.IsAH Hm χ ∧ u.IsRig x.rig ∧ u.IsFn x.th θ ∧ IsAddFundamentalDomain u.Λ Fd volume → u'.IsAH Hm' χ' ∧ u'.IsRig x.rig ∧ u'.IsFn x.th θ' ∧ IsAddFundamentalDomain u'.Λ Fd' volume → (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = (∫ z in Fd', ‖θ' z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' z z).re)) / (volume Fd').toReal ∧ ∀ (v w : epsR ℂ ⟶ x.P.A) (V W V' W' : Fin x.P.g → ℂ), IsTangent v → IsTangent w → u.IsDiff V v → u.IsDiff W w → u'.IsDiff V' v → u'.IsDiff W' w → hermForm Hm V W = hermForm Hm' V' W' := by
  rintro x u Hm χ θ Fd u' Hm' χ' θ' Fd' ⟨hA, hR, hθ, hD⟩ ⟨hA', hR', hθ', hD'⟩
  obtain ⟨-, t1, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  obtain ⟨-, t1', t2'⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u' Hm' χ' hA'
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u' t1' t2' u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u' F hF)
  have hd : ∀ w v, u.IsDiff w v ↔ u'.IsDiff (F w) v :=
    UnifCompare.isDiff_iff u u' e.toContinuousLinearEquiv hF
  refine ⟨?_, fun v w V W V' W' hv hw h1 h2 h3 h4 => ?_⟩
  · obtain ⟨N, hN, κ, -, -, -, -, hK⟩ := keyFormulaPow_and_keyDegree.1
    choose W hW using fun i => (t1 _ (x.basis.1 i)).exists
    have k := hK x u Hm (Matrix.of W) χ θ Fd _ _ hA hR hθ hW hD rfl rfl
    have k' := hK x u' Hm' (Matrix.of fun i => F (W i)) χ' θ' Fd' _ _ hA' hR' hθ' (fun i => (hd _ _).1 (hW i)) hD' rfl rfl
    have := u'.discrete
    have hvol : (volume Fd').toReal = ‖LinearMap.det F‖ ^ 2 * (volume Fd).toReal :=
      volume_fund u.Λ u'.Λ e (UnifCompare.mem_iff u u' F hF) hD hD'
    have hdet : (Matrix.of fun i => F (W i)).det = LinearMap.det F * (Matrix.of W).det := by
      have : (Matrix.of fun i => F (W i)) = Matrix.of W * (LinearMap.toMatrix' F).transpose := by
        ext i j
        rw [Matrix.of_apply, ← LinearMap.toMatrix'_mulVec, Matrix.mul_apply, Matrix.mulVec, dotProduct]
        exact Finset.sum_congr rfl fun _ _ => _root_.mul_comm _ _
      rw [this, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix', _root_.mul_comm]
    have h0 : ‖LinearMap.det F‖ ≠ 0 := norm_ne_zero_iff.2 e.isUnit_det'.ne_zero
    have hη : (volume Fd').toReal / (Real.pi ^ x.P.g * ‖(Matrix.of fun i => F (W i)).det‖ ^ 2) =
        (volume Fd).toReal / (Real.pi ^ x.P.g * ‖(Matrix.of W).det‖ ^ 2) := by
      rw [hvol, hdet, norm_mul, mul_pow, mul_left_comm, mul_div_mul_left _ _ (pow_ne_zero 2 h0)]
    rw [hη] at k'
    have hne := k.trans_ne (pow_ne_zero _ Real.two_pi_pos.ne')
    have h1 := mul_left_cancel₀ (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
      (mul_right_cancel₀ (right_ne_zero_of_mul hne) (k.trans k'.symm))
    exact (pow_left_inj₀ (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (div_nonneg (integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg)
      (by have := hN x.P.g; omega)).1 h1
  · rw [(t1' v hv).unique h3 ((hd _ _).1 h1), (t1' w hw).unique h4 ((hd _ _).1 h2)]
    exact (UnifCompare.hermForm_eq x.P.isLB u u' hA hA' F hF V W).symm

end GlobalTheory.KeyUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationEqOfIsLocGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.KeyVal

theorem exists_unit_of_pow {R K' : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K'] [Algebra R K']
    [IsFractionRing R K'] {z : K'} {m : ℕ} (hm : 0 < m) (w : Rˣ) (h : z ^ m = algebraMap R K' w) :
    ∃ u : Rˣ, z = algebraMap R K' u := by
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (K := K') (x := z) hm
    (by rw [h]; exact isIntegral_algebraMap)
  have h1 : r ^ m = w := IsFractionRing.injective R K' (by rw [map_pow, hr, h])
  have h2 : IsUnit r := (isUnit_pow_iff hm.ne').1 (h1 ▸ w.isUnit)
  exact ⟨h2.unit, by simp [hr]⟩

theorem unit_iff {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K)) {R K' : Type} [CommRing R]
    [Field K'] [Algebra R K'] (hi : Function.Injective (algebraMap R K')) (f : K →+* K')
    (hv : ∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) (y : K) :
    (∃ u : Rˣ, f y = algebraMap R K' u) ↔ p.valuation K y = 1 := by
  constructor
  · rintro ⟨u, hu⟩
    have hy : y ≠ 0 := by
      rintro rfl
      exact (u.isUnit.map (algebraMap R K')).ne_zero (by rw [← hu, map_zero])
    refine eq_one_of_one_le_mul_left ((hv y).1 ⟨_, hu.symm⟩)
      ((hv y⁻¹).1 ⟨(u⁻¹ : Rˣ), by rw [map_units_inv, map_inv₀, hu]⟩) ?_
    rw [← map_mul, mul_inv_cancel₀ hy, map_one]
  · intro h
    have hy : y ≠ 0 := by
      rintro rfl
      simp at h
    obtain ⟨r, hr⟩ := (hv y).2 h.le
    obtain ⟨s, hs⟩ := (hv y⁻¹).2 (by rw [map_inv₀, h, inv_one])
    have e : r * s = 1 := hi (by rw [map_mul, hr, hs, ← map_mul, mul_inv_cancel₀ hy, map_one, map_one])
    exact ⟨Units.mkOfMulEqOne r s e, by simp [hr]⟩

theorem valuation_eq_of_isLocGen {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {c c' : K}
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (h : IsLocGen p c I) (h' : IsLocGen p c' I) :
    p.valuation K c = p.valuation K c' := by
  rw [valuation_eq_exp_count p h.1, valuation_eq_exp_count p h'.1, h.2, h'.2]

theorem exists_pow_rel (K : Type) [Field K] [NumberField K] (x : KeyIn K) :
    ∃ (n : ℕ) (k : K), 1 ≤ n ∧ k ≠ 0 ∧ ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K']
      [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K'), KeyPB x' x f →
      KeyIntegral R x' a d → ∃ u : Rˣ, a ^ (8 * n) * algebraMap R K' u = d ^ (4 * n) * f k := by
  obtain ⟨N, hN, κ, hH, hF, hU, -⟩ := GlobalTheory.keyFormulaPow_and_keyDegree.1
  refine ⟨N x.P.g, κ K x, hN _, (κ K x).ne_zero, ?_⟩
  intro R K' _ _ _ _ _ _ f x' a d hPB hInt
  haveI : CharZero K' := (RingHom.charZero_iff f.injective).1 inferInstance
  obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
  have hFx := hF K K' f x x' hPB
  have hHx := hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
  obtain ⟨u, hu, -⟩ := hU R K' xR _ hPBR
  have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
  refine ⟨u, ?_⟩
  rw [← hu, ← hFx, ← hMdet, ← hg]
  exact hHx

theorem integral_section_unit : ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (Tl abelian₂ : MLine K) (p : HeightOneSpectrum (𝓞 K)), KeyLocAt x Tl abelian₂ p → ∀ (R K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K'] [Algebra R K'] [IsFractionRing R K'] (f : K →+* K') (x' : KeyIn K') (a d : K') (ca cd : K) (ud : Rˣ), (∀ y : K, f y ∈ Set.range (algebraMap R K') ↔ p.valuation K y ≤ 1) → KeyPB x' x f → KeyIntegral R x' a d → IsLocGen p cd abelian₂.I → d = f cd * algebraMap R K' ud → IsLocGen p ca Tl.I → ∃ u : Rˣ, a = f ca * algebraMap R K' u := by
  intro K _ _ x Tl abelian₂ p hloc R K' _ _ _ _ _ _ f x' a d ca cd ud hval hPB hInt hcd hd hca
  obtain ⟨n, k, hn, hk, H⟩ := exists_pow_rel K x
  obtain ⟨K₁, _, _, R₁, _, _, _, _, _, f₁, x₁, a₁, d₁, ca₁, cd₁, ua₁, ud₁, hPB₁, hInt₁, hval₁, ha₁, hd₁, hca₁, hcd₁⟩ := hloc
  obtain ⟨u₁, hu₁⟩ := H R₁ K₁ f₁ x₁ a₁ d₁ hPB₁ hInt₁
  obtain ⟨u, hu⟩ := H R K' f x' a d hPB hInt
  have h1 : p.valuation K (cd₁ ^ (4 * n) * k / ca₁ ^ (8 * n)) = 1 := by
    refine (unit_iff p (IsFractionRing.injective R₁ K₁) f₁ hval₁ _).1 ⟨ua₁ ^ (8 * n) * u₁ * ud₁⁻¹ ^ (4 * n), ?_⟩
    have hfa : f₁ ca₁ ≠ 0 := (map_ne_zero f₁).2 hca₁.1
    have hD : algebraMap R₁ K₁ (ud₁ : R₁) ≠ 0 := (ud₁.isUnit.map (algebraMap R₁ K₁)).ne_zero
    rw [ha₁, hd₁, mul_pow, mul_pow] at hu₁
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_pow, map_units_inv, map_div₀, map_mul, map_pow, map_pow, inv_pow, ← div_eq_mul_inv,
      div_eq_div_iff (pow_ne_zero _ hfa) (pow_ne_zero _ hD)]
    linear_combination -hu₁
  have h2 : p.valuation K (cd ^ (4 * n) * k / ca ^ (8 * n)) = 1 := by
    rw [map_div₀, map_mul, map_pow, map_pow] at h1 ⊢
    rw [valuation_eq_of_isLocGen hca hca₁, valuation_eq_of_isLocGen hcd hcd₁, h1]
  obtain ⟨w, hw⟩ := (unit_iff p (IsFractionRing.injective R K') f hval _).2 h2
  have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
  have hU : algebraMap R K' (u : R) ≠ 0 := (u.isUnit.map (algebraMap R K')).ne_zero
  obtain ⟨t, ht⟩ := exists_unit_of_pow (R := R) (z := a / f ca) (m := 8 * n) (by omega) (w * ud ^ (4 * n) * u⁻¹) (by
    rw [hd, mul_pow] at hu
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_mul,
      map_pow, map_units_inv, ← hw, map_div₀, map_mul, map_pow, map_pow, div_pow, ← div_eq_mul_inv,
      eq_div_iff hU, div_mul_eq_mul_div, div_mul_eq_mul_div, hu]
    ring)
  exact ⟨t, by rw [← ht, mul_div_cancel₀ _ hfa]⟩

end GlobalTheory.KeyVal
end

