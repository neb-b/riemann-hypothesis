module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemIffConjugateNotMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnitHmA
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
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HermFormSumSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermNorm

section Form

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (h : HermFam K V) (s : K →+* ℂ)

theorem form_sum_right {J : Type} (t : Finset J) (x : V) (c : J → K) (y : J → V) :
    h.form s x (∑ j ∈ t, c j • y j) = ∑ j ∈ t, s (c j) * h.form s x (y j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using h.smul_right s 0 x 0
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, h.add_right, h.smul_right, ih]

theorem form_sum_left {J : Type} (t : Finset J) (c : J → K) (x : J → V) (y : V) :
    h.form s (∑ i ∈ t, c i • x i) y = ∑ i ∈ t, starRingEnd ℂ (s (c i)) * h.form s (x i) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h.conj_symm, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, h.conj_symm]

end Form

theorem hermForm_sum_sum {g n : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : Fin n → ℂ) (W : Fin n → Fin g → ℂ) :
    hermForm Hm (∑ i, a i • W i) (∑ i, a i • W i) =
      ∑ i, starRingEnd ℂ (a i) * ∑ j, a j * hermForm Hm (W j) (W i) := by
  simp only [hermForm, star_sum, star_smul, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
    sum_dotProduct, smul_dotProduct, smul_eq_mul, Complex.star_def]

theorem form_eq {K : Type} [Field K] {g n : ℕ} (h : HermFam K (Fin n → K)) (s : K →+* ℂ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (W : Fin n → Fin g → ℂ) (r : ℂ)
    (e : ∀ i j, h.form s (Pi.single i 1) (Pi.single j 1) = r * hermForm Hm (W j) (W i)) (c : Fin n → K) :
    h.form s c c = r * hermForm Hm (∑ i, s (c i) • W i) (∑ i, s (c i) • W i) := by
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := pi_eq_sum_univ' c
  rw [hermForm_sum_sum, Finset.mul_sum]
  conv_lhs => rw [hc, form_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [form_sum_right, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [e]; ring

theorem isLieNormSq_form : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (h : HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (s : K →+* ℂ) u c, F.IsCoord u c → IsLieNormSq P u (s.comp (algebraMap (𝓞 K) K)) (h.form s c c).re := by
  rintro - - K _ _ P F h hh s u c ⟨-, w, hw, hc⟩
  obtain ⟨Q, ψ, v', U, Hm, χ, W, hQ, hA, hv, e⟩ := hh s
  refine (EllComp.isLieNormSq_iff F.fib hw s _).1 ?_
  obtain ⟨w', hw', -⟩ := existsUnique_isVecOver hQ.2.1.1 w
  have hc' := (lieComb_baseChange _ _ s _ _ ψ hQ.2.1 _ F.v w c v' w' (fun i => (hv i).1) hc).1 hw'
  refine ⟨Q, ψ, w', U, Hm, χ, ∑ i, s (c i) • W i, hQ, hw', hA,
    UnifDifferential.isDiff_of_isLieComb _ _ _ _ U W v' _ w'
      (fun i => (hv i).1.isTangent hQ.2.1 (F.basis.1 i)) (fun i => (hv i).2) hc', ?_⟩
  rw [form_eq h s Hm W _ e, Complex.re_ofReal_mul]

end GlobalTheory.CM.HermNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ImDiagEqTrace
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.OrthoHerm


open scoped Matrix ComplexConjugate in
theorem im_diag_eq_trace {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (q : ℕ) (ξ : E)
    (Gm : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (idx : Fin g ≃ Ψ × Fin r)
    (hξ : FD.cc ξ = -ξ) (x : FD.Frame Ψ r)
    (hx : ∀ τ : Ψ, FD.gram τ.1 Gm (FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((FD.sgn q (a : ℕ) : ℝ) : ℂ))
    (v w : Fin r → E) (z z' : Fin g → ℂ)
    (hz : ∀ k, z k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 v)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 v) (idx k).2)
    (hz' : ∀ k, z' k = if ((idx k).2 : ℕ) < q then
      FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 w)
      else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 w) (idx k).2) :
    (hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ)) z z').im =
      ((Algebra.trace ℚ E (ξ * FD.herm Gm v w) : ℚ) : ℝ) := by
  rw [GlobalTheory.UnitFrame.trace_eq_sum_re Ψ hΨ]
  let p : (Fin r → E) → Ψ × Fin r → ℂ := fun v t =>
    if (t.2 : ℕ) < q then
      FD.hermC t.1.1 Gm (FD.col (FD.mat x t.1) t.2) (FD.Data.emb t.1.1 v)
    else ((FD.mat x t.1)⁻¹ *ᵥ FD.Data.emb t.1.1 v) t.2
  have h2 : hermForm (Matrix.diagonal fun k => ((2 * ((idx k).1.1 ξ).im : ℝ) : ℂ)) z z' =
      ∑ t : Ψ × Fin r, ((2 * (t.1.1 ξ).im : ℝ) : ℂ) * (p v t * conj (p w t)) := by
    rw [hermForm, dotProduct]
    refine Fintype.sum_equiv idx _ _ fun k => ?_
    rw [Matrix.mulVec_diagonal, Pi.star_apply, hz, hz']
    simp only [p, RCLike.star_def]
    ring
  rw [h2, Fintype.sum_prod_type, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [p]
  rw [← Finset.mul_sum, Complex.im_ofReal_mul,
    GlobalTheory.UnitFrame.im_sum_periods q τ.1 Gm (FD.mat x τ) (hx τ)]
  have h3 : τ.1 (FD.herm Gm v w) = FD.hermC τ.1 Gm (FD.Data.emb τ.1 v) (FD.Data.emb τ.1 w) := by
    simp [FD.hermC, FD.herm, FD.Data.emb, FD.cc, IsCMField.complexEmbedding_complexConj]
  have hre : (τ.1 ξ).re = 0 := by
    have h := congrArg τ.1 hξ
    rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg] at h
    have := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at this
    linarith
  rw [map_mul, h3, Complex.mul_re, hre]
  ring

theorem hm_eq_smul_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (ξ : ℝ), GoodEmb c σ → IsUnf U → ∀ (k : U.Comp) (x : (U.X k).dom) (W : PullbackSections.UnfAt U k x) (Wu : PullbackSections.UnitAt W), (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ) → (U.X k).IsOrtho x.1 → Wu.Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1 (relab c σ) hbij
    Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  have hper : ∀ (v : Fin r → E) j, perFr (U.X k) x.1 v (relab c σ (W.e j).1) (W.e j).2 =
      if (((W.e.trans f) j).2 : ℕ) < (U.X k).p0 then
        FD.hermC ((W.e.trans f) j).1.1 (U.X k).Gm
          (FD.col (FD.mat x.1 ((W.e.trans f) j).1) ((W.e.trans f) j).2) (FD.Data.emb ((W.e.trans f) j).1.1 v)
      else ((FD.mat x.1 ((W.e.trans f) j).1)⁻¹.mulVec (FD.Data.emb ((W.e.trans f) j).1.1 v))
        ((W.e.trans f) j).2 := by
    intro v j
    have h := hf (W.e j)
    rw [Equiv.trans_apply]
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    generalize ((W.e j).2 : ℕ) = i at h ⊢
    dsimp only at h ⊢
    rw [← hp0] at h
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega)]
      unfold perFr
      rw [dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega)]
      unfold perFr
      rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have key : Wu.Hm = Matrix.diagonal fun j => ((2 * (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) := by
    refine PullbackSections.UH.herm_eq_of_im W.Pm W.per.2.2.2.1 _ _ fun a b => ?_
    rw [Wu.c1, im_diag_eq_trace (U.X k).p0 _ (U.X k).Gm (U.X k).Ψ (U.X k).cmType (W.e.trans f) hcc x.1 hx
      (W.φ k a) (W.φ k b) _ _ (fun j => (W.pm_eq a j).trans (hper _ j)) (fun j => (W.pm_eq b j).trans (hper _ j)),
      ← W.isom, Rat.cast_intCast]
  have hd : ∀ j, (((W.e.trans f) j).1.1 (-(U.X k).ξ0)).im = ξ := by
    intro j
    have hpos := Wu.pos (Pi.single j 1) (by simp)
    rw [key, hermForm, single_dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Pi.single_eq_same, star_one,
      _root_.one_mul, _root_.mul_one, Complex.ofReal_re] at hpos
    generalize ((W.e.trans f) j).1.1 = τ at hpos ⊢
    have hre : (τ (-(U.X k).ξ0)).re = 0 := by
      have h := congrArg τ hcc
      rw [FD.cc, IsCMField.complexEmbedding_complexConj, map_neg τ (-(U.X k).ξ0)] at h
      have := congrArg Complex.re h
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
    have hp : 0 < (τ (-(U.X k).ξ0)).im := by linarith
    rw [← hξ τ, ← norm_neg, ← map_neg, ← Complex.abs_im_eq_norm.mpr hre, abs_of_pos hp]
  rw [key]
  simp only [hd]
  rw [Matrix.smul_one_eq_diagonal]

end GlobalTheory.OrthoHerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegralEigenbasisBaseChangeDvr
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.LieIntBC

open Matrix
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec univChartLoc tanBC_alg tvec_tmap fB IsUnivChart sp JetR)
open Formalism.L2.Pj.LieRel
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

theorem flat_of_inj {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B] [Algebra A B]
    (hi : Function.Injective (algebraMap A B)) : Module.Flat A B := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : algebraMap A B a * x = 0 := (Algebra.smul_def a x).symm.trans hx
  have ha' : algebraMap A B a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem eig_flat {V V' : Type} [CommRing V] [IsNoetherianRing V] [CommRing V'] [Algebra V V'] [Module.Flat V V']
    {n m : ℕ} {J : Type} (L : J → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : J → V)
    (L' : J → (Fin n → V') →ₗ[V'] (Fin n → V'))
    (hL : ∀ a c, L' a (algebraMap V V' ∘ c) = algebraMap V V' ∘ L a c)
    (b : Fin m → Fin n → V) (hb : ∀ k a, L a (b k) = χ a • b k)
    (hbb : ∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ k, r k • b k)
    (w : Fin n → V') (hw : ∀ a, L' a w = algebraMap V V' (χ a) • w) :
    ∃! r : Fin m → V', w = ∑ k, r k • (algebraMap V V' ∘ b k) := by
  let M : J → Matrix (Fin n) (Fin n) V := fun a => Matrix.of fun j => L a (Pi.single j 1)
  have hM : ∀ a c, c ᵥ* M a = L a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    refine congrArg (fun q => c k * L a q j) ?_
    funext s
    simp [Pi.single_apply, eq_comm]
  have hM' : ∀ a c, c ᵥ* (M a).map (algebraMap V V') = L' a c := fun a c => by
    funext j
    rw [LinearMap.pi_apply_eq_sum_univ (L' a) c]
    simp only [M, Matrix.vecMul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    refine (congrFun (hL a (Pi.single k 1)) j).symm.trans ?_
    refine congrArg (fun q => L' a q j) ?_
    funext s
    by_cases h : k = s <;> simp [Pi.single_apply, h, eq_comm]
  refine (GlobalTheory.commonEigenvectors_flat_baseChange V J n m M χ).1 V b (fun k a => (hM a _).trans (hb k a))
    (fun z hz => ?_) V' w (fun a => (hM' a w).trans (hw a))
  simp only [Algebra.algebraMap_self, RingHom.id_apply, RingHom.coe_id, Matrix.map_id] at hz ⊢
  exact hbb z fun a => (hM a z).symm.trans (hz a)

theorem univChart_iso {S : Type} [CommRing S] {G G' : Over (Spec (CommRingCat.of S))} [GrpObj G] [GrpObj G']
    (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {x : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsUnivChart G' n (fun m => x m ≫ e.inv) := by
  have one : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G') ≫ e.hom = 1 := fun T =>
    map_one (IsMonHom.monoidHom e.hom T)
  have one' : ∀ T : Over (Spec (CommRingCat.of S)), (1 : T ⟶ G) ≫ e.inv = 1 := fun T => by
    rw [← one, Category.assoc, e.hom_inv_id, Category.comp_id]
  refine ⟨fun m => ?_, fun m => ?_, fun A _ _ aug m hm y hy => ?_⟩
  · rw [← Category.assoc, hx.1]
  · rw [← Category.assoc, hx.2.1, one']
  · have := hx.2.2 A aug m hm (y ≫ e.hom) (by rw [← Category.assoc, hy, one])
    simpa only [← Category.assoc, Iso.eq_comp_inv] using this

theorem exists_charts {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] {G₀ : Over (Sp R)} [GrpObj G₀]
    [Smooth G₀.hom] {G : Over (Sp S)} [GrpObj G] (f : R →+* S) {φ : G.left ⟶ G₀.left}
    (h : IsGrpPullback G G₀ (spMap f) φ) :
    ∃ (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (ReciprocityTheory.ChartRestriction.G.Chart.JetR R (Fin n) m) ⟶ G₀) (x' : ∀ m : ℕ, sp (R₀ := S) (ReciprocityTheory.ChartRestriction.G.Chart.JetR S (Fin n) m) ⟶ G),
      IsUnivChart G₀ n x ∧ IsUnivChart G n x' ∧ ∀ c : Fin n → R,
        (tvec (x := x') (f ∘ c)).left ≫ φ = spMap (Formalism.L2.Pj.dualMap f) ≫ (tvec (x := x) c).left := by
  let _ := f.toAlgebra
  obtain ⟨n, x, hx⟩ := univChartLoc G₀
  obtain ⟨x', hx', hc⟩ := tanBC_alg (R' := S) G₀ n x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G₀ (fB R S))
  refine ⟨n, x, _, hx, univChart_iso e hx', fun c => ?_⟩
  have e1 : tvec (x := fun m => x' m ≫ e.inv) (f ∘ c) = tvec (x := x') (f ∘ c) ≫ e.inv := (Category.assoc _ _ _).symm
  rw [e1, ← heφ, ← Category.assoc, ← Over.comp_left, Category.assoc, e.inv_hom_id, Category.comp_id]
  exact hc c

theorem sp_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : S →+* T) (g : R →+* S) :
    spMap (Formalism.L2.Pj.dualMap f) ≫ spMap (Formalism.L2.Pj.dualMap g) = spMap (Formalism.L2.Pj.dualMap (f.comp g)) := by
  rw [sp_comp]
  congr 1
  refine RingHom.ext fun s => ?_
  ext <;> simp [Formalism.L2.Pj.dualMap]

end GlobalTheory.LamT.LieIntBC

namespace GlobalTheory.LamT

open LieIntBC Formalism.L2.Pj.LieRel
open ReciprocityTheory.ChartRestriction.G.Chart (tvec tmap tvec_inj isTan_tvec tvec_tmap)

theorem lieInt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (T T' : CDVR) (ψ : T.V →+* T'.V) (i : T.Fr →+* T'.Fr), (algebraMap T'.V T'.Fr).comp ψ = i.comp (algebraMap T.V T.Fr) → ∀ (x : Sp T.Fr ⟶ Xo.X) (x' : Sp T'.Fr ⟶ Xo.X) (G : PAT H (Sp T.V)) (G' : PAT H (Sp T'.V)) (t : SAB H (Sp T.Fr)) (t' : SAB H (Sp T'.Fr)) (m1 : SABMap t Xo.univ.t x) (m2 : SABMap t G.t (spMap (algebraMap T.V T.Fr))) (m1' : SABMap t' Xo.univ.t x') (m2' : SABMap t' G'.t (spMap (algebraMap T'.V T'.Fr))) (n : SABMap G'.t G.t (spMap ψ)) (n' : SABMap t' t (spMap i)), x' = spMap i ≫ x → m1'.φ = n'.φ ≫ m1.φ → m2'.φ ≫ n.φ = n'.φ ≫ m2.φ → ∀ (io : c.F →+* T.Fr) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)), LieInt T io m1 m2 u → LieInt T' (i.comp io) m1' m2' (fun τ k => spMap (Formalism.L2.Pj.dualMap i) ≫ u τ k) := by
  intro E _ _ _ H Dw l Xo c T T' ψ i hψ x x' G G' t t' m1 m2 m1' m2' n n' hx h1 h2 io u hu
  obtain ⟨ub, ht, he, hb, hu⟩ := hu
  have := G.t.semi.smooth
  have : ∀ a, IsMonHom (G.t.act.act a) := G.t.act.hom
  have : ∀ a, IsMonHom (G'.t.act.act a) := G'.t.act.hom
  have hψ' : ∀ z, algebraMap T'.V T'.Fr (ψ z) = i (algebraMap T.V T.Fr z) := fun z => RingHom.congr_fun hψ z
  have hinj : Function.Injective ψ := fun a b hab =>
    IsFractionRing.injective T.V T.Fr (i.injective (by rw [← hψ', ← hψ', hab]))
  let _ := ψ.toAlgebra
  have : Module.Flat T.V T'.V := flat_of_inj hinj
  obtain ⟨N, xc, xc', hxc, hxc', hcomp⟩ := exists_charts ψ n.cart
  have hM : ∀ (a : 𝓞 E) (cc : Fin N → T.V),
      tmap hxc' (G'.t.act.act a) (ψ ∘ cc) = ψ ∘ tmap hxc (G.t.act.act a) cc := by
    intro a cc
    apply tvec_inj hxc'
    rw [tvec_tmap hxc']
    refine Over.OverMorphism.ext (n.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [hcomp, tvec_tmap hxc, Over.comp_left, Over.comp_left, Category.assoc, n.act, ← Category.assoc, hcomp,
      Category.assoc]
  choose χ hχ using fun τ a => int_val c T io τ a
  have hχ' : ∀ τ a, algebraMap T'.V T'.Fr (ψ (χ τ a)) = (i.comp io) (embK c τ a) := fun τ a => by
    rw [hψ', hχ]; rfl
  have eig : ∀ τ cc, IsEigV c io G.t τ (cvV (tvec (x := xc) cc)) ↔
      ∀ a, tmap hxc (G.t.act.act a) cc = χ τ a • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc _ cc _).1 (h a _ (hχ τ a)), fun h a z hz => by
      obtain rfl : z = χ τ a := IsFractionRing.injective T.V T.Fr (hz.trans (hχ τ a).symm)
      exact (eigV_iff hxc _ cc _).2 (h a)⟩
  have eig' : ∀ τ cc, IsEigV c (i.comp io) G'.t τ (cvV (tvec (x := xc') cc)) ↔
      ∀ a, tmap hxc' (G'.t.act.act a) cc = ψ (χ τ a) • cc := fun τ cc =>
    ⟨fun h a => (eigV_iff hxc' _ cc _).1 (h a _ (hχ' τ a)), fun h a z hz => by
      obtain rfl : z = ψ (χ τ a) := IsFractionRing.injective T'.V T'.Fr (hz.trans (hχ' τ a).symm)
      exact (eigV_iff hxc' _ cc _).2 (h a)⟩
  choose b hbe using fun τ k => tan_eq_cvV hxc (ht τ k)
  obtain rfl : ub = fun τ k => cvV (tvec (x := xc) (b τ k)) := funext fun τ => funext fun k => hbe τ k
  have hbe' : ∀ τ k a, tmap hxc (G.t.act.act a) (b τ k) = χ τ a • b τ k := fun τ k => (eig τ _).1 (he τ k)
  refine ⟨fun τ k => cvV (tvec (x := xc') (ψ ∘ b τ k)), fun τ k => isTan_cvV (isTan_tvec hxc' _),
    fun τ k => (eig' τ _).2 fun a => ?_, fun τ w hw hwe => ?_, fun τ k => ?_⟩
  · rw [hM, hbe']
    funext j
    simp
  · obtain ⟨cc, rfl⟩ := tan_eq_cvV hxc' hw
    simp only [comb_iff hxc']
    refine eig_flat (fun a => tmap hxc (G.t.act.act a)) (χ τ) (fun a => tmap hxc' (G'.t.act.act a)) hM (b τ)
      (hbe' τ) (fun z hz => ?_) cc ((eig' τ cc).1 hwe)
    have := hb τ _ (isTan_cvV (isTan_tvec hxc z)) ((eig τ z).2 hz)
    simpa only [comb_iff hxc] using this
  · obtain ⟨u', hu1, hu2⟩ := hu τ k
    have w0 : u' ≫ t.G.hom = spMap (algebraMap T.Fr (DualNumber T.Fr)) := by
      have : Mono (spMap (algebraMap T.V T.Fr)) := by
        have : Epi (CommRingCat.ofHom (algebraMap T.V T.Fr)) :=
          IsLocalization.epi (nonZeroDivisors T.V) T.Fr
        exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)).op))
      rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc]
      erw [hu2]
      rw [Category.assoc, Over.w]
      exact dual_alg _
    have w1 : (spMap (Formalism.L2.Pj.dualMap i) ≫ u') ≫ t.G.hom =
        spMap (algebraMap T'.Fr (DualNumber T'.Fr)) ≫ spMap i := by
      rw [Category.assoc, w0, dual_alg]
    have l1 : n'.cart.1.lift _ _ w1 ≫ n'.φ = spMap (Formalism.L2.Pj.dualMap i) ≫ u' := n'.cart.1.lift_fst _ _ _
    have l2 := n'.cart.1.lift_snd _ _ w1
    refine ⟨n'.cart.1.lift _ _ w1, ?_, n.cart.1.hom_ext ?_ ?_⟩
    · rw [h1, ← Category.assoc, l1, Category.assoc, hu1]
    · change (_ ≫ m2'.φ) ≫ n.φ = (_ ≫ _) ≫ n.φ
      rw [Category.assoc, h2, ← Category.assoc, l1, Category.assoc, hu2, cvV_left, cvV_left, Category.assoc, hcomp,
        ← Category.assoc, ← Category.assoc, dual_comp, dual_comp, hψ]
    · rw [Category.assoc, m2'.cart.1.w, ← Category.assoc, l2, Category.assoc, Over.w]
      exact (dual_alg _).symm

end GlobalTheory.LamT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InvMulVecEqZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.PurePer

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem emb_smul' (τ : E →+* ℂ) (a : E) (v : Fin r → E) :
    FD.Data.emb τ (a • v) = τ a • FD.Data.emb τ v := by
  funext k
  simp [FD.Data.emb]

theorem inv_mulVec_eq_zero {p : ℕ} (hp : p ≤ r) (M : Matrix (Fin r) (Fin r) ℂ) (hM : M.det ≠ 0)
    {u : Fin r → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun a : Fin p => FD.col M (Fin.castLE hp a)))
    (k : Fin r) (hk : p ≤ (k : ℕ)) : (M⁻¹.mulVec u) k = 0 := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    have h1 : (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = (M⁻¹ * M) k (Fin.castLE hp a) := by
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, FD.col]
    have hne : k ≠ Fin.castLE hp a := by
      intro h
      have h2 := congrArg Fin.val h
      have h3 := a.isLt
      simp at h2
      omega
    show (M⁻¹.mulVec (FD.col M (Fin.castLE hp a))) k = 0
    rw [h1, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hM), Matrix.one_apply_ne hne]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add, Pi.add_apply, ha, hb, add_zero]
  | smul c a _ ha => rw [Matrix.mulVec_smul, Pi.smul_apply, ha, smul_zero]

theorem perFr_pure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.DataX E r) (La : ℝ) (x : FD.Frame X.Ψ r) (lam : Fin r → Fin r → E), x ∈ X.toData.dom → FD.LamBasis X La x lam → ∀ (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ), ((j : ℕ) < X.p0 → τ ∈ X.Ψ → perFr X.toData x (a • lam j) τ i = 0) ∧ (X.p0 ≤ (j : ℕ) → τ ∉ X.Ψ → i < X.p0 → perFr X.toData x (a • lam j) τ i = 0) := by
  intro E _ _ _ r X La x lam hx hb a j τ i
  obtain ⟨-, -, ho, -, -, -, hsp⟩ := hb
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dite_eq_left hτ]
    split_ifs with h
    · refine inv_mulVec_eq_zero X.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dite_eq_right hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin X.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE X.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨X.p0 - 1 - i, by omega⟩, rfl⟩
      rw [emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨X.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

end GlobalTheory.PurePer
end

