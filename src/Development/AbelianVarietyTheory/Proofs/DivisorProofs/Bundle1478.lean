module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqProdBlockDetPolyPowMul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenSectionsDistinctInFibres
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionsSpread

theorem sep_elem (R : Type) [CommRing R] (X : Over (Sp R)) (hX : IsSeparated X.hom)
    (K : Type) [Field K] (e : R →+* K) (x y : Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 _) (hy : y ≫ X.hom = 𝟙 _) (hne : spMap e ≫ x ≠ spMap e ≫ y) :
    ∃ r : R, e r ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), ψ r ≠ 0 →
      spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  obtain ⟨I, hI⟩ := _root_.GlobalTheory.sections_eqLocus_ideal R X hX x y hx hy
  have h1 : ¬ ∀ r ∈ I, e r = 0 := fun h => hne ((hI K e).2 h)
  push_neg at h1
  obtain ⟨r, hrI, hr⟩ := h1
  refine ⟨r, hr, fun F _ ψ hψ heq => hψ ((hI F ψ).1 heq r hrI)⟩

theorem pairs : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), IsSeparated X.hom → ∀ (K : Type) [Field K] (e : R →+* K), Function.Injective e → ∀ t : Finset (Sp R ⟶ X.left), (∀ x ∈ t, x ≫ X.hom = 𝟙 _) → (∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap e ≫ x ≠ spMap e ≫ y) → ∃ f : R, e f ≠ 0 ∧ ∀ (F : Type) [Field F] (ψ : R →+* F), IsUnit (ψ f) → ∀ x ∈ t, ∀ y ∈ t, x ≠ y → spMap ψ ≫ x ≠ spMap ψ ≫ y := by
  intro R _ X hX K _ e _ t ht hsep
  classical
  let g : (Sp R ⟶ X.left) × (Sp R ⟶ X.left) → R := fun p =>
    if h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2 then
      Classical.choose (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
    else 1
  have hg : ∀ p : (Sp R ⟶ X.left) × (Sp R ⟶ X.left), e (g p) ≠ 0 ∧
      ∀ (F : Type) [Field F] (ψ : R →+* F), ψ (g p) ≠ 0 → p.1 ∈ t → p.2 ∈ t → p.1 ≠ p.2 →
        spMap ψ ≫ p.1 ≠ spMap ψ ≫ p.2 := by
    intro p
    by_cases h : p.1 ∈ t ∧ p.2 ∈ t ∧ p.1 ≠ p.2
    · have hs := Classical.choose_spec
        (sep_elem R X hX K e p.1 p.2 (ht _ h.1) (ht _ h.2.1) (hsep _ h.1 _ h.2.1 h.2.2))
      simp only [g, dif_pos h]
      exact ⟨hs.1, fun F _ ψ hψ _ _ _ => hs.2 F ψ hψ⟩
    · simp only [g, dif_neg h]
      exact ⟨by simp, fun F _ ψ _ h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  refine ⟨∏ p ∈ t ×ˢ t, g p, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun p _ => (hg p).1
  · intro F _ ψ hu x hx y hy hxy
    have hmem : (x, y) ∈ t ×ˢ t := Finset.mem_product.2 ⟨hx, hy⟩
    have hdvd : g (x, y) ∣ ∏ p ∈ t ×ˢ t, g p := Finset.dvd_prod_of_mem g hmem
    have hu' : IsUnit (ψ (g (x, y))) := isUnit_of_dvd_unit (map_dvd ψ hdvd) hu
    exact (hg (x, y)).2 F ψ hu'.ne_zero hx hy hxy

end GlobalTheory.SectionsSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorAlongValuationPath
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem den_along_path : ∀ (k E : Type) [Field k] [Field E] [Algebra k E] (p : Place k E) (u : E) (Y : Scheme.{0}) (ζ : Sp (PowerSeries p.O) ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U) (f : Γ(Y, U)), ∃ e ψ : PowerSeries p.O, PowerSeries.constantCoeff e ≠ 0 ∧ (⊤ ≤ ζ ⁻¹ᵁ U → e = 1) ∧ sc p u e * evAt (spMap (sc p u) ≫ ζ) h f = sc p u ψ := by
  intro k E _ _ _ p u Y ζ U h f
  obtain ⟨hcomp, -, hres, hloc, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  by_cases hU : ⊤ ≤ ζ ⁻¹ᵁ U
  · refine ⟨1, evAt ζ hU f, by simp, fun _ => rfl, ?_⟩
    rw [map_one, _root_.one_mul, hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U hU h f]
  · obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hy0, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (ζ (IsLocalRing.closedPoint (PowerSeries p.O)))) isOpen_univ
    have hζ0 : ⊤ ≤ ζ ⁻¹ᵁ U₀ := (hloc _ _ _ _).2 hy0
    have hη0 : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ U₀ := fun x _ => hζ0 (Set.mem_univ ((spMap (sc p u)) x))
    have hyU := (hloc _ _ _ _).1 h
    have hyU₀ := (hloc _ _ _ _).1 hη0
    obtain ⟨t, htU, hyt⟩ := hU₀.exists_basicOpen_le (V := U) ⟨_, hyU⟩ hyU₀
    have hηt : ⊤ ≤ (spMap (sc p u) ≫ ζ) ⁻¹ᵁ Y.basicOpen t := (hloc _ _ _ _).2 hyt
    haveI := hU₀.isLocalization_basicOpen t
    obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hmk⟩ := IsLocalization.mk'_surjective (Submonoid.powers t)
      (Y.presheaf.map (homOfLE htU).op f)
    have hspec := IsLocalization.mk'_spec Γ(Y, Y.basicOpen t) a (⟨t ^ n, n, rfl⟩ : Submonoid.powers t)
    simp only at hmk
    rw [hmk] at hspec
    have hle : Y.basicOpen t ≤ U₀ := Y.basicOpen_le t
    have key : evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE htU).op f) *
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op (t ^ n)) =
        evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op a) := by
      rw [← map_mul]; exact congrArg _ hspec
    have h1 := hres _ _ _ _ _ htU h hηt f
    have h2 := hres _ _ _ _ _ hle hη0 hηt (t ^ n)
    have h3 := hres _ _ _ _ _ hle hη0 hηt a
    have hu : IsUnit (evAt (spMap (sc p u) ≫ ζ) hηt (Y.presheaf.map (homOfLE hle).op t)) :=
      (Y.toRingedSpace.isUnit_res_basicOpen t).map _
    refine ⟨evAt ζ hζ0 (t ^ n), evAt ζ hζ0 a, ?_, fun h' => absurd h' hU, ?_⟩
    · intro h0
      have hu' : IsUnit (sc p u (evAt ζ hζ0 (t ^ n))) := by
        rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h2, map_pow, map_pow]
        exact hu.pow n
      rw [PowerSeries.isUnit_iff_constantCoeff] at hu'
      apply hu'.ne_zero
      rw [sc, RingHom.comp_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale,
        PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
      simp
    · rw [← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← hcomp (PowerSeries p.O) (PowerSeries E) Y (sc p u) ζ U₀ hζ0 hη0, ← h1, ← h2, ← h3, ← key]
      exact mul_comm _ _

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetNeZeroEvalFrNeZero
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj GlobalTheory.LamT

namespace GlobalTheory.LatFull.CMInt

theorem exists_denom {K : Type} [Field K] [NumberField K] (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (c : K) :
    ∃ N : 𝓞 K, N ≠ 0 ∧ ∀ x ∈ J, IsIntegral ℤ ((N : K) * (x * c)) := by
  obtain ⟨a, ha, h⟩ := (J * FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun x hx => ?_⟩
  obtain ⟨w, hw⟩ := h (x * c) (FractionalIdeal.mul_mem_mul hx (FractionalIdeal.mem_spanSingleton_self _ _))
  rw [Algebra.smul_def] at hw
  have : (a : K) * (x * c) = (w : K) := hw.symm
  rw [this]
  exact w.isIntegral_coe

theorem exists_denom_eval {K σ : Type} [Field K] [NumberField K] [Finite σ]
    (J : (σ →₀ ℕ) → FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (x : σ → K) (d : ℕ) :
    ∃ N : K, N ≠ 0 ∧ ∀ G : MvPolynomial σ K, G.IsHomogeneous d → (∀ μ, AddMonoidAlgebra.coeff G μ ∈ J μ) →
      IsIntegral ℤ (N * MvPolynomial.eval x G) := by
  classical
  choose M hM0 hM using fun μ : σ →₀ ℕ => exists_denom (J μ) (∏ i ∈ μ.support, x i ^ μ i)
  let S := (Finsupp.finite_of_degree_le (σ := σ) d).toFinset
  refine ⟨((∏ μ ∈ S, M μ : 𝓞 K) : K), ?_, fun G hG hJ => ?_⟩
  · have : (∏ μ ∈ S, M μ : 𝓞 K) ≠ 0 := Finset.prod_ne_zero_iff.2 fun μ _ => hM0 μ
    exact fun h => this (RingOfIntegers.coe_eq_zero_iff.1 h)
  · rw [MvPolynomial.eval_eq, Finset.mul_sum]
    refine IsIntegral.sum _ fun μ hμ => ?_
    have hS : μ ∈ S := by
      simp only [S, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      have := hG (MvPolynomial.mem_support_iff.1 hμ)
      rw [Finsupp.degree_eq_weight_one]
      exact this.le
    rw [← Finset.prod_erase_mul _ _ hS]
    have e : (((∏ ν ∈ S.erase μ, M ν) * M μ : 𝓞 K) : K) = ((∏ ν ∈ S.erase μ, M ν : 𝓞 K) : K) * (M μ : K) :=
      map_mul (algebraMap (𝓞 K) K) _ _
    rw [e, mul_assoc]
    exact (RingOfIntegers.isIntegral_coe _).mul (hM μ _ (hJ μ))

theorem coeff_mem_of_loc {K : Type} [Field K] [NumberField K] {g : ℕ} {B : Type} [Fintype B] {m : B → ℕ}
    (e : (Σ b, Fin (m b)) ≃ Fin g) (T abelian₂ : MLine K) (ℓ : Fin g → MLine K) (U : Matrix (Fin g) (Fin g) K)
    (G : MvPolynomial (FrVar m) K) (n : ℕ) (hT : T.Good) (hℓ : ∀ j, (ℓ j).Good)
    (hloc : ∀ p, Step5Loc e T abelian₂ ℓ U G n p) (μ : FrVar m →₀ ℕ) :
    AddMonoidAlgebra.coeff G μ ∈ (lineNN T ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
  classical
  refine coeff_mem_of_local K g ℓ T (FrVar m) _ μ n _ hT hℓ fun p => ?_
  obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hloc p
  refine ⟨t, cl, ht, hcl, ?_⟩
  have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
  have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
  obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
    (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
  have hrange : f (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
      Set.range (algebraMap V K') := by
    refine ⟨w, ?_⟩
    rw [map_div₀, map_mul, map_prod]
    simp only [map_pow]
    rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
  have h1 := (hind _).mp hrange
  calc p.valuation K (AddMonoidAlgebra.coeff G μ * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
      = p.valuation K (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
          p.valuation K (t ^ n) := by
        rw [← map_mul, div_mul_cancel₀ _ htn]
    _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

theorem exists_det_ne_zero_evalFr_ne_zero {K : Type} [Field K] [Infinite K] {B : Type} [Fintype B] {m : B → ℕ}
    (G : MvPolynomial (FrVar m) K) (hG : G ≠ 0) :
    ∃ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K, (∀ b, (Y b).det ≠ 0) ∧ evalFr G Y ≠ 0 := by
  classical
  have hev : ∀ Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K,
      evalFr (∏ b, FieldPoly.blockDetPoly K m b) Y = ∏ b, (Y b).det := fun Y => by
    simp only [← FieldPoly.evalFr_blockDetPoly m _ Y]
    simp only [evalFr, map_prod]
  have hD : (∏ b, FieldPoly.blockDetPoly K m b) ≠ 0 := fun h0 => by
    have h1 := hev fun _ => 1
    rw [h0] at h1
    simp [evalFr] at h1
  have hP := mul_ne_zero hD hG
  obtain ⟨x, hx⟩ : ∃ x : FrVar m → K, MvPolynomial.eval x ((∏ b, FieldPoly.blockDetPoly K m b) * G) ≠ 0 := by
    by_contra h
    push Not at h
    exact hP (MvPolynomial.funext fun x => by rw [h x, map_zero])
  rw [map_mul] at hx
  let X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K := fun b => Matrix.of fun i j => x ⟨b, (j, i)⟩
  refine ⟨X, fun b => ?_, right_ne_zero_of_mul hx⟩
  have h1 : (∏ b, (X b).det) ≠ 0 := by rw [← hev X]; exact left_ne_zero_of_mul hx
  exact (Finset.prod_ne_zero_iff.1 h1) b (Finset.mem_univ b)

theorem exists_frame_bounded_denom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (z : CMPt Xo c) (f : ℕ) (La : ℝ), z.Good f La → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F₀ ∈ sec Xo c a n, (∀ G, IsFrPoly F₀ z.y G → G ≠ 0) → ∃ (y : FrPt Xo c z.K) (N : z.K), N * evR Xo c F₀ y ≠ 0 ∧ ∀ F ∈ sec Xo c a n, (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → IsIntegral ℤ (N * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c _ z f La hz a n F₀ hF₀ hne
  classical
  obtain ⟨G₀, hG₀, -⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F₀ hF₀
  obtain ⟨Y, hY, hY0⟩ := exists_det_ne_zero_evalFr_ne_zero G₀ (hne G₀ hG₀)
  obtain ⟨y, hy, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c z.K z.y (fun b => (Y b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact (hY b).isUnit)
  rw [Units.val_one] at hy
  have hval : ∀ (F : Rul Xo c) (G : MvPolynomial (FrVar Dw.mult) z.K), IsFrPoly F z.y G →
      evR Xo c F y = evalFr G Y := fun F G hG => by
    have h1 := hG z.K (AlgHom.id c.F z.K) z.y y Y (fun b => (hY b).isUnit) (GlobalTheory.Frames.frMapUniq_refl z.y) hy
    have h2 : MvPolynomial.map (AlgHom.id c.F z.K).toRingHom G = G := MvPolynomial.map_id G
    rwa [h2] at h1
  have hgood : z.Tl.dual.Good ∧ ∀ k, (z.ℓ k).Good := by
    obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvΨ, hv', hT, -⟩, ⟨-, -, -, hℓ⟩, -⟩ := hz
    refine ⟨(degree_algebraic z.K z.Tl z.Tl hT hT).2.2.1, fun k => ?_⟩
    have h := hℓ k
    change (z.letters.ℓ k).Good
    generalize z.letters = L at h
    revert h
    cases L.src k with
    | inl q => intro h1; rw [h1]; exact (hvΨ q.2).1
    | inr q => intro h1; rw [h1]; exact (hv' q.2).1
  obtain ⟨N, hN, hint⟩ := exists_denom_eval
    (fun μ : FrVar Dw.mult →₀ ℕ => (lineNN z.Tl.dual z.ℓ (fun v : FrVar Dw.mult => z.e ⟨v.1, v.2.2⟩) μ n).I)
    (fun v : FrVar Dw.mult => Y v.1 v.2.2 v.2.1) (∑ τ, ∑ i : Fin (Dw.mult τ), a (τ, (i : ℕ)))
  refine ⟨y, N, by rw [hval F₀ G₀ hG₀]; exact mul_ne_zero hN hY0, fun F hF hv => ?_⟩
  obtain ⟨G, hG, hh⟩ := FieldPoly.exists_isFrPoly_isHomogeneous E H Dw l Xo c z.K z.y a n F hF
  rw [hval F G hG]
  exact hint G hh (coeff_mem_of_loc z.e z.Tl.dual z.LamL z.ℓ z.U G n hgood.1 hgood.2
    (LocClause.step5Loc_cmPt E H Dw l Xo c z f La hz a n F hF hv G hG))

end GlobalTheory.LatFull.CMInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFgSubringDescentGroupSectionsCurve
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadCurve

open Polynomial

theorem group_sections_curve_descend : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  intro k _ G _ hG g hg m hm hmk s hs P hP u a b hu hab
  classical
  obtain ⟨hc, h1, h2, h3, h5⟩ := hG
  obtain ⟨R₀, G₀, i₀, ic₀, φ, -, hR₀, s₁, s₂, s₃, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring k G ∅ h1 h2 h3

  haveI := s₁; haveI := s₂; haveI := s₃
  set L := Localization.Away P with hL

  have hu₀ : (u ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ L) := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hu]
    exact ModelDescent.spMap_comp_eq (RingHom.ext fun r => (IsScalarTower.algebraMap_apply R₀ k L r).symm)
  obtain ⟨S, yS, hSfg, -, hyS⟩ := Spread.exists_fg_points G₀.hom (fun _ : Unit => u ≫ φ) (fun _ => hu₀) ⊥
    Subalgebra.fg_bot
  obtain ⟨T, hT⟩ := hSfg
  obtain ⟨Fc, hFc⟩ := GlobalTheory.T.exists_finset_away_lift_descent k P T

  set X' : L := algebraMap (Polynomial k) L X with hX'
  have haev : ∀ (c : L →ₐ[k] k) (q : Polynomial k), c (algebraMap (Polynomial k) L q) = q.eval (c X') := by
    intro c q
    have : (c : L →+* k).comp (algebraMap (Polynomial k) L) = Polynomial.evalRingHom (c X') := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
        have e : algebraMap (Polynomial k) L (C r) = algebraMap k L r := by
          rw [IsScalarTower.algebraMap_apply k (Polynomial k) L, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [e]
        exact c.commutes r
      · simp [hX']
    exact congrArg (fun f : Polynomial k →+* k => f q) this
  have hne : ∀ c : L →ₐ[k] k, P.eval (c X') ≠ 0 := by
    intro c
    rw [← haev]
    exact ((IsLocalization.Away.algebraMap_isUnit P).map c).ne_zero

  let F : Finset k := Fc ∪ P.coeffs ∪ {(m : k)⁻¹, a X', b X', (P.eval (a X'))⁻¹, (P.eval (b X'))⁻¹}

  have hx₀ : ∀ i : s, (i.1.left ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ k) := by
    intro i
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w i.1]
    exact Category.id_comp _
  obtain ⟨R, y, hRfg, hR₁R, hy⟩ := Spread.exists_fg_points G₀.hom (fun i : s => i.1.left ≫ φ) hx₀
    (Algebra.adjoin R₀ (F : Set k)) (Subalgebra.fg_adjoin_finset F)
  let R' : Subring k := R.toSubring
  have hFR : (F : Set k) ⊆ R' := fun x hx => hR₁R (Algebra.subset_adjoin hx)
  have hR₀R : R₀ ≤ R' := fun r hr => R.algebraMap_mem ⟨r, hr⟩
  let jn : R₀ →+* R' := Subring.inclusion hR₀R
  have hjn : R'.subtype.comp jn = R₀.subtype := rfl
  have hjnsp : spMap R'.subtype ≫ spMap jn = spMap R₀.subtype := ModelDescent.spMap_comp_eq hjn
  let G₁ : Over (Sp R') := (Over.pullback (spMap jn)).obj G₀
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁c : IsCommMonObj G₁ := Functor.isCommMonObj_obj
  have hψ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (spMap jn) (spMap R'.subtype)
    (hφ.congr hjnsp.symm rfl)
  set ψ := pullback.lift φ (G.hom ≫ spMap R'.subtype) (by rw [hφ.1.w, Category.assoc, hjnsp]) with hψdef
  have hψ₁ : ψ ≫ pullback.fst G₀.hom (spMap jn) = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G₀.hom (spMap jn) = G.hom ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hyR : ∀ i : s, (y i : Sp R' ⟶ G₀.left) ≫ G₀.hom = spMap jn := fun i => (hy i).1
  have hyk : ∀ i : s, spMap R'.subtype ≫ (y i : Sp R' ⟶ G₀.left) = i.1.left ≫ φ := fun i => (hy i).2

  have hsq : IsPullback hψ.1.isoPullback.inv (pullback.snd G₁.hom (spMap R'.subtype)) G.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hgc : GeometricallyConnected (pullback.snd G₁.hom (spMap R'.subtype)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h5
  have hgd : SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R'.subtype)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hsq hg
  have hunit : IsUnit (m : R') := by
    refine IsUnit.of_mul_eq_one (a := (m : R')) ⟨(m : k)⁻¹, hFR (by simp [F])⟩ (Subtype.ext ?_)
    simp [mul_inv_cancel₀ hmk]

  let sec : s → (𝟙_ (Over (Sp R')) ⟶ G₁) := fun i =>
    Over.homMk (pullback.lift (y i : Sp R' ⟶ G₀.left) (𝟙 _) (by rw [hyR i, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  have hsec₁ : ∀ i : s, (sec i).left ≫ pullback.fst G₀.hom (spMap jn) = y i := fun i => pullback.lift_fst _ _ _
  have hkey : ∀ i : s, i.1.left ≫ ψ = spMap R'.subtype ≫ (sec i).left := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hsec₁, hyk]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w i.1, Category.assoc]
      erw [pullback.lift_snd]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hdist : ∀ i j : s, spMap R'.subtype ≫ (sec i).left = spMap R'.subtype ≫ (sec j).left → i = j := by
    intro i j e
    have e' : i.1.left ≫ φ = j.1.left ≫ φ := by
      rw [← hψ₁, ← Category.assoc, ← Category.assoc, hkey, hkey, e]
    refine Subtype.ext (Over.OverMorphism.ext (hφ.1.hom_ext e' ?_))
    rw [Over.w i.1, Over.w j.1]
  have hsec_inj : Function.Injective sec := fun i j e => hdist i j (by rw [e])
  haveI hsep₁ : IsSeparated G₁.hom := show IsSeparated (pullback.snd _ _) from inferInstance
  have hpow : ∀ i : s, sec i ^ m = 1 := by
    intro i
    have A := GlobalTheory.FrameMove.pow_comm hψ (hkey i) m
    have B := GlobalTheory.FrameMove.pow_comm hψ (hkey i) 0
    rw [hs i.1 i.2] at A
    rw [pow_zero, pow_zero] at B
    refine Over.OverMorphism.ext (Spread.point_ext R'.subtype Subtype.val_injective G₁.hom ?_ (A.symm.trans B))
    rw [Over.w, Over.w]

  have hPl : P ∈ Polynomial.lifts R'.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts P).2 fun n => ?_
    by_cases hn : P.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨P.coeff n, hFR (by simp [F, Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨P₁, hP₁⟩ := Polynomial.mem_lifts P |>.1 hPl
  have hP₁0 : P₁ ≠ 0 := by
    rintro rfl
    exact hP (by rw [← hP₁, Polynomial.map_zero])
  have hPu : IsUnit (((algebraMap (Polynomial k) L).comp (Polynomial.mapRingHom R'.subtype)) P₁) := by
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, hP₁]
    exact IsLocalization.Away.algebraMap_isUnit P
  set Lm := IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hPu with hLm
  have hinj : Function.Injective Lm := GlobalTheory.T.localizationAway_polynomial_subring_lift_injective k P hP R' P₁ hPu hP₁
  have hrange : ∀ t ∈ T, t ∈ Lm.range := hFc R' (fun x hx => hFR (by simp [F, hx])) P₁ hPu hP₁
  have hLmC : ∀ r : R', Lm (algebraMap R' (Localization.Away P₁) r) = algebraMap k L r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R' (Polynomial R') (Localization.Away P₁), hLm,
      IsLocalization.Away.lift_eq]
    simp [Polynomial.algebraMap_apply, IsScalarTower.algebraMap_apply k (Polynomial k) L]

  have hcl : Subring.closure (Set.range (algebraMap R₀ L) ∪ (T : Set L)) ≤ Lm.range := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · refine ⟨algebraMap R' (Localization.Away P₁) (jn r), ?_⟩
      rw [hLmC]
      exact (IsScalarTower.algebraMap_apply R₀ k L r).symm
    · exact hrange z hz
  have hSr : ∀ z : S, S.val.toRingHom z ∈ Lm.range := by
    intro z
    apply hcl
    rw [← Algebra.adjoin_eq_ring_closure, hT]
    exact z.2
  obtain ⟨gS, hgS⟩ := ModelDescent.exists_factor S.val.toRingHom Lm hinj hSr
  have hcomp : gS.comp (algebraMap R₀ S) = (algebraMap R' (Localization.Away P₁)).comp jn := by
    refine RingHom.ext fun r => hinj ?_
    change Lm (gS (algebraMap R₀ S r)) = Lm (algebraMap R' _ (jn r))
    rw [← RingHom.comp_apply Lm gS, hgS, hLmC]
    change (algebraMap R₀ L r) = _
    exact IsScalarTower.algebraMap_apply R₀ k L r
  let u₁' : Sp (Localization.Away P₁) ⟶ G₀.left := spMap gS ≫ yS ()
  have hu₁' : u₁' ≫ G₀.hom = spMap (algebraMap R' (Localization.Away P₁)) ≫ spMap jn := by
    rw [Category.assoc, (hyS ()).1, ModelDescent.spMap_comp_eq hcomp]
    exact (ModelDescent.spMap_comp_eq rfl).symm
  let u₁ : Sp (Localization.Away P₁) ⟶ G₁.left :=
    pullback.lift u₁' (spMap (algebraMap R' (Localization.Away P₁))) hu₁'
  have hu₁f : u₁ ≫ pullback.fst G₀.hom (spMap jn) = u₁' := pullback.lift_fst _ _ _
  have hu₁s : u₁ ≫ G₁.hom = spMap (algebraMap R' (Localization.Away P₁)) := pullback.lift_snd _ _ _

  have hpt : ∀ c : L →ₐ[k] k, c X' ∈ R' → (P.eval (c X'))⁻¹ ∈ R' → ∃ (w0 : R')
      (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm := by
    intro c hc hci
    have hev : ((Polynomial.eval (⟨c X', hc⟩ : R') P₁ : R') : k) = P.eval (c X') := by
      refine Eq.trans ?_ (congrArg (Polynomial.eval (c X')) hP₁)
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply R'.subtype _).symm
    have hw0 : IsUnit (Polynomial.evalRingHom (⟨c X', hc⟩ : R') P₁) := by
      refine IsUnit.of_mul_eq_one (b := ⟨(P.eval (c X'))⁻¹, hci⟩) (Subtype.ext ?_)
      rw [Subring.coe_mul, Polynomial.coe_evalRingHom, hev]
      exact mul_inv_cancel₀ (hne c)
    refine ⟨⟨c X', hc⟩, hw0, IsLocalization.ringHom_ext (Submonoid.powers P₁) ?_⟩
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        haev]
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rfl

  obtain ⟨α, hα, hαe⟩ := hpt a (hFR (by simp [F])) (hFR (by simp [F]))
  obtain ⟨β, hβ, hβe⟩ := hpt b (hFR (by simp [F])) (hFR (by simp [F]))
  have key : ∀ (c : L →ₐ[k] k) (w0 : R') (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm →
      (spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) ≫ u₁) ≫
        pullback.fst G₀.hom (spMap jn) = spMap c.toRingHom ≫ u ≫ φ := by
    intro c w0 hw0 hce
    rw [Category.assoc, Category.assoc, hu₁f, ← Category.assoc, ModelDescent.spMap_comp_eq hce,
      ← ModelDescent.spMap_comp_eq (f := Lm) (g := c.toRingHom) rfl, Category.assoc, ← Category.assoc (spMap Lm),
      ModelDescent.spMap_comp_eq hgS, (hyS ()).2]
  have hcG : ∀ c : L →ₐ[k] k, spMap c.toRingHom ≫ u ≫ G.hom = 𝟙 _ := by
    intro c
    rw [hu, ModelDescent.spMap_comp_eq (h := RingHom.id k) (RingHom.ext c.commutes)]
    simp [spMap]
  have hdistc : spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠
      spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
    intro e
    apply hab
    have ea := key a α hα hαe
    have eb := key b β hβ hβe
    rw [e] at ea
    have e2 : spMap a.toRingHom ≫ u ≫ φ = spMap b.toRingHom ≫ u ≫ φ := ea.symm.trans eb
    refine hφ.1.hom_ext (by simpa only [Category.assoc] using e2) ?_
    rw [Category.assoc, hcG, Category.assoc, hcG]
  refine ⟨R', G₁, inferInstance, SpreadGroup.finiteType_of_fg hR₀ hRfg, hunit, hG₁c,
    show Smooth (pullback.snd _ _) from inferInstance, hsep₁, show QuasiCompact (pullback.snd _ _) from inferInstance,
    hgc, hgd, ⟨s.attach.image sec, ?_, ?_, ?_⟩, P₁, hP₁0, u₁, α, β, hα, hβ, hu₁s, hdistc⟩
  · rw [Finset.card_image_of_injective _ hsec_inj, Finset.card_attach]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hpow i
  · intro x hx z hz hxz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
    exact fun e => hxz (by rw [hdist i j e])

end GlobalTheory.SpreadCurve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatTorsionSubgroup
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_flat_torsion_subgroup : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  first | (exact @GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (exact GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (intros; apply GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow  <;> assumption)
end

