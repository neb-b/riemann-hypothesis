module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0072
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.WeilBound.CoreStatements.SesquilinearFractions.DTransUnit
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0214
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0228
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPeriodProduct
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0222
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0224

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmHeight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem flatGen_finNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (ℓ : Nat.Primes), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → ∃ t : E, (∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ + Real.log ‖j (IsCMField.complexConj E t)‖ + Real.log ‖j (gramE (FU.Di i) e).det‖ = -((D.p : ℝ) + D.q) * logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E))) ∧ (IsLocBasis (𝓞 E) ℓ e → ∀ j : E →+* ℂ_[ℓ], Real.log ‖j t‖ = 0) ∧ ∀ (j : k →+* ℂ_[ℓ]) (t₀ : ℝ), HasFinNorm U τ φ ℓ (j.comp (IntermediateField.inclusion hc).toRingHom) t₀ → t₀ = Real.log ‖j r‖ - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) t)‖ - D.q * logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) + ((D.q : ℝ) - D.p) * (logIdeal ((j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ))).comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (H.rt : E))‖) := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r ℓ hty hrt hmem hline he hconst hr hz
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hxl, hfr⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fl.exists_cmPoint_locBasis_frames E H D l Xo c g ty FU i Z τ ℓ k inferInstance hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hdet, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
  have hT0 : T.det ≠ 0 := hdet hxl.1
  have hge : (gramE (FU.Di i) e).det ≠ 0 := (_root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  have hconj : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
    (AlgEquiv.map_det (IsCMField.complexConj E) T).symm
  have hgdet : (gramE (FU.Di i) x).det
      = T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hconj]
  refine ⟨T.det, ?_, ?_, ?_⟩
  · intro j
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Fl.GramDet.log_norm_det_gramE E H (FU.Di i) _ x ℓ hxl j
    have n1 : ‖j T.det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hT0)
    have n2 : ‖j (gramE (FU.Di i) e).det‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 hge)
    have n3 : ‖j (IsCMField.complexConj E T.det)‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hT0))
    rw [hgdet, map_mul, map_mul, norm_mul, norm_mul, Real.log_mul (mul_ne_zero n1 n2) n3,
      Real.log_mul n1 n2] at h1
    have hc2 : ((Fintype.card (Fin D.p ⊕ Fin D.q) : ℕ) : ℝ) = (D.p : ℝ) + D.q := by simp
    rw [hc2] at h1
    linarith
  · intro hel j
    rw [_root_.PositivityTheory.Xgf.padic_norm_transition_det_one E H (FU.Di i) _ x e T ℓ hxl hel hT j, Real.log_one]
  · intro j t₀ hN
    obtain ⟨j', hj'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField k X.K ℂ_[ℓ] (IntermediateField.inclusion hkK).toRingHom j
    obtain ⟨V, hV, hVf, Tm, m'', δ, δ', v', w', hval, hδ, hδ', hlogδ, hlogδ', hA, hB, hfr', hiv, hiw⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.Fl.GFin.intFrames_fin E H D l Xo c g ty FU i Z P hP X x hx τ ℓ j' v w hty hrt hxl hfr
    obtain ⟨hF, hφ⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt
      hmem hline he hconst hxl.1 hT hfr
    have hF' : IsFramed U τ X.β X.y v' w' := ⟨hfr'.1, hF.2.1, hfr'.2.2⟩
    have hβ : j'.comp X.β = j.comp (IntermediateField.inclusion hc).toRingHom := by
      rw [← hj']; ext a; rfl
    haveI := hV
    haveI := hVf
    have hfin := hN V X.K j' X.β X.y v' w' Tm X.t X.m m'' hval hβ hF' hiv hiw
    have hchg := hline.chg X.K X.β X.y v w v' w' (δ • (1 : Matrix (Fin D.p) (Fin D.p) X.K))
      (δ' • (1 : Matrix (Fin D.q) (Fin D.q) X.K)) hF hF' hA hB
    simp only [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hchg
    have hφ0 := hline.ne X.K X.β X.y v w hF
    have hφ'0 := hline.ne X.K X.β X.y v' w' hF'
    have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
      (_root_.GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    obtain ⟨hG0, hGlog⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.orthogonalBlock_gram_det_log_norm E H (FU.Di i) D.p D.q x ℓ hxl horth
    have hzt : (Z true).z ^ D.p ≠ 0 := pow_ne_zero _ (_root_.GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H _ (Z true))
    have hC : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
      apply mul_right_cancel₀ hzt
      rw [hφ, ← hz]
      ring
    have hK : φ X.K X.y v w * X.β (tauE c τ T.det)
        = (IntermediateField.inclusion hkK).toRingHom r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
      Subtype.ext hC
    have hjE : j'.comp (X.β.comp (tauE c τ))
        = j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) := by
      rw [← RingHom.comp_assoc, hβ, RingHom.comp_assoc]
    have happ : ∀ a : E, j' (X.β (tauE c τ a))
        = j ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) a) := fun a =>
      congrArg (fun f : E →+* ℂ_[ℓ] => f a) hjE
    have hjr : j' ((IntermediateField.inclusion hkK).toRingHom r) = j r := by
      rw [← hj']; rfl
    have nφ : ‖j' (φ X.K X.y v w)‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ0)
    have nφ' : ‖j' (φ X.K X.y v' w')‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hφ'0)
    have nδ : ‖j' δ‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ)
    have nδ' : ‖j' δ'‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j').2 hδ')
    have nr : ‖j r‖ ≠ 0 := norm_ne_zero_iff.2 ((map_ne_zero j).2 (by simpa using hr))
    have nt : ‖j' (X.β (tauE c τ T.det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hT0)))
    have nG : ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ ≠ 0 :=
      norm_ne_zero_iff.2 ((map_ne_zero j').2 ((map_ne_zero _).2 ((map_ne_zero _).2 hG0)))
    have hn : ‖j' (φ X.K X.y v w)‖ * ‖j' (X.β (tauE c τ T.det))‖
        = ‖j r‖ * ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      have h := congrArg (fun a => ‖j' a‖) hK
      simpa only [map_mul, norm_mul, hjr] using h
    have hl : Real.log ‖j' (φ X.K X.y v w)‖ + Real.log ‖j' (X.β (tauE c τ T.det))‖
        = Real.log ‖j r‖ + Real.log ‖j' (X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det))‖ := by
      rw [← Real.log_mul nφ nt, ← Real.log_mul nr nG, hn]
    have hm : ‖j' (φ X.K X.y v' w')‖ * ‖j' δ‖ ^ D.p = ‖j' (φ X.K X.y v w)‖ * ‖j' δ'‖ ^ D.q := by
      have h := congrArg (fun a => ‖j' a‖) hchg
      simp only [map_mul, map_pow, map_one, norm_mul, norm_pow, norm_one] at h
      linear_combination h
    have hlog : Real.log ‖j' (φ X.K X.y v' w')‖ + D.p * Real.log ‖j' δ‖
        = Real.log ‖j' (φ X.K X.y v w)‖ + D.q * Real.log ‖j' δ'‖ := by
      rw [← Real.log_pow, ← Real.log_pow, ← Real.log_mul nφ' (pow_ne_zero _ nδ),
        ← Real.log_mul nφ (pow_ne_zero _ nδ'), hm]
    have hGl := hGlog (j.comp (((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)))
    rw [RingHom.comp_apply, ← happ] at hGl
    rw [hjE, happ] at hlogδ
    rw [← happ]
    linear_combination -hfin + hlog + hl + hGl + (D.q : ℝ) * hlogδ' + ((D.q : ℝ) - D.p) * hlogδ

end GlobalTheory.CompanionTheory.Ar.Fl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmNumberField
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.InfPlace

theorem log_norm_det_scaled {E : Type} [Field E] (σ : E →+* ℂ) (rt : E) (d : ℕ) (hd : 0 < d)
    (hrt : rt ^ 2 = -(d : E)) (r : ℝ) (hr : 0 < r) (ε : ℤˣ) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) E) (hM : M.det ≠ 0) (Γ : Matrix (Fin n) (Fin n) ℂ)
    (hΓ : ∀ k k', Γ k k' = (r : ℂ) * ((ε : ℤ) : ℂ) * σ (rt * M k k')) :
    Real.log ‖Γ.det‖ = (n : ℝ) * (Real.log r + Real.log d / 2) + Real.log ‖σ M.det‖ := by
  have hΓ' : Γ = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) • (σ.mapMatrix M) := by
    ext k k'
    simp only [hΓ, Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, map_mul]
    ring
  have hdet : Γ.det = ((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n * σ M.det := by
    rw [hΓ', Matrix.det_smul, Fintype.card_fin, RingHom.map_det]
  have hε : ‖((ε : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hs : ‖σ rt‖ ^ 2 = d := by
    have h1 : σ rt ^ 2 = -(d : ℂ) := by
      rw [← map_pow, hrt]
      simp
    have h2 := congrArg norm h1
    simpa [norm_pow] using h2
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hs0 : ‖σ rt‖ ≠ 0 := by
    intro h
    rw [h] at hs
    have h0 : (d : ℝ) = 0 := by simpa using hs.symm
    linarith
  have hlog : Real.log ‖σ rt‖ = Real.log d / 2 := by
    have h3 := congrArg Real.log hs
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith
  have hσM : σ M.det ≠ 0 := (map_ne_zero σ).2 hM
  have hpos : ‖((r : ℂ) * ((ε : ℤ) : ℂ) * σ rt) ^ n‖ ≠ 0 := by
    rw [norm_pow, norm_mul, norm_mul, hε, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one]
    exact pow_ne_zero _ (mul_ne_zero hr.ne' hs0)
  rw [hdet, norm_mul, Real.log_mul hpos (norm_ne_zero_iff.2 hσM), norm_pow, norm_mul, norm_mul, hε,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, _root_.mul_one, Real.log_pow,
    Real.log_mul hr.ne' hs0, hlog]

theorem conj_eq_neg_of_sq {d : ℕ} (hd : 0 < d) {z : ℂ} (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z :=
  _root_.UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main hd hz

theorem hasInfNorm_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (k : IntermediateField ℚ ℂ) [NumberField k] (hc : c.F ≤ k) (hM : ∀ b, (Z b).M ≤ k) (r : k) (s : k →+* ℂ) (n n' t : ℝ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → r ≠ 0 → (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q → 0 < n → 0 < n' → IsLieNormSq (Z true).C.P (Z true).C.v ((s.comp (IntermediateField.inclusion (hM true)).toRingHom).comp (algebraMap (𝓞 (Z true).M) (Z true).M)) n → IsLieNormSq (Z false).C.P (Z false).C.v ((s.comp (IntermediateField.inclusion (hM false)).toRingHom).comp (algebraMap (𝓞 (Z false).M) (Z false).M)) n' → HasInfNorm U τ φ (s.comp (IntermediateField.inclusion hc).toRingHom) t → t = Real.log ‖s r‖ + ((D.p : ℝ) / 2 * (Real.log n + Real.log H.d / 2) - (D.q : ℝ) / 2 * (Real.log n' + Real.log H.d / 2)) + Real.log ‖s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det)‖ / 2 := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ k _ hc hM r s n n' t hty hτ hU hline he hconst hr hrz hn hn' hLt hLf hinf
  classical
  obtain ⟨P, hP, x, hx, X, v, w, hkK, hloc, hfr⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fl.exists_cmPoint_locBasis_frames E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ k inferInstance hty hτ
  have hxli : LinearIndependent (𝓞 E) x := hloc.1
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, hgram, hTdet, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists E H (FU.Di i) _ x e hcard he
  have hTne := hTdet hxli
  have hGe := (_root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) _ e hcard he).1
  obtain ⟨hfram, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hU hline he
    hconst hxli hT hfr
  obtain ⟨s', hs'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.exists_comp_eq_of_numberField k X.K ℂ (IntermediateField.inclusion hkK).toRingHom s
  have hs'a : ∀ a : k, s' (IntermediateField.inclusion hkK a) = s a := fun a => DFunLike.congr_fun hs' a
  have hβ : s'.comp X.β = s.comp (IntermediateField.inclusion hc).toRingHom := by
    ext a
    exact hs'a (IntermediateField.inclusion hc a)
  have hMs : ∀ b, s'.comp (IntermediateField.inclusion (X.hM b)).toRingHom =
      s.comp (IntermediateField.inclusion (hM b)).toRingHom := by
    intro b
    ext a
    exact hs'a (IntermediateField.inclusion (hM b) a)

  let y' : Sp ℂ ⟶ Xo.XF c := spMap s' ≫ X.y
  have hy' : under y' = spMap s' ≫ under X.y := Category.assoc _ _ _
  obtain ⟨⟨v', hv'⟩, hvI⟩ := _root_.PositivityTheory.Xgf.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hy'
  obtain ⟨⟨w', hw'⟩, hwI⟩ := _root_.PositivityTheory.Xgf.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ s' (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hy'
  have hfram' : IsFramed U τ (s.comp (IntermediateField.inclusion hc).toRingHom) y' v' w' := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hβ]
      simp only [y', Category.assoc, hfram.1]
      simp [spMap, ← Spec.map_comp, CommRingCat.ofHom_comp]
    · rintro _ ⟨u, rfl⟩
      apply hfram.2.1
      exact ⟨(spMap s') u, by simp [y']⟩
    · rw [← hβ, RingHom.comp_assoc]
      exact (hvI v' hv').1 hfram.2.2.1
    · rw [← hβ, RingHom.comp_assoc]
      exact (hwI w' hw').1 hfram.2.2.2
  have hconjτ : ComplexEmbedding.conjugate τ (H.rt : E) = sgnRt H false := by
    simp only [sgnRt, ComplexEmbedding.conjugate_coe_eq, hτ]
    exact conj_eq_neg_of_sq H.d_prime.pos H.sqrt_neg_disc_sq
  have hΓ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec E H D l Xo c g ty FU i Z P hP X true τ D.p (fun a => ⟨x (.inl a), hx.1 a⟩) v s' y' v' n
    (by simpa [sgnRt] using hτ) hfr.1 rfl hv' (by rw [hMs]; exact hLt)
  have hΔ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.GInf.hodgeGram_cmVec E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ) D.q
    (fun a => ⟨x (.inr a), hx.2 a⟩) w s' y' w' n' hconjτ hfr.2 rfl hw' (by rw [hMs]; exact hLf)
  have hmain := hinf y' v' w' _ _ hfram' hΓ hΔ
  rw [hline.nat X.K ℂ s' X.β X.y v w y' v' w' hfram rfl hv' hw'] at hmain

  have hblock : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · rfl
    · exact (_root_.GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
    · exact (_root_.GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure E H (FU.Di i) g ty P hP _ _ (hx.1 b) (hx.2 a)).2
    · rfl
  have hdet1 : (gramE (FU.Di i) x).det =
      (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₁₂]
  have hdet2 : (gramE (FU.Di i) x).det =
      T.det * (gramE (FU.Di i) e).det * IsCMField.complexConj E T.det := by
    have hc' : (T.map (IsCMField.complexConj E)).det = IsCMField.complexConj E T.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) T).symm
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hc']
  have hconjne : IsCMField.complexConj E T.det ≠ 0 := by
    simpa using hTne
  have hG : (gramE (FU.Di i) (x ∘ Sum.inl)).det * (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    rw [← hdet1, hdet2]
    exact mul_ne_zero (mul_ne_zero hTne hGe) hconjne
  have hG1 := left_ne_zero_of_mul hG
  have hG2 := right_ne_zero_of_mul hG

  let σ : E →+* ℂ := s'.comp (X.β.comp (tauE c τ))
  let σ' : E →+* ℂ := s'.comp (X.β.comp (tauE c (ComplexEmbedding.conjugate τ)))
  have hσ' : ∀ a, ‖σ' a‖ = ‖σ a‖ := by
    intro a
    have h1 : tauE c (ComplexEmbedding.conjugate τ) a = tauE c τ (IsCMField.complexConj E a) := by
      apply Subtype.ext
      change ComplexEmbedding.conjugate τ a = τ (IsCMField.complexConj E a)
      rw [IsCMField.complexEmbedding_complexConj, ComplexEmbedding.conjugate_coe_eq]
    have h2 : σ' a = σ (IsCMField.complexConj E a) := by
      simp only [σ', σ, RingHom.comp_apply, h1]
    rw [h2, IsCMField.complexEmbedding_complexConj, RCLike.norm_conj]
  have hrt : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hlΓ := log_norm_det_scaled σ (H.rt : E) H.d H.d_prime.pos hrt n hn (X.ε true)
    (gramE (FU.Di i) (x ∘ Sum.inl)) hG1
    (Matrix.of fun a a' => (n : ℂ) * ((X.ε true : ℤ) : ℂ) *
      s' (X.β (tauE c τ ((H.rt : E) * sesq (FU.Di i) (x (.inl a)) (x (.inl a')))))) (fun _ _ => rfl)
  have hlΔ := log_norm_det_scaled σ' (H.rt : E) H.d H.d_prime.pos hrt n' hn' (X.ε false)
    (gramE (FU.Di i) (x ∘ Sum.inr)) hG2
    (Matrix.of fun a a' => (n' : ℂ) * ((X.ε false : ℤ) : ℂ) *
      s' (X.β (tauE c (ComplexEmbedding.conjugate τ) ((H.rt : E) * sesq (FU.Di i) (x (.inr a)) (x (.inr a')))))) (fun _ _ => rfl)
  rw [hσ'] at hlΔ

  have hz := _root_.GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H _ (Z true)
  have hval2 : ((φ X.K X.y v w : X.K) : ℂ) * τ T.det = (r : ℂ) * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    apply mul_right_cancel₀ (pow_ne_zero D.p hz)
    rw [hval, ← hrz]
    ring
  have hK : (φ X.K X.y v w) * X.β (tauE c τ T.det) =
      IntermediateField.inclusion hkK r * X.β (tauE c τ (gramE (FU.Di i) (x ∘ Sum.inr)).det) :=
    Subtype.ext hval2
  have hS : s' (φ X.K X.y v w) * σ T.det = s r * σ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
    have := congrArg s' hK
    rw [map_mul, map_mul, hs'a] at this
    exact this
  have hφ0 : s' (φ X.K X.y v w) ≠ 0 := (map_ne_zero s').2 (hline.ne X.K X.β X.y v w hfram)
  have hσT : σ T.det ≠ 0 := (map_ne_zero σ).2 hTne
  have hσG2 : σ (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := (map_ne_zero σ).2 hG2
  have hσG1 : σ (gramE (FU.Di i) (x ∘ Sum.inl)).det ≠ 0 := (map_ne_zero σ).2 hG1
  have hσGe : σ (gramE (FU.Di i) e).det ≠ 0 := (map_ne_zero σ).2 hGe
  have hsr : s r ≠ 0 := (map_ne_zero s).2 hr
  have hl1 : Real.log ‖s' (φ X.K X.y v w)‖ + Real.log ‖σ T.det‖ =
      Real.log ‖s r‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hφ0) (norm_ne_zero_iff.2 hσT),
      ← Real.log_mul (norm_ne_zero_iff.2 hsr) (norm_ne_zero_iff.2 hσG2), ← norm_mul, ← norm_mul, hS]
  have hl2 : Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inl)).det‖ + Real.log ‖σ (gramE (FU.Di i) (x ∘ Sum.inr)).det‖ =
      2 * Real.log ‖σ T.det‖ + Real.log ‖σ (gramE (FU.Di i) e).det‖ := by
    have h1 := congrArg σ (hdet1.symm.trans hdet2)
    rw [map_mul, map_mul, map_mul, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj] at h2
    have h3 := congrArg Real.log h2
    rw [Real.log_mul (norm_ne_zero_iff.2 hσG1) (norm_ne_zero_iff.2 hσG2),
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)) (norm_ne_zero_iff.2 hσT),
      Real.log_mul (norm_ne_zero_iff.2 hσT) (norm_ne_zero_iff.2 hσGe)] at h3
    linarith
  have hlast : s ((((IntermediateField.inclusion hc).toRingHom).comp (tauE c τ)) (gramE (FU.Di i) e).det) =
      σ (gramE (FU.Di i) e).det :=
    (DFunLike.congr_fun hβ (tauE c τ (gramE (FU.Di i) e).det)).symm
  rw [hlast]
  rw [hlΓ, hlΔ] at hmain
  linarith

end GlobalTheory.CompanionTheory.Ar.Fl.InfPlace
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionCmValue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg

theorem finite_fieldRange {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) :
    FiniteDimensional ℚ τ.toRatAlgHom.fieldRange :=
  (AlgEquiv.ofInjectiveField τ.toRatAlgHom).toLinearEquiv.finiteDimensional

theorem const_algebraic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H)
    (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty)
    (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 →
    (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) →
    IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ →
    ∃ (k : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ k) (r : k), c.F ≤ k ∧ (∀ b, (Z b).M ≤ k) ∧ r ≠ 0 ∧
      (r : ℂ) * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q := by
  intro E _ _ _ H D l Xo c g ty FU i Z U τ φ e ρ hty hrt hmem hline he hconst
  obtain ⟨P, hP, x, hx, X, v, w, hk, hloc, hfr⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fl.exists_cmPoint_locBasis_frames E H D l Xo c g ty FU i Z τ ⟨2, Nat.prime_two⟩ τ.toRatAlgHom.fieldRange (finite_fieldRange τ) hty hrt
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨T, hT, -, hdet, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists E H (FU.Di i) _ x e hcard he
  have hT0 : T.det ≠ 0 := hdet hloc.1
  have horth : ∀ a b, sesq (FU.Di i) (x (.inl a)) (x (.inr b)) = 0 := fun a b =>
    (_root_.GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 b)).1
  have hG0 := (_root_.GlobalTheory.CompanionTheory.Ar.Fl.orthogonalBlock_gram_det_log_norm E H (FU.Di i) D.p D.q x ⟨2, Nat.prime_two⟩ hloc horth).1
  obtain ⟨hfm, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame E H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hrt hmem hline he
    hconst hloc.1 hT hfr
  have hφ : φ X.K X.y v w ≠ 0 := hline.ne X.K X.β X.y v w hfm
  have hmemK : ∀ t : E, τ t ∈ X.K := fun t => hk (τ.toRatAlgHom.mem_fieldRange.2 ⟨t, rfl⟩)
  set G := gramE (FU.Di i) (x ∘ Sum.inr) with hGdef
  let a : X.K := ⟨τ T.det, hmemK _⟩
  let b : X.K := ⟨τ G.det, hmemK _⟩
  have ha : a ≠ 0 := fun h => hT0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hb : b ≠ 0 := fun h => hG0 ((map_eq_zero τ).1 (congrArg Subtype.val h))
  have hbC : τ G.det ≠ 0 := (map_ne_zero τ).2 hG0
  refine ⟨X.K, inferInstance, φ X.K X.y v w * a / b, X.hc, X.hM, div_ne_zero (mul_ne_zero hφ ha) hb, ?_⟩
  have hcoe : ((φ X.K X.y v w * a / b : X.K) : ℂ) = ((φ X.K X.y v w : X.K) : ℂ) * τ T.det / τ G.det := rfl
  rw [hcoe]
  field_simp
  linear_combination hval

end GlobalTheory.CompanionTheory.Ar.Fl.ConstAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelClauseOfRankZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem modelClause_of_rankZero
    (hz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
      D.p + D.q = 0 → ToroidalLevelCompatibility (H := H) (D := D) ∧ ToroidalHeckeCompatibility (H := H) (D := D)) :
    PartI ∧ N1ab ∧ N1c ∧
      ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
        ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D) := by
  refine ⟨partI_holds, moduli_schemes_exist, complex_uniformisation_holds, ?_⟩
  intro E _ _ _ H D
  by_cases h : D.p + D.q = 0
  · exact hz E H D h
  · exact levelMaps_heckePoints_of_pos E H D (by omega)

end GlobalTheory.CompanionTheory.Ar.Top
end

