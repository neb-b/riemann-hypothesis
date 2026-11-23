module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcDatumSectionValueCoeffEqFourierJacobi
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNormAnOnOrbit
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicIndexSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TransvInOfHasPrinc
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FourierJacobiCoeffLinearBoundedSections
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmArcFunctionalVanishesLowFourierJacobi
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcKill

theorem eq_zero_of_eval_off {σ : Type} {P Q : MvPolynomial σ ℂ} (hQ : Q ≠ 0)
    (h : ∀ x, MvPolynomial.eval x Q ≠ 0 → MvPolynomial.eval x P = 0) : P = 0 := by
  have : P * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : MvPolynomial.eval x Q = 0
    · rw [hx, mul_zero]
    · rw [h x hx, zero_mul]
  exact (mul_eq_zero.1 this).resolve_right hQ

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem coeff_eq_zero_of_invBl (S : Finset (ArcLt Dw →₀ ℕ)) (f : (ArcLt Dw →₀ ℕ) → ℂ)
    (h : ∀ x : ArcLt Dw → ℂ, InvBl x → ∑ mo ∈ S, f mo * ∏ v ∈ mo.support, x v ^ mo v = 0) : ∀ mo ∈ S, f mo = 0 := by
  classical
  let Q : MvPolynomial (ArcLt Dw) ℂ := ∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) =>
    (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)).det
  have hQe : ∀ x : ArcLt Dw → ℂ, MvPolynomial.eval x Q ≠ 0 ↔ InvBl x := fun x => by
    rw [map_prod, Finset.prod_ne_zero_iff]
    refine forall_congr' fun τ => ?_
    have : (MvPolynomial.eval x).mapMatrix (Matrix.of fun i k : Fin (Dw.mult τ) =>
        (MvPolynomial.X (⟨τ, (i, k)⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℂ)) =
        Matrix.of fun i k : Fin (Dw.mult τ) => x ⟨τ, (i, k)⟩ := by
      ext i k : 2
      simp
    rw [RingHom.map_det, this]
    simp
  have hone : InvBl (Dw := Dw) fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2 :=
    fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
  have hQ : Q ≠ 0 := fun h0 => (hQe _).2 hone (by rw [h0, map_zero])
  have hP : ∑ mo ∈ S, MvPolynomial.monomial mo (f mo) = 0 := eq_zero_of_eval_off hQ fun x hx => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← h x ((hQe x).1 hx)]
    exact Finset.sum_congr rfl fun mo _ => MvPolynomial.eval_monomial
  intro mo hmo
  have := congrArg (AddMonoidAlgebra.coeff · mo) hP
  rw [MvPolynomial.coeff_sum] at this
  simpa [MvPolynomial.coeff_monomial, hmo] using this

theorem cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (em : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Fam n' La c₁ d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ F ∈ sec Xo c a' n, (∀ k, rdU U F k ∈ (U.X k).SSgt (laU U a' n k) c₁) → cfOf d.yF d.μ d.jj F = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ em r U a' n hfam hgood hunf hdom htv F hF hS
  obtain ⟨⟨hover, -, hpush⟩, ⟨s⟩⟩ := hfam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hmain⟩ := _root_.GlobalTheory.ArcId.ajAt_eq_fj hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5
    E H Dw l Xo c K₁ d em r U s.ξ s.ν₀ a' n (hK.ev E H Dw l Xo c) hgood hunf hover s.tan hpush s.rk s.ξ_ne s.beta
    hdom htv
  have hν : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    have h1 := TraceFormIndependence.trace_re (U.X k) s.ν₀
    have h2 := s.tr
    rw [h1, ← Finset.mul_sum] at h2
    linarith
  have h0 : ∀ x, InvBl x → ajAt d em F x = 0 := fun x hx => by
    have := hmain F hF (hS k).1.1 x hx
    rw [(hS k).2 ξ' hiso _ hν _ (hfr x hx), mul_zero] at this
    exact (mul_eq_zero.1 this).resolve_right (zpow_ne_zero _ hu)
  unfold cfOf
  by_cases hmo : d.μ ∈ (arcNum (evR Xo c F d.yF)).support
  · exact (map_eq_zero em).1 (coeff_eq_zero_of_invBl _
      (fun mo => em (((arcNum (evR Xo c F d.yF)).coeff mo).coeff d.jj)) h0 _ hmo)
  · rw [MvPolynomial.notMem_support_iff.1 hmo]
    rfl

end GlobalTheory.ArcKill
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCmArcDataAtSplitIsotropicPoint
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM.Exist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_lift_fibre {R R₂ K : Type} [CommRing R] [CommRing R₂] [Field K] {B : GlobalTheory.CM.PAT H (Sp R)}
    {B₂ : GlobalTheory.CM.PAT H (Sp R₂)} {j : R →+* R₂} (m : SABMap B₂.t B.t (spMap j)) {f : R →+* K} {f₂ : R₂ →+* K}
    (hf : f₂.comp j = f) {P : Out.PolAV (Sp K)} {ψ : P.A.left ⟶ B.pol.A.left} (hψ : IsPolFibre f B.pol P ψ)
    (act : 𝓞 E → (P.A ⟶ P.A)) (hact : ∀ x, (act x).left ≫ ψ = ψ ≫ (B.t.act.act x).left) :
    ∃ ψ₂ : P.A.left ⟶ B₂.pol.A.left, IsPolFibre f₂ B₂.pol P ψ₂ ∧
      ∀ x, (act x).left ≫ ψ₂ = ψ₂ ≫ (B₂.t.act.act x).left := by
  have hs : spMap f₂ ≫ spMap j = spMap f := (GlobalTheory.ArcId.sp_comp _ _).trans (congrArg spMap hf)
  have w : ψ ≫ B.t.G.hom = (P.A.hom ≫ spMap f₂) ≫ spMap j :=
    hψ.2.1.1.w.trans (by rw [Category.assoc, hs])
  obtain ⟨ψ₂, h₁, h₂⟩ : ∃ ψ₂ : P.A.left ⟶ B₂.t.G.left, ψ₂ ≫ m.φ = ψ ∧ ψ₂ ≫ B₂.t.G.hom = P.A.hom ≫ spMap f₂ :=
    ⟨_, m.cart.1.lift_fst _ _ w, m.cart.1.lift_snd _ _ w⟩
  have g₂ : IsGrpPullback P.A B₂.t.G (spMap f₂) ψ₂ := m.cart.cancel (hψ.2.1.congr hs.symm h₁.symm) h₂
  refine ⟨ψ₂, ⟨?_, g₂, ?_⟩, fun x => ?_⟩
  · exact H1.dim_unique P.A.hom P.smoothDim
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g₂.1 B₂.dim)
      (eSec P.A (IsLocalRing.closedPoint K))
  · have e : LBIso (B₂.t.PP.L.pull ψ₂) (B.t.PP.L.pull ψ) :=
      GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) ψ₂ h₁.symm
    exact LBIso.trans (pull_isLB B₂.t.PP.isLB _) (pull_isLB B.t.PP.isLB _) P.isLB e hψ.2.2
  · apply m.cart.1.hom_ext
    · have e := m.act x
      change ((act x).left ≫ ψ₂) ≫ m.φ = (ψ₂ ≫ (B₂.t.act.act x).left) ≫ m.φ
      rw [Category.assoc, Category.assoc, h₁, hact, e, ← Category.assoc, h₁]
    · rw [Category.assoc, Category.assoc, h₂, Over.w (B₂.t.act.act x), h₂, ← Category.assoc, Over.w (act x)]

theorem one_le_of_isIso {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    {U : Unf Xo c σ r} (hU : IsUnf U) {k : U.Comp} {ξ' : Fin r → E} (hξ : (U.X k).IsIso ξ') :
    1 ≤ Dw.p ∧ 1 ≤ Dw.q := by
  obtain ⟨τ⟩ : Nonempty (U.X k).Ψ := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    by_cases h : τ ∈ (U.X k).Ψ
    · exact ⟨⟨τ, h⟩⟩
    · exact ⟨⟨_, by_contra fun h' => h (((U.X k).cmType τ).2 h')⟩⟩
  have h := IsotropicIndexSums.isotropicIndex_bounds (U.X k) hξ.2.1 hξ.2.2 τ
  have h1 := hU.1
  have h2 := (hU.2.1 k).1
  omega

theorem exists_cmIn_tie : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (Xx : DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (La₀ La c₁ : ℝ) (lam : Fin (r - 2) → Fin r → E) (n' : ℕ) (ν₀ : E), IsUnf U → l.A = 1 → 3 ≤ r → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → SplitData Xx ξ' La₀ (hX ▸ x) lam → La₀ ^ 2 ≤ La ^ 2 → 0 < n' → (∀ m ∈ (U.X k).Λp ξ', ∃ e : E, e • ξ' ∈ (U.X k).Λ ∧ (n' : ℂ) • (U.X k).aproj x ξ' ((U.X k).embV m) = (U.X k).embV (e • ξ')) → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s : E, cc s = s → (∀ v ∈ (U.X k).Λ, ∃ u ∈ (U.X k).Λ, (transvMat (U.X k).Gm ξ' (s * (U.X k).κ0)).mulVec v - v = (l.M' : E) • u) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ((Algebra.trace ℚ E ν₀ : ℚ) : ℝ) / 2 ≤ c₁ → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra c.F K₁) (em : K₁ →+* ℂ) (a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)) (th : a.D₀.P.L.Sec) (jj : ℤ) (s : CMIn a e th jj n' La c₁), em.comp (algebraMap c.F K₁) = c.F.val.toRingHom ∧ s.ν₀ = ν₀ ∧ Comparison₂ Uw a em s.ξ k ξ' x := by
  intro hK E _ _ _ H Dw l Xo c _ _ r U Uw k ξ' x Xx hX 𝔄 La₀ La c₁ lam n' ν₀ hU hA hr hξ hx h𝔄 hΛ hS hLa hn hap hν hν₀
    hint htr
  letI := H.starRing
  have hg : GoodEmb c c.F.val.toRingHom := rfl
  obtain ⟨hp, hq⟩ := one_le_of_isIso hU hξ
  have hpq : 3 ≤ Dw.p + Dw.q := hU.1 ▸ hr
  obtain ⟨A, gam, ξ, jj, DB, tyB, eB, hO, hξ0, hrk, hdvd, hbeta, hprim, hct, hab, hDp, hDq⟩ :=
    GlobalTheory.T.exists_analytic_model_on_frame_orbit_isolating E H Dw l Xo c _ r U Uw k ξ' x n' ν₀ hg hU hξ hx hap hν hν₀ hint
  obtain ⟨A', gam', ξ₁, eX, hO', hprim', hnorm', hξ₁, hbe', hab'⟩ :=
    GlobalTheory.ArcShift.exists_normAn_onOrbit E H Dw l Xo c _ r U Uw k ξ' x n' hg hU hξ hx hn A gam ξ hO hξ0 hrk hprim hct
  obtain ⟨tyB', eB', hB'⟩ := hab' DB ⟨tyB, eB, hab⟩
  have hrk' : Module.finrank (𝓞 E) A'.X = 1 := eX.finrank_eq.trans hrk
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_cm_lattice_data_abelianPart_split_point E H Dw l Xo c _ r U Uw k ξ' x Xx hX 𝔄 La₀ lam hg hU hξ hx h𝔄 hΛ hS A' gam' ξ₁ DB
    tyB' eB' hO' hrk' hDp hDq hB'
  obtain ⟨K, _, _, _, σ₁, ρ, X, ex, hσ₁, hρ, hhh, hex⟩ :=
    GlobalTheory.ArcCM.exists_cmObj_of_period hK E H l c DB _ tyB' _ hB'.2.2.2.2 Z (by omega) hB'.2.1 hA
  obtain ⟨aC, Λ, hΛA, φ, hφ, hφa, hlift⟩ := GlobalTheory.T.exists_complexArcDatum_cmFibre hK E H Dw l Xo c _ r U Uw k ξ' x (𝓞 K) X.B _ hg hU hA A' gam'
    ξ₁ DB tyB' eB' ex hO' hrk' (fun y y' => (hbe' y y').symm ▸ hdvd _ _) hprim' hB' hDp hDq hp hq hex
  subst hΛA
  have htau : TauCan aC.D₀ n' := (GlobalTheory.KappaAn.tauCan_iff_normAn E H Dw l c _ _ _ aC Λ.toGtAn₀ n').2 hnorm'
  let fC : aC.D₀.X ≃ₗ[𝓞 E] A.X := Λ.eX.symm.trans eX
  let ξC : Module.Dual ℤ aC.D₀.X := ξ.comp (fC.toLinearMap.restrictScalars ℤ)
  have htie := GlobalTheory.T.holomorphicArc_matches_frame_of_model_on_orbit hK E H Dw l Xo c _ r U Uw k ξ' x aC Λ.toGtAn₀ ξC hg hU hξ hx hA gam' ξ₁ hO'
    (fun y => by rw [hξ₁]; exact congrArg (fun z => ξ (eX z)) (Λ.eX.symm_apply_apply y)) hlift
  obtain ⟨K₂, _, _, _, i, σ₂, a, p, ψ, hσ₂, hbc, htau₂, hψ, hψa⟩ :=
    GlobalTheory.T.exists_cmArcData_descent_numberField hK E H Dw l c K σ₁ _ X.B aC φ n' hσ₁ hn hφ hφa htau
  obtain ⟨ρ₂, X₂, m, hρ₂, hh₂⟩ := GlobalTheory.ArcCM.exists_cmObj_baseChange hK E H K ρ σ₁ _ _ X K₂ i σ₂ hσ₂
  obtain ⟨ψ₂, hψ₂, hψa₂⟩ := exists_lift_fibre m (f₂ := algebraMap (𝓞 K₂) K₂) (RingHom.ext fun _ => rfl) hψ
    a.oa.onB.act hψa
  let f : aC.D₀.X ≃ₗ[𝓞 E] a.D₀.X := { p.xe with map_smul' := hbc.2.1 }
  let g : a.D₀.X ≃ₗ[𝓞 E] A.X := f.symm.trans fC
  have hem : σ₂.comp (algebraMap c.F K₂) = c.F.val.toRingHom := by
    rw [← hσ₁, ← hσ₂]
    exact RingHom.ext fun y => congrArg σ₂ (i.commutes y).symm
  have hbe : ∀ y z, a.be y z = A.be (g y) (g z) := fun y z => by
    obtain ⟨y, rfl⟩ := (Λ.eX.trans f).surjective y
    obtain ⟨z, rfl⟩ := (Λ.eX.trans f).surjective z
    refine (hbc.2.2.1 _ _).symm.trans ((Λ.be_eq _ _).trans ((hbe' _ _).trans ?_))
    simp [g, fC]
  have hhh₂ : ∀ j (τ : E →+* ℂ), ‖τ (X₂.hh j : E)‖ ≤ La ^ 2 := fun j τ => by
    rw [hh₂, hhh]; exact (hZ j τ).trans hLa
  have hρ' : σ₂ (ρ₂ : K₂) = H.rt0 := by rw [hρ₂, ← hρ, ← hσ₂]; rfl
  clear m hh₂
  generalize DB.p = p₁, DB.q = q₁ at X₂ hDp hDq hhh₂ ψ₂ hψ₂ hψa₂
  subst hDp hDq
  obtain ⟨e, th, s, hs, hsν⟩ := GlobalTheory.ArcCM.Letters.exists_cmIn hK E H Dw l c K₂ a ρ₂ σ₂ X₂ ψ₂ n' La c₁
    (ξ.comp (g.toLinearMap.restrictScalars ℤ)) ν₀ jj hp hq hpq hem hρ' hhh₂ hψ₂ hψa₂ hn htau₂
    (g.finrank_eq.trans hrk)
    (fun h => hξ0 (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := g.surjective y
      exact LinearMap.congr_fun h y))
    (GlobalTheory.ArcId.betaAt_comp g ξ hbe hbeta) htr
  refine ⟨K₂, _, _, _, σ₂, a, e, th, jj, s, hem, hsν, aC, p, ξC, hbc, fun y => ?_, htie⟩
  rw [hs]
  exact congrArg (fun z => ξ (fC z)) (f.symm_apply_apply y).symm

end GlobalTheory.ArcCM.Exist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsCoeffNeZeroOfFourierJacobiArcDatum
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.DerivativeDetermination

theorem linear_ext {T : Type} {g : ℕ} (e : Fin g ≃ T) {A B : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (h : ∀ t, A (Pi.single (e.symm t) 1) = B (Pi.single (e.symm t) 1)) : A = B := by
  refine (Pi.basisFun ℂ (Fin g)).ext fun j => ?_
  have := h (e j)
  rwa [Equiv.symm_apply_apply, ← Pi.basisFun_apply] at this

theorem exists_inverse_comb {T : Type} {m : T → ℕ} {g : ℕ} (e : Fin g ≃ Σ τ : T, Fin (m τ)) (τ : T)
    (z : Fin (m τ) → Fin g → ℂ) (hz : LinearIndependent ℂ z) (ht : ∀ i j, z i j ≠ 0 → (e j).1 = τ) :
    ∃ X : Matrix (Fin (m τ)) (Fin (m τ)) ℂ, X.det ≠ 0 ∧
      ∀ i, ∑ k, X i k • z k = Pi.single (e.symm ⟨τ, i⟩) 1 := by
  classical
  let A : Matrix (Fin (m τ)) (Fin (m τ)) ℂ := Matrix.of fun k i => z k (e.symm ⟨τ, i⟩)
  have hcase : ∀ j, (∃ i, j = e.symm ⟨τ, i⟩) ∨ ∀ k, z k j = 0 := fun j => by
    by_cases h : (e j).1 = τ
    · subst h
      exact Or.inl ⟨(e j).2, (e.symm_apply_apply j).symm⟩
    · exact Or.inr fun k => by_contra fun h' => h (ht k j h')
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit, Fintype.linearIndependent_iff]
    intro c hc
    refine Fintype.linearIndependent_iff.1 hz c (funext fun j => ?_)
    rcases hcase j with ⟨i, rfl⟩ | h
    · simpa [A] using congrFun hc i
    · simp [h]
  have hd := (Matrix.isUnit_iff_isUnit_det A).1 hA
  refine ⟨A⁻¹, (Matrix.isUnit_nonsing_inv_det A hd).ne_zero, fun i => funext fun j => ?_⟩
  rcases hcase j with ⟨i', rfl⟩ | h
  · have := congrFun (congrFun (Matrix.nonsing_inv_mul A hd) i) i'
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [Finset.sum_apply, Pi.single_apply]
    refine this.trans (if_congr ⟨fun h => by rw [h], fun h => ?_⟩ rfl rfl)
    exact (eq_of_heq (Sigma.mk.inj (e.symm.injective h)).2).symm
  · rw [Finset.sum_apply, Finset.sum_eq_zero fun k _ => by rw [Pi.smul_apply, h, smul_zero]]
    by_contra hne
    obtain rfl : j = e.symm ⟨τ, i⟩ := by_contra fun h' => hne (by rw [Pi.single_eq_of_ne h'])
    have := congrFun (congrFun (Matrix.nonsing_inv_mul A hd) i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    exact zero_ne_one ((Finset.sum_eq_zero fun k _ => mul_eq_zero_of_right _ (h k)).symm.trans this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem ex_eq_of_deriv {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ ty) {T : Type}
    (e : Fin g ≃ T) {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i') ty P') (hu : F.u i P = F.u i' P')
    (v : T → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
    (hv : ∀ t, IsDerivAt0 (fun z => (F.ex i P z).left) (Pi.single (e.symm t) 1) (v t))
    (hv' : ∀ t, IsDerivAt0 (fun z => (F.ex i' P' z).left) (Pi.single (e.symm t) 1) (v t)) (z : Fin g → ℂ) :
    (F.ex i P z).left = (F.ex i' P' z).left := by
  obtain rfl : i = i' := F.disj i i' P P' hP hP' hu
  obtain ⟨gam, h, h1, h2, h3, h4⟩ := (F.fibre i P P' hP hP').1 hu
  have hm : ∀ z, (LinearMap.toMatrix' h.toLinearMap).mulVec z = h z := fun z =>
    LinearMap.toMatrix'_mulVec _ z
  obtain ⟨-, -, h5⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E H Dw l Xo σ g ty F i P P' gam
    (LinearMap.toMatrix' h.toLinearMap) hP hP' h1 h2 h3 (fun a => by rw [hm, h4])
  simp only [hm] at h5
  obtain ⟨t1, -, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ g ty F i P' hP'
  have hid : h.toLinearMap = LinearMap.id := linear_ext e fun t =>
    (t3 _ (t1 _ _ (hv' t))).unique
      ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo σ g ty F i P hP i P' h.toLinearMap hP' h5 _ _).1 (hv t)) (hv' t)
  rw [← h5 z]
  exact congrArg (fun w => (F.ex i P' w).left) (LinearMap.congr_fun hid z)

theorem type_map {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    {i i' : Fin F.n} {P : (F.Di i).La →+ (Fin g → ℂ)} {P' : (F.Di i').La →+ (Fin g → ℂ)}
    (hP : IsPeriod (F.Di i) (fun j => relab c σ (e j).1) P)
    (hP' : IsPeriod (F.Di i') (fun j => relab c σ (e j).1) P') (L : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hL : ∀ z, (F.ex i' P' (L z)).left = (F.ex i P z).left) (τ : E →+* ℂ) (w : Fin g → ℂ)
    (hw : ∀ j, w j ≠ 0 → (e j).1 = τ) : ∀ j, L w j ≠ 0 → (e j).1 = τ := by
  obtain ⟨v, hv, -⟩ := (GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ g _ F i P hP).2.1 w
  exact (GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F i' P' hP' _ v τ
    ((GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ g _ F i P hP i' P' L hP' hL _ _).1 hv)).1
    ((GlobalTheory.isEigAt_iff_of_isDerivAt0 E H Dw l Xo c σ g e F i P hP _ v τ hv).2 hw)


open GlobalTheory.ArcId in
set_option maxHeartbeats 1000000 in
theorem exists_cfOf_ne_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (n' : ℕ) (La c₁ : ℝ) (s : CMIn d.a d.e d.th d.jj n' La c₁) (em : K₁ →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (r : ℕ) (U : Unf Xo c (em.comp (algebraMap c.F K₁)) r) (Uw : UnfWit U) (k : U.Comp) (ξ' : Fin r → E) (x : Frame (U.X k).Ψ r) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Std d → GoodEmb c (em.comp (algebraMap c.F K₁)) → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso ξ' → x ∈ (U.X k).dom → Comparison₂ Uw d.a em s.ξ k ξ' x → ∀ F ∈ sec Xo c a' n, (∀ k', (U.X k').IsBddSec (laU U a' n k') (rdU U F k')) → (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U F k) x ≠ 0 → ∃ mo : ArcLt Dw →₀ ℕ, cfOf d.yF mo d.jj F ≠ 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d n' La c₁ s em _ _ r U Uw k ξ' x a' n hstd hgood hunf hprinc hdom hχ hiso hx
    htie F hF hbdd hfj
  have h1 := hK.laws
  have h2 := hK.laws2
  have hev := hK.ev E H Dw l Xo c
  obtain ⟨hover, ⟨y₀, hy₀, hc⟩, hpush⟩ := hstd
  obtain ⟨aC, p, ξC, hp, hξC, htie⟩ := htie
  letI : Algebra c.F ℂ⸨X⸩ := (cstL.comp (em.comp (algebraMap c.F K₁))).toAlgebra
  have hth : ThNZ d.th := s.th_nz
  have hp' : InBC em (d.a.restrict (c.V d.Wp).subtype) (aC.restrict (c.V d.Wp).subtype) p := ⟨rfl, hp.2⟩
  obtain ⟨hW, hlet, htan, hthx, hnz⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hK.ubc hK.laws5 E H Dw l Xo c _ _ d.Y K₁ ℂ _
    (d.a.restrict (c.V d.Wp).subtype) em em.injective ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) rfl).2
    (aC.restrict (c.V d.Wp).subtype) p hp'
  obtain ⟨W₁, hW₁⟩ := hW d.χ d.W
  choose e₁ he₁ using fun τ k => (hlet (d.e τ k)).exists
  obtain ⟨th₁, hth₁⟩ := (hthx d.th).exists
  have hover₁ : (spMap (PowerSeries.map em) ≫ d.χ) ≫ d.Y.s = spMap (PowerSeries.C (R := ℂ)) ≫
      spMap ((em.comp (algebraMap c.F K₁)).comp (c.V d.Wp).subtype) := by
    rw [Category.assoc, hover, sp_comp, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext fun x => PowerSeries.map_C _ _
  obtain ⟨Ha⟩ := hK.n5 E H Dw l Xo c _ _ d.Y (em.comp (algebraMap c.F K₁)) (aC.restrict (c.V d.Wp).subtype) _ W₁ Uw.g _
    Uw.F hgood ((GlobalTheory.Relab.relab_good E H l c _ hgood).2.2.2 Dw Uw.g Uw.e) (GlobalTheory.ArcInTest.exists_values c d.Wp) hover₁
    (generic_mem d em)
  obtain ⟨w₁, sf, hs, L₀, t, t', hw₁, ht, ht', hL₀t, hu, hex⟩ := htie _ _ d.Y _ W₁ Ha
  let f : aC.D₀.X ≃ₗ[𝓞 E] d.a.D₀.X := { p.xe with map_smul' := hp.2.1 }
  have hξf : ξC = s.ξ.comp (f.toLinearMap.restrictScalars ℤ) := LinearMap.ext hξC
  obtain ⟨k', ξ'', sE, C, hiso', -, -, -, hC, -, hmain⟩ := GlobalTheory.ArcCoeffAt.coeff_evR_eq_fj_anLie h1 h2 E H Dw l Xo c _ r
    U Uw _ _ d.Y (aC.restrict (c.V d.Wp).subtype) _ W₁ Ha th₁ ξC s.ν₀ d.jj a' n hev hgood hunf (fun _ => rfl) hover₁
    (mono_spMap_subtype _) hpush (hnz _ _ hth₁ hth) (f.finrank_eq.trans s.rk)
    (fun h => s.ξ_ne (LinearMap.ext fun y => by
      obtain ⟨y, rfl⟩ := f.surjective y
      exact (hξC y).symm.trans (LinearMap.congr_fun h y)))
    (hξf ▸ betaAt_comp f s.ξ hp.2.2.1 s.beta) hdom
    (GlobalTheory.TransvPrinc.transvIn_of_hasPrinc E H Dw l Xo c _ r U a' n hprinc hχ) w₁ hw₁
  obtain ⟨v₁, v₂, -, v₄⟩ := GlobalTheory.ExpTan.anVec_bijective h1.globalFns E H Dw l Xo c _ _ _ d.Y
    (aC.restrict (c.V d.Wp).subtype) _ W₁ _ _ Uw.F Ha
  choose z₁ hz₁ using fun τ i => (v₁ (e₁ τ i) (htan _ _ (he₁ τ i) (s.tan τ i))).exists
  have key : ∀ X : ArcLt Dw → ℂ, InvBl X → ∃ e₂ y, (∀ τ i, AnVec Ha (e₂ τ i) (∑ j, X ⟨τ, (i, j)⟩ • z₁ τ j)) ∧
      IsArcFr W₁ e₂ th₁ (HahnSeries.ofPowerSeries ℤ ℂ) y ∧ ajAt d em F X = (evR Xo c F y).coeff d.jj := fun X hX => by
    choose e₂ he₂ using fun (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) => (v₂ (∑ j, X ⟨τ, (i, j)⟩ • z₁ τ j)).exists
    obtain ⟨-, y, hy, hval⟩ := exists_frPt_at h1 h2 hev d em (fun _ => rfl) hy₀ hc hth hp' hW₁ he₁ hth₁
      (hnz _ _ hth₁ hth) hX (fun τ i => (v₄ _ _ _ _ _ (hz₁ τ)).2 (he₂ τ i)) a' n
    exact ⟨e₂, y, he₂, hy, by rw [hval F hF, map_one, one_pow, _root_.one_mul]⟩
  have hP := Ha.period w₁ hw₁
  have hQ := Uw.period k ⟨_, hs⟩
  have hzt : ∀ τ, LinearIndependent ℂ (z₁ τ) ∧ ∀ i j, z₁ τ i j ≠ 0 → (Uw.e j).1 = τ := by
    obtain ⟨e₂, y, he₂, hy, -⟩ := key (fun v => (1 : Matrix (Fin (Dw.mult v.1)) (Fin (Dw.mult v.1)) ℂ) v.2.1 v.2.2)
      fun τ => (Matrix.det_one (n := Fin (Dw.mult τ)) (R := ℂ)).trans_ne one_ne_zero
    refine GlobalTheory.ArcType.main h1 h2 E H Dw l Xo c _ r U Uw _ _ d.Y _ _ W₁ Ha y e₂ th₁ z₁ hgood (fun _ => rfl)
      (GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)) hy fun τ i => ?_
    simpa [Matrix.one_apply] using he₂ τ i
  choose Xm hXd hXm using fun τ => exists_inverse_comb Uw.e τ (fun i => L₀ (z₁ τ i))
    ((hzt τ).1.map' L₀.toLinearMap L₀.ker) fun i => type_map Uw.e Uw.F hP hQ L₀.toLinearMap hex τ _ ((hzt τ).2 i)
  obtain ⟨e₂, y, he₂, hy, hval⟩ := key (fun v => Xm v.1 v.2.1 v.2.2) hXd
  obtain ⟨x', κ, L, gm, hlie, hgm, -, hLz, ⟨t₂, ht₂, ht₂'⟩, hκ, hco⟩ := hmain e₂ _ y hy he₂
  have hL₀z : ∀ τ i, L₀ (∑ j, Xm τ i j • z₁ τ j) = Pi.single (Uw.e.symm ⟨τ, i⟩) 1 := fun τ i => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hXm τ i, map_sum]
    simp only [map_smul]
  have hLL : ∀ z, L z = L₀ z := fun z => by
    have := linear_ext Uw.e (A := L.toLinearMap ∘ₗ L₀.symm.toLinearMap) (B := LinearMap.id) fun t => by
      change L (L₀.symm _) = Pi.single _ _
      rw [← hL₀z t.1 t.2, L₀.symm_apply_apply, hL₀z]
      exact hLz t.1 t.2
    simpa using LinearMap.congr_fun this (L₀ z)
  obtain ⟨-, -, -, -, -, -, huniq⟩ := GlobalTheory.ArcQ.holArc_nilpotent E H Dw l Xo c _ _ _ d.Y _ _ W₁ _ _ Uw.F Ha
  obtain rfl : t₂ = t := (huniq ξC).unique ht₂ ht
  have hu' : Uw.F.u (Uw.ik k) (Uw.Pm k ⟨_, hs⟩) = Uw.F.u (Uw.ik k') (Uw.Pm k' x') :=
    hu.symm.trans (hlie.1.symm.trans (Uw.lie k' x').1)
  have hex' := ex_eq_of_deriv Uw.F Uw.e hQ (Uw.period k' x') hu' (fun t => (U.un k' x').u t.1 t.2)
    (fun t => hL₀z t.1 t.2 ▸ (GlobalTheory.ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ Uw.F _ _ hP _ _ L₀.toLinearMap hQ hex
      _ _).1 (hlie.2 t.1 t.2)) (fun t => (Uw.lie k' x').2 t.1 t.2)
  have hm := GlobalTheory.FrameMatch.fj_eq_zero_iff_of_same_exp hK E H Dw l Xo c _ r U Uw k k' ⟨_, hs⟩ x' t' (gm t₂) a' n s.ν₀ hgood hunf hprinc hdom hχ
    (ht' ▸ hiso) hu' hex' (by rw [hL₀t, hgm, hLL]) F hF
  rw [ht', ht₂', GlobalTheory.FjCauchy.fj_flow _ (hbdd k) hiso _ hx _ hs] at hm
  have hκ0 : κ ≠ 0 := norm_pos_iff.1 (by
    rw [hκ]
    exact mul_pos (Real.rpow_pos_of_pos (mul_pos hC (Finset.prod_pos fun τ _ =>
      inv_pos.2 (GlobalTheory.FjCauchy.tt_pos _ hiso' x'.2 τ))) _) (BoundedSectionAlgebra.nfac_pos _ x'.2 _))
  have hne := mul_ne_zero hκ0 (mt hm.2 (mul_ne_zero (Complex.exp_ne_zero _) hfj))
  rw [← hco F hF (hbdd k'), ← hval] at hne
  obtain ⟨mo, -, hmo⟩ := Finset.exists_ne_zero_of_sum_ne_zero (left_ne_zero_of_mul hne)
  exact ⟨mo, fun h => left_ne_zero_of_mul hmo ((congrArg em h).trans (map_zero em))⟩

end GlobalTheory.DerivativeDetermination
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SumCmArcFunctionalVanishesLowFourierJacobi
section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.ArcCM

namespace GlobalTheory.ArcKill

theorem sum_cfOf_eq_zero : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (ι : K₁ →+* ℂ) (r : ℕ) (U : Unf Xo c (ι.comp (algebraMap c.F K₁)) r) (a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (La c₁ : ℝ), GoodEmb c (ι.comp (algebraMap c.F K₁)) → IsUnf U → Fam n' La c₁ d → Dom a' n → (∀ k, TransvIn (U.X k) l.M' (laU U a' n k)) → ∀ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → Rul Xo c) (f : ∀ k : U.Comp, Frame (U.X k).Ψ r → ℂ), (∀ i, F i ∈ sec Xo c a' n) → (∀ i k, (U.X k).IsBddSec (laU U a' n k) (rdU U (F i) k)) → (∀ k, f k ∈ (U.X k).SSgt (laU U a' n k) c₁) → (∀ k, ∀ x ∈ (U.X k).dom, f k x = ∑ i, a i * rdU U (F i) k x) → ∀ μ : ArcLt Dw →₀ ℕ, ∑ i, a i * ι (cfOf d.yF μ d.jj (F i)) = 0 := by
  intro hK E _ _ _ H Dw l Xo c K₁ _ _ _ d ι r U a' n n' La c₁ hG hU hFam hDom hT m a F f hF hB hf hfe
  obtain ⟨⟨hob, -, hpush⟩, ⟨s⟩⟩ := hFam
  obtain ⟨k, ξ', fr, u₁, κ, hu, hiso, -, hfr, hid⟩ :=
    _root_.GlobalTheory.ArcId.ajAt_eq_fj hK.laws hK.laws2 hK.ubc hK.laws5 hK.n5 E H Dw l Xo c K₁ d ι r U s.ξ s.ν₀ a' n
      (hK.ev E H Dw l Xo c) hG hU hob s.tan hpush s.rk s.ξ_ne s.beta hDom hT
  refine _root_.GlobalTheory.ArcDense.coeff_eq_zero_of_vanish_on_invBl E H Dw l Xo c K₁ d ι m a F fun x hx => ?_
  have hlin := _root_.GlobalTheory.fj_eq_sum_of_eqOn_dom E r (U.X k) (laU U a' n k) m a (fun i => rdU U (F i) k) (f k) (fun i => hB i k)
    (hfe k) ξ' hiso (fun τ => (τ.1 s.ν₀).re) (fr x) (hfr x hx)
  have htr : ∑ τ : (U.X k).Ψ, (τ.1 s.ν₀).re ≤ c₁ := by
    rw [GlobalTheory.sum_re_cmType_eq_half_trace E r (U.X k) s.ν₀]
    exact s.tr
  have h0 := (hf k).2 ξ' hiso (fun τ => (τ.1 s.ν₀).re) htr (fr x) (hfr x hx)
  have hz : u₁ ^ d.jj ≠ 0 := zpow_ne_zero _ hu
  refine (mul_eq_zero.mp ?_).resolve_right hz
  rw [h0] at hlin
  rw [Finset.sum_mul]
  have : ∀ i, a i * ajAt d ι (F i) x * u₁ ^ d.jj =
      κ x * (a i * (U.X k).fj (laU U a' n k) ξ' (fun τ => (τ.1 s.ν₀).re) (rdU U (F i) k) (fr x)) := by
    intro i
    rw [mul_assoc, hid (F i) (hF i) (hB i k) x hx]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, ← hlin, mul_zero]

end GlobalTheory.ArcKill
end

