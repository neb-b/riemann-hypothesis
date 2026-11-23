module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0176

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BcRigidAtOfIntModel
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isUnit_prod_det (Dw : Datum H) (L : Type) [Field L] : IsUnit (∏ τ, (letM Dw L τ).det) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcS Dw L) (arcDet Dw L)
  have e : algebraMap _ (ArcS Dw L) (arcDet Dw L) = ∏ τ, (letM Dw L τ).det := by
    exact (map_prod _ _ _).trans (Finset.prod_congr rfl fun τ _ => RingHom.map_det _ _)
  exact e ▸ h

theorem exists_letterSub (Dw : Datum H) {K L : Type} [Field K] [Field L] (f : K →+* L)
    (N : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) L) (hN : ∀ τ, IsUnit (N τ).det) :
    ∃ φ : ArcS Dw K →+* ArcS Dw L,
      (∀ g : LaurentSeries K, φ (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) _ (MvPolynomial.C g)) =
        algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) _ (MvPolynomial.C (LetterMap.coeffMap f g))) ∧
      ∀ τ, (letM Dw K τ).map φ = letM Dw L τ * (N τ).map ((arcι Dw L).comp (PowerSeries.C (R := L))) := by
  let g : MvPolynomial (ArcLt Dw) (LaurentSeries K) →+* ArcS Dw L :=
    MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp
      (MvPolynomial.C.comp (LetterMap.coeffMap f)))
      fun x => (letM Dw L x.1 * (N x.1).map ((arcι Dw L).comp (PowerSeries.C (R := L)))) x.2.1 x.2.2
  have hg : IsUnit (g (arcDet Dw K)) := by
    have e : g (arcDet Dw K) = (∏ τ, (letM Dw L τ).det) *
        ∏ τ, (arcι Dw L).comp (PowerSeries.C (R := L)) (N τ).det := by
      rw [← Finset.prod_mul_distrib]
      refine (map_prod g _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
      congr 1
      ext i k : 2
      exact MvPolynomial.eval₂Hom_X' _ _ _
    rw [e]
    exact (isUnit_prod_det Dw L).mul (IsUnit.prod_univ_iff.2 fun τ => (hN τ).map _)
  refine ⟨IsLocalization.Away.lift (arcDet Dw K) hg, fun p => ?_, fun τ => ?_⟩
  · rw [IsLocalization.Away.lift_eq]
    exact MvPolynomial.eval₂Hom_C _ _ _
  · ext i k : 2
    exact (IsLocalization.Away.lift_eq (arcDet Dw K) hg _).trans (MvPolynomial.eval₂Hom_X' _ _ _)

theorem arcι_C (Dw : Datum H) {L : Type} [Field L] (x : L) : arcι Dw L (PowerSeries.C (R := L) x) =
    algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) _ (MvPolynomial.C (HahnSeries.C (Γ := ℤ) x)) := by
  rw [← HahnSeries.ofPowerSeries_C]
  rfl

theorem isUnit_arcι_X (Dw : Datum H) (L : Type) [Field L] : IsUnit (arcι Dw L PowerSeries.X) := by
  have h : HahnSeries.ofPowerSeries ℤ L PowerSeries.X ≠ 0 :=
    (map_ne_zero_iff _ HahnSeries.ofPowerSeries_injective).2 PowerSeries.X_ne_zero
  exact h.isUnit.map ((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries L)) (ArcS Dw L)).comp MvPolynomial.C)

theorem nontrivial_arcS (Dw : Datum H) (L : Type) [Field L] : Nontrivial (ArcS Dw L) :=
  (IsLocalization.injective (ArcS Dw L)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (LetterMap.det_ne_zero Dw L))).nontrivial

theorem exists_mul_pow (T : CDVR) {ϖ : T.V} (h : Irreducible ϖ) (y : T.Fr) :
    ∃ (v : T.V) (n : ℕ), y * algebraMap T.V T.Fr ϖ ^ n = algebraMap T.V T.Fr v := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors T.V) y
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible (nonZeroDivisors.ne_zero s.2) h
  exact ⟨a * u, n, by rw [← map_pow, ← hu, map_mul, ← mul_assoc, hs, map_mul]⟩


set_option maxHeartbeats 800000 in
theorem bcRigidAt_of_intModel : Out.Laws → Out.Laws2 → Out.UnifBaseChangeSt → Out.Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra c.F K₁] (d : ArcDatum Xo c K₁) (w : HeightOneSpectrum (𝓞 K₁)) (Z : FinSite K₁ w) (Dv : DvrFrame d w Z) (Wl : ValuationSubring ℂ) (Yw : Model Xo c (c.V Wl).subtype) (M : IntModel d Dv.Tv Dv.io Wl) (χw : Sp (PowerSeries Dv.Tv.V) ⟶ Yw.X) (Ww : Wit Yw M.aw χw) (y₀ : FrPt Xo c (ArcSR Dw Dv.Tv.V Dv.ϖ)) (ζ : K₁) (lam : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Dv.Tv.Fr) (A Bm : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr), d.OverBase → d.Normal ζ → χw ≫ Yw.s = spMap (PowerSeries.C (R := Dv.Tv.V)) ≫ spMap M.b → (∀ (x : c.F) (v : Dv.Tv.V) (n : ℕ), (Dv.io.comp (algebraMap c.F K₁)) x * algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ ^ n = algebraMap Dv.Tv.V Dv.Tv.Fr v → algebraMap c.F (ArcSR Dw Dv.Tv.V Dv.ϖ) x * arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) Dv.ϖ) ^ n = arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C (R := Dv.Tv.V) v)) → IsArcFr Ww M.ew M.thw (arcιR Dw Dv.Tv.V Dv.ϖ) y₀ → FrChg (letMR Dw Dv.Tv.V Dv.ϖ) 1 y₀ Dv.yR → M.γ ≠ 0 → (∀ τ k, lam τ k ≠ 0) → (∀ τ, A τ * Bm τ = 1) → (∀ τ k l, M.g τ k l = lam τ k * A τ k l) → BcRigidAt Dv (Dv.io ζ * M.γ) lam Bm := by
  intro h1 h2 hU h5 E _ _ _ H Dw l Xo c K₁ _ _ _ d w Z Dv Wl Yw M χw Ww y₀ ζ lam A Bm hd hN hχ hpin hy₀ hyR _ hlam hAB hg
  have calcu := frChg_calculus E H Dw l Xo c
  have exu := frChg_exists_unique_units E H Dw l Xo c
  have frbc := GlobalTheory.FramedBaseChange.exists_frMap h1 E H Dw l Xo c
  have := nontrivial_arcS Dw Dv.Tv.Fr

  let N : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Dv.Tv.Fr :=
    fun τ => Matrix.of fun i k => Bm τ i k * (lam τ k)⁻¹
  have hNg : ∀ τ, N τ * M.g τ = 1 := fun τ => by
    rw [← mul_eq_one_comm.1 (hAB τ)]
    ext i k
    simp only [Matrix.mul_apply, N, Matrix.of_apply, hg]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc, inv_mul_cancel_left₀ (hlam τ j)]
  let κ : Dv.Tv.Fr →+* ArcS Dw Dv.Tv.Fr := (arcι Dw Dv.Tv.Fr).comp (PowerSeries.C (R := Dv.Tv.Fr))

  obtain ⟨φ₀, hφC, hφX⟩ := exists_letterSub Dw Dv.io N fun τ => Matrix.isUnit_det_of_right_inverse (hNg τ)
  have hφι : φ₀.comp (arcι Dw K₁) = (arcι Dw Dv.Tv.Fr).comp (PowerSeries.map Dv.io) := RingHom.ext fun p =>
    (hφC _).trans (by rw [LetterMap.coeffMap_ofPowerSeries]; rfl)
  have hφc : ∀ x : K₁, φ₀ (cst Dw x) = κ (Dv.io x) := fun x =>
    (RingHom.congr_fun hφι (PowerSeries.C x)).trans (congrArg (arcι Dw Dv.Tv.Fr) (PowerSeries.map_C _ _))
  let φ : ArcS Dw K₁ →ₐ[c.F] ArcS Dw Dv.Tv.Fr :=
    { φ₀ with commutes' := fun r => (congrArg φ₀ (arcS_pin Dw K₁ r)).trans ((hφc _).trans (Dv.algW_eq r).symm) }
  obtain ⟨-, -, -, ⟨ψ₀, hψι, hψX⟩, -⟩ := GlobalTheory.LetterDenom.main E H Dw Dv.Tv Dv.ϖ Dv.ϖ_irr.ne_zero
  have hψc : ∀ v, ψ₀ (arcιR Dw Dv.Tv.V Dv.ϖ (PowerSeries.C v)) = κ (algebraMap Dv.Tv.V Dv.Tv.Fr v) := fun v =>
    (RingHom.congr_fun hψι (PowerSeries.C v)).trans (congrArg (arcι Dw Dv.Tv.Fr) (PowerSeries.map_C _ _))
  have hψa : ∀ r : c.F, ψ₀ (algebraMap c.F _ r) = algebraMap c.F _ r := fun r => by
    obtain ⟨v, n, hv⟩ := exists_mul_pow Dv.Tv Dv.ϖ_irr (Dv.io (algebraMap c.F K₁ r))
    have e := congrArg ψ₀ (hpin r v n hv)
    rw [map_mul ψ₀, map_pow ψ₀, hψc, hψc, ← hv, map_mul κ, map_pow κ] at e
    have hu : IsUnit (κ (algebraMap Dv.Tv.V Dv.Tv.Fr Dv.ϖ) ^ n) :=
      (((map_ne_zero_iff _ (IsFractionRing.injective Dv.Tv.V Dv.Tv.Fr)).2 Dv.ϖ_irr.ne_zero).isUnit.map κ).pow n
    exact (hu.mul_right_cancel e).trans (Dv.algW_eq r).symm
  let ψ : ArcSR Dw Dv.Tv.V Dv.ϖ →ₐ[c.F] ArcS Dw Dv.Tv.Fr := { ψ₀ with commutes' := hψa }
  have hψM : ∀ τ, (letMR Dw Dv.Tv.V Dv.ϖ τ).map ψ = letM Dw Dv.Tv.Fr τ := fun τ =>
    Matrix.ext fun i k => hψX ⟨τ, i, k⟩

  obtain ⟨th₁, th₂, t₁, t₂, t₃⟩ := M.th_tie
  obtain ⟨e₁, e₂, l₁, l₂, -, l₃⟩ := M.e_tie
  have bcK : InBC Dv.io (d.a.restrict (c.V d.Wp).subtype) (M.aK.restrict (c.V d.Wp).subtype) M.pK :=
    ⟨rfl, M.bcK.2⟩
  obtain ⟨w₁, -, -, -, n₁⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ Yw Dv.Tv.V Dv.Tv.Fr _ M.aw _
    (IsFractionRing.injective Dv.Tv.V Dv.Tv.Fr) _ M.bcw.1).2 (M.aK.restrict (c.V Wl).subtype) M.pw M.bcw
  obtain ⟨w₂, -, -, -, n₂⟩ := (GlobalTheory.ArcQBC.baseChanges h1 h2 hU h5 E H Dw l Xo c _ _ d.Y K₁ Dv.Tv.Fr _ (d.a.restrict (c.V d.Wp).subtype) _
    Dv.io.injective _ bcK.1).2 (M.aK.restrict (c.V d.Wp).subtype) M.pK bcK
  obtain ⟨W₁, hW₁⟩ := w₁ χw Ww
  obtain ⟨W₂, hW₂⟩ := w₂ d.χ d.W
  have nz : ThNZ d.th := by
    obtain ⟨_, _, _, _, h, -⟩ := d.isArc3
    exact (GlobalTheory.ThetaOverField.exists_ne_zero_iff _ _).1 h
  have hj : Mono Yw.j := GlobalTheory.ThetaShiftProofs.mono_j Yw (mono_spMap_subtype _)
  have hj' : Mono d.Y.j := GlobalTheory.ThetaShiftProofs.mono_j d.Y (mono_spMap_subtype _)

  obtain ⟨y₁, hy₁⟩ := frbc _ _ ψ y₀
  have a₁ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ Yw _ _ _ χw Ww _ _ M.thw_nz _ _ y₀ hy₀).2 hj _ ψ y₁ hy₁
  have a₂ : IsArcFr W₁ e₁ th₁ (arcι Dw Dv.Tv.Fr) y₁ :=
    GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ Yw _ _ M.aw χw Ww _ _ (M.aK.restrict (c.V Wl).subtype) _ M.pw W₁ hj M.bcw hW₁ _ _ _ _ l₁ t₁ _ _ y₁ (hψι ▸ a₁)
  obtain ⟨y₂, hy₂⟩ := (exu _ (fun τ => (M.g τ).map κ) (κ M.γ) y₁).1
    (fun τ => by
      have := (Matrix.isUnit_det_of_left_inverse (hNg τ)).map κ
      rwa [RingHom.map_det] at this) ((Ne.isUnit ‹M.γ ≠ 0›).map κ)
  have a₃ : IsArcFr W₁ e₂ th₂ (arcι Dw Dv.Tv.Fr) y₂ :=
    GlobalTheory.ArcQ.isArcFr_of_frChg_const h1 h2 E H Dw l Xo c _ _ Yw _ _ _ _ W₁ e₁ e₂ th₁ th₂ M.g M.γ (n₁ _ _ t₁ M.thw_nz) l₃ t₃ _ _ y₁ y₂ hj a₂ hy₂

  obtain ⟨x₀, hx₀, hxF⟩ := hN
  obtain ⟨x₁, hx₁⟩ := frbc _ _ φ x₀
  have b₁ := (GlobalTheory.ArcQ.isArcFr_unique_baseChange h1 h2 E H Dw l Xo c _ _ d.Y _ _ _ d.χ d.W _ _ nz _ _ x₀ hx₀).2 hj' _ φ x₁ hx₁
  have b₂ : IsArcFr W₂ e₂ th₂ (arcι Dw Dv.Tv.Fr) x₁ :=
    GlobalTheory.ArcQ.isArcFr_witBC h1 h2 E H Dw l Xo c _ _ d.Y _ _ (d.a.restrict (c.V d.Wp).subtype) d.χ d.W _ _
      (M.aK.restrict (c.V d.Wp).subtype) _ M.pK W₂ hj' bcK hW₂ _ _ _ _ l₂ t₂ _ _ x₁ (hφι ▸ b₁)

  have hC : ∀ {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R'),
      spMap (PowerSeries.map f) ≫ spMap (PowerSeries.C (R := R)) = spMap (PowerSeries.C (R := R')) ≫ spMap f :=
    fun f => by
      rw [← spMap_comp, ← spMap_comp]
      exact congrArg spMap (RingHom.ext fun x => PowerSeries.map_C _ _)
  obtain rfl : y₂ = x₁ := GlobalTheory.T.arc_framed_point_eq_of_models_over_base h1 h2 h5 E H Dw l Xo c _ _ M.aK _ _ Yw d.Y _ _ W₁ W₂
    (by rw [Category.assoc, hχ, ← Category.assoc, hC, Category.assoc, ← spMap_comp, ← M.bcw.1])
    (by rw [Category.assoc, hd, ← Category.assoc, hC, Category.assoc, ← spMap_comp, RingHom.comp_assoc])
    e₂ th₂ (n₂ _ _ t₂ nz) _ _ y₂ x₁ (isUnit_arcι_X Dw _) a₃ b₂

  obtain ⟨z₁, hz₁⟩ := frbc _ _ φ d.yF
  obtain ⟨z₂, hz₂⟩ := frbc _ _ ψ Dv.yR
  have c₁ := ((calcu _).1 _ _ _ _ _ _ _ hy₂).1 (((calcu _).2.2.1 _ φ _ _ _ _ _ _ hxF hx₁).1 hz₁)
  have c₂ := ((calcu _).2.2.1 _ ψ _ _ _ _ _ _ hyR hy₁).1 hz₂
  have eM : (fun τ => (letM Dw K₁ τ).map φ * (M.g τ).map κ) = fun τ => 1 * (letMR Dw Dv.Tv.V Dv.ϖ τ).map ψ :=
    funext fun τ => by
      rw [hψM, one_mul]
      refine (congrArg (· * (M.g τ).map κ) (hφX τ)).trans ?_
      change letM Dw Dv.Tv.Fr τ * (N τ).map κ * (M.g τ).map κ = _
      rw [mul_assoc, ← Matrix.map_mul, hNg, Matrix.map_one _ (map_zero κ) (map_one κ), mul_one]
  have eS : φ (cst Dw ζ) * κ M.γ = κ (Dv.io ζ * M.γ) * ψ 1 := by
    rw [map_one, mul_one, map_mul]
    exact congrArg (· * κ M.γ) (hφc ζ)
  rw [eM, eS] at c₁
  have c₃ := ((calcu _).1 _ (fun _ => 1) _ _ _ _ _ c₂).2 c₁
  have hu := ((exu _ _ _ _).2.2.1 _ c₃).2
  refine ⟨φ, ψ, z₁, z₂, fun o => o.elim hu.unit fun _ => 1, fun f => ⟨_, fun _ => rfl, hφC f⟩, fun x => ?_,
    fun p => RingHom.congr_fun hψι p, hψX, arcι_C Dw _, fun _ => rfl, hz₁, hz₂,
    ((calcu _).2.2.2 _ _ _).2 ⟨fun _ => 1, fun τ i => Matrix.one_apply_eq i,
      fun τ i j h => Matrix.one_apply_ne h.ne, c₃⟩⟩
  refine (congrFun (congrFun (hφX x.1) x.2.1) x.2.2).trans ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => congrArg (_ * ·) (arcι_C Dw _)

end GlobalTheory.ArcRigidity
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsHolToCompClm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcPts

theorem isHolTo_comp_clm {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup V']
    [NormedSpace ℂ V'] {X : Scheme.{0}} {y : V → (Sp ℂ ⟶ X)} (hy : IsHolTo Set.univ y) (φ : V' →L[ℂ] V) :
    IsHolTo Set.univ (fun z => y (φ z)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hy U f
  exact ⟨h1.preimage φ.continuous, h2.comp φ.differentiable.differentiableOn fun _ hz => hz⟩

theorem nonempty_holArc : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (Γ : Germs) (Ψ : SpecPts C.Φ Γ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (bF.comp (IntermediateField.inclusion c.le).toRingHom) ty) (laA laM : D.La → Λ.A.La) (K : Cmp Fu Λ.A Ψ.yw Ψ.pi laA laM), C.Φ.Rational → (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → ∀ lin cst (T₁ : ℝ), (∀ w : ℂ, T₁ < w.im → IsFibAt Λ.A Xo.univ.t lin cst w (Ψ.yw w) (Ψ.pi w) (Ψ.fr w)) → Nonempty (HolArc Y bF a χ W Fu) := by
  intro hL hL2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C Γ Ψ g ty Fu laA laM K hrat hA hM lin cst T₁ hfib
  obtain ⟨hadd, honto, hlin⟩ := ex0_additive_surjective_equivariant hL hL2 E H D l c O β _ a Λ
  obtain ⟨hb, hchi⟩ := analyticDictionaryExp_holomorphic_over_unif E H D l c O β _ a Λ
  obtain ⟨hker, hiota, htor, -⟩ := GtKer.ker_iota_torus E H D l c O β _ a Λ
  have hfin : AnFin Λ.A := (ArcThetaSpaces.sections_theta hL hL2 E H D l c O β _ a Λ).2.1
  have hrie := gtAn_orth_ker_iff hL hL2 E H D l c O β _ a Λ
  have hpt := ArcPoint.point_sumsAt E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K
  have hdiff := GlobalTheory.T.exponentialFamily_deriv_sumsAt_period hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin hrat
  obtain ⟨T₂, hth⟩ := GlobalTheory.T.arc_levelOne_section_eq_kappa_theta hL hL2 E H D l Xo c O β Y bF a χ W Λ C Γ Ψ g ty Fu laA laM K hfin lin cst T₁ hfib
  have hrep := _root_.GlobalTheory.GtRep.exists_rep_and_shift hL hL2 E H D l c O β _ a Λ
  have hsm : ∀ (s : ℂ) (v : Λ.A.V), K.h.symm (s • K.h v) = s • v := fun s v => by
    rw [map_smul, K.h.symm_apply_apply]
  refine ⟨{
    i := K.i
    T := max K.T T₂
    P₀ := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.P0).comp K.gam.toAddEquiv.toAddMonoidHom
    N := (K.h.toLinearEquiv.toAddEquiv.toAddMonoidHom.comp Λ.A.N).comp K.gam.toAddEquiv.toAddMonoidHom
    Pw := K.Pw
    Pw_eq := fun w v => ?_
    y := Λ.ε.toLinearMap ∘ₗ Λ.A.yLin ∘ₗ K.gam.toLinearMap
    y_onto := Λ.ε.surjective.comp (Λ.A.yLin_surjective.comp K.gam.surjective)
    ex₀ := fun z => Λ.ex0 (K.h.symm z)
    period := fun w hw => K.period w (lt_of_le_of_lt (le_max_left _ _) hw)
    add := fun z z' => ?_
    onto := honto.comp K.h.symm.surjective
    lin := fun x z => ?_
    hol_b := isHolTo_comp_clm hb (K.h.symm : (Fin g → ℂ) →L[ℂ] Λ.A.V)
    hol_chi := fun x j => (hchi x j).1.comp K.h.symm.differentiable.differentiableOn fun _ hz => hz
    ker := fun z => ?_
    iota := fun v => ?_
    shift := fun w v => ?_
    levelA := fun v => ?_
    levelM := fun v hv => ?_
    riemann := fun v => ?_
    point := hpt
    diff := fun z₀ ν v V f h1 h2 h3 => hdiff z₀ ν v V f ⟨h1, h2, h3⟩
    theta := fun th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ h1 h2 h3 =>
      hth _ (le_max_right _ _) th σ fam bas S h τ c₁ c₂ w₂ w₁ w₀ ⟨h1, h2, h3⟩ }⟩
  · show K.Pw w v = K.h (Λ.A.P0 (K.gam v)) + w • K.h (Λ.A.N (K.gam v))
    rw [K.Pw_eq, AnArc.Pw_apply, map_add (f := _), map_smul]
  · rw [map_add (f := _)]; exact hadd _ _
  · have : K.h.symm (fun k => ty k (x : E) * z k) = Λ.A.actV x (K.h.symm z) := by
      apply K.h.injective
      funext k
      rw [K.h_act, K.h.apply_symm_apply, K.h.apply_symm_apply]
    rw [this]
    exact hlin x _
  · refine (hker _).trans ⟨?_, ?_⟩
    · rintro ⟨la, h0, hz⟩
      obtain ⟨v, rfl⟩ := K.gam.surjective la
      refine ⟨v, ?_, ?_⟩
      · show Λ.ε (K.gam v).y = 0
        rw [h0, map_zero]
      · show z = K.h (Λ.A.P0 (K.gam v))
        rw [← hz, K.h.apply_symm_apply]
    · rintro ⟨v, h0, hz⟩
      refine ⟨K.gam v, (map_eq_zero_iff _ Λ.ε.injective).1 h0, ?_⟩
      rw [hz]
      exact K.h.symm_apply_apply _
  · show Out.GtPtF.IsIota (Λ.ε (K.gam v).y) (Λ.ex0 (K.h.symm (K.h (Λ.A.P0 (K.gam v)))))
    rw [K.h.symm_apply_apply]
    exact hiota _
  · show IsTorusPt (Λ.ex0 (K.h.symm (w • K.h (Λ.A.N (K.gam v))))) (fun x => eTwoPi (w * a.be (Λ.ε (K.gam v).y) x))
    have h1 : w • Λ.A.N (K.gam v) = ((w • Λ.A.N (K.gam v)).1, 0) := Prod.ext rfl (by simp [AnArc.N])
    rw [hsm, h1]
    convert htor (w • Λ.A.N (K.gam v)).1 using 3 with x
    show _ = w * ((Λ.A.be (K.gam v).y (Λ.ε.symm x) : ℤ) : ℂ)
    rw [Λ.be_eq, Λ.ε.apply_symm_apply]
  · obtain ⟨e, he⟩ := K.levA v
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.A l.A_pos).2 _ _ e (hA v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · obtain ⟨e, he⟩ := K.levM v hv
    obtain ⟨q, h1, h2, h3⟩ := (hrep l.M (le_trans (by norm_num) l.three_le)).2 _ _ e (hM v)
    rw [← he] at h1 h2
    exact ⟨q, h1, h2.trans (congrArg Λ.ex0 (hsm _ _).symm), h3⟩
  · show (∀ v', Λ.ε (K.gam v').y = 0 → (Fu.Di K.i).EF v v' = 0) ↔ (Λ.ε (K.gam v).y = 0 ∧ ∀ s : ℂ, ∃ x,
      IsTorusPt (Λ.ex0 (K.h.symm (s • K.h (Λ.A.P0 (K.gam v))))) x ∧
        ∀ v', x (Λ.ε (K.gam v').y) = eTwoPi (-(s * (Fu.Di K.i).EF v v')))
    simp only [hsm, ← K.EF_eq]
    have := hrie (K.gam v)
    simp only [K.gam.surjective.forall] at this
    exact this

end GlobalTheory.ArcPts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointExpEqOfIsometry
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.ArcCM

theorem isHolTo_comp_univ {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {B : Set W} {y : W → (Sp ℂ ⟶ X)} (hy : IsHolTo B y) {φ : V → W}
    (hφ : Differentiable ℂ φ) (hB : ∀ z, φ z ∈ B) : IsHolTo Set.univ (fun z => y (φ z)) := by
  unfold IsHolTo at hy ⊢
  intro U f
  obtain ⟨ho, hd⟩ := hy U f
  have hset : {b | b ∈ (Set.univ : Set V) ∧ ⊤ ≤ (fun z => y (φ z)) b ⁻¹ᵁ U} =
      φ ⁻¹' {b | b ∈ B ∧ ⊤ ≤ y b ⁻¹ᵁ U} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ, true_and, hB b]
  rw [hset]
  exact ⟨ho.preimage hφ.continuous, hd.comp hφ.differentiableOn (fun b hb => hb)⟩

theorem isHolTo_exp_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ (fun z => (Fu.ex i P z).left) := by

  have hper : IsHolPeriods (Fu.Di i) ty (Set.univ : Set (Fin 0 → ℂ)) (fun _ => P) :=
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩
  have hjoint : IsHolTo ((Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)))
      (fun bz : (Fin 0 → ℂ) × (Fin g → ℂ) => (Fu.ex i P bz.2).left) :=
    (Fu.21 i 0 Set.univ (fun _ => P) isOpen_univ hper).2
  have hφ : Differentiable ℂ (fun z : Fin g → ℂ => ((0 : Fin 0 → ℂ), z)) :=
    (differentiable_const _).prodMk differentiable_id
  have hmem : ∀ z : Fin g → ℂ, ((0 : Fin 0 → ℂ), z) ∈ (Set.univ : Set (Fin 0 → ℂ)) ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
    fun z => Set.mk_mem_prod (Set.mem_univ _) (Set.mem_univ _)
  have hcomp := isHolTo_comp_univ hjoint hφ hmem
  exact hcomp

theorem point_exp_eq_of_isometry : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i').La) (L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → (∀ u v, (Fu.Di i').EF (gm u) (gm v) = (Fu.Di i).EF u v) → (∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gm (Fu.t i v) = Fu.t i' v + l.M • e) → (∀ u, P' (gm u) = L (P u)) → Fu.u i P = Fu.u i' P' ∧ ∀ z, (Fu.ex i' P' (L z)).left = (Fu.ex i P z).left := by
  intro hK E _ _ _ H D l Xo σ g ty Fu i i' P P' gm L hpq hρ hty hA hP hP' hiso hmark hPL

  have hpt : Fu.u i P = Fu.u i' P' := by
    refine (GlobalTheory.UnifPoint.point_eq_iff_isometry_closed hK.theta hK.laws E H D l Xo σ g ty hpq hρ hty
      (Fu.Di i) (Fu.Di i') (Fu.t i) (Fu.t i') P P' (Fu.u i P) (Fu.u i' P') (Fu.ex i P) (Fu.ex i' P')
      ⟨Fu.over_σ i P hP, hP, ⟨Fu.ex_add i P hP, Fu.ex_onto i P hP, isHolTo_exp_of_isPeriod Fu i P hP,
        (Fu.22 i P hP).1, (Fu.22 i P hP).2⟩, Fu.ex_ker i P hP, Fu.ex_lin i P hP, Fu.ex_weil i P hP,
        Fu.ex_eta i P hP, Fu.ex_etaA i P hP⟩
      ⟨Fu.over_σ i' P' hP', hP', ⟨Fu.ex_add i' P' hP', Fu.ex_onto i' P' hP', isHolTo_exp_of_isPeriod Fu i' P' hP',
        (Fu.22 i' P' hP').1, (Fu.22 i' P' hP').2⟩, Fu.ex_ker i' P' hP', Fu.ex_lin i' P' hP', Fu.ex_weil i' P' hP',
        Fu.ex_eta i' P' hP', Fu.ex_etaA i' P' hP'⟩).2 ?_

    exact ⟨gm, L, hiso, hmark, fun a => ⟨gm (Fu.t i a) - Fu.t i' a, by rw [hA, one_smul]; abel⟩, hPL⟩

  have hii : i = i' := Fu.disj i i' P P' hP hP' hpt
  subst hii

  letI := H.starRing
  have hex := GlobalTheory.ArcPts.exp_eq_of_matching_markings E H D l Xo σ g ty Fu i P P' gm L rfl hP hP' hiso hmark
    (fun v => ⟨gm (Fu.t i v) - Fu.t i v, by rw [hA, one_smul]; abel⟩) hPL
  exact ⟨hpt, hex.2⟩

end GlobalTheory.ArcCM
end

