module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridgeAlt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DegreeInfimum.PlaceDegreeSums
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0047
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.MemOfEqMulInvPow
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsConstantEigenbasisTangentArc
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsLiftOpen
section
noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Units

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem arcιR_isUnit_mul (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) :
    IsUnit (arcιR Dw V ϖ (PowerSeries.C ϖ * PowerSeries.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  exact isUnit_of_mul_isUnit_left h

theorem letMR_det_isUnit (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    IsUnit (letMR Dw V ϖ τ).det := by
  classical
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  have h2 := isUnit_of_mul_isUnit_right h
  have h3 := isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))
    (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Finset.mem_univ τ))) h2
  rw [RingHom.map_det] at h3
  exact h3

theorem arcιR_C_isUnit (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) : IsUnit (arcιR Dw V ϖ (PowerSeries.C v)) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ
  have h := arcιR_isUnit_mul Dw V ϖ
  rw [map_mul (arcιR Dw V ϖ)] at h
  rw [map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ),
    map_pow (arcιR Dw V ϖ)]
  exact ((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)

end Units

theorem exists_lift_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {S : Type} [CommRing S] (g : c.F →+* S) (χ : Sp S ⟶ Y.X) (hcond : χ ≫ Y.s = spMap g ≫ spMap β)
    (hj : ∀ q : Sp S, χ q ∈ Set.range Y.j) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = χ ∧ z ≫ pullback.snd _ _ = spMap g := by
  let p : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift χ (spMap g) hcond
  have hr : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨w, hw⟩ := hj q
    rw [← hw]
    have h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨w, rfl⟩
    simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using h2
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

theorem exists_dvr_frPt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Tv : CDVR) (ϖ : Tv.V) (f : c.F →+* Tv.Fr) (b : O →+* Tv.V) (a : ArcIn Dw l β Tv.V b) (χ : Sp (PowerSeries Tv.V) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR Tv.V)) (th : a.D₀.P.L.Sec), Irreducible ϖ → f.comp β = (algebraMap Tv.V Tv.Fr).comp b → (∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = f (embK c τ x)) → χ ≫ Y.s = spMap (PowerSeries.C (R := Tv.V)) ≫ spMap b → (∀ x : Sp (PowerSeries Tv.V), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → ∃ (_ : Algebra c.F (ArcSR Dw Tv.V ϖ)), (∀ (x : c.F) (v : Tv.V) (n : ℕ), f x * algebraMap Tv.V Tv.Fr ϖ ^ n = algebraMap Tv.V Tv.Fr v → algebraMap c.F (ArcSR Dw Tv.V ϖ) x * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ) ^ n = arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) v)) ∧ ∃ y₀ yR : FrPt Xo c (ArcSR Dw Tv.V ϖ), IsArcFr W e th (arcιR Dw Tv.V ϖ) y₀ ∧ FrChg (letMR Dw Tv.V ϖ) 1 y₀ yR := by
  intro L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth
  let ι := arcιR Dw Tv.V ϖ
  let κ : Tv.V →+* ArcSR Dw Tv.V ϖ := ι.comp (PowerSeries.C (R := Tv.V))
  have hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y) := fun y =>
    arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)
  let g : Tv.Fr →+* ArcSR Dw Tv.V ϖ := IsLocalization.lift hκ
  have hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v := fun v => IsLocalization.lift_eq hκ v
  letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra
  have halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x) := fun _ => rfl
  refine ⟨alg, ?_, ?_⟩
  · intro x v n h
    have h2 := congrArg g h
    rw [map_mul, map_pow, hg, hg] at h2
    exact h2
  · have hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R := Tv.V)).comp b) := by
      ext1 x
      have h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x) := RingHom.congr_fun hfb x
      show g (f (β x)) = κ (b x)
      rw [h1, hg]
    have hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β := by
      rw [Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
    obtain ⟨z, hz1, hz2⟩ := exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by
      intro q
      rw [Scheme.Hom.comp_apply]
      refine hj _ fun h => ?_
      have h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal := h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))
    have hflat := (GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1
    obtain ⟨y₀, -, hy₀⟩ := exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush)
      (ArcSR Dw Tv.V ϖ) ι z hflat hz1
      (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl)
      (fun τ x => by rw [halg, ← hρ, hg]; rfl)
    obtain ⟨yR, hyR⟩ := (frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1
      (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one
    exact ⟨y₀, yR, hy₀, hyR⟩

end GlobalTheory.ArcQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsTauCanonicalTrivialisationIffNormalisedArc
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

namespace GlobalTheory.KappaAn

theorem exists_ev {Y : Scheme.{0}} (j : Sp ℂ ⟶ Y) :
    ∃ e : (Y.presheaf.stalk (j (IsLocalRing.closedPoint ℂ)))ˣ →* ℂ, ∀ (X : Scheme.{0}) (r : Y ⟶ X) (U : X.Opens),
      r (j (IsLocalRing.closedPoint ℂ)) ∈ U → ∀ a : Γ(X, U)ˣ,
        e (gm r (j (IsLocalRing.closedPoint ℂ)) U a) = valAt' (j ≫ r) U a.val := by
  refine ⟨(Scheme.stalkClosedPointTo j).hom.toMonoidHom.comp (Units.coeHom _), fun X r U h a => ?_⟩
  have h' : ⊤ ≤ j ⁻¹ᵁ (r ⁻¹ᵁ U) := (top_le_preimage_iff_mem j _).2 h
  rw [← GlobalTheory.valAt'_comp, valAt'_eq_valAt j h']
  change (Scheme.stalkClosedPointTo j).hom (gm r _ U a).val = _
  rw [gm_val r _ U h]
  have := Scheme.germ_stalkClosedPointTo j (r ⁻¹ᵁ U) h
  exact congrArg (fun q => q.hom ((r.app U).hom a.val)) this

variable {O : Type} [CommRing O] [StarRing O] [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ]
  {D₀ : Out.DegPre ℂ} [Module O D₀.X] {oa : D₀.OAct O} (d : GtDict D₀ oa)

theorem pow_eq_one_iff (n : ℕ) (y : d.A.X) : D₀.c (d.eX y) ^ n = 1 ↔ n • d.A.ct y ∈ d.A.abelian₂ := by
  have h : ∀ k : ℕ, d.u.ex (k • d.A.ct y) = D₀.c (d.eX y) ^ k := fun k => by
    induction k with
    | zero => rw [zero_nsmul, pow_zero]; exact (d.u.ker 0).2 (zero_mem _)
    | succ k ih => rw [succ_nsmul, d.u.ex_add, ih, d.ex_ct, pow_succ]
  rw [← h, d.u.ker, d.lam_eq]


omit [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] in
theorem ah_ratio (A : AnArc O) (l m : A.abelian₂) :
    A.ah (l + m) 0 = A.ah l 0 * A.ah m 0 * Complex.exp (Real.pi * A.H l m) := by
  have h1 := A.H_conj l m
  have h2 : A.H m l = (A.H l m).re - (A.H l m).im * Complex.I := by
    rw [← h1]; apply Complex.ext <;> simp
  have h3 := Complex.re_add_im (A.H l m)
  simp only [AnArc.ah, AnArc.H_zero_left, mul_zero, zero_add, A.chi_add, ← A.H_def, Submodule.coe_add,
    A.H_add_left, A.H_add_right]
  have : Complex.exp (Real.pi * Complex.I * ((A.H l m).im : ℂ)) *
      Complex.exp (Real.pi / 2 * (A.H l l + A.H l m + (A.H m l + A.H m m))) =
      Complex.exp (Real.pi / 2 * A.H l l) * Complex.exp (Real.pi / 2 * A.H m m) *
        Complex.exp (Real.pi * A.H l m) := by
    simp only [← Complex.exp_add]
    congr 1
    rw [h2]
    linear_combination (Real.pi / 2 : ℂ) * h3
  linear_combination A.chi l * A.chi m * this

theorem kappa_eq {n : ℕ} (hc : ∀ y, D₀.c y ^ n = 1) (y y' : d.A.X) :
    algebraMap (FractionRing ℂ) ℂ (TauTwist.kappa hc (d.eX y) (d.eX y')) =
      eTwoPi (d.A.T (n • y) (n • y')) * Complex.exp (Real.pi * d.A.H (n • d.A.ct y) (n • d.A.ct y')) := by
  let p : (Out.TK ℂ).left := Out.jFK (R := ℂ) ℂ (IsLocalRing.closedPoint ℂ)
  obtain ⟨e, he⟩ : ∃ e : ((Out.TK ℂ).left.presheaf.stalk p)ˣ →* ℂ, ∀ (X : Scheme.{0}) (r : (Out.TK ℂ).left ⟶ X)
      (U : X.Opens), r p ∈ U → ∀ a : Γ(X, U)ˣ, e (gm r p U a) = valAt' (Out.jFK (R := ℂ) ℂ ≫ r) U a.val :=
    exists_ev (Y := (Out.TK ℂ).left) (Out.jFK (R := ℂ) ℂ)
  choose J hJ using fun q : (Out.TK ℂ).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (q p)
  have hG : Good D₀.P.L p J := hJ
  let z₀ : (Out.TK ℂ).left ⟶ D₀.P.A.left := (toUnit (Out.TK ℂ)).left ≫ eSec D₀.P.A
  have hz : Out.jFK (R := ℂ) ℂ ≫ (toUnit (Out.TK ℂ)).left = 𝟙 (Sp ℂ) := jFK_comp_jK_complex
  have h0 : ⊤ ≤ (d.u.ex 0).left ⁻¹ᵁ D₀.P.L.U (J z₀) := by
    have : (d.u.ex 0).left = Out.jFK (R := ℂ) ℂ ≫ z₀ := by
      rw [d.ex_zero, ← Category.assoc, hz]; exact (Category.id_comp _).symm
    rw [this]
    exact (top_le_preimage_iff_mem _ _).2 (hJ z₀)
  have f0 := d.u.fr_ne _ _ h0
  have hψ : ∀ (x : d.A.X) (l : d.A.abelian₂), d.A.ct x = l →
      e (val (D₀.psi (d.eX x)) (𝟙 _) p J) = d.A.psi x * d.A.ah l 0 * (d.u.fr (J z₀) 0)⁻¹ := fun x l hl => by
    have h1 : D₀.c (d.eX x) = η[D₀.P.A] := by
      rw [← d.ex_ct, hl, ← d.ex_zero, ← d.ex_add_lam 0 l, zero_add]
    have h2 : Out.ptK (D₀.c (d.eX x)) = z₀ := by rw [h1]; rfl
    have h3 : ⊤ ≤ (d.u.ex (d.A.ct x)).left ⁻¹ᵁ D₀.P.L.U (J z₀) := by rw [d.ex_ct, h1, ← d.ex_zero]; exact h0
    rw [val_of _ _ _ _ (fun _ => J z₀) (fun _ => by rw [Category.id_comp, h2])]
    have hm : (𝟙 (Out.TK ℂ).left : _ ⟶ _) p ∈
        LB.wchart D₀.P.L (fun _ : PUnit => Out.ptK (D₀.c (d.eX x))) fun _ => J z₀ := by
      rw [h2]; exact Set.mem_iInter.2 fun _ => hJ z₀
    refine (he _ _ _ hm _).trans ?_
    rw [Category.comp_id]
    refine (d.psi_val x (fun _ => J z₀) h3).trans ?_
    have h4 := d.fr_eq_ah_mul l (J z₀) 0 h0
    have h5 := d.A.ah_ne_zero l 0
    have h6 := d.u.fr_ne _ _ h3
    rw [zero_add] at h4
    rw [hl] at h6 ⊢
    rw [h4]
    field_simp
  have hρ : e (val D₀.rigK (𝟙 _) p J) = d.u.fr (J z₀) 0 := by
    have h1 : ⊤ ≤ (D₀.P.L.pull (eSec D₀.P.A)).U fun _ => J z₀ := by
      have := (top_le_wchart_iff D₀.P.L (fun _ : PUnit => eSec D₀.P.A) (fun _ => J z₀) (𝟙 (Sp ℂ))).2 fun _ => by
        rw [d.ex_zero] at h0
        exact (Category.id_comp (eSec D₀.P.A)).symm ▸ h0
      exact this
    rw [Out.DegPre.rigK, val_pull hG, val_of _ _ _ _ (fun _ => J z₀) (fun _ => by rw [Category.id_comp])]
    refine (he _ _ _ (h1 trivial) _).trans ?_
    rw [Category.id_comp, hz]
    exact (d.isRig _ h1).symm
  have hk := congrArg e ((TauTwist.unitAt_kappa hc (d.eX y) (d.eX y') hG).trans (TauTwist.val_tau D₀ _ _ _ hG))
  have hl : ∀ x, d.A.ct (n • x) ∈ d.A.abelian₂ := fun x => by
    rw [map_nsmul]; exact (pow_eq_one_iff d n x).1 (hc _)
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, ← map_nsmul, ← map_nsmul, ← map_add (f := _), hρ,
    hψ (n • y) ⟨_, hl y⟩ rfl, hψ (n • y') ⟨_, hl y'⟩ rfl,
    hψ (n • y + n • y') (⟨_, hl y⟩ + ⟨_, hl y'⟩) (map_add _ _ _), ah_ratio, d.A.psi_add] at hk
  have hu : e (TauTwist.unitAt (𝟙 (Out.TK ℂ).left) p (TauTwist.kappa hc (d.eX y) (d.eX y'))) =
      algebraMap (FractionRing ℂ) ℂ (TauTwist.kappa hc (d.eX y) (d.eX y')) := by
    generalize TauTwist.kappa hc (d.eX y) (d.eX y') = t
    refine (he _ _ ⊤ trivial _).trans ?_
    have := GlobalTheory.valAt'_comp (𝟙 (Sp ℂ)) (Out.jFK (R := ℂ) ℂ) ⊤ (unitOn t).val
    rw [Category.id_comp] at this
    rw [Category.comp_id]
    refine this.symm.trans ?_
    exact (congrArg (valAt' (𝟙 (Sp ℂ)) ⊤) (congrArg (fun e => e.hom t.val)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing ℂ) ℂ)))).symm).trans
      (valAt'_id_top _)
  rw [← hu, hk, ← map_nsmul, ← map_nsmul]
  have := (d.A.psi (n • y)).ne_zero
  have := (d.A.psi (n • y')).ne_zero
  have := d.A.ah_ne_zero ⟨_, hl y⟩ 0
  have := d.A.ah_ne_zero ⟨_, hl y'⟩ 0
  field_simp

theorem tauCan_iff (n : ℕ) : TauCan D₀ n ↔
    (∀ y, n • d.A.ct y ∈ d.A.abelian₂) ∧
      ∀ y y', eTwoPi (d.A.T (n • y) (n • y')) * Complex.exp (Real.pi * d.A.H (n • d.A.ct y) (n • d.A.ct y')) = 1 := by
  constructor
  · rintro ⟨hc, hk⟩
    refine ⟨fun y => (pow_eq_one_iff d n y).1 (hc _), fun y y' => ?_⟩
    rw [← kappa_eq d hc, hk]
    exact map_one _
  · rintro ⟨h₁, h₂⟩
    have hc : ∀ y, D₀.c y ^ n = 1 := fun y => by
      obtain ⟨y, rfl⟩ := d.eX.surjective y
      exact (pow_eq_one_iff d n y).2 (h₁ y)
    refine ⟨hc, fun y y' => ?_⟩
    obtain ⟨y, rfl⟩ := d.eX.surjective y
    obtain ⟨y', rfl⟩ := d.eX.surjective y'
    exact Units.ext ((algebraMap (FractionRing ℂ) ℂ).injective (((kappa_eq d hc y y').trans (h₂ y y')).trans
      (map_one _).symm))

end GlobalTheory.KappaAn

theorem GlobalTheory.KappaAn.tauCan_iff_normAn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (O : Type) [CommRing O] (β : O →+* c.F) (b : O →+* ℂ) (a : ArcIn Dw l β ℂ b) (Λ : GtAn₀ a) (n : ℕ), letI := H.starRing; (TauCan a.D₀ n ↔ NormAn Λ.A n) := by
  intro E _ _ _ H Dw l c _ _ O _ β b a Λ n
  exact @GlobalTheory.KappaAn.tauCan_iff (𝓞 E) _ H.starRing _ _ a.D₀ a.mod a.oa Λ.toGtDict n
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem ndeg_eq_places {K : Type} [Field K] [NumberField K] (N : MLine K) (hN : N.Good)
    (hc : ∀ σ : K →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) :
    ((∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) -
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding)) / (Module.finrank ℚ K : ℝ) = N.ndeg := by
  have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) =
      -Real.log ((FractionalIdeal.absNorm N.I : ℚ) : ℝ) := by
    simp_rw [neg_mul]
    rw [finsum_neg_distrib, PlaceDegreeSums.sum_count_log_norm _ hN.1]
  have h2 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding) =
      ∑ τ : K →+* ℂ, Real.log (N.n τ) := by
    rw [PlaceDegreeSums.sum_infinite_places_mult (fun σ => Real.log (N.n σ.embedding))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]
    · rw [h]
      exact congrArg Real.log (hc τ)
  rw [h1, h2, MLine.ndeg, MLine.deg]

theorem qbridge_of_numGood : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ch Ah Cc Ac Tt cc : ℝ) (be : HeightOneSpectrum (𝓞 B.KO) → ℝ) (Carch Bdeg : ℝ), Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) → WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg + Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ F : B.Cusp j ka, F ∉ WeightFamilies.MggK B CR Tt cc j ka → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁) (φ : B.Cusp j ka →ₗ[B.KO] K₁), WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧ φ F ≠ 0 ∧ NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ) → QBridgeAt large₂ B j ka CR Ch Ah Cc Ac Tt cc := by
  intro D large₂ B j ka CR Ch Ah Cc Ac Tt cc be Carch Bdeg hlat hbe hbefin hbesum hconj hroom hdet
  classical
  obtain ⟨K₁, _, _, _, ρ, g, cf, hfam, hcf, hker, hdim⟩ := kerCore_holds B.KO (B.Cusp j ka)
    (WeightFamilies.MggK B CR Tt cc j ka)
    (fun K₁ _ _ _ φ => WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧
      NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ)
    (fun _ _ _ _ _ h => h.1)
    (fun v hv => by
      by_contra hn
      obtain ⟨K₁, _, _, _, φ, h1, h2, h3⟩ := hdet v hn
      exact h2 (hv K₁ φ ⟨h1, h3⟩))
    (fun K' K₁ _ _ _ _ _ _ e f hf => ⟨e.toLinearMap.comp f, ⟨fun v hv => by
      have := LinearMap.mem_ker.1 (hf.1 hv)
      simp [LinearMap.mem_ker, this], _root_.GlobalTheory.ArcCM.numGood_comp _ _ _ _ _ _ _ K' K₁ e f hf.2⟩, fun _ => rfl⟩)
  let _ := hlat
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg (Submodule.IsFullLattice.span_eq_top (A := B.KO) (M := B.Mlat j ka)) (WeightFamilies.MggK B CR Tt cc j ka)
  have hρ : ρ = WeightFamilies.rhoP B CR Tt cc j ka := by omega
  subst hρ
  choose N hG hd hc hint harch using fun i => (hfam i).2
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, cf, be,
    fun i w => -(FractionalIdeal.count K₁ w (N i).I : ℝ), fun i σ => Real.log ((N i).n σ.embedding), Carch, Bdeg,
    hker, hbe, hbefin, hbesum, fun i => ?_, fun la w hw i F hF hne => ?_, hconj, fun σ i F hF hne => ?_,
    fun i => ?_, hroom⟩
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (N i).I)).subset fun w hw h => hw ?_
    simp [h]
  · rw [hcf] at hne ⊢
    exact (hint i la w hw F hF hne).trans_eq (sub_eq_add_neg _ _)
  · rw [hcf] at hne ⊢
    rw [← InfinitePlace.norm_embedding_eq]
    exact harch i σ.embedding F hF hne
  · rw [ndeg_eq_places (N i) (hG i) (hc i)]
    exact hd i

end GlobalTheory.ArcCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecEqOfSecBCIdOne
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open MonoidalCategory CartesianMonoidalCategory

namespace GlobalTheory.ArcDatumExists

theorem isUnit_det_letM {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H)
    (K : Type) [Field K] (τ : E →+* ℂ) : IsUnit (letM Dw K τ).det := by
  have h1 : IsUnit (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K) (arcDet Dw K)) :=
    IsLocalization.Away.algebraMap_isUnit _
  have h2 : Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K))) ∣ arcDet Dw K :=
    Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (LaurentSeries K)))) (Finset.mem_univ τ)
  have h3 := isUnit_of_dvd_unit
    (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) h2) h1
  rw [RingHom.map_det] at h3
  exact h3

theorem flat_of_field {K S : Type} [Field K] [CommRing S] (f : K →+* S) : f.Flat := by
  let _ := f.toAlgebra
  exact (inferInstance : Module.Flat K S)

theorem appLE_id_apply {X : Scheme.{0}} (U : X.Opens) (h : U ≤ 𝟙 X ⁻¹ᵁ U) (r : Γ(X, U)) :
    (Scheme.Hom.appLE (𝟙 X) U U h).hom r = r :=
  GlobalTheory.Frames.ChgOf.appLE_id' U h r

theorem sec_eq_of_secBC_id_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s' : LB.Sec (PPx x))
    (h : SecBC (RingHom.id S) 1 x x s s') (i : (PPx x).ι) : s'.f i = s.f i := by
  simpa only [GlobalTheory.Frames.ChgOf.scal_one', one_mul] using
    (GlobalTheory.Frames.ChgOf.secBC_id_iff x 1 s s').mp h i

theorem isArcPt3At_of_frChg {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
    {K₁ : Type} [Field K₁] [Algebra c.F K₁] {b : O →+* K₁} {a : ArcIn Dw l β K₁ b} {χ : Sp (PowerSeries K₁) ⟶ Y.X}
    {W : Wit Y a χ} {e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR K₁)} {th : a.D₀.P.L.Sec}
    [Algebra c.F (ArcS Dw K₁)] {y₀ yF : FrPt Xo c (ArcS Dw K₁)} (hth : ∃ j, th.f j ≠ 0)
    (hfr : IsArcFr W e th (arcι Dw K₁) y₀) (hchg : FrChg (letM Dw K₁) 1 y₀ yF) : IsArcPt3At Y a χ W yF th := by
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := yF
  obtain ⟨hx, hu, hs⟩ := hchg
  dsimp only at hx hu hs
  subst hx
  obtain ⟨z, t', m1, m2, φ, -, -, -, h0, hm, -, θ, w1, w2, σ', s1, θ2, hθ, r1, r2, i1, i2, ps, hg⟩ := hfr
  obtain ⟨σ, fam, θ', a1, a2, a3, a4⟩ := hθ
  refine ⟨σ, fam, θ', θ, hth, a1, a2, a3, a4, t', m1, m2, w1, w2, σ', s1, θ2, ⟨φ, h0, hm⟩, r1, r2, i1, i2, ps, ?_⟩
  intro g g1 g2 j h
  rw [hg g g1 g2 j h]
  exact congrArg _ (sec_eq_of_secBC_id_one _ _ _ hs _).symm

theorem exists_arcDatum : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K₁ : Type) [Field K₁] [Algebra c.F K₁] (Wp : ValuationSubring ℂ) (Y : Model Xo c (c.V Wp).subtype), Y.N4 → ∀ a : ArcIn Dw l (RingHom.id c.F) K₁ (algebraMap c.F K₁), ∃ (χ : Sp (PowerSeries K₁) ⟶ Y.X) (W : Wit Y (a.restrict (c.V Wp).subtype) χ), (∃ e, ArcLieBasis W e) ∧ ∀ e, ArcLieBasis W e → ∀ th : a.D₀.P.L.Sec, (∃ j, th.f j ≠ 0) → ∀ (μ : ArcLt Dw →₀ ℕ) (jj : ℤ), ∃ d : ArcDatum Xo c K₁, d.Wp = Wp ∧ HEq d.Y Y ∧ d.a = a ∧ HEq d.e e ∧ HEq d.th th ∧ d.μ = μ ∧ d.jj = jj ∧ d.OverBase ∧ d.Normal 1 := by
  intro hL hL2 E _ _ _ H Dw l Xo c K₁ _ _ Wp Y hN4 a
  have : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap c.F K₁).injective
  obtain ⟨χ, hχ, -⟩ := hN4 K₁ ((algebraMap c.F K₁).comp (c.V Wp).subtype) 1
    (a.restrict (c.V Wp).subtype) (Or.inl ⟨Field.toIsField K₁, rfl⟩)
  obtain ⟨hs, -, hj, hW⟩ := (hχ χ).1 rfl
  obtain ⟨W⟩ := (Y.hasArcData_iff _ _ _ _ χ).1 hW
  refine ⟨χ, W, ?_, fun e he th hth μ jj => ?_⟩
  · obtain ⟨e, -, he⟩ := GlobalTheory.ConstBasis.exists_arcBasis hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ))
      ((algebraMap K₁ (FractionRing K₁)).comp (algebraMap c.F K₁)) rfl (fun _ _ => rfl)
      (GlobalTheory.JointModelGuards.exists_root_and_zeta l c Wp)
    exact ⟨e, he⟩
  · have hcomp : (algebraMap c.F (ArcS Dw K₁)).comp (c.V Wp).subtype =
        (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp ((algebraMap c.F K₁).comp (c.V Wp).subtype)) := by
      ext r
      simp only [RingHom.comp_apply]
      exact arcS_pin Dw K₁ ((c.V Wp).subtype r)
    obtain ⟨z, hz1, hz2⟩ := arcPt_point (Dw := Dw) Y ((algebraMap c.F K₁).comp (c.V Wp).subtype)
      hcomp χ hs (fun x hx => hj x (by rwa [map_one, one_mul]))
    have hnz : ThNZ th := (GlobalTheory.ThetaOverField.nonzero_generates hL hL2 K₁ a.D₀ th).1.1 hth
    have hflat : ((arcι Dw K₁).comp (PowerSeries.C (R := K₁))).Flat := flat_of_field _
    have hz3 : z ≫ pullback.fst _ _ ≫ Xo.s = sOf c (ArcS Dw K₁) := by
      rw [Y.jQ_over] at hz2
      rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]
      rfl
    obtain ⟨y₀, -, hy₀⟩ := GlobalTheory.ArcQ.exists_isArcFr hL hL2 E H Dw l Xo c _ _ Y K₁ _ (a.restrict (c.V Wp).subtype) χ W
      (fun τ => (algebraMap c.F K₁).comp (embK c τ)) e th he hnz (Or.inl (Field.toIsField K₁))
      (ArcS Dw K₁) (arcι Dw K₁) z hflat hz1 hz3 (fun τ x => arcS_pin Dw K₁ (embK c τ x))
    obtain ⟨yF, hyF⟩ := (GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c (ArcS Dw K₁) (letM Dw K₁) 1 y₀).1
      (isUnit_det_letM Dw K₁) isUnit_one
    have h12 := hy₀.isFramedPoint_changed_by_letters hyF hs
    have h3 := isArcPt3At_of_frChg (W := W) (e := e) hth hy₀ hyF
    refine ⟨⟨Wp, Y, a, χ, W, e, yF, th, h12, h3, μ, jj⟩, rfl, HEq.rfl, rfl, HEq.rfl, HEq.rfl, rfl, rfl, hs,
      y₀, hy₀, ?_⟩
    have h1 : GlobalTheory.ArcQ.cst Dw (1 : K₁) = 1 := by simp only [GlobalTheory.ArcQ.cst, map_one]
    rw [h1]
    exact hyF

end GlobalTheory.ArcDatumExists
end

