module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ThetaGeneratorPlaceValuationBoundStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0040
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtIntegralChartUniformisedModel
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

theorem GlobalTheory.PlaceInt.exists_ext_intChart_unif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y hT
  obtain ⟨T', io', y', e, hA, he, hU, φ, hv, hφ⟩ := GlobalTheory.T.exists_extension_all_models_uniformized E H Dw l Xo c T io y hT
  obtain ⟨iT, hiT⟩ : ∃ iT : T.Fr →+* T'.Fr,
      (letI := io.toAlgebra; letI := io'.toAlgebra; φ.toRingHom) = iT := ⟨_, rfl⟩
  have hio : io' = iT.comp io := by
    subst hiT
    letI := io.toAlgebra
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (φ.commutes a).symm
  have hv' : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a := by
    intro a
    by_cases ha : a = 0
    · subst ha
      simp [vV]
    · rw [← hiT]
      exact hv a ha
  subst hio
  obtain ⟨C', hC'⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists E H Dw l Xo c hstar T' (iT.comp io) y'
  exact ⟨T', iT, e, y', C', ⟨he, hv', φ, hiT, hφ⟩, hA, hC', hU C'.I⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeight
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PlaceTop

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

theorem vLa_int_mul_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (n : ℕ)
    (hs : a * (n : 𝓞 K) ≠ 0) :
    vLa la ((a * (n : 𝓞 K) : 𝓞 K) : K) = vLa la (a : K) + vLa la (n : K) := by
  have ha : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr (left_ne_zero_of_mul hs)
  have hn : (n : K) ≠ 0 := by
    have : n ≠ 0 := by
      rintro rfl
      exact hs (by simp)
    exact Nat.cast_ne_zero.2 this
  have e : ((a * (n : 𝓞 K) : 𝓞 K) : K) = (a : K) * (n : K) := by
    show algebraMap (𝓞 K) K _ = _
    rw [map_mul, map_natCast]
  rw [e, Crude.crv_vLa_mul la ha hn]

theorem thetaScalar_ne_zero {D : D7} (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) {j : ℕ}
    (w : WeightFamilies.Wt D j) : GlobalTheory.RunIn.sOf B hinj EX w ≠ 0 := by
  have hn : ∀ i, EX.piG i * piBarO EX i = (D.host.g i : 𝓞 D.host.E) := fun i => by
    apply Subtype.ext
    exact EX.piG_norm i
  have hn' : ∀ i, iE D hinj B (EX.piG i) * iE D hinj B (piBarO EX i) ≠ 0 := fun i => by
    rw [← map_mul, hn, map_natCast]
    exact Nat.cast_ne_zero.2 (D.host.g_prime i).ne_zero
  refine mul_ne_zero ?_ ?_
  · unfold nnW
    exact Finset.prod_ne_zero_iff.2 fun i _ =>
      mul_ne_zero (pow_ne_zero _ (left_ne_zero_of_mul (hn' i))) (pow_ne_zero _ (right_ne_zero_of_mul (hn' i)))
  · refine Nat.cast_ne_zero.2 ?_
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ D.host.hyp.1.ne_zero))
      (pow_ne_zero _ D.host.hyp.2.1.ne_zero)

theorem thInt_of_oriented (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (hO : Oriented T EX) (w : WeightFamilies.Wt D j) :
    GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w := by
  have hs := thetaScalar_ne_zero (recB h.toLawsCore) hinj EX w
  refine Pf.WWc_le_Mlat (recPJ h j hj) _ hs w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.th j w) := hG
  refine (Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la)) (fun g hg => ?_) _ hG').trans
    (recPJ_vAt_inc h j hj la y w G).ge
  refine le_trans (EReal.coe_le_coe_iff.2 ?_) (GlobalTheory.T.thetaGenerator_place_valuation_bound D T h j hj hinj EX hO w g hg la y)
  have h1 := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w _ _ le_rfl le_rfl
  have h2 := vLa_int_mul_natCast (K := T.Q.c.F) la (nnW (recB h.toLawsCore) hinj EX w) _ hs
  have h3 : ((vAdd la ((GlobalTheory.RunIn.sOf (recB h.toLawsCore) hinj EX w : 𝓞 (recB h.toLawsCore).KO) :
      (recB h.toLawsCore).KO) : ℤ) : ℝ) = _ := congrArg (fun z : ℤ => (z : ℝ)) h2
  rw [h3, Int.cast_add]
  exact neg_le_neg ((add_comm _ _).le.trans (add_le_add le_rfl h1))

end GlobalTheory.PlaceTop
end
end

