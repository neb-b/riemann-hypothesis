module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RuleValueIntegralOfSupLatticeValuesNonneg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

noncomputable section

namespace GlobalTheory.LamT

theorem mem_range_of_nval_nonneg {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] {e : ℕ} (he : 0 < e) {x : K'} (h : 0 ≤ Formalism.L2.Pj.nval V e x) :
    x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [map_zero, hx]⟩
  rw [nval_of_ne hx, EReal.coe_nonneg] at h
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have h1 : (0 : ℝ) ≤ vV V x := by
    have := mul_nonneg h he'.le
    rwa [div_mul_cancel₀ _ he'.ne'] at this
  have h2 : 0 ≤ vV V x := by exact_mod_cast h1
  have h3 : valV V x ≤ 1 := by
    refine (WithZero.log_le_log (valV_ne_zero (V := V) hx) one_ne_zero).1 ?_
    simp only [WithZero.log_one]
    simp only [vV] at h2
    omega
  exact IsDiscreteValuationRing.exists_lift_of_le_one (A := V) (K := K') h3

theorem evR_mem_range_of_valSet_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (F : Rul Xo c), (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v F) → ∀ (T : CDVR) (io : c.F →+* T.Fr), T.FinRes → letI := io.toAlgebra; ∀ y : FrPt Xo c T.Fr, Integral T io y → evR Xo c F y ∈ Set.range (algebraMap T.V T.Fr) := by
  intro E _ _ _ H Dw l Xo c F hF T io hT y hy
  let := io.toAlgebra
  have valV_le_one' (v : T.V) : valV T.V (algebraMap T.V T.Fr v) ≤ 1 := HeightOneSpectrum.valuation_le_one _ v
  have valV_lt_one_iff' (v : T.V) : valV T.V (algebraMap T.V T.Fr v) < 1 ↔ v ∈ IsLocalRing.maximalIdeal T.V :=
    HeightOneSpectrum.valuation_lt_one_iff_mem _ v
  have valV_eq_one_iff_isUnit' (v : T.V) : valV T.V (algebraMap T.V T.Fr v) = 1 ↔ IsUnit v := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← valV_lt_one_iff', not_lt]
    exact ⟨fun h => h.ge, fun h => le_antisymm (valV_le_one' v) h⟩
  have vV_pos' {v : T.V} (h0 : v ≠ 0) (h : v ∈ IsLocalRing.maximalIdeal T.V) : 0 < vV T.V (algebraMap T.V T.Fr v) := by
    have h1 : algebraMap T.V T.Fr v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective T.V T.Fr)).2 h0
    have := (WithZero.log_lt_log (valV_ne_zero (V := T.V) h1) one_ne_zero).2 ((valV_lt_one_iff' v).2 h)
    simp only [WithZero.log_one] at this
    simp only [vV]; omega
  open IsLocalRing in
  have hex : ∃ (la : HeightOneSpectrum (𝓞 c.F)) (e : ℕ), OverLa la T.V io e := by
    have hint : ∀ a : 𝓞 c.F, ∃ v : T.V, algebraMap T.V T.Fr v = io a := fun a =>
      IsIntegrallyClosed.algebraMap_eq_of_integral (R := T.V) (K := T.Fr)
        (IsIntegral.map_of_comp_eq (Int.castRingHom T.V) io (RingHom.ext_int _ _) a.isIntegral_coe)
    choose g0 hg0 using hint
    have hinj := IsFractionRing.injective T.V T.Fr
    let g : 𝓞 c.F →+* T.V :=
      { toFun := g0
        map_one' := hinj (by simp [hg0])
        map_mul' := fun a b => hinj (by simp [hg0])
        map_zero' := hinj (by simp [hg0])
        map_add' := fun a b => hinj (by simp [hg0]) }
    have hg : ∀ a, algebraMap T.V T.Fr (g a) = io (algebraMap (𝓞 c.F) c.F a) := hg0
    have hne : (maximalIdeal T.V).comap g ≠ ⊥ := by
      have : Finite (ResidueField T.V) := hT
      have hc : Nat.card (ResidueField T.V) ≠ 0 := Nat.card_pos.ne'
      intro h
      have h1 : ((Nat.card (ResidueField T.V) : ℕ) : 𝓞 c.F) ∈ (maximalIdeal T.V).comap g := by
        rw [Ideal.mem_comap, map_natCast, ← residue_eq_zero_iff, map_natCast, ← nsmul_one]
        exact card_nsmul_eq_zero'
      rw [h, Ideal.mem_bot] at h1
      exact hc (by exact_mod_cast h1)
    let la : HeightOneSpectrum (𝓞 c.F) := ⟨(maximalIdeal T.V).comap g, Ideal.comap_isPrime _ _, hne⟩
    have hun : ∀ a : 𝓞 c.F, a ∉ la.asIdeal → valV T.V (io (algebraMap (𝓞 c.F) c.F a)) = 1 := fun a ha => by
      rw [← hg, valV_eq_one_iff_isUnit']
      exact notMem_maximalIdeal.1 ha
    have hone : ∀ x : c.F, la.valuation c.F x = 1 → valV T.V (io x) = 1 := fun x hx => by
      obtain ⟨n, d, h⟩ := la.exists_primeCompl_mul_eq_of_integer x hx.le
      have hd : la.valuation c.F (algebraMap (𝓞 c.F) c.F d) = 1 := (la.valuation_eq_one_iff_notMem).2 d.2
      have hn : la.valuation c.F (algebraMap (𝓞 c.F) c.F n) = 1 := by rw [← h, map_mul, hx, hd, _root_.one_mul]
      have h2 := hun n ((la.valuation_eq_one_iff_notMem).1 hn)
      rwa [← h, map_mul, map_mul, hun d d.2, _root_.mul_one] at h2
    obtain ⟨π, hπ⟩ := la.intValuation_exists_uniformizer
    have hπK : la.valuation c.F (algebraMap (𝓞 c.F) c.F π) = WithZero.exp (-1 : ℤ) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, hπ]
    have hπ0 : algebraMap (𝓞 c.F) c.F π ≠ 0 := fun h => by simp [h] at hπK; exact WithZero.exp_ne_zero hπK.symm
    have hπm : π ∈ la.asIdeal := by
      rw [← la.valuation_lt_one_iff_mem (K := c.F), hπK, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
    have hpos : 0 < vV T.V (io (algebraMap (𝓞 c.F) c.F π)) := by
      rw [← hg]
      refine vV_pos' (fun h => ?_) hπm
      have := hg π
      rw [h, map_zero] at this
      exact (map_ne_zero io).2 hπ0 this.symm
    refine ⟨la, (vV T.V (io (algebraMap (𝓞 c.F) c.F π))).toNat, by omega, fun a => ?_⟩
    rw [Int.toNat_of_nonneg hpos.le]
    by_cases ha : a = 0
    · simp [ha, vV, vLa]
    have hva : la.valuation c.F a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
    have h1 := hone (a * (algebraMap (𝓞 c.F) c.F π) ^ (-vLa la a)) (by
      rw [map_mul, map_zpow₀, hπK, ← WithZero.exp_zsmul, ← WithZero.exp_log hva, ← WithZero.exp_add]
      simp [vLa])
    have h2 := congrArg WithZero.log h1
    rw [map_mul, map_mul, map_zpow₀, map_zpow₀, WithZero.log_mul (valV_ne_zero ((map_ne_zero io).2 ha))
      (zpow_ne_zero _ (valV_ne_zero ((map_ne_zero io).2 hπ0))), WithZero.log_zpow, WithZero.log_one] at h2
    simp only [vV, smul_eq_mul] at h2 ⊢
    linarith

  obtain ⟨la, e, ho⟩ := hex
  have ht := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c T.Fr y
  have h := hF la _ ⟨PtV.mk (cls := algCls Xo c) la ho ⟨y, ht, hy⟩ hT () trivial, rfl⟩
  exact mem_range_of_nval_nonneg ho.1 h

end GlobalTheory.LamT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UniversalTripleFibreKeyDataNonemptyField
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CM GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem nonempty_fibKey : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x : Sp K ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → Nonempty (FibKey Xo K x) := by
  intro E _ _ _ H Dw l Xo K _ x hpq
  have hT : Out.SecTwistSt := GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨U, hU, hg⟩ := exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨t, ⟨m⟩⟩ : ∃ t : SAB H (Sp K), Nonempty (SABMap t Xo.univ.t x) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull x Xo.univ.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨⟨T, rfl, hTg⟩, -⟩ := PAT.exists_of_sabMap E H _ _ x U t (hU ▸ m)
  have hpos : 1 ≤ Module.finrank ℚ E / 2 := by
    have h1 := (letI : Module.Free (maximalRealSubfield E) E := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E)
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h1
    have h2 : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
    omega
  obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section hT T.pol
  obtain ⟨a, -, hu⟩ := hb b
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis T.t.G T.dim
  refine ⟨⟨T, m, ?_, b, KeyPow.exists_mem_nonzeroLocus T.pol b ?_, v, hv⟩⟩
  · rw [hTg, hg]
    exact Nat.mul_pos hpos hpq
  · by_contra hn
    push Not at hn
    exact zero_ne_one ((hu 0 fun i => by rw [hn i, mul_zero]).trans (hu 1 fun i => by rw [hn i, mul_zero]).symm)

end GlobalTheory.LamT
end

