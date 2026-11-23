module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.LatticeOnly
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinJetSplitLattice
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma omegaFactor_ne_zero' {F : Type} [Field F] [NumberField F] (𝔞 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 ≠ 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm
  refine mul_ne_zero ?_ ?_
  · have h : (0:ℝ) < |((discr F : ℤ) : ℝ)| := by
      rw [abs_pos]; exact_mod_cast discr_ne_zero F
    positivity
  · rw [Rat.cast_ne_zero, Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact 𝔞.ne_zero


set_option autoImplicit false in
open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hasSum_jet_split : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ), Even k → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → 0 < τ.im → HasSum (fun ξ : F ↦ ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k * (a ξ * _root_.GlobalTheory.HilbFam.eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.HilbFam.lag k (κ i) c ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t))) (_root_.GlobalTheory.HilbFam.jet k (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) κ τ c t) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t κ hk ha hτ
  have h := (_root_.GlobalTheory.HilbFam.hasSum_iterD_gval_split F k 𝔞 𝔟 a₀ a x τ c t
    (_root_.GlobalTheory.HilbFam.word κ) hk ha hτ).mul_left
    (((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k)
  have hC : ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ)) ^ k ≠ 0 := by
    refine pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ ?_) ?_)
    · simp [Real.pi_ne_zero, Complex.I_ne_zero]
    · exact_mod_cast omegaFactor_ne_zero' 𝔞
  simp only [_root_.GlobalTheory.HilbFam.count_word_eq, mul_div_cancel₀ _ hC] at h
  exact h

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselianLocalRingHens
section
open IsLocalRing GlobalTheory.Henselisation Polynomial

namespace GlobalTheory.Henselisation

theorem eval_derivative_scaleRoots_mul {S : Type*} [CommRing S] (p : S[X]) (s x : S) :
    (derivative (p.scaleRoots s)).eval (s * x) = s ^ (p.natDegree - 1) * (derivative p).eval x := by
  have h1 : (derivative (p.scaleRoots s)).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le (p.scaleRoots s)
    rw [natDegree_scaleRoots] at this; omega
  have h2 : (derivative p).natDegree < p.natDegree + 1 := by
    have := natDegree_derivative_le p; omega
  rw [eval_eq_sum_range' h1, eval_eq_sum_range' h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_derivative, coeff_derivative, coeff_scaleRoots]
  by_cases hkd : k + 1 ≤ p.natDegree
  · have e : s ^ (p.natDegree - (k + 1)) * (s * x) ^ k = s ^ (p.natDegree - 1) * x ^ k := by
      rw [mul_pow, ← mul_assoc, ← pow_add]; congr 2; omega
    calc _ = p.coeff (k + 1) * (↑k + 1) * (s ^ (p.natDegree - (k + 1)) * (s * x) ^ k) := by ring
      _ = _ := by rw [e]; ring
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; ring

theorem isUnit_of_sub_mem_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] {x u : S}
    (hu : IsUnit u) (h : x - u ∈ maximalIdeal S) : IsUnit x := by
  by_contra hx
  have hx' : x ∈ maximalIdeal S := (mem_maximalIdeal x).2 hx
  have : u ∈ maximalIdeal S := by
    have := Ideal.sub_mem _ hx' h; simpa using this
  exact (mem_maximalIdeal u).1 this hu

theorem henselianLocalRing_hens : ∀ (R : Type) [CommRing R] [IsLocalRing R],
    HenselianLocalRing (Hens R) := by
  intro R _ _
  haveI : IsDirected (EtNbhd R) (· ≤ ·) := _root_.GlobalTheory.Henselisation.etNbhd_isDirected R
  obtain ⟨hloc, hofloc⟩ := _root_.GlobalTheory.Henselisation.hens_isLocalRing_and_isLocalHom_of R
  letI := hloc
  refine { toIsLocalRing := hloc, is_henselian := ?_ }
  intro f hf a₀ hfa₀ hf'a₀

  obtain ⟨i', b₀, hb₀⟩ : ∃ (i : EtNbhd R) (b : i.B), Hens.of i b = a₀ :=
    Ring.DirectLimit.exists_of a₀
  obtain ⟨r, hr⟩ := _root_.GlobalTheory.Henselisation.EtNbhd.exists_sub_mem_maximalIdeal R i' b₀
  set ρ := algebraMap R (Hens R) r with hρdef
  have hρ : a₀ - ρ ∈ maximalIdeal (Hens R) := by
    haveI := hofloc i'
    rw [← hb₀, hρdef, ← _root_.GlobalTheory.Henselisation.Hens.of_algebraMap R i' r, ← (Hens.of i').map_sub b₀ ((algebraMap R i'.B) r)]; exact map_nonunit _ _ hr
  have hfρ : f.eval ρ ∈ maximalIdeal (Hens R) := by
    have hd := sub_dvd_eval_sub ρ a₀ f
    have : f.eval ρ - f.eval a₀ ∈ maximalIdeal (Hens R) := by
      obtain ⟨c, hc⟩ := hd
      rw [hc]; apply Ideal.mul_mem_right
      have := (Ideal.neg_mem_iff _).2 hρ; simpa using this
    simpa using Ideal.add_mem _ this hfa₀
  have hf'ρ : IsUnit (f.derivative.eval ρ) := by
    refine isUnit_of_sub_mem_maximalIdeal hf'a₀ ?_
    obtain ⟨c, hc⟩ := sub_dvd_eval_sub ρ a₀ (derivative f)
    rw [hc]; apply Ideal.mul_mem_right
    have := (Ideal.neg_mem_iff _).2 hρ; simpa using this

  obtain ⟨i, g, hg⟩ : ∃ (i : EtNbhd R) (g : Polynomial i.B), g.map (Hens.of i) = f :=
    Ring.DirectLimit.Polynomial.exists_of (f' := fun _ _ h => EtNbhd.trans h) f
  haveI := hofloc i
  have hgm : g.Monic := monic_of_injective (_root_.GlobalTheory.Henselisation.Hens.of_injective_of_nbhd R i) (hg ▸ hf)
  let M := i.q.primeCompl
  let ψ : i.A →+* i.B := algebraMap i.A i.B
  let s : M := IsLocalization.commonDenom M g.support g.coeff
  have hl := IsLocalization.scaleRoots_commonDenom_mem_lifts M g
    (by rw [hgm.leadingCoeff]; exact ⟨1, map_one _⟩)
  obtain ⟨h, hhmap, -, hhm⟩ := lifts_and_natDegree_eq_and_monic hl
    ((monic_scaleRoots_iff _).2 hgm)
  let Φ : i.A →+* Hens R := (Hens.of i).comp ψ
  let u : Hens R := Φ s
  have hu : IsUnit u := (IsLocalization.map_units i.B s).map (Hens.of i)
  have hΦr : Φ (algebraMap R i.A r) = ρ := by
    simp only [Φ, ψ, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
    exact _root_.GlobalTheory.Henselisation.Hens.of_algebraMap R i r
  let a₀' : i.A := (s : i.A) * algebraMap R i.A r
  have hΦa₀' : Φ a₀' = u * ρ := by simp only [a₀', map_mul, hΦr]; rfl
  have hhΦ : h.map Φ = f.scaleRoots u := by
    rw [show Φ = (Hens.of i).comp ψ from rfl, ← Polynomial.map_map, hhmap, map_scaleRoots _ _ _
      (by rw [hgm.leadingCoeff, map_one]; exact one_ne_zero), hg]
    rfl
  have key1 : Φ (h.eval a₀') = u ^ f.natDegree * f.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, hhΦ, hΦa₀']
    exact scaleRoots_eval₂_mul (RingHom.id _) ρ u
  have key2 : Φ (h.derivative.eval a₀') = u ^ (f.natDegree - 1) * f.derivative.eval ρ := by
    rw [← eval₂_at_apply, ← eval_map, ← derivative_map, hhΦ, hΦa₀']
    exact eval_derivative_scaleRoots_mul f u ρ
  have hpt1 : i.pt (h.eval a₀') = 0 := by
    have hm : ψ (h.eval a₀') ∈ maximalIdeal i.B := by
      intro hun
      have : Φ (h.eval a₀') ∈ maximalIdeal (Hens R) := by
        rw [key1]; exact Ideal.mul_mem_left _ _ hfρ
      exact (mem_maximalIdeal _).1 this (hun.map (Hens.of i))
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).1 hm
    exact (RingHom.mem_ker).1 this
  have hpt2 : i.pt (h.derivative.eval a₀') ≠ 0 := by
    intro h0
    have hq : h.derivative.eval a₀' ∈ i.q := RingHom.mem_ker.2 h0
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff i.B i.q _).2 hq
    have hΦm : Φ (h.derivative.eval a₀') ∈ maximalIdeal (Hens R) := map_nonunit (Hens.of i) _ hm
    rw [key2] at hΦm
    exact (mem_maximalIdeal _).1 hΦm ((hu.pow _).mul hf'ρ)
  obtain ⟨j, hij, c, hc, hcm⟩ := GlobalTheory.T.exists_le_isRoot_of_simpleRoot_pointedEtaleNbhd R i h a₀' hhm hpt1 hpt2
  haveI := hofloc j
  have hofj : (Hens.of j).comp (EtNbhd.trans hij) = Hens.of i :=
    RingHom.ext fun x => Ring.DirectLimit.of_f hij x
  have hΦj : (Hens.of j).comp ((EtNbhd.trans hij).comp ψ) = Φ := by
    rw [← RingHom.comp_assoc, hofj]
  set c' := Hens.of j c
  have hroot : (f.scaleRoots u).eval c' = 0 := by
    rw [← hhΦ, ← hΦj, ← Polynomial.map_map, eval_map, eval₂_at_apply, hc.eq_zero, map_zero]
  have hcm' : c' - u * ρ ∈ maximalIdeal (Hens R) := by
    have := map_nonunit (Hens.of j) _ hcm
    rwa [(Hens.of j).map_sub c ((EtNbhd.trans hij) (ψ a₀')), ← RingHom.comp_apply (Hens.of j) (EtNbhd.trans hij),
      ← RingHom.comp_apply ((Hens.of j).comp (EtNbhd.trans hij)) ψ, hofj,
      show (Hens.of i).comp ψ = Φ from rfl, hΦa₀'] at this
  refine ⟨↑hu.unit⁻¹ * c', ?_, ?_⟩
  · have hc' : c' = u * (↑hu.unit⁻¹ * c') := by
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
    have e := scaleRoots_eval₂_mul (p := f) (RingHom.id _) (↑hu.unit⁻¹ * c') u
    simp only [RingHom.id_apply] at e
    change eval (u * _) _ = u ^ _ * eval _ f at e
    rw [← hc', hroot] at e
    exact (((hu.pow _).mul_right_eq_zero).1 e.symm)
  · have e1 : ↑hu.unit⁻¹ * c' - ρ = ↑hu.unit⁻¹ * (c' - u * ρ) := by
      rw [mul_sub, ← mul_assoc, hu.val_inv_mul, one_mul]
    have e2 : ↑hu.unit⁻¹ * c' - a₀ = (↑hu.unit⁻¹ * c' - ρ) - (a₀ - ρ) := by ring
    rw [e2, e1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hcm') hρ

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOf
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam

theorem derivWeierstrassP_eq_of_lattice_eq {L L' : PeriodPair} (h : L.lattice = L'.lattice) :
    L.derivWeierstrassP = L'.derivWeierstrassP := by
  rw [← L.deriv_weierstrassP, ← L'.deriv_weierstrassP, Formalism.L2.Th1.F.LatOnly.wp_eq h]

theorem derivWeierstrassP_scalePair (L : PeriodPair) (c : ℂ) (hc : c ≠ 0) (z : ℂ) :
    (scalePair L c hc).derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z := by
  unfold PeriodPair.derivWeierstrassP
  have hs := Formalism.L2.Th1.F.Homog.tsum_scale L c hc (fun w => 2 / (c * z - w) ^ 3)
  rw [hs]
  have hterm : ∀ l : L.lattice, 2 / (c * z - c * (l : ℂ)) ^ 3 = (c ^ 3)⁻¹ * (2 / (z - l) ^ 3) := by
    intro l
    rw [← mul_sub, mul_pow, div_mul_eq_div_div, div_eq_inv_mul (2 / c ^ 3), div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  ring

theorem lattice_eq_scalePair_tauPair {L : PeriodPair} {c : ℂ} {τ : ℍ} (h : IsTauOf L c τ) :
    L.lattice = (scalePair (tauPair τ) c h.1).lattice := by
  ext x
  rw [h.2 x, Formalism.L2.Th1.F.Homog.mem_scale, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨u, v, rfl⟩
    refine ⟨u, v, ?_⟩
    change (u : ℂ) * (τ : ℂ) + (v : ℂ) * 1 = c⁻¹ * (c * ((u : ℂ) * (τ : ℂ) + (v : ℂ)))
    rw [← mul_assoc, inv_mul_cancel₀ h.1, one_mul, mul_one]
  · rintro ⟨m, n, hmn⟩
    refine ⟨m, n, ?_⟩
    change (m : ℂ) * (τ : ℂ) + (n : ℂ) * 1 = c⁻¹ * x at hmn
    rw [mul_one] at hmn
    rw [hmn, ← mul_assoc, mul_inv_cancel₀ h.1, one_mul]

theorem homogeneity_of_isTauOf : ∀ (L : PeriodPair) (c : ℂ) (τ : ℍ), IsTauOf L c τ → (∀ z, c * z ∈ L.lattice ↔ z ∈ (tauPair τ).lattice) ∧ (∀ z, L.weierstrassP (c * z) = (c ^ 2)⁻¹ * (tauPair τ).weierstrassP z) ∧ (∀ z, L.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * (tauPair τ).derivWeierstrassP z) ∧ s2 L = (c ^ 2)⁻¹ * s2 (tauPair τ) ∧ area L = ‖c‖ ^ 2 * area (tauPair τ) := by
  intro L c τ h
  have hl := lattice_eq_scalePair_tauPair h
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_, ?_, ?_⟩
  · rw [hl, Formalism.L2.Th1.F.Homog.mem_scale, ← mul_assoc, inv_mul_cancel₀ h.1, one_mul]
  · rw [Formalism.L2.Th1.F.LatOnly.wp_eq hl, Formalism.L2.Th1.F.Homog.wp_scale]
  · rw [derivWeierstrassP_eq_of_lattice_eq hl, derivWeierstrassP_scalePair]
  · rw [Formalism.L2.Th1.F.LatOnly.quasiPeriodConst_eq hl, Formalism.L2.Th1.F.Homog.quasiPeriodConst_scale]
  · rw [Formalism.L2.Th1.F.LatOnly.area_eq hl, Formalism.L2.Th1.F.Homog.area_scale]

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExact
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh

theorem hyp2_eq_sum_cup_of_fn_exact : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ hc : Closed1 F = ⊤, Function.Surjective (toO F) → ∀ c : cechDeRhamTotalCocyclesTwo F, (∃ f, d1 F f = c.1.1) → ∃ (n : ℕ) (a : Fin n → Hyp1 F) (w : Fin n → Glob1 F), Hyp2.mk F c = ∑ k, cupHyp F (a k) (clAll F hc (w k)) := by
  intro R _ C _ F hfr h0 hc hs c ⟨f, hf⟩
  obtain ⟨m, ⟨fr⟩⟩ := hfr
  have hcl : ∀ (w : Glob1 F) (T : C), dOne R _ (w.1 T) = 0 := fun w T ↦
    (show w ∈ Closed1 F by rw [hc]; trivial) T
  have hclAll : ∀ w : Glob1 F, clAll F hc w = Hyp1.mk F ⟨(0, w.1), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨zero_mem _,
      fun T T' φ ↦ by simpa using w.2 φ, fun T ↦ hcl w T⟩⟩ := fun w ↦ rfl
  set c' : cechDeRhamTotalCocyclesTwo F := c - ⟨dTot1 F (f, 0), dTot1_mem F _⟩ with hc'
  have hmk : Hyp2.mk F c = Hyp2.mk F c' := by
    rw [hc', map_sub, (Hyp2.mk_eq_zero (c := ⟨dTot1 F (f, 0), dTot1_mem F _⟩)).2 ⟨(f, 0), rfl⟩, sub_zero]
  have hz : ∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''), c'.1.1 T T' T'' φ ψ = 0 := by
    intro T T' T'' φ ψ
    change c.1.1 T T' T'' φ ψ - d1 F f T T' T'' φ ψ = 0
    rw [hf, sub_self]
  set a : A1 F := c'.1.2.1 with ha
  have hacoc : ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ := by
    intro T T' T'' φ ψ
    rw [ha, cechDeRhamTotalCocyclesTwo.one c' φ ψ, hz, map_zero, add_zero]
  let g : Fin m → Z1 F := fun i ↦ ⟨fun T T' φ ↦ fr.δ i T' (a T T' φ), fun T T' T'' φ ψ ↦ by
    simp only [hacoc φ ψ, map_add (f := _), fr.nat]⟩
  have hE : ∀ i, ∃ e : cechDeRhamTotalCocyclesOne F, e.1.1 = (g i).1 := by
    intro i
    obtain ⟨x, hx⟩ := hs (H1.mk F (g i))
    obtain ⟨e0, rfl⟩ := Hyp1.mk_surjective F x
    rw [toO_mk, H1.mk_eq_mk] at hx
    obtain ⟨h, hh⟩ := hx
    refine ⟨e0 - ⟨dTot0 F h, dTot0_mem F h⟩, ?_⟩
    change e0.1.1 - d0 F h = (g i).1
    rw [hh]; change e0.1.1 - (e0.1.1 - (g i).1) = (g i).1; abel
  choose e he using hE
  let η' : W0 F 2 := fun T ↦ c'.1.2.2 T - ∑ i, wedge R _ ((e i).1.2 T) ((fr.w i).1 T)
  have hη' : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), η' T' = pOm F 2 φ (η' T) := by
    intro T T' φ
    have hd : dOne R _ (a T T' φ) = ∑ i, wedge R _ (D R _ (fr.δ i T' (a T T' φ))) ((fr.w i).1 T') := by
      conv_lhs => rw [fr.sum T' (a T T' φ)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, dOne_smul, hcl]
    have hw : ∀ i, (fr.w i).1 T' = p1 F φ ((fr.w i).1 T) := fun i ↦ (fr.w i).2 φ
    have he' : ∀ i, (e i).1.2 T' = p1 F φ ((e i).1.2 T) + D R _ (fr.δ i T' (a T T' φ)) := by
      intro i; rw [cechDeRhamTotalCocyclesOne.conn (e i) φ, he]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [η', map_sub, map_sum, pOm_wedge]
    rw [cechDeRhamTotalCocyclesTwo.two c' φ, ← ha, hd]
    simp only [he', map_add (f := _), LinearMap.add_apply, Finset.sum_add_distrib, ← hw]
    abel
  obtain ⟨n, u, v, huv⟩ := _root_.GlobalTheory.AbCoh.twoForm_eq_wsum R C F ⟨m, ⟨fr⟩⟩ h0 η' hη'
  refine ⟨m + n, Fin.append (fun i ↦ Hyp1.mk F (e i)) (fun k ↦ clAll F hc (u k)), Fin.append fr.w v, ?_⟩
  rw [Fin.sum_univ_add]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Fin.append_left, Fin.append_right, hclAll, cupHyp_mk, ← map_sum, ← map_add (f := _), hmk]
  congr 1
  apply Subtype.ext
  refine Tot2.ext (fun T T' T'' φ ψ ↦ ?_) (fun T T' φ ↦ ?_) (fun T ↦ ?_)
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.fst_add, Prod.fst_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_apply, hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
  · simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Prod.fst_add, Prod.fst_sum,
      Pi.add_apply, Finset.sum_apply, coe_cupZZ, cupTot_a, Pi.zero_apply, zero_smul, sub_zero,
      Finset.sum_const_zero, add_zero, he]
    exact fr.sum T' (a T T' φ)
  · have := congrFun huv T
    simp only [η', wsum] at this
    simp only [Submodule.coe_add, Submodule.coe_sum, Prod.snd_add, Prod.snd_sum, Pi.add_apply,
      Finset.sum_apply, coe_cupZZ, cupTot_η]
    rw [← this]; abel
end GlobalTheory.AbCoh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureEtaleAtOfHeightLeOnePurityStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosureEtaleAt_of_height_le_one_purity : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime], P.height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one) | (exact GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one) | (intros; apply GlobalTheory.KeyOriginEnlarge.closureEtaleAt_of_comap_height_le_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneForms
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isBaseChange_glob1 (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]) (he : ∀ w, e w = w.1 T) :
    IsBaseChange (F.obj T) e := by
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, hl, hsum⟩ := _root_.GlobalTheory.AbCoh.frame_coord R C F h0 n Φ
  let S := F.obj T
  let fwd : S ⊗[R] Glob1 F →ₗ[S] Ω[F.obj T⁄R] := e.liftBaseChange S
  let inv : Ω[F.obj T⁄R] →ₗ[S] S ⊗[R] Glob1 F :=
    ∑ i, (Φ.δ i T).smulRight ((1 : S) ⊗ₜ[R] Φ.w i)
  have hinv : ∀ ω, inv ω = ∑ i, Φ.δ i T ω ⊗ₜ[R] Φ.w i := by
    intro ω
    simp only [inv, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have h1 : ∀ ω, fwd (inv ω) = ω := by
    intro ω
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hinv, map_sum]
    simp only [fwd, LinearMap.liftBaseChange_tmul, he]
    exact (Φ.sum T ω).symm
  have h2 : ∀ x, inv (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul b w =>
      have : ∑ i, Φ.δ i T (w.1 T) ⊗ₜ[R] Φ.w i = (1 : S) ⊗ₜ[R] w := by
        conv_rhs => rw [hsum w]
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hl, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      show inv (e.liftBaseChange S (b ⊗ₜ[R] w)) = _
      rw [LinearMap.liftBaseChange_tmul, map_smul, he, hinv, this, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinear fwd inv (LinearMap.ext h1) (LinearMap.ext h2))
    (fun w ↦ by simp [fwd])

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionSurjectivePreimage
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.GlueColim


set_option backward.isDefEq.respectTransparency false in
theorem isClosedImmersion_surjective_preimage : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0}) [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected] (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G), (∀ x : X, ∃ U ∈ 𝒰, x ∈ G U) → ∀ (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U), (∀ U, IsClosedImmersion (e U)) → (∀ U, Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → ∀ j : X ⟶ colimit F, (∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U) → IsClosedImmersion j ∧ Surjective j ∧ ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
  intro B₀ 𝒰 F _ _ X G hG hc e he hs hnat j hj
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : (G U.1).toScheme),
      F.map f (e U x) = e V (X.homOfLE (hG (show U.1 ≤ V.1 from f.le)) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat (show U.1 ≤ V.1 from f.le)]
    rfl
  have hinj : ∀ U, Function.Injective (e U) := fun U ↦ (e U).isClosedEmbedding.injective
  have key2 : ∀ {U V : 𝒰} (x : (G U.1).toScheme) (y : (G V.1).toScheme),
      colimit.ι F U (e U x) = colimit.ι F V (e V y) → x.1 = y.1 := by
    intro U V x y h
    obtain ⟨W, f, g, z, h1, h2⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp h
    obtain ⟨z, rfl⟩ := (e W).surjective z
    rw [hnat'] at h1 h2
    have h1' := congrArg Subtype.val (hinj _ h1)
    have h2' := congrArg Subtype.val (hinj _ h2)
    simp only [Scheme.homOfLE_apply] at h1' h2'
    exact h1'.symm.trans h2'
  have hj' : ∀ (U : 𝒰) (x : (G U.1).toScheme), j x.1 = colimit.ι F U (e U x) := fun U x ↦
    congr($(hj U) x)
  have hpre : ∀ U : 𝒰, j ⁻¹ᵁ (colimit.ι F U).opensRange = G U.1 := by
    intro U
    ext x
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := (e U).surjective y
      obtain ⟨V, hV, hxV⟩ := hc x
      have := key2 (V := ⟨V, hV⟩) y ⟨x, hxV⟩ (hy.trans (hj' ⟨V, hV⟩ ⟨x, hxV⟩))
      have h2 : y.1 = x := this
      exact h2 ▸ y.2
    · intro hx
      exact ⟨_, (hj' U ⟨x, hx⟩).symm⟩
  refine ⟨?_, ⟨?_⟩, hpre⟩
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsClosedImmersion)
      (Scheme.IsLocallyDirected.openCover F)]
    intro U
    have H : IsPullback (e U) (G U.1).ι (colimit.ι F U) j :=
      IsOpenImmersion.isPullback _ _ _ _ (hj U) (by rw [hpre]; simp)
    have : pullback.snd j (colimit.ι F U) = H.flip.isoPullback.inv ≫ e U := by simp
    change IsClosedImmersion (pullback.snd j (colimit.ι F U))
    rw [this]
    infer_instance
  · intro b
    obtain ⟨U, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F b
    obtain ⟨x, rfl⟩ := (e U).surjective x
    exact ⟨_, hj' U x⟩

end GlobalTheory.GlueColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCocycleSimplicialLevelsCup
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ GlobalTheory.PBFc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_cocycle_simplicial_levels_cup : ∀ (q : ℕ) [NeZero q] {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) (hE : Inv q E) {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ) (z : ∀ j : Fin N, Cocycle ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ))) (hz : ∀ (a : ℕ) (j : Fin N), CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains (ZMod q)).map (ℓ.app (op (SimplexCategory.mk a))))) (z j) (zero_add _)) = cpow q (c1 q (ptimes.snd (E.obj (op (SimplexCategory.mk a))) (Fib N) ≫ Fib.line N)) (j : ℕ)) (hD : ∀ (F : PSh) (V₀ : disc.obj F ⟶ ofCat (glCat N)), Inv q (disc.obj F) → PBF q V₀), ∀ p ≤ (0 : ℤ), ∃ ψ : ∀ m, (∀ j : Fin N, CohomologyClass (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) → CohomologyClass ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m, (∀ m, Function.Bijective (ψ m)) ∧ ∀ n m, n + p = m → ∀ α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ)), (∀ j c r hr, p < c → (α j).v c r hr = 0) → ∀ (a : ∀ j : Fin N, Cocycle (sgl (((chains (ZMod q)).obj E).X p)) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (m - 2 * ((j : ℕ) : ℤ))) (b : Cocycle ((biChains (ZMod q) (twX E V)).X p) (res _ (tw q i)) m), (∀ j r hr hr', sglι (((chains (ZMod q)).obj E).X p) ≫ (a j).1.v 0 r hr = (α j).v p r hr') → (∀ (k t : ℤ) (h : p + k = t) r hr hr', b.1.v k r hr = (biChains (ZMod q) (twX E V)).ιTotal (ComplexShape.up ℤ) p k t h ≫ (phi q V ℓ i (fun j => (z j).1) n α).v t r hr') → ψ m (fun j => CohomologyClass.mk (a j)) = CohomologyClass.mk b := by
  first | (exact @GlobalTheory.PBFg.graded_bijective) | (exact GlobalTheory.PBFg.graded_bijective) | (intros; apply GlobalTheory.PBFg.graded_bijective  <;> assumption)
end

