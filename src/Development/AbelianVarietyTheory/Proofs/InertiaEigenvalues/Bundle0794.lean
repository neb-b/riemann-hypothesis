module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleConjugatePairPlacesEqSelfOfGoodChars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdmSelf

theorem not_mem_placesOver_of_normV {D : D7} {l M : ℕ} (hM : 0 < M) {P : Pl D.host.E}
    (h : normV P % (2 * l ^ M) = 1) : P ∉ placesOver D.host.E l := by
  intro hl
  have hmem : ((normV P : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have hn : normV P = Ideal.absNorm P.asIdeal := by
      rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn]
    exact Ideal.absNorm_mem P.asIdeal
  have hl' : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := hl
  have hdm := Nat.div_add_mod (normV P) (2 * l ^ M)
  rw [h] at hdm
  have hx : ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    push_cast
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hM
    rw [hk, pow_succ]
    exact P.asIdeal.mul_mem_right _ (P.asIdeal.mul_mem_left _ (P.asIdeal.mul_mem_left _ hl'))
  have h1 : (1 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have : (1 : 𝓞 D.host.E) = ((normV P : ℕ) : 𝓞 D.host.E) - ((2 * l ^ M * (normV P / (2 * l ^ M)) : ℕ) : 𝓞 D.host.E) := by
      generalize normV P / (2 * l ^ M) = q at hdm ⊢
      rw [← hdm]
      push_cast; ring
    rw [this]
    exact P.asIdeal.sub_mem hmem hx
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

end GlobalTheory.AdmSelf

namespace GlobalTheory.AdmSelf

theorem admissibleConjugatePairPlaces_eq_self_of_goodChar : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ)
    (Q : Finset (Pl D.host.E)) (d : PlE D.host → (G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)))),
    (∀ P ∈ Q, IsSplitPl D.host P) → (∀ P ∈ Q, ∀ P', IsConjPl D.host P P' → P' ∈ Q) →
    (∀ P ∈ Q, GlobalTheory.TwSys.GoodChar X i M P (d P) ∧ normV P % (2 * X.l i ^ M) = 1) →
    (0 < M ∨ ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i)) → admissibleConjugatePairPlaces X i Q M = Q := by
  intro D N X i M Q d hs hc hg hl
  classical
  have hnl : ∀ P ∈ Q, P ∉ placesOver D.host.E (X.l i) := fun P hP =>
    hl.elim (fun hM => not_mem_placesOver_of_normV hM (hg P hP).2) fun h => h P hP
  have hchar : ∀ P ∈ Q, ∃ χ : G D.host.E N.Om →* Multiplicative (ZMod (X.l i ^ M)),
      IsOpen (χ.ker : Set (G D.host.E N.Om)) ∧ AntiHom X.cc χ ∧
      (∀ w ∈ placesOver D.host.E (X.l i), ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Dec (F := D.host.E) A, χ σ = 1) ∧
      (∀ w : PlE D.host, w ≠ P → ¬ IsConjPl D.host P w → ∀ A : ValuationSubring N.Om, IsPlaceOver A w →
        ∀ σ ∈ Ine (F := D.host.E) A, χ σ = 1) ∧
      ∀ A : ValuationSubring N.Om, IsPlaceOver A P →
        Function.Surjective fun σ : Ine (F := D.host.E) A => Multiplicative.toAdd (χ σ) := fun P hP => by
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, -⟩ := hg P hP
    refine ⟨d P, h1, h2, h3, fun w a c => h4 w (fun t => t.elim a c), fun A hA x => ?_⟩
    obtain ⟨σ, hσ, hx⟩ := h5 P (Or.inl rfl) A hA (Multiplicative.ofAdd x)
    exact ⟨⟨σ, hσ⟩, congrArg Multiplicative.toAdd hx⟩
  refine Finset.Subset.antisymm (admissibleConjugatePairPlaces_subset i Q M) fun P hP => ?_
  obtain ⟨P', hPP'⟩ := GlobalTheory.TwistDet.exists_isConjPl P
  have hP' : P' ∈ Q := hc P hP P' hPP'
  refine mem_admissibleConjugatePairPlaces_iff.2 ⟨hP, P', hP', hPP', fun w hw => ?_, fun w hw => ?_⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨hs _ hP, hnl _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨hs _ hP', hnl _ hP'⟩
  · rcases Finset.mem_insert.1 hw with rfl | hw
    · exact ⟨⟨P', by simp, hPP'⟩, hchar _ hP⟩
    · obtain rfl := Finset.mem_singleton.1 hw
      exact ⟨⟨P, by simp, GlobalTheory.GalChar.isConjPl_symm hPP'⟩, hchar _ hP'⟩

end GlobalTheory.AdmSelf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientField
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalField

open Formalism.L2.Host

def sqN {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : ℝ :=
  Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

theorem absNorm_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem sqN_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : 0 < sqN v :=
  Real.sqrt_pos.2 (absNorm_pos v)

theorem sqN_sq {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    sqN v ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  Real.sq_sqrt (absNorm_pos v).le

theorem cpow_neg_half (n : ℕ) :
    ((n : ℕ) : ℂ) ^ (-(((-1 / 2 : ℝ)) : ℂ)) = ((Real.sqrt n : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  congr 1
  ring

theorem ordF_natCast {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (u : Eˣ) (M₀ : ℕ)
    (hu : (u : E) = ((M₀ : ℕ) : E)) :
    ordF v u = ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {((M₀ : ℕ) : 𝓞 E)})).factors : ℤ) := by
  have h0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have e : (u : E) = algebraMap (𝓞 E) E ((M₀ : ℕ) : 𝓞 E) := by rw [hu, map_natCast]
  rw [ordF, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v h0,
    WithZero.log_exp, neg_neg]

end GlobalTheory.FlipScalField

namespace GlobalTheory.FlipScalField
open Formalism.L2.Host


set_option maxHeartbeats 800000 in
theorem mem_fieldRange : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  intro E _ _ χ M₀ r w u a T k _ σ hw hu ha hT hunr hval hinf hTa hST
  classical
  have hM0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have hSfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set S := hSfin.toFinset with hSdef
  have hmemS : ∀ v, v ∈ S ↔ ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal := fun v => Set.Finite.mem_toFinset _
  set R := (GlobalTheory.HeckeProduct.finite_ordF a).toFinset with hRdef
  have hR : ∀ v, v ∉ R → ordF v a = 0 := fun v hv => by
    by_contra h; exact hv ((Set.Finite.mem_toFinset _).2 h)
  have hTS : T ⊆ S := fun v hv => (hmemS v).2 (hT v hv)
  have hoST : ∀ v ∈ S, v ∉ T → ordF v a = 0 := fun v hv hvT => by
    rw [ordF, (hST v ((hmemS v).1 hv) hvT).2, WithZero.log_one, neg_zero]
  have hoT : ∀ v ∈ T, ordF v a = ordF v u := fun v hv => by
    rw [ordF, ordF, (hTa v hv).2, hu]
  have hPR := Formalism.L2.Host.HChar.productRule χ S (fun v hv => hunr v (fun h => hv ((hmemS v).2 h))) a
  have hloc : ∏ v ∈ S, χ.locK v a = ∏ v ∈ T, χ.locK v u := by
    rw [← Finset.prod_subset hTS (fun v hv hvT => (hST v ((hmemS v).1 hv) hvT).1)]
    exact Finset.prod_congr rfl fun v hv => (hTa v hv).1
  have hfin : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v a) =
      ∏ v ∈ R \ S, χ.val v ^ ordF v a := by
    apply finprod_mem_eq_prod_of_subset (s := {v | v ∉ S})
    · rintro v ⟨hv1, hv2⟩
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      refine ⟨?_, hv1⟩
      by_contra h
      exact hv2 (by simp [hR v h])
    · intro v hv
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hv
      exact hv.2
  rw [hloc, hfin] at hPR
  choose! y hy using hval
  have hvalv : ∀ v, v ∉ S → ((χ.val v : ℂˣ) : ℂ) = σ (y v) / ((sqN v : ℝ) : ℂ) := fun v hv => by
    have h1 := hy v (hunr v fun h => hv ((hmemS v).2 h))
    have h2 : ((sqN v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqN_pos v).ne'
    rw [h1, HChar.valTw, cpow_neg_half, ← sqN, mul_div_assoc, div_self h2, mul_one]
  obtain ⟨y0, hy0⟩ := hinf
  set Q : ℝ := ∏ v ∈ R, sqN v ^ ordF v a with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hNa : |((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| = Q ^ 2 := by
    rw [← PI.AlgValsFin.W.prod_norm_emb, PI.AlgValsFin.W.prodNorm a R hR, hQ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  have hinfv : ((χ.inf a : ℂˣ) : ℂ) = σ y0 * (((Q ^ w)⁻¹ : ℝ) : ℂ) := by
    rw [hy0, hNa]
    congr 2
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_mul hQpos.le, ← Real.rpow_natCast, ← Real.rpow_neg hQpos.le]
    congr 1
    push_cast
    ring
  set A : ℝ := ∏ v ∈ T, sqN v ^ ordF v a with hA
  set B : ℝ := ∏ v ∈ R \ S, sqN v ^ ordF v a with hB
  have hApos : 0 < A := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hBpos : 0 < B := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hQAB : Q = A * B := by
    rw [hQ, ← Finset.prod_inter_mul_prod_diff R S]
    congr 1
    have e1 : ∏ v ∈ R ∩ S, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset Finset.inter_subset_right fun v hv hv' => by
        rw [hR v (fun h => hv' (Finset.mem_inter.2 ⟨h, hv⟩)), zpow_zero]
    have e2 : ∏ v ∈ T, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset hTS fun v hv hvT => by rw [hoST v hv hvT, zpow_zero]
    rw [e1, ← e2]
  have hprodval : ∏ v ∈ R \ S, ((χ.val v : ℂˣ) : ℂ) ^ ordF v a =
      σ (∏ v ∈ R \ S, y v ^ ordF v a) / ((B : ℝ) : ℂ) := by
    rw [map_prod, hB, Complex.ofReal_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hvalv v (Finset.mem_sdiff.1 hv).2, map_zpow₀, Complex.ofReal_zpow, div_zpow]
  have key := congrArg (fun z : ℂˣ => (z : ℂ)) hPR
  simp only [Units.val_mul, Units.val_one, Units.coe_prod, Units.val_zpow_eq_zpow_val] at key
  rw [hinfv, hprodval, hQAB] at key
  set P : ℂ := ∏ v ∈ T, ((χ.locK v u : ℂˣ) : ℂ) with hPdef
  set Y : k := ∏ v ∈ R \ S, y v ^ ordF v a with hY
  have h1 : σ y0 ≠ 0 := fun h => by rw [h] at key; simp at key
  have h2 : σ Y ≠ 0 := fun h => by rw [h] at key; simp at key
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hB0 : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hP : P = ((A : ℝ) : ℂ) ^ w * ((B : ℝ) : ℂ) ^ (w + 1) / (σ y0 * σ Y) := by
    rw [eq_div_iff (mul_ne_zero h1 h2)]
    push_cast at key
    field_simp at key
    linear_combination key

  have hsqrt : Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) =
      A ^ (r * w) := by
    rw [← Real.sqrt_sq (pow_nonneg hApos.le _)]
    congr 1
    push_cast
    rw [hA, ← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hoT v hv, ordF_natCast v u M₀ hu, HeightOneSpectrum.maxPowDividing, map_pow, zpow_natCast]
    push_cast
    rw [← sqN_sq v]
    ring
  set q : ℚ := ∏ v ∈ R \ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ ordF v a with hq
  have hqB : ((q : ℚ) : ℂ) = ((B : ℝ) : ℂ) ^ 2 := by
    have : ((q : ℚ) : ℝ) = B ^ 2 := by
      rw [hq, hB, ← Finset.prod_pow]
      push_cast
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    rw [← Complex.ofReal_ratCast, this, Complex.ofReal_pow]
  obtain ⟨m, rfl⟩ := hw
  have heq : (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) *
      ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * (2 * m + 1)) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ =
      (((q : ℚ) : ℂ) ^ (m + 1)) ^ r * ((σ y0 * σ Y)⁻¹) ^ r := by
    rw [hsqrt, Finset.prod_pow, ← hPdef, hP, hqB]
    push_cast
    field_simp
    ring
  rw [heq]
  refine mul_mem (pow_mem (pow_mem (SubfieldClass.ratCast_mem _ q) _) _) (pow_mem (inv_mem (mul_mem ?_ ?_)) _)
  · exact ⟨y0, rfl⟩
  · exact ⟨Y, rfl⟩

end GlobalTheory.FlipScalField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharInvCentralFlipIdeleEqProdLocalComponents
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FlipCharFormula

variable {D : D7}

theorem fa_mul (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a * b) Q = a Q * b Q := rfl
theorem fa_add (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a + b) Q = a Q + b Q := rfl
theorem fa_sub (a b : FiniteAdeleRing (𝓞 D.host.E) D.host.E) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (a - b) Q = a Q - b Q := rfl
theorem fa_one (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (1 : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = 1 := rfl
theorem fa_natCast (n : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    (n : FiniteAdeleRing (𝓞 D.host.E) D.host.E) Q = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.cast_succ, fa_add, ih, fa_one, Nat.cast_succ]
theorem fa_sum {α : Type*} (s : Finset α) (g : α → FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (Q : HeightOneSpectrum (𝓞 D.host.E)) : (∑ a ∈ s, g a) Q = ∑ a ∈ s, g a Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, fa_add, ih, Finset.sum_insert ha]

theorem finPart_incA (k : D.host.E) : finPart D (incA D k) = 1 ⊗ₜ k := rfl

theorem comp_of_isIdemAt (ι : Af ↥D.host.F ⊗[↥D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (h1 : ∀ (x : D.host.E), ι (1 ⊗ₜ[↥D.host.F] x) = (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)) x)
    (h2 : ∀ (y : Af ↥D.host.F ⊗[↥D.host.F] D.host.E),
      y ∈ intAE D ↔ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)), Valued.v ((ι y) P) ≤ 1)
    {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    ι (finPart D e) P = if P = PP then 1 else 0 := by
  obtain ⟨⟨hee, -, -⟩, hP⟩ := he
  have hidem : ∀ Q, ι (finPart D e) Q = 0 ∨ ι (finPart D e) Q = 1 := by
    intro Q
    apply IsIdempotentElem.iff_eq_zero_or_one.mp
    show ι (finPart D e) Q * ι (finPart D e) Q = ι (finPart D e) Q
    rw [← fa_mul, ← map_mul, ← map_mul, hee]
  have key : ∀ x : 𝓞 D.host.E, x ≠ 0 →
      (x ∈ PP.asIdeal ↔ ∃ Q, ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal) := by
    intro x hx
    rw [hP x hx, h2, map_mul, finPart_incA, map_mul, h1]
    have hQ : ∀ Q, (Valued.v ((ι (finPart D e) * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)
        ((x : D.host.E))⁻¹) Q) ≤ 1 ↔ ¬ (ι (finPart D e) Q = 1 ∧ x ∈ Q.asIdeal)) := by
      intro Q
      rw [fa_mul]
      rcases hidem Q with h | h
      · rw [h, zero_mul]; simp
      · rw [h, one_mul]
        have hv : Valued.v ((algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) ((x : D.host.E))⁻¹) Q)
            = HeightOneSpectrum.valuation D.host.E Q ((x : D.host.E))⁻¹ :=
          HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _
        have hx0 : HeightOneSpectrum.valuation D.host.E Q (x : D.host.E) ≠ 0 := by
          simpa using hx
        rw [hv, map_inv₀, inv_le_one₀ (zero_lt_iff.mpr hx0), ← not_lt,
          HeightOneSpectrum.valuation_lt_one_iff_mem]
        simp
    simp only [hQ, not_forall, not_not]
  have hne : ∀ Q, Q ≠ PP → ι (finPart D e) Q = 0 := by
    intro Q hQ
    rcases hidem Q with h | h
    · exact h
    · exfalso
      have hnle : ¬ Q.asIdeal ≤ PP.asIdeal := by
        intro hle
        apply hQ
        exact HeightOneSpectrum.ext (Q.isMaximal.eq_of_le PP.isPrime.ne_top hle)
      obtain ⟨x, hxQ, hxP⟩ := Set.not_subset.mp hnle
      have hx0 : x ≠ 0 := by rintro rfl; exact hxP PP.asIdeal.zero_mem
      exact hxP ((key x hx0).mpr ⟨Q, h, hxQ⟩)
  have hPP : ι (finPart D e) PP = 1 := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot PP.ne_bot
    obtain ⟨Q, hQ1, -⟩ := (key x hx0).mp hx
    by_cases hQ : Q = PP
    · rwa [hQ] at hQ1
    · rw [hne Q hQ] at hQ1; exact absurd hQ1 zero_ne_one
  split_ifs with h
  · rw [h, hPP]
  · exact hne P h

theorem infPart_of_isIdemAt {e : AE D} {PP : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) : infPart D e = 0 := by
  obtain ⟨⟨hee, hec, v, ε, ⟨α, rfl, -, -⟩, hsum⟩, -⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id (↥D.host.F) D.host.E)) ((pairA D.host.F 0 α : AF D.host.F) ⊗ₜ[↥D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul]
    have : (fstA D.host.F) (pairA D.host.F 0 α) = 0 := rfl
    rw [this]
    exact TensorProduct.zero_tmul _ _
  have hs := congrArg (infPart D) hsum
  have hm := congrArg (infPart D) hec
  have hi := congrArg (infPart D) hee
  rw [map_add (f := _), h0] at hs
  rw [map_mul, map_zero] at hm
  rw [map_mul] at hi
  have hc : infPart D (cA D e) = - infPart D e :=
    eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hs)
  rw [hc, mul_neg, hi, neg_eq_zero] at hm
  exact hm


set_option maxHeartbeats 800000 in
theorem char_inv_eq_prod_locK_of_flip : ∀ (D : D7) (V : HSp D) (χW : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (M₀ : ℕ) (u : D.host.Eˣ) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (x : (AE D)ˣ), ChrEq χW χ → (u : D.host.E) = ((M₀ : ℕ) : D.host.E) → IsIdemSum eT T → IsFlipDet V eT M₀ x → ((χW x : Circle) : ℂ)⁻¹ = ∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank := by
  intro D V χW χ M₀ u T eT x hχ hu hT hx
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) χW χ hχ
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hT
  unfold IsFlipDet at hx
  have heT : ∀ P, ι (finPart D (∑ PP ∈ T, es PP)) P = if P ∈ T then 1 else 0 := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, fa_sum,
      Finset.sum_congr rfl (fun PP hPP => comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq T P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ T, es PP) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    have := congrArg (infPart D) hx
    rw [map_mul, map_add (f := _), map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero, mul_one] at this
    exact this
  have hcomp : ∀ P, ι (finPart D (x : AE D)) P *
      ((if P ∈ T then 1 else 0) * (((M₀ ^ V.rank : ℕ) : HeightOneSpectrum.adicCompletion D.host.E P))
        + (1 - if P ∈ T then 1 else 0)) = 1 := by
    intro P
    have h0 : ι (finPart D ((x : AE D) * ((∑ PP ∈ T, es PP) * ((M₀ ^ V.rank : ℕ) : AE D)
        + (1 - ∑ PP ∈ T, es PP)))) P = ι (finPart D 1) P := by
      rw [Nat.cast_pow, hx]
    simp only [map_mul, map_add (f := _), map_sub, map_one, map_natCast] at h0
    rw [fa_mul, fa_add, fa_mul, fa_sub, fa_one, fa_natCast, heT] at h0
    exact h0
  let k : HeightOneSpectrum (𝓞 D.host.E) → D.host.Eˣ := fun P => if P ∈ T then (u⁻¹) ^ V.rank else 1
  have hxk : ∀ P, ι (finPart D (x : AE D)) P =
      algebraMap D.host.E (HeightOneSpectrum.adicCompletion D.host.E P) (k P : D.host.E) := by
    intro P
    have hc := hcomp P
    by_cases hP : P ∈ T
    · rw [if_pos hP, one_mul, sub_self, add_zero] at hc
      rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, hu,
        map_pow, map_inv₀, map_natCast, eq_inv_of_mul_eq_one_left hc, Nat.cast_pow, inv_pow]
    · rw [if_neg hP, zero_mul, sub_zero, zero_add, mul_one] at hc
      rw [show k P = 1 from if_neg hP, Units.val_one, map_one]
      exact hc
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (T ∪ (Ideal.finite_factors hI).toFinset) k
    (fun P _ => by
      rw [hxk P, sub_self, map_zero]
      exact ⟨HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _, zero_le'⟩)
    (fun P hP => by
      have hPT : P ∉ T := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨?_, ?_⟩
      · rw [hxk P, show k P = 1 from if_neg hPT, Units.val_one, map_one, map_one]
      · intro hNP
        apply hP
        apply Finset.mem_union_right
        rw [Set.Finite.mem_toFinset]
        exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key, ← Finset.prod_subset (Finset.subset_union_left)
    (fun P _ hPT => by rw [show k P = 1 from if_neg hPT, map_one, Units.val_one])]
  rw [Finset.prod_congr rfl (fun P hP => by
    rw [show k P = (u⁻¹) ^ V.rank from if_pos hP, map_pow, map_inv, Units.val_pow_eq_pow_val,
      Units.val_inv_eq_inv_val, inv_pow])]
  rw [Finset.prod_inv_distrib, inv_inv]

end GlobalTheory.FlipCharFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedData_normalCoefficientField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → ∃ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) ∧ M.lev = (O i).lev ∧ (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) ∧ Normal ℚ M.c'.F ∧ GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 ∧ (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) ∧ ∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e := by
  first | exact @GlobalTheory.PinsNormal.exists_pins_normal | exact GlobalTheory.PinsNormal.exists_pins_normal | (intros; apply GlobalTheory.PinsNormal.exists_pins_normal <;> assumption)
end

