module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFixingSubgroupMaxUnramifiedOfMemLocalGalois
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityWittTiltAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowMulEqThetaWitt
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem coeC (z : Om l) : (z : ℂ_[l]) = algebraMap (Om l) ℂ_[l] z := rfl

theorem norm_l_C : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]

theorem norm_l_Om : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.norm_extends l (l : Om l), coeC, map_natCast, norm_l_C]

theorem norm_OC_le (x : OC l) : ‖(x : ℂ_[l])‖ ≤ 1 := (GlobalTheory.RingBasics.mem_OC _).1 x.2

theorem mem_OL_of_norm_le (K : FinExt l) (y : ↥K.1) (h : ‖(y : Om l)‖ ≤ 1) : y ∈ OL K := by
  have hi : IsIntegral ℚ_[l] (y : Om l) := Algebra.IsIntegral.isIntegral _
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hi)] at h
  have hl : minpoly ℚ_[l] (y : Om l) ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hi)
  have h1 : IsIntegral ℤ_[l] (y : Om l) := ⟨q, hm, by
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩
  exact (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).1 h1

theorem norm_pi_lt {K : FinExt l} (bk : BK K) : ‖((Per.θ l (bk.ev X) : OC l) : ℂ_[l])‖ < 1 := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  set φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom) with hφ
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  have hπ1 : ‖π‖ ≤ 1 := norm_OC_le _
  have h0 : bk.Ep.eval₂ φ π = 0 := by
    have h1 : Per.θ l (bk.ev bk.E) = 0 := by
      have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact this
    have h2 := congrArg (PadicComplexInt l).toSubring.subtype h1
    rw [GlobalTheory.BSP.BK.E, ← Polynomial.eval₂_C_X_eq_coe, Polynomial.hom_eval₂, Polynomial.hom_eval₂,
      Polynomial.hom_eval₂, map_zero] at h2
    have hc : (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (bk.ev.comp C)) = φ :=
      RingHom.ext fun w => by simp [hφ, bk.ev_C]
    rw [hc] at h2
    exact h2
  have hcoef : ∀ i < bk.Ep.natDegree, ‖φ (bk.Ep.coeff i)‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro i hi
    obtain ⟨c, hc⟩ := bk.dvd_coeff i hi
    rw [hc, map_mul, map_natCast, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le (Per.θ l (wA l bk.a c)))
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree, map_one, one_mul] at h0
  have h3 : π ^ bk.Ep.natDegree = -∑ i ∈ Finset.range bk.Ep.natDegree, φ (bk.Ep.coeff i) * π ^ i := by
    linear_combination h0
  have h4 : ‖π‖ ^ bk.Ep.natDegree ≤ ‖(l : ℂ_[l])‖ := by
    rw [← norm_pow, h3, norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i hi => ?_
    rw [norm_mul, norm_pow]
    exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ1)).trans
      (hcoef i (Finset.mem_range.1 hi))
  rw [norm_l_C] at h4
  by_contra h5
  push_neg at h5
  have h6 := one_le_pow₀ (n := bk.Ep.natDegree) h5
  have h7 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  linarith

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem step {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ (w : Wq l bk.a) (y' : Om l), y' ∈ K.1 ∧ y' ∈ MaximalUnramifiedExtension l ∧ ‖y'‖ ≤ 1 ∧
      (y : ℂ_[l]) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) + (l : ℂ_[l]) * (y' : ℂ_[l]) := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let r : ↥(OL K) := ⟨⟨y, hyK⟩, mem_OL_of_norm_le K _ hy1⟩
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (bk.str r)
  have hθ : (y : ℂ_[l]) = ((Per.θ l (bk.ev f) : OC l) : ℂ_[l]) := by
    rw [bk.θ_ev r f hf, coe_intToOC]
  set z : Fq l bk.a := (constantCoeff f).coeff 0 with hz
  obtain ⟨u, hu⟩ : (l : Wq l bk.a) ∣ constantCoeff f - WittVector.teichmuller l z := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply, hz]
  set f' : bk.S := PowerSeries.mk fun p => coeff (p + 1) f
  have hfe : f = X * f' + C (constantCoeff f) := eq_X_mul_shift_add_const f
  have hc : constantCoeff f = WittVector.teichmuller l z + (l : Wq l bk.a) * u := by rw [← hu]; ring
  set Ψ : bk.S →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp bk.ev) with hΨ
  have hΨC : ∀ w, Ψ (C w) = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun w => by simp [hΨ, bk.ev_C]
  set π : ℂ_[l] := ((Per.θ l (bk.ev X) : OC l) : ℂ_[l]) with hπ
  set t : ℂ_[l] := ((Per.θ l (wA l bk.a (WittVector.teichmuller l z)) : OC l) : ℂ_[l]) with ht
  set A : ℂ_[l] := ((Per.θ l (wA l bk.a u) : OC l) : ℂ_[l]) with hA
  set B : ℂ_[l] := ((Per.θ l (bk.ev f') : OC l) : ℂ_[l]) with hB
  have hdec : (y : ℂ_[l]) = t + (l : ℂ_[l]) * A + π * B := by
    have e1 : (y : ℂ_[l]) = Ψ f := hθ
    have e2 : Ψ X = π := rfl
    have e3 : Ψ f' = B := rfl
    rw [e1, hfe, hc]
    simp only [map_add (f := _), map_mul, map_natCast, hΨC, e2, e3]
    rw [ht, hA]
    ring

  set rt : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (C (WittVector.teichmuller l z))) with hrt
  have htK : t = (((rt : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← coe_intToOC, ← bk.θ_ev rt (C (WittVector.teichmuller l z)) (by rw [hrt, RingEquiv.apply_symm_apply]), bk.ev_C]
  set yt : Om l := ((rt : ↥K.1) : Om l) with hyt
  have hytK : yt ∈ K.1 := (rt : ↥K.1).2
  have hteich : (WittVector.teichmuller l z) ^ (l ^ bk.a) = WittVector.teichmuller l z := by
    rw [← map_pow, Fq.pow_card]
  have hyt_pow : yt ^ (l ^ bk.a) = yt := by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_pow, ← coeC, ← htK, ht, ← SubmonoidClass.coe_pow, ← map_pow, ← map_pow, hteich]
  have hytU : yt ∈ MaximalUnramifiedExtension l := by
    by_cases h0 : yt = 0
    · rw [h0]; exact zero_mem _
    · have hq : 1 < l ^ bk.a := one_lt_pow_l l bk.a
      refine IntermediateField.subset_adjoin ℚ_[l] _ ⟨l ^ bk.a - 1, by omega, fun h => ?_, ?_⟩
      · exact hl.out.not_dvd_one ((Nat.dvd_sub_iff_right hq.le (dvd_pow_self l (NeZero.ne bk.a))).1 h)
      · apply mul_right_cancel₀ h0
        rw [← pow_succ, Nat.sub_add_cancel hq.le, hyt_pow, one_mul]

  have hdK : y - yt ∈ K.1 := sub_mem hyK hytK
  have hdU : y - yt ∈ MaximalUnramifiedExtension l := sub_mem hyU hytU
  have hdC : ((y - yt : Om l) : ℂ_[l]) = (l : ℂ_[l]) * A + π * B := by
    rw [coeC, map_sub, ← coeC, ← coeC, hdec, ← htK]
    ring
  have hd1 : ‖y - yt‖ < 1 := by
    rw [← PadicComplex.norm_extends, hdC]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul, norm_l_C]
      exact (mul_le_of_le_one_right (by positivity) (norm_OC_le _)).trans_lt (inv_lt_one_of_one_lt₀ hl1)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_OC_le _)).trans_lt (norm_pi_lt bk)
  have hd2 : ‖y - yt‖ ≤ (l : ℝ)⁻¹ := by
    by_cases h0 : y - yt = 0
    · rw [h0, norm_zero]; positivity
    obtain ⟨k, hk⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow hdU h0
    rw [hk] at hd1 ⊢
    have hk0 : k < 0 := by
      by_contra hk0
      push_neg at hk0
      exact absurd hd1 (not_lt.2 (one_le_zpow₀ hl1.le hk0))
    calc (l : ℝ) ^ k ≤ (l : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hl1.le (by omega)
      _ = (l : ℝ)⁻¹ := zpow_neg_one _
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine ⟨WittVector.teichmuller l z, (y - yt) / (l : Om l), div_mem hdK (natCast_mem _ l),
    div_mem hdU (natCast_mem _ l), ?_, ?_⟩
  · rw [norm_div, norm_l_Om, div_inv_eq_mul]
    calc ‖y - yt‖ * l ≤ (l : ℝ)⁻¹ * l := by gcongr
      _ = 1 := inv_mul_cancel₀ (by positivity)
  · have hlC : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
    rw [coeC ((y - yt) / (l : Om l)), map_div₀, map_natCast, ← coeC, hdC, hdec]
    field_simp
    ring

end GlobalTheory.UnrWitt

namespace GlobalTheory.UnrWitt

variable {l : ℕ} [hl : Fact l.Prime]

theorem exists_of_int {K : FinExt l} (bk : BK K) (y : Om l) (hyK : y ∈ K.1) (hyU : y ∈ MaximalUnramifiedExtension l) (hy1 : ‖y‖ ≤ 1) :
    ∃ w : Wq l bk.a, ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = (y : ℂ_[l]) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  let N : Type := {y : Om l // y ∈ K.1 ∧ y ∈ MaximalUnramifiedExtension l ∧ ‖y‖ ≤ 1}
  let Φ : Wq l bk.a →+* ℂ_[l] := (PadicComplexInt l).toSubring.subtype.comp ((Per.θ l).comp (wA l bk.a).toRingHom)
  have hΦ : ∀ w, Φ w = ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) := fun _ => rfl
  have hΦ1 : ∀ w, ‖Φ w‖ ≤ 1 := fun w => norm_OC_le _
  have hs : ∀ v : N, ∃ p : Wq l bk.a × N,
      ((v.1 : Om l) : ℂ_[l]) = Φ p.1 + (l : ℂ_[l]) * ((p.2.1 : Om l) : ℂ_[l]) := by
    intro v
    obtain ⟨w, y', h1, h2, h3, h⟩ := step bk v.1 v.2.1 v.2.2.1 v.2.2.2
    exact ⟨(w, ⟨y', h1, h2, h3⟩), h⟩
  choose g hg using hs
  let ys : ℕ → N := fun k => Nat.rec (motive := fun _ => N) ⟨y, hyK, hyU, hy1⟩ (fun _ v => (g v).2) k
  have hys : ∀ k, ys (k + 1) = (g (ys k)).2 := fun _ => rfl
  let s : ℕ → Wq l bk.a := fun k => ∑ i ∈ Finset.range k, (l : Wq l bk.a) ^ i * (g (ys i)).1
  have hinv : ∀ k, (y : ℂ_[l]) = Φ (s k) + (l : ℂ_[l]) ^ k * (((ys k).1 : Om l) : ℂ_[l]) := by
    intro k
    induction k with
    | zero => simp [s, ys]
    | succ k ih =>
      have h := hg (ys k)
      rw [← hys] at h
      simp only [s, Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
      linear_combination ih + (l : ℂ_[l]) ^ k * h
  have hcau : ∀ m n, m ≤ n → (l : Wq l bk.a) ^ m ∣ s n - s m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have e : s (n + 1) - s m = (s n - s m) + (l : Wq l bk.a) ^ n * (g (ys n)).1 := by
        simp only [s, Finset.sum_range_succ]; ring
      rw [e]
      exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(l : Wq l bk.a)}) s fun {m n} hmn => by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (dvd_sub_comm).1 (hcau m n hmn)
  refine ⟨L, ?_⟩
  rw [← hΦ]
  have hbd : ∀ n : ℕ, ‖(y : ℂ_[l]) - Φ L‖ ≤ ((l : ℝ)⁻¹) ^ n := by
    intro n
    have h := hL n
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨v, hv⟩ := h
    have e : (y : ℂ_[l]) - Φ L = (l : ℂ_[l]) ^ n * (Φ v + (((ys n).1 : Om l) : ℂ_[l])) := by
      have := congrArg Φ hv
      rw [map_sub, map_mul, map_pow, map_natCast] at this
      linear_combination hinv n + this
    rw [e, norm_mul, norm_pow, norm_l_C]
    refine mul_le_of_le_one_right (by positivity) ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hΦ1 v) ?_))
    rw [PadicComplex.norm_extends]
    exact (ys n).2.2.2
  by_contra hne
  have hpos : 0 < ‖(y : ℂ_[l]) - Φ L‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  exact absurd (hbd n) (not_le.2 hn)

theorem exists_pow_mul_eq_theta : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (x : Om l), x ∈ K.1 →
    x ∈ MaximalUnramifiedExtension l → ∃ (n : ℕ) (w : Wq l bk.a),
      ((Per.θ l (wA l bk.a w) : OC l) : ℂ_[l]) = ((((l : Om l) ^ n * x : Om l)) : ℂ_[l]) := by
  intro l _ K bk x hxK hxU
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖x‖ hl1
  have h1 : ‖(l : Om l) ^ n * x‖ ≤ 1 := by
    rw [norm_mul, norm_pow, norm_l_Om, inv_pow]
    rw [inv_mul_le_iff₀ (by positivity), mul_one]
    exact hn.le
  obtain ⟨w, hw⟩ := exists_of_int bk _ (mul_mem (pow_mem (natCast_mem _ l) n) hxK)
    (mul_mem (pow_mem (natCast_mem _ l) n) hxU) h1
  exact ⟨n, w, hw⟩

end GlobalTheory.UnrWitt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitCoeffOfNotXPowDvdLine
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.ResSel

theorem exists_algHom_groupRing {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι] [DecidableEq ι]
    (N : ℕ) [NeZero N] (u : ι → A) (hu : ∀ q, u q ^ N = 1) :
    ∃ th : MonoidAlgebra R (Multiplicative (ι → ZMod N)) →ₐ[R] A,
      ∀ q, th (MonoidAlgebra.of R _ (Multiplicative.ofAdd (Pi.single q 1))) = u q := by
  let e : Multiplicative (ι → ZMod N) →* A :=
    { toFun := fun x => ∏ q, u q ^ (x.toAdd q).val
      map_one' := by simp
      map_mul' := fun x y => by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [toAdd_mul, Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (hu q), pow_add] }
  refine ⟨MonoidAlgebra.lift R A _ e, fun q => ?_⟩
  rw [MonoidAlgebra.lift_of]
  change ∏ p, u p ^ ((Pi.single q (1 : ZMod N) : ι → ZMod N) p).val = u q
  rw [Finset.prod_eq_single q]
  · rw [Pi.single_eq_same, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (hu q), pow_one]
  · intro p _ hp
    rw [Pi.single_eq_of_ne hp, ZMod.val_zero, pow_zero]
  · simp

theorem X_pow_dvd_aeval_line {R K ι : Type} [CommRing R] [Field K] [Algebra R K] (b : ι → K) (n : ℕ)
    (F : MvPolynomial ι R) (h : ∀ m : ι →₀ ℕ, m.degree < n → algebraMap R K (F.coeff m) = 0) :
    (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) F := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.dvd_sum fun m _ => ?_
  by_cases hm : m.degree < n
  · rw [Polynomial.algebraMap_apply, h m hm, map_zero, zero_mul]
    exact dvd_zero _
  · refine Dvd.dvd.mul_left ?_ _
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ (not_lt.1 hm)) _

theorem exists_unit_coeff_of_not_dvd_line (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂)
    (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (M : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K]
    [Algebra (X.O0 i) K] (hK : IsRes i K) (b : ι → K) (n : ℕ) (hn : n ≤ X.l i ^ M) (F G : MvPolynomial ι (X.O0 i))
    (hFG : toLam X i M ι F = toLam X i M ι G)
    (hG : ¬ (Polynomial.X : Polynomial K) ^ n ∣ MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X) G) :
    ∃ m : ι →₀ ℕ, m.degree < n ∧ IsUnit (F.coeff m) := by
  classical
  by_contra hcon
  apply hG
  have hF := X_pow_dvd_aeval_line b n F fun m hm => hK _ (fun hu => hcon ⟨m, hm, hu⟩)
  have hp := X.lPrime i
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu => by
    have := hu.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at this
    exact X.O_l i this
  have hlK : ((X.l i : ℕ) : K) = 0 := by
    have := hK _ hl0
    rwa [map_natCast] at this
  have : CharP K (X.l i) := (CharP.charP_iff_prime_eq_zero hp.out).2 hlK
  have : NeZero (X.l i ^ M) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  let I : Ideal (Polynomial K) := Ideal.span {Polynomial.X ^ n}
  let π : Polynomial K →ₐ[X.O0 i] (Polynomial K ⧸ I) := Ideal.Quotient.mkₐ (X.O0 i) I
  have hu : ∀ q, (π (Polynomial.C (b q) * Polynomial.X + 1)) ^ (X.l i ^ M) = 1 := fun q => by
    rw [← map_pow, add_pow_char_pow, one_pow, map_add (f := _), map_one, add_eq_right]
    refine Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 ?_)
    rw [mul_pow]
    exact Dvd.dvd.mul_left (pow_dvd_pow _ hn) _
  obtain ⟨th, hth⟩ := exists_algHom_groupRing (R := X.O0 i) (X.l i ^ M) _ hu
  have hc : th.comp (toLam X i M ι) =
      π.comp (MvPolynomial.aeval (fun q => Polynomial.C (b q) * Polynomial.X)) := by
    refine MvPolynomial.algHom_ext fun q => ?_
    have := hth q
    simp only [AlgHom.comp_apply, toLam, MvPolynomial.aeval_X, map_sub, map_one]
    rw [sub_eq_iff_eq_add, ← map_one π, ← map_add (f := _), ← this]
  have h1 := DFunLike.congr_fun hc F
  have h2 := DFunLike.congr_fun hc G
  simp only [AlgHom.comp_apply] at h1 h2
  rw [hFG, h2] at h1
  have h3 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  simpa using dvd_add h3 hF

end GlobalTheory.ResSel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtensionRuleStmt
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
open TensorProduct

noncomputable section

namespace GlobalTheory.ExtDict

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
    [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]

theorem exists_ext_cocycle [IsTopologicalRing LL] {T Y Z : LocLat G Qp LL O}
    (ι : LatHom T.L Y.L) (π : LatHom Y.L Z.L) (hs : IsSESLat (Qp := Qp) ι π)
    (hZ : ∀ g z, Z.ρ g z = z) (x : ↥Y.L.T) :
    ∃ c : ↥(latticeCocycles T.L), ∀ g, ι.f ((c : G → T.V) g) = Y.ρ g (x : Y.V) - (x : Y.V) := by
  obtain ⟨h1, -, -, h4, h5⟩ := hs
  obtain ⟨r, hr⟩ := ι.f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 h1)
  have hr' : ∀ y, r (ι.f y) = y := fun y => LinearMap.congr_fun hr y
  have hval : ∀ g, ι.f (r (Y.ρ g (x : Y.V) - (x : Y.V))) = Y.ρ g (x : Y.V) - (x : Y.V) := by
    intro g
    obtain ⟨y, hy⟩ := (h4 (Y.ρ g (x : Y.V) - (x : Y.V))).1 (by rw [map_sub, π.equiv, hZ, sub_self])
    rw [← hy, hr']
  have : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  have hrc : Continuous r := IsModuleTopology.continuous_of_linearMap r
  have : IsTopologicalAddGroup Y.V := IsModuleTopology.topologicalAddGroup LL Y.V
  refine ⟨⟨fun g => r (Y.ρ g (x : Y.V) - (x : Y.V)), ⟨?_, fun g h => ?_⟩, fun g _ => ?_⟩, hval⟩
  · exact hrc.comp ((Y.cont x).sub continuous_const)
  · apply h1
    rw [map_add (f := _), ι.equiv, hval, hval, hval, map_mul, Module.End.mul_apply, map_sub]
    abel
  · apply h5
    change ι.f (r _) ∈ _
    rw [hval]
    exact Y.L.T.sub_mem (Y.actT g x).2 x.2

variable {K₀ K : Type} [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem exists_unit_fixed (E : EtTie W RA RW inclR φR gR πA) (u : ↥W.one.L.T) :
    ∃ e₀ ∈ tableLineDegreeTwo.fixDD W W.one, E.jD W.one e₀ = (1 : RW) ⊗ₜ[O] u := by
  obtain ⟨e₁, f₀, hf₀, hj, -⟩ := E.one_e
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hf₀ ▸ Submodule.mem_top : u ∈ Submodule.span O {f₀})
  have hje : E.jD W.one (c • e₁) = (1 : RW) ⊗ₜ[O] u := by
    rw [map_smul, hj, ← hc, TensorProduct.tmul_smul]
  have hφ : W.φD W.one (c • e₁) = c • e₁ := by
    apply E.jD_inj
    rw [E.jD_φ, hje]
    simp [TWmap]
  have hγ : ∀ g, W.γD W.one g (c • e₁) = c • e₁ := by
    intro g
    obtain ⟨g, rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    have hact : W.one.actT g u = u := Subtype.ext (W.one_triv g u)
    rw [E.jD_act, hje]
    simp [TWact, hact]
  refine ⟨c • e₁, ⟨⟨?_, ?_⟩, ?_⟩, hje⟩
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 hφ)
  · exact LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ _))
  · exact (Submodule.mem_iInf _).2 fun δ => (Submodule.mem_iInf _).2 fun _ =>
      LinearMap.mem_ker.2 (sub_eq_zero.2 (hγ δ))

end Generic

theorem herrExt_of_dense (S : LocalSituation.Sit) (E : S.Comparison₂) [IsTopologicalRing S.LL] [T2Space S.LL]
    (hR : Function.Injective (algebraMap S.O S.RW))
    (hDel : S.PD.p = 2 → S.W.DelF = {1})
    (hdens : ∀ A : Subgroup S.G, IsClosed (A : Set S.G) → (∀ g, S.W.resΓ g ∈ S.W.DelF → g ∈ A) →
      (∀ g, S.W.resΓ g = S.W.gamK → g ∈ A) → ∀ g, g ∈ A) : tableLineDegreeTwo.HerrExt S.W E := by
  refine ⟨exists_unit_fixed E, fun T Tp ι π hs x u hu e hδ he p h1 h2 => ?_⟩
  obtain ⟨c, hc⟩ := exists_ext_cocycle ι π hs S.W.one_triv x
  exact ⟨c, (dict_of_dense S E hR hDel hdens T Tp _ ι π hs x u e hu he hδ p h1 h2 c hc).symm, hc⟩

theorem extension_rule (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    InvariantsGenerators.HerrExtensionEtale D HW F := by
  intro l _ K LL hA
  let S := LocalSituation.sit D.loc HW l (D.locA l) K 1 LL hA.2.2
  let E : S.Comparison₂ := ((F l).E K 1 LL hA.2.2).tie
  have : IsTopologicalRing S.LL := inferInstanceAs (IsTopologicalRing ↥LL.1.toSubring)
  have : T2Space S.LL := inferInstanceAs (T2Space ↥LL.1)
  exact herrExt_of_dense S E (algebraMap_RW_injective LL)
    (fun h2 => absurd (((D.loc l).PD_p K).symm.trans h2) hA.2.1)
    (dense_DelF_gamK (D.loc l) S.W (D.locA l) fun h2 => absurd h2 hA.2.1)

end GlobalTheory.ExtDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobRowIntegral
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.HeightInt

theorem frob_row_integral : ∀ (l : ℕ) [Fact l.Prime] (κ : Type) [Fintype κ] (x : κ → WCb l)
    (c : κ → κ → Ainf l), (∀ j, frobW l (x j) = ∑ i, x i * inclW l (c i j)) →
    ∀ j, ∃ a : Ainf l, x j = inclW l a := by
  intro l _ κ _ x c h j
  let Z : Matrix Unit κ (WCb l) := Matrix.of fun _ i => x i
  have hZ : Z.map (frobW l) = (1 : Matrix Unit Unit (Ainf l)).map (inclW l) * Z *
      (Matrix.of c).map (inclW l) + (0 : Matrix Unit κ (Ainf l)).map (inclW l) := by
    ext1 u k
    simp only [Matrix.map_apply, Matrix.map_one (inclW l) (map_zero _) (map_one _), Matrix.one_mul,
      Matrix.map_zero (inclW l) (map_zero _), add_zero, Matrix.mul_apply, Matrix.of_apply, Z]
    exact h k
  obtain ⟨a, ha⟩ := GlobalTheory.FrobInt.frobenius_integrality l Unit κ Z 1 (Matrix.of c) 0 hZ () j
  exact ⟨a, ha.symm⟩

end GlobalTheory.HeightInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchangeStatement
section
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → ∀ χ : Gn g N → ℂ, IsClass χ → tr (eJ g N k s ψ) χ = tr (eJ' g N k ψ) χ := by
  first | exact @GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | exact GlobalTheory.GLq.tr_eJ_eq_tr_eJ' | (intros; apply GlobalTheory.GLq.tr_eJ_eq_tr_eJ' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1LatticeIndexGrowthStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H1_lattice_index_growth_of_tateDuality_eulerChar : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), Nat.card (QuotientCohomology LA _ hI) = Nat.card {x : ↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T) // ∀ g, actQ LA _ hI g x = x} * Nat.card {x : ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T) // ∀ g, actQ LA' _ hI' g x = x} * Nat.card (O ⧸ Ideal.span {((l : ℕ) : O)}) ^ (r * (finrank ℚ_[l] ↥K.1 * finrank LL A.V)) := by
  first | exact @GlobalTheory.EulerLevel.card_H1Q_eq | exact GlobalTheory.EulerLevel.card_H1Q_eq | (intros; apply GlobalTheory.EulerLevel.card_H1Q_eq <;> assumption)
end

