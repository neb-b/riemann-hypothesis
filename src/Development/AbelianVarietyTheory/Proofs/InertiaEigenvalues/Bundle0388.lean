module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerObstructionLeResidualSelmerSimpleExtension
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0366
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroLowCoeffThreeNilpotents
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem exists_pow_mul_pow_mul_pow_dvd_prod_pow {B : Type} [CommRing B] {ι : Type} (t x y : B)
    (ξ : ι → B) (hξ : ∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) (u : ι → ℕ) (s : Finset ι) :
    ∃ a b c : ℕ, a + b + c = ∑ q ∈ s, u q ∧ t ^ a * x ^ b * y ^ c ∣ ∏ q ∈ s, ξ q ^ u q := by
  classical
  induction s using Finset.induction_on
  case empty => exact ⟨0, 0, 0, by simp, by simp⟩
  case insert q s hq ih =>
    obtain ⟨a, b, c, habc, hd⟩ := ih
    rw [Finset.sum_insert hq, Finset.prod_insert hq]
    rcases hξ q with ⟨r, hr⟩ | hx | hy
    · refine ⟨u q + a, b, c, by omega, ?_⟩
      have h := mul_dvd_mul (dvd_mul_right (t ^ u q) (r ^ u q)) hd
      rw [hr, mul_pow]
      convert h using 1
      ring
    · refine ⟨a, u q + b, c, by omega, ?_⟩
      have h := mul_dvd_mul_left (x ^ u q) hd
      rw [hx]
      convert h using 1
      ring
    · refine ⟨a, b, u q + c, by omega, ?_⟩
      have h := mul_dvd_mul_left (y ^ u q) hd
      rw [hy]
      convert h using 1
      ring

theorem aeval_eq_zero_of_low_coeff_of_three_nilpotent :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t x y : B) (K m : ℕ)
      (ξ : ι → B) (F : MvPolynomial ι O), t ^ K = 0 → x * x = 0 → y ^ m = 0 →
      (∀ q, t ∣ ξ q ∨ ξ q = x ∨ ξ q = y) →
      (∀ u : ι →₀ ℕ, u.degree < K + m → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t x y K m ξ F ht hx hy hξ hF
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [F.as_sum, map_sum]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hu : u.degree < K + m
  · rw [hF u hu, zero_mul]
  · obtain ⟨a, b, c, habc, hd⟩ := exists_pow_mul_pow_mul_pow_dvd_prod_pow t x y ξ hξ u u.support
    have hdeg : u.degree = ∑ q ∈ u.support, u q := rfl
    have hzero : t ^ a * x ^ b * y ^ c = 0 := by
      by_cases hc : m ≤ c
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hc
        rw [pow_add, hy]
        simp
      · by_cases hb : 2 ≤ b
        · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hb
          rw [pow_add, pow_two, hx]
          simp
        · have hK : K ≤ a := by omega
          obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hK
          rw [pow_add, ht]
          simp
    rw [hzero, zero_dvd_iff] at hd
    rw [Finsupp.prod]
    simp only [hd, mul_zero]

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BkOnLeMapOfSurjective
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem tors_of_finite_local (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [show x = 0 from hx, zero_smul]

theorem bkOn_le_map_of_surjective : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → Kills i A → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y₂ : Type) [AddCommGroup Y₂] [Module A Y₂] [TopologicalSpace Y₂] [DiscreteTopology Y₂] (f : Y →ₗ[A] Y₂), Function.Surjective f → ∀ v, bkOn bkP i (Tgl i s) κ Y₂ v ≤ (bkOn bkP i (Tgl i s) κ Y v).map (h1MapSubgroup (Tgl i s) κ (DecV N v) f) := by
  intro D N X bkP i s A _ _ _ _ κ Q hS _ Y _ _ _ _ Y₂ _ _ _ _ f hf v
  haveI := hS.2.1
  exact GlobalTheory.SelObstruction.bkOn_onto bkP i s κ hS.2.2.2.2.2.1 (tors_of_finite_local A Y) f hf v

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem discAinf_isDomain : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    IsDomain (bk.DA ρ) ∧ (∀ x y : bk.DA ρ, (ρ : ℝ) ^ 2 * (‖x‖ * ‖y‖) ≤ ‖x * y‖) ∧
      ∀ a : bk.DA ρ, a ≠ 0 → ∃ C : ℝ, ∀ y, ‖y‖ ≤ C * ‖a * y‖ := by
  intro l _ K bk ρ h0 h1
  obtain ⟨N, hmul, hadd, hl, hle, hge⟩ := _root_.GlobalTheory.DiscGauss.exists_gauss_disc l K bk ρ h0 h1
  have hρ : (0 : ℝ) < (ρ : ℝ) := h0
  obtain ⟨hdom, hnorm⟩ := GlobalTheory.T.isDomain_closedDiscGaugeCompletion_of_equiv_norm l (Ainf l) (bk.ev X) ρ N (ρ : ℝ) hρ hmul hadd hl hle hge
  refine ⟨hdom, hnorm, fun a ha => ⟨((ρ : ℝ) ^ 2 * ‖a‖)⁻¹, fun y => ?_⟩⟩
  have hpos : 0 < (ρ : ℝ) ^ 2 * ‖a‖ := mul_pos (pow_pos hρ 2) (norm_pos_iff.2 ha)
  have h := hnorm a y
  rw [← mul_assoc] at h
  calc ‖y‖ = ((ρ : ℝ) ^ 2 * ‖a‖)⁻¹ * ((ρ : ℝ) ^ 2 * ‖a‖ * ‖y‖) := by field_simp
    _ ≤ ((ρ : ℝ) ^ 2 * ‖a‖)⁻¹ * ‖a * y‖ := mul_le_mul_of_nonneg_left h (inv_nonneg.2 hpos.le)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaNextCoeffThetaMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaStep

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (a : Ainf l) : Per.θ l a = 0 ↔ bk.ev bk.E ∣ a := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem dvd_of_dvd_lpow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : OC l)) ^ n ≠ 0 := pow_ne_zero _ (fun h0 =>
    GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h0))
  exact (mul_eq_zero.mp h).resolve_left hne

theorem pow_dvd_of_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_lpow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_lpow (i n : ℕ) (a : Ainf l) (h : bk.ev bk.E ^ i ∣ (l : Ainf l) ^ n * a) :
    bk.ev bk.E ^ i ∣ a := by
  induction n generalizing a with
  | zero => simpa using h
  | succ n ih =>
    apply ih
    apply pow_dvd_of_l_mul bk i
    rw [← mul_assoc, ← pow_succ']
    exact h

end GlobalTheory.BKLim.BetaStep


open GlobalTheory.BKLim.BetaStep in
theorem GlobalTheory.BKLim.beta_step : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ) (g : ↥(GK K)) (w : Ainf l), Per.σA (g : GQ l) (bk.ev bk.E) = bk.ev bk.E * w → ∀ (m k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β → ∀ (i n : ℕ), i + 1 ≤ m → ∀ γ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ n • γ) p q) → ∃ δ : Matrix (Fin d) (Fin d) bk.S, (∀ p q, bk.E ^ (i + 1) ∣ (β - (l : bk.S) ^ n • γ - bk.E ^ i • δ) p q) ∧ ∀ p q, ∃ y : OC l, Per.θ l (bk.ev (δ p q)) * (Per.θ l w ^ i - 1) = (l : OC l) ^ n * y := by
  intro l _ K bk N d ρ F g w hw m k β hβ i n him γ hγ
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  choose δ hδ using hγ
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hδ
  refine ⟨Matrix.of δ, fun p q => ?_, fun p q => ?_⟩
  · simp [Matrix.sub_apply, Matrix.smul_apply, hδ]
  set P : Fin d → Fin d → Ainf l := fun a c => WittVector.frobenius (F.ε g a c) with hPdef
  set σ := Per.σA (g : GQ l)
  have hent : ∀ a b, bk.ev bk.E ^ m ∣ ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) := by
    intro a b
    have := hβ.2 g a b
    simpa [Matrix.sub_apply, Matrix.mul_apply, Matrix.map_apply, hPdef] using this
  have hm : 0 < m := by omega
  have hθβ : ∀ c b, Per.θ l (bk.ev (β c b)) = (l : OC l) ^ k * (if c = b then 1 else 0) := by
    intro c b
    have h2 : Per.θ l (bk.ev ((β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) c b)) = 0 :=
      (theta_eq_zero_iff bk _).2 (map_dvd bk.ev (hβ.1 c b))
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub, map_mul, map_pow,
      map_natCast] at h2
    rw [sub_eq_zero] at h2
    rw [h2]; split_ifs <;> simp
  have hlOC : ((l : ℕ) : OC l) ≠ 0 := fun h =>
    GlobalTheory.RingBasics.p_ne_zero (p := l) (by simpa using congrArg Subtype.val h)
  have hP : ∀ a c, Per.θ l (P a c) = if a = c then 1 else 0 := by
    intro a b
    have h := (theta_eq_zero_iff bk _).2 ((dvd_pow_self _ hm.ne').trans (hent a b))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [σ, map_sub, map_sum, map_mul, GlobalTheory.BKLim.BetaBd.θ_σA_ev, hθβ, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [sub_eq_zero] at h
    have hl := pow_ne_zero k hlOC
    apply mul_right_cancel₀ hl
    rw [h]; split_ifs <;> simp

  have hβe : ∀ c b, β c b = (l : bk.S) ^ n * γ c b + bk.E ^ i * δ c b := fun c b => by
    rw [← hδ c b]; ring
  have hσE : σ (bk.ev bk.E) ^ i = bk.ev bk.E ^ i * w ^ i := by rw [hw, mul_pow]
  have hD : ∀ a b, ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) =
      (l : Ainf l) ^ n * (∑ c, P a c * σ (bk.ev (γ c b)) - bk.ev (γ a b)) +
      bk.ev bk.E ^ i * (w ^ i * ∑ c, P a c * σ (bk.ev (δ c b)) - bk.ev (δ a b)) := by
    intro a b
    have e1 : ∀ c, P a c * σ (bk.ev (β c b)) = (l : Ainf l) ^ n * (P a c * σ (bk.ev (γ c b))) +
        bk.ev bk.E ^ i * (w ^ i * (P a c * σ (bk.ev (δ c b)))) := by
      intro c
      rw [hβe]
      simp only [map_add (f := _), map_mul, map_pow, map_natCast, hσE]
      ring
    rw [Finset.sum_congr rfl (fun c _ => e1 c), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hβe a b]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  have hDγ : ∀ a b, bk.ev bk.E ^ i ∣ ∑ c, P a c * σ (bk.ev (γ c b)) - bk.ev (γ a b) := by
    intro a b
    apply pow_dvd_of_lpow bk i n
    have h1 : bk.ev bk.E ^ i ∣ ∑ c, P a c * σ (bk.ev (β c b)) - bk.ev (β a b) :=
      (pow_dvd_pow _ (by omega)).trans (hent a b)
    rw [hD] at h1
    exact (dvd_add_left (dvd_mul_right _ _)).1 h1
  choose η hη using hDγ
  have hX : bk.ev bk.E ∣ (l : Ainf l) ^ n * η p q +
      (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q)) := by
    have e : bk.ev bk.E ^ i * ((l : Ainf l) ^ n * η p q +
        (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q))) =
        ∑ c, P p c * σ (bk.ev (β c q)) - bk.ev (β p q) := by
      rw [hD, hη]; ring
    have h1 : bk.ev bk.E ^ i * bk.ev bk.E ∣ bk.ev bk.E ^ i * ((l : Ainf l) ^ n * η p q +
        (w ^ i * ∑ c, P p c * σ (bk.ev (δ c q)) - bk.ev (δ p q))) := by
      rw [e, ← pow_succ]
      exact (pow_dvd_pow _ him).trans (hent p q)
    exact (mul_dvd_mul_iff_left (pow_ne_zero i (evE_ne_zero bk))).1 h1
  rw [← theta_eq_zero_iff] at hX
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [σ, map_add (f := _), map_sub, map_mul, map_pow, map_natCast, map_sum, GlobalTheory.BKLim.BetaBd.θ_σA_ev, hP,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at hX
  refine ⟨-Per.θ l (η p q), ?_⟩
  simp only [Matrix.of_apply]
  linear_combination hX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscRestrictInjective
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem disc_restrict_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ ρ' : ℝ≥0), 0 < ρ' → ρ' ≤ ρ →
    ρ < 1 → ∀ R : bk.DS ρ →+* bk.DS ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id bk.S) R → Function.Injective R := by
  intro l _ K bk ρ ρ' h0 hle h1 R hR
  have hρ0 : 0 < ρ := h0.trans_le hle
  obtain ⟨a, ha1, ha2, ha3, -⟩ := _root_.GlobalTheory.BSP.DiscSer.exists_coeff_disc l K bk ρ hρ0 h1
  obtain ⟨a', ha1', ha2', -, -⟩ := _root_.GlobalTheory.BSP.DiscSer.exists_coeff_disc l K bk ρ' h0 (hle.trans_lt h1)
  obtain ⟨-, -, hdense, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ
  have htors : ∀ z : Disc l (0 : Wq l bk.a) 1, l • z = 0 → z = 0 := by
    intro z hz
    rw [nsmul_eq_mul] at hz
    exact ((isUnit_l_disc l (0 : Wq l bk.a) 1).mul_right_eq_zero).1 hz
  have hbound : ∀ (σ : ℝ≥0), 0 < σ → ∀ (b : bk.DS σ →+ Disc l (0 : Wq l bk.a) 1) (n : ℕ),
      (∀ y, ‖b y‖ * (σ : ℝ) ^ n ≤ ‖y‖) → ∀ y, ‖b y‖ ≤ ((σ : ℝ) ^ n)⁻¹ * ‖y‖ := by
    intro σ hσ b n hb y
    have hp : (0 : ℝ) < (σ : ℝ) ^ n := pow_pos (by exact_mod_cast hσ) n
    rw [inv_mul_eq_div, le_div_iff₀ hp]
    exact hb y
  have hcoef : ∀ n y, a' n (R y) = a n y := by
    intro n
    have e := hdense (Disc l (0 : Wq l bk.a) 1) htors ((a' n).comp R.toAddMonoidHom) (a n)
      (AddMonoidHomClass.continuous_of_bound _ (((ρ' : ℝ) ^ n)⁻¹) fun y =>
        (hbound ρ' h0 (a' n) n (ha2' n) (R y)).trans
          (mul_le_mul_of_nonneg_left (hR.norm_le y) (inv_nonneg.2 (by positivity))))
      (AddMonoidHomClass.continuous_of_bound _ (((ρ : ℝ) ^ n)⁻¹) (hbound ρ hρ0 (a n) n (ha2 n)))
      (fun x => by
        change a' n (R (toDisc l (X : bk.S) ρ x)) = a n (toDisc l (X : bk.S) ρ x)
        rw [hR.ext x, RingHom.id_apply, ha1', ha1])
    intro y
    exact DFunLike.congr_fun e y
  refine (injective_iff_map_eq_zero R).2 fun y hy => ?_
  have h := ha3 y 0 le_rfl fun n => by rw [← hcoef n y, hy, map_zero, norm_zero, zero_mul]
  exact norm_le_zero_iff.1 h

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDatumStructureMapInjective
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bk_ev_injective : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), Function.Injective bk.ev := by
  intro l _ K bk
  obtain ⟨ι, ⟨tb⟩⟩ := _root_.GlobalTheory.BSP.AinfTopBasis.main l K bk
  intro a a' h
  have h1 : tb.c tb.i₀ 1 = 1 := by simpa [tb.b_i₀] using tb.c_self tb.i₀
  have key : ∀ x, tb.c tb.i₀ (bk.ev x) = x := fun x => by
    have := tb.c_mul tb.i₀ x (tb.b tb.i₀)
    rw [tb.b_i₀, mul_one, h1, mul_one] at this
    exact this
  rw [← key a, ← key a', h]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFrameIsCrOfLinkedTower
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.CrLimit

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem exists_smul_of_dvd {R : Type} [CommRing R] {m n : Type} (c : R) (M : Matrix m n R)
    (h : ∀ i j, c ∣ M i j) : ∃ M' : Matrix m n R, M = c • M' := by
  choose M' hM' using h
  exact ⟨Matrix.of M', by ext i j; simp [hM']⟩

theorem ev_X_dvd_gal (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    bk.ev X ∣ Per.σA (g : GQ l) (bk.ev s) - bk.ev s := by
  obtain ⟨c, hc⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  obtain ⟨t, w, e⟩ : ∃ (t : bk.S) (w : Wq l bk.a), s = X * t + C w := ⟨_, _, eq_X_mul_shift_add_const s⟩
  subst e
  rw [map_add (f := _), map_mul, map_add (f := _), map_mul, bk.ev_C, bk.gal_w, hc]
  exact ⟨c * Per.σA (g : GQ l) (bk.ev t) - bk.ev t, by ring⟩

theorem isUnit_inclW_ev_X (bk : BK K) : IsUnit (inclW l (bk.ev X)) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [bk.ev_X, inclW, WittVector.map_teichmuller, WittVector.teichmuller_coeff_zero]
  exact (map_ne_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).2 (GlobalTheory.BSP.FlatDisc.flat_ne_zero bk)

end GlobalTheory.BKLim.CrLimit

namespace GlobalTheory.BKLim.CrLimit

theorem isCr_of_link : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (tw : Tower ρ) (F : ∀ n, Frame bk N (tw.d' n) fun g => (tw.ρ' n g).val) (F₀ : Frame bk N d fun g => (ρ g).val) (r : ℕ), (∀ n, ∃ m, n ≤ m ∧ Link bk F₀.T (F m).T (tw.Pi m) n r) → (∀ n, (F n).IsCr) → F₀.IsCr := by
  intro l _ K bk d N ρ tw F F₀ r hlink hcr g i j
  suffices hx : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * inclW l ((F₀.ε g - 1) i j) -
      inclW l (bk.ev X * a) by
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.AinfSat.mem_ideal_of_saturated l (bk.ev X) (isUnit_inclW_ev_X bk) r (inclW l ((F₀.ε g - 1) i j)) hx
    exact ⟨a, inclW_injective ha⟩
  intro n
  obtain ⟨m, hnm, R, G, hT, hRG⟩ := hlink n
  have hk := _root_.GlobalTheory.BKLim.LinkCocycle.main l K bk N N d (tw.d' m) n (fun g => (ρ g).val) (fun g => (tw.ρ' m g).val) F₀ (F m)
    (tw.Pi m) R (fun g i j => (pow_dvd_pow _ hnm).trans ((tw.onto m).equi g i j)) hT
  set σ := Per.σA (g : GQ l) with hσ
  set A := R.map bk.ev with hA
  set B := G.map bk.ev with hB
  set ε₀ := F₀.ε g with hε₀
  set ε' := (F m).ε g with hε'
  obtain ⟨D, hD⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (ε₀ * A.map σ - A * ε') (hk g)
  obtain ⟨P, hP⟩ := exists_smul_of_dvd ((l : Ainf l) ^ n) (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)))
    (fun i j => by
      have h := map_dvd bk.ev (hRG i j)
      have e : (A * B - (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l))) i j =
          bk.ev ((R * G - (l : bk.S) ^ r • (1 : Matrix (Fin d) (Fin d) bk.S)) i j) := by
        rw [hA, hB, ← Matrix.map_mul]
        simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_sub,
          map_mul, map_pow, map_natCast]
        split_ifs <;> simp
      rw [e]
      simpa only [map_pow, map_natCast] using h)
  obtain ⟨Z1, hZ1⟩ := exists_smul_of_dvd (bk.ev X) (ε' - 1) (hcr m g)
  obtain ⟨Z2, hZ2⟩ := exists_smul_of_dvd (bk.ev X) (B.map σ - B) (fun i j => by
    simpa only [hB, Matrix.sub_apply, Matrix.map_apply] using ev_X_dvd_gal bk g (G i j))
  have h1 : ε₀ * A.map σ = A * ε' + (l : Ainf l) ^ n • D := (sub_eq_iff_eq_add').1 hD
  have h2 : A * B = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P :=
    (sub_eq_iff_eq_add').1 hP
  have h3 : A.map σ * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P.map σ := by
    rw [← Matrix.map_mul, h2]
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, map_add (f := _), map_mul,
      map_pow, map_natCast]
    split_ifs <;> simp
  have h4 : ε' = 1 + bk.ev X • Z1 := (sub_eq_iff_eq_add').1 hZ1
  have h5 : B.map σ = B + bk.ev X • Z2 := (sub_eq_iff_eq_add').1 hZ2
  have e1 : ε₀ * (A.map σ * B.map σ) = (l : Ainf l) ^ r • ε₀ + (l : Ainf l) ^ n • (ε₀ * P.map σ) := by
    rw [h3, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
  have e2 : ε₀ * (A.map σ * B.map σ) = A * ε' * B.map σ + (l : Ainf l) ^ n • (D * B.map σ) := by
    rw [← Matrix.mul_assoc, h1, Matrix.add_mul, Matrix.smul_mul]
  have e3 : A * ε' * B.map σ = A * B.map σ + bk.ev X • (A * Z1 * B.map σ) := by
    rw [h4, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have e4 : A * B.map σ = (l : Ainf l) ^ r • (1 : Matrix (Fin d) (Fin d) (Ainf l)) + (l : Ainf l) ^ n • P +
      bk.ev X • (A * Z2) := by
    rw [h5, Matrix.mul_add, h2, Matrix.mul_smul]
  have key : (l : Ainf l) ^ r • (ε₀ - 1) = (l : Ainf l) ^ n • (P + D * B.map σ - ε₀ * P.map σ) +
      bk.ev X • (A * Z1 * B.map σ + A * Z2) := by
    have h := e1.symm.trans e2
    rw [e3, e4] at h
    refine eq_of_sub_eq_zero ?_
    rw [← sub_eq_zero.2 h, smul_sub, smul_sub, smul_add, smul_add]
    abel
  have hij := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hij
  refine ⟨(A * Z1 * B.map σ + A * Z2) i j, ?_⟩
  have hd : (l : Ainf l) ^ n ∣ (l : Ainf l) ^ r * (ε₀ - 1) i j - bk.ev X * (A * Z1 * B.map σ + A * Z2) i j :=
    ⟨(P + D * B.map σ - ε₀ * P.map σ) i j, by
      simp only [Matrix.add_apply, Matrix.sub_apply] at hij ⊢
      linear_combination hij⟩
  simpa only [map_sub, map_mul, map_pow, map_natCast] using map_dvd (inclW l) hd

end GlobalTheory.BKLim.CrLimit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEModPrimeLaurentFieldStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ y : Cb l, y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) ↔ ∃ (m : ℕ) (s : bk.S), algebraMap (OCb l) (Cb l) bk.flat ^ m * y = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0)) ∧ (∀ s : bk.S, bk.evW s ∈ bk.OE) ∧ IsUnit (bk.evW X) ∧ (∀ w : WCb l, bk.evW X * w ∈ bk.OE → w ∈ bk.OE) ∧ ∀ y ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)), y⁻¹ ∈ bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := by
  first | exact @GlobalTheory.BSP.oe_mod_l | exact GlobalTheory.BSP.oe_mod_l | (intros; apply GlobalTheory.BSP.oe_mod_l <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPeriodMatrixOfFinrankStatement
section
open TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodMatrix_of_finrank_alt : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [IsDomain B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n F), (∀ g, (A g).det ≠ 0) → (∀ g (c : E), act g (algebraMap E B c) = algebraMap E B c) → (∀ b b' : B, b ≠ 0 → (∀ g, b * act g b' = act g b * b') → ∃ c : E, b' = algebraMap E B c * b) → (∀ b : B, b ≠ 0 → (∀ g, ∃ x : F, act g b = algebraMap F B x * b) → IsUnit b) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, ((A g).map (algebraMap F B)).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n → ∃ Q : GL n B, ∀ g, (A g).map (algebraMap F B) * (Q : Matrix n n B).map (act g) = Q := by
  first | exact @GlobalTheory.RegularRing.exists_periodMatrix_of_finrank | exact GlobalTheory.RegularRing.exists_periodMatrix_of_finrank | (intros; apply GlobalTheory.RegularRing.exists_periodMatrix_of_finrank <;> assumption)
end

