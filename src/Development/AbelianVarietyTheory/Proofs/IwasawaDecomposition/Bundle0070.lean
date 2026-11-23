module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TeichmullerTiltMinusOneDvdOfThetaFrobeniusZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFixedEqPadicInt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusEigenFilEqQlMulTPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.MemLoc.FixR

theorem step_abs {R A K : Type} [CommRing R] [CommRing A] [IsDomain A] [Field K]
    (i : R →+* A) (f : R →+* R) (φ : A →+* A) (Θ : A →+* K) (p : A) (hp : Θ p ≠ 0)
    (hφp : φ p = p) (hf : ∀ a, φ (i a) = i (f a))
    (μ : R) (hμ : ∀ n, Θ (i (f^[n] μ)) = 0)
    (hI : ∀ a : R, (∀ n, Θ (i (f^[n] a)) = 0) → μ ∣ a)
    (w : A) (m : ℕ) (hw : p * w = i μ ^ (m + 1))
    (himg : ∀ y, ∃ a z, φ y = i a + w * z)
    (t u : A) (hu : IsUnit u) (ht : t = i μ * u) (ht0 : t ≠ 0) (hφt : φ t = p * t)
    (r : ℕ) (x : A) (hx : φ x = p ^ (r + 1) * x) (hx0 : Θ x = 0) :
    ∃ x', p ^ (r + 2) * x = t * x' ∧ φ x' = p ^ r * x' := by
  have hit : ∀ n a, φ^[n] (i a) = i (f^[n] a) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => intro a; rw [Function.iterate_succ_apply, hf, ih, Function.iterate_succ_apply]
  have hpn : ∀ n, (φ ^ n) p = p := by
    intro n
    rw [RingHom.coe_pow]
    exact Function.iterate_fixed hφp n
  have hit' : ∀ n a, (φ ^ n) (i a) = i (f^[n] a) := by
    intro n a
    rw [RingHom.coe_pow]; exact hit n a
  have hxn : ∀ n, Θ ((φ ^ n) x) = 0 := by
    intro n
    induction n with
    | zero => simpa using hx0
    | succ n ih =>
      rw [pow_succ, RingHom.mul_def, RingHom.comp_apply, hx]
      simp only [map_mul, ih, mul_zero]
  have hwn : ∀ n, Θ ((φ ^ n) w) = 0 := by
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) hw
    simp only [map_mul, map_pow, hpn, hit', hμ] at this
    simpa [hp] using this
  obtain ⟨a, z, haz⟩ := himg x
  obtain ⟨b, hb⟩ : μ ∣ a := by
    apply hI
    intro n
    have := congrArg (fun y => Θ ((φ ^ n) y)) (hx.symm.trans haz)
    simpa only [map_mul, map_add (f := _), hxn, hwn, hit', mul_zero, zero_mul, add_zero, eq_comm] using this
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have hp0 : p ≠ 0 := fun h => hp (by rw [h, map_zero])
  have h1 : p ^ (r + 2) * x = t * (v * (p * i b + i μ ^ m * z)) := by
    have e := hx.symm.trans haz
    rw [hb, map_mul] at e
    rw [ht]
    linear_combination p * e + z * hw - (i μ * (p * i b + i μ ^ m * z)) * hv
  refine ⟨_, h1, ?_⟩
  set x' := v * (p * i b + i μ ^ m * z)
  have h2 := congrArg φ h1
  rw [map_mul, map_mul, map_pow, hφp, hx, hφt] at h2
  apply mul_left_cancel₀ (mul_ne_zero hp0 ht0)
  linear_combination p ^ (r + 1) * h1 - h2

variable {l : ℕ} [Fact l.Prime]

theorem alg_eq (a : Per.Ainf l) : algebraMap (Per.Ainf l) (Per.Acris l) a =
    algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem phi_nat (n : ℕ) : phiA l (n : Per.Acris l) = n := map_natCast _ _

theorem phi_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_eq, hj.on0]
  rfl

theorem theta_phi_mu (e : Per.Fl l) (he : e.untilt = 1) (n : ℕ) :
    Per.θ l ((Per.φA l)^[n] (mu e)) = 0 := by
  induction n generalizing e with
  | zero => simp [mu, he]
  | succ n ih =>
    have h : Per.φA l (mu e) = mu (e ^ l) := by
      simp only [mu, map_sub, map_one, GlobalTheory.RingIface.phiA_teich]
    rw [Function.iterate_succ_apply, h]
    exact ih _ (by rw [map_pow, he, one_pow])

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := _root_.GlobalTheory.MemLoc.exists_mu_pow_div l e he
  have h : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  refine ⟨algebraMap (Per.Acris0 l) (Per.Acris l) w, ?_⟩
  rw [alg_eq, ← map_pow, ← h, map_mul, map_natCast]

theorem fil_div (C : Core l) (r : ℕ) (y : Per.BdRp l) (h : C.j C.t * y ∈ Per.FilP l (r + 1)) :
    y ∈ Per.FilP l r := by
  obtain ⟨hF, hreg, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε (_root_.GlobalTheory.MemLoc.core_isEps l C)
  obtain ⟨-, h1, h2, -⟩ := _root_.GlobalTheory.MemLoc.core_t_unit_fil l C
  obtain ⟨-, hk, hun, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  rw [hF] at h h1 h2 ⊢
  obtain ⟨v, hv⟩ := h1
  have hvu : IsUnit v := by
    apply hun
    intro h0
    obtain ⟨c, hc⟩ := (hF _ _).1 ((hk v).1 h0)
    exact h2 ⟨c, by rw [hv, hc]; ring⟩
  obtain ⟨c, hc⟩ := h
  rw [← hvu.dvd_mul_left]
  refine ⟨c, sub_eq_zero.1 (hreg _ ?_)⟩
  rw [hv] at hc
  linear_combination hc

end GlobalTheory.MemLoc.FixR

namespace GlobalTheory.MemLoc
open FixR

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem fix_pow (l : ℕ) [Fact l.Prime] (C : Core l) (r : ℕ) (x : Per.Acris l)
    (hx : phiA l x = (l : Per.Acris l) ^ r * x) (hF : C.j x ∈ Per.FilP l r) :
    ∃ (z : ℤ_[l]) (k : ℕ), (l : Per.Acris l) ^ k * x =
      algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l z) * C.t ^ r := by
  induction r generalizing x with
  | zero =>
    obtain ⟨z, hz⟩ := _root_.GlobalTheory.MemLoc.phi_fixed_eq_padicInt l x (by simpa using hx)
    exact ⟨z, 0, by simpa using hz⟩
  | succ r ih =>
    have he := _root_.GlobalTheory.MemLoc.core_isEps l C
    haveI := (_root_.GlobalTheory.MemLoc.BdRField.bdR_isField l).1
    haveI : IsDomain (Per.Acris l) := (_root_.GlobalTheory.MemLoc.crisP_injective l C.j C.j_cris).isDomain C.j
    obtain ⟨hFil, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε he
    obtain ⟨-, hk, -, hth, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
    obtain ⟨w, hw⟩ := exists_w C.ε he.1
    obtain ⟨t, u, htl, hu, htu⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l C.ε he.1
    have htt : C.t = t := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l C.ε t he.1 htl).1 _ C.t_log
    have hΘ : ∀ a, ((Per.θD l).comp C.j) (algebraMap (Per.Ainf l) (Per.Acris l) a) =
        (Per.θ l a : ℂ_[l]) := fun a => by
      rw [RingHom.comp_apply, j_alg C.j_cris, hth]
    have hl2 : l - 1 = (l - 2) + 1 := by
      have := (Fact.out : l.Prime).two_le
      omega
    obtain ⟨x', h1, h2⟩ := step_abs (algebraMap (Per.Ainf l) (Per.Acris l)) (Per.φA l) (phiA l)
      ((Per.θD l).comp C.j) (l : Per.Acris l) (by rw [map_natCast]; exact GlobalTheory.RingBasics.p_ne_zero)
      (phi_nat l) (phi_alg (l := l)) (mu C.ε)
      (fun n => by rw [hΘ, theta_phi_mu _ he.1]; rfl)
      (fun a ha => _root_.GlobalTheory.MemLoc.mu_dvd_of_theta_frob l C.ε he a fun n => Subtype.ext ((hΘ _).symm.trans (ha n)))
      w (l - 2) (hl2 ▸ hw) (_root_.GlobalTheory.MemLoc.phiA_mem_ainf_add l C.ε he w hw) C.t u hu (htt.trans htu)
      (fun h => (_root_.GlobalTheory.MemLoc.core_t_unit_fil l C).2.2.1 (by rw [h, map_zero]; exact zero_mem _))
      (_root_.GlobalTheory.MemLoc.TPhi.t_phi l C) r x hx
      ((hk _).2 ((hFil _ _).2 ((pow_dvd_pow _ (by omega)).trans ((hFil _ _).1 hF))))
    have h3 : C.j x' ∈ Per.FilP l r := by
      apply fil_div C
      rw [← map_mul, ← h1, map_mul]
      exact Ideal.mul_mem_left _ _ hF
    obtain ⟨z, k, hz⟩ := ih x' h2 h3
    exact ⟨z, k + (r + 2), by linear_combination (l : Per.Acris l) ^ k * h1 + C.t * hz⟩

end GlobalTheory.MemLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AinfKernelPowerClosed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem image_kerP_pow_separated : ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) (a : Per.Ainf l), (∀ k : ℕ, ∃ b : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) (a - ((l : ℕ) : Per.Ainf l) ^ k * b) ∈ Per.kerP l ^ n) → algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ n := by
  intro l _ n a h
  obtain ⟨e, he⟩ : ∃ e : Per.Fl l, IsEps e := Model.exists_isEps l
  obtain ⟨-, -, -, -, -, hinj, hk⟩ := thetaP_facts l
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.MemLoc.ainf_quot_xi_pow_torsionFree_sep l e he n
  have h3 : ∀ (j : ℕ) (c : Per.Ainf l), xi e ^ n ∣ ((l : ℕ) : Per.Ainf l) ^ j * c → xi e ^ n ∣ c := by
    intro j
    induction j with
    | zero => intro c hc; simpa using hc
    | succ j ih =>
      intro c hc
      refine h1 c (ih _ ?_)
      rwa [← mul_assoc, ← pow_succ]
  have key : ∀ c : Per.Ainf l, algebraMap (Per.Ainf l) (Per.AinfP l) c ∈ Per.kerP l ^ n ↔
      xi e ^ n ∣ c := by
    intro c
    rw [hk e he, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
    refine ⟨fun ⟨y, hy⟩ => ?_, fun hc => map_dvd _ hc⟩
    obtain ⟨j, d, hd⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    refine h3 j c ⟨d, hinj ?_⟩
    rw [map_mul, map_mul, ← hd, hy, map_pow, map_pow]
    ring
  refine (key a).2 (h2 a fun k => ?_)
  obtain ⟨b, hb⟩ := h k
  exact ⟨b, (key _).1 hb⟩

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMem
section
noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial Formalism.L2.Forms

theorem fnOf_apply_eq {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s A P y = (∏ τ, (A τ * y.1 τ).det ^ s τ) *
      eval (fun x : ι × Fin n × Fin n => (A x.1 * y.1 x.1) x.2.1 x.2.2) P := rfl

theorem map_mul_map_inv {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_inv_mul_map {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (τ : ι) :
    ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (M : Matrix (Fin n) (Fin n) E).map (emb τ) = 1 := by
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem det_map_emb {E ι : Type} [Field E] {n : ℕ} (emb : ι → E →+* ℂ) (M : Matrix (Fin n) (Fin n) E) (τ : ι) :
    emb τ M.det = (M.map (emb τ)).det := RingHom.map_det _ _

theorem fnOf_inv_twSub {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E)
    (s : ι → ℤ) (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ) (y : Frames G) :
    fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y
      = fnOf G s 1 P0 y := by
  rw [fnOf_apply_eq, fnOf_apply_eq]
  have h := eval_twSub emb M s P0
    (fun τ => atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  have hy : ∀ τ, (M : Matrix (Fin n) (Fin n) E).map (emb τ) *
      (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = y.1 τ := by
    intro τ; rw [← Matrix.mul_assoc, atInf, map_mul_map_inv, Matrix.one_mul]
  simp only [hy] at h
  rw [h]
  simp only [Pi.one_apply, Matrix.one_mul]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [mul_comm, ← mul_zpow, det_map_emb, ← Matrix.det_mul, hy]

theorem exists_det_poly {ι : Type} [Fintype ι] {n : ℕ} :
    ∃ D : MvPolynomial (ι × Fin n × Fin n) ℂ, ∀ x : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) D = ∏ τ, (x τ).det := by
  refine ⟨∏ τ, Matrix.det (Matrix.of fun a b => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)), ?_⟩
  intro x
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem eq_of_eval_units {ι : Type} [Fintype ι] {n : ℕ} (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ x : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, IsUnit (x τ).det) →
      eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) Q = 0) : Q = 0 := by
  obtain ⟨D, hD⟩ := exists_det_poly (ι := ι) (n := n)
  have hQD : Q * D = 0 := by
    apply MvPolynomial.funext
    intro x
    let xm : ι → Matrix (Fin n) (Fin n) ℂ := fun τ a b => x (τ, a, b)
    rw [map_zero, map_mul]
    show eval (fun k : ι × Fin n × Fin n => xm k.1 k.2.1 k.2.2) Q *
      eval (fun k : ι × Fin n × Fin n => xm k.1 k.2.1 k.2.2) D = 0
    rw [hD]
    by_cases hu : ∀ τ, IsUnit (xm τ).det
    · rw [hQ _ hu, zero_mul]
    · push_neg at hu
      obtain ⟨τ, hτ⟩ := hu
      rw [isUnit_iff_ne_zero, not_not] at hτ
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  have hD0 : D ≠ 0 := by
    intro h0
    have := hD (fun _ => 1)
    rw [h0, map_zero] at this
    simp at this
  exact (mul_eq_zero.mp hQD).resolve_right hD0

theorem fnOf_inv_iff_twSub_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  intro E ι _ _ n emb M s G P0 S Yt e f hf
  constructor
  · rintro ⟨P, hP, hPf⟩
    have hall : ∀ y : Frames G,
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P y =
        fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) (twSub emb M s P0) y := by
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [← hPf, hf, fnOf_inv_twSub]
    suffices hPeq : P - twSub emb M s P0 = 0 by
      rw [sub_eq_zero] at hPeq
      rw [← hPeq]; exact hP
    apply eq_of_eval_units
    intro x hx
    have hMu : IsUnit (M : Matrix (Fin n) (Fin n) E).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp M.isUnit
    let y : Frames G := ⟨fun τ => (M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ, fun τ => by
      rw [Matrix.det_mul, ← det_map_emb]; exact (hMu.map (emb τ)).mul (hx τ)⟩
    have h1 := hall y
    rw [fnOf_apply_eq, fnOf_apply_eq] at h1
    have hAx : ∀ τ, atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ = x τ := by
      intro τ
      show atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ *
        ((M : Matrix (Fin n) (Fin n) E).map (emb τ) * x τ) = x τ
      rw [← Matrix.mul_assoc, atInf, map_inv_mul_map, Matrix.one_mul]
    simp only [hAx] at h1
    have hne : (∏ τ, (x τ).det ^ s τ) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ (hx τ).ne_zero
    rw [map_sub, sub_eq_zero]
    exact mul_left_cancel₀ hne h1
  · intro h
    exact ⟨_, h, fun z => by rw [hf, fnOf_inv_twSub]⟩

end GlobalTheory.IntegralityCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem charpoly_eq_of_eqOn_dense : ∀ {X A : Type} [TopologicalSpace X] [Field A] [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] [Infinite A] {n : ℕ} (M N : X → Matrix (Fin n) (Fin n) A), Continuous M → Continuous N → ∀ U : Set X, Dense U → (∀ x ∈ U, (M x).charpoly = (N x).charpoly) → ∀ x, (M x).charpoly = (N x).charpoly := by
  intro X A _ _ _ _ _ _ n M N hM hN U hU hEq x
  apply Polynomial.funext
  intro c
  have hcM : Continuous fun y => (M y).charpoly.eval c := by
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hM).matrix_det
  have hcN : Continuous fun y => (N y).charpoly.eval c := by
    simp_rw [Matrix.eval_charpoly]
    exact (continuous_const.sub hN).matrix_det
  have h : (fun y => (M y).charpoly.eval c) = fun y => (N y).charpoly.eval c :=
    Continuous.ext_on hU hcM hcN (fun y hy => by simp only [hEq y hy])
  exact congrFun h x

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousRingHomFiniteDvrToPadicAlgClosure
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

noncomputable section

namespace GlobalTheory.AdicCont

theorem norm_le_one_of_monic_root_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    (P : K[X]) (hm : P.Monic) (hc : ∀ i, ‖P.coeff i‖ ≤ 1) {y : K} (hy : P.eval y = 0) : ‖y‖ ≤ 1 := by
  by_contra h
  push_neg at h
  have hn : 0 < P.natDegree := by
    rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
    · exfalso
      have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hm h0
      rw [h1, eval_one] at hy
      exact one_ne_zero hy
    · exact h0
  set n := P.natDegree with hndef
  have hsum := eval_eq_sum_range (p := P) y
  rw [Finset.sum_range_succ, ← hndef, hm.coeff_natDegree, one_mul, hy] at hsum
  have hyn : y ^ n = -∑ i ∈ Finset.range n, P.coeff i * y ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum.symm
  have hle : ‖∑ i ∈ Finset.range n, P.coeff i * y ^ i‖ ≤ ‖y‖ ^ (n - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' : i ≤ n - 1 := by have := Finset.mem_range.1 hi; omega
    calc ‖P.coeff i‖ * ‖y‖ ^ i ≤ 1 * ‖y‖ ^ (n - 1) :=
          mul_le_mul (hc i) (pow_le_pow_right₀ h.le hi') (by positivity) zero_le_one
      _ = _ := one_mul _
  have h2 : ‖y‖ ^ n ≤ ‖y‖ ^ (n - 1) := by rw [← norm_pow, hyn, norm_neg]; exact hle
  have h3 : ‖y‖ ^ (n - 1) < ‖y‖ ^ n := pow_lt_pow_right₀ h (by omega)
  linarith

theorem continuous_adic (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [TopologicalSpace O] [IsTopologicalRing O]
    (hO : IsAdic (IsLocalRing.maximalIdeal O)) (iq : FractionRing O →+* Qbar l)
    (hiq : ∀ z : ℤ_[l], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[l] O z)) =
      algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l])) :
    Continuous (fun x : O => iq (algebraMap O (FractionRing O) x)) := by
  set f : O →+* Qbar l := iq.comp (algebraMap O (FractionRing O)) with hf
  have hfz : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) := hiq

  have h1 : ∀ x : O, ‖f x‖ ≤ 1 := by
    intro x
    obtain ⟨p, hpm, hpx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x
    let g : ℤ_[l] →+* Qbar l := f.comp (algebraMap ℤ_[l] O)
    refine norm_le_one_of_monic_root_ultra (p.map g) (hpm.map g) (fun i => ?_) ?_
    · rw [coeff_map]
      simp only [g, RingHom.comp_apply, hfz, PadicAlgCl.norm_extends]
      exact (p.coeff i).2
    · have := congrArg f hpx
      rw [hom_eval₂, map_zero] at this
      rw [eval_map]
      exact this

  have hlnorm : ‖f (l : O)‖ = (l : ℝ)⁻¹ := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] (Qbar l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (l : O) ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hlnorm
    have : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
    linarith
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hlu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hr : ‖f ϖ‖ < 1 := by
    have he : ϖ ^ e = ((u⁻¹ : Oˣ) : O) * (l : O) := by
      rw [hlu, ← mul_assoc, Units.inv_mul, one_mul]
    have hnorm : ‖f ϖ‖ ^ e ≤ (l : ℝ)⁻¹ := by
      rw [← norm_pow, ← map_pow, he, map_mul, norm_mul, hlnorm]
      calc ‖f ((u⁻¹ : Oˣ) : O)‖ * (l : ℝ)⁻¹ ≤ 1 * (l : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right (h1 _) (by positivity)
        _ = _ := one_mul _
    have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
    by_contra hge
    push_neg at hge
    have : 1 ≤ ‖f ϖ‖ ^ e := one_le_pow₀ hge
    linarith
  have hcont : ContinuousAt f 0 := by
    rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hr
    have hopen : IsOpen ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) := (isAdic_iff.1 hO).1 n
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    rw [dist_zero_right]
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton'] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [map_mul, norm_mul, map_pow, norm_pow]
    calc ‖f a‖ * ‖f ϖ‖ ^ n ≤ 1 * ‖f ϖ‖ ^ n := mul_le_mul_of_nonneg_right (h1 a) (by positivity)
      _ < ε := by rwa [one_mul]
  exact continuous_of_continuousAt_zero f hcont

end GlobalTheory.AdicCont

end
end

