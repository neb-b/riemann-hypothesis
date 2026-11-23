module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import ReciprocityTheory.DualLattices.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem pow_sub_one_pow_congr_geom_sum_pow {R : Type} [CommRing R] {l : ℕ} (hl : l.Prime) (x : R) :
    (l : R) ∣ (x ^ l - 1) ^ (l - 1) - (∑ i ∈ Finset.range l, x ^ i) ^ l := by
  have key : (l : Polynomial ℤ) ∣ (Polynomial.X ^ l - 1) ^ (l - 1) -
      (∑ i ∈ Finset.range l, (Polynomial.X : Polynomial ℤ) ^ i) ^ l := by
    set y : Polynomial ℤ := Polynomial.X - 1 with hy
    have hy0 : y ≠ 0 := Polynomial.X_sub_C_ne_zero (1 : ℤ)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl y 1
    have hX : y + 1 = Polynomial.X := by rw [hy]; ring
    rw [hX, one_pow] at hr
    obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, (Nat.sub_add_cancel hl.one_le).symm⟩
    set s : Polynomial ℤ := ∑ i ∈ Finset.range (k + 1), (Polynomial.X : Polynomial ℤ) ^ i with hs
    have h1 : s * y = Polynomial.X ^ (k + 1) - 1 := geom_sum_mul _ _
    have h2 : s = y ^ k + ((k + 1 : ℕ) : Polynomial ℤ) * r := by
      refine mul_right_cancel₀ hy0 ?_
      rw [h1, hr]; ring
    have h3 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ s - y ^ k := ⟨r, by rw [h2]; ring⟩
    have h4 : ((k + 1 : ℕ) : Polynomial ℤ) ∣ (Polynomial.X ^ (k + 1) - 1) - y ^ (k + 1) :=
      ⟨y * r, by rw [hr]; ring⟩
    have h5 := h3.trans (sub_dvd_pow_sub_pow s (y ^ k) (k + 1))
    have h6 := h4.trans (sub_dvd_pow_sub_pow _ (y ^ (k + 1)) k)
    have h7 := dvd_sub h6 h5
    rw [← pow_mul, ← pow_mul, mul_comm k (k + 1), sub_sub_sub_cancel_right] at h7
    simpa using h7
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum] using map_dvd (Polynomial.aeval (R := ℤ) x) key

theorem exists_div_prime_pow_dvd {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {l : ℕ} (hl : l.Prime)
    (hu : ∀ n : ℕ, IsUnit ((n.factorial : ℕ) : A)) (S : Subalgebra R A) (η z : R)
    (hη : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A η ^ n)
    (hz : ∀ n : ℕ, ∃ g ∈ S, ((n.factorial : ℕ) : A) * g = algebraMap R A z ^ n) :
    ∃ w : S, (l : A) * (w : A) = algebraMap R A (η ^ l + l * z) ∧ (l : S) ∣ w ^ l := by
  obtain ⟨g₁, m₁, h₁⟩ := hη l
  obtain ⟨g₂, m₂, h₂⟩ := hη (l * l)
  obtain ⟨g₃, m₃, h₃⟩ := hz l
  have hf : ((l.factorial : ℕ) : A) = (l : A) * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.ne_zero]; push_cast; rfl
  have hb : (((l * l).factorial : ℕ) : A) =
      (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) ^ l * ((l.factorial : ℕ) : A) := by
    rw [← Nat.uniformBell_mul_eq l hl.ne_zero]; push_cast; rfl
  have hg : g₁ ^ l = (Nat.uniformBell l l : A) * ((l.factorial : ℕ) : A) * g₂ := by
    refine ((hu l).pow l).mul_left_cancel ?_
    rw [← mul_pow, h₁, ← pow_mul, ← h₂, hb]; ring
  let a : S := (((l - 1).factorial : ℕ) : S) * ⟨g₁, m₁⟩
  let b : S := algebraMap R S z
  refine ⟨a + b, ?_, ?_⟩
  · rw [map_add (f := _), map_mul, map_pow, map_natCast, ← h₁, hf]
    simp only [a, b]
    push_cast
    ring
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl a b
    have ha : (l : S) ∣ a ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) ^ l * (Nat.uniformBell l l : S) * (((l - 1).factorial : ℕ) : S) *
        ⟨g₂, m₂⟩, Subtype.ext ?_⟩
      simp only [a]
      push_cast
      rw [mul_pow, hg, hf]; ring
    have hb : (l : S) ∣ b ^ l := by
      refine ⟨(((l - 1).factorial : ℕ) : S) * ⟨g₃, m₃⟩, Subtype.ext ?_⟩
      simp only [b]
      push_cast
      rw [← h₃, hf]; ring
    rw [hr]
    exact dvd_add (dvd_add ha hb) ⟨a * b * r, by ring⟩

theorem exists_dividedPower_mem_Acris0 (l : ℕ) [Fact l.Prime] (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ) :
    ∃ g ∈ Per.Acris0 l, ((n.factorial : ℕ) : Per.AinfP l) * g = algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := (GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero).exists_right_inv
  have h : ((n.factorial : ℕ) : Per.AinfP l) * (u * algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n) =
      algebraMap (Per.Ainf l) (Per.AinfP l) x ^ n := by rw [← mul_assoc, hu, one_mul]
  refine ⟨_, ?_, h⟩
  apply GlobalTheory.RingIface.dividedPower_mem_Acris0 <;> assumption

theorem tm_root_pow (l : ℕ) [Fact l.Prime] (e : Per.Fl l) :
    Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) ^ l = Per.tm e := by
  rw [← map_pow]
  congr 1
  exact frobeniusEquiv_symm_pow_p (Per.Fl l) l e

theorem exists_mu_pow_div_of_isEps (l : ℕ) [hl : Fact l.Prime] (e : Per.Fl l) (he : IsEps e) :
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  set x := Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) with hx
  have hxl : x ^ l = Per.tm e := tm_root_pow l e
  have hmu : mu e = x ^ l - 1 := by rw [hxl]; rfl
  have hθmu : Per.θ l (x ^ l - 1) = 0 := by
    rw [hxl, map_sub, map_one, WittVector.fontaineTheta_teichmuller, he.1, sub_self]
  have hθx : Per.θ l (x - 1) ≠ 0 := by
    rw [hx, map_sub, map_one, WittVector.fontaineTheta_teichmuller, sub_ne_zero]
    exact he.2
  have hη : Per.θ l (∑ i ∈ Finset.range l, x ^ i) = 0 := by
    rw [← geom_sum_mul, map_mul] at hθmu
    exact (mul_eq_zero.1 hθmu).resolve_right hθx
  obtain ⟨z, hz⟩ := pow_sub_one_pow_congr_geom_sum_pow hl.out x
  have hθz : Per.θ l z = 0 := by
    have h := congrArg (Per.θ l) hz
    have h1 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    rw [map_sub, map_pow, map_pow, hθmu, hη, zero_pow h1, zero_pow hl.out.ne_zero, sub_self, map_mul,
      map_natCast] at h
    refine (mul_eq_zero.1 h.symm).resolve_left ?_
    exact_mod_cast hl.out.ne_zero
  obtain ⟨w, hw, hd⟩ := exists_div_prime_pow_dvd hl.out
    (fun n => GlobalTheory.RingBasics.isUnit_nat l _ n.factorial_ne_zero) (Per.Acris0 l) _ z
    (exists_dividedPower_mem_Acris0 l _ hη) (exists_dividedPower_mem_Acris0 l _ hθz)
  refine ⟨w, ?_, hd⟩
  rw [hw, ← hz, add_sub_cancel, map_pow, hmu]

theorem exists_mu_pow_div : ∀ (l : ℕ) [Fact l.Prime], ∀ e : Per.Fl l, e.untilt = 1 →
    ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
  intro l hl e he
  have step : ∀ m : ℕ, ∀ e : Per.Fl l, e.untilt = 1 →
      (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1 →
      ∃ w : Per.Acris0 l, (l : Per.AinfP l) * (w : Per.AinfP l) =
        algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1) ∧ (l : Per.Acris0 l) ∣ w ^ l := by
    intro m
    induction m with
    | zero => exact fun e h1 h2 => absurd h1 h2
    | succ m ih =>
      intro e h1 h2
      by_cases h : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt = 1
      · obtain ⟨w, hw, hd⟩ := ih _ h h2
        have hmu : mu e = xi e * mu ((frobeniusEquiv (Per.Fl l) l).symm e) := by
          rw [xi, mu, mu, geom_sum_mul, tm_root_pow]
        refine ⟨algebraMap _ _ (xi e ^ (l - 1)) * w, ?_, ?_⟩
        · rw [hmu, map_mul, mul_pow, ← hw, ← map_pow, Subalgebra.coe_mul, Subalgebra.coe_algebraMap]
          ring
        · rw [mul_pow]
          exact hd.mul_left _
      · exact exists_mu_pow_div_of_isEps l e ⟨h1, h⟩
  by_cases h : ∃ m : ℕ, (((frobeniusEquiv (Per.Fl l) l).symm)^[m] e).untilt ≠ 1
  · obtain ⟨m, hm⟩ := h
    exact step m e he hm
  · push Not at h
    have h1 : e = 1 := by
      refine Perfection.ext fun n => ?_
      have h2 := PreTilt.mk_untilt_eq_coeff_zero (((frobeniusEquiv (Per.Fl l) l).symm)^[n] e)
      rw [h n, map_one, PreTilt.coeff_iterate_frobeniusEquiv_symm, zero_add] at h2
      exact h2.symm.trans (map_one (PreTilt.coeff (O := Per.OC l) (p := l) n)).symm
    have h0 : l - 1 ≠ 0 := by have := hl.out.two_le; omega
    refine ⟨0, ?_, by rw [zero_pow hl.out.ne_zero]; exact dvd_zero _⟩
    have hm : mu e = 0 := by
      rw [h1]
      exact sub_eq_zero.2 (map_one (WittVector.teichmuller l))
    rw [hm, map_zero, zero_pow h0]
    simp

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitPowNormVSubOne
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.OneUnitRoot

open IsDedekindDomain.HeightOneSpectrum IsLocalRing Polynomial

theorem exists_unit_pow_normV_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (y : (v.adicCompletion E)ˣ) (hy : Valued.v ((y : v.adicCompletion E) - 1) < 1) :
    ∃ z : (v.adicCompletion E)ˣ, Valued.v (z : v.adicCompletion E) = 1 ∧ z ^ (normV v - 1) = y := by
  have hc := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  set n := normV v - 1 with hn
  have hcard : Nat.card (ResidueField (v.adicCompletionIntegers E)) = normV v := by
    simpa [Formalism.UG.qV, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      Formalism.UG.P.tjcosets_card_residue v
  haveI : Finite (ResidueField (v.adicCompletionIntegers E)) :=
    GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  haveI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers E))
  have hq0 : ((normV v : ℕ) : ResidueField (v.adicCompletionIntegers E)) = 0 := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero _
  have hq1 : 2 ≤ normV v := by
    rw [← hcard]; exact Finite.one_lt_card
  have hnres : ((n : ℕ) : ResidueField (v.adicCompletionIntegers E)) = -1 := by
    rw [hn, Nat.cast_sub (by omega), hq0]; simp
  have hnpos : 0 < n := by omega

  have hy1 : Valued.v (y : v.adicCompletion E) = 1 := by
    have e : (y : v.adicCompletion E) = ((y : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  set y' : v.adicCompletionIntegers E := ⟨y, by
    show Valued.v (y : v.adicCompletion E) ≤ 1; exact hy1.le⟩
  have hm : (X ^ n - C y' : (v.adicCompletionIntegers E)[X]).Monic := monic_X_pow_sub_C y' hnpos.ne'
  have hev : eval 1 (X ^ n - C y' : (v.adicCompletionIntegers E)[X]) ∈ maximalIdeal (v.adicCompletionIntegers E) := by
    simp only [eval_sub, eval_pow, eval_X, one_pow, eval_C]
    rw [← neg_sub, Ideal.neg_mem_iff, mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ne_of_lt hy
  have hder : IsUnit (eval 1 (derivative (X ^ n - C y' : (v.adicCompletionIntegers E)[X]))) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_C, eval_pow, eval_X, one_pow, mul_one]
    rw [← isUnit_map_iff (residue (v.adicCompletionIntegers E)), map_natCast, hnres]
    exact isUnit_one.neg
  obtain ⟨r, hr, hr1⟩ := HenselianRing.is_henselian (I := maximalIdeal (v.adicCompletionIntegers E))
    _ hm 1 hev (hder.map _)
  have hrn : r ^ n = y' := by
    have := hr
    simp only [IsRoot, eval_sub, eval_pow, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  have hrv : Valued.v (r : v.adicCompletion E) = 1 := by
    have h1 : Valued.v ((r : v.adicCompletion E) - 1) < 1 := by
      have := hr1
      rw [mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one] at this
      exact lt_of_le_of_ne (r - 1).2 this
    have e : (r : v.adicCompletion E) = ((r : v.adicCompletion E) - 1) + 1 := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    · exact map_one _
    · rwa [map_one]
  have hr0 : (r : v.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hrv; exact zero_ne_one hrv
  refine ⟨Units.mk0 _ hr0, hrv, Units.ext ?_⟩
  rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  exact congrArg Subtype.val hrn

end GlobalTheory.OneUnitRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineThetaEqZeroIffFontaineXiElementDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem IsEps.isPrimitiveRoot_untilt {l : ℕ} [hl : Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    IsPrimitiveRoot ((frobeniusEquiv (Per.Fl l) l).symm e).untilt l := by
  have hp : ((frobeniusEquiv (Per.Fl l) l).symm e).untilt ^ l = 1 := by
    rw [← map_pow, frobeniusEquiv_symm_pow_p, h.1]
  have ho := orderOf_eq_prime hp h.2
  have := IsPrimitiveRoot.orderOf ((frobeniusEquiv (Per.Fl l) l).symm e).untilt
  rwa [ho] at this

theorem ker_theta_eq_span_xi {l : ℕ} [Fact l.Prime] {e : Per.Fl l} (h : IsEps e) :
    RingHom.ker (Per.θ l) = Ideal.span {xi e} := by
  obtain ⟨⟨pf, hpf⟩, -, -, hX, -⟩ :=
    ReciprocityTheory.PGsh.a0 l ℂ_[l] Valued.v (Per.OC l) (PadicComplexInt.integers l)
  exact ((hX e (PadicComplexInt.integers l) h.isPrimitiveRoot_untilt).2.2.2 pf hpf).1

theorem theta_eq_zero_iff_xi_dvd (l : ℕ) [Fact l.Prime] :
    ∀ e : Per.Fl l, IsEps e → ∀ a : Per.Ainf l, Per.θ l a = 0 ↔ xi e ∣ a := by
  intro e h a
  rw [← RingHom.mem_ker, ker_theta_eq_span_xi h, Ideal.mem_span_singleton]

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
section
noncomputable section

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem tauPt_one (τ : L →+* ℂ) : tauPt τ (1 : GL (Fin n) ℂ) = fun _ => 1 := by
  funext σ
  simp only [tauPt, inv_one, Units.val_one, Matrix.transpose_one]
  split_ifs <;> rfl

theorem tauPt_mul (τ : L →+* ℂ) (A B : GL (Fin n) ℂ) :
    tauPt τ (A * B) = fun σ => tauPt τ A σ * tauPt τ B σ := by
  funext σ
  simp only [tauPt]
  split_ifs
  · simp
  · simp [_root_.mul_inv_rev, Matrix.transpose_mul]
  · simp


open Classical in
def tauSubst (τ : L →+* ℂ) : (L →+* ℂ) × Fin n × Fin n →
    MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ := fun p =>
  if p.1 = τ then MvPolynomial.X (Sum.inl (p.2.1, p.2.2))
  else if p.1 = ComplexEmbedding.conjugate τ then MvPolynomial.X (Sum.inr (p.2.2, p.2.1))
  else MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)

theorem eval_evPt (τ : L →+* ℂ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (B : GL (Fin n) ℂ) :
    MvPolynomial.eval (evPt τ B) Q =
      MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2))
        (MvPolynomial.bind₁ (tauSubst τ) Q) := by
  have e := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℂ)
    (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2)) (tauSubst τ) Q
  erw [e]
  show MvPolynomial.eval _ Q = MvPolynomial.eval _ Q
  congr 2
  funext p
  simp only [evPt_eq_upt, upt, tauPt, tauSubst]
  split_ifs <;> simp [Matrix.one_apply, *]

theorem isPolyRep_evPt (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (h : Agrees a b P) (τ : L →+* ℂ) :
    IsPolyRep (fun B => evM P (evPt τ B)) := by
  obtain ⟨h1, hm⟩ := _root_.GlobalTheory.AlgWtMul.evM_mul L n a ι b P h
  refine ⟨?_, ?_, ?_⟩
  · show evM P (evPt τ 1) = 1
    rw [evPt_eq_upt, tauPt_one]
    exact h1
  · intro A B
    show evM P (evPt τ (A * B)) = evM P (evPt τ A) * evM P (evPt τ B)
    rw [evPt_eq_upt, evPt_eq_upt, evPt_eq_upt, tauPt_mul]
    exact hm _ _ (isUPt_tauPt τ A) (isUPt_tauPt τ B)
  · intro i j
    refine ⟨MvPolynomial.bind₁ (tauSubst τ) (P i j), fun B => ?_⟩
    show MvPolynomial.eval (evPt τ B) (P i j) = _
    exact eval_evPt τ (P i j) B

end GlobalTheory.AlgWtHW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem core_isEps : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  intro l _ C
  refine ⟨?_, ?_⟩
  · have h := C.ε_root 0
    rw [C.ζ_zero, map_one] at h
    exact Subtype.ext h
  · intro h1
    have h := C.ε_root 1
    have h2 : rootT C.ε 1 = 1 := h1
    rw [h2] at h
    apply C.ζ_one
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h]
    rfl

end GlobalTheory.MemLoc
end

