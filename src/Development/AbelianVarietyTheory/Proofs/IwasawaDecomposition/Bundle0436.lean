module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAddCharPlaceIdempotentDivPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem intTrace_modEq (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K))
    (hvI : IsCoprime v.asIdeal I) (hpI : Ideal.span {(p : 𝓞 K)} = v.asIdeal * I)
    (hnorm : Ideal.absNorm v.asIdeal = p) (x : 𝓞 K) (b : ℤ) (hxv : x - (b : 𝓞 K) ∈ v.asIdeal) (hxI : x ∈ I) :
    ∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m := by
  classical
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hPdef
  haveI hPm : P.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  letI := Ideal.Quotient.field P
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) P = v.asIdeal * I := by
    rw [hPdef, Ideal.map_span, Set.image_singleton, map_natCast]; exact hpI
  have hPv : P ≤ v.asIdeal.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_left (I := v.asIdeal) (J := I)
  have hPI : P ≤ I.comap (algebraMap ℤ (𝓞 K)) := by
    rw [← Ideal.map_le_iff_le_comap, hmap]; exact Ideal.mul_le_right (I := v.asIdeal) (J := I)
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hPv
  letI : Algebra (ℤ ⧸ P) (𝓞 K ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap hPI
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := .of_algebraMap_eq' rfl
  haveI : IsScalarTower ℤ (ℤ ⧸ P) (𝓞 K ⧸ I) := .of_algebraMap_eq' rfl
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Module.Finite (ℤ ⧸ P) (𝓞 K ⧸ I) := Module.Finite.of_restrictScalars_finite ℤ _ _
  let e : (𝓞 K ⧸ Ideal.map (algebraMap ℤ (𝓞 K)) P) ≃ₐ[ℤ ⧸ P] ((𝓞 K ⧸ v.asIdeal) × (𝓞 K ⧸ I)) :=
    { __ := (Ideal.quotEquivOfEq hmap).trans (Ideal.quotientMulEquivQuotientProd v.asIdeal I hvI),
      commutes' := Quotient.ind fun _ ↦ rfl }
  have he : e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk v.asIdeal x, Ideal.Quotient.mk I x) := rfl
  have hx2 : Ideal.Quotient.mk I x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hxI
  have hx1 : Ideal.Quotient.mk v.asIdeal x = algebraMap (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) (Ideal.Quotient.mk P b) := by
    rw [Ideal.Quotient.eq.mpr hxv]
    show _ = Ideal.Quotient.mk v.asIdeal (algebraMap ℤ (𝓞 K) b)
    rw [algebraMap_int_eq, eq_intCast]
  have hcardP : Nat.card (ℤ ⧸ P) = p := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardv : Nat.card (𝓞 K ⧸ v.asIdeal) = p := by
    rw [← hnorm, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfr : Module.finrank (ℤ ⧸ P) (𝓞 K ⧸ v.asIdeal) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ℤ ⧸ P) (V := 𝓞 K ⧸ v.asIdeal)
    rw [hcardP, hcardv] at h
    exact (Nat.pow_right_injective hp.two_le (h.symm.trans (pow_one p).symm))
  have key : Ideal.Quotient.mk P (Algebra.intTrace ℤ (𝓞 K) x) = Ideal.Quotient.mk P b := by
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv e, he,
      Algebra.trace_prod_apply, hx2, map_zero, add_zero, hx1, Algebra.trace_algebraMap, hfr, one_smul]
  rw [Ideal.Quotient.eq, hPdef, Ideal.mem_span_singleton] at key
  obtain ⟨m, hm⟩ := key
  exact ⟨m, by linear_combination hm⟩

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem integral_of_mul (w : HeightOneSpectrum (𝓞 K)) (n z s y : 𝓞 K) (hn : n ≠ 0) (hs : s ∉ w.asIdeal)
    (h : z * s = n * y) :
    algebraMap K (Af K) ((z : K) / (n : K)) w ∈ w.adicCompletionIntegers K := by
  have hs0 : (s : K) ≠ 0 := by
    intro h0; apply hs; rw [show s = 0 from by exact_mod_cast h0]; exact zero_mem _
  have hn0 : (n : K) ≠ 0 := by exact_mod_cast hn
  have hq : (z : K) / (n : K) = (y : K) / (s : K) := by
    rw [div_eq_div_iff hn0 hs0]
    have := congrArg (fun t : 𝓞 K => (t : K)) h
    simp only [map_mul] at this
    push_cast at this
    linear_combination this
  rw [hq, HeightOneSpectrum.mem_adicCompletionIntegers]
  have e := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w ((y : K) / (s : K))
  erw [e]
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff.mpr hs, div_one]
  exact HeightOneSpectrum.intValuation_le_one w y

theorem exists_cofactor (p : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) :
    ∃ I : Ideal (𝓞 K), IsCoprime v.asIdeal I ∧ Ideal.span {(p : 𝓞 K)} = v.asIdeal * I := by
  have hpv : (p : 𝓞 K) ∈ v.asIdeal := by
    have := Ideal.absNorm_mem v.asIdeal
    rwa [hnorm] at this
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hpv)
  refine ⟨I, ?_, hI⟩
  have hpr := (Ideal.prime_iff_isPrime v.ne_bot).mpr v.isPrime
  rw [Ideal.isCoprime_iff_gcd, hpr.irreducible.gcd_eq_one_iff]
  rintro ⟨J, rfl⟩
  apply hsq
  have : Ideal.span {(p : 𝓞 K)} ≤ v.asIdeal ^ 2 := by
    rw [hI, pow_two, ← mul_assoc]; exact Ideal.mul_le_left (I := v.asIdeal * v.asIdeal) (J := J)
  exact this (Ideal.mem_span_singleton_self _)

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

variable {K : Type} [Field K] [NumberField K]

theorem fin_part (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 K))
    (hnorm : Ideal.absNorm v.asIdeal = p) (hsq : (p : 𝓞 K) ∉ v.asIdeal ^ 2) (α : Af K)
    (hα1 : evalV K v α = 1) (hα0 : ∀ w, w ≠ v → evalV K w α = 0) (a : 𝓞 K) (b : ℤ)
    (hab : a - (b : 𝓞 K) ∈ v.asIdeal) :
    ∃ x : 𝓞 K, (∃ m : ℤ, Algebra.intTrace ℤ (𝓞 K) x = b + p * m) ∧
      ∀ w : HeightOneSpectrum (𝓞 K), (α * algebraMap K (Af K) ((a : K) / (p : K)) -
        algebraMap K (Af K) ((x : K) / (p : K))) w ∈ w.adicCompletionIntegers K := by
  obtain ⟨I, hvI, hpI⟩ := exists_cofactor p v hnorm hsq
  obtain ⟨u, hu, t, ht, hut⟩ := Ideal.isCoprime_iff_exists.mp hvI
  have htv : t ∉ v.asIdeal := fun h =>
    v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (hut ▸ add_mem hu h))
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hmemp : ∀ z ∈ v.asIdeal * I, ∃ y, z = (p : 𝓞 K) * y := fun z hz => by
    rw [← hpI, Ideal.mem_span_singleton'] at hz
    obtain ⟨y, hy⟩ := hz
    exact ⟨y, by rw [← hy, mul_comm]⟩
  have hxv : (b : 𝓞 K) * t - b ∈ v.asIdeal := by
    have e : (b : 𝓞 K) * t - b = -((b : 𝓞 K) * u) := by linear_combination (b : 𝓞 K) * hut
    rw [e]; exact neg_mem (Ideal.mul_mem_left _ _ hu)
  refine ⟨b * t, intTrace_modEq p hp v I hvI hpI hnorm _ b hxv (Ideal.mul_mem_left _ _ ht), fun w => ?_⟩
  have hcomp : (α * algebraMap K (Af K) ((a : K) / (p : K)) - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K))) w =
      α w * algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w := rfl
  rw [hcomp]
  by_cases hw : w = v
  · subst hw
    have h1 : α w = 1 := hα1
    have hsub : algebraMap K (Af K) ((a : K) / (p : K)) w - algebraMap K (Af K) ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) w =
        algebraMap K (Af K) (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) w := by
      rw [show (((a - (b : 𝓞 K) * t : 𝓞 K) : K) / ((p : 𝓞 K) : K)) =
        (a : K) / (p : K) - ((((b : 𝓞 K) * t : 𝓞 K) : K) / (p : K)) by push_cast; ring, map_sub]
      rfl
    rw [h1, one_mul, hsub]
    have hmem : (a - (b : 𝓞 K) * t) * t ∈ w.asIdeal * I := by
      refine Ideal.mul_mem_mul ?_ ht
      have e : a - (b : 𝓞 K) * t = (a - b) - ((b : 𝓞 K) * t - b) := by ring
      rw [e]; exact sub_mem hab hxv
    obtain ⟨y, hy⟩ := hmemp _ hmem
    exact integral_of_mul w _ _ t y hp0 htv hy
  · have h0 : α w = 0 := hα0 w hw
    rw [h0, zero_mul, zero_sub]
    refine neg_mem ?_
    obtain ⟨s, hsv, hsw⟩ : ∃ s ∈ v.asIdeal, s ∉ w.asIdeal := by
      by_contra hc
      push_neg at hc
      exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hc).symm)
    obtain ⟨y, hy⟩ := hmemp _ (Ideal.mul_mem_mul hsv (Ideal.mul_mem_left _ (b : 𝓞 K) ht))
    have := integral_of_mul w (p : 𝓞 K) ((b : 𝓞 K) * t) s y hp0 hsw (by rw [mul_comm]; exact hy)
    simpa using this

end GlobalTheory.StdCharDegOne

namespace GlobalTheory.StdCharDegOne

theorem stdChar_placeIdem_div : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (p : ℕ), p.Prime → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), Ideal.absNorm v.asIdeal = p → (p : 𝓞 D.host.F) ∉ v.asIdeal ^ 2 → ∀ ε, IsPlaceIdem D v ε → ∀ (a : 𝓞 D.host.F) (b : ℤ), a - (b : 𝓞 D.host.F) ∈ v.asIdeal → ψ (ε * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F))) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D ψ hψ p hp v hnorm hsq ε hε a b hab
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  obtain ⟨x, ⟨m, hm⟩, hint⟩ := fin_part p hp v hnorm hsq α hα1 hα0 a b hab
  have hsplit : pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) ((a : D.host.F) / (p : D.host.F)) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) +
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F))) := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) * _ = 0 + 0
      rw [zero_mul, add_zero]
    · show α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) =
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)) +
        (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
          algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))
      rw [add_sub_cancel]
  have htr : ∀ r : 𝓞 D.host.F, Algebra.trace ℚ D.host.F (r : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) r : ℤ) : ℚ) :=
    fun r => (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) r).symm
  have h1 : ψ (pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) ((a : D.host.F) / (p : D.host.F)) -
        algebraMap D.host.F (Af D.host.F) ((x : D.host.F) / (p : D.host.F)))) = 1 := by
    refine GlobalTheory.IntDense.mem_of_isClosed D.host.F (C := {y | ψ (pairA D.host.F 0 y) = 1})
      (isClosed_eq (hψ.1.1.comp (Continuous.prodMk continuous_const continuous_id)) continuous_const)
      (fun r => ?_) _ hint
    show ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (r : D.host.F))) = 1
    rw [GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hsplit, AddChar.map_add_eq_mul, h1, mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ]
  have hq : Algebra.trace ℚ D.host.F ((x : D.host.F) / (p : D.host.F)) = ((b : ℚ) + p * m) / p := by
    have e : (x : D.host.F) / (p : D.host.F) = ((p : ℚ)⁻¹) • (x : D.host.F) := by
      rw [Algebra.smul_def, map_inv₀, map_natCast, div_eq_inv_mul]
    rw [e, map_smul, htr, hm, smul_eq_mul]
    push_cast
    ring
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hq, show 2 * ↑Real.pi * Complex.I * ((((b : ℚ) + p * m) / p : ℚ) : ℂ) =
      2 * Real.pi * Complex.I * b / (p : ℂ) + m * (2 * Real.pi * Complex.I) by
    push_cast; field_simp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end GlobalTheory.StdCharDegOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TargetPairingSizesInCoefficientFieldValueGroup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.KerVal
open MvPolynomial

theorem deX_map {Lt k k' : Type} [Fintype Lt] [CommRing k] [CommRing k'] (f : k →+* k') (N : ℕ) (nu : Lt → YoungDiagram)
    (y : Lt → Fin N → ℕ → k) : MvPolynomial.map f (GL3Columns.DeX N nu y) = GL3Columns.DeX N nu (fun s a j => f (y s a j)) := by
  unfold GL3Columns.DeX
  simp only [map_prod, RingHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, map_C, map_X]

theorem dual_map_eval {σ V k : Type} [Field k] (χ : Module.Dual k (MvPolynomial σ k)) (p : MvPolynomial σ (MvPolynomial V k)) (x : V → k) :
    MvPolynomial.eval x (∑ m ∈ p.support, AddMonoidAlgebra.coeff p m * C (χ (monomial m 1))) = χ (MvPolynomial.map (MvPolynomial.eval x) p) := by
  conv_rhs => rw [p.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, eval_C, map_monomial]
  rw [show monomial m (MvPolynomial.eval x (AddMonoidAlgebra.coeff p m)) = (MvPolynomial.eval x (AddMonoidAlgebra.coeff p m)) • (monomial m 1 : MvPolynomial σ k) by
    rw [smul_monomial, smul_eq_mul, mul_one]]
  rw [map_smul, smul_eq_mul]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

def uFr : Bool × HH D → Fin N → ℕ → MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  fun s a j => if h : j < N then X (tauPl D s, a, ⟨j, h⟩) else 0

def canPol (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) : MvPolynomial (GL3Theta.FrV D N) (Cw D w) :=
  ∑ m ∈ (GL3Columns.DeX N nu (uFr w N)).support, AddMonoidAlgebra.coeff (GL3Columns.DeX N nu (uFr w N)) m * C (χ (monomial m 1))

theorem canM_apply (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := rfl

theorem canM_eq_eval (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w))) (y : FrP D w N) :
    canM D w N nu χ y = MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (canPol w N nu χ) := by
  have e1 : (fun s a j => MvPolynomial.eval (fun v : GL3Theta.FrV D N => y v.1 v.2.1 v.2.2) (uFr w N s a j)) =
      fun s => GL3Columns.colsOf (y (tauPl D s)) := by
    funext s a j
    unfold uFr GL3Columns.colsOf
    split_ifs <;> simp
  unfold canPol
  rw [dual_map_eval, deX_map, e1, canM_apply]

theorem canM_ker (hfit : ∀ s c, (nu s).colLen c ≤ N) (χ : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)))
    (h0 : ∀ y, canM D w N nu χ y = 0) (J : KM.ColChoice N nu) :
    χ (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N nu J)) = 0 := by
  refine GL3Columns.wwInj_holds D (D.what₂.places.resChar w) N nu χ (fun y => ?_) J
  let e := Equiv.ofBijective (tauPl D) (Formalism.L2.DIV.tauPl_bijective D)
  have h1 : χ (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ)) (tauPl D s))) = 0 :=
    h0 (fun τ (a b : Fin N) => y (e.symm τ) a (b : ℕ))
  refine Eq.trans (congrArg χ ?_) h1
  unfold GL3Columns.DeX
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => congrArg Matrix.det ?_
  ext i j
  have hj : (j : ℕ) < N := lt_of_lt_of_le j.2 (hfit s c)
  have hs : e.symm (tauPl D s) = s := e.symm_apply_apply s
  simp only [Matrix.of_apply, GL3Columns.colsOf, dif_pos hj, hs]

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

variable {D : D7} (P : Examples₂.EntPl D) (w : D.what₂.places.Pl) (N : ℕ) (nu : Bool × HH D → YoungDiagram)

theorem colsOf_map {k k' : Type} [CommRing k] [CommRing k'] (f : k →+* k') {M : ℕ} (Y : Matrix (Fin M) (Fin M) k) (a : Fin M) (j : ℕ) :
    f (GL3Columns.colsOf Y a j) = GL3Columns.colsOf (Y.map f) a j := by
  unfold GL3Columns.colsOf
  split_ifs <;> simp

theorem onMin_canInv_mem (hfit : ∀ s c, (nu s).colLen c ≤ N) (F : FrP D w N → Cw D w) (hF : F ∈ LinearMap.range (canM D w N nu))
    (hrat : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL, ∃ x, F (fun τ => (y τ).map (P.iL w)) = P.iL w x)
    (J : KM.ColChoice N nu) : ∃ b : D.what₂.LL, onMin D w N nu (canInv D w N nu F) J = P.iL w b := by
  set ψ := canInv D w N nu F with hψdef
  have hψ : canM D w N nu ψ = F := canInv_spec D w N nu F hF
  letI : Algebra D.what₂.LL (Cw D w) := (P.iL w).toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap D.what₂.LL (Cw D w))
    (LinearMap.ker_eq_bot.2 (P.iL w).injective)
  let ρ : Cw D w → Cw D w := fun z => P.iL w (π z)
  have ρ_add : ∀ a b, ρ (a + b) = ρ a + ρ b := fun a b => by
    simp only [ρ, map_add (f := _)]
  have ρ_mul : ∀ x z, ρ (P.iL w x * z) = P.iL w x * ρ z := fun x z => by
    have : P.iL w x * z = x • z := by rw [Algebra.smul_def]; rfl
    simp only [ρ, this, map_smul, smul_eq_mul, map_mul]
  have ρ_fix : ∀ x, ρ (P.iL w x) = P.iL w x := fun x => by
    have := LinearMap.congr_fun hπ x
    simp only [ρ]
    exact congrArg (P.iL w) this
  let ψ' : Module.Dual (Cw D w) (MvPolynomial ((Bool × HH D) × ℕ × Fin N) (Cw D w)) :=
    (MvPolynomial.basisMonomials _ (Cw D w)).constr (Cw D w) fun m => ρ (ψ (monomial m 1))
  have ψ'_mon : ∀ m, ψ' (monomial m 1) = ρ (ψ (monomial m 1)) := fun m => by
    have := (MvPolynomial.basisMonomials ((Bool × HH D) × ℕ × Fin N) (Cw D w)).constr_basis (Cw D w)
      (fun m => ρ (ψ (monomial m 1))) m
    rw [MvPolynomial.coe_basisMonomials] at this
    exact this
  have key : ∀ q : MvPolynomial ((Bool × HH D) × ℕ × Fin N) D.what₂.LL,
      ψ' (MvPolynomial.map (P.iL w) q) = ρ (ψ (MvPolynomial.map (P.iL w) q)) := by
    intro q
    induction q using MvPolynomial.induction_on' with
    | monomial m x =>
      have e : MvPolynomial.map (P.iL w) (monomial m x) = P.iL w x • (monomial m 1 : MvPolynomial _ (Cw D w)) := by
        rw [map_monomial, smul_monomial, smul_eq_mul, mul_one]
      rw [e, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ρ_mul, ψ'_mon]
    | add p q hp hq =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, ρ_add]
  have hpt : ∀ y : D.what₂.Tau → Matrix (Fin N) (Fin N) D.what₂.LL,
      canM D w N nu ψ' (fun τ => (y τ).map (P.iL w)) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w)) := by
    intro y
    have e : (GL3Columns.DeX N nu fun s => GL3Columns.colsOf ((fun τ => (y τ).map (P.iL w)) (tauPl D s))) =
        MvPolynomial.map (P.iL w) (GL3Columns.DeX N nu fun s => GL3Columns.colsOf (y (tauPl D s))) := by
      rw [deX_map]
      congr 1
      funext s a j
      rw [colsOf_map]
    rw [canM_apply, canM_apply, e, key, ← e]
    change ρ (canM D w N nu ψ (fun τ => (y τ).map (P.iL w))) = canM D w N nu ψ (fun τ => (y τ).map (P.iL w))
    obtain ⟨x, hx⟩ := hrat y
    rw [hψ, hx, ρ_fix]
  have hCZ : Set.Infinite (Set.range (Nat.cast : ℕ → Cw D w)) := Set.infinite_range_of_injective Nat.cast_injective
  have hpol : canPol w N nu (ψ' - ψ) = 0 := by
    refine MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → Cw D w)) (fun _ => hCZ) fun x hx => ?_
    choose n hn using fun v => hx v (Set.mem_univ v)
    have e : (fun v : GL3Theta.FrV D N => x v) = fun v => ((fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w)) :
        FrP D w N) v.1 v.2.1 v.2.2 := by
      funext v
      simp [hn]
    have h1 := canM_eq_eval w N nu (ψ' - ψ) (fun τ => (Matrix.of fun a b => ((n (τ, a, b) : ℕ) : D.what₂.LL)).map (P.iL w))
    simp only [map_sub, Pi.sub_apply, hpt, sub_self] at h1
    rw [map_zero, show x = _ from e]
    exact h1.symm
  have h0 : ∀ y, canM D w N nu (ψ' - ψ) y = 0 := fun y => by
    rw [canM_eq_eval, hpol, map_zero]
  have hJ := canM_ker w N nu hfit (ψ' - ψ) h0 J
  have eJ : MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J) =
      MvPolynomial.map (P.iL w) (MvPolynomial.map (Int.castRingHom D.what₂.LL) (KM.nablaX N nu J)) := by
    rw [MvPolynomial.map_map, RingHom.ext_int ((P.iL w).comp (Int.castRingHom _)) (Int.castRingHom _)]
  rw [LinearMap.sub_apply, sub_eq_zero, eJ, key] at hJ
  exact ⟨π (ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J))), by
    show ψ (MvPolynomial.map (Int.castRingHom (Cw D w)) (KM.nablaX N nu J)) = _
    rw [eJ]
    exact hJ.symm⟩

end GlobalTheory.KerVal

namespace GlobalTheory.KerVal
open MvPolynomial Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G

theorem colLen_le_of_fits {D : D7} {N : ℕ} {nu : Bool × HH D → YoungDiagram} {ν : D.what₂.Tau → Fin N → ℕ} (h : NuFits D nu ν) :
    ∀ s c, (nu s).colLen c ≤ N := by
  intro s c
  by_contra hc
  have hm : (N, c) ∈ nu s := (nu s).mem_iff_lt_colLen.2 (lt_of_not_ge hc)
  have h1 := (nu s).mem_iff_lt_rowLen.1 hm
  rw [h.2 s N le_rfl] at h1
  exact Nat.not_lt_zero _ h1

theorem tgtFun_rat {D : D7} (P : Examples₂.EntPl D) (Bs : PlaceMatrixFamily D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) (i : ℕ)
    (c' : (D.chTw u μ).cls (i + 1)) (hE : ∀ τ j k, ∃ x : D.what₂.LL, Bs u μ w (i + 1) c' τ j k = P.iL w x) (v : polV D u (i + 1))
    (y : D.what₂.Tau → Matrix (Fin (D.R.N (i + 1))) (Fin (D.R.N (i + 1))) D.what₂.LL) :
    ∃ x, tgtFun P Bs u μ w i c' v (fun τ => (y τ).map (P.iL w)) = P.iL w x := by
  choose B' hB' using hE
  have hB : Bs u μ w (i + 1) c' = fun τ => (Matrix.of (B' τ)).map (P.iL w) := by
    funext τ
    ext j k
    exact hB' τ j k
  refine ⟨(∏ τ, (Matrix.of (B' τ)).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL), ?_⟩
  show (∏ τ, (Bs u μ w (i + 1) c' τ).det ^ (-(D.chTw u μ).sDiv i τ)) *
    MvPolynomial.eval (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Bs u μ w (i + 1) c' k.1 * (y k.1).map (P.iL w)) k.2.1 k.2.2)
      (MvPolynomial.map (P.iL w) (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)) = _
  rw [hB, map_mul, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_zpow₀, RingHom.map_det]
    rfl
  · have h2 := MvPolynomial.eval₂_comp_left (P.iL w) (RingHom.id D.what₂.LL)
      (fun k : GL3Theta.FrV D (D.R.N (i + 1)) => (Matrix.of (B' k.1) * y k.1) k.2.1 k.2.2)
      (v : MvPolynomial (GL3Theta.FrV D (D.R.N (i + 1))) D.what₂.LL)
    refine Eq.trans ?_ h2.symm
    rw [MvPolynomial.eval_map, RingHom.comp_id]
    congr 1
    funext k
    rw [Function.comp_apply, ← Matrix.map_mul]
    rfl

end GlobalTheory.KerVal

theorem GlobalTheory.KerVal.prTC_val : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v' : ValQ O u μ (i + 1)) (J : KM.ColChoice ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i)), ∃ b : (I.rec7 l Z).what₂.LL, ‖prTC Pl O Bs u μ w i c' v' J‖ = ‖Pl.iL w b‖ := by
  intro B X I _ _ l Z _ Y O Pl Bs _ _ _ hEnt _ _ u μ w hw i hi c' v' J
  obtain ⟨b, hb⟩ := GlobalTheory.KerVal.onMin_canInv_mem Pl w _ _
    (GlobalTheory.KerVal.colLen_le_of_fits (nuFits_tgt (I.rec7 l Z) u i hi))
    (tgtFun Pl Bs u μ w i c' (secC O u μ (i + 1) v'))
    (canT_of Pl Bs (_root_.GlobalTheory.Mem.CanonicalSurjection.canOnto_all _ Pl) u μ w i hi c' (secC O u μ (i + 1) v'))
    (GlobalTheory.KerVal.tgtFun_rat Pl Bs u μ w i c' (hEnt u μ w hw (i + 1) hi c') (secC O u μ (i + 1) v')) J
  exact ⟨b, congrArg norm hb⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFockVacuumProperties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VecP


open scoped ComplexOrder in
theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hε1 : ∀ a, ε a = 1 := fun a =>
    ((hε a).resolve_right fun h' => absurd h'.2 (not_le.mpr a.2)).1
  have hB1 : Bᴴ * G * B = 1 := by simpa [hε1] using hB
  have hBC : B * (Bᴴ * G) = 1 := mul_eq_one_comm.mp hB1
  have hGB : G * B = (Bᴴ * G)ᴴ := by
    calc G * B = (B * (Bᴴ * G))ᴴ * (G * B) := by rw [hBC, conjTranspose_one, Matrix.one_mul]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ := by rw [hB1, Matrix.mul_one]
  have hG : G = (Bᴴ * G)ᴴ * (Bᴴ * G) := by
    calc G = G * (B * (Bᴴ * G)) := by rw [hBC, Matrix.mul_one]
      _ = G * B * (Bᴴ * G) := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G) := by rw [hGB]
  have hinj : Function.Injective (Bᴴ * G).mulVec := by
    intro v w hvw
    have h2 := congrArg (fun x => B *ᵥ x) hvw
    simpa only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec] using h2
  unfold IsCartanInv
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end GlobalTheory.OneMapRef.VecP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilTiedEqOfEqTied
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Th

theorem weilTiedEq_of_eqTied : ∀ (D : D7) (X : ThetaX D) (T : ThetaTied D X) (W : WeilTied D X T), WeilThetaCompatibility W → WeilCompatibleEquivariance W :=
  fun _ _ _ _ h => ⟨h.range, h.Heisenberg₂, h.aut, h.cont, h.unit, h.split, ⟨h.twW, h.twV⟩, h.th⟩

end GlobalTheory.Mem.Th
end

