module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterDecompositionAndClassFunctionExpansion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism

section Defs

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]


variable (l) in
def LTo0 {ι : Type} (w : ι → Wq l a) : Prop := ∀ r : ℕ, ∀ᶠ n in cofinite, (l : Wq l a) ^ r ∣ w n

variable (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def SdSet : Set (ZMod a → K⟦X⟧) :=
  {F | ∃ w : ℕ → Wq l a, LTo0 l w ∧
    ∀ τ n, ((n / e).factorial : K) * coeff n (F τ) = algebraMap O K (emb t τ (w n))}

def Sd : Subring (ZMod a → K⟦X⟧) := Subring.closure (SdSet t K e)

def PPSet : Set (ZMod a → K⟦X⟧⟦X⟧) :=
  {F | ∃ w : ℕ × ℕ → Wq l a, LTo0 l w ∧
    ∀ τ i n, ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (F τ)) =
      algebraMap O K (emb t τ (w (i, n)))}

def PPd : Subring (ZMod a → K⟦X⟧⟦X⟧) := Subring.closure (PPSet t K e)

def inclS : (Wq l a)⟦X⟧ →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (A O K).val.toRingHom.comp ((Pi.evalRingHom (fun _ : ZMod a => A O K) τ).comp (toAc t K))

theorem inclS_apply (x : (Wq l a)⟦X⟧) (τ : ZMod a) : inclS t K x τ = (toAc t K x τ : K⟦X⟧) := rfl

variable {K}

def frob2 (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => φ₂.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) (τ - 1))


variable (a K) in
def constP : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)


variable (a) in
def shP (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) : (ZMod a → K⟦X⟧) →+* (ZMod a → K⟦X⟧⟦X⟧) :=
  Pi.ringHom fun τ => sh.comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧) τ)


variable (a K) in
def diag : (ZMod a → K⟦X⟧⟦X⟧) →+* (ZMod a → K⟦X⟧) :=
  Pi.ringHom fun τ => (constantCoeff : K⟦X⟧⟦X⟧ →+* K⟦X⟧).comp (Pi.evalRingHom (fun _ : ZMod a => K⟦X⟧⟦X⟧) τ)

end Defs

theorem tf_pi {R : Type} [CommRing R] [IsDomain R] {n a : ℕ} (hn : (n : R) ≠ 0) (x : ZMod a → R)
    (h : (n : ZMod a → R) * x = 0) : x = 0 := funext fun τ => by
  have h1 := congrFun h τ
  simp only [Pi.mul_apply, Pi.natCast_apply, Pi.zero_apply] at h1
  exact (mul_eq_zero.1 h1).resolve_left hn

theorem natCast_ne_zero_ps {R : Type} [CommRing R] {n : ℕ} (h : (n : R) ≠ 0) : (n : R⟦X⟧) ≠ 0 := fun h' =>
  h (by simpa using congrArg (constantCoeff : R⟦X⟧ →+* R) h')

theorem tf_sub {R : Type} [CommRing R] {n : ℕ} (s : Subring R) (htf : ∀ x : R, (n : R) * x = 0 → x = 0)
    (x : ↥s) (h : (n : ↥s) * x = 0) : x = 0 := Subtype.ext (htf _ (by simpa using congrArg Subtype.val h))

theorem nzd_of_tf {R : Type} [CommRing R] {n : ℕ} (htf : ∀ x : R, (n : R) * x = 0 → x = 0) :
    (n : R) ∈ nonZeroDivisors R :=
  mem_nonZeroDivisors_iff.2 ⟨htf, fun x hx => htf x (by rw [mul_comm]; exact hx)⟩

theorem bdd_self {R : Type} [CommRing R] (n : ℕ) : ∃ m : ℕ, ∀ x : R ⧸ Ideal.span {(n : R)},
    (∃ k : ℕ, (n : R ⧸ Ideal.span {(n : R)}) ^ k * x = 0) → (n : R ⧸ Ideal.span {(n : R)}) ^ m * x = 0 := by
  refine ⟨1, fun x _ => ?_⟩
  have h : (n : R ⧸ Ideal.span {(n : R)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(n : R)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [h, pow_one, zero_mul]

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_delta_l {A : Type} [CommRing A] (D : Delta l A) (htf : ∀ x : A, (l : A) * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span {(l : A)}) A] : IsUnit (D.δ l) := by
  have h1 : D.δ l = 1 - (l : A) ^ (l - 1) := by
    rw [← sub_eq_zero]
    apply htf
    have h := D.φ_eq (l : A)
    rw [map_natCast] at h
    have h2 : (l : A) ^ l = (l : A) * (l : A) ^ (l - 1) := by
      rw [← pow_succ']; congr 1; have := hl.out.one_lt; omega
    linear_combination -h - h2
  rw [h1]
  have hm : -(l : A) ^ (l - 1) ∈ Ideal.span {(l : A)} := (Ideal.neg_mem_iff _).2
    (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (by have := hl.out.one_lt; omega))
  have := Ideal.mem_jacobson_bot.1 (IsAdicComplete.le_jacobson_bot _ hm) 1
  rwa [mul_one, neg_add_eq_sub] at this

section Sh

variable {K : Type} [NormedField K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
  (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f)
include hsh

theorem constantCoeff_sh (f : K⟦X⟧) : constantCoeff (sh f) = f := by
  simpa using hsh f 0

theorem sh_X : sh X = C X + X := by
  ext i : 1
  have h := hsh X i
  rcases i with _ | _ | i
  · simpa using h
  · simp [coeff_C, coeff_X]
    simpa [derivative_X] using h
  · have h3 : ((i + 2).factorial : K⟦X⟧) ≠ 0 := natCast_ne_zero_ps (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))
    have h4 : (PowerSeries.derivative (R := K))^[i + 2] X = 0 := by
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, derivative_X]
      rw [derivative_one]
      exact iterate_derivative_zero
    rw [h4] at h
    rw [(mul_eq_zero.1 h).resolve_left h3]
    simp [coeff_C, coeff_X]

theorem constantCoeff_φ₂ (l : ℕ) [Fact l.Prime] (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hφC : ∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f))
    (hφsh : ∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) (G : K⟦X⟧⟦X⟧) :
    constantCoeff (φ₂ G) = frob K l (constantCoeff G) := by
  have hX : φ₂ X = sh (X ^ l) - C (X ^ l) := by
    have h : (X : K⟦X⟧⟦X⟧) = sh X - C X := by rw [sh_X sh hsh]; ring
    rw [h, map_sub, hφsh, hφC, frob_X]
  conv_lhs => rw [eq_shift_mul_X_add_const G]
  rw [map_add (f := _), map_mul, hX, hφC, map_add (f := _), map_mul, map_sub, constantCoeff_sh sh hsh, constantCoeff_C,
    constantCoeff_C, sub_self, mul_zero, zero_add]

end Sh

section Maps

variable {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem constP_mem {F : ZMod a → K⟦X⟧} (hF : F ∈ SdSet t K e) : constP a K F ∈ PPSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun p => if p.1 = 0 then w p.2 else 0, fun r => ?_, fun τ i n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    refine (h.image fun n => ((0 : ℕ), n)).subset ?_
    rintro ⟨i, n⟩ hin
    by_cases hi : i = 0
    · subst hi; exact ⟨n, by simpa using hin, rfl⟩
    · simp [hi] at hin
  · change ((i.factorial * (n / e).factorial : ℕ) : K) * coeff n (coeff i (C (F τ))) = _
    rw [coeff_C]
    by_cases hi : i = 0
    · subst hi; simpa using hF τ n
    · simp [hi]

theorem diag_mem {F : ZMod a → K⟦X⟧⟦X⟧} (hF : F ∈ PPSet t K e) : diag a K F ∈ SdSet t K e := by
  obtain ⟨w, hw, hF⟩ := hF
  refine ⟨fun n => w (0, n), fun r => ?_, fun τ n => ?_⟩
  · have h := hw r
    rw [Filter.eventually_cofinite] at h ⊢
    exact h.preimage (fun _ _ _ _ h => by simpa using h)
  · have h := hF τ 0 n
    simp only [Nat.factorial_zero, one_mul, coeff_zero_eq_constantCoeff] at h
    exact h

end Maps

end GlobalTheory.CrysPrism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NcardGenericIrreducibleCharactersGLnLe
section
noncomputable section

open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.GenericCount

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem ip_comm {G : Type} [Group G] [Fintype G] (α β : G → ℂ) : ip α β = ip β α := by
  unfold ip
  congr 1
  exact Fintype.sum_equiv (Equiv.inv G) _ _ (fun x => by simp [mul_comm])

theorem tr_finset_sum {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (S : Finset (G → ℂ))
    (c : (G → ℂ) → ℂ) : tr a (∑ ρ ∈ S, c ρ • ρ) = ∑ ρ ∈ S, c ρ * tr a ρ := by
  unfold tr
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun x _ => by ring

theorem gg_isClass {g : ℕ} [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  simp only [gg]
  congr 1
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun y => ?_)
  have h : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, h]

end GlobalTheory.GLq.GenericCount

namespace GlobalTheory.GLq


open GlobalTheory.GLq.GenericCount in
theorem card_generic_irr_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ n : ℕ, 0 < n →
    Set.ncard {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} ≤ g ^ n - g ^ (n - 1) := by
  intro g _ ψ hψ n hn
  obtain ⟨hfin, -⟩ := GlobalTheory.T.finite_irrCharacters_and_finsum_centralIdempotents_eq_one (Gn g n)
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ IsIrr ρ := fun ρ => by rw [hS, Set.Finite.mem_toFinset]; rfl
  have hnorm := _root_.GlobalTheory.GLq.GGNorm.gg_norm g ψ hψ n hn
  have hdec := (_root_.GlobalTheory.charDec (Gn g n) (gg ψ n)).2.1 (gg_isClass ψ n)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hdec
  have hirrC : ∀ ρ : Gn g n → ℂ, IsIrr ρ → IsClass ρ := fun ρ h =>
    (_root_.GlobalTheory.charDec (Gn g n) ρ).2.2.1 (isChar_of_isIrr h)
  have hnat : ∀ ρ : Gn g n → ℂ, IsIrr ρ → ∃ m : ℕ, wh ψ ρ = m := fun ρ h =>
    (_root_.GlobalTheory.GLq.trIdem (Gn g n) (eU g n ψ) ρ).1 (_root_.GlobalTheory.Adopt.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).1 (isChar_of_isIrr h)
  choose! m hm using hnat
  have hsum : ((∑ ρ ∈ S, m ρ ^ 2 : ℕ) : ℂ) = ((g ^ n - g ^ (n - 1) : ℕ) : ℂ) := by
    rw [Nat.cast_sub (Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (Nat.sub_le n 1))]
    push_cast
    rw [← hnorm.1]
    have hw : wh ψ (gg ψ n) = ∑ ρ ∈ S, ip (gg ψ n) ρ * wh ψ ρ := by
      conv_lhs => rw [hdec]
      unfold wh
      exact tr_finset_sum _ _ _
    rw [hw]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have hI := (hmemS ρ).1 hρ
    rw [ip_comm, hnorm.2 ρ (hirrC ρ hI), hm ρ hI]
    ring
  have hsumN : ∑ ρ ∈ S, m ρ ^ 2 = g ^ n - g ^ (n - 1) := by exact_mod_cast hsum
  have hset : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0} = ↑(S.filter fun ρ => m ρ ≠ 0) := by
    ext ρ
    simp only [Set.mem_setOf_eq, Finset.coe_filter, hmemS]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1, h0, Nat.cast_zero])⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun h0 => h2 (by rw [hm ρ h1] at h0; exact_mod_cast h0)⟩
  rw [hset, Set.ncard_coe_finset, ← hsumN, Finset.card_eq_sum_ones]
  calc ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), 1 ≤ ∑ ρ ∈ S.filter (fun ρ => m ρ ≠ 0), m ρ ^ 2 :=
        Finset.sum_le_sum fun ρ hρ => Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (Finset.mem_filter.1 hρ).2)
    _ ≤ ∑ ρ ∈ S, m ρ ^ 2 := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

end GlobalTheory.GLq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvAtTypePrimes
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.NoLocalInvariants

section General

variable {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]

theorem eq_zero_of_fixed {M : Matrix n n R} (h : (M - 1).det ≠ 0)
    {x : n → FractionRing R} (hx : (M.map (algebraMap R (FractionRing R))).mulVec x = x) : x = 0 := by
  have h1 : ((M - 1).map (algebraMap R (FractionRing R))).mulVec x = 0 := by
    have e : (M - 1).map (algebraMap R (FractionRing R)) =
        M.map (algebraMap R (FractionRing R)) - 1 := by
      ext a b
      simp [Matrix.sub_apply, Matrix.one_apply, apply_ite (algebraMap R (FractionRing R))]
    rw [e, Matrix.sub_mulVec, hx, Matrix.one_mulVec, sub_self]
  have h2 : ((M - 1).map (algebraMap R (FractionRing R))).det ≠ 0 := by
    have e : ((M - 1).map (algebraMap R (FractionRing R))).det =
        algebraMap R (FractionRing R) (M - 1).det := by
      simpa using ((algebraMap R (FractionRing R)).map_det (M - 1)).symm
    rw [e]
    exact fun h0 => h ((IsFractionRing.injective R (FractionRing R)) (by simpa using h0))
  exact Matrix.eq_zero_of_mulVec_eq_zero h2 h1

theorem det_inv_transpose_sub_one_ne_zero {M : Matrix n n R} (hu : IsUnit M.det)
    (h : (M - 1).det ≠ 0) : ((M⁻¹).transpose - 1).det ≠ 0 := by
  have e : (M⁻¹).transpose - 1 = (M⁻¹ - 1).transpose := by simp
  rw [e, Matrix.det_transpose]
  intro h0
  have h1 : (M⁻¹ - 1) * M = -(M - 1) := by
    rw [sub_mul, Matrix.nonsing_inv_mul _ hu, one_mul]
    abel
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_neg] at h2
  have h3 : ((-1 : R) ^ Fintype.card n) ≠ 0 := pow_ne_zero _ (by simp)
  exact h (by simpa [h3] using h2.symm)


omit [IsDomain R] in
theorem det_scaled_sub_one_ne_zero [IsLocalRing R] (P : Matrix n n R) (c : Rˣ)
    (h : (P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _)).det ≠ 0) :
    ((((c⁻¹ : Rˣ) : R) • P) - 1).det ≠ 0 := by
  intro h0
  have e1 : P - (c : R) • (1 : Matrix n n R) = (c : R) • ((((c⁻¹ : Rˣ) : R) • P) - 1) := by
    rw [smul_sub, smul_smul, Units.mul_inv, one_smul]
  have e2 : (P - (c : R) • (1 : Matrix n n R)).det = 0 := by
    rw [e1, Matrix.det_smul, h0, mul_zero]
  apply h
  have e3 : P.map (IsLocalRing.residue R) - (IsLocalRing.residue R (c : R)) • (1 : Matrix n n _) =
      (P - (c : R) • (1 : Matrix n n R)).map (IsLocalRing.residue R) := by
    ext a b
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite (IsLocalRing.residue R)]
  rw [e3]
  have := (IsLocalRing.residue R).map_det (P - (c : R) • (1 : Matrix n n R))
  rw [e2, map_zero] at this
  simpa using this.symm

end General

theorem noInv_of_adm2At : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → ∀ k, D.host.g k ≠ D.ntw.l i → ∀ v ∈ placesOver D.host.E (D.host.g k), NoInv i (Tmat i s) v ∧ NoInv i (Tdual i s) v := by
  intro D i s h k hk v hv
  have hvl : v ∉ placesOver D.host.E (D.ntw.l i) := by
    intro hl
    have hlp : (D.ntw.l i).Prime := Fact.out
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2
      ((Nat.coprime_primes (D.host.g_prime k) hlp).2 hk)
    have h1 : (1 : 𝓞 D.host.E) ∈ v.asIdeal := by
      have e : (1 : 𝓞 D.host.E) = (a : 𝓞 D.host.E) * ((D.host.g k : ℕ) : 𝓞 D.host.E) +
          (b : 𝓞 D.host.E) * ((D.ntw.l i : ℕ) : 𝓞 D.host.E) := by
        have h2 := congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
        push_cast at h2
        exact h2.symm
      rw [e]
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hv) (v.asIdeal.mul_mem_left _ hl)
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  have key : ∀ A : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) A v →
      ∃ σ ∈ Ine (F := D.host.E) A, (Tmat i s σ - 1).det ≠ 0 := by
    intro A hA
    obtain ⟨-, σ, hσ, hdet⟩ := h.2 k hk v hv A hA
    exact ⟨σ, hσ, det_scaled_sub_one_ne_zero _ _ hdet⟩
  constructor
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    exact eq_zero_of_fixed hd (hx σ (Ine_le_Dec A hσ))
  · intro A hA x hx
    obtain ⟨σ, hσ, hd⟩ := key A hA
    have he := (GlobalTheory.TripleGal.eps0_unram_frob D i v hvl A hA).1 σ hσ
    have hu : IsUnit (Tmat i s σ).det := by
      rw [← Tgl_coe]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    have hT : Tdual i s σ = ((Tmat i s σ)⁻¹).transpose := by
      simp [Tdual, he]
    have := hx σ (Ine_le_Dec A hσ)
    rw [hT] at this
    exact eq_zero_of_fixed (det_inv_transpose_sub_one_ne_zero hu hd) this

end GlobalTheory.NoLocalInvariants
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEisensteinMulClosedDiscEqRpow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem BK.exists_Ep_eq_X_pow_add {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : Polynomial (Wq l bk.a),
      bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | hi | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos hi, hi, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hi, sub_zero]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  exact ⟨q, by rw [← hq]; ring⟩

theorem BK.norm_toDisc_E_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ < 1 →
    ∀ y : bk.DS ρ, ‖toDisc l (X : bk.S) ρ bk.E * y‖ = (ρ : ℝ) ^ bk.Ep.natDegree * ‖y‖ := by
  intro l _ K bk ρ h0 h1 y
  obtain ⟨_, _, ⟨hρ0, _, hρe⟩, _⟩ := _root_.GlobalTheory.BSP.flat_disc l K bk
  have hρ : 0 < ρ := hρ0.trans_le h0
  rw [_root_.GlobalTheory.BSP.GaussMul.norm_mul l K bk ρ hρ h1]
  congr 1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  apply le_antisymm
  · obtain ⟨q, hq⟩ := bk.exists_Ep_eq_X_pow_add
    have hE : bk.E = (X : bk.S) ^ bk.Ep.natDegree + (l : bk.S) * (q : bk.S) := by
      simp only [BK.E]
      conv_lhs => rw [hq]
      rw [Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C,
        map_natCast]
    have hl' : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ ≤ (l : ℝ)⁻¹ :=
      gauge_le l (X : bk.S) ρ (by positivity) (Submodule.subset_span ⟨1, 0, 0,
        by rw [pow_zero, pow_zero, pow_one, inv_mul_cancel₀ hl0.ne', mul_one], by simp⟩)
    have hX : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) ((X : bk.S) ^ bk.Ep.natDegree)‖ ≤
        (ρ : ℝ) ^ bk.Ep.natDegree :=
      (norm_ofPre l (X : bk.S) ρ _).symm.trans_le (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) _ hρ)
    have hup : ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) bk.E‖ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
      rw [hE, map_add (f := _), map_mul, norm_preDisc]
      refine (gauge_add_le_max l (X : bk.S) ρ _ _).trans (max_le ?_ ?_)
      · rw [← norm_preDisc]; exact hX
      · rw [← norm_preDisc]
        calc _ ≤ ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (l : bk.S)‖ *
              ‖algebraMap bk.S (PreDisc l (X : bk.S) ρ) (q : bk.S)‖ := norm_mul_le _ _
          _ ≤ (l : ℝ)⁻¹ * 1 := mul_le_mul hl' (norm_algebraMap_le _) (norm_nonneg _) (by positivity)
          _ = ((bk.ρ₀ ^ bk.Ep.natDegree : ℝ≥0) : ℝ) := by rw [hρe]; simp
          _ ≤ (ρ : ℝ) ^ bk.Ep.natDegree := by
            rw [NNReal.coe_pow]; exact pow_le_pow_left₀ (NNReal.coe_nonneg _) (by exact_mod_cast h0) _
    exact (norm_ofPre l (X : bk.S) ρ _).trans_le hup
  · obtain ⟨a, ha1, ha2, -, -⟩ := _root_.GlobalTheory.BSP.DiscSer.exists_coeff_disc l K bk ρ hρ h1
    obtain ⟨-, -, -, hk⟩ := _root_.GlobalTheory.BSP.disc_zero_one l K bk
    have hc : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [BK.E, Polynomial.coeff_coe, bk.monic.coeff_natDegree]
    have h := ha2 bk.Ep.natDegree (toDisc l (X : bk.S) ρ bk.E)
    rw [ha1, hc, hk 1 isUnit_one, one_mul] at h
    exact h

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecordCaseA
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.DdREqDcris

theorem record_caseA : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K LL : FinExt l), CaseA K LL →
    Formalism.MainNotions.TruncatedSeriesCountingBounds.DdREqDcris ((D.loc l).PD K) ↥LL.1 := by
  intro D l _ K LL _ hb V _ _ _ _ _ ρ _ _ _ hc
  exact map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.Per.DdREqDcris
end

