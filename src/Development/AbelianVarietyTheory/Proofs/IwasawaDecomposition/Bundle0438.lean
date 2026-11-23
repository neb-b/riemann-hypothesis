module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0374
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdAtEntryEqOneOfNotOver
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdSupport

theorem adAt_entry_eq_one_of_not_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hz : ∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ Formalism.L2.Col.IsOver v P)
    (r s : Fin n) :
    adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  have hne : P.under (𝓞 F) ≠ v := by
    intro h
    apply hP
    rw [← h]
    rfl
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s) (hz _ hne)
  have h3 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s := h2
  have h4 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = 0 := by
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h5 := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E (P.under (𝓞 F)) _).1.1 h4) P rfl
  rw [map_sub, sub_eq_zero] at h5
  rw [h5, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdSupport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceBadPrimeIffCompletion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary

theorem vAlg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

theorem v_qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (hp : (qOf P).Prime)
    (h2 : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  have e : ((qOf P : ℕ) : P.adicCompletion E) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E)) := by
    simp
  rw [e, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  have hmem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 1 := by
    rw [pow_one]
    exact Ideal.absNorm_mem P.asIdeal
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 1).2 hmem
  have h2' : ¬ P.intValuation ((qOf P : ℕ) : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 2).1 h)
  have hne : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := by
    have : ((qOf P : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    exact (HeightOneSpectrum.intValuation_ne_zero P _ this)
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  congr 1
  push_cast at h1 h2'
  omega

theorem exists_clear {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hP : Valued.v (y P) ≤ 1) : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * y Q) ≤ 1 := by
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | ¬ y Q ∈ Q.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.1 y.2
  set S := hfin.toFinset with hS
  have memS : ∀ Q, Q ∈ S ↔ 1 < Valued.v (y Q) := by
    intro Q
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]
  have hPS : P ∉ S := fun h => absurd hP (not_le.2 ((memS P).1 h))
  let m : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (y Q))).toNat
  let J : Ideal (𝓞 E) := ∏ Q ∈ S, Q.asIdeal ^ m Q
  have hJ : ¬ J ≤ P.asIdeal := by
    intro h
    obtain ⟨Q, hQ, hle⟩ := (Ideal.IsPrime.prod_le P.isPrime).1 h
    have h1 : Q.asIdeal ≤ P.asIdeal := by
      by_cases hm : m Q = 0
      · exfalso
        have h3 := (memS Q).1 hQ
        have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one h3)
        rw [← WithZero.exp_log hne] at h3
        have h4 : (0 : ℤ) < WithZero.log (Valued.v (y Q)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          exact h3
        have : m Q ≠ 0 := by
          show (WithZero.log (Valued.v (y Q))).toNat ≠ 0
          omega
        exact this hm
      · exact P.isPrime.le_of_pow_le hle
    have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
    exact hPS (h2 ▸ hQ)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJ
  refine ⟨s, hsP, fun Q => ?_⟩
  rw [map_mul, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hQ : Q ∈ S
  · have hsQ : s ∈ Q.asIdeal ^ m Q :=
      (Finset.inf_le (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal ^ m Q) hQ) (Ideal.prod_le_inf hsJ)
    have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem Q s (m Q)).2 hsQ
    have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one ((memS Q).1 hQ))
    have h2 : Valued.v (y Q) ≤ WithZero.exp ((m Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      show WithZero.log (Valued.v (y Q)) ≤ ((WithZero.log (Valued.v (y Q))).toNat : ℤ)
      omega
    calc Q.intValuation s * Valued.v (y Q) ≤ WithZero.exp (-((m Q : ℕ) : ℤ)) * WithZero.exp ((m Q : ℕ) : ℤ) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · have h1 : Valued.v (y Q) ≤ 1 := not_lt.1 fun h => hQ ((memS Q).2 h)
    exact mul_le_one' (HeightOneSpectrum.intValuation_le_one Q s) h1

theorem intAtA_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : AfE F E) :
    IntAtA (F := F) P x ↔ Valued.v (adAt F P x) ≤ 1 := by
  constructor
  · intro h
    exact GlobalTheory.TwU.IsAdIso.val_le (ι := afIso F E) ⟨afIso_tmul_one F E, mem_rInt_iff F E⟩ h
  · intro h
    obtain ⟨s, hs, hall⟩ := exists_clear P (afIso F E x) h
    refine ⟨s, hs, ?_⟩
    show _ ∈ RInt F E
    rw [mem_rInt_iff]
    intro Q
    have e : afIso F E (iA F E (algebraMap (𝓞 E) E s) * x) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * afIso F E x Q := by
      rw [map_mul]
      have h2 : afIso F E (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) :=
        afIso_tmul_one F E _
      rw [h2]
      rfl
    rw [e]
    exact hall Q

theorem entry_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (N : ℕ) (z : GL (Fin n) (AfE F E)) (r s : Fin n) :
    IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ N)⁻¹ * ((z : Matrix (Fin n) (Fin n) (AfE F E)) - 1) r s) ↔
      Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [intAtA_iff, map_mul, adAt_inclE, Matrix.sub_apply, map_sub]
  have h1 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  rw [h1, map_mul, map_inv₀, map_pow, map_natCast, map_inv₀, map_pow, hq]
  have hE : (WithZero.exp (-1 : ℤ) ^ N)⁻¹ = WithZero.exp (N : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]
    congr 1
    simp
  rw [hE]
  generalize Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) = x
  have hm : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
    rw [← WithZero.exp_add]; simp
  constructor
  · intro h
    calc x = (WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ)) * x := by rw [hm, one_mul]
      _ = WithZero.exp (-(N : ℤ)) * (WithZero.exp (N : ℤ) * x) := mul_assoc _ _ _
      _ ≤ WithZero.exp (-(N : ℤ)) * 1 := mul_le_mul' le_rfl h
      _ = WithZero.exp (-(N : ℤ)) := mul_one _
  · intro h
    calc WithZero.exp (N : ℤ) * x ≤ WithZero.exp (N : ℤ) * WithZero.exp (-(N : ℤ)) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hm]

theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n N : ℕ) (P : SBof I a) (z : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 ∧ Valued.v ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) = WithZero.exp (-1 : ℤ) ∧ (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ↔ ∀ r s, Valued.v (adAt B.host.F P.1 (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  intro B X I hI l Z a n N P z
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x
  have hdeg := degOne_of_ok hI a P
  have hq := v_qOf P.1 hdeg.1 hdeg.2
  refine ⟨hseam, hq, ?_⟩
  rw [hseam]
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact forall_congr' fun r => forall_congr' fun s => @entry_iff (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ P.1 hq n N z r s
end GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrame
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CongMove

open GlobalTheory.TwU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

theorem intAtA_sum {ι : Type} (s : Finset ι) (f : ι → E ⊗[F] FiniteAdeleRing (𝓞 F) F)
    (h : ∀ i ∈ s, IntAtA (F := F) P (f i)) : IntAtA (F := F) P (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using intAtA_int (F := F) (P := P) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intAtA_add (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intAtA_one_apply (a b : Fin N) :
    IntAtA (F := F) P ((1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) := by
  rw [Matrix.one_apply]
  split_ifs
  · simpa using intAtA_int (F := F) (P := P) 1
  · simpa using intAtA_int (F := F) (P := P) 0

theorem qpow_facts (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) :
    iA F E (((qOf P : ℕ) : E) ^ n) * iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ = 1 ∧
      IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ n)) := by
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  refine ⟨by rw [← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one], ?_⟩
  have := intAtA_int (F := F) (P := P) (((qOf P : ℕ) : 𝓞 E) ^ n)
  simpa using this

theorem intAtA_of_congAt (n : ℕ) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (a b : Fin N) :
    IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b) := by
  obtain ⟨hdc, hd⟩ := qpow_facts (F := F) P n
  have e : (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b =
      (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b +
        iA F E (((qOf P : ℕ) : E) ^ n) * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ *
          ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) := by
    rw [← mul_assoc, hdc, one_mul, Matrix.sub_apply]; ring
  rw [e]
  exact intAtA_add (intAtA_one_apply a b) (intAtA_mul hd (h a b))

theorem congAt_mul (n : ℕ) {k k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P n k) (h' : CongAt P n k') :
    CongAt P n (k * k') := by
  intro a b
  have hk' := intAtA_of_congAt n h'
  set K := (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set K' := (k' : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have e : ((k * k' : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      (K - 1) * K' + (K' - 1) := by
    rw [Units.val_mul, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum]
  refine intAtA_add (intAtA_sum _ _ fun j _ => ?_) (h' a b)
  rw [← mul_assoc]
  exact intAtA_mul (h a j) (hk' j b)

theorem congAt_conj (n : ℕ) {A B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (hA : CongAt P n A)
    (hB : ∀ r s, IntAtA (F := F) P ((B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s))
    (hBi : ∀ r s, IntAtA (F := F) P (((B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :
      Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s)) :
    CongAt P n (B⁻¹ * A * B) := by
  intro a b
  set Bm := (B : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set Bi := ((B⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  set Am := (A : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
  have hBB : Bi * Bm = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e : ((B⁻¹ * A * B : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1 =
      Bi * ((Am - 1) * Bm) := by
    rw [Units.val_mul, Units.val_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, ← hBB, Matrix.mul_assoc]
  rw [e, Matrix.mul_apply, Finset.mul_sum]
  refine intAtA_sum _ _ fun j _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum, Finset.mul_sum]
  refine intAtA_sum _ _ fun l _ => ?_
  have e2 : iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (Bi a j * ((Am - 1) j l * Bm l b)) =
      Bi a j * (iA F E (((qOf P : ℕ) : E) ^ n)⁻¹ * (Am - 1) j l) * Bm l b := by ring
  rw [e2]
  exact intAtA_mul (intAtA_mul (hBi a j) (hA j l)) (hB l b)

end GlobalTheory.CongMove

namespace GlobalTheory.CongMove

open GlobalTheory.TwU

theorem nearAt_conj_ratA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (κ x k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (f g : GL (Fin N) E)
    (hk : ∀ r s, IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hki : ∀ r s, IntAtA (F := F) P (((k⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hm : ∀ r s, IntAtA (F := F) P (((k⁻¹ * x * k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hmi : ∀ r s, IntAtA (F := F) P ((((k⁻¹ * x * k)⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) :
      Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s))
    (hκ : GlobalTheory.TwU.CongAt P n (κ⁻¹ * x)) (hg : GlobalTheory.TwU.NearAt P n (k⁻¹ * x * k) g)
    (he : GlobalTheory.TwU.CongAt P n (k⁻¹ * GlobalTheory.TwU.ratA F f)) (hei : GlobalTheory.TwU.CongAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * k)) :
    GlobalTheory.TwU.NearAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * κ * GlobalTheory.TwU.ratA F f) g := by
  unfold NearAt at hg ⊢
  set Fr := ratA F f
  set G := ratA F g
  set m := k⁻¹ * x * k
  have key : (Fr⁻¹ * κ * Fr)⁻¹ * G =
      (Fr⁻¹ * k) * (k⁻¹ * (κ⁻¹ * x) * k) * (m⁻¹ * (k⁻¹ * Fr) * m) * (m⁻¹ * G) := by
    simp only [m]
    group
  rw [key]
  refine congAt_mul n (congAt_mul n (congAt_mul n hei ?_) ?_) hg
  · have h := congAt_conj n hκ (B := k) hk hki
    simpa only [inv_inv] using h
  · have h := congAt_conj n he (B := m) hm hmi
    exact h

end GlobalTheory.CongMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseRowCountEqFinrankTypePartBaseLevelStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseRowCount_eq_finrank_typePart_baseLevel : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  first | exact @GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE | exact GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE | (intros; apply GlobalTheory.BaseRowCount.nRows0_eq_finrank_isotE <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwinerStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_lastStep_real_intertwiner : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.chain_ωX → R.chain_vX → R.chain_ptX ∧ ∃ It, ({ R with ItX := It } : RealDat D A Ks).chain_ItX := by
  first | exact @GlobalTheory.CompactHowe.LastStep.lastStep_intertwiner | exact GlobalTheory.CompactHowe.LastStep.lastStep_intertwiner | (intros; apply GlobalTheory.CompactHowe.LastStep.lastStep_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChain
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P ∈ SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P) := by
  classical
  intro B X I hOk l Z a v hv
  obtain ⟨-, hPr, -⟩ := base_fields_primes_ok B X
  rcases hv with hv | ⟨P, hP, rfl⟩
  · have key : ∀ (i : Fin 2), v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) ((B.primes X).vG i) ↔ ((B.primes X).g i : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal := by
      intro i
      have h0 : B.fields.conjO ((B.primes X).piG i) ≠ 0 := by
        intro h
        have h1 := hPr.piG_norm i
        rw [h, mul_zero] at h1
        exact (Nat.cast_ne_zero.2 (hPr.g_prime i).ne_zero) h1.symm
      refine mem_plUnder_iff_norm (I.rec7 l Z).sp.cm (fun P => mem_divs h0 P) ((B.primes X).g i) ?_ v
      have h2 : cO (I.rec7 l Z).host.E (B.fields.conjO ((B.primes X).piG i)) = (B.primes X).piG i := cO_cO ((B.primes X).piG i)
      rw [h2]
      have h3 : B.fields.conjO ((B.primes X).piG i) * (B.primes X).piG i = ((B.primes X).g i : 𝓞 B.fields.E) := by
        rw [mul_comm]
        exact hPr.piG_norm i
      exact h3
    have hv' : v ∈ plUnder (I.rec7 l Z).host.F (E := (I.rec7 l Z).host.E) (B.primes X).vGs := by
      rcases hv with h | h
      · obtain ⟨P, hP, hPv⟩ := (key 0).2 h
        exact ⟨P, Finset.mem_union_left _ hP, hPv⟩
      · obtain ⟨P, hP, hPv⟩ := (key 1).2 h
        exact ⟨P, Finset.mem_union_right _ hP, hPv⟩
    obtain ⟨P, hP, hPv⟩ := hv'
    refine ⟨P, Finset.mem_union_left _ hP, ?_⟩
    exact hPv
  · refine ⟨P, Finset.mem_union_right _ hP, ?_⟩
    exact rfl

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteOrder_charts_middle_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k → ∃ K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.Mem.Col2.ChExM.exists_charts | exact GlobalTheory.Mem.Col2.ChExM.exists_charts | (intros; apply GlobalTheory.Mem.Col2.ChExM.exists_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertHeckeDoubleCosetOperatorsLiftsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inertHecke_doubleCosetOperators_lifts : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k → ∀ P : LiftBrg.PresL X I hX U Xg tr L cV i t, LiftBrg.ReadsStd X I hX U Xg tr L cV i t A k P →
    Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc X.toD7 i)) P ((famR X I hX U Xg tr).heckeLI i t)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc X.toD7 i).rank k.2)
      (fun k => IsLabElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1 (labIn (Vc X.toD7 i).rank k.2))
      fun k => IsLocElt (Vc X.toD7 i) (k.1.1 : PlI X.B px).1) := by
  first | exact @GlobalTheory.Mem.R3.LiftBrg.InertTie.exists_inertTie | exact GlobalTheory.Mem.R3.LiftBrg.InertTie.exists_inertTie | (intros; apply GlobalTheory.Mem.R3.LiftBrg.InertTie.exists_inertTie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMiddleStepLevelInverseLifts
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_midAt_liftsInv : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i < B.R.m) (b : (I.stp u a i).β) (κ : (I.stp u a i).G b) (P : SBof I a), ∃ g z, MidAt I hi b P g z ∧ LiftsInv I κ P g := by
  intro B X I hOk u a i hi b κ P
  have hL := hOk.idx_ok a
  obtain ⟨al, rfl⟩ : ∃ al, b = Idx.of al hi := ⟨_, (Idx.of_get b hi _).symm⟩
  by_cases hP : P.1 ∈ (B.primes X).vGs
  · have hm : κ.2.1.1 ⟨P.1, hP⟩ ∈ ((I.idx a).levG i al ⟨P.1, hP⟩).H := κ.2.1.2 ⟨P.1, hP⟩ trivial
    obtain ⟨g, hg, hred⟩ := (hL.grpG i al ⟨P.1, hP⟩ _).1 (inv_mem hm)
    obtain ⟨z, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P _ g).2 hg
    exact ⟨g, z, hz, hL.int i al P hg, fun _ => hred, fun h => absurd hP (Q_notMem_of_ok hOk a _ h)⟩
  · have hP' : P.1 ∈ I.Q a := (@Finset.mem_union _ (Classical.decEq _) _ _ _).1 P.2 |>.resolve_left hP
    have hm : κ.2.2.1 ⟨P.1, hP'⟩ ∈ ((I.idx a).levQ i al ⟨P.1, hP'⟩).H := κ.2.2.2 ⟨P.1, hP'⟩ trivial
    have h3 := inv_mem hm
    rw [hL.grpQ, Subgroup.mem_subgroupOf] at h3
    obtain ⟨z, hz⟩ := (GlobalTheory.TwU.exists_midLev_iff (R := B.R) I.Ch I.sel (I.tup a) (I.cst a) i P _ _).2 h3
    exact ⟨_, z, hz, ((κ.2.2.1 ⟨P.1, hP'⟩)⁻¹).2, fun h => absurd h hP, fun _ => rfl⟩

end GlobalTheory.Mem.Col2.AdT
end

