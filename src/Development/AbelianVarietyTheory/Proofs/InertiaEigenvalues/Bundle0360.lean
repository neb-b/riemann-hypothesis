module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsGenIsUnitSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLattice
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaRingStructureDeltaFrobeniusComm
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem int_frob_lift (l : ℕ) [hl : Fact l.Prime] (a : ℤ) :
    ∃ b : ℤ, (RingHom.id ℤ) a = a ^ l + (l : ℤ) * b := by
  have h : ((a ^ l : ℤ) : ZMod l) = ((a : ℤ) : ZMod l) := by
    push_cast; exact ZMod.pow_card _
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by simp only [RingHom.id_apply]; linear_combination hb⟩

def intDelta (l : ℕ) [hl : Fact l.Prime] : Delta l ℤ :=
  Delta.ofLift l (RingHom.id ℤ)
    (fun x hx => (mul_eq_zero.1 hx).resolve_left (by exact_mod_cast hl.out.ne_zero))
    (int_frob_lift l)

theorem poly_δ_φ (l : ℕ) [hl : Fact l.Prime] (x : MvPolynomial ℕ ℤ) :
    (polyDelta (intDelta l)).δ ((polyDelta (intDelta l)).φ x) =
      (polyDelta (intDelta l)).φ ((polyDelta (intDelta l)).δ x) := by
  set D := polyDelta (intDelta l)
  have hl0 : (l : MvPolynomial ℕ ℤ) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  refine mul_left_cancel₀ hl0 ?_
  have h1 := D.φ_eq (D.φ x)
  have h2 := D.φ_eq x
  have h3 : D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) = (l : MvPolynomial ℕ ℤ) * D.φ (D.δ x) := by
    rw [map_mul, map_natCast]
  have h4 : D.φ (D.φ x) = D.φ (x ^ l) + D.φ ((l : MvPolynomial ℕ ℤ) * D.δ x) := by
    rw [← map_add (f := _), ← h2]
  rw [map_pow] at h4
  linear_combination -h1 + h4 + h3

theorem Delta.δ_φ_comm : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (a : A),
    D.δ (D.φ a) = D.φ (D.δ a) := by
  intro l hl A _ D a
  set D₀ := polyDelta (intDelta l)
  let g : MvPolynomial ℕ ℤ →+* A := MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i => D.δ^[i] a)
  have hg : ∀ p, p ∈ δLocus D₀ D g := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C n =>
      have : MvPolynomial.C n = ((n : ℤ) : MvPolynomial ℕ ℤ) := by simp
      rw [this]; exact intCast_mem _ n
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp (mem_δLocus.2 ?_)
      rw [polyDelta_X]
      simp only [g, MvPolynomial.eval₂Hom_X']
      rw [Function.iterate_succ_apply']
  have hgδ : ∀ p, g (D₀.δ p) = D.δ (g p) := fun p => mem_δLocus.1 (hg p)
  have hgφ : ∀ p, g (D₀.φ p) = D.φ (g p) := Delta.map_φ_of_map_δ D₀ D g hgδ
  have hX : g (MvPolynomial.X 0) = a := by simp [g]
  have := congrArg g (poly_δ_φ l (MvPolynomial.X 0))
  rw [hgδ, hgφ, hgφ, hgδ, hX] at this
  exact this

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdIffDvdCoeffBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.TopBasis.dvd_iff_dvd_c : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A]
    (s : bk.S →+* A) (ι : Type) (TB : TopBasis s bk.J ι) (a : bk.S) (x : A), s a ∣ x ↔ ∀ i, a ∣ TB.c i x := by
  intro l _ K bk A _ s ι TB a x
  haveI hH : IsHausdorff bk.J bk.S := bk.complete.toIsHausdorff
  obtain ⟨h1, -, -, h4, -⟩ := _root_.GlobalTheory.BSP.TopBasis.basic_facts bk.S A s bk.J ι TB hH
  constructor
  · rintro ⟨y, rfl⟩ i
    exact ⟨TB.c i y, TB.c_mul i a y⟩
  · intro h
    by_cases ha : a = 0
    · subst ha
      refine ⟨0, ?_⟩
      rw [mul_zero]
      exact h1 x fun i => zero_dvd_iff.1 (h i)
    · choose z hz using h
      obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul bk.J (M := bk.S) (Submodule.span bk.S {a})
      have key : ∀ (n : ℕ) (w : bk.S), a * w ∈ bk.J ^ (n + k) → w ∈ bk.J ^ n := by
        intro n w hw
        have hmem : a * w ∈ bk.J ^ (n + k) • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a} := by
          refine Submodule.mem_inf.2 ⟨?_, ?_⟩
          · rw [Ideal.smul_eq_mul, Ideal.mul_top]; exact hw
          · exact Submodule.mem_span_singleton.2 ⟨w, by rw [smul_eq_mul, mul_comm]⟩
        rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at hmem
        have h2 : bk.J ^ n • (bk.J ^ k • (⊤ : Submodule bk.S bk.S) ⊓ Submodule.span bk.S {a}) ≤
            bk.J ^ n * Ideal.span {a} :=
          Submodule.smul_mono le_rfl inf_le_right
        obtain ⟨v, hv, hva⟩ := Ideal.mem_mul_span_singleton.1 (h2 hmem)
        have hwv : w = v := mul_left_cancel₀ ha (by rw [← hva, mul_comm])
        exact hwv ▸ hv
      have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := fun n =>
        (TB.fin x (n + k)).subset fun i hi hx => hi (key n (z i) (hz i ▸ hx))
      obtain ⟨y, hy⟩ := h4 z hfin
      refine ⟨y, ?_⟩
      have h0 := h1 (x - s a * y) fun i => by
        rw [map_sub, TB.c_mul, hy, hz, sub_self]
      exact sub_eq_zero.1 h0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SstPer

variable {l : ℕ} [Fact l.Prime]


variable (l) in
def ecoefQ (k₀ k i : ℕ) : ℚ_[l] := (l : ℚ_[l]) ^ k₀ * ((i.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (k * i))⁻¹


variable (l) in
def ecoef (k₀ k i : ℕ) : ℤ_[l] :=
  ⟨if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0, by
    split_ifs with h
    · exact h
    · simp⟩

def kap (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a))
    (z : ℤ_[l]) : Matrix (Fin d) (Fin d) (Per.Acris l) :=
  ∑ i ∈ Finset.range d, (algebraMap (Ainf l) (Per.Acris l) (Per.zA l (ecoef l k₀ k i)) *
    (algebraMap (Ainf l) (Per.Acris l) (Per.zA l z) * C.t) ^ i) •
      (Mn.map (((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev).comp PowerSeries.C)) ^ i

theorem ecoefQ_norm_le {d e m : ℕ} (k : ℕ) (hm : ¬ l ∣ m) (hd : d.factorial = l ^ e * m) {i : ℕ} (hi : i < d) :
    ‖ecoefQ l (e + k * d) k i‖ ≤ 1 := by
  obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial hi.le
  obtain ⟨r, rfl⟩ : ∃ r, d = i + r := ⟨d - i, by omega⟩
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hm0 : (m : ℚ_[l]) ≠ 0 := by
    rintro h
    exact hm (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero _)
  have hf0 : (i.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero i)
  have h : (l : ℚ_[l]) ^ e * m = i.factorial * q := by
    exact_mod_cast (hd.symm.trans hq)
  have e1 : ecoefQ l (e + k * (i + r)) k i = (l : ℚ_[l]) ^ (k * r) * q * (m : ℚ_[l])⁻¹ := by
    unfold ecoefQ
    rw [show e + k * (i + r) = e + k * i + k * r by ring]
    field_simp
    rw [pow_add, pow_add]
    linear_combination ((l : ℚ_[l]) ^ (k * i) * (l : ℚ_[l]) ^ (k * r)) * h
  rw [e1, norm_mul, norm_mul, norm_inv, (Padic.norm_natCast_eq_one_iff (p := l)).2 ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hm), inv_one, mul_one]
  have h1 : ‖(l : ℚ_[l]) ^ (k * r)‖ ≤ 1 := by
    rw [norm_pow, Padic.norm_p]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
  have h2 : ‖(q : ℚ_[l])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (q : ℤ)
  calc ‖(l : ℚ_[l]) ^ (k * r)‖ * ‖(q : ℚ_[l])‖ ≤ 1 * 1 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem ecoef_val {k₀ k i : ℕ} (h : ‖ecoefQ l k₀ k i‖ ≤ 1) :
    ((ecoef l k₀ k i : ℤ_[l]) : ℚ_[l]) = ecoefQ l k₀ k i := by
  show (if ‖ecoefQ l k₀ k i‖ ≤ 1 then ecoefQ l k₀ k i else 0) = _
  rw [if_pos h]

theorem kap_zero (C : Core l) {K : FinExt l} (bk : BK K) {d : ℕ} (k₀ k : ℕ) (Mn : Matrix (Fin d) (Fin d) (Wq l bk.a)) :
    kap C bk k₀ k Mn 0 = (l : Per.Acris l) ^ k₀ • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact Subsingleton.elim _ _
  unfold kap
  rw [Finset.sum_eq_single 0]
  · have h0 : ecoef l k₀ k 0 = (l : ℤ_[l]) ^ k₀ := by
      have hn : ‖ecoefQ l k₀ k 0‖ ≤ 1 := by
        simp only [ecoefQ, Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, inv_one]
        rw [norm_pow, Padic.norm_p]
        exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt.le))
      apply Subtype.ext
      rw [ecoef_val hn]
      simp [ecoefQ]
    simp [h0]
  · intro i _ hi
    simp [zero_pow hi]
  · intro h
    exact absurd (Finset.mem_range.2 hd) h

end GlobalTheory.SstPer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinDistinguishedPowerSeriesAdicComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKReal

theorem constantCoeff_frobS_apply (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (p : (Wq l a)⟦X⟧) :
    constantCoeff (frobS l a p) = sigma l a (constantCoeff p) := by
  simp only [frobS]
  simp only [RingHom.coe_comp, Function.comp_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map]
  simp

theorem eisPoly_distinguished_complete : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → IsUnit ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) ∧ IsAdicComplete (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)}) (Wq l a)⟦X⟧ := by
  intro l _ a _ Ep ⟨hmon, hdeg, hdvd, w, hw⟩
  constructor
  · have hφ := (deltaS l a).φ_eq (Ep : (Wq l a)⟦X⟧)
    have h1 := congrArg constantCoeff hφ
    rw [show (deltaS l a).φ (Ep : (Wq l a)⟦X⟧) = frobS l a Ep from rfl, constantCoeff_frobS_apply] at h1
    simp only [Polynomial.constantCoeff_coe, map_add (f := _), map_pow, map_mul, map_natCast, hw] at h1
    set c := constantCoeff ((deltaS l a).δ (Ep : (Wq l a)⟦X⟧)) with hc
    obtain ⟨k, hk⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := (Fact.out : l.Prime).two_le; omega⟩
    have h2 : c = sigma l a (w : Wq l a) - (l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l := by
      have hl0 : (l : Wq l a) ≠ 0 := WittVector.p_nonzero l (Fq l a)
      apply mul_left_cancel₀ hl0
      have : ((l : Wq l a) * w) ^ l = (l : Wq l a) * ((l : Wq l a) ^ (k + 1) * (w : Wq l a) ^ l) := by
        have e : (l : Wq l a) ^ l = (l : Wq l a) ^ (k + 2) := by rw [← hk]
        rw [mul_pow, e]; ring
      rw [this] at h1
      linear_combination -h1
    rw [isUnit_iff_constantCoeff, ← hc, h2]
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply]
    simp only [map_sub, map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_pow k.succ_ne_zero, zero_mul, sub_zero]
    rw [WittVector.constantCoeff_apply, coeff_sigma, ← WittVector.constantCoeff_apply]
    exact pow_ne_zero _ ((w.isUnit.map (WittVector.constantCoeff (p := l) (R := Fq l a))).ne_zero)
  · set e := Ep.natDegree with he
    haveI : NeZero e := ⟨hdeg.ne'⟩
    have hP : Polynomial.C (l : Wq l a) ∣ Ep - Polynomial.X ^ e := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
      rcases lt_trichotomy i e with h | rfl | h
      · rw [if_neg h.ne, sub_zero]; exact hdvd i h
      · have h1 : Ep.coeff e = 1 := hmon.coeff_natDegree
        rw [if_pos rfl, h1, sub_self]; exact dvd_zero _
      · rw [if_neg h.ne', Polynomial.coeff_eq_zero_of_natDegree_lt h, sub_zero]; exact dvd_zero _
    obtain ⟨q, hq⟩ := hP
    have hS : (Ep : (Wq l a)⟦X⟧) = X ^ e + (l : (Wq l a)⟦X⟧) * (q : (Wq l a)⟦X⟧) := by
      have := congrArg (fun p : Polynomial (Wq l a) => (p : (Wq l a)⟦X⟧)) hq
      simp only [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul,
        map_natCast] at this
      have hc : ((l : Polynomial (Wq l a)) : (Wq l a)⟦X⟧) = l := map_natCast (Polynomial.coeToPowerSeries.ringHom (R := Wq l a)) l
      rw [hc] at this
      linear_combination this
    have hJ : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(Ep : (Wq l a)⟦X⟧)} =
        Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {eis l a e} := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem, hS,
          show (X : (Wq l a)⟦X⟧) ^ e + (l : (Wq l a)⟦X⟧) * q = eis l a e + (l : (Wq l a)⟦X⟧) * (q - 1) by
            rw [eis]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
      · refine sup_le le_sup_left ?_
        rw [Ideal.span_singleton_le_iff_mem,
          show eis l a e = (Ep : (Wq l a)⟦X⟧) + (l : (Wq l a)⟦X⟧) * (1 - q) by rw [eis, hS]; ring]
        exact add_mem (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
          (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))
    rw [hJ]
    exact complete_eis l a e

end GlobalTheory.BKReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfEPow

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evE_ne_zero : bk.ev bk.E ≠ 0 := fun h =>
  bk.E_ne_zero (bk.ev_injective (by rw [h, map_zero]))

theorem theta_eq_zero_iff (x : Ainf l) : Per.θ l x = 0 ↔ bk.ev bk.E ∣ x := by
  rw [← RingHom.mem_ker, ← bk.span_ev, Ideal.mem_span_singleton]

theorem theta_of_natPow_mul (n : ℕ) (c : Ainf l) (h : Per.θ l ((l : Ainf l) ^ n * c) = 0) :
    Per.θ l c = 0 := by
  rw [map_mul, map_pow, map_natCast] at h
  have hne : ((l : Per.OC l)) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.out.ne_zero)
  exact (mul_eq_zero.mp h).resolve_left hne

theorem dvd_of_dvd_natPow_mul (n : ℕ) (c : Ainf l) (h : bk.ev bk.E ∣ (l : Ainf l) ^ n * c) :
    bk.ev bk.E ∣ c := by
  rw [← theta_eq_zero_iff] at h ⊢
  exact theta_of_natPow_mul n c h

theorem pow_dvd_of_pow_dvd_l_mul (m : ℕ) : ∀ a : Ainf l,
    bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have h1 : bk.ev bk.E ∣ (l : Ainf l) ^ 1 * a := by
      rw [pow_one]; exact dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    obtain ⟨a', rfl⟩ := dvd_of_dvd_natPow_mul bk 1 a h1
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem pow_dvd_of_pow_dvd_lpow_mul (m k : ℕ) (a : Ainf l)
    (h : bk.ev bk.E ^ m ∣ (l : Ainf l) ^ k * a) : bk.ev bk.E ^ m ∣ a := by
  induction k generalizing a with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply pow_dvd_of_pow_dvd_l_mul bk m
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem pow_dvd_of_ev_pow_dvd (m : ℕ) : ∀ s : bk.S,
    bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s := by
  induction m with
  | zero => intro s _; simp
  | succ m ih =>
    intro s h
    have h1 : bk.ev bk.E ∣ bk.ev s := dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero m)) h
    have hE : bk.E ∣ s := by
      set r := bk.str.symm (Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s) with hr
      have hmk : Ideal.Quotient.mk (Ideal.span {(bk.Ep : bk.S)}) s = bk.str r := by
        rw [hr, RingEquiv.apply_symm_apply]
      have hθ := bk.θ_ev r s hmk
      rw [(theta_eq_zero_iff bk _).mpr h1] at hθ
      have hr0 : r = 0 := intToOC_injective K (by rw [← hθ, map_zero])
      rw [hr0, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hmk
      exact hmk
    obtain ⟨s', rfl⟩ := hE
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    rw [pow_succ', map_mul] at h
    exact (mul_dvd_mul_iff_left (evE_ne_zero bk)).mp h

theorem theta_eq_zero_of_forall (y : Per.OC l) (h : ∀ n : ℕ, ∃ z : Per.OC l, y = (l : Per.OC l) ^ n * z) :
    y = 0 := by
  apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(l : Per.OC l)})) y
  intro n
  obtain ⟨z, hz⟩ := h n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨z, hz⟩

theorem pow_dvd_of_forall_approx (m : ℕ) : ∀ a : Ainf l,
    (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) →
      bk.ev bk.E ^ m ∣ a := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a h
    have hθ : Per.θ l a = 0 := by
      apply theta_eq_zero_of_forall
      intro n
      obtain ⟨b, c, hbc⟩ := h n
      refine ⟨Per.θ l c, ?_⟩
      have hE : Per.θ l (bk.ev bk.E) = 0 := (theta_eq_zero_iff bk _).mpr dvd_rfl
      rw [hbc, map_add (f := _), map_mul, map_mul, map_pow, map_pow, hE, map_natCast]
      simp
    obtain ⟨a', rfl⟩ := (theta_eq_zero_iff bk a).mp hθ
    rw [pow_succ']
    apply mul_dvd_mul_left
    apply ih
    intro n
    obtain ⟨b, c, hbc⟩ := h n
    have hc : bk.ev bk.E ∣ (l : Ainf l) ^ n * c :=
      ⟨a' - bk.ev bk.E ^ m * b, by rw [mul_sub, ← mul_assoc, ← pow_succ', hbc]; ring⟩
    obtain ⟨c', rfl⟩ := dvd_of_dvd_natPow_mul bk n c hc
    refine ⟨b, c', ?_⟩
    apply mul_left_cancel₀ (evE_ne_zero bk)
    rw [hbc]; ring

theorem ker_localizedTheta_eq_span_eisenstein (bk : BK K) : Per.kerP l = Ideal.span {(algebraMap (Per.Ainf l) (Per.AinfP l)) (bk.ev bk.E)} :=
  GlobalTheory.MemLoc.ker_localizedTheta_eq_span_of_dvd l _ (fun a => theta_eq_zero_iff bk a)

theorem mem_filtration_iff_eisenstein_pow_dvd (m : ℕ) (a : Ainf l) :
    aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a := by
  have key : aDp l a ∈ Per.FilP l m ↔
      (algebraMap (Per.Ainf l) (Per.AinfP l)) a ∈ Per.kerP l ^ m := by
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    unfold aDp
    rw [RingHom.comp_apply, GlobalTheory.RingIface.ev_alg]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [key, ker_localizedTheta_eq_span_eisenstein bk, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← map_pow]
  constructor
  · rintro ⟨y, hy⟩
    haveI : IsLocalization (Submonoid.powers (l : Per.Ainf l)) (Per.AinfP l) :=
      inferInstance
    obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.surj (Submonoid.powers (l : Per.Ainf l)) y
    obtain ⟨k, hk⟩ := s.2
    simp only at hs hk
    rw [← hk] at hs
    have hl0 : (l : Per.Ainf l) ≠ 0 := fun h => by
      have h' := congrArg (Per.θ l) h
      rw [map_natCast, map_zero] at h'
      exact (Nat.cast_ne_zero.mpr hl.out.ne_zero) h'
    have hinj : Function.Injective (algebraMap (Per.Ainf l) (Per.AinfP l)) :=
      IsLocalization.injective (Per.AinfP l) (powers_le_nonZeroDivisors_of_noZeroDivisors hl0)
    have heq : (l : Ainf l) ^ k * a = bk.ev bk.E ^ m * b := by
      apply hinj
      rw [map_mul, map_mul, ← hs, hy]
      ring
    exact pow_dvd_of_pow_dvd_lpow_mul bk m k a ⟨b, heq⟩
  · exact fun h => map_dvd _ h

theorem ePow_facts : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), (∀ a : Ainf l, bk.ev bk.E ^ m ∣ (l : Ainf l) * a → bk.ev bk.E ^ m ∣ a) ∧ (∀ s : bk.S, bk.ev bk.E ^ m ∣ bk.ev s → bk.E ^ m ∣ s) ∧ (∀ a : Ainf l, aDp l a ∈ Per.FilP l m ↔ bk.ev bk.E ^ m ∣ a) ∧ ∀ a : Ainf l, (∀ n : ℕ, ∃ b c : Ainf l, a = bk.ev bk.E ^ m * b + (l : Ainf l) ^ n * c) → bk.ev bk.E ^ m ∣ a := by
  intro l _ K bk m
  exact ⟨pow_dvd_of_pow_dvd_l_mul bk m, pow_dvd_of_ev_pow_dvd bk m, mem_filtration_iff_eisenstein_pow_dvd bk m,
    pow_dvd_of_forall_approx bk m⟩

end GlobalTheory.AinfEPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeltaRingStructureQuotientSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.delta_quot_span : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (s : Set A), (∀ x ∈ s, D.δ x ∈ Ideal.span s) → ∃ D' : Delta l (A ⧸ Ideal.span s), IsδMap D D' (Ideal.Quotient.mk (Ideal.span s)) := by
  intro l _ A _ D s hs
  let N := Ideal.span s
  let g : A →+* W2 l (A ⧸ N) := (W2.map (Ideal.Quotient.mk N)).comp (deltaSectionToWittLengthTwo D)
  have hg : ∀ a ∈ N, g a = 0 := by
    intro a ha
    have hle : N ≤ RingHom.ker g := by
      refine Ideal.span_le.2 fun x hx => ?_
      rw [SetLike.mem_coe, RingHom.mem_ker]
      refine W2.ext ?_ ?_
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span hx)
      · exact Ideal.Quotient.eq_zero_iff_mem.2 (hs x hx)
    exact hle ha
  let sec : A ⧸ N →+* W2 l (A ⧸ N) := Ideal.Quotient.lift N g hg
  have hsec : ∀ a, (sec a).fst = a := by
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  exact ⟨deltaStructureOfWittLengthTwoSection sec hsec, fun a => rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTauComponentFrameOfLatticeStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tau_component_frame_of_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (τ : S.K →ₐ[S.Qp] S.LL), HypW S E T M0 h0 → ∀ (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)), IsMat K LL T M A → ∃ (r : ℕ) (Pm : Matrix (Fin r) (Fin d) (PadicComplex l)) (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l) (J : Finset ℤ), (∀ u, u ∈ J → IsJumpV S.PD T.ρ τ u) ∧ {u | IsJumpV S.PD T.ρ τ u}.Finite ∧ Frame (D.loc l).χQ K (mN l s (M0 + h0)) U g ∧ HTBasis (D.locA l).actC (D.loc l).χQ (Gj K (mN l s (M0 + h0))) U (J : Set ℤ) ∧ (∀ σ ∈ Gj K (mN l s (M0 + h0)), Pm * M σ = U σ * Pm.map ((D.locA l).actC σ)) ∧ ball l r ⊆ Pm.mulVec '' ball l d ∧ (∀ x ∈ ball l d, (l : PadicComplex l) • Pm.mulVec x ∈ ball l r) ∧ ∀ y : Fin d → ℚ_[l], Pm.mulVec (fun a => algebraMap ℚ_[l] (PadicComplex l) (y a)) ∈ Pm.mulVec '' ball l d → ∀ a, ‖y a‖ ≤ 1 := by
  first | exact @GlobalTheory.TauFrame.exists_tau_frame | exact GlobalTheory.TauFrame.exists_tau_frame | (intros; apply GlobalTheory.TauFrame.exists_tau_frame <;> assumption)
end

