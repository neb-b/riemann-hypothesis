module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import Formalism.PolynomialDimension.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeDeterminantLineTwoHermitianLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentPowerLimitCongruentOne
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.PowIdem

theorem exists_period {M : Type*} [Monoid M] [Finite M] (y : M) :
    ∃ i p : ℕ, 0 < p ∧ i + p ≤ Nat.card M ∧ y ^ (i + p) = y ^ i := by
  classical
  haveI := Fintype.ofFinite M
  obtain ⟨a, b, hab, h⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.card M + 1) => y ^ (i : ℕ)) (by simp [Nat.card_eq_fintype_card])
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne (Fin.val_injective.ne hab) with hlt | hlt
  · refine ⟨a, b - a, by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h.symm
  · refine ⟨b, a - b, by omega, by omega, ?_⟩
    rw [Nat.add_sub_cancel' hlt.le]; exact h

theorem pow_add_mul_factorial {M : Type*} [Monoid M] [Finite M] (y : M) (n : ℕ)
    (hn : Nat.card M ≤ n) (k j : ℕ) (hk : n ≤ k) : y ^ (k + j * n.factorial) = y ^ k := by
  obtain ⟨i, p, hp, hip, h⟩ := exists_period y
  have step : ∀ t, i ≤ t → y ^ (t + p) = y ^ t := by
    intro t ht
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [show i + s + p = s + (i + p) by ring, pow_add, h, ← pow_add, add_comm s i]
  have iter : ∀ q t, i ≤ t → y ^ (t + q * p) = y ^ t := by
    intro q
    induction q with
    | zero => intro t _; simp
    | succ q ih =>
      intro t ht
      rw [show t + (q + 1) * p = (t + q * p) + p by ring, step _ (by omega), ih t ht]
  obtain ⟨c, hc⟩ := Nat.dvd_factorial hp (by omega : p ≤ n)
  rw [hc, show j * (p * c) = (j * c) * p by ring]
  exact iter _ _ (by omega)

theorem finite_quot (D : D7) (N : ℕ) (hN : 0 < N) :
    Finite (OhE D ⧸ Ideal.span {(N : OhE D)}) := by
  let ι : 𝓞 D.host.E →+* OhE D :=
    ((inc D).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict _
      fun x => GlobalTheory.CongApprox.inc_mem_OhE D x
  haveI : Finite (𝓞 D.host.E ⧸ Ideal.span {(N : 𝓞 D.host.E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN.ne')
  refine Finite.of_surjective (Ideal.quotientMap (I := Ideal.span {(N : 𝓞 D.host.E)})
    (Ideal.span {(N : OhE D)}) ι ?_) ?_
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change ι N ∈ Ideal.span {(N : OhE D)}
    rw [map_natCast]
    exact Ideal.mem_span_singleton_self _
  · intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, w, hw, h⟩ := GlobalTheory.CongApprox.exists_int_approx D N hN z z.2
    refine ⟨Ideal.Quotient.mk _ x, ?_⟩
    rw [Ideal.quotientMap_mk, eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (z : AE D) - inc D (x : D.host.E) = ((N : OhE D) : AE D) * w
    rw [h, add_sub_cancel_left]
    simp

theorem exists_of_mk_eq (D : D7) (N : ℕ) (a b : OhE D)
    (h : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) a = Ideal.Quotient.mk _ b) :
    ∃ w ∈ OhE D, (a : AE D) = b + (N : AE D) * w := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
  obtain ⟨c, hc⟩ := h
  refine ⟨c, c.2, ?_⟩
  have := congrArg Subtype.val hc
  push_cast at this
  linear_combination this

theorem mk_eq_of_exists (D : D7) (N : ℕ) (a b : OhE D) (w : AE D) (hw : w ∈ OhE D)
    (h : (a : AE D) = b + (N : AE D) * w) :
    Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) a = Ideal.Quotient.mk _ b := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
  push_cast
  linear_combination h

theorem pow_sub_one_mem (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (y : AE D) (hy : y ∈ OhE D)
    (hy1 : y - 1 ∈ hatId D 𝔪) (k : ℕ) : y ^ k - 1 ∈ hatId D 𝔪 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : y ^ (k + 1) - 1 = y * (y ^ k - 1) + (y - 1) := by ring
    rw [e]
    exact add_mem (GlobalTheory.CongApprox.mul_mem_hatId D 𝔪 y hy _ ih) hy1


set_option maxHeartbeats 1600000 in
theorem exists_idem : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ y ∈ OhE D, y - 1 ∈ hatId D 𝔪 → ∃ g ∈ OhE D, y * g * (y * g) = y * g ∧ y * g - 1 ∈ hatId D 𝔪 := by
  intro D 𝔪 h𝔪 y hy hy1
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.T.cmFiniteAdele_integral_separated_complete D
  let R : ℕ → ℕ := fun N =>
    ∑ n ∈ Finset.range (N + 1), Nat.card (OhE D ⧸ Ideal.span {(n : OhE D)})
  have hR : ∀ N : ℕ, Nat.card (OhE D ⧸ Ideal.span {(N : OhE D)}) ≤ R N := fun N =>
    Finset.single_le_sum (f := fun n : ℕ => Nat.card (OhE D ⧸ Ideal.span {((n : ℕ) : OhE D)}))
      (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ N)
  have hRmono : ∀ N M, N ≤ M → R N ≤ R M := fun N M h =>
    Finset.sum_le_sum_of_subset (by intro a ha; simp only [Finset.mem_range] at ha ⊢; omega)
  let ys : OhE D := ⟨y, hy⟩
  let e : ℕ → ℕ := fun N => 2 * (R N).factorial - 1
  have key : ∀ N : ℕ, 0 < N → ∀ k j, R N ≤ k →
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (k + j * (R N).factorial) =
        (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ k := by
    intro N hN k j hk
    haveI := finite_quot D N hN
    exact pow_add_mul_factorial _ _ (hR N) k j hk
  have he : ∀ N : ℕ, R N ≤ e N := by
    intro N
    have := Nat.self_le_factorial (R N)
    have := Nat.factorial_pos (R N)
    simp only [e]
    omega
  have he1 : ∀ N : ℕ, e N + 1 = 2 * (R N).factorial := by
    intro N
    have := Nat.factorial_pos (R N)
    simp only [e]
    omega
  have hediv : ∀ N M : ℕ, R N ≤ R M → ∃ j : ℕ, e M = e N + j * (R N).factorial := by
    intro N M hle
    obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hle
    have hF := Nat.factorial_pos (R N)
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · have := Nat.factorial_pos (R M); rw [hc, h0, mul_zero] at this; omega
      · exact h0
    obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le' hc0
    refine ⟨2 * c', ?_⟩
    simp only [e]
    rw [hc]
    have h1 : (R N).factorial * (c' + 1) = (R N).factorial * c' + (R N).factorial := by ring
    have h2 : 2 * c' * (R N).factorial = 2 * ((R N).factorial * c') := by ring
    rw [h1, h2]
    omega
  clear_value e R
  let x : ℕ → AE D := fun N => ((ys ^ e N : OhE D) : AE D)
  have hx : ∀ N : ℕ, x N ∈ OhE D := fun N => (ys ^ e N).2
  have hcong : ∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w := by
    intro N m hN hm
    apply exists_of_mk_eq
    obtain ⟨j, hj⟩ := hediv N (N * m) (hRmono _ _ (Nat.le_mul_of_pos_right N hm))
    rw [map_pow, map_pow, hj, key N hN _ _ (he N)]
  obtain ⟨g, hg, hgN⟩ := hcpl x hx hcong
  let gs : OhE D := ⟨g, hg⟩
  have hmk : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) gs =
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ e N := by
    intro N hN
    obtain ⟨w, hw, h⟩ := hgN N hN
    rw [← map_pow]
    exact mk_eq_of_exists D N gs (ys ^ e N) w hw h
  have hyg : ∀ N : ℕ, 0 < N → Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) =
      (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := by
    intro N hN
    rw [map_mul, hmk N hN, ← he1]
    exact (pow_succ' _ _).symm
  refine ⟨g, hg, ?_, ?_⟩
  · have h0 : y * g * (y * g) - y * g = 0 := by
      apply hsep
      intro N hN
      have hq : Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs)) =
          Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := by
        have hk : R N ≤ 2 * (R N).factorial := (he N).trans ((Nat.le_succ _).trans (he1 N).le)
        calc Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs * (ys * gs))
            = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) *
                Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := map_mul _ _ _
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) *
                (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) := by
              rw [hyg N hN]
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^
                (2 * (R N).factorial + 2 * (R N).factorial) := (pow_add _ _ _).symm
          _ = (Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) ys) ^ (2 * (R N).factorial) :=
              key N hN _ 2 hk
          _ = Ideal.Quotient.mk (Ideal.span {(N : OhE D)}) (ys * gs) := (hyg N hN).symm
      obtain ⟨w, hw, h⟩ := exists_of_mk_eq D N _ _ hq
      refine ⟨w, hw, ?_⟩
      have h' : y * g * (y * g) = y * g + (N : AE D) * w := h
      rw [h']; ring
    exact sub_eq_zero.1 h0
  · have hN0 : 0 < Ideal.absNorm 𝔪 := by
      rcases Nat.eq_zero_or_pos (Ideal.absNorm 𝔪) with h0 | h0
      · exact absurd (Ideal.absNorm_eq_zero_iff.1 h0) h𝔪
      · exact h0
    obtain ⟨w, hw, h⟩ := exists_of_mk_eq D (Ideal.absNorm 𝔪) (ys * gs) (ys ^ (2 * (R (Ideal.absNorm 𝔪)).factorial))
      (by rw [map_pow]; exact hyg _ hN0)
    have h' : y * g = y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w := by
      exact h
    have hmem : (Ideal.absNorm 𝔪 : AE D) * w ∈ hatId D 𝔪 := by
      refine AddSubgroup.subset_closure ⟨(Ideal.absNorm 𝔪 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔪, w, hw, ?_⟩
      congr 1
    rw [h', show y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) + (Ideal.absNorm 𝔪 : AE D) * w - 1 =
      (y ^ (2 * (R (Ideal.absNorm 𝔪)).factorial) - 1) + (Ideal.absNorm 𝔪 : AE D) * w by ring]
    exact add_mem (pow_sub_one_mem D 𝔪 y hy hy1 _) hmem

end GlobalTheory.PowIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralUnitaryGlueIdempotent
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.GlueUnitary

theorem tri_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (e1 e2 e3 : R) (h12 : e1 * e2 = 0) (h13 : e1 * e3 = 0) (h23 : e2 * e3 = 0)
    (A B C A' B' C' : Matrix n n R) :
    (e1 • A + e2 • B + e3 • C) * (e1 • A' + e2 • B' + e3 • C') =
      (e1 * e1) • (A * A') + (e2 * e2) • (B * B') + (e3 * e3) • (C * C') := by
  have h21 : e2 * e1 = 0 := by rw [mul_comm]; exact h12
  have h31 : e3 * e1 = 0 := by rw [mul_comm]; exact h13
  have h32 : e3 * e2 = 0 := by rw [mul_comm]; exact h23
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, h12, h13, h23, h21, h31, h32,
    zero_smul, add_zero, zero_add]

theorem st_mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] (s : R →+* R) (A B : Matrix n n R) :
    ((A * B).map s).transpose = (B.map s).transpose * (A.map s).transpose := by
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem st_smul {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (c : R) (A : Matrix n n R) :
    ((c • A).map s).transpose = s c • (A.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply]

theorem st_add {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (A B : Matrix n n R) :
    ((A + B).map s).transpose = (A.map s).transpose + (B.map s).transpose := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply]

theorem st_one {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] (s : R →+* R) :
    (((1 : Matrix n n R)).map s).transpose = 1 := by
  ext i j; by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem st_st {R : Type*} [CommRing R] {n : Type*} (s : R →+* R) (hs : ∀ y, s (s y) = y)
    (A : Matrix n n R) : ((((A.map s).transpose).map s).transpose) = A := by
  ext i j; simp [Matrix.map_apply, Matrix.transpose_apply, hs]

end GlobalTheory.GlueUnitary

namespace GlobalTheory.GlueUnitary

theorem key_alg {R : Type*} [CommRing R] (z p d f fb g : R) (hg : g = 1 - f - fb) (h : fb * f = 0) :
    z - (f * z + fb * p + g * d) = (z - fb * p - (1 - fb) * d) * (1 - f) := by
  subst hg; linear_combination (d - p) * h

theorem glue_unitary : ∀ (D : D7) (𝔫 : Ideal (𝓞 D.host.E)) (a : ℕ) (Z : Matrix (Fin a) (Fin a) (𝓞 D.host.E)) (f w : AE D), f ∈ OhE D → w ∈ OhE D → f * f = f → f * sgA D f = 0 → f = inc D ((Z.det : 𝓞 D.host.E) : D.host.E) * w → 1 - f ∈ hatId D 𝔫 → ∃ k ∈ intG D a, ∀ i l, (Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) - (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i l ∈ hatId D 𝔫 := by
  intro D 𝔫 a Z f w hf hw hff hffb hfdet h1f
  set s := sgA D with hs
  have hss : ∀ y, s (s y) = y := VacMove.sgA_sgA D
  set φ : 𝓞 D.host.E →+* AE D := (inc D).comp (algebraMap (𝓞 D.host.E) D.host.E) with hφ
  have hφapp : ∀ z : 𝓞 D.host.E, φ z = inc D (z : D.host.E) := fun z => rfl
  have hφint : ∀ z : 𝓞 D.host.E, φ z ∈ OhE D := fun z => VacMove.inc_int D z
  set fb := s f with hfb
  set g := 1 - f - fb with hg
  have hfbf : fb * f = 0 := by rw [mul_comm]; exact hffb
  have hfbfb : fb * fb = fb := by rw [hfb, ← map_mul, hff]
  have hfg : f * g = 0 := by rw [hg]; linear_combination -hff - hffb
  have hfbg : fb * g = 0 := by rw [hg]; linear_combination -hfbf - hfbfb
  have hgg : g * g = g := by rw [hg]; linear_combination hff + hfbfb + 2 * hffb
  have hsg : s g = g := by rw [hg, map_sub, map_sub, map_one, hss]; ring
  have hfO : fb ∈ OhE D := VacMove.sgA_mem D hf
  have hgO : g ∈ OhE D := by
    rw [hg]; exact sub_mem (sub_mem (one_mem _) hf) hfO
  let st : Matrix (Fin a) (Fin a) (AE D) → Matrix (Fin a) (Fin a) (AE D) := fun M => (M.map s).transpose
  let Zi : Matrix (Fin a) (Fin a) (AE D) := Z.map φ
  let P : Matrix (Fin a) (Fin a) (AE D) := w • Z.adjugate.map φ
  have hZP : Zi * P = f • (1 : Matrix (Fin a) (Fin a) (AE D)) := by
    simp only [Zi, P, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
    rw [hfdet]
    ext i j
    by_cases h : i = j
    · subst h; simp [Matrix.smul_apply, hφapp, mul_comm]
    · simp [Matrix.smul_apply, Matrix.one_apply, h]
  let X : Matrix (Fin a) (Fin a) (AE D) := f • Zi + fb • st P + g • 1
  let X' : Matrix (Fin a) (Fin a) (AE D) := f • P + fb • st Zi + g • 1
  have hXX' : X * X' = 1 := by
    simp only [X, X']
    rw [tri_mul f fb g hffb hfg hfbg, ← st_mul s Zi P, hZP]
    simp only [st, st_smul, st_one, hff, hfbfb, hgg, Matrix.mul_one, smul_smul]
    rw [← hfb, hfbfb, ← add_smul, ← add_smul, hg]; simp
  have hstX' : st X' = X := by
    simp only [X, X', st, st_add, st_smul, st_one, hsg]
    rw [← hfb, hss, st_st s hss]
    abel
  have hX'X : X' * X = 1 := mul_eq_one_comm.mp hXX'
  let u : GL (Fin a) (AE D) := ⟨X', X, hX'X, hXX'⟩
  have huGA : u ∈ GA D a := by
    rw [PtsMem.mem_GA]
    change st X' * X' = 1
    rw [hstX', hXX']
  let k : GA D a := ⟨u, huGA⟩
  have hkinv : (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = X := rfl
  have hentO : ∀ (M : Matrix (Fin a) (Fin a) (AE D)), (∀ i j, M i j ∈ OhE D) → ∀ i j, st M i j ∈ OhE D := by
    intro M hM i j; exact VacMove.sgA_mem D (hM j i)
  have hZiO : ∀ i j, Zi i j ∈ OhE D := fun i j => hφint _
  have hPO : ∀ i j, P i j ∈ OhE D := fun i j => mul_mem hw (hφint _)
  have h1O : ∀ i j, (1 : Matrix (Fin a) (Fin a) (AE D)) i j ∈ OhE D := by
    intro i j; by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Matrix.one_apply, h, zero_mem]
  have hXO : ∀ i j, X i j ∈ OhE D := by
    intro i j
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hZiO i j)) (mul_mem hfO (hentO P hPO i j))) (mul_mem hgO (h1O i j))
  have hX'O : ∀ i j, X' i j ∈ OhE D := by
    intro i j
    simp only [X', Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact add_mem (add_mem (mul_mem hf (hPO i j)) (mul_mem hfO (hentO Zi hZiO i j))) (mul_mem hgO (h1O i j))
  refine ⟨k, ?_, ?_⟩
  · rw [mem_intG]
    intro i j
    exact ⟨hX'O i j, hXO i j⟩
  · intro i l
    rw [hkinv]
    have hZ : Z.map (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) = Zi := rfl
    rw [hZ]
    rw [Matrix.sub_apply]
    simp only [X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [key_alg (Zi i l) (st P i l) ((1 : Matrix (Fin a) (Fin a) (AE D)) i l) f fb g hg hfbf]
    refine GlobalTheory.CongIdx.mul_mem_hatId ?_ h1f
    exact sub_mem (sub_mem (hZiO i l) (mul_mem hfO (hentO P hPO i l))) (mul_mem (sub_mem (one_mem _) hfO) (h1O i l))

end GlobalTheory.GlueUnitary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalBasisLatticeOfInverseAdelicMatrixFami
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.DefPt MvPolynomial
open scoped Matrix

namespace GlobalTheory.LocMatBasis

variable {K : Type} [Field K] [NumberField K]

theorem exists_notMem_mul_le (P u : HeightOneSpectrum (𝓞 K)) (y : K) (h : u ≠ P ∨ u.valuation K y ≤ 1) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ u.valuation K ((s : K) * y) ≤ 1 := by
  have h1 : (1 : 𝓞 K) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  by_cases hy : u.valuation K y ≤ 1
  · exact ⟨1, h1, by simpa using hy⟩
  have hne : u ≠ P := h.resolve_right hy
  have hy0 : u.valuation K y ≠ 0 := fun h0 => hy (by rw [h0]; exact zero_le_one)
  have hnle : ¬ u.asIdeal ≤ P.asIdeal := fun hle =>
    hne (HeightOneSpectrum.ext (u.isMaximal.eq_of_le P.isPrime.ne_top hle))
  obtain ⟨π, hπu, hπP⟩ := SetLike.not_le_iff_exists.1 hnle
  have hlt : u.valuation K (π : K) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem u π).2 hπu
  obtain ⟨N, hN⟩ := exists_pow_lt₀ hlt (Units.mk0 _ hy0)⁻¹
  refine ⟨π ^ N, fun hm => hπP (P.isPrime.mem_of_pow_mem N hm), ?_⟩
  have e : ((π ^ N : 𝓞 K) : K) = (π : K) ^ N := by simp
  rw [e, map_mul, map_pow]
  have hN' : u.valuation K (π : K) ^ N ≤ (u.valuation K y)⁻¹ := by simpa using hN.le
  calc _ ≤ (u.valuation K y)⁻¹ * u.valuation K y := by gcongr
    _ = 1 := inv_mul_cancel₀ hy0

theorem exists_denom_notMem {ι : Type} [Fintype ι] (B : HeightOneSpectrum (𝓞 K) → Matrix ι ι K)
    (h : {w | ¬ IntAt w (B w)}.Finite) (P : HeightOneSpectrum (𝓞 K)) (hP : IntAt P (B P)) :
    ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ ∀ w, IntAt w ((s : K) • B w) := by
  classical
  haveI : Fintype {w | ¬ IntAt w (B w)} := h.fintype
  have hex : ∀ p : {w | ¬ IntAt w (B w)} × ι × ι, ∃ s : 𝓞 K, s ∉ P.asIdeal ∧
      p.1.1.valuation K ((s : K) * B p.1.1 p.2.1 p.2.2) ≤ 1 := fun p =>
    exists_notMem_mul_le P _ _ (Or.inl fun e => p.1.2 (by rw [e]; exact hP))
  choose s hs hv using hex
  refine ⟨∏ p, s p, fun hm => ?_, fun w i j => ?_⟩
  · obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
    exact hs p hp
  by_cases hw : IntAt w (B w)
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hw i j)
  · rw [Matrix.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨w, hw⟩, i, j))]
    have e : ∀ a b : 𝓞 K, ((a * b : 𝓞 K) : K) = (a : K) * (b : K) := fun a b => by simp
    rw [e, mul_assoc, map_mul]
    exact mul_le_one' (w.valuation_le_one _) (hv (⟨w, hw⟩, i, j))

theorem intAt_mul {ι : Type} [Fintype ι] {w : HeightOneSpectrum (𝓞 K)} {M N : Matrix ι ι K}
    (hM : IntAt w M) (hN : IntAt w N) : IntAt w (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_one' (hM i k) (hN k j)

theorem finite_not_intAt {ι : Type} [Fintype ι] (M : Matrix ι ι K) :
    {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w M}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => HeightOneSpectrum.Support.finite (𝓞 K) (M p.1 p.2)).subset ?_
  intro w hw
  simp only [IntAt, Set.mem_setOf_eq, not_forall, not_le] at hw
  obtain ⟨i, j, hij⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), hij⟩

theorem exists_locBasis_inv : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (A : HeightOneSpectrum (𝓞 K) → Matrix (Fin n) (Fin n) K), IsAdelic A → ∀ P : HeightOneSpectrum (𝓞 K), ∃ s : 𝓞 K, s ∉ P.asIdeal ∧ GlobalTheory.PtDeg.LocBasis P (locLat A) (fun j => (s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
  intro K _ _ n A hA P
  classical
  obtain ⟨hdet, hfin⟩ := hA
  have hu : IsUnit (A P).det := isUnit_iff_ne_zero.2 (hdet P)
  have hone : ∀ (w : HeightOneSpectrum (𝓞 K)) (j k : Fin n), w.valuation K ((Pi.single j 1 : Fin n → K) k) ≤ 1 :=
    fun w j k => by by_cases hk : k = j <;> simp [Pi.single_apply, hk]
  obtain ⟨s, hs, hint⟩ := exists_denom_notMem (fun w => A w * (A P)⁻¹)
    ((hfin.union (finite_not_intAt (A P)⁻¹)).subset fun w hw => by
      by_contra hn
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
      exact hw (intAt_mul hn.1.1 hn.2)) P (by
      intro i j
      rw [Matrix.mul_nonsing_inv _ hu]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
  have hs0 : (s : K) ≠ 0 := fun h0 => hs (by
    have : s = 0 := by exact_mod_cast h0
    rw [this]; exact P.asIdeal.zero_mem)
  refine ⟨s, hs, fun j w i => ?_, ?_, fun x hx => ?_⟩
  · rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
    exact GlobalTheory.LocMatLat.mulVec_le w (hint w) (hone w j) i
  · have h1 : LinearIndependent K (A P)⁻¹.col :=
      Matrix.linearIndependent_cols_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 ((Matrix.isUnit_iff_isUnit_det _).2 hu))
    have h2 : LinearIndependent K (fun j => (s : K) • (A P)⁻¹.col j) :=
      h1.units_smul fun _ => Units.mk0 (s : K) hs0
    convert h2 using 3 with j
    simp
  · have hex := fun j => P.exists_primeCompl_mul_eq_of_integer _ (hx P j)
    choose c d hcd using hex
    have hd : (∏ j, (d j : 𝓞 K)) ∉ P.asIdeal := fun hm => by
      obtain ⟨p, -, hp⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact (d p).2 hp
    refine ⟨(∏ j, (d j : 𝓞 K)) * s, fun hm => (P.isPrime.mem_or_mem hm).elim hd hs, ?_⟩
    have hx' : x = ∑ j, (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) := by
      simp_rw [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, ← pi_eq_sum_univ', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu,
        Matrix.one_mulVec]
    rw [hx', Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    have e : ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * (d j : 𝓞 K) * s) •
        (A P *ᵥ x) j • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K)) =
        ((∏ k ∈ Finset.univ.erase j, (d k : 𝓞 K)) * c j) •
          ((s : K) • ((A P)⁻¹ *ᵥ (Pi.single j 1 : Fin n → K))) := by
      rw [← algebraMap_smul K, ← algebraMap_smul K (_ * c j), smul_smul, smul_smul, map_mul, map_mul, map_mul,
        ← hcd j]
      congr 1
      change _ = _ * algebraMap (𝓞 K) K s
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

end GlobalTheory.LocMatBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportedAdeleSplitPlaceMatrixCoordinateEqStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAdele_splitPlace_matrix_coordinate_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v))
    (Y : Matrix (Fin n) (Fin d) (Fv F v)), ∃ x : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) x ∧
      x.map (piW (t.comp σ)) = 0 ∧ (b⁻¹).1 * x.map (piW t) * (c⁻¹).1ᵀ = Y := by
  first | exact @GlobalTheory.VacLift.exists_lift | exact GlobalTheory.VacLift.exists_lift | (intros; apply GlobalTheory.VacLift.exists_lift <;> assumption)
end

