module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.DualLattices.CyclicRecursionStatement
section
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

section Ainf

variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

def KerThetaStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    RingHom.ker (fontaineTheta O p) =
        span {(p : WittVector p (PreTilt O p)) - teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ∈
        nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) =
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat}

def XiNuStatement : Prop :=
  ∀ ε : PreTilt O p, v.Integers O →
    IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p →
      teichmuller p ε - 1 =
          (∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i) *
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) ∧
        fontaineTheta O p (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) =
          ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt - 1 ∧
        v (algebraMap O C (fontaineTheta O p
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1))) ^ (p - 1) =
          v (p : C) ∧
        ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
          RingHom.ker (fontaineTheta O p) =
              span {∑ i ∈ Finset.range p,
                teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i} ∧
            ∃ u : (WittVector p (PreTilt O p))ˣ,
              ∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i =
                u * ((p : WittVector p (PreTilt O p)) - teichmuller p pflat)

def RegularStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    (p : WittVector p (PreTilt O p)) ∈ nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      (∀ x : WittVector p (PreTilt O p),
          teichmuller p pflat * x ∈ span {(p : WittVector p (PreTilt O p))} →
            x ∈ span {(p : WittVector p (PreTilt O p))}) ∧
      span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} ≠ ⊤

def FlatW'Statement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat} =
        span {((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ^ 2, teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) ^ 2 = 0) ∧
      (∀ x : WittVector p (PreTilt O p) ⧸
            span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat},
          (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * x = 0 →
            ∃ y, x = (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * y) ∧
      ∀ [Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})],
        Module.Flat (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})

end Ainf

def TiltStructureStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O],
      (∃ pflat : PreTilt O p, pflat.untilt = (p : O)) ∧
      (∃ ε : PreTilt O p, IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) ∧
      KerThetaStatement p O ∧ XiNuStatement p C v O ∧ RegularStatement p O ∧
      FlatW'Statement p O

def TeichSumStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (ι : Type) (s : Finset ι),
    (∃ S : MvPolynomial ι ℤ, (p : MvPolynomial ι ℤ) * S =
      ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p) ∧
    ∀ (K : Type) [CommRing K] [CharP K p] [PerfectRing K p] (X : ι → K) (S : MvPolynomial ι ℤ),
      (p : MvPolynomial ι ℤ) * S =
          ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p →
        (∃ w : WittVector p K,
          ∑ i ∈ s, teichmuller p (X i) =
            teichmuller p (∑ i ∈ s, X i) + (p : WittVector p K) *
              teichmuller p (MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S) +
              (p : WittVector p K) ^ 2 * w) ∧
        ∀ (y : K) (t : WittVector p K), ∃ w : WittVector p K,
          (teichmuller p y + (p : WittVector p K) * t) ^ p =
            teichmuller p (y ^ p) + (p : WittVector p K) ^ 2 * w

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.Eisenstein4CoeffBound
section
namespace ReciprocityTheory.PGsh

open ModularForm EisensteinSeries ArithmeticFunction PowerSeries UpperHalfPlane
open scoped ArithmeticFunction.sigma

def e4Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else 240 * (σ 3 n : ℤ)

def e6Z : PowerSeries ℤ := PowerSeries.mk fun n => if n = 0 then 1 else -504 * (σ 5 n : ℤ)

theorem qExpansion_E₄_eq : qExpansion 1 E₄ = PowerSeries.map (Int.castRingHom ℂ) e4Z := by
  ext n
  rw [coeff_map, e4Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨2, rfl⟩, hn, show bernoulli 4 = -1 / 30 by decide +kernel]

theorem qExpansion_E₆_eq : qExpansion 1 E₆ = PowerSeries.map (Int.castRingHom ℂ) e6Z := by
  ext n
  rw [coeff_map, e6Z, coeff_mk]
  by_cases hn : n = 0
  · subst hn; norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩]
  · norm_num [E_qExpansion_coeff _ ⟨3, rfl⟩, hn, show bernoulli 6 = 1 / 42 by decide +kernel]

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.FischerAdjointStatement
section
noncomputable section

open MvPolynomial Matrix Finset

namespace ReciprocityTheory.PGsh

section Cayley

variable (n : ℕ) (R : Type*) [CommRing R]

abbrev cayDet : MvPolynomial (Fin n × Fin n) R :=
  (Matrix.mvPolynomialX (Fin n) (Fin n) R).det

def cayMono (σ : Equiv.Perm (Fin n)) : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ((List.finRange n).map fun j => ((pderiv (σ j, j) : Derivation R _ _) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R)).prod

def cayOp : Module.End R (MvPolynomial (Fin n × Fin n) R) :=
  ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ)) • cayMono n R σ

def CayleyStatement : Prop :=
  ∀ (n : ℕ) (R : Type) [CommRing R] (s : ℕ),
    cayOp n R (cayDet n R ^ s) = (∏ k ∈ range n, (s + k)) • cayDet n R ^ (s - 1)

end Cayley

section Tests

variable (R : Type*) [CommRing R]

end Tests

section HW

variable {ν : ℕ} {ι : Type*}

def rowSubst (g : Matrix (Fin ν) (Fin ν) ℂ) :
    MvPolynomial (Fin ν × ι) ℂ →ₐ[ℂ] MvPolynomial (Fin ν × ι) ℂ :=
  aeval fun p => ∑ l, C (g l p.1) * X (l, p.2)


open scoped Classical in
def fischer (P Q : MvPolynomial (Fin ν × ι) ℂ) : ℂ := by
  classical
  exact ∑ A ∈ P.support ∪ Q.support,
    AddMonoidAlgebra.coeff P A * starRingEnd ℂ (AddMonoidAlgebra.coeff Q A) * ((A.prod fun _ e => e.factorial : ℕ) : ℂ)

def IsUpperUnitri (g : Matrix (Fin ν) (Fin ν) ℂ) : Prop :=
  (∀ i, g i i = 1) ∧ ∀ i j, j < i → g i j = 0

end HW

end ReciprocityTheory.PGsh
end
end

-- bundled from ReciprocityTheory.DualLattices.FrobEqOfLe
section
noncomputable section

open Finset Filter Topology

namespace ReciprocityTheory.PGsh.Up.Det2

theorem v_det_scaled {C : Type} [Field C] (v : Valuation C NNReal) {ι : Type} [Fintype ι]
    [DecidableEq ι] (c : Matrix ι ι C) (y z : ι → C) :
    v (Matrix.of fun j k => c j k * (y j / z k)).det =
      v c.det * (∏ j, v (y j)) / ∏ k, v (z k) := by
  have hM : (Matrix.of fun j k => c j k * (y j / z k)) =
      Matrix.diagonal y * c * Matrix.diagonal fun k => (z k)⁻¹ := by
    ext j k
    simp only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, div_eq_mul_inv]
    ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, map_mul, map_mul,
    map_prod, map_prod]
  simp only [map_inv₀, Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

end ReciprocityTheory.PGsh.Up.Det2
end
end

-- bundled from ReciprocityTheory.DualLattices.IsAdicCompleteOfBasis
section
noncomputable section

open Polynomial IsLocalRing

namespace ReciprocityTheory.PGsh.Up.FrobeniusGroupField

variable {p : ℕ} [hp : Fact p.Prime]

theorem smul_top_self (k : ℕ) :
    ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p]) = (maximalIdeal ℤ_[p]) ^ k := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem mem_pow_smul_top_iff {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) (k : ℕ) (x : M) :
    x ∈ ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ↔
      ∀ i, b.repr x i ∈ (maximalIdeal ℤ_[p]) ^ k := by
  constructor
  · intro hx i
    have hle : ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] M) ≤
        Submodule.comap (b.coord i) ((maximalIdeal ℤ_[p]) ^ k) :=
      Submodule.smul_le.2 fun r hr m _ => by
        rw [Submodule.mem_comap, map_smul, smul_eq_mul]
        exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    rw [← b.sum_repr x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem isPrecomplete_of_basis {M : Type} [AddCommGroup M] [Module ℤ_[p] M] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] M) : IsPrecomplete (maximalIdeal ℤ_[p]) M := by
  rw [isPrecomplete_iff]
  intro F hF
  have hP := (inferInstance : IsPrecomplete (maximalIdeal ℤ_[p]) ℤ_[p])
  rw [isPrecomplete_iff] at hP
  have hc : ∀ i, ∃ L : ℤ_[p], ∀ k, b.repr (F k) i ≡ L
      [SMOD ((maximalIdeal ℤ_[p]) ^ k • ⊤ : Submodule ℤ_[p] ℤ_[p])] := by
    intro i
    refine hP (fun k => b.repr (F k) i) fun {m n} hmn => ?_
    have := hF hmn
    rw [SModEq.sub_mem, mem_pow_smul_top_iff b] at this
    rw [SModEq.sub_mem, smul_top_self]
    simpa using this i
  choose L hL using hc
  refine ⟨∑ i, L i • b i, fun k => ?_⟩
  rw [SModEq.sub_mem, mem_pow_smul_top_iff b]
  intro i
  have := hL i k
  rw [SModEq.sub_mem, smul_top_self] at this
  have hr : b.repr (∑ j, L j • b j) i = L i := by
    have h := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply] at h
  rw [map_sub, Finsupp.sub_apply, hr]
  exact this

theorem span_p_eq (S : Type) [CommRing S] [Algebra ℤ_[p] S] :
    (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] S) = Ideal.span {(p : S)} := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]

theorem isAdicComplete_of_basis (S : Type) [CommRing S] [Algebra ℤ_[p] S] {ι : Type} [Fintype ι]
    (b : Module.Basis ι ℤ_[p] S) : IsAdicComplete (Ideal.span {(p : S)}) S := by
  have : Module.Finite ℤ_[p] S := Module.Finite.of_basis b
  have hH : IsHausdorff (maximalIdeal ℤ_[p]) S := inferInstance
  have hP : IsPrecomplete (maximalIdeal ℤ_[p]) S := isPrecomplete_of_basis b
  rw [← span_p_eq S]
  exact { toIsHausdorff := IsHausdorff.map_algebraMap_iff.2 hH
          toIsPrecomplete := IsPrecomplete.map_algebraMap_iff.2 hP }

theorem hensel (f : ℤ_[p][X]) (hf : f.Monic) {m : ℕ} (hm0 : 0 < m) (hmp : ¬ p ∣ m) (Q0 : ℤ_[p][X])
    (h0 : ∃ K : ℤ_[p][X], AdjoinRoot.mk f (Q0 ^ m - 1) = (p : AdjoinRoot f) * AdjoinRoot.mk f K) :
    ∃ Q K : ℤ_[p][X], f ∣ Q ^ m - 1 ∧
      AdjoinRoot.mk f (Q - Q0) = (p : AdjoinRoot f) * AdjoinRoot.mk f K := by
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  have : IsAdicComplete J S := isAdicComplete_of_basis S (AdjoinRoot.powerBasis' hf).basis
  have hHen : HenselianRing S J := inferInstance
  obtain ⟨K0, hK0⟩ := h0
  set a0 : S := AdjoinRoot.mk f Q0
  have ha0 : a0 ^ m - 1 ∈ J := by
    have : a0 ^ m - 1 = AdjoinRoot.mk f (Q0 ^ m - 1) := by simp [a0]
    rw [this, hK0]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hmon : (X ^ m - C (1 : S)).Monic := monic_X_pow_sub_C _ hm0.ne'
  have hev : (X ^ m - C (1 : S)).eval a0 ∈ J := by simpa using ha0
  have hu0 : IsUnit (Ideal.Quotient.mk J a0) := by
    have h1 : (Ideal.Quotient.mk J a0) ^ m = 1 := by
      rw [← map_pow, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk J), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.2 ha0
    exact IsUnit.of_pow_eq_one h1 hm0.ne'
  have hum : IsUnit (m : S ⧸ J) := by
    have hcop : Nat.Coprime m p :=
      Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hmp)
    have hg := Nat.gcd_eq_gcd_ab m p
    rw [hcop, Nat.cast_one] at hg
    have hp0 : (p : S ⧸ J) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk J)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    refine IsUnit.of_mul_eq_one ((Nat.gcdA m p : ℤ) : S ⧸ J) ?_
    have := congrArg (fun z : ℤ => (z : S ⧸ J)) hg
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast, hp0, zero_mul,
      add_zero] at this
    exact this.symm
  have hder : IsUnit (Ideal.Quotient.mk J ((X ^ m - C (1 : S)).derivative.eval a0)) := by
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, eval_mul, eval_natCast,
      eval_pow, eval_X, map_mul, map_pow, map_natCast]
    exact hum.mul (hu0.pow _)
  obtain ⟨a, ha, haJ⟩ := hHen.is_henselian _ hmon a0 hev hder
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective a
  refine ⟨Q, ?_⟩
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 haJ
  obtain ⟨K, rfl⟩ := AdjoinRoot.mk_surjective s
  refine ⟨K, ?_, ?_⟩
  · rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, map_one]
    simpa [IsRoot, sub_eq_zero] using ha
  · rw [map_sub, ← hs, mul_comm]

theorem finite_quot (f : ℤ_[p][X]) (hf : f.Monic) :
    Finite (AdjoinRoot f ⧸ Ideal.span {(p : AdjoinRoot f)}) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  let S := AdjoinRoot f
  let J : Ideal S := Ideal.span {(p : S)}
  let b := (AdjoinRoot.powerBasis' hf).basis
  let Φ : (Fin (AdjoinRoot.powerBasis' hf).dim → ZMod p) → S ⧸ J := fun c =>
    Ideal.Quotient.mk J (∑ i, (((c i).val : ℕ) : ℤ_[p]) • b i)
  refine Finite.of_surjective Φ fun y => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨fun i => PadicInt.toZMod (b.repr s i), ?_⟩
  simp only [Φ]
  rw [Ideal.Quotient.eq]
  have key : (∑ i, (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) • b i) - s =
      ∑ i, ((((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib, b.sum_repr]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  have hz := PadicInt.toZMod_spec (b.repr s i)
  rw [ZMod.cast_eq_val, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hz
  obtain ⟨w, hw⟩ := hz
  have : (((PadicInt.toZMod (b.repr s i)).val : ℕ) : ℤ_[p]) - b.repr s i = -(w * p) := by
    rw [hw]; ring
  rw [this, neg_smul, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  exact J.neg_mem (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))

theorem exists_pow_idem {S : Type} [Monoid S] [Finite S] (x : S) :
    ∃ M : ℕ, 0 < M ∧ x ^ (2 * M) = x ^ M := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  wlog h : a < b generalizing a b
  · exact this b a hab.symm he.symm (lt_of_le_of_ne (not_lt.1 h) hab.symm)
  set d := b - a with hd
  have hd0 : 0 < d := by omega
  have hstep : ∀ n, a ≤ n → x ^ (n + d) = x ^ n := by
    intro n hn
    have : n + d = (n - a) + b := by omega
    rw [this, pow_add, ← he, ← pow_add]; congr 1; omega
  have hk : ∀ k n, a ≤ n → x ^ (n + k * d) = x ^ n := by
    intro k
    induction k with
    | zero => intro n _; simp
    | succ k ih =>
      intro n hn
      rw [show n + (k + 1) * d = (n + k * d) + d by ring, hstep _ (by omega), ih n hn]
  refine ⟨d * (a + 1), Nat.mul_pos hd0 (Nat.succ_pos a), ?_⟩
  rw [show 2 * (d * (a + 1)) = d * (a + 1) + (a + 1) * d by ring]
  exact hk _ _ (by nlinarith)

end ReciprocityTheory.PGsh.Up.FrobeniusGroupField
end
end

-- bundled from ReciprocityTheory.DualLattices.NearIdentityColengthStatement
section
namespace ReciprocityTheory.PGsh

open Matrix

def CharTableStatement : Prop :=
  ∀ (K : Type) [Field K] (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (e : G ≃ AddChar G K),
    (Matrix.of fun g h : G => e h g).det ^ 2 = (Fintype.card G : K) ^ Fintype.card G ∨
    (Matrix.of fun g h : G => e h g).det ^ 2 = -(Fintype.card G : K) ^ Fintype.card G

def GaussCongruenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (O : Type) [CommRing O] [IsDomain O] (m : Ideal O) [m.IsPrime]
    (ι : F →+* O ⧸ m) (ω : MulChar F O) (ζ : O),
    Fintype.card F ≠ 2 → ζ ^ p = 1 → (∀ a, Ideal.Quotient.mk m (ω a) = ι a) →
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    ∃ y ∈ m, (∑ a : F, ω⁻¹ a * ζ ^ (Algebra.trace (ZMod p) F a).val) = (ζ - 1) * (y - 1)

end ReciprocityTheory.PGsh
end

-- bundled from ReciprocityTheory.DualLattices.SmallLevelClassSet
section
noncomputable section

open Polynomial Matrix
open scoped TensorProduct

namespace ReciprocityTheory.PGsh

def stdJ (D : Type*) [CommRing D] (g : ℕ) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D :=
  Matrix.fromBlocks 0 (-1) 1 0

def ExistsPointLeviLogNormSqPos : Prop :=
  ∀ (D : Type) [CommRing D] [IsDomain D] (g : ℕ)
    (E Φ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (c : D),
    Eᵀ = -E → (∀ i, E i i = 0) → IsUnit E.det → c ≠ 0 →
    Φᵀ * stdJ D g * Φ = c • E →
    let Ht : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inl id
    let Bt : Matrix (Fin g) (Fin g ⊕ Fin g) D := Φ.submatrix Sum.inr id
    let hb : Matrix (Fin g ⊕ Fin g) (Fin g) D := (Eᵀ)⁻¹ * Htᵀ
    let ι := algebraMap D (FractionRing D)
    (∀ f : Fin g → D, ∃ t : Fin g ⊕ Fin g → D, Ht *ᵥ t = c • f) ∧
    Ht * hb = 0 ∧ Bt * hb = c • (1 : Matrix (Fin g) (Fin g) D) ∧ hbᵀ * E * hb = 0 ∧
    (∀ t : Fin g ⊕ Fin g → FractionRing D, Ht.map ι *ᵥ t = 0 →
      ∃ x : Fin g → FractionRing D, hb.map ι *ᵥ x = t) ∧
    (∀ x : Fin g → FractionRing D, (∃ w : Fin g ⊕ Fin g → D, hb.map ι *ᵥ x = ι ∘ w) →
      ∃ y : Fin g → D, c • x = ι ∘ y)

abbrev extModR (R K V : Type*) [CommRing R] [Field K] [Algebra R K] [AddCommGroup V]
    [Module K V] : Module R (ExteriorAlgebra K V) :=
  Module.compHom _ (algebraMap R K)

attribute [local instance] extModR

def TruncatedPolynomialStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H]
    [FiniteDimensional k H] (d : ℕ) (x : Fin d → H),
    (∀ f ∈ RingHom.ker (Bialgebra.counitAlgHom k H), f ^ p = 0) →
    (∀ i, x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H)) →
    (∀ y ∈ RingHom.ker (Bialgebra.counitAlgHom k H), ∃ l : Fin d → k,
      y - ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2) →
    (∀ l : Fin d → k, ∑ i, l i • x i ∈ RingHom.ker (Bialgebra.counitAlgHom k H) ^ 2 → l = 0) →
    Function.Surjective (MvPolynomial.aeval (R := k) x) ∧
      RingHom.ker (MvPolynomial.aeval (R := k) x) =
        Ideal.span (Set.range fun i => (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ p)

end ReciprocityTheory.PGsh
end
end

