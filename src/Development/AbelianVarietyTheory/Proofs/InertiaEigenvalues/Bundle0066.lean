module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LangCountFrobeniusEqMulVecSolutions
section
noncomputable section

namespace GlobalTheory.PMonE

open Polynomial

theorem langCount_card_fixed (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) : Nat.card {c : F // c ^ p ^ e = c} = p ^ e := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  have hsep : (X ^ p ^ e - X : F[X]).Separable := galois_poly_separable p (p ^ e) (dvd_pow_self p he.ne')
  have hdeg : (X ^ p ^ e - X : F[X]).natDegree = p ^ e := Polynomial.natDegree_X_pow_sub_X (R := F) hq
  have hne : (X ^ p ^ e - X : F[X]) ≠ 0 := Polynomial.X_pow_sub_X_ne_zero hq
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := F) hsep (IsAlgClosed.splits_domain _)
  rw [hdeg] at hcard
  have h2 : Nat.card ((X ^ p ^ e - X : F[X]).rootSet F) = p ^ e := by
    rw [Nat.card_eq_fintype_card]
    exact hcard
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)).trans h2
  rw [Polynomial.mem_rootSet_of_ne hne]
  simp [sub_eq_zero]

theorem langCount_integral {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (q : ℕ) (hq : 1 < q) (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (x : m → F)
    (hx : ∀ i, x i ^ q = A.mulVec x i) : Integral x := by
  by_contra hcon
  simp only [Integral, not_forall, not_le] at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖x j‖) ⟨i₀, Finset.mem_univ _⟩
  have hgt : 1 < ‖x i‖ := lt_of_lt_of_le hi₀ (hi i₀ (Finset.mem_univ _))
  have hle : ‖x i‖ ^ q ≤ ‖x i‖ := by
    rw [← norm_pow, hx i]
    simp only [Matrix.mulVec, dotProduct]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro j _
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x i‖ :=
          mul_le_mul (hA i j) (hi j (Finset.mem_univ _)) (norm_nonneg _) zero_le_one
      _ = ‖x i‖ := one_mul _
  have hlt : ‖x i‖ < ‖x i‖ ^ q := lt_self_pow₀ hgt hq
  linarith

theorem langCount_card_semilinear (F : Type) [Field F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (e : ℕ) (he : 0 < e) {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (Φ : V →+ V)
    (hΦ : ∀ (a : F) (v : V), Φ (a • v) = a ^ p ^ e • Φ v) (hinj : Function.Injective Φ) :
    Nat.card {v : V // Φ v = v} = (p ^ e) ^ Module.finrank F V := by
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  obtain ⟨b, hb⟩ := LangIsogenyConstruction.lang_basis (p ^ e) hq Φ hΦ hinj
  have hkey : ∀ v, b.equivFun (Φ v) = fun i => b.equivFun v i ^ p ^ e := by
    intro v
    have hv : Φ v = b.equivFun.symm (fun i => b.equivFun v i ^ p ^ e) := by
      conv_lhs => rw [← b.sum_equivFun v]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hΦ, hb]
    rw [hv, LinearEquiv.apply_symm_apply]
  have e1 : {v : V // Φ v = v} ≃
      {c : Fin (Module.finrank F V) → F // ∀ i, c i ^ p ^ e = c i} :=
    b.equivFun.toEquiv.subtypeEquiv fun v => by
      constructor
      · intro h i
        have := congrFun (hkey v) i
        rw [h] at this
        exact this.symm
      · intro h
        apply b.equivFun.injective
        rw [hkey v]
        funext i
        exact h i
  rw [Nat.card_congr (e1.trans (Equiv.subtypePiEquivPi (p := fun _ c => c ^ p ^ e = c))), Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _),
    Fintype.card_fin, langCount_card_fixed F p e he]

theorem langCount : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e →
    ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → A.det ≠ 0 →
    (∀ x : m → F, (∀ i, x i ^ p ^ e = A.mulVec x i) → Integral x) ∧
    Nat.card {x : m → F // ∀ i, x i ^ p ^ e = A.mulVec x i} = (p ^ e) ^ Fintype.card m := by
  intro F _ _ _ p _ _ m _ _ e he A hA hdet
  have hq : 1 < p ^ e := Nat.one_lt_pow he.ne' (Fact.out : p.Prime).one_lt
  refine ⟨fun x hx => langCount_integral (p ^ e) hq A hA x hx, ?_⟩
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  let Φ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun x => A⁻¹.mulVec (fun i => x i ^ p ^ e)) (by
    intro a b
    rw [← Matrix.mulVec_add]
    congr 1
    ext i
    simpa using (add_pow_char_pow (a i) (b i) p e))
  have hΦ : ∀ (c : F) (v : m → F), Φ (c • v) = c ^ p ^ e • Φ v := by
    intro c v
    show A⁻¹.mulVec (fun i => (c • v) i ^ p ^ e) = c ^ p ^ e • A⁻¹.mulVec (fun i => v i ^ p ^ e)
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp [mul_pow]
  have hfix : ∀ x : m → F, Φ x = x ↔ ∀ i, x i ^ p ^ e = A.mulVec x i := by
    intro x
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = x ↔ _
    constructor
    · intro h i
      have h2 := congrArg A.mulVec h
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
      exact congrFun h2 i
    · intro h
      have h2 : (fun i => x i ^ p ^ e) = A.mulVec x := funext h
      rw [h2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hu, Matrix.one_mulVec]
  have hinj : Function.Injective Φ := by
    intro x y hxy
    change A⁻¹.mulVec (fun i => x i ^ p ^ e) = A⁻¹.mulVec (fun i => y i ^ p ^ e) at hxy
    have h2 := congrArg A.mulVec hxy
    simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hu, Matrix.one_mulVec] at h2
    funext i
    have h3 := congrFun h2 i
    rw [← iterateFrobenius_def, ← iterateFrobenius_def] at h3
    exact (iterateFrobenius F p e).injective h3
  have hc := langCount_card_semilinear F p e he Φ hΦ hinj
  rw [Module.finrank_fintype_fun_eq_card] at hc
  rw [← hc]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => (hfix x).symm)

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LvlPolyDistinguished
section
noncomputable section

open PowerSeries GlobalTheory.CycFr

namespace GlobalTheory.CycFr.Red

def lvlPoly (l : ℕ) (R : Type) [CommRing R] (k : ℕ) : Polynomial R :=
  ∑ i ∈ Finset.range l, ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i

variable {l : ℕ} {R S : Type} [CommRing R] [CommRing S]

theorem lvlPoly_coe (k : ℕ) : ((lvlPoly l R k : Polynomial R) : R⟦X⟧) = lvl l R k := by
  have := map_sum (Polynomial.coeToPowerSeries.ringHom (R := R))
    (fun i => ((1 + Polynomial.X : Polynomial R) ^ l ^ k) ^ i) (Finset.range l)
  rw [Polynomial.coeToPowerSeries.ringHom_apply] at this
  rw [lvlPoly, this, lvl]
  simp

theorem lvlPoly_map (j : R →+* S) (k : ℕ) : (lvlPoly l R k).map j = lvlPoly l S k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lvlPoly, Polynomial.map_sum]

theorem lvlPoly_mul (k : ℕ) :
    lvlPoly l R k * ((1 + Polynomial.X) ^ l ^ k - 1) = (1 + Polynomial.X) ^ l ^ (k + 1) - 1 := by
  rw [lvlPoly, geom_sum_mul, ← pow_mul, pow_succ]

theorem lvlPoly_monic [Nontrivial R] [hl : Fact l.Prime] (k : ℕ) : (lvlPoly l R k).Monic := by
  have h : lvlPoly l R k =
      (Polynomial.cyclotomic (l ^ (k + 1)) R).comp (Polynomial.X + Polynomial.C 1) := by
    rw [Polynomial.cyclotomic_prime_pow_eq_geom_sum hl.out, lvlPoly]
    simp [Polynomial.sum_comp, add_comm]
  rw [h]
  exact (Polynomial.cyclotomic.monic _ _).comp_X_add_C _

theorem lvlPoly_charP {F : Type} [Field F] [hl : Fact l.Prime] [CharP F l] (k : ℕ) :
    lvlPoly l F k = Polynomial.X ^ (l ^ (k + 1) - l ^ k) := by
  have h := lvlPoly_mul (l := l) (R := F) k
  rw [add_pow_char_pow, add_pow_char_pow, one_pow, one_pow, add_sub_cancel_left,
    add_sub_cancel_left] at h
  have hle : l ^ k ≤ l ^ (k + 1) := Nat.pow_le_pow_right hl.out.pos (Nat.le_succ k)
  apply mul_right_cancel₀ (pow_ne_zero (l ^ k) Polynomial.X_ne_zero)
  rw [h, ← pow_add, Nat.sub_add_cancel hle]

theorem lvlPoly_distinguished [hl : Fact l.Prime] [IsLocalRing R] (h : ¬ IsUnit (l : R)) (k : ℕ) :
    (lvlPoly l R k).IsDistinguishedAt (IsLocalRing.maximalIdeal R) := by
  refine ⟨⟨fun {n} hn => ?_⟩, lvlPoly_monic k⟩
  have h0 : (l : IsLocalRing.ResidueField R) = 0 := by
    rw [← map_natCast (IsLocalRing.residue R), IsLocalRing.residue_eq_zero_iff]; exact h
  haveI : CharP (IsLocalRing.ResidueField R) l := (CharP.charP_iff_prime_eq_zero hl.out).2 h0
  have h1 := lvlPoly_map (l := l) (IsLocalRing.residue R) k
  rw [lvlPoly_charP] at h1
  have h2 : (lvlPoly l R k).natDegree = l ^ (k + 1) - l ^ k := by
    rw [← (lvlPoly_monic (l := l) (R := R) k).natDegree_map (IsLocalRing.residue R), h1,
      Polynomial.natDegree_X_pow]
  have h3 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p n) h1
  rw [h2] at hn
  simp only [Polynomial.coeff_map, Polynomial.coeff_X_pow, hn.ne, if_false] at h3
  exact (IsLocalRing.residue_eq_zero_iff _).1 h3

theorem lvlPoly_separable {K : Type} [Field K] [CharZero K] [hl : Fact l.Prime] (k : ℕ) :
    (lvlPoly l K k).Separable := by
  have hN : 0 < l ^ (k + 1) := pow_pos hl.out.pos _
  have hs : ((1 + Polynomial.X : Polynomial K) ^ l ^ (k + 1) - 1).Separable := by
    obtain ⟨M, hM⟩ : ∃ M, l ^ (k + 1) = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hN).symm⟩
    rw [hM, Polynomial.separable_def']
    have hc : ((M : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
    refine ⟨-1, Polynomial.C ((M : K) + 1)⁻¹ * (1 + Polynomial.X), ?_⟩
    have e : Polynomial.C ((M : K) + 1)⁻¹ * Polynomial.C ((M : K) + 1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    simp only [Polynomial.derivative_sub, Polynomial.derivative_one, Polynomial.derivative_pow_succ,
      Polynomial.derivative_add, Polynomial.derivative_X, zero_add, mul_one, sub_zero]
    linear_combination ((1 + Polynomial.X : Polynomial K) ^ (M + 1)) * e
  rw [← lvlPoly_mul] at hs
  exact hs.of_mul_left

theorem lvl_dvd_of_dvd_sq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O]
    (h : ¬ IsUnit (l : O)) (k : ℕ) (a : O⟦X⟧) (ha : lvl l O k ∣ a ^ 2) : lvl l O k ∣ a := by
  rw [← lvlPoly_coe] at ha ⊢
  have H := lvlPoly_distinguished h k
  obtain ⟨r, -, hr⟩ := GlobalTheory.NB.LT.exists_poly_mod H a
  have h1 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ ((r ^ 2 : Polynomial O) : O⟦X⟧) := by
    rw [Polynomial.coe_pow,
      show (r : O⟦X⟧) ^ 2 = a ^ 2 - (a - r) * (a + r) by ring]
    exact ha.sub (hr.mul_right _)
  have h2 := GlobalTheory.NB.LT.poly_dvd_of_dvd H h1
  let K := FractionRing O
  haveI : CharZero K := algebraRat.charZero K
  have h3 := Polynomial.map_dvd (algebraMap O K) h2
  rw [Polynomial.map_pow, lvlPoly_map] at h3
  have h4 := (lvlPoly_separable (l := l) (K := K) k).squarefree.dvd_pow_iff_dvd two_ne_zero |>.1 h3
  rw [← lvlPoly_map (algebraMap O K),
    Polynomial.map_dvd_map _ (IsFractionRing.injective O K) H.monic] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : ((lvlPoly l O k : Polynomial O) : O⟦X⟧) ∣ (r : O⟦X⟧) :=
    ⟨s, by rw [hs, Polynomial.coe_mul]⟩
  simpa using hr.add h5

end GlobalTheory.CycFr.Red
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixGaussSumMulDualEqCardPowSq
section
open Matrix Finset
open scoped TensorProduct Classical

namespace GlobalTheory

theorem sum_addChar_trace_mul_eq {k : Type} [Field k] [Fintype k] [DecidableEq k] {R : Type}
    [CommRing R] [IsDomain R] (ψ : AddChar k R) (hψ : ψ.IsPrimitive) {r : ℕ}
    (m : Matrix (Fin r) (Fin r) k) :
    ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m)) =
      if m = 0 then (Fintype.card k : R) ^ (r ^ 2) else 0 := by
  split_ifs with hm
  · subst hm
    simp only [Matrix.mul_zero, trace_zero, AddChar.map_zero_eq_one, sum_const, card_univ,
      nsmul_eq_mul, mul_one]
    rw [show Fintype.card (Matrix (Fin r) (Fin r) k) = Fintype.card (Fin r → Fin r → k) from rfl]
    simp [Fintype.card_fun, ← pow_mul, sq]
  · obtain ⟨i, j, hij⟩ : ∃ i j, m i j ≠ 0 := by
      by_contra h; push_neg at h; exact hm (Matrix.ext h)
    have h1 := hψ hij
    obtain ⟨c, hc⟩ : ∃ c, ψ (m i j * c) ≠ 1 := by
      by_contra h; push_neg at h; apply h1; ext c; simp [AddChar.mulShift_apply, h]
    set a₀ : Matrix (Fin r) (Fin r) k := Matrix.single j i c
    have ha₀ : trace (a₀ * m) = m i j * c := by
      simp [a₀, Matrix.trace_single_mul, mul_comm]
    set S := ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * m))
    have hS : S = ψ (trace (a₀ * m)) * S := by
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.subRight a₀) _ _ (fun a => ?_)
      simp only [Equiv.subRight_apply, ← AddChar.map_add_eq_mul, Matrix.sub_mul, trace_sub]
      congr 1; ring
    rw [ha₀] at hS
    have : (1 - ψ (m i j * c)) * S = 0 := by rw [sub_mul, one_mul, ← hS, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hc
    · exact h

end GlobalTheory

namespace GlobalTheory

theorem matrixGaussSum_mul_dual_eq_card_pow : ∀ (k : Type) [Field k] [Fintype k] [DecidableEq k] (R : Type) [CommRing R] [IsDomain R] (ψ : AddChar k R) (ξ : kˣ →* Rˣ) (r : ℕ), ψ.IsPrimitive → ξ ≠ 1 → (∑ x : GL (Fin r) k, (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) * (∑ x : GL (Fin r) k, (((ξ⁻¹ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ⁻¹ (Matrix.trace (1 * (x : Matrix (Fin r) (Fin r) k)))) = (Fintype.card k : R) ^ (r ^ 2) := by
  intro k _ _ _ R _ _ ψ ξ r hψ hξ
  obtain ⟨hsing, hinv⟩ := GlobalTheory.matrixGaussSum_singular_and_invertible k R ψ ξ r hψ hξ
  let S : Matrix (Fin r) (Fin r) k → R := fun a => ∑ x : GL (Fin r) k,
    (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k)))

  have key1 : ∑ a, S a * ψ (-trace a) = (Fintype.card k : R) ^ (r ^ 2) := by
    simp only [S, Finset.sum_mul]
    rw [Finset.sum_comm]
    have hx : ∀ x : GL (Fin r) k, ∑ a : Matrix (Fin r) (Fin r) k,
        (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) * ψ (trace (a * (x : Matrix (Fin r) (Fin r) k))) * ψ (-trace a)
        = (((ξ (Matrix.GeneralLinearGroup.det x))⁻¹ : Rˣ) : R) *
          ∑ a : Matrix (Fin r) (Fin r) k, ψ (trace (a * ((x : Matrix (Fin r) (Fin r) k) - 1))) := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [mul_assoc, ← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.mul_one, trace_sub, sub_eq_add_neg]
    simp_rw [hx, sum_addChar_trace_mul_eq ψ hψ]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro x _ hx1
      rw [if_neg, mul_zero]
      intro h
      apply hx1
      ext1
      simpa using sub_eq_zero.mp h
    · simp

  have key2 : ∑ a, S a * ψ (-trace a) =
      ∑ g : GL (Fin r) k, S (g : Matrix (Fin r) (Fin r) k) * ψ (-trace (g : Matrix (Fin r) (Fin r) k)) := by
    symm
    refine Fintype.sum_of_injective (fun g : GL (Fin r) k => (g : Matrix (Fin r) (Fin r) k)) (fun g h e => Units.ext e) _ _ ?_ (fun g => rfl)
    intro a ha
    have hdet : a.det = 0 := by
      by_contra h
      exact ha ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero a h, rfl⟩
    simp only [S]
    rw [hsing a hdet, zero_mul]
  rw [← key1, key2]
  simp only [S]
  simp_rw [hinv]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp [MonoidHom.inv_apply, AddChar.inv_apply]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MoorePowSubSelfEqProd
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset Polynomial

theorem moore_pow_sub_self_eq_prod {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x : F) :
    x ^ p - x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F)) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := Polynomial.natDegree_X_pow_sub_X (R := (ZMod p)) hp
  have hmon : (X ^ p - X : (ZMod p)[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact_mod_cast hp
  have h := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by
    rw [hroots, hdeg]; simp)
  rw [hroots] at h
  have h2 : (X ^ p - X : (ZMod p)[X]) = ∏ c : ZMod p, (X - C c) := by
    rw [← h]; rfl
  have h3 := congrArg (Polynomial.aeval x) h2
  simp only [map_sub, map_pow, aeval_X, map_prod, aeval_C] at h3
  rw [h3]
  refine Finset.prod_congr rfl fun c _ => ?_
  congr 1
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [map_natCast]

theorem moore_step_eq_prod {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) :
    x ^ p - t ^ (p - 1) * x = ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  by_cases ht : t = 0
  · subst ht
    rw [zero_pow (by omega)]
    simp
  · have h := moore_pow_sub_self_eq_prod p (x / t)
    have h1 : ∏ c : ZMod p, (x - ((c.val : ℕ) : F) * t) = ∏ c : ZMod p, (t * (x / t - ((c.val : ℕ) : F))) := by
      refine Finset.prod_congr rfl fun c _ => ?_
      field_simp
    rw [h1, Finset.prod_mul_distrib, ← h, Finset.prod_const, Finset.card_univ, ZMod.card]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, div_pow]
    field_simp
    ring

theorem moore_step_norm_ge {F : Type*} [NormedField F] (p : ℕ) [Fact p.Prime] [CharP F p] (x t : F) (r : ℝ)
    (hr : 0 ≤ r) (h : ∀ c : ℤ, r ≤ ‖x + (c : F) * t‖) : r ^ p ≤ ‖x ^ p - t ^ (p - 1) * x‖ := by
  rw [moore_step_eq_prod, norm_prod]
  have : r ^ p = ∏ _c : ZMod p, r := by simp
  rw [this]
  refine Finset.prod_le_prod₀ (fun _ _ => hr) fun c _ => ?_
  have := h (-(c.val : ℤ))
  simpa only [Int.cast_neg, Int.cast_natCast, neg_mul, ← sub_eq_add_neg] using this

theorem moore_step_norm_le {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime] (x t : F)
    (h : ‖t‖ ≤ ‖x‖) : ‖x ^ p - t ^ (p - 1) * x‖ ≤ ‖x‖ ^ p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_pow]
  · rw [norm_neg, norm_mul, norm_pow]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    gcongr

theorem moore_step_sum {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {h : ℕ} (c : Fin h → ℤ)
    (x : Fin h → F) (t : F) :
    ∑ i, (c i : F) * (x i ^ p - t ^ (p - 1) * x i) =
      (∑ i, (c i : F) * x i) ^ p - t ^ (p - 1) * ∑ i, (c i : F) * x i := by
  rw [sum_pow_char, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (c i : F) ^ p = c i := by
    have := map_intCast (frobenius F p) (c i)
    rwa [frobenius_def] at this
  rw [mul_pow, this]
  ring

theorem moore_det_succ {F : Type*} [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] {k : ℕ} (lam : Fin (k + 1) → F) :
    (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det =
      (-1) ^ k * lam (Fin.last k) * (Matrix.of fun r j : Fin k =>
        (lam j.castSucc ^ p - lam (Fin.last k) ^ (p - 1) * lam j.castSucc) ^ p ^ (r : ℕ)).det := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set t := lam (Fin.last k) with ht
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) F :=
    Matrix.of fun r j => Fin.cases (motive := fun _ => F) (lam j)
      (fun s => (lam j ^ p - t ^ (p - 1) * lam j) ^ p ^ (s : ℕ)) r
  have hB : (Matrix.of fun r j : Fin (k + 1) => lam j ^ p ^ (r : ℕ)).det = B.det := by
    refine Matrix.det_eq_of_forall_row_eq_smul_add_pred (fun s => (t ^ (p - 1)) ^ p ^ (s : ℕ)) ?_ ?_
    · intro j; simp [B]
    · intro i j
      simp only [B, Matrix.of_apply, Fin.cases_succ, Fin.val_succ, Fin.val_castSucc]
      rw [sub_pow_char_pow, mul_pow, ← pow_mul (lam j) p, pow_succ' p]
      ring
  have h0 : t ^ p - t ^ (p - 1) * t = 0 := by
    rw [← pow_succ, Nat.sub_add_cancel hp.le, sub_self]
  rw [hB, Matrix.det_succ_column B (Fin.last k), Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · congr 1
    · simp [B, ht]
    · congr 1
      ext r j
      simp [B]
  · intro i _
    have : B i.succ (Fin.last k) = 0 := by
      simp only [B, Matrix.of_apply, Fin.cases_succ, ← ht, h0]
      exact zero_pow (pow_ne_zero _ (by omega))
    rw [this]; simp

theorem mooreNorm : MooreNorm := by
  intro F _ _ p _ _ _ h
  induction h with
  | zero => intro lam _ _; simp
  | succ k ih =>
    intro lam hanti horth
    set t := lam (Fin.last k) with ht
    have hlow : ∀ (c : Fin k → ℤ) (j : Fin k), ¬ (p : ℤ) ∣ c j →
        ‖lam j.castSucc‖ ^ p ≤ ‖∑ i, (c i : F) * (lam i.castSucc ^ p - t ^ (p - 1) * lam i.castSucc)‖ := by
      intro c j hc
      rw [moore_step_sum p c (fun i => lam i.castSucc) t]
      refine moore_step_norm_ge p _ _ _ (norm_nonneg _) fun d => ?_
      have := horth (Fin.snoc (α := fun _ => ℤ) c d) j.castSucc (by simpa using hc)
      rw [Fin.sum_univ_castSucc] at this
      simpa using this
    have hnorm : ∀ j : Fin k, ‖lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc‖ = ‖lam j.castSucc‖ ^ p := by
      intro j
      refine le_antisymm (moore_step_norm_le p _ _ (hanti (Fin.le_last _))) ?_
      have := hlow (Pi.single j 1) j (by
        simp only [Pi.single_eq_same]
        exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).not_dvd_one)
      rw [Finset.sum_eq_single j] at this
      · simpa using this
      · intro b _ hb; simp [hb]
      · simp
    have hih := ih (fun j => lam j.castSucc ^ p - t ^ (p - 1) * lam j.castSucc) (by
      intro a b hab
      simp only [hnorm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hanti (Fin.castSucc_le_castSucc_iff.mpr hab)) _) (by
      intro c j hc
      simp only [hnorm]
      exact hlow c j hc)
    rw [moore_det_succ, norm_mul, norm_mul, ← ht, hih, Fin.prod_univ_castSucc]
    simp only [hnorm, norm_pow, norm_neg, norm_one, one_pow, one_mul, Fin.val_last, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, pow_one, Fin.val_castSucc, ← ht]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, ← pow_succ']
    congr 2
    have := j.isLt
    omega

end GlobalTheory.PMonE

end
end

