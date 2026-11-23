module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletedLocalisationInvariants
section
open PowerSeries

namespace GlobalTheory

namespace CompletedInvariants

theorem smodEq_iff {R : Type} [CommRing R] (q : R) (n : ℕ) (a b : R) :
    a ≡ b [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule R R)] ↔ q ^ n ∣ a - b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

theorem eq_zero_of_dvd {R : Type} [CommRing R] (q : R) (h : IsAdicComplete (Ideal.span {q}) R)
    (z : R) (hz : ∀ k : ℕ, q ^ k ∣ z) : z = 0 := by
  refine IsHausdorff.haus h.toIsHausdorff z fun n => ?_
  rw [smodEq_iff, sub_zero]; exact hz n

theorem exists_lim {R : Type} [CommRing R] (q : R) (h : IsAdicComplete (Ideal.span {q}) R)
    (f : ℕ → R) (hf : ∀ m n, m ≤ n → q ^ m ∣ f m - f n) : ∃ L, ∀ n, q ^ n ∣ f n - L := by
  obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f)
    (fun {m n} hmn => (smodEq_iff q m _ _).2 (hf m n hmn))
  exact ⟨L, fun n => (smodEq_iff q n _ _).1 (hL n)⟩

theorem map_dvd' {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (p k : ℕ) {z : R} (h : (p : R) ^ k ∣ z) : (p : S) ^ k ∣ f z := by
  have := map_dvd f h
  simpa using this

end CompletedInvariants


open CompletedInvariants in
theorem completed_localisation_invariants : ∀ {O A A' E E' J : Type} [CommRing O] [CommRing A] [CommRing A'] [CommRing E] [CommRing E'] [Algebra O A] [Algebra O A'] [Algebra O E] [Algebra O E'] (p : ℕ) (x : A) (x' : A') (ι : A →ₐ[O] E) (ι' : A' →ₐ[O] E') (j : A →ₐ[O] A') (g : E →ₐ[O] E') (D : Finset J) (δA : J → (A' →ₐ[O] A')) (δE : J → (E' →ₐ[O] E')), (∀ a, g (ι a) = ι' (j a)) → (∀ d a, δE d (ι' a) = ι' (δA d a)) → IsUnit (ι x) → IsAdicComplete (Ideal.span {(p : E)}) E → IsAdicComplete (Ideal.span {(p : E')}) E' → (∀ (y : E) (k : ℕ), ∃ (a : A) (m : ℕ), (p : E) ^ k ∣ y * ι (x ^ m) - ι a) → (∀ (y : E') (k : ℕ), ∃ (a : A') (m : ℕ), (p : E') ^ k ∣ y * ι' (x' ^ m) - ι' a) → (∀ (a : A') (k : ℕ), (p : E') ^ k ∣ ι' a → (p : A') ^ k ∣ a) → (∀ (a : A) (k : ℕ), (p : A') ^ k ∣ j a → (p : A) ^ k ∣ a) → x' ∣ j x → IsUnit (D.card : O) → (∀ a', (∃ a, j a = a') ↔ ∀ d ∈ D, δA d a' = a') → (∀ a', ∀ d ∈ D, δA d (∑ d' ∈ D, δA d' a') = ∑ d' ∈ D, δA d' a') → Function.Injective g ∧ ∀ y, (∃ z, g z = y) ↔ ∀ d ∈ D, δE d y = y := by
  intro O A A' E E' J _ _ _ _ _ _ _ _ _ p x x' ι ι' j g D δA δE hg hδ hx hE hE' dE dE' sE' sj
    hxx hD hinv havg
  have hxm : ∀ m : ℕ, IsUnit (ι (x ^ m)) := fun m => by rw [map_pow]; exact hx.pow m
  have hfix : ∀ a, ∀ d ∈ D, δE d (g (ι a)) = g (ι a) := fun a d hd => by
    rw [hg, hδ, (hinv (j a)).1 ⟨a, rfl⟩ d hd]
  have sat : ∀ (z : E) (k : ℕ), (p : E') ^ k ∣ g z → (p : E) ^ k ∣ z := by
    intro z k hz
    obtain ⟨a, m, h⟩ := dE z k
    have h1 := map_dvd' g p k h
    rw [map_sub, map_mul] at h1
    have h2 : (p : E') ^ k ∣ g (ι a) := (dvd_sub_right (hz.mul_right _)).1 h1
    rw [hg] at h2
    have h3 := map_dvd' ι p k (sj a k (sE' _ k h2))
    have h4 : (p : E) ^ k ∣ z * ι (x ^ m) := by
      have := dvd_add h h3
      simpa using this
    exact (hxm m).dvd_mul_right.1 h4
  refine ⟨?_, fun y => ⟨?_, fun hy => ?_⟩⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact eq_zero_of_dvd _ hE z fun k => sat z k (hz ▸ dvd_zero _)
  · rintro ⟨z, rfl⟩ d hd
    rw [← sub_eq_zero]
    refine eq_zero_of_dvd _ hE' _ fun k => ?_
    obtain ⟨a, m, h⟩ := dE z k
    have h1 := map_dvd' g p k h
    rw [map_sub, map_mul] at h1
    have h2 := map_dvd' (δE d) p k h1
    rw [map_sub, map_mul, hfix _ d hd, hfix _ d hd] at h2
    have h3 := dvd_sub h2 h1
    have hu : IsUnit (g (ι (x ^ m))) := (hxm m).map g
    refine hu.dvd_mul_right.1 ?_
    convert h3 using 1
    ring
  · have key : ∀ k : ℕ, ∃ z, (p : E') ^ k ∣ y - g z := by
      intro k
      obtain ⟨a', m, h⟩ := dE' y k
      obtain ⟨c, hc⟩ := hxx
      have h1 : (p : E') ^ k ∣ y * g (ι (x ^ m)) - ι' (a' * c ^ m) := by
        have := h.mul_right (ι' (c ^ m))
        convert this using 1
        rw [hg, map_pow j, hc, mul_pow, map_mul, map_mul]
        ring
      set b := a' * c ^ m
      have h2 : ∀ d ∈ D, (p : E') ^ k ∣ y * g (ι (x ^ m)) - ι' (δA d b) := fun d hd => by
        have := map_dvd' (δE d) p k h1
        rwa [map_sub, map_mul, hfix _ d hd, hy d hd, hδ] at this
      have h3 := Finset.dvd_sum h2
      obtain ⟨a, ha⟩ := (hinv _).2 (havg b)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_sub_distrib, ← map_sum, ← ha, ← hg, Finset.sum_const, nsmul_eq_mul] at h3
      obtain ⟨n, hn⟩ := hD.exists_left_inv
      obtain ⟨v, hv⟩ := (hxm m).exists_right_inv
      have hn' : algebraMap O E' n * (D.card : E') = 1 := by
        have := congrArg (algebraMap O E') hn
        simpa using this
      have hv' : g (ι (x ^ m)) * g v = 1 := by rw [← map_mul, hv, map_one]
      refine ⟨algebraMap O E n * ι a * v, ?_⟩
      have := h3.mul_right (algebraMap O E' n * g v)
      convert this using 1
      rw [map_mul, map_mul, AlgHom.commutes]
      linear_combination (-y) * hv' - y * (g (ι (x ^ m)) * g v) * hn'
    choose z hz using key
    obtain ⟨L, hL⟩ := exists_lim _ hE z fun m n hmn => sat _ _ (by
      have := dvd_sub ((pow_dvd_pow _ hmn).trans (hz n)) (hz m)
      convert this using 1
      rw [map_sub]; ring)
    refine ⟨L, ?_⟩
    rw [eq_comm, ← sub_eq_zero]
    refine eq_zero_of_dvd _ hE' _ fun k => ?_
    have := dvd_add (hz k) (map_dvd' g p k (hL k))
    convert this using 1
    rw [map_sub]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceInvariantConstOnFrameTranslate
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem invariant_const_on_translate : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ), (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → Φ x = Φ ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ Φ hΦ x g z hx
  classical
  set z₁ : Matrix (Fin r) (Fin r) O := Matrix.toRows₁ z
  set z₂ : Matrix (Fin t) (Fin r) O := Matrix.toRows₂ z
  set M : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O :=
    Matrix.fromBlocks (1 + ϖ • z₁) 0 (ϖ • z₂) 1 with hMdef
  have hmem : ϖ ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hres : IsLocalRing.residue O ϖ = 0 := (IsLocalRing.residue_eq_zero_iff ϖ).2 hmem
  have hdet : IsUnit M.det := by
    rw [hMdef, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
      ← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have h1 : (IsLocalRing.residue O).mapMatrix (1 + ϖ • z₁) = 1 := by
      ext i j
      simp [Matrix.one_apply, hres]
    rw [h1, Matrix.det_one]
    exact one_ne_zero
  let h : GL (Fin r ⊕ Fin t) O := M.nonsingInvUnit hdet
  have hh : (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) = M := rfl
  set e : Matrix (Fin r ⊕ Fin t) (Fin r) O :=
    Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O) with hedef
  have key : M * e = e + ϖ • z := by
    ext (a | a) b <;>
      simp [hMdef, hedef, z₁, z₂, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
        Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.toRows₁, Matrix.toRows₂, Matrix.one_apply, add_mul, Sum.elim_inl,
        Sum.elim_inr, mul_ite, ite_mul, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have h1 : ∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) -
      (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ} := by
    intro a b
    rw [hh, hMdef, Matrix.fromBlocks_apply₁₁, Matrix.add_apply, add_sub_cancel_left,
      Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have h2 : ∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈
      Ideal.span {ϖ} := by
    intro a b
    rw [hh, hMdef, Matrix.fromBlocks_apply₂₁, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have hinv := hΦ h h1 h2 (e.map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K))
  rw [← hinv, hh, ← Matrix.mul_assoc, ← Matrix.map_mul, key, ← hx, Matrix.mul_assoc,
    Units.mul_inv, Matrix.mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjSubMulNegMulOfNormOne
section
open Polynomial

namespace GlobalTheory

theorem conj_sub_mul_neg_mul_of_norm_one {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    (starRingEnd ℂ) (x - y) * (-(x * y)) = x - y := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  have cx : (starRingEnd ℂ) x = x⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hx]; simp
  have cy : (starRingEnd ℂ) y = y⁻¹ := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hy]; simp
  rw [map_sub, cx, cy]
  field_simp
  ring

theorem resultant_phase_unit_circle :
    ∀ (a b : ℕ) (α : Fin a → ℂ) (β : Fin b → ℂ), (∀ i, ‖α i‖ = 1) → (∀ j, ‖β j‖ = 1) →
      (∀ i j, α i ≠ β j) → ∀ k : ℤ,
        let R : ℂ := ∏ i, ∏ j, (α i - β j)
        (R / (‖R‖ : ℂ)) ^ (2 * k - 1) * (‖R‖ : ℂ) =
          (starRingEnd ℂ) R * ((-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a) ^ k := by
  intro a b α β hα hβ hne k R
  set D : ℂ := (-1 : ℂ) ^ (a * b) * (∏ i, α i) ^ b * (∏ j, β j) ^ a with hD
  have hR : R ≠ 0 := by
    simp only [R]
    rw [Finset.prod_ne_zero_iff]; intro i _
    rw [Finset.prod_ne_zero_iff]; intro j _
    exact sub_ne_zero.mpr (hne i j)
  have hDprod : D = ∏ i, ∏ j, (-(α i * β j)) := by
    simp only [hD, Finset.prod_neg, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin, Finset.prod_pow, pow_mul]
    ring
  have hconj : (starRingEnd ℂ) R * D = R := by
    rw [hDprod]
    simp only [R, map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    exact conj_sub_mul_neg_mul_of_norm_one (hα i) (hβ j)
  have hcR : (starRingEnd ℂ) R ≠ 0 := by simpa using hR
  have hr : ((‖R‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hR
  have hsq : ((‖R‖ : ℝ) : ℂ) ^ 2 = R * (starRingEnd ℂ) R := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  set u : ℂ := R / ((‖R‖ : ℝ) : ℂ) with hu
  have hu0 : u ≠ 0 := div_ne_zero hR hr
  have hu2 : u ^ 2 = D := by
    rw [hu, div_pow, hsq, pow_two, mul_div_mul_left _ _ hR, eq_comm]
    exact eq_div_of_mul_eq hcR (by rw [mul_comm]; exact hconj)
  have : u ^ (2 * k - 1) = D ^ k * u⁻¹ := by
    rw [zpow_sub₀ hu0, zpow_mul, zpow_one, zpow_two, ← pow_two, hu2, div_eq_mul_inv]
  rw [this, hu]
  field_simp
  linear_combination (D ^ k) * hsq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoprimeAbsNormOfNatCastNotMem
section
namespace GlobalTheory.CoprimeAbsNorm

open NumberField IsDedekindDomain

theorem coprime_absNorm_of_natCast_notMem {E : Type} [Field E] [NumberField E]
    {P : HeightOneSpectrum (RingOfIntegers E)} {m : ℕ}
    (hm : (m : RingOfIntegers E) ∉ P.asIdeal) :
    Nat.Coprime m (Ideal.absNorm P.asIdeal) := by
  apply Nat.coprime_of_dvd
  intro p hp hpm hpN
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : Finite (RingOfIntegers E ⧸ P.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  have hcard : p ∣ Nat.card (RingOfIntegers E ⧸ P.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hpN
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hcard
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hpx : (p : RingOfIntegers E ⧸ P.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have hp0 : (p : RingOfIntegers E ⧸ P.asIdeal) = 0 :=
    (mul_eq_zero.mp hpx).resolve_right hx0
  have hpP : (p : RingOfIntegers E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact hp0
  obtain ⟨k, rfl⟩ := hpm
  apply hm
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hpP

end GlobalTheory.CoprimeAbsNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetOneAddSmulBlkMem
section
open scoped BigOperators
open Polynomial

namespace GlobalTheory.BlockDet

def blk {B : Type} {g n : ℕ} (M : Fin g → Fin g → Matrix (Fin n) (Fin n) B) :
    Matrix (Fin g × Fin n) (Fin g × Fin n) B :=
  Matrix.of fun pa qb => M pa.1 qb.1 pa.2 qb.2

def splitIdx (g n : ℕ) : Fin n ⊕ (Fin g × Fin n) ≃ Fin (g + 1) × Fin n where
  toFun := Sum.elim (fun a => (0, a)) (fun pa => (pa.1.succ, pa.2))
  invFun := fun pa => Fin.cases (motive := fun _ => Fin n ⊕ (Fin g × Fin n)) (Sum.inl pa.2)
    (fun p => Sum.inr (p, pa.2)) pa.1
  left_inv := by rintro (a | ⟨p, a⟩) <;> simp
  right_inv := by
    rintro ⟨p, a⟩
    refine Fin.cases ?_ (fun p => ?_) p <;> simp

theorem det_one_add_smul_blk_mem {B : Type} [CommRing B] {n : ℕ} (S : Subring B)
    (A : Subring (Matrix (Fin n) (Fin n) B)) (hdet : ∀ a ∈ A, a.det ∈ S) (e : B)
    (he : IsNilpotent e) (heA : ∀ a ∈ A, e • a ∈ A) (g : ℕ) :
    ∀ Θ : Fin g → Fin g → Matrix (Fin n) (Fin n) B, (∀ p q, Θ p q ∈ A) →
      (1 + e • blk Θ).det ∈ S := by
  induction g with
  | zero => intro Θ _; rw [Matrix.det_isEmpty]; exact S.one_mem
  | succ g ih =>
    intro Θ hΘ
    have hnil : IsNilpotent (⟨e • Θ 0 0, heA _ (hΘ 0 0)⟩ : A) := by
      obtain ⟨k, hk⟩ := he
      refine ⟨k, Subtype.ext ?_⟩
      simp [_root_.smul_pow, hk]
    obtain ⟨w, hw⟩ := hnil.isUnit_one_add
    set u : Matrix (Fin n) (Fin n) B := ((w⁻¹ : Aˣ) : A).1 with hu
    have huA : u ∈ A := ((w⁻¹ : Aˣ) : A).2
    have hw' : ((w : A) : Matrix (Fin n) (Fin n) B) = 1 + e • Θ 0 0 := by rw [hw]; rfl
    letI : Invertible (1 + e • Θ 0 0) :=
      ⟨u, by rw [← hw', hu, ← Subring.coe_mul]; simp, by rw [← hw', hu, ← Subring.coe_mul]; simp⟩
    have hinv : ⅟(1 + e • Θ 0 0) = u := rfl
    let Bm : Matrix (Fin n) (Fin g × Fin n) B := Matrix.of fun a qb => Θ 0 qb.1.succ a qb.2
    let Cm : Matrix (Fin g × Fin n) (Fin n) B := Matrix.of fun pa b => Θ pa.1.succ 0 pa.2 b
    have h1 : (1 + e • blk Θ).submatrix (splitIdx g n) (splitIdx g n) =
        Matrix.fromBlocks (1 + e • Θ 0 0) (e • Bm) (e • Cm)
          (1 + e • blk (fun p q => Θ p.succ q.succ)) := by
      ext (a | ⟨p, a⟩) (b | ⟨q, b⟩) <;>
        simp [splitIdx, blk, Bm, Cm, Matrix.one_apply, (Fin.succ_ne_zero _).symm]
    have h2 : (1 + e • blk (fun p q => Θ p.succ q.succ)) - (e • Cm) * u * (e • Bm) =
        1 + e • blk (fun p q => Θ p.succ q.succ - e • (Θ p.succ 0 * u * Θ 0 q.succ)) := by
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, add_sub_assoc, ← smul_sub]
      congr 2
    rw [← Matrix.det_submatrix_equiv_self (splitIdx g n), h1, Matrix.det_fromBlocks₁₁, hinv, h2]
    refine S.mul_mem (hdet _ (A.add_mem A.one_mem (heA _ (hΘ 0 0)))) (ih _ fun p q => ?_)
    exact A.sub_mem (hΘ _ _) (heA _ (A.mul_mem (A.mul_mem (hΘ _ _) huA) (hΘ _ _)))

def swapM {O X : Type} {n : ℕ} (a : X → Matrix (Fin n) (Fin n) O) :
    Matrix (Fin n) (Fin n) (X → O) :=
  Matrix.of fun i j x => a x i j

theorem det_sum_smul_mem {O X B : Type} [CommRing O] [CommRing B] (T : Subalgebra O (X → O))
    {n : ℕ} (ι : (X → O) →+* B) (S : Subring B) (hS : ∀ t ∈ T, ι t ∈ S) {m : ℕ}
    (a : Fin m → X → Matrix (Fin n) (Fin n) O)
    (h : ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
      (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T)
    (c : Fin m → B) (hc : ∀ k, c k ∈ S) :
    (∑ k, c k • (swapM (a k)).map ι).det ∈ S := by
  set D : MvPolynomial (Fin m) (X → O) := Matrix.det
    (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) • (swapM (a k)).map MvPolynomial.C)
    with hD
  have hco : ∀ d, AddMonoidAlgebra.coeff D d ∈ T := by
    intro d
    convert h d using 1
    funext x
    have : AddMonoidAlgebra.coeff D d x =
        AddMonoidAlgebra.coeff (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) D) d := by
      rw [MvPolynomial.coeff_map]; rfl
    rw [this, hD, RingHom.map_det]
    have hm : (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) (X → O)) •
        (swapM (a k)).map MvPolynomial.C).map (MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map (MvPolynomial.C (σ := Fin m)) := by
      ext i j
      simp [swapM, Matrix.sum_apply]
    exact congrArg (fun M => AddMonoidAlgebra.coeff (Matrix.det M) d) hm
  have hev : (∑ k, c k • (swapM (a k)).map ι).det = MvPolynomial.eval₂Hom ι c D := by
    rw [hD, RingHom.map_det]
    congr 1
    ext i j : 1
    simp [Matrix.sum_apply]
  rw [hev, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hco d)) (S.prod_mem fun k _ => S.pow_mem (hc k) _)

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T) → ∀ (g : ℕ) (Θ : Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ p q, Θ p q ∈ R) → (fun x => Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => Θ pa.1 qb.1 x pa.2 qb.2)) ∈ T := by
  intro O X _ T n R hR g Θ hΘ
  set N := Fintype.card (Fin g × Fin n) with hN
  let I : Ideal (X → O)[X] := Ideal.span {Polynomial.X ^ (N + 1)}
  let π : (X → O)[X] →+* (X → O)[X] ⧸ I := Ideal.Quotient.mk I
  let ι : (X → O) →+* (X → O)[X] ⧸ I := π.comp Polynomial.C
  let S : Subring ((X → O)[X] ⧸ I) := (π.comp (Polynomial.mapRingHom T.val.toRingHom)).range
  have hS : ∀ t ∈ T, ι t ∈ S := fun t ht => ⟨Polynomial.C ⟨t, ht⟩, by simp [ι]⟩
  have heS : π Polynomial.X ∈ S := ⟨Polynomial.X, by simp⟩
  have he : IsNilpotent (π Polynomial.X) :=
    ⟨N + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)⟩
  let G : Set (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    {M | ∃ a ∈ R, (swapM a).map ι = M}
  have hone : (1 : Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) ∈ G := by
    refine ⟨1, R.one_mem, ?_⟩
    have : swapM (1 : X → Matrix (Fin n) (Fin n) O) = 1 := by
      ext i j x
      simp [swapM, Matrix.one_apply, apply_ite (fun f : X → O => f x)]
    rw [this, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hmul : ∀ M ∈ G, ∀ M' ∈ G, M * M' ∈ G := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    refine ⟨a * b, R.mul_mem ha hb, ?_⟩
    rw [← Matrix.map_mul]
    congr 1
    ext i j x
    simp [swapM, Matrix.mul_apply]
  let A : Subalgebra S (Matrix (Fin n) (Fin n) ((X → O)[X] ⧸ I)) :=
    (Submodule.span S G).toSubalgebra (Submodule.subset_span hone) (by
      intro x y hx hy
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨M, hM, M', hM', rfl⟩
      exact hmul M hM M' hM')
  have hdet : ∀ a ∈ A.toSubring, a.det ∈ S := by
    intro a ha
    obtain ⟨m, c, f, rfl⟩ := Submodule.mem_span_set'.1 (show a ∈ Submodule.span S G from ha)
    choose b hb hbf using fun k => (f k).2
    have := det_sum_smul_mem T ι S hS b (hR m b hb) (fun k => c k) (fun k => (c k).2)
    simp only [hbf] at this
    exact this
  have key := det_one_add_smul_blk_mem S A.toSubring hdet (π Polynomial.X) he
    (fun a ha => A.smul_mem ha (⟨_, heS⟩ : S)) g (fun p q => (swapM (Θ p q)).map ι)
    (fun p q => Submodule.subset_span (R := S) (s := G) ⟨_, hΘ p q, rfl⟩)
  set M : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O) := blk fun p q => swapM (Θ p q) with hM
  set F : (X → O)[X] := Matrix.det ((Polynomial.X : (X → O)[X]) • M.map Polynomial.C +
    (1 : Matrix (Fin g × Fin n) (Fin g × Fin n) (X → O)).map Polynomial.C) with hF
  have hπ : (1 + π Polynomial.X • blk fun p q => (swapM (Θ p q)).map ι).det = π F := by
    rw [hF, RingHom.map_det, Matrix.map_one _ (map_zero _) (map_one _), map_add (f := _), map_one, add_comm]
    congr 2
  rw [hπ] at key
  obtain ⟨t, ht⟩ := key
  have hdvd : Polynomial.X ^ (N + 1) ∣ t.map T.val.toRingHom - F :=
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 ht)
  have hc := Polynomial.X_pow_dvd_iff.1 hdvd N (Nat.lt_succ_self N)
  rw [Polynomial.coeff_sub, Polynomial.coeff_map, hF, hN, Polynomial.coeff_det_X_add_C_card,
    sub_eq_zero] at hc
  have hmem : M.det ∈ T := by rw [← hc]; exact (t.coeff _).2
  convert hmem using 1
  funext x
  exact ((Pi.evalRingHom (fun _ : X => O) x).map_det M).symm

end GlobalTheory.BlockDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTraceGramBlockMatrix
section
open Matrix

namespace GlobalTheory

theorem det_traceGram_blockMatrix {E E' : Type} [Field E] [Field E'] [Algebra E E'] [FiniteDimensional E E'] {d n : ℕ}
    (w : Module.Basis (Fin d) E E') (H : Matrix (Fin n) (Fin n) E') (v : Fin d → E') :
    (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1)).det
      = (Matrix.of fun k l => Algebra.trace E E' (w k * v l)).det ^ n * Algebra.norm E H.det := by
  classical
  set D : Matrix (Fin d) (Fin d) E := Matrix.of fun k m => Algebra.trace E E' (w k * w m) with hD
  set C : Matrix (Fin d) (Fin d) E := w.toMatrix v with hC
  set Λ : Matrix (Fin d × Fin n) (Fin d × Fin n) E :=
    Matrix.of fun p q => Algebra.leftMulMatrix w (H p.2 q.2) p.1 q.1 with hΛ

  have htr : ∀ k (y : E'), Algebra.trace E E' (w k * y) = ∑ m, D k m * w.repr y m := by
    intro k y
    calc Algebra.trace E E' (w k * y) = Algebra.trace E E' (w k * ∑ m, w.repr y m • w m) := by
          rw [w.sum_repr y]
      _ = ∑ m, D k m * w.repr y m := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, smul_eq_mul, hD, of_apply]
          exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  have hrep : ∀ (x y : E') m, w.repr (x * y) m = ∑ s, Algebra.leftMulMatrix w x m s * w.repr y s := by
    intro x y m
    have := congrFun (Algebra.leftMulMatrix_mulVec_repr w x y) m
    rw [← this]; simp [Matrix.mulVec, dotProduct]
  have hDC : D * C = Matrix.of fun k l => Algebra.trace E E' (w k * v l) := by
    ext k l
    simp [Matrix.mul_apply, htr, hC, Module.Basis.toMatrix_apply]
  have hM : (Matrix.of fun (p q : Fin d × Fin n) => Algebra.trace E E' (w p.1 * H p.2 q.2 * v q.1))
      = blockDiagonal (fun _ : Fin n => D) * Λ * blockDiagonal (fun _ : Fin n => C) := by
    ext ⟨k, i⟩ ⟨l, j⟩
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul, mul_ite, zero_mul,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, of_apply, hΛ]
    rw [mul_assoc, htr]
    simp only [hrep, hC, Module.Basis.toMatrix_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hΛdet : Λ.det = Algebra.norm E H.det := by
    let bt := w.smulTower (Pi.basisFun E' (Fin n))
    have hmat : LinearMap.toMatrix bt bt ((Matrix.toLin' H).restrictScalars E) = Λ := by
      ext ⟨k, i⟩ ⟨l, j⟩
      simp [LinearMap.toMatrix_apply, bt, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, hΛ,
        Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct, Pi.single_apply]
      rw [mul_comm]
    rw [← hmat, LinearMap.det_toMatrix, LinearMap.det_restrictScalars, LinearMap.det_toLin']
  rw [hM, det_mul, det_mul, det_blockDiagonal, det_blockDiagonal, hΛdet, ← hDC, det_mul]
  simp [Finset.prod_const, mul_pow]
  ring

end GlobalTheory
end

