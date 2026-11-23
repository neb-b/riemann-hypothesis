module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterp
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

theorem interp_of : SpanProd → Expand → Extract → DenseCoset → Interp := by
  intro hS hE hX hC O K ι _ _ _ _ τ hτ n P hP
  classical
  obtain ⟨k₀, hk₀⟩ := hS K ι n P hP
  refine ⟨k₀, fun k hk N hN a Q hQ => ?_⟩
  obtain ⟨w, hw⟩ := hk₀ k hk
  let A := {α : Fin k → O // (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0}
  let x : A → ι × Fin k → K := fun α => pt τ α.1
  have hdense : ZDense (Set.range x) := by
    have hset : Set.range x =
        {z | ∃ α, (∀ s, N ∣ α s - a s) ∧ eval (pt τ α) Q ≠ 0 ∧ z = pt τ α} := by
      ext z
      constructor
      · rintro ⟨α, rfl⟩
        exact ⟨α.1, α.2.1, α.2.2, rfl⟩
      · rintro ⟨α, h1, h2, rfl⟩
        exact ⟨⟨α, h1, h2⟩, rfl⟩
    rw [hset]
    exact hC O K ι τ hτ N hN k a Q hQ
  have he : Function.Injective
      (fun (m : ι × Fin k → Fin (n + 1)) (p : ι × Fin k) => (m p : ℕ)) := by
    intro m₁ m₂ h
    funext p
    exact Fin.ext (congrFun h p)
  obtain ⟨c, hc⟩ := hX K (ι × Fin k) A (ι × Fin k → Fin (n + 1)) x hdense _ he w
  refine ⟨c.mapDomain Subtype.val, ?_, ?_⟩
  · intro α hα
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hα)
    exact β.2
  · intro R _ _ g
    let F : (Fin k → O) → R := fun α => ∏ t, ∏ s, detOne (algebraMap K R (τ t (α s))) (g t)
    have hmd : ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) =
        c.sum fun β (r : K) => r • F β.1 := by
      apply Finsupp.sum_mapDomain_index
      · intro _
        exact zero_smul K _
      · intro _ r₁ r₂
        exact add_smul r₁ r₂ _
    change ((c.mapDomain Subtype.val).sum fun α (r : K) => r • F α) = _
    rw [hmd]
    have hexp : ∀ β : A, F β.1 =
        ∑ m : ι × Fin k → Fin (n + 1), algebraMap K R (∏ p, x β p ^ (m p : ℕ)) *
          ∏ p : ι × Fin k, (-1) ^ (m p : ℕ) * aeval (g p.1) (esymm (Fin n) K (m p : ℕ)) := by
      intro β
      have h := hE K R (ι × Fin k) n (fun p => algebraMap K R (pt τ β.1 p)) (fun p => g p.1)
      rw [Fintype.prod_prod_type] at h
      simp only [pt] at h
      simp only [F]
      rw [h]
      apply Finset.sum_congr rfl
      intro m _
      simp only [x, pt, map_prod, map_pow]
    simp only [Finsupp.sum, hexp]
    rw [hw R g]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    rw [← hc m, Finsupp.sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro β _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    ring

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PInterpNF
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private lemma resO_injective {E K : Type} [Field E] [NumberField E] [Field K] :
    Function.Injective (resO : (E →+* K) → (NumberField.RingOfIntegers E →+* K)) := by
  intro τ τ' h
  exact IsLocalization.ringHom_ext (nonZeroDivisors (NumberField.RingOfIntegers E)) h

private lemma resO_ne_zero {E K : Type} [Field E] [NumberField E] [Field K] (τ : E →+* K)
    {N : NumberField.RingOfIntegers E} (hN : N ≠ 0) : resO τ N ≠ 0 := by
  intro h
  apply hN
  have h1 : τ (algebraMap (NumberField.RingOfIntegers E) E N) = 0 := h
  have h2 : algebraMap (NumberField.RingOfIntegers E) E N = 0 := by
    simpa using h1
  exact NumberField.RingOfIntegers.coe_injective (by simpa using h2)

private lemma one_sub_ne_zero {K σ : Type} [Field K] (p : σ) (b : K) :
    (1 - X p * C b : MvPolynomial σ K) ≠ 0 := by
  intro h
  have := congrArg (eval (fun _ : σ => (0 : K))) h
  simp at this

theorem interpNF_of : Interp → InterpNF := by
  intro hI E K _ _ _ _ n lam
  classical
  by_cases hE : IsEmpty (E →+* K)
  · refine ⟨0, fun k _ N hN B => ?_⟩
    refine ⟨Finsupp.single (fun _ => N) 1, ?_, ?_⟩
    · intro α hα s
      have hα' : α = fun _ => N := by
        simpa using Finsupp.support_single_subset hα
      subst hα'
      exact ⟨hN, dvd_rfl, fun τ => hE.elim τ⟩
    · intro R _ _ _ g
      rw [Finsupp.sum_single_index (by simp)]
      simp [Finset.univ_eq_empty]
  · rw [not_isEmpty_iff] at hE
    obtain ⟨τ₀⟩ := hE
    obtain ⟨k₀, hk⟩ := hI (NumberField.RingOfIntegers E) K (E →+* K) resO resO_injective n
      (fun τ => MvPolynomial.map (algebraMap ℚ K)
        (GroundTheory.Heights₂.Heights.RestTerms.schur (Fin n) (lam τ)))
      (fun τ => (GroundTheory.Heights₂.Heights.RestTerms.Schur.schur_isSymmetric _).map _)
    refine ⟨k₀, fun k hkk N hN B => ?_⟩
    let Q : MvPolynomial ((E →+* K) × Fin k) K :=
      ∏ p, (X p * ∏ b ∈ B, (1 - X p * C b))
    have hQ : Q ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun p _ => mul_ne_zero (X_ne_zero p) ?_
      exact Finset.prod_ne_zero_iff.mpr fun b _ => one_sub_ne_zero p b
    obtain ⟨c, hc, hsum⟩ := hk k hkk N (fun t => resO_ne_zero t hN) (fun _ => 0) Q hQ
    refine ⟨c, ?_, ?_⟩
    · intro α hα s
      obtain ⟨hdvd, hev⟩ := hc α hα
      have hfac : ∀ p : (E →+* K) × Fin k, pt resO α p ≠ 0 ∧
          ∀ b ∈ B, 1 - pt resO α p * b ≠ 0 := by
        intro p
        have h0 : eval (pt resO α) (X p * ∏ b ∈ B, (1 - X p * C b)) ≠ 0 := by
          intro h
          apply hev
          exact (map_prod (eval (pt resO α)) _ _).trans
            (Finset.prod_eq_zero (Finset.mem_univ p) h)
        simp only [map_mul, eval_X, map_prod, map_sub, map_one, eval_C] at h0
        refine ⟨left_ne_zero_of_mul h0, fun b hb => ?_⟩
        exact (Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h0)) b hb
      refine ⟨?_, by simpa using hdvd s, fun τ b hb => (hfac (τ, s)).2 b hb⟩
      intro h0
      apply (hfac (τ₀, s)).1
      simp [pt, h0]
    · intro R _ _ _ g
      have hR := hsum R g
      letI : IsScalarTower ℚ K R := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
      rw [hR]
      refine Finset.prod_congr rfl fun τ _ => ?_
      exact MvPolynomial.aeval_map_algebraMap _ _ _

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffPow
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrPow_of :
    SchurYOffClr → VdmSplit → PairCount → OffClrPow := by
  intro hS hV hP R _ _ n lam g y
  have key : ∀ i : Fin n, vdm (scaleOff y i g) = y ^ (n - 1).choose 2 *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) := by
    intro i
    have h1 : vdmAway i (scaleOff y i g) = y ^ (n - 1).choose 2 * vdmAway i g := by
      rw [← (hP n i).2, ← Finset.prod_pow_eq_pow_sum]
      unfold vdmAway
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun a ha => ?_
      have ha' : a ≠ i := (Finset.mem_erase.mp ha).1
      calc ∏ b ∈ (Finset.Ioi a).erase i, (scaleOff y i g a - scaleOff y i g b)
          = ∏ b ∈ (Finset.Ioi a).erase i, (y * (g a - g b)) := by
            refine Finset.prod_congr rfl fun b hb => ?_
            have hb' : b ≠ i := (Finset.mem_erase.mp hb).1
            simp [scaleOff, ha', hb', mul_sub]
        _ = y ^ ((Finset.Ioi a).erase i).card * ∏ b ∈ (Finset.Ioi a).erase i, (g a - g b) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
    have h2 : ∏ k ∈ univ.erase i, (scaleOff y i g i - scaleOff y i g k) =
        ∏ k ∈ univ.erase i, (g i - y * g k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hk' : k ≠ i := (Finset.mem_erase.mp hk).1
      simp [scaleOff, hk']
    rw [hV R n (scaleOff y i g) i, h1, h2]
    ring
  have hL : y ^ (n - 1).choose 2 * ∑ i, sch lam (scaleOff y i g) *
      ((-1) ^ (i : ℕ) * vdmAway i g * ∏ k ∈ univ.erase i, (g i - y * g k)) =
      ∑ i, sch lam (scaleOff y i g) * vdm (scaleOff y i g) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i]
    ring
  have hR : ∀ i : Fin n, y ^ (∑ k ∈ univ.erase i, (lam k + (n - 1 - (k : ℕ)))) =
      y ^ (n - 1).choose 2 * y ^ (∑ k ∈ univ.erase i, lam k + (i : ℕ)) := by
    intro i
    rw [Finset.sum_add_distrib, (hP n i).1, ← pow_add]
    congr 1
    omega
  rw [hL, hS R n lam g y, Finset.sum_congr rfl fun i _ => hR i, ← Finset.mul_sum]
  ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.POffRed
section
open Finset MvPolynomial UpperTheory.Gal.Schur

namespace UpperTheory.Gal.Schur

end UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.offClrRed_of :
    OffClrPow → OffClrRed := by
  intro h R _ _ n lam g y
  have key := h (Polynomial R) n lam (fun k => Polynomial.C (g k)) Polynomial.X
  have key' := (Polynomial.isRegular_X_pow ((n - 1).choose 2)).left key
  let φ : Polynomial R →ₐ[ℚ] R := (Polynomial.evalRingHom y).toRatAlgHom
  have hφ : ∀ (f : Fin n → Polynomial R) (p : MvPolynomial (Fin n) ℚ),
      φ (MvPolynomial.aeval f p) = MvPolynomial.aeval (fun k => φ (f k)) p := by
    intro f p
    rw [← MvPolynomial.comp_aeval]
    rfl
  have hC : ∀ r : R, φ (Polynomial.C r) = r := fun r => by simp [φ]
  have hX : φ Polynomial.X = y := by simp [φ]
  have hs : ∀ i, (fun k => φ (scaleOff Polynomial.X i (fun k => Polynomial.C (g k)) k)) = scaleOff y i g := by
    intro i
    funext k
    simp only [scaleOff]
    split_ifs
    · simp [hC]
    · rw [map_mul, hC, hX]
  have := congrArg φ key'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, map_prod, map_pow, map_sub, map_neg, map_one, sch, hφ, vdmAway, vdm,
    hs, hC, hX] at this
  simpa [sch, vdmAway, vdm] using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PPairSplit
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.pairSplit :
    PairSplit := by
  intro R _ n F i
  have hA : ∀ a : Fin n, ∏ b ∈ Ioi a, F a b =
      (∏ b ∈ (Ioi a).erase i, F a b) * (if a < i then F a i else 1) := by
    intro a
    split_ifs with h
    · exact (Finset.prod_erase_mul _ _ (by simpa using h)).symm
    · rw [Finset.erase_eq_self.mpr (by simpa using h), mul_one]
  have hL : ∏ a, ∏ b > a, F a b = ∏ a, ∏ b ∈ Ioi a, F a b := by
    refine Finset.prod_congr rfl fun a _ => ?_
    rfl
  have h1 : (univ : Finset (Fin n)).filter (fun a => a < i) = (univ.erase i).filter (fun k => k < i) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, true_and, and_true]
    constructor
    · intro h; exact ⟨ne_of_lt h, h⟩
    · intro h; exact h.2
  have h2 : (univ.erase i).filter (fun k => ¬ k < i) = Ioi i := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_erase, Finset.mem_Ioi, and_true, not_lt]
    constructor
    · intro h; exact lt_of_le_of_ne h.2 (Ne.symm h.1)
    · intro h; exact ⟨ne_of_gt h, le_of_lt h⟩
  rw [hL, Finset.prod_congr rfl fun a _ => hA a, Finset.prod_mul_distrib,
    ← Finset.mul_prod_erase univ _ (Finset.mem_univ i),
    Finset.erase_eq_self.mpr (by simp), ← Finset.prod_filter, Finset.prod_ite, h1, h2]
  simp only [mul_comm, mul_left_comm, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanE
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem one_mem_eSpan (K : Type) [CommRing K] (n : ℕ) :
    (1 : MvPolynomial (Fin n) K) ∈ eSpan K n 0 := by
  unfold eSpan
  exact Submodule.subset_span ⟨Fin.elim0, by simp⟩

private theorem esymm_mem_eSpan (K : Type) [CommRing K] (n : ℕ) (i : Fin n) :
    esymm (Fin n) K ((i : ℕ) + 1) ∈ eSpan K n 1 := by
  unfold eSpan
  exact Submodule.subset_span ⟨fun _ => i.succ, by simp⟩

private theorem exists_mem_eSpan (h : ESpanMul) (K : Type) [CommRing K] (n : ℕ)
    (q : MvPolynomial (Fin n) K) :
    ∃ k, aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q ∈ eSpan K n k := by
  obtain ⟨hmono, hmul⟩ := h K n
  induction q using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, ?_⟩
    rw [aeval_C, Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ a (one_mem_eSpan K n)
  | add p q hp hq =>
    obtain ⟨k, hk⟩ := hp
    obtain ⟨l, hl⟩ := hq
    refine ⟨max k l, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem _ (hmono _ _ (le_max_left k l) hk) (hmono _ _ (le_max_right k l) hl)
  | mul_X p i hp =>
    obtain ⟨k, hk⟩ := hp
    refine ⟨k + 1, ?_⟩
    rw [map_mul, aeval_X]
    exact hmul _ _ _ _ hk (esymm_mem_eSpan K n i)

theorem spanE_of : ESpanMul → SpanE := by
  intro h K _ n P hP
  obtain ⟨q, hq⟩ := esymmAlgHom_fin_surjective K (le_refl n) ⟨P, (mem_symmetricSubalgebra P).2 hP⟩
  have hq' : aeval (fun i : Fin n => esymm (Fin n) K ((i : ℕ) + 1)) q = P := by
    have := congrArg Subtype.val hq
    rwa [esymmAlgHom_apply] at this
  obtain ⟨k₀, hk₀⟩ := exists_mem_eSpan h K n q
  refine ⟨k₀, fun k hk => ?_⟩
  have hmem := (h K n).1 _ _ hk hk₀
  rw [hq'] at hmem
  unfold eSpan at hmem
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hmem
  exact ⟨w, hw.symm⟩

end UpperTheory.Gal.Schur
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanProd
section
open Finset MvPolynomial UpperTheory.Gal.Schur

theorem UpperTheory.Gal.Schur.spanProd_of :
    SpanE → SpanProd := by
  intro hS K ι _ _ _ n P hP
  choose k0 hk0 using fun t => hS K n (P t) (hP t)
  refine ⟨univ.sup k0, fun k hk => ?_⟩
  have hle : ∀ t, k0 t ≤ k := fun t => (le_sup (mem_univ t)).trans hk
  choose w hw using fun t => hk0 t k (hle t)
  refine ⟨fun m => ∏ t, (w t (fun s => m (t, s)) * ∏ s, (-1 : K) ^ ((m (t, s) : Fin (n + 1)) : ℕ)), ?_⟩
  intro R _ _ g
  have step : ∀ t, aeval (g t) (P t) = ∑ m : Fin k → Fin (n + 1),
      (w t m * ∏ s, (-1 : K) ^ (m s : ℕ)) • ∏ s, ((-1) ^ (m s : ℕ) * aeval (g t) (esymm (Fin n) K (m s))) := by
    intro t
    conv_lhs => rw [hw t]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_prod]
    refine sum_congr rfl fun m _ => ?_
    rw [prod_mul_distrib, Algebra.smul_def, Algebra.smul_def, map_mul, map_prod]
    simp only [map_pow, map_neg, map_one]
    have hc : (∏ s, (-1 : R) ^ (m s : ℕ)) * ∏ s, (-1 : R) ^ (m s : ℕ) = 1 := by
      rw [← prod_mul_distrib]
      simp [← mul_pow]
    linear_combination (-(algebraMap K R (w t m) * ∏ s, aeval (g t) (esymm (Fin n) K (m s)))) * hc
  simp only [step]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.curry ι (Fin k) (Fin (n + 1))).symm _ _ fun M => ?_
  rw [Fintype.prod_prod_type]
  simp only [Equiv.curry_symm_apply, Function.uncurry_apply_pair, Algebra.smul_def, map_prod,
    prod_mul_distrib]
  rw [← map_prod, prod_mul_distrib]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.PSpanTop
section
noncomputable section

open Finset MvPolynomial

namespace UpperTheory.Gal.Schur

private theorem span_embeddings_mul_eq_univ_of_injective {O K ι : Type} [CommRing O] [Field K] [Fintype ι] (τ : ι → O →+* K)
    (hτ : Function.Injective τ) (N : O) (hN : ∀ t, τ t N ≠ 0) :
    Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} = ⊤ := by
  classical
  by_contra hne
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hφv : ∀ v : ι → K, φ v = ∑ t, v t * φ (Pi.single t 1) := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ φ v]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_eq_mul]
    congr 2
    ext s
    simp [Pi.single_apply, eq_comm]
  have hzero : ∀ x : O, ∑ t, (φ (Pi.single t 1) * τ t N) * τ t x = 0 := by
    intro x
    have hx : (fun t => τ t (N * x)) ∈ Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)} :=
      Submodule.subset_span ⟨x, rfl⟩
    have : φ (fun t => τ t (N * x)) = 0 := by
      have h2 := Submodule.mem_map_of_mem (f := φ) hx
      rw [hmap, Submodule.mem_bot] at h2
      exact h2
    rw [hφv] at this
    rw [← this]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul]
    ring
  have hli : LinearIndependent K (fun t => ((τ t : O →* K) : O → K)) := by
    refine (linearIndependent_monoidHom O K).comp (fun t => (τ t : O →* K)) ?_
    intro a b hab
    apply hτ
    ext y
    exact DFunLike.congr_fun hab y
  have hc : ∀ t, φ (Pi.single t 1) * τ t N = 0 := by
    refine Fintype.linearIndependent_iff.1 hli _ ?_
    funext x
    simpa [Finset.sum_apply] using hzero x
  apply hφ
  refine LinearMap.ext fun v => ?_
  rw [hφv, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  rw [(mul_eq_zero.1 (hc t)).resolve_right (hN t), mul_zero]

theorem spanTop : SpanTop := by
  classical
  intro O K ι _ _ _ τ hτ N hN k
  have hA := span_embeddings_mul_eq_univ_of_injective τ hτ N hN
  let L : Fin k → (ι → K) →ₗ[K] (ι × Fin k → K) := fun j =>
    LinearMap.pi (fun p => if p.2 = j then LinearMap.proj p.1 else 0)
  have hL : ∀ j w p, L j w p = if p.2 = j then w p.1 else 0 := by
    intro j w p
    simp only [L, LinearMap.pi_apply]
    split_ifs <;> simp
  have hsub : ∀ j, Submodule.map (L j) (Submodule.span K {v : ι → K | ∃ x : O, v = fun t => τ t (N * x)}) ≤
      Submodule.span K {x | ∃ β : Fin k → O, x = pt τ fun s ↦ N * β s} := by
    intro j
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨v, ⟨x, rfl⟩, rfl⟩
    refine ⟨Pi.single j x, ?_⟩
    funext p
    rw [hL]
    simp only [pt, Pi.single_apply]
    split_ifs <;> simp_all
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ j, L j (fun t => v (t, j)) := by
    funext p
    simp [Finset.sum_apply, hL]
  rw [hv]
  refine Submodule.sum_mem _ fun j _ => hsub j ?_
  refine Submodule.mem_map_of_mem ?_
  rw [hA]
  exact Submodule.mem_top

end UpperTheory.Gal.Schur
end
end

