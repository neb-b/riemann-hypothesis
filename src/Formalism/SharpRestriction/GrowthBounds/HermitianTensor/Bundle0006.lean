module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.QaWeightRowInd
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.SubYGenCoefHom
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.GrowthOfBasic
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.MemInvariantSectionsIffIntegral
public import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionBlockEmb
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

section LC

variable {K σ ρ : Type} [Field K]

private theorem coeff_lcoef_eq (L : MvPolynomial ρ K →ₗ[K] K) (f : MvPolynomial σ (MvPolynomial ρ K))
    (w : σ →₀ ℕ) : AddMonoidAlgebra.coeff (lcoef L f) w = L (AddMonoidAlgebra.coeff f w) :=
  coeff_sum_monomial_linear L f w

theorem qa_lcoef_C (L : MvPolynomial ρ K →ₗ[K] K) (b : MvPolynomial ρ K) :
    lcoef L (C b : MvPolynomial σ (MvPolynomial ρ K)) = C (L b) := by
  classical
  ext w
  rw [coeff_lcoef_eq, coeff_C, coeff_C]
  split_ifs <;> simp

theorem qa_lcoef_mapC_mul (L : MvPolynomial ρ K →ₗ[K] K) (G : MvPolynomial σ K)
    (h : MvPolynomial σ (MvPolynomial ρ K)) : lcoef L (map C G * h) = G * lcoef L h := by
  classical
  ext w
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_lcoef_eq, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_lcoef_eq, MvPolynomial.C_mul', map_smul, smul_eq_mul]

theorem qa_eval_lcoef (L : MvPolynomial ρ K →ₗ[K] K) (x : σ → K) (h : MvPolynomial σ (MvPolynomial ρ K)) :
    eval x (lcoef L h) = L (eval (fun i => C (x i)) h) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show lcoef L h = ∑ u ∈ h.support, monomial u (L (AddMonoidAlgebra.coeff h u)) from rfl, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [h.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [eval_monomial, eval_monomial]
  rw [show (u.prod fun n e => (C (x n) : MvPolynomial ρ K) ^ e) = C (u.prod fun n e => x n ^ e) by
    simp [Finsupp.prod, map_prod, map_pow]]
  rw [mul_comm (AddMonoidAlgebra.coeff h u), MvPolynomial.C_mul', map_smul, smul_eq_mul, mul_comm]

theorem qa_lcoef_rowAct {k n : ℕ} (L : MvPolynomial ρ K →ₗ[K] K) (g : Matrix (Fin k) (Fin k) K)
    (h : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) :
    lcoef L (rowAct (MvPolynomial ρ K) (g.map C) h) = rowAct K g (lcoef L h) := by
  classical
  have key : ∀ P : MvPolynomial (Fin k × Fin n) K,
      rowAct (MvPolynomial ρ K) (g.map C) (map C P) = map C (rowAct K g P) := by
    intro P
    have e := MvPolynomial.ringHom_ext
      (f := ((rowAct (MvPolynomial ρ K) (n := n) (g.map C)).toRingHom.comp (map C) :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (g := ((map C).comp (rowAct K (n := n) g).toRingHom :
        MvPolynomial (Fin k × Fin n) K →+* MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)))
      (fun a => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hm : (monomial u (AddMonoidAlgebra.coeff h u) : MvPolynomial (Fin k × Fin n) (MvPolynomial ρ K)) =
      map C (monomial u 1) * C (AddMonoidAlgebra.coeff h u) := by
    rw [map_monomial, map_one, mul_comm, C_mul_monomial, mul_one]
  have hr1 : rowAct (MvPolynomial ρ K) (n := n) (g.map C) (C (AddMonoidAlgebra.coeff h u)) = C (AddMonoidAlgebra.coeff h u) := by simp [rowAct]
  have hr2 : rowAct K (n := n) g (C (L (AddMonoidAlgebra.coeff h u))) = C (L (AddMonoidAlgebra.coeff h u)) := by simp [rowAct]
  rw [hm, map_mul, key, hr1, qa_lcoef_mapC_mul, qa_lcoef_mapC_mul, qa_lcoef_C, map_mul, hr2]

end LC

section S2

variable {K : Type} [Field K] {r : ℕ}

theorem qa_blockEmb_C {S : Type} {k n : ℕ} (b : S) (a : K) : blockEmb K (k := k) (n := n) b (C a) = C a := by
  simp [blockEmb]

theorem qa_blockEmb_X {S : Type} {k n : ℕ} (b : S) (x : Fin k × Fin n) : blockEmb K b (X x) = X (b, x) := by
  simp [blockEmb]

theorem block_substitution_C (a : K) : sub2 K r (C a) = C (C a) := by
  simp [sub2]

theorem block_substitution_X (b : Bool) (x : Fin (r + 1 + 1) × Fin (r + 1 + 1)) :
    sub2 K r (X (b, x)) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r (X x)) := by
  simp [sub2]

theorem block_substitution_blockEmb (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = map (blockEmb K (k := r) (n := r) b).toRingHom (subY K r v) := by
  induction v using MvPolynomial.induction_on
  next a =>
    rw [qa_blockEmb_C, block_substitution_C]
    simp [subY]
  next p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  next p x hp =>
    rw [map_mul, map_mul, hp, qa_blockEmb_X, block_substitution_X, map_mul, map_mul]

theorem qa_blockEmb_comp_C (b : Bool) :
    ((blockEmb K (k := r) (n := r) b).toRingHom).comp C = (C : K →+* MvPolynomial (Bool × (Fin r × Fin r)) K) := RingHom.ext fun a => by simp

theorem qa_lamOf_apply (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (x : MvPolynomial (Bool × (Fin (r + 1 + 1) × Fin (r + 1 + 1))) K) : lamOf K r L x = lcoef L (sub2 K r x) := rfl

theorem qa_eval_map_block (b : Bool)
    (h : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)) :
    eval (fun i => (C (idPoint K (r + 1 + 1) (r + 1 + 1) i) : MvPolynomial (Bool × (Fin r × Fin r)) K))
        (map (blockEmb K (k := r) (n := r) b).toRingHom h) =
      blockEmb K b (eval (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h) := by
  rw [MvPolynomial.eval_map]
  show _ = (blockEmb K (k := r) (n := r) b).toRingHom
    (MvPolynomial.eval₂ (RingHom.id _) (idPoint (MvPolynomial (Fin r × Fin r) K) (r + 1 + 1) (r + 1 + 1)) h)
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  simp only [Function.comp_apply, idPoint]
  split_ifs <;> simp

end S2

theorem lamCoeffP : LamCoeffP := by
  classical
  intro K _ r L v t u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, coeff_lcoef_eq, coeff_mul, map_sum]
  simp only [coeff_map]
  rfl

theorem lamMulP : LamMulP := by
  classical
  intro K _ r Q L F s t hF
  rw [qa_lamOf_apply, map_mul (blockEmb K true) F s, map_mul (sub2 K r), map_mul (sub2 K r),
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, hF,
    map_mul (map (blockEmb K (k := r) (n := r) true).toRingHom), map_C, MvPolynomial.map_map,
    qa_blockEmb_comp_C, ← qa_lcoef_mapC_mul]
  congr 1
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

theorem lamEvalP : LamEvalP := by
  classical
  intro K _ r L v t
  rw [qa_lamOf_apply, map_mul, block_substitution_blockEmb, block_substitution_blockEmb, qa_eval_lcoef, map_mul,
    qa_eval_map_block, qa_eval_map_block]
  rfl

theorem lamEquivP : LamEquivP := by
  intro K _ r L g v t
  have hcomm : ∀ (b : Bool) (P : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K)),
      map (blockEmb K (k := r) (n := r) b).toRingHom
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C) P) =
        rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)
          (map (blockEmb K (k := r) (n := r) b).toRingHom P) := by
    intro b P
    have e := MvPolynomial.ringHom_ext
      (f := ((map (blockEmb K (k := r) (n := r) b).toRingHom).comp
          (rowAct (MvPolynomial (Fin r × Fin r) K) (n := r + 1 + 1) (g.map C)).toRingHom :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (g := ((rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)).toRingHom.comp
          (map (blockEmb K (k := r) (n := r) b).toRingHom) :
        MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) K) →+*
          MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K)))
      (fun c => by simp [rowAct]) (fun i => by simp [rowAct, Matrix.map_apply, map_sum])
    simpa using RingHom.congr_fun e P
  rw [qa_lamOf_apply, qa_lamOf_apply, map_mul (sub2 K r), map_mul (sub2 K r), block_substitution_blockEmb,
    block_substitution_blockEmb, block_substitution_blockEmb, block_substitution_blockEmb, qa_subY_rowAct, qa_subY_rowAct, hcomm, hcomm,
    ← map_mul (rowAct (MvPolynomial (Bool × (Fin r × Fin r)) K) (n := r + 1 + 1) (g.map C)), qa_lcoef_rowAct]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.BlockSubstitutionEmbedding
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf.QB

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def th (K : Type) [Field K] (r : ℕ) (b : Bool) :
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K →ₐ[K]
      MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Bool × (Fin r × Fin r)) K) :=
  (mapAlgHom (blockEmb K (k := r) (n := r) b)).comp (subY K r)

theorem blockEmb_X (K : Type) [Field K] {k n : ℕ} (b : Bool) (x : Fin k × Fin n) :
    blockEmb K b (X x) = (X (b, x) : MvPolynomial (Bool × (Fin k × Fin n)) K) := by
  show rename _ (X x) = _
  rw [rename_X]

theorem th_C (K : Type) [Field K] (r : ℕ) (b : Bool) (a : K) : th K r b (C a) = C (C a) := by
  rw [th, AlgHom.comp_apply, subY_C, mAH_C, algHom_C, algebraMap_eq]

theorem th_X_mid (K : Type) [Field K] (r : ℕ) (b : Bool) (a : Fin (r + 1 + 1)) (j : Fin r) :
    th K r b (X (a, midI r j)) = ∑ i : Fin r, C (X (b, (i, j))) * X (a, midI r i) := by
  rw [th, AlgHom.comp_apply, mAH_subY_mid]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockEmb_X]

theorem th_X_none (K : Type) [Field K] (r : ℕ) (b : Bool) (a t : Fin (r + 1 + 1)) (h : midOf t = none) :
    th K r b (X (a, t)) = X (a, t) := by
  rw [th, AlgHom.comp_apply, mAH_subY_none r _ a t h]

theorem th_coeff (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)
    (u : Fin (r + 1 + 1) × Fin (r + 1 + 1) →₀ ℕ) :
    AddMonoidAlgebra.coeff (th K r b v) u = blockEmb K b (AddMonoidAlgebra.coeff (subY K r v) u) := by
  rw [th, AlgHom.comp_apply, mAH_coeff]

theorem block_substitution_embedding (K : Type) [Field K] (r : ℕ) (b : Bool) (v : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    sub2 K r (blockEmb K b v) = th K r b v := by
  have : (sub2 K r).comp (blockEmb K (k := r + 1 + 1) (n := r + 1 + 1) b) = th K r b := by
    apply algHom_ext
    intro w
    rw [AlgHom.comp_apply, blockEmb_X]
    unfold sub2
    rw [aeval_X]
    rfl
  exact AlgHom.congr_fun this v

theorem lam_eq (K : Type) [Field K] (r : ℕ) (L : MvPolynomial (Bool × (Fin r × Fin r)) K →ₗ[K] K)
    (v t : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K) :
    lamOf K r L (blockEmb K true v * blockEmb K false t) = lcoef L (th K r true v * th K r false t) := by
  unfold lamOf
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, block_substitution_embedding, block_substitution_embedding]

section Psi

variable {K B σ : Type} [Field K] [CommRing B] [Algebra K B]

def psiB (B : Type) [CommRing B] [Algebra K B] (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) :
    MvPolynomial σ B →+* MvPolynomial σ B :=
  eval₂Hom C (fun w => map (algebraMap K B) (ψ (X w)))

theorem psiB_C (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (b : B) : psiB B ψ (C b) = C b := by
  show eval₂ _ _ (C b) = _
  rw [eval₂_C]

theorem psiB_X (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (w : σ) :
    psiB B ψ (X w) = map (algebraMap K B) (ψ (X w)) := by
  show eval₂ _ _ (X w) = _
  rw [eval₂_X]

theorem psiB_map (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (G : MvPolynomial σ K) :
    psiB B ψ (map (algebraMap K B) G) = map (algebraMap K B) (ψ G) := by
  have : (psiB B ψ).comp (map (algebraMap K B)) = (map (algebraMap K B)).comp (ψ : MvPolynomial σ K →+* MvPolynomial σ K) := by
    apply ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_C, psiB_C, algHom_C, algebraMap_eq]
    · intro w
      simp only [RingHom.comp_apply, RingHom.coe_coe, map_X, psiB_X]
  exact RingHom.congr_fun this G

theorem lcoef_C_mul_map (L : B →ₗ[K] K) (b : B) (G : MvPolynomial σ K) :
    lcoef L (C b * map (algebraMap K B) G) = L b • G := by
  ext u
  rw [coeff_lcoef, coeff_C_mul, coeff_map, coeff_smul, smul_eq_mul, mul_comm b, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

theorem lcoef_comm (ψ : MvPolynomial σ K →ₐ[K] MvPolynomial σ K) (L : B →ₗ[K] K) (h : MvPolynomial σ B) :
    ψ (lcoef L h) = lcoef L (psiB B ψ h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial u b =>
    have e : (monomial u b : MvPolynomial σ B) = C b * map (algebraMap K B) (monomial u 1) := by
      rw [map_monomial, map_one, C_mul_monomial, mul_one]
    rw [e, lcoef_C_mul_map, map_mul, psiB_map, psiB_C, lcoef_C_mul_map, map_smul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]

theorem hom_eq_on {S : Type} [CommRing S] (f g : MvPolynomial σ K →+* S) (hC : ∀ a, f (C a) = g (C a))
    (hX : ∀ w, f (X w) = g (X w)) (v : MvPolynomial σ K) : f v = g v := by
  rw [ringHom_ext hC hX]

end Psi

theorem pow_exp_inj {K : Type} [Field K] [Infinite K] (a b : ℕ) (h : ∀ c : K, c ≠ 0 → c ^ a = c ^ b) : a = b := by
  have h1 : (Polynomial.X ^ (a + 1) : Polynomial K) = Polynomial.X ^ (b + 1) := by
    apply Polynomial.funext
    intro c
    simp only [Polynomial.eval_pow, Polynomial.eval_X]
    by_cases hc : c = 0
    · rw [hc, zero_pow (Nat.succ_ne_zero _), zero_pow (Nat.succ_ne_zero _)]
    · rw [pow_succ, pow_succ, h c hc]
  have h2 := congrArg Polynomial.natDegree h1
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at h2
  omega

section Scale

variable {K : Type} [Field K]

theorem sc_monomial {σ : Type} (d : σ → K) (u : σ →₀ ℕ) (a : K) :
    aeval (fun w => C (d w) * X w) (monomial u a) = monomial u (a * u.prod fun w e => d w ^ e) := by
  rw [aeval_monomial]
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (d v) : MvPolynomial σ K) ^ e) = C (u.prod fun v e => d v ^ e) := by
    rw [map_finsuppProd]; simp only [map_pow]
  rw [hC, monomial_eq, C_mul, algebraMap_eq]
  ring

theorem sc_coeff {σ : Type} (d : σ → K) (f : MvPolynomial σ K) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun w => C (d w) * X w) f) m = AddMonoidAlgebra.coeff f m * m.prod fun w e => d w ^ e := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [sc_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

def scCol (K : Type) [Field K] (k : ℕ) (t0 : Fin k) (c : K) :
    MvPolynomial (Fin k × Fin k) K →ₐ[K] MvPolynomial (Fin k × Fin k) K :=
  aeval (fun w => C (if w.2 = t0 then c else 1) * X w)

theorem scCol_X {k : ℕ} (t0 : Fin k) (c : K) (w : Fin k × Fin k) :
    scCol K k t0 c (X w) = C (if w.2 = t0 then c else 1) * X w := by
  unfold scCol
  rw [aeval_X]

theorem sc_prod {k : ℕ} (t0 : Fin k) (c : K) (m : Fin k × Fin k →₀ ℕ) :
    (m.prod fun w e => (if w.2 = t0 then c else 1) ^ e) = c ^ (Finsupp.weight (colW k k) m t0) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type, lccomp_weight_colW_apply,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Finset.prod_eq_single t0]
  · simp
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem scCol_coeff {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (m : Fin k × Fin k →₀ ℕ) :
    AddMonoidAlgebra.coeff (scCol K k t0 c f) m = AddMonoidAlgebra.coeff f m * c ^ (Finsupp.weight (colW k k) m t0) := by
  unfold scCol
  rw [sc_coeff, sc_prod]

theorem scCol_of_hom {k : ℕ} (t0 : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K) (ν : Fin k → ℕ)
    (hf : IsWeightedHomogeneous (colW k k) f ν) : scCol K k t0 c f = c ^ ν t0 • f := by
  ext m
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm]
  by_cases h : AddMonoidAlgebra.coeff f m = 0
  · rw [h, mul_zero, mul_zero]
  · rw [hf h]

theorem wt_of_scale [Infinite K] {k : ℕ} (t0 : Fin k) (n : ℕ) (f : MvPolynomial (Fin k × Fin k) K)
    (h : ∀ c : K, c ≠ 0 → scCol K k t0 c f = c ^ n • f) (m : Fin k × Fin k →₀ ℕ) (hm : AddMonoidAlgebra.coeff f m ≠ 0) :
    Finsupp.weight (colW k k) m t0 = n := by
  apply pow_exp_inj (K := K)
  intro c hc
  have := congrArg (AddMonoidAlgebra.coeff · m) (h c hc)
  rw [scCol_coeff, coeff_smul, smul_eq_mul, mul_comm] at this
  exact mul_right_cancel₀ hm this

theorem colAdd_trivial {k : ℕ} (l j : Fin k) (c : K) (f : MvPolynomial (Fin k × Fin k) K)
    (hf : ∀ m, AddMonoidAlgebra.coeff f m ≠ 0 → Finsupp.weight (colW k k) m j = 0) : colAdd K l j c f = f := by
  classical
  have e : colAdd K l j c f = ∑ m ∈ f.support, colAdd K l j c (monomial m (AddMonoidAlgebra.coeff f m)) := by
    conv_lhs => rw [f.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
  rw [e]
  conv_rhs => rw [f.as_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  unfold colAdd
  rw [aeval_monomial, monomial_eq, algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro w hw
  have hwj : w.2 ≠ j := by
    intro h
    have h0 := hf m (mem_support_iff.1 hm)
    rw [lccomp_weight_colW_apply] at h0
    have h1 := Finset.sum_eq_zero_iff.1 h0 w.1 (Finset.mem_univ _)
    have e2 : w = (w.1, j) := Prod.ext rfl h
    apply Finsupp.mem_support_iff.1 hw
    rw [e2]
    exact h1
  rw [if_neg hwj]

end Scale

end Formalism.MainNotions.flipOneThree.Pf.QB

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.HermitianTensor.PbSmithLam
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem pb_nabla_one {O K : Type} [CommRing O] [Field K] [Algebra O K] (m : ℕ) (lam : Fin (m + 1) → ℤ) :
    nablaLTw O K m lam 1 = intO O (m + 1) (nuOf lam) := by
  ext F
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m lam 1 (by simp) F, Matrix.det_one, one_zpow, one_smul, tn_rowAct_one]
  exact Iff.rfl

theorem pb_finrank (K : Type) [Field K] (n : ℕ) (nu : Fin n → ℕ) (hnu : Antitone nu) :
    (Module.finrank K (dualWeyl K n n nu) : ℚ) = weylDim n (fun i => (nu i : ℤ)) := by
  rw [Formalism.L2.G.Model.weyl_dualWeyl K n nu hnu]
  unfold weylDim
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  push_cast
  rfl

theorem pb_smith_lam {p n' : ℕ} (R : RS p n') (m : ℕ) (lam : Fin (m + 1) → ℤ) (hlam : Antitone lam) :
    ∃ B : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf] R.Kf,
      (∀ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Kf) (P Q : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
        B (rowAct R.Kf g P) Q = B P (rowAct R.Kf g.transpose Q)) ∧
      (∀ P ∈ intO R.O (m + 1) (nuOf lam), ∀ Q ∈ intO R.O (m + 1) (nuOf lam), B P Q ∈ Set.range (algebraMap R.O R.Kf)) ∧
      ∃ (nb : ℕ) (x x' : Fin nb → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf) (ka : Fin nb → ℕ),
        (nb : ℚ) = weylDim (m + 1) (fun j => (nuOf lam j : ℤ)) ∧ (∀ b, ka b ≤ Formalism.L2.G.Model.expN p m lam) ∧
        (∀ b, x b ∈ intO R.O (m + 1) (nuOf lam)) ∧ (∀ a', x' a' ∈ intO R.O (m + 1) (nuOf lam)) ∧
        ∀ a' b, B (x b) (x' a') = if a' = b then (p : R.Kf) ^ ka b else 0 := by
  classical
  have hfr := R.std.1.frac_O
  have hinj : Function.Injective (algebraMap R.O R.Kf) := IsFractionRing.injective R.O R.Kf
  obtain ⟨B0, ha, hb, hc, hd⟩ :=
    Formalism.L2.G.Model.formCore p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m lam hlam
  obtain ⟨Bs, -, hB1, hB3, hB2⟩ := la_basis hinj m lam 1 (by rw [Matrix.det_one]; exact isUnit_one)
  rw [pb_nabla_one] at hB1
  have : Fintype ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) := (sSIdxFinite _ _ _).fintype
  let e : Fin (Fintype.card ↥(ssIdx (m + 1) (m + 1) (nuOf lam))) ≃ ↥(ssIdx (m + 1) (m + 1) (nuOf lam)) :=
    (Fintype.equivFin _).symm
  have hrange : Set.range (Bs ∘ e) = Set.range Bs := e.surjective.range_comp Bs
  have hli : LinearIndependent R.Kf (Bs ∘ e) := hB3.comp e e.injective
  have hsK : Submodule.span R.Kf (Set.range (Bs ∘ e)) = dualWeyl R.Kf (m + 1) (m + 1) (nuOf lam) := by rw [hrange, hB2]
  have hsO : Submodule.span R.O (Set.range (Bs ∘ e)) = intO R.O (m + 1) (nuOf lam) := by rw [hrange, hB1]
  have hpc : algebraMap R.O R.Kf (p : R.O) = (p : R.Kf) := map_natCast _ p
  obtain ⟨x, x', ka, hka, hx, hx', hdiag⟩ := pb_abs (O := R.O) (K := R.Kf) R.w (p : R.O) R.std.2.1 R.std.1.w_sq
    (Formalism.L2.G.Model.expN p m lam) _ (Bs ∘ e) hli B0
    (by rw [hsK]; exact hb)
    (by rw [hsK, hsO]; exact hc)
    (by rw [hsO, hpc]; exact hd)
  rw [hsO] at hx hx'
  rw [hpc] at hdiag
  refine ⟨((p : R.Kf) ^ Formalism.L2.G.Model.expN p m lam) • B0, ?_, ?_, _, x, x', ka, ?_, hka, hx, hx', ?_⟩
  · intro g P Q
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, ha]
  · intro P hP Q hQ
    have h := hd Q hQ P hP
    rw [map_smul] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply]
    exact h
  · rw [← pb_finrank R.Kf (m + 1) (nuOf lam) (nuOf_anti lam hlam), ← hsK, finrank_span_eq_card hli, Fintype.card_fin]
  · intro a' b
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact hdiag a' b

theorem smithP : SmithP := by
  intro p n' R m ν hνA hν0
  have hlam : Antitone (fun j => ((ν j : ℕ) : ℤ)) := fun i j h => by
    show ((ν j : ℕ) : ℤ) ≤ ((ν i : ℕ) : ℤ)
    exact_mod_cast hνA h
  have hnu : nuOf (fun j => ((ν j : ℕ) : ℤ)) = ν := by
    funext t
    simp only [nuOf, hν0]
    simp
  have hexp : Formalism.L2.G.Model.expN p m (fun j => ((ν j : ℕ) : ℤ)) ≤ N0 (m + 1) * deF p (m + 1) (ν 0) := by
    unfold Formalism.L2.G.Model.expN
    split_ifs
    · exact Nat.zero_le _
    · have : ellWt (fun j : Fin (m + 1) => ((ν j : ℕ) : ℤ)) = ν 0 := by
        unfold ellWt
        have hl : lastIdx (m + 1) = Fin.last m := Fin.ext (by simp [lastIdx])
        rw [hl]
        show (((ν 0 : ℕ) : ℤ) - ((ν (Fin.last m) : ℕ) : ℤ)).toNat = ν 0
        rw [hν0]
        simp
      rw [this]
  obtain ⟨B, h1, h2, nb, x, x', ka, h3, h4, h5, h6, h7⟩ := pb_smith_lam R m _ hlam
  rw [hnu] at h2 h3 h5 h6
  exact ⟨B, h1, h2, nb, x, x', ka, h3, fun b => (h4 b).trans hexp, h5, h6, h7⟩

end Formalism.MainNotions.flipOneThree.Pf

end
end

