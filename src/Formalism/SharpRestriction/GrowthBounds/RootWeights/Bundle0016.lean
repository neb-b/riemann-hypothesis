module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0014
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0023
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.CasimirPowerScaledInsertDividedPower
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section Alg

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def singleConjugation (E : GLOps n K V) (c i : Fin n) : Module.End K (Module.End K V) :=
  (LinearMap.mulLeft K (E c i)).comp (LinearMap.mulRight K (E i c))

theorem singleConjugation_apply (E : GLOps n K V) (c i : Fin n) (X : Module.End K V) :
    singleConjugation E c i X = E c i * (X * E i c) := rfl

theorem singleConjugation_pow_apply (E : GLOps n K V) (c i : Fin n) (k : ℕ) (X : Module.End K V) :
    ((singleConjugation E c i) ^ k) X = (E c i) ^ k * (X * (E i c) ^ k) := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, singleConjugation_apply, pow_succ, pow_succ']
    simp only [mul_assoc]

theorem casimirConjugation_eq_sum_single (E : GLOps n K V) (c : Fin n) (s : Finset (Fin n)) :
    casimirConjugation E c s = ∑ i ∈ s, singleConjugation E c i := rfl

theorem singleConjugation_commute {E : GLOps n K V} (hE : IsGLRep E) (c i j : Fin n) (hi : i ≠ c) (hj : j ≠ c) :
    Commute (singleConjugation E c i) (singleConjugation E c j) := by
  have h1 : E c i * E c j = E c j * E c i := by
    have := hE.1 c i c j
    rw [if_neg hi, if_neg hj, sub_zero, sub_eq_zero] at this
    exact this
  have h2 : E j c * E i c = E i c * E j c := by
    have := hE.1 j c i c
    rw [if_neg (Ne.symm hi), if_neg (Ne.symm hj), sub_zero, sub_eq_zero] at this
    exact this
  unfold Commute SemiconjBy
  ext X : 1
  simp only [Module.End.mul_apply, singleConjugation_apply, ← mul_assoc, h1]
  simp only [mul_assoc, h2]

theorem casimirPowerW_insert_binomial {E : GLOps n K V} (hE : IsGLRep E) (c i : Fin n) (s : Finset (Fin n)) (his : i ∉ s)
    (hi : i ≠ c) (hs : ∀ j ∈ s, j ≠ c) (q : ℕ) :
    casimirPower E c (insert i s) q =
      ∑ k ∈ range (q + 1), (q.choose k) • ((E c i) ^ k * (casimirPower E c s (q - k) * (E i c) ^ k)) := by
  have hc : Commute (singleConjugation E c i) (casimirConjugation E c s) := by
    rw [casimirConjugation_eq_sum_single]
    exact Commute.sum_right _ _ _ fun j hj => singleConjugation_commute hE c i j hi (hs j hj)
  unfold casimirPower
  rw [casimirConjugation_eq_sum_single E c (insert i s), Finset.sum_insert his, ← casimirConjugation_eq_sum_single, hc.add_pow, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, Module.End.natCast_apply, map_nsmul, map_nsmul,
    singleConjugation_pow_apply]

theorem casimirPowerW_empty (E : GLOps n K V) (c : Fin n) (q : ℕ) :
    casimirPower E c ∅ q = if q = 0 then 1 else 0 := by
  unfold casimirPower casimirConjugation
  rw [Finset.sum_empty]
  rcases q with _ | q <;> simp

end Alg

section Alg2

variable {n : ℕ} {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]

theorem factorial_ratio_choose_identity (b q k : ℕ) (hk : k ≤ q) :
    ((b.factorial : K) / (((q + b).factorial : K) * (q.factorial : K))) * ((q.choose k : ℕ) : K) =
      (1 / (((q + b).choose k : ℕ) : K)) * ((k.factorial : K)⁻¹ *
        (((b.factorial : K) / (((q - k + b).factorial : K) * ((q - k).factorial : K))) * (k.factorial : K)⁻¹)) := by
  have hk' : k ≤ q + b := le_trans hk (Nat.le_add_right q b)
  rw [Nat.cast_choose K hk, Nat.cast_choose K hk', Nat.sub_add_comm hk]
  have h1 : ((q + b).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : (q.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (k.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h4 : ((q - k).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h5 : ((q - k + b).factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h6 : (b.factorial : K) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

theorem casimirPowerScaled_insert_dividedPower {E : GLOps n K V} (hE : IsGLRep E) (c i : Fin n) (s : Finset (Fin n)) (his : i ∉ s)
    (hi : i ≠ c) (hs : ∀ j ∈ s, j ≠ c) (b q : ℕ) (y : V) :
    casimirPowerScaled E c (insert i s) b q y =
      ∑ k ∈ range (q + 1), (1 / (((q + b).choose k : ℕ) : K)) •
        divPowE E c i k (casimirPowerScaled E c s b (q - k) (divPowE E i c k y)) := by
  unfold casimirPowerScaled divPowE
  rw [casimirPowerW_insert_binomial hE c i s his hi hs q]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum, Module.End.mul_apply, map_smul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [← Nat.cast_smul_eq_nsmul K, smul_smul]
  congr 1
  rw [factorial_ratio_choose_identity b q k hkq]

end Alg2

section Lattice

variable {p : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : ℕ} {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

private theorem isUnit_natCast_of_not_dvd_root_weights (S : UniformizedDVR p O) (hp : p.Prime) (u : ℕ) (hu : ¬ p ∣ u) :
    IsUnit (u : O) := by
  by_contra hnu
  have hum : (u : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hcop : IsCoprime (u : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu))
  obtain ⟨x, z, hxz⟩ := hcop
  have h1 : ((x * u + z * p : ℤ) : O) = 1 := by rw [hxz]; simp
  push_cast at h1
  have h2 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hum) (Ideal.mul_mem_left _ _ S.p_mem)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h2)

private theorem charZero_KK_of_uniformizedDVR (S : UniformizedDVR p O) (hp : p.Prime) : CharZero (KK O) := by
  refine charZero_of_inj_zero fun N hN => ?_
  by_contra hN0
  have hN' : (N : O) = 0 := by
    apply IsFractionRing.injective O (KK O)
    rw [map_natCast, map_zero, hN]
  have hCu : p ^ N.factorization p * (N / p ^ N.factorization p) = N := by
    first
      | exact Nat.ordProj_mul_ordCompl_eq_self N p
      | exact Nat.ord_proj_mul_ord_compl_eq_self N p
  have hu : ¬ p ∣ (N / p ^ N.factorization p) := by
    first
      | exact Nat.not_dvd_ordCompl hp hN0
      | exact Nat.not_dvd_ord_compl hp hN0
  rw [← hCu, Nat.cast_mul, Nat.cast_pow] at hN'
  rcases mul_eq_zero.mp hN' with h | h
  · exact S.p_ne (pow_eq_zero_iff'.mp h).1
  · exact (isUnit_natCast_of_not_dvd_root_weights S hp _ hu).ne_zero h

private theorem exists_integral_p_pow_div_choose_of_log_le (S : UniformizedDVR p O) (hp : p.Prime) (N k d : ℕ)
    (hN : Nat.log p N ≤ d) (hk : k ≤ N) :
    ∃ o : O, algebraMap O (KK O) o = ((p : KK O) ^ d) * (1 / ((N.choose k : ℕ) : KK O)) := by
  have hC0 : N.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hCu : p ^ (N.choose k).factorization p * (N.choose k / p ^ (N.choose k).factorization p) =
      N.choose k := by
    first
      | exact Nat.ordProj_mul_ordCompl_eq_self (N.choose k) p
      | exact Nat.ord_proj_mul_ord_compl_eq_self (N.choose k) p
  have hu : ¬ p ∣ (N.choose k / p ^ (N.choose k).factorization p) := by
    first
      | exact Nat.not_dvd_ordCompl hp hC0
      | exact Nat.not_dvd_ord_compl hp hC0
  have ha : (N.choose k).factorization p ≤ d := Nat.factorization_choose_le_log.trans hN
  generalize (N.choose k).factorization p = a at hCu hu ha
  generalize N.choose k / p ^ a = u at hCu hu
  have huO : IsUnit (u : O) := isUnit_natCast_of_not_dvd_root_weights S hp u hu
  have hp0 : (p : KK O) ≠ 0 := by
    rw [← map_natCast (algebraMap O (KK O))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr S.p_ne
  have hu0 : ((u : ℕ) : KK O) ≠ 0 := by
    rw [← map_natCast (algebraMap O (KK O))]
    exact (huO.map _).ne_zero
  have hinv : algebraMap O (KK O) ((huO.unit⁻¹ : Oˣ) : O) = ((u : ℕ) : KK O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_natCast (algebraMap O (KK O)), ← map_mul, huO.val_inv_mul, map_one]
  refine ⟨(p : O) ^ (d - a) * ((huO.unit⁻¹ : Oˣ) : O), ?_⟩
  rw [map_mul, map_pow, map_natCast, hinv, ← hCu]
  push_cast
  conv_rhs => rw [← Nat.sub_add_cancel ha, pow_add]
  field_simp
  try ring

theorem scaled_casimirPower_integral_bound (S : UniformizedDVR p O) (hp : p.Prime) {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {M : Submodule O V} (hM : UZStable (O := O) E M) (c : Fin n) (L : ℕ) (s : Finset (Fin n)) :
    (∀ j ∈ s, j ≠ c) → ∀ q b : ℕ, q + b ≤ L + n - 1 → ∀ y ∈ M,
      ((p : O) ^ (s.card * deF p n L)) • casimirPowerScaled E c s b q y ∈ M := by
  haveI := charZero_KK_of_uniformizedDVR S hp
  induction s using Finset.induction_on with
  | empty =>
    intro _ q b _ y hy
    simp only [Finset.card_empty, zero_mul, pow_zero, one_smul]
    unfold casimirPowerScaled
    rw [casimirPowerW_empty]
    split_ifs with hq
    · subst hq
      have hb0 : (b.factorial : KK O) ≠ 0 := by exact_mod_cast (Nat.factorial_pos b).ne'
      simpa [hb0] using hy
    · simp
  | @insert i s his ih =>
    intro hs q b hqb y hy
    have hic : i ≠ c := hs i (Finset.mem_insert_self i s)
    have hs' : ∀ j ∈ s, j ≠ c := fun j hj => hs j (Finset.mem_insert_of_mem hj)
    rw [casimirPowerScaled_insert_dividedPower hE c i s his hic hs' b q y, Finset.smul_sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hy' : divPowE E i c k y ∈ M := hM _ (Or.inl ⟨i, c, k, hic, rfl⟩) y hy
    have hz : ((p : O) ^ (s.card * deF p n L)) • casimirPowerScaled E c s b (q - k) (divPowE E i c k y) ∈ M :=
      ih hs' (q - k) b (by omega) _ hy'
    have hz' := hM _ (Or.inl ⟨c, i, k, Ne.symm hic, rfl⟩) _ hz
    obtain ⟨o, ho⟩ := exists_integral_p_pow_div_choose_of_log_le S hp (q + b) k (deF p n L)
      (by unfold deF; exact Nat.log_mono_right hqb) (by omega)
    have heq : ((p : O) ^ ((insert i s).card * deF p n L)) • ((1 / (((q + b).choose k : ℕ) : KK O)) •
        divPowE E c i k (casimirPowerScaled E c s b (q - k) (divPowE E i c k y))) =
        o • divPowE E c i k (((p : O) ^ (s.card * deF p n L)) •
          casimirPowerScaled E c s b (q - k) (divPowE E i c k y)) := by
      first
        | rw [Finset.card_insert_of_notMem his]
        | rw [Finset.card_insert_of_not_mem his]
      simp only [← algebraMap_smul (R := O) (KK O), map_smul, smul_smul]
      congr 1
      rw [ho]
      simp only [map_pow, map_natCast]
      ring
    rw [heq]
    exact M.smul_mem o hz'

theorem extremalProjector_denominator_bound (S : UniformizedDVR p O) (hp : p.Prime) {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {M : Submodule O V} (hM : UZStable (O := O) E M) (c : Fin n) (L : ℕ) (y : V) (hy : y ∈ M) :
    ((p : O) ^ (c.val * deF p n L)) • extremalProjector E c L y ∈ M := by
  unfold extremalProjector
  rw [LinearMap.sum_apply, Finset.smul_sum]
  refine Submodule.sum_mem _ fun q hq => ?_
  have hqL : q ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have h := scaled_casimirPower_integral_bound S hp hE hM c L (Finset.Iio c) (fun j hj => ne_of_lt (Finset.mem_Iio.mp hj))
    q c.val (by have := c.isLt; omega) y hy
  rw [Fin.card_Iio] at h
  have heq : ((p : O) ^ (c.val * deF p n L)) • (((-1 : KK O) ^ q) • casimirPowerScaled E c (Finset.Iio c) c.val q) y =
      ((-1 : O) ^ q) • (((p : O) ^ (c.val * deF p n L)) • casimirPowerScaled E c (Finset.Iio c) c.val q y) := by
    simp only [LinearMap.smul_apply, ← algebraMap_smul (R := O) (KK O), smul_smul, map_pow, map_neg,
      map_one, map_natCast]
    congr 1
    ring
  rw [heq]
  exact M.smul_mem _ h

end Lattice

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrAevalStable
section
noncomputable section

open Finset Polynomial

namespace Formalism.MainNotions.G.GLWeightTheory

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem cr_pow_mod (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (a : K) (x : V)
    (hx : T x - a • x ∈ Z) (k : ℕ) : (T ^ k) x - a ^ k • x ∈ Z := by
  induction k with
  | zero => simp [Z.zero_mem]
  | succ k ih =>
    have e1 : (T ^ (k + 1)) x = T ((T ^ k) x) := by rw [pow_succ', Module.End.mul_apply]
    have e2 : a ^ (k + 1) • x = a ^ k • (a • x) := by rw [pow_succ, mul_smul]
    have e3 : (T ^ (k + 1)) x - a ^ (k + 1) • x =
        T ((T ^ k) x - a ^ k • x) + a ^ k • (T x - a • x) := by
      rw [e1, e2, map_sub, map_smul, smul_sub]; abel
    rw [e3]
    exact Z.add_mem (hZ _ ih) (Z.smul_mem _ hx)

theorem cr_aeval_mod (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (a : K) (x : V)
    (hx : T x - a • x ∈ Z) (q : K[X]) : aeval T q x - q.eval a • x ∈ Z := by
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · have e : aeval T (p + r) x - (p + r).eval a • x =
        (aeval T p x - p.eval a • x) + (aeval T r x - r.eval a • x) := by
      rw [map_add (f := _), LinearMap.add_apply, eval_add, add_smul]; abel
    rw [e]; exact Z.add_mem hp hr
  · rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, eval_monomial, mul_smul,
      ← smul_sub]
    exact Z.smul_mem c (cr_pow_mod T Z hZ a x hx n)

theorem cr_aeval_eig (T : Module.End K V) (a : K) (x : V) (hx : T x = a • x) (q : K[X]) :
    aeval T q x = q.eval a • x := by
  have h := cr_aeval_mod T ⊥ (fun y hy => by
      rw [Submodule.mem_bot] at hy ⊢; rw [hy, map_zero]) a x
    (by rw [hx, sub_self]; exact Submodule.zero_mem _) q
  rw [Submodule.mem_bot, sub_eq_zero] at h
  exact h

theorem cr_aeval_stable (T : Module.End K V) (Z : Submodule K V) (hZ : ∀ x ∈ Z, T x ∈ Z) (x : V) (hx : x ∈ Z)
    (q : K[X]) : aeval T q x ∈ Z := by
  have h := cr_aeval_mod T Z hZ 0 x (by rw [zero_smul, sub_zero]; exact hZ x hx) q
  have h' := Z.add_mem h (Z.smul_mem (q.eval 0) hx)
  rwa [sub_add_cancel] at h'

theorem cr_aeval_comm (T X' : Module.End K V) (h : T * X' = X' * T) (q : K[X]) (x : V) :
    aeval T q (X' x) = X' (aeval T q x) := by
  have hc : Commute T X' := h
  refine Polynomial.induction_on' q (fun p r hp hr => ?_) (fun n c => ?_)
  · rw [map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, hp, hr, map_add (f := _)]
  · rw [aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, map_smul]
    congr 1
    exact LinearMap.congr_fun (hc.pow_left n).eq x

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.CrCCommApply
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def cr_C (E : GLOps n K V) : Module.End K V := ∑ a : Fin n, ∑ b : Fin n, E a b * E b a

theorem cr_C_comm (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) : cr_C E * E c d = E c d * cr_C E := by
  classical
  have key : ∀ a b, E a b * E b a * E c d - E c d * (E a b * E b a) =
      E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a := by
    intro a b
    rw [← hR b a c d, ← hR a b c d]; noncomm_ring
  have S1 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_ite]
  have S2 : ∑ a : Fin n, ∑ b : Fin n, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [mul_ite]
  have S3 : ∑ a : Fin n, ∑ b : Fin n, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [ite_mul]
  have S4 : ∑ a : Fin n, ∑ b : Fin n, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [ite_mul]
  rw [← sub_eq_zero, cr_C, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have : ∀ a : Fin n, (∑ b : Fin n, E a b * E b a) * E c d - E c d * ∑ b : Fin n, E a b * E b a =
      ∑ b : Fin n, (E a b * ((if a = c then E b d else 0) - (if d = b then E c a else 0)) +
        ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    intro a
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => key a b
  rw [Finset.sum_congr rfl fun a _ => this a]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4]
  abel

theorem cr_C_comm_apply (E : GLOps n K V) (hR : SatisfiesGLRelations E) (c d : Fin n) (x : V) :
    cr_C E (E c d x) = E c d (cr_C E x) := by
  have := congrArg (fun f : Module.End K V => f x) (cr_C_comm E hR c d)
  simpa using this

theorem cr_sym {M : Type*} [AddCommMonoid M] (F : Fin n → Fin n → M) :
    ∑ a, ∑ b, F a b = ∑ a, F a a + ∑ a, ∑ b, if a < b then F a b + F b a else 0 :=
  _root_.UpperTheory.Reformulated.B.DoubleSumDiagonalOffDiagonal.main F

theorem cr_C_wt (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x = ((cr_c mu : ℤ) : K) • x + (2 : K) • ∑ a : Fin n, ∑ b : Fin n, if a < b then E b a (E a b x) else 0 := by
  classical
  have hx' := (v2rep_mem_weightSp E mu x).1 hx
  have e0 : cr_C E x = ∑ a : Fin n, ∑ b : Fin n, E a b (E b a x) := by
    simp [cr_C, LinearMap.sum_apply]
  have e1 : ∀ a, E a a (E a a x) = ((mu a : K) ^ 2) • x := by
    intro a
    rw [hx' a, map_smul, hx' a, smul_smul, sq]
  have e2 : ∀ a b : Fin n, E a b (E b a x) + E b a (E a b x) =
      (2 : K) • E b a (E a b x) + ((mu a : K) - (mu b : K)) • x := by
    intro a b
    rw [v2rep_comm E hR a b b a x]
    simp only [if_true, hx' a, hx' b, sub_smul, two_smul]
    abel
  rw [e0, cr_sym, Finset.sum_congr rfl fun a _ => e1 a]
  have e3 : ∀ a b : Fin n, (if a < b then E a b (E b a x) + E b a (E a b x) else 0) =
      (2 : K) • (if a < b then E b a (E a b x) else 0) + (if a < b then ((mu a : K) - (mu b : K)) else 0) • x := by
    intro a b
    split_ifs
    · exact e2 a b
    · simp
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e3 a b]
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.sum_smul]
  have e4 : ((cr_c mu : ℤ) : K) = ∑ a, (mu a : K) ^ 2 + ∑ a : Fin n, ∑ b : Fin n,
      (if a < b then ((mu a : K) - (mu b : K)) else 0) := by
    simp only [cr_c, cr_h]
    push_cast
    rfl
  rw [e4, add_smul]
  abel

theorem cr_C_hwv (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) :
    cr_C E v = ((cr_c mu : ℤ) : K) • v := by
  rw [cr_C_wt E hR mu v hv.2.1]
  have : ∑ a : Fin n, ∑ b : Fin n, (if a < b then E b a (E a b v) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with h
    · rw [hv.2.2 a b h, map_zero]
    · rfl
  rw [this, smul_zero, add_zero]

theorem cr_C_stable (E : GLOps n K V) (W : Submodule K V) (hW : IsStableUnderOperators E W) (x : V) (hx : x ∈ W) :
    cr_C E x ∈ W := by
  simp only [cr_C, LinearMap.sum_apply, Module.End.mul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => hW a b _ (hW b a _ hx)

theorem cr_C_weightSp (E : GLOps n K V) (hR : SatisfiesGLRelations E) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) :
    cr_C E x ∈ weightSp E mu := by
  rw [v2rep_mem_weightSp] at hx ⊢
  intro a
  rw [← cr_C_comm_apply E hR, hx a, map_smul]

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedWeightLemmaOfReducibility
section
namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_weight_lemma_of_reducibility (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hV1 : ValuationsAdditive D) : ShaLengthVersionTwo D :=
  generated_weight_lemma_of_formulas D h2 hV1 dividedPower_formula_char_zero binomial_formula_char_zero

end Formalism.MainNotions.G.GLWeightTheory
end

