module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0025
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.SumFinsuppAntidiagEqSumPiFinset
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0022
public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.GeneratedModuleWeightLemmaPartB
section
noncomputable section

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem generated_module_weight_lemma_part_b : GeneratedModuleWeightDescription :=
  generated_module_weight_lemma_of_interfaces transvectionExpansion torus_acts_through_weight binomial_stable_contains_components twist_exponents_are_weight_entries generic_monomials_specialise

theorem valuationsAdditive_D7 (D : Formalism.BasicNotions.D7) : ValuationsAdditive D := valuations_additive_of_generated_weight_description D generated_module_weight_lemma_part_b

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.LoweringSpanLowerDividedPowerMem
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

inductive IsLoweringWord (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) : (Fin n → ℤ) → V → Prop
  | base : IsLoweringWord E lam v lam v
  | step (c d : Fin n) (h : d < c) (l : ℕ) (hl : 1 ≤ l) (nu : Fin n → ℤ) (x : V) :
      IsLoweringWord E lam v nu x → IsLoweringWord E lam v (nu + (l : ℤ) • rootW c d) (divPowE E c d l x)

theorem weight_height_add_root_smul (nu : Fin n → ℤ) (a b : Fin n) (l : ℕ) :
    weightHeightAscending (nu + (l : ℤ) • rootW a b) = weightHeightAscending nu + l * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have e : nu + ((l + 1 : ℕ) : ℤ) • rootW a b = nu + (l : ℤ) • rootW a b + rootW a b := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [e, weightHeightAscending_add_root, ih]; push_cast; ring

theorem dividedPower_mem_shifted_weight {E : GLOps n (KK O) V} (hE : IsGLRep E) {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu)
    (a c : Fin n) (j : ℕ) : divPowE E a c j x ∈ weightSp E (nu + (j : ℤ) • rootW a c) := by
  rw [divPowE, LinearMap.smul_apply]
  exact Submodule.smul_mem _ _ (integral_operator_pow_shifts_weight hE hx a c j)

theorem loweringWord_mem_weightSpace {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V} (hv : v ∈ weightSp E lam)
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : x ∈ weightSp E nu := by
  induction h with
  | base => exact hv
  | step c d _ l _ nu x _ ih => exact dividedPower_mem_shifted_weight hE ih c d l

theorem loweringWord_height_ge_highest {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V}
    {nu : Fin n → ℤ} {x : V} (h : IsLoweringWord E lam v nu x) : weightHeightAscending lam ≤ weightHeightAscending nu := by
  induction h with
  | base => exact le_refl _
  | step c d hdc l _ nu x _ ih =>
    rw [weight_height_add_root_smul]
    have h1 : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hdc
    have : (0 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) := mul_nonneg (by positivity) (by omega)
    omega

def loweringSpanOfHeight (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) (N : ℤ) : Submodule O V :=
  Submodule.span O {x | ∃ nu, IsLoweringWord E lam v nu x ∧ weightHeightAscending nu ≤ weightHeightAscending lam + N}

theorem loweringSpan_height_monotone (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) {N N' : ℤ} (h : N ≤ N') :
    loweringSpanOfHeight (O := O) E lam v N ≤ loweringSpanOfHeight (O := O) E lam v N' := by
  refine Submodule.span_mono ?_
  rintro x ⟨nu, h1, h2⟩
  exact ⟨nu, h1, by omega⟩

theorem loweringSpan_map_le_of_words {E : GLOps n (KK O) V} {lam : Fin n → ℤ} {v : V} {N : ℤ} {L : Submodule O V}
    (T : Module.End (KK O) V)
    (h : ∀ nu x, IsLoweringWord E lam v nu x → weightHeightAscending nu ≤ weightHeightAscending lam + N → T x ∈ L) :
    ∀ y ∈ loweringSpanOfHeight (O := O) E lam v N, T y ∈ L := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy => obtain ⟨nu, h1, h2⟩ := hy; exact h nu y h1 h2
  | zero => simp
  | add y z _ _ hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [← algebraMap_smul (KK O) r y, map_smul, algebraMap_smul]; exact Submodule.smul_mem _ _ hy

theorem loweringSpan_lower_dividedPower_mem (E : GLOps n (KK O) V) (lam : Fin n → ℤ) (v : V) {c d : Fin n} (hdc : d < c) (i : ℕ) (M : ℤ) :
    ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
      divPowE E c d i y ∈ loweringSpanOfHeight (O := O) E lam v (M + i * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))) := by
  refine loweringSpan_map_le_of_words _ fun nu x h1 h2 => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have : divPowE E c d 0 x = x := by simp [divPowE]
    rw [this]
    exact Submodule.subset_span ⟨nu, h1, by simpa using h2⟩
  · exact Submodule.subset_span ⟨_, IsLoweringWord.step c d hdc i hi nu x h1, by rw [weight_height_add_root_smul]; omega⟩

theorem dividedPower_eq_divPowE (E : GLOps n (KK O) V) (a b : Fin n) (k : ℕ) : dividedPower (KK O) (E a b) k = divPowE E a b k := rfl

theorem dividedPower_neg_sign (X : Module.End (KK O) V) (j : ℕ) :
    dividedPower (KK O) (-X) j = (((-1 : ℤ) ^ j : ℤ) : KK O) • dividedPower (KK O) X j := by
  rw [dividedPower, dividedPower, neg_pow, smul_smul]
  push_cast
  rw [mul_comm, ← smul_smul]
  congr 1
  rcases Nat.even_or_odd j with h | h <;> simp [h.neg_one_pow]

theorem raising_dividedPower_loweringSpan [CharZero (KK O)] {E : GLOps n (KK O) V} (hE : IsGLRep E) {lam : Fin n → ℤ} {v : V}
    (hv : IsHWV E lam v) (N : ℕ) : ∀ nu x, IsLoweringWord E lam v nu x → weightHeightAscending nu ≤ weightHeightAscending lam + N →
      ∀ a b : Fin n, a < b → ∀ k : ℕ, divPowE E a b k x ∈ loweringSpanOfHeight (O := O) E lam v N := by
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro nu x hLW hht a b hab k
  cases hLW with
  | base =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : divPowE E a b 0 v = v := by simp [divPowE]
      rw [this]
      exact Submodule.subset_span ⟨lam, IsLoweringWord.base, by omega⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have : divPowE E a b (k' + 1) v = 0 := by
        rw [divPowE, LinearMap.smul_apply, pow_succ, Module.End.mul_apply, hv.2.2 a b hab, map_zero, smul_zero]
      rw [this]; exact Submodule.zero_mem _
  | step c d hdc l hl nu' x' hLW' =>
    have hgap : (1 : ℤ) ≤ ((c : ℕ) : ℤ) - ((d : ℕ) : ℤ) := by
      have : ((d : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast hdc
      omega
    have hab' : ((a : ℕ) : ℤ) < ((b : ℕ) : ℤ) := by exact_mod_cast hab
    rw [weight_height_add_root_smul] at hht
    have hlow := loweringWord_height_ge_highest hLW'
    have hlg : (1 : ℤ) ≤ (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) := by
      have h1 : (1 : ℤ) ≤ (l : ℤ) := by exact_mod_cast hl
      nlinarith
    obtain ⟨M, hM⟩ : ∃ M : ℕ, (M : ℤ) = N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)) :=
      ⟨(N - (l : ℤ) * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ))).toNat, by omega⟩
    have hMN : M < N := by omega
    have hx'M : weightHeightAscending nu' ≤ weightHeightAscending lam + M := by omega
    have IHM := IH M hMN
    have RL : ∀ a' b' : Fin n, a' < b' → ∀ k' : ℕ, ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
        divPowE E a' b' k' y ∈ loweringSpanOfHeight (O := O) E lam v M := fun a' b' h' k' =>
      loweringSpan_map_le_of_words _ fun nu2 x2 h1 h2 => IHM nu2 x2 h1 h2 a' b' h' k'
    have hx'w := loweringWord_mem_weightSpace hE hv.2.1 hLW'
    by_cases hcase : c = b ∧ d = a
    · obtain ⟨rfl, rfl⟩ := hcase
      rw [raise_lower_dividedPower_binomial hE (ne_of_lt hab) hx'w k l]
      refine Submodule.sum_mem _ fun j _ => ?_
      split_ifs with hj
      · refine intCast_smul_mem_submodule _ _ ?_
        refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) M _ (IHM nu' x' hLW' hx'M d c hab (k - j)))
        have : ((l - j : ℕ) : ℤ) ≤ (l : ℤ) := by exact_mod_cast Nat.sub_le l j
        nlinarith
      · exact Submodule.zero_mem _
    ·
      have key : ∀ Z : Module.End (KK O) V, E a b * E c d = E c d * E a b + Z → Z * E c d = E c d * Z →
          E a b * Z = Z * E a b →
          (∀ j : ℕ, ∀ y ∈ loweringSpanOfHeight (O := O) E lam v M,
            dividedPower (KK O) Z j y ∈ loweringSpanOfHeight (O := O) E lam v (M + j * (((c : ℕ) : ℤ) - ((d : ℕ) : ℤ)))) →
          divPowE E a b k (divPowE E c d l x') ∈ loweringSpanOfHeight (O := O) E lam v N := by
        intro Z h1 h2 h3 h4
        have e := heisenberg_dividedPower_expansion (K := KK O) h1 h2 h3 k l
        have e2 : divPowE E a b k (divPowE E c d l x') =
            (dividedPower (KK O) (E a b) k * dividedPower (KK O) (E c d) l) x' := rfl
        rw [e2, e, LinearMap.sum_apply]
        refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs with hj
        · rw [Module.End.mul_apply, Module.End.mul_apply]
          have s1 := IHM nu' x' hLW' hx'M a b hab (k - j)
          have s2 := h4 j _ s1
          have s3 := loweringSpan_lower_dividedPower_mem E lam v hdc (l - j) _ _ s2
          refine loweringSpan_height_monotone E lam v ?_ s3
          push_cast [Nat.cast_sub hj]
          rw [hM]; ring_nf; exact le_refl _
        · simp
      have hr := hE.1 a b c d
      by_cases hbc : b = c
      · have hda : d ≠ a := fun e => hcase ⟨hbc.symm, e⟩
        subst hbc
        refine key (E a d) ?_ ?_ ?_ ?_
        · rw [if_pos rfl, if_neg hda, sub_zero] at hr
          rw [← hr]; abel
        · have := hE.1 a d b d
          rw [if_neg (ne_of_lt hdc), if_neg hda, sub_zero] at this
          exact sub_eq_zero.1 this
        · have := hE.1 a b a d
          rw [if_neg (ne_of_gt hab), if_neg hda, sub_zero] at this
          exact sub_eq_zero.1 this
        · intro j y hy
          rw [dividedPower_eq_divPowE]
          rcases lt_or_gt_of_ne hda with h | h
          · have hh : ((d : ℕ) : ℤ) < ((a : ℕ) : ℤ) := by exact_mod_cast h
            refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)
            have : (0 : ℤ) ≤ (j : ℤ) := by positivity
            nlinarith
          · refine loweringSpan_height_monotone E lam v ?_ (RL a d h j y hy)
            have : (0 : ℤ) ≤ (j : ℤ) := by positivity
            nlinarith
      · by_cases hda : d = a
        · subst hda
          refine key (-E c b) ?_ ?_ ?_ ?_
          · rw [if_neg hbc, if_pos rfl, zero_sub] at hr
            rw [← hr]; abel
          · have := hE.1 c b c d
            rw [if_neg hbc, if_neg (ne_of_lt hdc), sub_zero] at this
            rw [neg_mul, mul_neg, sub_eq_zero.1 this]
          · have := hE.1 d b c b
            rw [if_neg hbc, if_neg (ne_of_gt hab), sub_zero] at this
            rw [neg_mul, mul_neg, sub_eq_zero.1 this]
          · intro j y hy
            rw [dividedPower_neg_sign, LinearMap.smul_apply, dividedPower_eq_divPowE]
            refine intCast_smul_mem_submodule _ _ ?_
            rcases lt_or_gt_of_ne hbc with h | h
            · have hh : ((b : ℕ) : ℤ) < ((c : ℕ) : ℤ) := by exact_mod_cast h
              refine loweringSpan_height_monotone E lam v ?_ (loweringSpan_lower_dividedPower_mem E lam v h j M y hy)
              have : (0 : ℤ) ≤ (j : ℤ) := by positivity
              nlinarith
            · refine loweringSpan_height_monotone E lam v ?_ (RL c b h j y hy)
              have : (0 : ℤ) ≤ (j : ℤ) := by positivity
              nlinarith
        · refine key 0 ?_ (by simp) (by simp) ?_
          · rw [if_neg hbc, if_neg hda, sub_zero] at hr
            rw [add_zero]; exact sub_eq_zero.1 hr
          · intro j y hy
            rcases Nat.eq_zero_or_pos j with rfl | hj
            · simpa [dividedPower] using hy
            · have : dividedPower (KK O) (0 : Module.End (KK O) V) j = 0 := by
                rw [dividedPower, zero_pow (by omega), smul_zero]
              rw [this]; exact Submodule.zero_mem _

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightMemWeightsOfNeZero
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section hw

variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

theorem weight_mem_weights_of_ne_zero {E : GLOps n (KK O) V} {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) :
    nu ∈ wtsOf E ⊤ := by
  show weightSp E nu ⊓ ⊤ ≠ ⊥
  rw [inf_top_eq]
  intro hb
  rw [hb] at hx
  exact h0 ((Submodule.mem_bot _).mp hx)

theorem weight_difference_le_ell [CharZero (KK O)] [FiniteDimensional (KK O) V] {E : GLOps n (KK O) V} (hE : IsGLRep E)
    {nu : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E nu) (h0 : x ≠ 0) (a c : Fin n) :
    nu a - nu c ≤ (ellOf E ⊤ : ℤ) := by
  by_cases hac : a = c
  · subst hac
    simp
  by_cases hpos : 0 < nu a - nu c
  · have hne : weightSp E nu ≠ ⊥ := by
      intro hb
      rw [hb] at hx
      exact h0 ((Submodule.mem_bot _).mp hx)
    obtain ⟨j, hy0, hytop⟩ := offdiag_string_reaches_top_nonzero hE hx h0 hac
    have hyw := integral_operator_pow_shifts_weight hE hx a c j
    generalize ((E a c) ^ j) x = y at hy0 hytop hyw
    have hmu : (nu + (j : ℤ) • rootW a c) a - (nu + (j : ℤ) • rootW a c) c = nu a - nu c + 2 * j := by
      simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.single_apply, hac,
        Ne.symm hac, if_true, if_false]
      ring
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = nu a - nu c + 2 * j :=
      ⟨(nu a - nu c + 2 * j).toNat, Int.toNat_of_nonneg (by omega)⟩
    have hcomm : ∀ w : V, E a c (E c a w) = E c a (E a c w) + (E a a w - E c c w) := by
      intro w
      have h1 := hE.1 a c c a
      rw [if_pos rfl, if_pos rfl] at h1
      have h2 := LinearMap.congr_fun h1 w
      first
        | simp only [LinearMap.sub_apply, Module.End.mul_apply] at h2
        | simp only [LinearMap.sub_apply, LinearMap.mul_apply] at h2
      rw [← h2]
      abel
    have hps : ∀ (r : ℕ) (w : V), E c a (((E c a) ^ r) w) = ((E c a) ^ (r + 1)) w := by
      intro r w
      rw [pow_succ']
      rfl
    have hwt : ∀ r : ℕ, E a a (((E c a) ^ r) y) - E c c (((E c a) ^ r) y) =
        (((N : ℤ) - 2 * (r : ℤ) : ℤ) : KK O) • ((E c a) ^ r) y := by
      intro r
      have hm := integral_operator_pow_shifts_weight hE hyw c a r
      simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply] at hm
      have ha := sub_eq_zero.mp (hm a)
      have hc' := sub_eq_zero.mp (hm c)
      simp only [Module.End.one_apply] at ha hc'
      rw [ha, hc', ← sub_smul]
      congr 1
      have hω : (nu + (j : ℤ) • rootW a c + (r : ℤ) • rootW c a) a -
          (nu + (j : ℤ) • rootW a c + (r : ℤ) • rootW c a) c = (N : ℤ) - 2 * (r : ℤ) := by
        simp [rootW, Pi.single_apply, hac, Ne.symm hac]
        omega
      rw [← hω]
      push_cast
      ring
    have hkey : ∀ r : ℕ, E a c (((E c a) ^ (r + 1)) y) =
        ((((r + 1 : ℕ) : KK O) * ((N : KK O) - r))) • ((E c a) ^ r) y := by
      intro r
      induction r with
      | zero =>
        have h0' := hwt 0
        have e1 : ((E c a) ^ (0 + 1)) y = E c a y := by rw [zero_add, pow_one]
        rw [e1, hcomm, hytop, map_zero, zero_add]
        simp only [pow_zero, Module.End.one_apply] at h0' ⊢
        rw [h0']
        congr 1
        push_cast
        ring
      | succ r ih =>
        rw [← hps (r + 1) y, hcomm, ih, map_smul, hps, hwt (r + 1), ← add_smul]
        congr 1
        push_cast
        ring
    have hz : ∀ r : ℕ, r ≤ N → ((E c a) ^ r) y ≠ 0 := by
      intro r
      induction r with
      | zero => intro _; simpa using hy0
      | succ r ih =>
        intro hr hz0
        have hk := hkey r
        rw [hz0, map_zero] at hk
        have hc : (((r + 1 : ℕ) : KK O) * ((N : KK O) - r)) ≠ 0 := by
          refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero r) ?_
          have e : ((N : KK O) - r) = ((N - r : ℤ) : KK O) := by push_cast; ring
          rw [e]
          exact_mod_cast (show (N - r : ℤ) ≠ 0 by omega)
        exact ih (by omega) ((smul_eq_zero.mp hk.symm).resolve_left hc)
    have hzN := hz N le_rfl
    have hzw := integral_operator_pow_shifts_weight hE hyw c a N
    have hmem : N ∈ {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule (KK O) V), ∃ nu ∈ wtsOf E (⊤ : Submodule (KK O) V),
        ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
      refine ⟨nu + (j : ℤ) • rootW a c, weight_mem_weights_of_ne_zero hyw hy0,
        nu + (j : ℤ) • rootW a c + (N : ℤ) • rootW c a, weight_mem_weights_of_ne_zero hzw hzN, a, c, hac, ?_⟩
      funext i
      simp only [rootW, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hle : N ≤ ellOf E ⊤ := by
      unfold ellOf
      exact le_csSup (root_differences_bddAbove E hE ⊤) hmem
    have hle' : (N : ℤ) ≤ (ellOf E ⊤ : ℤ) := by exact_mod_cast hle
    omega
  · push_neg at hpos
    have : (0 : ℤ) ≤ (ellOf E ⊤ : ℤ) := Nat.cast_nonneg _
    omega

theorem linf_homRep_le_ell_add [NeZero n] [CharZero (KK O)] [FiniteDimensional (KK O) V] (E : GLOps n (KK O) V)
    (hE : IsGLRep E) (lam : Fin n → ℤ) (hdom : Dominant lam) (v0 : V) (hv0 : IsHWV E lam v0)
    (hL : IsSubrepresentation E (cyclicSubmodule E v0)) :
    linf (homRepresentation (restrictRepresentation E _ hL) E) ⊤ ≤ ellOf E ⊤ + ellWt lam := by
  refine csSup_le' ?_
  rintro k ⟨ka, hk, hsum, a, rfl⟩
  have hres := restrictRepresentation_isRep E hE _ hL
  have hne : weightSp (homRepresentation (restrictRepresentation E _ hL) E) ka ≠ ⊥ := by
    intro h0; apply hk; rw [h0, bot_inf_eq]
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hex : ∃ nu, ∃ x ∈ weightSp (restrictRepresentation E _ hL) nu, g x ≠ 0 := by
    by_contra hc
    apply hg0
    refine linearMap_ext_on_weightSpaces _ hres g 0 fun nu x hx => ?_
    by_contra h1
    exact hc ⟨nu, x, hx, h1⟩
  obtain ⟨nu, x, hx, hgx⟩ := hex
  have hx0 : x ≠ 0 := by
    intro h0
    apply hgx
    rw [h0, map_zero]
  have hgw : g x ∈ weightSp E (ka + nu) := by
    rw [mem_weightSp_iff_diagonal_apply]
    intro c
    have h1 := congrArg (fun f : cyclicSubmodule E v0 →ₗ[KK O] V => f x) ((mem_weightSp_iff_diagonal_apply _ _ g).1 hg c)
    simp only [homRepresentation_apply, LinearMap.smul_apply] at h1
    have h2 : restrictRepresentation E _ hL c c x = (nu c : KK O) • x := (mem_weightSp_iff_diagonal_apply _ _ x).1 hx c
    rw [h2, map_smul, sub_eq_iff_eq_add] at h1
    rw [h1, Pi.add_apply, Int.cast_add, add_smul]
  have hI : IsIrrHW (restrictRepresentation E _ hL) lam (⟨v0, self_mem_cyclicSubmodule E v0⟩ : cyclicSubmodule E v0) :=
    ⟨hres, hdom, highest_vector_restrict E _ hL lam v0 (self_mem_cyclicSubmodule E v0) hv0, cyclicSubmodule_restrict_eq_top E v0 hL⟩
  have hent := fun c => weight_entries_between_extreme_highest hI hx hx0 c
  have hdif := fun c c' => weight_difference_le_ell hE hgw hgx c c'

  have hc1 : ∃ c, ka c ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have : 0 < ∑ c, ka c := Finset.sum_pos (fun c _ => hcon c) ⟨0, Finset.mem_univ _⟩
    omega
  have hc2 : ∃ c, 0 ≤ ka c := by
    by_contra hcon
    push Not at hcon
    have : ∑ c, ka c < 0 := Finset.sum_neg (fun c _ => hcon c) ⟨0, Finset.mem_univ _⟩
    omega
  obtain ⟨c1, hc1⟩ := hc1
  obtain ⟨c2, hc2⟩ := hc2
  have e1 := hdif a c1
  have e2 := hdif c2 a
  have e3 := hent a
  have e4 := hent c1
  have e5 := hent c2
  simp only [Pi.add_apply] at e1 e2
  unfold ellWt
  omega

end hw

end Formalism.MainNotions.G.GLWeightTheory
end
end

