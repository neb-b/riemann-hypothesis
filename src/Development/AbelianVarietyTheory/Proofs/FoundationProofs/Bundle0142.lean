module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SquarefreeLabelTorusMassRootsNotDistinctLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisCoboundaryCongZeroModPrimePow
section
open GlobalTheory.K5

namespace GlobalTheory.K5.KernLoc

theorem kern_of (SPAN : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) (ORTH : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (c : ℕ → Ω), (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) →
  IsInt (p := p) (∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j) → ∀ j < p ^ N, IsInt (p := p) (c j)) : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 := by
  intro p _ _ Ω _ _ hΩ T τ hτ hτq k N w o hw hwH ho hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap hΩ.inj
  have hp0 : (p : Ω) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero

  have hζalg : IsAlgZp p (T.ζ N) := by
    refine ⟨Polynomial.X ^ (p ^ N) - 1, Polynomial.X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos N) 1, ?_⟩
    simp [(T.prim N).pow_eq_one]
  have hfixζ : ∀ g ∈ Ggeo p Ω, g (T.ζ N) = T.ζ N := fun g hg => hg (T.ζ N) hζalg
  have hτpow : ∀ i : ℕ, (τ ^ i) (T.qq N) = T.ζ N ^ i * T.qq N := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, AlgEquiv.mul_apply, hτq, map_mul, ih, hfixζ _ (Subgroup.pow_mem _ hτ i)]
      ring
  have hτi : ∀ i : ℕ, τ ^ i ∈ Ggeo p Ω := fun i => Subgroup.pow_mem _ hτ i

  have hτN : (τ ^ (p ^ N)) w = w := by
    apply hwH
    refine ⟨hτi _, ?_⟩
    show (τ ^ (p ^ N)) (T.qq N) = T.qq N
    rw [hτpow, (T.prim N).pow_eq_one, one_mul]

  obtain ⟨z, hz, hze⟩ := hc
  have hzH : ∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z := by
    intro g hg
    have hg1 : g ∈ Ggeo p Ω := hg.1
    have hg2 : g (T.qq N) = T.qq N := hg.2
    have hconj : τ⁻¹ * g * τ ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N) := by
      refine ⟨(Ggeo p Ω).mul_mem ((Ggeo p Ω).mul_mem ((Ggeo p Ω).inv_mem hτ) hg1) hτ, ?_⟩
      show (τ⁻¹ * g * τ) (T.qq N) = T.qq N
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hτq, map_mul, hfixζ g hg1, hg2, ← hτq,
        ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    have hgτw : g (τ w) = τ w := by
      have := hwH _ hconj
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
      have h2 := congrArg τ this
      rwa [← AlgEquiv.mul_apply τ τ⁻¹, mul_inv_cancel, AlgEquiv.one_apply] at h2
    have e := congrArg g hze
    rw [map_sub, map_sub, hgτw, hwH g hg, ho g hg1, map_mul, map_pow, map_natCast, hze] at e
    exact (mul_left_cancel₀ (pow_ne_zero k hp0) e).symm
  obtain ⟨c, hcfix, hzc⟩ := SPAN p Ω hΩ T τ hτ hτq N z hzH

  have hsumz : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) z = (p : Ω) ^ N * c 0 := by
    have h1 : ∀ i j : ℕ, (τ ^ i) (c j * T.qq N ^ j) = c j * T.qq N ^ j * (T.ζ N ^ j) ^ i := by
      intro i j
      rw [map_mul, map_pow, hcfix j _ (hτi i), hτpow]
      ring
    rw [hzc]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [map_sum, h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single 0]
    · simp [mul_comm]
    · intro j hj hj0
      have hj' := Finset.mem_range.1 hj
      have hne : T.ζ N ^ j ≠ 1 := (T.prim N).pow_ne_one_of_pos_of_lt hj0 hj'
      rw [geom_sum_eq hne, ← pow_mul, mul_comm j, pow_mul, (T.prim N).pow_eq_one, one_pow, sub_self,
        zero_div, mul_zero]
    · intro h
      exact absurd (Finset.mem_range.2 (pow_pos (Fact.out : p.Prime).pos N)) h
  have hsumL : ∑ i ∈ Finset.range (p ^ N), (τ ^ i) (τ w - w - o) = -((p : Ω) ^ N * o) := by
    have h1 : ∀ i : ℕ, (τ ^ i) (τ w - w - o) = (τ ^ (i + 1)) w - (τ ^ i) w - o := by
      intro i
      rw [map_sub, map_sub, pow_succ, AlgEquiv.mul_apply, ho _ (hτi i)]
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_range_sub (fun i => (τ ^ i) w), hτN, pow_zero,
      AlgEquiv.one_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  have key : -((p : Ω) ^ N * o) = (p : Ω) ^ k * ((p : Ω) ^ N * c 0) := by
    rw [← hsumL, ← hsumz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hze, map_mul, map_pow, map_natCast]
  have hc0 : IsInt (p := p) (c 0) := ORTH p Ω hΩ T N c hcfix (hzc ▸ hz) 0 (pow_pos (Fact.out : p.Prime).pos N)
  refine ⟨-c 0, hc0.neg, ?_⟩
  have hpN : (p : Ω) ^ N ≠ 0 := pow_ne_zero N hp0
  apply mul_left_cancel₀ hpN
  linear_combination -key

theorem main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (k N : ℕ) (w o : Ω), IsInt (p := p) w → (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g w = w) →
  (∀ g ∈ Ggeo p Ω, g o = o) → Cong (p := p) k (τ w - w) o → Cong (p := p) k o 0 :=
  kern_of GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau GlobalTheory.T.isIntegral_coeffs_of_geometricInvariant_towerParameter_expansion

end GlobalTheory.K5.KernLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodSquarefreeLabelTuplesWeightGe
section
noncomputable section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

variable (g : ℕ) [Fact g.Prime]

def tupleMass {ι : Type} [Fintype ι] (N : ℕ) (P : (ι → (ZMod g)[X]) → Prop) : ℝ :=
  ∑ F ∈ Fintype.piFinset fun _ : ι => sqSet g N, if P F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0

variable {g} {ι : Type} [Fintype ι] {N : ℕ}

theorem tupleWeight_nonneg (F : ι → (ZMod g)[X]) : 0 ≤ ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  exact Finset.prod_nonneg fun v _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem tupleMass_le_add {P Q R : (ι → (ZMod g)[X]) → Prop}
    (h : ∀ F, (∀ v, F v ∈ sqSet g N) → P F → Q F ∨ R F) :
    tupleMass g N P ≤ tupleMass g N Q + tupleMass g N R := by
  unfold tupleMass
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun F hF => ?_
  have hw := tupleWeight_nonneg F
  have hmem : ∀ v, F v ∈ sqSet g N := fun v => Fintype.mem_piFinset.mp hF v
  by_cases hP : P F
  · rw [if_pos hP]
    rcases h F hmem hP with hQ | hR
    · rw [if_pos hQ]; split_ifs <;> linarith
    · rw [if_pos hR]; split_ifs <;> linarith
  · rw [if_neg hP]; split_ifs <;> linarith

theorem tupleMass_exists_le {κ : Type} (s : Finset κ) (Q : κ → (ι → (ZMod g)[X]) → Prop) :
    tupleMass g N (fun F => ∃ i ∈ s, Q i F) ≤ ∑ i ∈ s, tupleMass g N (Q i) := by
  unfold tupleMass
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun F _ => ?_
  have hz : ∀ j ∈ s, 0 ≤ (if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := fun j _ => by
    split_ifs
    · exact tupleWeight_nonneg F
    · exact le_rfl
  split_ifs with h
  · obtain ⟨i, hi, hQ⟩ := h
    calc ∏ v, ((torusCard g (F v) : ℝ))⁻¹ = (if Q i F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) := by rw [if_pos hQ]
      _ ≤ ∑ j ∈ s, if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0 :=
        Finset.single_le_sum (f := fun j => if Q j F then ∏ v, ((torusCard g (F v) : ℝ))⁻¹ else 0) hz hi
  · exact Finset.sum_nonneg hz

theorem tupleMass_forall (A : ι → (ZMod g)[X] → Prop) :
    tupleMass g N (fun F => ∀ v, A v (F v)) = ∏ v, mass g N (A v) := by
  unfold tupleMass mass
  simp_rw [Finset.sum_filter]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  split_ifs with h
  · exact Finset.prod_congr rfl fun v _ => (if_pos (h v)).symm
  · push Not at h
    obtain ⟨v, hv⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)).symm

theorem tupleMass_single_le (h1 : (mass g N fun _ => True) ≤ 1) (v : ι) (A : (ZMod g)[X] → Prop) :
    tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) ≤ mass g N A := by
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have key : tupleMass g N (fun F : ι → (ZMod g)[X] => A (F v)) =
      tupleMass g N (fun F => ∀ w, (if w = v then A else fun _ => True) (F w)) := by
    unfold tupleMass
    refine Finset.sum_congr rfl fun F _ => ?_
    have hiff : A (F v) ↔ ∀ w, (if w = v then A else fun _ => True) (F w) :=
      ⟨fun h w => by by_cases hw : w = v <;> simp_all, fun h => by simpa using h v⟩
    by_cases h : A (F v)
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (mt hiff.mpr h)]
  rw [key, tupleMass_forall, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v), if_pos rfl]
  have hrest : ∏ w ∈ Finset.univ.erase v, mass g N (if w = v then A else fun _ => True) ≤ 1 := by
    apply Finset.prod_le_one₀
    · exact fun w _ => hm _
    · intro w hw
      rw [if_neg (Finset.ne_of_mem_erase hw)]
      exact h1
  calc mass g N A * _ ≤ mass g N A * 1 := mul_le_mul_of_nonneg_left hrest (hm A)
    _ = _ := mul_one _

theorem goodSet_weight_ge : ∀ (g : ℕ) [Fact g.Prime], ∀ (N m q d : ℕ) (ι : Type) [Fintype ι] (ch : ι → Fin m → (ZMod g)ˣ), 100000 ≤ N → 2 ^ 12 ≤ g → (q.Prime ∧ d.Prime ∧ q ≠ 2 ∧ d ≠ 2 ∧ q ≠ d ∧ 16 ≤ max q d ∧ 16 * q * d ∣ g - 1) → 1 - (badBound g (Fintype.card ι) m N ((min q d : ℕ) : ℝ) - (Fintype.card ι : ℝ) / g) ≤ ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
  intro g _ N m q d ι _ ch hN hg hqd
  have hm : ∀ B : (ZMod g)[X] → Prop, 0 ≤ mass g N B := fun B => by
    unfold mass
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)
  have h1 : (mass g N fun _ => True) ≤ 1 := (_root_.GlobalTheory.BadShare.divisor_bound g).1 N
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  have hg4 : (4096 : ℝ) ≤ g := by exact_mod_cast hg
  have hN' : (100000 : ℝ) ≤ N := by exact_mod_cast hN
  have hall : 1 - 2 * (Fintype.card ι : ℝ) / g ≤ tupleMass g N (fun _ : ι → (ZMod g)[X] => True) := by
    have e := tupleMass_forall (g := g) (N := N) (fun (_ : ι) (_ : (ZMod g)[X]) => True)
    simp only [implies_true] at e
    rw [e]
    have h2 : 0 ≤ 1 - 2 / (g : ℝ) := by
      rw [sub_nonneg, div_le_one hg0]; linarith
    have h3 : (-2 : ℝ) ≤ -2 / g := by
      rw [le_div_iff₀ hg0]; nlinarith
    calc 1 - 2 * (Fintype.card ι : ℝ) / g = 1 + (Fintype.card ι : ℝ) * (-2 / g) := by ring
      _ ≤ (1 + (-2 / (g : ℝ))) ^ Fintype.card ι := one_add_mul_le_pow h3 _
      _ = ∏ _v : ι, (1 - 2 / (g : ℝ)) := by rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ ∏ _v : ι, mass g N (fun _ => True) :=
        Finset.prod_le_prod₀ (fun _ _ => h2) (fun _ _ => _root_.GlobalTheory.BadShare.one_sub_two_div_le_mass_true g N)
  have hsq : ∀ f ∈ sqSet g N, (f.Monic ∧ f.natDegree = N ∧ f.coeff 0 ≠ 0) ∧ Squarefree f := by
    intro f hf
    unfold sqSet at hf
    rw [Finset.mem_filter, Finset.mem_image] at hf
    obtain ⟨⟨c, -, rfl⟩, hsf, hc0⟩ := hf
    have hdeg := degree_sum_fin_lt c
    refine ⟨⟨monic_X_pow_add hdeg, ?_, hc0⟩, hsf⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have hE1 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ≤
      (Fintype.card ι : ℝ) * (23 * Real.log g / Real.sqrt g) := by
    calc _ ≤ ∑ v ∈ Finset.univ, tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsApart g N (F v)) :=
          tupleMass_exists_le (Finset.univ : Finset ι) (fun (v : ι) (F : ι → (ZMod g)[X]) => ¬ RootsApart g N (F v))
      _ ≤ ∑ _v ∈ (Finset.univ : Finset ι), (23 * Real.log g / Real.sqrt g) :=
          Finset.sum_le_sum fun v _ => (tupleMass_single_le h1 v _).trans (_root_.GlobalTheory.BadShare.mass_not_rootsApart_le g N hg)
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hE2 : ∀ c : ι → Fin m → (ZMod g)ˣ,
      tupleMass g N (fun F : ι → (ZMod g)[X] =>
        ∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (c p.1 p.2) (F p.1)) ≤
      (Fintype.card ι : ℝ) * m * (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) := by
    intro c
    calc _ ≤ ∑ p ∈ (Finset.univ : Finset (ι × Fin m)),
            tupleMass g N (fun F : ι → (ZMod g)[X] => ¬ RootsAvoid g (c p.1 p.2) (F p.1)) :=
          tupleMass_exists_le (Finset.univ : Finset (ι × Fin m))
            (fun (p : ι × Fin m) (F : ι → (ZMod g)[X]) => ¬ RootsAvoid g (c p.1 p.2) (F p.1))
      _ ≤ ∑ _p ∈ (Finset.univ : Finset (ι × Fin m)),
            (1 / (4 * ((min q d : ℕ) : ℝ)) + (1 + Real.log N) / ((g : ℝ) - 1)) :=
          Finset.sum_le_sum fun p _ => (tupleMass_single_le h1 p.1 _).trans (_root_.GlobalTheory.BadShare.mass_not_rootsAvoid_le g N q d _ hqd)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have hE4 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ≤
      (N : ℝ) / 2 * (7 / 8) ^ Fintype.card ι := by
    calc _ ≤ ∑ a ∈ Finset.Icc 1 (N / 2), tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, HasDiv g a (F v)) :=
          tupleMass_exists_le (Finset.Icc 1 (N / 2)) (fun (a : ℕ) (F : ι → (ZMod g)[X]) => ∀ v, HasDiv g a (F v))
      _ = ∑ a ∈ Finset.Icc 1 (N / 2), ∏ _v : ι, mass g N (HasDiv g a) :=
          Finset.sum_congr rfl fun a _ => tupleMass_forall (fun _ => HasDiv g a)
      _ ≤ ∑ _a ∈ Finset.Icc 1 (N / 2), ((7 : ℝ) / 8) ^ Fintype.card ι := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [Finset.mem_Icc] at ha
          calc ∏ _v : ι, mass g N (HasDiv g a) ≤ ∏ _v : ι, ((7 : ℝ) / 8) :=
                Finset.prod_le_prod₀ (fun _ _ => hm _) (fun _ _ => _root_.GlobalTheory.BadShare.mass_hasDiv_le g N a (by omega) (by omega))
            _ = _ := by rw [Finset.prod_const, Finset.card_univ]
      _ = ((N / 2 : ℕ) : ℝ) * (7 / 8) ^ Fintype.card ι := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right Nat.cast_div_le (by positivity)
  have hL : (1 : ℝ) ≤ 10 * Real.log N := by
    have : (1 : ℝ) ≤ Real.log N :=
      calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
        _ ≤ Real.log N := Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hE5 : tupleMass g N (fun F : ι → (ZMod g)[X] => ∀ v, ¬ HasPrimeFactor g N (F v)) ≤
      Real.exp (-((Fintype.card ι : ℝ) / (10 * Real.log N))) := by
    calc _ = ∏ _v : ι, mass g N (fun f => ¬ HasPrimeFactor g N f) :=
          tupleMass_forall (fun _ f => ¬ HasPrimeFactor g N f)
      _ ≤ ∏ _v : ι, (1 - 1 / (10 * Real.log N)) :=
          Finset.prod_le_prod₀ (fun _ _ => hm _) (fun _ _ => _root_.GlobalTheory.BadShare.mass_not_hasPrimeFactor_le g N hN)
      _ = (1 + (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          rw [Finset.prod_const, Finset.card_univ]; ring
      _ ≤ (Real.exp (-(1 / (10 * Real.log N)))) ^ Fintype.card ι := by
          refine pow_le_pow_left₀ ?_ ?_ _
          · have : 1 / (10 * Real.log N) ≤ 1 := by rw [div_le_one (by linarith)]; exact hL
            linarith
          · linarith [Real.add_one_le_exp (-(1 / (10 * Real.log N)))]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsplit : ∀ F : ι → (ZMod g)[X], (∀ v, F v ∈ sqSet g N) → True →
      Good g N ch F ∨
      ((∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨
      ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)),
          ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨
      ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨
      (∀ v, ¬ HasPrimeFactor g N (F v)))))) := by
    intro F hF _
    by_contra hcon
    simp only [not_or] at hcon
    obtain ⟨hG, h1', h2', h3', h4', h5'⟩ := hcon
    apply hG
    have hA : ∀ v, RootsApart g N (F v) := fun v =>
      Classical.byContradiction fun h => h1' ⟨v, Finset.mem_univ _, h⟩
    have hB : ∀ v j, RootsAvoid g (ch v j) (F v) := fun v j =>
      Classical.byContradiction fun h => h2' ⟨(v, j), Finset.mem_univ _, h⟩
    have hC : ∀ v j, RootsAvoid g (ch v j)⁻¹ (F v) := fun v j =>
      Classical.byContradiction fun h => h3' ⟨(v, j), Finset.mem_univ _, h⟩
    have hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ v, ¬ HasDiv g a (F v) := fun a ha1 ha2 => by
      by_contra h
      push Not at h
      exact h4' ⟨a, Finset.mem_Icc.mpr ⟨ha1, by omega⟩, h⟩
    have hE : ∃ v, HasPrimeFactor g N (F v) := by
      by_contra h
      push Not at h
      exact h5' h
    unfold Good Formalism.CyclotomicNorms.IsGood
    exact ⟨⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hB v j l hl hlg, hD, hE⟩,
      ⟨fun v => (hsq _ (hF v)).1, fun v => (hsq _ (hF v)).2,
        fun l hl hl' v => hA v l hl hl', fun l hl hlg v j => hC v j l hl hlg, hD, hE⟩⟩
  have hor : ∀ {P Q : (ι → (ZMod g)[X]) → Prop},
      tupleMass g N (fun F => P F ∨ Q F) ≤ tupleMass g N P + tupleMass g N Q :=
    fun {_ _} => tupleMass_le_add fun _ _ h => h
  have hgood : tupleMass g N (Good g N ch) = ∑ F ∈ goodSet g N ch, ∏ v, ((torusCard g (F v) : ℝ))⁻¹ := by
    unfold tupleMass goodSet
    rw [Finset.sum_filter]
  have s0 := tupleMass_le_add hsplit
  have s1 := hor (P := fun F => (∃ v ∈ Finset.univ, ¬ RootsApart g N (F v)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)) ∨ ((∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))))
  have s2 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g (ch p.1 p.2) (F p.1)))
    (Q := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)) ∨ ((∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v))))
  have s3 := hor (P := fun F => (∃ p ∈ (Finset.univ : Finset (ι × Fin m)), ¬ RootsAvoid g ((fun v j => (ch v j)⁻¹) p.1 p.2) (F p.1)))
    (Q := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)) ∨ (∀ v, ¬ HasPrimeFactor g N (F v)))
  have s4 := hor (P := fun F => (∃ a ∈ Finset.Icc 1 (N / 2), ∀ v, HasDiv g a (F v)))
    (Q := fun F => (∀ v, ¬ HasPrimeFactor g N (F v)))
  beta_reduce at s0 s1 s2 s3 s4
  have b2 := hE2 ch
  have b3 := hE2 (fun v j => (ch v j)⁻¹)
  have hb4 := s4.trans (add_le_add hE4 hE5)
  have hb3 := s3.trans (add_le_add b3 hb4)
  have hb2 := s2.trans (add_le_add b2 hb3)
  have hb1 := s1.trans (add_le_add hE1 hb2)
  have hb0 := s0.trans (add_le_add le_rfl hb1)
  rw [← hgood]
  unfold badBound
  rw [Real.rpow_natCast]
  ring_nf at hall hb0 ⊢
  linarith only [hall, hb0]

end GlobalTheory.BadShare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerPotentialSpanHeckeLetterStable
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.H3.LamStab

theorem polySlash_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (p : MvPolynomial (Fin 2) R) : slP m (MvPolynomial.map φ p) = MvPolynomial.map φ (slP m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X, Betti.slP_X, map_add (f := _), map_smul]
    simp [MvPolynomial.smul_eq_C_mul]

theorem opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opP S m (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opP R m F z) := by
  funext z
  simp only [opP, LinearMap.coe_mk, AddHom.coe_mk, polySlash_map]

theorem sum_opP_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {ι : Type} (s : Finset ι)
    (m : ι → Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    (∑ j ∈ s, opP S (m j)) (fun z => MvPolynomial.map φ (F z)) =
      fun z => MvPolynomial.map φ ((∑ j ∈ s, opP R (m j)) F z) := by
  funext z
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, Finset.sum_apply, opP_map, map_sum]

theorem opL_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (N l : ℕ) (T : Letter)
    (F : ℂ → MvPolynomial (Fin 2) R) :
    opL S N l T (fun z => MvPolynomial.map φ (F z)) = fun z => MvPolynomial.map φ (opL R N l T F z) := by
  cases T with
  | T q =>
    simp only [opL, LinearMap.add_apply, sum_opP_map, opP_map]
    funext z; simp
  | U => simp only [opL, sum_opP_map]
  | D d => simp only [opL, opP_map]

end GlobalTheory.KZ.H3.LamStab


open GlobalTheory.KZ.H3 GlobalTheory.KZ.H3.LamStab in
theorem GlobalTheory.KZ.H3.lam_stable : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (T : Letter) (p : (E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)),
    p ∈ H3.abelian₂ X l E → (X.opV N l E T p.1, opL E N l T p.2) ∈ H3.abelian₂ X l E := by
  intro Ω _ _ ε X N l _ E _ _ T p hp
  let Φ : ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) →ₗ[E]
      ((E ⊗[ℤ_[l]] X.Fn l) × (ℂ → MvPolynomial (Fin 2) E)) :=
    LinearMap.prodMap (X.opV N l E T) (opL E N l T)
  have key : abelian₂ X l E ≤ (abelian₂ X l E).comap Φ := by
    unfold abelian₂
    rw [Submodule.span_le]
    rintro q ⟨b, F, hR, rfl⟩
    refine Submodule.subset_span ⟨X.op N l T b, opL ℤ_[l] N l T F,
      (_root_.GlobalTheory.KZ.H3.rel_ops Ω ε X l).2.2.2.2 N T b F hR, ?_⟩
    simp only [Φ, LinearMap.prodMap_apply, Tower.opV, LinearMap.baseChange_tmul, opL_map]
  exact key hp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldAnSlGerm
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def germCompMob (g : GQ) : Mero →+* Mero where
  toFun F := F.compTendsto (mob g) (_root_.GlobalTheory.FN.tendsto_mob_codiscreteWithin g)
  map_one' := rfl
  map_mul' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl
  map_zero' := rfl
  map_add' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl

theorem germCompMob_coe (g : GQ) (φ : ℂ → ℂ) :
    germCompMob g (φ : Mero) = ((fun z => φ (mob g z)) : Mero) := rfl

theorem an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  intro Ω _ _ _ ε T g f φ hf
  have key : T.an.comp ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) = (germCompMob g).comp T.an := by
    apply (_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).1 Mero
    intro a
    obtain ⟨a', ha', hs⟩ := (_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).2.1 g a
    simp only [RingHom.comp_apply]
    rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) (T.io a) = T.sl g (T.io a) from rfl, hs, T.an_io, T.an_io]
    unfold germ
    rw [germCompMob_coe]
    apply (_root_.GlobalTheory.FN.germ_ringHom_and_restrict).2.2.1
    intro z hz
    rw [ha']
    exact (_root_.GlobalTheory.FN.cmp_props).2.2.2 g a z hz
  have h2 := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at h2
  rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) f = T.sl g f from rfl] at h2
  rw [h2, hf, germCompMob_coe]

end GlobalTheory.FN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedThetaQProductModularSTransformStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothedThetaQProduct_modularS_transform : ∀ (c : ℕ) (τ : ℍ) (z : ℂ), 1 < c → Nat.Coprime c 6 → (∀ m n : ℤ, (c : ℂ) * z ≠ (m : ℂ) * (τ : ℂ) + n) → cth c (ee ((ModularGroup.S • τ : ℍ) : ℂ)) (ee (z / (τ : ℂ))) = cth c (ee (τ : ℂ)) (ee z) := by
  first | exact @GlobalTheory.Sieg.cth_modular_S | exact GlobalTheory.Sieg.cth_modular_S | (intros; apply GlobalTheory.Sieg.cth_modular_S <;> assumption)
end

