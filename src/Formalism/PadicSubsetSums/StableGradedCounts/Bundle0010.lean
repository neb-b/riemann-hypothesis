module

public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0001
public import Formalism.WindowSums.PowerSeriesRelationList
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.ContractBij
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.Bundle0001
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.Bundle0002
public import Mathlib
public import Formalism.GaloisIrreducibility.NoSolvableTransitive
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Window
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
public import Formalism.CyclotomicNorms.Bundle0001
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0009
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0001
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0002
public import Formalism.PadicSubsetSums.StableGradedCounts.ZBrauerNesbitt
public import Formalism.PadicSubsetSums.CentralIdempotents.StretchedExponentialDominance
public import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight

@[expose] public section

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.ARCReuse
section
namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial

theorem colength_bound_two_layers : ColengthTwoStep := Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts.lenBound2

theorem lagrange_resolvent_T : LagrangeT := by
  intro l _ D₁ D₂ ρ hd hρ
  have hass : ∀ a ∈ D₁, ∀ b ∈ D₁ ∪ D₂, a ≠ b →
      Associated (((a : ℤ) : ℤ_[l]) - ((b : ℤ) : ℤ_[l])) ((l : ℤ_[l]) ^ (0 + padicValInt l (a - b))) := by
    intro a _ b _ hab
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    set v := padicValInt l (a - b) with hv
    obtain ⟨c, hc⟩ : (l : ℤ) ^ v ∣ a - b := padicValInt_dvd (a - b)
    have hcn : ¬ (l : ℤ) ∣ c := by
      intro ⟨c', hc'⟩
      have : (l : ℤ) ^ (v + 1) ∣ a - b := ⟨c', by rw [hc, hc']; ring⟩
      have h2 := (padicValInt_dvd_iff (p := l) _ (a - b)).mp this
      rcases h2 with h2 | h2
      · exact hne h2
      · omega
    have hu : IsUnit ((c : ℤ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff]
      exact ((Nat.prime_iff_prime_int.mp (Fact.out : l.Prime)).coprime_iff_not_dvd.mpr hcn).symm
    rw [zero_add, ← Int.cast_sub, hc]
    push_cast
    exact (associated_mul_unit_left _ _ hu)
  have h := Formalism.ZetaNonvanishing.LIFTV.lagrangeIdealSg_proof l ℤ_[l] 0 D₁ D₂ (fun a => ((a : ℤ) : ℤ_[l])) hd hass
  set E := D₁.sup fun a => (∑ b ∈ D₂, (0 + padicValInt l (a - b))) +
    ∑ a' ∈ D₁.erase a, (0 + padicValInt l (a - a')) with hE
  have hle : E ≤ ρ := by
    rw [hE]; apply Finset.sup_le; intro a ha
    simpa using hρ a ha
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  rw [pow_add, mul_comm, C_mul]
  exact Ideal.mul_mem_left _ _ h

theorem filtered_product : FiltProd := by
  intro R V _ _ _ T F c k a
  induction a with
  | zero => intro _ x hx; simpa using hx
  | succ a ih =>
    intro h x hx
    have hy := ih (fun i h1 h2 => h i h1 (by omega)) x hx
    rw [← add_assoc, Finset.prod_Ico_succ_top (by omega), mul_comm, map_mul, Module.End.mul_apply]
    have := h (k + a) (by omega) (by omega) _ hy
    simpa [Module.algebraMap_end_apply] using this

theorem aeval_mapQ {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] (T : Module.End R V)
    (W : Submodule R V) (hW : W ≤ W.comap T) (P : R[X]) (y : V) :
    aeval (W.mapQ W T hW : Module.End R (V ⧸ W)) P (W.mkQ y) = W.mkQ (aeval T P y) := by
  have hpow : ∀ (n : ℕ) (z : V),
      ((W.mapQ W T hW : Module.End R (V ⧸ W)) ^ n) (W.mkQ z) = W.mkQ ((T ^ n) z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have : (W.mapQ W T hW : Module.End R (V ⧸ W)) (W.mkQ z) = W.mkQ (T z) := rfl
      rw [this, ih]
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n r =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, hpow,
      map_smul]

end Formalism.IrreducibleCountingLemmas.WindowSums
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.CardLtAddCardGtAddCardEq
section
open Polynomial Filter Topology

namespace Formalism.IrreducibleCountingLemmas.Z

theorem charpolyRev_map_alt {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) :
    Matrix.charpolyRev (M.map f) = (Matrix.charpolyRev M).map f := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j : 1
  by_cases h : i = j <;> simp [h]

theorem third_reduction_holds : ResidueCharpolyEq := by
  intro O _ _ X' _ T hT G n r hr x y g
  have h1 : Matrix.charpolyRev ((r x g).map (IsLocalRing.residue O)) =
      Matrix.charpolyRev ((r y g).map (IsLocalRing.residue O)) := by
    rw [charpolyRev_map_alt, charpolyRev_map_alt]
    ext j
    rw [coeff_map, coeff_map]
    exact same_residue_holds O X' T hT _ (hr g j) x y
  refine ⟨h1, ?_⟩
  have key : ∀ M : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      M.charpoly = (Matrix.charpolyRev M).reflect n := by
    intro M
    rw [← Matrix.reverse_charpoly, Polynomial.reverse, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin, reflect_reflect]
  rw [key, key, h1]

theorem nonempty_of_local_subalgebra {O X' : Type} [CommRing O] (T : Subalgebra O (X' → O)) [IsLocalRing T] :
    Nonempty X' := by
  by_contra h
  have : IsEmpty X' := not_nonempty_iff.1 h
  exact zero_ne_one (α := T) (Subtype.ext (funext fun x => isEmptyElim x))

theorem monic_of_eval_monic {O X' : Type} [CommRing O] [IsLocalRing O] (T : Subalgebra O (X' → O))
    [IsLocalRing T] (p : T[X]) (h : ∀ x, (p.map (ev T x)).Monic) : p.Monic := by
  obtain ⟨x₀⟩ := nonempty_of_local_subalgebra T
  have hp0 : p ≠ 0 := by
    intro h0
    have := h x₀
    rw [h0, Polynomial.map_zero] at this
    exact this.ne_zero rfl
  have ha0 : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hp0
  have hval : ∀ x, ev T x p.leadingCoeff = 1 ∨ ev T x p.leadingCoeff = 0 := by
    intro x
    have hle : (p.map (ev T x)).natDegree ≤ p.natDegree := natDegree_map_le
    have hc : ev T x p.leadingCoeff = (p.map (ev T x)).coeff p.natDegree := by
      rw [coeff_map]; rfl
    rcases hle.eq_or_lt with he | hl
    · left
      rw [hc, ← he]; exact h x
    · right
      rw [hc]; exact coeff_eq_zero_of_natDegree_lt hl
  have hidem : p.leadingCoeff * (1 - p.leadingCoeff) = 0 := by
    apply Subtype.ext
    funext x
    have : ev T x (p.leadingCoeff * (1 - p.leadingCoeff)) = 0 := by
      rw [map_mul, map_sub, map_one]
      rcases hval x with h1 | h1 <;> rw [h1] <;> simp
    exact this
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self p.leadingCoeff with hu | hu
  · have := (hu.mul_right_eq_zero).1 hidem
    exact (sub_eq_zero.1 this).symm
  · exact absurd ((hu.mul_left_eq_zero).1 hidem) ha0

theorem fifth_factor_monic : FactorOverLocalSubalgebraMonic := by
  intro O _ _ X' _ T hT t c F s hF h1 h2
  obtain ⟨P, hP1, hP2, hP3⟩ := factorOverLocalSubalgebra O X' T hT t c F s h1 h2
  refine ⟨P, ?_, hP1, hP2, hP3⟩
  rw [hP1] at hF
  exact Monic.of_mul_monic_right ((monic_X_sub_C _).pow t) hF

theorem charpoly_smul_id {K B : Type} [Field K] [AddCommGroup B] [Module K B]
    [FiniteDimensional K B] (c : K) :
    (c • (LinearMap.id : B →ₗ[K] B)).charpoly = (X - C c) ^ Module.finrank K B := by
  rw [LinearMap.charpoly_def, map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal,
    Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ,
    Module.finrank_eq_card_chooseBasisIndex]

theorem charpoly_eq_restrict_mul_scalar {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K V) (γ₀ : Module.End K V) (c : K) (hAB : IsCompl A B)
    (hA0 : ∀ v ∈ A, γ₀ v ∈ A) (hB0 : ∀ v ∈ B, γ₀ v = c • v) :
    γ₀.charpoly = (γ₀.restrict hA0).charpoly * (X - C c) ^ Module.finrank K B := by
  have hconj : (Submodule.prodEquivOfIsCompl A B hAB).conj
      ((γ₀.restrict hA0).prodMap (c • (LinearMap.id : B →ₗ[K] B))) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := (Submodule.prodEquivOfIsCompl A B hAB).surjective v
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    simp [Submodule.coe_prodEquivOfIsCompl', hB0 b b.2]
  rw [← charpoly_smul_id, ← LinearMap.charpoly_prodMap, ← LinearEquiv.charpoly_conj
    (Submodule.prodEquivOfIsCompl A B hAB), hconj]

theorem fifth_assembly_second : FactorAnnihilatorFamily := by
  intro O K _ _ _ _ hinj X' _ T hT V _ _ _ A B γ₀ γ c cγ t F hF hAB hA0 hA hB0 hB hfr hmult
  have := hT
  have hDm : ((X - C c : O[X]) ^ t).Monic := (monic_X_sub_C _).pow t
  have hDK : ((X - C c : O[X]) ^ t).map (algebraMap O K) = (X - C (algebraMap O K c)) ^ t := by
    rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  have hsplit : ∀ x, (γ₀ x).charpoly =
      ((γ₀ x).restrict (hA0 x)).charpoly * (X - C (algebraMap O K c)) ^ t := by
    intro x
    have := charpoly_eq_restrict_mul_scalar (A x) (B x) (γ₀ x) (algebraMap O K c) (hAB x) (hA0 x) (hB0 x)
    rwa [hfr x] at this
  have hFx : ∀ x, F.map (ev T x) = (F.map (ev T x) /ₘ (X - C c) ^ t) * (X - C c) ^ t := by
    intro x
    have hrem : F.map (ev T x) %ₘ (X - C c) ^ t = 0 := by
      apply Polynomial.map_injective _ hinj
      rw [map_modByMonic _ hDm, hDK, hF x, hsplit x, Polynomial.map_zero]
      exact (modByMonic_eq_zero_iff_dvd ((monic_X_sub_C _).pow t)).2 (dvd_mul_left _ _)
    have := modByMonic_add_div (F.map (ev T x)) ((X - C c) ^ t)
    rw [hrem, zero_add] at this
    rw [mul_comm]; exact this.symm
  have hFm : ∀ x, (F.map (ev T x)).Monic := by
    intro x
    apply monic_of_injective hinj
    rw [hF x]; exact LinearMap.charpoly_monic _
  have hsm : ∀ x, (F.map (ev T x) /ₘ (X - C c) ^ t).Monic := by
    intro x
    have := hFm x
    rw [hFx x] at this
    exact Monic.of_mul_monic_right hDm this
  have hunit : ∀ x, IsUnit ((F.map (ev T x) /ₘ (X - C c) ^ t).eval c) := by
    intro x
    apply g5b_multiplicity_holds O t c _ (hsm x)
    rw [← hFx x]; exact hmult x
  obtain ⟨P, hPm, hP1, hP2, hP3⟩ := fifth_factor_monic O X' T hT t c F
    (fun x => F.map (ev T x) /ₘ (X - C c) ^ t) (monic_of_eval_monic T F hFm) hFx hunit
  refine ⟨P, hPm, hP1, hP2, fun x => ?_⟩
  apply charpolyFactorAnnihilator K (V x) (A x) (B x) (γ₀ x) (γ x) (algebraMap O K c) (algebraMap O K cγ) t _
    (hAB x) (hA0 x) (hA x) (hB0 x) (hB x) (hfr x)
  rw [hP3 x, ← hF x, ← hDK, ← Polynomial.map_mul, ← hFx x]

theorem good_cuspidal_multiplicity_one : GoodCuspidalOne := by
  intro k _ P _ r f I _ n d h hr hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨hd, hcard⟩ := goodCuspidal_holds k P r f I n d h hdeg hsq hprod hn hn1 hd1 hno
  obtain ⟨v₀⟩ := ‹Nonempty P›
  have hne : Nonempty I := by
    by_contra hemp
    have : IsEmpty I := not_nonempty_iff.1 hemp
    have := hdeg v₀
    rw [hprod v₀, Finset.univ_eq_empty, Finset.prod_empty, natDegree_one] at this
    omega
  have hsub : Subsingleton I := Fintype.card_le_one_iff_subsingleton.1 hcard
  refine ⟨le_antisymm hcard (Fintype.card_pos_iff.2 hne), fun i => ⟨hd i, ?_⟩⟩
  have := hdeg v₀
  rw [hprod v₀, Fintype.prod_subsingleton _ i, hd i, pow_one, hn] at this
  exact this

theorem first_charpoly_in_T : CharpolyOverSubalgebra := by
  intro O _ _ X' _ T n M h
  have hdeg : ∀ x, (M x).charpoly.natDegree = n := fun x => by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hco : ∀ (x : X') (j : ℕ), j ≤ n →
      (M x).charpoly.coeff j = (Matrix.charpolyRev (M x)).coeff (n - j) := by
    intro x j hj
    rw [← Matrix.reverse_charpoly, coeff_reverse, hdeg, revAt_le (Nat.sub_le n j),
      Nat.sub_sub_self hj]
  have hmem : ∀ j : ℕ, (fun x => (M x).charpoly.coeff j) ∈ T := by
    intro j
    by_cases hj : j ≤ n
    · have : (fun x => (M x).charpoly.coeff j) =
          fun x => (Matrix.charpolyRev (M x)).coeff (n - j) := funext fun x => hco x j hj
      rw [this]; exact h _
    · have : (fun x => (M x).charpoly.coeff j) = 0 := funext fun x =>
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
      rw [this]; exact T.zero_mem
  let F : T[X] := ∑ j ∈ Finset.range (n + 1), C (⟨_, hmem j⟩ : T) * X ^ j
  have hFc : ∀ j, F.coeff j = if j ≤ n then (⟨_, hmem j⟩ : T) else 0 := by
    intro j
    simp only [F, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp
  refine ⟨F, ?_, fun x => ?_⟩
  · apply monic_of_natDegree_le_of_coeff_eq_one n
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hFc, if_neg (by omega)]
    · rw [hFc, if_pos le_rfl]
      apply Subtype.ext
      funext x
      have := (Matrix.charpoly_monic (M x)).coeff_natDegree
      rw [hdeg] at this
      exact this
  · ext j
    rw [coeff_map, hFc]
    by_cases hj : j ≤ n
    · rw [if_pos hj]; rfl
    · rw [if_neg hj, map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)).symm

end Formalism.IrreducibleCountingLemmas.Z
end

-- bundled from Formalism.PadicSubsetSums.StableGradedCounts.DominantNumbersEighthOfSharp
section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem dominant_numbers_sharp_holds : StretchedExponentialDominance := by
  intro C ε hε
  have ha : 0 < ε / 6 := by positivity
  have hab : 0 < ε / 6 - ε / 7 := by linarith
  have hc : (0 : ℝ) < 1 / (3 * (|C| + 1)) := by positivity
  filter_upwards [(tendsto_rpow_atTop hab).eventually_ge_atTop 3,
    (isLittleO_log_rpow_atTop ha).bound hc,
    (tendsto_rpow_atTop ha).eventually_ge_atTop (3 * Real.log 20),
    Filter.eventually_ge_atTop (1 : ℝ)] with x h1 h2 h3 h4
  have hx0 : 0 < x := by linarith
  have hsplit : x ^ (ε / 6) = x ^ (ε / 7) * x ^ (ε / 6 - ε / 7) := by
    rw [← Real.rpow_add hx0]
    ring_nf
  have hb0 : 0 ≤ x ^ (ε / 7) := Real.rpow_nonneg hx0.le _
  have hxb : 3 * x ^ (ε / 7) ≤ x ^ (ε / 6) := by
    rw [hsplit]
    nlinarith
  have ha0 : 0 ≤ x ^ (ε / 6) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha0] at h2
  have hlog : C * Real.log x ≤ x ^ (ε / 6) / 3 := by
    have hC0 : 0 ≤ |C| := abs_nonneg C
    have e1 : C * Real.log x ≤ |C| * |Real.log x| := by
      rw [← abs_mul]
      exact le_abs_self _
    have e2 : |C| * |Real.log x| ≤ |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) :=
      mul_le_mul_of_nonneg_left h2 hC0
    have e3 : |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) ≤ x ^ (ε / 6) / 3 := by
      rw [show |C| * (1 / (3 * (|C| + 1)) * x ^ (ε / 6)) = |C| / (|C| + 1) * (x ^ (ε / 6) / 3) by
        field_simp]
      have : |C| / (|C| + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      have h6 : 0 ≤ x ^ (ε / 6) / 3 := by positivity
      nlinarith
    linarith
  have h20 : (1 : ℝ) / 20 = Real.exp (-Real.log 20) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add, h20, ← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

