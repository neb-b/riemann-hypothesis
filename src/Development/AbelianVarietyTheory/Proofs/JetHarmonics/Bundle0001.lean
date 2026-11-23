module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterLeSuccAndSqSumLePow
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem card_filter_le_succ_and_sq_sum_le_pow : ∀ (n kk : ℕ) (bv : ℝ), 1 ≤ kk → kk + 1 ≤ n → (n : ℝ) ≤ bv → (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk ∧ (18 / 13 : ℝ) ^ 2 + ((n + 1 - kk : ℕ) : ℝ) * (3 * (6 * bv) ^ (n - kk)) ^ 2 ≤ (6 * bv) ^ (2 * (n + 1 - kk)) := by
  intro n kk bv h1 h2 h3
  refine ⟨?_, ?_⟩
  · have hlt : kk - 1 < n := by omega
    have : (univ.filter fun a : Fin n => kk ≤ a.val + 1) = Finset.Ici (⟨kk - 1, hlt⟩ : Fin n) := by
      ext a
      simp only [mem_filter, mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      omega
    rw [this, Fin.card_Ici]
    simp only
    omega
  · have e1 : n + 1 - kk = (n - kk) + 1 := by omega
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hM : ((n + 1 - kk : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega : n + 1 - kk ≤ n)
    have hb : (2 : ℝ) ≤ bv := hn2.trans h3
    have hX : (1 : ℝ) ≤ (6 * bv) ^ (n - kk) := one_le_pow₀ (by linarith)
    have e2 : (6 * bv) ^ (2 * (n + 1 - kk)) = 36 * bv ^ 2 * ((6 * bv) ^ (n - kk)) ^ 2 := by
      rw [e1]; ring
    rw [e2]
    set X := (6 * bv) ^ (n - kk)
    set c := ((n + 1 - kk : ℕ) : ℝ)
    have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ hX
    have hc : c ≤ bv := hM.trans h3
    have h4 : c * X ^ 2 ≤ bv * X ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have h5 : (9 * bv + 2) * X ^ 2 ≤ 36 * bv ^ 2 * X ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffProdXSubCNormLe
section
namespace GlobalTheory.RootProductCoeffBound

open Polynomial

theorem coeff_prod_X_sub_C_norm_le {K : Type} [NormedField K] [IsUltrametricDist K]
    (θ : ℝ) (h0 : (0 : ℝ) ≤ θ) (h1 : θ ≤ (1 : ℝ)) (S : Finset K)
    (hS : ∀ x ∈ S, ‖x‖ ≤ θ) (a : ℕ) :
    ‖AddMonoidAlgebra.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖
      ≤ θ ^ (Finset.card S - a) := by
  classical
  induction S using Finset.induction_on generalizing a with
  | empty =>
    rcases a with _ | k
    · simp
    · simp [Polynomial.coeff_one]
  | insert y S hy ih =>
    have ihS : ∀ b, ‖(∏ x ∈ S, (X - C x)).coeff b‖ ≤ θ ^ (S.card - b) :=
      fun b => ih (fun x hx => hS x (Finset.mem_insert_of_mem hx)) b
    have hyθ : ‖y‖ ≤ θ := hS y (Finset.mem_insert_self y S)
    rw [Finset.prod_insert hy, Finset.card_insert_of_notMem hy]
    set P := ∏ x ∈ S, (X - C x) with hP
    rw [sub_mul, coeff_sub, coeff_C_mul]
    have hyb : ∀ b, ‖y * P.coeff b‖ ≤ θ ^ (S.card + 1 - (b + 1)) * θ := by
      intro b
      rw [norm_mul, mul_comm]
      refine mul_le_mul ?_ hyθ (norm_nonneg _) (pow_nonneg h0 _)
      simpa using ihS b
    rcases a with _ | k
    · rw [coeff_X_mul_zero, zero_sub, norm_neg]
      calc ‖y * P.coeff 0‖ ≤ θ ^ (S.card + 1 - (0 + 1)) * θ := hyb 0
        _ = θ ^ (S.card + 1 - 0) := by simp [pow_succ]
    · rw [coeff_X_mul]
      rw [sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ihS k
      · rw [norm_neg]
        calc ‖y * P.coeff (k + 1)‖ ≤ θ ^ (S.card - (k + 1)) * θ := by
              have := hyb (k + 1); simpa using this
          _ = θ ^ (S.card - (k + 1) + 1) := by rw [pow_succ]
          _ ≤ θ ^ (S.card + 1 - (k + 1)) := by
              apply pow_le_pow_of_le_one h0 h1
              omega

theorem main : ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (θ : ℝ), (0 : ℝ) ≤ θ → θ ≤ (1 : ℝ) → ∀ (S : Finset K), (∀ x ∈ S, ‖x‖ ≤ θ) → ∀ (a : ℕ), ‖AddMonoidAlgebra.coeff (∏ x ∈ S, (Polynomial.X - (Polynomial.C : K → Polynomial K) x)) a‖ ≤ θ ^ (Finset.card S - a) :=
  fun θ h0 h1 S hS a => coeff_prod_X_sub_C_norm_le θ h0 h1 S hS a

end GlobalTheory.RootProductCoeffBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivationMemPowOfMemPowSucc
section
namespace GlobalTheory.DerivationMemPow

theorem derivation_mem_pow_of_mem_pow_succ {k A : Type} [CommRing k] [CommRing A] [Algebra k A]
    (D : Derivation k A A) (I : Ideal A) (n : ℕ) :
    ∀ x ∈ I ^ (n + (1 : ℕ)), (D : A → A) x ∈ I ^ n := by
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ ?_
      · exact Ideal.mul_mem_right _ _ ha
      · have h := Ideal.mul_mem_mul hb (ih a ha)
        rwa [← pow_succ'] at h
    · intro y z hy hz
      rw [map_add (f := _)]
      exact Ideal.add_mem _ hy hz

end GlobalTheory.DerivationMemPow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCutIntoBoundedGroupsFinset
section
namespace GlobalTheory

theorem exists_le_sum_eq_of_le_sum (S : Finset ℕ) (e : ℕ → ℕ) :
    ∀ n, n ≤ ∑ k ∈ S, e k →
      ∃ f : ℕ → ℕ, (∀ k, f k ≤ e k) ∧ ∑ k ∈ S, f k = n ∧ ∀ k, k ∉ S → f k = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro n hn
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_, fun _ _ => rfl⟩
    simp only [Finset.sum_empty] at hn ⊢
    omega
  | insert a S ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨g, hge, hgs, hgo⟩ := ih (min n (∑ k ∈ S, e k)) (min_le_right _ _)
    refine ⟨fun k => if k = a then n - min n (∑ k ∈ S, e k) else g k, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = a
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        exact hge k
    · rw [Finset.sum_insert ha, if_pos rfl]
      have hS : ∑ k ∈ S, (if k = a then n - min n (∑ k ∈ S, e k) else g k) = ∑ k ∈ S, g k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have : k ≠ a := fun h => ha (h ▸ hk)
        simp only [this, if_false]
      rw [hS, hgs]
      omega
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hka, if_false]
      exact hgo k hkS

theorem exists_cut_into_bounded_groups_finset (S : Finset ℕ) (B : ℕ) :
    ∀ (s : ℕ) (e : ℕ → ℕ), ∑ k ∈ S, e k ≤ s * B →
      ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ S, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ S, pc u k ≤ B) ∧
        ∀ u k, k ∉ S → pc u k = 0 := by
  classical
  intro s
  induction s with
  | zero =>
    intro e he
    refine ⟨fun _ _ => 0, ?_, fun u => u.elim0, fun u => u.elim0⟩
    intro k hk
    simp only [zero_mul, nonpos_iff_eq_zero] at he
    rw [Finset.sum_eq_zero_iff] at he
    simp [he k hk]
  | succ s ih =>
    intro e he
    obtain ⟨f, hfe, hfs, hfo⟩ :=
      exists_le_sum_eq_of_le_sum S e (min B (∑ k ∈ S, e k)) (min_le_right _ _)
    have hsplit : ∑ k ∈ S, (e k - f k) + ∑ k ∈ S, f k = ∑ k ∈ S, e k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfe k)
    have hmul : (s + 1) * B = s * B + B := by ring
    obtain ⟨pc, hpcs, hpcb, hpco⟩ := ih (fun k => e k - f k) (by omega)
    refine ⟨Fin.cons f pc, ?_, ?_, ?_⟩
    · intro k hk
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hpcs k hk]
      exact Nat.add_sub_cancel' (hfe k)
    · intro u
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        omega
      · simp only [Fin.cons_succ]
        exact hpcb i
    · intro u k hk
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        exact hfo k hk
      · simp only [Fin.cons_succ]
        exact hpco i k hk

theorem exists_cut_columns_bounded_width : ∀ (K s B : ℕ) (e : ℕ → ℕ), ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ Finset.Icc 1 K, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧ ∀ u k, k ∉ Finset.Icc 1 K → pc u k = 0 := by
  intro K s B e h
  exact exists_cut_into_bounded_groups_finset (Finset.Icc 1 K) B s e h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDualFormsOfSeparatedTypes
section
namespace GlobalTheory

theorem exists_matrix_fix_type_kill {O A : Type} [CommRing O] {d : ℕ}
    (ρ : A → Matrix (Fin d) (Fin d) O) {T : Type} [DecidableEq T] {r : T → ℕ} (σ : T → A → O)
    (u : (Σ t : T, Fin (r t)) → Fin d → O)
    (hsep : ∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a))
    (heig : ∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) (t₀ : T) (S : Finset T) (hS : t₀ ∉ S) :
    ∃ P : Matrix (Fin d) (Fin d) O, (∀ l, l.1 = t₀ → P.mulVec (u l) = u l) ∧
      (∀ l, l.1 ∈ S → P.mulVec (u l) = 0) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun l _ => Matrix.one_mulVec _, fun l hl => absurd hl (by simp)⟩
  | insert t S htS ih =>
    obtain ⟨P, hP1, hP2⟩ := ih (fun h => hS (Finset.mem_insert_of_mem h))
    have hne : t₀ ≠ t := fun h => hS (h ▸ Finset.mem_insert_self t S)
    obtain ⟨a, c, hc⟩ := hsep t₀ t hne
    have key : ∀ l, (P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O)))).mulVec (u l)
        = ((↑c⁻¹ : O) * (σ l.1 a - σ t a)) • P.mulVec (u l) := by
      intro l
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, heig, ← sub_smul, smul_smul, Matrix.mulVec_smul]
    refine ⟨P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O))),
      fun l hl => ?_, fun l hl => ?_⟩
    · rw [key, hP1 l hl, hl, ← hc, Units.inv_mul, one_smul]
    · rw [key]
      rcases Finset.mem_insert.mp hl with h | h
      · rw [h, sub_self, mul_zero, zero_smul]
      · rw [hP2 l h, smul_zero]

theorem exists_dual_forms_of_separated_types :
    ∀ (O A : Type) [CommRing O] (d : ℕ) (ρ : A → Matrix (Fin d) (Fin d) O) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (σ : T → A → O) (u : (Σ t : T, Fin (r t)) → Fin d → O), (∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a)) → (∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) → (∀ t, ∃ lam : Fin (r t) → Fin d → O, ∀ i i', ∑ s, lam i s * u ⟨t, i'⟩ s = if i = i' then 1 else 0) → ∃ lam : (Σ t : T, Fin (r t)) → Fin d → O, ∀ l l', ∑ s, lam l s * u l' s = if l = l' then 1 else 0 := by
  intro O A _ d ρ T _ _ r σ u hsep heig hdual
  choose lam hlam using hdual
  choose P hP1 hP2 using fun t₀ : T =>
    exists_matrix_fix_type_kill ρ σ u hsep heig t₀ (Finset.univ.erase t₀) (by simp)
  refine ⟨fun l => Matrix.vecMul (lam l.1 l.2) (P l.1), ?_⟩
  rintro ⟨t, i⟩ ⟨t', i'⟩
  change Matrix.vecMul (lam t i) (P t) ⬝ᵥ u ⟨t', i'⟩ = _
  rw [← Matrix.dotProduct_mulVec]
  by_cases h : t' = t
  · subst h
    rw [hP1 t' ⟨t', i'⟩ rfl]
    have := hlam t' i i'
    simpa [dotProduct] using this
  · rw [hP2 t ⟨t', i'⟩ (by simpa using h), dotProduct_zero, if_neg]
    intro h'
    exact h (congrArg Sigma.fst h').symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntCoordsOfRegularParam
section
namespace GlobalTheory

theorem exists_int_coords_of_regular_param (n : ℕ) (u : ℕ → ℝ)
    (h : ∀ i ∈ Finset.Icc 1 n, ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) :
    ∃ (β : ℂ) (L : Fin (n + 1) → ℤ), StrictAnti L ∧
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) ∧
      ∀ i j : Fin (n + 1), (L i : ℝ) - (L j : ℝ) = u ((i : ℕ) + 1) - u ((j : ℕ) + 1) := by
  have key : ∀ j : ℕ, j ≤ n → ∃ z : ℤ, (z : ℝ) = u (j + 1) - u 1 := by
    intro j
    induction j with
    | zero => intro _; exact ⟨0, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨z, hz⟩ := ih (by omega)
      obtain ⟨N, hN⟩ := h (k + 1) (Finset.mem_Icc.2 ⟨by omega, hk⟩)
      refine ⟨z - N - 1, ?_⟩
      push_cast
      linarith
  choose z hz using key
  refine ⟨(u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2, fun j => z j (Nat.lt_succ_iff.1 j.2), ?_, ?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    obtain ⟨N, hN⟩ := h (i + 1) (Finset.mem_Icc.2 ⟨by omega, i.2⟩)
    have h1 := hz (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2)
    have h2 := hz (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2)
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : ((z (i.succ : Fin (n + 1)) (Nat.lt_succ_iff.1 i.succ.2) : ℤ) : ℝ)
        < (z (i.castSucc : Fin (n + 1)) (Nat.lt_succ_iff.1 i.castSucc.2) : ℤ) := by
      rw [h1, h2]
      simp only [Fin.val_succ, Fin.val_castSucc]
      linarith
    exact_mod_cast this
  · intro j
    have h1 := congrArg (fun x : ℝ => (x : ℂ)) (hz j (Nat.lt_succ_iff.1 j.2))
    simp only [Complex.ofReal_intCast, Complex.ofReal_sub] at h1
    simp only [h1]
    ring
  · intro i j
    simp only [hz]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsLocalHomExtension
section
namespace GlobalTheory.LocalHomExtension

theorem exists_isLocalHom_extension {A B O C : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    [CommRing B] [IsDomain B] [IsLocalRing B] [CommRing O] [IsLocalRing O] [Field C]
    [IsAlgClosed C] [Algebra O C] (v : Valuation C NNReal) (hv : Valuation.Integers v O)
    (φ : A →+* B) (hφ : Function.Injective φ) (hint : φ.IsIntegral)
    (ι : A →+* O) [IsLocalHom ι]
    (hι : Function.Injective ((algebraMap O C).comp ι)) :
    ∃ ι' : B →+* O, IsLocalHom ι' ∧ ι'.comp φ = ι := by
  let : Algebra A B := φ.toAlgebra
  let : Algebra A O := ι.toAlgebra
  let : Algebra A C := ((algebraMap O C).comp ι).toAlgebra
  have : IsScalarTower A O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.IsTorsionFree A B := Module.isTorsionFree_iff_algebraMap_injective.mpr hφ
  have : Module.IsTorsionFree A C := Module.isTorsionFree_iff_algebraMap_injective.mpr hι
  have : Algebra.IsIntegral A B := ⟨hint⟩

  let f : B →ₐ[A] C := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])

  have hO : ∀ b : B, ∃ o : O, algebraMap O C o = f b := fun b => by
    have h1 : IsIntegral A (f b) := (Algebra.IsIntegral.isIntegral b).map f
    exact hv.exists_of_le_one (hv.mem_of_integral h1.tower_top)
  choose g hg using hO
  have inj := hv.hom_inj
  let ι' : B →+* O :=
    { toFun := g
      map_one' := inj (by rw [hg, map_one, map_one])
      map_mul' := fun x y => inj (by rw [hg, map_mul, map_mul, hg, hg])
      map_zero' := inj (by rw [hg, map_zero, map_zero])
      map_add' := fun x y => inj (by rw [hg, map_add (f := _), map_add (f := _), hg, hg]) }
  have hcomp : ι'.comp φ = ι := by
    ext a
    apply inj
    show algebraMap O C (g (φ a)) = algebraMap O C (ι a)
    rw [hg]
    exact f.commutes a
  refine ⟨ι', ?_, hcomp⟩

  have hA : (IsLocalRing.maximalIdeal O).comap ι = IsLocalRing.maximalIdeal A :=
    ((IsLocalRing.local_hom_TFAE ι).out 1 5).mp (inferInstance : IsLocalHom ι)
  have hp : (((IsLocalRing.maximalIdeal O).comap ι').comap (algebraMap A B)).IsMaximal := by
    rw [Ideal.comap_comap, show ι'.comp (algebraMap A B) = ι from hcomp, hA]
    exact IsLocalRing.maximalIdeal.isMaximal A
  have hpm := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap A B)
    (show (algebraMap A B).IsIntegral from hint) ((IsLocalRing.maximalIdeal O).comap ι') hp
  exact ((IsLocalRing.local_hom_tfae ι').out 1 5).mpr (IsLocalRing.eq_maximalIdeal hpm)

end GlobalTheory.LocalHomExtension
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsUnitSubOfRingHomNe
section
namespace GlobalTheory

theorem _root_.GlobalTheory.exists_isUnit_sub_of_ringHom_ne : ∀ (A O : Type) [CommRing A] [Module.Finite ℤ A] [CommRing O] [IsLocalRing O] (g : ℕ), g.Prime → ¬ IsUnit (g : O) → (∀ x : A, x ^ g - x ∈ Ideal.span {(g : A)}) → ∀ σ σ' : A →+* O, σ ≠ σ' → ∃ a : A, IsUnit (σ a - σ' a) := by
  intro A O _ _ _ _ g hg hgO hA σ σ' hne
  by_contra hcon
  push_neg at hcon
  apply hne
  have hgm : (g : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hgO)
  have hspan : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hgm
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := A)
  set J : Ideal O := Ideal.span ((fun a => σ a - σ' a) '' (s : Set A)) with hJ
  have hmem : ∀ a : A, σ a - σ' a ∈ J := by
    intro a
    have ha : a ∈ Submodule.span ℤ (s : Set A) := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem y hy => exact Ideal.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
        have : σ (y + z) - σ' (y + z) = (σ y - σ' y) + (σ z - σ' z) := by
          rw [map_add (f := _), map_add (f := _)]; ring
        rw [this]
        exact J.add_mem hy hz
    | smul n y _ hy =>
        have : σ (n • y) - σ' (n • y) = (n : O) * (σ y - σ' y) := by
          simp [zsmul_eq_mul, mul_sub]
        rw [this]
        exact J.mul_mem_left _ hy
  have hgk : (g : IsLocalRing.ResidueField O) = 0 := by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]
    exact hgm
  have hle : J ≤ Ideal.span {(g : O)} • J := by
    rw [hJ, Ideal.span_le]
    rintro _ ⟨a, -, rfl⟩
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hA a)
    have hc1 : σ c * g = σ a ^ g - σ a := by
      rw [← map_natCast σ g, ← map_mul, hc, map_sub, map_pow]
    have hc2 : σ' c * g = σ' a ^ g - σ' a := by
      rw [← map_natCast σ' g, ← map_mul, hc, map_sub, map_pow]
    have hgeom := geom_sum₂_mul (σ a) (σ' a) g
    have key : (σ a - σ' a) * ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) =
        (g : O) * (σ c - σ' c) := by
      linear_combination hgeom - hc1 + hc2
    have hr : IsLocalRing.residue O (σ' a) = IsLocalRing.residue O (σ a) := by
      rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr (hcon a))
    have hS : (∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) ∈
        IsLocalRing.maximalIdeal O := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← IsLocalRing.residue_eq_zero_iff, map_sum]
      simp_rw [map_mul, map_pow, hr, ← pow_add]
      rw [Finset.sum_congr rfl (g := fun _ => IsLocalRing.residue O (σ a) ^ (g - 1))
        (fun i hi => by have := Finset.mem_range.mp hi; congr 1; omega)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hgk, zero_mul]
    have hu : IsUnit ((∑ i ∈ Finset.range g, σ a ^ i * σ' a ^ (g - 1 - i)) - 1) := by
      by_contra hu
      have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
        have := Ideal.sub_mem _ hS
          ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hu))
        simpa using this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
    have : σ a - σ' a = ((g : O) * (σ c - σ' c)) * ↑hu.unit⁻¹ := by
      rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
    show σ a - σ' a ∈ (Ideal.span {(g : O)} • J : Ideal O)
    rw [this, Ideal.smul_eq_mul]
    exact Ideal.mul_mem_right _ _
      (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (hmem c))
  have hfg : J.FG := by
    classical
    exact ⟨s.image (fun a => σ a - σ' a), by rw [Finset.coe_image]⟩
  have hjac : Ideal.span {(g : O)} ≤ (⊥ : Ideal O).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact hspan
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ J hfg hle hjac
  ext a
  have := hmem a
  rw [hbot] at this
  exact sub_eq_zero.mp ((Submodule.mem_bot _).mp this)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolarisationOnSubspace
section
open MeasureTheory Filter Topology

namespace GlobalTheory

theorem polarisation_on_subspace : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (S : V → Prop) (B T : V → V → ℂ), (∀ (a : ℂ) x y, S x → S y → S (x + a • y)) → (∀ (a : ℂ) x y, S x → S y → B (x + a • y) (x + a • y) = B x x + a * B y x + (starRingEnd ℂ) a * B x y + a * (starRingEnd ℂ) a * B y y) → (∀ (a : ℂ) x y, S x → S y → T (x + a • y) (x + a • y) = T x x + a * T y x + (starRingEnd ℂ) a * T x y + a * (starRingEnd ℂ) a * T y y) → (∀ x, S x → B x x = T x x) → ∀ x y, S x → S y → B x y = T x y := by
  intro V _ _ S B T hS hB hT hd x y hx hy
  have key : ∀ a : ℂ, a * B y x + (starRingEnd ℂ) a * B x y = a * T y x + (starRingEnd ℂ) a * T x y := by
    intro a
    have h := hd _ (hS a x y hx hy)
    rw [hB a x y hx hy, hT a x y hx hy, hd x hx, hd y hy] at h
    linear_combination h
  have h1 := key 1
  have h2 := key Complex.I
  rw [map_one] at h1
  rw [Complex.conj_I] at h2
  linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2
    - ((B y x - T y x - B x y + T x y) / 2) * Complex.I_mul_I

end GlobalTheory
end

