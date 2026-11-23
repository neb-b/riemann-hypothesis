module

public import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bundle0009

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NkExponent
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem nk_vi (c Ah ρ u τ : ℝ) (hc : 0 < c) (hA : 0 < Ah) (hρ0 : 0 ≤ ρ) (hρc : ρ ≤ c) (hρA : ρ ≤ Ah) (hu0 : 0 ≤ u)
    (hτ0 : 0 < τ) (hτ : τ < 1 / 4) (hu : 2 * τ * max c Ah < u) : ρ * (c + Ah - u - ρ) ≤ (1 - τ) * (c * Ah) := by
  have hid : ρ * (c + Ah - u - ρ) = c * Ah - (c - ρ) * (Ah - ρ) - ρ * u := by ring
  rw [hid]
  have h1 : 0 ≤ (c - ρ) * (Ah - ρ) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ρ * u := mul_nonneg hρ0 hu0
  have hcA : 0 < c * Ah := mul_pos hc hA
  rcases le_total c Ah with h | h
  · rw [max_eq_right h] at hu
    rcases le_total (c / 2) ρ with h3 | h3
    · have : c / 2 * (2 * τ * Ah) ≤ ρ * u := mul_le_mul h3 hu.le (by positivity) hρ0
      nlinarith
    · have : c / 2 * (Ah / 2) ≤ (c - ρ) * (Ah - ρ) := mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
      nlinarith
  · rw [max_eq_left h] at hu
    rcases le_total (Ah / 2) ρ with h3 | h3
    · have : Ah / 2 * (2 * τ * c) ≤ ρ * u := mul_le_mul h3 hu.le (by positivity) hρ0
      nlinarith
    · have : c / 2 * (Ah / 2) ≤ (c - ρ) * (Ah - ρ) := mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
      nlinarith

theorem nk_iv (c Ah ρ u : ℝ) (hρ0 : 0 ≤ ρ) (hρc : ρ ≤ c) (hρA : ρ ≤ Ah) (hu0 : 0 ≤ u) :
    ρ * (c + Ah - u - ρ) ≤ c * Ah := by
  have hid : ρ * (c + Ah - u - ρ) = c * Ah - (c - ρ) * (Ah - ρ) - ρ * u := by ring
  rw [hid]
  have h1 : 0 ≤ (c - ρ) * (Ah - ρ) := mul_nonneg (by linarith) (by linarith)
  have h2 : 0 ≤ ρ * u := mul_nonneg hρ0 hu0
  linarith

theorem nk_tele (s : ℕ) (c : ℕ → ℝ) (x y : Fin s → ℝ) (hc : ∀ l, 0 ≤ c l) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (h : ∀ i : Fin s, x i * c (i + 1) ≤ y i * c i) : c s * ∏ i, x i ≤ c 0 * ∏ i, y i := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have ih' := ih (fun i => x i.castSucc) (fun i => y i.castSucc) (fun i => hx _) (fun i => hy _)
      (fun i => by simpa using h i.castSucc)
    have hl := h (Fin.last s)
    simp only [Fin.val_last] at hl
    have hp : 0 ≤ ∏ i : Fin s, x i.castSucc := Finset.prod_nonneg fun i _ => hx _
    calc c (s + 1) * ((∏ i : Fin s, x i.castSucc) * x (Fin.last s))
        = (∏ i : Fin s, x i.castSucc) * (x (Fin.last s) * c (s + 1)) := by ring
      _ ≤ (∏ i : Fin s, x i.castSucc) * (y (Fin.last s) * c s) := mul_le_mul_of_nonneg_left hl hp
      _ = y (Fin.last s) * (c s * ∏ i : Fin s, x i.castSucc) := by ring
      _ ≤ y (Fin.last s) * (c 0 * ∏ i : Fin s, y i.castSucc) := mul_le_mul_of_nonneg_left ih' (hy _)
      _ = _ := by ring

theorem nk_bracket (s : ℕ) (c : ℕ → ℝ) (x nn Ai Ci κ μ : Fin s → ℝ) (l A E1 E2 : ℝ)
    (hc : ∀ l, 0 ≤ c l) (hx : ∀ i, 0 ≤ x i) (hn0 : ∀ i, 0 ≤ nn i) (hAi : ∀ i, 0 ≤ Ai i) (hCi : ∀ i, 0 ≤ Ci i)
    (hκ : ∀ i, 0 ≤ κ i) (hμ : ∀ i, 0 ≤ μ i) (hl0 : 0 ≤ l) (hE2 : 0 ≤ E2)
    (hstep : ∀ i : Fin s, x i * c (i + 1) ≤ (κ i * (E2 * Ai i)) * c i)
    (hl : l ≤ c s) (hn : ∀ i, nn i ≤ μ i * (E2 * Ci i)) (hA : c 0 ≤ E1 * A) :
    l * (∏ i, x i) * (∏ i, nn i) ≤
      (E1 * E2 ^ s * E2 ^ s * ((∏ i, κ i) * ∏ i, μ i)) * (A * (∏ i, Ai i) * ∏ i, Ci i) := by
  have h1 := nk_tele s c x (fun i => κ i * (E2 * Ai i)) hc hx (fun i => by have := hκ i; have := hAi i; positivity) hstep
  have hpx : 0 ≤ ∏ i, x i := Finset.prod_nonneg fun i _ => hx i
  have hpn : 0 ≤ ∏ i, nn i := Finset.prod_nonneg fun i _ => hn0 i
  have hpy : 0 ≤ ∏ i, (κ i * (E2 * Ai i)) :=
    Finset.prod_nonneg fun i _ => by have := hκ i; have := hAi i; positivity
  have h2 : ∏ i, nn i ≤ ∏ i, (μ i * (E2 * Ci i)) := Finset.prod_le_prod₀ (fun i _ => hn0 i) fun i _ => hn i
  have e1 : ∏ i, (κ i * (E2 * Ai i)) = (∏ i, κ i) * (E2 ^ s * ∏ i, Ai i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have e2 : ∏ i, (μ i * (E2 * Ci i)) = (∏ i, μ i) * (E2 ^ s * ∏ i, Ci i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc l * (∏ i, x i) * (∏ i, nn i) ≤ (c s * ∏ i, x i) * ∏ i, nn i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl hpx) hpn
    _ ≤ (c 0 * ∏ i, (κ i * (E2 * Ai i))) * ∏ i, nn i := mul_le_mul_of_nonneg_right h1 hpn
    _ ≤ (E1 * A * ∏ i, (κ i * (E2 * Ai i))) * ∏ i, nn i :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hpy) hpn
    _ ≤ (E1 * A * ∏ i, (κ i * (E2 * Ai i))) * ∏ i, (μ i * (E2 * Ci i)) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_trans (hc 0) hA) hpy)
    _ = _ := by rw [e1, e2]; ring

theorem nk_exponent (s r : ℕ) (La γ : ℝ) (hr : 9 ≤ r) (hs : 2 * s + 1 ≤ r) (hLa : 0 ≤ La) (hγ0 : 0 ≤ γ)
    (hγ : γ ≤ Real.exp (-(La / (4 * ((r : ℝ) + 1))))) :
    (Real.exp (1 / ((r : ℝ) + 1) ^ 2) * Real.exp (2 / ((r : ℝ) + 1) ^ 2) ^ s * Real.exp (2 / ((r : ℝ) + 1) ^ 2) ^ s * γ) ^
      (r - 1) ≤ Real.exp (2 - La / 5) := by
  have hr9 : (9 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hk : (10 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  set k : ℝ := (r : ℝ) + 1 with hkdef
  have hsr : 2 * (s : ℝ) + 1 ≤ k - 1 := by
    have : ((2 * s + 1 : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast hs
    push_cast at this
    linarith
  have hn : ((r - 1 : ℕ) : ℝ) = k - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hb : Real.exp (1 / k ^ 2) * Real.exp (2 / k ^ 2) ^ s * Real.exp (2 / k ^ 2) ^ s * γ ≤
      Real.exp (1 / k ^ 2 + s * (2 / k ^ 2) + s * (2 / k ^ 2) - La / (4 * k)) := by
    rw [← Real.exp_nat_mul, sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hγ (by positivity)
  have hb0 : 0 ≤ Real.exp (1 / k ^ 2) * Real.exp (2 / k ^ 2) ^ s * Real.exp (2 / k ^ 2) ^ s * γ := by positivity
  refine (pow_le_pow_left₀ hb0 hb (r - 1)).trans ?_
  rw [← Real.exp_nat_mul, hn]
  apply Real.exp_le_exp.mpr
  have hk0 : 0 < k := by linarith
  have e1 : (k - 2) * (1 / k ^ 2 + s * (2 / k ^ 2) + s * (2 / k ^ 2) - La / (4 * k)) =
      (k - 2) * (4 * s + 1) / k ^ 2 - (k - 2) * La / (4 * k) := by
    field_simp
    ring
  rw [e1]
  have h1 : (k - 2) * (4 * s + 1) / k ^ 2 ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : La / 5 ≤ (k - 2) * La / (4 * k) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  linarith

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

abbrev IntAlg (O : Type) [CommRing O] [IsDomain O] (σ : Type*) : Subalgebra O (MvPolynomial σ (KK O)) :=
  (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)).range

theorem X_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ : Type*} (v : σ) : (X v : MvPolynomial σ (KK O)) ∈ IntAlg O σ := by
  exact (AlgHom.mem_range _).mpr ⟨MvPolynomial.X v, by simp⟩

theorem intPol_le (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntPol O σ) :
    P ∈ IntAlg O σ := by
  obtain ⟨Q, hQ⟩ := LinearMap.mem_range.mp h
  exact (AlgHom.mem_range _).mpr ⟨Q, hQ⟩

theorem inA_of_mem (O : Type) [CommRing O] [IsDomain O] {σ : Type*} {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) :
    InA (O := O) P := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  unfold InA
  intro m
  exact ⟨Q.coeff m, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.coeff_map]⟩

theorem rename_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → τ) {P : MvPolynomial σ (KK O)}
    (h : P ∈ IntAlg O σ) : rename f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  exact (AlgHom.mem_range _).mpr ⟨rename f Q, by simp [MvPolynomial.mapAlgHom_apply, MvPolynomial.map_rename]⟩

theorem aeval_mem_intAlg (O : Type) [CommRing O] [IsDomain O] {σ τ : Type*} (f : σ → MvPolynomial τ (KK O))
    (hf : ∀ v, f v ∈ IntAlg O τ) {P : MvPolynomial σ (KK O)} (h : P ∈ IntAlg O σ) : aeval f P ∈ IntAlg O τ := by
  obtain ⟨Q, rfl⟩ := (AlgHom.mem_range _).mp h
  have e : (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial σ O →ₐ[O] MvPolynomial σ (KK O)) Q =
      MvPolynomial.map (algebraMap O (KK O)) Q := rfl
  rw [e, MvPolynomial.aeval_map_algebraMap]
  clear h e
  induction Q using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C]; exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p v hp => rw [map_mul, MvPolynomial.aeval_X]; exact mul_mem hp (hf v)

theorem ssz_le_intAlg (O : Type) [CommRing O] [IsDomain O] {N r : ℕ} [NeZero r] (D : BlockData N) :
    ∀ x ∈ D.SSZ O (r := r), x ∈ IntAlg O (BVar N r D.T.t) := by
  intro x hx
  unfold BlockData.SSZ at hx
  refine Submodule.span_induction (p := fun x _ => x ∈ IntAlg O (BVar N r D.T.t)) ?_ ?_ ?_ ?_ hx
  · intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, _, y, hy, g0, hg0, rfl⟩ := hx
    have hX := fun v => X_mem_intAlg O (σ := BVar N r D.T.t) v
    have hE : ∀ i, D.Ehat O (r := r) i ∈ IntAlg O (BVar N r D.T.t) := fun i => by
      unfold BlockData.Ehat
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    have hP : D.Eplus O (r := r) ∈ IntAlg O (BVar N r D.T.t) := by
      unfold BlockData.Eplus
      exact (IntAlg O _).add_mem ((IntAlg O _).mul_mem (hX _) (hX _))
        ((IntAlg O _).sum_mem fun c _ => (IntAlg O _).mul_mem (hX _) (hX _))
    refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem ((IntAlg O _).mul_mem
      ((IntAlg O _).mul_mem ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hE i) _)
        ((IntAlg O _).pow_mem hP _)) ((IntAlg O _).prod_mem fun i _ => (IntAlg O _).pow_mem (hX _) _))
      ((IntAlg O _).pow_mem (hX _) _)) (rename_mem_intAlg O _ (intPol_le O hy.2))) (intPol_le O hg0.2)
  · exact (IntAlg O _).zero_mem
  · intro x y _ _ hx hy; exact (IntAlg O _).add_mem hx hy
  · intro a x _ hx; exact (IntAlg O _).smul_mem hx a

theorem symIntAt (C0 CE1 CE2 : ℝ) : SymIntAt C0 CE1 CE2 := by
  intro X _ O _ _ mm β s hs
  apply inA_of_mem
  unfold symFam
  refine (IntAlg O _).prod_mem fun j _ => ?_
  unfold ioBlock
  have hX := fun v => X_mem_intAlg O (σ := (X.TT × Bool) × Fin (X.m + 1)) v
  refine (IntAlg O _).mul_mem ((IntAlg O _).mul_mem ?_ ?_) ?_
  · unfold digitMon
    exact (IntAlg O _).prod_mem fun i _ => (IntAlg O _).prod_mem fun c _ =>
      (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
  · unfold sTopMon
    refine (IntAlg O _).prod_mem fun i _ => ?_
    split_ifs
    · exact (IntAlg O _).mul_mem ((IntAlg O _).pow_mem (hX _) _) ((IntAlg O _).pow_mem (hX _) _)
    · exact (IntAlg O _).one_mem
  · have hsj : s j ∈ IntAlg O (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) :=
      ssz_le_intAlg O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) mm (β j)) (s j) (hs j)
    exact aeval_mem_intAlg O _ (fun v => (IntAlg O _).pow_mem (hX _) _) hsj

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Function

variable {s r : ℕ}

theorem strip_first [NeZero r] {nu mu : Fin r → ℤ} {g : ℕ} (h : Strip nu mu g) : nu 0 ≤ mu 0 + g := by
  obtain ⟨h1, -, h3⟩ := h
  have hs : ∑ i, (nu i - mu i) = g := by
    rw [Finset.sum_sub_distrib]
    exact h3
  have h0 := Finset.single_le_sum (f := fun i => nu i - mu i) (fun i _ => sub_nonneg.mpr (h1 i))
    (Finset.mem_univ (0 : Fin r))
  linarith

theorem sum_lt_succ (f : Fin s → ℤ) (i : Fin s) :
    (∑ x : Fin s, if x.val < i.val + 1 then f x else 0) = (∑ x : Fin s, if x.val < i.val then f x else 0) + f i := by
  have hpt : ∀ x : Fin s, (if x.val < i.val + 1 then f x else 0) =
      (if x.val < i.val then f x else 0) + (if x = i then f x else 0) := by
    intro x
    by_cases h1 : x.val < i.val
    · have h2 : x ≠ i := fun h => by rw [h] at h1; exact lt_irrefl _ h1
      have h5 : x.val < i.val + 1 := by omega
      simp [h1, h2, h5]
    · by_cases h3 : x = i
      · subst h3
        simp
      · have h4 : ¬ x.val < i.val + 1 := by
          intro h
          apply h3
          apply Fin.ext
          omega
        simp [h1, h3, h4]
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

private theorem eventually_abs_le_half_add_of_doubling_bounds [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) (m : ℕ) (hm : m < 2 * s + 1) :
    ka ⟨m + 1, by omega⟩ 0 ≤ ka ⟨m, by omega⟩ 0 + (if m % 2 = 0 then (LLv.deg ⟨m, hm⟩ : ℤ) else 0) := by
  have h := hch.2 ⟨m, hm⟩
  have e1 : (⟨m, hm⟩ : Fin (2 * s + 1)).succ = ⟨m + 1, by omega⟩ := rfl
  have e2 : (⟨m, hm⟩ : Fin (2 * s + 1)).castSucc = ⟨m, by omega⟩ := rfl
  rw [e1, e2, hv] at h
  by_cases hpar : m % 2 = 0
  · simp [hpar] at h ⊢
    exact strip_first h
  · simp [hpar] at h ⊢
    exact h.1 0

theorem row_even [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) :
    ∀ (n : ℕ) (hn : n ≤ s), ka ⟨2 * n, by omega⟩ 0 ≤
      ∑ l : Fin s, if l.val < n then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0 := by
  intro n
  induction n with
  | zero =>
    intro hn
    have h0 : ka ⟨2 * 0, by omega⟩ = 0 := hch.1
    rw [h0]
    simp
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have hs1 := hch.2 ⟨2 * n, by omega⟩
    rw [if_pos (by rw [hv]; simp)] at hs1
    have hs2 := hch.2 ⟨2 * n + 1, by omega⟩
    rw [if_neg (by rw [hv]; simp)] at hs2
    have a1 : ka ⟨2 * n + 1, by omega⟩ 0 ≤ ka ⟨2 * n, by omega⟩ 0 + (LLv.deg ⟨2 * n, by omega⟩ : ℤ) := strip_first hs1
    have a2 : ka ⟨2 * (n + 1), by omega⟩ 0 ≤ ka ⟨2 * n + 1, by omega⟩ 0 := hs2.1 0
    have hsum : (∑ l : Fin s, if l.val < n + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
        (∑ l : Fin s, if l.val < n then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) +
          (LLv.deg ⟨2 * n, by omega⟩ : ℤ) :=
      sum_lt_succ (fun l : Fin s => (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ)) ⟨n, by omega⟩
    rw [hsum]
    linarith

theorem row_odd [NeZero r] {LLv : ChainLetters (2 * s + 1)} {ka : Fin (2 * s + 1 + 1) → Fin r → ℤ}
    (hv : ∀ a, LLv.vec a = decide (a.val % 2 = 0)) (hch : IsChain LLv ka) (i : Fin s) :
    ka ⟨2 * i.val + 1, by omega⟩ 0 ≤
      ∑ l : Fin s, if l.val < i.val + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0 := by
  have h1 := eventually_abs_le_half_add_of_doubling_bounds hv hch (2 * i.val) (by omega)
  rw [if_pos (by omega)] at h1
  have h3 := row_even hv hch i.val (by omega)
  have hsum : (∑ l : Fin s, if l.val < i.val + 1 then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
      (∑ l : Fin s, if l.val < i.val then (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) +
        (LLv.deg ⟨2 * i.val, by omega⟩ : ℤ) :=
    sum_lt_succ (fun l : Fin s => (LLv.deg ⟨2 * l.val, by omega⟩ : ℤ)) i
  rw [hsum]
  linarith

def SecondKernelAtLevel (C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ) : Prop :=
  ∀ (X : Loc) [NeZero X.m], D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X →
    ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
      ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma →
        (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
          cap X.p (X.seg C0 CE1 CE2 j) b i.val ∧
        (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (b.w l : ℤ) else 0) ≤
          cap X.p (X.seg C0 CE1 CE2 j) b (i.val + 1)

theorem sTopRows_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hK : SecondKernelAtLevel C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    STopRowsAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hH hc j m hm rz ry hd z hz i hi
  have h1 := row_odd (LLv := (BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2) (fun a => rfl) hz.2.2.1 i
  have e : (∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then
        (((BD C0 CE1 CE2 X j m z.1).lettersAt z.2.1.1 z.2.1.2).deg ⟨2 * l.val, by omega⟩ : ℤ) else 0) =
      ∑ l : Fin (segS X.TT j), if l.val < i.val + 1 then (z.1.w l : ℤ) else 0 := by
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < i.val + 1
    · rw [if_pos hl, if_pos hl, levW, if_pos (by omega), jE_S _ _ (by omega), Nat.sub_zero]
    · rw [if_neg hl, if_neg hl]
  rw [e] at h1
  have h2 := hK X hD hH hc j z.1 hz.1.1 i hi
  exact ⟨le_trans h1 h2.1, le_trans h1 h2.2⟩

def LeadingRowsBeyondThreshold : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SecondKernelAtLevel C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restSTopRows_of (h : LeadingRowsBeyondThreshold) : RestSTopRows :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ hK => sTopRows_of hK) h

theorem upper_count_of_top_rows (hCD : ChainDimAt) (hNB : NumBranchAt) (h : LeadingRowsBeyondThreshold) : RestCountUp :=
  restCountUp_of_STop hCD hNB (restSTopRows_of h)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

