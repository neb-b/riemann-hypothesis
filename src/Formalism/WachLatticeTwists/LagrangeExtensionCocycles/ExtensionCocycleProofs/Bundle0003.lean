module

public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.GrothendieckTopDegree
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.Bundle0002
public import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.SecondDescentFreePartHolds

@[expose] public section

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.LiftExistsSecondCase
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

open Polynomial Formalism.CoboundaryTransfers

section

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℤ_[ℓ] A} {M : ℕ}
  {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']

def gbase (B : Base ℤ_[ℓ] A) (u : ℤ_[ℓ]ˣ) (h : B.GammaX (u : ℤ_[ℓ])) : GBase ℓ A :=
  { γ := B.γ, X := B.X, u := u, γX := h }

def pairOfHom {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) : GPair (gbase B u h) D' :=
  { N := W'.N
    N' := W.N.map F.f
    le := by rintro _ ⟨x, hx, rfl⟩; exact F.N_le x hx
    γ := W'.γ
    γ_smul := W'.γ_smul
    X_inj := W'.X_inj
    γ_N := W'.γ_N
    γ_N' := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨x', hx', h⟩ := W.γ_N x hx
      exact ⟨F.f x', ⟨x', hx', rfl⟩, by rw [← F.γ_comm, ← map_sub, h, map_smul]; rfl⟩ }

theorem kills_iff {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (a : A) :
    (pairOfHom F u h).Kills a ↔ ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = a • n := by
  constructor
  · intro hk n hn
    obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.1 (hk n hn)
    exact ⟨x, hx, hfx⟩
  · intro h' n hn
    obtain ⟨x, hx, hfx⟩ := h' n hn
    exact Submodule.mem_map.2 ⟨x, hx, hfx⟩

theorem natCast_pow_smul (e : ℕ) (n : D) : ((ℓ : A) ^ e) • n = ((ℓ : ℤ_[ℓ]) ^ e) • n := by
  rw [← map_natCast (algebraMap ℤ_[ℓ] A), ← map_pow, algebraMap_smul]

theorem homKillsB {W : WachMod B M D} {W' : WachMod B M D'} (F : Hom W W') (u : ℤ_[ℓ]ˣ)
    (h : B.GammaX (u : ℤ_[ℓ])) (s a : ℕ) (hs : 1 ≤ s) (h2 : ℓ = 2 → 2 ≤ s)
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = s) (hK : XKills F a) :
    ∀ n ∈ W'.N, ∃ n₁ ∈ W.N, F.f n₁ = ((ℓ : ℤ_[ℓ]) ^ eWB ℓ a s) • n := by
  have := unit_lemma_case_b_holds ℓ A (gbase B u h) D' (pairOfHom F u h) s a hs h2 hv ((kills_iff F u h _).2 hK)
  intro n hn
  obtain ⟨n₁, hn₁, e⟩ := (kills_iff F u h _).1 this n hn
  exact ⟨n₁, hn₁, by rw [e, natCast_pow_smul]⟩

theorem aeval_mem (N : Submodule ℤ_[ℓ] D) (γ : D →ₗ[ℤ_[ℓ]] D) (h : ∀ n ∈ N, γ n ∈ N)
    (R : ℤ_[ℓ][X]) : ∀ n ∈ N, aeval γ R n ∈ N := by
  induction R using Polynomial.induction_on with
  | C a =>
    intro n hn
    rw [aeval_C, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact N.smul_mem a hn
  | add p q hp hq =>
    intro n hn
    rw [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem (hp n hn) (hq n hn)
  | monomial k a ih =>
    intro n hn
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, Module.End.mul_apply]
    exact ih _ (h n hn)

theorem zero_notMem_JSet (jumps : Finset ℤ) (M : ℕ) : (0 : ℤ) ∉ JSet jumps M := by
  simp [JSet]

theorem eigSet_subset (jumps : Finset ℤ) (M : ℕ) : eigSet jumps M ⊆ insert 0 (JSet jumps M) := by
  intro x hx
  by_cases h0 : x = 0
  · exact Finset.mem_insert.2 (Or.inl h0)
  · exact Finset.mem_insert.2 (Or.inr (Finset.mem_union.2 (Or.inl (Finset.mem_erase.2 ⟨h0, hx⟩))))

theorem prod_eig_dvd (jumps : Finset ℤ) (M : ℕ) (f : ℤ → ℤ_[ℓ][X]) :
    (∏ j ∈ eigSet jumps M, f j) ∣ f 0 * ∏ j ∈ JSet jumps M, f j := by
  have h := Finset.prod_dvd_prod_of_subset _ _ f (eigSet_subset jumps M)
  rwa [Finset.prod_insert (zero_notMem_JSet jumps M)] at h

end

theorem lift_exists_second_case : StatLiftB := by
  intro ℓ _ A _ _ B M u s H jumps hp hφX hγX hγQ hs h2 hv D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S
    H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g I _ hQI hφI hRX hRL hNT hXK hSemi hNat hC1 hC2 hInj hE1 hE2 hRO
  set eW := eWB ℓ H s with heW

  have hCK : CokerKilled S eW := by
    intro n hn
    rw [hp]
    exact homKillsB S.π u hγX s H hs h2 hv hXK n hn

  have hInt₁ : ∀ κ ∈ Hf₁, ∃ pr : W₁.Z1, W₁.Cocycle (pr : D₁ × D₁).1 (pr : D₁ × D₁).2 ∧
      cl₁ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE1 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₁ W₁ H₁ cl₁ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)
  have hInt₂ : ∀ κ ∈ Hf₂, ∃ pr : W₂.Z1, W₂.Cocycle (pr : D₂ × D₂).1 (pr : D₂ × D₂).2 ∧
      cl₂ pr = ((ℓ : ℤ_[ℓ]) ^ eW) • κ := by
    intro κ hκ
    obtain ⟨E, hEK, hED⟩ := hE2 κ hκ
    exact extension_class_is_cocycle ℓ A B M D₂ W₂ H₂ cl₂ κ E eW hED (homKillsB E.S.π u hγX s H hs h2 hv hEK)

  have hRS : RatSurj S :=
    rational_points_map_surjective ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW hp hNat hC2 hInj hRO hInt₁

  have h1 := phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I 1 (M + 1) ⟨1, by rw [hφX]; ring⟩ (by omega) hQI hφI

  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], W₀.γ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : W₀.γ n = n + B.X • x' := by rw [← h]; abel
    rw [this]
    exact W₀.N.add_mem hn (W₀.N.smul_mem _ hx')
  have h3 : ∀ y, W₀.QInv y → aeval W₀.γ ((X - 1) *
      ∏ j ∈ JSet jumps M, (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R, hR⟩ := prod_eig_dvd jumps M (fun j => (X - C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))))
    have e0 : (X - C (((u ^ (-(0 : ℤ)) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) : ℤ_[ℓ][X]) = X - 1 := by simp
    simp only [e0] at hR
    rw [hR, mul_comm, map_mul, Module.End.mul_apply]
    exact aeval_mem _ W₀.γ hstab R _ (hSemi y hy)
  have hL : Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + Formalism.LIFT.eU ℓ M s (JSet jumps M))) :=
    wachLatticeUnramified_statement ℓ A B M u hp hφX hγX hγQ D₀ D₁ D₂ W₀ W₁ W₂ S eW s (JSet jumps M) hs h2 hv
      (zero_notMem_JSet jumps M) h1 (regulator_bound_for_x ℓ A B M D₀ W₀ hRX) h3
      (regulator_bound_for_l ℓ A B M D₀ W₀ hRL hNT) hCK hRS
  intro κ hκ
  obtain ⟨κ₁, hκ₁, h⟩ := finiteClassesLift_holds ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S H₁ H₂ cl₁ cl₂ Hf₁ Hf₂ g eW _
    hNat hC1 ⟨hC2, by rw [hp]; exact hInt₂⟩ hL κ hκ
  refine ⟨κ₁, hκ₁, ?_⟩
  rw [h, hp, ← pow_add]
  congr 2
  simp only [eUB, Formalism.LIFT.eU]
  ring

end Formalism.RepresentationBoundsCohomology.N2
end
end

-- bundled from Formalism.WachLatticeTwists.LagrangeExtensionCocycles.ExtensionCocycleProofs.TotallyRealRoots
section
noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N2

theorem cost_formula_holds : StatCostFormula := by
  intro ℓ _ hℓ2 j s hjs
  have hℓ : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  have hd : 0 < ℓ - 1 := by omega
  induction s, hjs using Nat.le_induction with
  | base => simp [cost]
  | succ s hjs ih =>
    have hI : Finset.Ioc j (s + 1) = insert (s + 1) (Finset.Ioc j s) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_insert]
      omega
    have hnot : s + 1 ∉ Finset.Ioc j s := by simp
    have hc : cost ℓ j (s + 1) =
        cost ℓ j s + (if (ℓ - 1) ∣ (s + 1) then 1 + padicValNat ℓ (s + 1) else 0) := by
      unfold cost
      rw [hI, Finset.sum_insert hnot, add_comm]
    rw [hc]
    by_cases hdv : (ℓ - 1) ∣ (s + 1)
    · rw [if_pos hdv]
      have hq : (s + 1) / (ℓ - 1) = s / (ℓ - 1) + 1 := Nat.succ_div_of_dvd hdv
      have hjq : j / (ℓ - 1) ≤ s / (ℓ - 1) := Nat.div_le_div_right hjs
      have hmul : s + 1 = (ℓ - 1) * (s / (ℓ - 1) + 1) := by
        rw [← hq]
        exact (Nat.mul_div_cancel' hdv).symm
      have hv0 : padicValNat ℓ (ℓ - 1) = 0 := by
        rw [Nat.padicValNat_def]
        exact padicValNat.eq_zero_of_not_dvd (fun h => by have := Nat.le_of_dvd hd h; omega)
      have hv : padicValNat ℓ (s + 1) = padicValNat ℓ (s / (ℓ - 1) + 1) := by
        rw [hmul, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.pos_iff_ne_zero.1 hd) (Nat.succ_ne_zero _), hv0, zero_add]
      have hf : padicValNat ℓ (s / (ℓ - 1) + 1).factorial =
          padicValNat ℓ (s / (ℓ - 1) + 1) + padicValNat ℓ (s / (ℓ - 1)).factorial := by
        rw [Nat.factorial_succ, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _)]
      rw [hq, hv, hf]
      omega
    · rw [if_neg hdv, add_zero, Nat.succ_div_of_not_dvd hdv]
      exact ih

theorem cost_bound : StatCostBound := by
  intro ℓ _ hℓ j s H hjs hsH
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  have hform := cost_formula_holds ℓ hℓ j s hjs
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hform
  have hL2 : 2 ≤ L := by omega
  set k0 := j / L with hk0
  set k1 := s / L with hk1
  have hk01 : k0 ≤ k1 := Nat.div_le_div_right hjs
  obtain ⟨n', hn'⟩ : ∃ n', k1 = k0 + n' := ⟨k1 - k0, by omega⟩
  have hch := Nat.choose_mul_factorial_mul_factorial hk01
  have hvch : padicValNat (L + 1) k1.factorial = padicValNat (L + 1) (k1.choose k0) +
      padicValNat (L + 1) k0.factorial + padicValNat (L + 1) n'.factorial := by
    rw [← hch, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.mul_ne_zero (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _), (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.choose_pos hk01).ne' (Nat.factorial_ne_zero _),
      show k1 - k0 = n' by omega]
  have hcost : cost (L + 1) j s = n' + padicValNat (L + 1) n'.factorial +
      padicValNat (L + 1) (k1.choose k0) := by omega
  have hLr : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL2
  have hsub : (((L + 1 : ℕ) : ℝ) - 1) = L := by push_cast; ring
  have hb1 : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hHr : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hlog0 : 0 ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := Real.logb_nonneg hb1 (by linarith)
  have hjsr : (j : ℝ) ≤ s := by exact_mod_cast hjs
  rw [hsub]
  have hpos : (0 : ℝ) < (L : ℝ) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos n' with h0 | hpos'
  · have : cost (L + 1) j s = 0 := by
      rw [hcost, h0, hn', h0]; simp [Nat.padicValNat_def]
    rw [this]
    have : 0 ≤ ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 := by
      apply div_nonneg _ hpos.le
      apply mul_nonneg (by linarith) (by linarith)
    push_cast at this hlog0 ⊢
    linarith
  ·
    have hw : L * padicValNat (L + 1) n'.factorial < n' := by
      have := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := L + 1) (n := n') hpos'.ne'
      simpa [Nat.padicValNat_def] using this
    have hc : padicValNat (L + 1) (k1.choose k0) ≤ Nat.log (L + 1) k1 := by
      rw [Nat.padicValNat_def, ← Nat.factorization_def _ hprime]
      exact Nat.factorization_choose_le_log
    have hk1pos : 1 ≤ k1 := by
      rw [hn']; exact le_trans hpos' (Nat.le_add_left _ _)
    have hk1H : k1 ≤ H := le_trans (Nat.div_le_self _ _) hsH
    have hlog : (Nat.log (L + 1) k1 : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) := by
      refine le_trans (Real.natLog_le_logb _ _) ?_
      apply Real.logb_le_logb_of_le hb1
      · exact_mod_cast hk1pos
      · have : (k1 : ℝ) ≤ H := by exact_mod_cast hk1H
        linarith
    have h1 : L * k1 ≤ s := Nat.mul_div_le s L
    have h2 : j < L * k0 + L := by
      have := Nat.lt_mul_div_succ j (show 0 < L by omega)
      rw [← hk0] at this
      nlinarith
    have hA : L * n' + j + 1 ≤ s + L := by
      have : L * k1 = L * k0 + L * n' := by rw [hn']; ring
      omega
    set w := padicValNat (L + 1) n'.factorial with hwdef
    set c := padicValNat (L + 1) (k1.choose k0) with hcdef
    have rA : (L : ℝ) * n' + j + 1 ≤ s + L := by exact_mod_cast hA
    have rB : (L : ℝ) * w + 1 ≤ n' := by exact_mod_cast hw
    have rC : (c : ℝ) ≤ Real.logb ((L + 1 : ℕ) : ℝ) ((H : ℝ) + 1) :=
      le_trans (by exact_mod_cast hc) hlog
    have key : ((n' : ℝ) + w) < ((s : ℝ) - j) * ((L + 1 : ℕ) : ℝ) / (L : ℝ) ^ 2 + 1 := by
      rw [← sub_lt_iff_lt_add, lt_div_iff₀ hpos]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left rA (by linarith : (0 : ℝ) ≤ L),
        mul_le_mul_of_nonneg_left rB (by linarith : (0 : ℝ) ≤ L)]
    rw [hcost]
    push_cast at key rC ⊢
    linarith

theorem unconditional_first_statement : Stat1 := first_descent_of_cost_bound cost_bound

theorem unit_lemma_case_a_unconditional : StatWA := wA_of unconditional_first_statement

end Formalism.RepresentationBoundsCohomology.N2
end
end

