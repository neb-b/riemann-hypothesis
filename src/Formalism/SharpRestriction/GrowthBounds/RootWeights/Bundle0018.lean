module

public import Formalism.SharpRestriction.GrowthBounds.RootWeights.Bundle0014

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightDifferenceLeEllOfRep
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem mem_weightSp_iff (E : GLOps n K V) (μ : Fin n → ℤ) (x : V) :
    x ∈ weightSp E μ ↔ ∀ c, E c c x = (μ c : K) • x := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

private theorem E_apply_mem_weightSp_add_rootW_of_ne {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n} (hab : a ≠ b)
    {μ : Fin n → ℤ} {x : V} (hx : x ∈ weightSp E μ) : E a b x ∈ weightSp E (μ + rootW a b) := by
  rw [mem_weightSp_iff] at hx ⊢
  intro c
  have hc := LinearMap.congr_fun (hE.1 c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hx c, map_smul] at hc
  rw [sub_eq_iff_eq_add] at hc
  by_cases h1 : c = a
  · have h2 : ¬ b = c := fun h => hab (h1.symm.trans h.symm)
    rw [if_pos h1, if_neg h2, h1] at hc
    rw [h1] at *
    simp only [LinearMap.zero_apply, sub_zero] at hc
    rw [hc]
    simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hab, if_false,
      sub_zero, Int.cast_add, Int.cast_one, add_smul, one_smul]
    abel
  · by_cases h2 : b = c
    · rw [if_neg h1, if_pos h2] at hc
      subst h2
      simp only [LinearMap.zero_apply, zero_sub] at hc
      rw [hc]
      simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply,
        Ne.symm hab, if_false, zero_sub, Int.cast_add, Int.cast_neg, Int.cast_one, add_smul,
        neg_smul, one_smul]
      abel
    · rw [if_neg h1, if_neg h2] at hc
      simp only [LinearMap.zero_apply, sub_zero, zero_add] at hc
      rw [hc]
      have h2' : c ≠ b := fun h => h2 h.symm
      simp only [rootW, Pi.add_apply, Pi.sub_apply, Pi.single_apply, h1, h2', if_false, sub_zero,
        add_zero]

private theorem E_pow_apply_mem_weightSp_ne_zero_of_highest [CharZero K] {E : GLOps n K V} (hE : IsGLRep E) {a b : Fin n}
    (hab : a ≠ b) {μ : Fin n → ℤ} {v : V} (hv : v ∈ weightSp E μ) (hv0 : v ≠ 0)
    (htop : E a b v = 0) (N : ℕ) (hN : (N : ℤ) = μ a - μ b) :
    (E b a ^ N) v ∈ weightSp E (μ + (N : ℤ) • rootW b a) ∧ (E b a ^ N) v ≠ 0 := by
  have hNK : (N : K) = (μ a : K) - (μ b : K) := by exact_mod_cast hN
  have hlow : ∀ k : ℕ, (E b a ^ k) v ∈ weightSp E (μ + (k : ℤ) • rootW b a) := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have h := E_apply_mem_weightSp_add_rootW_of_ne hE (Ne.symm hab) ih
      have e : μ + ((k + 1 : ℕ) : ℤ) • rootW b a = μ + (k : ℤ) • rootW b a + rootW b a := by
        push_cast
        rw [add_smul, one_smul, add_assoc]
      rw [pow_succ', Module.End.mul_apply, e]
      exact h
  have hcomm : ∀ w : V, E a b (E b a w) = E b a (E a b w) + (E a a w - E b b w) := by
    intro w
    have h := LinearMap.congr_fun (hE.1 a b b a) w
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    exact sub_eq_iff_eq_add'.1 h
  have hdiag : ∀ k : ℕ, E a a ((E b a ^ k) v) - E b b ((E b a ^ k) v) =
      ((N : K) - 2 * k) • (E b a ^ k) v := by
    intro k
    have h := (mem_weightSp_iff E _ _).1 (hlow k)
    rw [h a, h b, ← sub_smul]
    congr 1
    simp only [rootW, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply,
      hab, Ne.symm hab, if_false, smul_eq_mul]
    push_cast
    rw [hNK]
    ring
  have hQ : ∀ k : ℕ, E a b ((E b a ^ (k + 1)) v) = (((k : K) + 1) * ((N : K) - k)) • (E b a ^ k) v := by
    intro k
    induction k with
    | zero =>
      have h0 := hdiag 0
      simp only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, sub_zero] at h0
      simp only [zero_add, pow_one, pow_zero, Module.End.one_apply, Nat.cast_zero, sub_zero, one_mul]
      rw [hcomm, htop, map_zero, zero_add, h0]
    | succ k ih =>
      have fold : E b a ((E b a ^ k) v) = (E b a ^ (k + 1)) v := by
        rw [pow_succ', Module.End.mul_apply]
      rw [pow_succ' (E b a) (k + 1), Module.End.mul_apply, hcomm, ih, map_smul, fold, hdiag (k + 1),
        ← add_smul]
      congr 1
      push_cast
      ring
  have hne : ∀ k : ℕ, k ≤ N → (E b a ^ k) v ≠ 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hv0
    | succ k ih =>
      intro hk h
      apply ih (by omega)
      have hq := hQ k
      rw [h, map_zero] at hq
      have hc : ((k : K) + 1) * ((N : K) - k) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast Nat.succ_ne_zero k
        · exact sub_ne_zero.2 (by exact_mod_cast (show N ≠ k by omega))
      exact (smul_eq_zero.1 hq.symm).resolve_left hc
  exact ⟨hlow N, hne N le_rfl⟩

private theorem finite_set_of_nonzero_weightSp [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) :
    {μ : Fin n → ℤ | weightSp E μ ≠ ⊥}.Finite := by
  have hfin : ∀ c : Fin n, {z : ℤ | (E c c).HasEigenvalue (z : K)}.Finite := fun c =>
    (Module.End.finite_hasEigenvalue (E c c)).preimage Int.cast_injective.injOn
  refine (Set.Finite.pi (t := fun c => {z : ℤ | (E c c).HasEigenvalue (z : K)}) hfin).subset ?_
  intro μ hμ
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  rw [mem_weightSp_iff] at hx
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_ofPred_eq, true_implies]
  intro c
  exact Module.End.hasEigenvalue_of_hasEigenvector
    (Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 (hx c), hx0⟩)

theorem root_string_through_weight [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (ν : Fin n → ℤ)
    (hν : weightSp E ν ≠ ⊥) (a b : Fin n) (hab : a ≠ b) (hpos : 0 < ν a - ν b) :
    ∃ t N : ℕ, (N : ℤ) = ν a - ν b + 2 * t ∧ weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥ ∧
      weightSp E (ν + (t : ℤ) • rootW a b + (N : ℤ) • rootW b a) ≠ ⊥ := by
  classical
  have hinj : Function.Injective (fun t : ℕ => ν + (t : ℤ) • rootW a b) := by
    intro t1 t2 h
    have h' := congr_fun h a
    simp [rootW, hab] at h'
    exact_mod_cast h'
  obtain ⟨T, hTdef⟩ : ∃ T : Set ℕ, T = {t : ℕ | weightSp E (ν + (t : ℤ) • rootW a b) ≠ ⊥} := ⟨_, rfl⟩
  have hT : T.Finite := by
    rw [hTdef]
    exact (finite_set_of_nonzero_weightSp E).preimage hinj.injOn
  have h0 : (0 : ℕ) ∈ T := by
    rw [hTdef]
    simpa using hν
  have ht : sSup T ∈ T := Nat.sSup_mem ⟨0, h0⟩ hT.bddAbove
  have ht1 : sSup T + 1 ∉ T := fun h => by
    have := le_csSup hT.bddAbove h
    omega
  have ht' : weightSp E (ν + ((sSup T : ℕ) : ℤ) • rootW a b) ≠ ⊥ := (Set.ext_iff.1 hTdef _).1 ht
  have ht1' : ¬ weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) ≠ ⊥ :=
    fun h => ht1 ((Set.ext_iff.1 hTdef _).2 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ht'
  have htop : E a b v = 0 := by
    have h1 := E_apply_mem_weightSp_add_rootW_of_ne hE hab hv
    have e : ν + ((sSup T : ℕ) : ℤ) • rootW a b + rootW a b =
        ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b := by
      push_cast
      rw [add_smul, one_smul, add_assoc]
    rw [e] at h1
    have hbot : weightSp E (ν + ((sSup T + 1 : ℕ) : ℤ) • rootW a b) = ⊥ := by
      by_contra hne
      exact ht1' hne
    rw [hbot, Submodule.mem_bot] at h1
    exact h1
  have hμa : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) a = ν a + sSup T := by
    simp [rootW, hab]
  have hμb : (ν + ((sSup T : ℕ) : ℤ) • rootW a b) b = ν b - sSup T := by
    simp [rootW, Ne.symm hab]
    ring
  have hnn : 0 ≤ ν a - ν b + 2 * ((sSup T : ℕ) : ℤ) := by omega
  refine ⟨sSup T, (ν a - ν b + 2 * ((sSup T : ℕ) : ℤ)).toNat, Int.toNat_of_nonneg hnn, ht', ?_⟩
  obtain ⟨hmem, hne⟩ := E_pow_apply_mem_weightSp_ne_zero_of_highest hE hab hv hv0 htop _
    (by rw [Int.toNat_of_nonneg hnn, hμa, hμb]; ring)
  intro hbot
  rw [hbot, Submodule.mem_bot] at hmem
  exact hne hmem

theorem root_differences_bddAbove_top [CharZero K] [FiniteDimensional K V] (E : GLOps n K V) :
    BddAbove {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b, a ≠ b ∧
      mu - nu = (k : ℤ) • rootW a b} := by
  classical
  have hW := finite_set_of_nonzero_weightSp E
  have hsub : {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V), ∃ a b,
      a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} ⊆
      (fun p : (Fin n → ℤ) × (Fin n → ℤ) × Fin n => (p.1 p.2.2 - p.2.1 p.2.2).toNat) ''
        ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ ({μ : Fin n → ℤ | weightSp E μ ≠ ⊥} ×ˢ Set.univ)) := by
    rintro k ⟨mu, hmu, nu, hnu, a, b, hab, h⟩
    have hmu' : weightSp E mu ≠ ⊥ := by simpa [wtsOf] using hmu
    have hnu' : weightSp E nu ≠ ⊥ := by simpa [wtsOf] using hnu
    refine ⟨(mu, nu, a), ⟨hmu', hnu', Set.mem_univ _⟩, ?_⟩
    have h' := congr_fun h a
    simp [rootW, hab] at h'
    simp [h']
  exact ((hW.prod (hW.prod Set.finite_univ)).image _).subset hsub |>.bddAbove

theorem weight_difference_le_ell_of_rep [CharZero K] [FiniteDimensional K V] {E : GLOps n K V} (hE : IsGLRep E) (ν : Fin n → ℤ)
    (hν : weightSp E ν ≠ ⊥) (a b : Fin n) (hab : a ≠ b) (hpos : 0 < ν a - ν b) :
    ν a - ν b ≤ (ellOf E (⊤ : Submodule K V) : ℤ) := by
  obtain ⟨t, N, hN, h1, h2⟩ := root_string_through_weight hE ν hν a b hab hpos
  have hr : rootW b a = -rootW a b := by
    ext c
    simp only [rootW, Pi.sub_apply, Pi.neg_apply]
    ring
  have hmem : N ∈ {k : ℕ | ∃ mu ∈ wtsOf E (⊤ : Submodule K V), ∃ nu ∈ wtsOf E (⊤ : Submodule K V),
      ∃ a b, a ≠ b ∧ mu - nu = (k : ℤ) • rootW a b} := by
    refine ⟨_, by simpa [wtsOf] using h1, _, by simpa [wtsOf] using h2, a, b, hab, ?_⟩
    rw [hr]
    ext c
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul,
      Pi.natCast_apply]
    ring
  have hle : N ≤ ellOf E (⊤ : Submodule K V) := le_csSup (root_differences_bddAbove_top E) hmem
  have hle' := (Nat.cast_le (α := ℤ)).2 hle
  omega

end Formalism.MainNotions.G.GLWeightTheory
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.RootWeights.WeightProjectionPreservesLattice
section
noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section pw
variable {n : ℕ} {K : Type} [Field K] {L W : Type} [AddCommGroup L] [Module K L] [AddCommGroup W] [Module K W]

theorem llcomp_pow_apply (X : Module.End K W) (m : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.llcomp K L W W X) ^ m) f = (X ^ m) ∘ₗ f := by
  induction m generalizing f with
  | zero =>
    ext x
    simp
  | succ m ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]
    rfl

theorem lcomp_pow_apply (Y : Module.End K L) (j : ℕ) (f : L →ₗ[K] W) :
    ((LinearMap.lcomp K W Y) ^ j) f = f ∘ₗ (Y ^ j) := by
  induction j generalizing f with
  | zero =>
    ext x
    simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    rfl

theorem homRepresentation_pow_apply (EL : GLOps n K L) (E : GLOps n K W) (a b : Fin n) (k : ℕ) (f : L →ₗ[K] W) (x : L) :
    ((homRepresentation EL E a b) ^ k) f x =
      ∑ m ∈ range (k + 1), ((k.choose m : K) * (-1) ^ (k - m)) • (E a b ^ m) (f ((EL a b ^ (k - m)) x)) := by
  have hc : Commute (LinearMap.llcomp K L W W (E a b)) ((-1 : K) • LinearMap.lcomp K W (EL a b)) := by
    refine Commute.smul_right ?_ (-1 : K)
    ext g y
    rfl
  have ht : homRepresentation EL E a b =
      LinearMap.llcomp K L W W (E a b) + (-1 : K) • LinearMap.lcomp K W (EL a b) := by
    rw [neg_one_smul, ← sub_eq_add_neg]
    rfl
  rw [ht, hc.add_pow, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Module.End.mul_apply, Module.End.natCast_apply, smul_pow, LinearMap.smul_apply,
    map_nsmul, map_smul, llcomp_pow_apply, lcomp_pow_apply, LinearMap.comp_apply]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul]

end pw

section lat
variable {n : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {W : Type} [AddCommGroup W] [Module (KK O) W] [Module O W] [IsScalarTower O (KK O) W]

theorem restrictRepresentation_pow_coe (E : GLOps n (KK O) W) (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (j : ℕ)
    (x : L) : (((restrictRepresentation E L hL a b) ^ j) x : W) = (E a b ^ j) (x : W) := by
  induction j generalizing x with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
    rfl

theorem int_smul_mem_lattice (M : Submodule O W) (z : ℤ) {x : W} (hx : x ∈ M) : ((z : ℤ) : KK O) • x ∈ M := by
  rw [Int.cast_smul_eq_zsmul]
  exact zsmul_mem hx z

theorem weightProjection_preserves_lattice [CharZero (KK O)] [FiniteDimensional (KK O) W] (E : GLOps n (KK O) W) (hE : IsGLRep E)
    (M : Submodule O W) (hM : UZStable (O := O) E M) (mu : Fin n → ℤ) (π : Module.End (KK O) W)
    (hπ : IsWtProj E mu π) : ∀ x ∈ M, π x ∈ M := by
  classical
  obtain ⟨sh, shwt, shM⟩ : ∃ sh : Fin n → ℤ → ℕ → Module.End (KK O) W,
      (∀ a c d ρ x, x ∈ weightSp E ρ → sh a c d x = ((Ring.choose (ρ a + c) d : ℤ) : KK O) • x) ∧
      (∀ a c d x, x ∈ M → sh a c d x ∈ M) := by
    refine ⟨fun a c d => ∑ ij ∈ antidiagonal d, ((Ring.choose c ij.2 : ℤ) : KK O) • binomE E a ij.1,
      ?_, ?_⟩
    · intro a c d ρ x hx
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, binomial_diagonal_apply_weight E a ρ x hx, smul_smul]
      rw [← Finset.sum_smul, Ring.add_choose_eq d (Commute.all _ _)]
      push_cast
      congr 1
      exact Finset.sum_congr rfl fun ij _ => by ring
    · intro a c d x hx
      rw [LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun ij _ => ?_
      rw [LinearMap.smul_apply]
      exact int_smul_mem_lattice M _ (hM _ (Or.inr ⟨a, ij.1, rfl⟩) x hx)
  have hT : ∀ nu : Fin n → ℤ, ∃ (T : Module.End (KK O) W) (h : (Fin n → ℤ) → ℤ), h mu = 1 ∧
      (nu ≠ mu → h nu = 0) ∧ (∀ ρ, ∀ x ∈ weightSp E ρ, T x = ((h ρ : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, T x ∈ M := by
    intro nu
    by_cases hne : nu = mu
    · refine ⟨1, fun _ => 1, rfl, fun h => absurd hne h, fun ρ x _ => by simp, fun x hx => by simpa using hx⟩
    · obtain ⟨a, ha⟩ := Function.ne_iff.1 hne
      rcases lt_or_gt_of_ne ha with hlt | hgt
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, mu a - nu a = (d : ℤ) := ⟨(mu a - nu a).toNat, by omega⟩
        have hd0 : 0 < d := by omega
        refine ⟨sh a (-(nu a)) d, fun ρ => Ring.choose (ρ a + -(nu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(nu a)) d = 1
          rw [show mu a + -(nu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast, Nat.choose_self]
          rfl
        · intro _
          show Ring.choose (nu a + -(nu a)) d = 0
          rw [show nu a + -(nu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro ρ x hx
          exact shwt a _ _ ρ x hx
        · intro x hx
          exact shM a _ _ x hx
      · obtain ⟨d, hd⟩ : ∃ d : ℕ, nu a - mu a = (d : ℤ) := ⟨(nu a - mu a).toNat, by omega⟩
        refine ⟨sh a (-(mu a)) 0 - sh a (-(mu a)) d,
          fun ρ => Ring.choose (ρ a + -(mu a)) 0 - Ring.choose (ρ a + -(mu a)) d, ?_, ?_, ?_, ?_⟩
        · show Ring.choose (mu a + -(mu a)) 0 - Ring.choose (mu a + -(mu a)) d = 1
          have hd0 : 0 < d := by omega
          rw [Ring.choose_zero_right, show mu a + -(mu a) = ((0 : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_eq_zero_of_lt hd0]
          rfl
        · intro _
          show Ring.choose (nu a + -(mu a)) 0 - Ring.choose (nu a + -(mu a)) d = 0
          rw [Ring.choose_zero_right, show nu a + -(mu a) = ((d : ℕ) : ℤ) by omega, Ring.choose_natCast,
            Nat.choose_self]
          rfl
        · intro ρ x hx
          rw [LinearMap.sub_apply, shwt a _ _ ρ x hx, shwt a _ _ ρ x hx, ← sub_smul]
          push_cast
          rfl
        · intro x hx
          rw [LinearMap.sub_apply]
          exact M.sub_mem (shM a _ _ x hx) (shM a _ _ x hx)
  have hproj : ∀ F : Finset (Fin n → ℤ), ∃ (P : Module.End (KK O) W) (g : (Fin n → ℤ) → ℤ), g mu = 1 ∧
      (∀ nu ∈ F, nu ≠ mu → g nu = 0) ∧ (∀ nu, ∀ x ∈ weightSp E nu, P x = ((g nu : ℤ) : KK O) • x) ∧
      ∀ x ∈ M, P x ∈ M := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      exact ⟨1, fun _ => 1, rfl, by simp, fun nu x _ => by simp, fun x hx => by simpa using hx⟩
    | insert nu F hnu ih =>
      obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := ih
      obtain ⟨T, h, hh1, hh0, hhw, hhM⟩ := hT nu
      refine ⟨T * P, fun ρ => h ρ * g ρ, by simp [hh1, hg1], ?_, ?_, ?_⟩
      · intro ν hν hne
        rcases Finset.mem_insert.1 hν with rfl | hν'
        · simp [hh0 hne]
        · simp [hg0 ν hν' hne]
      · intro ρ x hx
        rw [Module.End.mul_apply, hgw ρ x hx, map_smul, hhw ρ x hx, smul_smul]
        congr 1
        push_cast
        ring
      · intro x hx
        exact hhM _ (hgM x hx)
  obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n → ℤ), (⊤ : Submodule (KK O) W) ≤ ⨆ nu ∈ F, weightSp E nu := by
    let bs := Module.finBasis (KK O) W
    have hb : ∀ i, ∃ s : Finset (Fin n → ℤ), bs i ∈ ⨆ nu ∈ s, weightSp E nu := by
      intro i
      apply Submodule.mem_iSup_iff_exists_finset.1
      rw [hE.2.2]
      exact Submodule.mem_top
    choose s hs using hb
    refine ⟨Finset.univ.biUnion s, ?_⟩
    rw [← bs.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hmono : (⨆ nu ∈ s i, weightSp E nu) ≤ ⨆ nu ∈ Finset.univ.biUnion s, weightSp E nu :=
      biSup_mono fun nu hnu => Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hnu⟩
    exact hmono (hs i)
  obtain ⟨P, g, hg1, hg0, hgw, hgM⟩ := hproj F
  have hπP : π = P := by
    have hle : (⨆ nu ∈ F, weightSp E nu) ≤ LinearMap.ker (π - P) := by
      refine iSup₂_le fun nu hnu => ?_
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, hgw nu x hx]
      by_cases h : nu = mu
      · subst h
        rw [hπ.1 x hx, hg1]
        simp
      · rw [hπ.2 nu h x hx, hg0 nu hnu h]
        simp
    ext x
    have hx := hle (hF (Submodule.mem_top (x := x)))
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at hx
    exact hx
  intro x hx
  rw [hπP]
  exact hgM x hx

theorem homLattice_dividedPower_stable [CharZero (KK O)] (E : GLOps n (KK O) W) (M : Submodule O W) (hM : UZStable (O := O) E M)
    (L : Submodule (KK O) W) (hL : IsSubrepresentation E L) (a b : Fin n) (hab : a ≠ b) (k : ℕ)
    (f : L →ₗ[KK O] W) (hf : f ∈ homLattice M L) :
    divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f ∈ homLattice M L := by
  have hf' : ∀ y : L, (y : W) ∈ M → f y ∈ M := hf
  show ∀ x : L, (x : W) ∈ M → divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x ∈ M
  intro x hx
  have hexp : divPowE (homRepresentation (restrictRepresentation E L hL) E) a b k f x =
      ∑ m ∈ range (k + 1), (((-1 : ℤ) ^ (k - m) : ℤ) : KK O) •
        divPowE E a b m (f ((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x)) := by
    rw [divPowE, LinearMap.smul_apply, LinearMap.smul_apply, homRepresentation_pow_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    simp only [divPowE, LinearMap.smul_apply, map_smul, smul_smul]
    congr 1
    have hc : ((k.choose m : ℕ) : KK O) * (m.factorial : KK O) * ((k - m).factorial : KK O) =
        (k.factorial : KK O) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hmk
    have h1 : (m.factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have h2 : ((k - m).factorial : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero (k - m))
    rw [← hc]
    have h3 : ((k.choose m : ℕ) : KK O) ≠ 0 := Nat.cast_ne_zero.2 (Nat.choose_pos hmk).ne'
    push_cast
    field_simp
  rw [hexp]
  refine Submodule.sum_mem _ fun m _ => ?_
  apply int_smul_mem_lattice
  have hy : (((((k - m).factorial : KK O)⁻¹) • ((restrictRepresentation E L hL a b) ^ (k - m)) x : L) : W) =
      divPowE E a b (k - m) (x : W) := by
    rw [Submodule.coe_smul, restrictRepresentation_pow_coe, divPowE, LinearMap.smul_apply]
  have hyM : divPowE E a b (k - m) (x : W) ∈ M := hM _ (Or.inl ⟨a, b, k - m, hab, rfl⟩) _ hx
  have hfy := hf' _ (by rw [hy]; exact hyM)
  exact hM _ (Or.inl ⟨a, b, m, hab, rfl⟩) _ hfy

end lat

end Formalism.MainNotions.G.GLWeightTheory
end
end

