module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0008
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0003

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.AntitonePowersInDominantMonoid
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem exists_tExp_eq_indicator (b : Fin n → ℤ) (hb : Antitone b) :
    ∃ i : Fin (n + 2), tExp n i = fun j => if 0 < b j then 1 else 0 := by
  classical
  have hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0 := ⟨n, Or.inl rfl⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨⟨Nat.find hex, by omega⟩, ?_⟩
  funext j
  have hne : Nat.find hex ≠ n + 1 := by omega
  simp only [tExp, hne, if_false]
  by_cases hj : (j : ℕ) < Nat.find hex
  · have hnot := Nat.find_min hex hj
    have hpos : 0 < b j := by
      by_contra hcon
      exact hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)
    rw [if_pos hj, if_pos hpos]
  · have hspec := Nat.find_spec hex
    have hnpos : ¬ 0 < b j := by
      rcases hspec with h | ⟨h, h'⟩
      · have := j.2
        omega
      · have hmono : b j ≤ b ⟨Nat.find hex, h⟩ := hb (by
          rw [Fin.le_def]
          exact not_lt.mp hj)
        omega
    rw [if_neg hj, if_neg hnpos]

theorem dPow_mem_closure_of_nonneg (p : Lˣ) (N : ℕ) :
    ∀ b : Fin n → ℤ, Antitone b → (∀ j, 0 ≤ b j) → (∀ j, b j ≤ N) →
      dPow p b ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction N with
  | zero =>
    intro b _ h0 hN
    have hb : b = 0 := by
      funext j
      have h1 := h0 j
      have h2 := hN j
      simp only [Nat.cast_zero] at h2
      simp only [Pi.zero_apply]
      omega
    rw [hb, dPow_zero]
    exact Submonoid.one_mem _
  | succ N ih =>
    intro b hb h0 hN
    obtain ⟨i, hi⟩ := exists_tExp_eq_indicator b hb
    have hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i := by
      rw [hi]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)
    · intro x y hxy
      have hm := hb hxy
      have hx := h0 x
      have hy := h0 y
      show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      show 0 ≤ (b j - if 0 < b j then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      have h2 := hN j
      push_cast at h2
      show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)
      split_ifs <;> omega

theorem dPow_mem_closure_of_ge (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction C with
  | zero =>
    intro a ha h0
    have hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ) := by
      intro j
      have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
        Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      omega
    refine dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd
    have := h0 j
    simpa using this
  | succ C ih =>
    intro a ha h0
    have hlast : tExp n (Fin.last (n + 1)) = fun _ => -1 := by
      funext j
      simp [tExp]
    have hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1)) := by
      rw [hlast]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_)
      (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)
    · intro x y hxy
      have := ha hxy
      show a y + 1 ≤ a x + 1
      omega
    · intro j
      have := h0 j
      push_cast at this
      show -(C : ℤ) ≤ a j + 1
      omega

theorem dPow_antitone_mem_closure (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (p : Lˣ) (a : Fin n → ℤ) (ha : Antitone a) :
    dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  refine dPow_mem_closure_of_ge p (∑ k, (a k).natAbs) a ha (fun j => ?_)
  have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
    Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatchStatement
section
open Finset Polynomial

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_polynomial_permutation_match : ∀ (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ),
    (∀ a, lev a < M) → (∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card) →
    (∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) →
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | exact GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.UnitBall

variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]

noncomputable def ball : ValuationSubring L :=
  by apply _root_.UpperTheory.Reformulated.B.BallSubgroup.ball <;> assumption

variable {L}

theorem mem_ball {x : L} : x ∈ ball L ↔ ‖x‖ ≤ 1 := Iff.rfl

theorem isUnit_of_norm_eq_one {x : ball L} (h : ‖(x : L)‖ = 1) : IsUnit x := by
  have hx : (x : L) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  have hi : (x : L)⁻¹ ∈ ball L := by
    rw [mem_ball, norm_inv, h, inv_one]
  refine IsUnit.of_mul_eq_one ⟨(x : L)⁻¹, hi⟩ ?_
  apply Subtype.ext
  simp [hx]

theorem norm_eq_one_of_isUnit {x : ball L} (h : IsUnit x) : ‖(x : L)‖ = 1 := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  have h1 : (x : L) * (y : L) = 1 := by
    have := congrArg (Subtype.val) hy
    simpa using this
  have h2 : ‖(x : L)‖ * ‖(y : L)‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  have hx : ‖(x : L)‖ ≤ 1 := x.2
  have hy' : ‖(y : L)‖ ≤ 1 := y.2
  nlinarith [norm_nonneg (x : L), norm_nonneg (y : L)]

variable {p : Lˣ}

theorem norm_unif_pos (p : Lˣ) : 0 < ‖(p : L)‖ := norm_pos_iff.2 p.ne_zero

theorem exists_nat_norm (hp : IsUnif p) {x : L} (hx : x ≠ 0) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = ‖(p : L)‖ ^ m := by
  obtain ⟨a, ha⟩ := hp.2 x hx
  have h0 := norm_unif_pos p
  have hnn : 0 ≤ a := by
    by_contra hneg
    have hlt : a < 0 := not_le.1 hneg
    have : 1 < ‖(p : L)‖ ^ a := one_lt_zpow_of_neg₀ h0 hp.1 hlt
    linarith
  refine ⟨a.toNat, ?_⟩
  rw [ha, ← zpow_natCast, Int.toNat_of_nonneg hnn]

def unif (hp : IsUnif p) : ball L := ⟨p, hp.1.le⟩

theorem unif_coe (hp : IsUnif p) : ((unif hp : ball L) : L) = p := rfl

theorem irreducible_unif (hp : IsUnif p) : Irreducible (unif hp) := by
  have h0 := norm_unif_pos p
  refine ⟨fun h => ?_, ?_⟩
  · have := norm_eq_one_of_isUnit h
    rw [unif_coe] at this
    exact absurd this hp.1.ne
  · intro a b hab
    have hab' : (p : L) = (a : L) * (b : L) := by
      have := congrArg (Subtype.val) hab
      simpa [unif_coe] using this
    have ha0 : (a : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, zero_mul])
    have hb0 : (b : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, mul_zero])
    obtain ⟨i, hi⟩ := exists_nat_norm hp ha0 a.2
    obtain ⟨j, hj⟩ := exists_nat_norm hp hb0 b.2
    have hn : ‖(p : L)‖ ^ 1 = ‖(p : L)‖ ^ (i + j) := by
      rw [pow_one, pow_add, ← hi, ← hj, ← norm_mul, ← hab']
    have hij : 1 = i + j := pow_right_injective₀ h0 hp.1.ne hn
    rcases Nat.eq_zero_or_pos i with h | h
    · left
      apply isUnit_of_norm_eq_one
      rw [hi, h, pow_zero]
    · right
      have : j = 0 := by omega
      apply isUnit_of_norm_eq_one
      rw [hj, this, pow_zero]

theorem isDVR (hp : IsUnif p) : IsDiscreteValuationRing (ball L) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif hp, irreducible_unif hp, ?_⟩
  intro x hx
  have hx0 : (x : L) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_nat_norm hp hx0 x.2
  have h0 := norm_unif_pos p
  have hpm : (p : L) ^ m ≠ 0 := pow_ne_zero _ p.ne_zero
  have hq : ‖(x : L) / (p : L) ^ m‖ = 1 := by
    rw [norm_div, norm_pow, hm]
    exact div_self (pow_ne_zero _ h0.ne')
  let q : ball L := ⟨(x : L) / (p : L) ^ m, hq.le⟩
  obtain ⟨u, hu⟩ := isUnit_of_norm_eq_one (x := q) hq
  refine ⟨m, u, ?_⟩
  apply Subtype.ext
  have hu' : ((u : ball L) : L) = (x : L) / (p : L) ^ m := by rw [hu]
  change ((unif hp : ball L) : L) ^ m * ((u : ball L) : L) = (x : L)
  rw [hu', unif_coe]
  field_simp

theorem map_mem_congK (n : ℕ) (U : GL (Fin n) (ball L)) :
    Matrix.GeneralLinearGroup.map (algebraMap (ball L) L) U ∈ congK L n 1 zero_le_one le_rfl := by
  have key : ∀ (A : Matrix (Fin n) (Fin n) (ball L)) (i j : Fin n),
      ‖(A.map (algebraMap (ball L) L) - 1) i j‖ ≤ 1 := by
    intro A i j
    rw [Matrix.sub_apply, Matrix.map_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (A i j).2 ?_)
    rw [norm_neg, Matrix.one_apply]
    split_ifs <;> simp
  intro i j
  refine ⟨key _ i j, ?_⟩
  rw [← map_inv]
  exact key _ i j

end GlobalTheory.CompanionTheory.CartGL.UnitBall

namespace GlobalTheory.CompanionTheory.CartGL


open UnitBall in
theorem cartan_unitBall (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (p : Lˣ) (hp : IsUnif p) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ congK L n 1 zero_le_one le_rfl,
      ∃ k₂ ∈ congK L n 1 zero_le_one le_rfl, g = k₁ * dPow p a * k₂ := by
  haveI := isDVR hp
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) L).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  obtain ⟨u, v, a, hu, hv, ha, hg⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists (ball L) L n (unif hp)
    (irreducible_unif hp) (g : Matrix (Fin n) (Fin n) L) hdet
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det u).2 hu
  obtain ⟨V, rfl⟩ := (Matrix.isUnit_iff_isUnit_det v).2 hv
  refine ⟨a, ha, _, map_mem_congK n U, _, map_mem_congK n V, ?_⟩
  apply Units.ext
  rw [hg, Units.val_mul, Units.val_mul, dPow_val]
  have hd : (Matrix.diagonal fun i => (algebraMap (ball L) L (unif hp)) ^ (a i)) =
      Matrix.diagonal fun i => ((p ^ a i : Lˣ) : L) := by
    congr 1
    funext i
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hd]
  rfl

end GlobalTheory.CompanionTheory.CartGL
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsCompact
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isCompact_entryBall (L : Type) [NontriviallyNormedField L] [ProperSpace L] (n : ℕ) (r : ℝ) :
    IsCompact {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} := by
  have h : IsCompact (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
      Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _
  have e : {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} =
      (Set.univ.pi fun i : Fin n => Set.univ.pi fun j : Fin n =>
        Metric.closedBall ((1 : Matrix (Fin n) (Fin n) L) i j) r) := by
    ext M
    constructor
    · intro hM i _ j _
      have := hM i j
      rw [Matrix.sub_apply] at this
      exact mem_closedBall_iff_norm.2 this
    · intro hM i j
      have := mem_closedBall_iff_norm.1 (hM i (Set.mem_univ _) j (Set.mem_univ _))
      rw [Matrix.sub_apply]
      exact this
  rw [e]
  exact h

theorem isCompact_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsCompact (congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  have hS := isCompact_entryBall L n r
  have hS' := hS.image MulOpposite.continuous_op
  have h := Units.isClosedEmbedding_embedProduct.isCompact_preimage (hS.prod hS')
  have e : (congK L n r h0 h1 : Set (GL (Fin n) L)) =
      Units.embedProduct (Matrix (Fin n) (Fin n) L) ⁻¹'
        ({M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} ×ˢ
          (MulOpposite.op '' {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r})) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_preimage, Set.mem_prod, Units.embedProduct_apply,
      Set.mem_image, Set.mem_setOf_eq, MulOpposite.op_inj, exists_eq_right]
    exact ⟨fun hk => ⟨fun i j => (hk i j).1, fun i j => (hk i j).2⟩,
      fun hk i j => ⟨hk.1 i j, hk.2 i j⟩⟩
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupIsOpen
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  intro L _ _ n r h0 h1 hr
  have hball : IsOpen (Metric.closedBall (0 : L) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hval : Continuous fun k : GL (Fin n) L => (k : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val
  have hinv : Continuous fun k : GL (Fin n) L => ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val.comp continuous_inv
  have hset : (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ((fun k : GL (Fin n) L => ((k : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r ∩
          (fun k : GL (Fin n) L =>
            (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      mem_closedBall_zero_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hval.sub continuous_const)
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hinv.sub continuous_const)

end GlobalTheory.CompanionTheory.CartGL
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CongruenceSubgroupNormalInMaximalCompact
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Normal

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem entry_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖(A - 1) i j‖ ≤ 1) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) ?_)
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem entry_conj {C D X : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hC : ∀ i j, ‖C i j‖ ≤ 1) (hD : ∀ i j, ‖D i j‖ ≤ 1) (hCD : C * D = 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ r) (i j : Fin n) : ‖(C * X * D - 1) i j‖ ≤ r := by
  have e : C * X * D - 1 = C * (X - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  rw [e]
  have h := entry_mul (mul_nonneg zero_le_one h0) zero_le_one
    (entry_mul zero_le_one h0 hC hX) hD i j
  simpa using h

theorem conj_mem_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L)
    (hc : c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (hx : x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) :
    c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  have hC : ∀ i j, ‖((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).1
  have hD : ∀ i j, ‖(((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).2
  have hCD : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).1) i j
  · have e : (c * x * c⁻¹)⁻¹ = c * x⁻¹ * c⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).2) i j

end GlobalTheory.CompanionTheory.CartGL.Normal
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DominantConjugationPreservesUpperCongruence
section
open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem conj_upper_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r u hlow hr i j
  have hinv : (((dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  have hent : ((dPow p a * u * (dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (a i - a j) : Lˣ) : L) * (u : Matrix (Fin n) (Fin n) L) i j := by
    rw [Units.val_mul, Units.val_mul, dPow_val, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul,
      sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
    ring
  rw [Matrix.sub_apply, hent]
  have hri := hr i j
  rw [Matrix.sub_apply] at hri
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : i ≠ j := ne_of_lt hij
    rw [Matrix.one_apply_ne hne] at hri ⊢
    rw [sub_zero] at hri ⊢
    have hexp : 0 ≤ a i - a j := sub_nonneg.mpr (ha hij.le)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hexp
    have hpow : ‖((p ^ (a i - a j) : Lˣ) : L)‖ ≤ 1 := by
      rw [hm, zpow_natCast, Units.val_pow_eq_pow_val, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp.le
    rw [norm_mul]
    calc _ ≤ 1 * ‖(u : Matrix (Fin n) (Fin n) L) i j‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ r := hri
  · subst hij
    simpa using hri
  · rw [hlow i j hij, mul_zero]
    rw [hlow i j hij] at hri
    exact hri

end GlobalTheory.CompanionTheory.CartGL
end

