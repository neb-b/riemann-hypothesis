module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardCompletionsToFullRank
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntCols

variable {k : Type} [Field k]

theorem rank_fromCols_eq_iff {n : ℕ} (C D : Matrix (Fin n) (Fin n) k) :
    (Matrix.fromCols C D).rank = n ↔ ∀ y : Fin n → k, y ᵥ* C = 0 → y ᵥ* D = 0 → y = 0 := by
  have h1 : (Matrix.fromCols C D).rank = Module.finrank k (LinearMap.range (Matrix.fromCols C D)ᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose]; rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.fromCols C D)ᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  constructor
  · intro h y hC hD
    have h3 : Module.finrank k (LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin) = 0 := by omega
    have h4 := Submodule.finrank_eq_zero.mp h3
    have h5 : y ∈ LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols, hC, hD]
      ext i; cases i <;> simp
    rw [h4] at h5
    simpa using h5
  · intro h
    have h3 : LinearMap.ker (Matrix.fromCols C D)ᵀ.mulVecLin = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro y hy
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose, Matrix.vecMul_fromCols] at hy
      refine h y ?_ ?_
      · ext i; simpa using congrFun hy (Sum.inl i)
      · ext i; simpa using congrFun hy (Sum.inr i)
    rw [h3] at h2
    simpa using h2

theorem finrank_leftKer {n : ℕ} (D : Matrix (Fin n) (Fin n) k) :
    Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - D.rank := by
  have h1 : D.rank = Module.finrank k (LinearMap.range Dᵀ.mulVecLin) := by
    rw [← Matrix.rank_transpose]; rfl
  have h2 := LinearMap.finrank_range_add_finrank_ker Dᵀ.mulVecLin
  rw [← h1, Module.finrank_fin_fun] at h2
  omega

theorem li_iff {V Z ι : Type} [AddCommGroup V] [Module k V] [AddCommGroup Z] [Module k Z] [Fintype ι]
    (b : Module.Basis ι k Z) (g : Z →ₗ[k] V) :
    LinearIndependent k (fun i => g (b i)) ↔ ∀ y, g y = 0 → y = 0 := by
  constructor
  · intro h y hy
    have h1 := Fintype.linearIndependent_iff.mp h (fun i => b.repr y i) (by
      have := congrArg g (b.sum_repr y)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, hy] at this
      simpa using this)
    rw [← b.sum_repr y]
    simp [h1]
  · intro h
    have : LinearMap.ker g = ⊥ := by
      rw [Submodule.eq_bot_iff]; intro y hy; exact h y hy
    exact b.linearIndependent.map' g this

theorem card_completions : ∀ (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (D : Matrix (Fin n) (Fin n) k), D.rank = ρ →
    Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} =
      Fintype.card k ^ (n * ρ) * ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) := by
  intro k _ _ n ρ D hD
  have hρ : ρ ≤ n := by simpa [hD] using D.rank_le_width
  have hZ : Module.finrank k (LinearMap.ker Dᵀ.mulVecLin) = n - ρ := by rw [finrank_leftKer, hD]
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker Dᵀ.mulVecLin)
  have hWf : Module.finrank k W = ρ := by
    have := Submodule.finrank_add_eq_of_isCompl hW
    rw [hZ, Module.finrank_fin_fun] at this
    omega
  let bZ := Module.finBasisOfFinrankEq k _ hZ
  let bW := Module.finBasisOfFinrankEq k _ hWf
  let bV := (bZ.prod bW).map (Submodule.prodEquivOfIsCompl _ W hW)
  let E : Matrix (Fin n) (Fin n) k ≃ (Fin (n - ρ) → Fin n → k) × (Fin ρ → Fin n → k) :=
    ((Matrix.transposeLinearEquiv (Fin n) (Fin n) k k).toEquiv.trans
      (Matrix.toLin' (R := k) (m := Fin n) (n := Fin n)).toEquiv).trans
      ((bV.constr k).symm.toEquiv.trans (Equiv.sumArrowEquivProdArrow _ _ _))
  have hE : ∀ C i, (E C).1 i = (bZ i : Fin n → k) ᵥ* C := by
    intro C i
    simp [E, bV, Equiv.sumArrowEquivProdArrow, Module.Basis.constr, Matrix.mulVec_transpose]
  have hp : ∀ C, (Matrix.fromCols C D).rank = n ↔ LinearIndependent k (E C).1 := by
    intro C
    have h1 : (E C).1 = fun i => (Cᵀ.mulVecLin ∘ₗ (LinearMap.ker Dᵀ.mulVecLin).subtype) (bZ i) := by
      funext i
      rw [hE]
      simp [Matrix.mulVec_transpose]
    rw [h1, li_iff, rank_fromCols_eq_iff]
    constructor
    · intro h y hy
      have h2 : (y : Fin n → k) ᵥ* D = 0 := by
        have := y.2
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose] at this
      have h3 : (y : Fin n → k) ᵥ* C = 0 := by simpa [Matrix.mulVec_transpose] using hy
      exact Subtype.ext (h _ h3 h2)
    · intro h y hC hD'
      have hy : y ∈ LinearMap.ker Dᵀ.mulVecLin := by
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_transpose]
      have := h ⟨y, hy⟩ (by simpa [Matrix.mulVec_transpose] using hC)
      simpa using congrArg Subtype.val this
  rw [Nat.card_congr ((Equiv.subtypeEquiv (q := fun x => LinearIndependent k x.1) E hp).trans
      (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun s : Fin (n - ρ) → Fin n → k => LinearIndependent k s))), Nat.card_prod,
    card_linearIndependent (K := k) (V := Fin n → k) (by rw [Module.finrank_fin_fun]; omega), Module.finrank_fin_fun,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j), mul_comm]
  congr 1
  simp [Nat.card_fun, pow_mul]

end GlobalTheory.CompanionTheory.Jp.CntCols
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFixedLowerRightBlock
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntHalf

variable {k : Type} [Field k] {n : ℕ}

def lowH (g : GL (Ix n) k) : Matrix (Fin n) (Ix n) k := g.1.submatrix Sum.inr id

lemma lowH_eq (g : GL (Ix n) k) : lowH g = fromCols (lowerLeftBlock g) (dBlk g) := by
  ext i (j | j) <;> simp [lowH, lowerLeftBlock, dBlk, toBlocks₂₁, toBlocks₂₂]

lemma lowH_mul (g h : GL (Ix n) k) : lowH (g * h) = lowH g * h.1 := by
  ext i j
  simp [lowH, Matrix.mul_apply]

lemma lowH_one : lowH (1 : GL (Ix n) k) = fromCols 0 1 := by
  ext i (j | j) <;> simp [lowH, Matrix.one_apply]

lemma rank_lowH (g : GL (Ix n) k) : (lowH g).rank = n := by
  have h : LinearIndependent k g.1.row := Matrix.linearIndependent_rows_of_isUnit g.isUnit
  have h2 : LinearIndependent k (lowH g).row := h.comp Sum.inr Sum.inr_injective
  simpa using h2.rank_matrix

lemma exists_lowH (M : Matrix (Fin n) (Ix n) k) (hM : M.rank = n) : ∃ g : GL (Ix n) k, lowH g = M := by
  have hli : LinearIndependent k M.row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, ← M.rank_eq_finrank_span_row, hM]
    simp
  obtain ⟨W', hW'⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range M.row))
  have hfr : Module.finrank k W' = n := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW'
    have h2 := M.rank_eq_finrank_span_row
    simp at h1
    omega
  let b := Module.finBasisOfFinrankEq k W' hfr
  let w : Fin n → (Ix n → k) := fun i => (b i : Ix n → k)
  have hw : LinearIndependent k w := b.linearIndependent.map' W'.subtype (Submodule.ker_subtype _)
  have hspan : Submodule.span k (Set.range w) ≤ W' := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b i).2
  have hall : LinearIndependent k (Sum.elim w M.row) :=
    LinearIndependent.sum_type hw hli (Disjoint.mono_left hspan hW'.disjoint.symm)
  let A : Matrix (Ix n) (Ix n) k := Matrix.of (Sum.elim w M.row)
  have hA : IsUnit A := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hall
  refine ⟨hA.unit, ?_⟩
  ext i j
  rfl

lemma card_fibre (g₀ : GL (Ix n) k) :
    Nat.card {g : GL (Ix n) k // lowH g = lowH g₀} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.mulRight g₀⁻¹) ?_)
  intro g
  have hone : lowH g₀ * (g₀⁻¹).1 = fromCols 0 1 := by
    rw [← lowH_mul, mul_inv_cancel, lowH_one]
  have hcd : (lowerLeftBlock (g * g₀⁻¹) = 0 ∧ dBlk (g * g₀⁻¹) = 1) ↔ lowH (g * g₀⁻¹) = fromCols 0 1 := by
    rw [lowH_eq, Matrix.fromCols_inj.eq_iff]
  simp only [Equiv.coe_mulRight]
  rw [hcd, lowH_mul, ← hone]
  constructor
  · intro h; rw [h]
  · intro h
    have := congrArg (· * g₀.1) h
    simpa [Matrix.mul_assoc, ← Units.val_mul] using this

theorem card_lowerRightBlock_eq_fibre_formula (k : Type) [Field k] [Fintype k] (n : ℕ) (D : Matrix (Fin n) (Fin n) k) :
    Nat.card {g : GL (Ix n) k // dBlk g = D} =
      Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} *
        Nat.card {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := by
  classical
  haveI : Fintype {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} := Fintype.ofFinite _
  let f : {g : GL (Ix n) k // dBlk g = D} → {C : Matrix (Fin n) (Fin n) k // (Matrix.fromCols C D).rank = n} :=
    fun g => ⟨lowerLeftBlock g.1, by have h := rank_lowH g.1; rw [lowH_eq, g.2] at h; exact h⟩
  have hfib : ∀ C, Nat.card {x // f x = C} = Nat.card {g : GL (Ix n) k // lowerLeftBlock g = 0 ∧ dBlk g = 1} := by
    intro C
    obtain ⟨g₀, hg₀⟩ := exists_lowH (Matrix.fromCols C.1 D) C.2
    rw [← card_fibre g₀]
    have hy : ∀ y : {g : GL (Ix n) k // lowH g = lowH g₀},
        Matrix.fromCols (lowerLeftBlock y.1) (dBlk y.1) = Matrix.fromCols C.1 D := by
      intro y
      rw [← lowH_eq, ← hg₀]
      exact y.2
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, ?_⟩
        invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    · rw [hg₀, lowH_eq, x.1.2, show lowerLeftBlock x.1.1 = C.1 from congrArg Subtype.val x.2]
    · exact (Matrix.fromCols_inj (hy y)).2
    · exact Subtype.ext (Matrix.fromCols_inj (hy y)).1
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma,
    Finset.sum_congr rfl (fun C _ => hfib C), Finset.sum_const, smul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, mul_comm]

end GlobalTheory.CompanionTheory.Jp.CntHalf
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardFunctionalsVanishingSubspace
section
open Matrix Classical PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.GLFirstBasisOrbit

namespace GlobalTheory.CompanionTheory.GapOpCount

theorem card_forms_vanishing_missing_line : ∀ (k : Type) [Field k] [Fintype k] (n j : ℕ) (M : Submodule k (Fin (n + 1) → k)), e0 k n ∉ M →
    Module.finrank k M + (j + 1) = n + 1 →
    (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card = Fintype.card k ^ j := by
  intro k _ _ n j M hM hdim
  let E := dotProductEquiv k (Fin (n + 1))
  have hE : ∀ a x : Fin (n + 1) → k, E a x = a ⬝ᵥ x := fun a x => by
    simp [E, dotProductEquiv]
  let W : Submodule k (Fin (n + 1) → k) := M ⊔ Submodule.span k {e0 k n}
  let T : Submodule k (Fin (n + 1) → k) := W.dualAnnihilator.comap E.toLinearMap
  have hT : ∀ a, a ∈ T ↔ a ⬝ᵥ e0 k n = 0 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0 := by
    intro a
    simp only [T, W, Submodule.mem_comap, Submodule.mem_dualAnnihilator, LinearEquiv.coe_coe, hE]
    constructor
    · intro h
      exact ⟨h _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)),
        fun x hx => h x (Submodule.mem_sup_left hx)⟩
    · rintro ⟨h0, h1⟩ w hw
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
      rw [dotProduct_add, dotProduct_smul, h0, h1 x hx, smul_zero, add_zero]
  have hfr : Module.finrank k T = j := by
    have hmap : T.map E.toLinearMap = W.dualAnnihilator :=
      Submodule.map_comap_eq_of_surjective E.surjective _
    have h1 : Module.finrank k T = Module.finrank k W.dualAnnihilator := by
      rw [← hmap]
      exact (LinearEquiv.finrank_map_eq E T).symm
    have h2 := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    have h3 : Module.finrank k W = Module.finrank k M + 1 := Submodule.finrank_sup_span_singleton hM
    have h4 : Module.finrank k (Fin (n + 1) → k) = n + 1 := by simp
    omega
  obtain ⟨f, hf0, hfM⟩ := Submodule.exists_le_ker_of_notMem hM
  obtain ⟨b, rfl⟩ := E.surjective f
  have hb0 : b ⬝ᵥ e0 k n ≠ 0 := by rwa [← hE]
  have hbM : ∀ x ∈ M, b ⬝ᵥ x = 0 := fun x hx => by
    rw [← hE]
    exact hfM hx
  let a0 : Fin (n + 1) → k := (b ⬝ᵥ e0 k n)⁻¹ • b
  have ha0 : a0 ⬝ᵥ e0 k n = 1 := by
    simp only [a0, smul_dotProduct, smul_eq_mul]
    exact inv_mul_cancel₀ hb0
  have ha0M : ∀ x ∈ M, a0 ⬝ᵥ x = 0 := fun x hx => by
    simp only [a0, smul_dotProduct, hbM x hx, smul_zero]
  have hcard : (Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1 ∧ ∀ x ∈ M, a ⬝ᵥ x = 0)).card
      = (Finset.univ : Finset T).card := by
    refine Finset.card_bij' (fun a ha => ⟨a - a0, ?_⟩) (fun t _ => t.1 + a0) ?_ ?_ ?_ ?_
    · obtain ⟨-, h1, h2⟩ := Finset.mem_filter.1 ha
      refine (hT _).2 ⟨?_, fun x hx => ?_⟩
      · rw [sub_dotProduct, h1, ha0, sub_self]
      · rw [sub_dotProduct, h2 x hx, ha0M x hx, sub_self]
    · intro a ha
      exact Finset.mem_univ _
    · intro t _
      obtain ⟨h1, h2⟩ := (hT t.1).1 t.2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, fun x hx => ?_⟩
      · rw [add_dotProduct, h1, ha0, zero_add]
      · rw [add_dotProduct, h2 x hx, ha0M x hx, add_zero]
    · intro a ha
      simp
    · intro t _
      ext1
      simp
  rw [hcard, Finset.card_univ, Module.card_eq_pow_finrank (K := k) (V := T), hfr]

end GlobalTheory.CompanionTheory.GapOpCount
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankCompletionSymmetry
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CountRank

open Module

variable {k : Type} [Field k] [Fintype k]

theorem card_injective {U V : Type} [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [FiniteDimensional k U] [FiniteDimensional k V] {e n : ℕ}
    (hU : finrank k U = e) (hV : finrank k V = n) (he : e ≤ n) :
    Nat.card {g : U →ₗ[k] V // Function.Injective g} =
      ∏ j ∈ Finset.range e, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  let b : Module.Basis (Fin e) k U := Module.finBasisOfFinrankEq k U hU
  have key : ∀ g : U →ₗ[k] V, Function.Injective g ↔ LinearIndependent k (g ∘ b) := by
    intro g
    constructor
    · intro hg
      exact b.linearIndependent.map' g (LinearMap.ker_eq_bot.mpr hg)
    · intro hli
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hsum : ∑ i, (b.repr x i) • (g ∘ b) i = 0 := by
        have h0 : g (∑ i, (b.repr x i) • b i) = 0 := by rw [b.sum_repr]; exact hx
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at h0
        simpa only [Function.comp_apply, map_smul] using h0
      have hc := Fintype.linearIndependent_iff.mp hli _ hsum
      apply b.repr.injective
      ext i
      simp [hc i]
  have E : {g : U →ₗ[k] V // Function.Injective g} ≃ {s : Fin e → V // LinearIndependent k s} :=
    { toFun := fun g => ⟨g.1 ∘ b, (key g.1).mp g.2⟩
      invFun := fun s => ⟨b.constr k s.1, (key _).mpr (by
          have hs : (b.constr k s.1 : U → V) ∘ b = s.1 := by
            funext i
            simp
          rw [hs]
          exact s.2)⟩
      left_inv := fun g => Subtype.ext (b.ext fun i => by simp)
      right_inv := fun s => Subtype.ext (funext fun i => by simp) }
  rw [Nat.card_congr E, card_linearIndependent (K := k) (V := V) (k := e) (by omega), hV,
    Finset.prod_range (fun j => Fintype.card k ^ n - Fintype.card k ^ j)]

theorem card_ker_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) (K : Submodule k V)
    (hK : finrank k K = n - ρ) :
    Nat.card {f : V →ₗ[k] V // LinearMap.ker f = K} =
      ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have hQ : finrank k (V ⧸ K) = ρ := by
    have := Submodule.finrank_quotient_add_finrank K
    omega
  have E : {f : V →ₗ[k] V // LinearMap.ker f = K} ≃
      {g : (V ⧸ K) →ₗ[k] V // Function.Injective g} :=
    { toFun := fun f => ⟨K.liftQ f.1 (le_of_eq f.2.symm),
        LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq f.2))⟩
      invFun := fun g => ⟨g.1.comp K.mkQ, by
        rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr g.2, Submodule.comap_bot,
          Submodule.ker_mkQ]⟩
      left_inv := fun f => Subtype.ext (Submodule.liftQ_mkQ K f.1 _)
      right_inv := fun g => Subtype.ext (Submodule.linearMap_qext K (Submodule.liftQ_mkQ K _ _)) }
  rw [Nat.card_congr E]
  exact card_injective hQ hV (by omega)

theorem card_rank_eq {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n ρ : ℕ} (hV : finrank k V = n) (hρ : ρ ≤ n) :
    Nat.card {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} =
      Nat.card {K : Submodule k V // finrank k K = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (V →ₗ[k] V) := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  letI : Fintype {K : Submodule k V // finrank k K = n - ρ} := Fintype.ofFinite _
  have E : {f : V →ₗ[k] V // finrank k (LinearMap.range f) = ρ} ≃
      Σ K : {K : Submodule k V // finrank k K = n - ρ},
        {f : V →ₗ[k] V // LinearMap.ker f = K.1} :=
    { toFun := fun f => ⟨⟨LinearMap.ker f.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker f.1
          have h2 := f.2
          omega⟩, ⟨f.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by
          have h1 := LinearMap.finrank_range_add_finrank_ker p.2.1
          have h2 := p.1.2
          have h3 := p.2.2
          rw [h3] at h1
          omega⟩
      left_inv := fun f => rfl
      right_inv := by
        rintro ⟨⟨K, hK⟩, ⟨f, hf⟩⟩
        dsimp only at hf
        subst hf
        rfl }
  rw [Nat.card_congr E, Nat.card_sigma,
    Finset.sum_congr rfl (fun a _ => card_ker_eq hV hρ a.1 a.2), Finset.sum_const,
    Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card (α := {K : Submodule k V // finrank k K = n - ρ})]

theorem card_sub_le {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} ≤
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  classical
  have : Finite V := Module.finite_of_finite k
  have : Finite (Submodule k V) :=
    Finite.of_injective (fun K : Submodule k V => (K : Set V)) SetLike.coe_injective
  let eV : Module.Dual k V ≃ₗ[k] V := ((Module.finBasis k V).toDualEquiv).symm
  have hDual : ∀ K : Submodule k V,
      finrank k (K.dualAnnihilator) = finrank k V - finrank k K := by
    intro K
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq K
    omega
  let F : {K : Submodule k V // finrank k K = d} → {K : Submodule k V // finrank k K = n - d} :=
    fun K => ⟨(K.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V), by
      rw [LinearEquiv.finrank_map_eq, hDual, hV, K.2]⟩
  apply Nat.card_le_card_of_injective F
  intro K₁ K₂ h
  apply Subtype.ext
  have h1 : (K₁.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) =
      (K₂.1.dualAnnihilator).map (eV : Module.Dual k V →ₗ[k] V) := congrArg Subtype.val h
  have h2 := Submodule.map_injective_of_injective eV.injective h1
  exact Subspace.dualAnnihilator_inj.mp h2

theorem card_sub_symm {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {n : ℕ} (hV : finrank k V = n) (d : ℕ) (hd : d ≤ n) :
    Nat.card {K : Submodule k V // finrank k K = d} =
      Nat.card {K : Submodule k V // finrank k K = n - d} := by
  apply le_antisymm (card_sub_le hV d hd)
  have := card_sub_le hV (n - d) (Nat.sub_le n d)
  rwa [Nat.sub_sub_self hd] at this

theorem card_matrix_rank (n ρ : ℕ) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} =
      Nat.card {f : (Fin n → k) →ₗ[k] (Fin n → k) // finrank k (LinearMap.range f) = ρ} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquiv
    (Matrix.toLin' : Matrix (Fin n) (Fin n) k ≃ₗ[k] ((Fin n → k) →ₗ[k] (Fin n → k))).toEquiv
    (fun D => by
      show D.rank = ρ ↔ finrank k (LinearMap.range (Matrix.toLin' D)) = ρ
      rw [Matrix.toLin'_apply']
      rfl)

theorem rank_symm (k : Type) [Field k] [Fintype k] (n ρ : ℕ) (h : ρ ≤ n) :
    Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = ρ} *
        ∏ j ∈ Finset.range (n - ρ), (Fintype.card k ^ n - Fintype.card k ^ j) =
      Nat.card {D : Matrix (Fin n) (Fin n) k // D.rank = n - ρ} *
        ∏ j ∈ Finset.range ρ, (Fintype.card k ^ n - Fintype.card k ^ j) := by
  have hV : finrank k (Fin n → k) = n := Module.finrank_fin_fun k
  rw [card_matrix_rank, card_matrix_rank, card_rank_eq hV h, card_rank_eq hV (Nat.sub_le n ρ),
    Nat.sub_sub_self h, card_sub_symm hV ρ h]
  ring

end GlobalTheory.CompanionTheory.Jp.CountRank
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardRankLowerLeftEqLowerRight
section
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp.CntSwap

def swapW (k : Type) [Field k] (n : ℕ) : GL (Ix n) k :=
  ⟨fromBlocks 0 1 1 0, fromBlocks 0 1 1 0,
    by simp [fromBlocks_multiply, fromBlocks_one],
    by simp [fromBlocks_multiply, fromBlocks_one]⟩

lemma lowerRightBlock_mul_block_swap {k : Type} [Field k] {n : ℕ} (g : GL (Ix n) k) :
    dBlk (g * swapW k n) = lowerLeftBlock g := by
  show (g.1 * fromBlocks 0 1 1 0).toBlocks₂₂ = g.1.toBlocks₂₁
  conv_lhs => rw [← fromBlocks_toBlocks g.1]
  rw [fromBlocks_multiply]
  simp

theorem card_lower_left_rank_eq_card_lower_right_rank : ∀ (k : Type) [Field k] [Fintype k] (n i : ℕ),
    Nat.card {g : GL (Ix n) k // (lowerLeftBlock g).rank = i} = Nat.card {g : GL (Ix n) k // (dBlk g).rank = i} := by
  intro k _ _ n i
  exact Nat.card_congr ((Equiv.mulRight (swapW k n)).subtypeEquiv (fun g => by
    rw [Equiv.coe_mulRight, lowerRightBlock_mul_block_swap]))

end GlobalTheory.CompanionTheory.Jp.CntSwap
end

