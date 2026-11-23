module

public import Mathlib
public import ReciprocityTheory.DualLattices.FormalChartAtZero
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsLocalRingTensorProductOfFiniteOfPoints
section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private theorem tenLocal_sub_mem {O A : Type} [CommRing O] [CommRing A] [IsLocalRing O]
    [IsLocalRing A] [Algebra O A] (φ : A →ₐ[O] O) (a : A) :
    a - algebraMap O A (φ a) ∈ maximalIdeal A := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h2 := h.map φ
  simp at h2

theorem isLocalRing_tensorProduct_of_finite_of_points :
  (∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A] [IsLocalRing A'] [Algebra O A] [Algebra O A']
    [Module.Finite O A] [Module.Finite O A'], (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')) := by
  intro O A A' _ _ _ _ _ _ _ _ _ _ φ φ'
  let Φ : A ⊗[O] A' →ₐ[O] O := Algebra.TensorProduct.productMap φ φ'
  have hsurj : Function.Surjective Φ := fun o => ⟨algebraMap _ _ o, Φ.commutes o⟩
  have hM0 : ((maximalIdeal O).comap Φ).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective Φ hsurj
  refine IsLocalRing.of_unique_max_ideal ⟨(maximalIdeal O).comap Φ, hM0, ?_⟩
  intro M hM
  have hint : Algebra.IsIntegral O (A ⊗[O] A') := Algebra.IsIntegral.of_finite _ _
  have key : ∀ {B : Type} [CommRing B] [IsLocalRing B] [Algebra O B] (f : B →ₐ[O] A ⊗[O] A'),
      M.comap f = maximalIdeal B := by
    intro B _ _ _ f
    have hf : (f : B →+* A ⊗[O] A').IsIntegral := by
      refine RingHom.IsIntegral.tower_top (algebraMap O B) _ ?_
      rw [f.comp_algebraMap]
      exact fun x => hint.isIntegral x
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (f : B →+* A ⊗[O] A') hf M
    exact IsLocalRing.eq_maximalIdeal this
  have hA := key (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A')
  have hA' := key (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A')
  have hO := key (Algebra.ofId O (A ⊗[O] A'))
  have hx : ∀ x : A ⊗[O] A', x - algebraMap O _ (Φ x) ∈ M := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      have := M.add_mem hx hy
      rw [map_add (f := _), map_add (f := _)]
      convert this using 1
      ring
    | tmul a a' =>
      have h1 := tenLocal_sub_mem φ a
      have h2 := tenLocal_sub_mem φ' a'
      rw [← hA, Ideal.mem_comap, map_sub, AlgHom.commutes] at h1
      rw [← hA', Ideal.mem_comap, map_sub, AlgHom.commutes] at h2
      have h3 := M.add_mem
        (M.mul_mem_right ((Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a') h1)
        (M.mul_mem_left (algebraMap O (A ⊗[O] A') (φ a)) h2)
      have e1 : a ⊗ₜ[O] a' = (Algebra.TensorProduct.includeLeft : A →ₐ[O] A ⊗[O] A') a *
          (Algebra.TensorProduct.includeRight : A' →ₐ[O] A ⊗[O] A') a' := by simp
      have e2 : Φ (a ⊗ₜ[O] a') = φ a * φ' a' := by simp [Φ]
      rw [e2, map_mul, e1]
      convert h3 using 1
      ring
  refine hM.eq_of_le hM0.ne_top ?_
  intro x hxM
  rw [Ideal.mem_comap, ← hO, Ideal.mem_comap]
  have := M.sub_mem hxM (hx x)
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegral
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.GaugeDeriv

variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def linForm {ι ι' : Type} [Fintype ι] [Fintype ι'] (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries (ι ⊕ ι') C :=
  (∑ c : ι, e c w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
    ∑ b : ι', e' b w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)

variable {ι ι' : Type} [Fintype ι] [Fintype ι']

theorem hPullW_eq (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW H e e' = MvPowerSeries.subst (linForm e e') H := rfl

theorem constantCoeff_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) :
    MvPowerSeries.constantCoeff (linForm e e' w) = 0 := by
  simp [linForm]

theorem hasSubst_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) :
    MvPowerSeries.HasSubst (linForm e e') := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_linForm e e' w)

theorem pderiv_linForm (e : ι → WV I → C) (e' : ι' → WV I → C) (w : WV I) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (linForm e e' w) = MvPowerSeries.C (e' b w) := by
  classical
  simp [linForm, MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]

theorem dVar_eq {σ : Type} (w : σ) (F : MvPowerSeries σ C) :
    dVar w F = MvPowerSeries.pderiv (R := C) w F := by
  ext μ
  rw [MvPowerSeries.coeff_pderiv]
  show ((μ w + 1 : ℕ) : C) * MvPowerSeries.coeff (μ + Finsupp.single w 1) F = _
  push_cast
  ring

theorem sum_toW {M : Type} [AddCommGroup M] [Module C M] (g : Fin 2) (u : I g → C) (F : WV I → M) :
    ∑ w, toW g u w • F w = ∑ k, u k • F ⟨g, k⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single g]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    simp [toW]
  · intro g' _ hg'
    refine Finset.sum_eq_zero (fun k _ => ?_)
    simp [toW, hg']
  · simp

theorem pderiv_hPullW (H : MvPowerSeries (WV I) C) (e : ι → WV I → C) (g : Fin 2)
    (v' : ι' → I g → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (hPullW H e (fun b => toW g (v' b))) =
      ∑ k, v' b k • hPullW (dVar ⟨g, k⟩ H) e (fun b => toW g (v' b)) := by
  have hs := hasSubst_linForm e (fun b => toW g (v' b))
  rw [hPullW_eq, GlobalTheory.FormalCalc.pderiv_subst hs]
  have key : ∀ w : WV I,
      MvPowerSeries.subst (linForm e (fun b => toW g (v' b))) (MvPowerSeries.pderiv (R := C) w H) *
          MvPowerSeries.pderiv (R := C) (Sum.inr b) (linForm e (fun b => toW g (v' b)) w) =
        toW g (v' b) w • hPullW (dVar w H) e (fun b => toW g (v' b)) := by
    intro w
    rw [pderiv_linForm, hPullW_eq, dVar_eq, MvPowerSeries.smul_eq_C_mul, mul_comm]
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  exact sum_toW g (v' b) (fun w => hPullW (dVar w H) e (fun b => toW g (v' b)))

theorem constantCoeff_upG (g : Fin 2) {F : MvPowerSeries (I g) C}
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (upG g F) = 0 := by
  unfold upG
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X _))
    (fun _ => MvPowerSeries.constantCoeff_X _), hF, map_zero]

variable {V : VF C} {d : ℕ} {J : Fin 2 → Type} [∀ g, Fintype (J g)]

theorem hPullW_toLeaf (G : ∀ g, Cart V d (I g) (J g)) (g : Fin 2) (a a' : ZMod d)
    (e : ι → I g → C) (v' : ι' → I (1 - g) → C)
    (he : ∀ c x, (G g).ty (Sum.inl x) ≠ a → e c x = 0)
    (hv : ∀ b k, (G (1 - g)).ty (Sum.inl k) ≠ a' → v' b k = 0) (F : MvPowerSeries (WV I) C) :
    hPullW (toLeaf G g a a' F) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
      hPullW F (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  rw [hPullW_eq, hPullW_eq]
  apply GlobalTheory.subst_eq_of_coeff_eq_of_killed C (WV I) (ι ⊕ ι') (OnLeafV G g a a')
  · exact constantCoeff_linForm _ _
  · rintro ⟨w1, w2⟩ hw
    have h1 : ∀ c, toW g (e c) ⟨w1, w2⟩ = 0 := by
      intro c
      by_cases h : w1 = g
      · subst h
        simp only [toW]
        exact he c w2 (fun hty => hw (Or.inl ⟨rfl, hty⟩))
      · simp [toW, h]
    have h2 : ∀ b, toW (1 - g) (v' b) ⟨w1, w2⟩ = 0 := by
      intro b
      by_cases h : w1 = 1 - g
      · subst h
        simp only [toW]
        exact hv b w2 (fun hty => hw (Or.inr ⟨rfl, hty⟩))
      · simp [toW, h]
    simp [linForm, h1, h2]
  · intro μ hμ
    rw [show MvPowerSeries.coeff μ (toLeaf G g a a' F) = toLeaf G g a a' F μ from rfl]
    unfold toLeaf
    exact if_pos hμ

theorem odd_val_sub {d : ℕ} [NeZero d] (a : ZMod d) {i : ℕ} (hi : Odd i) (hid : i < d) :
    Odd (a + (i : ZMod d) - a).val := by
  rw [add_sub_cancel_left, ZMod.val_natCast, Nat.mod_eq_of_lt hid]
  exact hi

private theorem hPullW_add (H H' : MvPowerSeries (WV I) C) (e : ι → WV I → C)
    (e' : ι' → WV I → C) :
    hPullW (H + H') e e' = hPullW H e e' + hPullW H' e e' := by
  rw [hPullW_eq, hPullW_eq, hPullW_eq, MvPowerSeries.subst_add (hasSubst_linForm e e')]

private theorem hPullW_sum_smul {κ : Type} [Fintype κ] (c : κ → C) (F : κ → MvPowerSeries (WV I) C)
    (e : ι → WV I → C) (e' : ι' → WV I → C) :
    hPullW (∑ q, c q • F q) e e' = ∑ q, c q • hPullW (F q) e e' := by
  simp only [hPullW_eq]
  rw [GlobalTheory.FormalCalc.subst_sum' (hasSubst_linForm e e')]
  simp only [MvPowerSeries.subst_smul (hasSubst_linForm e e')]

theorem pderiv_hM : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → ∀ b : ι', ∃ γ : MvPowerSeries (WV I) C, (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧ MvPowerSeries.pderiv (R := C) (Sum.inr b) (X.hM g a i e v') = MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • hPullW (upG g ((S g).ze (t g) κ)) (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
  intro C _ V d _ I J _ _ X hAlt g a i hi hid S t ht ι ι' _ _ e v' he hvint hv b
  have hΦ : MvPowerSeries.HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => constantCoeff_upG w.1 ((ht w.1).1 w.2))
  have hLs := hasSubst_linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b))
  have hK : ∀ k : I (1 - g), ∃ γ : MvPowerSeries (WV I) C,
      (∀ μ, V.Ge 0 (MvPowerSeries.coeff μ γ)) ∧
      v' b k • hPullW (dVar (⟨1 - g, k⟩ : WV I) (X.hL g a (a + (i : ZMod d))))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) =
        v' b k • hPullW (∑ κ : J g, X.pair g κ k • upG g ((S g).ze (t g) κ))
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) +
        v' b k • hPullW (MvPowerSeries.subst (fun w : WV I => upG w.1 (t w.1 w.2)) γ)
          (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) := by
    intro k
    by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
    · obtain ⟨K, ⟨γ, hγ, rfl⟩, hEq⟩ :=
        X.C_eq hAlt g a (a + (i : ZMod d)) (odd_val_sub a hi hid) S t ht k hk
      refine ⟨γ, hγ, ?_⟩
      rw [sub_eq_iff_eq_add'] at hEq
      rw [hEq, hPullW_add, hPullW_toLeaf X.G g a _ e v' he hv,
        hPullW_toLeaf X.G g a _ e v' he hv, smul_add]
    · refine ⟨0, fun μ => ?_, ?_⟩
      · rw [map_zero]
        exact VF.Ge.zero 0
      · rw [hv b k hk]
        simp only [zero_smul, add_zero]
  choose γ hγint hγeq using hK
  refine ⟨∑ k, v' b k • γ k, ?_, ?_⟩
  · intro μ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine VF.Ge.sum (fun k _ => ?_)
    simp only [map_smul, smul_eq_mul]
    exact VF.Ge.mul_int (hvint b k) (hγint k μ)
  · unfold RowData.hM
    rw [pderiv_hPullW (X.hL g a (a + (i : ZMod d))) (fun c => toW g (e c)) (1 - g) v' b,
      Finset.sum_congr rfl (fun k _ => hγeq k), Finset.sum_add_distrib]
    refine (add_comm _ _).trans ?_
    congr 1
    · simp only [hPullW_eq]
      have hΨ : MvPowerSeries.HasSubst (fun w : WV I =>
          MvPowerSeries.subst (linForm (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)))
            (upG w.1 (t w.1 w.2))) := by
        have h := hΦ.comp hLs
        simp only [MvPowerSeries.substAlgHom_apply] at h
        exact h
      rw [GlobalTheory.FormalCalc.subst_sum' hΨ]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [MvPowerSeries.subst_smul hΨ, MvPowerSeries.subst_comp_subst_apply hΦ hLs]
    · simp only [hPullW_sum_smul, Finset.smul_sum, smul_smul, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun κ _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [mul_comm]

end GlobalTheory.GaugeDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdeal
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.SemilinearNullity

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  refine V.v.map_lt_add ha ?_
  rw [V.v.map_neg]; exact hb

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_inv {a : C} (h : ¬ V.MM a) : V.Ge 0 a⁻¹ := by
  have h0 : a ≠ 0 := by rintro rfl; exact h mm_zero
  show (0 : WithTop ℝ) ≤ V.v a⁻¹
  have e : V.v a⁻¹ + V.v a = 0 := by rw [← V.v.map_mul, inv_mul_cancel₀ h0, V.v.map_one]
  have h1 : V.v a ≤ 0 := not_lt.mp h
  calc (0 : WithTop ℝ) = V.v a⁻¹ + V.v a := e.symm
    _ ≤ V.v a⁻¹ := add_le_of_nonpos_right h1

def IndepOn (V : VF C) {m : ℕ} {σ : Type} (Y : Fin m → σ → C) (T : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → C, (∀ δ, V.Ge 0 (c δ)) → (∀ δ, δ ∉ T → c δ = 0) →
    (∀ s, V.MM (∑ δ, c δ * Y δ s)) → ∀ δ, V.MM (c δ)

theorem IndepOn.indepMod {m : ℕ} {σ : Type} {Y : Fin m → σ → C} {T : Finset (Fin m)}
    (h : IndepOn V Y T) {N : ℕ} (f : Fin N ↪ Fin m) (hf : ∀ ν, f ν ∈ T) :
    IndepMod V (fun ν => Y (f ν)) := by
  intro c hc hs ν
  have key := h (fun δ => ∑ ν, if f ν = δ then c ν else 0) (fun δ => VF.Ge.sum fun ν _ => by
      split_ifs
      · exact hc ν
      · exact VF.Ge.zero 0)
    (fun δ hδ => Finset.sum_eq_zero fun ν _ => if_neg (by rintro rfl; exact hδ (hf ν)))
    (fun s => by
      convert hs s using 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp) (f ν)
  simpa using key

theorem exists_relation {m : ℕ} {σ : Type} {Y : Fin m → σ → C} (hY : ∀ δ x, V.Ge 0 (Y δ x))
    {T : Finset (Fin m)} (hT : IndepOn V Y T) {δ : Fin m}
    (hn : ¬ IndepOn V Y (insert δ T)) :
    ∃ r : Fin m → C, (∀ ε, V.Ge 0 (r ε)) ∧ r δ = 1 ∧ (∀ ε, ε ∉ T → ε ≠ δ → r ε = 0) ∧
      ∀ s, V.MM (∑ ε, r ε * Y ε s) := by
  unfold IndepOn at hn
  push Not at hn
  obtain ⟨c, hc, hc0, hs, ε₀, hε₀⟩ := hn
  have hcd : ¬ V.MM (c δ) := by
    intro hm
    have key := hT (fun ε => if ε = δ then 0 else c ε) (fun ε => by
        split_ifs
        · exact VF.Ge.zero 0
        · exact hc ε)
      (fun ε hε => by
        split_ifs with h
        · rfl
        · exact hc0 ε (by simp [h, hε]))
      (fun s => by
        have h1 : V.MM (Y δ s * c δ) := mm_int_mul (hY δ s) hm
        convert mm_sub (hs s) h1 using 1
        rw [eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ δ),
          ← Finset.add_sum_erase _ (fun ε => c ε * Y ε s) (Finset.mem_univ δ)]
        rw [Finset.sum_congr rfl (g := fun ε => c ε * Y ε s)
          (fun ε hε => by rw [if_neg (Finset.ne_of_mem_erase hε)])]
        simp only [if_true]
        ring) ε₀
    by_cases h : ε₀ = δ
    · exact hε₀ (h ▸ hm)
    · exact hε₀ (by simpa [h] using key)
  have h0 : c δ ≠ 0 := by intro h; exact hcd (h ▸ mm_zero)
  refine ⟨fun ε => (c δ)⁻¹ * c ε, fun ε => (ge_inv hcd).mul_int (hc ε), inv_mul_cancel₀ h0,
    fun ε h1 h2 => ?_, fun s => ?_⟩
  · simp only [hc0 ε (by simp [h1, h2]), mul_zero]
  · convert mm_int_mul (ge_inv hcd) (hs s) using 1
    simp only [Finset.mul_sum, mul_assoc]

theorem rank_nullity : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  intro C _ _ V σ m k Q hQ Y hY hk
  have hQ0 : Q ≠ 0 := by omega
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun T : Finset (Fin m) => IndepOn V Y T) Finset.card
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro c _ h0 _ δ
      rw [h0 δ (by simp)]
      exact mm_zero⟩
  have hT' : IndepOn V Y T := (Finset.mem_filter.1 hT).2
  have hn : ∀ δ, δ ∉ T → ¬ IndepOn V Y (insert δ T) := fun δ hδ h => by
    have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [Finset.card_insert_of_notMem hδ] at this
    omega
  have hrt : ∀ a : C, ∃ z : C, z ^ Q = a ∧ (a = 1 → z = 1) ∧ (a = 0 → z = 0) := by
    intro a
    by_cases h : a = 1
    · exact ⟨1, by simp [h], fun _ => rfl, fun h0 => absurd (h.symm.trans h0) one_ne_zero⟩
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (Nat.pos_of_ne_zero hQ0)
      exact ⟨z, hz, fun h1 => absurd h1 h, fun h0 => pow_eq_zero_iff hQ0 |>.mp (hz.trans h0)⟩
  choose rt hrt hrt1 hrt0 using hrt
  let e : Fin Tᶜ.card ↪ Fin m := (Tᶜ.orderEmbOfFin rfl).toEmbedding
  have he : ∀ ν, e ν ∉ T := fun ν => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ rfl ν)
  choose r hr hr1 hr0 hrs using fun ν => exists_relation hY hT' (hn _ (he ν))
  have hle := hk Tᶜ.card (fun ν δ => rt (r ν δ))
    (fun ν δ => ge_of_pow hQ0 (by rw [hrt]; exact hr ν δ))
    (fun c _ hs ν => by
      have h1 : V.MM (∑ b, c b * rt (r b (e ν))) := hs (e ν)
      rw [Finset.sum_eq_single ν (fun b _ hb => by
        rw [hrt0 _ (hr0 b _ (he ν) (fun h => hb (e.injective h).symm)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), hrt1 _ (hr1 ν), mul_one] at h1
      exact h1)
    (fun ν s => by simp only [hrt]; exact hrs ν s)
  refine ⟨T.card, (T.orderEmbOfFin rfl).toEmbedding, ?_,
    hT'.indepMod _ fun ν => Finset.orderEmbOfFin_mem _ rfl ν⟩
  rw [Finset.card_compl, Fintype.card_fin] at hle
  omega

end GlobalTheory.SemilinearNullity
end

