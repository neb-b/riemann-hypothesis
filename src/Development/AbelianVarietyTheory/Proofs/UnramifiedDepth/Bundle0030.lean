module

public import Mathlib
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0005
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0016
public import ReciprocityTheory.DualLattices.Bundle0029
public import ReciprocityTheory.DualLattices.Bundle0032
public import ReciprocityTheory.DualLattices.Bundle0026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeSubMainTermIntegralLowBidegree
section
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm

private theorem ge_coeff_rename_inl {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι →₀ ℕ, ν.degree = ∑ c, μ (Sum.inl c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inl F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective]

private theorem ge_coeff_rename_inr {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (F : MvPowerSeries ι' C) (μ : ι ⊕ ι' →₀ ℕ)
    (h : ∀ ν : ι' →₀ ℕ, ν.degree = ∑ c, μ (Sum.inr c) → V.Ge 0 (MvPowerSeries.coeff ν F)) :
    V.Ge 0 (MvPowerSeries.coeff μ (MvPowerSeries.rename Sum.inr F)) := by
  rw [MvPowerSeries.coeff_rename]
  apply VF.Ge.sum
  intro ν hν
  rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hν
  apply h
  rw [Finsupp.degree_eq_sum, ← hν]
  simp [Finsupp.mapDomain_apply_of_injective Sum.inr_injective]

private theorem constantCoeff_linPull_eq_zero {C : Type} [Field C] {σ ι : Type} [Fintype σ]
    [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (h : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  unfold linPull
  apply MvPowerSeries.constantCoeff_subst_eq_zero
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun x => by simp)
  · intro x
    simp
  · exact h

private theorem pderiv_inr_mainM_one {C : Type} [Field C] (V : VF C) {ι ι' : Type} [Fintype ι]
    [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (mainM V 1 Φ) =
      MvPowerSeries.rename Sum.inl ((V.l : C)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X c : MvPowerSeries ι C) ^ V.l) := by
  have hE : expE V.l 1 = 1 := by simp [expE]
  unfold mainM
  rw [hE, pow_one, pow_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, MvPowerSeries.rename_X, map_pow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_eq_single b]
  · rw [Derivation.map_smul, Derivation.leibniz, MvPowerSeries.pderiv_X_self, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr]
    simp [mul_comm]
  · intro x _ hx
    rw [Derivation.map_smul, Derivation.leibniz, Derivation.leibniz_pow,
      MvPowerSeries.pderiv_X_of_ne Sum.inl_ne_inr,
      MvPowerSeries.pderiv_X_of_ne (fun h => hx (Sum.inr_injective h))]
    simp
  · intro hb
    exact absurd (Finset.mem_univ b) hb

theorem mPlus_of_good_tangents : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 1 < d → ∀ (g : Fin 2) (a : ZMod d) (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N : ℕ) (em : Fin N ↪ I g) (v' : Fin X.n → I (1 - g) → C), (∀ δ, (X.G g).ty (Sum.inl (em δ)) = a) → (∀ δ x, (S g).al (em δ) 1 x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + ((1 : ℕ) : ZMod d) → v' b k = 0) → X.MPlusConcl g a N (fun δ => (S g).tan (em δ)) v' (fun b c => ∑ κ : J g, ∑ k : I (1 - g), -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k) := by
  intro C _ V d _ I J _ _ X hAlt hd g a S t hT N em v' hty hal hint hpure μ hμl hμr
  by_cases h0 : ∀ b, μ (Sum.inr b) = 0
  · rw [_root_.GlobalTheory.MainTerm.Axis.coeff_hM_sub_mainM_eq_zero _ _ _ _ _ X g a 1 _ _ _ v' _ μ h0]
    exact VF.Ge.zero 0
  simp only [not_forall] at h0
  obtain ⟨b, hb⟩ := h0
  have he_pure : ∀ (c : Fin N) (x : I g), (X.G g).ty (Sum.inl x) ≠ a →
      (fun δ => (S g).tan (em δ)) c x = 0 := by
    intro c x hx
    exact tan_pure (S g) (em c) x (by rw [hty c]; exact hx)
  obtain ⟨γ, hγ, hγeq⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hAlt g a 1 odd_one hd S t hT (Fin N) (Fin X.n)
    (fun δ => (S g).tan (em δ)) v' he_pure hint hpure b
  have h91 := _root_.GlobalTheory.MainTerm.hPullW_upG_toW C I g (Fin N) (Fin X.n) (fun δ => (S g).tan (em δ)) v'
  have hsingle : Finsupp.single (Sum.inr b) 1 ≤ μ :=
    Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hb)
  obtain ⟨μ', rfl⟩ : ∃ μ', μ = μ' + Finsupp.single (Sum.inr b) 1 :=
    ⟨μ - Finsupp.single (Sum.inr b) 1, (tsub_add_cancel_of_le hsingle).symm⟩
  have hl' : ∑ c, μ' (Sum.inl c) < V.l ^ 2 :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμl
  have hr' : ∑ b', μ' (Sum.inr b') < V.l :=
    lt_of_le_of_lt (Finset.sum_le_sum fun c _ => by rw [Finsupp.add_apply]; exact Nat.le_add_right _ _) hμr
  have hbl : μ' (Sum.inr b) + 1 < V.l := by
    refine lt_of_le_of_lt ?_ hμr
    have := Finset.single_le_sum (f := fun b' => (μ' + Finsupp.single (Sum.inr b) 1 : Fin N ⊕ Fin X.n →₀ ℕ) (Sum.inr b'))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
    simpa only [Finsupp.add_apply, Finsupp.single_eq_same] using this
  have hunit : V.v ((μ' (Sum.inr b) : C) + 1) = 0 := by
    have hc : ((μ' (Sum.inr b) : C) + 1) = ((μ' (Sum.inr b) + 1 : ℕ) : C) := by push_cast; ring
    rw [hc]
    exact ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_zero_of_coprime V.v V.v_l
      (Nat.coprime_of_lt_prime (by omega) hbl V.l_prime)
  have hne : ((μ' (Sum.inr b) : C) + 1) ≠ 0 := by
    intro h
    rw [h] at hunit
    simp at hunit
  set Φ : Fin X.n → Fin N → C := fun b c => ∑ κ : J g, ∑ k : I (1 - g),
    -((V.l : C) * (S g).be (em c) 1 κ) * X.pair g κ k * v' b k with hΦ
  set F := X.hM g a 1 (fun δ => (S g).tan (em δ)) v' - mainM V 1 Φ with hF
  have hcoeff : MvPowerSeries.coeff (μ' + Finsupp.single (Sum.inr b) 1) F =
      ((μ' (Sum.inr b) : C) + 1)⁻¹ * MvPowerSeries.coeff μ' (MvPowerSeries.pderiv (R := C) (Sum.inr b) F) := by
    rw [MvPowerSeries.coeff_pderiv]
    field_simp
  rw [hcoeff]
  refine VF.Ge.mul_int (inv_unit_int hunit) ?_
  set G : MvPowerSeries (Fin N) C :=
    (∑ κ : J g, (∑ k, X.pair g κ k * v' b k) • linPull (fun δ => (S g).tan (em δ)) ((S g).ze (t g) κ)) -
      (V.l : C)⁻¹ • ∑ c : Fin N, Φ b c • (MvPowerSeries.X c : MvPowerSeries (Fin N) C) ^ V.l with hG
  have hsplit : MvPowerSeries.pderiv (R := C) (Sum.inr b) F =
      MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2))
        (fun c => toW g ((fun δ => (S g).tan (em δ)) c)) (fun b => toW (1 - g) (v' b))) γ +
      MvPowerSeries.rename Sum.inl G := by
    rw [hF, map_sub, hγeq, pderiv_inr_mainM_one V Φ b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [h91.1, hG, map_sub, map_sum, map_smul]
    abel
  rw [hsplit, map_add (f := _)]
  refine VF.Ge.add ?_ ?_
  · have h2 : ∀ j g : Fin 2, j = g ∨ j = 1 - g := by decide
    refine _root_.GlobalTheory.LowerSubst.subst_int_on_lower C V (Fin N ⊕ Fin X.n) (WV I)
      (fun ν => ∑ c, ν (Sum.inl c) < V.l ^ 2 ∧ ∑ b', ν (Sum.inr b') < V.l) ?_ γ _ hγ ?_ ?_ μ' ⟨hl', hr'⟩
    · intro ν ν' hle hP
      exact ⟨lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inl c)) hP.1,
        lt_of_le_of_lt (Finset.sum_le_sum fun c _ => hle (Sum.inr c)) hP.2⟩
    · rintro ⟨j, x⟩
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT j).1 x)
      · simp only
        rw [h91.2, MvPowerSeries.constantCoeff_rename]
        exact constantCoeff_linPull_eq_zero _ _ ((hT (1 - g)).1 x)
    · rintro ⟨j, x⟩ ν hP
      rcases h2 j g with rfl | rfl
      · simp only
        rw [h91.1]
        apply ge_coeff_rename_inl V
        intro ν' hν'
        set_option synthInstance.maxHeartbeats 100000 in
          rw [(_root_.GlobalTheory.MainTerm.coeff_low_good C V d (I j) (J j) (X.G j) (S j) (t j) (hT j) N em hal ν'
          (by rw [hν']; exact hP.1)).1 x, map_sum]
        apply VF.Ge.sum
        intro δ _
        split_ifs
        · rw [MvPowerSeries.coeff_X]
          split_ifs
          exacts [VF.Ge.one, VF.Ge.zero 0]
        · rw [map_zero]
          exact VF.Ge.zero 0
      · simp only
        rw [h91.2]
        apply ge_coeff_rename_inr V
        intro ν' hν'
        exact _root_.GlobalTheory.MainTerm.linPull_coord_int_of_degree_lt C V d (I (1 - g)) (J (1 - g)) (X.G (1 - g)) (S (1 - g)) (t (1 - g))
          (hT (1 - g)) X.n v' hint ν' (by rw [hν']; exact hP.2) x
  · apply ge_coeff_rename_inl V
    intro ν hν
    have hdeg : ν.degree < V.l ^ 2 := by rw [hν]; exact hl'
    have h19 := (_root_.GlobalTheory.MainTerm.coeff_low_good C V d (I g) (J g) (X.G g) (S g) (t g) (hT g) N em hal ν hdeg).2
    have hz : MvPowerSeries.coeff ν G = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hG, map_sub, map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [MvPowerSeries.coeff_smul, h19, map_neg, map_sum, hΦ]
      have hL : (V.l : C) ≠ 0 := VF.l_ne_zero
      rw [sub_eq_zero]
      simp only [Finset.mul_sum, Finset.sum_mul, mul_neg, Finset.sum_neg_distrib, neg_mul]
      rw [neg_inj, Finset.sum_comm]
      refine Finset.sum_congr rfl fun δ _ => Finset.sum_congr rfl fun κ _ => Finset.sum_congr rfl fun k _ => ?_
      field_simp
    rw [hz]
    exact VF.Ge.zero 0

end GlobalTheory.MainTerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HtDualExists
section
noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory

private def htDualRing {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S) (ψ : LHom Λ S) :
    DualNum.DN Λ →+* (Dq.D : Type) :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((Dq.σ.1.comp ψ.1 : (Λ : Type) →ₐ[R₀] (Dq.D : Type)) :
      (Λ : Type) →+* (Dq.D : Type)) Dq.η) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, sq, Dq.η_sq, mul_zero])

private lemma htDualRing_C {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (r : (Λ : Type)) :
    htDualRing Dq ψ (Ideal.Quotient.mk _ (Polynomial.C r)) = Dq.σ.1 (ψ.1 r) := by
  rw [htDualRing, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  rfl

private lemma htDualRing_X {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) : htDualRing Dq ψ (DualNum.eta Λ) = Dq.η := by
  rw [htDualRing, DualNum.eta, Ideal.Quotient.lift_mk, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private lemma htDualRing_π {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) (x : DualNum.DN Λ) :
    Dq.π.1 (htDualRing Dq ψ x) = ψ.1 (DualNum.ev Λ x) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction f using Polynomial.induction_on with
  | C a => rw [htDualRing_C, Dq.sect, DualNum.ev_mk, Polynomial.eval_C]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | monomial n a _ =>
    have h := htDualRing_X Dq ψ
    rw [DualNum.eta] at h
    rw [DualNum.ev_mk, pow_succ Polynomial.X n, ← mul_assoc, map_mul, map_mul, h, map_mul, Dq.π_η]
    simp

private lemma htDual_exists {R₀ : Type} [CommRing R₀] {Λ S : LAlg R₀} (Dq : DualPair S)
    (ψ : LHom Λ S) :
    ∃ f : LHom (DualNum.dualPair Λ).D Dq.D,
      (∀ x, Dq.π.1 (f.1 x) = ψ.1 ((DualNum.dualPair Λ).π.1 x)) ∧
      (∀ x, f.1 ((DualNum.dualPair Λ).σ.1 x) = Dq.σ.1 (ψ.1 x)) ∧
      f.1 (DualNum.dualPair Λ).η = Dq.η := by
  let fA : DualNum.DN Λ →ₐ[R₀] (Dq.D : Type) :=
    { htDualRing Dq ψ with
      commutes' := fun r => by
        show htDualRing Dq ψ (algebraMap R₀ (DualNum.DN Λ) r) = _
        rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C,
          AlgHom.commutes, AlgHom.commutes] }
  refine ⟨mkLHom (R := (DualNum.dualPair Λ).D) fA fun a ha => ?_, fun x => htDualRing_π Dq ψ x,
    fun x => ?_, htDualRing_X Dq ψ⟩
  · refine (DualNum.dualPair Λ).isUnit_of_π ?_
    have h1 : IsUnit (Dq.π.1 (htDualRing Dq ψ a)) := ha.map Dq.π.1
    exact ψ.2.map_nonunit _ ((htDualRing_π Dq ψ a) ▸ h1)
  · show htDualRing Dq ψ (algebraMap (Λ : Type) (DualNum.DN Λ) x) = _
    rw [← Ideal.Quotient.mk_algebraMap, Polynomial.algebraMap_apply, htDualRing_C]
    rfl

private lemma ht_padic_val {p : ℕ} [Fact p.Prime] (a : ℤ_[p]) :
    ∃ b : ℤ_[p], a - ((PadicInt.toZMod a).val : ℤ_[p]) = p * b := by
  have h : a - ((PadicInt.toZMod a).val : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZMod (p := p)) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨b, hb⟩ := h
  exact ⟨b, by rw [← hb, mul_comm]⟩

theorem evHt_of_lam :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), 0 < g → maximalIdeal (D.K : Type) = ⊥ ∧ IsNilOver D.wd.ρ1 ∧ ∀ i : D.fin.ι,
    ∃ (Λ : LAlg R₀) (μ : LHom (D.fin.AAx i) Λ) (j : LHom (Tw.R 0) Λ) (ρΛ : LHom Λ D.K),
      IsNilOver ρΛ ∧ Function.Surjective μ.1 ∧ ρΛ.comp j = D.wd.ρ1 ∧ μ.comp (D.fin.sO i) = j.comp (Tw.q 0) ∧
      ∀ φ : LHom (D.fin.AAx i) Tw.O, φ.comp (D.fin.sO i) = LHom.id Tw.O →
        ∃ ψ : LHom Λ (Tw.R 0), ψ.comp μ = (Tw.q 0).comp φ ∧ ψ.comp j = LHom.id (Tw.R 0) ∧ D.wd.ρ1.comp ψ = ρΛ) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), EvHtStatement D) := by
  intro hLam R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D C _ _ k
  have hg : 0 < g := Nat.zero_lt_of_lt k.2
  obtain ⟨-, -, hL⟩ := hLam D hg
  clear hLam
  choose Λ μ j ρΛ _ hμ _ _ hψ using hL
  have hB1 := pairingProperties B
  have hchar := Tw.toATower.char_R 0
  have hcharΛ : ∀ i, ((p ^ (0 + 1) : ℕ) : (Λ i : Type)) = 0 := fun i => by
    rw [← map_natCast (j i).1, hchar, map_zero]
  have hy : ∀ i, (p ^ (0 + 1)) • B.map (μ i) (D.fin.y i) = 0 := fun i => by
    rw [← map_nsmul, zero_add, pow_one, D.fin.y_p, map_zero]
  choose h hh using fun i =>
    B.isHeight_exists hB1 (DualNum.dualPair (Λ i)) (p ^ (0 + 1)) (hcharΛ i) _ (hy i)
  choose F hF using fun i => hμ i (h i (D.ch.gb k))
  refine ⟨D.evAll C F, Submodule.subset_span ⟨F, rfl⟩, fun t => ?_⟩
  obtain ⟨hs, hyt, -⟩ := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ (red p g t)) (D.pt_p (red p g t))))
  change (D.ptMap (red p g t)).comp (D.fin.sO (D.ptIdx (red p g t))) = LHom.id Tw.O at hs
  change B.map (D.ptMap (red p g t)) (D.fin.y (D.ptIdx (red p g t))) = ptOf B D.L.τ (red p g t) at hyt
  obtain ⟨ψ, hψμ, -, -⟩ := hψ _ _ hs
  obtain ⟨f, f1, f2, f3⟩ := htDual_exists (Dt.Dp 0) ψ
  have H1 := B.isHeight_map hB1 _ _ ψ f f1 f2 f3 _ _ _ (hh (D.ptIdx (red p g t)))
  rw [← B.map_comp, hψμ, B.map_comp, hyt] at H1
  choose b hb using fun i => ht_padic_val (t i)
  have hp0 : ((p : ℕ) : (Tw.R 0 : Type)) = 0 := by simpa using hchar
  have hy2 : ∀ i, (p ^ (0 + 1)) • B.map (Tw.q 0) (D.L.τ i 0) = 0 := fun i => by
    rw [← map_nsmul, D.L.τ_tors, map_zero]
  have H2 := B.isHeight_sum hB1 (Dt.Dp 0) _ hchar Finset.univ
    (fun i => (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0))
    (fun i => by rw [smul_comm, hy2, smul_zero]) _
    (fun i => B.isHeight_zsmul hB1 (Dt.Dp 0) _ hchar (hy2 i) (D.L.ht_spec i 0) _)
  have e1 : ∑ i, (((red p g t i).val : ℕ) : ℤ) • B.map (Tw.q 0) (D.L.τ i 0) =
      B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ptOf, map_sum, map_nsmul, natCast_zsmul]
  rw [e1] at H2
  have hyp : (p ^ (0 + 1)) • B.map (Tw.q 0) (ptOf B D.L.τ (red p g t)) = 0 := by
    rw [← map_nsmul, zero_add, pow_one, D.pt_p, map_zero]
  have hU := LinearMap.congr_fun (B.isHeight_unique hB1 _ _ hchar _ hyp _ _ H1 H2) (D.ch.gb k)
  have hmem : (D.H.Ht *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k -
      (D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t))) ∈ RingHom.ker (Tw.q 0).1 := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    have e2 : (Tw.q 0).1 ((D.ptMap (red p g t)).1 (F (D.ptIdx (red p g t)))) =
        ψ.1 (h (D.ptIdx (red p g t)) (D.ch.gb k)) := by
      rw [← hF]
      exact (congrArg (fun u : LHom _ _ => u.1 (F (D.ptIdx (red p g t)))) hψμ).symm
    rw [e2]
    refine Eq.trans ?_ hU.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, Matrix.mulVec, dotProduct, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e3 : t i = ((red p g t i).val : ℤ_[p]) + p * b i := by
      rw [← hb i]
      show t i = ((PadicInt.toZMod (t i)).val : ℤ_[p]) + _
      ring
    rw [D.L.Ht_eq, Function.comp_apply, e3]
    rw [map_add (f := _), map_mul (algebraMap ℤ_[p] (Tw.O : Type)), map_natCast, map_natCast, map_mul, map_add (f := _),
      map_mul (Tw.q 0).1, map_natCast, map_natCast, hp0, zero_mul, add_zero, natCast_zsmul,
      LinearMap.smul_apply, nsmul_eq_mul, mul_comm]
    rfl
  rw [D.tower_zero_ker, Ideal.mem_span_singleton'] at hmem
  obtain ⟨r, hr⟩ := hmem
  refine ⟨r, ?_⟩
  rw [Dat.evAll, ← map_sub, ← hr, mul_comm]

end GlobalTheory
end
end

