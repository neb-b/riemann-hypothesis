module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Formalism.GradedWeylDivisibility.FinalB
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundary
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.WDer

theorem X_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (j : τ) : (X j : MvPowerSeries τ (Fr p k)) ∈ intBy p k τ 1 := by
  classical
  intro β
  refine ⟨if β = Finsupp.single j 1 then 1 else 0, ?_⟩
  rw [coeff_X, one_mul]
  split_ifs <;> simp

theorem lift_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (f : MvPowerSeries τ k) : lift p f ∈ intBy p k τ 1 := by
  intro β
  exact ⟨WittVector.teichmuller p (coeff β f), by rw [coeff_lift, one_mul]⟩

theorem coboundaryOne_teichmullerLift_mem_integralDifferential (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
    (g : MvPowerSeries (Fin d) (Fr p k)) (hg : g ∈ quasiInt p k (Fin d)) :
    cob1 (fun i => lift p (μ i)) g ∈ quasiInt p k (Fin d ⊕ Fin d) := by
  unfold cob1 inL inR
  refine sub_mem (sub_mem ?_ ?_) ?_
  · exact _root_.GlobalTheory.Katz.subst_mem_quasiInt p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_lift p (hμ.const i)) (fun i => lift_mem_intBy p k _) hg
  · exact _root_.GlobalTheory.Katz.subst_mem_quasiInt p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg
  · exact _root_.GlobalTheory.Katz.subst_mem_quasiInt p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  intro p _ k _ _ _ d μ hμ N g h hN hg hh hcob α i hα
  classical
  by_cases hi : α i = 0
  · exact ⟨0, by simp [hi]⟩
  set β : Fin d →₀ ℕ := α - Finsupp.single i 1 with hβdef
  have hαβ : α = β + Finsupp.single i 1 := by
    ext j
    simp only [hβdef, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with hj
    · subst hj; omega
    · omega
  have hβdeg : β.degree + 1 = N := by
    rw [← hα, hαβ, map_add (f := _), Finsupp.degree_single]
  have hβ0 : β ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hβdeg
    omega
  set γ : Fin d ⊕ Fin d →₀ ℕ := β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 with hγdef
  have hγdeg : γ.degree = N := by
    rw [hγdef, map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single, hβdeg]
  have hγi : γ (Sum.inr i) = 1 := by
    rw [hγdef, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, Finsupp.single_eq_same, zero_add]
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

  obtain ⟨wg, hwg⟩ := coboundaryOne_teichmullerLift_mem_integralDifferential p k d μ hμ g hg γ (Sum.inr i)
  rw [hγi, Nat.cast_one, one_mul] at hwg
  obtain ⟨wt, hwt⟩ := hcob γ hγdeg

  have hlin : ∀ j (a : Fin d ⊕ Fin d →₀ ℕ), a.degree ≤ 1 →
      coeff a (lift p (μ j)) = coeff a (addLaw (Fr p k) d j) :=
    fun j a ha => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ j a ha).2
  have hlead := ((_root_.GlobalTheory.CobLead.cob_eq_additive_lead (Fr p k) d (fun j => lift p (μ j)) N hlin).1 h hh γ).2
    hγdeg.le
  have hhom := (_root_.GlobalTheory.homog_cob_addLaw (Fr p k) d N).2.2.2 h β i hβ0
  rw [formalCoboundary_add (fun j => constantCoeff_lift p (hμ.const j)), map_add (f := _), hwg, hlead,
    hhom, ← hαβ] at hwt
  refine ⟨wt - wg, ?_⟩
  have hai : α i = β i + 1 := by
    conv_lhs => rw [hαβ]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [map_sub, ← hwt, hai, add_sub_cancel_left]

end GlobalTheory.Katz.WDer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPairingChartPartialDerivativeModMax
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.PairingEv

theorem mem_of_monomial_mem_of_tail_mem {σ R : Type} [CommRing R] [Fintype σ]
    (S : Submodule R (MvPowerSeries σ R)) (N : ℕ) (h1 : ∀ γ : σ →₀ ℕ, monomial γ (1 : R) ∈ S)
    (h2 : ∀ T : MvPowerSeries σ R, (∀ α : σ →₀ ℕ, α.degree < N → coeff α T = 0) → T ∈ S)
    (H : MvPowerSeries σ R) : H ∈ S := by
  classical
  have hP : ∀ P : MvPolynomial σ R, (P : MvPowerSeries σ R) ∈ S := fun P => by
    induction P using MvPolynomial.induction_on' with
    | monomial γ a =>
      rw [MvPolynomial.coe_monomial]
      have := S.smul_mem a (h1 γ)
      rwa [← map_smul, smul_eq_mul, mul_one] at this
    | add P Q hP hQ => rw [MvPolynomial.coe_add]; exact S.add_mem hP hQ
  have := S.add_mem (hP (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H))
    (h2 (H - (trunc' R (Finsupp.equivFunOnFinite.symm fun _ => N) H : MvPolynomial σ R)) ?_)
  · simpa using this
  · intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos, sub_self]
    intro j
    exact (Finsupp.le_degree j α).trans hα.le

theorem coeff_atZero_pderiv_inr {R : Type} [CommRing R] {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) (i : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (atZero (pderiv (R := R) (Sum.inr i) H)) =
      coeff (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) H := by
  rw [atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv,
    Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
  simp

theorem atZero_pderiv_inr_monomial {R : Type} [CommRing R] {d : ℕ} (α β : Fin d →₀ ℕ) (i : Fin d) :
    atZero (pderiv (R := R) (Sum.inr i) (monomial (α.sumElim β) (1 : R))) =
      lin (monomial β (1 : R)) i • monomial α (1 : R) := by
  classical
  ext γ
  rw [coeff_atZero_pderiv_inr, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]
  have : γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 = γ.sumElim (Finsupp.single i 1) := by
    rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]
  rw [this]
  have h2 : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔ γ = α ∧ Finsupp.single i 1 = β := by
    constructor
    · intro h
      exact ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
        Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
    · rintro ⟨rfl, rfl⟩; rfl
  simp only [h2]
  by_cases h3 : γ = α <;> by_cases h4 : Finsupp.single i 1 = β <;> simp [h3, h4]

theorem chart_ev₂_monomial {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}
    (c : QLog.Chart G d) (n : ℕ) (α β : Fin d →₀ ℕ) :
    c.ev₂ n (monomial (α.sumElim β) 1) = c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1) := by
  simp only [monomial_one_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, (c.isEval n).1, (c.isEval₂ n).1, Sum.elim_inl,
    Sum.elim_inr, Finsupp.sumElim_inl, Finsupp.sumElim_inr]
  have e1 := map_prod (Algebra.TensorProduct.includeLeft : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ α j) Finset.univ
  have e2 := map_prod (Algebra.TensorProduct.includeRight : G.A n →ₐ[O] G.A n ⊗[O] G.A n)
    (fun j => c.x n j ^ β j) Finset.univ
  simp only [map_pow, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at e1 e2
  rw [← e1, ← e2, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem pairing_ev₂_sub_mem : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) ∈ m := by
  intro p O _ G d c n m hp u φ hφ ψ H
  obtain ⟨N₁, h₁⟩ := (c.isEval n).2 1
  obtain ⟨N₂, h₂⟩ := (c.isEval₂ n).2 1
  have hs : HasSubst (Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp)
  let D : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] MvPowerSeries (Fin d) O :=
    ∑ i, u i • ((substAlgHom hs).toLinearMap ∘ₗ (pderiv (R := O) (Sum.inr i)).toLinearMap)
  have hD : ∀ H, D H = ∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H) := fun H => by
    simp [D, atZero, LinearMap.sum_apply, coe_substAlgHom]
  let P : G.A n ⊗[O] G.A n →ₗ[O] O := LinearMap.mul' O O ∘ₗ TensorProduct.map ψ φ.ofConv
  let L : MvPowerSeries (Fin d ⊕ Fin d) O →ₗ[O] O :=
    P ∘ₗ (c.ev₂ n).toLinearMap - ψ ∘ₗ (c.ev n).toLinearMap ∘ₗ D
  have hL : ∀ H, L H = P (c.ev₂ n H) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) :=
    fun H => by rw [← hD]; rfl
  have key := mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H
  · rw [Submodule.mem_comap, hL] at key
    exact key
  · intro γ
    rw [Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]
    generalize Finsupp.comapDomain Sum.inl γ _ = α
    generalize Finsupp.comapDomain Sum.inr γ _ = β
    rw [chart_ev₂_monomial]
    simp only [atZero_pderiv_inr_monomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]
    have := m.mul_mem_left (ψ (c.ev n (monomial α 1))) (hφ (monomial β 1))
    convert this using 1
    have e : P (c.ev n (monomial α 1) ⊗ₜ[O] c.ev n (monomial β 1)) =
        ψ (c.ev n (monomial α 1)) * φ (c.ev n (monomial β 1)) := by
      simp only [P, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply]
    rw [e]; ring
  · intro T hT
    rw [Submodule.mem_comap, hL]
    obtain ⟨a, ha⟩ := h₂ T fun α hα => hT α (by omega)
    obtain ⟨b, hb⟩ := h₁ (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) T)) fun α hα => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [map_smul, coeff_atZero_pderiv_inr, hT, smul_zero]
      rw [map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single]
      omega
    rw [ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul]
    exact m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)

end GlobalTheory.PairingEv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperators
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem rTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ A A) (x y : A ⊗[ℚ] B) :
    LinearMap.rTensor B (D : A →ₗ[ℚ] A) (x * y) =
      x * LinearMap.rTensor B (D : A →ₗ[ℚ] A) y + y * LinearMap.rTensor B (D : A →ₗ[ℚ] A) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, add_tmul]
      rw [mul_comm b' b]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add (f := _), hx, hx']; abel

theorem lTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (x y : A ⊗[ℚ] B) :
    LinearMap.lTensor A (D : B →ₗ[ℚ] B) (x * y) =
      x * LinearMap.lTensor A (D : B →ₗ[ℚ] B) y + y * LinearMap.lTensor A (D : B →ₗ[ℚ] B) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, tmul_add]
      rw [mul_comm a' a]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add (f := _), hx, hx']; abel

theorem natAdd_ne_castAdd' {p q : ℕ} (b : Fin q) (d : Fin p) : Fin.natAdd p b ≠ Fin.castAdd q d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

theorem castAdd_ne_natAdd' {p q : ℕ} (a : Fin p) (d : Fin q) : Fin.castAdd q a ≠ Fin.natAdd p d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

theorem resT_der_left_X (p q : ℕ) (c d : Fin p) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) (X v)) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]
    | right t =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
  | right b =>
    rw [if_neg (natAdd_ne_castAdd' b d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]

theorem resT_der_right_X (p q : ℕ) (c d : Fin q) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) (X v)) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    rw [if_neg (castAdd_ne_natAdd' a d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]
  | right b =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
    | right t =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]

theorem weight_rowW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (x : Fin N) :
    Finsupp.weight (rowW N N) m x = ∑ s, m (x, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [rowW, Pi.single_apply]

theorem weight_colW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (y : Fin N) :
    Finsupp.weight (colW N N) m y = ∑ a, m (a, y) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]

theorem resT_monomial_eq_zero (p q : ℕ) (m : Fin (p + q) × Fin (p + q) →₀ ℕ) (a : ℚ)
    (v : Fin (p + q) × Fin (p + q)) (hv : resVarT ℚ p q v = 0) (hm : m v ≠ 0) : resT ℚ p q (monomial m a) = 0 := by
  rw [resT, aeval_monomial]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm) (by simp only [hv]; exact zero_pow hm)

theorem resVarT_castAdd_natAdd (p q : ℕ) (a : Fin p) (t : Fin q) :
    resVarT ℚ p q (Fin.castAdd q a, Fin.natAdd p t) = 0 := by simp [resVarT]

theorem resVarT_natAdd_castAdd (p q : ℕ) (b : Fin q) (s : Fin p) :
    resVarT ℚ p q (Fin.natAdd p b, Fin.castAdd q s) = 0 := by simp [resVarT]

theorem resT_wrong_degree (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (ν : Fin (p + q) → ℕ) (t : ℚ)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f ν)
    (hsum : ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f)
    (ht : t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ)) : resT ℚ p q f = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hc : AddMonoidAlgebra.coeff f m ≠ 0 := mem_support_iff.1 hm
  by_contra hne
  have h1 : ∀ (a : Fin p) (t' : Fin q), m (Fin.castAdd q a, Fin.natAdd p t') = 0 := by
    intro a t'
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_castAdd_natAdd p q a t') h0)
  have h2 : ∀ (b : Fin q) (s : Fin p), m (Fin.natAdd p b, Fin.castAdd q s) = 0 := by
    intro b s
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_natAdd_castAdd p q b s) h0)
  have hw : Finsupp.weight (colW (p + q) (p + q)) m = ν := hf hc
  have ht' : t = ∑ c : Fin p, ((Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) : ℕ) : ℚ) := by
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    rw [coeff_sum, coeff_smul, smul_eq_mul] at h3
    simp only [Formalism.CohomologicalDescent.LR.coeff_der_diag] at h3
    rw [← Finset.sum_mul] at h3
    exact (mul_right_cancel₀ hc h3).symm
  have key : ∑ c : Fin p, Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) =
      ∑ c : Fin p, Finsupp.weight (colW (p + q) (p + q)) m (Fin.castAdd q c) := by
    simp only [weight_rowW_apply, weight_colW_apply, Fin.sum_univ_add, h1, h2, Finset.sum_const_zero, add_zero]
    exact Finset.sum_comm
  apply ht
  rw [ht', ← hw]
  exact_mod_cast key

theorem dualWeyl_resDer : ResDer := by
  intro p q f
  refine ⟨fun c d => ?_, fun c d => ?_, fun ν t hf hsum ht => resT_wrong_degree p q f ν t hf hsum ht⟩
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul]
      simp
    | add g h hg hh => rw [map_add (f := _), map_add (f := _), map_add (f := _), hg, hh, map_add (f := _)]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, rTensor_der_mul, resT_der_left_X, hg]
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]
      simp
    | add g h hg hh => rw [map_add (f := _), map_add (f := _), map_add (f := _), hg, hh, map_add (f := _)]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, lTensor_der_mul, resT_der_right_X, hg]

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylSchurEndomorphism
section
open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.LeviCut

theorem eV_coe_fin (N : ℕ) (ν : Fin N → ℕ) (a b : Fin N) (x : dualWeyl ℚ N N ν) :
    ((eV N ν a b x : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) =
      Formalism.CohomologicalDescent.LR.der N N a b (x : MvPolynomial (Fin N × Fin N) ℚ) := by
  simp only [eV, dif_pos (And.intro a.isLt b.isLt)]
  rfl

theorem nablaSchur : NablaSchur := by
  intro N ν hν S hS hfix
  have hc : ∀ (a b : Fin N) (x : dualWeyl ℚ N N ν), eV N ν a b (S x) = S (eV N ν a b x) := by
    intro a b x
    have h := LinearMap.congr_fun (hS a a.isLt b b.isLt) x
    simpa only [Module.End.mul_apply] using h
  set v : dualWeyl ℚ N N ν := ⟨hw ℚ le_rfl ν, hwMem ℚ N N le_rfl ν hν⟩ with hv

  have hder : ∀ a b : Fin N, a < b →
      Formalism.CohomologicalDescent.LR.der N N a b ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab
    have h1 : eV N ν a b v = 0 := by
      apply Subtype.ext
      rw [eV_coe_fin]
      exact Formalism.CohomologicalDescent.LR.der_hw_raise ν a b hab
    rw [← eV_coe_fin, hc, h1, map_zero]
    rfl
  have hkill : ∀ a b : Fin N, a < b → ∀ k : ℕ, 1 ≤ k →
      rowDiv ℚ a b k ((S v : dualWeyl ℚ N N ν) : MvPolynomial (Fin N × Fin N) ℚ) = 0 := by
    intro a b hab k hk
    obtain ⟨k, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Formalism.CohomologicalDescent.LR.der_pow a b (ne_of_lt hab), pow_succ, Module.End.mul_apply]
    have h2 := hder a b hab
    change (Formalism.CohomologicalDescent.LR.der N N a b : Module.End ℚ (MvPolynomial (Fin N × Fin N) ℚ)) _ = 0 at h2
    rw [h2, map_zero, smul_zero]
  obtain ⟨c, hcv⟩ := hwLine ℚ N N le_rfl ν hν _ (S v).2 hkill
  have hc1 : c = 1 := by
    rw [hcv, Formalism.CohomologicalDescent.LR.fock_smul_right] at hfix
    have hpos := Formalism.CohomologicalDescent.LR.hw_norm_pos ν
    have h3 : (c - 1) * fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) = 0 := by rw [sub_mul, hfix, one_mul, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · linarith
    · exact absurd h (ne_of_gt hpos)
  have hSv : S v = v := by
    apply Subtype.ext
    rw [hcv, hc1, one_smul]

  set M : Submodule ℚ (MvPolynomial (Fin N × Fin N) ℚ) :=
    (LinearMap.ker (S - 1)).map (dualWeyl ℚ N N ν).subtype with hM
  have hmem : ∀ x : dualWeyl ℚ N N ν, S x = x → (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by
    intro x hx
    refine ⟨x, ?_, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hx, sub_self]
  have hle : M ≤ dualWeyl ℚ N N ν := by
    rintro f ⟨x, _, rfl⟩
    exact x.2
  have hcl : RowDivClosed M := by
    intro a b k
    refine Formalism.CohomologicalDescent.LR.closed_of_der a b M ?_ k
    rintro f ⟨x, hx, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hx
    have h4 := hmem (eV N ν a b x) (by rw [← hc, hx])
    rw [eV_coe_fin] at h4
    exact h4
  have hhw : hw ℚ le_rfl ν ∈ M := hmem v hSv
  have heq := closedEqNabla N N le_rfl ν hν M hle hcl hhw
  apply LinearMap.ext
  intro x
  have hx : (x : MvPolynomial (Fin N × Fin N) ℚ) ∈ M := by rw [heq]; exact x.2
  obtain ⟨y, hy, hyx⟩ := hx
  have hyx' : y = x := Subtype.ext hyx
  subst hyx'
  simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hy
  rw [Module.End.one_apply]
  exact hy

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ n : ℤ, (∀ x : H R (sp c.pt) F n, ∃ j y, pull R (spMap (c.ι.app j).hom) F n y = x) ∧ ∀ j (y : H R (sp (D.obj j)) F n), pull R (spMap (c.ι.app j).hom) F n y = 0 → ∃ (k : J) (f : j ⟶ k), pull R (spMap (D.map f).hom) F n y = 0 := by
  first
  | exact @GlobalTheory.EtC.RingContH.main
  | exact GlobalTheory.EtC.RingContH.main
  | (intros; apply GlobalTheory.EtC.RingContH.main <;> assumption)
end

