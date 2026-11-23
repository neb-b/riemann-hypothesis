module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffCob1HomogLiftBinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedInOfQuasiLogarithm
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDiff

theorem restr_inL_inR {R : Type} [CommRing R] {d : ℕ} (f : MvPowerSeries (Fin d) R) (i : Fin d) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ => 0))
        (pderiv (R := R) (Sum.inr i) (inL f)) = 0 ∧
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ => 0))
        (pderiv (R := R) (Sum.inr i) (inR f)) = C (lin f i) := by
  classical
  have hl : ∀ s : Fin d, constantCoeff (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
    fun s => by simp
  have hr : ∀ s : Fin d, constantCoeff (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R) = 0 :=
    fun s => by simp
  have hρ : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R)) (fun _ : Fin d => 0)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  constructor
  · unfold inL
    have hchain := GlobalTheory.PSChain.pderiv_subst_chain _ hl f (Sum.inr i)
    rw [hchain,
      Finset.sum_eq_zero (fun j _ => by rw [pderiv_X_of_ne (by simp), mul_zero]),
      ← substAlgHom_apply hρ, map_zero]
  · unfold inR
    have hchain := GlobalTheory.PSChain.pderiv_subst_chain _ hr f (Sum.inr i)
    rw [hchain, Finset.sum_eq_single i
      (fun j _ hj => by rw [pderiv_X_of_ne (by simpa using hj), mul_zero]) (by simp),
      pderiv_X_self, mul_one, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hr) hρ]
    have e : (fun s : Fin d => subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin d) R))
        (fun _ : Fin d => 0)) (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) R)) = 0 := by
      funext s; simp [subst_X hρ]
    rw [e, subst_zero_eq_C_constantCoeff, Algebra.algebraMap_self, map_id, RingHom.id_apply,
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp [lin]

end GlobalTheory.QLogDiff

namespace GlobalTheory.QLogDiff

theorem pderiv_map_eq {R S σ : Type} [CommRing R] [CommRing S] (h : R →+* S)
    (f : MvPowerSeries σ R) (i : σ) :
    pderiv (R := S) i (map h f) = map h (pderiv (R := R) i f) := by
  ext n; simp [coeff_pderiv, coeff_map]

theorem in_add {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {N : Ideal B}
    {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) : In N (f + g) := fun α => by
  obtain ⟨a, ha, ea⟩ := hf α
  obtain ⟨b, hb, eb⟩ := hg α
  exact ⟨a + b, N.add_mem ha hb, by rw [map_add (f := _), ea, eb, map_add (f := _)]⟩

theorem coeff_inr_of_unit {B : Type} [CommRing B] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hu : op μ (fun i => (X i : MvPowerSeries (Fin d) B)) (fun _ => 0) = fun i => X i)
    (hc : ∀ i, swap (μ i) = μ i) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr i) 1) (μ j) = if i = j then 1 else 0 := by
  classical
  have hs : HasSubst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i)) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have hw : HasSubst (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
      (fun i => X (Sum.inl i))) :=
    hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp)
  have key : subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i)) (μ j) = X j := by
    have h1 := congrFun hu j
    simp only [op, at2] at h1
    rw [← hc j, swap, at2, subst_comp_subst_apply hw hs]
    have e : (fun s => subst (Sum.elim (fun _ : Fin d => (0 : MvPowerSeries (Fin d) B)) (fun i : Fin d => X i))
        (Sum.elim (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) B))
          (fun i => X (Sum.inl i)) s)) = Sum.elim (fun i => X i) (fun _ => 0) := by
      funext s; cases s <;> simp [subst_X hs]
    rw [e]; exact h1
  have := (_root_.GlobalTheory.coeff_subst_restrict_sum (μ j)).2 (Finsupp.single i 1)
  rw [key, Finsupp.mapDomain_single] at this
  rw [← this, coeff_X]
  simp [Finsupp.single_left_inj one_ne_zero]

theorem dIn_of_QL : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O]
    [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B),
    IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → DIn N f := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf
  classical
  obtain ⟨-, hlin, hcob⟩ := hf
  have hμ0 : ∀ j, constantCoeff (up Q μ j) = 0 := fun j => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hμ.const j, map_zero]
  have haμ : HasSubst (up Q μ) := hasSubst_of_constantCoeff_zero hμ0
  obtain ⟨ρ, hρe⟩ : ∃ ρ : Fin d ⊕ Fin d → MvPowerSeries (Fin d) Q,
    ρ = Sum.elim (fun j => (X j : MvPowerSeries (Fin d) Q)) (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨ρB, hρBe⟩ : ∃ ρ : Fin d ⊕ Fin d → MvPowerSeries (Fin d) B,
    ρ = Sum.elim (fun j => (X j : MvPowerSeries (Fin d) B)) (fun _ => 0) := ⟨_, rfl⟩
  have hρ : HasSubst ρ := hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hρe])
  have hρB : HasSubst ρB := hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp [hρBe])
  have hmapρ : (fun s => map (algebraMap B Q) (ρB s)) = ρ := by
    funext s; cases s <;> simp [hρe, hρBe]
  have hmapsub : ∀ g : MvPowerSeries (Fin d ⊕ Fin d) B,
      map (algebraMap B Q) (subst ρB g) = subst ρ (map (algebraMap B Q) g) := by
    intro g; rw [map_subst hρB, hmapρ]
  have hunit : ∀ j, subst ρ (up Q μ j) = X j := by
    intro j
    have h1 := congrFun hμ.unit j
    simp only [op, at2] at h1
    rw [← hρBe] at h1
    have h2 := congrArg (map (algebraMap B Q)) h1
    rw [hmapsub, map_X] at h2
    exact h2
  let M : Matrix (Fin d) (Fin d) (MvPowerSeries (Fin d) B) :=
    fun j i => subst ρB (pderiv (R := B) (Sum.inr i) (μ j))
  have hM : ∀ j i, constantCoeff (M j i) = if j = i then 1 else 0 := by
    intro j i
    have h2 := (_root_.GlobalTheory.coeff_subst_restrict_sum (R := B) (pderiv (R := B) (Sum.inr i) (μ j))).1 0
    rw [← hρBe] at h2
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [M]
    rw [h2, Finsupp.mapDomain_zero, coeff_pderiv, zero_add, coeff_inr_of_unit μ hμ.unit hμ.comm i j]
    simp [eq_comm]
  let g : Fin d → MvPowerSeries (Fin d) Q :=
    fun i => subst ρ (pderiv (R := Q) (Sum.inr i) (subst (up Q μ) f))
  have hvg : ∀ i, ∑ j, pderiv (R := Q) j f * map (algebraMap B Q) (M j i) = g i := by
    intro i
    simp only [g, M]
    have hchain := GlobalTheory.PSChain.pderiv_subst_chain (up Q μ) hμ0 f (Sum.inr i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hchain, ← substAlgHom_apply hρ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, substAlgHom_apply, substAlgHom_apply, subst_comp_subst_apply haμ hρ, hmapsub]
    have e : (fun s => subst ρ (up Q μ s)) = X := funext hunit
    rw [e, subst_self, id, up, pderiv_map_eq]
  have hg : ∀ i, In N (g i) := by
    intro i
    have hsplit : subst (up Q μ) f = cob1 (up Q μ) f + inL f + inR f := by
      unfold cob1; abel
    have l4 := restr_inL_inR f i
    rw [← hρe] at l4
    simp only [g]
    rw [hsplit, map_add (f := _), map_add (f := _), ← substAlgHom_apply hρ, map_add (f := _), map_add (f := _)]
    simp only [substAlgHom_apply]
    rw [l4.1, l4.2, add_zero]
    refine in_add ?_ ?_
    · intro α
      have h2 := (_root_.GlobalTheory.coeff_subst_restrict_sum (R := Q)
        (pderiv (R := Q) (Sum.inr i) (cob1 (up Q μ) f))).1 α
      rw [← hρe] at h2
      rw [h2, coeff_pderiv]
      obtain ⟨b, hb, e⟩ := hcob (Finsupp.mapDomain Sum.inl α + Finsupp.single (Sum.inr i) 1)
      refine ⟨b, hb, ?_⟩
      rw [e, Finsupp.mapDomain_of_notMem_range _ _ (by simp), Nat.cast_zero, zero_add, mul_one]
    · intro α
      obtain ⟨b, hb, e⟩ := hlin i
      by_cases h0 : α = 0
      · exact ⟨b, hb, by rw [h0, coeff_zero_C, e]⟩
      · exact ⟨0, N.zero_mem, by rw [coeff_C, ite_eq_right h0, map_zero]⟩
  have hv := _root_.GlobalTheory.InvSolve.solve N M hM
    (fun j => pderiv (R := Q) j f) g hvg hg
  intro α i
  by_cases hi : α i = 0
  · exact ⟨0, N.zero_mem, by rw [hi, Nat.cast_zero, zero_mul, map_zero]⟩
  · have hle : Finsupp.single i 1 ≤ α := by
      rw [Finsupp.single_le_iff]; omega
    obtain ⟨b, hb, e⟩ := hv i (α - Finsupp.single i 1)
    refine ⟨b, hb, ?_⟩
    rw [← e, coeff_pderiv, tsub_add_cancel_of_le hle, Finsupp.tsub_apply, Finsupp.single_eq_same,
      mul_comm, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hi), Nat.cast_one, sub_add_cancel]

end GlobalTheory.QLogDiff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPairingChartPartialDerivativeModMaxStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_pairing_chart_partial_derivative_mod_max : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (ψ : G.A n →ₗ[O] O) (H : MvPowerSeries (Fin d ⊕ Fin d) O), LinearMap.mul' O O (TensorProduct.map ψ φ.ofConv (c.ev₂ n H)) - ψ (c.ev n (∑ i, u i • atZero (pderiv (R := O) (Sum.inr i) H))) ∈ m := by
  intro p O _ G d c n m hp u φ hφ ψ H
  have hCoeff (T : MvPowerSeries (Fin d ⊕ Fin d) O) (i : Fin d) (α : Fin d →₀ ℕ) :
      coeff α (atZero (pderiv (R := O) (Sum.inr i) T)) =
        coeff (α.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1) T := by
    rw [atZero, (coeff_subst_restrict_sum _).1, coeff_pderiv,
      Finsupp.mapDomain_of_notMem_range _ _ (by simp)]
    simp
  have hMonomial (α β : Fin d →₀ ℕ) (i : Fin d) :
      atZero (pderiv (R := O) (Sum.inr i) (monomial (α.sumElim β) (1 : O))) =
        lin (monomial β (1 : O)) i • monomial α (1 : O) := by
    classical
    ext γ
    rw [hCoeff, map_smul, lin, coeff_monomial, coeff_monomial, coeff_monomial]
    have hγ : γ.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 =
        γ.sumElim (Finsupp.single i 1) := by
      rw [Finsupp.sumElim_eq_add, Finsupp.mapDomain_single]
    rw [hγ]
    have h : γ.sumElim (Finsupp.single i 1) = α.sumElim β ↔
        γ = α ∧ Finsupp.single i 1 = β := by
      constructor
      · intro h
        exact ⟨Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inl j),
          Finsupp.ext fun j => by simpa using DFunLike.congr_fun h (Sum.inr j)⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    simp only [h]
    by_cases hα : γ = α <;> by_cases hβ : Finsupp.single i 1 = β <;> simp [hα, hβ]
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
  have key := GlobalTheory.PairingEv.mem_of_monomial_mem_of_tail_mem (Submodule.comap L m) (N₁ + N₂ + 1) ?_ ?_ H
  · rw [Submodule.mem_comap, hL] at key
    exact key
  · intro γ
    rw [Submodule.mem_comap, hL, ← Finsupp.comapDomain_sumElim_comapDomain γ]
    generalize Finsupp.comapDomain Sum.inl γ _ = α
    generalize Finsupp.comapDomain Sum.inr γ _ = β
    rw [GlobalTheory.PairingEv.chart_ev₂_monomial]
    simp only [hMonomial, smul_smul, ← Finset.sum_smul, map_smul, smul_eq_mul]
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
      rw [map_smul, hCoeff, hT, smul_zero]
      rw [map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single]
      omega
    rw [ha, hb, pow_one, pow_one, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul, map_nsmul,
      nsmul_eq_mul, nsmul_eq_mul]
    exact m.sub_mem (m.mul_mem_right _ hp) (m.mul_mem_right _ hp)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfLinearZeroCoboundaryZeroFractions
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.LogUniq

theorem eq_zero_of_linear_zero_coboundary_zero_fractions : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E]
    [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ R : MvPowerSeries (Fin d) E,
    lin R = 0 → cob1 (up E μ) R = 0 → R = 0 := by
  intro p _ O E _ _ _ hF d μ hμ R hlin hcob
  classical
  have hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : E) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
    rw [Nat.cast_mul, Nat.cast_pow]
    refine (hF.unit_p.pow a).mul ?_
    have hc : Nat.Coprime m p :=
      Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
    have := (hF.unit_coprime m hc).map (algebraMap O E)
    simpa using this
  have hL : IsLift (RingHom.id O) μ := ⟨hμ.const, hμ.unit, hμ.comm, by simpa using hμ⟩
  have hlow : ∀ i (α : Fin d ⊕ Fin d →₀ ℕ), α.degree ≤ 1 →
      coeff α (up E μ i) = coeff α (addLaw E d i) := by
    intro i α hα
    rw [up, coeff_map, GlobalTheory.CobHom.coeff_lift_low hL i α hα, GlobalTheory.Katz.LowLaw.coeff_addLaw]
    split_ifs <;> simp
  have hdeg : ∀ a e : Fin d →₀ ℕ, (Finsupp.sumElim a e).degree = (a + e).degree := by
    intro a e
    rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_sum_type,
      ← Finset.sum_add_distrib]
    simp
  have key : ∀ N : ℕ, ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α R = 0 := by
    intro N
    induction N with
    | zero => intro α h; omega
    | succ N ih =>
      intro α hα
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.1 hα) with h | h
      · exact ih α h
      have hc := (GlobalTheory.CobLead.cob_eq_additive_lead E d (up E μ) N hlow).1 R ih
      have hcoef : ∀ a e : Fin d →₀ ℕ, a + e = α →
          coeff (Finsupp.sumElim a e) (cob1 (addLaw E d) R) = 0 := by
        intro a e hae
        rw [← (hc _).2 (by rw [hdeg, hae, h]), hcob, map_zero]
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · have h0 : α = 0 := (Finsupp.degree_eq_zero_iff α).1 h
          subst h0
          have := hcoef 0 0 (by simp)
          rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial] at this
          simpa using this
        · obtain ⟨j, rfl⟩ := GlobalTheory.Katz.LowLaw.eq_single_of_degree_eq_one h
          exact congrFun hlin j
      · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
          by_contra! hc0
          have : α = 0 := Finsupp.ext hc0
          rw [this, map_zero] at h
          omega
        set a := α - Finsupp.single i 1 with ha
        have hae : a + Finsupp.single i 1 = α := by
          ext k
          simp only [ha, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
            Finsupp.single_apply]
          split_ifs with h1 <;> (try subst h1) <;> omega
        have ha0 : a ≠ 0 := by
          intro h0
          rw [h0, zero_add] at hae
          rw [← hae, Finsupp.degree_single] at h
          omega
        have hs0 : Finsupp.single i 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
        have := hcoef a (Finsupp.single i 1) hae
        rw [GlobalTheory.CobHom.coeff_cob1_additive_law_binomial, if_neg hs0, if_neg ha0, sub_zero, sub_zero, hae] at this
        have hpos : (∏ s, (α s).choose (a s)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.2 fun s _ => (Nat.choose_pos ?_).ne'
          rw [← hae]; simp
        exact (hunit _ hpos).mul_right_eq_zero.1 this
  ext α
  simpa using key (α.degree + 1) α (by omega)

end GlobalTheory.LogUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_unique_quotAut {O M G : Type*} [Ring O] [AddCommGroup M] [Module O M] [Group G]
    (W : Submodule O M) (act : O → G → G) (L L' : M → G)
    (hadd : ∀ a b, L (a + b) = L a * L b) (hadd' : ∀ a b, L' (a + b) = L' a * L' b)
    (hsm : ∀ (c : O) a, L (c • a) = act c (L a)) (hsm' : ∀ (c : O) a, L' (c • a) = act c (L' a))
    (hker : ∀ a, L a = 1 ↔ a ∈ W) (hker' : ∀ a, L' a = 1 ↔ a ∈ W)
    (hsurj : ∀ a, ∃ b, L b = L' a) (hsurj' : ∀ a, ∃ b, L' b = L a) :
    ∃! g : (M ⧸ W) ≃ₗ[O] (M ⧸ W),
      ∀ y, L (Function.surjInv (Submodule.mkQ_surjective W) (g (W.mkQ y))) = L' y := by
  have key : ∀ {L : M → G}, (∀ a b, L (a + b) = L a * L b) → (∀ a, L a = 1 ↔ a ∈ W) →
      ∀ a b, L a = L b ↔ W.mkQ a = W.mkQ b := by
    intro L hadd hker a b
    have h : L a = L (a - b) * L b := by rw [← hadd, sub_add_cancel]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, h]
    constructor
    · intro e
      exact mul_right_cancel (e.trans (_root_.one_mul _).symm)
    · intro e
      rw [e, _root_.one_mul]
  have eq := key hadd hker
  choose z hz using hsurj
  let f₀ : M →ₗ[O] M ⧸ W :=
    { toFun := fun y => W.mkQ (z y)
      map_add' := fun a b => by
        rw [← map_add (f := _), ← eq, hadd, hz, hz, hz, hadd']
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← LinearMap.map_smul, ← eq, hsm, hz, hz, hsm'] }
  have hf₀ : W ≤ LinearMap.ker f₀ := by
    intro y hy
    rw [LinearMap.mem_ker]
    show W.mkQ (z y) = 0
    rw [← map_zero W.mkQ, ← eq, hz, (hker' y).2 hy, (hker 0).2 W.zero_mem]
  let f := W.liftQ f₀ hf₀
  have hf : ∀ y, f (W.mkQ y) = W.mkQ (z y) := fun y => rfl
  have bij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨y, rfl⟩ := W.mkQ_surjective q
      rw [hf, ← map_zero W.mkQ, ← eq, hz, (hker 0).2 W.zero_mem, hker'] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hq
    · intro q
      obtain ⟨a, rfl⟩ := W.mkQ_surjective q
      obtain ⟨y, hy⟩ := hsurj' a
      exact ⟨W.mkQ y, by rw [hf, ← eq, hz, hy]⟩
  refine ⟨LinearEquiv.ofBijective f bij, ?_, ?_⟩
  · intro y
    rw [← hz y, eq, Function.surjInv_eq (Submodule.mkQ_surjective W)]
    rfl
  · intro g hg
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := W.mkQ_surjective q
    rw [LinearEquiv.ofBijective_apply, hf, ← Function.surjInv_eq (Submodule.mkQ_surjective W) (g (W.mkQ y)),
      ← eq, hg y, hz]

theorem etLev_rel_existsUnique (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)) :
    IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  intro hl hl'
  obtain ⟨hinj, hsur⟩ := hl.2.2.2 k (𝟙 _)
  obtain ⟨hinj', hsur'⟩ := hl'.2.2.2 k (𝟙 _)
  have canc : ∀ u v : Over.mk x ⟶ o.A,
      (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ u =
        (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ v → u = v := by
    intro u v h
    ext
    have := congrArg CommaMorphism.left h
    simpa using this
  have killed : ∀ (l₁ : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l₁ → ∀ a, ∀ c ∈ w0 ^ r,
      ((Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ l₁ a) ≫
        o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro l₁ h₁ a c hc
    rw [Category.assoc, ← h₁.2.1, h₁.2.2.1 _ (Submodule.subset_span ⟨c, hc, a, rfl⟩), comp_one]
  exact exists_unique_quotAut (wSub D w0 r) (fun c g => g ≫ o.act.act c) l l' hl.1 hl'.1 hl.2.1 hl'.2.1
    (fun a => ⟨fun h => hinj a (by rw [h, comp_one]), fun h => hl.2.2.1 a h⟩)
    (fun a => ⟨fun h => hinj' a (by rw [h, comp_one]), fun h => hl'.2.2.1 a h⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur _ (killed l' hl' a)
      exact ⟨y, canc _ _ hy⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur' _ (killed l hl a)
      exact ⟨y, canc _ _ hy⟩)

end GlobalTheory.UPel.HT.EtLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T T' : Over S) (l : D.La → (T ⟶ o.A)) (f : T' ⟶ T), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => f ≫ l y) := by
  intro p _ D R _ b N S s o w0 r T T' l f h
  obtain ⟨hadd, hlin, hker, hgeo⟩ := h
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ?_⟩
  · simp only [hadd, MonObj.comp_mul]
  · simp only [hlin, Category.assoc]
  · simp only [hker x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hgeo k (x ≫ f.left)
    let e : Over.mk (x ≫ T'.hom) ≅ Over.mk ((x ≫ f.left) ≫ T.hom) :=
      Over.isoMk (Iso.refl _) (by simp [Over.w f])
    have hfac : (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ f =
        e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) := by
      ext; simp [e]
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h1 : e.hom ≫ (Over.homMk (x ≫ f.left) rfl : Over.mk ((x ≫ f.left) ≫ T.hom) ⟶ T) ≫ l y = 1 := by
        rw [← Category.assoc, ← hfac, Category.assoc]; exact hy
      have h2 := congrArg (fun z => e.inv ≫ z) h1
      simpa [MonObj.comp_one] using h2
    · obtain ⟨y, hy⟩ := hsurj (e.inv ≫ g) (fun c hc => by
        exact (Category.assoc _ _ _).trans (by rw [hg c hc, MonObj.comp_one]))
      refine ⟨y, ?_⟩
      rw [← Category.assoc, hfac, Category.assoc, hy, Iso.hom_inv_id_assoc]

end GlobalTheory.UPel.HT.EtLev
end

