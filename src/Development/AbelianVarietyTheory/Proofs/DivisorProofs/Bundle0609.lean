module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstEqZeroOfDegree
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries TensorProduct GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup WithConv

namespace GlobalTheory.EvMul

theorem coeff_subst_eq_zero_of_degree {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, constantCoeff (a i) = 0) {N : ℕ}
    {f : MvPowerSeries σ R} (hf : ∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0)
    (β : τ →₀ ℕ) (hβ : β.degree < N) : coeff β (subst a f) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha)]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree < N
  · rw [hf α h, zero_smul]
  · rw [coeff_of_lt_order (f := α.prod fun s e => a s ^ e) (d := β) ?_, smul_zero]
    refine lt_of_lt_of_le (b := ((α.degree : ℕ) : ℕ∞)) (by exact_mod_cast (by omega : β.degree < α.degree)) ?_
    rw [Finsupp.prod]
    refine le_trans ?_ (le_order_prod _ _)
    show ((∑ i ∈ α.support, α i : ℕ) : ℕ∞) ≤ _
    push_cast
    exact Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have h : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun l => (X l : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = at2 (μ i) (nmul μ k) (fun l => X l) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    rw [e, at2]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (hμ i)

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

theorem mulBy_succ_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (k : ℕ) (a : A) :
    PDiv.mulBy O A (k + 1) a = Algebra.TensorProduct.lmul' O
      (Algebra.TensorProduct.map (PDiv.mulBy O A k : A →ₐ[O] A) (AlgHom.id O A) (Coalgebra.comul a)) := by
  rw [PDiv.mulBy, pow_succ]
  rfl

theorem mulBy_zero_apply {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] (a : A) :
    PDiv.mulBy O A 0 a = algebraMap O A (Coalgebra.counit a) := by
  rw [PDiv.mulBy, pow_zero]
  rfl

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]

theorem pow_dvd_map {A B : Type} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B]
    (φ : A →ₐ[O] B) {m : ℕ} {a : A} (h : (p : A) ^ m ∣ a) : (p : B) ^ m ∣ φ a := by
  obtain ⟨y, rfl⟩ := h
  exact ⟨φ y, by rw [map_mul, map_pow, map_natCast]⟩

theorem cont_subst {σ τ : Type} [Finite τ] {A : Type} [CommRing A] [Algebra O A]
    (E : MvPowerSeries σ O →ₐ[O] A)
    (hE : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : σ →₀ ℕ, α.degree < N → coeff α f = 0) → (p : A) ^ m ∣ E f)
    {a : τ → MvPowerSeries σ O} (ha : ∀ i, constantCoeff (a i) = 0) :
    ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : τ →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : A) ^ m ∣ E.comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha)) f := by
  intro m
  obtain ⟨N, hN⟩ := hE m
  exact ⟨N, fun f hf => by
    rw [AlgHom.comp_apply, substAlgHom_apply]
    exact hN _ (coeff_subst_eq_zero_of_degree ha hf)⟩

variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_subst_of_gen (n k : ℕ)
    (hk : ∀ i, c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i))
    (h : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  have ha := constantCoeff_nmul c.isLaw.const k
  have gens : ∀ i, ((c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero ha))) (X i) =
      ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) (X i) := by
    intro i
    rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X, (c.isEval n).1, hk]
    rfl
  have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
      (p : G.A n) ^ m ∣ ((PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n).comp (c.ev n)) f := by
    intro m
    obtain ⟨N, hN⟩ := (c.isEval n).2 m
    exact ⟨N, fun f hf => by
      rw [AlgHom.comp_apply]
      exact pow_dvd_map (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (hN f hf)⟩
  have e := _root_.GlobalTheory.PadicMvPowerSeriesExt.algHom_ext p O (Fin d) (G.A n) _ _ gens (cont_subst (c.ev n) (c.isEval n).2 ha) cont'
  have := DFunLike.congr_fun e h
  rw [AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply] at this
  exact this

end GlobalTheory.EvMul

namespace GlobalTheory.EvMul

variable {p : ℕ} {O : Type} [CommRing O]
variable [IsAdicComplete (Ideal.span {(p : O)}) O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_nmul (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  induction k generalizing i with
  | zero =>
    rw [mulBy_zero_apply, c.aug, map_zero]
    exact map_zero _
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun l => (X l : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    set Θ := (c.ev n).comp (substAlgHom (R := O) (hasSubst_of_constantCoeff_zero hs)) with hΘ
    set Λ := (Algebra.TensorProduct.lmul' O).comp ((Algebra.TensorProduct.map
      (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) (AlgHom.id O (G.A n))).comp (c.ev₂ n)) with hΛ
    have gens : ∀ j, Θ (X j) = Λ (X j) := by
      rintro (j | j)
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inl, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, mul_one]
        exact ih j
      · rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_X,
          (c.isEval₂ n).1]
        simp only [Sum.elim_inr, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
          Algebra.TensorProduct.lmul'_apply_tmul, map_one, one_mul]
        exact (c.isEval n).1 j
    have cont' : ∀ m : ℕ, ∃ N : ℕ, ∀ f, (∀ α : Fin d ⊕ Fin d →₀ ℕ, α.degree < N → coeff α f = 0) →
        (p : G.A n) ^ m ∣ Λ f := by
      intro m
      obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
      exact ⟨N, fun f hf => by
        rw [hΛ, AlgHom.comp_apply, AlgHom.comp_apply]
        exact pow_dvd_map _ (pow_dvd_map _ (hN f hf))⟩
    have e : Θ = Λ := _root_.GlobalTheory.PadicMvPowerSeriesExt.algHom_ext p O (Fin d ⊕ Fin d) (G.A n) Θ Λ gens
      (cont_subst (c.ev n) (c.isEval n).2 hs) cont'
    have e1 : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun l => X l) (c.μ i) := by
      unfold nmul; rw [Function.iterate_succ_apply']; rfl
    have e2 := DFunLike.congr_fun e (c.μ i)
    rw [hΘ, hΛ, AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, substAlgHom_apply,
      c.comul] at e2
    rw [e1, e2, mulBy_succ_apply]

theorem ev_subst_nmul : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (n k : ℕ) (h : MvPowerSeries (Fin d) O),
    c.ev n (subst (nmul c.μ k) h) = PDiv.mulBy O (G.A n) k (c.ev n h) := by
  intro p _ O _ _ G d c n k h
  exact ev_subst_of_gen c n k (ev_nmul c n k) h

end GlobalTheory.EvMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffEqZeroOfEvalEqComul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory

theorem constantCoeff_eq_zero_of_eval_eq_comul : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : O)}) O] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, constantCoeff (μ i) = 0 := by
  intro p O A _ _ _ _ d x E₂ μ hx hE hμ i
  let φ : A ⊗[O] A →ₐ[O] O := Algebra.TensorProduct.lift (Bialgebra.counitAlgHom O A)
    (Bialgebra.counitAlgHom O A) (fun _ _ => Commute.all _ _)
  have hφ : ∀ a b : A, φ (a ⊗ₜ[O] b) = Coalgebra.counit (R := O) a * Coalgebra.counit (R := O) b := by
    intro a b
    simp [φ, Algebra.TensorProduct.lift_tmul, Bialgebra.counitAlgHom_apply]

  have hφc : ∀ a : A, φ (Coalgebra.comul (R := O) a) = Coalgebra.counit (R := O) a := by
    intro a
    have hL : (φ.toLinearMap : A ⊗[O] A →ₗ[O] O) =
        (LinearMap.mul' O O) ∘ₗ (LinearMap.lTensor O (Coalgebra.counit (R := O) (A := A))) ∘ₗ
          (LinearMap.rTensor A (Coalgebra.counit (R := O) (A := A))) := by
      apply TensorProduct.ext'
      intro a b
      simp [hφ]
    have := LinearMap.congr_fun hL (Coalgebra.comul (R := O) a)
    simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply, Coalgebra.rTensor_counit_comul,
      LinearMap.lTensor_tmul, LinearMap.mul'_apply, one_mul] at this
    exact this
  let c : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) O →+* O) with
      commutes' := fun r => by
        first
        | exact constantCoeff_C r
        | (rw [MvPowerSeries.algebraMap_apply]; simp)
        | (show constantCoeff (C r) = r; simp)
        | simp [MvPowerSeries.algebraMap_apply'] }
  have hc : ∀ f, c f = constantCoeff f := fun _ => rfl
  have hnil : ∀ j : Fin d ⊕ Fin d, ∃ N : ℕ, (p : O) ∣ (fun _ => (0 : O)) j ^ N :=
    fun _ => ⟨1, by simp⟩
  obtain ⟨⟨E, _, huniq⟩, _⟩ := _root_.GlobalTheory.CEval.continuous_eval p O O (Fin d ⊕ Fin d) (fun _ => (0 : O)) hnil
  have h1 : IsEval p (fun _ => (0 : O)) (φ.comp E₂) := by
    refine ⟨?_, ?_⟩
    · intro j
      rw [AlgHom.comp_apply, hE.1 j]
      cases j with
      | inl k => simp [hφ, hx]
      | inr k => simp [hφ, hx]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨a, ha⟩ := hN f hf
      refine ⟨φ a, ?_⟩
      rw [AlgHom.comp_apply, ha, map_mul, map_pow, map_natCast]
  have h2 : IsEval p (fun _ => (0 : O)) c := by
    refine ⟨fun j => by simp [hc], fun m => ⟨1, fun f hf => ?_⟩⟩
    have : constantCoeff f = 0 := by
      have := hf 0 (by simp)
      simpa [coeff_zero_eq_constantCoeff_apply] using this
    rw [hc, this]; exact dvd_zero _
  have e1 := huniq _ h1
  have e2 := huniq _ h2
  have := congrArg (fun F : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] O => F (μ i)) (e1.trans e2.symm)
  simp only [AlgHom.comp_apply, hμ, hφc, hx, hc] at this
  exact this.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIterateInvariantDerivationMem
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

set_option autoImplicit false

namespace GlobalTheory.LawDer.Kernel

variable {R : Type} [CommRing R] {d : ℕ}

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_atZero_eq_coeff_mapDomain_inl {S : Type} [CommRing S] {n : ℕ}
    (G : MvPowerSeries (Fin n ⊕ Fin n) S) (α : Fin n →₀ ℕ) :
    coeff α (_root_.GlobalTheory.LawDer.atZero G) = coeff (Finsupp.mapDomain Sum.inl α) G :=
  (_root_.GlobalTheory.coeff_subst_restrict_sum G).1 α

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_subst_X_comp_eq_finsum {σ τ S : Type} [CommRing S] [Finite σ] [DecidableEq τ] (g : σ → τ)
    (F : MvPowerSeries σ S) (γ : τ →₀ ℕ) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      ∑ᶠ e : σ →₀ ℕ, if γ = Finsupp.mapDomain g e then coeff e F else 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  refine finsum_congr fun e => ?_
  rw [← Finsupp.prod_mapDomain_index (h := fun t k => (X t : MvPowerSeries τ S) ^ k) (by simp)
    (by intros; simp [pow_add]), ← monomial_one_eq, coeff_monomial]
  split_ifs <;> simp

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_subst_X_comp_eq_zero_of_not_mem_range {σ τ S : Type} [CommRing S] [Finite σ] (g : σ → τ)
    (F : MvPowerSeries σ S) {γ : τ →₀ ℕ} (hγ : γ ∉ Set.range (Finsupp.mapDomain g)) :
    coeff γ (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) = 0 := by
  classical
  rw [coeff_subst_X_comp_eq_finsum]
  exact (finsum_congr fun e => if_neg fun h => hγ ⟨e, h.symm⟩).trans finsum_zero

open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
private lemma coeff_mapDomain_subst_X_comp_of_injective {σ τ S : Type} [CommRing S] [Finite σ] {g : σ → τ}
    (hg : Function.Injective g) (F : MvPowerSeries σ S) (e : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain g e) (subst (fun s => (X (g s) : MvPowerSeries τ S)) F) =
      coeff e F := by
  classical
  rw [coeff_subst_X_comp_eq_finsum, finsum_eq_single _ e, if_pos rfl]
  intro e' he'
  rw [if_neg]
  exact fun h => he' (Finsupp.mapDomain_injective hg h).symm


open MvPowerSeries in
set_option autoImplicit false in
variable {R : Type} [CommRing R] {d : ℕ} in
theorem _root_.GlobalTheory.LawDer.Kernel.constantCoeff_iterate_invDer_mem : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ i) = 0) → ∀ (N : Ideal B) (l : MvPowerSeries (Fin d) Q) (j : Fin d), _root_.GlobalTheory.QLog.In N (_root_.GlobalTheory.Katz.cob1 (_root_.GlobalTheory.QLog.up Q μ) l) → _root_.GlobalTheory.Katz.lin l = Pi.single j 1 → ∀ (u : Fin d → B) (n : ℕ), 2 ≤ n → ∃ b ∈ N, constantCoeff ((_root_.GlobalTheory.LawDer.invDer (_root_.GlobalTheory.QLog.up Q μ) (fun i => algebraMap B Q (u i)))^[n] l) = algebraMap B Q b := by
  intro B Q _ _ _ d μ hμ N l j hc hl u n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold _root_.GlobalTheory.QLog.In at hc
  set μ' := _root_.GlobalTheory.QLog.up Q μ with hμ'
  set D := _root_.GlobalTheory.LawDer.invDer μ' (fun i => algebraMap B Q (u i)) with hD
  let S : Submodule B Q := Submodule.map (Algebra.linearMap B Q) N
  have memS : ∀ x : Q, x ∈ S ↔ ∃ b ∈ N, x = algebraMap B Q b := fun x => by
    simp only [S, Submodule.mem_map, Algebra.linearMap_apply]
    exact ⟨fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩, fun ⟨b, hb, h⟩ => ⟨b, hb, h.symm⟩⟩
  have hμ0 : ∀ i, constantCoeff (μ' i) = 0 := fun i => by
    simp [μ', _root_.GlobalTheory.QLog.up, constantCoeff_map, hμ i]
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear Q d μ' hμ0 (fun i => algebraMap B Q (u i))
  have hlinD : ∀ F G : MvPowerSeries (Fin d) Q, D (F + G) = D F + D G := hlin.1
  have hcoeffD : ∀ (F : MvPowerSeries (Fin d) Q) (β : Fin d →₀ ℕ), coeff β (D F) =
      ∑ i, algebraMap B Q (u i) * (coeff (Finsupp.mapDomain Sum.inl β +
        Finsupp.single (Sum.inr i) 1) (subst μ' F) *
          ((Finsupp.mapDomain Sum.inl β (Sum.inr i) : Q) + 1)) := by
    intro F β
    rw [hD]
    unfold _root_.GlobalTheory.LawDer.invDer
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_smul, coeff_atZero_eq_coeff_mapDomain_inl, coeff_pderiv]
  have hP : ∀ F : MvPowerSeries (Fin d) Q, (∀ α, coeff α F ∈ S) → ∀ β, coeff β (D F) ∈ S := by
    intro F hF β
    rw [hcoeffD]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ?_
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul]
    exact nsmul_mem (_root_.GlobalTheory.SubstSub.coeff_subst_up_mem B Q (Fin d) (Fin d ⊕ Fin d) S F μ
      hμ hF _) _
  have hPit : ∀ (k : ℕ) (F : MvPowerSeries (Fin d) Q), (∀ α, coeff α F ∈ S) →
      ∀ β, coeff β (D^[k] F) ∈ S := by
    intro k
    induction k with
    | zero => intro F hF; simpa using hF
    | succ k ih => intro F hF; rw [Function.iterate_succ_apply]; exact ih _ (hP F hF)
  have hadd : ∀ (k : ℕ) (F G : MvPowerSeries (Fin d) Q), D^[k] (F + G) = D^[k] F + D^[k] G := by
    intro k
    induction k with
    | zero => intro F G; rfl
    | succ k ih =>
      intro F G
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        hlinD, ih]
  have hD0 : D 0 = 0 := by
    have h := hlinD 0 0
    rw [add_zero] at h
    simpa using h
  have hDC : ∀ c : Q, D (C c) = 0 := by
    intro c
    ext β
    rw [hcoeffD]
    simp [subst_C, coeff_C]
  have hCit : ∀ (k : ℕ) (c : Q), D^[k + 1] (C c) = 0 := fun k c => by
    rw [Function.iterate_succ_apply, hDC, Function.iterate_fixed hD0]
  have hzero : ∀ (β : Fin d →₀ ℕ) (i : Fin d), Finsupp.mapDomain Sum.inl β (Sum.inr i) = 0 :=
    fun β i => Finsupp.mapDomain_notin_range _ _ (by simp)
  have hsplit : subst μ' l = _root_.GlobalTheory.Katz.cob1 μ' l + _root_.GlobalTheory.Katz.inL l +
      _root_.GlobalTheory.Katz.inR l := by
    unfold _root_.GlobalTheory.Katz.cob1
    ring
  have hleft : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inL l) = 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inL
    apply coeff_subst_X_comp_eq_zero_of_not_mem_range
    rintro ⟨e, he⟩
    have h := congrArg (fun x => x (Sum.inr i)) he
    simp [hzero] at h
  have hright : ∀ (β : Fin d →₀ ℕ) (i : Fin d), coeff (Finsupp.mapDomain Sum.inl β +
      Finsupp.single (Sum.inr i) 1) (_root_.GlobalTheory.Katz.inR l) =
        if β = 0 then (Pi.single j 1 : Fin d → Q) i else 0 := by
    intro β i
    unfold _root_.GlobalTheory.Katz.inR
    split_ifs with hβ
    · subst hβ
      rw [Finsupp.mapDomain_zero, zero_add, ← Finsupp.mapDomain_single,
        coeff_mapDomain_subst_X_comp_of_injective Sum.inr_injective, ← hl]
      rfl
    · apply coeff_subst_X_comp_eq_zero_of_not_mem_range
      rintro ⟨e, he⟩
      obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
        by_contra h
        push_neg at h
        exact hβ (Finsupp.ext h)
      have h := congrArg (fun x => x (Sum.inl k)) he
      rw [Finsupp.mapDomain_notin_range _ _ (by simp)] at h
      simp [Finsupp.mapDomain_apply_of_injective Sum.inl_injective] at h
      omega
  have hg : ∀ β, coeff β (D l - C (algebraMap B Q (u j))) ∈ S := by
    intro β
    have hsum : coeff β (D l - C (algebraMap B Q (u j))) = ∑ i, algebraMap B Q (u i) *
        coeff (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
          (_root_.GlobalTheory.Katz.cob1 μ' l) := by
      rw [map_sub, hcoeffD]
      simp only [hsplit, map_add (f := _), hleft, hright, hzero, Nat.cast_zero, zero_add, add_zero,
        mul_one, mul_add, Finset.sum_add_distrib]
      by_cases hβ : β = 0 <;> simp [hβ, Pi.single_apply, coeff_C]
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Algebra.smul_def]
    refine S.smul_mem _ ((memS _).2 ?_)
    obtain ⟨b, hb, h⟩ := hc (Finsupp.mapDomain Sum.inl β + Finsupp.single (Sum.inr i) 1)
    exact ⟨b, hb, h⟩
  have key : D^[m + 2] l = D^[m + 1] (D l - C (algebraMap B Q (u j))) := by
    conv_lhs => rw [Function.iterate_succ_apply, ← sub_add_cancel (D l) (C (algebraMap B Q (u j)))]
    rw [hadd, hCit, add_zero]
  rw [key]
  obtain ⟨b, hb, h⟩ := (memS _).1 (hPit (m + 1) _ hg 0)
  refine ⟨b, hb, ?_⟩
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact h

end GlobalTheory.LawDer.Kernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CounitFormalChartEvSubConstantCoeffDvd
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
open TensorProduct

namespace GlobalTheory.FrNil

theorem counit_ev_sub_constantCoeff (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ)
    (c : QLog.Chart G d) (n : ℕ) (F : MvPowerSeries (Fin d) O) :
    (p : O) ∣ Coalgebra.counit (R := O) (c.ev n F) - constantCoeff F := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 1
  set P : MvPolynomial (Fin d) O := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => N) F with hP

  have halg : ((Bialgebra.counitAlgHom O (G.A n)).comp
      ((c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O))) =
      MvPolynomial.aeval (fun _ => (0 : O)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.coe_X,
      MvPowerSeries.map_id]
    rw [(c.isEval n).1 i]
    exact c.aug n i
  have hPc : Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) = constantCoeff F := by
    have := congrArg (fun φ => φ P) halg
    simp only [AlgHom.coe_comp, Function.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      Algebra.algebraMap_self, RingHom.id_apply, MvPowerSeries.map_id] at this
    rw [show Coalgebra.counit (R := O) (c.ev n (P : MvPowerSeries (Fin d) O)) =
      Bialgebra.counitAlgHom O (G.A n) (c.ev n (P : MvPowerSeries (Fin d) O)) from rfl, this]
    rw [MvPolynomial.aeval_zero', hP, ← coeff_zero_eq_constantCoeff_apply, Algebra.algebraMap_self,
      RingHom.id_apply, MvPolynomial.constantCoeff_eq, coeff_trunc', if_pos]
    intro i
    exact Nat.zero_le _
  have hT : ∀ α : Fin d →₀ ℕ, α.degree < N → coeff α (F - (P : MvPowerSeries (Fin d) O)) = 0 := by
    intro α hα
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc', if_pos, sub_self]
    intro i
    show α i ≤ N
    exact le_trans (Finsupp.le_degree i α) hα.le
  obtain ⟨a, ha⟩ := hN _ hT
  rw [pow_one] at ha
  have hsplit : c.ev n F = c.ev n (F - (P : MvPowerSeries (Fin d) O)) + c.ev n P := by
    rw [← map_add (f := _), sub_add_cancel]
  refine ⟨Coalgebra.counit (R := O) a, ?_⟩
  rw [hsplit, map_add (f := _), ha, hPc, add_sub_cancel_right]
  rw [show ((p : G.A n)) * a = (p : O) • a by rw [Algebra.smul_def, map_natCast], map_smul, smul_eq_mul]

end GlobalTheory.FrNil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterGLIsCharacterNormOneOfRegularStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidalCharacterGL_isCharacter_norm_one_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ m k : ℕ, 0 < m → Reg (Nat.card F) m k → IsChar ℂ ℂ (cusp θ m k) ∧ ∑ᶠ x, cusp θ m k x * star (cusp θ m k x) = (Nat.card (GL (Fin m) F) : ℂ) := by
  first | (exact @GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (exact GlobalTheory.Shin.isChar_cusp_and_norm_of_reg) | (intros; apply GlobalTheory.Shin.isChar_cusp_and_norm_of_reg  <;> assumption)
end

