module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.Chart

theorem isEval_comp {p : ℕ} {O A A' : Type} {σ : Type} [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E)
    (g : A →ₐ[O] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem ev₂_eval : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f,
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧
    c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧
    c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  intro p O _ _ G d c n f
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have h1 : c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h2 : c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h3 : c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) := by
    have hx : (fun j => c.ev₂ n (c.μ j)) =
        fun j => Bialgebra.comulAlgHom O (G.A n) (c.x n j) := funext fun j => c.comul n j
    have hE := isEval_comp (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ c.isLaw.const hE f
  refine ⟨h1, h2, h3, ?_⟩
  rw [cob1, map_sub, map_sub, h1, h2, h3, cobOne_apply]

end GlobalTheory.QLog.Chart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartGroupLawEvalRightUnit
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.ChartUnit

theorem isEval_comp {p : ℕ} {σ R A A' : Type} [CommRing R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R A']
    {x : σ → A} {E : MvPowerSeries σ R →ₐ[R] A} (φ : A →ₐ[R] A') (h : IsEval p x E) :
    IsEval p (fun i => φ (x i)) (φ.comp E) := by
  refine ⟨fun i => by simp [h.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := h.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd φ (hN f hf)
  simpa using this

theorem lift_counit_eq {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A] (t : A ⊗[O] A) :
    Algebra.TensorProduct.lift (AlgHom.id O A) ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A))
      (fun _ _ => Commute.all _ _) t = TensorProduct.rid O A (LinearMap.lTensor A (Coalgebra.counit (R := O)) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [Algebra.smul_def, mul_comm]
  | add s t hs ht => simp only [map_add (f := _), hs, ht]

end GlobalTheory.ChartUnit


open GlobalTheory.ChartUnit in
theorem GlobalTheory.chart_unit : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [IsAdicComplete (Ideal.span {(p : A)}) A] {d : ℕ} (x : Fin d → A) (ev : MvPowerSeries (Fin d) O →ₐ[O] A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → (∀ i, Coalgebra.counit (R := O) (x i) = 0) → IsEval p x ev → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, ev (op μ (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0) i) = x i := by
  intro p O A _ _ _ _ d x ev E₂ μ hnil hcu hev hev₂ hcomul i
  set ψ : A ⊗[O] A →ₐ[O] A := Algebra.TensorProduct.lift (AlgHom.id O A)
    ((Algebra.ofId O A).comp (Bialgebra.counitAlgHom O A)) (fun _ _ => Commute.all _ _) with hψ
  have key := (GlobalTheory.CEval.continuous_eval p O A (Fin d) x hnil).2 ev hev
  let u : Fin d ⊕ Fin d → MvPowerSeries (Fin d) O :=
    Sum.elim (fun i => (X i : MvPowerSeries (Fin d) O)) (fun _ => 0)
  have hE' : IsEval p (fun j => ev (u j)) (ψ.comp E₂) := by
    have h := isEval_comp ψ hev₂
    convert h using 2 with j
    rcases j with j | j
    · simp [u, hψ, hev.1 j]
    · simp [u, hψ, hcu j]
  have hu : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [u]
  have := key.1 (Fin d ⊕ Fin d) u (ψ.comp E₂) hu hE' (μ i)
  show ev (subst u (μ i)) = x i
  rw [this, AlgHom.comp_apply, hcomul, hψ, lift_counit_eq, Coalgebra.lTensor_counit_comul]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartHasPeriodLinearIntegral
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem lift_topNil {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q]
    [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ} (c : Chart G d)
    (t : G.Tate) (n : ℕ) (z : Fin d → B) (hz : ∀ i, θ (z i) = t.pt n (c.x n i)) :
    ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N := by
  intro i
  obtain ⟨N, a, ha⟩ := c.nil n i
  obtain ⟨a', ha'⟩ := hF.surj (t.pt n a)
  have hw : θ (z i ^ N - p * a') = 0 := by
    rw [map_sub, map_pow, hz, map_mul, map_natCast, ha', ← map_pow, ha, map_mul, map_natCast, sub_self]
  obtain ⟨w, -, hw'⟩ := hF.pd _ hw
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) * a' ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := by
    have := sub_dvd_pow_sub_pow (z i ^ N) (z i ^ N - p * a') p
    simpa using this
  rw [pow_mul]
  have h2 : (p : B) ∣ (z i ^ N) ^ p - (z i ^ N - p * a') ^ p := dvd_trans (dvd_mul_right _ _) h1
  have h3 : (p : B) ∣ (z i ^ N - p * a') ^ p := hw' ▸ dvd_mul_right _ _
  have := dvd_add h2 h3
  simpa using this

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem val_integral {p : ℕ} {σ B Q : Type} [Fintype σ] [DecidableEq σ] [CommRing B] [CommRing Q]
    [Algebra B Q] (z : σ → B) (s : MvPowerSeries σ B) (q : Q)
    (h : HasVal p z (map (algebraMap B Q) s) q) : ∃ b : B, q = algebraMap B Q b := by
  obtain ⟨N, hN⟩ := h 0
  obtain ⟨b, hb⟩ := hN N le_rfl
  have hE : (MvPolynomial.eval fun i => algebraMap B Q (z i))
      (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s)) := by
    rw [trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.eval₂_comp_left]
    rfl
  refine ⟨MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ => N) s) + b, ?_⟩
  rw [hE, pow_zero, one_mul, sub_eq_iff_eq_add'] at hb
  rw [hb, map_add (f := _)]

end GlobalTheory.QLog

namespace GlobalTheory.QLog

theorem hasPeriod_add_smul {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) {f g : MvPowerSeries (Fin d) Q} {y y' : B} (b : B)
    (hf : c.HasPeriod θ t f y) (hg : c.HasPeriod θ t g y') :
    c.HasPeriod θ t (f + algebraMap B Q b • g) (y + b * y') := by
  rw [c.hasPeriod_iff hF] at hf hg ⊢
  intro n z hz
  obtain ⟨q, hq, b1, hb1⟩ := hf n z hz
  obtain ⟨r, hr, b2, hb2⟩ := hg n z hz
  have h1 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z g g r r hr).2.1 (algebraMap B Q b)
  have h2 := (GlobalTheory.QLog.ValLin.hasVal_add_smul_map p B O Q θ hF (Fin d) z _ _ q _ hq).1 h1
  refine ⟨_, h2, b1 + b * b2, ?_⟩
  have e : (p : Q) ^ n * (q + algebraMap B Q b * r) =
      (p : Q) ^ n * q + algebraMap B Q b * ((p : Q) ^ n * r) := by ring
  rw [e, hb1, hb2, ← map_mul, ← map_add (f := _)]
  congr 1
  ring

theorem hasPeriod_integral {p : ℕ} [Fact p.Prime] {O B Q : Type} [CommRing O] [CommRing B]
    [CommRing Q] [Algebra B Q] {θ : B →+* O} (hF : IsFrame p Q θ) {G : PDivGroup p O} {d : ℕ}
    (c : Chart G d) (t : G.Tate) (s : MvPowerSeries (Fin d) B) :
    c.HasPeriod θ t (map (algebraMap B Q) s) 0 := by
  rw [c.hasPeriod_iff hF]
  intro n z hz
  have hD : DIn (⊤ : Ideal B) (map (algebraMap B Q) s) := fun α i =>
    ⟨(α i : B) * coeff α s, trivial, by rw [coeff_map, map_mul, map_natCast]⟩
  obtain ⟨q, hq, -⟩ := GlobalTheory.QLog.existsUnique_hasVal_of_dIn p B O Q θ hF (Fin d) z (lift_topNil hF c t n z hz) _ hD
  obtain ⟨e, he⟩ := val_integral z s q hq
  exact ⟨q, hq, e, by rw [he, zero_add, map_mul, map_pow, map_natCast]⟩

open MvPowerSeries in
private lemma exists_pow_dvd_of_theta_eq_of_isFrame {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] {θ : B →+* O} (hθ : _root_.GlobalTheory.QLog.IsFrame p Q θ)
    {z : B} {a : O} (hza : θ z = a) {N : ℕ} (ha : (p : O) ∣ a ^ N) :
    ∃ M, (p : B) ∣ z ^ M := by
  obtain ⟨w, hw⟩ := ha
  obtain ⟨b, hb⟩ := hθ.surj w
  obtain ⟨y, -, hy⟩ := hθ.pd (z ^ N - p * b)
    (by simp [hza, hb, hw])
  refine ⟨N * p, ?_⟩
  have h1 : (p : B) ∣ (z ^ N) ^ p - (z ^ N - p * b) ^ p :=
    (dvd_mul_right (p : B) b).trans (by simpa using sub_dvd_pow_sub_pow (z ^ N) (z ^ N - p * b) p)
  have h2 : (z ^ N) ^ p = ((z ^ N) ^ p - (z ^ N - p * b) ^ p) + p * y := by rw [← hy]; ring
  rw [pow_mul, h2]
  exact dvd_add h1 (dvd_mul_right _ _)

open MvPowerSeries in
private lemma eval_algebraMap_trunc'_map_eq_algebraMap_eval {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]
    {d : ℕ} (s : MvPowerSeries (Fin d) B) (z : Fin d → B) (N : ℕ) :
    MvPolynomial.eval (fun i ↦ algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ ↦ N) (map (algebraMap B Q) s)) =
      algebraMap B Q (MvPolynomial.eval z (trunc' B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s)) := by
  rw [MvPowerSeries.trunc'_map, MvPolynomial.eval_map, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom,
    MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  rfl


open MvPowerSeries in
theorem _root_.GlobalTheory.QLog.hasPeriod_linear : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (f g : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y y' b : F.B), c.HasPeriod F.θ t f y → c.HasPeriod F.θ t g y' → c.HasPeriod F.θ t (f + algebraMap F.B F.Q b • g) (y + b * y') ∧ (∀ s : MvPowerSeries (Fin d) F.B, constantCoeff s = 0 → c.HasPeriod F.θ t (map (algebraMap F.B F.Q) s) 0) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ f g t y y' b hf hg
  have hF := F.frame
  rw [c.hasPeriod_iff hF] at hf hg
  refine ⟨?_, ?_⟩
  · rw [c.hasPeriod_iff hF]
    intro n z hz
    obtain ⟨q, hq, b₁, hb₁⟩ := hf n z hz
    obtain ⟨r, hr, b₂, hb₂⟩ := hg n z hz
    have hbr := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z g f
      r q hr).2.1 (algebraMap _ _ b)
    refine ⟨q + algebraMap _ _ b * r,
      (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF (Fin d) z f _ q _
        hq).1 hbr, b₁ + b * b₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_pow, map_natCast] at hb₁ hb₂ ⊢
    linear_combination hb₁ + algebraMap _ _ b * hb₂
  · intro s _
    rw [c.hasPeriod_iff hF]
    intro n z hz
    have hz' : ∀ i, ∃ M, (p : F.B) ∣ z i ^ M := fun i => by
      obtain ⟨N, hN⟩ := c.nil n i
      refine exists_pow_dvd_of_theta_eq_of_isFrame hF (hz i) (N := N) ?_
      simpa [map_pow, map_natCast] using map_dvd (t.pt n) hN
    have hd : _root_.GlobalTheory.QLog.DIn (⊤ : Ideal F.B)
        (map (algebraMap F.B F.Q) s) := by
      intro α i
      exact ⟨(α i : F.B) * coeff α s, Submodule.mem_top, by simp⟩
    obtain ⟨q, hq, -⟩ := _root_.GlobalTheory.QLog.existsUnique_hasVal_of_dIn p _ O _
      F.θ hF (Fin d) z hz' _ hd
    have hq' := hq
    unfold _root_.GlobalTheory.QLog.HasVal at hq'
    obtain ⟨N, hN⟩ := hq' 0
    obtain ⟨e, he⟩ := hN N le_rfl
    refine ⟨q, hq, MvPolynomial.eval z
      (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e, ?_⟩
    rw [eval_algebraMap_trunc'_map_eq_algebraMap_eval, pow_zero, one_mul] at he
    have hq2 : q = algebraMap _ F.Q (MvPolynomial.eval z
        (trunc' F.B (Finsupp.equivFunOnFinite.symm fun _ ↦ N) s) + e) := by
      rw [map_add (f := _), ← he]
      ring
    rw [hq2, zero_add, map_mul, map_pow, map_natCast]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartNatMultipleEvalProperties
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.ChartMul

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ}

theorem isEval_algHom_comp {A A' σ : Type} [CommRing A] [CommRing A'] [Algebra O A] [Algebra O A']
    {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E) (g : A →ₐ[O] A') :
    IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) : constantCoeff (nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul]
  | succ k ih =>
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    have e : nmul μ (k + 1) i = subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (μ i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
      rfl
    rw [e]
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

variable [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem ev₂_inL (c : QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
      fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
        (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
  have hE := isEval_algHom_comp (c.isEval n)
    (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
  rw [← hx] at hE
  exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

theorem ev₂_inR (c : QLog.Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
      fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
        (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
  have hE := isEval_algHom_comp (c.isEval n)
    (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
  rw [← hx] at hE
  exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f

theorem ev_nmul (c : QLog.Chart G d) (n k : ℕ) (i : Fin d) :
    c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
  have H := ((CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
  induction k generalizing i with
  | zero =>
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero]
    simp [mulBy, c.aug n i]
  | succ k ih =>
    let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
    let L : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift M (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hs : ∀ j, constantCoeff (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul c.isLaw.const k j
      · exact constantCoeff_X _
    have e : nmul c.μ (k + 1) i = subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ i) := by
      simp only [nmul]
      rw [Function.iterate_succ_apply']
      rfl
    have hE := isEval_algHom_comp (c.isEval₂ n) L
    have hx : (fun j => L (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
        fun j => c.ev n (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) := by
      funext j
      rcases j with j | j
      · simp [L, M, ih j]
      · simp [L, (c.isEval n).1 j]
    rw [hx] at hE
    rw [e, H _ _ _ hs hE, AlgHom.comp_apply, c.comul n i]
    have h1 : mulBy O (G.A n) (k + 1) (c.x n i) =
        (WithConv.toConv (AlgHom.id O (G.A n)) ^ (k + 1)).ofConv (c.x n i) :=
      DFunLike.congr_fun (comp_mulBy_pts (AlgHom.id O (G.A n)) (k + 1)) (c.x n i)
    have h2 : (M : G.A n →ₐ[O] G.A n) = (WithConv.toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
      comp_mulBy_pts (AlgHom.id O (G.A n)) k
    rw [h1, pow_succ, AlgHom.convMul_apply]
    simp only [L, h2]

theorem ev_subst_nmul (c : QLog.Chart G d) (n k : ℕ) (f : MvPowerSeries (Fin d) O) :
    c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n)
  have H := ((CEval.continuous_eval p O (G.A n) (Fin d) _ (c.nil n)).2 (c.ev n) (c.isEval n)).1
  let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
  have hE := isEval_algHom_comp (c.isEval n) M
  have hx : (fun j => M (c.x n j)) = fun j => c.ev n (nmul c.μ k j) :=
    funext fun j => (ev_nmul c n k j).symm
  rw [hx] at hE
  exact H (Fin d) _ _ (constantCoeff_nmul c.isLaw.const k) hE f

theorem ev₂_pull2_nmul (c : QLog.Chart G d) (n k : ℕ) (s : MvPowerSeries (Fin d ⊕ Fin d) O) :
    c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) := by
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    _root_.GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  let M : G.A n →ₐ[O] G.A n := (mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
  let T : G.A n ⊗[O] G.A n →ₐ[O] G.A n ⊗[O] G.A n := Algebra.TensorProduct.map M M
  have hs : ∀ j, constantCoeff (Sum.elim (fun j => inL (nmul c.μ k j))
      (fun j => inR (nmul c.μ k j)) j) = 0 := by
    have hX : ∀ j : Fin d, constantCoeff (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
      fun _ => constantCoeff_X _
    have hY : ∀ j : Fin d, constantCoeff (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) O) = 0 :=
      fun _ => constantCoeff_X _
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hX) hX
        (constantCoeff_nmul c.isLaw.const k j)
    · exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hY) hY
        (constantCoeff_nmul c.isLaw.const k j)
  have hE := isEval_algHom_comp (c.isEval₂ n) T
  have hx : (fun j => T (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n))
      (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) j)) =
      fun j => c.ev₂ n (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j)) j) := by
    funext j
    rcases j with j | j
    · simp [T, M, ev₂_inL, ev_nmul]
    · simp [T, M, ev₂_inR, ev_nmul]
  rw [hx] at hE
  have e : pull2 (nmul c.μ k) s =
      subst (Sum.elim (fun j => inL (nmul c.μ k j)) (fun j => inR (nmul c.μ k j))) s := rfl
  rw [e, H _ _ _ hs hE, AlgHom.comp_apply]
  generalize c.ev₂ n s = t
  induction t with
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  | tmul a b => simp [T, M]

theorem nmul_ev : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n k,
    (∀ i, c.ev n (nmul c.μ k i) = mulBy O (G.A n) k (c.x n i)) ∧
    (∀ f, c.ev n (subst (nmul c.μ k) f) = mulBy O (G.A n) k (c.ev n f)) ∧
    ∀ s, c.ev₂ n (pull2 (nmul c.μ k) s) = pullbackTwo (mulBy O (G.A n) k) (c.ev₂ n s) :=
  fun _ _ _ _ _ _ c n k => ⟨ev_nmul c n k, ev_subst_nmul c n k, ev₂_pull2_nmul c n k⟩

end GlobalTheory.QLog.ChartMul
end
end

