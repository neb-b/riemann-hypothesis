module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapCoboundarySwapPullbackCommute
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

namespace Katz

namespace CoefChange

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (r : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map r (at2 c u v) = at2 (map r c) (fun i => map r (u i)) (fun i => map r (v i)) := by
  unfold at2
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun j => by
    cases j with
    | inl i => exact hu i
    | inr i => exact hv i))]
  congr 1
  funext j
  cases j <;> rfl

theorem map_subst' (r : R →+* S) {σ : Type} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    map r (subst a f) = subst (fun i => map r (a i)) (map r f) := by
  rw [map_subst (hasSubst_of_constantCoeff_zero ha)]

theorem map_inL (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inL f) = inL (map r f) := by
  unfold inL
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem map_inR (r : R →+* S) (f : MvPowerSeries (Fin d) R) : map r (inR f) = inR (map r f) := by
  unfold inR
  rw [map_subst' r _ (fun _ => constantCoeff_X _)]
  congr 1
  funext i
  exact map_X r _

theorem inL_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inL f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

theorem inR_const {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 0) :
    constantCoeff (inR f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) hf

end CoefChange


open CoefChange in
theorem map_cob_swap_pull : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (S : Type) [CommRing S] (r : R →+* S), (∀ f, map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f)) ∧ (∀ c, map r (cob2 μ c) = cob2 (fun i => map r (μ i)) (map r c)) ∧ (∀ c : MvPowerSeries (Fin d ⊕ Fin d) R, map r (Katz.swap c) = Katz.swap (map r c)) ∧ (∀ f : MvPowerSeries (Fin d) R, lin (map r f) = fun i => r (lin f i)) ∧ ∀ φ : Fin d → MvPowerSeries (Fin d) R, (∀ i, constantCoeff (φ i) = 0) → (∀ c, map r (pull2 φ c) = pull2 (fun i => map r (φ i)) (map r c)) ∧ ∀ f : MvPowerSeries (Fin d) R, map r (subst φ f) = subst (fun i => map r (φ i)) (map r f) := by
  intro R _ d μ hμ S _ r
  have hX : ∀ {τ : Type} (i : τ), constantCoeff (X i : MvPowerSeries τ R) = 0 :=
    fun i => constantCoeff_X i
  have hop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (op μ u v i) = 0 := by
    intro u v hu hv i
    unfold op at2
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i)) (fun j => by
      cases j with
      | inl i => exact hu i
      | inr i => exact hv i) (hμ i)
  have mapop : ∀ (u v : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R),
      (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      (fun i => map r (op μ u v i)) =
        op (fun i => map r (μ i)) (fun i => map r (u i)) (fun i => map r (v i)) := by
    intro u v hu hv
    funext i
    exact mvPowerSeriesMap_evalTwoGroups r (μ i) u v hu hv
  have mx1 : (fun i => map r ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x1 := by
    funext i; exact map_X r _
  have mx2 : (fun i => map r ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x2 := by
    funext i; exact map_X r _
  have mx3 : (fun i => map r ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i)) = x3 := by
    funext i; exact map_X r _
  have h1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  have h3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) i) = 0 :=
    fun _ => hX _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f
    unfold cob1
    rw [map_sub, map_sub, map_subst' r μ hμ, map_inL, map_inR]
  · intro c
    unfold cob2
    rw [map_sub, map_add (f := _), map_sub, mvPowerSeriesMap_evalTwoGroups r c _ _ h2 h3, mvPowerSeriesMap_evalTwoGroups r c _ _ (hop _ _ h1 h2) h3,
      mvPowerSeriesMap_evalTwoGroups r c _ _ h1 (hop _ _ h2 h3), mvPowerSeriesMap_evalTwoGroups r c _ _ h1 h2, mapop _ _ h1 h2,
      mapop _ _ h2 h3, mx1, mx2, mx3]
  · intro c
    unfold Katz.swap
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun _ => hX _) (fun _ => hX _)]
    congr 1 <;> funext i <;> exact map_X r _
  · intro f
    funext i
    unfold lin
    rw [coeff_map]
  · intro φ hφ
    refine ⟨?_, fun f => map_subst' r φ hφ f⟩
    intro c
    unfold pull2
    rw [mvPowerSeriesMap_evalTwoGroups r c _ _ (fun i => inL_const (hφ i)) (fun i => inR_const (hφ i))]
    congr 1 <;> funext i
    · exact map_inL r (φ i)
    · exact map_inR r (φ i)

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterate
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

theorem map_pderiv_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) s f) = MvPowerSeries.pderiv (R := S) s (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map,
    map_mul, map_add, map_natCast, map_one]

theorem map_atZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) : map f (atZero H) = atZero (map f H) := by
  unfold atZero
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp))]
  congr 1
  funext s
  cases s <;> simp

theorem map_smul_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R)
    (H : MvPowerSeries σ R) : map f (a • H) = f a • map f H := by
  ext m
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul]

theorem map_invDer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (F : MvPowerSeries (Fin d) R) :
    map f (invDer μ u F) = invDer (fun i => map f (μ i)) (fun i => f (u i)) (map f F) := by
  unfold invDer
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_coeffChange, map_atZero, map_pderiv_coeffChange, map_subst (hasSubst_of_constantCoeff_zero hμ)]

theorem map_invDer_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R),
    map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  intro R S _ _ f d μ hμ u k F
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_invDer f μ hμ, ih]

end GlobalTheory.LawDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem constantCoeff_nmul_zero {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact ih j
      | inr j => simp
    show constantCoeff ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = 0
    rw [Function.iterate_succ_apply']
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem up_nmul : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  intro R S _ _ _ d μ hμ n
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact constantCoeff_nmul_zero μ hμ n j
      | inr j => simp
    funext i
    show map (algebraMap R S) ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = (fun v : Fin d → MvPowerSeries (Fin d) S => op (up S μ) v fun i => X i)^[n + 1]
      (fun _ => 0) i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change map (algebraMap R S) (subst (Sum.elim (nmul μ n) fun i => X i) (μ i)) =
      subst (Sum.elim (nmul (up S μ) n) fun i => X i) (up S μ i)
    rw [map_subst (hasSubst_of_constantCoeff_zero h0), ← ih]
    congr 1
    funext j
    cases j with
    | inl j => rfl
    | inr j => simp

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapSumSmul
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory.QLog

theorem defect_sum {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0) (m : ℕ)
    {ι : Type} [Fintype ι] (a : ι → E) (f : ι → MvPowerSeries (Fin d) E) :
    defect μ m (∑ i, a i • f i) = ∑ i, a i • defect μ m (f i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [defect, ← coe_substAlgHom (hasSubst_up_nmul (Q := E) hμ m), map_sum, map_smul,
    Finset.smul_sum, smul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem map_sum_smul {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {σ : Type}
    {ι : Type} [Fintype ι] (b : ι → O) (s : ι → MvPowerSeries σ O) :
    map (algebraMap O E) (∑ i, b i • s i) = ∑ i, algebraMap O E (b i) • map (algebraMap O E) (s i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map]
  simp only [smul_eq_mul, map_mul]

theorem Chart.isLie_comb : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) E) (l : ι → G.dual.Lie) (b : ι → O), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, c.IsLie (e i) (l i)) → c.IsLie (comb b e) (∑ i, b i • l i) := by
  intro p _ O E _ _ _ hF G d c ι _ e l b _ hl
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  rw [c.isLie_iff hinj]
  intro n
  choose s hs hc using fun i => (c.isLie_iff hinj _ _).1 (hl i) n
  refine ⟨∑ i, b i • s i, ?_, fun w φ hφ => ?_⟩
  · rw [map_sum_smul, comb, defect_sum c.isLaw.const]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i]
  · have : (∑ i, b i • l i) w - φ (c.ev n (∑ i, b i • s i)) =
        ∑ i, b i * (l i w - φ (c.ev n (s i))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
        smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
    rw [this]
    exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hc i w φ hφ) _

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.QLog GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.WinLift

section Nil

theorem isNil_of_theta_eq {B R ι : Type} [CommRing B] [CommRing R] [IsLocalRing R] [Fintype ι]
    (p : ℕ) [Fact p.Prime] (θ : B →+* R) (σ : B →+* B) (hp : ¬IsUnit (p : R))
    (hσ : ∀ b, (p : B) ∣ σ b - b ^ p) (M M' : Matrix ι ι B) (h : ∀ i j, θ (M i j) = θ (M' i j))
    (hM : IsNil θ σ M) : IsNil θ σ M' := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun v i => ?_⟩
  have hs : ∀ z : B, θ z ∈ IsLocalRing.maximalIdeal R → θ (σ z) ∈ IsLocalRing.maximalIdeal R := by
    intro z hz
    obtain ⟨c, hc⟩ := hσ z
    have e : σ z = z ^ p + p * c := by rw [← hc]; ring
    rw [e, map_add (f := _), map_pow, map_mul, map_natCast]
    exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hz _ (Fact.out : p.Prime).pos)
      (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 hp))
  have key : ∀ (n : ℕ) (w : ι → B) (i : ι),
      θ (((fun w : ι → B => M.mulVec fun j => σ (w j))^[n] w) i) -
        θ (((fun w : ι → B => M'.mulVec fun j => σ (w j))^[n] w) i) ∈
          IsLocalRing.maximalIdeal R := by
    intro n
    induction n with
    | zero => intro w i; simp
    | succ n ih =>
      intro w i
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      simp only [Matrix.mulVec, dotProduct]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul, map_mul, h i j, ← mul_sub, ← map_sub, ← map_sub]
      exact Ideal.mul_mem_left _ _ (hs _ (by rw [map_sub]; exact ih w j))
  intro hu
  have h1 := (IsLocalRing.mem_maximalIdeal _).2 (hN v i)
  have h2 := Ideal.sub_mem _ h1 (key N v i)
  rw [sub_sub_cancel] at h2
  exact (IsLocalRing.mem_maximalIdeal _).1 h2 hu

theorem isNil_of_map {A B R ι : Type} [CommRing A] [CommRing B] [CommRing R] [Fintype ι]
    (a : A →+* B) (θA : A →+* R) (θB : B →+* R) (φ : A →+* A) (σ : B →+* B)
    (hθ : ∀ x, θB (a x) = θA x) (hσ : ∀ x, σ (a x) = a (φ x)) (M : Matrix ι ι A)
    (h : IsNil θB σ (M.map a)) : IsNil θA φ M := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, fun v i => ?_⟩
  have key : ∀ (n : ℕ) (w : ι → A),
      (fun w : ι → B => (M.map a).mulVec fun j => σ (w j))^[n] (fun j => a (w j)) =
        fun j => a (((fun w : ι → A => M.mulVec fun j => φ (w j))^[n] w) j) := by
    intro n
    induction n with
    | zero => intro w; rfl
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.mulVec, dotProduct, map_sum, hσ]
  have := hN (fun j => a (v j)) i
  rwa [key, hθ] at this

theorem map_inv_of_isUnit {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] [DecidableEq ι]
    (f : R →+* S) (M : Matrix ι ι R) (hM : IsUnit M) : (M.map f)⁻¹ = M⁻¹.map f := by
  apply Matrix.inv_eq_right_inv
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det M).1 hM), map_one]

end Nil

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem frob_xi (ε : PreTilt O p) :
    WittVector.frobenius (xi ε) = ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
  have : root ε ^ p = ε := (_root_.frobeniusEquiv (PreTilt O p) p).apply_symm_apply ε
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [xi, map_sum, map_pow, frob_teich]
  simp only [← map_pow, this]

theorem frob_mu (ε : PreTilt O p) :
    WittVector.frobenius (Sandwich.mu ε) = WittVector.frobenius (xi ε) * Sandwich.mu ε := by
  rw [frob_xi, Sandwich.mu, geom_sum_mul, map_sub, map_one, frob_teich]

theorem mu_dvd_frob_xi_sub (ε : PreTilt O p) :
    Sandwich.mu ε ∣ WittVector.frobenius (xi ε) - p := by
  have : (p : Ainf p O) = ∑ i ∈ Finset.range p, 1 ^ i := by simp
  rw [this, frob_xi, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum fun i _ => sub_dvd_pow_sub_pow _ _ i

end Frob

end GlobalTheory.WinLift

namespace GlobalTheory.WinLift

section Frame

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p}

theorem root_prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (PreTilt.untilt (root ε)) p := by
  simpa [zeta] using hε 1

theorem theta_mu (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 :=
  Sandwich.Model.theta_mu hv (root_prim hε)

theorem theta_frob_xi (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    WittVector.fontaineTheta O p (WittVector.frobenius (xi ε)) = p := by
  have h1 : WittVector.fontaineTheta O p (WittVector.teichmuller p ε) = 1 := by
    have := theta_mu hv hε
    rw [Sandwich.mu, map_sub, map_one, sub_eq_zero] at this
    exact this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [frob_xi, map_sum]
  simp [h1]

variable (F : BFrame ε)

theorem tf (b : F.B) (h : (p : F.B) * b = 0) : b = 0 := by
  apply F.frame.inj
  have h1 := congrArg (algebraMap F.B F.Q) h
  rw [map_mul, map_natCast, map_zero] at h1
  rw [map_zero]
  exact (F.frame.unit_p.mul_right_eq_zero).1 h1

theorem theta_tau (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : F.θ F.τ = 0 := by
  apply F.frame.sat
  have h := congrArg F.θ F.p_τ
  rw [map_mul, map_natCast, F.θ_a, theta_mu hv hε] at h
  exact h

theorem sigma_tau : F.σ F.τ = F.a (WittVector.frobenius (xi ε)) * F.τ := by
  apply sub_eq_zero.1
  apply tf F
  have h := congrArg F.σ F.p_τ
  rw [map_mul, map_natCast, F.σ_a, frob_mu, map_mul, ← F.p_τ] at h
  rw [mul_sub, h]
  ring

theorem tau_dvd_sigma (b : F.B) (h : F.τ ∣ b) : F.τ ∣ F.σ b := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul, sigma_tau]
  exact ⟨F.a (WittVector.frobenius (xi ε)) * F.σ c, by ring⟩

theorem mu_dvd_of_p_mul (F : BFrame ε) (z : Ainf p O) (h : Sandwich.mu ε ∣ (p : Ainf p O) * z) :
    Sandwich.mu ε ∣ z := by
  obtain ⟨w, hw⟩ := h
  apply (F.τ_mul z).1
  apply tf F
  have h1 := congrArg F.a hw
  rw [map_mul, map_natCast, map_mul, ← F.p_τ] at h1
  calc (p : F.B) * (F.τ * F.a z) = F.τ * ((p : F.B) * F.a z) := by ring
    _ = 0 := by rw [h1]; linear_combination (p * F.a w) * F.τ_sq

theorem mu_dvd_of_xi_mul (F : BFrame ε) (z : Ainf p O)
    (h : Sandwich.mu ε ∣ WittVector.frobenius (xi ε) * z) : Sandwich.mu ε ∣ z := by
  apply mu_dvd_of_p_mul F
  have h2 := (mu_dvd_frob_xi_sub ε).mul_right z
  have := dvd_sub h h2
  rwa [sub_mul, sub_sub_cancel] at this

end Frame

end GlobalTheory.WinLift
end
end

