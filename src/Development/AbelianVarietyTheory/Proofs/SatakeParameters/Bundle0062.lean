module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0059
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumModGPeriodValues
section
noncomputable section

namespace GlobalTheory.PadicUnfold.Period

def extZero {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ) (y : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0)

theorem extZero_single {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) (s : Fin (n' + c')) (l : Fin (n + c)) :
    extZero c' c y (Pi.single s 1) l = if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0 := by
  simp [extZero, Matrix.toLin'_apply]

theorem periodXX1_add_smul {k : Type} [CommRing k] {n' c' n c : ℕ} (a : k)
    (x y : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Formalism.L2.Col.Loc.FC n' c' n c → k) :
    Formalism.L2.Col.Loc.xx1 (x + a • y) t =
      Formalism.L2.Col.Loc.xx1 x t + a • extZero c' c y := by
  refine hom_ext fun s l => ?_
  rw [LinearMap.add_apply, Pi.add_apply, LinearMap.smul_apply, Pi.smul_apply, linearMap_unfolding_apply_single, linearMap_unfolding_apply_single,
    extZero_single]
  by_cases hf : Formalism.L2.Col.Loc.IsFree n' n c l.1 s.1
  · have hs : ¬ s.1 < n' := not_lt.2 hf.1
    simp [hf, hs]
  · by_cases hs : s.1 < n'
    · by_cases hl : l.1 < n <;> simp [hf, hs, hl]
    · simp [hf, hs]

theorem chArg_smul_extZero {k : Type} [CommRing k] {n' n c : ℕ} (a : k)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    Formalism.L2.Col.Loc.chArg (a • extZero (c + 1) c y) = 0 := by
  rw [chArg_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, extZero_single, dite_eq_right (by simp; omega), smul_zero]

variable {g : ℕ} [Fact g.Prime]

end GlobalTheory.PadicUnfold.Period
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SumRepsEquiv
section
open Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaInter

noncomputable section

namespace GlobalTheory.KerLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V]

omit [Module ℂ V] in
theorem sum_reps {Λ₁ Λ₂ : AddSubgroup V} {S S' : Finset V} (h : IsReps Λ₁ Λ₂ S) (h' : IsReps Λ₁ Λ₂ S') (f : V → ℂ)
    (hf : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → f (x + l) = f x) : ∑ x ∈ S, f x = ∑ x ∈ S', f x := by
  choose! r hr hr' using h'.2.2
  refine Finset.sum_bij (fun x _ => r x) (fun x hx => hr x (h.1 x hx)) (fun x hx y hy e => ?_) (fun y hy => ?_) fun x hx => ?_
  · refine h.2.1 x hx y hy ?_
    have := Λ₁.sub_mem (hr' x (h.1 x hx)) (hr' y (h.1 y hy))
    rwa [e, sub_sub_sub_cancel_right] at this
  · obtain ⟨x, hx, e⟩ := h.2.2 y (h'.1 y hy)
    refine ⟨x, hx, h'.2.1 _ (hr x (h.1 x hx)) _ hy ?_⟩
    have := Λ₁.neg_mem (Λ₁.add_mem e (hr' x (h.1 x hx)))
    rwa [sub_add_sub_cancel, neg_sub] at this
  · have h2 := h'.1 _ (hr x (h.1 x hx))
    rw [← hf _ h2 _ (Λ₂.sub_mem (h.1 x hx) h2) (hr' x (h.1 x hx)), add_sub_cancel]

omit [Module ℂ V] in
theorem sum_reps_equiv {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (h : IsReps Λ₁ Λ₂ S) (φ : V ≃ V)
    (h2 : ∀ x, φ x ∈ Λ₂ ↔ x ∈ Λ₂) (h1 : ∀ x y, φ x - φ y ∈ Λ₁ ↔ x - y ∈ Λ₁) (f : V → ℂ)
    (hf : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → f (x + l) = f x) : ∑ x ∈ S, f (φ x) = ∑ x ∈ S, f x := by
  rw [← sum_reps (S := S.map φ.toEmbedding) ?_ h f hf, Finset.sum_map]
  · rfl
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx', rfl⟩ := Finset.mem_map.1 hx
    exact (h2 x).2 (h.1 x hx')
  · obtain ⟨x, hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y, hy', rfl⟩ := Finset.mem_map.1 hy
    rw [h.2.1 x hx' y hy' ((h1 x y).1 e)]
  · obtain ⟨y, rfl⟩ := φ.surjective y
    obtain ⟨x, hx, e⟩ := h.2.2 y ((h2 y).1 hy)
    exact ⟨φ x, Finset.mem_map_of_mem _ hx, (h1 y x).2 e⟩

variable {H : Sesq V} {α : V → ℂ}

theorem brk_eq (y t : V) : brk H y t = chi H t y := by
  unfold brk chi
  congr 1
  ring

theorem int_of_semi {A : AddSubgroup V} (hs : IsSemiChar H A α) {x y : V} (hx : x ∈ A) (hy : y ∈ A) : chi H x y = 1 := by
  have h1 := alpha_sq hs (A.add_mem hx hy)
  have h2 := alpha_sq hs hx
  have h3 := alpha_sq hs hy
  rw [hs.2 x hx y hy] at h1
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) = 1 := by
    linear_combination h1 - (α y * α y * h2 + h3) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) ^ 2
  rw [← Complex.exp_add] at h4
  rw [chi, Complex.exp_neg, ← inv_one, ← h4]
  congr 2
  ring

theorem w_add (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (F : V → ℂ) (z : V) : α (x + y) * opU H (x + y) F z = α x * opU H x (fun w => α y * opU H y F w) z := by
  have h := int_of_semi hs hx hy
  have e : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
      Complex.exp (-(Real.pi * Complex.I * (altE H x y : ℂ))) := by
    rw [← mul_one (Complex.exp ((Real.pi : ℂ) * _ * _)), ← h, chi, ← Complex.exp_add]
    congr 1
    ring
  rw [opU_mul, opU_opU hH, hs.2 x hx y hy, e]
  ring

theorem chi_ne (x y : V) : chi H x y ≠ 0 := Complex.exp_ne_zero _

theorem xiL_stab (hH : IsHerm H) {A B Λ : AddSubgroup V} (hA : IsSemiChar H A α) (hB : IsSemiChar H B α)
    (hΛ : IsSemiChar H Λ α) {SX SA SB : Finset V} (hX : IsReps Λ A SX) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB)
    (vol : ℝ) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α Λ) {Φ : V → ℂ} (hΦ : InvOn A B Φ) (T : V ≃+ V)
    (tH : ∀ x y, H (T x) (T y) = H x y) (tα : ∀ x, α (T x) = α x) (tA : ∀ x, T x ∈ A ↔ x ∈ A) (tB : ∀ x, T x ∈ B ↔ x ∈ B)
    (tΛ : ∀ x, T x ∈ Λ ↔ x ∈ Λ) (tθ : ∀ z, θ (T z) = θ z) (k : ℂ) (tΦ : ∀ x, Φ (T x) = k * Φ x) (z : V) :
    xiL H α vol SX SA SB Φ θ (T z) = k * xiL H α vol SX SA SB Φ θ z := by
  have tU : ∀ x F w, opU H (T x) F (T w) = opU H x (fun v => F (T v)) w := fun x F w => by
    simp only [opU, tH, map_add (f := _)]
  have tc : ∀ x y, chi H (T x) (T y) = chi H x y := fun x y => by simp only [chi, altE, tH]
  have invA : ∀ x ∈ A, ∀ y ∈ B, ∀ t ∈ Λ ⊓ A, ∀ l ∈ Λ ⊓ A, l ∈ B →
      Φ (t + l - x) * (brk H y (t + l))⁻¹ = Φ (t - x) * (brk H y t)⁻¹ := fun x hx y hy t ht l hl hl' => by
    rw [add_sub_right_comm, hΦ _ (A.sub_mem ht.2 hx) l hl.2 hl', brk_eq, brk_eq, chi_add_left, int_of_semi hB hl' hy, mul_one]
  have hatT : ∀ x ∈ A, ∀ y ∈ B, hatS H vol SA (fun s => Φ (s - T x)) (T y) = k * hatS H vol SA (fun s => Φ (s - x)) y := by
    intro x hx y hy
    unfold hatS
    rw [← sum_reps_equiv hSA T.toEquiv (fun t => and_congr (tΛ t) (tA t)) (fun t u => by
      change T t - T u ∈ B ↔ _
      rw [← map_sub, tB]) (fun t => Φ (t - T x) * (brk H (T y) t)⁻¹) (invA _ ((tA x).2 hx) _ ((tB y).2 hy))]
    have : ∀ t, Φ (T.toEquiv t - T x) * (brk H (T y) (T.toEquiv t))⁻¹ = k * (Φ (t - x) * (brk H y t)⁻¹) := fun t => by
      change Φ (T t - T x) * (brk H (T y) (T t))⁻¹ = _
      rw [← map_sub, tΦ, brk_eq, brk_eq, tc, mul_assoc]
    simp only [this, ← Finset.mul_sum]
    ring
  have hatL : ∀ x ∈ A, ∀ y ∈ B, ∀ l ∈ A, l ∈ Λ →
      hatS H vol SA (fun s => Φ (s - (x + l))) y = (chi H l y)⁻¹ * hatS H vol SA (fun s => Φ (s - x)) y := by
    intro x hx y hy l hl hl'
    unfold hatS
    rw [← sum_reps_equiv hSA (Equiv.addRight l) (fun t => (Λ ⊓ A).add_mem_cancel_right ⟨hl', hl⟩) (fun t u => by simp)
      (fun t => Φ (t - (x + l)) * (brk H y t)⁻¹) (invA _ (A.add_mem hx hl) _ hy)]
    have : ∀ t, Φ (Equiv.addRight l t - (x + l)) * (brk H y (Equiv.addRight l t))⁻¹ =
        (chi H l y)⁻¹ * (Φ (t - x) * (brk H y t)⁻¹) := fun t => by
      rw [Equiv.coe_addRight, add_sub_add_right_eq_sub, brk_eq, brk_eq, chi_add_left, mul_inv]
      ring
    simp only [this, ← Finset.mul_sum]
    ring
  have invB : ∀ (Ψ : V → ℂ) w, ∀ y ∈ B, ∀ l ∈ B, l ∈ Λ →
      hatS H vol SA Ψ (y + l) * α (y + l) * opU H (y + l) θ w = hatS H vol SA Ψ y * α y * opU H y θ w := by
    intro Ψ w y hy l hl hl'
    have e1 : hatS H vol SA Ψ (y + l) = hatS H vol SA Ψ y := by
      unfold hatS
      congr 2
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [brk_eq, brk_eq, chi_add_right, int_of_semi hΛ (hSA.1 t ht).1 hl', mul_one]
    rw [e1, mul_assoc, w_add hH hB hy hl, funext (hθ l hl'), mul_assoc]
  have xiT : ∀ x ∈ A, ∀ w, xiS H α vol SA SB (fun s => Φ (s - T x)) θ (T w) = k * xiS H α vol SA SB (fun s => Φ (s - x)) θ w := by
    intro x hx w
    unfold xiS sumU
    rw [← sum_reps_equiv hSB T.toEquiv tB (fun t u => by
      change T t - T u ∈ Λ ↔ _
      rw [← map_sub, tΛ]) _ (invB _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    change hatS H vol SA _ (T y) * α (T y) * opU H (T y) θ (T w) = _
    rw [hatT x hx y (hSB.1 y hy), tα, tU, funext tθ]
    ring
  have invX : ∀ w, ∀ x ∈ A, ∀ l ∈ A, l ∈ Λ →
      α (x + l) * opU H (x + l) (xiS H α vol SA SB (fun s => Φ (s - (x + l))) θ) w =
        α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) θ) w := by
    intro w x hx l hl hl'
    rw [w_add hH hA hx hl]
    congr 2
    funext v
    unfold xiS sumU
    rw [opU_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    beta_reduce
    rw [opU_mul, opU_comm hH, hatL x hx y (hSB.1 y hy) l hl hl', opU_of_fixed hΛ hθ hl', opU_mul]
    have h1 := alpha_sq hΛ hl'
    have h2 := chi_ne (H := H) l y
    field_simp
    linear_combination (hatS H vol SA (fun s => Φ (s - x)) y * α y * opU H y θ v) * h1
  unfold xiL
  rw [← sum_reps_equiv hX T.toEquiv tA (fun t u => by
      change T t - T u ∈ Λ ↔ _
      rw [← map_sub, tΛ]) _ (invX _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  change α (T x) * opU H (T x) (xiS H α vol SA SB (fun s => Φ (s - T x)) θ) (T z) = _
  rw [tα, tU, funext (xiT x (hX.1 x hx)), opU_mul]
  ring

end GlobalTheory.KerLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem tateDual_matRep_crys : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  intro l _ P K LL k M hT hM hC
  haveI : IsTopologicalRing ↥LL.1 := by
    first
      | infer_instance
      | exact Subring.instIsTopologicalRing LL.1.toSubring
      | exact inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  have hχ := _root_.GlobalTheory.HTW.Rec.continuous_cycLL_period P K LL
  have hinv : Continuous fun g : ↥(GK K) => M g⁻¹ := hM.comp continuous_inv
  have hc : Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) := by
    change Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose
    exact hχ.smul hinv.matrix_transpose
  refine ⟨hc, ?_⟩
  exact hT (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) M hM)
    (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) _ hc) (dotProductBilin ↥LL.1 ↥LL.1)
    (TwistDualLoc.isDual1_dot (P.PD K) M) hC

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowBox
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem sum_count_Icc (s : Multiset ℤ) (η : ℕ) :
    ∑ u ∈ Finset.Icc (-(η : ℤ)) η, ((s.count u : ℕ) : ℤ) =
      ((s.filter fun u : ℤ => |u| ≤ (η : ℤ)).card : ℤ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    by_cases hx : |x| ≤ (η : ℤ)
    · have hm : x ∈ Finset.Icc (-(η : ℤ)) η := Finset.mem_Icc.2 (abs_le.1 hx)
      rw [Multiset.filter_cons_of_pos (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, Multiset.card_cons, ← Finset.add_sum_erase _ _ hm,
        Multiset.count_cons_self]
      have he : ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u (x ::ₘ s) : ℕ) : ℤ) =
          ∑ u ∈ (Finset.Icc (-(η : ℤ)) η).erase x, ((Multiset.count u s : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun u hu => by
          rw [Multiset.count_cons_of_ne (Finset.ne_of_mem_erase hu)]
      rw [he]
      push_cast
      rw [← ih, ← Finset.add_sum_erase _ _ hm]
      ring
    · have hm : x ∉ Finset.Icc (-(η : ℤ)) η := fun h => hx (abs_le.2 (Finset.mem_Icc.1 h))
      rw [Multiset.filter_cons_of_neg (p := fun u : ℤ => |u| ≤ (η : ℤ)) _ hx, ← ih]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Multiset.count_cons_of_ne (fun h => hm (by rw [← h]; exact hu))]

theorem letter_one_zero {φ : Formalism.HC.Frame} (τ : φ.GG) : letter τ 1 (0 : ZMod (orderOf (1 : φ.GG))) = τ := by
  simp [letter]

theorem recWord_jumps : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ} (g : ZMod n → D.R.GG), Roomy L C → ∀ a, (∀ u ∈ jT1 (hcAt D (g a)) j (pos ε (g a)), u ∈ (recWord L j ε g).win a ∧ u ∈ Set.Icc (-((recWord L j ε g).Mi a : ℤ)) ((recWord L j ε g).hi a : ℤ)) ∧ (∀ u ∈ jT2 (hcAt D (g a)) j (pos ε (g a)), u ∈ jT1 (hcAt D (g a)) j (pos ε (g a))) ∧ ∑ u ∈ Finset.Icc (-(etaHat L : ℤ)) (etaHat L), (((jT2 (hcAt D (g a)) j (pos ε (g a))).count u : ℕ) : ℤ) ≤ D.R.m := by
  intro D L C j ε n g hR a
  obtain ⟨hT1, hbox⟩ := _root_.GlobalTheory.HTW.pageWord_T1_and_J1_mem_window_of_roomy L C j ε (g a) 1 hR
  obtain ⟨hT2, hcard⟩ := _root_.GlobalTheory.HTW.twistedDualPageWord_small_jumps_card L C j ε (g a) 1 hR
  obtain ⟨hsz, hMi, hhi, -⟩ := _root_.GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord L C j ε (g a) 1 hR 0
  have hl := letter_one_zero (g a)
  have t1 := hT1 0
  have t2 := hT2 0
  have bx := hbox 0
  have cd := (hcard 0).2
  simp only [pageWord, recWord, WordData.Mi, WordData.hi, hl] at t1 t2 bx cd hsz hMi hhi
  refine ⟨fun u hu => ?_, fun u hu => (t2.1 u hu), ?_⟩
  · have h1 := t1 u hu
    have h2 := bx u hu
    refine ⟨?_, ?_⟩
    · simp only [NWord.win, recWord, Set.mem_setOf_eq]
      rw [hsz]
      exact h1
    · simp only [recWord, Set.mem_Icc]
      rw [hMi, hhi]
      exact h2
  · rw [sum_count_Icc, cd]

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordClusterDepthLongOrbit
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_hypA_depth_of_long_orbit {D : D7} (L : SizeData₂ D) (hP : ParameterChoice' D L) (C : ℝ)
    (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG) (l : ℕ) (hR : Roomy L C) (hl : 11 ≤ l)
    (hlA : (l : ℝ) < LevelStarExponents.lA L) (ho : 4 * D.host.Lw < orderOf φ.2) :
    (pageWord L j ε τ φ).HypA (depth L l) := by
  obtain ⟨-, hLw, h2⟩ := _root_.GlobalTheory.depth_spec L hP l hl
  have h1 : 1 ≤ depth L l := le_trans (by norm_num) (h2 hlA)
  obtain ⟨hcl, hn⟩ := _root_.GlobalTheory.long_clusters D.host τ φ (depth L l) ho h1 hLw
  have hbox := _root_.GlobalTheory.HTW.pageWord_box L C j ε τ φ hR
  have hth : (pageWord L j ε τ φ).thick = fun i : ZMod (orderOf φ) => Thick D.host (letter τ φ i) :=
    funext fun i => propext (_root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ φ hR i)
  have hpar := GlobalTheory.T.mul_smallBounds_le_roundedSizeBound L 40 C (depth L l) hR (by norm_num) (by linarith [hR.1]) hLw
  refine ⟨fun i => ?_, h1, hn, fun _ => ?_, ?_⟩
  · have := hbox.2.2.2.2.2 i
    have h0 : (0 : ℤ) ≤ ((pageWord L j ε τ φ).η : ℤ) := Int.natCast_nonneg _
    linarith
  · show 40 * (depth L l + 1) * (wHat D + sHat L + etaHat L + 1) ≤ bHat L
    exact_mod_cast hpar
  · rw [hth]; exact hcl

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualPageWordInertPrimeDichotomy
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_inert_dichotomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ)
    (τ φ : D.R.GG) (l : ℕ), Roomy L C → 11 ≤ l → φ.1.2 = -1 →
    (pageWord L j ε τ φ).Box ∧ ((pageWord L j ε τ φ).HypNT ∨
      (φ = D.R.cc ∧ (pageWord L j ε τ φ).HypAT l ∧ ∀ i, (pageWord L j ε τ φ).thick i)) := by
  intro D L C j ε τ φ l hR hl hφ
  refine ⟨_root_.GlobalTheory.HTW.pageWord_box L C j ε τ φ hR, ?_⟩
  by_cases h : φ = D.R.cc ∧ Thick D.host τ
  · obtain ⟨rfl, hτ⟩ := h
    exact Or.inr ⟨rfl, GlobalTheory.T.twistedDualOrbitPageWord_conj_hypAT_allThick L C j ε τ l hR hl hτ⟩
  · left
    have hLw : 3 ≤ D.host.Lw := by
      have := L.weightLength_ge_depth
      omega
    obtain ⟨h3, i, hi⟩ := _root_.GlobalTheory.HTW.InertWord.inert_nothree_nonthick D.host τ φ hLw hφ h
    have hth := _root_.GlobalTheory.HTW.pageWord_thick_iff L C j ε τ φ hR
    refine ⟨(_root_.GlobalTheory.signs_alternate_inert ε τ φ hφ).2, ⟨i, fun h' => hi ((hth i).1 h')⟩, ?_⟩
    intro k hk
    exact h3 k ⟨(hth _).1 hk.1, (hth _).1 hk.2.1, (hth _).1 hk.2.2⟩

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordParams
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_wordNum : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) {n : ℕ}
    (g : ZMod n → D.R.GG) (ψ : D.R.GG), Roomy L C → IsOrbit g ψ → WordNum L (recWord L j ε g) := by
  intro D L C j ε n g ψ hR hO
  obtain ⟨rfl, hg⟩ := hO
  generalize g 0 = τ at hg
  obtain rfl : g = letter τ ψ := funext hg
  have hsm := pageWord_S_eta_m L j ε τ ψ
  refine ⟨?_, ?_, ?_, hsm.1, hsm.2.1, rfl⟩
  · intro a
    obtain ⟨hsz, -, -, hth⟩ := _root_.GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord L C j ε τ ψ hR a
    rcases _root_.GlobalTheory.HTW.pageWord_thickOr L C j ε τ ψ hR a with h | h
    · exact Or.inl (hth.2 h)
    · refine Or.inr ?_
      have h' : (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) ≤ ((wHat D : ℕ) : ℤ) := by
        rw [hsz]; exact h
      exact_mod_cast h'
  · have h := bHat_add_etaHat_add_sHat_le_hPage L C hR
    exact h
  · exact (_root_.GlobalTheory.HTW.Rec.wMax_le_wB L).2

end GlobalTheory.HTW.Rec
end

