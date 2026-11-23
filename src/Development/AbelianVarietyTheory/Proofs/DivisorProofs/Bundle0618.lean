module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryOneMapEqZero
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
open GlobalTheory.QLog.Window

namespace GlobalTheory.QLog.WindowMat

theorem integers_isIntegrallyClosedIn {C : Type} [Field C] {v : Valuation C NNReal} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) : IsIntegrallyClosedIn O C :=
  isIntegrallyClosedIn_iff.2 ⟨hv.hom_inj, fun h => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 h)⟩

theorem hasPeriod_zero {p : ℕ} {O B Q : Type} [CommRing O] [CommRing B] [CommRing Q] [Algebra B Q]
    {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d) {θ : B →+* O} (h : IsFrame p Q θ)
    (t : G.Tate) : c.HasPeriod θ t (0 : MvPowerSeries (Fin d) Q) 0 := by
  refine (c.hasPeriod_iff h t (0 : MvPowerSeries (Fin d) Q) 0).2 fun n z _ => ⟨0, fun m => ⟨0, fun N _ => ⟨0, ?_⟩⟩, 0, ?_⟩
  · have h0 : trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N) (0 : MvPowerSeries (Fin d) Q) = 0 :=
      map_zero _
    rw [h0, map_zero, sub_zero, mul_zero, map_zero]
  · simp

section Transfer

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] (θ : B →+* O) (Θ : Q →+* C)
  (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
include hΘ

theorem in_map_top {σ : Type} {f : MvPowerSeries σ Q} (hf : In (⊤ : Ideal B) f) :
    In (⊤ : Ideal O) (map Θ f) := fun α => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨θ b, Submodule.mem_top, by rw [coeff_map, eb, hΘ]⟩

theorem map_eq_zero_of_in_ker {σ : Type} {f : MvPowerSeries σ Q} (hf : In (RingHom.ker θ) f) :
    map Θ f = 0 := by
  ext α
  obtain ⟨b, hb, eb⟩ := hf α
  rw [coeff_map, eb, hΘ, RingHom.mem_ker.1 hb, map_zero, map_zero]

theorem map_comb {σ ι : Type} [Finite σ] [Fintype ι] (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) fun i => map Θ (e i) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul', hΘ]

theorem lin_map {d : ℕ} (f : MvPowerSeries (Fin d) Q) (i : Fin d) : lin (map Θ f) i = Θ (lin f i) := by
  simp only [lin, coeff_map]

theorem up_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i) (i : Fin d) :
    up C μ i = map Θ (up Q μ' i) := by
  ext α
  simp only [up, coeff_map, ← hμ, hΘ]

theorem ql_map {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL μ ⊤ (map Θ f) := by
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, hf.1, map_zero]
  · obtain ⟨b, -, eb⟩ := hf.2.1 i
    exact ⟨θ b, Submodule.mem_top, by rw [lin_map θ Θ hΘ, eb, hΘ]⟩
  · have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
    rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
    exact in_map_top θ Θ hΘ hf.2.2

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} {μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B}
    {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, map θ (μ' i) = μ i)
    (h0 : ∀ i, constantCoeff (μ' i) = 0) {f : MvPowerSeries (Fin d) Q}
    (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) : cob1 (up C μ) (map Θ f) = 0 := by
  have : up C μ = fun i => map Θ (up Q μ' i) := funext (up_map θ Θ hΘ hμ)
  rw [this, ← map_formalGroupLawCoboundaryOne_eq Θ _ (constantCoeff_up h0)]
  exact map_eq_zero_of_in_ker θ Θ hΘ hf

end Transfer

theorem comb_sum {B Q σ ι κ : Type} [CommRing B] [CommRing Q] [Algebra B Q] [Fintype ι] [Fintype κ]
    (R : κ → ι → B) (a : ι → B) (e : κ → MvPowerSeries σ Q) :
    comb (fun l => ∑ i, R l i * a i) e = ∑ i, algebraMap B Q (a i) • comb (fun l => R l i) e := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem din_of_in {B Q σ : Type} [CommRing B] [CommRing Q] [Algebra B Q] {f : MvPowerSeries σ Q}
    (hf : In (⊤ : Ideal B) f) : DIn (⊤ : Ideal B) f := fun α i => by
  obtain ⟨b, -, eb⟩ := hf α
  exact ⟨(α i : B) * b, Submodule.mem_top, by rw [eb, map_mul, map_natCast]⟩

end GlobalTheory.QLog.WindowMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawNatMultipleAddMulLaws
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NMul

variable {R : Type} [CommRing R] {d : ℕ}

theorem nmul_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) :
    nmul μ 0 = fun _ => 0 := rfl

theorem nmul_succ' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) (fun i => X i) := by
  unfold nmul
  rw [Function.iterate_succ_apply']

theorem nmul_const (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul_zero']
  | succ n ih =>
    rw [nmul_succ']
    exact (_root_.GlobalTheory.Katz.LawMonoid.mon R d μ hμ (Fin d) (nmul μ n) (fun i => X i) (fun _ => 0) ih
      (fun i => constantCoeff_X i) (fun _ => map_zero _)).1

theorem nmul_add (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) := by
  induction n with
  | zero =>
    rw [Nat.add_zero, nmul_zero']
    exact ((_root_.GlobalTheory.Katz.LawMonoid.mon R d μ hμ (Fin d) (nmul μ m) (fun _ => 0) (fun _ => 0)
      (nmul_const μ hμ m) (fun _ => map_zero _) (fun _ => map_zero _)).2.2.2.1).symm
  | succ n ih =>
    rw [← Nat.add_assoc, nmul_succ', ih, nmul_succ']
    exact (_root_.GlobalTheory.Katz.LawMonoid.mon R d μ hμ (Fin d) (nmul μ m) (nmul μ n) (fun i => X i)
      (nmul_const μ hμ m) (nmul_const μ hμ n) (fun i => constantCoeff_X i)).2.1

theorem nmul_one (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) :
    nmul μ 1 = fun i => X i := by
  rw [nmul_succ', nmul_zero']
  have h := _root_.GlobalTheory.Katz.LawMonoid.mon R d μ hμ (Fin d) (fun i => X i) (fun _ => 0) (fun _ => 0)
    (fun i => constantCoeff_X i) (fun _ => map_zero _) (fun _ => map_zero _)
  rw [← h.2.2.1, h.2.2.2.1]

theorem nmul_mul (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : IsLaw μ) (m n : ℕ) :
    ∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i) := by
  have ha : HasSubst (nmul μ n) := hasSubst_of_constantCoeff_zero (nmul_const μ hμ n)
  induction m with
  | zero =>
    intro i
    rw [Nat.zero_mul, nmul_zero']
    exact (map_zero (substAlgHom (R := R) ha)).symm.trans (by rw [coe_substAlgHom])
  | succ m ih =>
    intro i
    rw [Nat.succ_mul, nmul_add μ hμ, nmul_succ']
    rw [(_root_.GlobalTheory.Katz.LawMonoid.mon R d μ hμ (Fin d) (nmul μ m) (fun i => X i) (fun _ => 0)
      (nmul_const μ hμ m) (fun i => constantCoeff_X i) (fun _ => map_zero _)).2.2.2.2
      (Fin d) (nmul μ n) (nmul_const μ hμ n) i]
    have e1 : (fun j => subst (nmul μ n) (nmul μ m j)) = nmul μ (m * n) := funext fun j => (ih j).symm
    have e2 : (fun j => subst (nmul μ n) ((X j : MvPowerSeries (Fin d) R))) = nmul μ n :=
      funext fun j => subst_X ha j
    rw [e1, e2]

theorem nmul_laws : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    IsLaw μ → ∀ m n : ℕ, (∀ i, constantCoeff (nmul μ n i) = 0) ∧
      nmul μ (m + n) = op μ (nmul μ m) (nmul μ n) ∧
      (∀ i, nmul μ (m * n) i = subst (nmul μ n) (nmul μ m i)) ∧ nmul μ 1 = fun i => X i :=
  fun _ _ _ μ hμ m n => ⟨nmul_const μ hμ n, nmul_add μ hμ m n, nmul_mul μ hμ m n, nmul_one μ hμ⟩

end GlobalTheory.NMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDp
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.DPLog

theorem finsum_mem_addSubmonoid {M ι : Type*} [AddCommMonoid M] (S : AddSubmonoid M)
    {f : ι → M} (hf : ∀ i, f i ∈ S) : ∑ᶠ i, f i ∈ S := by
  classical
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]; exact S.sum_mem fun i _ => hf i
  · rw [finsum_of_infinite_support h]; exact S.zero_mem

theorem formalLog_in_of_sub_one_mem : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B]
    [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ →
    ∀ J : Ideal B, (∀ x ∈ J, ∃ y ∈ J, x ^ p = p * y) → ∀ (σ : Type) (h : MvPowerSeries σ B),
    constantCoeff h = 1 → (∀ α, coeff α (h - 1) ∈ J) →
    In J (formalLog (map (algebraMap B Q) h)) := by
  intro p _ B O Q _ _ _ _ _ θ hF J hJ σ h h1 hJh
  let S : AddSubmonoid Q := J.toAddSubmonoid.map (algebraMap B Q).toAddMonoidHom
  have hS : ∀ q, q ∈ S ↔ ∃ b ∈ J, q = algebraMap B Q b := fun q =>
    AddSubmonoid.mem_map.trans
      ⟨fun ⟨b, hb, e⟩ => ⟨b, hb, e.symm⟩, fun ⟨b, hb, e⟩ => ⟨b, hb, e.symm⟩⟩
  have hww : map (algebraMap B Q) h - 1 = map (algebraMap B Q) (h - 1) := by
    rw [map_sub, map_one]
  have hsub : PowerSeries.HasSubst (map (algebraMap B Q) h - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [h1])
  intro α
  refine (hS _).1 ?_
  rw [formalLog, PowerSeries.coeff_subst hsub]
  refine finsum_mem_addSubmonoid S fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [S.zero_mem]
  obtain ⟨y, hy, hwy⟩ :=
    DPSeries.pow_eq_factorial_mul p B O Q θ hF J hJ σ (h - 1) hJh d hd
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  refine (hS _).2 ⟨((-1 : B) ^ (k + 2) * (k.factorial : B)) * coeff α y,
    J.mul_mem_left _ (hy α), ?_⟩
  rw [hww, ← map_pow, hwy, coeff_map, ← map_natCast (C (σ := σ) (R := B)), coeff_C_mul,
    PowerSeries.coeff_log, if_neg (Nat.succ_ne_zero k), smul_eq_mul]
  have e : algebraMap ℚ Q ((k + 1 : ℕ) : ℚ)⁻¹ * ((k + 1 : ℕ) : Q) = 1 := by
    rw [← map_natCast (algebraMap ℚ Q), ← map_mul, inv_mul_cancel₀ (by positivity), map_one]
  rw [div_eq_mul_inv, map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_neg, map_neg,
    map_one, map_one, map_natCast, map_natCast, Nat.factorial_succ, Nat.cast_mul]
  linear_combination ((-1 : Q) ^ (k + 2) * (k.factorial : Q) * algebraMap B Q (coeff α y)) * e

end GlobalTheory.DPLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobXiEigenvectorEqOfFrameImageEq
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WinLift

theorem eigen_eq_of_frame_eq : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ x y : Ainf p O, WittVector.frobenius x = WittVector.frobenius (xi ε) * x → WittVector.frobenius y = WittVector.frobenius (xi ε) * y → F.a x = F.a y → x = y := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F x y hx hy hxy
  have hsub : WittVector.frobenius (x - y) = WittVector.frobenius (xi ε) * (x - y) := by
    rw [map_sub, hx, hy, mul_sub]
  obtain ⟨c, hc, -⟩ := GlobalTheory.PDivLat.existsUnique_padic_of_eigen p C v O hv ε hε (x - y) hsub
  have h0 : F.a (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [← hc, map_mul, ← F.p_τ] at h0
  have h1 : F.τ * F.a (ofPadic p O c) = 0 := by
    apply tf F
    rw [← h0]; ring
  have h2 : Sandwich.mu ε ∣ ofPadic p O c := (F.τ_mul _).1 h1
  have h3 : WittVector.fontaineTheta O p (ofPadic p O c) = 0 := by
    obtain ⟨w, hw⟩ := h2
    rw [hw, map_mul, theta_mu hv hε, zero_mul]
  have hc0 : c = 0 := by
    by_contra hne
    have hs := PadicInt.unitCoeff_spec hne
    rw [hs, map_mul, map_pow, map_natCast, map_mul, map_pow, map_natCast] at h3
    have hp : (p : O) ≠ 0 := by
      intro h
      have := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
    have hu : IsUnit (WittVector.fontaineTheta O p (ofPadic p O (PadicInt.unitCoeff hne : ℤ_[p]))) :=
      ((PadicInt.unitCoeff hne).isUnit.map (ofPadic p O)).map _
    rcases mul_eq_zero.1 h3 with h | h
    · exact hu.ne_zero h
    · exact hp (pow_eq_zero_iff'.1 h).1
  rw [← sub_eq_zero, ← hc, hc0, map_zero, zero_mul]

end GlobalTheory.WinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusCongruenceCombinationOverIntegers
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

namespace GlobalTheory.SmallSecond.ToO

theorem frob_eq_expand {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) : frob p s f = expand p hp (map s f) := by
  rw [frob, expand, substAlgHom_apply]

theorem coeff_frob_smul {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) (β : τ →₀ ℕ) : coeff (p • β) (frob p s f) = s (coeff β f) := by
  rw [frob_eq_expand p hp, coeff_expand_smul, coeff_map]

theorem coeff_frob_of_not_dvd {Q τ : Type} [CommRing Q] (p : ℕ) (hp : p ≠ 0) (s : Q →+* Q)
    (f : MvPowerSeries τ Q) {α : τ →₀ ℕ} {i : τ} (h : ¬ p ∣ α i) : coeff α (frob p s f) = 0 := by
  rw [frob_eq_expand p hp]
  exact coeff_expand_of_not_dvd p hp _ h

theorem formalGroupLawCoboundaryOne_sub {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) (f g : MvPowerSeries (Fin d) Q) :
    cob1 μ (f - g) = cob1 μ f - cob1 μ g := by
  have := formalCoboundary_add h (f - g) g
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

theorem formalGroupLawCoboundaryOne_finset_sum {Q : Type} [CommRing Q] {d : ℕ} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) Q}
    (h : ∀ i, constantCoeff (μ i) = 0) {ι : Type} (S : Finset ι) (f : ι → MvPowerSeries (Fin d) Q) :
    cob1 μ (∑ i ∈ S, f i) = ∑ i ∈ S, cob1 μ (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have := formalCoboundary_smul h 0 0
    simpa using this
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, formalCoboundary_add h, ih]

end GlobalTheory.SmallSecond.ToO


open GlobalTheory.SmallSecond.ToO in
theorem GlobalTheory.SmallSecond.frob_congr_to_O : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (F : BFrame ε) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), (∀ i, QL μ' ⊤ (e i)) → ∀ (W : Fin d ⊕ Fin k → F.B) (b : Fin k → F.B), (∀ l, ¬IsUnit (F.θ (W l))) → In (⊤ : Ideal F.B) (frob p F.s (comb (Sum.elim (fun _ => 0) b) e) - comb W e) → In (Ideal.span {(p : F.B)}) (cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => 0) b) e)) - frob p F.s (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e))) → ∃ (F₁ : MvPowerSeries (Fin d ⊕ Fin d) F.B) (t : MvPowerSeries (Fin d) O), map (algebraMap F.B F.Q) F₁ = cob1 (up F.Q μ') (comb (Sum.elim (fun _ => 0) b) e) ∧ (∀ i, ¬IsUnit (lin t i)) ∧ (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - F.θ (coeff β F₁) ^ p)) ∧ ∀ α : Fin d ⊕ Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α (cob1 μ t)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε F d μ μ' hlift hmap k e he W b hW hT hC
  classical
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  haveI : IsLocalRing O := ValuationRing.isLocalRing O
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set m := IsLocalRing.maximalIdeal O with hm
  have memm : ∀ x : O, x ∈ m ↔ ¬IsUnit x := fun x => by
    rw [hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hpm : (p : O) ∈ m := (memm _).2 Fact.out
  have hθp : ∀ x : F.B, F.θ ((p : F.B) * x) ∈ m := fun x => by
    rw [map_mul, map_natCast]; exact m.mul_mem_right _ hpm
  have hWm : ∀ l, F.θ (W l) ∈ m := fun l => (memm _).2 (hW l)
  have hμQ : ∀ i, constantCoeff (up F.Q μ' i) = 0 := fun i => by
    rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hlift.const, map_zero]
  have hcomb : ∀ c : Fin d ⊕ Fin k → F.B, cob1 (up F.Q μ') (comb c e) =
      ∑ l, algebraMap F.B F.Q (c l) • cob1 (up F.Q μ') (e l) := by
    intro c
    unfold comb
    rw [formalGroupLawCoboundaryOne_finset_sum hμQ]
    exact Finset.sum_congr rfl fun l _ => formalCoboundary_smul hμQ _ _
  choose g _ hg using fun l => (he l).2.2
  choose c1 _ hc1 using fun l => (he l).2.1
  have hSm : ∀ α, F.θ (∑ l, W l * g l α) ∈ m := fun α => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l)
  have hF : In (⊤ : Ideal F.B) (cob1 (up F.Q μ') (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) := by
    intro α
    refine ⟨∑ l, Sum.elim (fun _ => (0 : F.B)) b l * g l α, trivial, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hcomb, map_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [MvPowerSeries.coeff_smul, hg, map_mul]
  obtain ⟨F₁, hF₁⟩ := In.top_iff.1 hF
  obtain ⟨T, hTT⟩ := In.top_iff.1 hT
  have hcobT : ∀ α, coeff α (cob1 μ (map F.θ T)) = F.θ (coeff α (cob1 μ' T)) := by
    intro α
    have hμeq : μ = fun i => map F.θ (μ' i) := funext fun i => (hmap i).symm
    rw [hμeq, ← map_formalGroupLawCoboundaryOne_eq F.θ μ' hlift.const T, coeff_map]
  have hup : map (algebraMap F.B F.Q) (cob1 μ' T) =
      cob1 (up F.Q μ') (frob p F.s (comb (Sum.elim (fun _ => (0 : F.B)) b) e)) -
        ∑ l, algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l) := by
    rw [map_formalGroupLawCoboundaryOne_eq (algebraMap F.B F.Q) μ' hlift.const T]
    change cob1 (up F.Q μ') (map (algebraMap F.B F.Q) T) = _
    rw [hTT, formalGroupLawCoboundaryOne_sub hμQ, hcomb]
  choose r hr hrC using hC
  have hgen : ∀ α, algebraMap F.B F.Q (coeff α (cob1 μ' T)) =
      coeff α (frob p F.s (map (algebraMap F.B F.Q) F₁)) + algebraMap F.B F.Q (r α) -
        algebraMap F.B F.Q (∑ l, W l * g l α) := by
    intro α
    have h1 := congrArg (coeff α) hup
    rw [coeff_map] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, ← hrC α, map_sub, map_sub, hF₁, map_sum, map_sum]
    have h2 : ∑ l, coeff α (algebraMap F.B F.Q (W l) • cob1 (up F.Q μ') (e l)) =
        ∑ l, algebraMap F.B F.Q (W l * g l α) :=
      Finset.sum_congr rfl fun l _ => by rw [MvPowerSeries.coeff_smul, hg, map_mul]
    rw [h2]; ring
  refine ⟨F₁, map F.θ T, hF₁, fun i => (memm _).1 ?_, fun β => (memm _).1 ?_,
    fun α ⟨i, hi⟩ => (memm _).1 ?_⟩
  · have key : coeff (Finsupp.single i 1) T = -∑ l, W l * c1 l i := by
      apply F.frame.inj
      have h1 := congrArg (coeff (Finsupp.single i 1)) hTT
      rw [coeff_map] at h1
      have hnd : ¬ p ∣ (Finsupp.single i 1 : Fin d →₀ ℕ) i := by
        rw [Finsupp.single_eq_same]; exact (Fact.out : p.Prime).not_dvd_one
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h1, map_sub, coeff_frob_of_not_dvd p hp0 _ _ hnd, zero_sub, map_neg, map_sum]
      unfold comb
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      have := hc1 l i
      simp only [lin] at this
      rw [MvPowerSeries.coeff_smul, this, map_mul]
    unfold lin
    set_option synthInstance.maxHeartbeats 100000 in
      rw [coeff_map, key, map_neg, map_sum]
    exact m.neg_mem (m.sum_mem fun l _ => by rw [map_mul]; exact m.mul_mem_right _ (hWm l))
  · have h1 := hgen (p • β)
    rw [coeff_frob_smul p hp0, coeff_map, F.s_alg, ← map_add (f := _), ← map_sub] at h1
    rw [hcobT, F.frame.inj h1]
    obtain ⟨y, hy⟩ := F.σ_pow (coeff β F₁)
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr (p • β))
    have e1 : F.θ (F.σ (coeff β F₁) + r (p • β) - ∑ l, W l * g l (p • β)) - F.θ (coeff β F₁) ^ p =
        F.θ (F.σ (coeff β F₁) - coeff β F₁ ^ p) + F.θ (r (p • β)) -
          F.θ (∑ l, W l * g l (p • β)) := by
      simp only [map_sub, map_add (f := _), map_pow]; ring
    rw [e1, hy, hr']
    exact m.sub_mem (m.add_mem (hθp y) (hθp r')) (hSm _)
  · have h1 := hgen α
    rw [coeff_frob_of_not_dvd p hp0 _ _ hi, zero_add, ← map_sub] at h1
    rw [hcobT, F.frame.inj h1, map_sub]
    obtain ⟨r', hr'⟩ := Ideal.mem_span_singleton.1 (hr α)
    rw [hr']
    exact m.sub_mem (hθp r') (hSm _)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusSubstMapCongrPowModPStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_subst_map_congr_pow_mod_p : ∀ (p : ℕ) [Fact p.Prime] (B : Type) [CommRing B] (σB : B →+* B), (∀ b, (p : B) ∣ σB b - b ^ p) → ∀ (d : ℕ) (g : MvPowerSeries (Fin d) B) (α : Fin d →₀ ℕ), (p : B) ∣ coeff α (subst (fun i => (X i : MvPowerSeries (Fin d) B) ^ p) (map σB g) - g ^ p) := by
  first | exact @GlobalTheory.FrobCong.frobenius_congr | exact GlobalTheory.FrobCong.frobenius_congr | (intros; apply GlobalTheory.FrobCong.frobenius_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeEndProductPowersTransportGrpPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.ActFin
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupSchemeEndProductPowers_transport_grpPullback : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S') [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A t φ → ∀ (r : ℕ) (g : Fin r → (A' ⟶ A')) (f : Fin r → (A ⟶ A)) (c : Fin r → ℤ), (∀ k, (g k).left ≫ φ = φ ≫ (f k).left) → (∏ k, g k ^ c k).left ≫ φ = φ ≫ (∏ k, f k ^ c k).left := by
  first | (exact @GlobalTheory.ActFin.prod_zpow_transport) | (exact GlobalTheory.ActFin.prod_zpow_transport) | (intros; apply GlobalTheory.ActFin.prod_zpow_transport  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinearStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ u : Fin d → R, (∀ F G : MvPowerSeries (Fin d) R, invDer μ u (F + G) = invDer μ u F + invDer μ u G) ∧ (∀ (a : R) (F : MvPowerSeries (Fin d) R), invDer μ u (a • F) = a • invDer μ u F) ∧ ∀ a : R, invDer μ u (C a) = 0 := by
  first | exact @GlobalTheory.LawDer.Linear.invDer_linear | exact GlobalTheory.LawDer.Linear.invDer_linear | (intros; apply GlobalTheory.LawDer.Linear.invDer_linear <;> assumption)
end

