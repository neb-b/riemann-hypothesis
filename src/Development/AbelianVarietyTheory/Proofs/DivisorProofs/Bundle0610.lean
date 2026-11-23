module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0566
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0014

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstZero
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.PullQuasiLog

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (j : σ) :
    Katz.lift p (X j : MvPowerSeries σ k) = X j := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs <;> simp

theorem intBy_le_one (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type}
    (c : WittVector p k) : intBy p k σ c ≤ intBy p k σ 1 := by
  intro f hf α
  obtain ⟨w, hw⟩ := hf α
  exact ⟨c * w, by rw [hw, one_mul]⟩

theorem constantCoeff_subst_zero {R : Type} [CommRing R] {σ τ : Type} [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ R}
    (hf : constantCoeff f = 0) : constantCoeff (subst a f) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ha) ha hf

theorem elim_const {R : Type} [CommRing R] {d : ℕ} {τ : Type} {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    ∀ s, constantCoeff (Sum.elim u v s) = 0 := fun s => by cases s <;> simp [hu, hv]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hν : IsLaw ν), ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) f = f ∧ (∀ (d' : ℕ) (φ : Fin d → MvPowerSeries (Fin d') k) (ψ : Fin e → MvPowerSeries (Fin d) k), (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (subst φ (ψ l))) f - subst (fun j => Katz.lift p (φ j)) (subst (fun l => Katz.lift p (ψ l)) f) ∈ intBy p k (Fin d') 1) ∧ ∀ φ ψ : Fin e → MvPowerSeries (Fin d) k, (∀ j, constantCoeff (φ j) = 0) → (∀ j, constantCoeff (ψ j) = 0) → subst (fun l => Katz.lift p (op ν φ ψ l)) f - subst (fun l => Katz.lift p (φ l)) f - subst (fun l => Katz.lift p (ψ l)) f ∈ intBy p k (Fin d) 1 := by
  intro p _ k _ _ _ d e ν hν f hf
  have hf' : f ∈ quasiInt p k (Fin e) ∧ cob1 (fun i => lift p (ν i)) f ∈ intBy p k _ 1 := hf
  have hred := fun (σ : Type) => _root_.GlobalTheory.Katz.red_rules p k σ
  refine ⟨?_, ?_, ?_⟩
  · have : (fun j => Katz.lift p (X j : MvPowerSeries (Fin e) k)) = X := funext fun j => lift_X p j
    rw [this, subst_self]; rfl
  · intro d' φ ψ hφ hψ
    have hΦ : ∀ j, constantCoeff (lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (lift p (ψ j)) = 0 := fun j => constantCoeff_lift p (hψ j)
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hΨ)
      (hasSubst_of_constantCoeff_zero hΦ)]
    apply intBy_le_one p (p : WittVector p k)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d') _ _ (fun l => subst φ (ψ l)) f
      (fun l => constantCoeff_lift p (constantCoeff_subst_zero hφ (hψ l)))
      (fun l => constantCoeff_subst_zero hΦ (hΨ l))
      (fun l => (hred (Fin d')).2.2.1 _)
      (fun l => (_root_.GlobalTheory.Katz.red_subst p k (Fin d) (Fin d') (fun j => lift p (φ j)) φ hΦ
        (fun j => (hred (Fin d')).2.2.1 _)).1 _ _ ((hred (Fin d)).2.2.1 _)) hf'.1
  · intro φ ψ hφ hψ
    set Φ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (φ l) with hΦdef
    set Ψ : Fin e → MvPowerSeries (Fin d) (Fr p k) := fun l => lift p (ψ l) with hΨdef
    have hΦ : ∀ j, constantCoeff (Φ j) = 0 := fun j => constantCoeff_lift p (hφ j)
    have hΨ : ∀ j, constantCoeff (Ψ j) = 0 := fun j => constantCoeff_lift p (hψ j)
    have hL : ∀ i, constantCoeff (lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
    have hcalc := _root_.GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt (Fr p k) e (Fin d) (Fin d) Φ Ψ hΦ hΨ
    have hredE : ∀ s, Red p (Sum.elim Φ Ψ s) (Sum.elim φ ψ s) := fun s => by
      cases s <;> exact (hred (Fin d)).2.2.1 _
    have hsub := _root_.GlobalTheory.Katz.red_subst p k (Fin e ⊕ Fin e) (Fin d) (Sum.elim Φ Ψ) (Sum.elim φ ψ)
      (elim_const hΦ hΨ) hredE
    have hcob : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ =
        subst (op (fun i => lift p (ν i)) Φ Ψ) f - subst Φ f - subst Ψ f := by
      unfold cob1
      rw [(hcalc.2.2.1 _ _).2, (hcalc.2.2.1 _ _).2, hcalc.1, hcalc.2.1,
        hcalc.2.2.2.2.2.1 e _ hL f]
      rfl
    have h1 : at2 (cob1 (fun i => lift p (ν i)) f) Φ Ψ ∈ intBy p k (Fin d) 1 :=
      hsub.2 1 _ hf'.2
    have h2 : subst (fun l => lift p (op ν φ ψ l)) f - subst (op (fun i => lift p (ν i)) Φ Ψ) f
        ∈ intBy p k (Fin d) 1 := by
      apply intBy_le_one p (p : WittVector p k)
      refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d) _ _ (op ν φ ψ) f
        (fun l => constantCoeff_lift p (constantCoeff_subst_zero (elim_const hφ hψ) (hν.const l)))
        (fun l => constantCoeff_subst_zero (elim_const hΦ hΨ) (hL l))
        (fun l => (hred (Fin d)).2.2.1 _)
        (fun l => hsub.1 _ _ ((hred (Fin e ⊕ Fin e)).2.2.1 _)) hf'.1
    have := add_mem h2 h1
    rw [hcob] at this
    convert this using 1
    abel

end GlobalTheory.Katz.PullQuasiLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffUpNmul
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DefectComp

variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ}

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_zero (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) :
    _root_.GlobalTheory.QLog.nmul μ 0 = fun _ => 0 := rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_succ_eq_op_X (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S) (k : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (k + 1) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ k) (fun i => X i) := by
  rw [_root_.GlobalTheory.QLog.nmul, _root_.GlobalTheory.QLog.nmul, Function.iterate_succ_apply']

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma hasSubst_sumElim_of_constantCoeff_eq_zero {τ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) :
    HasSubst (Sum.elim v w) :=
  hasSubst_of_constantCoeff_zero fun s => by cases s <;> simp [hv, hw]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_katz_op_eq_zero {τ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.Katz.op μ v w i) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw)
    (fun s => by cases s <;> simp [hv, hw]) (hμ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma constantCoeff_nmul_eq_zero' (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (k : ℕ) (i : Fin d) :
    constantCoeff (_root_.GlobalTheory.QLog.nmul μ k i) = 0 := by
  induction k generalizing i with
  | zero => simp [nmul_zero]
  | succ k ih =>
    rw [nmul_succ_eq_op_X]
    exact constantCoeff_katz_op_eq_zero μ hμ ih (fun j => constantCoeff_X j) i

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma mvPowerSeries_map_injective {σ A B : Type} [CommRing A] [CommRing B] {h : A →+* B}
    (hh : Function.Injective h) : Function.Injective (map (σ := σ) h) := fun p q hpq => by
  ext n
  apply hh
  simpa using congrArg (coeff n) hpq

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_zero_divisor {σ τ : Type} {c : σ → MvPowerSeries τ S} (hc : HasSubst c) :
    subst c (0 : MvPowerSeries σ S) = 0 := by
  rw [← coe_substAlgHom hc, map_zero]

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_subst_sumElim_eq_subst_sumElim_subst {τ υ : Type} {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (g : MvPowerSeries (Fin d ⊕ Fin d) S) :
    subst c (subst (Sum.elim v w) g) =
      subst (Sum.elim (fun j => subst c (v j)) (fun j => subst c (w j))) g := by
  rw [subst_comp_subst_apply (hasSubst_sumElim_of_constantCoeff_eq_zero hv hw) hc]
  congr 1
  funext s
  cases s <;> rfl

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_katz_op_eq_op_subst {τ υ : Type} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S)
    {v w : Fin d → MvPowerSeries τ S}
    (hv : ∀ i, constantCoeff (v i) = 0) (hw : ∀ i, constantCoeff (w i) = 0)
    {c : τ → MvPowerSeries υ S} (hc : HasSubst c) (i : Fin d) :
    subst c (_root_.GlobalTheory.Katz.op μ v w i) =
      _root_.GlobalTheory.Katz.op μ (fun j => subst c (v j)) (fun j => subst c (w j)) i :=
  subst_subst_sumElim_eq_subst_sumElim_subst hv hw hc (μ i)

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma nmul_add_eq_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (a b : ℕ) :
    _root_.GlobalTheory.QLog.nmul μ (a + b) =
      _root_.GlobalTheory.Katz.op μ (_root_.GlobalTheory.QLog.nmul μ a) (_root_.GlobalTheory.QLog.nmul μ b) := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have ha : HasSubst (_root_.GlobalTheory.QLog.nmul μ a) := hasSubst_of_constantCoeff_zero (hN a)
  induction b with
  | zero =>
    funext i
    have h := congrArg (subst (_root_.GlobalTheory.QLog.nmul μ a))
      (congrFun hG.unit i)
    rw [subst_katz_op_eq_op_subst μ (fun j => constantCoeff_X j) (fun _ => by simp) ha] at h
    simp only [subst_X ha, subst_zero_divisor ha] at h
    rw [Nat.add_zero, nmul_zero]
    exact h.symm
  | succ b ih =>
    rw [← Nat.add_assoc, nmul_succ_eq_op_X, ih, nmul_succ_eq_op_X]
    funext i
    have hc : HasSubst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))) :=
      hasSubst_of_constantCoeff_zero fun s => by rcases s with s | s | s <;> simp [hN]
    have h := congrArg (subst (Sum.elim (_root_.GlobalTheory.QLog.nmul μ a)
        (Sum.elim (_root_.GlobalTheory.QLog.nmul μ b) fun j => (X j : MvPowerSeries (Fin d) S))))
      (congrFun hG.assoc i)
    have h1 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x1 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x1]
    have h2 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x2 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x2]
    have h3 : ∀ j, constantCoeff (_root_.GlobalTheory.Katz.x3 (R := S) (d := d) j) = 0 := fun j => by
      simp [_root_.GlobalTheory.Katz.x3]
    rw [subst_katz_op_eq_op_subst μ (constantCoeff_katz_op_eq_zero μ hμ h1 h2) h3 hc,
      subst_katz_op_eq_op_subst μ h1 (constantCoeff_katz_op_eq_zero μ hμ h2 h3) hc] at h
    simp_rw [subst_katz_op_eq_op_subst μ h1 h2 hc, subst_katz_op_eq_op_subst μ h2 h3 hc] at h
    simp only [_root_.GlobalTheory.Katz.x1, _root_.GlobalTheory.Katz.x2, _root_.GlobalTheory.Katz.x3,
      subst_X hc, Sum.elim_inl, Sum.elim_inr] at h
    exact h

set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
private lemma subst_nmul_nmul_eq_nmul_mul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) S}
    (hG : _root_.GlobalTheory.Katz.IsLaw μ) (k m : ℕ) (i : Fin d) :
    subst (_root_.GlobalTheory.QLog.nmul μ m) (_root_.GlobalTheory.QLog.nmul μ k i) =
      _root_.GlobalTheory.QLog.nmul μ (k * m) i := by
  have hμ := hG.const
  have hN := constantCoeff_nmul_eq_zero' μ hμ
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) := hasSubst_of_constantCoeff_zero (hN m)
  induction k generalizing i with
  | zero =>
    simp only [Nat.zero_mul, nmul_zero]
    exact subst_zero_divisor hm
  | succ k ih =>
    rw [nmul_succ_eq_op_X, subst_katz_op_eq_op_subst μ (hN k) (fun j => constantCoeff_X j) hm]
    simp_rw [ih, subst_X hm]
    rw [Nat.succ_mul, nmul_add_eq_op hG]


set_option autoImplicit false in
open MvPowerSeries TensorProduct in
variable {R Q : Type} [CommRing R] [CommRing Q] [Algebra R Q] {d : ℕ} in
variable {S : Type} [CommRing S] in
theorem _root_.GlobalTheory.DefectComp.main : ∀ (R Q : Type) [CommRing R] [CommRing Q] [Algebra R Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), _root_.GlobalTheory.Katz.IsLaw μ → Function.Injective (algebraMap R Q) → ∀ (f : MvPowerSeries (Fin d) Q), constantCoeff f = 0 → ∀ (k m : ℕ) (s t u : MvPowerSeries (Fin d) R), map (algebraMap R Q) s = _root_.GlobalTheory.QLog.defect μ k f → map (algebraMap R Q) t = _root_.GlobalTheory.QLog.defect μ m f → map (algebraMap R Q) u = _root_.GlobalTheory.QLog.defect μ (k * m) f → u = subst (_root_.GlobalTheory.QLog.nmul μ m) s + (k : R) • t := by
  intro R Q _ _ _ d μ hG hinj f _ k m s t u hs ht hu
  have hμ := hG.const
  have hm : HasSubst (_root_.GlobalTheory.QLog.nmul μ m) :=
    hasSubst_of_constantCoeff_zero (constantCoeff_nmul_eq_zero' μ hμ m)
  have hmQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ m
  have hkQ := _root_.GlobalTheory.QLog.hasSubst_up_nmul (Q := Q) hμ k
  apply mvPowerSeries_map_injective hinj
  rw [map_add (f := _), map_subst hm, hs, hu, Nat.cast_smul_eq_nsmul, map_nsmul, ht]
  change _ = subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
    (_root_.GlobalTheory.QLog.defect μ k f) + _
  simp only [_root_.GlobalTheory.QLog.defect]
  rw [subst_sub hmQ, subst_smul hmQ, subst_comp_subst_apply hkQ hmQ]
  have hcomp : (fun i => subst (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ m))
      (_root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ k) i)) =
      _root_.GlobalTheory.QLog.up Q (_root_.GlobalTheory.QLog.nmul μ (k * m)) := by
    funext i
    change subst (fun j => map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ m j))
      (map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ k i)) =
        map (algebraMap R Q) (_root_.GlobalTheory.QLog.nmul μ (k * m) i)
    rw [← map_subst hm, subst_nmul_nmul_eq_nmul_mul hG]
  rw [hcomp, ← Nat.cast_smul_eq_nsmul Q, Nat.cast_mul, mul_smul, smul_sub]
  abel

end GlobalTheory.DefectComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalPiTensorNoBlockUnipotentFixed
section
noncomputable section

namespace GlobalTheory.HcIrr

open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.DIV

section UnipGroup

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}

theorem unip_diag_mul (b : ι → Fin s) {g h : GL ι K} (hg : g ∈ unip K b) (hh : h ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g * h : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hg.2 i i rfl, if_pos rfl, one_mul, hh.2 i j hij]
  · intro k _ hki
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.1 i k hlt, zero_mul]
    · rw [hg.2 i k heq.symm, if_neg (Ne.symm hki), zero_mul]
    · rw [hh.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem unip_diag_inv (b : ι → Fin s) {g : GL ι K} (hg : g ∈ unip K b)
    (i j : ι) (hij : b i = b j) : ((g⁻¹ : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
  have h1 : ((g⁻¹ * g : GL ι K) : Matrix ι ι K) i j = if i = j then 1 else 0 := by
    rw [inv_mul_cancel, Units.val_one, Matrix.one_apply]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single j] at h1
  · rwa [hg.2 j j rfl, if_pos rfl, mul_one] at h1
  · intro k _ hkj
    rcases lt_trichotomy (b k) (b i) with hlt | heq | hgt
    · rw [hg.1.2 i k hlt, zero_mul]
    · rw [hg.2 k j (heq.trans hij), if_neg hkj, mul_zero]
    · rw [hg.1.1 k j (by rw [← hij]; exact hgt), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

def cuspUnipGroup (b : ι → Fin s) : Subgroup (GL ι K) where
  carrier := unip K b
  one_mem' := ⟨one_mem _, fun i j _ => by rw [Units.val_one, Matrix.one_apply]⟩
  mul_mem' hg hh := ⟨mul_mem hg.1 hh.1, unip_diag_mul b hg hh⟩
  inv_mem' hg := ⟨inv_mem hg.1, unip_diag_inv b hg⟩

end UnipGroup

theorem tensor_eq_zero_of_fixed {K : Type} [Field K] [Fintype K] [DecidableEq K] {r s : ℕ} (b : Fin r → Fin s)
    (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)) (c : Fin s)
    (U : Subgroup (GL {i // b i = c} K))
    (hU : ∀ v : (lam c : Type), (∀ u ∈ U, (lam c).ρ u v = v) → v = 0)
    (y : PiTensorProduct ℂ (fun c => (lam c : Type)))
    (hy : ∀ u ∈ U, PiTensorProduct.map (Function.update
      (fun c' => (LinearMap.id : (lam c' : Type) →ₗ[ℂ] (lam c' : Type))) c ((lam c).ρ u)) y = y) :
    y = 0 := by
  classical
  let f : U → ((lam c : Type) →ₗ[ℂ] (lam c : Type)) := fun u => (lam c).ρ u
  have hinv : ∀ (g : U) (v : (lam c : Type)), f g (∑ u : U, f u v) = ∑ u : U, f u v := by
    intro g v
    have hm : ∀ u : U, f g (f u v) = f (g * u) v := fun u => by
      simp only [f, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [hm]
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun u => f u v)
  have hA : (∑ u : U, f u) = 0 := by
    ext v
    rw [LinearMap.sum_apply, LinearMap.zero_apply]
    exact hU _ fun u hu => hinv ⟨u, hu⟩ v
  let F := PiTensorProduct.mapMultilinear ℂ (fun c => (lam c : Type)) (fun c => (lam c : Type))
  let m : ∀ c', (lam c' : Type) →ₗ[ℂ] (lam c' : Type) := fun c' => LinearMap.id
  have h1 : F (Function.update m c (∑ u : U, f u)) y = (Fintype.card U) • y := by
    rw [MultilinearMap.map_update_sum, LinearMap.sum_apply]
    have : ∀ u : U, F (Function.update m c (f u)) y = y := fun u => hy u u.2
    simp_rw [this]
    rw [Finset.sum_const, Finset.card_univ]
  rw [hA, MultilinearMap.map_update_zero, LinearMap.zero_apply] at h1
  have hcard : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_left hcard

theorem cuspidal_tensor_no_unip_fixed : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (r s : ℕ) (b : Fin r → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K)), (∀ c, IsCuspidal K (lam c)) → ∀ S : Finset (Fin r), (∃ i j, natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → ∀ y : PiTensorProduct ℂ (fun c => (lam c : Type)), (∀ u : blockTri (κ := K) (natBlocks b), (∀ i j, ((u : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) i j ≠ (1 : Matrix (Fin r) (Fin r) K) i j → natBlocks b i = natBlocks b j ∧ i ∈ S ∧ j ∉ S) → leviTensor b lam u y = y) → y = 0 := by
  intro K _ _ _ r s b lam hcusp S ⟨i, j, hb, hi, hj⟩ y hy
  have hb' : b i = b j := Fin.ext hb
  let c := b i
  let b₂ : {k // b k = c} → Fin 2 := fun k => if k.1 ∈ S then 0 else 1
  have hsurj : Function.Surjective b₂ := by
    intro t
    fin_cases t
    · exact ⟨⟨i, rfl⟩, by simp [b₂, hi]⟩
    · exact ⟨⟨j, hb'.symm⟩, by simp [b₂, hj]⟩
  refine tensor_eq_zero_of_fixed b lam c (cuspUnipGroup b₂)
    (fun v hv => hcusp c 2 b₂ hsurj le_rfl v hv) y ?_
  intro u' hu'
  have hu : u' ∈ unip K b₂ := hu'
  rw [← leviTensor_blockExt b lam c u']
  apply hy
  intro x z hxz
  by_cases hin : b x = c ∧ b z = c
  · refine ⟨by simp only [natBlocks, hin.1, hin.2], ?_⟩
    have e := blockExt_in b c u' ⟨x, hin.1⟩ ⟨z, hin.2⟩
    dsimp only at e
    rw [e] at hxz
    by_contra hcon
    apply hxz
    by_cases hxS : x ∈ S <;> by_cases hzS : z ∈ S
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
    · exact absurd ⟨hxS, hzS⟩ hcon
    · rw [hu.1.1 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS]),
        Matrix.one_apply_ne (by rintro rfl; exact hxS hzS)]
    · rw [hu.2 ⟨x, hin.1⟩ ⟨z, hin.2⟩ (by simp [b₂, hxS, hzS])]
      simp [Matrix.one_apply, Subtype.ext_iff]
  · exact absurd (blockExt_out b c u' x z hin) hxz

end GlobalTheory.HcIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidalStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerateWhittakerDim_parabolicInduction_cuspidal : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → ∀ j : ℕ, j < r ∨ j = 0 → whCut ψ (parInd b σ) j = splitDoublingNBlock b j * leviWh ψ b σ := by
  first | exact @GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction | exact GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction | (intros; apply GlobalTheory.FinGL.WhCutInd.degenerateWhittakerDim_parabolicInduction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogEqSumLinearCoefficientsFormExplicitStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), constantCoeff u = 1 → (∀ n, c.ev n u = charElem χ n) → dlog G χ = ∑ i, lin u i • c.form i := by
  first | exact @GlobalTheory.QLog.Chart.dlog_eq_sum_lin' | exact GlobalTheory.QLog.Chart.dlog_eq_sum_lin' | (intros; apply GlobalTheory.QLog.Chart.dlog_eq_sum_lin' <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem dvd_of_forall_omega_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (a : O) (b : G.A n),
    (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) →
      (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  intro p O _ G n a b h
  have hall : ∀ φ : CartierDual O (G.A n), a ∣ φ b := fun φ => by
    obtain ⟨w, hw⟩ := G.dual.omegaLevel_surjective n (dUnit (R := O) φ)
    exact h w φ hw.symm
  exact ⟨_root_.GlobalTheory.projective_dvd_of_forall_dual_dvd O (G.A n) a b (fun φ => hall (WithConv.toConv φ)),
    fun w => AugCot.d_surjective _ (w.1 n)⟩

end GlobalTheory.PDivGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EffCartierComapOfIsIsoRestrictOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem effCartier_comap_of_isIso_restrict : ∀ {Y Y' : Scheme.{0}} (s : Y' ⟶ Y) (I : Y.IdealSheafData) (U : Y.Opens), IsIso (s ∣_ U) → FinalTheorems.EffCartier (I.comap s) → FinalTheorems.EffCartier (I.comap U.ι) := by
  intro Y Y' s I U hiso hE
  have h1 : FinalTheorems.EffCartier ((I.comap s).comap (s ⁻¹ᵁ U).ι) :=
    effCartier_comap_of_isOpenImmersion' _ _ hE
  have h2 := effCartier_comap_of_isOpenImmersion' _ (inv (s ∣_ U)) h1
  have key : inv (s ∣_ U) ≫ (s ⁻¹ᵁ U).ι ≫ s = U.ι := by
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, Category.assoc, key] at h2
  exact h2

end GlobalTheory
end

