module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerValuationLowerBoundSumPowTwelve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEntireLatticeSumOfHeckeLContinuation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorMapEigenvalueNormBound
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin.IntBound

variable (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

noncomputable def mu : KQ p Kw r →+* PadicAlgCl p :=
  (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _) :
    Kw ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] PadicAlgCl p).toRingHom

theorem mu_inclK (a : Kw) : mu p Kw r (inclK p Kw r a) = (a : PadicAlgCl p) := by
  change (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

theorem mu_inclQ (b : Qr p r) : mu p Kw r (inclQ p Kw r b) = (b : PadicAlgCl p) := by
  change (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) ((1 : Kw) ⊗ₜ[ℚ_[p]] b) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

theorem intKQ_le : intKQ p Kw r ≤ (ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p).toSubring.comap (mu p Kw r) := by
  rw [intKQ, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · change mu p Kw r (inclK p Kw r a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [mu_inclK]
    exact a.2
  · change mu p Kw r (inclQ p Kw r b) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [mu_inclQ]
    exact b.2

theorem norm_mu_le_one (x : KQ p Kw r) (hx : x ∈ intKQ p Kw r) : ‖mu p Kw r x‖ ≤ 1 :=
  ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 (intKQ_le p Kw r hx)

end GlobalTheory.StabFin.IntBound

namespace GlobalTheory.StabFin

theorem norm_eigen_le_one_of_conj_Kres : ∀ (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r : ℕ) (N : Matrix (Fin n) (Fin n) Kw) (H k : GL (Fin n) (KQ p Kw r)), k ∈ Kres p Kw n r →
    N.map (inclK p Kw r) = ((H * k * H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r)) →
    ∀ (v : Fin n → PadicAlgCl p) (c : PadicAlgCl p), v ≠ 0 →
      N.map (fun x => (x : PadicAlgCl p)) *ᵥ v = c • v → ‖c‖ ≤ 1 := by
  intro p _ Kw n r N H k hk hN v c hv hev
  set μ := IntBound.mu p Kw r
  set A := μ.mapMatrix (H : Matrix (Fin n) (Fin n) (KQ p Kw r))
  set Ai := μ.mapMatrix ((H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r))
  set B := μ.mapMatrix (k : Matrix (Fin n) (Fin n) (KQ p Kw r))
  have hAAi : A * Ai = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hAiA : Ai * A = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hM : N.map (fun x => (x : PadicAlgCl p)) = A * B * Ai := by
    have h1 : N.map (fun x => (x : PadicAlgCl p)) = μ.mapMatrix (N.map (inclK p Kw r)) := by
      ext i j
      simp [μ, IntBound.mu_inclK]
    rw [h1, hN, Units.val_mul, Units.val_mul, map_mul, map_mul]
  set v' := Ai *ᵥ v
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    have : A *ᵥ v' = v := by rw [mulVec_mulVec, hAAi, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hBv : B *ᵥ v' = c • v' := by
    have e1 : Ai *ᵥ (N.map (fun x => (x : PadicAlgCl p)) *ᵥ v) = c • v' := by
      rw [hev, mulVec_smul]
    rw [hM, mulVec_mulVec, ← mul_assoc, ← mul_assoc, hAiA, one_mul, ← mulVec_mulVec] at e1
    exact e1
  have hB : ∀ i j, ‖B i j‖ ≤ 1 := by
    obtain ⟨k0, rfl⟩ := hk
    intro i j
    simp only [B, RingHom.mapMatrix_apply, Matrix.map_apply, GeneralLinearGroup.map_apply]
    exact IntBound.norm_mu_le_one p Kw r _ (k0 i j).2
  haveI : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv' (Subsingleton.elim _ _)
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l => ‖v' l‖)
  have hpos : 0 < ‖v' j‖ := by
    rcases (norm_nonneg (v' j)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hv'
      funext l
      have := hj l
      rw [← h] at this
      exact norm_le_zero_iff.1 this
  have key : ‖c‖ * ‖v' j‖ ≤ 1 * ‖v' j‖ := by
    have e : c * v' j = ∑ l, B j l * v' l := by
      have := congrFun hBv j
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      rfl
    rw [← norm_mul, e, one_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
    rw [norm_mul]
    calc ‖B j l‖ * ‖v' l‖ ≤ 1 * ‖v' j‖ :=
          mul_le_mul (hB j l) (hj l) (norm_nonneg _) zero_le_one
      _ = ‖v' j‖ := one_mul _
  exact le_of_mul_le_mul_right key hpos

end GlobalTheory.StabFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar.SizeBounds

theorem one_le_rdE (D : D7) : (1 : ℝ) ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h
  · positivity

theorem one_le_b (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) : 1 ≤ b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    show 0 < 2 * D.R.ord
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    omega
  obtain ⟨-, -, -, hb⟩ := h.1 τ
  have hq := (D.hc τ).gap_be i
  have hr : ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((D.hc τ).e i - (D.hc τ).b i : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hr
  have habs := abs_le.mp (hb i)
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith [habs.1, habs.2]

theorem lam_bounds (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (τ : D.what₂.Tau) (n : ℕ) :
    -b ≤ ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ∧
      ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ≤ 3 * b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨he0, he2, hv, hb⟩ := h.1 τ
  have hb0 : (0 : ℝ) ≤ b := by linarith
  unfold Formalism.L2.NTheta.lamAt
  split_ifs with h1 h2
  · obtain ⟨hv0, hv1⟩ := hv ⟨n, h1⟩
    constructor <;> linarith
  · have habs := abs_le.mp (hb ⟨n - (D.R.k - 1), h2⟩)
    push_cast
    constructor <;> linarith [habs.1, habs.2]
  · push_cast
    constructor <;> linarith

theorem toNat_floor_le (x : ℚ) (c : ℝ) (hc : 0 ≤ c) (hx : (x : ℝ) ≤ c) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ c := by
  rcases le_or_gt ⌊x⌋ 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]
    simpa using hc
  · have h1 : ((⌊x⌋.toNat : ℕ) : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg h0.le
    have h2 : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2]
    have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast Int.floor_le x
    linarith

theorem aPl_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aPl D i p τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ n).2
  have hb1 := one_le_b D i b h
  unfold aPl
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hnp : (n : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem aMi_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p q : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aMi D i p q τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ (p + (q - n) - 1)).1
  have hb1 := one_le_b D i b h
  unfold aMi
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hqn : (0 : ℝ) ≤ ((q - n : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem degAt_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  have hb1 := one_le_b D i b h
  have hi := i.isLt
  have hs := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D ρ)
  have hP : ∀ n, ((aPlAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aPl_le D i b h _ _ n
  have hM : ∀ n, ((aMiAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aMi_le D i b h _ _ _ n
  have h1 := Finset.sum_le_sum (s := Finset.range (pW D i ρ)) (fun n _ => hP n)
  have h2 := Finset.sum_le_sum (s := Finset.range (qW D i ρ)) (fun n _ => hM n)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  have hr : (pW D i ρ : ℝ) + (qW D i ρ : ℝ) = (D.R.r : ℝ) := by
    have hn : pW D i ρ + qW D i ρ = D.R.r := by
      simp only [pW, qW, Wc, hs]
      unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r
      dsimp only
      omega
    exact_mod_cast hn
  unfold degAt
  push_cast
  calc _ ≤ (pW D i ρ : ℝ) * (3 * b) + (qW D i ρ : ℝ) * (3 * b) := add_le_add h1 h2
    _ = 3 * (D.R.r : ℝ) * b := by rw [← hr]; ring

theorem sizes : ∀ (D : D7) (i : Fin D.R.m) (b : ℝ), Sizes D i b → (5.5 : ℝ) ≤ Lp D b ∧ Real.log (D.R.nV : ℝ) ≤ Lp D b ∧ 0 ≤ b ∧ Real.log (3 * (D.R.r : ℝ) * b + 2) ≤ 2 * Lp D b ∧ ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  intro D i b h
  have hb1 := one_le_b D i b h
  have hrd := one_le_rdE D
  have hnV : (1 : ℝ) ≤ (D.R.nV : ℝ) := by
    have h1 := D.R.t_odd.pos
    have h2 : 1 ≤ D.R.nV := by
      unfold Formalism.BasicNotions.Ranks.nV
      omega
    exact_mod_cast h2
  have hk5 : 5 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    omega
  have hrk : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hr2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast hrk
  have hgl := h.2
  have hg0 := hgl 0
  have hg1 := hgl 1
  set y : ℝ := (D.R.k : ℝ) * b with hy
  have hy5 : 5 ≤ y := by nlinarith
  have hy8 : y ^ 3 ≤ y ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hyy : 25 ≤ y * y := by nlinarith
  have hy3 : 25 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hyy (by linarith : (0 : ℝ) ≤ y)]
  have hyP : (390625 : ℝ) ≤ y ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hy5 8
    norm_num at this
    linarith
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by linarith
  have hg0' : (0 : ℝ) ≤ (D.host.g 0 : ℝ) := Nat.cast_nonneg _
  have hbr : (1 : ℝ) ≤ b * D.host.rdE := one_le_mul_of_one_le_of_one_le hb1 hrd
  have hG : (D.host.g 0 : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := le_mul_of_one_le_right hg0' hg1'
  have hA : (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hbr
  have hB : b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤
      b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_right (by positivity) hnV
  have hC : (1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by linarith
  have hD : (D.R.nV : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_left (by positivity) hC
  have hX : y ^ 8 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have hL : Lp D b = Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ)) := rfl
  have hXpos : 0 < b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have he6 : Real.exp (5.5 : ℝ) ≤ 729 := by
    have h1 : Real.exp (5.5 : ℝ) ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 6 ≤ (3 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 6
    norm_num at h3
    linarith
  have h55 : (5.5 : ℝ) ≤ Lp D b := by
    rw [hL]
    calc (5.5 : ℝ) = Real.log (Real.exp 5.5) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  refine ⟨h55, ?_, by linarith, ?_, fun σ ρ => degAt_le D i b h σ ρ⟩
  · rw [hL]
    exact Real.log_le_log (by linarith) hD
  · have hb0 : (0 : ℝ) ≤ b := by linarith
    have hrb : (D.R.r : ℝ) * b ≤ (2 * (D.R.k : ℝ)) * b := mul_le_mul_of_nonneg_right hr2 hb0
    have h32 : 3 * (D.R.r : ℝ) * b + 2 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by
      nlinarith
    have hpos : 0 < 3 * (D.R.r : ℝ) * b + 2 := by positivity
    have hlog := Real.log_le_log hpos h32
    rw [← hL] at hlog
    linarith

end GlobalTheory.AdelicScalar.SizeBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricDenominatorOfZetaDenominators
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds

namespace GlobalTheory.ToricDenomRow

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem beta_eq_pow (d s : ℕ) (κ : I → ℕ) (Λ : PeriodPair) {Ω : ℂ} (hΩ : Ω ^ 12 = latDisc Λ) (T : ℂ) :
    beta E d s κ Λ T = ((C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ) ^ 12 := by
  rw [beta, div_pow, ← pow_mul, mul_comm _ 12, pow_mul, hΩ]

theorem classTerm_rep [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)}
    (hc : c ≠ ⊥) {χ : HChar E} (hinf : HasInf χ φ (fun i => (κ i : ℤ) + s)) (htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1)
    {l : ℕ} (hl : l.Prime) (hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S)
    (y : (Af E)ˣ) (S : ℂ → ℂ) (hS : IsLatSum φ (2 * s) κ (lattice c y) S) :
    ∃ y' : (Af E)ˣ, OneOver l y' ∧ ∃ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' ∧ ∃ u : ℂ, IntAt l u ∧
      ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0 = u * S' 0 := by
  obtain ⟨y', hy', hone⟩ := GlobalTheory.CMVal.TrivAbove.exists_rep_trivial_above E c l hc hl (QuotientGroup.mk y)
  obtain ⟨S', hS'⟩ := hex y'
  refine ⟨y', hone, S', hS', ((finPart χ y' : ℂ) * ((modF y' ^ s : ℝ) : ℂ))⁻¹, ?_, ?_⟩
  · have hu := GlobalTheory.CMVal.value_unitAt E I φ hφ s κ c χ l hc hl hinf htriv y' fun w hw => by
      rw [hone w hw, map_one]
    exact (GlobalTheory.CMVal.LUnit.unitAt_inv hu).2.1
  · exact GlobalTheory.ClassInvAny.classInv_of_unit_trivial E I φ hφ s κ c χ hinf htriv y y' S S' hy'.symm hS hS'

theorem toricDenominator (hZ : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hR : LatIntRam) (hU : LatIntUnr) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator := by
  intro E _ _ _ _ I _ d φ s hd hs
  obtain ⟨z, hz⟩ := (hZ E s hs).1
  have hzc : IsClassZetaVals (2 * s) z := hz
  refine ⟨z, hzc, fun κ 𝔣 Λ χ hb hΛ hχ => ?_⟩
  have hUr : UnramFin E := hd.2.2.1
  have hφ : IsCMType φ := hd.2.2.2.2.2.2.1
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc Λ) (by norm_num : 0 < 12)
  intro l hl Q hQ hQl
  set c := condQ 𝔣 Q with hcdef
  have hc : c ≠ ⊥ := mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  have h0 := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hUr hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have htriv : ∀ u ∈ hatOUnits c, finPart χ u = 1 := fun u hu => h0 u (hatOUnits_mono hle hu)
  have hex : ∀ y : (Af E)ˣ, ∃ S, IsLatSum φ (2 * s) κ (lattice c y) S := fun y =>
    GlobalTheory.CMVal.LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 c χ hUr hs hb
      (dvd_mul_right _ _) hc hχ.1 hχ.2.2.1 htriv y
  set x : ℂ → ℂ := fun T => (C0 E d (2 * s) κ : ℂ) * T / Ω ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ with hxdef
  have hx : ∀ T, beta E d s κ Λ T = x T ^ 12 := fun T => beta_eq_pow d s κ Λ hΩ T
  have hxmul : ∀ u T, x (u * T) = u * x T := fun u T => by simp only [hxdef]; ring

  have hlat : ∀ y' : (Af E)ˣ, OneOver l y' → ∀ S' : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y') S' →
      ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (x (S' 0) ^ 12) := fun y' hy' S' hS' => by
    rw [← hx]
    by_cases h : c_vp 𝔣 l = 0
    · exact hU E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'
    · exact hR E I d φ s hd hs z hzc 𝔣 Λ hb hΛ l hl Q hQ hQl y' hy' h κ S' hS'

  have hterm : ∀ χ' : HChar E, HasInf χ' φ (fun i => (κ i : ℤ) + s) → (∀ u ∈ hatOUnits c, finPart χ' u = 1) →
      ∀ (y : (Af E)ˣ) (S : ℂ → ℂ), IsLatSum φ (2 * s) κ (lattice c y) S →
      ∃ u w : ℂ, IntAt l u ∧ ValGe_vp l (betaBound_vp d s κ 𝔣 z l) (w ^ 12) ∧
        x (((finPart χ' y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0) = u * w := by
    intro χ' hinf' htriv' y S hS
    obtain ⟨y', hy', S', hS', u, hu, e⟩ := classTerm_rep hφ hc hinf' htriv' hl hex y S hS
    exact ⟨u, x (S' 0), hu, hlat y' hy' S' hS', by rw [e, hxmul]⟩
  refine ⟨fun y T ⟨S, hS, hT⟩ => ?_, fun ψ T hψ ⟨hfin, S, hS, hT⟩ => ?_⟩
  · obtain ⟨u, w, hu, hw, e⟩ := hterm χ hχ.2.2.1 htriv y S hS
    have := _root_.GlobalTheory.LatValSum.valGe_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) Unit (fun _ => u) (fun _ => w) (fun _ => hu) (fun _ => hw)
    rw [hx, hT, e]
    simpa using this
  · have hinf' : HasInf (χ * ψ) φ (fun i => (κ i : ℤ) + s) := hχ.2.2.1.mul_triv hψ.1
    have htriv' : ∀ u ∈ hatOUnits c, finPart (χ * ψ) u = 1 := fun u hu => by
      show finPart χ u * finPart ψ u = 1
      rw [htriv u hu, hψ.2 u hu, one_mul]
    have := Fintype.ofFinite (PicO c)
    choose u w hu hw e using fun q : PicO c => hterm (χ * ψ) hinf' htriv' q.out (S q) (hS q)
    have key := _root_.GlobalTheory.LatValSum.valGe_sum_pow_twelve l hl (betaBound_vp d s κ 𝔣 z l) (PicO c) u w hu hw
    rw [hx, hT, finsum_eq_sum_of_fintype]
    have : x (∑ q, ((finPart (χ * ψ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ * S q 0) = ∑ q, u q * w q := by
      rw [← Finset.sum_congr rfl fun q _ => e q]
      simp only [hxdef, Finset.mul_sum, Finset.sum_div]
    rw [this]
    exact key

end GlobalTheory.ToricDenomRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricRatioConjugatesOfTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf ToricRatioConjugates)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem exists_toricSum_ne_zero [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ) :
    ∃ T₀ : ℂ, IsToricSum φ s κ (condQ 𝔣 ∅) χ T₀ ∧ T₀ ≠ 0 := by
  obtain ⟨i₀, -⟩ := hφ (Classical.arbitrary _)
  obtain ⟨Λ, hΛ⟩ := GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ _ χ hφ hχ.1 hχ.2.2.1 ⟨i₀, by omega⟩
  obtain ⟨P₀⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩⟩
  have t1 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 ∅ χ (fun _ => P₀) Λ hU hs hb
    (fun _ h => absurd h (Finset.notMem_empty _)) hχ (fun _ h => absurd h (Finset.notMem_empty _)) hΛ
  rw [Finset.filter_empty, Finset.prod_empty, mul_one] at t1
  exact ⟨Λ s, t1, hΛ.ne_zero_nat hχ.1 hs⟩

theorem condQ_ne_bot {𝔣 : Ideal (OF E)} (hb : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ :=
  mul_ne_zero hb.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem exists_twistedSum [IsCMField E] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)} {χ : HChar E}
    (hU : UnramFin E) (hφ : IsCMType φ) (hs : 1 ≤ s) (hb : IsBaseCond 𝔣) (hχ : IsValChar φ s κ 𝔣 ∅ χ)
    (Q : Finset (HeightOneSpectrum (OF E))) (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) : ∃ T, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T := by
  have h0 := OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 ∅ χ hU hb (fun _ h => absurd h (Finset.notMem_empty _)) hχ
  have hle : condQ 𝔣 Q ≤ condQ 𝔣 ∅ := by
    rw [show condQ 𝔣 ∅ = 𝔣 by simp [condQ]]
    exact Ideal.dvd_iff_le.1 (dvd_mul_right 𝔣 _)
  choose S hS using fun q : PicO (condQ 𝔣 Q) =>
    LatEnt.exists_isLatSum GlobalTheory.ToricDistribution.exists_isHeckeL_of_hasInf E I φ hφ s κ 𝔣 _ χ hU hs hb (dvd_mul_right _ _)
      (condQ_ne_bot hb Q) hχ.1 hχ.2.2.1 (fun y hy => h0 y (hatOUnits_mono hle hy)) q.out
  exact ⟨_, PicFin.finite_picO E _ (condQ_ne_bot hb Q), S, hS, rfl⟩

theorem isTwistedSum_one {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} (T : ℂ) :
    IsTwistedSum φ s κ c χ 1 T ↔ IsToricSum φ s κ c χ T := by
  simp [IsTwistedSum, IsToricSum, GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.lamF]

theorem conjChar_one {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) : conjChar g (1 : PicO c →* ℂˣ) = 1 :=
  MonoidHom.ext fun _ => Units.ext (map_one g)

theorem toricRatioConjugates_of_transport (hT : TwistedTransport) : ToricRatioConjugates := by
  intro E _ _ _ K _ _ _ d δ ι I _ φ s κ 𝔣 Q χ hU hK hd hδ hφ hι hs hκ hb hQ hχ
  obtain ⟨Ω₀, hΩ₀, halg, hconj⟩ := hT K d δ ι hK hd hδ
  obtain ⟨T₀, hT₀, h0⟩ := exists_toricSum_ne_zero hU hφ hs hb hχ
  choose T hTw using exists_twistedSum hU hφ hs hb hχ Q
  have hD : IsDatum ι φ s κ 𝔣 Q χ := ⟨hU, hφ, hι, hs, hκ, hb, hQ, hχ⟩
  have hD₀ : IsDatum ι φ s κ 𝔣 ∅ χ := ⟨hU, hφ, hι, hs, hκ, hb, fun _ h => absurd h (Finset.notMem_empty _), hχ⟩
  have hT₀' := (isTwistedSum_one T₀).2 hT₀
  have e : condQ 𝔣 ∅ = 𝔣 := by simp [condQ]
  refine ⟨T₀, T, e ▸ hT₀, h0, hTw, fun ψ => ?_, fun Ω _ _ _ j art hj ha g σ t hgE hgl hσ ht ψ => ⟨?_, ?_⟩⟩
  · rw [← coordIn_div E hd hs κ hΩ₀, div_eq_mul_inv]
    exact (halg E I φ s κ 𝔣 Q χ hD ψ _ (hTw ψ)).mul (halg E I φ s κ 𝔣 ∅ χ hD₀ 1 _ hT₀').inv
  · obtain ⟨Ω₁, hΩ₁, h⟩ := hconj Ω j art hj ha g σ t hσ ht
    have hw : IsConjWt φ g κ κ := fun i i' hi => by
      have : φ i = φ i' := RingHom.ext fun x => (hgE i x).symm.trans (hi x)
      rw [(hφ (φ i)).unique (Or.inl rfl) (Or.inl this)]
    have hc : IsConjChar φ s κ g χ χ := ⟨fun y => (hgl y).symm, hχ.2.2.1⟩
    have h1 := h E I φ s κ 𝔣 Q χ hD κ χ hw hc ψ _ _ (hTw ψ) (hTw _)
    have h2 := h E I φ s κ 𝔣 ∅ χ hD₀ κ χ hw hc 1 T₀ T₀ hT₀' (by rw [conjChar_one]; exact hT₀')
    have hl := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero s χ (upIdele K E t)
    have hm : ((modF t : ℝ) : ℂ) ≠ 0 := by
      have := GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.lamF_ne_zero 1 (1 : HChar K) t
      rw [lamF, pow_one] at this
      exact right_ne_zero_of_mul this
    rw [← coordIn_div E hd hs κ hΩ₀, map_div₀, h1, h2, coordIn_div E hd hs κ hΩ₁, conjChar_one]
    simp only [MonoidHom.one_apply, Units.val_one, mul_one]
    have := (conjChar g ψ (classOf K (condQ 𝔣 Q) t)).ne_zero
    field_simp
  · have := PicFin.finite_picO E _ (condQ_ne_bot hb Q)
    exact (conjChar g ψ).isOfFinOrder (isOfFinOrder_of_finite _)

end GlobalTheory.ToricTransport
end
end

