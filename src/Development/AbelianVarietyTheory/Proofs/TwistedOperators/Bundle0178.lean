module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockCreaDir

section Mat

variable {m n : ℕ}

theorem eq_sum_unitMap {Bm : Matrix (Fin m) (Fin m) ℂ} {Am : Matrix (Fin n) (Fin n) ℂ} (hB : IsUnit Bm.det)
    (hA : IsUnit Am.det) (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, (Bm⁻¹ * z * Am) i j • Formalism.IndefR.Datum.unitMap Am Bm i j := by
  have e : z = Bm * (Bm⁻¹ * z * Am) * Am⁻¹ := by
    rw [← Matrix.mul_assoc Bm, ← Matrix.mul_assoc Bm, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hA]
  have e2 := Matrix.matrix_eq_sum_single (Bm⁻¹ * z * Am)
  calc z = Bm * (∑ i, ∑ j, Matrix.single i j ((Bm⁻¹ * z * Am) i j)) * Am⁻¹ := by rw [← e2, ← e]
    _ = _ := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h : Matrix.single i j ((Bm⁻¹ * z * Am) i j) = ((Bm⁻¹ * z * Am) i j) • Matrix.single i j (1 : ℂ) := by
        rw [Matrix.smul_single, smul_eq_mul, mul_one]
      rw [h, Matrix.mul_smul, Matrix.smul_mul, Formalism.IndefR.Datum.unitMap]

theorem Jm_single_Jm (ε : Fin m → Bool) (δ : Fin n → Bool) (i : Fin m) (j : Fin n) :
    Formalism.REAL.Jm ε * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm δ =
      (if (ε i == δ j) then 1 else -1 : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext p q
  rw [Formalism.REAL.Jm, Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply,
    smul_eq_mul]
  by_cases h : i = p ∧ j = q
  · obtain ⟨rfl, rfl⟩ := h
    cases ε i <;> cases δ j <;> simp
  · simp [h]

end Mat

open GlobalTheory.ChainFr

variable {D : D7} {V W : HSp D}

theorem cplxO_unitMap_fr (A : Fr V) (B : Fr W) (τ : D.what₂.Tau) (i : Fin W.rank) (j : Fin V.rank) :
    cplxO (A.cart τ) (B.cart τ) (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) =
      ((if (B.ε τ i == A.ε τ j) then 1 else -1 : ℂ) * Complex.I) •
        Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := by
  have hA := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  have hB := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
  have h1 : B.cart τ * B.onb τ = B.onb τ * Formalism.REAL.Jm (B.ε τ) := by
    rw [Fr.cart, Fr.onb, Matrix.mul_nonsing_inv_cancel_right _ _ hB]
  have h2 : (A.onb τ)⁻¹ * A.cart τ = Formalism.REAL.Jm (A.ε τ) * (A.onb τ)⁻¹ := by
    rw [Fr.cart, Fr.onb, Matrix.nonsing_inv_nonsing_inv _ hA]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hA]
  unfold cplxO Formalism.IndefR.Datum.unitMap
  rw [mul_comm _ Complex.I, ← smul_smul]
  congr 1
  calc B.cart τ * (B.onb τ * Matrix.single i j (1 : ℂ) * (A.onb τ)⁻¹) * A.cart τ
      = (B.cart τ * B.onb τ) * Matrix.single i j (1 : ℂ) * ((A.onb τ)⁻¹ * A.cart τ) := by
        simp only [Matrix.mul_assoc]
    _ = B.onb τ * (Formalism.REAL.Jm (B.ε τ) * Matrix.single i j (1 : ℂ) * Formalism.REAL.Jm (A.ε τ)) * (A.onb τ)⁻¹ := by
        rw [h1, h2]
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [Jm_single_Jm, Matrix.mul_smul, Matrix.smul_mul]

theorem fockScale_ne_zero (D : D7) (τ : D.what₂.Tau) : ((fockScale D τ : ℝ) : ℂ) ≠ 0 := by
  have h0 : 0 < ‖tauE D τ D.host.xi0‖ := by
    refine norm_pos_iff.2 fun h => ?_
    have := Formalism.L2.Theta.xi_zero_im_pos D τ
    rw [h] at this
    simp at this
  have : 0 < fockScale D τ := by
    unfold fockScale
    have := Real.sqrt_pos.2 (mul_pos (mul_pos two_pos Real.pi_pos) h0)
    positivity
  exact_mod_cast this.ne'

end GlobalTheory.FockCreaDir


open GlobalTheory.FockCreaDir in
theorem GlobalTheory.FockCreaDir.crea_ptF : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (P : PolF D W.rank V.rank), ∃ Q : PolF D W.rank V.rank, crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f Q := by
  intro D V W A B θ ψ hψ hθ f hf τ z P
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf P
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨c, rfl⟩ : ∃ c : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, c i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  refine ⟨((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
    (MvPolynomial.X (τ, i, j) * P), ?_⟩
  have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
      crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
        ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g := fun y g => by
    rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
  rw [h1]
  have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) • (MvPolynomial.X (τ, i, j) * P)) =
      ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then c i j else starRingEnd ℂ (c i j)) •
        Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
          (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
    unfold GlobalTheory.ChainFr.ptF pureTensorO
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_smul, map_sum, hX]
    rfl
  rw [h2]
  congr 1
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorMaximalCompactMovedBases
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockSubBoth

open GlobalTheory.FockSubst GlobalTheory.FockCompare GlobalTheory.OrientedHeis Complex

theorem unitMap_mul_both {m n : ℕ} (B k : Matrix (Fin n) (Fin n) ℂ) (B' k' : Matrix (Fin m) (Fin m) ℂ) (a : Fin m)
    (c : Fin n) : unitMap (B * k) (B' * k') a c =
      ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • unitMap B B' b.1 b.2 := by
  unfold unitMap
  rw [Matrix.mul_inv_rev]
  have key : k' * single a c (1 : ℂ) * k⁻¹ = ∑ b : Fin m × Fin n, (k' b.1 a * k⁻¹ c b.2) • single b.1 b.2 (1 : ℂ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.single_apply, Matrix.sum_apply, Fintype.sum_prod_type, ite_and, Finset.sum_ite_eq,
      Finset.sum_ite_eq', ite_mul, zero_mul]
  calc B' * k' * single a c (1 : ℂ) * (k⁻¹ * B⁻¹) = B' * (k' * single a c (1 : ℂ) * k⁻¹) * B⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [key, Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]

theorem onb_sign {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsUnit B.det ∧ s * B = B * Matrix.diagonal (fun a : Fin k => if a.val < p then (1 : ℂ) else -1) := by
  obtain ⟨ε, hε, hG, hs⟩ := h
  have hdiag : (diagonal fun a => ((ε a : _) : ℂ)) = diagonal fun a : Fin k => if a.val < p then (1 : ℂ) else -1 := by
    congr 1
    funext a
    rcases hε a with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [h1, h2]
    · simp [h1, not_lt.mpr h2]
  refine ⟨?_, hs.trans (by rw [hdiag])⟩
  rw [isUnit_iff_ne_zero]
  intro h0
  have hd := congrArg Matrix.det hG
  rw [Matrix.det_mul, h0, mul_zero, hdiag, Matrix.det_diagonal] at hd
  have : ∀ a ∈ (Finset.univ : Finset (Fin k)), (if a.val < p then (1 : ℂ) else -1) ≠ 0 := by
    intro a _
    split_ifs <;> norm_num
  exact (Finset.prod_ne_zero_iff.mpr this) hd.symm

theorem cplxO_unitMap_both {m n : ℕ} {G s B : Matrix (Fin n) (Fin n) ℂ} {p : ℕ} (h : IsONBasis G s B p)
    {G' s' B' : Matrix (Fin m) (Fin m) ℂ} {p' : ℕ} (h' : IsONBasis G' s' B' p') (i : Fin m) (j : Fin n) :
    cplxO s s' (unitMap B B' i j) =
      ((if decide (i.val < p' ↔ j.val < p) then 1 else -1 : ℂ) * I) • unitMap B B' i j := by
  obtain ⟨hB, hs⟩ := onb_sign h
  obtain ⟨-, hs'⟩ := onb_sign h'
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have hBB : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have hBi : B⁻¹ * s = diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * s * (B * B⁻¹) := by rw [hBB, Matrix.mul_one]
      _ = B⁻¹ * (s * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * (B * diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by rw [hs]
      _ = _ := by rw [← Matrix.mul_assoc B⁻¹, hinv, Matrix.one_mul]
  have e1 : s' * (B' * single i j (1 : ℂ) * B⁻¹) * s =
      B' * (diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
        diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1)) * B⁻¹ := by
    calc s' * (B' * single i j (1 : ℂ) * B⁻¹) * s = (s' * B') * single i j (1 : ℂ) * (B⁻¹ * s) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hs', hBi]; simp only [Matrix.mul_assoc]
  have e2 : diagonal (fun a : Fin m => if a.val < p' then (1 : ℂ) else -1) * single i j (1 : ℂ) *
      diagonal (fun a : Fin n => if a.val < p then (1 : ℂ) else -1) =
      ((if i.val < p' then (1 : ℂ) else -1) * (if j.val < p then (1 : ℂ) else -1)) • single i j (1 : ℂ) := by
    ext x y
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    by_cases hxy : i = x ∧ j = y
    · rw [if_pos hxy]
      obtain ⟨rfl, rfl⟩ := hxy
      ring
    · rw [if_neg hxy]
      ring
  unfold cplxO unitMap
  rw [e1, e2, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 1
  by_cases hi : i.val < p' <;> by_cases hj : j.val < p <;> simp [hi, hj]

theorem isKMat_inv_zero {k p : ℕ} {κ : Matrix (Fin k) (Fin k) ℂ} (h : IsKMat p κ) {i j : Fin k}
    (hij : ¬ (i.val < p ↔ j.val < p)) : κ⁻¹ i j = 0 := by
  obtain ⟨hu, hz⟩ := h
  have hinv : κ⁻¹ = star κ := Matrix.inv_eq_right_inv (Matrix.mem_unitaryGroup_iff.mp hu)
  rw [hinv, Matrix.star_apply, hz j i (fun h' => hij h'.symm), star_zero]

theorem pureTensorO_fockSub : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ S.rank) → (∀ ρ, pT ρ ≤ T.rank) → (∀ ρ, IsCartanInv (gramAt D S ρ) (sS ρ)) → (∀ ρ, IsCartanInv (gramAt D T ρ) (sT ρ)) → (∀ ρ, IsONBasis (gramAt D S ρ) (sS ρ) (BS ρ) (pS ρ)) → (∀ ρ, IsONBasis (gramAt D T ρ) (sT ρ) (BT ρ) (pT ρ)) → ∀ f, IsThetaFunO ψ S T f → ∀ (τ : D.what₂.Tau) κS κT, IsKMat (pS τ) κS → IsKMat (pT τ) κT → ∀ (BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), BS' τ = BS τ * κS → BT' τ = BT τ * κT → (∀ ρ, ρ ≠ τ → BS' ρ = BS ρ ∧ BT' ρ = BT ρ) → ∀ P, pureTensorO ψ θ S T sS sT BS' BT' f P = pureTensorO ψ θ S T sS sT BS BT f (fockSub τ (pS τ) (pT τ) κS κT P) := by
  intro D ψ θ S T hψ hθ sS BS sT BT pS pT hpS hpT hcS hcT hoS hoT f hf τ κS κT hkS hkT BS' BT' hS hT hne P
  classical
  obtain ⟨-, hkTz⟩ := hkT
  have hτ : ∀ (i : Fin T.rank) (j : Fin S.rank) (g : WO S T → ℂ), IsThetaFunO ψ S T g →
      aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS' τ) (BT' τ) i j) g =
      ∑ b : Fin T.rank × Fin S.rank, (if (i.val < pT τ ↔ j.val < pS τ) then κT b.1 i * κS⁻¹ j b.2
          else starRingEnd ℂ (κT b.1 i * κS⁻¹ j b.2)) •
        aPlus (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (unitMap (BS τ) (BT τ) b.1 b.2) g := by
    intro i j g hg
    rw [hS, hT, unitMap_mul_both, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ (sS τ) (sT τ) hg]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ (sS τ) (sT τ) hg (decide (b.1.val < pT τ ↔ b.2.val < pS τ)) _
      (cplxO_unitMap_both (hoS τ) (hoT τ) b.1 b.2)]
    congr 1
    by_cases hw : κT b.1 i * κS⁻¹ j b.2 = 0
    · rw [hw]
      simp
    · have h1 : (b.1.val < pT τ ↔ i.val < pT τ) := by
        by_contra hc
        exact hw (by rw [hkTz b.1 i hc, zero_mul])
      have h2 : (j.val < pS τ ↔ b.2.val < pS τ) := by
        by_contra hc
        exact hw (by rw [isKMat_inv_zero hkS hc, mul_zero])
      by_cases hc : (i.val < pT τ ↔ j.val < pS τ)
      · have hd : decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_pos hd, if_pos hc]
      · have hd : ¬ decide (b.1.val < pT τ ↔ b.2.val < pS τ) = true := by
          rw [decide_eq_true_iff, h1, ← h2]
          exact hc
        rw [if_neg hd, if_neg hc]
  have key := GlobalTheory.FockSubst.pure_subst (ι := FVar D T.rank S.rank) (X := WO S T) (κ := Fin T.rank × Fin S.rank)
    (A := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (A' := fun k => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS' k.1) (BT' k.1) k.2.1 k.2.2))
    (P := IsThetaFunO ψ S T)
    (fun g g' hg hg' => GlobalTheory.OrientedHeis.theta_add hg hg')
    (fun a g hg => GlobalTheory.OrientedHeis.theta_smul a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun k g hg => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ hg)
    (fun k l g hg => GlobalTheory.FockSubst.aPlus_comm hψ hθ _ _ hcS hcT _ _ hg)
    (fun k g g' hg hg' => GlobalTheory.FockSubst.aPlus_add hψ hθ _ _ _ hg hg')
    (fun k a g hg => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a hg)
    (fun v b => if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0))
    (fun v b => (v.1, b.1, b.2))
    (by
      rintro ⟨ρ, i, j⟩ g hg
      dsimp only
      by_cases hρ : ρ = τ
      · subst hρ
        simp only [if_true]
        exact hτ i j g hg
      · obtain ⟨h1, h2⟩ := hne ρ hρ
        simp [hρ, h1, h2, ite_smul])
    hf P
  have hsub : (MvPolynomial.aeval fun v : FVar D T.rank S.rank => ∑ b : Fin T.rank × Fin S.rank,
      (if v.1 = τ then
        (if (v.2.1.val < pT τ ↔ v.2.2.val < pS τ) then κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2
          else starRingEnd ℂ (κT b.1 v.2.1 * κS⁻¹ v.2.2 b.2))
        else (if b = (v.2.1, v.2.2) then 1 else 0)) •
        (MvPolynomial.X (v.1, b.1, b.2) : MvPolynomial (FVar D T.rank S.rank) ℂ)) P =
      fockSub τ (pS τ) (pT τ) κS κT P := by
    unfold fockSub
    congr 2
    funext y
    obtain ⟨ρ, i, j⟩ := y
    by_cases hρ : ρ = τ
    · subst hρ
      simp only [if_true, Fintype.sum_prod_type, MvPolynomial.smul_eq_C_mul]
    · simp [hρ, ite_smul]
  unfold pureTensorO aPlusAll
  beta_reduce
  rw [key, hsub]

end GlobalTheory.FockSubBoth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockSourceGlActionEqQuadraticAddNonRaising
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.FockSrcDec

open GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators

theorem deg_X_pderiv {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.X a * MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum, Finset.mul_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [MvPolynomial.pderiv_monomial]
  by_cases h : s b = 0
  · simp [h]
  · refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
    rw [MvPolynomial.X, MvPolynomial.monomial_mul]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans (le_of_eq ?_)
    have h1 : s = Finsupp.single b 1 + (s - Finsupp.single b 1) := by
      rw [add_tsub_cancel_of_le]
      exact Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 h)
    conv_rhs => rw [h1]
    rw [Finsupp.sum_add_index' (by simp) (by simp), Finsupp.sum_add_index' (by simp) (by simp)]
    simp [Function.id_def]

theorem deg_pderiv {σ : Type} (b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b P).totalDegree ≤ P.totalDegree := by
  by_cases h : MvPolynomial.pderiv b P = 0
  · simp [h]
  · have := deg_X_pderiv b b P
    rw [MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _) h] at this
    omega

theorem deg_pderiv_X {σ : Type} (a b : σ) (P : MvPolynomial σ ℂ) :
    (MvPolynomial.pderiv b (MvPolynomial.X a * P)).totalDegree ≤ P.totalDegree := by
  classical
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le (deg_X_pderiv _ _ _) ?_)
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

def nonRaising (σ : Type) : Submodule ℂ (Module.End ℂ (MvPolynomial σ ℂ)) where
  carrier := {L | ∀ P, (L P).totalDegree ≤ P.totalDegree}
  add_mem' {L L'} h h' P := (MvPolynomial.totalDegree_add _ _).trans (max_le (h P) (h' P))
  zero_mem' P := by simp
  smul_mem' c L h P := (MvPolynomial.totalDegree_smul_le _ _).trans (h P)

theorem mem_nonRaising {σ : Type} {L : Module.End ℂ (MvPolynomial σ ℂ)} :
    L ∈ nonRaising σ ↔ ∀ P, (L P).totalDegree ≤ P.totalDegree := Iff.rfl

variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

def quad (i : Fin b) (j k : Fin a) : PolF D b a :=
  if ε' i = ε j ∧ ε' i ≠ ε k then
    (sgn (ε j) * sgn (ε k)) • (MvPolynomial.X (τ, i, j) * MvPolynomial.X (τ, i, k)) else 0

theorem quad_hom (i : Fin b) (j k : Fin a) : (quad τ ε ε' i j k).IsHomogeneous 2 := by
  unfold quad
  split_ifs
  · exact (MvPolynomial.homogeneousSubmodule _ ℂ 2).smul_mem _
      ((MvPolynomial.isHomogeneous_X ℂ _).mul (MvPolynomial.isHomogeneous_X ℂ _))
  · exact MvPolynomial.isHomogeneous_zero _ _ _

theorem term_mem (i : Fin b) (j k : Fin a) :
    raiO τ ε ε' i j * lowO τ ε ε' i k - LinearMap.mulLeft ℂ (quad τ ε ε' i j k) ∈ nonRaising (FVar D b a) := by
  unfold raiO lowO quad
  by_cases h1 : ε' i = ε j <;> by_cases h2 : ε' i = ε k
  · rw [if_pos h1, if_pos h2, if_neg (fun h => h.2 h2), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm]
    exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => deg_X_pderiv _ _ P)
  · rw [if_pos h1, if_neg h2, if_pos ⟨h1, h2⟩]
    convert Submodule.zero_mem _
    rw [sub_eq_zero]
    refine LinearMap.ext fun P => ?_
    simp [smul_smul, mul_assoc, mul_comm (sgn (ε k))]
  · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm, neg_mul]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (mem_nonRaising.2 fun P => (deg_pderiv _ _).trans (deg_pderiv _ P)))
  · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1), LinearMap.mulLeft_zero_eq_zero, sub_zero,
      smul_mul_smul_comm, neg_mul]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _
      (mem_nonRaising.2 fun P => deg_pderiv_X _ _ P))

def quadS (X : Matrix (Fin a) (Fin a) ℂ) : PolF D b a :=
  ∑ j, ∑ k, X j k • ∑ i, quad τ ε ε' i j k

theorem quadS_hom (X : Matrix (Fin a) (Fin a) ℂ) : (quadS τ ε ε' X).IsHomogeneous 2 :=
  (MvPolynomial.homogeneousSubmodule _ ℂ 2).sum_mem fun j _ =>
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ <|
      Submodule.sum_mem _ fun i _ => quad_hom τ ε ε' i j k

theorem rest_mem (X : Matrix (Fin a) (Fin a) ℂ) :
    fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X) ∈ nonRaising (FVar D b a) := by
  have h : LinearMap.mulLeft ℂ (quadS τ ε ε' X) =
      ∑ j, ∑ k, X j k • ∑ i, LinearMap.mulLeft ℂ (quad τ ε ε' i j k) := by
    refine LinearMap.ext fun P => ?_
    simp [quadS, Finset.sum_mul, LinearMap.sum_apply]
  rw [h, fockS, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => ?_)
  rw [add_sub_right_comm]
  refine Submodule.add_mem _ (term_mem τ ε ε' i j k) ?_
  split_ifs
  · exact Submodule.smul_mem _ _ (mem_nonRaising.2 fun P => le_rfl)
  · exact Submodule.zero_mem _

theorem sgn_ne_zero (e : Bool) : sgn e ≠ 0 := by
  cases e <;> simp [sgn]

theorem quadS_ne_zero (X : Matrix (Fin a) (Fin a) ℂ) (i : Fin b) (j k : Fin a) (hj : ε' i = ε j)
    (hk : ε' i ≠ ε k) (hX : X j k ≠ 0) : quadS τ ε ε' X ≠ 0 := by
  classical
  intro h0
  let f : FVar D b a → ℂ := fun v => if v = (τ, i, j) ∨ v = (τ, i, k) then 1 else 0
  have key : ∀ i' j' k', MvPolynomial.aeval f (quad τ ε ε' i' j' k') =
      if i' = i ∧ j' = j ∧ k' = k then sgn (ε j) * sgn (ε k) else 0 := by
    intro i' j' k'
    by_cases h : i' = i ∧ j' = j ∧ k' = k
    · obtain ⟨rfl, rfl, rfl⟩ := h
      simp [quad, hj, f, hj ▸ hk]
    · rw [if_neg h]
      unfold quad
      split_ifs with h'
      · simp only [map_smul, map_mul, MvPolynomial.aeval_X, f, Prod.mk.injEq, true_and]
        split_ifs with h1 h2
        · exfalso
          rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h2 with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact h'.2 hj
          · exact h ⟨rfl, rfl, rfl⟩
          · exact hk h'.1
          · exact hk h'.1
        all_goals simp
      · simp
  have h1 := congrArg (MvPolynomial.aeval f) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [quadS, map_sum, map_smul, key, map_zero] at h1
  rw [Finset.sum_eq_single j, Finset.sum_eq_single k, Finset.sum_eq_single i] at h1
  · simp [hX, sgn_ne_zero] at h1
  · intro i' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp
  · intro i' _ h; simp [h]
  · simp

theorem fockS_decomp : ∀ (D : D7) (a b : ℕ) (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool) (X : Matrix (Fin a) (Fin a) ℂ), 0 < b → (∃ j k, ε j ≠ ε k ∧ X j k ≠ 0 ∧ X k j ≠ 0) → ∃ (Q : PolF D b a) (L : Module.End ℂ (PolF D b a)), Q ≠ 0 ∧ Q.IsHomogeneous 2 ∧ (∀ P, (L P).totalDegree ≤ P.totalDegree) ∧ GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockS τ ε ε' X = LinearMap.mulLeft ℂ Q + L := by
  rintro D a b τ ε ε' X hb ⟨j, k, hjk, h1, h2⟩
  refine ⟨quadS τ ε ε' X, fockS τ ε ε' X - LinearMap.mulLeft ℂ (quadS τ ε ε' X), ?_, quadS_hom τ ε ε' X,
    mem_nonRaising.1 (rest_mem τ ε ε' X), by abel⟩
  by_cases h : ε' ⟨0, hb⟩ = ε j
  · exact quadS_ne_zero τ ε ε' X ⟨0, hb⟩ j k h (h ▸ hjk) h1
  · refine quadS_ne_zero τ ε ε' X ⟨0, hb⟩ k j ?_ h h2
    revert h hjk
    cases ε' ⟨0, hb⟩ <;> cases ε j <;> cases ε k <;> simp

end GlobalTheory.Chain.RealIt.FockSrcDec

end
end

