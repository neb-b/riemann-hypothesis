module

public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.Bundle0001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselNormSteps.BesselLine.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorExpansion
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0086
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0085
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0010
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0074
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKPt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensityOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixOneZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwoDiagonalZeroSize

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.AdjointOfIso
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace Formalism.FourierDecayAlt.P.S3dx6

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

variable {k r : ℕ}

theorem unit_of_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 ∧ g⁻¹ * g = 1 := by
  obtain ⟨-, h2, -⟩ := PI.WBL.Cv.grpAll k r 0
  exact ⟨(h2 g hg).1, (h2 g hg).2.1⟩

theorem inv_inv_uh {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹⁻¹ = g :=
  Matrix.inv_eq_left_inv (unit_of_uh hg).1

theorem inner_sig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hU : PI.WBL.Cv.SigU σ) {a : Mx k r} (ha : a ∈ UH (Hpk k r)) (u v : H) :
    ⟪σ a u, v⟫_ℂ = ⟪u, σ a⁻¹ v⟫_ℂ := by
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ a : H →ₗ[ℂ] H), norm_map' := hU.2.2 a ha }
  have hai : a⁻¹ ∈ UH (Hpk k r) := WeylGroupFacts.uh_inv ha
  have hv : σ a (σ a⁻¹ v) = v := by
    rw [← ContinuousLinearMap.comp_apply, ← hU.2.1 a ha _ hai, (unit_of_uh ha).1, hU.1]; rfl
  calc ⟪σ a u, v⟫_ℂ = ⟪T u, T (σ a⁻¹ v)⟫_ℂ := by
        show ⟪σ a u, v⟫_ℂ = ⟪σ a u, σ a (σ a⁻¹ v)⟫_ℂ
        rw [hv]
    _ = ⟪u, σ a⁻¹ v⟫_ℂ := T.inner_map_map _ _

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Mx k r) : ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem measurePreserving_invM_of_isHaarOn {z : Fin (2 * r + k + 1) → ℂ} {μ : Measure (Mt k r)} (h : B.IsHaarOn (UWset k r z) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r z) h⟩

theorem mp_inv_N {μ : Measure (Mt k r)} (h : B.IsHaarOn (Nset k r) μ) :
    MeasurePreserving (B7.invM (k := k) (r := r)) μ μ :=
  ⟨B7.measurable_invM, Formalism.FourierDecayAlt.P.haar_measure_inversion k r _ μ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) h⟩

end Formalism.FourierDecayAlt.P.S3dx6
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorEquivariance
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.TL

open TLC in
theorem capelli_vector_equivariance : TL.CapVEquiv := by
  intro Wq _ _ _ k r z' π' B0 ν ν' h hk hz hT hπ hB0 hν hh hνν' w
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  obtain ⟨he, hez, hee⟩ := cap_vec hB0 hν
  set e := ∑ j, ν j • B0 j with hedef
  set g := h⁻¹ with hgdef
  have hg : g ∈ UWset (n + 1) r z' := LieBracketMultiplication.uw_inv hh
  have hgU : g ∈ UH (Hpk (n + 1) r) := hg.1
  have hgL : g ∈ Glev (n + 1) r (Fin.last r) := Qx8.uw_glev _ hg
  have hν' : C6.sq2 ν' = 1 := by
    have h1 : herm (Hpk (n + 1) r) (∑ j, ν' j • B0 j) (∑ j, ν' j • B0 j) = 1 := by
      rw [hνν', Qx2.herm_uh hgU, hee]
    rw [HermitianFormSums.herm_comb hB0] at h1
    have : ∀ a, ν' a * star (ν' a) = ((Complex.normSq (ν' a) : ℝ) : ℂ) := fun a => Complex.mul_conj (ν' a)
    simp only [this] at h1
    rw [← Complex.ofReal_sum] at h1
    exact_mod_cast h1
  obtain ⟨Bs, hBs⟩ := exists_frame_two n r z' e hz hT he hez hee
  set Bs' : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ := fun a => g *ᵥ Bs a with hBs'def
  have hBs' : IsFrameOf (n + 1) r [z', ∑ j, ν' j • B0 j] Bs' := by
    refine ⟨fun a => Qx8.inWb_mulVec hgL (hBs.1 a), fun a b => ?_, fun a v hv => ?_⟩
    · rw [hBs'def, Qx2.herm_uh hgU]; exact hBs.2.1 a b
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · have e1 := Qx2.herm_uh hgU (Bs a) v
        rw [hg.2.2] at e1
        rw [e1]; exact hBs.2.2 a _ (by simp)
      · rw [hνν', Qx2.herm_uh hgU]; exact hBs.2.2 a _ (by simp)
  have hF := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs ν (by omega) hz hT hπ hB0 hν hBs w
  have hF' := capelli_vector_frame Wq (n + 1) r z' π' B0 Bs' ν' (by omega) hz hT hπ hB0 hν' hBs' w
  have hBs1 := HermitianFormSums.frame_sub hBs
  have hBs1' := HermitianFormSums.frame_sub hBs'
  have hq := (frame_general_linear Wq (n + 1) r n z' π' Bs hπ hBs1).2 w
  have hq' := (frame_general_linear Wq (n + 1) r n z' π' Bs' hπ hBs1').2 w
  have hgi : g⁻¹ = h := Matrix.nonsing_inv_nonsing_inv _ (WeylGroupFacts.isUnit_of_uh hh.1)
  have hgh : g * h = 1 := LeftDerivativeCurves.uh_inv_mul hh.1
  have hhg : h * g = 1 := LeftDerivativeCurves.uh_mul_inv hh.1
  have hUUi : (π' g).comp (π' h) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hg _ hh, hgh, hπ.1.1]; rfl
  have hUiU : (π' h).comp (π' g) = ContinuousLinearMap.id ℂ Wq := by
    rw [← hπ.1.2 _ hh _ hg, hhg, hπ.1.1]; rfl
  set U : Module.End ℂ Wq := (π' g : Wq →ₗ[ℂ] Wq) with hU
  set Ui : Module.End ℂ Wq := (π' h : Wq →ₗ[ℂ] Wq) with hUi
  have hUUi' : U * Ui = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUUi
    simpa [hU, hUi] using this
  have hUiU' : Ui * U = 1 := by
    apply LinearMap.ext; intro v
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hU, hUi] using this
  have hEB : ∀ a b, U * EB π' Bs a b * Ui = EB π' Bs' a b := by
    intro a b
    obtain ⟨hX1, hX2⟩ := QrD.frame_lie hBs1 a b
    obtain ⟨-, -, e1⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX1 g hg
    obtain ⟨-, -, e2⟩ := differential_operator_adjoint Wq (n + 1) r z' π' hπ _ hX2 g hg
    obtain ⟨c1, c2⟩ := Qx8.hpart_conj Bs a b hgU
    unfold EB QrD.ecOp
    rw [c1, c2, e1, e2, hgi]
    apply LinearMap.ext; intro v
    simp [hU, hUi]
  let f : Module.End ℂ Wq →+* Module.End ℂ Wq :=
    { toFun := fun T => U * T * Ui
      map_one' := by simp only [mul_one, hUUi']
      map_mul' := fun S T => by
        show U * (S * T) * Ui = U * S * Ui * (U * T * Ui)
        calc U * (S * T) * Ui = U * S * (Ui * U) * T * Ui := by rw [hUiU']; noncomm_ring
          _ = U * S * Ui * (U * T * Ui) := by noncomm_ring
      map_zero' := by simp only [mul_zero, zero_mul]
      map_add' := fun S T => by noncomm_ring }
  have hf : ∀ v, f (algebraMap ℂ (Module.End ℂ Wq) v) = algebraMap ℂ (Module.End ℂ Wq) v := by
    intro v
    show U * algebraMap ℂ (Module.End ℂ Wq) v * Ui = _
    rw [← Algebra.commutes, mul_assoc, hUUi', mul_one]
  have hqd := QuantumMinorExpansion.map_qminor (EB π' Bs') f hf (EB π' Bs) (fun a b => hEB a b) id id w
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  rw [hF', hF, hq', hq]
  unfold qdet
  rw [← hqd]
  show U (qminor (EB π' Bs) id id w (Ui (π' h⁻¹ v))) = π' h⁻¹ (qminor (EB π' Bs) id id w v)
  have : Ui (π' h⁻¹ v) = v := by
    rw [← hgdef]
    have := congrArg (fun T : Wq →L[ℂ] Wq => T v) hUiU
    simpa [hUi] using this
  rw [this]
  rfl

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity
section
open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem la_intmul {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (La : A →ₗ[ℂ] M) (z : ℤ) (x : A) :
    La ((z : A) * x) = (z : ℂ) • La x := by
  have hz : ((z : A) * x) = (z : ℂ) • x := by
    rw [Algebra.smul_def, map_intCast]
  rw [hz, map_smul]

theorem chain_first_identity : LastColumnChain := by
  intro A _ _ M _ _ k r z' c E La hG hc hR hL m hm u
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
    have : dpsiP k r z' (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) = 0 := by
      unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
    rw [this, zero_smul, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ ⟨m + 1, by omega⟩ ⟨m, by omega⟩ (by simp), if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      have hq := q.isLt
      rw [hx, hL _ ⟨m + 1, by omega⟩ ⟨q.val, by omega⟩ (by simp <;> omega), if_neg (by simp <;> omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne, hR _ _ _ (by simp only [InNp, hav]; simp; omega)]
    have : dpsiP k r z' (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1))) = 1 := by
      unfold dpsiP; simp only [hav]; simp; split_ifs <;> first | rfl | omega
    rw [this, one_smul]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.SignAntidiagonal
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqWigMapsValueECas
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.WigCas

open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Qr

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem cas_comm {A : Type*} [Ring A] {n : ℕ} {E : Fin n → Fin n → A} (hE : GlRel E) (c d : Fin n) :
    Cas E * E c d = E c d * Cas E := by
  have expand : Cas E * E c d - E c d * Cas E = ∑ a, ∑ b, (E a b * ((if a = c then E b d else 0) -
      (if d = b then E c a else 0)) + ((if b = c then E a d else 0) - (if d = a then E c b else 0)) * E b a) := by
    simp only [Cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    rw [← hE b a c d, ← hE a b c d]
    noncomm_ring
  have hT1 : ∑ a, ∑ b, E a b * (if a = c then E b d else 0) = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
    simp
  have hT4 : ∑ a, ∑ b, (if d = a then E c b else 0) * E b a = ∑ b, E c b * E b d := by
    rw [Finset.sum_eq_single d (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  have hT2 : ∑ a, ∑ b, E a b * (if d = b then E c a else 0) = ∑ a, E a d * E c a := by
    simp [mul_ite]
  have hT3 : ∑ a, ∑ b, (if b = c then E a d else 0) * E b a = ∑ a, E a d * E c a := by
    simp [ite_mul]
  rw [← sub_eq_zero, expand]
  simp only [mul_sub, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hT1, hT2, hT3, hT4]
  abel

end Formalism.FourierDecayAlt.P.WigCas

end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRTopAct
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem top_action_on_gauge_holds : GTRTopAct := TopAct.gTRTopAct_of_cut quadratic_top_algebra_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLSliceSS
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section closure

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem sliceLoc_zero : SliceLoc P Bs 0 := by
  intro Φ Φ' c c' _ _ _ ζ _
  simp

theorem sliceLoc_add {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T + S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ, hS Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_smul {T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (a : ℂ) (hT : SliceLoc P Bs T) :
    SliceLoc P Bs (a • T) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
  rw [hT Φ Φ' c c' hc hc' h ζ hζ]

theorem sliceLoc_mul {T S : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} (hT : SliceLoc P Bs T)
    (hS : SliceLoc P Bs S) : SliceLoc P Bs (T * S) := by
  intro Φ Φ' c c' hc hc' h ζ hζ
  exact hT (S Φ) (S Φ') c c' hc hc' (hS Φ Φ' c c' hc hc' h) ζ hζ

theorem sliceLoc_sum {ι : Type} (s : Finset ι) (T : ι → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))
    (hT : ∀ i ∈ s, SliceLoc P Bs (T i)) : SliceLoc P Bs (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    exact sliceLoc_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact sliceLoc_add (hT i (Finset.mem_insert_self _ _)) (ih fun j hj => hT j (Finset.mem_insert_of_mem hj))

theorem sliceLoc_of_smul {T U : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')} {a : ℂ} (ha : a ≠ 0)
    (hU : U = a • T) (h : SliceLoc P Bs U) : SliceLoc P Bs T := by
  have hTU : T = a⁻¹ • U := by rw [hU, smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hTU]
  exact sliceLoc_smul _ h

end closure

open Formalism.FourierDecayAlt.P.NFx4.NO in
theorem second_shift_slice_operator : GTSSLSliceSS := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH hT l hl
  have hP := hH.1.1
  have hRel := hH.2.2.2.2.2.1
  have hQQ := hH.2.2.2.2.2.2
  obtain ⟨Qr, hQ⟩ := gauge_kappa_pointwise_holds Wp Wq P Bs X d hH
  have hK : ∀ f : M.Ty P → ℂ, SliceLoc P Bs (d.κ f).1 := by
    intro f Φ Φ' c c' hc hc' h ζ hζ
    have e1 := hQ.2.2.2 f Φ ⟨(c, ζ), ⟨hc, hζ⟩⟩
    have e2 := hQ.2.2.2 f Φ' ⟨(c', ζ), ⟨hc', hζ⟩⟩
    simp only at e1 e2
    rw [e1, e2, h ζ hζ]
  have hPj : ∀ ρ, SliceLoc P Bs (Pj d ρ).1 := fun ρ => hK _
  have e10 : ∀ Y, X.t Y 1 0 = (d.QQ Y 1 0).1 := fun Y => by rw [← hQQ Y]; rfl
  have e01 : ∀ Y, X.t Y 0 1 = (d.QQ Y 0 1).1 := fun Y => by rw [← hQQ Y]; rfl
  refine ⟨?_, ?_⟩
  · have hdec : (d.SS l).1 = ∑ a, ∑ b, (Pj d a * d.SS l * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (d.SS l))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l b a
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} b Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hne : M.rho P b i ≠ M.rho P b l :=
          rho_ne P hP b hi'.1 hl (fun e => hi'.2 (by simp [e]))
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by rw [hY] at h0; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 1 0 * (Pj d b).1 = M.xEx P {l} b Y • (Pj d a * d.SS l * Pj d b).1 := by
        have h := congrArg (fstA _) (B1 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e10]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 1 0)) (hPj b))
    · rw [block_zero hRel hUp]
      exact sliceLoc_zero
  · have hdec : (star (d.SS l)).1 = ∑ a, ∑ b, (Pj d a * star (d.SS l) * Pj d b).1 := by
      have h := congrArg (fstA _) (decomp d (star (d.SS l)))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum] at h
      exact h
    rw [hdec]
    refine sliceLoc_sum _ _ fun a _ => sliceLoc_sum _ _ fun b _ => ?_
    by_cases hUp : M.Up P l a b
    · set Y : ℂ := -(M.rho P b l : ℂ) with hY
      have hc0 : M.xEx P {l} a Y ≠ 0 := by
        unfold M.xEx
        refine Finset.prod_ne_zero_iff.2 fun i hi => ?_
        have hi' := Finset.mem_sdiff.1 hi
        have hil : i ≠ l := fun e => hi'.2 (by simp [e])
        have hup := Formalism.FourierDecayAlt.P.Mx3.rhoUp P l a b hUp i hi'.1
        rw [if_neg hil, add_zero] at hup
        have hne : M.rho P b i ≠ M.rho P b l := rho_ne P hP b hi'.1 hl hil
        intro h0
        apply hne
        have : ((M.rho P b i : ℝ) : ℂ) = ((M.rho P b l : ℝ) : ℂ) := by
          rw [hY] at h0; rw [hup]; linear_combination h0
        exact_mod_cast this
      have hE : (Pj d a).1 * X.t Y 0 1 * (Pj d b).1 = M.xEx P {l} a Y • (Pj d a * star (d.SS l) * Pj d b).1 := by
        have h := congrArg (fstA _) (B4 hRel hl hUp Y)
        rw [map_mul, map_mul, map_smul] at h
        rw [e01]
        exact h
      exact sliceLoc_of_smul hc0 hE (sliceLoc_mul (sliceLoc_mul (hPj a) (hT Y 0 1)) (hPj b))
    · rw [star_block_zero hRel hUp]
      exact sliceLoc_zero

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostermanDensity
section
namespace Formalism.FourierDecayAlt.P

theorem kloosterman_density : Formalism.FourierDecayAlt.KB.KloostDens :=
  PBJ.Asm.kloosterman_density_of_parts PBJ.fubini_head_last_part PBJ.freeze_last_entry PBJ.long_orbital_integral_multiple PBJ.block_orbital_integral_multiple

end Formalism.FourierDecayAlt.P
end

