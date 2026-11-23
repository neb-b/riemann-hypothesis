module

public import Formalism.HermitianCurvature.Bundle0009
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.HermitianCurvature.Bundle0007
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0006
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
public import Formalism.HermitianCurvature.StatementJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0048
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0040

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ProductIntervalFrames
section
open Matrix Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.ProductIntervalFrames

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem isInternal_comp {ι κ W : Type*} [DecidableEq ι] [DecidableEq κ] [AddCommGroup W] [Module ℂ W]
    (Φ : ι → κ) (hΦ : Function.Bijective Φ) (S : κ → Submodule ℂ W) (h : DirectSum.IsInternal S) :
    DirectSum.IsInternal (fun i => S (Φ i)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h ⊢
  exact ⟨h.1.comp hΦ.1, by rw [hΦ.2.iSup_comp S]; exact h.2⟩

theorem prod_Icc_one (n : ℕ) (f : ℕ → ℂ) : ∏ i ∈ Icc 1 n, f i = ∏ j : Fin n, f ((j : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc (n := n)]
    simp

abbrev par (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) : M.Par := ⟨n + 1, r, T, T', u, u⟩

theorem rho_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (ρ : M.Ty (par n r T T' u)) (j : Fin n) :
    M.rho (par n r T T' u) ρ ((j : ℕ) + 1) = u ((j : ℕ) + 2) + 1 / 2 + (((ρ j : Fin _) : ℕ) : ℝ) := by
  have hj := j.isLt
  simp only [M.rho, M.Par.lo, par, max_self]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

theorem wid_eq (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (L : Fin (n + 1) → ℤ)
    (hL : ∀ j : Fin (n + 1), u ((j : ℕ) + 1) - u 1 = (L j : ℝ))
    (hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc) (j : Fin n) :
    (((par n r T T' u).wid ((j : ℕ) + 1) : ℕ) : ℤ) = L j.castSucc - L j.succ - 1 := by
  have h1 := hL j.castSucc
  have h2 := hL j.succ
  simp only [Fin.coe_castSucc, Fin.val_succ] at h1 h2
  have hd : (par n r T T' u).hi ((j : ℕ) + 1) - (par n r T T' u).lo ((j : ℕ) + 1) =
      ((L j.castSucc - L j.succ - 1 : ℤ) : ℝ) := by
    simp only [M.Par.hi, M.Par.lo, par, min_self, max_self]
    push_cast
    linarith
  have hnn : 0 ≤ L j.castSucc - L j.succ - 1 := by linarith [hg j]
  simp only [M.Par.wid]
  rw [hd, ← Int.floor_toNat, Int.floor_intCast, Int.toNat_of_nonneg hnn]

theorem main (hK : BranchingK) (Wp : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (n r : ℕ) (T T' : ℝ) (u : ℕ → ℝ) (hOK : (par n r T T' u).OK)
    (z e : Fin (2 * r + (n + 1) + 1) → ℂ) (π : Mx (n + 1) r → (Wp →L[ℂ] Wp)) (hz : inWb (n + 1) r z)
    (hT : 0 < Tz (n + 1) r z) (hπ : IsType (n + 1) r z π u) (he : inWb (n + 1) r e)
    (hez : herm (Hpk (n + 1) r) e z = 0) (hee : herm (Hpk (n + 1) r) e e = 1) :
    ∃ S : M.Ty (par n r T T' u) → Submodule ℂ Wp, DirectSum.IsInternal S ∧
      (∀ ρ, S ρ ≠ ⊥ ∧ ∀ S' : Submodule ℂ Wp, S' ≤ S ρ →
        (∀ h ∈ UWset (n + 1) r z, h *ᵥ e = e → ∀ v ∈ S', π h v ∈ S') → S' = ⊥ ∨ S' = S ρ) ∧
      ∀ Bs : Fin n → Fin (2 * r + (n + 1) + 1) → ℂ, IsFrameOf (n + 1) r [z, e] Bs →
        ∀ (ρ : M.Ty (par n r T T' u)) (w : ℂ), ∀ v ∈ S ρ,
        capRep (n + 1) r π Bs w v = M.xC (par n r T T' u) ρ (w - (((n + 1 : ℕ) : ℂ) - 2) / 2) • v := by
  have hint : ∀ j : Fin (n + 1), ∃ N : ℤ, u ((j : ℕ) + 1) - u 1 = (N : ℝ) := fun j =>
    hOK.int_u ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1
        omega)
  choose L hL using hint
  have hgap : ∀ j : Fin n, u ((j : ℕ) + 2) + 1 ≤ u ((j : ℕ) + 1) := fun j => by
    have h := hOK.gap ((j : ℕ) + 1) (by
      have := j.2
      rw [mem_Icc]
      constructor
      · omega
      · show (j : ℕ) + 1 ≤ n + 1 - 1
        omega)
    simp only [M.Par.lo, M.Par.hi, max_self, min_self] at h
    linarith
  have hg : ∀ j : Fin n, L j.succ + 1 ≤ L j.castSucc := fun j => by
    have h1 := hL j.castSucc
    have h2 := hL j.succ
    simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
    have h3 := hgap j
    have : (L j.succ : ℝ) + 1 ≤ (L j.castSucc : ℝ) := by linarith
    exact_mod_cast this
  have hanti : StrictAnti L := Fin.strictAnti_iff_succ_lt.2 fun j => by have := hg j; omega
  have hw := wid_eq n r T T' u L hL hg
  set β : ℂ := (u 1 : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 with hβ
  have hrel : ∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ) := fun j => by
    have h : (u ((j : ℕ) + 1) : ℂ) - (u 1 : ℂ) = (L j : ℂ) := by exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (hL j)
    rw [hβ, ← h]
    ring
  obtain ⟨S₀, hint₀, hirr, heig⟩ := hK Wp n r z e π u β L hz hT hπ hanti hrel he hez hee
  let Φ : M.Ty (par n r T T' u) → {M : Fin n → ℤ // Box L M} := fun ρ =>
    ⟨fun j => L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ), fun j => by
      have h1 := (ρ j).2
      have h2 := hw j
      constructor
      · show L j.succ < L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ)
        omega
      · show L j.succ + 1 + (((ρ j : Fin _) : ℕ) : ℤ) ≤ L j.castSucc
        omega⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro ρ ρ' h
      funext j
      have h1 := congrFun (congrArg Subtype.val h) j
      simp only [Φ] at h1
      apply Fin.ext
      omega
    · intro M
      refine ⟨fun j => ⟨(M.1 j - L j.succ - 1).toNat, ?_⟩, ?_⟩
      · have h1 := M.2 j
        have h2 := hw j
        omega
      · apply Subtype.ext
        funext j
        have h1 := M.2 j
        simp only [Φ]
        omega
  refine ⟨fun ρ => S₀ (Φ ρ), isInternal_comp Φ hΦ S₀ hint₀, fun ρ => hirr (Φ ρ), ?_⟩
  intro Bs hBs ρ w v hv
  rw [heig Bs hBs (Φ ρ) w v hv]
  congr 1
  unfold M.xC cpol
  rw [show (par n r T T' u).k - 1 = n from rfl, prod_Icc_one]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rho_eq]
  have h : (u ((j : ℕ) + 2) : ℂ) - (u 1 : ℂ) = (L j.succ : ℂ) := by
    have := hL j.succ
    simp only [Fin.val_succ] at this
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this
  simp only [shf, Φ, hβ]
  push_cast
  rw [← h]
  ring

end Formalism.FourierDecayAlt.P.ProductIntervalFrames

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem qr_branching_of : Qr.BranchingK → Formalism.FourierDecayAlt.Q.Branching := by
  intro hK Wp _ _ _ P hOK hu'
  obtain ⟨k, r, T, T', u, u'⟩ := P
  dsimp only at hu'
  subst hu'
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by have := hOK.k_pos; dsimp only at this; omega⟩
  intro z e π hz hT hπ he hez hee
  exact ProductIntervalFrames.main hK Wp n r T T' _ hOK z e π hz hT hπ he hez hee

end Formalism.FourierDecayAlt.P
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.QuantumMinorCommutation
section
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.QuantumMinorCommutation

open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

theorem sgn_congr {a b : ℕ} (h : a % 2 = b % 2) : (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

section alg

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)

theorem commute_Tm (v : ℂ) (a b : Fin n) (x : A) (h : Commute x (E a b)) : Commute x (Tm E v a b) := by
  unfold Tm
  refine Commute.add_right ?_ h
  split_ifs
  · exact (Algebra.commutes v x).symm
  · exact Commute.zero_right x

theorem Tm_comm (v : ℂ) (a b : Fin n) (x : A) :
    Tm E v a b * x - x * Tm E v a b = E a b * x - x * E a b := by
  unfold Tm
  have h : (if a = b then algebraMap ℂ A v else 0) * x = x * (if a = b then algebraMap ℂ A v else 0) := by
    split_ifs
    · exact Algebra.commutes v x
    · simp
  rw [add_mul, mul_add, h]
  abel

theorem commute_qminor {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : A)
    (h : ∀ s s', Commute x (E (a s) (b s'))) : Commute x (qminor E a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.commute_cast x _) ?_
  refine Commute.list_prod_right _ _ (fun y hy => ?_)
  obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact commute_Tm E _ _ _ x (h _ _)

theorem rowExp (hE : GlRel E) {m : ℕ} (a b : Fin (m + 1) → Fin n) (l₀ : Fin (m + 1)) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
      (Tm E (u - (m : ℂ)) (a l₀) (b l) * qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by
  have h := quantumMinorRowSkew_holds A n (m + 1) E a b (Fin.cycleRange l₀).symm u
  have hs : ((Equiv.Perm.sign (Fin.cycleRange l₀).symm : ℤˣ) : ℤ) = (-1) ^ (l₀ : ℕ) := by
    rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
    simp
  rw [hs] at h
  have h2 : qminor E a b u = (((-1 : ℤ) ^ (l₀ : ℕ) : ℤ) : A) * qminor E (a ∘ (Fin.cycleRange l₀).symm) b u := by
    rw [h, ← mul_assoc, ← Int.cast_mul, ← pow_add, sgn_congr (b := 0) (by omega)]
    simp
  rw [h2, expansion_first_line A n m E hE _ b u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h0 : (a ∘ (Fin.cycleRange l₀).symm) 0 = a l₀ := by
    simp [Fin.cycleRange_symm_zero]
  have h1 : (a ∘ (Fin.cycleRange l₀).symm) ∘ Fin.succ = a ∘ l₀.succAbove := by
    funext k
    simp [Fin.cycleRange_symm_succ]
  rw [h0, h1, ← mul_assoc, ← Int.cast_mul, ← pow_add]

theorem colExp (hE : GlRel E) {m : ℕ} (a b : Fin (m + 1) → Fin n) (l₀ : Fin (m + 1)) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * Tm E (u - (m : ℂ)) (a l) (b l₀)) := by
  have h := quantumMinorColSkew_holds A n (m + 1) E hE a b (cycleToLast m l₀) u
  have hs : ((Equiv.Perm.sign (cycleToLast m l₀) : ℤˣ) : ℤ) = (-1) ^ (m - (l₀ : ℕ)) := by
    rw [sign_cycleToLast]
    simp
  rw [hs] at h
  have h2 : qminor E a b u = (((-1 : ℤ) ^ (m - (l₀ : ℕ)) : ℤ) : A) * qminor E a (b ∘ cycleToLast m l₀) u := by
    rw [h, ← mul_assoc, ← Int.cast_mul, ← pow_add, sgn_congr (b := 0) (by omega)]
    simp
  rw [h2, expansion_last_column A n m E a _ u, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have h0 : (b ∘ cycleToLast m l₀) (Fin.last m) = b l₀ := by
    simp [cycleToLast_last]
  have h1 : (b ∘ cycleToLast m l₀) ∘ Fin.castSucc = b ∘ l₀.succAbove := by
    funext k
    simp [cycleToLast_castSucc]
  have hl := l₀.isLt
  rw [h0, h1, ← mul_assoc, ← Int.cast_mul, ← pow_add,
    sgn_congr (a := m - (l₀ : ℕ) + (m + (l : ℕ))) (b := (l₀ : ℕ) + (l : ℕ)) (by omega)]

theorem minorVec_gen (hE : GlRel E) (y : Fin n → A) (hy : IsVec E y) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, a (l₀.succAbove k) ≠ a l₀) (u : ℂ) :
    qminor E a b u * y (a l₀) = y (a l₀) * qminor E a b u -
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (y (b l) * qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by
  rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', rowExp E hE a b l₀ u, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hM : Commute (y (a l₀)) (qminor E (a ∘ l₀.succAbove) (b ∘ l.succAbove) u) := by
    refine commute_qminor E _ _ u _ (fun s s' => ?_)
    have := hy ((a ∘ l₀.succAbove) s) ((b ∘ l.succAbove) s') (a l₀)
    rw [if_neg (show (a ∘ l₀.succAbove) s ≠ a l₀ from hne s), sub_eq_zero] at this
    exact this.symm
  have hT : Tm E (u - (m : ℂ)) (a l₀) (b l) * y (a l₀) - y (a l₀) * Tm E (u - (m : ℂ)) (a l₀) (b l) = -y (b l) := by
    rw [Tm_comm, hy, if_pos rfl]
  have hc : y (a l₀) * (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) =
      (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) * y (a l₀) := (Int.commute_cast _ _).eq
  have hT' : y (b l) = y (a l₀) * Tm E (u - (m : ℂ)) (a l₀) (b l) - Tm E (u - (m : ℂ)) (a l₀) (b l) * y (a l₀) := by
    rw [← neg_sub, hT, neg_neg]
  rw [← mul_assoc (y (a l₀)), hc, mul_assoc _ (y (a l₀)), mul_assoc _ _ (y (a l₀)), mul_assoc _ _ (y (a l₀)),
    ← hM.eq, ← mul_sub]
  congr 1
  rw [hT', sub_mul, mul_assoc, mul_assoc]

theorem minorCov_gen (hE : GlRel E) (η : Fin n → A) (hη : IsCov E η) {m : ℕ} (a b : Fin (m + 1) → Fin n)
    (l₀ : Fin (m + 1)) (hne : ∀ k, b (l₀.succAbove k) ≠ b l₀) (u : ℂ) :
    qminor E a b u * η (b l₀) - η (b l₀) * qminor E a b u =
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u * η (a l)) := by
  rw [colExp E hE a b l₀ u, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  have hM : Commute (η (b l₀)) (qminor E (a ∘ l.succAbove) (b ∘ l₀.succAbove) u) := by
    refine commute_qminor E _ _ u _ (fun s s' => ?_)
    have := hη ((a ∘ l.succAbove) s) ((b ∘ l₀.succAbove) s') (b l₀)
    rw [if_neg (show (b ∘ l₀.succAbove) s' ≠ b l₀ from hne s'), sub_eq_zero] at this
    exact this.symm
  have hT : Tm E (u - (m : ℂ)) (a l) (b l₀) * η (b l₀) - η (b l₀) * Tm E (u - (m : ℂ)) (a l) (b l₀) = η (a l) := by
    rw [Tm_comm, hη, if_pos rfl]
  have hc : η (b l₀) * (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) =
      (((-1 : ℤ) ^ ((l₀ : ℕ) + (l : ℕ)) : ℤ) : A) * η (b l₀) := (Int.commute_cast _ _).eq
  rw [← mul_assoc (η (b l₀)), hc, mul_assoc _ (η (b l₀)), ← mul_assoc (η (b l₀)), hM.eq,
    mul_assoc _ _ (η (b l₀)), mul_assoc _ _ (η (b l₀)), mul_assoc _ (η (b l₀)), ← mul_sub, ← mul_sub, hT]

end alg

theorem sa_val {m : ℕ} (q : Fin (m + 1)) (l : Fin m) :
    ((q.succAbove l : Fin (m + 1)) : ℕ) = if (l : ℕ) < (q : ℕ) then (l : ℕ) else (l : ℕ) + 1 := by
  unfold Fin.succAbove
  simp only [Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> simp

theorem skip_one_eq_succAbove {m : ℕ} (q : Fin (m + 1)) : (skip1 q : Fin m → Fin (m + 1)) = q.succAbove :=
  funext (skip_succ_identity m q)

theorem skip_comp {m : ℕ} (q : Fin (m + 2)) (l : Fin (m + 1)) :
    (q.succAbove ∘ l.succAbove : Fin m → Fin (m + 2)) = skip2 (min (q.succAbove l) q) (max (q.succAbove l) q) := by
  funext k
  apply Fin.ext
  simp only [Function.comp, skip2, Fin.coe_min, Fin.coe_max, sa_val]
  split_ifs <;> simp only [] <;> omega

theorem eps_sa {m : ℕ} (q : Fin (m + 1)) (l : Fin m) :
    eps (q.succAbove l) q * (-1) ^ ((q.succAbove l : Fin (m + 1)) : ℕ) = (-1) ^ (l : ℕ) := by
  unfold eps
  rw [sa_val]
  split_ifs
  · simp
  · omega
  · rw [pow_succ]; ring

theorem detVec_succ {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A)
    (y : Fin (m + 1) → A) (hE : GlRel E) (hy : IsVec E y) (w : ℂ) (j : Fin (m + 1)) :
    qdet E w * y j = y j * qdet E w -
      ∑ l : Fin (m + 1), (((-1 : ℤ) ^ ((j : ℕ) + (l : ℕ)) : ℤ) : A) *
        (y l * qminor (t := m) E (skip1 j) (skip1 l) w) := by
  have h := minorVec_gen E hE y hy id id j (fun k => Fin.succAbove_ne j k) w
  simp only [id, Function.id_comp] at h
  simp only [skip_one_eq_succAbove]
  exact h

theorem minorCov_succ {A : Type} [Ring A] [Algebra ℂ A] {m : ℕ} (E : Fin (m + 2) → Fin (m + 2) → A)
    (η : Fin (m + 2) → A) (hE : GlRel E) (hη : IsCov E η) (u : ℂ) (q p i : Fin (m + 2)) (hip : i ≠ p) :
    qminor (t := m + 1) E (skip1 q) (skip1 p) u * η i - η i * qminor (t := m + 1) E (skip1 q) (skip1 p) u =
      ∑ a : Fin (m + 2), if a = q then 0 else
        ((eps a q * eps i p * (-1) ^ ((a : ℕ) + (i : ℕ)) : ℤ) : A) *
          (qminor (t := m) E (skip2 (min a q) (max a q)) (skip2 (min i p) (max i p)) u * η a) := by
  obtain ⟨l₀, rfl⟩ := Fin.exists_succAbove_eq hip
  have h := minorCov_gen E hE η hη q.succAbove p.succAbove l₀
    (fun k => fun hk => Fin.succAbove_ne l₀ k (Fin.succAbove_right_injective hk)) u
  rw [skip_one_eq_succAbove, skip_one_eq_succAbove, h, Fin.sum_univ_succAbove _ q, if_pos rfl, zero_add]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [if_neg (Fin.succAbove_ne q l), skip_comp, skip_comp]
  congr 2
  rw [pow_add, pow_add, ← eps_sa q l, ← eps_sa p l₀]
  ring

end Formalism.FourierDecayAlt.P.QuantumMinorCommutation

theorem Formalism.FourierDecayAlt.P.quantum_determinant_vector : Formalism.FourierDecayAlt.Qr.DetVec := by
  intro A _ _ t E y hE hy w j
  cases t with
  | zero => exact j.elim0
  | succ m => exact Formalism.FourierDecayAlt.P.QuantumMinorCommutation.detVec_succ E y hE hy w j

theorem Formalism.FourierDecayAlt.P.quantum_minor_covariance : Formalism.FourierDecayAlt.Qr.MinorCov := by
  intro A _ _ t E η hE hη u q p i
  by_cases hip : i = p
  · rw [if_pos hip, sub_eq_zero]
    refine (Formalism.FourierDecayAlt.P.QuantumMinorCommutation.commute_qminor E _ _ u _ (fun s s' => ?_)).eq.symm
    have := hη (Formalism.FourierDecayAlt.Q.skip1 q s) (Formalism.FourierDecayAlt.Q.skip1 p s') i
    have hne : Formalism.FourierDecayAlt.Q.skip1 p s' ≠ i := by
      rw [hip]
      intro h
      have h' := congrArg Fin.val h
      unfold Formalism.FourierDecayAlt.Q.skip1 at h'
      split_ifs at h' <;> simp only [] at h' <;> omega
    rw [if_neg hne, sub_eq_zero] at this
    exact this.symm
  · rw [if_neg hip]
    match t, E, η, hE, hη, q, p, i, hip with
    | 0, _, _, _, _, q, _, _, _ => exact q.elim0
    | 1, _, _, _, _, _, p, i, hip => exact absurd (Subsingleton.elim i p) hip
    | m + 2, E, η, hE, hη, q, p, i, hip => exact Formalism.FourierDecayAlt.P.QuantumMinorCommutation.minorCov_succ E η hE hη u q p i hip
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialAdjointOfParts
section
open Matrix MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem bcWeight_nonneg (T T' : ℝ) (q : (Fin r → ℂ) × ℂ) : 0 ≤ bcWeight k r T T' q := by
  unfold bcWeight
  split_ifs with h
  · exact mul_nonneg (Finset.prod_nonneg fun a _ => by positivity) (pow_nonneg (sub_nonneg.2 h) _)
  · exact le_rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem adj_local (Θ : DiffOp k r Wp Wq) {f₁ f₂ : Mat k r → (Wq →L[ℂ] Wp)} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) : ∀ x ∈ V, x ∈ GV k r → opAdj Θ f₁ x = opAdj Θ f₂ x := by
  intro x hx hxG
  unfold opAdj
  congr 1
  refine List.map_congr_left fun T _ => ?_
  rw [PositiveOrbitOpen.rw_local (f₁ := fun y => T.coefAdj y (f₁ y)) (f₂ := fun y => T.coefAdj y (f₂ y)) hV
    (fun y hy hyG => by simp only [h y hy hyG]) T.word.reverse
    (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) x hx hxG]

theorem betaBig_congr (D : RealPlaceData k r Wp Wq)
    {J₁ J₁' J₂ J₂' : Mat k r → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)}
    (h : ∀ g ∈ Om k r D.z D.z', J₁ g = J₂ g) (h' : ∀ g ∈ Om k r D.z D.z', J₁' g = J₂' g) :
    betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₁ J₁' = betaBig k r (Tz k r D.z) (Tz k r D.z') D.μsec J₂ J₂' := by
  unfold betaBig
  apply integral_congr_ae
  filter_upwards [ae_imp_of_ae_restrict (Formalism.FourierDecayAlt.P.big_cell_orbit_set k r Wp Wq D)] with q hq
  by_cases hQ : q ∈ Qset D
  · have hg : bigCell k r q.1 (D.μsec q.2) ∈ Om k r D.z D.z' := hq hQ
    simp only [h _ hg, h' _ hg]
  · have h0 : bcWeight k r (Tz k r D.z) (Tz k r D.z') q = 0 :=
      le_antisymm (not_lt.1 hQ) (bcWeight_nonneg _ _ q)
    simp only [h0, Complex.ofReal_zero, zero_mul]

end Formalism.FourierDecayAlt.P.JFxG

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Formalism.FourierDecayAlt.P
end
end

