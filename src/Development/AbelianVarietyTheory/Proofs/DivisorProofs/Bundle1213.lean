module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1193
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem sig_eq_star (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := by
  have τ0 : D.what₂.Tau := D.eTau.symm 1
  apply (tauE D τ0).injective
  rw [GlobalTheory.FockCompare.tauE_star]
  exact D.sp.cm.cmUnram.2.1 (tauE D τ0) x

theorem cT_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
  refine Matrix.ext fun i j => ?_
  simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (A j i) = star (A j i)
  exact sig_eq_star _

theorem hRat_eq (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T x y = Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x) := by
  simp only [GlobalTheory.LatVac.hRat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem hRat_frames (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1)
    (hB' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)
      (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = Matrix.trace (Mᴴ * M) := by
  rw [cT_eq] at hB hB'
  rw [hRat_eq]
  set Bi := (B⁻¹ : GL (Fin S.rank) D.host.E).1 with hBi_def
  have hBi : Bi * B.1 = 1 := by rw [hBi_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSi : S.gram⁻¹ = B.1 * B.1ᴴ := by
    have h1 : B.1 * (B.1ᴴ * S.gram) = 1 := mul_eq_one_comm.1 hB
    have h2 : (B.1 * B.1ᴴ) * S.gram = 1 := by rw [Matrix.mul_assoc]; exact h1
    exact Matrix.inv_eq_left_inv h2
  have hBB : B.1ᴴ * Biᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  calc Matrix.trace (S.gram⁻¹ * (B'.1 * M * Bi)ᴴ * T.gram * (B'.1 * M * Bi))
      = Matrix.trace (B.1 * ((B.1ᴴ * Biᴴ) * (Mᴴ * ((B'.1ᴴ * T.gram * B'.1) * (M * Bi))))) := by
        rw [hSi]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (B.1 * (Mᴴ * (M * Bi))) := by rw [hBB, hB', Matrix.one_mul, Matrix.one_mul]
    _ = Matrix.trace ((Mᴴ * M * Bi) * B.1) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M) := by rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem embT_sqrt (τ : D.what₂.Tau) :
    embT D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  Formalism.L2.Theta.tauE_sqrtMinusD D τ

theorem embT_ne_conj (τ τ' : D.what₂.Tau) : embT D τ ≠ (starRingEnd ℂ).comp (embT D τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h D.host.sqrtMinusD)
  rw [RingHom.comp_apply, embT_sqrt, embT_sqrt] at h1
  have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  simp at h1
  linarith

theorem trace_split (z : D.host.E) :
    ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = ∑ τ : D.what₂.Tau, (embT D τ z + starRingEnd ℂ (embT D τ z)) := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (x := z)
  let e : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →ₐ[ℚ] ℂ) := fun s =>
    RingHom.equivRatAlgHom _ _ (Sum.elim (embT D) (fun τ => (starRingEnd ℂ).comp (embT D τ)) s)
  have he : Function.Bijective e := by
    refine (RingHom.equivRatAlgHom _ _).bijective.comp ⟨?_, fun σ => ?_⟩
    · rintro (a | a) (b | b) hab
      · rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D hab]
      · exact absurd hab (embT_ne_conj a b)
      · exact absurd hab.symm (embT_ne_conj b a)
      · have : embT D a = embT D b := RingHom.ext fun x =>
          (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
        rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D this]
    · obtain ⟨τ, h | h⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D σ
      · exact ⟨Sum.inl τ, h.symm⟩
      · exact ⟨Sum.inr τ, h.symm⟩
  rw [← Fintype.sum_bijective e he (fun s => e s z) (fun σ => σ z) fun _ => rfl, Fintype.sum_sum_type] at h
  rw [show ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E z) from rfl, h,
    ← Finset.sum_add_distrib]
  rfl

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_star (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (star x) = starRingEnd ℂ (embT D τ x) :=
  GlobalTheory.FockCompare.tauE_star τ x

theorem absNorm_ne : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by
  have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  exact_mod_cast this

theorem embT_c_add_conj (τ : D.what₂.Tau) :
    embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) +
      starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2)) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) := by
  have hN := absNorm_ne (D := D)
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D).ne'
  have e : embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) =
      -1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ))) *
        ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) ^ 2 := by
    unfold Formalism.BasicNotions.Host.xi0
    simp only [map_mul, map_div₀, map_neg, map_one, map_natCast, map_pow, map_add (f := _), map_ofNat, embT_sqrt]
  rw [e]
  simp only [map_mul, map_div₀, map_neg, map_one, map_pow, map_add (f := _), map_natCast, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  field_simp
  ring_nf

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_trace (τ : D.what₂.Tau) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    embT D τ (Matrix.trace (Mᴴ * M)) =
      ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    embT_star, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]

theorem k_eq {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (k : ℤ)
    (hk : (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M))) :
    (k : ℝ) = -(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ) := by
  have h : ((k : ℚ) : ℂ) = ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M)) : ℚ) : ℂ) := by rw [hk]
  rw [trace_split] at h
  have h2 : ∀ τ : D.what₂.Tau,
      embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) +
        starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M))) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) *
        ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
    intro τ
    rw [show embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) =
        embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) * embT D τ (Matrix.trace (Mᴴ * M)) from
        map_mul _ _ _, embT_trace, map_mul (starRingEnd ℂ), Complex.conj_ofReal, ← add_mul, embT_c_add_conj]
  rw [Finset.sum_congr rfl fun τ _ => h2 τ, ← Finset.mul_sum] at h
  have hN := absNorm_ne (D := D)
  have h3 : ((k : ℝ) : ℂ) = (((-(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [show ((k : ℂ)) = ((k : ℚ) : ℂ) by push_cast; rfl, h]
    field_simp
    simp only [Complex.ofReal_sum]
  exact_mod_cast h3

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem qH_eq {m n : ℕ} (δ : ℂ) (hδ : δ ≠ 0) (M : Matrix (Fin m) (Fin n) D.host.E) :
    Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re =
      (∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) / (Ideal.absNorm D.host.ccK : ℝ) := by
  have hA := GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot
  have hH : Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M) =
      (((Complex.normSq δ * ∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
        area (lamOf D D.host.ccK δ) : ℝ) : ℂ) := by
    unfold Hf
    rw [Complex.ofReal_div]
    congr 1
    simp only [embV, tor0, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [hH, Complex.ofReal_re, hA]
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
  field_simp

theorem al_mul_neg_one_pow : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) → Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) * (-1 : ℂ) ^ k = 1 := by
  intro D S T B B' hB hB' δ hδ M k hk
  rw [hRat_frames S T B B' hB hB' M] at hk
  have hk' := k_eq M k hk
  have hq := qH_eq δ hδ M
  have hr : Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re = ((-k : ℤ) : ℝ) := by
    rw [hq, Int.cast_neg, hk', neg_div, neg_neg]
  unfold al
  rw [hr, round_intCast, _root_.zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))

end GlobalTheory.SemicharTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

noncomputable section

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

def dprod (L : List (ℂ × A)) : ℂ := (L.map Prod.fst).prod

def sub1 (L : List (ℂ × A)) : A := List.rec 0 (fun p L s => dprod L • p.2 + p.1 • s) L

theorem sub1_nil : sub1 ([] : List (ℂ × A)) = 0 := rfl

theorem sub1_cons (p : ℂ × A) (L : List (ℂ × A)) : sub1 (p :: L) = dprod L • p.2 + p.1 • sub1 L := rfl

theorem prod_affine (L : List (ℂ × A)) : ∃ c : ℕ → A, (∀ k, L.length < k → c k = 0) ∧
    (∀ u : ℂ, (L.map fun p => (u * p.1) • (1 : A) + p.2).prod =
      ∑ k ∈ Finset.range (L.length + 1), u ^ k • c k) ∧
    c L.length = dprod L • (1 : A) ∧ (∀ j, j + 1 = L.length → c j = sub1 L) := by
  induction L with
  | nil => exact ⟨fun k => if k = 0 then 1 else 0, fun k hk => by simp at hk; simp [Nat.pos_iff_ne_zero.1 hk],
      fun u => by simp, by simp [dprod], fun j hj => by simp at hj⟩
  | cons p L ih =>
    obtain ⟨c, hc0, hcu, hctop, hcsub⟩ := ih
    refine ⟨fun k => (if k = 0 then 0 else p.1 • c (k - 1)) + p.2 * c k, ?_, ?_, ?_, ?_⟩
    · intro k hk
      simp only [List.length_cons] at hk
      have h1 : k ≠ 0 := by omega
      simp only [h1, if_false, hc0 k (by omega), hc0 (k - 1) (by omega), smul_zero, mul_zero, add_zero]
    · intro u
      have hS1 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (if k = 0 then (0:A) else p.1 • c (k - 1)) =
          ∑ k ∈ Finset.range (L.length + 1), (u * p.1) • (u ^ k • c k) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true, smul_zero, add_zero]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_smul, smul_smul, pow_succ]; ring_nf
      have hS2 : ∑ k ∈ Finset.range (L.length + 1 + 1), u ^ k • (p.2 * c k) =
          ∑ k ∈ Finset.range (L.length + 1), p.2 * (u ^ k • c k) := by
        rw [Finset.sum_range_succ, hc0 (L.length + 1) (by omega)]
        simp [mul_smul_comm]
      simp only [List.map_cons, List.prod_cons, hcu, List.length_cons, smul_add, Finset.sum_add_distrib, hS1, hS2,
        add_mul, Finset.mul_sum, smul_mul_assoc, one_mul]
    · simp only [List.length_cons, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, hctop,
        hc0 (L.length + 1) (by omega), mul_zero, add_zero, dprod, List.map_cons, List.prod_cons, smul_smul]
    · intro j hj
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hj
      subst hj
      beta_reduce
      rw [hctop, sub1_cons]
      rcases Nat.eq_zero_or_pos L.length with h | h
      · rw [if_pos h]
        have : L = [] := List.length_eq_zero_iff.1 h
        subst this
        simp [sub1_nil, dprod]
      · rw [if_neg (by omega), hcsub _ (by omega), mul_smul_comm, mul_one, add_comm]

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem coeff_mem (S : Submodule ℂ A) (n : ℕ) (c : ℕ → A)
    (h : ∀ u : ℂ, ∑ k ∈ Finset.range (n + 1), u ^ k • c k ∈ S) (m : ℕ) (hm : m ≤ n) : c m ∈ S := by
  let v : Fin (n + 1) → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun i j hij => Fin.ext (by simpa [v] using hij)
  have hdet : IsUnit (Matrix.vandermonde v).det :=
    isUnit_iff_ne_zero.2 (Matrix.det_vandermonde_ne_zero_iff.2 hv)
  have hW : (Matrix.vandermonde v)⁻¹ * Matrix.vandermonde v = 1 := Matrix.nonsing_inv_mul _ hdet
  set W := (Matrix.vandermonde v)⁻¹
  let m' : Fin (n + 1) := ⟨m, by omega⟩
  have key : c m = ∑ j, W m' j • ∑ k ∈ Finset.range (n + 1), v j ^ k • c k := by
    calc c m = ∑ k : Fin (n + 1), (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) m' k • c k := by
          rw [Finset.sum_eq_single m']
          · simp [m']
          · intro k _ hk; rw [Matrix.one_apply_ne (Ne.symm hk), zero_smul]
          · simp
      _ = ∑ k : Fin (n + 1), (W * Matrix.vandermonde v) m' k • c k := by rw [hW]
      _ = ∑ j, W m' j • ∑ k : Fin (n + 1), v j ^ (k : ℕ) • c k := by
          simp only [Matrix.mul_apply, Matrix.vandermonde_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
          exact Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_range (fun k => v j ^ k • c k)]
  rw [key]
  exact S.sum_mem fun j _ => S.smul_mem _ (h _)

theorem sub1_ones (L : List (ℂ × A)) (h : ∀ p ∈ L, p.1 = 1) : sub1 L = (L.map Prod.snd).sum ∧ dprod L = 1 := by
  induction L with
  | nil => simp [sub1_nil, dprod]
  | cons p L ih =>
    obtain ⟨h1, h2⟩ := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    refine ⟨?_, ?_⟩
    · rw [sub1_cons, h1, h2, hp]; simp
    · simp only [dprod, List.map_cons, List.prod_cons, hp, one_mul]; exact h2

theorem dprod_eq_zero (L : List (ℂ × A)) (p : ℂ × A) (hp : p ∈ L) (h : p.1 = 0) : dprod L = 0 :=
  List.prod_eq_zero (List.mem_map.2 ⟨p, hp, h⟩)

theorem sub1_ofFn_eq_zero : ∀ (n : ℕ) (d : Fin n → ℂ) (B : Fin n → A) (k₀ k₁ : Fin n), k₀ ≠ k₁ → d k₀ = 0 →
    d k₁ = 0 → sub1 (List.ofFn fun k => (d k, B k)) = 0 := by
  intro n
  induction n with
  | zero => intro d B k₀; exact k₀.elim0
  | succ n ih =>
    intro d B k₀ k₁ hne h₀ h₁
    rw [List.ofFn_succ, sub1_cons]
    have hmem : ∀ j : Fin n, d j.succ = 0 → dprod (List.ofFn fun k : Fin n => (d k.succ, B k.succ)) = 0 :=
      fun j hj => dprod_eq_zero _ (d j.succ, B j.succ) (List.mem_ofFn.2 ⟨j, rfl⟩) hj
    induction k₀ using Fin.cases with
    | zero =>
      induction k₁ using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j₁ => simp [h₀, hmem j₁ h₁]
    | succ j₀ =>
      induction k₁ using Fin.cases with
      | zero => simp [h₁, hmem j₀ h₀]
      | succ j₁ =>
        rw [ih (fun k => d k.succ) (fun k => B k.succ) j₀ j₁ (fun e => hne (by rw [e])) h₀ h₁, hmem j₀ h₀]
        simp

end GlobalTheory.CapTrace

namespace GlobalTheory.CapTrace

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem trace_mem_of_qdet_mem {n : ℕ} (X : Fin n → Fin n → A) (S : Subalgebra ℂ A)
    (h : ∀ u : ℂ, Formalism.REAL.qdet X u ∈ S) : ∑ i, X i i ∈ S := by
  classical
  let d : Equiv.Perm (Fin n) → Fin n → ℂ := fun σ k => if σ k = k then 1 else 0
  let B : Equiv.Perm (Fin n) → Fin n → A := fun σ k =>
    (if σ k = k then algebraMap ℂ A (-((k : ℕ) : ℂ)) else 0) + X (σ k) k
  let L : Equiv.Perm (Fin n) → List (ℂ × A) := fun σ => List.ofFn fun k => (d σ k, B σ k)
  have hlen : ∀ σ, (L σ).length = n := fun σ => List.length_ofFn
  choose c hc0 hcu hctop hcsub using fun σ => prod_affine (L σ)
  have hfac : ∀ σ (u : ℂ), (List.ofFn fun k : Fin n => Formalism.REAL.Tm X (u - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod =
      ((L σ).map fun p => (u * p.1) • (1 : A) + p.2).prod := by
    intro σ u
    simp only [L, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    simp only [Function.comp_apply, Formalism.REAL.Tm, id, d, B]
    split_ifs
    · rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, mul_one, sub_eq_add_neg, add_smul]; abel
    · simp
  let C : ℕ → A := fun k => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : A) * c σ k
  have hC : ∀ u : ℂ, Formalism.REAL.qdet X u = ∑ k ∈ Finset.range (n + 1), u ^ k • C k := by
    intro u
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, hfac, hcu, hlen, C, Finset.mul_sum, Finset.smul_sum, mul_smul_comm]
    exact Finset.sum_comm
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hmem : C (n - 1) ∈ S := coeff_mem (Subalgebra.toSubmodule S) n C (fun u => by
    rw [← hC]; exact h u) (n - 1) (by omega)
  have hsub : ∀ σ, c σ (n - 1) = sub1 (L σ) := fun σ => hcsub σ _ (by rw [hlen]; omega)
  have hCeq : C (n - 1) = ∑ k : Fin n, B 1 k := by
    simp only [C, hsub]
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · rw [(sub1_ones (L 1) ?_).1]
      · simp [L, List.map_ofFn, List.sum_ofFn]
      · intro p hp
        obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
        simp [d]
    · intro σ _ hσ
      obtain ⟨k₀, hk₀⟩ : ∃ k, σ k ≠ k := by
        by_contra hc; exact hσ (Equiv.ext fun k => not_not.1 fun hk => hc ⟨k, hk⟩)
      have hk₁ : σ (σ k₀) ≠ σ k₀ := fun e => hk₀ (σ.injective e)
      rw [sub1_ofFn_eq_zero n (d σ) (B σ) k₀ (σ k₀) (Ne.symm hk₀) (by simp [d, hk₀]) (by simp [d, hk₁]), mul_zero]
    · simp
  have hB : ∀ k : Fin n, B 1 k = algebraMap ℂ A (-((k : ℕ) : ℂ)) + X k k := fun k => by simp [B]
  simp only [hCeq, hB, Finset.sum_add_distrib] at hmem
  have hs : ∑ k : Fin n, algebraMap ℂ A (-((k : ℕ) : ℂ)) ∈ S := S.sum_mem fun k _ => S.algebraMap_mem _
  simpa using S.sub_mem hmem hs

end GlobalTheory.CapTrace

namespace GlobalTheory.CuspRep

theorem Eop_add_Eop_conj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (τ : E →+* ℂ)
    (i : Fin a) : Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  simp only [Eop, atEmb_conj, map_one, Complex.conj_I, e, map_neg, smul_neg, sub_neg_eq_add]
  rw [← smul_add]
  module

end GlobalTheory.CuspRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffHolomorphicFrameChangeStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (ρ : V n → ℝ) {G₀ G₁ A : V n → Matrix r r ℂ} {v : V n}, MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → MContDiffAt 2 A v → IsUnit (A v).det → (∀ᶠ x in 𝓝 v, ∀ η, mdbar A x η = 0) → corrC ρ (fun x => (A x)ᵀ * G₀ x * (A x)ᴴᵀ) (fun x => (A x)ᵀ * G₁ x * (A x)ᴴᵀ) v = corrC ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.corrC_changeFrame | exact GlobalTheory.GoodTop.corrC_changeFrame | (intros; apply GlobalTheory.GoodTop.corrC_changeFrame <;> assumption)
end

