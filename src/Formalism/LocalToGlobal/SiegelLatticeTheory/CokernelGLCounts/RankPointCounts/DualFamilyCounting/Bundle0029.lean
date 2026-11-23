module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0017
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0028
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocDensCorank
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0026
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0027

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensCut
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical ValuativeRel

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LocSelfDual : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (p : PlF D), (L.H p).IsSelfDual (lattice₂ L p (VS D).L0)

def GaPlusDiag : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∀ p : PlF D,
          ∃ (A : Matrix (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1)) (D.s.atP p).Ep)
            (a : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1) → 𝒪[(D.s.atP p).Fp]),
            (∀ i j, A i j ∈ (M p).L.O) ∧ (∃ y ∈ (M p).L.O, A.det * y = 1) ∧
            GaPlus M δ p (Tn u) (Tn u') Z = (A.map (M p).L.cj).transpose *
              Matrix.diagonal (fun i => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (a i : (D.s.atP p).Fp)) * A ∧
            (Finset.univ.filter fun i => ϖ p ∣ a i).card =
              cJ (VS D).hT (UPair D F0 F') (MMof D F0 F') p.asIdeal

def NotIntDens : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ (L : LocSp D M) (u u' : D.what₂.Word),
    (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    ∀ (F0 : FlagG (VS D) D.R.rS (Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)),
      IsRowReps D F0 what₂ → ∀ (ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp]), (∀ p, Irreducible (ϖ p)) →
      ∀ (Z : MatZ D) (F' : LFlag (D.sp.Y 0) D.R.rS (Tn u')), F'.zt = F'.fl.z → ZhatL (lf D F0) F' = Z →
        Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (Tn u) (Tn u') Z) →
        ¬ Formalism.HermitianLatticesTheory.IsIntegralLat (VS D).hT (MMof D F0 F') → ∃ p : PlF D, densP L δ ϖ (Tn u) (Tn u') Z p = 0

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DetNeOfTotPos
section
noncomputable section

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.CntLocal
open Classical

namespace Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section D7

variable (D : Formalism.BasicNotions.D7)

theorem emb_G {T T' : ℕ} (Z : MatZ D) (φ : D.host.E →+* ℂ) :
    φ (GZ (T : D.host.E) (T' : D.host.E) Z) =
      ((Complex.normSq (φ Z.det) - (T : ℝ) * T' * Complex.normSq (φ (leadMinorE Z D.R.rS)) : ℝ) : ℂ) := by
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  have hfull : leadMinorE Z (D.R.rS + 1) = Z.det := by
    unfold leadMinorE
    rw [dite_eq_left le_rfl]
    rfl
  rw [GZ, hfull]
  simp only [map_sub, map_mul, map_natCast, hφ, Complex.mul_conj]
  push_cast
  ring

theorem det_ne_of_totPos {T T' : ℕ} (Z : MatZ D) (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (T : D.host.E) (T' : D.host.E) Z)) :
    Z.det ≠ 0 := by
  intro h0
  have : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; have h := D.R.m_le_f; have h₂ := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    omega)
  obtain ⟨τ⟩ := this
  have h1 := hP τ
  rw [emb_G D Z, Complex.ofReal_re, h0, map_zero, Complex.normSq_zero, zero_sub] at h1
  have := mul_nonneg (mul_nonneg (Nat.cast_nonneg (α := ℝ) T) (Nat.cast_nonneg (α := ℝ) T'))
    (Complex.normSq_nonneg (D.host.emb (D.eTau τ) (leadMinorE Z D.R.rS)))
  linarith

theorem inv_last (Z : MatZ D) (hdet : Z.det ≠ 0) :
    Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS) = leadMinorE Z D.R.rS / Z.det := by
  have hprev : leadMinorE Z D.R.rS = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
    unfold leadMinorE
    rw [dite_eq_left (Nat.le_succ _)]
    rfl
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply,
    PI.UnitaryGroupMassFormula.CntFormula.DetGa.det_updateRow_last_single, ← hprev,
    Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

theorem gam'_last (N' : ℕ) (Z : MatZ D) :
    Gam' N' Z (Fin.last D.R.rS) (Fin.last D.R.rS) =
      -(N' : D.host.E) * (star (Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) * Z⁻¹ (Fin.last D.R.rS) (Fin.last D.R.rS)) := by
  simp only [Gam', Gam, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, ite_and]
  simp [Finset.sum_ite_eq', Finset.sum_ite_eq, mul_ite, ite_mul]
  ring

theorem tv_star (N N' : ℕ) (Z : MatZ D) : star (tv N N' Z) = tv N N' Z := by
  rw [tv, star_add, gam'_herm, star_inv₀, star_natCast]

theorem tv_pos (hD : TotPosAll) {N N' : ℕ} (hN : 0 < N) (Z : MatZ D)
    (hP : Formalism.MainNotions.S.LocalSplitGroups.TotPos (GZ (N : D.host.E) (N' : D.host.E) Z)) :
    Formalism.HermitianLattices.Ext.L3.TotPos (tv N N' Z) := by
  have hdet := det_ne_of_totPos D Z hP
  have hGs : star (GZ (N : D.host.E) (N' : D.host.E) Z) = GZ (N : D.host.E) (N' : D.host.E) Z := by
    simp only [GZ, star_sub, star_mul, star_star, star_natCast]
    ring
  have hG := hD D _ hGs hP
  intro φ
  have hφ : ∀ a, φ (star a) = starRingEnd ℂ (φ a) := D.sp.cm.cmUnram.2.1 φ
  have h1 := hG φ
  rw [emb_G D Z, Complex.ofReal_re] at h1
  have hA : 0 < Complex.normSq (φ Z.det) := Complex.normSq_pos.2 ((map_ne_zero φ).2 hdet)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : φ (tv N N' Z) = (((N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) /
      Complex.normSq (φ Z.det)) : ℝ) : ℂ) := by
    rw [tv, gam'_last, inv_last D Z hdet]
    simp only [map_add (f := _), map_mul, map_neg, map_natCast, map_inv₀, hφ, map_div₀, star_div₀]
    rw [div_mul_div_comm, ← Complex.normSq_eq_conj_mul_self, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [ht, Complex.ofReal_re]
  have e : (N : ℝ)⁻¹ - N' * (Complex.normSq (φ (leadMinorE Z D.R.rS)) / Complex.normSq (φ Z.det)) =
      (Complex.normSq (φ Z.det) - N * N' * Complex.normSq (φ (leadMinorE Z D.R.rS))) /
        (N * Complex.normSq (φ Z.det)) := by
    field_simp
  rw [e]
  exact div_pos h1 (mul_pos hNr hA)

end D7

end Formalism.L2.SG.Pf.Cnt.R1

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.L2.SG.Pf.Cnt.R1

attribute [local instance] Formalism.BasicNotions.Host.cmStar


variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem ratPair_of (hD : TotPosAll) : RatPair := by
  intro D u u' _ F0 what₂ _ Z hP
  have hN : 0 < (D.mem u).A.T := (D.mem u).A.T_prime.pos
  obtain ⟨y, hy⟩ := dual_of_flag D hN F0
  have hdet := det_ne_of_totPos D Z hP
  obtain ⟨w0, hw0, hwt⟩ := exists_W_vec D hN hy (tv (D.mem u).A.T (D.mem u').A.T Z)
    (tv_star D _ _ Z) (tv_pos D hD hN Z hP)
  set p := pv F0.e y F0.z (D.mem u).A.T (D.mem u').A.T Z w0 with hp
  set f' : Fin (D.R.rS + 1) → (VS D).V := fun b => ∑ a, Z a b • p a with hf'
  have hfp : ∀ a a', (VS D).hT (F0.fvec a) (p a') = if a = a' then 1 else 0 :=
    fun a a' => hf_pv hy hN hw0 a a'
  have hpp : ∀ a a', (VS D).hT (p a) (p a') = Gam' (D.mem u').A.T Z a a' := hpv_pv hy hN hw0 hwt
  have hzh : ∀ a b, (VS D).hT (F0.fvec a) (f' b) = Z a b := by
    intro a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hf', map_sum, map_smul, smul_eq_mul, hfp, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  have hgr : ∀ b c, (VS D).hT (f' b) (f' c) = Gam D.host.E D.R.rS (D.mem u').A.T b c := by
    intro b c
    rw [hf', gram_comb' p Z b c]
    have h1 : Matrix.of (fun a a' => (VS D).hT (p a) (p a')) = Gam' (D.mem u').A.T Z := by
      ext a a'; simp [hpp]
    have hinv : Z⁻¹ * Z = 1 := Matrix.nonsing_inv_mul Z (isUnit_iff_ne_zero.2 hdet)
    rw [h1, Gam']
    simp only [Matrix.mul_assoc]
    rw [hinv, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hinv, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hne : ∀ d : Fin D.R.rS, Fin.castSucc d ≠ Fin.last D.R.rS := fun d => (Fin.castSucc_lt_last d).ne
  have hind : LinearIndependent D.host.E (fun d : Fin D.R.rS => f' (Fin.castSucc d)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc d
    have hv : Z.mulVec (Fin.snoc (α := fun _ => D.host.E) c 0) = 0 := by
      funext a
      have h1 := congrArg ((VS D).hT (F0.fvec a)) hc
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h1
      simp only [map_smul, smul_eq_mul, hzh] at h1
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hv
    simpa using congrFun this (Fin.castSucc d)
  let Fl : FlagG (VS D) D.R.rS (Tn u') :=
    { e := fun d => f' (Fin.castSucc d)
      z := f' (Fin.last D.R.rS)
      e_indep := hind
      e_iso := fun a b => by rw [hgr]; simp [Gam, hne]
      z_orth := fun a => by rw [hgr]; simp [Gam, hne]
      z_norm := by rw [hgr]; simp [Gam, Tn] }
  refine ⟨⟨Fl, f' (Fin.last D.R.rS)⟩, rfl, ?_⟩
  funext a b
  have hfv : Fl.fvec b = f' b := by
    induction b using Fin.lastCases with
    | last => simp [FlagG.fvec, Fl]
    | cast b => simp [FlagG.fvec, Fl]
  show brS (VS D) (Fl.fvec b) (F0.fvec a) = Z a b
  rw [brS, hfv, hzh]

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsTotPosCongr
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_totPos_congr {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hne : 𝔭 ≠ ⊥) (a : 𝓞 F) (k : ℕ) :
    ∃ x : F, TotPos (algebraMap F K x) ∧ InP 𝔭 k (algebraMap F K ((a : F) + x)) := by
  have := h𝔭.isPrime
  have ht0 : Ideal.absNorm (𝔭 ^ k) ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact pow_ne_zero _ hne
  have htm : ((Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := Ideal.absNorm_mem _
  obtain ⟨N, hN⟩ := exists_nat_gt (∑ φ : K →+* ℂ, ‖φ (algebraMap F K (a : F))‖)
  have hz : ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) ∈ 𝔭 ^ k := by
    rw [Nat.cast_mul]; exact Ideal.mul_mem_left _ _ htm
  have hzF : (((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) = ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : F) := by
    simp
  refine ⟨(((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : 𝓞 F) : F) - (a : F), ?_, ?_⟩
  · intro φ
    rw [hzF, map_sub, map_sub, map_natCast, map_natCast, Complex.sub_re, Complex.natCast_re]
    have h1 : (φ (algebraMap F K (a : F))).re ≤ ∑ ψ : K →+* ℂ, ‖ψ (algebraMap F K (a : F))‖ :=
      (Complex.re_le_norm _).trans (Finset.single_le_sum
        (f := fun ψ : K →+* ℂ => ‖ψ (algebraMap F K (a : F))‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ φ))
    have h2 : (N : ℝ) ≤ ((N * Ideal.absNorm (𝔭 ^ k) : ℕ) : ℝ) := by
      push_cast
      exact le_mul_of_one_le_right (Nat.cast_nonneg _)
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 ht0)
    linarith
  · rw [add_sub_cancel]
    exact inP_of_mem_pow hz

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FamilyGramHolds
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

theorem family_gram_holds : FamGram := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUc M hM hMi 𝔭 h𝔭 b a hba π w c τ hg
  have := h𝔭.isPrime
  obtain ⟨hbU, -, hbo, hbn, ha0⟩ := hba
  obtain ⟨hwW, hwo, hwn, hτ, ⟨s₀, hu⟩, hcong, hunit⟩ := hg
  have hwn1 : ∀ j, h (w j) (w j) = algebraMap F K (c j) := fun j => (hwn j).1
  have hbw : ∀ i j, h (b i) (w j) = 0 := fun i j =>
    LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (hwW j) (b i)) (hbU i))
  have hwb : ∀ i j, h (w j) (b i) = 0 := fun i j => by
    rw [← hs.eq (b i) (w j), hbw]; simp
  have hcP : ∀ i, vF 𝔭 (a i) ≠ 0 → InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K (c (τ i))) := by
    intro i hi
    have h1 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : F) + c (τ i))) :=
      (hcong i hi).mono (by omega)
    have h2 : InP 𝔭 (vF 𝔭 (a i)) (algebraMap F K ((a i : 𝓞 F) : F)) := inP_vF h𝔭 (ha0 i)
    have e : algebraMap F K (c (τ i)) =
        algebraMap F K ((a i : F) + c (τ i)) + -algebraMap F K ((a i : 𝓞 F) : F) := by
      rw [map_add (f := _)]; ring
    rw [e]; exact h1.add h2.neg
  have hcS : ∀ j, algebraMap F K (c j) ∈ SP K 𝔭 := by
    intro j
    by_cases hj : ∃ i, vF 𝔭 (a i) ≠ 0 ∧ τ i = j
    · obtain ⟨i, hi, rfl⟩ := hj
      exact (hcP i hi).mem_SP
    · push Not at hj
      exact (hunit j fun i hi => hj i hi).1
  have haS : ∀ i, algebraMap F K ((a i : 𝓞 F) : F) ∈ SP K 𝔭 := fun i => by
    rw [← jι_eq']; exact jK_mem_SP _
  have key_ii : ∀ i, h (b i + w (τ i)) (b i + w (τ i)) = algebraMap F K ((a i : F) + c (τ i)) := by
    intro i
    simp only [map_add (f := _), LinearMap.add_apply, hbw, hwb, hbn, hwn1]
    ring
  have key_ik : ∀ i k, i ≠ k → vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 →
      h (b i + w (τ i)) (b k + w (τ k)) = 0 := by
    intro i k hik hi hk
    have hτik : τ i ≠ τ k := fun e => hik (hτ i k hi hk e)
    simp only [map_add (f := _), LinearMap.add_apply, hbw, hwb, hbo i k hik, hwo _ _ hτik]
    ring
  suffices H : ∀ x y, h (glueFam K 𝔭 b a π w τ x) (glueFam K 𝔭 b a π w τ y) ∈ SP K 𝔭 by
    intro x y; rw [← mem_SP_iff_locF]; exact H x y
  rintro (i | j) (k | l)
  · simp only [glueFam, Sum.elim_inl]
    by_cases hik : i = k
    · subst hik
      by_cases hi : vF 𝔭 (a i) = 0
      · rw [if_pos hi, hbn]; exact haS i
      · rw [if_neg hi, form_smul_smul, key_ii i, star_inv_pow hF, ← pow_add, ← two_mul]
        exact mem_SP_of_inP hu (hcong i hi)
    · by_cases hi : vF 𝔭 (a i) = 0 <;> by_cases hk : vF 𝔭 (a k) = 0
      · rw [if_pos hi, if_pos hk, hbo i k hik]; exact (SP K 𝔭).zero_mem
      · rw [if_pos hi, if_neg hk, form_smul_right, map_add (f := _), hbo i k hik, hbw, add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_pos hk, form_smul_left, map_add (f := _), LinearMap.add_apply, hbo i k hik, hwb,
          add_zero, mul_zero]
        exact (SP K 𝔭).zero_mem
      · rw [if_neg hi, if_neg hk, form_smul_smul, key_ik i k hik hi hk, mul_zero]
        exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hi : vF 𝔭 (a i) = 0
    · rw [if_pos hi, hbw]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hi, form_smul_left, map_add (f := _), LinearMap.add_apply, hbw, zero_add, star_inv_pow hF]
      by_cases hj : τ i = l
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP i hi)
      · rw [hwo _ _ hj, mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inl, Sum.elim_inr]
    by_cases hk : vF 𝔭 (a k) = 0
    · rw [if_pos hk, hwb]; exact (SP K 𝔭).zero_mem
    · rw [if_neg hk, form_smul_right, map_add (f := _), hwb, zero_add]
      by_cases hj : τ k = j
      · subst hj; rw [hwn1]; exact mem_SP_of_inP hu (hcP k hk)
      · rw [hwo _ _ (Ne.symm hj), mul_zero]; exact (SP K 𝔭).zero_mem
  · simp only [glueFam, Sum.elim_inr]
    by_cases hjl : j = l
    · subst hjl; rw [hwn1]; exact hcS j
    · rw [hwo _ _ hjl]; exact (SP K 𝔭).zero_mem

end Formalism.L2.SG.Pf.GluingBases
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormMemOfDual
section
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalProjections

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G6

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {hc : IsCompl U (orthK h U)}
  {M T Λ Λ₀ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}

theorem h_UW {x y : V} (hx : x ∈ U) (hy : y ∈ orthK h U) : h x y = 0 := by
  simp only [orthK, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact hy x hx

theorem h_WU (hs : h.IsSymm) {x y : V} (hx : x ∈ orthK h U) (hy : y ∈ U) : h x y = 0 := by
  rw [← LinearMap.isSymm_def.1 hs y x, h_UW hy hx, map_zero]

theorem prO_of_mem_U {hc' : IsCompl U (orthK h U)} {x : V} (hx : x ∈ U) : prO hc' x = x := by
  have e := prO_add hc' x
  rw [prO_symm_of_mem_U (hc' := hc') hx, add_zero] at e
  exact e

theorem split (hs : h.IsSymm) (hc' : IsCompl U (orthK h U)) (x y : V) :
    h x y = h (prO hc' x) (prO hc' y) + h (prO hc'.symm x) (prO hc'.symm y) := by
  conv_lhs => rw [← prO_add hc' x, ← prO_add hc' y]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [h_UW (prO_mem hc' x) (prO_symm_mem hc' y), h_WU hs (prO_symm_mem hc' x) (prO_mem hc' y)]
  ring

theorem form_mem_of_dual (hd : dualF h 𝔭 Λ = Λ) {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    h a b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  have hb' : b ∈ dualF h 𝔭 Λ := by rw [hd]; exact hb
  exact hb' a ha

theorem mem_T_of (hG : Good hc M T 𝔭 Λ) (hd : dualF h 𝔭 Λ = Λ) {b : V} (hb : b ∈ orthK h U)
    (H : ∀ b' ∈ locF 𝔭 (dualIn h (orthK h U) T), h b' b ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) :
    b ∈ locF 𝔭 T := by
  have hbΛ : b ∈ Λ := by
    rw [← hd]
    intro y hy
    rw [← prO_add hc y, map_add (f := _), LinearMap.add_apply, h_UW (prO_mem hc y) hb, zero_add]
    exact H _ (hG.iW y hy)
  rw [← hG.cW]
  exact Submodule.mem_inf.2 ⟨hbΛ, hb⟩

def FP (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)) : Prop :=
  ∀ x y x' y' : ↥(locF 𝔭 (dualIn h (orthK h U) T)),
    Submodule.Quotient.mk x' = P (Submodule.Quotient.mk x) →
    Submodule.Quotient.mk y' = P (Submodule.Quotient.mk y) →
    h (x' : V) (y' : V) - h (x : V) (y : V) ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

theorem FP.injective (hG : Good hc M T 𝔭 Λ) (hd : dualF h 𝔭 Λ = Λ)
    {P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)} (hP : FP P) : Function.Injective P := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨z, -, hz⟩ := hG.oW (x : V) x.2
  have hxW : (x : V) ∈ orthK h U := hz ▸ prO_symm_mem hc z
  have H : ∀ b' ∈ locF 𝔭 (dualIn h (orthK h U) T), h b' x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro b' hb'
    obtain ⟨b'', hb''⟩ := Submodule.Quotient.mk_surjective _ (P (Submodule.Quotient.mk ⟨b', hb'⟩))
    have e := hP ⟨b', hb'⟩ x b'' 0 hb'' (by rw [hq, Submodule.Quotient.mk_zero])
    simpa using e
  have hxT := mem_T_of hG hd hxW H
  rw [← Submodule.Quotient.mk_zero, mk_eq_iff]
  simpa using hxT

theorem fp_of (hs : h.IsSymm) (hd₀ : dualF h 𝔭 Λ₀ = Λ₀) (hd : dualF h 𝔭 Λ = Λ)
    (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭))
    (H : ∀ b x' : ↥(locF 𝔭 (dualIn h (orthK h U) T)),
      Submodule.Quotient.mk x' = P (Submodule.Quotient.mk b) →
      ∃ z ∈ Λ₀, ∃ w ∈ Λ, prO hc.symm z = b ∧ prO hc.symm w = x' ∧ prO hc z = prO hc w) : FP P := by
  intro x y x' y' hx hy
  obtain ⟨z₁, hz₁, w₁, hw₁, hq₁, hq₁', hp₁⟩ := H x x' hx
  obtain ⟨z₂, hz₂, w₂, hw₂, hq₂, hq₂', hp₂⟩ := H y y' hy
  have e₁ := split hs hc w₁ w₂
  have e₂ := split hs hc z₁ z₂
  rw [hq₁', hq₂', ← hp₁, ← hp₂] at e₁
  rw [hq₁, hq₂] at e₂
  have e : h (x' : V) (y' : V) - h (x : V) (y : V) = h w₁ w₂ - h z₁ z₂ := by
    rw [e₁, e₂]
    ring
  rw [e]
  exact sub_mem (form_mem_of_dual hd hw₁ hw₂) (form_mem_of_dual hd₀ hz₁ hz₂)

def glue (hc' : IsCompl U (orthK h U)) (T : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (Λ₀ : Submodule (𝓞 K) V) (P : Module.End (𝓞 K) (DiscMod h (orthK h U) T 𝔭)) :
    Submodule (𝓞 K) V where
  carrier := {x | ∃ b : ↥(locF 𝔭 (dualIn h (orthK h U) T)), (b : V) = prO hc'.symm x ∧
    ∃ y ∈ Λ₀, ∃ c : ↥(locF 𝔭 (dualIn h (orthK h U) T)), (c : V) = prO hc'.symm y ∧
      prO hc' y = prO hc' x ∧ Submodule.Quotient.mk b = P (Submodule.Quotient.mk c)}
  zero_mem' := ⟨0, by simp, 0, Λ₀.zero_mem, 0, by simp, by simp, by simp⟩
  add_mem' := by
    rintro x x' ⟨b, hb, y, hy, c, hcy, hU, hP⟩ ⟨b', hb', y', hy', c', hcy', hU', hP'⟩
    refine ⟨b + b', by simp [hb, hb'], y + y', Λ₀.add_mem hy hy', c + c', by simp [hcy, hcy'],
      by simp [hU, hU'], ?_⟩
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, map_add (f := _), hP, hP']
  smul_mem' := by
    rintro r x ⟨b, hb, y, hy, c, hcy, hU, hP⟩
    refine ⟨r • b, by simp [hb], r • y, Λ₀.smul_mem r hy, r • c, by simp [hcy], by simp [hU], ?_⟩
    rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul, map_smul, hP]

end Formalism.L2.SG.Pf.OrthogonalProjections
end
end

