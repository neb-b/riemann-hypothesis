module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0970
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardKerSubspacesAndHeckePolyOfConvolution
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIntertwinerValuesSobolevContinuous
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingReindex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0364

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepDiagonalCoordinatesMemComplementIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct BigOperators
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF GlobalTheory.XCharBF.DiagCoord
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {F : Frames G}, Std F →
    ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m)
      (u : WO (negSp (G.V (.grid (2 * ρ + 2) 0))) (G.V (.grid (2 * ρ + 1) 0))),
    u ∈ latO _ _ (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) →
    ∀ p : Fin ρ, ((F.dJ ρ h).pY * u * (F.dB ρ h).jY) p p ∈ complId (D.host.AA * G.pl.stAbar sc) := by
  intro D T L sc G F hF ρ h u hu p
  have rat_tmul_entry {m n k l : ℕ} (q : Matrix (Fin k) (Fin m) D.host.E)
      (C : Matrix (Fin m) (Fin n) D.host.E)
      (e : Matrix (Fin n) (Fin l) D.host.E) (X : AF D.host.F) (p : Fin k) (p' : Fin l) :
      (rat q * (Matrix.of fun i j => X ⊗ₜ[D.host.F] C i j : Mx D m n) * rat e) p p' = X ⊗ₜ[D.host.F] (q * C * e) p p' := by
    have hinc : ∀ x, incA D x = (1 : AF D.host.F) ⊗ₜ[D.host.F] x := fun _ => rfl
    simp only [Matrix.mul_apply, rat, Matrix.map_apply, Matrix.of_apply, hinc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, ← TensorProduct.tmul_sum]
  obtain ⟨hcJ, heJ, -⟩ := hF.hJ ρ h
  obtain ⟨hcB, heB, sB, he'B⟩ := hF.hB ρ h
  set aJ := G.colDec (2 * ρ + 1) (by omega) (by omega) with haJ
  set aB := G.colDec (2 * ρ + 2) (by omega) h with haB
  obtain ⟨hAA, -⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).1
  obtain ⟨hA, hconj⟩ := (GlobalTheory.ChiGrid.StairConj.conj_AA_and_stA D).2 T L G.pl sc
  have hAb : G.pl.stAbar sc ≠ 0 := by
    intro h0
    apply hA
    rw [FractionalIdeal.eq_zero_iff] at h0 ⊢
    intro y hy
    have h1 : star y ∈ G.pl.stAbar sc := (hconj _).2 (by rwa [star_star])
    have h2 := h0 _ h1
    rwa [star_eq_zero] at h2

  have hJ : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((F.dJ ρ h).qY *ᵥ t) p =
      star ((-D.host.xi0) ^ (p.1 + 1)) * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) := by
    intro t _
    simp only [HypDec.qY, heJ, mulVec, dotProduct, Matrix.mul_apply, conjTranspose_apply, colsOf, star_mul', Finset.mul_sum,
      Finset.sum_mul, mul_assoc]
  have hJmem : ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0), ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) ∈
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p).rev := by
    intro t ht
    have ht' : t ∈ aJ.lat (G.sp.P (2 * ρ + 1)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := by
      rw [haJ, ← G.sp.colLat (2 * ρ + 1) (by omega) (by omega)]; exact ht
    exact auxiliaryCoordinate_mem_staircaseIdeal aJ _ _ ht' _ (by simp only [Fin.val_castLE]; omega)

  have hBmem : ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0),
      star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev) ∈
      (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)⁻¹ := by
    intro s hs
    have hs' : s ∈ aB.lat (G.sp.P (2 * ρ + 2)).lat (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 2 - 1)) := by
      rw [haB, ← G.sp.colLat (2 * ρ + 2) (by omega) h]; exact hs
    have h1 := auxiliaryCoordinate_mem_staircaseIdeal aB _ _ hs' (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
      (by simp only [Fin.val_rev, Fin.val_castLE]; omega)
    exact ((GlobalTheory.ChiGrid.stairId_ne_zero_and_mem_rev_iff D _ _ hA hconj _ _).2 _).1 h1

  have hsc : star ((-D.host.xi0) ^ (p.1 + 1)) * sB p = 1 := by
    have h1 := congrFun (congrFun (F.dB ρ h).e'e p) p
    rw [he'B, heB, colsOf_gram, Matrix.one_apply_eq] at h1
    have h2 : (aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev
        (Fin.castLE (by omega) p) = 1 := by
      rw [show aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram * aB.a = antiDiagonalSignGramMatrix (2 * ρ + 2 - 1) (-1) from aB.gram]
      simp only [antiDiagonalSignGramMatrix, Fin.val_rev, Fin.val_castLE]
      rw [ite_eq_left (by omega), ite_eq_right (fun e => by rw [Fin.ext_iff, Fin.val_rev, Fin.val_castLE] at e; omega)]
    rw [h2, mul_one] at h1
    have h3 := congrArg star h1
    rw [star_mul', star_star, star_one] at h3
    rw [mul_comm]; exact h3
  have hGB : ∀ i j, star ((G.V (.grid (2 * ρ + 2) 0)).gram j i) = (G.V (.grid (2 * ρ + 2) 0)).gram i j := fun i j =>
    (G.V (.grid (2 * ρ + 2) 0)).herm.eq ((G.V (.grid (2 * ρ + 2) 0)).frame j) ((G.V (.grid (2 * ρ + 2) 0)).frame i)

  have keyE : ∀ a ∈ D.host.AA, ∀ s ∈ G.Λ (.grid (2 * ρ + 2) 0), ∀ t ∈ G.Λ (.grid (2 * ρ + 1) 0),
      ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) *
        (F.dB ρ h).e') p p ∈ D.host.AA * G.pl.stAbar sc := by
    intro a ha s hs t ht
    rw [entry_rankOne _ _ a t (fun j => ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j), hJ t ht, he'B,
      negSp_gram, negPair_colsOf _ hGB]
    have e : a * (star ((-D.host.xi0) ^ (p.1 + 1)) *
          ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p)) *
        -(sB p * star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev)) =
        -(a * (((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) := by
      linear_combination (-(a * ((aJ.aᴴ * (G.V (.grid (2 * ρ + 1) 0)).gram) *ᵥ t) (Fin.castLE (by omega) p) *
          star (((aB.aᴴ * (G.V (.grid (2 * ρ + 2) 0)).gram) *ᵥ s) (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev))) * hsc
    rw [e]
    refine Submodule.neg_mem _ (FractionalIdeal.mul_mem_mul ha ?_)
    rw [← stairId_mul_inv_succ (G.pl.stA sc) (G.pl.stAbar sc) hA hAb (Fin.castLE (by omega) p : Fin (2 * ρ + 1 - 1)).rev
      (Fin.castLE (by omega) p : Fin (2 * ρ + 2 - 1)).rev (by omega) (by simp only [Fin.val_rev, Fin.val_castLE]; omega)]
    exact FractionalIdeal.mul_mem_mul (hJmem t ht) (hBmem s hs)
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ((F.dJ ρ h).pY * (Matrix.of fun i j => (pairA D.host.F 0 α) ⊗ₜ[D.host.F]
        (a * t i * ∑ k, star (s k) * (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j)) * (F.dB ρ h).jY) p p =
        (pairA D.host.F 0 α) ⊗ₜ[D.host.F] ((F.dJ ρ h).qY * Matrix.of (fun i j => a * t i * ∑ k, star (s k) *
          (negSp (G.V (.grid (2 * ρ + 2) 0))).gram k j) * (F.dB ρ h).e') p p :=
      rat_tmul_entry _ _ _ _ _ _
    rw [key]
    exact tmul_mem_complId hα (keyE a ha s hs t ht)
  | zero => simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]; exact neg_mem hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateDatumLiftJointEigenspaceIntoOnePart
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjScalar.LiftPart
open GlobalTheory.Hk3

theorem tri_solve {X : Type} [AddCommGroup X] [Module ℂ X] (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) (m : ℕ) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X), (∀ k, k < m → ∑ j ∈ Finset.range (k + 1), z k j • T j = α k • F) →
      ∀ k, k < m → T k = β k • F := by
  induction m with
  | zero => exact ⟨0, fun _ _ _ k hk => absurd hk (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨β, hβ⟩ := ih
    refine ⟨Function.update β m ((z m m)⁻¹ * (α m - ∑ j ∈ Finset.range m, z m j * β j)), fun F T h k hk => ?_⟩
    have hlow : ∀ k, k < m → T k = β k • F := hβ F T fun k hk => h k (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
    · rw [Function.update_of_ne (by omega)]
      exact hlow k hk
    · rw [Function.update_self]
      have e := h k (by omega)
      rw [Finset.sum_range_succ] at e
      have e2 : ∑ j ∈ Finset.range k, z k j • T j = (∑ j ∈ Finset.range k, z k j * β j) • F := by
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun j hj => by rw [hlow j (Finset.mem_range.1 hj), smul_smul]
      rw [e2] at e
      have e3 : z k k • T k = (α k - ∑ j ∈ Finset.range k, z k j * β j) • F := by
        rw [sub_smul, ← e]; abel
      rw [mul_smul, ← e3, smul_smul, inv_mul_cancel₀ (hz k), one_smul]

variable {D : D7}

theorem rep_of_not {V : HSp D} {P : Pl D.host.E} {d : List ℤ} (h : ¬ IsLab V P d) : GlobalTheory.Hk3.rep V P d = ∅ := by
  unfold GlobalTheory.Hk3.rep; rw [dite_eq_right h]

theorem hkF_evC (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (a : List ℤ → ℂ)
    (Φ : Bridge.Gf V → W) (h : ∀ d, IsLab V P d → hkF V P (Finsupp.single d 1) Φ = a d • Φ) (c : List ℤ →₀ ℂ) :
    hkF V P c Φ = evC V P a c • Φ := by
  classical
  funext g
  have e : ∀ d, ∑ γ ∈ GlobalTheory.Hk3.rep V P d, Φ (g * (finHom V).rangeRestrict γ) = (if IsLab V P d then a d else 0) • Φ g := by
    intro d
    by_cases hd : IsLab V P d
    · have := congrFun (h d hd) g
      unfold hkF at this
      rw [Finsupp.sum_single_index (by simp), one_smul] at this
      rw [if_pos hd, this]; rfl
    · rw [if_neg hd, rep_of_not hd, Finset.sum_empty, zero_smul]
  simp only [hkF, evC, Finsupp.sum, Pi.smul_apply, Finset.sum_smul, e, smul_smul]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

theorem hk_splitC (V : HSp D) (P : Pl D.host.E) (n : ℕ) (z : ℕ → ℂ) :
    hk V P (splitC n z) = ∑ j ∈ Finset.range (n + 1), z j • hk V P (Finsupp.single (splitLab n j) 1) := by
  unfold splitC hk
  rw [← Finsupp.sum_finsetSum_index (by simp) (by simp [add_smul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp), one_smul]

theorem postOn_sum {V : HSp D} {S : _} (M : DSModel V S) (s : Finset ℕ) (w : ℕ → ℂ)
    (L : ℕ → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (T : MMap M) :
    postOn M (∑ j ∈ s, w j • L j) T = ∑ j ∈ s, w j • postOn M (L j) T := by
  ext v
  simp [postOn]

theorem tri_solve' {X : Type} [AddCommGroup X] [Module ℂ X] (n : ℕ) (z : ℕ → ℕ → ℂ) (α : ℕ → ℂ) (hz : ∀ k, z k k ≠ 0) :
    ∃ β : ℕ → ℂ, ∀ (F : X) (T : ℕ → X),
      (∀ k, k ≤ n → α k • F = ∑ j ∈ Finset.range (n + 1), (if j ≤ k then z k j else 0) • T j) →
      ∀ k, k ≤ n → T k = β k • F := by
  obtain ⟨β, hβ⟩ := tri_solve (X := X) z α hz (n + 1)
  refine ⟨β, fun F T h k hk => hβ F T (fun k' hk' => ?_) k (by omega)⟩
  rw [h k' (by omega)]
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun j hj hj' => ?_)
  · rw [Finset.mem_range] at hj
    rw [if_pos (by omega)]
  · rw [Finset.mem_range] at hj hj'
    rw [if_neg (by omega), zero_smul]

theorem exists_split_data {P : Pl D.host.E} (hc : Formalism.DivisionValues.conjPl P ≠ P) : ∃ (e : AE D) (ϖ : 𝓞 D.host.E) (x : (AE D)ˣ),
    Formalism.L2.NTheta.IsIdemAt e P ∧ ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 ∧ (x : AE D) = e * incA D (ϖ : D.host.E) + (1 - e) := by
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt hc
  obtain ⟨ϖ, h1, h2⟩ : ∃ ϖ ∈ P.asIdeal, ϖ ∉ P.asIdeal ^ 2 :=
    SetLike.exists_of_lt (Ideal.pow_lt_self _ P.ne_bot P.isPrime.ne_top 2 le_rfl)
  have h0 : (ϖ : D.host.E) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 fun h => h2 (h ▸ zero_mem _)
  exact ⟨e, ϖ, Formalism.L2.JoinChr.locU he.1.1 (Units.mk0 _ h0), he, h1, h2, by
    rw [Formalism.L2.JoinChr.locU_val, Formalism.L2.JoinChr.locE, Units.val_mk0]; ring⟩

theorem diag_ne_zero (P : Pl D.host.E) (χS χT : (AE D)ˣ →* Circle) (x : (AE D)ˣ) (nS nT t k : ℕ) :
    (Ideal.absNorm P.asIdeal : ℂ) ^ ((nT - k) * (k - k)) * (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) t (k - k) : ℂ) *
      ((χT x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nT)⁻¹ ^ k *
      ((χS x : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ nS) ^ k ≠ 0 := by
  have hq0 : Ideal.absNorm P.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  have hs0 : (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_ne_zero'.2 (by exact_mod_cast Nat.pos_of_ne_zero hq0))
  have hT : (χT x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hS : (χS x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  rw [Nat.sub_self, mul_zero, pow_zero, one_mul, GlobalTheory.KerRangeCount.gaussBin_zero_right, Nat.cast_one, one_mul]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (mul_ne_zero hT (pow_ne_zero _ hs0))))
    (pow_ne_zero _ (mul_ne_zero hS (pow_ne_zero _ hs0)))

theorem dualC_dualC' (c : List ℤ →₀ ℂ) : dualC (dualC c) = c := by
  unfold dualC
  rw [← Finsupp.mapDomain_comp]
  have : dualLab ∘ dualLab = id := by
    funext d
    simp [dualLab, List.map_reverse]
  rw [this, Finsupp.mapDomain_id]

section Loc

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) {c : CoefA (Vc D i)}
  {H : HMod (Bridge.Gf (Vc D i) → c.W)} (th : H.H →ₗ[ℂ] (R.HW i σ).H) (μ' η' : (AE D)ˣ →* Circle)
  (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ)) (P : Pl D.host.E)
  (a : Pl D.host.E → List ℤ → ℂ)


set_option maxHeartbeats 2000000 in
theorem loc_inert (hHowe : HoweUnram) (hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) (hP : Good R A.μ0 P)
    (hvac : VacFix R.ψ ω P) (hc : Formalism.DivisionValues.conjPl P = P)
    (step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
      (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y))) (d : List ℤ) :
    ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
  have hsc := _root_.GlobalTheory.Hk3.CorrInert.sphCorr_of_inert hHowe R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω P hW hc hvac
  have hcorr := hsc.2.1
  obtain ⟨cS, hM⟩ := hcorr (Finsupp.single d 1)
  refine ⟨evC (Vc D i) P (a P) (dualC cS), fun u hu => ?_⟩
  have hM' : Match R.ψ ω P (dualC (dualC cS)) (Finsupp.single d 1) := by rwa [dualC_dualC']
  have hy : H.e (evC (Vc D i) P (a P) (dualC cS) • u) = hkF (Vc D i) P (dualC cS) (H.e u) := by
    rw [map_smul, hkF_evC (Vc D i) P (a P) (H.e u) (fun d' hd' => hu P d' hP (Or.inr ⟨hc, hd'⟩))]
  have := step (dualC cS) (Finsupp.single d 1) hM' u _ hy
  rw [map_smul, map_smul] at this
  exact this.symm


set_option maxHeartbeats 2000000 in
theorem loc_split (hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω) (hP : Good R A.μ0 P)
    (hu1 : UnrPl P μ') (hu2 : UnrPl P (μ' * η'⁻¹)) (hc : Formalism.DivisionValues.conjPl P ≠ P)
    (step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
      (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y))) (d : List ℤ)
    (hd : RelLab (Wc D i) P d) :
    ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
  have hd' : ∃ k, k ≤ (Wc D i).rank ∧ d = splitLab (Wc D i).rank k := by
    rcases hd with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hc
  obtain ⟨k, hkr, rfl⟩ := hd'
  have hdat := exists_split_data hc
  obtain ⟨e, ϖ, x, he, h1, h2, hx⟩ := hdat
  have hrk : (Vc D i).rank = (Wc D i).rank + D.R.t := by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2, rank_Wc]; rfl
  have hms0 := GlobalTheory.Hk3.SplitMatch.match_split R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω P hW hc hu1 hu2
  have hms := (hms0.2 e ϖ x D.R.t he h1 h2 hx).2 hrk
  have htri := tri_solve' (X := MMap (R.MW i σ)) (Wc D i).rank
    (fun k j => (Ideal.absNorm P.asIdeal : ℂ) ^ (((Wc D i).rank - j) * (k - j)) *
      (Formalism.L2.Col.gaussBin (Ideal.absNorm P.asIdeal) D.R.t (k - j) : ℂ) *
      ((((μ' * η'⁻¹) x : Circle) : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Wc D i).rank)⁻¹ ^ k *
      (((μ' x : Circle) : ℂ) * (Real.sqrt (Ideal.absNorm P.asIdeal) : ℂ) ^ (Vc D i).rank) ^ j)
    (fun k => a P (splitLab (Vc D i).rank k))
    (fun k => diag_ne_zero P μ' (μ' * η'⁻¹) x (Vc D i).rank (Wc D i).rank D.R.t k)
  obtain ⟨β, hβ⟩ := htri
  refine ⟨β k, fun u hu => hβ ((R.HW i σ).e (th u))
    (fun j => postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single (splitLab (Wc D i).rank j) 1)) ((R.HW i σ).e (th u)))
    (fun k' hk' => ?_) k hkr⟩
  have hy : H.e (a P (splitLab (Vc D i).rank k') • u) =
      hkF (Vc D i) P (Finsupp.single (splitLab (Vc D i).rank k') 1) (H.e u) := by
    rw [map_smul, hu P _ hP (Or.inl ⟨hc, k', by omega, rfl⟩)]
  have := step _ _ (hms k' (by omega)) u _ hy
  rw [map_smul, map_smul, hk_splitC, postOn_sum] at this
  exact this

end Loc


set_option maxHeartbeats 4000000 in
theorem lift_eig_mem_part : GlobalTheory.Hk3.HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ gramR c0R c0L, GlobalTheory.GalLift.Comparison₂ R gramR c0R c0L → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) (H : HMod (Bridge.Gf (Vc D i) → c.W)) (j : A.fam.amb.FL i A.μ0 →ₛₗ[σ] H.H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK σ → ∀ (μ' η' : (AE D)ˣ →* Circle) (th : H.H →ₗ[ℂ] (R.HW i σ).H), GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.IsConjDatum R i σ (c0L i) μ' η' c c₁ H j th → GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.HypConj R i σ μ' η' → ∀ a : Pl D.host.E → List ℤ → ℂ, ∃ ev, ∀ u : H.H, GlobalTheory.ConjScalar.EigF R i a (H.e u) → th u ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  intro hHowe D G _ _ Pl0 T0 A Ks _ _ _ R F hC gramR c0R c0L tie i σ c c₁ H j hK μ' η' th hD hyp a
  have hforms := hD.2.2.1
  have hlift := hD.2.2.2
  have h2 := (GlobalTheory.GalLift.isConjLift_iff R i σ μ' η' c H th).1 hlift
  obtain ⟨ω, f₀, f, B, io, thP, hh⟩ := h2
  have hLD := hh.1
  have hproj := hh.2
  have hW : IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω := hLD.1
  have hVec : GlobalTheory.GalLift.VecData R i σ f₀ f B := hLD.2.1
  have loc : ∀ P, Good R A.μ0 P → ∀ d, RelLab (Wc D i) P d → ∃ z : ℂ, ∀ u : H.H, EigF R i a (H.e u) →
      postOn (R.MW i σ) (hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e (th u)) = z • (R.HW i σ).e (th u) := by
    intro P hP d hd
    have h38 := _root_.GlobalTheory.ConjVacFix.unr_and_vacFix R F hC i σ μ' η' hyp ω hW f₀ f B hVec P hP
    obtain ⟨hu1, hu2, hvac⟩ := h38
    have step : ∀ cV cW, Match R.ψ ω P (dualC cV) cW → ∀ y y' : H.H, H.e y' = hkF (Vc D i) P cV (H.e y) →
        (R.HW i σ).e (th y') = postOn (R.MW i σ) (hk (Wc D i) P cW) ((R.HW i σ).e (th y)) :=
      GlobalTheory.T.conjugate_theta_lift_matched_hecke_combination R F hC gramR c0R c0L tie i σ c c₁ H j hK hforms μ' η' th ω f₀ f B io thP hLD hproj P hP hvac
    by_cases hc : Formalism.DivisionValues.conjPl P = P
    · exact loc_inert R i σ th μ' η' ω P a hHowe hW hP hvac hc step d
    · exact loc_split R i σ th μ' η' ω P a hW hP hu1 hu2 hc step d hd
  classical
  let b : Pl D.host.E → List ℤ → ℂ := fun P d =>
    if h : Good R A.μ0 P ∧ RelLab (Wc D i) P d then (loc P h.1 d h.2).choose else 0
  obtain ⟨ev, hev⟩ := _root_.GlobalTheory.ConjScalar.OnePart.mem_one_part R hC.lev hC.models.HW i σ b
  refine ⟨ev, fun u hu => hev (th u) fun P d hP hd => ?_⟩
  simp only [b, dif_pos (And.intro hP hd)]
  exact (loc P hP d hd).choose_spec u hu

end GlobalTheory.ConjScalar.LiftPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerValuesSmoothAutomorphic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjAutSmooth

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) : castGA e x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst e; rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    {γ : GA D (D.sp.Y 0)} (hγ : γ ∈ GQ (D.sp.Y 0)) : iotaX X h γ ∈ X.B.I.GFset := by
  show castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D γ) ∈ X.B.I.GFset
  rw [castGA_mem]
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D γ).1 hγ


set_option maxHeartbeats 1000000 in
theorem conjMap_isAutFunSm : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsAutFunSm R.θ (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u
  set Ψ := GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t with hΨ
  have hθ : IsInfFam R.θ := hMod.inf
  have he : GlobalTheory.RepSmooth.IsEquiv R.θ Ψ := fun τ g hg v w hw =>
    _root_.GlobalTheory.ConjEquivReal.conjMap_update_real hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ g hg v w hw
  have hs : GlobalTheory.RepSmooth.IsSob Ψ := fun τ v x =>
    _root_.GlobalTheory.ConjRowCont.conjMap_sobCont hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep τ v x
  have hval : ∀ v (y : GA D (Yc D 0)), Ψ v y = star (GlobalTheory.ConjRowMult.contRepL X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)))
      (iotaX X h (y * t⁻¹))) := fun v y => GlobalTheory.ConjRowMult.conjMap_apply X (MP R) c Φ h t v y
  have hcont : ∀ v, Continuous (Ψ v) := by
    intro v
    obtain ⟨ψ, hψ⟩ := hrep v
    have e : Ψ v = fun y : GA D (Yc D 0) => star (ψ (iotaX X h (y * t⁻¹))) := by
      funext y; exact (hval v y).trans (by rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ])
    rw [e]
    exact continuous_star.comp (hψ.1.comp ((iotaX X h).continuous.comp (continuous_mul_const t⁻¹)))
  refine ⟨⟨?_, ?_, hcont u⟩, fun k τs Xs hX g => GlobalTheory.RepSmooth.smooth hθ he hs hcont u k τs Xs hX g,
    GlobalTheory.RepSmooth.zfin he hs u, ?_⟩
  · intro γ hγ g
    obtain ⟨ψ, hψ⟩ := hrep u
    rw [hval, hval, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
    congr 1
    have e2 : iotaX X h (γ * g * t⁻¹) = iotaX X h γ * iotaX X h (g * t⁻¹) := by
      exact (congrArg (iotaX X h) (mul_assoc γ g t⁻¹)).trans (map_mul (iotaX X h) γ (g * t⁻¹))
    rw [e2]; exact hψ.2.1 _ (iotaX_rat X h hγ) _
  · obtain ⟨U, hU, hUk⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))
    refine ⟨U, hU, fun k hk hkf g => ?_⟩
    obtain ⟨h1, h2⟩ := hUk k hk hkf
    rw [_root_.GlobalTheory.ConjRowLevel.conjMap_level hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep u k h1 g, h2, one_mul]
  · have key : ∃ N : ℕ, ∀ v (x : GA D (Yc D 0)), ∃ C : ℝ, ∀ g ∈ GinfC (Yc D 0),
        ‖Ψ v (x * g)‖ ≤ C * normInf R.θ (Yc D 0) g ^ N := by
      rcases Nat.eq_zero_or_pos (D.sp.Y 0).rank with hn | hn
      · refine ⟨0, fun v x => ⟨‖Ψ v x‖, fun a _ => ?_⟩⟩
        have : a = 1 := Subtype.ext (Units.ext (Matrix.ext fun i => (Fin.cast hn i).elim0))
        simp [this]
      obtain ⟨hfin, hnorm⟩ := _root_.GlobalTheory.IotaNorm.iotaX_norm R F X h hRI hGrp hMod hιE
      obtain ⟨m, hm⟩ := _root_.GlobalTheory.ConjRepBound.contRep_bound hDS R F X h hRI hGrp hMod hHost hιE t c ht hCL hcq Φ hΦ hrep hn
      refine ⟨m, fun v x => ?_⟩
      obtain ⟨C, hC⟩ := hm v
      obtain ⟨C', hC0, hC'⟩ := hnorm hn (iotaX X h (x * t⁻¹))
      refine ⟨|C| * C' ^ m, fun a ha => ?_⟩
      have hi2 : (iotaX X h t⁻¹).1 = 1 :=
        ((GlobalTheory.IotaReal.iotaX_real_finite R F X h hRI hGrp hMod hιE).1 t⁻¹).1 (inv_mem ht)
      have hi1 : (iotaX X h a).2 = 1 := hfin a ha
      have hc : iotaX X h a * iotaX X h t⁻¹ = iotaX X h t⁻¹ * iotaX X h a :=
        Prod.ext (by simp [Prod.fst_mul, hi2]) (by simp [Prod.snd_mul, hi1])
      have hcomm : iotaX X h (x * a * t⁻¹) = iotaX X h (x * t⁻¹) * iotaX X h a := by
        have e1 : iotaX X h (x * a * t⁻¹) = iotaX X h x * iotaX X h a * iotaX X h t⁻¹ := by
          exact (map_mul (iotaX X h) (x * a) t⁻¹).trans (congrArg (· * iotaX X h t⁻¹) (map_mul (iotaX X h) x a))
        have e2 : iotaX X h (x * t⁻¹) = iotaX X h x * iotaX X h t⁻¹ := by
          exact map_mul (iotaX X h) x t⁻¹
        rw [e1, e2, mul_assoc, hc, ← mul_assoc]
      have hp : 0 ≤ (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ :=
        inv_nonneg.2 ((GlobalTheory.TauLipschitz.tauLip X.B.I (by rw [h]; exact hn)).1 _).le
      have h1 := hC (iotaX X h (x * a * t⁻¹))
      rw [hcomm] at h1
      rw [hval, norm_star, hcomm]
      refine h1.trans ?_
      calc C * (GlobalTheory.Count.tau1 X.B.I (iotaX X h (x * t⁻¹) * iotaX X h a))⁻¹ ^ m
          ≤ |C| * (C' * normInf R.θ (Yc D 0) a) ^ m :=
            mul_le_mul (le_abs_self _) (pow_le_pow_left₀ hp (hC' a ha) m) (pow_nonneg hp m) (abs_nonneg _)
        _ = |C| * C' ^ m * normInf R.θ (Yc D 0) a ^ m := by rw [mul_pow, mul_assoc]
    obtain ⟨N, hN⟩ := key
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨v, hv⟩ := GlobalTheory.RepSmooth.foldr_rder he hs u l hl
    obtain ⟨C, hC⟩ := hN v x
    exact ⟨C, fun g hg => (congrArg norm (congrFun hv (x * g))).le.trans (hC g hg)⟩

end GlobalTheory.ConjAutSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsRigIsoOfIsGen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_of_isGen : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : RigLB A) (Y : Scheme.{0})
    (x x' : Y ⟶ S) (Ψ : (Over.mk x ⊗ A).left ⟶ (Over.mk x' ⊗ A).left) (k : ℤ)
    (β : LB.Gen (isoLB A L Ψ k)), IsPointed A Ψ → β.IsGen → ∃ β', IsRigIso A L Ψ k β' := by
  intro S A _ L Y x x' Ψ k β hΨ hβ
  exact GlobalTheory.RigIsoDescent.exists_isRigIso_of_gen hΨ β hβ

end GlobalTheory.HeckeEx
end

