module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BddGood
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeparatingCharacterConjugateHalfSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.DualSep

variable {D : D7}

theorem algebraMap_OI {v : FinPl D} (o : OI v) : algebraMap (OI v) (Fv D.host.F v) o = (o : Fv D.host.F v) := rfl

theorem mem_pow_iff {v : FinPl D} (ϖ : OI v) (hϖ : (ϖ : Fv D.host.F v) ≠ 0) (N : ℕ) (x : Fv D.host.F v) :
    (∃ o : OI v, x = algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N * o)) ↔
      Valued.v x ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
  constructor
  · rintro ⟨o, rfl⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]
    have ho : Valued.v (o : Fv D.host.F v) ≤ 1 :=
      (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 o.2
    calc Valued.v (ϖ : Fv D.host.F v) ^ N * Valued.v (o : Fv D.host.F v)
        ≤ Valued.v (ϖ : Fv D.host.F v) ^ N * 1 := by gcongr
      _ = _ := mul_one _
  · intro h
    have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ
    have hv : 0 < Valued.v ((ϖ : Fv D.host.F v) ^ N) := by
      rw [zero_lt_iff]; exact (map_ne_zero _).2 hp
    have hmem : x / (ϖ : Fv D.host.F v) ^ N ∈ v.adicCompletionIntegers D.host.F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, div_le_one₀ hv, map_pow]
      exact h
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [algebraMap_OI, Subring.coe_mul, SubmonoidClass.coe_pow]
    show x = (ϖ : Fv D.host.F v) ^ N * (x / (ϖ : Fv D.host.F v) ^ N)
    rw [mul_div_cancel₀ _ hp]

theorem adjCo_smul {v : FinPl D} (φ : SplitProj D v) (S T : HSp D) (BS : GL (Fin S.rank) (Fv D.host.F v))
    (BT : GL (Fin T.rank) (Fv D.host.F v)) (s : AE D) (z : WO S T) :
    adjCo φ S T BS BT (cA D s • z) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • adjCo φ S T BS BT z := by
  have h1 : ((cA D s • z : WO S T) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) =
      s • (z : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (cA D) := by
    ext i j
    simp [GlobalTheory.DualPairCheck.cA_cA]
  have h2 : ∀ (M : Matrix (Fin S.rank) (Fin T.rank) (AE D)),
      (s • M).map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ s • M.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) := by
    intro M; ext i j; simp
  unfold adjCo
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.DownLift.GenSplit.DualSep

namespace GlobalTheory.DownLift.GenSplit


open DualSep in
theorem exists_sep_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ (N : ℕ) (x : WO S T), IsHalf (cA D e) x → ¬ InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) → ∃ y, IsHalf e y ∧ (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, ψ (symplO S T z y) = 1) ∧ ψ (symplO S T x y) ≠ 1 := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ N x hx hxN
  obtain ⟨a, -, ha0, -, himg⟩ := (GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he).2
  have hα : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) ≠ 0 := by
    rw [← GlobalTheory.SplitProjChart.emb_apply]
    exact (map_ne_zero _).2 (star_ne_zero.2 ha0)
  have hϖ0 : (ϖ : Fv D.host.F v) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hp : (ϖ : Fv D.host.F v) ^ N ≠ 0 := pow_ne_zero _ hϖ0
  set c : Fv D.host.F v := GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) / (ϖ : Fv D.host.F v) ^ N with hcdef
  have hc : c ≠ 0 := div_ne_zero hα hp
  obtain ⟨s, hs⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.1 c
  have hcoef : ∀ z : WO S T, adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) =
      c • adjCo φ S T (frCo φ βS) (frCo φ βT) z := fun z => by rw [adjCo_smul, hs]
  have hval : ∀ m : Fv D.host.F v, Valued.v (c * m) ≤ Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) ↔
      Valued.v m ≤ Valued.v (ϖ : Fv D.host.F v) ^ N := by
    intro m
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = c * (ϖ : Fv D.host.F v) ^ N := by
      rw [hcdef, div_mul_cancel₀ _ hp]
    rw [e1, map_mul, map_mul, map_pow, mul_le_mul_iff_right₀ (zero_lt_iff.2 ((map_ne_zero _).2 hc))]
  have hinPow : ∀ z : WO S T, InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) ↔
      ∀ i j, Valued.v ((c • adjCo φ S T (frCo φ βS) (frCo φ βT) z) i j) ≤
        Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a)) := by
    intro z
    unfold InPow
    simp only [Matrix.smul_apply, smul_eq_mul, hval, mem_pow_iff ϖ hϖ0 N]
  have hhalf : ∀ z : WO S T, IsHalf (cA D e) z → IsHalf (cA D e) (cA D s • z) := by
    intro z hz
    rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hz]
  have hcoord := (GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)).1
  have hmem : ∀ z : WO S T, IsHalf (cA D e) z → InPow ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) z) →
      cA D s • z ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro z hz hzN
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • z) ∈ adjCo φ S T (frCo φ βS) (frCo φ βT) ''
        {t | t ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧
          IsHalf (cA D e) t} := by
      rw [himg, hcoef]
      exact (hinPow z).1 hzN
    obtain ⟨t, ⟨htΛ, htH⟩, hteq⟩ := h1
    have h2 : t = cA D s • z := hcoord.2.1.injOn htH (hhalf z hz) hteq
    rw [← h2]
    exact htΛ
  have hnot : cA D s • x ∉
      latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    intro hmx
    apply hxN
    rw [hinPow]
    have h1 : adjCo φ S T (frCo φ βS) (frCo φ βT) (cA D s • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤
          Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a))} := by
      rw [← himg]
      exact ⟨_, ⟨hmx, hhalf x hx⟩, rfl⟩
    rw [hcoef] at h1
    exact h1
  have hsd := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hse := GlobalTheory.SplitScalar.isSplitIdem_conj he.1
  obtain ⟨l, hlΛ, hlH, hne⟩ := GlobalTheory.SplitScalar.exists_dual_half hse hsd
    (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.SplitScalar.idem_smul_mem he.1.1 u hu) (hhalf x hx) hnot
  rw [GlobalTheory.DualPairCheck.cA_cA] at hlH
  refine ⟨s • l, ?_, fun z hz => ?_, ?_⟩
  · rw [GlobalTheory.SplitScalar.isHalf_iff] at *
    rw [smul_comm, hlH]
  · obtain ⟨hz1, hz2⟩ := hz
    have h1 := (hsd _ (GlobalTheory.SplitScalar.half_fin hse (hhalf z hz1))).1 (hmem z hz1 hz2) l hlΛ
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1
  · have h1 := GlobalTheory.SplitScalar.psi_skew_ne hne
    rwa [GlobalTheory.SplitScalar.symplO_smul, GlobalTheory.DualPairCheck.cA_cA] at h1

end GlobalTheory.DownLift.GenSplit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockMinorProductEqSignDualWeylExtremalVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.DeltaExtremal

noncomputable def lead {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) : ℂ :=
  if h : k ≤ n then (y.submatrix (Fin.castLE h) (Fin.castLE h)).det else 1

theorem lead_zero {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y 0 = 1 := by
  simp [lead]

theorem lead_self {n : ℕ} (y : Matrix (Fin n) (Fin n) ℂ) : lead y n = y.det := by
  simp [lead]

theorem det_inv_rev {n k : ℕ} (hk : k ≤ n) (y : GL (Fin n) ℂ) :
    (Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b))).det =
      lead y.val (n - k) * (y.val.det)⁻¹ := by
  obtain ⟨e, hl, hr⟩ := GlobalTheory.ValCmp.exists_equiv_castLE_rev hk
  have hj := GlobalTheory.ValCmp.jacobi_blocks_of_mul (y.val.submatrix e e) ((y⁻¹).val.submatrix e e) 1 (by
    rw [Matrix.submatrix_mul_equiv, Units.mul_inv, one_smul, Matrix.submatrix_one_equiv])
  have e1 : (y.val.submatrix e e).toBlocks₁₁ =
      y.val.submatrix (Fin.castLE (Nat.sub_le n k)) (Fin.castLE (Nat.sub_le n k)) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hl]
  have e2 : ((y⁻¹).val.submatrix e e).toBlocks₂₂ =
      Matrix.of fun a b : Fin k => (y⁻¹).val (Fin.rev (Fin.castLE hk a)) (Fin.rev (Fin.castLE hk b)) := by
    ext a b
    simp only [Matrix.toBlocks₂₂, hr, Matrix.of_apply, Matrix.submatrix_apply]
  rw [e1, e2, one_pow, one_mul, Matrix.det_submatrix_equiv_self] at hj
  rw [← hj, lead, dif_pos (Nat.sub_le n k), Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

variable {D : D7} {m n : ℕ}

theorem aeval_minorPlus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hk : k ≤ p τ) (hm : k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorPlus τ k : PolF D m n) = lead (y τ).val k := by
  rw [minorPlus, AlgHom.map_det, lead, dif_pos hn]
  congr 1
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  have h1 : b.val < m ∧ a.val < n := ⟨by omega, by omega⟩
  have h2 : b.val < p τ := by omega
  have h3 : b.val < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_pos h2, dif_pos h3, Matrix.submatrix_apply]
  rfl

theorem aeval_minorMinus (p : D.what₂.Tau → ℕ) (y : GLR D n) (τ : D.what₂.Tau) {k : ℕ} (hm : p τ + k ≤ m) (hn : k ≤ n) :
    MvPolynomial.aeval (fockPt p y) (minorMinus τ (p τ) k : PolF D m n) =
      ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin k)) : ℤ) : ℂ) * (lead (y τ).val (n - k) * ((y τ).val.det)⁻¹) := by
  rw [minorMinus, AlgHom.map_det, ← det_inv_rev hn, ← Matrix.det_permute', ← Matrix.det_transpose]
  congr 1
  ext b a
  have ha := a.isLt
  have hb := b.isLt
  have h1 : p τ + b.val < m ∧ n - k + a.val < n := ⟨by omega, by omega⟩
  have h2 : ¬ p τ + b.val < p τ := by omega
  have h3 : p τ + b.val - p τ < n := by omega
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, varF, dif_pos h1, MvPolynomial.aeval_X, fockPt,
    if_neg h2, dif_pos h3, Matrix.submatrix_apply, Matrix.transpose_apply, id]
  refine congrArg₂ _ (congrArg Fin.rev (Fin.ext ?_)) (Fin.ext ?_)
  · simp
  · simp only [Fin.revPerm_apply, Fin.val_rev, Fin.val_castLE]
    omega

theorem sum_drops (q : ℕ) (a : ℕ → ℕ) (h : ∀ i, i + 1 < q → a (i + 1) ≤ a i) :
    ∑ i ∈ Finset.range q, (a i - if i + 1 < q then a (i + 1) else 0) = if 0 < q then a 0 else 0 := by
  have := Finset.sum_range_sub' (fun i => if i < q then (a i : ℤ) else 0) q
  simp only [lt_irrefl, if_false, sub_zero] at this
  refine Nat.cast_injective (R := ℤ) ?_
  rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← this]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.1 hi
  have := h i
  split_ifs <;> omega

theorem prod_exponents {n p q : ℕ} (ap am : ℕ → ℕ) (c : ℤ) (lam : DomWeight n) (hle : p + q ≤ n)
    (hl : ∀ i : Fin n, lam.w i = (if i.val < p then (ap i : ℤ) else if n - q ≤ i.val then -(am (n - 1 - i) : ℤ) else 0) + c)
    (L : ℕ → ℂ) (h0 : L 0 = 1) (hd : L n ≠ 0) :
    L n ^ c * ((∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) *
      ∏ i ∈ Finset.range q, (L (n - (i + 1)) * (L n)⁻¹) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
    L n ^ lam.detShift * ∏ s : Fin n, L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) := by
  rcases n with _ | k
  · obtain rfl : p = 0 := by omega
    obtain rfl : q = 0 := by omega
    simp [h0]
  have hanti : ∀ i j (hi : i < k + 1) (hj : j < k + 1), i ≤ j → lam.w ⟨j, hj⟩ ≤ lam.w ⟨i, hi⟩ :=
    fun i j hi hj h => lam.anti (show (⟨i, hi⟩ : Fin (k + 1)) ≤ ⟨j, hj⟩ from h)
  have ham : ∀ i, i + 1 < q → am (i + 1) ≤ am i := by
    intro i hi
    have := hanti (k - (i + 1)) (k - i) (by omega) (by omega) (by omega)
    rw [hl, hl] at this
    dsimp only at this
    rw [show k + 1 - 1 - (k - i) = i by omega, show k + 1 - 1 - (k - (i + 1)) = i + 1 by omega] at this
    split_ifs at this <;> omega
  have hshift : lam.detShift = lam.w ⟨k, Nat.lt_succ_self k⟩ := by
    simp [DomWeight.detShift]
  set A : ℕ → ℕ := fun i => if i < p then ap i - if i + 1 < p then ap (i + 1) else 0 else 0 with hA
  set B : ℕ → ℕ := fun i => if i < q then am i - if i + 1 < q then am (i + 1) else 0 else 0 with hB
  have eA : (∏ i ∈ Finset.range p, L (i + 1) ^ (ap i - if i + 1 < p then ap (i + 1) else 0)) =
      (∏ i ∈ Finset.range k, L (i + 1) ^ A i) * L (k + 1) ^ A k := by
    rw [← Finset.prod_range_succ (fun i => L (i + 1) ^ A i),
      ← Finset.prod_subset (Finset.range_subset_range.2 (show p ≤ k + 1 by omega))
        (fun i _ hi => by rw [hA]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hA]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eB : (∏ i ∈ Finset.range q, L (k + 1 - (i + 1)) ^ (am i - if i + 1 < q then am (i + 1) else 0)) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
    have : ∏ i ∈ Finset.range (k + 1), L (k + 1 - (i + 1)) ^ B i = ∏ i ∈ Finset.range k, L (i + 1) ^ B (k - 1 - i) := by
      rw [Finset.prod_range_succ, Nat.sub_self, h0, one_pow, mul_one, ← Finset.prod_range_reflect]
      refine Finset.prod_congr rfl fun i hi => ?_
      have := Finset.mem_range.1 hi
      rw [show k + 1 - (k - 1 - i + 1) = i + 1 by omega]
    rw [← this, ← Finset.prod_subset (Finset.range_subset_range.2 (show q ≤ k + 1 by omega))
        (fun i _ hi => by rw [hB]; dsimp only; rw [if_neg (fun h => hi (Finset.mem_range.2 h)), pow_zero])]
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [hB]; dsimp only; rw [if_pos (Finset.mem_range.1 hi)]
  have eR : ∏ s : Fin (k + 1), L (s + 1) ^ (lam.natW s - Formalism.GradedWeylDivisibility.nuNext lam.natW s) =
      ∏ i ∈ Finset.range k, L (i + 1) ^ (A i + B (k - 1 - i)) := by
    rw [Fin.prod_univ_castSucc, show lam.natW (Fin.last k) = 0 by
      rw [DomWeight.natW, hshift]; simp [Fin.last], Nat.zero_sub, pow_zero, mul_one,
      ← Fin.prod_univ_eq_prod_range (fun i => L (i + 1) ^ (A i + B (k - 1 - i)))]
    refine Finset.prod_congr rfl fun s _ => ?_
    obtain ⟨s, hs⟩ := s
    have hs' : s + 1 < k + 1 := by omega
    simp only [Fin.castSucc_mk, Formalism.GradedWeylDivisibility.nuNext, dif_pos hs', DomWeight.natW, hshift]
    congr 1
    have a1 := hanti s (s + 1) (by omega) hs' (by omega)
    have a2 := hanti (s + 1) k hs' (by omega) (by omega)
    have b1 := hl ⟨s, by omega⟩
    have b2 := hl ⟨s + 1, hs'⟩
    dsimp only at b1 b2
    rw [show k + 1 - 1 - s = k - 1 - s + 1 by omega] at b1
    rw [show k + 1 - 1 - (s + 1) = k - 1 - s by omega] at b2
    rw [hA, hB]
    dsimp only
    split_ifs at b1 b2 ⊢ <;> omega
  have eS : lam.detShift = c + (A k : ℤ) - ((if 0 < q then am 0 else 0 : ℕ) : ℤ) := by
    rw [hshift, hl, hA]
    dsimp only
    rw [show k + 1 - 1 - k = 0 by omega]
    split_ifs <;> omega
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [eA, eB, eR, eS, sum_drops q am ham, zpow_sub₀ hd, zpow_add₀ hd, zpow_natCast, zpow_natCast]
  simp only [pow_add, Finset.prod_mul_distrib, inv_pow]
  ring

theorem eval_extremal (lam : D.what₂.Tau → DomWeight n) (y : GLR D n) (τ : D.what₂.Tau) :
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (y v.1).val v.2.1 v.2.2)
      (Formalism.GradedWeylDivisibility.blockEmb ℂ τ (extremal ℂ n (lam τ))) =
    ∏ s : Fin n, lead (y τ).val (s + 1) ^ ((lam τ).natW s - Formalism.GradedWeylDivisibility.nuNext (lam τ).natW s) := by
  rw [extremal, Formalism.GradedWeylDivisibility.hw, map_prod, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, map_pow, Formalism.GradedWeylDivisibility.lpMinor, AlgHom.map_det, RingHom.map_det, lead, dif_pos (Nat.succ_le_of_lt s.isLt)]
  congr 2
  ext a b
  simp [Formalism.GradedWeylDivisibility.blockEmb]

theorem harmFn_delta : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → ∃ s : ℤˣ, ∀ x, harmFn m w B (w.delta m) x = ((s : ℤ) : ℂ) * coefFn (RingHom.id ℂ) w.lam (ten fun τ => extremal ℂ n (w.lam τ)) (B⁻¹ * x) := by
  intro D m n w B hw hm
  refine ⟨∏ τ, ∏ i ∈ Finset.range (w.q τ), Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (i + 1))) ^
    (w.am τ i - if i + 1 < w.q τ then w.am τ (i + 1) else 0), fun x => ?_⟩
  rw [harmFn_apply, coefFn, ten]
  generalize B⁻¹ * x = y
  rw [Weight.delta, Datum.delta, map_prod, map_prod]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply, Int.cast_prod, Units.val_pow_eq_pow_val, Int.cast_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := hw.le τ
  have h2 := hm τ
  have hd : lead (y τ).val n ≠ 0 := by
    rw [lead_self]; exact (GeneralLinearGroup.det (y τ)).ne_zero
  rw [eval_extremal, ← lead_self, ← prod_exponents (w.ap τ) (w.am τ) (w.c τ) (w.lam τ) h1 (hw.lam_eq τ) _ (lead_zero _) hd,
    deltaAt, map_mul, map_prod, map_prod,
    Finset.prod_congr rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorPlus w.p y τ (by omega) (by omega) (by omega)],
    Finset.prod_congr (s₁ := Finset.range (w.q τ)) rfl fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_pow, aeval_minorMinus w.p y τ (by omega) (by omega), mul_pow, ← lead_self],
    Finset.prod_mul_distrib]
  ring

end GlobalTheory.ExportSeries.DeltaExtremal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SingleDatum

variable {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H}

def IsHalfIdem (l : Geo.Tor.Level H) (e : AE D) : Prop :=
  ∃ P : Finset (Formalism.L2.DIV.Pl D.host.E), IsIdemSum e P ∧ ∀ PP, PP ∈ P ↔ l.Mb ≤ PP.asIdeal

def levPoint (V W : HSp D) (l : Geo.Tor.Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D)
    (q : Fin V.rank → LevQ Dw l) : WO V W :=
  Matrix.of fun a b => e * incA D (ι (cSep l • levRep (q b)) a / (l.M : D.host.E))

def transSum (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : Geo.Tor.Level H)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (e : AE D) (f₀ : WO V W → ℂ) (w : (Fin V.rank → LevQ Dw l) → ℂ) :
    WO V W → ℂ :=
  ((Nat.card (Fin V.rank → LevQ Dw l) : ℂ))⁻¹ • ∑ᶠ q : Fin V.rank → LevQ Dw l, w q • heisO ψ V W (levPoint V W l ι e q) f₀

def VacPair (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ) : Prop :=
  IsPair ψ θ V W χV χW om ∧ V.rank ≠ 0 ∧ (ΛV : Set (Fin V.rank → D.host.E)) = L0c D V ∧
    (ΛW : Set (Fin W.rank → D.host.E)) = L0c D W ∧ IsSelfDualC V ΛV ∧ IsSelfDualC W ΛW ∧
    (ΛV : Set (Fin V.rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) ∧
    (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) ∧
    IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f₀

def clsScal (χ : (AE D)ˣ →* Circle) (y : (AE D)ˣ) {n : ℕ} (Λ : GenLat D.host.E n) (r : ℕ) : ℂ :=
  ((χ y : Circle) : ℂ)⁻¹ * ((Real.sqrt ((((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E n).toAddSubgroup.addSubgroupOf
    Λ.La.toAddSubgroup).index : ℝ) ^ r) : ℝ) : ℂ)⁻¹


variable (Dw) in
def IsLetters {m n : ℕ} (lt : LtN Dw n ≃ FVar D m n) : Prop :=
  ∀ ℓ, (lt ℓ).2.2 = ℓ.2.2 ∧ ((ℓ.1 = tauE D (lt ℓ).1 ∧ ((lt ℓ).2.1 : ℕ) = ℓ.2.1) ∨
    (ℓ.1 = conjEmb (tauE D (lt ℓ).1) ∧ ((lt ℓ).2.1 : ℕ) = Dw.p + ℓ.2.1))



variable (Dw) in
def degA (a : (D.host.E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ τ : D.host.E →+* ℂ, ∑ j : Fin (Dw.mult τ), a (τ, j)

variable {l : Geo.Tor.Level H} {Xo : Moduli Dw l}

def IsDict {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (dict : GA D W → Σ k, Frame (U.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  IsUnf U ∧ GlobalTheory.Member.IotaOK Dw W ι ∧ (∀ k, IsMod W hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
      (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
      (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ)
      (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
      (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictLat U W hr dict ι e F ik φ th x₀

def FrameTie {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (W : HSp D) (hr : W.rank = r)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) : Prop :=
  ∀ k, IsInvOf W hr (U.X k) (fun τ => x₀ τ.1) s ∧
    ∀ hq : (U.X k).p0 + Dw.p = r, IsBasOf W hr (U.X k) hq (fun τ => x₀ τ.1) BW

def MarkedVal {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) (θ : InfFam D) (W : HSp D) {r : ℕ} (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (f : Rul d.Xo₂ d.c₂) (ν : GA D W → ℂ) : Prop :=
  ∀ (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (k : GA D W) (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), IsMod W hr X → X.p0 = Dw.q → IsSympl X bas →
    IdxIs c (inC c) X idx e → latR hr (latG W k) = X.Λ → IsMark d.l₂ X.Λ mk → MarkAd d.l₂ W hr ι k mk →
    letI : Algebra d.c₂.F ℂ := ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ ℂ) (A₂ : AnFib X bas idx e (frMove θ W hr X k (fun τ => x₀ τ.1)) X.Λ y₂), A₂.Marked mk →
      evR d.Xo₂ d.c₂ f y₂ = ν k

def IsThetaSum {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {T : Type} [Fintype T] (cs : T → Rul d.Xo₂ d.c₂)
    (w : T → (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat D.host.E n) (N : ℕ) (P : T → MvPolynomial (LtN Dw n) c.F)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ x : c.F, algebraMap d.c₂.F k (d.eF x) = algebraMap c.F k x) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y → ∃ v : T → k,
      (∀ t, thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w t q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (P t)) y₂ (v t)) ∧
      evR Xo c f y = ∑ t, evR d.Xo₂ d.c₂ (cs t) y₂ * v t


end GlobalTheory.SingleDatum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLatAtIffHat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatAtHLat

theorem mem_latAt_iff_hat {D : D7} {S T : HSp D} (B : Base S T) (h : Bridge.Gf S) (x : Fin S.rank → D.host.E) :
    x ∈ B.latAt h ↔ (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
      GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E)) := by
  have e : ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
      fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (((h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
    rw [← map_inv]
    funext i
    change _ = Lev.swapAE D _
    rw [RingHom.map_mulVec (Lev.swapAE D)]
    rfl
  change ((Formalism.UG.bc (Lev.swapAE D) h.1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) B.F.ΛS ↔ _
  rw [e]
  constructor
  · intro hz
    have := GlobalTheory.PrincInLevel.swap_symm_mem_hat B.F.ΛS _ hz
    simpa only [AlgEquiv.symm_apply_apply] using this
  · intro hz
    exact GlobalTheory.PrincInLevel.swap_mem_hatL B.F.ΛS _ hz

theorem latAt_eq_hLat : ∀ (D : D7) (S T : HSp D) (B : Base S T), (B.F.ΛS : Set (Fin S.rank → D.host.E)) = L0c D S → ∀ h, B.latAt h = Bridge.hLat S h := by
  intro D S T B hΛ h
  have e : Bridge.hLat S h = Submodule.span (𝓞 D.host.E) {x : Fin S.rank → D.host.E |
      (h.1⁻¹).1 *ᵥ (fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
        GlobalTheory.AdLat.hat D.host.F (B.F.ΛS : Set (Fin S.rank → D.host.E))} := by
    unfold Bridge.hLat
    rw [hΛ]
    rfl
  rw [e, ← Submodule.span_eq (B.latAt h)]
  congr 1
  ext x
  exact mem_latAt_iff_hat B h x

end GlobalTheory.LatAtHLat
end

