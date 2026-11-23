module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerDiagonalBlockAsGLMemIntegralGeneralLinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0039
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetRepsMaximalIdealMatrixModMul
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke

noncomputable section

namespace GlobalTheory.LowerHecke.MaxReps

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]


variable (k D A) in
def maxLat : AddSubgroup (Matrix D A k) where
  carrier := {ν | ∀ i a, valuation k (ν i a) < 1}
  add_mem' ha hb i a := by simpa using Valuation.map_add_lt _ (ha i a) (hb i a)
  zero_mem' i a := by simp
  neg_mem' ha i a := by simpa using ha i a

def mulLat (g : Matrix D D k) : AddSubgroup (Matrix D A k) where
  carrier := {x | ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ x = g * μ}
  add_mem' := by
    rintro _ _ ⟨μ, hμ, rfl⟩ ⟨μ', hμ', rfl⟩
    exact ⟨μ + μ', fun i a => by simpa using Valuation.map_add_lt _ (hμ i a) (hμ' i a),
      (Matrix.mul_add _ _ _).symm⟩
  zero_mem' := ⟨0, fun i a => by simp, by simp⟩
  neg_mem' := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact ⟨-μ, fun i a => by simpa using hμ i a, (Matrix.mul_neg _ _).symm⟩

theorem inv_mul_mem {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {x : k} (hx : valuation k x < 1) :
    (ϖ : k)⁻¹ * x ∈ 𝒪[k] := by
  show valuation k _ ≤ 1
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one, hϖ, le_uniformizer_iff]
  exact hx

def redMap (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) : maxLat k A D →+ (D → A → 𝓀[k]) where
  toFun ν i a := IsLocalRing.residue 𝒪[k] ⟨(ϖ : k)⁻¹ * (ν : Matrix D A k) i a, inv_mul_mem hϖ (ν.2 i a)⟩
  map_zero' := by
    funext i a
    simp only [AddSubgroup.coe_zero, Matrix.zero_apply, mul_zero, Pi.zero_apply]
    exact map_zero _
  map_add' ν ν' := by
    funext i a
    simp only [Pi.add_apply]
    rw [← map_add (f := _)]
    congr 1
    ext
    simp [mul_add]

theorem exists_int_right_inv {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : Finset D) (g : GL D k)
    (hg : ∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') :
    ∃ Q : Matrix D D k, GlobalTheory.StepData.IntM Q ∧ g.1 * Q = (ϖ : k) • (1 : Matrix D D k) := by
  obtain ⟨κ, hκ, κ', hκ', rfl⟩ := hg
  have hϖ1 : (ϖ : k) ∈ 𝒪[k] := (hϖ ▸ uniformizer_lt_one).le
  let D0 : Matrix D D k := diagonal fun i => (ϖ : k) ^ (1 - indic s i)
  have hD0 : (torusElt k D ϖ (indic s)).1 * D0 = (ϖ : k) • (1 : Matrix D D k) := by
    rw [val_torusElt, diagonal_mul_diagonal, smul_one_eq_diagonal]
    congr 1
    funext i
    rw [← zpow_add₀ ϖ.ne_zero]
    simp
  refine ⟨(κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1, ?_, ?_⟩
  · refine ((GlobalTheory.StepData.mem_KO.1 hκ').2.mul ?_).mul (GlobalTheory.StepData.mem_KO.1 hκ).2
    intro i j
    simp only [D0, diagonal_apply]
    split_ifs
    · by_cases hi : i ∈ s <;> simp [indic, hi, hϖ1]
    · exact zero_mem _
  · have e1 : κ'.1 * (κ'⁻¹ : GL D k).1 = 1 := Units.mul_inv κ'
    have e2 : κ.1 * (κ⁻¹ : GL D k).1 = 1 := Units.mul_inv κ
    simp only [Units.val_mul]
    calc κ.1 * (torusElt k D ϖ (indic s)).1 * κ'.1 * ((κ'⁻¹ : GL D k).1 * D0 * (κ⁻¹ : GL D k).1)
        = κ.1 * ((torusElt k D ϖ (indic s)).1 * (κ'.1 * (κ'⁻¹ : GL D k).1) * D0) * (κ⁻¹ : GL D k).1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [e1, Matrix.mul_one, hD0, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, e2]

end GlobalTheory.LowerHecke.MaxReps


open GlobalTheory.LowerHecke.MaxReps in
theorem GlobalTheory.LowerHecke.exists_finset_reps_maxLat_mod_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (g : GL D k), (∃ κ ∈ KO k D, ∃ κ' ∈ KO k D, g = κ * torusElt k D ϖ (indic s) * κ') → ∃ N : Finset (Matrix D A k), (∀ ν ∈ N, ∀ i a, valuation k (ν i a) < 1) ∧ ∀ ν : Matrix D A k, (∀ i a, valuation k (ν i a) < 1) → ∃! ν', ν' ∈ N ∧ ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ν' = g.1 * μ := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s g hg
  classical
  obtain ⟨Q, hQ, hgQ⟩ := exists_int_right_inv hϖ s g hg
  let M := maxLat k A D
  let H := (mulLat (A := A) g.1).addSubgroupOf M
  have hK : (redMap (D := D) (A := A) ϖ hϖ).ker ≤ H := by
    intro ν hν
    rw [AddMonoidHom.mem_ker] at hν
    rw [AddSubgroup.mem_addSubgroupOf]
    have hμ : ∀ i a, valuation k ((ϖ : k)⁻¹ * (ν : Matrix D A k) i a) < 1 := fun i a => by
      have := congrFun (congrFun hν i) a
      simp only [redMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.zero_apply] at this
      exact (GlobalTheory.StepData.residue_eq_zero_iff_lt _).1 this
    refine ⟨Q * ((ϖ : k)⁻¹ • (ν : Matrix D A k)), hQ.mul_maxM (fun i a => by simpa using hμ i a), ?_⟩
    rw [← Matrix.mul_assoc, hgQ, Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ ϖ.ne_zero, one_smul]
  haveI : Finite (M ⧸ (redMap (D := D) (A := A) ϖ hϖ).ker) :=
    Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivRange _).symm.toEquiv
  haveI : (redMap (D := D) (A := A) ϖ hϖ).ker.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  haveI : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hK
  haveI : Finite (M ⧸ H) := AddSubgroup.finite_quotient_of_finiteIndex
  letI := Fintype.ofFinite (M ⧸ H)
  refine ⟨Finset.univ.image fun q : M ⧸ H => ((Quotient.out q : M) : Matrix D A k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hν
    exact (Quotient.out q).2
  · intro ν hν
    have key : ∀ q : M ⧸ H, q = (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) ↔
        ∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν - ((Quotient.out q : M) : Matrix D A k) = g.1 * μ := by
      intro q
      conv_lhs => rw [← QuotientAddGroup.out_eq' q]
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      refine exists_congr fun μ => and_congr_right fun _ => ?_
      show -((Quotient.out q : M) : Matrix D A k) + ν = g.1 * μ ↔ _
      rw [neg_add_eq_sub]
    refine ⟨((Quotient.out (QuotientAddGroup.mk ⟨ν, hν⟩ : M ⧸ H) : M) : Matrix D A k),
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).1 rfl⟩, ?_⟩
    rintro y ⟨hy, hyμ⟩
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [(key q).2 hyμ]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLowerUnipotentBlockDiagCosetRep
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke GlobalTheory.LowerHecke GlobalTheory.ParHeckeSource GlobalTheory.ParahoricConjBlocks

noncomputable section

namespace GlobalTheory.LowerHecke

theorem lowU_conj_blocks {k : Type} [Field k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (M W : Matrix D D k) (ν : Matrix D A k) (a : Matrix A A k) (b : Matrix A D k) (c : Matrix D A k) (e : Matrix D D k) :
    fromBlocks 1 0 0 M * fromBlocks 1 0 (-ν) 1 * fromBlocks a b c e * fromBlocks 1 0 0 W =
      fromBlocks a (b * W) (M * (c - ν * a)) (M * (e - ν * b) * W) := by
  simp only [fromBlocks_multiply]
  congr 1 <;> simp [Matrix.mul_sub, sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul] <;> abel

end GlobalTheory.LowerHecke

namespace GlobalTheory.LowerHecke

theorem exists_lowU_diag_coset : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (s : Finset D) (R : Finset (GL D k)), IsRepsK (torusElt k D ϖ (indic s)) R → ∀ (κ κ' : GL D k → GL D k), (∀ g ∈ R, κ g ∈ KO k D ∧ κ' g ∈ KO k D ∧ g = κ g * torusElt k D ϖ (indic s) * κ' g) → ∀ j ∈ parahoric k A D, ∃ g ∈ R, ∃ ν₀ : Matrix D A k, (∀ i a, valuation k (ν₀ i a) < 1) ∧ ∀ ν : Matrix D A k, (∃ μ : Matrix D A k, (∀ i a, valuation k (μ i a) < 1) ∧ ν₀ - ν = g.1 * μ) → (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, κ g) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) ∈ parahoric k A D := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ s R hR κ κ' hκ j hj
  set w := torusElt k D ϖ (indic s) with hw
  have hjI : IsIntM j.1 := isIntM_of_mem_parahoric hj
  have hjl : ∀ i l, valuation k (j.1 (.inr i) (.inl l)) < 1 := (mem_parahoric.1 hj).2
  have hjd : valuation k j.1.det = 1 := val_det_of_mem_KO (mem_parahoric.1 hj).1
  obtain ⟨ha, he⟩ := (val_det_iff_of_lower j.1 (fun i l => hjI i l) hjl).1 hjd
  obtain ⟨haI, hbI, hcI, heI⟩ := isIntM_toBlocks hjI
  set a := j.1.toBlocks₁₁ with ha_def
  set b := j.1.toBlocks₁₂ with hb_def
  set c := j.1.toBlocks₂₁ with hc_def
  set e := j.1.toBlocks₂₂ with he_def
  have hcM : ∀ i l, valuation k (c i l) < 1 := fun i l => hjl i l
  have ha0 : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at ha; exact zero_ne_one ha
  have hainvI : IsIntM a⁻¹ := isIntM_inv haI ha
  have hinva : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha0
  letI : Invertible a := Matrix.invertibleOfIsUnitDet a ha0
  set E := e - c * a⁻¹ * b with hE_def
  have hjE : j.1.det = a.det * E.det := by
    rw [← fromBlocks_toBlocks j.1, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
  have hEd : valuation k E.det = 1 := by
    rw [hjE, map_mul, ha, one_mul] at hjd; exact hjd
  have hEI : IsIntM E := isIntM_sub heI (isIntM_mul (isIntM_mul hcI hainvI) hbI)
  have hEu : IsUnit E := (Matrix.isUnit_iff_isUnit_det E).2
    (isUnit_iff_ne_zero.2 fun h0 => by rw [h0, map_zero] at hEd; exact zero_ne_one hEd)
  set E' : GL D k := hEu.unit with hE'_def
  have hE'v : E'.1 = E := hEu.unit_spec
  have hE'K : E' ∈ KO k D := mem_KO_of (by rw [hE'v]; exact hEI) (by rw [hE'v]; exact hEd)
  obtain ⟨g, ⟨hgR, hgK⟩, -⟩ := hR.2 E' hE'K
  obtain ⟨hκg, hκ'g, hgeq⟩ := hκ g hgR

  refine ⟨g, hgR, c * a⁻¹, fun i l => GlobalTheory.StepData.MaxM.mul_intM (k := k) hcM (fun i l => hainvI i l) i l, ?_⟩
  rintro ν ⟨μ, hμ, hνμ⟩
  have hν : ν = c * a⁻¹ - g.1 * μ := by rw [← hνμ]; abel
  set K1 := κ g with hK1
  set K2 := κ' g with hK2
  have hm : (w⁻¹ * K1⁻¹) * g = K2 := by rw [hgeq]; group
  have hm' : K2 * g⁻¹ = w⁻¹ * K1⁻¹ := by rw [← hm]; group
  have hX : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, K1) * mtor ϖ (indic s))⁻¹ * (j * mtor ϖ (indic s)) =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w) := by
    rw [mtor_eq, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_lowU, ← map_inv, ← map_inv, Prod.inv_mk, Prod.inv_mk,
      inv_one, ← emb_mul_emb]
    simp only [mul_assoc, hw]
  rw [hX]
  set M : Matrix D D k := (w⁻¹ * K1⁻¹).1 with hM
  have hXv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1 =
      fromBlocks a (b * w.1) (M * (c - ν * a)) (M * (e - ν * b) * w.1) := by
    rw [Units.val_mul, Units.val_mul, Units.val_mul, val_emb_one, val_emb_one, val_lowU, ← fromBlocks_toBlocks j.1]
    exact lowU_conj_blocks _ _ _ _ _ _ _
  have h21 : M * (c - ν * a) = K2.1 * (μ * a) := by
    rw [hν, Matrix.sub_mul, Matrix.mul_assoc c, hinva, Matrix.mul_one, sub_sub_cancel, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hM, ← Units.val_mul, hm, Matrix.mul_assoc]
  have he' : e - ν * b = E + g.1 * μ * b := by rw [hν, hE_def, Matrix.sub_mul]; abel
  have h22 : M * (e - ν * b) * w.1 = (K2 * (g⁻¹ * (E' * w))).1 + K2.1 * (μ * b * w.1) := by
    rw [he', Matrix.mul_add, Matrix.add_mul]
    congr 1
    · rw [hM, ← hm', ← hE'v]; simp only [Units.val_mul, Matrix.mul_assoc]
    · rw [← hm, hM]; simp only [Units.val_mul, Matrix.mul_assoc]
  have hwI : IsIntM w.1 := by
    have h := inv_torusElt_int (D := D) hϖ s
    rw [val_inv_torusElt] at h
    rw [hw, val_torusElt]; simpa using h
  have hμa : ∀ i l, valuation k ((μ * a) i l) < 1 := GlobalTheory.StepData.MaxM.mul_intM (k := k) hμ (fun i l => haI i l)
  have hll : ∀ i l, valuation k ((K2.1 * (μ * a)) i l) < 1 := val_lt_mul (isIntM_of_mem_KO hκ'g) hμa
  have hwdet : (w⁻¹).1.det * w.1.det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  refine mem_parahoric_of ?_ ?_ ?_
  · rw [hXv, h21, h22]
    refine isIntM_fromBlocks_iff.2 ⟨haI, isIntM_mul hbI hwI, fun i l => (hll i l).le, ?_⟩
    intro i l
    exact add_mem (isIntM_of_mem_KO (mul_mem hκ'g hgK) i l)
      (isIntM_mul (isIntM_of_mem_KO hκ'g) (isIntM_mul (isIntM_mul (fun i l => (hμ i l).le) hbI) hwI) i l)
  · have hdet : (emb₂ k (Equiv.refl (A ⊕ D)) (1, w⁻¹ * K1⁻¹) * lowU (-ν) * j * emb₂ k (Equiv.refl (A ⊕ D)) (1, w)).1.det =
        (K1⁻¹).1.det * j.1.det * ((w⁻¹).1.det * w.1.det) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, val_emb_one,
        val_emb_one, val_lowU, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, Units.val_mul,
        Matrix.det_mul]
      simp only [Matrix.det_one]; ring
    rw [hdet, hwdet, mul_one, map_mul, hjd, mul_one]
    exact val_det_of_mem_KO (inv_mem hκg)
  · intro i l
    rw [hXv, fromBlocks_apply₂₁, h21]
    exact hll i l

end GlobalTheory.LowerHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogAdditiveModPrime
section
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

open Formalism.L2.Th1.C

theorem twistLog_norm_iterate {K : Type} [NormedField K] (σ : K →+* K) (hσ : ∀ x : K, ‖σ x‖ = ‖x‖) (i : ℕ)
    (x : K) : ‖(σ ^ i) x‖ = ‖x‖ := by
  induction i generalizing x with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    exact (ih (σ x)).trans (hσ x)

theorem twistLog_additive_mod : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m,
      ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2))
        (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  intro K _ _ _ l σ hU f e hf i hi m
  have hU' := hU
  obtain ⟨hlp, -, hl1, -, hσn, -⟩ := hU
  obtain ⟨hlog, hd, hint⟩ := hf
  have hlog0 := hlog
  obtain ⟨h0, h1, h0', hfe, hef⟩ := hlog
  have hn : l ^ i ≠ 0 := pow_ne_zero _ hlp.ne_zero
  have hτ : ∀ x : K, ‖(σ ^ i) x‖ = ‖x‖ := twistLog_norm_iterate σ hσn i
  set g := PowerSeries.map (σ ^ i) f with hg
  set e' := PowerSeries.map (σ ^ i) e with he'
  have hXm : MvPowerSeries.map (σ ^ i) (PowerSeries.X : K⟦X⟧) = PowerSeries.X := PowerSeries.map_X _
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hg, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  have he0 : PowerSeries.constantCoeff e' = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, he', PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0', map_zero]
  have hlog' : IsLogPair g e' := by
    refine ⟨hg0, ?_, he0, ?_, ?_⟩
    · rw [hg, PowerSeries.coeff_map, h1, map_one]
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hfe
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0), hXm] at this
      exact this
    · have := congrArg (MvPowerSeries.map (σ ^ i)) hef
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' h0'), hXm] at this
      exact this
  have hd' : CoefLe 1 (d⁄dX g) := by
    intro k
    rw [PowerSeries.coeff_derivative, hg, PowerSeries.coeff_map]
    have hk : (σ ^ i) ((PowerSeries.coeff (k + 1)) f) * ((k : K) + 1)
        = (σ ^ i) ((PowerSeries.coeff (k + 1)) f * ((k : K) + 1)) := by
      rw [map_mul, map_add (f := _), map_one, map_natCast]
    rw [hk, hτ, ← PowerSeries.coeff_derivative]
    exact hd k
  set X0 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 0 with hX0
  set X1 : MvPowerSeries (Fin 2) K := MvPowerSeries.X 1 with hX1
  have hX00 : MvPowerSeries.constantCoeff X0 = 0 := by simp [X0]
  have hX10 : MvPowerSeries.constantCoeff X1 = 0 := by simp [X1]
  set F := fadd f e X0 X1 with hF
  have hF0 : MvPowerSeries.constantCoeff F = 0 := Pts.constantCoeff_fadd hlog0 hX00 hX10
  have hFint : ∀ m, ‖MvPowerSeries.coeff m F‖ ≤ 1 := fun m => hint m
  have hAB := _root_.GlobalTheory.Honda.pow_frob_sub_le K l σ hU' (Fin 2) F hFint i hn
  set A := F ^ l ^ i with hA
  set B := MvPowerSeries.expand (l ^ i) hn (MvPowerSeries.map (σ ^ i) F) with hB
  have hA0 : MvPowerSeries.constantCoeff A = 0 := by
    rw [hA, map_pow, hF0, zero_pow hn]
  have hB0 : MvPowerSeries.constantCoeff B = 0 := by
    simp [hB, hF0]
  have hA1 : ∀ m, ‖MvPowerSeries.coeff m A‖ ≤ 1 := fun m => IntegralMvPolynomialLemmas.intMv_pow hint (l ^ i) m
  have hB1 : ∀ m, ‖MvPowerSeries.coeff m B‖ ≤ 1 := by
    intro m
    have hb : MvPowerSeries.coeff m B
        = MvPowerSeries.coeff m A + -(MvPowerSeries.coeff m (A - B)) := by
      rw [map_sub]
      ring
    rw [hb]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    rw [norm_neg]
    exact max_le (hA1 m) ((hAB m).trans hl1.le)
  have key := GlobalTheory.T.subst_congr_mod_prime_of_integral_derivative K l hlp hl1 g hd' (Fin 2) A B hA0 hB0 hA1 hB1 hAB m
  have hsX : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (frobOp σ l i f) = PowerSeries.subst (a ^ l ^ i) g := by
    intro a ha
    have has := PowerSeries.HasSubst.of_constantCoeff_zero ha
    unfold frobOp
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.X_pow hn) has,
      PowerSeries.subst_pow has, PowerSeries.subst_X has]
  have hs0 : MvPowerSeries.constantCoeff (PowerSeries.subst X0 g + PowerSeries.subst X1 g) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero hX00 _ hg0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ hg0, add_zero]
  have hs0f : MvPowerSeries.constantCoeff (PowerSeries.subst X0 f + PowerSeries.subst X1 f) = 0 := by
    rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero hX00 _ h0,
      PowerSeries.constantCoeff_subst_eq_zero hX10 _ h0, add_zero]
  have hmapF : MvPowerSeries.map (σ ^ i) F
      = PowerSeries.subst (PowerSeries.subst X0 g + PowerSeries.subst X1 g) e' := by
    rw [hF]
    unfold fadd
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hs0f), map_add (f := _),
      PowerSeries.map_subst (PowerSeries.HasSubst.X 0), PowerSeries.map_subst (PowerSeries.HasSubst.X 1),
      hX0, hX1, MvPowerSeries.map_X, MvPowerSeries.map_X]
  have hBf : B = fadd g e' (X0 ^ l ^ i) (X1 ^ l ^ i) := by
    rw [hB, hmapF, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.of_constantCoeff_zero hs0),
      map_add, PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 0),
      PowerSeries.expand_subst (l ^ i) hn (PowerSeries.HasSubst.X 1), hX0, hX1,
      MvPowerSeries.expand_X, MvPowerSeries.expand_X]
    rfl
  have hBeq : PowerSeries.subst B g
      = PowerSeries.subst (X0 ^ l ^ i) g + PowerSeries.subst (X1 ^ l ^ i) g := by
    rw [hBf]
    exact Pts.l_fadd hlog' (by rw [map_pow, hX00, zero_pow hn]) (by rw [map_pow, hX10, zero_pow hn])
  have hbe : be0 f e (frobOp σ l i f) X0 X1 = PowerSeries.subst A g - PowerSeries.subst B g := by
    unfold be0
    rw [← hF, hsX F hF0, hsX X0 hX00, hsX X1 hX10, hBeq]
    abel
  rw [hbe]
  exact key

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsIntegralHondaLogarithmPairShortWeierstrass
section
open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

theorem intLog_shortW (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖(2 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1) :
    IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  set W := Formalism.L2.Th1.A.shortW g2 g3 with hW
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → x ∈ Formalism.G.unitBall K := fun x hx => hx
  have ha4 : W.a₄ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg2
  have ha6 : W.a₆ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg3
  have h0 : (0 : K) ∈ Formalism.G.unitBall K := (Formalism.G.unitBall K).zero_mem
  have hcm := Formalism.L2.Th1.A.coeffMem K W (Formalism.G.unitBall K) h0 h0 h0 ha4 ha6
  obtain ⟨hl0, hl1, hlom, -⟩ := Formalism.L2.Th1.A.logSpec K W
  obtain ⟨he0, -, hle, hel, -⟩ := Formalism.L2.Th1.A.expSpec K W
  obtain ⟨-, hfgl⟩ := Formalism.L2.Th1.A.fglLog K W
  refine ⟨⟨hl0, hl1, he0, hel, hle⟩, ?_, ?_⟩
  · intro n
    rw [hlom]
    exact hcm.2.2.2.2.1 n
  · intro n
    unfold Formalism.L2.Th1.C.fadd
    rw [← hfgl]
    exact hcm.2.2.2.2.2.2.1 n

end GlobalTheory.Honda
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexPreimagePiEqProd
section
namespace GlobalTheory

theorem relIndex_preimage_pi_eq_prod :
    ∀ {G : Type} [Group G] {r : ℕ} {H : Fin r → Type} [∀ i, Group (H i)]
      (φ : G →* ((i : Fin r) → H i)) (U U' : Subgroup G) (K J : (i : Fin r) → Subgroup (H i)),
      (∀ i, J i ≤ K i) → (∀ g ∈ U, ∀ i, φ g i ∈ K i) →
      (∀ x : (i : Fin r) → H i, (∀ i, x i ∈ K i) → ∃ g ∈ U, φ g = x) →
      (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i, φ g i ∈ J i) →
      U'.relIndex U = ∏ i, (J i).relIndex (K i) := by
  intro G _ r H _ φ U U' K J _ hUK hsurj hU'
  let f : U →* (∀ i, K i) :=
    { toFun := fun g i => ⟨φ g i, hUK g g.2 i⟩
      map_one' := by
        funext i
        apply Subtype.ext
        simp
      map_mul' := by
        intro a b
        funext i
        apply Subtype.ext
        simp }
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, hg, hx⟩ := hsurj (fun i => (x i : H i)) (fun i => (x i).2)
    refine ⟨⟨g, hg⟩, ?_⟩
    funext i
    apply Subtype.ext
    change φ g i = _
    rw [hx]
  have hc : U'.subgroupOf U =
      (Subgroup.pi Set.univ fun i => (J i).subgroupOf (K i)).comap f := by
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hU']
    constructor
    · rintro ⟨-, h⟩ i -
      exact Subgroup.mem_subgroupOf.2 (h i)
    · intro h
      exact ⟨g.2, fun i => Subgroup.mem_subgroupOf.1 (h i (Set.mem_univ _))⟩
  rw [Subgroup.relIndex, hc, Subgroup.index_comap_of_surjective _ hf, index_pi_univ_dep]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumNormSqOrthonormalLeHilbertSchmidtStatement
section
open Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_sq_orthonormal_le_hilbertSchmidt : ∀ {V H : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (A : V →L[ℂ] H) {ι : Type} [Fintype ι] (v : ι → V), Orthonormal ℂ v → ∑ i, ‖A (v i)‖ ^ 2 ≤ hsNormSq A := by
  first | exact @GlobalTheory.sum_norm_sq_le_hsNormSq | exact GlobalTheory.sum_norm_sq_le_hsNormSq | (intros; apply GlobalTheory.sum_norm_sq_le_hsNormSq <;> assumption)
end

