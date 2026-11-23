module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
public import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorOfIntegrableDiscreteSeriesCoefficient
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial MeasureTheory GlobalTheory.FockTensor

noncomputable section

namespace GlobalTheory.CoefProjector

variable {p q : ℕ} {T : GrpData p q}

theorem inner_opE (πU : URep T) {e : T.G → ℂ} (hi : Integrable e T.haar)
    (hc : Continuous e) (z x : πU.H) :
    inner ℂ z (opE T πU.π e x) = ∫ g, e g * inner ℂ z (πU.π g x) ∂T.haar := by
  have h : Integrable (fun g => e g • πU.π g x) T.haar := by
    refine Integrable.mono' (hi.norm.mul_const ‖x‖) (hc.smul (πU.cont x)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, πU.isom]
  unfold opE
  rw [← integral_inner h]
  simp only [inner_smul_right]

theorem continuous_eFun (D : DSRep T) (v : D.HK.V) : Continuous (eFun D v) :=
  continuous_const.mul (continuous_const.inner (D.U.cont _)).star

theorem pi_mul (πU : URep T) (g h : T.G) (x : πU.H) : πU.π (g * h) x = πU.π g (πU.π h x) := by
  rw [map_mul]; rfl

theorem eFun_inv (D : DSRep T) (v : D.HK.V) (g : T.G) : eFun D v g⁻¹ = star (eFun D v g) := by
  simp only [eFun, mcoef]
  rw [← inner_pi_left]
  simp [inner_conj_symm]

theorem fdeg_ne (D : DSRep T) : (D.fdeg : ℂ) ≠ 0 := by exact_mod_cast D.fdeg_pos.ne'

theorem integral_eFun_mul (D : DSRep T) (v : D.HK.V) (w u : D.U.H) :
    ∫ g, eFun D v g * inner ℂ w (D.U.π g u) ∂T.haar = inner ℂ (D.ι v) u * inner ℂ w (D.ι v) := by
  have h := (GlobalTheory.SchurPol.schur_polarised p q T D u w (D.ι v) (D.ι v)).2
  have h2 : ∀ g, eFun D v g * inner ℂ w (D.U.π g u) =
      (D.fdeg : ℂ) * (inner ℂ w (D.U.π g u) * star (inner ℂ (D.ι v) (D.U.π g (D.ι v)))) := by
    intro g; simp only [eFun, mcoef]; ring
  simp only [h2]
  rw [integral_const_mul, h]
  have := fdeg_ne D
  have h3 : star (inner ℂ (D.ι v) w) = inner ℂ w (D.ι v) := inner_conj_symm _ _
  rw [h3]
  field_simp

theorem opE_self (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (u : D.U.H) :
    opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v := by
  refine ext_inner_left ℂ fun w => ?_
  rw [inner_opE D.U hi (continuous_eFun D v), integral_eFun_mul, inner_smul_right]

theorem opE_selfAdjoint (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x y : πU.H) :
    inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y) := by
  haveI := (GlobalTheory.HolDS.haar_unimodular p q T).2
  rw [← inner_conj_symm, inner_opE πU hi (continuous_eFun D v), inner_opE πU hi (continuous_eFun D v),
    ← integral_conj, ← integral_inv_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_mul, inner_conj_symm, inner_pi_left, inv_inv, eFun_inv]
  simp

theorem eFun_conv (D : DSRep T) (v : D.HK.V) (x h : T.G) :
    ∫ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) ∂T.haar = mcoef D v x * eFun D v h := by
  have h2 : ∀ g, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) =
      (D.fdeg : ℂ) * (eFun D v g * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v)))) := by
    intro g
    have : eFun D v (x⁻¹ * (g⁻¹ * h)) =
        (D.fdeg : ℂ) * inner ℂ (D.U.π h (D.ι v)) (D.U.π g (D.U.π x (D.ι v))) := by
      simp only [eFun, mcoef]
      rw [pi_mul, pi_mul, ← inner_pi_left, ← inner_pi_left]
      congr 1
      exact inner_conj_symm _ _
    rw [this]; ring
  simp only [h2]
  rw [integral_const_mul, integral_eFun_mul]
  simp only [eFun, mcoef]
  have h3 : star (inner ℂ (D.ι v) (D.U.π h (D.ι v))) = inner ℂ (D.U.π h (D.ι v)) (D.ι v) :=
    inner_conj_symm _ _
  rw [h3]; ring

theorem opE_pi_opE (D : DSRep T) (v : D.HK.V) (hi : Integrable (eFun D v) T.haar) (πU : URep T)
    (x : T.G) (y : πU.H) :
    opE T πU.π (eFun D v) (πU.π x (opE T πU.π (eFun D v) y)) =
      mcoef D v x • opE T πU.π (eFun D v) y := by
  have hc := continuous_eFun D v
  refine ext_inner_left ℂ fun z => ?_
  rw [inner_smul_right, inner_opE πU hi hc, inner_opE πU hi hc z y, ← integral_const_mul]
  have h1 : ∀ g, eFun D v g * inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
      ∫ h, eFun D v g * eFun D v (x⁻¹ * (g⁻¹ * h)) * inner ℂ z (πU.π h y) ∂T.haar := by
    intro g
    have e1 : inner ℂ z (πU.π g (πU.π x (opE T πU.π (eFun D v) y))) =
        inner ℂ (πU.π (g * x)⁻¹ z) (opE T πU.π (eFun D v) y) := by
      rw [inner_pi_left, inv_inv, pi_mul]
    rw [e1, inner_opE πU hi hc, ← integral_const_mul, ← integral_mul_left_eq_self _ (g * x)⁻¹]
    refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only
    rw [pi_mul, inner_pi_pi, mul_inv_rev, mul_assoc x⁻¹, mul_assoc]
  simp only [h1]
  have hi' : Integrable (fun k => eFun D v (x⁻¹ * k)) T.haar := hi.comp_mul_left x⁻¹
  have hp := ((measurePreserving_prod_inv_mul T.haar T.haar).integrable_comp_of_integrable
    (hi.mul_prod hi'))
  have hcont : Continuous fun h : T.G × T.G => inner ℂ z (πU.π h.2 y) :=
    (continuous_const.inner (πU.cont y)).comp continuous_snd
  have hp2 := hp.mul_bdd (c := ‖z‖ * ‖y‖) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => by
      simpa [πU.isom] using norm_inner_le_norm (𝕜 := ℂ) z (πU.π h.2 y))
  rw [integral_integral_swap hp2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  rw [integral_mul_const, eFun_conv, mul_assoc]

theorem dense_orbit (D : DSRep T) (u : D.U.H) (hu : u ≠ 0) :
    DenseRange (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) := by
  have : Dense ((LinearMap.range (Finsupp.linearCombination ℂ fun g : T.G => D.U.π g u) :
      Submodule ℂ D.U.H) : Set D.U.H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro w hw
    have h := ext_orbit D u hu (innerSL ℂ w) 0 fun g => by
      refine Submodule.inner_left_of_mem_orthogonal ?_ hw
      exact ⟨Finsupp.single g 1, by simp⟩
    have h2 := congrArg (fun f : D.U.H →L[ℂ] ℂ => f w) h
    simpa using h2
  exact this

theorem exists_intertwiner (D : DSRep T) (v : D.HK.V) (hv : ‖D.ι v‖ = 1) (πU : URep T) (ξ : πU.H)
    (hξ : ∀ g, inner ℂ ξ (πU.π g ξ) = mcoef D v g * inner ℂ ξ ξ) :
    ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  have hu : D.ι v ≠ 0 := by
    intro h; rw [h, norm_zero] at hv; exact zero_ne_one hv
  set A := Finsupp.linearCombination ℂ fun g : T.G => D.U.π g (D.ι v) with hA
  set B := Finsupp.linearCombination ℂ fun g : T.G => πU.π g ξ with hB
  have hd : DenseRange A := dense_orbit D _ hu
  have hgram : ∀ g h, inner ℂ (πU.π g ξ) (πU.π h ξ) =
      inner ℂ (D.U.π g (D.ι v)) (D.U.π h (D.ι v)) * inner ℂ ξ ξ := by
    intro g h
    rw [inner_pi_left, inner_pi_left, ← pi_mul, ← pi_mul, hξ, mcoef]
  have hn : ∀ c, ‖B c‖ = ‖ξ‖ * ‖A c‖ := by
    intro c
    have h : inner ℂ (B c) (B c) = inner ℂ (A c) (A c) * inner ℂ ξ ξ := by
      simp only [hA, hB, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
        inner_smul_left, inner_smul_right, hgram, Finset.sum_mul, mul_assoc]
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have h' : ‖B c‖ ^ 2 = (‖ξ‖ * ‖A c‖) ^ 2 := by
      rw [mul_pow, mul_comm]; exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'
  have hT : ∀ c, B.extendOfNorm A (A c) = B c :=
    LinearMap.extendOfNorm_eq hd ⟨‖ξ‖, fun c => (hn c).le⟩
  have hg : ∀ g, B.extendOfNorm A (D.U.π g (D.ι v)) = πU.π g ξ := fun g => by
    simpa [hA, hB] using hT (Finsupp.single g 1)
  refine ⟨B.extendOfNorm A, fun g => ext_orbit D _ hu _ _ fun h => ?_, ?_, fun x => ?_⟩
  · show B.extendOfNorm A (D.U.π g (D.U.π h (D.ι v))) = πU.π g (B.extendOfNorm A (D.U.π h (D.ι v)))
    rw [← pi_mul, hg, hg, pi_mul]
  · simpa using hg 1
  · refine hd.induction_on (p := fun x => ‖B.extendOfNorm A x‖ = ‖ξ‖ * ‖x‖) x
      (isClosed_eq (by fun_prop) (by fun_prop)) fun c => ?_
    rw [hT, hn]

theorem projector_of_integrable_coefficient :
    ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T) (v : D.HK.V), ‖D.ι v‖ = 1 → MeasureTheory.Integrable (eFun D v) T.haar → (∀ u, opE T D.U.π (eFun D v) u = inner ℂ (D.ι v) u • D.ι v) ∧ ∀ πU : URep T, (∀ x y, inner ℂ (opE T πU.π (eFun D v) x) y = inner ℂ x (opE T πU.π (eFun D v) y)) ∧ (∀ g x, opE T πU.π (eFun D v) (πU.π g (opE T πU.π (eFun D v) x)) = mcoef D v g • opE T πU.π (eFun D v) x) ∧ ∀ ξ, opE T πU.π (eFun D v) ξ = ξ → ∃ io : D.U.H →L[ℂ] πU.H, IsHomG D πU io ∧ io (D.ι v) = ξ ∧ ∀ x, ‖io x‖ = ‖ξ‖ * ‖x‖ := by
  intro p q T D v hv hi
  refine ⟨opE_self D v hi, fun πU => ⟨opE_selfAdjoint D v hi πU, opE_pi_opE D v hi πU, fun ξ hξ => ?_⟩⟩
  refine exists_intertwiner D v hv πU ξ fun g => ?_
  have h1 := opE_selfAdjoint D v hi πU ξ (πU.π g (opE T πU.π (eFun D v) ξ))
  rw [opE_pi_opE D v hi, hξ, inner_smul_right] at h1
  exact h1

end GlobalTheory.CoefProjector
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowCutUnipBMulLevSet
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW

theorem truncatedRow_unipotent_mul_and_ne_zero : ∀ (n : ℕ) (ρ : Fin n), ∀ g ∈ levSet n (ρ + 1),
    (∀ u ∈ GlobalTheory.SmGL.unipB ℂ (Fin n), rowCut ρ ((u * g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ)) ∧
    ∃ j, j ≤ ρ ∧ rowCut ρ (g : Matrix (Fin n) (Fin n) ℂ) j ≠ 0 := by
  intro n ρ g hg
  constructor
  · intro u hu
    obtain ⟨hu0, hu1⟩ := (GlobalTheory.SmGL.mem_unipB ℂ).1 hu
    funext j
    unfold rowCut
    split_ifs with hj
    · rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single ρ]
      · rw [hu1, one_mul]
      · intro k _ hk
        rcases lt_or_gt_of_ne hk with h | h
        · rw [hu0 ρ k h, zero_mul]
        · have h' := Fin.lt_def.1 h
          rw [(hg k (by omega)).1 j (lt_of_le_of_lt hj h), mul_zero]
      · simp
    · rfl
  · by_contra hne
    push_neg at hne
    have hinv := (_root_.GlobalTheory.JSW.levSet_closed_subgroup n (ρ + 1)).2.1 g hg
    have h1 : ((g * g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ρ ρ = 1 := by simp
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      by_cases hk : k ≤ ρ
      · have := hne k hk
        simp only [rowCut, hk, if_true] at this
        rw [this, zero_mul]
      · push_neg at hk
        have h' := Fin.lt_def.1 hk
        rw [(hinv k (by omega)).1 ρ hk, mul_zero]

end GlobalTheory.JSW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowLevelPrincipalFirstBlockIndexEqCard
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Matrix
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RowLevIndex

section Gen

variable {κ : Type} [CommRing κ]

theorem firstDiagonalBlock_of_diagonal_embedding {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (p : GL (Fin r) κ) (M : GL (Fin n) κ)
    (hM : M ∈ blockUT n κ r bl) (e : M = diagEmb κ h p) : blk0 n κ h bl ⟨M, hM⟩ = p := by
  subst e
  apply Units.ext
  ext i j
  rw [blockZero_val]
  show (diagEmb κ h p : Matrix (Fin n) (Fin n) κ) (Fin.castLE h i) (Fin.castLE h j) = _
  rw [diagEmb_val, diagMat_of_lt _ (show (Fin.castLE h i).val < r from i.2) (show (Fin.castLE h j).val < r from j.2)]
  rfl

theorem HK_le_HPar {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (H₀ : Subgroup (GL (Fin r) κ)) :
    HK n κ r bl ≤ HPar n κ h bl H₀ := by
  rw [HK_eq_HPar h bl]
  intro M hM
  obtain ⟨hb, h0⟩ := mem_HPar.mp hM
  exact mem_HPar.mpr ⟨hb, by rw [Subgroup.mem_bot] at h0; rw [h0]; exact H₀.one_mem⟩

theorem mem_HK_iff {n r : ℕ} (h : r ≤ n) (bl : List ℕ) (M : GL (Fin n) κ) (hM : M ∈ blockUT n κ r bl) :
    M ∈ HK n κ r bl ↔ blk0 n κ h bl ⟨M, hM⟩ = 1 := by
  rw [HK_eq_HPar h bl, mem_HPar]
  constructor
  · rintro ⟨_, h0⟩
    exact (Subgroup.mem_bot).mp h0
  · intro h0
    exact ⟨hM, (Subgroup.mem_bot).mpr h0⟩

end Gen

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)


open Classical in
abbrev inL (v : Pr.vGs) : rowSG Pr sel mu := ⟨v.1, Finset.mem_union_left _ v.2⟩

theorem rowTy_inL (P : LevFam X.E X.K R.r Pr.vGs) (v : Pr.vGs) :
    rowTy Ch sel mu P (inL sel mu v) = rowTyG Ch P v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTyKK_inL (v : Pr.vGs) :
    rowTyKK Ch sel mu (inL sel mu v) = rowTyK Ch v := LevFam.glue_of_mem _ _ _ v.2

theorem rowTy_H_of_not (P : LevFam X.E X.K R.r Pr.vGs) (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) :
    (rowTy Ch sel mu P w).H = (rowTyKK Ch sel mu w).H := by
  unfold rowTy rowTyKK
  rw [LevFam.glue_of_not _ _ _ hw, LevFam.glue_of_not _ _ _ hw]

theorem memP (P : LevFam X.E X.K R.r Pr.vGs) (x : ↥(rowTy Ch sel mu P).inv.grp) (v : Pr.vGs) :
    x.1 (inL sel mu v) ∈ HPar (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t) (P v).H := by
  have h := x.2 (inL sel mu v) (Set.mem_univ _)
  change x.1 (inL sel mu v) ∈ (rowTy Ch sel mu P (inL sel mu v)).H at h
  rw [rowTy_inL] at h
  exact h

theorem grp_le (P : LevFam X.E X.K R.r Pr.vGs) :
    (rowTyKK Ch sel mu).inv.grp ≤ (rowTy Ch sel mu P).inv.grp := by
  intro x hx w _
  have h := hx w (Set.mem_univ _)
  change x w ∈ (rowTyKK Ch sel mu w).H at h
  change x w ∈ (rowTy Ch sel mu P w).H
  by_cases hw : w.1 ∈ Pr.vGs
  · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
    have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
    change rowTyKK Ch sel mu w = _ at e1
    change rowTy Ch sel mu P w = _ at e2
    rw [e1] at h
    rw [e2]
    exact GlobalTheory.RowLevIndex.HK_le_HPar _ _ _ h
  · rw [rowTy_H_of_not Ch sel mu P w hw]
    exact h

def blkMap (P : LevFam X.E X.K R.r Pr.vGs) : FormG (rowTy Ch sel mu P).inv →* GLG (E := X.E) (n := R.r) (SG := Pr.vGs) where
  toFun x v := blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t)
    ⟨x.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P x.2 v)⟩
  map_one' := by
    funext v
    exact map_one (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
  map_mul' a b := by
    funext v
    exact map_mul (blk0 (R.N R.m - 1) (𝓞 X.E ⧸ v.1.asIdeal) (r_le_X' R) (List.replicate R.m R.t))
      ⟨a.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P a.2 v)⟩ ⟨b.2.1 (inL sel mu v), HPar_le _ _ _ (memP Ch sel mu P b.2 v)⟩

end Rows

section Rows2

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (P : LevFam X.E X.K R.r Pr.vGs)

def incl : FormG (rowTyKK Ch sel mu).inv →* FormG (rowTy Ch sel mu P).inv :=
  MonoidHom.prodMap (MonoidHom.id _) (Subgroup.inclusion (grp_le Ch sel mu P))

theorem incl_injective : Function.Injective (incl Ch sel mu P) := by
  intro a b e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg (fun x => (x.2 : GLG (E := X.E) (n := R.N R.m - 1) (SG := rowSG Pr sel mu))) e
  exact Prod.ext e1 (Subtype.ext e2)

theorem range_incl : (incl Ch sel mu P).range = (blkMap Ch sel mu P).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    funext v
    have h := y.2.2 (inL sel mu v) (Set.mem_univ _)
    change y.2.1 (inL sel mu v) ∈ (rowTyKK Ch sel mu (inL sel mu v)).H at h
    rw [rowTyKK_inL] at h
    exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ _).mp h
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    have hmem : x.2.1 ∈ (rowTyKK Ch sel mu).inv.grp := by
      intro w _
      change x.2.1 w ∈ (rowTyKK Ch sel mu w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e1 := rowTyKK_inL Ch sel mu ⟨w.1, hw⟩
        change rowTyKK Ch sel mu w = _ at e1
        rw [e1]
        exact (GlobalTheory.RowLevIndex.mem_HK_iff (r_le_X' R) _ _ (HPar_le _ _ _ (memP Ch sel mu P x.2 ⟨w.1, hw⟩))).mpr
          (congrFun hx ⟨w.1, hw⟩)
      · rw [← rowTy_H_of_not Ch sel mu P w hw]
        exact x.2.2 w (Set.mem_univ _)
    exact ⟨(x.1, ⟨x.2.1, hmem⟩), rfl⟩

open Classical in
theorem range_blkMap : (blkMap Ch sel mu P).range = P.grp := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    intro v _
    obtain ⟨_, h0⟩ := mem_HPar.mp (memP Ch sel mu P x.2 v)
    exact h0
  · intro hp
    let h : GLG (E := X.E) (n := R.N R.m - 1) (SG := rowSG Pr sel mu) := fun w =>
      if hw : w.1 ∈ Pr.vGs then diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) else 1
    have hmem : h ∈ (rowTy Ch sel mu P).inv.grp := by
      intro w _
      change h w ∈ (rowTy Ch sel mu P w).H
      by_cases hw : w.1 ∈ Pr.vGs
      · have e2 := rowTy_inL Ch sel mu P ⟨w.1, hw⟩
        change rowTy Ch sel mu P w = _ at e2
        rw [e2]
        have hh : h w = diagEmb _ (r_le_X' R) (p ⟨w.1, hw⟩) := dif_pos hw
        rw [hh]
        exact mem_HPar.mpr ⟨diagEmb_mem_blockUT _ _ _, by
          rw [GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p ⟨w.1, hw⟩) _ _ rfl]; exact hp ⟨w.1, hw⟩ (Set.mem_univ _)⟩
      · have hh : h w = 1 := dif_neg hw
        rw [hh]
        exact Subgroup.one_mem _
    refine ⟨((1 : UF X.E (R.N R.m - 1)), ⟨h, hmem⟩), ?_⟩
    funext v
    exact GlobalTheory.RowLevIndex.firstDiagonalBlock_of_diagonal_embedding _ _ (p v) _ _ (dif_pos v.2)

end Rows2

theorem index_eq : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (P : LevFam X.E X.K R.r Pr.vGs), ∃ ι : (mtildeKGSD W Ch sel mu).G →* (mtildeGSD W Ch sel mu P).G, Function.Injective ι ∧ (∀ (a : (mtildeKGSD W Ch sel mu).G) (d : (mtildeKGSD W Ch sel mu).D), ι a • d = a • d) ∧ ι.range.index = Nat.card P.grp := by
  intro X Pr R W Ch sel S mu P
  refine ⟨incl Ch sel mu P, incl_injective Ch sel mu P, fun a d => rfl, ?_⟩
  rw [range_incl, Subgroup.index_ker, range_blkMap]

end GlobalTheory.RowLevIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormula
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

open GlobalTheory.JSW

theorem GlobalTheory.JSW.shintani_formula : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  intro E _ _ w n ψ hψ W α hN hK hH ϖ hϖ l
  have hvan := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w n ψ hψ W hN hK ϖ hϖ
  have hrec := GlobalTheory.T.sphericalWhittaker_torus_hecke_recursion E w n ψ hψ W α hN hK hH ϖ hϖ
  have hq : ((qV E w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (GlobalTheory.LFun.qV_ne_zero w)
  have hes : ∀ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ)) (MvPolynomial.esymm (Fin n) ℤ j) =
      (Finset.univ.val.map fun i => (α i : ℂ)).esymm j := fun j => by
    rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ]
    rfl
  let V : (Fin n → ℕ) → ℂ := fun m =>
    (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((m) k : ℕ) : ℂ))) / 2) *
      W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
        (MulEquiv.piUnits.symm fun i => ϖ ^ (m) i))
  let U : (Fin n → ℕ) → ℂ := fun m => if Antitone m then schurAt m (fun i => (α i : ℂ)) * W 1 else 0
  have hVU : V = U := by
    refine _root_.GlobalTheory.pieri_recursion_unique n (fun j => (Finset.univ.val.map fun i => (α i : ℂ)).esymm j) V U
      (fun m hm => by simp only [V, hvan m hm, mul_zero]) (fun m hm => by simp only [U, if_neg hm])
      (fun m hm j hj => hrec m hm j hj) (fun m hm j hj => ?_) ?_
    · have hp := congrArg (MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (α i : ℂ))) (_root_.GlobalTheory.JSW.esymm_mul_schur n m hm j hj)
      rw [MvPolynomial.eval₂_mul, hes, MvPolynomial.eval₂_sum] at hp
      simp only [U, if_pos hm]
      rw [← Finset.sum_filter, Finset.filter_filter, ← Finset.sum_mul, ← mul_assoc]
      simp only [schurAt]
      rw [hp]
    · have h1 : (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
          (MulEquiv.piUnits.symm fun i => ϖ ^ (0 : Fin n → ℕ) i)) = 1 := by
        ext i j
        simp [Matrix.one_apply, Matrix.diagonal_apply]
      have h0 : (0 : Fin n → ℕ) = fun _ => 0 := rfl
      have ha0 : Antitone (0 : Fin n → ℕ) := antitone_const
      have hs : schurAt (0 : Fin n → ℕ) (fun i => (α i : ℂ)) = 1 := by
        rw [h0, schurAt, GlobalTheory.JSW.schur_zero, MvPolynomial.eval₂_one]
      have hU : U 0 = W 1 := by
        change (if Antitone (0 : Fin n → ℕ) then schurAt 0 (fun i => (α i : ℂ)) * W 1 else 0) = W 1
        rw [if_pos ha0, hs, one_mul]
      rw [hU]
      change _ * W _ = W 1
      rw [h1]
      simp
  have hl := congrFun hVU l
  simp only [V, U] at hl
  by_cases ha : Antitone l
  · rw [if_pos ha] at hl
    have hne : (qV E w : ℂ) ^ ((∑ k : Fin n, (((n : ℂ) - 1 - 2 * (k : ℕ)) * (((l) k : ℕ) : ℂ))) / 2) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hq]; exact Complex.exp_ne_zero _
    rw [sphW, if_pos ha, neg_div, Complex.cpow_neg, mul_assoc, ← hl, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  · rw [hvan l ha, GlobalTheory.JSW.sphW_of_not_antitone _ _ ha, zero_mul]
end

