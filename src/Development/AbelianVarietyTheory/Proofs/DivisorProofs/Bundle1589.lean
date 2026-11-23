module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1543
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1526
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTorsionMemClosureGenerators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomKillsTorsionOfComplexPointsOneEmbedding
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeyl
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.SpGen
open Matrix

theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  have hExists : ∃ X : Matrix κ κ K, X.IsSymm ∧ IsUnit (A + X * C).det := by
    -- Use the field case of Mathlib's construction in LinearAlgebra/SymplecticGroup.
    have hker (x : κ → K) (hAx : A • x = 0) (hCx : C • x = 0) : x = 0 := by
      rw [smul_eq_mulVec] at hAx hCx
      have hunit := (fromBlocks A B C D).isUnit_iff_isUnit_det.2
        (SymplecticGroup.symplectic_det hsp)
      have hzero : fromBlocks A B C D *ᵥ Sum.elim x 0 =
          fromBlocks A B C D *ᵥ Sum.elim 0 0 := by
        simp [fromBlocks_mulVec, hAx, hCx]
      exact (Sum.elim_eq_iff.1 (mulVec_injective_iff_isUnit.2 hunit hzero)).1
    have hsymm := (SymplecticGroup.fromBlocks_mem_iff.1 hsp).1
    obtain ⟨V, U, e, hV, hU, heq⟩ := exists_rank_normal_form C
    set R := V * C * U with hR
    set S := Vᵀ⁻¹ * A * U with hS
    let f := fun M : Matrix κ κ K ↦ M.submatrix e.symm e.symm
    have hf (M : Matrix κ κ K) : f M = M.submatrix e.symm e.symm := rfl
    have f_unit {M} : IsUnit M → IsUnit (f M) := (isUnit_submatrix_equiv ..).2
    have f_mul (M N) : f (M * N) = f M * f N := submatrix_mul _ _ _ _ _ e.symm.bijective
    let _ : Invertible V := hV.invertible
    let _ : Invertible U := hU.invertible
    let _ : Invertible (f Vᵀ) := (f_unit (V.isUnit_transpose.2 hV)).invertible
    have hker' (x : Fin C.rank ⊕ Fin (Fintype.card κ - C.rank) → K)
        (hxS : f S • x = 0) (hxR : f R • x = 0) : x = 0 := by
      refine (f_unit hU).smul_left_cancel.1 ?_
      rw [f_mul, f_mul, mul_assoc, mul_smul, IsUnit.smul_eq_zero, mul_smul, hf,
        smul_eq_mulVec, submatrix_mulVec_equiv, Equiv.symm_symm] at hxS hxR
      · rw [Equiv.comp_symm_eq, Pi.zero_comp] at hxS hxR
        exact e.surjective.injective_comp_right <| by simpa using hker _ hxS hxR
      · exact f_unit hV
      · exact f_unit <| isUnit_nonsing_inv_iff.2 <| V.isUnit_transpose.2 hV
    have hSR : Sᵀ * R = Rᵀ * S := by
      simp only [hR, mul_assoc, transpose_mul, transpose_nonsing_inv, transpose_transpose, hS,
        inv_mul_cancel_left_of_invertible, mul_inv_cancel_left_of_invertible]
      rw [← mul_assoc Aᵀ, hsymm, mul_assoc]
    have hblocks : (f S).toBlocks₁₁ᵀ = (f S).toBlocks₁₁ ∧ (f S).toBlocks₁₂ = 0 := by
      apply_fun reindex e e at hSR
      rw [reindex_apply, reindex_apply, ← hf, ← hf, f_mul, f_mul Rᵀ, heq, hf,
        ← transpose_submatrix, ← hf S, ← (f S).fromBlocks_toBlocks, hf (_)ᵀ, hf
        ((fromBlocks 1 0 0 0).submatrix _ _)] at hSR
      simp [fromBlocks_transpose, fromBlocks_multiply] at hSR
      tauto
    have h₂₂ : IsUnit (f S).toBlocks₂₂ := by
      refine mulVec_injective_iff_isUnit.1 ?_
      rw [← coe_mulVecLin, ← LinearMap.ker_eq_bot]
      refine ker_mulVecLin_eq_bot_iff.2 fun x hx ↦ Sum.elim_injective' <|
        (hker' _ ?_ ?_).trans Sum.elim_zero_zero.symm
      · rw [← (f S).fromBlocks_toBlocks]
        simp [hx, hblocks.2, fromBlocks_mulVec]
      · simp [hf, heq, fromBlocks_mulVec]
    set Y : Matrix (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank))
      (Fin C.rank ⊕ Fin (Fintype.card κ - C.rank)) K :=
      fromBlocks (1 - (f S).toBlocks₁₁) 0 0 0 with hY
    have hYsymm : Y.IsSymm := by
      rw [hY, isSymm_fromBlocks_iff]
      exact ⟨IsSymm.sub isSymm_one hblocks.1, by simp⟩
    set X := f Vᵀ * Y * f V with hX
    refine ⟨X.submatrix e e, IsSymm.submatrix ?_ e, (isUnit_iff_isUnit_det _).1
      ((isUnit_submatrix_equiv e.symm e.symm).1 ?_)⟩
    · simp_rw [hX, Matrix.IsSymm, transpose_mul, hYsymm.eq, hf, transpose_submatrix,
        transpose_transpose, mul_assoc]
    · have hsum : f (A + X.submatrix e e * C) = f Vᵀ * (f S + Y * f R) * f U⁻¹ := by
        simp_rw [hf, submatrix_add, Pi.add_apply, hS, hR, ← hf, f_mul, hf, mul_add, ← mul_assoc,
          ← inv_submatrix_equiv, add_mul, mul_assoc _ (U.submatrix _ _), mul_inv_of_invertible]
        simp [hX]
        rfl
      rw [← hf, hsum, IsUnit.mul_iff, IsUnit.mul_iff]
      refine ⟨⟨isUnit_of_invertible _, ?_⟩, f_unit (isUnit_nonsing_inv_iff.2 hU)⟩
      nth_rw 1 [hY, heq, ← (f S).fromBlocks_toBlocks, hblocks.2]
      simpa [hf, fromBlocks_multiply, fromBlocks_add] using h₂₂
  obtain ⟨X, hX, hu⟩ := hExists
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LatBound

theorem exists_mul_mem_integers {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {T : Type} [Fintype T] (w : T → Fv F v) :
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ t, c * w t ∈ v.adicCompletionIntegers F := by
  classical
  have key : ∀ x : Fv F v, ∃ c : Fv F v, c ≠ 0 ∧ c ∈ v.adicCompletionIntegers F ∧
      c * x ∈ v.adicCompletionIntegers F := by
    intro x
    by_cases hx : x ∈ v.adicCompletionIntegers F
    · exact ⟨1, one_ne_zero, one_mem _, by simpa using hx⟩
    · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
      refine ⟨x⁻¹, inv_ne_zero hx0, ?_, by rw [inv_mul_cancel₀ hx0]; exact one_mem _⟩
      exact ((v.adicCompletionIntegers F).mem_or_inv_mem x).resolve_left hx
  choose cw hcw0 hcwO hcw using key
  refine ⟨∏ t, cw (w t), Finset.prod_ne_zero_iff.2 fun t _ => hcw0 _, fun t => ?_⟩
  rw [← Finset.mul_prod_erase Finset.univ (fun t => cw (w t)) (Finset.mem_univ t), mul_comm (cw (w t)), mul_assoc]
  exact mul_mem (prod_mem fun t' _ => hcwO _) (hcw _)

theorem locCo_latAtV_bounded : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    {B : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → AF F}
    {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ), X.L.IsLattice E → Y.L.IsLattice E →
    ∃ c : Fv F v, c ≠ 0 ∧ ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ i,
      c * (GlobalTheory.LatVac.locCo co v γ).1 i ∈ v.adicCompletionIntegers F ∧
      c * (GlobalTheory.LatVac.locCo co v γ).2 i ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ n d X Y v B κ _ co hX hY
  obtain ⟨M, _, g, hg⟩ := GlobalTheory.LatParam.latAtV_param X Y hX hY v
  obtain ⟨c, hc0, hc⟩ := exists_mul_mem_integers v
    (fun t : Bool × M × κ => if t.1 then (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).1 t.2.2
      else (GlobalTheory.LatVac.locCo co v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F (g t.2.1))).2 t.2.2)
  have hsmul : ∀ (t : Fv F v) z, GlobalTheory.LatVac.locCo co v (GlobalTheory.EmbChart.atPlace v t • z) =
      t • GlobalTheory.LatVac.locCo co v z := by
    intro t z
    simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
    ext k <;> simp [smul_eq_mul, map_mul, GlobalTheory.EmbChart.evFin_atPlace]
  refine ⟨c, hc0, fun γ hγ i => ?_⟩
  obtain ⟨a, rfl⟩ := (hg γ).1 hγ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hsmul, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  constructor
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (true, m, i))
  · refine sum_mem fun m _ => ?_
    rw [mul_left_comm]
    exact mul_mem (a m).2 (by simpa using hc (false, m, i))

end GlobalTheory.LatBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeSplitPlaceEqAddComponentParts
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tmul_smul_gen {n d : ℕ} (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (a : Fv F v) (o : 𝓞 E) (c : AF F) (x : Fin n → E)
    (y : Fin d → E) :
    ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • (c • incM F (Matrix.vecMulVec x y))) =
      (GlobalTheory.LatVac.liftV v a * c) • incM F (Matrix.vecMulVec (o • x) y) := by
  ext i j
  simp [incM, inclR, Matrix.vecMulVec_apply, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_assoc]

theorem tmul_smul_mem {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    ∀ γ ∈ latAtV X Y v, ((GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E) : AE F E) • γ) ∈ latAtV X Y v := by
  intro γ hγ
  induction hγ using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, hc, hci, x, hx, y, hy, rfl⟩ := hz
    rw [tmul_smul_gen]
    refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, rfl⟩
    · intro u hu
      rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
    · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
      exact mul_mem ha hci
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_lift {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v := by
  refine intLoc_induction (p := fun y => ∃ e : AE F E, compFin F E v e = y ∧ ∀ γ ∈ latAtV X Y v, e • γ ∈ latAtV X Y v)
    ?_ ?_ ?_ ?_ hy
  · intro a ha o
    refine ⟨GlobalTheory.LatVac.liftV v a ⊗ₜ[F] (o : E), ?_, tmul_smul_mem X Y v ha o⟩
    simp [compFin, GlobalTheory.LatVac.evFin_liftV]
  · exact ⟨0, map_zero _, fun γ _ => by rw [zero_smul]; exact zero_mem _⟩
  · intro y z hy hz
    obtain ⟨e, he, he'⟩ := hy
    obtain ⟨f, hf, hf'⟩ := hz
    exact ⟨e + f, by rw [map_add (f := _), he, hf], fun γ hγ => by rw [add_smul]; exact add_mem (he' γ hγ) (hf' γ hγ)⟩
  · intro y hy
    obtain ⟨e, he, he'⟩ := hy
    exact ⟨-e, by rw [map_neg, he], fun γ hγ => by rw [neg_smul]; exact neg_mem (he' γ hγ)⟩

theorem map_piW_smul {n d : ℕ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (t : E →ₐ[F] Fv F v) (e : AE F E)
    (γ : Matrix (Fin n) (Fin d) (AE F E)) : (e • γ).map (piW t) = piW t e • γ.map (piW t) := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply, map_mul]

end GlobalTheory.SplitPlaceLat

namespace GlobalTheory.SplitPlaceLat

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

theorem latAtV_eq_add_parts : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E)),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γA ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
      ∃ γB ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
        γ = γA + γB ∧ γA.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW Bs.τ₁) = 0 ∧
          γB.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (Bs.τ₁.comp D.sp.cm.sig)) = 0 := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ γ hγ
  have h := hTr.base.cm
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitPlaceLat.exists_lift {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁
    (splitIdem_mem h Bs.τ₁)
  have p1 : piW Bs.τ₁ e = 1 := by
    change splitProj Bs.τ₁ (compFin _ _ _ e) = 1
    rw [he]; exact splitProj_splitIdem h _
  have p2 : piW (Bs.τ₁.comp D.sp.cm.sig) e = 0 := by
    change splitProj (Bs.τ₁.comp D.sp.cm.sig) (compFin _ _ _ e) = 0
    rw [he]; exact splitProj_comp_splitIdem h _
  refine ⟨γ - e • γ, sub_mem hγ (he' γ hγ), e • γ, he' γ hγ, (sub_add_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, map_sub, map_mul, p1]
  · rw [GlobalTheory.SplitPlaceLat.map_piW_smul, p2, zero_smul]

end GlobalTheory.SplitPlaceLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionCmUnitaryShimuraMemClosureLinearHomImages
section
set_option autoImplicit false

open NumberField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.TorsGen

theorem exists_linear_pow_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (A B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (G : A.t.G ⟶ B.t.G),
    GlobalTheory.Serre.IsLinearHom A.t.act B.t.act G → ∀ m : ℕ, 0 < m →
    (∀ x : Over.mk (spMap (σ.comp (algebraMap (𝓞 K) K))) ⟶ A.t.G, x ^ m = 1 → x ≫ G = 1) →
    ∃ F : A.t.G ⟶ B.t.G, GlobalTheory.Serre.IsLinearHom A.t.act B.t.act F ∧ F ^ m = G := by
  intro E _ _ _ H K _ _ σ A B G hG m hm hker
  have hGm := hG.isMonHom
  obtain ⟨_, hfl, hsu, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp (𝓞 K)) A.pol m hm
  have : Flat (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m).left := hfl
  have : Surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m).left := hsu
  have hc : IsCommMonObj A.t.G := A.ab.comm
  have hcB : IsCommMonObj B.t.G := B.ab.comm
  have hall := _root_.GlobalTheory.TorsionKill.kill_torsion E H K σ A B G hGm m hm hker
  obtain ⟨F, hF⟩ := GlobalTheory.DivisibleHom.exists_factor (A := A.t.G) m G hall
  have hFm : IsMonHom (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m ≫ F) := hF ▸ hGm
  have : IsMonHom F := GlobalTheory.DivisibleHom.isMonHom_of_factor m F
  refine ⟨F, ⟨this, fun c => ?_⟩, by rw [← hF, GlobalTheory.DivisibleHom.mulA_comp]⟩
  have := A.t.act.hom c
  have := B.t.act.hom c
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (ReciprocityTheory.ChartRestriction.G.Out.mulA A.t.G m)
  rw [← Category.assoc, GlobalTheory.DivisibleHom.mulA_comp, ← GlobalTheory.DivisibleHom.comp_mulA, Category.assoc, hF, hG.comm,
    ← Category.assoc, hF]

theorem gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (n : ℕ), 0 < n →
    ∀ y : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G, y ^ n = 1 →
    y ∈ Submonoid.closure {w : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ X.B.t.G |
      ∃ (x : Over.mk (spMap (σ₁.comp (algebraMap (𝓞 K) K))) ⟶ (X.A true).t.G) (f : (X.A true).t.G ⟶ X.B.t.G),
        x ^ n = 1 ∧ GlobalTheory.Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
        (∃ m : ℕ, 0 < m ∧ ∃ z : Fin p → 𝓞 E, f ^ m = ∏ a, ((X.A true).t.act.act (z a) ≫ GlobalTheory.FlatCM.phiP X a)) ∧
        w = x ≫ f} := by
  intro E _ _ _ H hH K _ _ ρ σ₁ p X n hn y hy
  refine Submonoid.closure_mono ?_ (GlobalTheory.T.cm_torsion_mem_closure_generators E H hH K ρ σ₁ p X n hn y hy)
  rintro w ⟨m, x, z, hm, hx, hG, rfl⟩
  obtain ⟨F, hF, hFm⟩ := exists_linear_pow_eq E H K σ₁ (X.A true) X.B _
    (GlobalTheory.FlatCM.HomLat.isLinearHom_prod X z) m hm hG
  have := hF.isMonHom
  refine ⟨x ^ m, F, ?_, hF, ⟨m, hm, z, hFm⟩, ?_⟩
  · rw [← pow_mul, mul_comm, hx]
  · rw [← hFm, MonObj.comp_pow, MonObj.pow_comp]

end GlobalTheory.FlatCM.TorsGen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticAddSelfExpansionHalfIdempotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplectic_add_self_expansion_half_idempotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : E, θ + σ θ = 1 →
    ∀ γ γ' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ') =
        GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                     (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ' +
          2 * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' := by
  first | exact @GlobalTheory.VacExpand.symp_add_self_expand | exact GlobalTheory.VacExpand.symp_add_self_expand | (intros; apply GlobalTheory.VacExpand.symp_add_self_expand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen.SympAct

theorem hTens_eq_mat {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_actB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E) : symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  have key : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E).map c)ᵀ by
      ext i j; simp [Matrix.mul_apply, map_sum, map_mul]]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc x * ((g : GL β E) : Matrix β β E)ᵀ * JB * (((g : GL β E) : Matrix β β E).map c * (y.map c)ᵀ)
        = x * (((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c) * (y.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_mat, hTens_eq_mat, key]

end GlobalTheory.DblVacEigen.SympAct
end

