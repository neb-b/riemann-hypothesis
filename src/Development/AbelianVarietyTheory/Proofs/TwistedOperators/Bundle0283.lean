module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelMultiplicativeEqProdDiagonalValuations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelati
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTransformEqAtThetaLiftOfVacuumEq
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem prodId1 : ∀ (n : ℕ) (qu : ℂˣ) (Y : ℂ), Y ≠ 0 → ∀ (α : Fin (n / 2) → ℂˣ) (d : Fin (n / 2) → ℤ), (∏ k, Y ^ d k) * ∏ r : Fin (n / 2), (Y * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ (-d r.rev) = ∏ k, ((α k : ℂ) * (qu : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n qu Y hY α d
  have hq := qu.ne_zero
  have hα : ∀ k, (α k : ℂ) ≠ 0 := fun k => (α k).ne_zero
  rw [← Equiv.prod_comp Fin.revPerm]
  conv_rhs => rw [← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.zpow_neg, ← div_eq_mul_inv, ← div_zpow]
  congr 1
  have e : ((n / 2 : ℕ) : ℤ) - 1 - ((k : ℕ) : ℤ) = ((k.rev : ℕ) : ℤ) := by
    have := k.isLt
    rw [Fin.val_rev]; omega
  rw [e, _root_.zpow_neg]
  have := hα k.rev
  have := zpow_ne_zero ((n : ℤ) - 1 - 2 * ((k.rev : ℕ) : ℤ)) hq
  field_simp

theorem prodId2 : ∀ (n n' : ℕ) (hn : n ≤ n') (qu : ℂˣ) (α : Fin (n / 2) → ℂˣ) (d : Fin (n' / 2) → ℤ), (∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ d k) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d ⟨n' / 2 - n / 2 + r.1, by omega⟩ = ∏ k, ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n n' hn qu α d
  have hq := qu.ne_zero
  have hfac : ∀ k : Fin (n' / 2), ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) =
      ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) * (if h : n' / 2 - n / 2 ≤ k.1 then
        ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ))) /
          (α (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩) : ℂ)) else 1) := by
    intro k
    unfold liftPar
    split_ifs with h1 h2 h2
    · omega
    · push_cast
      rw [mul_one, mul_assoc, ← zpow_add₀ hq]
      congr 2; ring
    · have e : (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩ : Fin (n / 2)) = ⟨n' / 2 - 1 - k.1, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [e]
      have e2 : (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ))) = (qu : ℂ) ^ (-(n : ℤ)) * ((qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ)))) := by
        rw [← zpow_add₀ hq, ← zpow_add₀ hq]
        congr 1
        have := k.isLt
        omega
      rw [e2]
      push_cast
      rw [pow_add]
      have := (α ⟨n' / 2 - 1 - k.1, by omega⟩).ne_zero
      field_simp
    · omega
  simp only [hfac, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  symm
  rw [← Fin.prod_congr' _ (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega), Fin.prod_univ_add]
  rw [Finset.prod_eq_one (fun i _ => ?_), one_mul]
  · refine Finset.prod_congr rfl fun r _ => ?_
    have e : Fin.cast (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega) (Fin.natAdd (n' / 2 - n / 2) r) =
        ⟨n' / 2 - n / 2 + r.1, by omega⟩ := Fin.ext (by simp)
    rw [e, dite_eq_left (by simp)]
    simp only [Fin.val_mk, Nat.add_sub_cancel_left, Fin.eta]
  · rw [dite_eq_right (by simp; omega), _root_.one_zpow]

theorem satU_eq_satU_liftPar_of_heckeVec_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → n ≤ n' → ∀ h ∈ Hecke ℂ (KU σ n), ∀ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s → ∀ qu : ℂˣ, (qu : ℂ) = q → ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h' (fun i => (liftPar qu n n' α i : ℂ)) := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC hC' hnn h hh h' hh' hE qu hqu α
  have hU := hS.1.unr
  obtain ⟨ℓ, hℓs, hℓa, hℓ0, hℓu, hℓz⟩ := _root_.GlobalTheory.SphTheta.exists_mixLat_form L ϖ σ q δ ψ n n' M ρ ω s hS
  have hvac : LocVac ρ s := hS.2.2.1
  have hb1 : ∀ {N : ℕ}, IsBorelU (1 : GU σ N) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_gt hij)]
  have hmix := _root_.GlobalTheory.SphTheta.mixLat_form_borel L ϖ σ q δ ψ n n' M ρ ω s hS ℓ hℓa hℓu
  have hμ : ∀ b : GU σ n, IsBorelU b → ℓ (ω (b, 1) s) =
      ∏ k, ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n')) ^ ordL (b.1.1 (lo n k) (lo n k)) := by
    refine _root_.GlobalTheory.BorelChar.borel_char L ϖ σ q hU n (fun g => ℓ (ω (g, 1) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (b * b', 1) s = ω (b, 1) (ω (b', 1) s) := by
        rw [show ((b * b', 1) : GU σ n × GU σ n') = (b, 1) * (b', 1) by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix b 1 hb hb1).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup L ϖ σ q δ ψ n n' M ρ ω s hS hC ℓ hℓs hℓa hℓ0 k t ht, hqu]
  have hμ' : ∀ b : GU σ n', IsBorelU b → ℓ (ω (1, b) s) =
      ∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ ordL (b.1.1 (lo n' k) (lo n' k)) := by
    refine _root_.GlobalTheory.BorelChar.borel_char L ϖ σ q hU n' (fun g => ℓ (ω (1, g) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (1, b * b') s = ω (1, b) (ω (1, b') s) := by
        rw [show ((1, b * b') : GU σ n × GU σ n') = (1, b) * (1, b') by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix 1 b hb1 hb).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)).trans hℓs
    · intro k t ht
      rw [_root_.GlobalTheory.SphTheta.mixed_torus_value L ϖ σ q δ ψ n n' M ρ ω s hS hC' ℓ hℓs hℓa hℓ0 k t ht, hqu]
  obtain ⟨ι, _, b, hb, hvec, hsat⟩ := _root_.GlobalTheory.SatBorel.heckeVec_satU_borel L ϖ σ q hU n h hh
  obtain ⟨κ, _, b', hb', hvec', hsat'⟩ := _root_.GlobalTheory.SatBorel.heckeVec_satU_borel L ϖ σ q hU n' h' hh'
  have E := hE
  rw [hvec M (ω.comp (MonoidHom.inl _ _)) s (fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac),
    hvec' M (ω.comp (MonoidHom.inr _ _)) s (fun k hk => hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)] at E
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at E
  obtain ⟨hbl1, hbl2⟩ := _root_.GlobalTheory.SphTheta.lowBlocks_borel L ϖ σ q hU n n' hnn
  choose U hU1 hU2 hU3 using fun i => hbl1 (b i) (hb i)
  choose V hVt hV2 hV3 using fun j => hbl2 (b' j) (hb' j)
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (n / 2)) (Fin (n / 2)) L → Matrix (Fin (n' / 2)) (Fin (n / 2)) L,
      ∀ t, Z t = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0 :=
    ⟨_, fun _ => rfl⟩
  have hZmul : ∀ t A, Z t * A = Z (t * A) := by
    intro t A; ext r c
    simp only [hZ, Matrix.mul_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hZint : ∀ t, Z t ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) ↔ t ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) := by
    intro t
    constructor
    · intro ht i j
      have := ht ⟨i.1, by omega⟩ j
      simpa [hZ] using this
    · intro ht i j
      simp only [hZ, Matrix.of_apply]
      split_ifs
      exacts [ht _ _, zero_mem _]
  have hlow1 : ∀ N : ℕ, lowBlock (((1 : GU σ N) : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) = 1 := by
    intro N
    simp only [OneMemClass.coe_one, Units.val_one, lowBlock]
    exact Matrix.submatrix_one _ (fun a b e => by simp [hi, Fin.ext_iff] at e; exact Fin.ext (by omega))
  have key : ∀ t : GL (Fin (n / 2)) L,
      ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) =
      ∑ j, (h' (b' j) * ℓ (ω (1, b' j) s)) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
    intro t
    have l1 : ∀ i, ℓ (ρ (embLow n' n (Z t.1)) (ω (b i, 1) s)) =
        ℓ (ω (b i, 1) s) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro i
      rw [(hmix (b i) 1 (hb i) hb1).2, inv_one, hlow1, Matrix.one_mul, ← hU1 i, hZmul, hℓz, hZint]
    have l2 : ∀ j, ℓ (ρ (embLow n' n (Z t.1)) (ω (1, b' j) s)) =
        ℓ (ω (1, b' j) s) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro j
      have e3 := hV3 j t.1
      simp only [← hZ] at e3
      rw [(hmix 1 (b' j) hb1 (hb' j)).2, hlow1, Matrix.mul_one, e3, hℓz, hZint]
    have := congrArg (fun v => ℓ (ρ (embLow n' n (Z t.1)) v)) E
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, l1, l2] at this
    simpa only [mul_assoc] using this
  have G := _root_.GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator L ϖ σ q hU (n / 2) ι κ _ _ U V hU2 hVt key
    (fun d => ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
      (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d r)
  have hY : ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') : ℂ) ≠ 0 := by
    have := qu.ne_zero
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ this)
  rw [hsat α, hsat' (liftPar qu n n' α)]
  simp only [← hqu]
  calc _ = ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
        (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ ordL ((U i).1 r r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμ _ (hb i), mul_assoc, ← prodId1 n qu _ hY α]
        simp only [hU3]
    _ = _ := G
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hμ' _ (hb' j), mul_assoc, ← prodId2 n n' hnn qu α]
        simp only [hV2]

end GlobalTheory.SphTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFiniteDense

open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.TypeSum

section WordCurve

variable {n : ℕ}

theorem dRep_fsum {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Mx n → (H →L[ℂ] H)} (h : Std ε σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (c : ι → ℂ) (w : ι → H) (hw : ∀ j, Sm ε σ (w j)) :
    dRep σ Z (∑ j ∈ s, c j • w j) = ∑ j ∈ s, c j • dRep σ Z (w j) := by
  classical
  have hl : ∀ Y ∈ [Z], Y ∈ lieSet ε := by simpa using hZ
  have hsm : ∀ t : Finset ι, Sm ε σ (∑ j ∈ t, c j • w j) := fun t =>
    (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).sum_mem fun j _ =>
      (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem _ (hw j)
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul h.1 hl (0 : ℂ) (x := (0 : H)) (GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).zero_mem
    simp only [zero_smul, Dw, List.foldr_cons, List.foldr_nil] at this
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have e1 := Dw_add h.1 hl ((GlobalTheory.LowTypeDetermined.smooth (Jm ε) σ).smul_mem (c a) (hw a)) (hsm s)
    have e2 := Dw_smul h.1 hl (c a) (hw a)
    simp only [Dw, List.foldr_cons, List.foldr_nil] at e1 e2
    rw [e1, e2, ih]

theorem exists_coord (ε : Fin n → Bool) : ∃ (d : ℕ) (B : Fin d → Mx n) (φ : Fin d → (Mx n →ₗ[ℝ] ℝ)),
    (∀ i, B i ∈ lieSet ε) ∧ ∀ Y ∈ lieSet ε, Y = ∑ i, φ i Y • B i := by
  let b := Module.finBasis ℝ (GlobalTheory.LowTypeDetermined.lie (Jm ε))
  choose g hg using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨_, fun i => b i, g, fun i => (b i).2, fun Y hY => ?_⟩
  have e := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at e
  conv_lhs => rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := LinearMap.congr_fun (hg i) ⟨Y, hY⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [this]
  rfl

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem analyticAt_coord (X Y : Mx n) (φ : Mx n →ₗ[ℝ] ℝ) :
    AnalyticAt ℝ (fun t : ℝ => ((φ (NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) : ℝ) : ℂ)) 0 := by
  have h1 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (t • X)) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const)
  have h2 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X))) 0 :=
    AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _) (analyticAt_id.smul analyticAt_const).neg
  have h3 : AnalyticAt ℝ (fun t : ℝ => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) 0 :=
    (h2.fun_mul analyticAt_const).fun_mul h1
  have h4 := ((LinearMap.toContinuousLinearMap φ).analyticAt _).comp h3
  exact (Complex.ofRealCLM.analyticAt _).comp h4

end

theorem wordCurve : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), GlobalTheory.TypeSum.Std ε σ → ∀ X : Matrix (Fin n) (Fin n) ℂ, X ∈ GlobalTheory.SmoothGlob.lieSet ε → ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ Y ∈ l, Y ∈ GlobalTheory.SmoothGlob.lieSet ε) → ∀ v : H, Formalism.MainNotions.S.IsKFin ε σ v → ∃ (m : ℕ) (c : Fin m → ℝ → ℂ) (w : Fin m → H), (∀ j, AnalyticAt ℝ (c j) 0) ∧ (∀ j, Formalism.MainNotions.S.IsKFin ε σ (w j)) ∧ ∀ t : ℝ, List.foldr (Formalism.L2.Theta.dRep σ) v (l.map fun Y => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)) = ∑ j, c j t • w j := by
  intro n ε H _ _ _ σ h X hX l hl v hv
  obtain ⟨d, B, φ, hB, hφ⟩ := exists_coord (n := n) ε
  induction l with
  | nil => exact ⟨1, fun _ _ => 1, fun _ => v, fun _ => analyticAt_const, fun _ => hv, fun t => by simp⟩
  | cons Y l ih =>
    obtain ⟨m, c, w, hc, hw, he⟩ := ih (fun Z hZ => hl Z (List.mem_cons_of_mem _ hZ))
    have hY := hl Y List.mem_cons_self
    let A : ℝ → Mx n := fun t => NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X)
    have hA : ∀ t, A t ∈ lieSet ε := fun t => by
      show NormedSpace.exp (-(t • X)) * Y * NormedSpace.exp (t • X) ∈ lieSet ε
      rw [Matrix.exp_neg]
      exact GlobalTheory.LowTypeDetermined.conj_mem_lie (isUnit_Jm ε) (exp_mem_UJ hX t) hY
    let e := (finProdFinEquiv (m := m) (n := d)).symm
    refine ⟨m * d, fun k t => c (e k).1 t * ((φ (e k).2 (A t) : ℝ) : ℂ),
      fun k => dRep σ (B (e k).2) (w (e k).1), fun k => (hc _).fun_mul (analyticAt_coord X Y _),
      fun k => isKFin_dRep n ε H σ h _ (hw _) _ (hB _), fun t => ?_⟩
    rw [List.map_cons, List.foldr_cons, he t]
    change dRep σ (A t) _ = _
    rw [dRep_fsum h (hA t) Finset.univ _ w (fun j => h.2.2.1 _ (hw j))]
    have hs : ∀ j, dRep σ (A t) (w j) = ∑ i, ((φ i (A t) : ℝ) : ℂ) • dRep σ (B i) (w j) := fun j => by
      conv_lhs => rw [hφ _ (hA t)]
      exact h.dRep_sum hB (h.2.2.1 _ (hw j)) _
    simp only [hs, Finset.smul_sum, smul_smul]
    rw [← Fintype.sum_prod_type']
    exact (Fintype.sum_equiv e _ _ fun k => rfl).symm

end WordCurve

theorem eq_zero_of_iteratedDeriv_eq_zero : ∀ f : ℝ → ℂ, AnalyticOnNhd ℝ f Set.univ → (∀ m : ℕ, iteratedDeriv m f 0 = 0) → ∀ t, f t = 0 := by
  intro f hf h0 t
  obtain ⟨p, r, hp⟩ := hf 0 trivial
  have hc : ∀ m (y : ℝ), p m (fun _ => y) = 0 := by
    intro m y
    have e1 := hp.factorial_smul 1 m
    rw [← iteratedDeriv_eq_iteratedFDeriv, h0 m] at e1
    have e2 : p m (fun _ => (1 : ℝ)) = 0 := by
      exact (smul_eq_zero.1 e1).resolve_left (Nat.factorial_ne_zero m)
    have e3 := (p m).map_smul_univ (fun _ => y) (fun _ => (1 : ℝ))
    simp only [smul_eq_mul, mul_one] at e3
    rw [e3, e2, smul_zero]
  have hev : f =ᶠ[nhds 0] 0 := by
    have hb : Metric.eball (0 : ℝ) r ∈ nhds 0 := Metric.eball_mem_nhds 0 hp.r_pos
    filter_upwards [hb] with y hy
    have := hp.hasSum (y := y) (by simpa using hy)
    simp only [hc, zero_add] at this
    exact (this.unique hasSum_zero).symm ▸ rfl
  exact hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ trivial hev trivial

section Coef

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem analyticAt_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticAt ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) 0 := by
  obtain ⟨m, S, Λ, hS, hΛ⟩ := GlobalTheory.LowTypeDetermined.exists_factor (isUnit_Jm ε) h.1 hℓ
  have hsm : Sm ε σ v := h.2.2.1 v hv
  choose N c w hc hw he using fun i => wordCurve n ε H σ h X hX (S i) (hS i) v hv
  have key : ∀ t : ℝ, ℓ (σ (NormedSpace.exp (t • X)) v) =
      ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j)) := by
    intro t
    have hg := exp_mem_UJ hX t
    rw [hΛ _ (hsm.translate h.1 hg)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 := Dw_translate h.1 hg hsm (hS i)
    have e2 : (NormedSpace.exp (t • X))⁻¹ = NormedSpace.exp (-(t • X)) := (Matrix.exp_neg _).symm
    simp only [Dw] at e1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, e2, he i t, map_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have ha : ∀ i j, AnalyticAt ℝ (fun t : ℝ => Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    intro i j
    have := ((hHC.analytic h.1 h.2.1 (hw i j)).clm ((Λ i).restrictScalars ℝ)).analytic_exp (g := 1)
      (one_mem_UJ ε) hX 0
    simpa only [one_mul, ContinuousLinearMap.coe_restrictScalars'] using this
  have hsum : AnalyticAt ℝ (fun t : ℝ => ∑ i, ∑ j, c i j t * Λ i (σ (NormedSpace.exp (t • X)) (w i j))) 0 := by
    exact Finset.analyticAt_fun_sum _ fun i _ => Finset.analyticAt_fun_sum _ fun j _ => (hc i j).fun_mul (ha i j)
  exact hsum.congr (Filter.Eventually.of_forall fun t => (key t).symm)

theorem analyticOnNhd_coef (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {v : H} (hv : IsKFin ε σ v) {X : Mx n} (hX : X ∈ lieSet ε) :
    AnalyticOnNhd ℝ (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) v)) Set.univ := by
  intro t₀ _
  have hg := exp_mem_UJ hX t₀
  have h1 := analyticAt_coef hHC h (sobCont_translate h.1 hℓ hg) hv hX
  have h2 : AnalyticAt ℝ (fun t : ℝ => t - t₀) t₀ := analyticAt_id.sub analyticAt_const
  have h3 := h1.comp_of_eq h2 (sub_self t₀)
  refine h3.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_def, LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  rw [← sigma_mul h.1 hg (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem hasDerivAt_coef1 (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {u : H} (hu : Sm ε σ u)
    {X : Mx n} (hX : X ∈ lieSet ε) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) (ℓ (σ (NormedSpace.exp (s • X)) (dRep σ X u))) s := by
  have hs := exp_mem_UJ hX s
  have h1 := h.hasDerivAt_sobFun ((sobFun_of_sobCont hℓ).translate h.1 hs) hu hX
  have h2 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact h1)
  refine HasDerivAt.congr_of_eventuallyEq h2 (Filter.Eventually.of_forall fun t => ?_)
  show _ = ℓ (σ _ (σ _ u))
  rw [← sigma_mul h.1 hs (exp_mem_UJ hX _), ← exp_add_smul, add_sub_cancel]

theorem isKFin_iterate (h : Std ε σ) {X : Mx n} (hX : X ∈ lieSet ε) (m : ℕ) {u : H} (hu : IsKFin ε σ u) :
    IsKFin ε σ ((dRep σ X)^[m] u) := by
  induction m with
  | zero => exact hu
  | succ m ih => rw [Function.iterate_succ_apply']; exact isKFin_dRep n ε H σ h _ ih X hX

theorem iteratedDeriv_coef (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ} (hℓ : Sobolev₂ (lieSet ε) σ ℓ) {X : Mx n}
    (hX : X ∈ lieSet ε) (m : ℕ) : ∀ u : H, IsKFin ε σ u →
    iteratedDeriv m (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
      fun t => ℓ (σ (NormedSpace.exp (t • X)) ((dRep σ X)^[m] u)) := by
  induction m with
  | zero => intro u _; simp
  | succ m ih =>
    intro u hu
    have hd : deriv (fun t : ℝ => ℓ (σ (NormedSpace.exp (t • X)) u)) =
        fun t => ℓ (σ (NormedSpace.exp (t • X)) (dRep σ X u)) :=
      funext fun t => (hasDerivAt_coef1 h hℓ (h.2.2.1 u hu) hX t).deriv
    rw [iteratedDeriv_succ', hd, ih _ (isKFin_dRep n ε H σ h u hu X hX)]
    funext t
    rw [Function.iterate_succ_apply]

theorem coef_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {X : Mx n}
    (hX : X ∈ lieSet ε) (t : ℝ) : ℓ (σ (NormedSpace.exp (t • X)) v) = 0 := by
  refine eq_zero_of_iteratedDeriv_eq_zero _ (analyticOnNhd_coef hHC h hℓ hv hX) (fun m => ?_) t
  rw [iteratedDeriv_coef h hℓ hX m v hv]
  simp only [zero_smul, NormedSpace.exp_zero, sigma_one h.1]
  exact h0 _ (isKFin_iterate h hX m hv)

theorem orbit_eq_zero (hHC : GlobalTheory.Published.HarishChandraModules) (h : Std ε σ) {ℓ : H →ₗ[ℂ] ℂ}
    (hℓ : Sobolev₂ (lieSet ε) σ ℓ) (h0 : ∀ u, IsKFin ε σ u → ℓ u = 0) {v : H} (hv : IsKFin ε σ v) {g : Mx n}
    (hg : g ∈ UJset ε) : ℓ (σ g v) = 0 := by
  have hk := mul_exp_neg_polarLog_mem_compact (ε := ε) hg
  have hL' : polarLog g ∈ lieSet ε := (polarLog_mem_hermitian_part (ε := ε) hg).1
  have e : g = (g * NormedSpace.exp (-polarLog g)) * NormedSpace.exp ((1 : ℝ) • polarLog g) := by
    rw [one_smul]; exact polar_decomposition_eq
  rw [e, sigma_mul h.1 (K_le_UJ hk) (exp_mem_UJ hL' 1)]
  exact coef_eq_zero (ℓ := ℓ ∘ₗ (σ (g * NormedSpace.exp (-polarLog g)) : H →ₗ[ℂ] H)) hHC h
    (sobCont_translate h.1 hℓ (K_le_UJ hk)) (fun u hu => h0 _ (isKFin_translate hu hk)) hv hL' 1

end Coef

theorem eq_zero_of_kFin : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (ℓ : M.H τ →ₗ[ℂ] ℂ), Sobolev₂ (lieAt V τ) (M.rep τ) ℓ → (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, ℓ w = 0) → ∀ w ∈ M.sm τ, ℓ w = 0 := by
  intro hHC D V S M τ ℓ hℓ h0 w hw
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have h := std_of_isDS hHC (M.ds τ)
  have hℓ' : Sobolev₂ (lieSet (M.ε τ)) (M.σ τ) ℓ :=
    GlobalTheory.SmoothCyclic.sobCont_transport (M.fr_unit τ) (M.fr_gram τ) hℓ
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin_ne_bot M τ)
  have hw' : Sm (M.ε τ) (M.σ τ) w := (GlobalTheory.SmoothCyclic.sm_eq M τ).le hw
  exact h.eq_zero_of_orbit hℓ' (h.2.2.1 a ha) ha0
    (fun g hg => orbit_eq_zero hHC h hℓ' (fun u hu => h0 u hu) ha hg) hw'

end GlobalTheory.KFiniteDense
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgree
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypeHypForms


open GlobalTheory.SmGL in
theorem unipBlock_subset_radicalTwo {k : Type} [Field k] {a b r : ℕ} (h : a + b = r) :
    GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.unipBlock k r a ⊆ (GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo k h : Set (GL (Fin r) k)) := by
  intro g hg
  rw [SetLike.mem_coe, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.radicalTwo, mem_unipRad]
  refine ⟨(mem_parab_two k).2 fun j i => ?_, ?_⟩
  · have hj := j.isLt
    have hi := i.isLt
    rw [hg (stdSum h (.inr j)) (stdSum h (.inl i)) (by simp only [stdSum_inl, stdSum_inr]; omega),
      Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp only [stdSum_inl, stdSum_inr] at this
    omega
  · rintro (_ | _) i j
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inl i)) (stdSum h (.inl j)) = (1 : Matrix (Fin a) (Fin a) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inl.injEq]
    · have hj := j.isLt
      have hi := i.isLt
      show (g : Matrix (Fin r) (Fin r) k) (stdSum h (.inr i)) (stdSum h (.inr j)) = (1 : Matrix (Fin b) (Fin b) k) i j
      rw [hg _ _ (by simp only [stdSum_inl, stdSum_inr]; omega)]
      simp only [Matrix.one_apply, (stdSum h).injective.eq_iff, Sum.inr.injEq]

theorem noRadicalFixed_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (hT : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T := by
  intro a b h ha hb
  obtain ⟨v, hv⟩ := hT.2 a ha (by omega)
  refine ⟨v, (Submodule.eq_bot_iff _).2 fun y hy => hv y fun g hg => ?_⟩
  have := hy ⟨g, unipBlock_subset_radicalTwo h hg⟩
  simpa using this

theorem hypH_of_noFixed {D : D7} {V : HSp D} (T : TypeDataG V) (h : NoFixed T) :
    GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ := by
  intro a ha har
  obtain ⟨v, hv⟩ := h.2 a ha har
  refine ⟨v, fun y hy => hv y fun g hg => hy g ?_⟩
  intro i j hij
  by_contra hc
  exact hij (hg i j hc)

theorem hypH_and_noRadicalFixed : ∀ (D : D7) (V : HSp D) (T : TypeDataG V), NoFixed T → GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors.HypH (k := fun v : T.S => ResF v.1) T.τ ∧ GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed.NoRadicalFixed T :=
  fun _ _ T h => ⟨hypH_of_noFixed T h, noRadicalFixed_of_noFixed T h⟩

end GlobalTheory.TypeHypForms

end
end

