module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEmbeddingMemUnitGroup
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodTupleConditionOfIdempotentZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0098
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0096
public import Development.AutomorphicArithmetic.WeightCongruences.IsRootOfIntegral
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveAlgebraMapIntegralClosureOfBirational
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0259

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHilbertChainOfLevelOverTops
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.ChainHilb

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem hp_add_right (h : PeterssonHilbertSpace.IsHermPos C ip) (x y y' : C) : ip x ((y : N) + y') = ip x y + ip x y' := by
  rw [← Submodule.coe_add, ← h.herm (y + y') x, Submodule.coe_add, h.add y y' x, map_add (f := _), h.herm y x, h.herm y' x]

theorem hp_smul_right (h : PeterssonHilbertSpace.IsHermPos C ip) (s : ℂ) (x y : C) : ip x (s • (y : N)) = s * ip x y := by
  rw [← Submodule.coe_smul, ← h.herm (s • y) x, Submodule.coe_smul, h.smul s y x, map_mul, h.herm y x,
    Complex.conj_conj]

theorem hp_restrict (h : PeterssonHilbertSpace.IsHermPos C ip) {C' : Submodule ℂ N} (hle : C' ≤ C) : PeterssonHilbertSpace.IsHermPos C' ip := by
  haveI := h.fd
  refine ⟨Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle), ?_, ?_, ?_, ?_⟩
  · intro x x' y; exact h.add ⟨x, hle x.2⟩ ⟨x', hle x'.2⟩ ⟨y, hle y.2⟩
  · intro s x y; exact h.smul s ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x y; exact h.herm ⟨x, hle x.2⟩ ⟨y, hle y.2⟩
  · intro x hx
    refine h.pos ⟨x, hle x.2⟩ ?_
    intro h0; apply hx; ext; simpa using congrArg Subtype.val h0

theorem hp_model (h : PeterssonHilbertSpace.IsHermPos C ip) : ∃ H : Hs, ∃ j : H.T →ₗ[ℂ] N,
    Function.Injective j ∧ LinearMap.range j = C ∧ ∀ x x', ⟪x, x'⟫_ℂ = ip (j x) (j x') := by
  have h1 : ∀ x ∈ C, ∀ y ∈ C, ∀ z ∈ C, ∀ c : ℂ, ip x (y + c • z) = ip x y + c * ip x z ∧ ip y x = star (ip x y) := by
    intro x hx y hy z hz c
    refine ⟨?_, ?_⟩
    · have e1 := hp_add_right h ⟨x, hx⟩ ⟨y, hy⟩ ⟨c • z, C.smul_mem c hz⟩
      have e2 := hp_smul_right h c ⟨x, hx⟩ ⟨z, hz⟩
      exact e1.trans (congrArg (fun t => ip x y + t) e2)
    · exact (h.herm ⟨x, hx⟩ ⟨y, hy⟩).symm
  have h2 : ∀ x ∈ C, x ≠ 0 → 0 < (ip x x).re := fun x hx hne =>
    h.pos ⟨x, hx⟩ (fun h0 => hne (by simpa using congrArg Subtype.val h0))
  obtain ⟨M, hM⟩ := GlobalTheory.HilbertModel.exists_hmod N C ip h.fd h1 h2
  exact ⟨⟨M.H⟩, M.e, hM.1, hM.2.1, hM.2.2⟩

theorem hp_riesz {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (h : PeterssonHilbertSpace.IsHermPos C ip) (j : H →ₗ[ℂ] N) (hj : ∀ x, j x ∈ C) :
    ∃ r : C →ₗ[ℂ] H, ∀ x (w : C), ⟪x, r w⟫_ℂ = ip (j x) w := by
  have key : ∀ w : C, ∃ y : H, ∀ x, ⟪x, y⟫_ℂ = ip (j x) w := by
    intro w
    let φ : H →ₗ[ℂ] ℂ :=
      { toFun := fun x => ip w (j x)
        map_add' := fun a b => by
          have := hp_add_right h w ⟨j a, hj a⟩ ⟨j b, hj b⟩
          simpa [map_add (f := _)] using this
        map_smul' := fun s a => by
          have := hp_smul_right h s w ⟨j a, hj a⟩
          simpa [map_smul] using this }
    refine ⟨(InnerProductSpace.toDual ℂ H).symm (LinearMap.toContinuousLinearMap φ), fun x => ?_⟩
    rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
    exact h.herm w ⟨j x, hj x⟩
  choose y hy using key
  refine ⟨⟨⟨y, fun a b => ext_inner_left ℂ fun x => ?_⟩, fun s a => ext_inner_left ℂ fun x => ?_⟩, fun x w => hy w x⟩
  · rw [inner_add_right, hy, hy, hy, Submodule.coe_add]
    exact hp_add_right h ⟨j x, hj x⟩ a b
  · rw [RingHom.id_apply, inner_smul_right, hy, hy, Submodule.coe_smul]
    exact hp_smul_right h s ⟨j x, hj x⟩ a

end Gen

def heqv {A B : Hs} (h : A = B) : A.T ≃ₗᵢ[ℂ] B.T := by
  subst h; exact LinearIsometryEquiv.refl ℂ A.T

theorem heqv_heq {A B E : Hs} (e1 : A = E) (e2 : B = E) (v' : A.T) (v : B.T) (h : HEq v' v) :
    heqv e1 v' = heqv e2 v := by
  subst e1; subst e2; cases h; rfl

theorem heqv_self {A : Hs} (h : A = A) (x : A.T) : heqv h x = x := rfl

def chSel (m : ℕ) (A B : Hs) (L : ℕ → Hs) (j : ℕ) : Hs := if j = 0 then A else if j = m then B else L j

theorem chSel_zero {m : ℕ} {A B : Hs} {L : ℕ → Hs} : chSel m A B L 0 = A := if_pos rfl

theorem chSel_top {m : ℕ} {A B : Hs} {L : ℕ → Hs} (hm : m ≠ 0) : chSel m A B L m = B := by
  rw [chSel, if_neg hm, if_pos rfl]

theorem chSel_mid {m j : ℕ} {A B : Hs} {L : ℕ → Hs} (h1 : j ≠ 0) (h2 : j ≠ m) : chSel m A B L j = L j := by
  rw [chSel, if_neg h1, if_neg h2]

end GlobalTheory.ChainHilb

namespace GlobalTheory.ChainHilb

theorem exists_chainHilb : ∀ (D : D7) (C : ChainReal D) (b : Bool) (U : D.what₂.Tup → Prop) (Top : D.what₂.Tup → Hs) (jX : ∀ μ, (Top μ).T →ₗ[ℂ] C.AmbX), 2 ≤ D.R.m → PeterssonHilbertSpace.IsHermPos (C.EEc b) (C.ipE b) → (∀ μ, C.EEc b ≤ C.CC b μ 0 ∧ C.CCXP b μ ≤ C.CCX b μ ∧ PeterssonHilbertSpace.IsHermPos (C.CCX b μ) (C.ipXP b μ) ∧ ∀ j, j ≤ D.R.m - 1 → C.CCP b μ j ≤ C.CC b μ j ∧ PeterssonHilbertSpace.IsHermPos (C.CC b μ j) (C.ipP b μ j)) → (∀ μ, PeterssonHilbertSpace.IsHermPos (C.CC b μ 0) (C.ipE b)) → (∀ μ, U μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = C.CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipXP b μ (jX μ x) (jX μ x')) → ∃ (EE : Hs) (Mult : D.what₂.Tup → ℕ → Hs) (multZero : ∀ μ, (Mult μ 0).T ≃ₗᵢ[ℂ] EE.T) (multTop : ∀ μ, (Mult μ D.R.m).T ≃ₗᵢ[ℂ] (Top μ).T) (io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T) (jE : EE.T →ₗ[ℂ] C.Amb 0) (jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j), Function.Injective jE ∧ LinearMap.range jE = C.EEc b ∧ (∀ x x', ⟪x, x'⟫_ℂ = C.ipE b (jE x) (jE x')) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j ≤ D.R.m - 1 → Function.Injective (jM μ j) ∧ LinearMap.range (jM μ j) = C.CCP b μ j ∧ ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jM μ j x) (jM μ j x')) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ 1).T) (h : jM μ 1 v ∈ C.CC b μ 1), ⟪x, multZero μ (io μ 0 v)⟫_ℂ = C.ipE b (jE x) (C.ioC b μ 0 ⟨jM μ 1 v, h⟩ : C.Amb 0)) ∧ (∀ μ, U μ → ∀ j, 1 ≤ j → j + 1 ≤ D.R.m - 1 → ∀ x (v : (Mult μ (j + 1)).T) (h : jM μ (j + 1) v ∈ C.CC b μ (j + 1)), ⟪x, io μ j v⟫_ℂ = C.ipP b μ j (jM μ j x) (C.ioC b μ j ⟨jM μ (j + 1) v, h⟩ : C.Amb j)) ∧ (∀ μ, U μ → ∀ x (v : (Mult μ D.R.m).T) (v' : (Mult μ (D.R.m - 1 + 1)).T), HEq v' v → ∀ h : jX μ (multTop μ v) ∈ C.CCX b μ, ⟪x, io μ (D.R.m - 1) v'⟫_ℂ = C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x) (C.ioX b μ ⟨jX μ (multTop μ v), h⟩ : C.Amb (D.R.m - 1))) ∧ (∀ μ, ¬ U μ → ∀ j, io μ j = 0) := by
  classical
  intro D C b U Top jX hm hE hle hE0 hX
  obtain ⟨EE, jE, hEi, hEr, hEip⟩ := hp_model hE
  have jE_mem : ∀ μ x, jE x ∈ C.CC b μ 0 := fun μ x =>
    (hle μ).1 (by rw [← hEr]; exact LinearMap.mem_range_self jE x)
  have hLo : ∀ (μ : D.what₂.Tup) (j : ℕ), ∃ H : Hs, ∃ jj : H.T →ₗ[ℂ] C.Amb j, j ≤ D.R.m - 1 →
      Function.Injective jj ∧ LinearMap.range jj = C.CCP b μ j ∧
        ∀ x x', ⟪x, x'⟫_ℂ = C.ipP b μ j (jj x) (jj x') := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨h1, h2⟩ := (hle μ).2.2.2 j hj
      obtain ⟨H, jj, a1, a2, a3⟩ := hp_model (hp_restrict h2 h1)
      exact ⟨H, jj, fun _ => ⟨a1, a2, a3⟩⟩
    · exact ⟨EE, 0, fun h => absurd h hj⟩
  choose Lo jL hL using hLo
  let Mult : D.what₂.Tup → ℕ → Hs := fun μ => chSel D.R.m EE (Top μ) (Lo μ)
  let jM : ∀ μ j, (Mult μ j).T →ₗ[ℂ] C.Amb j := fun μ j =>
    if h : 1 ≤ j ∧ j ≤ D.R.m - 1 then
      (jL μ j).comp (heqv (chSel_mid (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)
        (by have := h.1; omega) (by have := h.2; omega))).toLinearEquiv.toLinearMap
    else 0
  have jM_mem : ∀ μ j x, jM μ j x ∈ C.CC b μ j := by
    intro μ j x
    dsimp only [jM]
    split_ifs with h
    · rw [LinearMap.comp_apply]
      refine ((hle μ).2.2.2 j h.2).1 ?_
      rw [← (hL μ j h.2).2.1]
      exact LinearMap.mem_range_self _ _
    · rw [LinearMap.zero_apply]; exact zero_mem _
  have hr0 : ∀ μ, ∃ r : C.CC b μ 0 →ₗ[ℂ] EE.T, ∀ x (w : C.CC b μ 0), ⟪x, r w⟫_ℂ = C.ipE b (jE x) w :=
    fun μ => hp_riesz (hE0 μ) jE (jE_mem μ)
  choose r0 hr0 using hr0
  have hR : ∀ μ j, ∃ r : C.CC b μ j →ₗ[ℂ] (Mult μ j).T, j ≤ D.R.m - 1 →
      ∀ x (w : C.CC b μ j), ⟪x, r w⟫_ℂ = C.ipP b μ j (jM μ j x) w := by
    intro μ j
    by_cases hj : j ≤ D.R.m - 1
    · obtain ⟨r, hr⟩ := hp_riesz ((hle μ).2.2.2 j hj).2 (jM μ j) (jM_mem μ j)
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose R hR using hR
  have memX : ∀ μ, U μ → ∀ y, jX μ y ∈ C.CCX b μ := fun μ hU y =>
    (hle μ).2.1 (by rw [← (hX μ hU).2.1]; exact LinearMap.mem_range_self (jX μ) y)
  let io : ∀ μ j, (Mult μ (j + 1)).T →ₗ[ℂ] (Mult μ j).T := fun μ j =>
    if hU : U μ then
      if h0 : j = 0 then
        (heqv (show Mult μ j = EE by rw [h0]; exact chSel_zero)).symm.toLinearEquiv.toLinearMap ∘ₗ r0 μ ∘ₗ
          C.ioC b μ 0 ∘ₗ (jM μ 1 ∘ₗ (heqv (show Mult μ (j + 1) = Mult μ 1 by rw [h0])).toLinearEquiv.toLinearMap).codRestrict
            (C.CC b μ 1) (fun y => jM_mem μ 1 _)
      else if hT : j + 1 = D.R.m then
        (heqv (show Mult μ (D.R.m - 1) = Mult μ j by rw [show D.R.m - 1 = j by omega])).toLinearEquiv.toLinearMap ∘ₗ
          R μ (D.R.m - 1) ∘ₗ C.ioX b μ ∘ₗ
          (jX μ ∘ₗ (heqv (show Mult μ (j + 1) = Top μ by rw [hT]; exact chSel_top (by omega))).toLinearEquiv.toLinearMap).codRestrict
            (C.CCX b μ) (fun y => memX μ hU _)
      else
        R μ j ∘ₗ C.ioC b μ j ∘ₗ (jM μ (j + 1)).codRestrict (C.CC b μ (j + 1)) (jM_mem μ (j + 1))
    else 0
  refine ⟨EE, Mult, fun μ => heqv (chSel_zero (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ)),
    fun μ => heqv (chSel_top (m := D.R.m) (A := EE) (B := Top μ) (L := Lo μ) (by omega)), io, jE, jM,
    hEi, hEr, hEip, ?_, ?_, ?_, ?_, ?_⟩
  · intro μ _ j h1 h2
    have hh : 1 ≤ j ∧ j ≤ D.R.m - 1 := ⟨h1, h2⟩
    obtain ⟨hi, hr, hip⟩ := hL μ j h2
    dsimp only [jM]
    rw [dite_eq_left hh]
    refine ⟨?_, ?_, ?_⟩
    · rw [LinearMap.coe_comp]; exact hi.comp (LinearEquiv.injective _)
    · rw [LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), hr]
    · intro x x'
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hip]
      exact (LinearIsometryEquiv.inner_map_map _ x x').symm
  · intro μ hU x v h
    dsimp only [io]
    rw [dite_eq_left hU, dite_eq_left rfl]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.apply_symm_apply]
    exact hr0 μ x _
  · intro μ hU j h1 h2 x v h
    dsimp only [io]
    rw [dite_eq_left hU, dite_eq_right (by omega), dite_eq_right (by omega)]
    rw [LinearMap.comp_apply, hR μ j (by omega)]
    rfl
  · intro μ hU x v v' hv h
    dsimp only [io]
    rw [dite_eq_left hU, dite_eq_right (by omega), dite_eq_left (by omega)]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    rw [heqv_self, hR μ _ le_rfl]
    refine congrArg (fun y => C.ipP b μ (D.R.m - 1) (jM μ (D.R.m - 1) x)
      ((C.ioX b μ y : C.CC b μ (D.R.m - 1)) : C.Amb (D.R.m - 1))) (Subtype.ext ?_)
    exact congrArg (jX μ) (heqv_heq _ _ v' v hv)
  · intro μ hU j
    dsimp only [io]
    rw [dite_eq_right hU]

end GlobalTheory.ChainHilb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
section
noncomputable section

namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace StagesInhab

def HasLetters (P : Pre) : Prop :=
  ∃ (Del : ℚ) (letter : P.Word → Fin (P.R.k - 2) → Bool), 0 < Del ∧ Function.Injective letter ∧
    (∀ w τ (l : ℕ) (h : l + 1 < P.R.k - 1), (P.hcW w τ).v ⟨l, by omega⟩ - (P.hcW w τ).v ⟨l + 1, h⟩ = 4 * Del) ∧
    ∀ w τ (l : ℕ) (h : l < P.R.k - 2), (P.hcW w τ).u ⟨l + 1, by omega⟩ =
      (P.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then Del else 0)

theorem ipC_conj (B : Base) (u : B.Word)
    (φ ψ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) :
    ((ColsModel.cols B).fm u).ipC 0 ψ φ = starRingEnd ℂ (((ColsModel.cols B).fm u).ipC 0 φ ψ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [RowsModel.ipC_cols, RowsModel.ipC_cols, map_sum]
  exact Finset.sum_congr rfl fun c _ => by simp [mul_comm]

theorem ipC_pos (B : Base) (u : B.Word)
    (φ : ((ColsModel.cols B).mem u).C.cls 0 → ((ColsModel.cols B).mem u).C.Y 0 → ℂ) (hφ : φ ≠ 0) :
    0 < (((ColsModel.cols B).fm u).ipC 0 φ φ).re := by
  rw [RowsModel.ipC_cols, Complex.re_sum]
  obtain ⟨c, hc⟩ : ∃ c, φ c () ≠ 0 := by
    by_contra h
    exact hφ (funext fun c => funext fun _ => not_not.mp fun hc => h ⟨c, hc⟩)
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity

theorem exists_rows (B : Base) (D : ℕ) :
    ∃ W : RowsRest B (ColsModel.cols B), W.Drows = D ∧ W.Dall = D ∧ ∀ u, Nontrivial (W.Mu u) := by
  classical
  have hf : ∀ u, ∃ e : RowsModel.Euc ((ColsModel.cols B).mem u).A.du ≃ₗ[ℂ] ((ColsModel.cols B).mem u).A.Mram,
      ∀ φ ψ, inner ℂ φ ψ = ((ColsModel.cols B).fm u).ipC 0 (e φ).1 (e ψ).1 := fun u =>
    haveI := RowsModel.mram_fd (ColsModel.cols B) u
    RowsModel.exists_frame (RowsModel.ramCore (ColsModel.cols B) u (fun φ _ ψ _ => ipC_conj B u φ ψ)
      (fun φ _ h => ipC_pos B u φ h))
  choose eM heM using hf
  let e : ℂ ≃ₗ[ℂ] RowsModel.Euc 1 :=
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm.trans (WithLp.linearEquiv 2 ℂ _).symm
  refine ⟨RowsModel.model (ColsModel.cols B) (fun _ => 1) D (fun _ => e) (fun _ _ => e) eM heM, rfl, rfl,
    fun u => ?_⟩
  have : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  have hne : ((ColsModel.cols B).mem u).A.Mram ≠ ⊥ :=
    MemberTorsor.mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (ColsModel.two_lt_alt B.toPre u)
  have := Submodule.nontrivial_iff_ne_bot.mpr hne
  exact (eM u).toEquiv.nontrivial

theorem exists_stages_over (B : Base) (hB : HasLetters B.toPre) (D : ℕ) :
    ∃ X : Stages, X.B = B ∧ X.W.Drows = D ∧ X.W.Dall = D ∧ (∀ u, Nontrivial (X.W.Mu u)) ∧
      (∀ u i, Nonempty ((X.C.mem u).C.cls i)) ∧ Nonempty X.G.jet.Sit := by
  obtain ⟨Del, letter, hD, hinj, gap, hu⟩ := hB
  obtain ⟨W, h1, h2, h3⟩ := exists_rows B D
  have hc : ∀ u i, Nonempty (((ColsModel.cols B).mem u).C.cls i) :=
    fun u _ => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩
  obtain ⟨L⟩ := locStage_inhabited
  obtain ⟨N, -⟩ := GaloisStage.exists_nStage_adapt B _ W L
  obtain ⟨V, -⟩ := DivInhab.exists_divStage B _ (GaloisStage.adapt W)
  obtain ⟨S⟩ := SStageInhab.nonempty_sStage B _ (GaloisStage.adapt W) Del hD gap letter hinj hu
    (fun u x _ y _ => (ipC_conj B u y x).symm) (fun u x _ h => ipC_pos B u x h)
    (show W.Drows ≤ W.Dall by omega)
  obtain ⟨G, -, hG⟩ := (GJInhab.inhabited_stage B (ColsModel.cols B)).2.2 (hc _ _) (hc _ _)
  exact ⟨⟨B, _, GaloisStage.adapt W, V, S, N, G⟩, rfl, h1, h2, h3, hc, hG⟩

end StagesInhab

end GlobalTheory.Mem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelFormOfFaceLevelMultiplicity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.MultLevelP

theorem multT_mono {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    MultT θ M J χ ≤ MultT θ M J' χ' := by
  unfold MultT Mult
  exact Submodule.map_mono (Submodule.span_mono fun T hT =>
    ⟨hT.aut, hT.cusp, fun v k hk g => by rw [hχ k hk]; exact hT.lev v k (hJ hk) g, hT.equiv, hT.cont⟩)

variable {D : D7} {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}

theorem levS_flag1_sub (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) : levS V β (flag1L L) ⊆ levS V β L := by
  rintro κ ⟨hκ, hp, hr⟩
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  refine ⟨hκ, hp, ?_⟩
  show Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H
  rw [e]
  exact L.P.H.one_mem

theorem levChi_flag1 (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {κ : GA D V} (hκ : κ ∈ levS V β (flag1L L)) :
    levChi V β (flag1L L) κ = levChi V β L κ := by
  obtain ⟨-, -, hr⟩ := hκ
  have e : Formalism.L2.DIV.rTup β L (finE V κ) = 1 := Subgroup.mem_bot.1 hr
  have h1 : Formalism.L2.DIV.rTup β L (finE V κ) ∈ L.P.H := e ▸ L.P.H.one_mem
  have h := levFn_withP (β := β) (L := L) L.P (finE V κ)
  change Formalism.L2.DIV.levFn β L (finE V κ) = _ at h
  have e1 : (⟨_, h1⟩ : L.P.H) = 1 := Subtype.ext e
  unfold levChi
  rw [levFn_flag1, h, Formalism.L2.DIV.extendOne_of_mem _ h1, e1, map_one, one_mul]

end GlobalTheory.MultLevelP


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.MultLevelP.exists_form_of_mult : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → ∀ (b : Bool) (t : T) (Tm : SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)), Tm ∈ Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) → ∃ Fn ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ, (∀ (q : (levEnv D.sp.X' R.βX (R.datXt t)).Q) (hq : (R.B.R t).act_tie.red q ∈ (F.lvl b).P) (h : Bridge.Gf D.sp.X'), Fn (h * q) = (((levEnv D.sp.X' R.βX (R.datXt t)).ch q : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hq⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Fn h) ∧ R.cX.toMap R.prX Fn = Tm := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB b t Tm hTm
  have hθ := hB.models.inf
  have hc := hB.models.cX
  have hpr := hB.models.prX
  have hp := GlobalTheory.DefiniteMult.allPlus_parB (V := D.sp.X') _ (Nat.sub_le _ _) R.MX
  have hT0 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (datXP R t (R.levR F b))))
      (levChi _ R.βX (flag1L (datXP R t (R.levR F b)))) :=
    GlobalTheory.MultLevelP.multT_mono R.θ R.MX (GlobalTheory.MultLevelP.levS_flag1_sub (β := R.βX) (datXP R t (R.levR F b)))
      (fun k hk => GlobalTheory.MultLevelP.levChi_flag1 (datXP R t (R.levR F b)) hk) hTm
  have e : flag1L (datXP R t (R.levR F b)) = flag1L (R.datXt t) := rfl
  have hT1 : Tm ∈ MultT R.θ R.MX (levS _ R.βX (flag1L (R.datXt t))) (levChi _ R.βX (flag1L (R.datXt t))) := by
    rw [← e]; exact hT0
  have X := GlobalTheory.DefiniteMult.exists_form (D := D) (V := D.sp.X') (M := R.MX) (θ := R.θ) (c := R.cX) (pr := R.prX) (β := R.βX) (L := R.datXt t) hθ hp hc hpr hT1
  obtain ⟨Fn, hFn, hmap⟩ := X
  refine ⟨Fn, hFn, ?_, hmap⟩
  rintro ⟨q, hqQ⟩ hq h
  obtain ⟨κ, hκκ⟩ := GlobalTheory.DefiniteMult.exists_fin_lift (D := D) D.sp.X' q
  have hκ := hκκ.1
  have hκq := hκκ.2
  obtain ⟨g, hg⟩ := (finHom D.sp.X').rangeRestrict_surjective h
  subst hg
  have hqQ' : (finHom D.sp.X').rangeRestrict κ ∈ (levEnv D.sp.X' R.βX (R.datXt t)).Q := by rw [hκq]; exact hqQ
  have eQ : (⟨_, hqQ'⟩ : (levEnv D.sp.X' R.βX (R.datXt t)).Q) = ⟨q, hqQ⟩ := Subtype.ext hκq
  have hq' : (R.B.R t).act_tie.red ⟨_, hqQ'⟩ ∈ (F.lvl b).P :=
    (congrArg (fun x => (R.B.R t).act_tie.red x ∈ (F.lvl b).P) eQ).mpr hq
  have key : ∀ (x y : (levEnv D.sp.X' R.βX (R.datXt t)).Q), x = y → ∀ (hx : (R.B.R t).act_tie.red x ∈ (F.lvl b).P)
      (hy : (R.B.R t).act_tie.red y ∈ (F.lvl b).P),
      ((levEnv D.sp.X' R.βX (R.datXt t)).ch x : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hx⟩ : D.what₂.LLˣ) : D.what₂.LL) =
        ((levEnv D.sp.X' R.βX (R.datXt t)).ch y : ℂ) * D.what₂.embLL (((F.lvl b).ψ ⟨_, hy⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    rintro x _ rfl hx hy
    rfl
  have hbr := _root_.GlobalTheory.TopBridge.mem_levelSubgroup_localDatum_iff D G Pl0 T A Ks R F hB.grp.red_R b t κ hκ
  have hκS : κ ∈ levS _ R.βX (datXP R t (R.levR F b)) := hbr.1.2 ⟨hqQ', hq'⟩
  have hχ := hbr.2 hqQ' hq'
  have hM := (mem_multT _ _ _ _ _).1 hTm
  have hlev : ∀ x g', Tm x (g' * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ * Tm x g' := by
    intro x g'
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      have := (GlobalTheory.mult_value_left_cont_level R.θ R.MX _ _ _ hM v).2.2 κ hκS g'
      rw [map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
      exact congrArg (r * ·) this
    | add x y hx hy => rw [map_add (f := _), Pi.add_apply, Pi.add_apply, hx, hy, mul_add]
  have hb := (GlobalTheory.DefiniteMult.pair_bijective hθ hp hc hpr).1
  have hext : R.cX.ext Fn (g * κ) = levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ext Fn g := by
    refine hb (LinearMap.ext fun x => ?_)
    have a1 : R.prX (R.cX.ext Fn (g * κ)) x = Tm x (g * κ) := congrFun (LinearMap.congr_fun hmap x) (g * κ)
    have a2 : R.prX (R.cX.ext Fn g) x = Tm x g := congrFun (LinearMap.congr_fun hmap x) g
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul, a1, a2, hlev]
  change R.cX.ρ (g * κ)⁻¹ (Fn ((finHom D.sp.X').rangeRestrict (g * κ))) =
    levChi _ R.βX (datXP R t (R.levR F b)) κ • R.cX.ρ g⁻¹ (Fn ((finHom D.sp.X').rangeRestrict g)) at hext
  rw [GlobalTheory.DefiniteMult.rho_right_inv R.cX.ρ g (hc.1 _ (inv_mem hκ)), map_mul] at hext
  have inj : Function.Injective (R.cX.ρ g⁻¹) := fun a a' haa => by
    have := congrArg (R.cX.ρ g) haa
    rwa [GlobalTheory.DefiniteEnd.rho_inv_cancel, GlobalTheory.DefiniteEnd.rho_inv_cancel] at this
  calc Fn ((finHom D.sp.X').rangeRestrict g * q) = Fn ((finHom D.sp.X').rangeRestrict g * (finHom D.sp.X').rangeRestrict κ) :=
      congrArg (fun x => Fn ((finHom D.sp.X').rangeRestrict g * x)) hκq.symm
    _ = levChi _ R.βX (datXP R t (R.levR F b)) κ • Fn ((finHom D.sp.X').rangeRestrict g) :=
      inj (hext.trans ((R.cX.ρ g⁻¹).map_smul _ _).symm)
    _ = _ := congrArg (fun c : ℂ => c • Fn ((finHom D.sp.X').rangeRestrict g)) (hχ.trans (key _ _ eQ hq' hq))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsZeroOfInvOfNotRegularNormal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.NormalPole

theorem exists_height_one {R K : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] (f : K) (Q : Ideal R)
    (hQ : ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ Q) [Q.IsPrime] :
    ∃ p : Ideal R, p.IsPrime ∧ p ≤ Q ∧ p.height = 1 ∧
      ∀ s c : R, algebraMap R K s * f = algebraMap R K c → s ∈ p := by
  obtain ⟨b, c, hc, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcK : algebraMap R K c ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hc0
  let d : Ideal R := (Ideal.span {c}).colon {b}
  have hd : ∀ s, s ∈ d ↔ c ∣ s * b := fun s => by
    simp only [d, Submodule.mem_colon_singleton, smul_eq_mul, Ideal.mem_span_singleton]
  have reg : ∀ s, (∃ e : R, algebraMap R K s * (algebraMap R K b / algebraMap R K c) =
      algebraMap R K e) ↔ s ∈ d := fun s => by
    rw [hd]
    refine exists_congr fun e => ?_
    rw [← mul_div_assoc, div_eq_iff hcK, ← map_mul, ← map_mul, (IsFractionRing.injective R _).eq_iff,
      mul_comm e]
  have hdQ : d ≤ Q := fun s hs => by
    obtain ⟨e, he⟩ := (reg s).2 hs
    exact hQ s e he
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le hdQ
  have hpa : p ∈ associatedPrimes R (R ⧸ d) := by
    apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
    rw [Ideal.annihilator_quotient]
    exact hp
  obtain ⟨hpp, x, hx⟩ := isAssociatedPrime_iff.mp hpa
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : p.height = 1 := height_eq_one_of_forall_mem_iff_dvd (b := x * b) hc0 fun r => by
    rw [hx, Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, hd, _root_.mul_assoc]
  exact ⟨p, hpp, hpQ, h1, fun s e he => hp.1.2 ((reg s).1 ⟨e, he⟩)⟩

theorem mem_range_iff {R B K : Type} [CommRing R] [CommRing B] [Field K] [Algebra R B] [Algebra R K]
    [Algebra B K] [IsScalarTower R B K] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime B p] (f : K) :
    (∃ a : B, algebraMap B K a = f) ↔
      ∃ s c : R, algebraMap R K s * f = algebraMap R K c ∧ s ∉ p := by
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj p.primeCompl a
    refine ⟨s, c, ?_, s.2⟩
    rw [IsScalarTower.algebraMap_apply R B K, IsScalarTower.algebraMap_apply R B K c, ← map_mul,
      mul_comm, e]
  · rintro ⟨s, c, e, hs⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units B (⟨s, hs⟩ : p.primeCompl)
    refine ⟨↑u⁻¹ * algebraMap R B c, ?_⟩
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← e, IsScalarTower.algebraMap_apply R B K s]
    have hu' : algebraMap R B s = u := hu.symm
    rw [hu', ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]

end GlobalTheory.NormalPole
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelFormOrthogonalKilledByThetaMapStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftLevelForm_orthogonal_killed_by_thetaMap : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → ∀ (i : Fin D.R.m) (t : T) (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL), (∀ z, Formalism.DivisionValues.hform (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ z) x = 0) → R.thG i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) = 0 := by
  first | exact @GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | exact GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth | (intros; apply GlobalTheory.Mem.ThOrth.thG_eq_zero_of_orth <;> assumption)
end

