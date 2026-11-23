module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0249
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0231
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0241
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0267
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0260
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0243
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatioAlt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0238
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0239
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0266
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0202
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0258
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0106
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0191

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfHeadTop
section
namespace Formalism.FourierDecayAlt.P

theorem built_bounds_compact_of_head_top (hH : Formalism.FourierDecayAlt.KB.HeadTop) : Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt := fun hA =>
  built_bounds_compact_of_leaves radial_head hH degree_of_lift_pairing top_local_built_places degree_top
    top_ratio (germ_parts_compact_support kernel_continuity_built germ_rate_bound hA)
    (fun hA' => uniform_decay_of_place hA' radial_head hH
      (uniform_decay_of_heads radial_head hH)) hA

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSALoc
section
noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants

section loc

variable {r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem rds_pbOp_locO (l : Fin r) {f₁ f₂ : (Fin r → ℂ) → E} (h : ∀ c ∈ OmX r, f₁ c = f₂ c) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) : pbOp l f₁ c = pbOp l f₂ c := by
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hev : f₁ =ᶠ[nhds c] f₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) h
  unfold pbOp wirtBar
  rw [if_pos hc, if_pos hc, hev.fderiv_eq]

theorem rds_vABm_loc (Y : ℂ) : ∀ (i : ℕ) (f₁ f₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, f₁ c = f₂ c) →
    ∀ c ∈ OmX r, (CutMP.vABm r Y i).1 f₁ c = (CutMP.vABm r Y i).1 f₂ c ∧
      (CutMP.vABm r Y i).2 f₁ c = (CutMP.vABm r Y i).2 f₂ c
  | 0, f₁, f₂, h, c, hc => ⟨h c hc, rfl⟩
  | i + 1, f₁, f₂, h, c, hc => by
    have ih := rds_vABm_loc Y i f₁ f₂ h
    by_cases hi : i < r
    · simp only [CutMP.vABm, dif_pos hi]
      refine ⟨?_, ?_⟩
      · simp only [Pi.sub_apply, Pi.smul_apply, cbOp]
        rw [(ih c hc).1, (ih c hc).2, rds_pbOp_locO _ (fun c' hc' => (ih c' hc').1) hc]
      · simp only [cbiOp]
        rw [(ih c hc).1]
    · simp only [CutMP.vABm, dif_neg hi]
      exact ih c hc

end loc

theorem spectral_action_locality : RDSALoc := by
  intro r E _ _ y f f' h c hc
  have hopen : IsOpen (OmX r) := by
    have e : OmX r = ⋂ l, {x : Fin r → ℂ | x l ≠ 0} := by
      ext x
      simp [OmX]
    rw [e]
    exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hpO : ∀ (l : Fin r) (g₁ g₂ : (Fin r → ℂ) → E), (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      pOp l g₁ c = pOp l g₂ c := by
    intro l g₁ g₂ hg c hc
    have hev : g₁ =ᶠ[nhds c] g₂ := Filter.eventuallyEq_of_mem (hopen.mem_nhds hc) hg
    unfold pOp Formalism.QuantumDeterminants.wirt
    rw [if_pos hc, if_pos hc, hev.fderiv_eq]
  have hA : ∀ i : ℕ, ∀ g₁ g₂ : (Fin r → ℂ) → E, (∀ c ∈ OmX r, g₁ c = g₂ c) → ∀ c ∈ OmX r,
      (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c ∧ (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := by
    intro i
    induction i with
    | zero =>
      intro g₁ g₂ hg c hc
      simp only [Q.vAB]
      exact ⟨hg c hc, by trivial⟩
    | succ i ih =>
      intro g₁ g₂ hg c hc
      have ih1 : ∀ c ∈ OmX r, (Q.vAB r y i).1 g₁ c = (Q.vAB r y i).1 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).1
      have ih2 : ∀ c ∈ OmX r, (Q.vAB r y i).2 g₁ c = (Q.vAB r y i).2 g₂ c := fun c hc => (ih g₁ g₂ hg c hc).2
      simp only [Q.vAB]
      split_ifs with hi
      · refine ⟨?_, ?_⟩
        · simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
          rw [ih1 c hc, hpO ⟨i, hi⟩ _ _ ih1 c hc]
          simp only [cOp]
          rw [ih2 c hc]
        · simp only [ciOp]
          rw [ih1 c hc]
      · exact ih g₁ g₂ hg c hc
  exact ⟨(hA r f f' h c hc).1, (rds_vABm_loc y r f f' h c hc).1⟩

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSARad
section
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section pre

variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ} (L : R.LevelData A r)

def rdsVp (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.finRange r).take i).reverse.map fun l => L.Tl Y l).prod

def rdsVvp (Y : ℂ) (i : ℕ) : Matrix (Fin 2) (Fin 2) A :=
  (((List.finRange r).take i).reverse.map fun l => L.Tvl Y l).prod

theorem rdsVp_zero (Y : ℂ) : rdsVp L Y 0 = 1 := by simp [rdsVp]

theorem rdsVvp_zero (Y : ℂ) : rdsVvp L Y 0 = 1 := by simp [rdsVvp]

theorem rdsVp_succ (Y : ℂ) (i : ℕ) (h : i < r) : rdsVp L Y (i + 1) = L.Tl Y ⟨i, h⟩ * rdsVp L Y i := by
  simp [rdsVp, List.take_add_one, h]

theorem rdsVvp_succ (Y : ℂ) (i : ℕ) (h : i < r) : rdsVvp L Y (i + 1) = L.Tvl Y ⟨i, h⟩ * rdsVvp L Y i := by
  simp [rdsVvp, List.take_add_one, h]

theorem rds_tprod (Y : ℂ) : L.Tprod Y = rdsVp L Y r := by
  simp [R.LevelData.Tprod, rdsVp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem rds_tvprod (Y : ℂ) : L.Tvprod Y = rdsVvp L Y r := by
  simp [R.LevelData.Tvprod, rdsVvp, List.ofFn_eq_map, List.map_reverse, List.take_of_length_le]

theorem rds_Tl_mul_0 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tl Y l * V) 0 0 = (algebraMap ℂ A Y + L.p l) * V 0 0 + -L.c l * V 1 0 := by
  simp [R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]

theorem rds_Tl_mul_1 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tl Y l * V) 1 0 = L.ci l * V 0 0 := by
  simp [R.LevelData.Tl, Matrix.mul_apply, Fin.sum_univ_two]

theorem rds_Tvl_mul_0 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tvl Y l * V) 0 0 = (algebraMap ℂ A Y - L.pb l) * V 0 0 + -L.cb l * V 1 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

theorem rds_Tvl_mul_1 (Y : ℂ) (l : Fin r) (V : Matrix (Fin 2) (Fin 2) A) :
    (L.Tvl Y l * V) 1 0 = L.cbi l * V 0 0 := by
  simp [R.LevelData.Tvl, Matrix.mul_apply, Fin.sum_univ_two]

end pre

section rad

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem rdsR_fst_neg (a : Pr V) : (-a).1 = -a.1 := rfl
theorem rdsR_fst_sub (a b : Pr V) : (a - b).1 = a.1 - b.1 := rfl
theorem rdsR_fst_one : (1 : Pr V).1 = 1 := rfl
theorem rdsR_fst_zero : (0 : Pr V).1 = 0 := rfl

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
  {π' : Mx k r → (Wq →L[ℂ] Wq)} (X : ActualOps k r z z' π π') (L : R.LevelData (Pr (RadSp k r z z' π π')) r)

theorem rds_op_coe (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.op l i Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) = crd (opL l i) (Φ : Fn k r (Wq →L[ℂ] Wp)) :=
  X.op_apply l i Φ

theorem rds_vab_ind (hL : IsActualLevel X L) (Y : ℂ) : ∀ i : ℕ, i ≤ r → ∀ Φ : RadSp k r z z' π π',
    ((((rdsVp L Y i) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (Q.vAB r Y i) 0) (Φ : Fn k r (Wq →L[ℂ] Wp)) ∧
      ((((rdsVp L Y i) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (Q.vAB r Y i) 1) (Φ : Fn k r (Wq →L[ℂ] Wp)) := by
  intro i
  induction i with
  | zero =>
    intro _ Φ
    rw [rdsVp_zero]
    refine ⟨?_, ?_⟩
    · funext c g
      simp only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]
      rfl
    · funext c g
      simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rfl
  | succ i ih =>
    intro hi Φ
    have h : i < r := hi
    obtain ⟨hA, hB⟩ := ih (Nat.le_of_lt h) Φ
    have hp : (L.p ⟨i, h⟩).1 = X.op ⟨i, h⟩ 0 := by rw [hL.1 ⟨i, h⟩]; rfl
    have hc : (L.c ⟨i, h⟩).1 = X.op ⟨i, h⟩ 1 := by rw [hL.2.2.1 ⟨i, h⟩]; rfl
    have hci : (L.ci ⟨i, h⟩).1 = X.op ⟨i, h⟩ 2 := by rw [hL.2.2.2.1 ⟨i, h⟩]; rfl
    rw [rdsVp_succ L Y i h, rds_Tl_mul_0, rds_Tl_mul_1]
    refine ⟨?_, ?_⟩
    · have e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y + L.p ⟨i, h⟩) * rdsVp L Y i 0 0 +
          -L.c ⟨i, h⟩ * rdsVp L Y i 1 0).1 Φ : RadSp k r z z' π π') =
          Y • ((rdsVp L Y i 0 0).1 Φ) + X.op ⟨i, h⟩ 0 ((rdsVp L Y i 0 0).1 Φ) -
            X.op ⟨i, h⟩ 1 ((rdsVp L Y i 1 0).1 Φ) := by
        rw [rds_fst_add, rds_fst_mul, rds_fst_mul, rds_fst_add, rds_fst_alg, rdsR_fst_neg, hp, hc]
        simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.neg_apply, Module.algebraMap_end_apply,
          sub_eq_add_neg]
      rw [e, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]
      funext c g
      simp only [crd, Q.cmp, Q.vAB, dif_pos h, if_true, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rfl
    · have e : ((L.ci ⟨i, h⟩ * rdsVp L Y i 0 0).1 Φ : RadSp k r z z' π π') =
          X.op ⟨i, h⟩ 2 ((rdsVp L Y i 0 0).1 Φ) := by
        rw [rds_fst_mul, hci]
        rfl
      rw [e, rds_op_coe, hA]
      funext c g
      simp only [crd, Q.cmp, Q.vAB, dif_pos h]
      rfl

theorem rds_vabm_ind (hL : IsActualLevel X L) (Y : ℂ) : ∀ i : ℕ, i ≤ r → ∀ Φ : RadSp k r z z' π π',
    ((((rdsVvp L Y i) 0 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (CutMP.vABm r Y i) 0) (Φ : Fn k r (Wq →L[ℂ] Wp)) ∧
      ((((rdsVvp L Y i) 1 0).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        crd (Q.cmp (CutMP.vABm r Y i) 1) (Φ : Fn k r (Wq →L[ℂ] Wp)) := by
  intro i
  induction i with
  | zero =>
    intro _ Φ
    rw [rdsVvp_zero]
    refine ⟨?_, ?_⟩
    · funext c g
      simp only [Matrix.one_apply_eq, rdsR_fst_one, Module.End.one_apply]
      rfl
    · funext c g
      simp only [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), rdsR_fst_zero, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rfl
  | succ i ih =>
    intro hi Φ
    have h : i < r := hi
    obtain ⟨hA, hB⟩ := ih (Nat.le_of_lt h) Φ
    have hp : (L.pb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 3 := by rw [hL.2.1 ⟨i, h⟩]; rfl
    have hc : (L.cb ⟨i, h⟩).1 = X.op ⟨i, h⟩ 4 := by rw [hL.2.2.2.2.1 ⟨i, h⟩]; rfl
    have hci : (L.cbi ⟨i, h⟩).1 = X.op ⟨i, h⟩ 5 := by rw [hL.2.2.2.2.2.1 ⟨i, h⟩]; rfl
    rw [rdsVvp_succ L Y i h, rds_Tvl_mul_0, rds_Tvl_mul_1]
    refine ⟨?_, ?_⟩
    · have e : (((algebraMap ℂ (Pr (RadSp k r z z' π π')) Y - L.pb ⟨i, h⟩) * rdsVvp L Y i 0 0 +
          -L.cb ⟨i, h⟩ * rdsVvp L Y i 1 0).1 Φ : RadSp k r z z' π π') =
          Y • ((rdsVvp L Y i 0 0).1 Φ) - X.op ⟨i, h⟩ 3 ((rdsVvp L Y i 0 0).1 Φ) -
            X.op ⟨i, h⟩ 4 ((rdsVvp L Y i 1 0).1 Φ) := by
        rw [rds_fst_add, rds_fst_mul, rds_fst_mul, rdsR_fst_sub, rds_fst_alg, rdsR_fst_neg, hp, hc]
        simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.neg_apply,
          Module.algebraMap_end_apply, sub_eq_add_neg]
      rw [e, Submodule.coe_sub, Submodule.coe_sub, Submodule.coe_smul, rds_op_coe, rds_op_coe, hA, hB]
      funext c g
      simp only [crd, Q.cmp, CutMP.vABm, dif_pos h, if_true, Pi.sub_apply, Pi.smul_apply]
      rfl
    · have e : ((L.cbi ⟨i, h⟩ * rdsVvp L Y i 0 0).1 Φ : RadSp k r z z' π π') =
          X.op ⟨i, h⟩ 5 ((rdsVvp L Y i 0 0).1 Φ) := by
        rw [rds_fst_mul, hci]
        rfl
      rw [e, rds_op_coe, hA]
      funext c g
      simp only [crd, Q.cmp, CutMP.vABm, dif_pos h]
      rfl

theorem rds_cprod (hL : IsActualLevel X L) : ∀ (ls : List (Fin r)) (Φ : RadSp k r z z' π π'),
    ((((ls.map L.c).prod).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        (fun c g => (ls.map fun l => c l).prod • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) ∧
      ((((ls.map L.cb).prod).1 Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
        (fun c g => (ls.map fun l => star (c l)).prod • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g) := by
  intro ls
  induction ls with
  | nil =>
    intro Φ
    refine ⟨?_, ?_⟩ <;> (funext c g; simp only [List.map_nil, List.prod_nil, one_smul]; rfl)
  | cons a ls ih =>
    intro Φ
    obtain ⟨h1, h2⟩ := ih Φ
    have hc : (L.c a).1 = X.op a 1 := by rw [hL.2.2.1 a]; rfl
    have hcb : (L.cb a).1 = X.op a 4 := by rw [hL.2.2.2.2.1 a]; rfl
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, rds_fst_mul, hc, Module.End.mul_apply, rds_op_coe, h1]
      funext c g
      simp only [crd, opL, cOp, List.map_cons, List.prod_cons, smul_smul]
    · rw [List.map_cons, List.prod_cons, rds_fst_mul, hcb, Module.End.mul_apply, rds_op_coe, h2]
      funext c g
      simp only [crd, opL, cbOp, List.map_cons, List.prod_cons, smul_smul]

end rad

theorem spectral_radial_action : RDSARad := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X L hL y Φ
  have hDr : ∀ Ψ : RadSp P.k P.r z z' π π',
      (((L.Dr).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
        CutMP.dMul (CutMP.drF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Ψ
    rw [R.LevelData.Dr, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).1]
    funext c g
    simp only [CutMP.dMul, CutMP.drF, List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.prod_ofFn]
  have hDrb : ∀ Ψ : RadSp P.k P.r z z' π π',
      (((L.Drb).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) =
        CutMP.dMul (CutMP.drbF P.r) (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    intro Ψ
    rw [R.LevelData.Drb, List.ofFn_eq_map, (rds_cprod X L hL _ Ψ).2]
    funext c g
    simp only [CutMP.dMul, CutMP.drbF, List.map_map, Function.comp_def]
    rw [← List.ofFn_eq_map, List.prod_ofFn, map_prod]
    rfl
  refine ⟨?_, ?_⟩
  · rw [R.LevelData.Ahat, rds_fst_mul, Module.End.mul_apply, hDr, R.LevelData.Ar, rds_tprod,
      (rds_vab_ind X L hL y P.r le_rfl Φ).1]
  · rw [R.LevelData.Ahatv, rds_fst_mul, Module.End.mul_apply, hDrb, R.LevelData.Avr, rds_tvprod,
      (rds_vabm_ind X L hL y P.r le_rfl Φ).1]

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpRGrp
section
open MeasureTheory
open scoped Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

def RDSNicePoly : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (o κ : ℕ)
    (Θ : B.DiffOp k r Wp Wq), CutMP.PolyOp o κ Θ →
      ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), NiceAll D F → NiceAll D (B.opApply Θ F) ∧ NiceAll D (B.opAdj Θ F)

section swap

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

end swap

theorem opProp1_of_poly (hN : RDSNicePoly) {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (D : B.RealPlaceData k r Wp Wq) {o κ : ℕ} {Θ : B.DiffOp k r Wp Wq} (hP : CutMP.PolyOp o κ Θ)
    (hC : B.Commutes D (B.GPos D) Θ) : OpProp1 D Θ := by
  obtain ⟨hS, hG, -⟩ := CutMP.polynomial_decay_admissible k r Wp Wq o κ Θ hP
  refine ⟨hS _, hC, fun ε _ => ⟨κ, Nat.cast_nonneg _, fun T hT => ?_⟩, fun F hF => hN k r Wp Wq D o κ Θ hP F hF⟩
  obtain ⟨-, -, hb⟩ := hG κ le_rfl T hT
  obtain ⟨C₁, hC₁⟩ := hb (B.opOrder Θ + 5)
  exact ⟨C₁, fun u v hu hv hl g hg _ => hC₁ u v hu hv hl g hg⟩

section ffl

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
  [NormedSpace ℂ Wq] {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

theorem ffl_mono {D₁ D₂ : Set (Q.Mx k r)} (h : ∀ g ∈ Q.Glev k r 0, g ∈ D₂ → g ∈ D₁) {J : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r z z' π π' 0 D₁) : J ∈ Q.FFl k r z z' π π' 0 D₂ := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨fun g₀ hg₀ => h1 g₀ ⟨hg₀.1, h g₀ hg₀.1 hg₀.2⟩, fun g hg n hn => h2 g ⟨hg.1, h g hg.1 hg.2⟩ n hn,
    fun g hg n hn => h3 g ⟨hg.1, h g hg.1 hg.2⟩ n hn, fun g hg u hu u' hu' => h4 g ⟨hg.1, h g hg.1 hg.2⟩ u hu u' hu'⟩

end ffl

theorem rDSOpRGrp_of_nice (hN : RDSNicePoly) : RDSOpRGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadP_of_steps CutMP.residue_first_move_holds CutMP.residue_second_move_holds k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.ri_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_positive_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

theorem rDSOpRvGrp_of_nice (hN : RDSNicePoly) : RDSOpRvGrp := by
  intro Wp Wq _ _ _ _ _ _ k r D Y σ
  obtain ⟨ε, hε⟩ := CutMP.jDRRadM_of_parts CutMP.mirror_residue_beta_holds CutMP.mirror_residue_top_holds CutMP.GrpMA.mirror_residue_first_move
    CutMP.mirror_residue_second_move (CutMP.jDRvConseq_of CutMP.mirror_residue_continuity) k r
  obtain ⟨Θ, hP, hO, hR⟩ := CutMP.rim_real (Wp := Wp) (Wq := Wq) D.z D.z' Y (σ * ε)
  have hComm : B.Commutes D (B.GPos D) Θ := by
    intro p hp F hF g hg
    rw [hO] at hF
    have hgG : g ∈ B.GV k r := hg.1
    have hsg : B.sgs p g ∈ B.GV k r := Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hgG
    rw [hR _ _ (Formalism.FourierDecayAlt.P.B5.ckOn_rho D hp hF) g hgG hgG]
    have e2 : B.rho D p (B.opApply Θ F) g =
        B.rho D p (fun x => (σ * ε) • CutMP.rvhatOp k r D.z D.z' Y F x) g := by
      simp only [B.rho]
      rw [hR _ _ hF _ hsg hsg]
    rw [e2, CutMP.inverse_function_minus_holds k r Wp Wq D Y p hp F hF g hg]
    simp only [B.rho, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp]
  refine ⟨Θ, opProp1_of_poly hN D hP hComm, ?_⟩
  intro J hJ x hx
  have hJ' : J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (Q.OmPlus k r D.z D.z') :=
    ffl_mono (D₁ := JF.Om k r D.z D.z') (D₂ := Q.OmPlus k r D.z D.z')
      (fun g hg hgO => ⟨by simpa [Q.Glev] using hg.1, hgO⟩) hJ
  have hDom := Formalism.FourierDecayAlt.P.JCx2.rma_isDom_omPlus (k := k) (r := r) D.z_mem D.z'_mem
  have hcell : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.OmPlus k r D.z D.z' :=
    Formalism.FourierDecayAlt.P5.Rad.wCell_mem_omPlus D.z_mem D.z'_mem hx.1 hx.2.1 hx.2.2
  have key := hε Wp Wq D.z D.z' D.π D.π' (Q.OmPlus k r D.z D.z') Y D.z_mem D.z'_mem hDom J hJ' x.1 hx.1 x.2
    hx.2.1 hcell
  rw [← key]
  have hW0 : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ Q.Glev k r 0 :=
    Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hx.1 _)
      (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hx.2.1)
  have hWG : Q.wCell k r (Fin.last r) x.1 * x.2 ∈ B.GV k r := by simpa [Q.Glev] using hW0.1
  have hCk : B.CkOn ((r + k : ℕ) : ℕ∞) (Q.Glev k r 0 ∩ JF.Om k r D.z D.z') J := by
    intro g₀ hg₀
    obtain ⟨U', F', hU', hg₀U, hc, he⟩ := hJ.1 g₀ hg₀
    refine ⟨U', F', hU', hg₀U, hc.of_le (by exact_mod_cast le_top), fun y hy hyG => he y hy ?_⟩
    simpa [Q.Glev] using hyG
  simp only [Q.resG]
  rw [hR _ J hCk _ ⟨hW0, hWG, hcell⟩ hWG, smul_smul, smul_smul, smul_smul]
  congr 1
  ring

end Formalism.FourierDecayAlt.P.CutSE
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSPLoc
section
namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_pairing_locality : RDSPLoc := by
  intro k r Wp Wq _ _ _ _ _ _ Θ U X Y hU hXY g hgU hgV
  have h : ∀ x ∈ B.GV k r, x ∈ U → X x = Y x := fun x hx hxU => hXY x hxU hx
  exact ⟨Formalism.FourierDecayAlt.P.MinorPolynomials.opApply_congr Θ hU h hgV hgU,
    Formalism.FourierDecayAlt.P.CutMP.JA.LocOp.opAdj_congr_GV Θ hU h g hgV hgU⟩

end Formalism.FourierDecayAlt.P.CutSE
end

