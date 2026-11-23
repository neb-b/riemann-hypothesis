module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0243
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0215
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0242
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0038

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockTwoApply
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem fsym (m n : ℕ) (i : Fin (m + n)) : finSumFinEquiv.symm i =
    if h : i.val < m then Sum.inl ⟨i, h⟩ else Sum.inr ⟨i - m, by omega⟩ := by
  split_ifs with h
  · rw [Equiv.symm_apply_eq]; ext; simp
  · rw [Equiv.symm_apply_eq]; ext; simp; omega

theorem block_two_apply {p s : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (B' : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D' : Matrix (Fin s) (Fin s) ℂ) (a b : Fin (p + s)) :
    U.blk2 A B' C D' a b =
      if ha : a.val < p then (if hb : b.val < p then A ⟨a, ha⟩ ⟨b, hb⟩ else B' ⟨a, ha⟩ ⟨b - p, by omega⟩)
      else (if hb : b.val < p then C ⟨a - p, by omega⟩ ⟨b, hb⟩ else D' ⟨a - p, by omega⟩ ⟨b - p, by omega⟩) := by
  simp only [U.blk2, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [fsym, fsym]
  split_ifs <;> rfl

theorem w_mul_apply {d : ℕ} {ι : Type*} (M : Matrix (Fin d) ι ℂ) (a : Fin d) (b : ι) :
    (G.wMat d * M) a b = M a.rev b := by
  simp [G.wMat, Matrix.mul_apply]

theorem mul_w_apply {d : ℕ} {ι : Type*} [Fintype ι] (M : Matrix ι (Fin d) ℂ) (a : ι) (b : Fin d) :
    (M * G.wMat d) a b = M a b.rev := by
  simp only [G.wMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro c _ hc; rw [if_neg]; intro h; apply hc; rw [h, Fin.rev_rev]
  · simp

theorem xcongr {j : ℕ} (x : MJ j) {a a' b b' : Fin j} (ha : a.val = a'.val) (hb : b.val = b'.val) :
    x a b = x a' b' := by
  rw [Fin.ext ha, Fin.ext hb]

theorem levi_eq {k r j : ℕ} (hj : j + 1 ≤ r) (x : MJ j) :
    levi k r j x = D.castM (by omega : j + 1 + (r - (j + 1)) = r)
      (U.blk3 (k := k) (j := j + 1) (ρ := r - (j + 1)) (U.blk2 x 0 0 0) 0 0 0 0 0 0 0
        (G.wMat (j + 1) * U.blk2 (-xᴴ) 0 0 0 * G.wMat (j + 1))) := by
  ext p q
  obtain ⟨X, hX⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) p)
  obtain ⟨Y, hY⟩ := (U.eB k (j + 1) (r - (j + 1))).surjective (Fin.cast (by omega) q)
  have hp : p.val = (U.eB k (j + 1) (r - (j + 1)) X).val := by rw [hX]; rfl
  have hq : q.val = (U.eB k (j + 1) (r - (j + 1)) Y).val := by rw [hY]; rfl
  have e : ∀ M : B.Mat k (j + 1 + (r - (j + 1))),
      D.castM (by omega : j + 1 + (r - (j + 1)) = r) M p q =
        M (U.eB k (j + 1) (r - (j + 1)) X) (U.eB k (j + 1) (r - (j + 1)) Y) := by
    intro M
    rw [hX, hY]; rfl
  rw [e, Ux4.block3_apply]
  rcases X with ((a | v) | a) <;> rcases Y with ((b | w) | b) <;>
    simp only [Ux4.block_index_first_val_eq, Ux4.block_index_middle_val_eq, Ux4.block_index_last_val_eq] at hp hq <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, Matrix.fromCols_apply_inl,
      Matrix.fromCols_apply_inr, Matrix.zero_apply, levi, Matrix.of_apply, block_two_apply, w_mul_apply, mul_w_apply,
      Matrix.mul_assoc, Fin.val_rev, Matrix.neg_apply, Matrix.conjTranspose_apply] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | skip
  all_goals first
    | exact xcongr x (by simp; omega) (by simp; omega)
    | (simp only [Complex.star_def]; congr 2; exact xcongr x (by simp; omega) (by simp; omega))

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ContDiffOfSnd
section
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem cont_ofSnd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := continuous_snd

theorem contDiff_ofSnd : ContDiff ℝ ∞ fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := contDiff_snd

theorem contDiff_pair (τ : ℂ) : ContDiff ℝ ∞ fun Z : MJ j => ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) :=
  contDiff_const.prodMk contDiff_id

theorem isOpen_inv : IsOpen {Z : MJ j | Z.det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem diffAt_fst {G : ℂ × (Fin j → Fin j → ℂ) → E} {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    DifferentiableAt ℝ (fun τ : ℂ => G (τ, q.2)) q.1 := by
  have hd : DifferentiableAt ℝ G q := (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  exact hd.comp q.1 ((differentiableAt_id).prodMk (differentiableAt_const _))

theorem dz_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dz (fun s => F s + G s) τ = PBP.dz F τ + PBP.dz G τ := by
  unfold PBP.dz
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dzb_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dzb (fun s => F s + G s) τ = PBP.dzb F τ + PBP.dzb G τ := by
  unfold PBP.dzb
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dz_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dz (fun s => c • F s) τ = c • PBP.dz F τ := by
  unfold PBP.dz
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dzb_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dzb (fun s => c • F s) τ = c • PBP.dzb F τ := by
  unfold PBP.dzb
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dz_const (v : E) (τ : ℂ) : PBP.dz (fun _ : ℂ => v) τ = 0 := by simp [PBP.dz]

theorem dzb_const (v : E) (τ : ℂ) : PBP.dzb (fun _ : ℂ => v) τ = 0 := by simp [PBP.dzb]

theorem zop_id : ZOp (E := E) (j := j) (fun h => h) := by
  refine ⟨fun h₁ h₂ Z h => h.eq_of_nhds, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U κ _ _ hκ
  exact ⟨hκ, fun q _ => ⟨rfl, rfl⟩⟩

theorem zop_zero : ZOp (E := E) (j := j) (fun _ _ => 0) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ => by simp, ?_⟩
  intro U κ _ _ _
  exact ⟨contDiffOn_const, fun q _ => ⟨dz_const _ _, dzb_const _ _⟩⟩

theorem ZOp.smooth {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {V : Set (MJ j)} (hV : IsOpen V)
    (hVi : V ⊆ {Z | Z.det ≠ 0}) {h : MJ j → E} (hh : ContDiffOn ℝ ∞ h V) : ContDiffOn ℝ ∞ (T h) V := by
  let U : Set (ℂ × (Fin j → Fin j → ℂ)) := {q | (Matrix.of q.2 : MJ j) ∈ V}
  have hU : IsOpen U := hV.preimage cont_ofSnd
  have hUi : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hVi hq
  have hκ : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (fun _ : ℂ => h) q.1 (Matrix.of q.2)) U :=
    hh.comp contDiff_ofSnd.contDiffOn (fun q hq => hq)
  have h1 := (hT.par U (fun _ => h) hU hUi hκ).1
  exact h1.comp (contDiff_pair 0).contDiffOn (fun Z hZ => hZ)

theorem ZOp.add' {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) :
    ZOp (fun h Z => T h Z + S h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h, hS.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, hS.add V h₁ h₂ hV hVi s₁ s₂ Z hZ]; abel
  · intro V c h hV hVi s Z hZ
    rw [hT.smul V c h hV hVi s Z hZ, hS.smul V c h hV hVi s Z hZ, smul_add]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    refine ⟨t1.add s1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    have d2 := diffAt_fst hU s1 hq
    refine ⟨?_, ?_⟩
    · rw [dz_add d1 d2, (t2 q hq).1, (s2 q hq).1]
    · rw [dzb_add d1 d2, (t2 q hq).2, (s2 q hq).2]

theorem ZOp.cmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {c : MJ j → ℂ}
    (hc : ContDiffOn ℝ ∞ c {Z | Z.det ≠ 0}) : ZOp (fun h Z => c Z • T h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, smul_add]
  · intro V c' h hV hVi s Z hZ
    rw [hT.smul V c' h hV hVi s Z hZ, smul_comm]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    have hc' : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => c (Matrix.of q.2)) U :=
      hc.comp contDiff_ofSnd.contDiffOn (fun q hq => hUi hq)
    refine ⟨hc'.smul t1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    exact ⟨by rw [dz_smul d1, (t2 q hq).1], by rw [dzb_smul d1, (t2 q hq).2]⟩

theorem ZOp.csmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (c : ℂ) : ZOp (fun h Z => c • T h Z) :=
  hT.cmul (c := fun _ => c) contDiffOn_const

theorem ZOp.comp {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) : ZOp (fun h => T (S h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h₁ h₂ Z h
    apply hT.loc
    filter_upwards [h.eventually_nhds] with Z' hZ'
    exact hS.loc _ _ Z' hZ'
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    have e : S (h₁ + h₂) =ᶠ[𝓝 Z] S h₁ + S h₂ := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.add V h₁ h₂ hV hVi s₁ s₂ Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.add V (S h₁) (S h₂) hV hVi (hS.smooth hV hVi s₁) (hS.smooth hV hVi s₂) Z hZ
  · intro V c h hV hVi s Z hZ
    have e : S (c • h) =ᶠ[𝓝 Z] c • S h := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.smul V c h hV hVi s Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.smul V c (S h) hV hVi (hS.smooth hV hVi s) Z hZ
  · intro U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U (fun τ => S (κ τ)) hU hUi s1
    refine ⟨t1, fun q hq => ?_⟩
    have hsl : IsOpen {Z : MJ j | ((q.1, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (contDiff_pair q.1).continuous
    have e1 : (fun Z => PBP.dz (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dz (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).1
    have e2 : (fun Z => PBP.dzb (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).2
    exact ⟨by rw [(t2 q hq).1, hT.loc _ _ _ e1], by rw [(t2 q hq).2, hT.loc _ _ _ e2]⟩

theorem zop_sum {ι : Type*} (s : Finset ι) {T : ι → (MJ j → E) → MJ j → E} (hT : ∀ i ∈ s, ZOp (T i)) :
    ZOp (fun h Z => ∑ i ∈ s, T i h Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zop_zero (E := E) (j := j))
  | insert a s ha ih =>
    have h1 := (hT a (by simp)).add' (ih (fun i hi => hT i (by simp [hi])))
    simpa [Finset.sum_insert ha] using h1

theorem zop_foldr : ∀ L : List ((MJ j → E) → MJ j → E), (∀ T ∈ L, ZOp T) →
    ZOp (fun f => L.foldr (fun T h => T h) f)
  | [], _ => zop_id
  | T :: L, h => by
    simp only [List.foldr_cons]
    exact (h T (by simp)).comp (zop_foldr L (fun T' hT' => h T' (by simp [hT'])))

end Formalism.FourierDecayAlt.P.WirtingerOperators
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixLeviBlockThree
section
open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem leviElement_mem_GV {k p ρ : ℕ} (q : Matrix (Fin p) (Fin p) ℂ) (hq : IsUnit q.det) : U.muP k p ρ q ∈ B.GV k (p + ρ) :=
  (Formalism.FourierDecayAlt.P.slice_membership k p ρ).2.1 q (isUnit_iff_ne_zero.mp hq)

def MuPToOm : Prop := ∀ (k p ρ : ℕ) (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ), inWb k (p + ρ) z → inWb k (p + ρ) z' →
  ∀ y ∈ domP k (p + ρ) p z z', y ∈ B.GV k (p + ρ) →
  ∃ q : Matrix (Fin p) (Fin p) ℂ, IsUnit q.det ∧ ∃ V ∈ nhds y, IsCompact V ∧
    ∀ g ∈ V, g ∈ B.GV k (p + ρ) → U.muP k p ρ q * g ∈ JF.Om k (p + ρ) z z'

section zhat

variable {k p ρ : ℕ}

theorem corner_matrix_levi_block_three (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ)
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.muP k p ρ q * U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks ((qᴴ)⁻¹ * (G.wMat p * BlochKatoReduction))
        ((qᴴ)⁻¹ * (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z')))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) := by
  unfold U.muP
  rw [Ux3.block3_mul, Ux3.z_hat_of_block3 z z' hz hz']
  have hw : ∀ M : Matrix (Fin p) (Fin p) ℂ, G.wMat p * (G.wMat p * M * G.wMat p) = M * G.wMat p := by
    intro M
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Ux3.wMat_mul_self, Matrix.one_mul]
  congr 2 <;> simp only [Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, hw, Matrix.mul_assoc]
  · rw [← Matrix.mul_assoc (G.wMat p), hw]; simp only [Matrix.mul_assoc]

theorem zhat_eq_blk (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (product_first_partition : Matrix (Fin p) (Fin p) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin p) (Fin p) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ)
    (BlochKatoReduction : Matrix (Fin p) (Fin p) ℂ) (SumRepresentations : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin p) (Fin p) ℂ) :
    Zhat k (p + ρ) z z' (U.blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks (G.wMat p * BlochKatoReduction)
        (G.wMat p * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (U.lowV k p ρ z'))) :=
  Ux3.z_hat_of_block3 z z' hz hz' _ _ _ _ _ _ _ _ _

theorem minor_gen {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hl : m ≤ ρ + 1) (h : p + m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A (Bm.submatrix id (Fin.castLE hl))
        (Cm.submatrix (Fin.castLE hl) id) (Dm.submatrix (Fin.castLE hl) (Fin.castLE hl))) := by
  ext a b
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b <;>
    simp [Matrix.reindex_apply, Ux3.eC_symm_castAdd h, Ux3.eC_symm_natAdd h hl]

theorem minor_low {m : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ)
    (Cm : Matrix (Fin (ρ + 1)) (Fin p) ℂ) (Dm : Matrix (Fin (ρ + 1)) (Fin (ρ + 1)) ℂ)
    (hmp : m ≤ p) (h : m ≤ p + ρ + 1) :
    (Matrix.reindex (Ux3.eC p ρ) (Ux3.eC p ρ) (Matrix.fromBlocks A Bm Cm Dm)).submatrix (Fin.castLE h) (Fin.castLE h) =
      A.submatrix (Fin.castLE hmp) (Fin.castLE hmp) := by
  have e : ∀ a : Fin m, (Ux3.eC p ρ).symm (Fin.castLE h a) = Sum.inl (Fin.castLE hmp a) := by
    intro a; rw [Equiv.symm_apply_eq]; ext; simp [Ux3.column_index_first_val]
  ext a b
  simp [Matrix.reindex_apply, e]

theorem zh_eq_blk (y : B.Mat k (p + ρ)) :
    G.wMat p * y.submatrix (fun a => U.eB k p ρ (Sum.inr a)) (fun b => U.eB k p ρ (Sum.inl (Sum.inl b))) =
      U.Zh k p ρ y := by
  ext a b
  rw [Ux3.wMat_mul_apply]
  simp only [Matrix.submatrix_apply, U.Zh]
  congr 1
  all_goals (ext; first | (rw [Ux3.block_index_last_val]; simp [Fin.val_rev]; omega) | (rw [Ux3.block_index_first_val]))

theorem minor_leviElement_mul_high (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) (m : ℕ) (hm : m ≤ ρ + 1) :
    Dmin k (p + ρ) z z' (U.muP k p ρ q * g) ⟨p + m, by omega⟩ =
      ((qᴴ)⁻¹).det * Dmin k (p + ρ) z z' g ⟨p + m, by omega⟩ := by
  have hg := Ux3.block3_eta g
  unfold Dmin
  rw [hg, corner_matrix_levi_block_three z z' hz hz', zhat_eq_blk z z' hz hz']
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det = _ * ((Matrix.reindex _ _ _).submatrix
      (Fin.castLE (show p + m ≤ p + ρ + 1 by omega)) (Fin.castLE (show p + m ≤ p + ρ + 1 by omega))).det
  rw [minor_gen _ _ _ _ hm, minor_gen _ _ _ _ hm, Matrix.det_reindex_self, Matrix.det_reindex_self]
  set Q := (qᴴ)⁻¹
  have e : ∀ (A : Matrix (Fin p) (Fin p) ℂ) (Bm : Matrix (Fin p) (Fin m) ℂ) (Cm : Matrix (Fin m) (Fin p) ℂ)
      (Dm : Matrix (Fin m) (Fin m) ℂ),
      Matrix.fromBlocks (Q * A) (Q * Bm) Cm Dm = Matrix.fromBlocks Q 0 0 1 * Matrix.fromBlocks A Bm Cm Dm := by
    intro A Bm Cm Dm
    rw [Matrix.fromBlocks_multiply]
    simp
  have hsub : ∀ (Bm : Matrix (Fin p) (Fin (ρ + 1)) ℂ),
      (Q * Bm).submatrix id (Fin.castLE hm) = Q * Bm.submatrix id (Fin.castLE hm) := by
    intro Bm; ext a b; simp [Matrix.mul_apply]
  rw [hsub, e, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

theorem minor_leviElement_mul_low (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hA : IsUnit (U.Zh k p ρ y).det) (m : ℕ) (hmp : m ≤ p) :
    Dmin k (p + ρ) z z' (U.muP k p ρ (U.Zh k p ρ y)ᴴ * y) ⟨m, by omega⟩ = 1 := by
  have hg := Ux3.block3_eta y
  unfold Dmin
  conv_lhs => rw [hg]
  rw [corner_matrix_levi_block_three z z' hz hz', ← hg]
  show ((Matrix.reindex _ _ _).submatrix (Fin.castLE (show m ≤ p + ρ + 1 by omega))
    (Fin.castLE (show m ≤ p + ρ + 1 by omega))).det = 1
  rw [minor_low _ _ _ _ hmp, zh_eq_blk, Matrix.conjTranspose_conjTranspose, Matrix.nonsing_inv_mul _ hA]
  have : (1 : Matrix (Fin p) (Fin p) ℂ).submatrix (Fin.castLE hmp) (Fin.castLE hmp) = 1 := by
    ext a b; simp [Matrix.one_apply, Fin.ext_iff]
  rw [this, Matrix.det_one]

end zhat

section main

variable {k p ρ : ℕ}

theorem gf_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (q : Matrix (Fin p) (Fin p) ℂ) (g : B.Mat k (p + ρ)) :
    Gf k (p + ρ) z z' (U.muP k p ρ q * g) = Complex.normSq ((qᴴ)⁻¹).det * Gf k (p + ρ) z z' g := by
  have e1 : Fin.last (p + ρ + 1) = (⟨p + (ρ + 1), by omega⟩ : Fin (p + ρ + 2)) := Fin.ext rfl
  have e0 : (⟨p + ρ, by omega⟩ : Fin (p + ρ + 2)) = ⟨p + ρ, by omega⟩ := rfl
  unfold Gf
  rw [e1, minor_leviElement_mul_high z z' hz hz' q g (ρ + 1) le_rfl, minor_leviElement_mul_high z z' hz hz' q g ρ (by omega),
    Complex.normSq_mul, Complex.normSq_mul]
  ring

theorem det_Q_ne {A : Matrix (Fin p) (Fin p) ℂ} (hAd : A.det ≠ 0) : (((Aᴴ)ᴴ)⁻¹).det ≠ 0 := by
  rw [Matrix.conjTranspose_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero hAd

theorem omPlus_muP (z z' : Fin (2 * (p + ρ) + k + 1) → ℂ) (hz : inWb k (p + ρ) z) (hz' : inWb k (p + ρ) z')
    (y : B.Mat k (p + ρ)) (hy : y ∈ domP k (p + ρ) p z z') (hAd : (U.Zh k p ρ y).det ≠ 0) :
    U.muP k p ρ (U.Zh k p ρ y)ᴴ * y ∈ Q.OmPlus k (p + ρ) z z' := by
  have hQ := det_Q_ne hAd
  refine ⟨fun l hl => ?_, ?_⟩
  · by_cases hlp : l.val ≤ p
    · have e : l = ⟨l.val, by omega⟩ := Fin.ext rfl
      rw [e, minor_leviElement_mul_low z z' hz hz' y (isUnit_iff_ne_zero.mpr hAd) l.val hlp]
      exact one_ne_zero
    · have e : l = ⟨p + (l.val - p), by omega⟩ := Fin.ext (by simp only; omega)
      have hyl := hy.1 l (by omega) hl
      rw [e] at hyl ⊢
      rw [minor_leviElement_mul_high z z' hz hz' _ y (l.val - p) (by omega)]
      exact mul_ne_zero hQ hyl
  · rw [gf_muP z z' hz hz']
    exact mul_pos (Complex.normSq_pos.mpr hQ) hy.2

end main

theorem mem_of_sub_pre {k n : ℕ} {S : Set (B.Mat k n)} {f : B.Mat k n → B.Mat k n} {V : Set (B.Mat k n)}
    (hVO : V ⊆ {g | f g ∈ S}) {g : B.Mat k n} (hg : g ∈ V) : f g ∈ S := hVO hg

theorem mem_Om_of {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {x : B.Mat k r} (h1 : x ∈ B.GV k r)
    (h2 : x ∈ Q.OmPlus k r z z') : x ∈ JF.Om k r z z' := ⟨h1, h2⟩

theorem levi_move_into_big_cell : MuPToOm := by
  intro k p ρ z z' hz hz' y hy hyG
  have hDp : Dmin k (p + ρ) z z' y ⟨p, by omega⟩ ≠ 0 := hy.1 ⟨p, by omega⟩ (le_refl p) (by simp)
  have hAd : (U.Zh k p ρ y).det ≠ 0 := by
    have h := Formalism.FourierDecayAlt.P.Ux3.zhDmin k p ρ z z' y
    unfold U.DjU at h
    rw [← h]; exact hDp
  have hqu : IsUnit ((U.Zh k p ρ y)ᴴ).det := by
    rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hAd)
  have hy1 := omPlus_muP z z' hz hz' y hy hAd
  have hO : IsOpen {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} :=
    (Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.isOpen_OmPlus z z').preimage (continuous_const.matrix_mul continuous_id)
  have hy1' : y ∈ {g : B.Mat k (p + ρ) | U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z'} := hy1
  have hmem := hO.mem_nhds hy1'
  have hLC : LocallyCompactSpace (B.Mat k (p + ρ)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (2 * (p + ρ) + k + 1) → Fin (2 * (p + ρ) + k + 1) → ℂ))
  obtain ⟨V, hV, hVO, hVc⟩ := local_compact_nhds hmem
  refine ⟨(U.Zh k p ρ y)ᴴ, hqu, ?_⟩
  refine ⟨V, hV, hVc, ?_⟩
  intro g hg hgG
  have h1 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ B.GV k (p + ρ) := by
    have hm := leviElement_mem_GV (k := k) (ρ := ρ) (U.Zh k p ρ y)ᴴ hqu
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hm hgG
  have h2 : U.muP k p ρ (U.Zh k p ρ y)ᴴ * g ∈ Q.OmPlus k (p + ρ) z z' :=
    mem_of_sub_pre (f := fun g => U.muP k p ρ (U.Zh k p ρ y)ᴴ * g) hVO hg
  exact mem_Om_of h1 h2

end Formalism.FourierDecayAlt.P.PBQ
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpFromBlocks
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def fbHom (m n : Type*) [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] :
    Matrix m m ℂ × Matrix n n ℂ →+* Matrix (m ⊕ n) (m ⊕ n) ℂ where
  toFun p := Matrix.fromBlocks p.1 0 0 p.2
  map_one' := Matrix.fromBlocks_one
  map_mul' p q := by simp [Matrix.fromBlocks_multiply]
  map_zero' := by simp
  map_add' p q := by simp [Matrix.fromBlocks_add]

set_option backward.isDefEq.respectTransparency false in
theorem exp_reindex (e : m ≃ n) (M : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e M) = Matrix.reindex e e (NormedSpace.exp M) := by
  have hc : Continuous fun M : Matrix m m ℂ => Matrix.reindexAlgEquiv ℂ ℂ e M := by
    simp only [Matrix.coe_reindexAlgEquiv]; exact continuous_id.matrix_reindex e e
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) hc M
  simp only [Matrix.coe_reindexAlgEquiv] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem exp_fromBlocks (A : Matrix m m ℂ) (D : Matrix n n ℂ) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 D) = Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp D) := by
  have hc : Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => fbHom m n p := by
    show Continuous fun p : Matrix m m ℂ × Matrix n n ℂ => Matrix.fromBlocks p.1 0 0 p.2
    exact Continuous.matrix_fromBlocks continuous_fst continuous_const continuous_const continuous_snd
  open scoped Matrix.Norms.Operator in
  have h := NormedSpace.map_exp (fbHom m n) hc (A, D)
  open scoped Matrix.Norms.Operator in
  have h1 := Prod.fst_exp (A, D)
  open scoped Matrix.Norms.Operator in
  have h2 := Prod.snd_exp (A, D)
  change Matrix.fromBlocks _ 0 0 _ = NormedSpace.exp (Matrix.fromBlocks _ 0 0 _) at h
  rw [h1, h2] at h
  exact h.symm

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end

