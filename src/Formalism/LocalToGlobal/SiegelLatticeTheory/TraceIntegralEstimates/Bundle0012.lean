module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0021
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0017
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensRep
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.Bundle0005

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HJSpanLtZero
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal
open Matrix

namespace Formalism.L2.S.Pv.TauS

open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Loc

variable {n r : ℕ} (ε : Fin n → Bool) {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ}

private theorem hJ_add_lemma (x a b : Fin n → ℂ) : hJ ε x (a + b) = hJ ε x a + hJ ε x b := by
  simp only [hJ, Matrix.mulVec_add, dotProduct_add]

private theorem hJ_smul_lemma_2 (x a : Fin n → ℂ) (c : ℂ) : hJ ε x (c • a) = c * hJ ε x a := by
  simp only [hJ, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem hJ_zero_lemma_3 (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  simp only [hJ, Matrix.mulVec_zero, dotProduct_zero]

private theorem spanLt_mono_lemma_4 (e : Fin r → Fin n → ℂ) {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b := by
  unfold spanLt
  exact Submodule.span_mono (Set.image_mono (fun x (hx : x.1 < a) => (lt_of_lt_of_le hx h : x.1 < b)))

theorem hJ_spanLt_zero (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (a : Fin r) :
    ∀ u ∈ spanLt e a.1, hJ ε (f a) u = 0 := by
  intro u hu
  unfold spanLt at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    rw [hfe, if_neg]
    intro hab
    subst hab
    simp only [Set.mem_setOf_eq, lt_self_iff_false] at hb
  | zero => exact hJ_zero_lemma_3 ε _
  | add x y _ _ hx hy => rw [hJ_add_lemma, hx, hy, add_zero]
  | smul c x _ hx => rw [hJ_smul_lemma_2, hx, mul_zero]

theorem sub_one_spanLt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (k : ℕ) :
    ∀ u ∈ spanLt e (k + 1), (g - 1) *ᵥ u ∈ spanLt e k := by
  intro u hu
  unfold spanLt at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    have hbk : b.1 ≤ k := Nat.lt_succ_iff.mp hb
    exact spanLt_mono_lemma_4 e hbk (hg.1 b)
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx

theorem sub_one_nxt {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : Fin r) :
    (g - 1) *ᵥ nxt e z a ∈ spanLt e (a.1 + 1) := by
  have ha := a.isLt
  unfold nxt
  split_ifs with h
  · exact hg.1 ⟨a.1 + 1, h⟩
  · have hr : a.1 + 1 = r := by omega
    rw [hr]
    exact hg.2

theorem hJ_nxt (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (a : Fin r) : hJ ε (f a) (nxt e z a) = 0 := by
  unfold nxt
  split_ifs with h
  · rw [hfe, if_neg]
    intro hc
    have := congrArg Fin.val hc
    simp at this
  · exact hfz a

theorem rootCoord_mul (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hg' : InS e z g') (a : Fin r) :
    rootCoord ε e f z (g * g') a = rootCoord ε e f z g a + rootCoord ε e f z g' a := by
  unfold rootCoord
  have hs_mem : (g' - 1) *ᵥ nxt e z a ∈ spanLt e (a.1 + 1) := sub_one_nxt hg' a
  have h1 : (g - 1) *ᵥ ((g' - 1) *ᵥ nxt e z a) ∈ spanLt e a.1 := sub_one_spanLt hg a.1 _ hs_mem
  have hg'v : g' *ᵥ nxt e z a = nxt e z a + (g' - 1) *ᵥ nxt e z a := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  have hgs : g *ᵥ ((g' - 1) *ᵥ nxt e z a) =
      (g' - 1) *ᵥ nxt e z a + (g - 1) *ᵥ ((g' - 1) *ᵥ nxt e z a) := by
    rw [Matrix.sub_mulVec g 1, Matrix.one_mulVec]
    abel
  rw [← Matrix.mulVec_mulVec, hg'v, Matrix.mulVec_add, hgs]
  simp only [hJ_add_lemma]
  rw [hJ_spanLt_zero ε hfe a _ h1, hJ_nxt ε hfe hfz a]
  ring

theorem rootCoord_one (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) (hfz : ∀ a, hJ ε (f a) z = 0)
    (a : Fin r) : rootCoord ε e f z 1 a = 0 := by
  simp only [rootCoord, Matrix.one_mulVec]
  exact hJ_nxt ε hfe hfz a

theorem psiR_mul (gg : ℕ) (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) {g g' : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hg' : InS e z g') :
    psiR ε gg e f z (g * g') = psiR ε gg e f z g * psiR ε gg e f z g' := by
  have hsum : ∀ a, rootCoord ε e f z (g * g') a + star (rootCoord ε e f z (g * g') a) =
      (rootCoord ε e f z g a + star (rootCoord ε e f z g a)) +
        (rootCoord ε e f z g' a + star (rootCoord ε e f z g' a)) := by
    intro a
    rw [rootCoord_mul ε hfe hfz hg hg', star_add]
    ring
  unfold psiR
  rw [← Complex.exp_add]
  congr 1
  simp only [hsum, Finset.sum_add_distrib]
  ring

theorem psiR_one (gg : ℕ) (hfe : ∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0)
    (hfz : ∀ a, hJ ε (f a) z = 0) : psiR ε gg e f z 1 = 1 := by
  simp only [psiR, rootCoord_one ε hfe hfz, star_zero, add_zero, Finset.sum_const_zero, zero_div, mul_zero,
    Complex.exp_zero]

end Loc

section Glob

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

private theorem hJ_swap_lemma_5 {m : ℕ} (ε : Fin m → Bool) (x y : Fin m → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : ε i <;> simp [h] <;> ring

theorem hfe_X (v : InfinitePlace X.B.I.F) (a b : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0 := by
  rw [hJ_swap_lemma_5, ← Formalism.L2.SG.PoincareInHH.Cut.phi_hform]
  have h1 := Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) (X.eX b) (X.fY a)
  rw [X.ef b a] at h1
  have h0 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.eR b) (X.fR a) = if a = b then 1 else 0 := by
    apply X.ιE.injective
    refine h1.trans ?_
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg (Ne.symm hab), if_neg hab, map_zero]
  rw [h0]
  by_cases hab : a = b <;> simp [hab]

theorem hfz_X (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin D.R.rS) :
    hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := by
  rw [← Formalism.L2.SG.PoincareInHH.Cut.phi_hform]
  have h0 : Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.fR a) (X.zR u) = 0 := by
    apply X.ιE.injective
    rw [map_zero]
    exact (Formalism.L2.SG.PoincareInHH.Cut.hform_crd (X := X) (X.fY a) (X.zu u)).trans (X.zu_orth u a).2
  rw [h0, map_zero]

theorem psiInfU_one (u : D.what₂.Word) : X.psiInfU u 1 = 1 := by
  unfold HidaSetting.psiInfU psiInf
  refine Finset.prod_eq_one (fun v _ => ?_)
  have h1 : uMat ((1 : X.B.I.Ginf) v) = 1 := rfl
  rw [h1]
  exact psiR_one (X.B.I.ε v) X.B.g (hfe_X X v) (hfz_X X u v)

theorem psiInfU_mul (u : D.what₂.Word) {s t : X.B.I.Ginf} (hs : s ∈ X.SinfU u) (ht : t ∈ X.SinfU u) :
    X.psiInfU u (s * t) = X.psiInfU u s * X.psiInfU u t := by
  unfold HidaSetting.psiInfU psiInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  have h1 : uMat ((s * t) v) = uMat (s v) * uMat (t v) := rfl
  rw [h1]
  exact psiR_mul (X.B.I.ε v) X.B.g (hfe_X X v) (hfz_X X u v) (hs v) (ht v)

theorem tauU_one (u : D.what₂.Word) : Formalism.L2.SG.RealObj.EnergyInst.tauU X u 1 = 1 := by
  unfold Formalism.L2.SG.RealObj.EnergyInst.tauU
  rw [psiInfU_one, (X.piU_rep u).1, one_smul]

theorem tauU_mul (u : D.what₂.Word) : ∀ s ∈ X.SinfU u, ∀ t ∈ X.SinfU u,
    Formalism.L2.SG.RealObj.EnergyInst.tauU X u (s * t) =
      Formalism.L2.SG.RealObj.EnergyInst.tauU X u s * Formalism.L2.SG.RealObj.EnergyInst.tauU X u t := by
  intro s hs t ht
  unfold Formalism.L2.SG.RealObj.EnergyInst.tauU
  rw [psiInfU_mul X u hs ht, (X.piU_rep u).2.1 s hs t ht, smul_mul_smul_comm]

end Glob

end Formalism.L2.S.Pv.TauS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Hu (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Set X.B.I.Ginf :=
  Hset X.B.I (Set.range (fun a => X.eR a) ∪ Set.range (fun a => X.fR a) ∪ {X.zR u})

def SDecomp : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsClosed (X.SinfU u) ∧ (1 : X.B.I.Ginf) ∈ X.SinfU u ∧
    (∀ a ∈ X.SinfU u, ∀ b ∈ X.SinfU u, a * b ∈ X.SinfU u) ∧ (∀ a ∈ X.SinfU u, a⁻¹ ∈ X.SinfU u) ∧
    (1 : X.B.I.Ginf) ∈ X.NinfU u ∧ (∀ a ∈ X.NinfU u, ∀ b ∈ X.NinfU u, a * b ∈ X.NinfU u) ∧
    (∀ a ∈ X.NinfU u, a⁻¹ ∈ X.NinfU u) ∧
    IsCompact (Hu X u) ∧ (1 : X.B.I.Ginf) ∈ Hu X u ∧ (∀ a ∈ Hu X u, ∀ b ∈ Hu X u, a * b ∈ Hu X u) ∧
    (∀ a ∈ Hu X u, a⁻¹ ∈ Hu X u) ∧
    (∀ h ∈ Hu X u, ∀ n ∈ X.NinfU u, h * n * h⁻¹ ∈ X.NinfU u) ∧
    (∀ n ∈ X.NinfU u, ∀ h ∈ Hu X u, n * h ∈ X.SinfU u) ∧
    (∀ s ∈ X.SinfU u, ∃ n ∈ X.NinfU u, ∃ h ∈ Hu X u, s = n * h)

def MeasN : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    (∀ K : Set X.B.I.Ginf, IsCompact K → X.muN u K < ⊤) ∧
    (∀ n ∈ X.NinfU u, (X.muN u).map (fun x => x * n) = X.muN u) ∧
    (X.muN u).map (fun x => x⁻¹) = X.muN u ∧
    ∀ h ∈ Hu X u, (X.muN u).map (fun x => h * x * h⁻¹) = X.muN u

def MeasH : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word),
    IsFiniteMeasure (X.muH u) ∧ (∀ h ∈ Hu X u, (X.muH u).map (fun x => x * h) = X.muH u) ∧
    (X.muH u).map (fun x => x⁻¹) = X.muH u

def NuQSFinite : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word), SFinite (X.nuQ u)

end Formalism.L2.S.Pv.HaarSubS
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SchurTensInst
section
noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.SchurTens

open Formalism.L2.SG.Pf.EnergyAbs Formalism.MainNotions.S

section Loc

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem unitRep_of_URepOn {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : IsURepOn (UJset ε) σ) :
    IsUnitRep (fun g : Formalism.REAL.UJ ε => σ (uMat g)) := by
  obtain ⟨⟨h1, hmul⟩, hnorm, hcont⟩ := hU
  have hmem : ∀ g : Formalism.REAL.UJ ε, uMat g ∈ UJset ε := fun g => g.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · show σ (uMat 1) = 1
    simpa [uMat] using h1
  · intro x y
    show σ (uMat (x * y)) = σ (uMat x) * σ (uMat y)
    rw [show uMat (x * y) = uMat x * uMat y from rfl, hmul _ (hmem x) _ (hmem y)]
    rfl
  · intro x a b
    let Li : H →ₗᵢ[ℂ] H := { toLinearMap := (σ (uMat x)).toLinearMap, norm_map' := hnorm _ (hmem x) }
    exact Li.inner_map_map a b
  · intro a
    exact (hcont a).comp_continuous (Units.continuous_val.comp continuous_subtype_val) hmem

theorem isSchur_of_isFdeg {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ}
    (h : IsFdeg (Formalism.REAL.muG ε) σ d) : IsSchur (Formalism.REAL.muG ε) (fun g : Formalism.REAL.UJ ε => σ (uMat g)) d :=
  ⟨h.1, fun a b a' b' => h.2 a b a' b'⟩

theorem fdegOf_eq' {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d : ℝ} (h : IsFdeg (Formalism.REAL.muG ε) σ d)
    {w : H} (hw : w ≠ 0) : fdegOf (Formalism.REAL.muG ε) σ w = d := by
  obtain ⟨hd, hI⟩ := h
  have h2 := (hI w w w w).2
  have hc : ∀ g : Formalism.REAL.UJ ε, coefOn σ w w g * star (coefOn σ w w g) = ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def]
    rw [RCLike.mul_conj (K := ℂ)]
    norm_cast
  have hin : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp only [hc] at h2
  rw [integral_complex_ofReal, hin] at h2
  have hr : (∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε)) = ‖w‖ ^ 4 / d := by
    have h3 : ((∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) : ℝ) : ℂ) = ((‖w‖ ^ 4 / d : ℝ) : ℂ) := by
      rw [h2]
      push_cast
      ring
    exact_mod_cast h3
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hd' : d ≠ 0 := hd.ne'
  unfold fdegOf
  rw [hr]
  field_simp

end Loc

theorem stepSchurG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSchurG := by
  intro D X
  have hU : ∀ v, IsUnitRep (fun g : Formalism.REAL.UJ (X.B.I.ε v) => X.B.σ v (uMat g)) := fun v =>
    unitRep_of_URepOn (X.ds v).2.2.1
  have hw : ∀ v, ‖X.B.w v‖ = 1 := fun v => (X.low v).1
  have hF : ∀ v, IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.dv v) := by
    intro v
    obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS _ (X.B.σ v) (X.ds v)
    have hw0 : X.B.w v ≠ 0 := by
      intro h0
      have := hw v
      rw [h0, norm_zero] at this
      exact zero_ne_one this
    have he : X.dv v = d := fdegOf_eq' hd hw0
    rw [he]
    exact hd
  have hT : IsTensAbs (fun v (g : Formalism.REAL.UJ (X.B.I.ε v)) => X.B.σ v (uMat g)) X.B.σs X.B.tens :=
    X.B.tens_spec
  refine ⟨isUnitRep_tens hU hT, ?_, ?_, ?_⟩
  · exact isSchur_tens (fun v => Formalism.REAL.muG (X.B.I.ε v)) X.dv hU (fun v => isSchur_of_isFdeg (hF v)) hT
  · have h1 := X.B.tens_spec.1 X.B.w X.B.w
    have h2 : ∏ v, ⟪X.B.w v, X.B.w v⟫_ℂ = 1 := by
      refine Finset.prod_eq_one fun v _ => ?_
      rw [inner_self_eq_norm_sq_to_K, hw v]
      simp
    rw [h2] at h1
    have h3 : ‖X.B.tens X.B.w‖ ^ 2 = 1 := by
      have := congrArg RCLike.re h1
      rw [inner_self_eq_norm_sq (𝕜 := ℂ)] at this
      simpa using this
    have h4 := norm_nonneg (X.B.tens X.B.w)
    nlinarith [h3, h4]
  · intro y
    simp only [Formalism.L2.SG.ProjRows.phInf, Formalism.L2.SG.ProjRows.mInf, Formalism.L2.SG.RealObj.degX]
    rw [X.B.tens_spec.2.1 y, X.B.tens_spec.1]
    rfl

end Formalism.L2.S.Pv.SchurTens
end
end

