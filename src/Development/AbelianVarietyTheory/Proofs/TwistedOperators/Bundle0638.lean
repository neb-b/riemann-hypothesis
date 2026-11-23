module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualModulusShiftHalfMemCompletedModulusHom
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselStepPiecesBMutualAnnihilators
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.PcBFDual

variable {D : D7}

section Proj

variable {T : HSp D} {Λ : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} (M : Mx D T.rank T.rank)

theorem mulVec_latV (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) {y : Fin T.rank → AE D} (hy : y ∈ latV T Λ P) : M *ᵥ y ∈ latV T Λ P := by
  refine (GlobalTheory.FinPlLoc.part_lat P T Λ _ hΛ).2 ⟨GlobalTheory.FinPl.ExtZeroAt.mulVec_idAt _ (GlobalTheory.FinPlLoc.latV_idAt hy), fun v hv e he => ?_⟩
  rw [← Matrix.mulVec_smul]
  exact hM v hv _ (GlobalTheory.FinPlLoc.smul_latV v he hy)

theorem smul_mem_latA_idLat (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {a s : D.host.E} (ha : a ∈ D.host.AA) (hs : s ∈ I)
    {w : Fin T.rank → AE D} (hw : w ∈ latV T Λ P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * s)) • w ∈ latA T (idLat I Λ) P := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, s • x, Submodule.subset_span ⟨s, hs, x, hx, rfl⟩, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz


set_option maxHeartbeats 1000000 in
theorem mulVec_latA_idLat (hM : ∀ v, P v → ∀ y ∈ latV T Λ (· = v), M *ᵥ y ∈ latV T Λ (· = v))
    (hΛ : Submodule.IsLattice D.host.E Λ) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) {z : Fin T.rank → AE D}
    (hz : z ∈ latA T (idLat I Λ) P) : M *ᵥ z ∈ latA T (idLat I Λ) P := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hz
    have key : ∀ x ∈ Submodule.span (𝓞 D.host.E) {z | ∃ s ∈ I, ∃ y ∈ Λ, z = s • y}, ∀ c : 𝓞 D.host.E,
        M *ᵥ (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) ∈ latA T (idLat I Λ) P := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨s, hs, y, hy, rfl⟩ := hx
        intro c
        have hyv : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) ∈ latV T Λ P :=
          AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, y, hy, rfl⟩
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • s • y) i)) =
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * (c • s))) • (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * y i)) := by
          funext i
          rw [← smul_assoc]
          simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_assoc]
        rw [e, Matrix.mulVec_smul]
        exact smul_mem_latA_idLat I ha (Submodule.smul_mem _ c hs) (mulVec_latV M hM hΛ hyv)
      | zero =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (0 : Fin T.rank → D.host.E)) i)) = 0 := by
          funext i; simp only [smul_zero, Pi.zero_apply, mul_zero, TensorProduct.tmul_zero]
        rw [e, Matrix.mulVec_zero]; exact zero_mem _
      | add x x' _ _ h h' =>
        intro c
        have e : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • (x + x')) i)) =
            (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x) i)) +
              (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * (c • x') i)) := by
          funext i; simp only [smul_add, Pi.add_apply, mul_add, TensorProduct.tmul_add]
        rw [e, Matrix.mulVec_add]; exact add_mem (h c) (h' c)
      | smul c' x _ h =>
        intro c
        rw [smul_smul]
        exact h (c * c')
    have := key x hx 1
    simpa only [one_smul] using this
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

end Proj

section Split

theorem projY_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jY ⬝ d.pY) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jY ⬝ d.pY) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).2.1 i

theorem projX_mem {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : GlobalTheory.FinPl.Pl D}
    (h : MonoAt d L L₀ v) {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = v)) : (d.jX ⬝ d.pX) *ᵥ y ∈ latV S L (· = v) := by
  have e : (d.jX ⬝ d.pX) *ᵥ y = ∑ i, GlobalTheory.FinPl.colMul d.jX i ((d.pX *ᵥ y) i) := by
    rw [← Matrix.mulVec_mulVec]
    funext k
    rw [Finset.sum_apply]
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.FinPl.colMul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e]
  exact sum_mem fun i _ => ((h y).1 hy).1 i

theorem extend_mem_lattice_iff {V V₀ W : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {LV : Lat V} {LV₀ : Lat V₀} {LW : Lat W}
    (hV : IsSelfDualC V LV) (hV₀ : IsSelfDualC V₀ LV₀) (hW : IsSelfDualC W LW) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hm : ∀ v, P v → MonoAt d LV LV₀ v) (w : WO V₀ W) :
    d.ext0 W w ∈ latO V W (LV : Set _) (LW : Set _) P ↔ w ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) P := by
  constructor
  · intro hw
    have hx := GlobalTheory.FinPl.LatMem.latO_mxAt hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V₀ W LV₀ LW hV₀ hW P _).2 ⟨?_, fun y hy => ?_⟩
    · have := GlobalTheory.AscFinWit.mxAt_mul' hx d.j0
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at this
    · have h2 := GlobalTheory.FinPl.LatMem.latO_maps hV hw (GlobalTheory.FinPl.ExtZeroAt.wittCoreInclusion_mem_latticeCompletionAtPlace d hV.1 hm hy)
      rwa [HypDec.matrixExtendByZero_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc, d.p0_j0, Matrix.mul_one] at h2
  · intro hw
    refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D V W LV LW hV hW P _).2
      ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.FinPl.LatMem.latO_mxAt hw) _, fun y hy => ?_⟩
    rw [HypDec.matrixExtendByZero_apply, ← Matrix.mulVec_mulVec]
    exact GlobalTheory.FinPl.LatMem.latO_maps hV₀ hw (GlobalTheory.FinPl.ExtZeroAt.wittProjectionZero_mem_latticeCompletion_of_splits d hV₀.1 hm hy)

theorem left_mem {S W : HSp D} {LS : Lat S} {Λ : Lat W} {I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hS : IsSelfDualC S LS) (hW : IsSelfDualC W (idLat I Λ)) (hΛ : Submodule.IsLattice D.host.E Λ) (M : Mx D W.rank W.rank)
    (hM : ∀ v, P v → ∀ y ∈ latV W Λ (· = v), M *ᵥ y ∈ latV W Λ (· = v)) {u : WO S W}
    (hu : u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P) : M ⬝ u ∈ latO S W (LS : Set _) (idLat I Λ : Set _) P := by
  refine (GlobalTheory.FinPl.LatMem.mem_latO_iff D S W LS _ hS hW P _).2
    ⟨GlobalTheory.AscFinWit.mxAt_mul _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu), fun y hy => ?_⟩
  show (M * u) *ᵥ y ∈ _
  rw [← Matrix.mulVec_mulVec]
  exact mulVec_latA_idLat M hM hΛ I (GlobalTheory.FinPl.LatMem.latO_maps hS hu hy)

end Split

end GlobalTheory.PcBFDual

namespace GlobalTheory.PcBFDual

theorem dualB : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m),
    (∀ ξ, MxAt (fun _ => True) ξ → (ξ ∈ (pcBF W F ρ h).B₁ ↔ ∀ η ∈ (pcBF W F ρ h).B₂,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1)) ∧
    ∀ η, MxAt (fun _ => True) η → (η ∈ (pcBF W F ρ h).B₂ ↔ ∀ ξ ∈ (pcBF W F ρ h).B₁,
      W.ψ (symplO (F.V₀ ρ) _ ((F.dJ ρ h).incX _ ξ) ((F.dJ ρ h).incY _ η)) = 1) := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h
  have I := _root_.GlobalTheory.AscFin.GridLat.lattices_grid D hq T L μ0 hL sc G W M hM F hF
  have sd : ∀ X : Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → IsSelfDualC (G.V X) (G.Λ X) :=
    fun X h1 h2 => (G.isV h1 h2).sd
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    sd _ ⟨h, Nat.zero_le _⟩ (fun j e => by cases e)
  have hΛ : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    sd _ ⟨by omega, Nat.zero_le _⟩ (fun j e => by cases e)
  have hV₀ : IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := (I.2.1 ρ h).1
  have hW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (I.1 (2 * ρ + 1) (by omega)).2.2.2
  have hmV : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((I.2.1 ρ h).2.1 v).1
  have hmW : ∀ v, MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v :=
    fun v => ((I.2.1 ρ h).2.1 v).2
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hB : ∀ w, (F.dB ρ h).ext0 _ w ∈ latBig G (2 * ρ + 1) ↔
      w ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) fun _ => True :=
    fun w => extend_mem_lattice_iff (F.dB ρ h) hV hV₀ hW (fun v _ => hmV v) w
  have tY : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incY _ ((F.dJ ρ h).pY ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incY_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projY_mem _ (hmW v) hy) hu
  have tX : ∀ u ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
      (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True),
      (F.dJ ρ h).incX _ ((F.dJ ρ h).pX ⬝ u) ∈ latO (F.V₀ ρ) (G.V (.grid (2 * ρ + 1) 0)) (lat0 F ρ h : Set _)
        (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0)) : Set _) (fun _ => True) := fun u hu => by
    rw [HypDec.incX_apply, ← Matrix.mul_assoc]
    exact left_mem hV₀ hW hΛ.1 _ (fun v _ y hy => projX_mem _ (hmW v) hy) hu
  refine ⟨fun ξ hξ => ?_, fun η hη => ?_⟩
  · refine (hB ((F.dJ ρ h).incX _ ξ)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jX hξ)).trans ?_
    refine ⟨fun H η hη => H _ ((hB ((F.dJ ρ h).incY _ η)).1 hη), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incX (F.dJ ρ h) _ ξ u)).trans (H _ ((hB ((F.dJ ρ h).incY _ _)).2 (tY u hu)))
  · refine (hB ((F.dJ ρ h).incY _ η)).trans ?_
    refine (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hV₀ hW _ _ (GlobalTheory.AscFinWit.mxAt_mul (F.dJ ρ h).jY hη)).trans ?_
    refine ⟨fun H ξ hξ => (GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ ξ)).1 hξ)), fun H u hu => ?_⟩
    exact (congrArg W.ψ (GlobalTheory.AscFinWit.symplO_incY (F.dJ ρ h) _ η u)).trans
      ((GlobalTheory.AscFinWit.psi_swap _ _).1 (H _ ((hB ((F.dJ ρ h).incX _ _)).2 (tX u hu))))

end GlobalTheory.PcBFDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BidualityDepthLatticePieceBesselStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.BidualLattice

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  unfold latO
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]
  · rw [AddSubgroup.closure_le]
    rintro w ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _)]
    refine neg_mem (AddSubgroup.subset_closure ⟨α, hα, hP, a, ha, s, hs, t, ht, ?_⟩)
    funext i j
    simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem extY_jY_mem {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (hm : ∀ v, MonoAt d LS L₀ v) {u : WO S T}
    (hu : u ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True) :
    d.extY T (u * d.jY) ∈ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ _ _ hS hT] at hu ⊢
  refine ⟨GlobalTheory.AscFinWit.mxAt_mul' (GlobalTheory.AscFinWit.mxAt_mul' hu.1 _) _, fun y hy => ?_⟩
  have e : (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from d.extY T (u * d.jY)) *ᵥ y =
      (show Matrix (Fin T.rank) (Fin S.rank) (AE D) from u) *ᵥ (d.jY *ᵥ (d.pY *ᵥ y)) := by
    simp only [HypDec.extY_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [e]
  refine hu.2 _ ?_
  rw [GlobalTheory.FinPlLoc.part_lat _ _ _ _ hS.1] at hy ⊢
  refine ⟨fun i => ?_, fun v _ c hc => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _
      (Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hy.1 l))
  · have hs := ((hm v) (c • y)).1 (hy.2 v trivial c hc)
    have e1 : c • (d.jY *ᵥ (d.pY *ᵥ y)) = ∑ i, GlobalTheory.FinPl.colMul d.jY i ((d.pY *ᵥ (c • y)) i) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [e1]
    exact sum_mem fun i _ => hs.2.1 i

theorem dual_extX {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {LS : Lat S} {L₀ : Lat S₀} {LT : Lat T}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT)
    (hm : ∀ v, MonoAt d LS L₀ v) {a : Mx D T.rank ρ} (ha : MxAt (fun _ => True) a) :
    d.extX T a ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) ↔
      ∀ a', d.extY T a' ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True) →
        ψ (symplO S T (d.extX T a) (d.extY T a')) = 1 := by
  refine (GlobalTheory.SelfDualAt.latO_ann_at D ψ hψ S T LS LT hS hT _ _ (GlobalTheory.AscFinWit.mxAt_mul' ha d.pX)).trans ?_
  exact ⟨fun h _ ha' => h _ ha', fun h u hu =>
    (congrArg ψ (GlobalTheory.AscFinWit.symplO_extX d T a u)).trans (h _ (extY_jY_mem d hS hT hm hu))⟩

theorem mxAt_of_extY {S S₀ T : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {a' : Mx D T.rank ρ}
    (h : MxAt (fun _ => True) (d.extY T a')) : MxAt (fun _ => True) a' := by
  simpa only [HypDec.extY_apply, Matrix.mul_assoc, d.pY_jY, Matrix.mul_one] using GlobalTheory.AscFinWit.mxAt_mul' h d.jY

end GlobalTheory.AscFin.BidualLattice

namespace GlobalTheory.AscFin.BidualLattice

theorem bidual_main (hin : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latRow G i, e • u ∈ latBig G i) (hout : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → OffQ D → ∀ (G : GridData L sc) (i : ℕ), i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 → ∀ u ∈ latBig G i, e • u ∈ hatMx (G.modul • homLat (G.Λ (.grid (i + 1) 0)) (G.Λ (.grid i 0)))) : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ := by
  have hI := _root_.GlobalTheory.AscFin.GridLat.lattices_grid
  unfold OnStd at hI ⊢
  delta All at hI ⊢
  intro D hD T L μ0 hL sc G W M hM F hF ρ h a ha H
  have hJ := hI D hD T L μ0 hL sc G W M hM F hF
  have hi : 2 * ρ + 1 < D.R.m := by omega
  have hψ : IsStdChar D W.ψ (-1) := W.ψ_std
  have hSV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by cases hj)).sd
  have hSW : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 1) 0)) :=
    (GlobalTheory.CosetRow.selfDual_chi hL G (2 * ρ + 1) hi).2
  have hbig : IsSelfDualC (G.V (.grid (2 * ρ + 1) 0)) (idLat (shiftId G) (G.Λ (.grid (2 * ρ + 1) 0))) :=
    (hJ.1 (2 * ρ + 1) hi).2.2.2
  have hmono : ∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := fun v => ((hJ.2.1 ρ h).2.1 v).1
  have hrowO : ∀ u ∈ latRow G (2 * ρ + 1), u ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := fun u hu => by
    have h0 := hu.1
    rwa [BidualLattice.latO_negSp] at h0
  have hA2 : ∀ a', MxAt (fun _ => True) a' → (∀ b, (F.dB ρ h).extX _ b ∈ latRow G (2 * ρ + 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ b) ((F.dB ρ h).extY _ a')) = 1) →
      W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1 :=
    fun a' h1 h2 => H a' (AddSubgroup.subset_closure ⟨h1, h2⟩)
  have hO : (F.dB ρ h).extX _ a ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
      (G.Λ (.grid (2 * ρ + 2) 0) : Set _) (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) := by
    refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hSW hmono ha).2 fun a' ha' => ?_
    refine hA2 a' (BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')) fun b hb => ?_
    have hb' := hrowO _ hb
    exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hSW _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
  refine ⟨?_, fun e he => ?_⟩
  · exact (BidualLattice.latO_negSp (G.V (.grid (2 * ρ + 2) 0)) _ _ _ _).ge hO
  · have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
    have hsx : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extX _ (e • x) = e • (F.dB ρ h).extX _ x :=
      fun x => by simp only [HypDec.extX_apply, Matrix.smul_mul]
    have hsy : ∀ x : Mx D (G.V (.grid (2 * ρ + 1) 0)).rank ρ, (F.dB ρ h).extY _ (cA D e • x) =
        cA D e • (F.dB ρ h).extY _ x := fun x => by simp only [HypDec.extY_apply, Matrix.smul_mul]
    have hea : MxAt (fun _ => True) (e • a) := fun i j => Ideal.mul_mem_left _ _ (ha i j)
    have hB : (F.dB ρ h).extX _ (e • a) ∈ latBig G (2 * ρ + 1) := by
      refine (BidualLattice.dual_extX (F.dB ρ h) hψ hSV hbig hmono hea).2 fun a' ha' => ?_
      rw [hsx, GlobalTheory.SplitScalar.symplO_smul, ← hsy]
      have ha'f := BidualLattice.mxAt_of_extY _ (GlobalTheory.FinPl.LatMem.latO_mxAt ha')
      refine hA2 _ (fun i j => Ideal.mul_mem_left _ _ (ha'f i j)) fun b hb => ?_
      rw [hsy, ← GlobalTheory.SplitScalar.symplO_smul]
      have hb' := hin hL hD G (2 * ρ + 1) hi e he _ hb
      exact (GlobalTheory.SelfDualAt.latO_ann_at D W.ψ hψ _ _ _ _ hSV hbig _ _ (GlobalTheory.FinPl.LatMem.latO_mxAt hb')).1 hb' _ ha'
    have h2 := hout hL hD G (2 * ρ + 1) hi e he _ hB
    rwa [hsx, smul_smul, hee] at h2

theorem bidual_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ a, MxAt (fun _ => True) a → (∀ a' ∈ (pcBF W F ρ h).A₂, W.ψ (symplO _ _ ((F.dB ρ h).extX _ a) ((F.dB ρ h).extY _ a')) = 1) → a ∈ (pcBF W F ρ h).A₁ :=
  bidual_main _root_.GlobalTheory.DepHalf.smul_mem_latBig _root_.GlobalTheory.HalfOut.smul_mem_hatMx_of_mem_latBig

end GlobalTheory.AscFin.BidualLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BplusEqCoef
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem bplus_eq_coef {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (φ : Fn G (.top 0)) (F : Fn G (.grid D.R.m 0)) :
    Bplus W M φ F = ∫ h in M.fd (.top 0), φ h *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F (embTop G h) ∂M.ν (.top 0) := by
  simp only [Bplus, besInt, GlobalTheory.Mem.TrueRecord.coef, ← integral_const_mul, mul_assoc]

theorem nu_top_eq {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {M M' : Vol G}
    (hM : M.IsRow) (hM' : M'.IsRow) : M.ν (.top 0) = M'.ν (.top 0) := by
  obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have h1 := hM.top
  have h2 := hM'.top
  unfold Vol.IsAt at h1 h2
  have hz : Node.neg D.R.m (Node.top 0) = 0 := rfl
  rw [if_pos hz] at h1 h2
  haveI := h1.1.1
  haveI := h2.1.1
  have e := Measure.isMulLeftInvariant_eq_smul (M.ν (.top 0)) (M'.ν (.top 0))
  have a1 := GlobalTheory.Mass.Levels.measure_comap_finE h1.1
  have a2 := GlobalTheory.Mass.Levels.measure_comap_finE h2.1
  have hc : Measure.haarScalarFactor (M.ν (.top 0)) (M'.ν (.top 0)) = 1 := by
    rw [e, Measure.smul_apply, a2] at a1
    simpa using a1
  rw [e, hc, one_smul]

theorem bplus_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (W : G.Weil) (M M' : Vol G),
    M.IsRow → M'.IsRow → ∀ φ F, GlobalTheory.Unf.IsContAut _ φ → GlobalTheory.Unf.IsContAut _ F → Bplus W M φ F = Bplus W M' φ F := by
  intro D T L sc G W M M' hM hM' φ F hφ hF
  have hψ := W.ψ_std
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hF' : ∀ γ ∈ GQ (G.V (.grid D.R.m 0)), ∀ g, F (γ * g) = F g := hF.1
  have hN := hM.unip
  have hN' := hM'.unip
  rw [bplus_eq_coef, bplus_eq_coef]
  have ec : ∀ g, GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M.νN M.fdN F g =
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F g := fun g =>
    GlobalTheory.Mem.TrueRecord.coef_eq hψ hι G.besTop hN.1 hN.2.1 hN.2.2 hN'.1 hN'.2.1 hN'.2.2 hF' g
  simp only [ec]
  obtain ⟨i1, i2, i3, i4, i5, -, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hf1 := (hM.top.haar_fund).2
  have hf2 := hM'.top.haar_fund
  rw [nu_top_eq hM hM'] at hf1 ⊢
  haveI := hf2.1
  set d := G.rowDec 0 (by have := D.R.two_le_m; omega)
  have e0 : ∀ h, embTop G h = stabilizerEmbedding d h := fun h => rfl
  have e1 : stabilizerEmbedding d 1 = 1 := by
    have := GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul d 1 1
    rw [one_mul] at this
    exact left_eq_mul.mp this
  refine hf1.setIntegral_eq hf2.2 fun γ h => ?_
  have hγ : (γ : GA D (G.V (.top 0))) ∈ GQ (G.V (.top 0)) := γ.2
  have hinv : stabilizerEmbedding d (γ : GA D (G.V (.top 0)))⁻¹ = (stabilizerEmbedding d γ)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul, inv_mul_cancel, e1]
  have r1 : EmbRel _ _ d.ι (stabilizerEmbedding d γ) γ := (embRel_iff d _ _).2 rfl
  have r2 : EmbRel _ _ d.ι (stabilizerEmbedding d γ)⁻¹ (γ : GA D (G.V (.top 0)))⁻¹ := hinv ▸ (embRel_iff d _ _).2 rfl
  change φ ((γ : GA D (G.V (.top 0))) * h) *
      GlobalTheory.Mem.TrueRecord.coef W.ψ G.besTop M'.νN M'.fdN F (embTop G ((γ : GA D (G.V (.top 0))) * h)) = _
  rw [hφ.1 _ hγ, e0, e0, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul,
    GlobalTheory.Mem.TrueRecord.coef_left hψ hι G.besTop hN'.1 hN'.2.1 hN'.2.2 hF' (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational d _ hγ) r1 r2]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefProd
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowWt

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def colCoef (ch : Choice R) (t : T) (β : CosFam ch.G t) (j : ℕ) : ℚ :=
  ∏ w : locPl ch.G t, if h : j < D.R.m then
    invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) else 1

theorem coef_prod (ch : Choice R) (t : T) (Φ : ch.G.Datum) (β : CosFam ch.G t) :
    ∏ w, ((ch.S.term t Φ β w).coef : ℂ) = ((idx D).map fun j => (colCoef ch t β j : ℂ)).prod := by
  have hw : ∀ w, (ch.S.term t Φ β w).coef = ∏ i : Fin (D.R.m - 2), (if h : 1 + (i : ℕ) < D.R.m then
      invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := 1 + (i : ℕ)) h) else 1) := by
    intro w
    have hj : ∀ (j j' : ℕ) (_ : j = j') (h : j < D.R.m) (h' : j' < D.R.m),
        invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j) h) =
          invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w)) (j := j') h') := by
      rintro j _ rfl h h'
      rfl
    show ∏ i : Fin (D.R.m - 2), invVol (conjLevel one_le_sLen (givenLevel ch.G t w) ((repsAt ch.G t w).elt (β w))
      (j := (i : ℕ) + 1) (show (i : ℕ) + 1 < D.R.m by have := i.isLt; omega)) = _
    exact Finset.prod_congr rfl fun i _ => by
      rw [dite_eq_left (show 1 + (i : ℕ) < D.R.m by have := i.isLt; omega)]
      exact hj _ _ (Nat.add_comm _ _) _ _
  have key : ∏ w, (ch.S.term t Φ β w).coef = ((idx D).map fun j => colCoef ch t β j).prod := by
    simp only [hw]
    rw [Finset.prod_comm]
    simp only [idx, List.range'_eq_map_range, List.map_map]
    rw [← List.map_coe_finRange_eq_range, List.map_map, ← List.ofFn_eq_map, List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => rfl
  have := congrArg (Rat.cast : ℚ → ℂ) key
  rw [Rat.cast_prod, Rat.cast_list_prod, List.map_map] at this
  exact this

end GlobalTheory.RowWt
end
end

