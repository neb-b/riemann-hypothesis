module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0448
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0455

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowLatticeSelfDualComponentsRescaledWordFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

def basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) :
    Module.Basis (Fin (D.sp.Y 0).rank) D.host.E (VS D).V :=
  X.bas.reindex (finCongr (rank_eq X h)).symm

theorem cY_eq_basY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z = (basY X h).equivFun z := by
  funext k
  simp [GlobalTheory.Core.SBesEx.cY, HidaSetting.crd, crdOf, basY, Module.Basis.repr_reindex]

theorem mem_hermitianCoordinateLattice_iff (S : HSp D) (y : Fin S.rank → D.host.E) :
    y ∈ Formalism.L2.Herm.crdLat S S.L0 ↔ S.frame.equivFun.symm y ∈ S.L0 := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [Formalism.L2.Herm.crd] using hw
  · intro hy
    exact ⟨_, hy, S.frame.equivFun.apply_symm_apply y⟩

theorem mem_rowLatticeYZeroFrame_iff_basis_sum (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hId : ∀ x : I.E, HEq (ιE x) x) (bas : Module.Basis (Fin I.n) D.host.E (VS D).V)
    (hL : ∀ x : Fin I.n → I.E, x ∈ I.L ↔ (∑ i, ιE (x i) • bas i) ∈ (VS D).L0) (hn : (D.sp.Y 0).rank = I.n)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (∑ k, y k • bas (Fin.cast hn k)) ∈ (VS D).L0 := by
  subst hI
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hId x)
  have e1 := hL y
  have e2 : (∑ i, ιE (y i) • bas i) = ∑ k, y k • bas (Fin.cast hn k) :=
    Finset.sum_congr rfl fun i _ => congrArg (· • bas i) (hι (y i))
  refine Iff.trans ?_ (e1.trans (Eq.to_iff (congrArg (· ∈ (VS D).L0) e2)))
  rw [mem_hermitianCoordinateLattice_iff]
  show _ ↔ y ∈ Formalism.L2.SG.InstExistsPf.Lv D
  rw [Formalism.L2.SG.InstExistsPf.mem_Lv, Module.Basis.equivFun_symm_apply]

theorem mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X)
    (y : Fin (D.sp.Y 0).rank → D.host.E) :
    y ∈ latS D ↔ (basY X h).equivFun.symm y ∈ (VS D).L0 := by
  rw [mem_rowLatticeYZeroFrame_iff_basis_sum X.B.I h X.ιE hId X.bas X.L_eq (rank_eq X h), Module.Basis.equivFun_symm_apply]
  simp [basY]

theorem cY_mem_latS (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (hId : IdE X) (z : (VS D).V) :
    GlobalTheory.Core.SBesEx.cY X h z ∈ latS D ↔ z ∈ (VS D).L0 := by
  rw [mem_latS X h hId, cY_eq_basY, LinearEquiv.symm_apply_apply]

theorem hT_swap (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := by
  have := (VS D).herm.eq x y
  rw [← this]
  rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem hT_fY_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.fY i) Y ∈ aaD D i := by
  have key : (VS D).L0 ≤ (aaD D i : Submodule (𝓞 D.host.E) D.host.E).comap
      (((VS D).hT (X.fY i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.eX a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, hT_swap, X.ef]
      by_cases hai : a = i
      · subst hai; simpa using hx
      · simp [hai]
    · intro x hx
      show (VS D).hT (X.fY i) x ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).2]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.fY i) (x • X.fY a) ∈ (aaD D i : Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ff, smul_zero]; exact zero_mem _
  exact key hY

theorem hT_eX_mem (X : HidaSetting D) (i : Fin D.R.rS) {Y : (VS D).V} (hY : Y ∈ (VS D).L0) :
    (VS D).hT (X.eX i) Y ∈ (aaD D i)⁻¹ := by
  have key : (VS D).L0 ≤ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
      Submodule (𝓞 D.host.E) D.host.E).comap (((VS D).hT (X.eX i)).restrictScalars (𝓞 D.host.E)) := by
    rw [X.Lam_split]
    refine sup_le (sup_le ?_ ?_) ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.eX a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, X.ee, smul_zero]; exact zero_mem _
    · intro x hx
      show (VS D).hT (X.eX i) x ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [((X.Lb_perp x hx) i).1]; exact zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨a, x, hx, rfl⟩
      show (VS D).hT (X.eX i) (x • X.fY a) ∈ (((aaD D i)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E)
      rw [map_smul, smul_eq_mul, X.ef]
      by_cases hai : i = a
      · subst hai; simpa using hx
      · simp [hai]
  exact key hY

theorem smul_eX_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.eX i ∈ (VS D).L0 ↔ c ∈ aaD D i := by
  constructor
  · intro hc
    have := hT_fY_mem X i hc
    rwa [map_smul, smul_eq_mul, hT_swap, X.ef, if_pos rfl, star_one, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, c, hc, rfl⟩))

theorem smul_fY_mem_iff (X : HidaSetting D) (i : Fin D.R.rS) (c : D.host.E) :
    c • X.fY i ∈ (VS D).L0 ↔ c ∈ (aaD D i)⁻¹ := by
  constructor
  · intro hc
    have := hT_eX_mem X i hc
    rwa [map_smul, smul_eq_mul, X.ef, if_pos rfl, mul_one] at this
  · intro hc
    rw [X.Lam_split]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, c, hc, rfl⟩)

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

variable {D : D7}

theorem star_smul_dotProduct {n : ℕ} (c : D.host.E) (v w : Fin n → D.host.E) :
    star (c • v) ⬝ᵥ w = star c * (star v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum, mul_assoc]

theorem qX_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qX *ᵥ y) i = star (fun r => d.e' r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qX, ← Matrix.mulVec_mulVec]; rfl

theorem qY_mulVec_apply {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (y : Fin S.rank → D.host.E) (i : Fin ρ) :
    (d.qY *ᵥ y) i = star (fun r => d.e r i) ⬝ᵥ (S.gram *ᵥ y) := by
  rw [HypDec.qY, ← Matrix.mulVec_mulVec]; rfl

end GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch

theorem latS_rescaled_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (μ lam : D.host.E), GlobalTheory.Core.Mi.IdE X → B.FrameAt μ lam → IsSelfDualC (D.sp.Y 0) (latS D) ∧ (∀ y ∈ latS D, ∀ i, (fun r => (B.d.qX *ᵥ y) i * B.d.e r i) ∈ latS D ∧ (fun r => (B.d.qY *ᵥ y) i * B.d.e' r i) ∈ latS D) ∧ (∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i) ∧ ∀ (i : Fin D.R.rS) (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔ (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
  intro D X h u ψ A B μ lam hId hF
  have hcY_smul : ∀ (c : D.host.E) (z : (VS D).V), c • GlobalTheory.Core.SBesEx.cY X h z = GlobalTheory.Core.SBesEx.cY X h (c • z) := by
    intro c z; rw [cY_eq_basY, cY_eq_basY, map_smul]
  have hcol_e : ∀ i, (fun r => B.d.e r i) = GlobalTheory.Core.SBesEx.scl μ lam i • GlobalTheory.Core.SBesEx.cY X h (X.eX i) := by
    intro i; funext r; rw [hF.e]; rfl
  have hcol_e' : ∀ i, (fun r => B.d.e' r i) =
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ • GlobalTheory.Core.SBesEx.cY X h (X.fY i) := by
    intro i; funext r; rw [hF.e']; rfl
  have colE : ∀ i (t : D.host.E), t • (fun r => B.d.e r i) ∈ latS D ↔ GlobalTheory.Core.SBesEx.scl μ lam i * t ∈ aaD D i := by
    intro i t
    rw [hcol_e, smul_smul, hcY_smul, cY_mem_latS X h hId, smul_eX_mem_iff, mul_comm]
  have colE' : ∀ i (t : D.host.E), t • (fun r => B.d.e' r i) ∈ latS D ↔
      (star (GlobalTheory.Core.SBesEx.scl μ lam i))⁻¹ * t ∈ (aaD D i)⁻¹ := by
    intro i t
    rw [hcol_e', smul_smul, hcY_smul, cY_mem_latS X h hId, smul_fY_mem_iff, mul_comm]
  have hdot := @star_smul_dotProduct D (D.sp.Y 0).rank
  have hqX := qX_mulVec_apply B.d
  have hqY := qY_mulVec_apply B.d
  refine ⟨GlobalTheory.LineSelfDual.isSelfDualC_selfDualLatticeCoordsInFrame D (D.sp.Y 0), ?_, colE, colE'⟩
  intro y hy i
  have hY : (basY X h).equivFun.symm y ∈ (VS D).L0 := (mem_latS X h hId y).1 hy
  have hyY : y = GlobalTheory.Core.SBesEx.cY X h ((basY X h).equivFun.symm y) := by
    rw [cY_eq_basY, LinearEquiv.apply_symm_apply]
  set Y := (basY X h).equivFun.symm y
  constructor
  · have hq : (B.d.qX *ᵥ y) i = (GlobalTheory.Core.SBesEx.scl μ lam i)⁻¹ * (VS D).hT (X.fY i) Y := by
      rw [hqX, hcol_e', hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.fY i), star_inv₀, star_star]
    show (B.d.qX *ᵥ y) i • (fun r => B.d.e r i) ∈ latS D
    rw [colE, hq]
    by_cases hs : GlobalTheory.Core.SBesEx.scl μ lam i = 0
    · rw [hs, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]; exact hT_fY_mem X i hY
  · have hq : (B.d.qY *ᵥ y) i = star (GlobalTheory.Core.SBesEx.scl μ lam i) * (VS D).hT (X.eX i) Y := by
      rw [hqY, hcol_e, hdot, hyY, GlobalTheory.Core.SBesEx.cY_isom D X h hId Y (X.eX i)]
    show (B.d.qY *ᵥ y) i • (fun r => B.d.e' r i) ∈ latS D
    rw [colE', hq]
    by_cases hs : star (GlobalTheory.Core.SBesEx.scl μ lam i) = 0
    · rw [hs, _root_.inv_zero, zero_mul]; exact FractionalIdeal.mem_coe.mp (zero_mem _)
    · rw [← mul_assoc, inv_mul_cancel₀ hs, one_mul]; exact hT_eX_mem X i hY

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapMovedCoreLatticeVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.FinPl.MovedVac

variable {D : D7}

theorem smul_mem_latA {S : HSp D} {L : Lat S} {P : Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀} {v : Pl D}
    (hm : MonoAt d L L₀ v) {z : Fin S₀.rank → AE D} (hz : z ∈ latA S₀ L₀ (· = v)) :
    d.j0 *ᵥ z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S₀.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ latV S₀ L₀ (· = v) := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    refine smul_mem_latA ha ((hm _).2 ⟨fun i => ?_, fun i => ?_, ?_⟩)
    · rw [Matrix.mulVec_mulVec, d.pX_j0, Matrix.zero_mulVec]
      have : colMul d.jX i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.pY_j0, Matrix.zero_mulVec]
      have : colMul d.jY i ((0 : Fin ρ → AE D) i) = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    · rw [Matrix.mulVec_mulVec, d.p0_j0, Matrix.one_mulVec]
      exact hy'm
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem wittExt_wittInc_core_hom_eq {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) (u : WO J.W₀ B.V₀) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) = B.d.j0 * u * J.d.p0 := rfl

theorem wittExt_wittInc_mem_completed_hom_lattice {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {LV : Lat J.W} {LV₀ : Lat J.W₀} {L : Lat B.V}
    {M : Lat B.V₀} {v : Pl D} (hV : IsSelfDualC J.W LV) (hV₀ : IsSelfDualC J.W₀ LV₀) (hL : IsSelfDualC B.V L)
    (hmV : MonoAt J.d LV LV₀ v) (hmW : MonoAt B.d L M v) {u : WO J.W₀ B.V₀}
    (hu : u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v)) :
    J.d.ext0 B.V (B.d.inc0 J.W₀ u) ∈ latO J.W B.V (LV : Set _) (L : Set _) (· = v) := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D J.W B.V LV L hV hL (· = v)]
  have hmx := GlobalTheory.FinPl.LatMem.latO_mxAt hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [wittExt_wittInc_core_hom_eq, Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (B.d.j0 * u * J.d.p0) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact wittCoreInclusion_mem_latticeCompletionAAScaledAtPlace B.d hmW (GlobalTheory.FinPl.LatMem.latO_maps hV₀ hu ((hmV y).1 hy).2.2)

theorem wittExt_wittInc_isHalf {σ : ℕ} (J : JacLev D (σ + 1)) (B : BesLev D σ) {e : AE D} {u : WO J.W₀ B.V₀}
    (hu : IsHalf e u) : IsHalf e (J.d.ext0 B.V (B.d.inc0 J.W₀ u)) := by
  intro i j
  rw [wittExt_wittInc_core_hom_eq]
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  linear_combination (B.d.j0 i k * J.d.p0 l j) * hu k l

end GlobalTheory.FinPl.MovedVac


open GlobalTheory.FinPl.MovedVac in
theorem GlobalTheory.FinPl.movedVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (v : Pl D), AdaptFB ψ J B LV LV₀ LW LW₀ v → UnrAt s v → ∀ f, Vac ψ J.W B.V LV LW (· = v) f → ∀ γ ∈ grpAt B.V₀ (· = v), ∃ M : Lat B.V₀, IsSelfDualC B.V₀ M ∧ Moves B.V₀ γ LW₀ M (· = v) ∧ Vac ψ J.W₀ B.V₀ LV₀ M (· = v) (flatFB s (s.om (1, B.d.emb0 γ) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ v hA _ f hf γ _
  have hflat : IsFlatFB s (· = v) (flatFB s) := (_root_.GlobalTheory.FinPl.flatLaws_all D ψ (· = v)).2 σ J B s
  obtain ⟨M, hM, hMv⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D B.V₀ LW₀ hA.sdW₀).1 γ
  obtain ⟨L', hL', hL'v⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D B.V LW hA.sdW).1 (B.d.emb0 γ)
  have hmono : MonoAt B.d L' M v :=
    (_root_.GlobalTheory.FinPl.GlobImage.glob D B.V LW hA.sdW).2 B.V₀ σ B.d LW₀ M L' γ v hA.monoW (hMv _) (hL'v _)
  have h1 : Moves J.W 1 LV LV (· = v) := fun y _ => by
    rw [show mt J.W 1 = 1 by simp [Formalism.L2.Theta.mt], Matrix.one_mulVec]
  have hf' : Vac ψ J.W B.V LV L' (· = v) (s.om (1, B.d.emb0 γ) f) :=
    ((_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B.V s.χV s.χW s.om s.weil LV LW hA.sdV hA.sdW (· = v)
      (fun w hw => hw ▸ hA.tame) f).2.2 hf 1 (B.d.emb0 γ) LV L' hA.sdV hL' h1 (hL'v _))
  refine ⟨M, hM, hMv _, hflat.Heisenberg₂.theta _ hf'.1, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hu2 : 2 • u ∈ latO J.W₀ B.V₀ (LV₀ : Set _) (M : Set _) (· = v) := nsmul_mem hu 2
    rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu2), map_nsmul, map_nsmul]
    rw [hf'.2.1 _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu)]
  · rw [← hflat.Heisenberg₂.core _ hf'.1 _ (GlobalTheory.FinPl.LatMem.latO_mxAt hu)]
    rw [hf'.2.2 e he _ (wittExt_wittInc_mem_completed_hom_lattice J B hA.sdV hA.sdV₀ hL' hA.monoV hmono hu) (wittExt_wittInc_isHalf J B hh)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondFlatMapVacuumTranslateIsVacuum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.VacSecondPf

variable {D : D7}

theorem latO_of_none (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (hP : ∀ v, ¬ P v) : latO S T LS LT P = ⊥ := by
  rw [eq_bot_iff, latO, AddSubgroup.closure_le]
  rintro w ⟨α, -, hα, a, -, s, -, t, -, rfl⟩
  have h0 : α = 0 := by
    ext v : 1
    exact hα v (hP v)
  subst h0
  rw [SetLike.mem_coe, AddSubgroup.mem_bot]
  have hp : pairA D.host.F 0 0 = 0 := rfl
  ext i j
  simp [hp]

theorem heisO_zero (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem vac_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B) (LV : Lat J.W) (LV₀ : Lat J.W₀) (LW : Lat B.V) (LW₀ : Lat B.V₀) (P : Pl D → Prop), (∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v ∧ UnrAt s v) → ∀ f, Vac ψ J.W B.V LV LW P f → ∀ h₁ ∈ grpOff J.W P, ∀ h₂ ∈ grpOff B.V P, Vac ψ J.W₀ B.V₀ LV₀ LW₀ P (flatFB s (s.om (h₁, h₂) f)) := by
  intro D ψ σ J B s LV LV₀ LW LW₀ P hP f hf h₁ hh₁ h₂ hh₂
  have hflat : ∀ Q : Pl D → Prop, IsFlatFB s Q (flatFB s) := fun Q => (_root_.GlobalTheory.FinPl.flatLaws_all D ψ Q).2 σ J B s
  have htheta : IsThetaFunO ψ J.W B.V (s.om (h₁, h₂) f) := s.weil.om_pres _ _ hf.1
  have hth0 : IsThetaFunO ψ J.W₀ B.V₀ (flatFB s (s.om (h₁, h₂) f)) := (hflat P).Heisenberg₂.theta _ htheta
  by_cases hne : ∃ v, P v
  · obtain ⟨v₀, hv₀⟩ := hne
    have a₀ := (hP v₀ hv₀).1
    have hT : ∀ v, P v → Tame D v := fun v hv => (hP v hv).1.tame
    have L1 := _root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B.V s.χV s.χW s.om s.weil LV LW a₀.sdV a₀.sdW P hT
    have L0 := _root_.GlobalTheory.VacLoc.vac_loc D ψ J.W₀ B.V₀ s.χV s.χW s.om₀ s.weil₀ LV₀ LW₀ a₀.sdV₀ a₀.sdW₀ P hT
    have hg : Vac ψ J.W B.V LV LW P (s.om (h₁, h₂) f) := (L1 f).2.1 hf h₁ hh₁ h₂ hh₂
    have hgv := ((L1 _).1.mp hg).2
    refine (L0 _).1.mpr ⟨hth0, fun v hv => ?_⟩
    exact (_root_.GlobalTheory.FinPl.supportShift D ψ σ J B s LV LV₀ LW LW₀ v (hP v hv).1 (hP v hv).2 (flatFB s) (hflat (· = v))
      ((_root_.GlobalTheory.FlatShiftPf.flatShift D ψ (· = v)).2 σ J B s) _ (hgv v hv)).1
  · push_neg at hne
    have hbot := latO_of_none J.W₀ B.V₀ (LV₀ : Set _) (LW₀ : Set _) P hne
    refine ⟨hth0, ?_, ?_⟩
    · intro u hu
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [two_nsmul, add_zero, heisO_zero]
    · intro e _ u hu _
      rw [hbot, AddSubgroup.mem_bot] at hu
      subst hu
      rw [heisO_zero]

end GlobalTheory.VacSecondPf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesTopStep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMove

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem weil_rec {n k : ℕ} (e : n = k) {χS χT : (AE D)ˣ →* Circle} {o : Om (Yc D n) D.sp.X'}
    (h : IsWeilDatumO R.ψ (Yc D n) D.sp.X' χS χT o) :
    IsWeilDatumO R.ψ (Yc D k) D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') o e) := by
  subst e
  exact h

theorem vac_rec {n k : ℕ} (e : n = k) {f : WO (Yc D n) D.sp.X' → ℂ}
    (h : IsVacO R.ψ R.θ (Yc D n) D.sp.X' (cart (R.MY n)) (cart R.MX) (R.ΛY n) R.ΛX f) :
    IsVacO R.ψ R.θ (Yc D k) D.sp.X' (cart (R.MY k)) (cart R.MX) (R.ΛY k) R.ΛX
      (Eq.rec (motive := fun n _ => WO (Yc D n) D.sp.X' → ℂ) f e) := by
  subst e
  exact h

theorem weil_omT (hω : R.chain_ωX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsWeilDatumO R.ψ (Yc D (j + 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
      (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (omT R t j h) :=
  weil_rec R (idx_top h) (hω t)

theorem isVacO_vacT (hv : R.chain_vX) (t : T) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) :
    IsVacO R.ψ R.θ (Yc D (j + 1)) D.sp.X' (cart (R.MY (j + 1))) (cart R.MX) (R.ΛY (j + 1)) R.ΛX (vacT R j h) :=
  vac_rec R (idx_top h) (hv t).1

end Package

theorem fock_vac_moved_top : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex), PkHyp W → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (g : GA D (Yc D (j + 1))) (gT : GA D D.sp.X'), g ∈ GfC (Yc D (j + 1)) → gT ∈ GfC D.sp.X' → ∀ (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (LT : GlobalTheory.FinPl.Lat D.sp.X'), IsSelfDualC (Yc D (j + 1)) M' → IsSelfDualC D.sp.X' LT → (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) g ((pk W).ΛY (j + 1)) M' P) → (∀ P, GlobalTheory.FinPl.Moves D.sp.X' gT (pk W).ΛX LT P) → (∀ P, GlobalTheory.FinPl.Vac (pk W).ψ (Yc D (j + 1)) D.sp.X' M' LT (fun _ => True) (omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) P))) ∧ omT (pk W) W.P.A3.A.μ0 j h (g, gT) (pureTensorO (pk W).ψ (pk W).θ (Yc D (j + 1)) D.sp.X' (cart ((pk W).MY (j + 1))) (cart (pk W).MX) (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (vacT (pk W) j h) 1) ≠ 0 := by
  intro D L hT Gi Gl Kc Yd cX ex W hW j h g gT hg hgT M' LT hM' hLT hm hmT
  have hLev := hW.bot.hyp.2.2.2.1.lev
  have sdY : IsSelfDualC (Yc D (j + 1)) ((pk W).ΛY (j + 1)) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY (j + 1) (by omega))
  have sdX : IsSelfDualC D.sp.X' (pk W).ΛX := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hLev.βX
  have key := GlobalTheory.StepMove.gen (weil_omT (pk W) W.Q.charW.base.chain.ωX W.P.A3.A.μ0 j h) sdY hM' sdX hLT hg hgT (hm _) (hmT _)
    (onb ((pk W).MY (j + 1))) (onb (pk W).MX) (isVacO_vacT (pk W) W.Q.charW.base.chain.vX W.P.A3.A.μ0 j h)
  refine ⟨fun P => ?_, key.2⟩
  have h1 := key.1 P 1 (one_mem _) 1 (one_mem _)
  rwa [one_mul, one_mul] at h1

end GlobalTheory.TopMove

end
end

