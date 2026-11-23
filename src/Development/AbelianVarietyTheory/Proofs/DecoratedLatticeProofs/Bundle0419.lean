module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SupportedStabilizerConjSatisfiesDeepCongruence
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.KTwoAwayLevel

theorem mem_mL_of_fix {I : AutInst} (g : ℕ) {t : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F} (ht : t ∈ IntAf I.F I.E) {z : VA I}
    (hz : z ∈ I.Lf) (hfix : ((g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t) • z = z) : z ∈ mL I g := by
  have e : z = (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) • (t • z) := by rw [smul_smul]; exact hfix.symm
  rw [e]
  exact Submodule.subset_span ⟨t • z, I.Lf.smul_mem (⟨t, ht⟩ : IntAf I.F I.E) hz, rfl⟩

theorem conj_fix {I : AutInst} {a y : I.Gf} (ha : a ∈ I.Kset) (hy : y ∈ I.Kset) (c : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)
    (hc : ∀ i j, c * (I.fmat y - 1) i j = (I.fmat y - 1) i j) {w : VA I} (hw : w ∈ I.Lf) :
    (I.fmat (a⁻¹ * y * a) - 1) *ᵥ w ∈ I.Lf ∧
      c • ((I.fmat (a⁻¹ * y * a) - 1) *ᵥ w) = (I.fmat (a⁻¹ * y * a) - 1) *ᵥ w := by
  have hK : a⁻¹ * y * a ∈ I.Kset := by
    show ((a⁻¹ * y * a : I.Gf) : GL _ _) ∈ Formalism.UG.stabGL I.Lf
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem (mul_mem (inv_mem ha) hy) ha
  refine ⟨?_, ?_⟩
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact sub_mem (Formalism.L2.SG.Pf.unitaryCongruence.K_mv I hK hw) hw
  · have hM : c • (I.fmat y - 1) = I.fmat y - 1 := by
      ext i j
      rw [Matrix.smul_apply, smul_eq_mul, hc]
    have hinv : I.fmat a⁻¹ * I.fmat a = 1 := by
      simp only [Formalism.MainNotions.S.AutInst.fmat]
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    have e : I.fmat (a⁻¹ * y * a) - 1 = I.fmat a⁻¹ * (I.fmat y - 1) * I.fmat a := by
      simp only [Formalism.MainNotions.S.AutInst.fmat] at hinv ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_one, ← hinv]
    rw [e, ← Matrix.smul_mulVec]
    conv_rhs => rw [← hM]
    rw [Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7}

open Classical in
theorem exists_div_indP (v : GlobalTheory.FinPl.Pl D) (g : ℕ) (hg : (g : 𝓞 D.host.F) ∉ v.asIdeal) :
    ∃ s : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F, s ∈ Formalism.UG.intAd D.host.F ∧
      (g : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) * s = GlobalTheory.FinPl.KOpen.indP D (· = v) := by
  have hg' : g ≠ 0 := by rintro rfl; exact hg (by simp)
  have hg0 : (g : D.host.F) ≠ 0 := Nat.cast_ne_zero.2 hg'
  refine ⟨GlobalTheory.FinPl.KOpen.indP D (· = v) * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (g : D.host.F)⁻¹,
    fun w => ?_, ?_⟩
  · have e : (GlobalTheory.FinPl.KOpen.indP D (· = v) * algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (g : D.host.F)⁻¹) w =
        (if w = v then 1 else 0) * algebraMap D.host.F (w.adicCompletion D.host.F) (g : D.host.F)⁻¹ := rfl
    rw [e]
    by_cases hw : w = v
    · subst hw
      have h2 : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (g : D.host.F)⁻¹) =
          w.valuation D.host.F (g : D.host.F)⁻¹ := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
      rw [if_pos rfl, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers, h2, map_inv₀]
      have h1 : w.valuation D.host.F (g : D.host.F) = 1 := by
        have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (g : 𝓞 D.host.F)
        rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hg] at this
        simpa using this
      rw [h1, inv_one]
    · rw [if_neg hw, zero_mul]; exact zero_mem _
  · rw [mul_left_comm, ← map_natCast (algebraMap D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) g, ← map_mul,
      mul_inv_cancel₀ hg0, map_one, mul_one]

open Classical in
theorem fix_of_grpAt {I : AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (v : GlobalTheory.FinPl.Pl D) (g : ℕ)
    (hg : (g : 𝓞 D.host.F) ∉ v.asIdeal) (κ : GA D (D.sp.Y 0)) (hκ : κ ∈ grpAt (D.sp.Y 0) (· = v)) :
    ∃ t ∈ IntAf I.F I.E, ∀ i j, (g : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) * t *
      (I.fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2) - 1) i j =
      (I.fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)) κ).2) - 1) i j := by
  subst h
  obtain ⟨s, hs, hgs⟩ := exists_div_indP v g hg
  refine ⟨(1 : (Formalism.L2.SG.InstExistsPf.instOf D).E) ⊗ₜ[(Formalism.L2.SG.InstExistsPf.instOf D).F] s, Subring.subset_closure (Or.inr ⟨⟨s, hs⟩, rfl⟩), fun i j => ?_⟩
  have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  rw [ContinuousMulEquiv.symm_apply_apply] at e
  have hf : (Formalism.L2.SG.InstExistsPf.instOf D).fmat ((((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA rfl)) κ).2) =
      (Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) :=
    (congrArg Units.val e).symm
  have key : ∀ i j : Fin (D.sp.Y 0).rank, (1 ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = v)) *
      ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j =
      ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j := by
    intro i j
    have hb : (Formalism.L2.Theta.mt (D.sp.Y 0) κ - 1) i j ∈ idAt D (· = v) :=
      (GlobalTheory.FinPl.SetCut.mem_congGrp_iff _ _ κ).1 hκ i j
    have hent : ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j =
        Formalism.IndefR.Datum.toEAf D ((Formalism.L2.Theta.mt (D.sp.Y 0) κ - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.map_apply]
      congr 1
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
    have hm := congrArg (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E)
      (GlobalTheory.FinPl.KOpen.e_mul_fin hb)
    rw [map_mul, Algebra.TensorProduct.comm_tmul] at hm
    rw [hent]
    exact hm
  have hg1 : ((g : ℕ) : D.host.E ⊗[D.host.F] Formalism.MainNotions.S.Af D.host.F) * ((1 : D.host.E) ⊗ₜ[D.host.F] s) =
      1 ⊗ₜ[D.host.F] GlobalTheory.FinPl.KOpen.indP D (· = v) := by
    rw [← hgs, ← map_natCast (Algebra.TensorProduct.includeRight (R := D.host.F) (A := D.host.E)) g,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hf]
  exact (congrArg (fun c => c * ((Formalism.L2.Theta.mt (D.sp.Y 0) κ).map (Formalism.IndefR.Datum.toEAf D) - 1) i j) hg1).trans
    (key i j)

theorem k2cong_conj_of_grpAt : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (v : GlobalTheory.FinPl.Pl D), ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal → ∀ κ : GA D (D.sp.Y 0), κ ∈ grpAt (D.sp.Y 0) (· = v) → (iotaX X h κ).2 ∈ X.B.I.Kset → K2cong X.B.I X.B.g X.e0 X.z0 X.bw ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) := by
  intro D X h u v hv κ hκ hK
  obtain ⟨t, ht, hfix⟩ := fix_of_grpAt h v _ hv κ hκ
  have hc : ∀ i j, ((X.B.g : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) * t) * (X.B.I.fmat (iotaX X h κ).2 - 1) i j =
      (X.B.I.fmat (iotaX X h κ).2 - 1) i j := by
    rw [X.g_eq]; exact hfix
  have key : ∀ w ∈ X.B.I.Lf,
      (X.B.I.fmat ((X.xu u)⁻¹ * (iotaX X h κ).2 * X.xu u) - 1) *ᵥ w ∈ mL X.B.I X.B.g := by
    intro w hw
    obtain ⟨h1, h2⟩ := conj_fix (X.xu_K u) hK _ hc hw
    exact mem_mL_of_fix X.B.g ht h1 h2
  unfold K2cong InMod
  exact ⟨fun a => Submodule.mem_sup_right (key _ (X.vectorsInLattice.1 a).1), Submodule.mem_sup_right (key _ X.vectorsInLattice.2.1),
    fun i => Submodule.mem_sup_right (key _ (X.vectorsInLattice.2.2 i).1)⟩

end GlobalTheory.Core.Mi.KTwoAwayLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PosOne
open scoped ENNReal

attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

section Scale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem isQuotInt_smul_measure {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (a : ℝ≥0∞)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX (a • μG) p f ((a.toReal : ℂ) * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨F, hF, hf, ?_⟩
  rw [integral_smul_measure, hz, Complex.real_smul]

theorem isQuotInt_const_mul {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (b : ℂ)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX μG p (fun x => b * f x) (b * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨fun x => b * F x, (SB _).smul_mem b hF, fun x => ?_, ?_⟩
  · dsimp only
    rw [hf x, ← integral_const_mul]
    congr 1
    funext g
    exact (integral_const_mul _ _).symm
  · rw [hz, integral_const_mul]

theorem app_smul {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (b : ℂ) (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app (b • l) f = b • app l f := by
  unfold app
  split_ifs <;> simp

theorem oneDbl_smul {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] {ψ : AddChar k Circle} {ν : Measure k}
    {m₁ : Measure (GL n₁ k)} {G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)} {m₂ : Measure (GL n₂ k)}
    {G₂ : Measure (GL (n₂ ⊕ Fin c) k)} {μ₁ μ₂ : kˣ →* ℂˣ} {ρ : ℕ} {σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} {F : A}
    {Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ}
    {Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ} {z : ℂ} (a b : ℝ≥0∞)
    (h : OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁ Φ₂ z) :
    OneDbl ψ ν m₁ (a • G₁) m₂ (b • G₂) μ₁ μ₂ ρ σ T F Φ₁ Φ₂ ((a.toReal : ℂ) * ((b.toReal : ℂ) * z)) := by
  obtain ⟨w, hw, hz⟩ := h
  refine ⟨fun x => (b.toReal : ℂ) • w x, fun x Ψ => ?_, ?_⟩
  · exact isQuotInt_smul_measure b (hw x Ψ)
  · have := isQuotInt_smul_measure a (isQuotInt_const_mul (b.toReal : ℂ) hz)
    convert this using 2 with x
    rw [app_smul, smul_eq_mul]

theorem relIndex_mul_measure_KO {Y : Type} [Fintype Y] [DecidableEq Y] (G : Measure (GL Y k)) [G.IsHaarMeasure]
    (hK : G (KO k Y) = 1) (J : Subgroup (GL Y k)) (hJ : IsCO J) (hle : J ≤ KO k Y) :
    (J.relIndex (KO k Y) : ℝ≥0∞) * G J = 1 ∧ J.relIndex (KO k Y) ≠ 0 := by
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have hc : IsCompact (KO k Y : Set (GL Y k)) := GlobalTheory.SplitFlip.isCompact_KO
  haveI : CompactSpace (KO k Y) := isCompact_iff_compactSpace.1 hc
  have ho : IsOpen ((J.subgroupOf (KO k Y) : Subgroup (KO k Y)) : Set (KO k Y)) :=
    hJ.1.preimage continuous_subtype_val
  haveI : Finite (KO k Y ⧸ J.subgroupOf (KO k Y)) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : (J.subgroupOf (KO k Y)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup J (KO k Y) hle hJ.1.measurableSet G, hK]

theorem rescale_one_eq {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (hc : 1 ≤ c) {ν : Measure k} (hν : IsUnitVol ν)
    (m : Measure (GL n k)) : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν (1 : GL (n ⊕ Fin c) k) m = m := by
  have h := _root_.GlobalTheory.HaarR.volN_KO_eq_one k n c 1 le_rfl hc ν hν
  have e : (((stabLat (1 : GL (n ⊕ Fin c) k)).subgroupOf (N k n c 1) : Subgroup (N k n c 1)) : Set (N k n c 1)) =
      {u : N k n c 1 | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
    ext u
    simp [Subgroup.mem_subgroupOf, mem_stabLat]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  rw [e, h, inv_one, one_smul]

end Scale


set_option maxHeartbeats 4000000 in
theorem comb_eq_sum_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ hm₁ hG₁ hm₂ hG₂ hK₁ hK₂
    L₀ L₁ L₂ hco₁ hco₂ hle₁ hle₂ A _ _ τ hτ T hT F hF P₁ P₂ hty₁ hty₂ α A₁ A₂ hcov₁ hcov₂ e₀ he₀ e₂ he₂ z hz
  haveI := hm₁
  haveI := hG₁
  haveI := hm₂
  haveI := hG₂
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((GlobalTheory.SplitWeil.selfDual_measure k ψ hψ hne).2.1 hcond ν).1 hν
  obtain ⟨⟨ρ₀, hρ₀⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₀ ⊕ Fin (c + 1 + 1)) (n₁ ⊕ Fin (c + 1)) μ₁ ho₁
  have hsm₀ := hsm ρ₀ hρ₀

  have hcomb : ∀ f : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ,
      comb (e₀.mapDomain (· * α⁻¹)) (fun g => f (g * α)) = comb e₀ f := by
    intro f
    unfold comb
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [inv_mul_cancel_right]
  have hsrc : SrcComb ψ ν (ρ + 1) ρ₀ (ρ₀ α P₁) (e₀.mapDomain (· * α⁻¹)) := by
    intro L hL
    have hP : ∀ j : L₀.J, ρ₀ (j : GL (n₀ ⊕ Fin (c + 1 + 1)) k) P₁ = (L₀.lam j : ℂ) • P₁ := fun j =>
      Subtype.ext ((hρ₀ _ _).trans (hty₁.1 j))
    rw [he₀ _ ρ₀ hsm₀ L hL P₁ hP, ← hcomb]
    congr 1
    funext g
    rw [map_mul, Module.End.mul_apply]
  have hsym : ∀ g ∈ (e₀.mapDomain (· * α⁻¹)).support,
      SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ g 1 (ρ₀ α P₁).1) P₂.1 (z (g * α)) := by
    intro g hg
    classical
    rw [Finsupp.mapDomain_support_of_injective (mul_left_injective α⁻¹)] at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
    have e : om μ₁ (a * α⁻¹) 1 (ρ₀ α P₁).1 = om μ₁ (a * α⁻¹ * α) 1 P₁.1 := by
      rw [← hρ₀, ← hρ₀, map_mul ρ₀ (a * α⁻¹) α, Module.End.mul_apply]
    rw [e]
    simpa only [inv_mul_cancel_right] using hz a ha
  have h1 := _root_.GlobalTheory.PosOne.oneDbl_of_symDbl k n₀ n₁ n₂ c ρ hcρ ψ hψ hne ν hsd μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ A τ hτ T hT F ρ₀ hρ₀ (ρ₀ α P₁) P₂
    (e₀.mapDomain (· * α⁻¹)) hsrc (fun g => z (g * α)) hsym
  rw [hcomb, hρ₀] at h1

  obtain ⟨hi₁, hn₁⟩ := relIndex_mul_measure_KO G₁ hK₁ L₁.J hco₁ hle₁
  obtain ⟨hi₂, hn₂⟩ := relIndex_mul_measure_KO G₂ hK₂ L₂.J hco₂ hle₂
  set r₁ : ℝ≥0∞ := (L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℝ≥0∞) with hr₁
  set r₂ : ℝ≥0∞ := (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℝ≥0∞) with hr₂
  haveI : (r₁ • G₁).IsHaarMeasure := Measure.IsHaarMeasure.smul G₁ (by simpa [hr₁] using hn₁) (by simp [hr₁])
  haveI : (r₂ • G₂).IsHaarMeasure := Measure.IsHaarMeasure.smul G₂ (by simpa [hr₂] using hn₂) (by simp [hr₂])
  have h2 := oneDbl_smul r₁ r₂ h1
  have hc : 1 ≤ c := by omega
  rw [← rescale_one_eq (n := n₁) (c := c + 1) (by omega) hν m₁, ← rescale_one_eq (n := n₂) hc hν m₂] at h2
  have h3 := (GlobalTheory.PosOne.oneDbl_iff_sum k n₀ n₁ n₂ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ (r₁ • G₁) m₂ (r₂ • G₂) L₁ L₂
    hco₁ hco₂ (by rw [Measure.smul_apply, smul_eq_mul, hi₁]) (by rw [Measure.smul_apply, smul_eq_mul, hi₂]) 1 1 A τ hτ T hT F hF
    P₁ P₂ hty₁.2 hty₂ α A₁ A₂ hcov₁ hcov₂ _).1 h2

  have hex : ∀ γ ∈ A₁, ∀ β ∈ A₂, toOne ν τ ρ (fun v => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) v)
      (τ β F) = comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F) := by
    intro γ _ β hβ
    refine he₂ β hβ A τ hτ _ ?_ F hF
    intro g hg v
    unfold app
    split_ifs with h₁ h₂
    · exact (hT.1 _).1 _ g hg v
    · simp
    · simp
  have hr : ((r₁.toReal : ℂ) * (r₂.toReal : ℂ)) = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ)) := by
    simp [hr₁, hr₂]
  have hr0 : ((L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℂ) * (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn₁) (Nat.cast_ne_zero.2 hn₂)
  rw [← mul_assoc, hr] at h3
  rw [eq_inv_mul_iff_mul_eq₀ hr0, h3]
  refine Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun β hβ => ?_
  rw [hex γ hγ β hβ]

end GlobalTheory.PosOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepVectorTwoLevelLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecLawBoth


set_option maxHeartbeats 1000000 in
open Classical in
theorem stepLevLawT (D : D7) (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D) (hs : s.Is c k)
    (hs' : s'.Is c (k + 1)) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (hW : IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (f₀ f : WO s.V s'.V → ℂ)
    (hv : IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) :
    ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ω (1, κ) f = (Lev.levChi s'.V s'.β s'.L κ)⁻¹ • f := by
  intro κ hκ
  obtain ⟨hr, ξ1, hL⟩ := hs.lev
  obtain ⟨hr', ξ2, hL'⟩ := hs'.lev
  rw [hL] at hv
  rw [hL'] at hκ ⊢
  have ea : s.V.rank = D.R.r + k * D.R.t := hs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hs'.rank
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← Finset.union_empty c.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := _root_.GlobalTheory.ChainOnto.levRes_step D c hc k hk
  have hlev : Lev.finE s'.V κ ∈ lev D.sp.cm s'.V.gram s'.β
      (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B) := hκ.2
  have sg : Lev.finE s.V 1 ∈ St s.β := by rw [map_one]; exact Subgroup.one_mem _
  have sh : Lev.finE s'.V κ ∈ St s'.β := parLev_St hlev.1
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) hs.selfDual hs'.selfDual hs.frame hs'.frame hf he'
    (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT (Subgroup.one_mem _) hκ.1 sg sh
  set H : ∀ PP : Pl D.host.E, GL (Fin s'.V.rank) (kP PP) := fun PP => redFn s'.β PP (Lev.finE s'.V κ) with hH
  have hPeq : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P = c.P := by simp [Lev.datY]
  have hcg : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).cg = c.chi := by simp [Lev.datY]
  have hP : (fun PP : ↥c.Pg => upperLeftBlock hr' (H PP.1)) ∈ c.P.H := by
    have := hlev.2
    rw [hPeq] at this
    exact this
  have hBT : ∀ PP ∈ c.Pg, H PP ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hPP => parLev_g hlev.1 hPP
  have h1' : ω (1, κ) f₀ = ((∏ PP ∈ c.Pg, (c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)))⁻¹ : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_one, one_mul, hH]
  have hoT := _root_.GlobalTheory.ChainOnto.omegaG_levelP_move D s.V.rank s'.V.rank D.R.r D.R.t k hr hr' ea eb c.Pg c.P c.chi ξ1 H hBT hP
  have h2 := _root_.GlobalTheory.ThetaMove.om_theta_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (_root_.GlobalTheory.SchrTheta.isTheta_placeModel D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ 1 κ
    (_root_.GlobalTheory.StabLatInv.mem_latO_iff_actO_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame 1 κ sg sh) _
    ((((c.P.chi ⟨_, hP⟩ * ∏ PP ∈ c.Pg, ∏ i ∈ Finset.range (k + 1),
        c.chi (i + 1) PP (dBlk (blkOf D.R.r D.R.t) (i + 1) (H PP)))⁻¹ *
      ∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ)) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := _root_.GlobalTheory.FrameRed.frMapO_actO_int_red D s.V s'.V s.β s'.β 1 κ sg sh x
      have i0 : IsHalf e (actO s.V s'.V 1⁻¹ κ⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V 1 κ x ▸ GlobalTheory.SplitHecke.isHalf_actO 1 κ H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), StepLevLaw.omegaQ_empty, StepLevLaw.omegaQ_empty,
          mul_one, mul_one]
        simp only [map_one, redFn_one, Units.val_one, Matrix.mul_one]
        exact hoT (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2]
  congr 1
  have hchi : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P.chi ⟨_, hlev.2⟩ =
      c.P.chi ⟨_, hP⟩ := rfl
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hlev.2, hchi]
  simp only [Lev.datY, ↓reduceIte, Finset.prod_empty, mul_one]
  rw [Finset.prod_inv_distrib, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [mul_comm _ (∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP))), inv_mul_cancel_left]

theorem vecLaw : ∀ D : D7, ForStep D fun _ _ s s' p => VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L)
    (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  intro D _ c hc k hk s s' hs hs' p hp
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  refine ⟨fun κ hκ => (StepLevLaw.stepLevLaw D c hc ⟨k, hk⟩ s s' hs hs' p.ω hp.weil ξ f₀ p.f hv κ hκ).2, ?_⟩
  exact stepLevLawT D c hc k hk s s' hs hs' p.ω hp.weil ξ f₀ p.f hv

end GlobalTheory.ChainOnto.StepVecLawBoth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrcSingleApply
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem trc_single_apply {D : D7} {V : HSp D} (b : GA D V) (ε : ℂ) (f : GA D V → ℂ) (x : GA D V) :
    trc (Finsupp.single b ε) f x = ε * f (x * b) := by
  unfold trc
  by_cases hε : ε = 0
  · simp [hε]
  · rw [Finsupp.support_single_ne_zero _ hε]
    simp [GlobalTheory.MixPer.rTrans]
end GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.AdForm

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

def ellTop (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) :
    (FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) →ₗ[ℂ] ℂ :=
  (ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ)) •
    ((I.per l u a).period.flip (G' f) ∘ₗ eW.symm.toLinearMap ∘ₗ
      LinearMap.single ℂ (fun _ : (I.fm l u a).clsP => FrP (I.rec7 l Z) → ℂ) c ∘ₗ
      LinearMap.funLeft ℂ ℂ (fun y : FrP (I.rec7 l Z) => (⟨y.1, y.2⟩ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1))))

theorem ellTop_apply (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ)
    (G' : CXP R P t → (I.per l u a).Mt) (c : (I.fm l u a).clsP) (f : CXP R P t) (φ : FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) :
    ellTop R P eW ε G' c f φ = ε * (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) *
      (I.per l u a).period (eW.symm (Pi.single c (fun y : FrP (I.rec7 l Z) => φ ⟨y.1, y.2⟩))) (G' f) := by
  simp only [ellT, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, LinearMap.flip_apply,
    LinearEquiv.coe_coe, LinearMap.coe_single, smul_eq_mul]
  rfl

@[reducible] def clsTop (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ)
    (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X')
    (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)) (ε : ℂ) (G' : CXP R P t → (I.per l u a).Mt) :
    ClsT (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := (I.fm l u a).clsP
  U := UT
  h := h
  ell := fun _ _ _ c f => ellTop R P eW ε G' c f

end GlobalTheory.AdForm
end
end

