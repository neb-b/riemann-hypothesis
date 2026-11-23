module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFrameWZeroExists
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0020
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MeasurePreservingPiProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.RealPlaceAnalysis.FinalF

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JUMeasurableEmbedding
section
noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries

section MeasUJ

variable {n : ℕ} (ε : Fin n → Bool)

def jU (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)

theorem jU_eq (g : Formalism.REAL.UJ ε) : (jU ε g : Matrix (Fin n) (Fin n) ℂ) = Formalism.MainNotions.S.uMat g := rfl

theorem inUJ_val (g : Formalism.REAL.UJ ε) : Formalism.REAL.inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := g.2

theorem inv_val (g : Formalism.REAL.UJ ε) :
    (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      Formalism.REAL.Jm ε * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε := by
  apply Units.inv_eq_of_mul_eq_one_left
  have hg : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
      ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = Formalism.REAL.Jm ε := inUJ_val ε g
  calc Formalism.REAL.Jm ε * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      = Formalism.REAL.Jm ε * (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε *
        ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
          simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε := by rw [hg]
    _ = 1 := Formalism.REAL.Jm_mul_self ε

theorem jU_isEmbedding : IsEmbedding (jU ε) := by
  have hcont : Continuous (jU ε) := by
    show Continuous fun g : Formalism.REAL.UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
    exact (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val
  have hinj : Function.Injective (jU ε) := fun a b h => Subtype.ext (Units.ext h)
  let φ : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun m => ((m : Matrix (Fin n) (Fin n) ℂ),
      MulOpposite.op (Formalism.REAL.Jm ε * (m : Matrix (Fin n) (Fin n) ℂ)ᴴ * Formalism.REAL.Jm ε))
  have hφ : Continuous φ :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : φ ∘ jU ε = Units.embedProduct (Matrix (Fin n) (Fin n) ℂ) ∘ Subtype.val := by
    funext g
    refine Prod.ext rfl ?_
    simp only [Function.comp_apply, φ, Units.embedProduct_apply, MulOpposite.op_inj]
    exact (inv_val ε g).symm
  refine ⟨Topology.IsInducing.of_comp hcont hφ ?_, hinj⟩
  rw [hcomp]
  exact (Units.isEmbedding_embedProduct.comp IsEmbedding.subtypeVal).isInducing

theorem jU_range : Set.range (jU ε) = {m : Fin n → Fin n → ℂ | Formalism.REAL.inUJ ε (m : Matrix (Fin n) (Fin n) ℂ)} := by
  ext m
  constructor
  · rintro ⟨g, rfl⟩
    exact inUJ_val ε g
  · intro hm
    exact ⟨⟨Matrix.nonsingInvUnit (m : Matrix (Fin n) (Fin n) ℂ)
      (isUnit_iff_ne_zero.mpr (det_ne_zero_of_inUJ ε hm)), hm⟩, rfl⟩

theorem jU_measurableEmbedding : MeasurableEmbedding (jU ε) := by
  have hcl : IsClosed (Set.range (jU ε)) := by
    rw [jU_range]
    exact isClosed_eq
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
      continuous_const
  exact (⟨jU_isEmbedding ε, hcl⟩ : IsClosedEmbedding (jU ε)).measurableEmbedding

theorem measurable_toUJ {α : Type*} [MeasurableSpace α] (M : α → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ c, IsIsom ε (M c)) (hmeas : ∀ i j, Measurable fun c => M c i j) :
    Measurable fun c => toUJ ε (hM c) := by
  refine (jU_measurableEmbedding ε).measurable_comp_iff.mp ?_
  have h : (jU ε ∘ fun c => toUJ ε (hM c)) = fun c => (M c : Fin n → Fin n → ℂ) := by
    funext c
    exact (jU_eq ε _).trans (uMat_toUJ ε (hM c))
  rw [h]
  exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hmeas i j

end MeasUJ

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLie
section
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf

theorem exp_mulVec_of_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) (h : A *ᵥ v = 0) :
    NormedSpace.exp A *ᵥ v = v := by
  letI : SeminormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin d) (Fin d) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin d) (Fin d) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  have hpow : ∀ n : ℕ, A ^ (n + 1) *ᵥ v = 0 := by
    intro n
    induction n with
    | zero => simpa using h
    | succ n ih => rw [pow_succ, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  let L0 : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] (Fin d → ℂ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by ext i; simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
  let L : Matrix (Fin d) (Fin d) ℂ →L[ℂ] (Fin d → ℂ) := LinearMap.toContinuousLinearMap L0
  have hL : ∀ M, L M = M *ᵥ v := fun M => rfl
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), ← hL, L.map_tsum (NormedSpace.expSeries_summable' (𝕂 := ℂ) A)]
  rw [tsum_eq_single 0]
  · simp [hL]
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [hL, Matrix.smul_mulVec, hpow m, smul_zero]

theorem adjH_def {k r : ℕ} (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Formalism.MainNotions.BridgeCSB.adjH X = Hpk k r * Xᴴ * Hpk k r := rfl

theorem exp_mem_UH {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : Hpk k r * Xᴴ * Hpk k r + X = 0) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r) := by
  rw [Formalism.MainNotions.BridgeCSB.mem_UH_iff, Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul]
  have ha : Formalism.MainNotions.BridgeCSB.adjH X = -X := eq_neg_of_add_eq_zero_left hX
  rw [ha, Complex.star_def, Complex.conj_ofReal, smul_neg, ← Matrix.exp_add_of_commute]
  · rw [neg_add_cancel, NormedSpace.exp_zero]
  · exact (Commute.refl _).neg_left

theorem adj_of_lie {k r : ℕ} {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hX : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ UH (Hpk k r)) : Hpk k r * Xᴴ * Hpk k r + X = 0 := by
  have hadj : Formalism.MainNotions.BridgeCSB.adjH X = -X := by
    apply Formalism.MainNotions.BridgeCSB.exp_smul_inj
    intro t
    have hU := hX t
    have h1 : Formalism.MainNotions.BridgeCSB.adjH (NormedSpace.exp ((t : ℂ) • X)) = (NormedSpace.exp ((t : ℂ) • X))⁻¹ :=
      (Matrix.inv_eq_left_inv ((Formalism.MainNotions.BridgeCSB.mem_UH_iff _).1 hU)).symm
    rw [Formalism.MainNotions.BridgeCSB.adjH_exp_gen, Formalism.MainNotions.BridgeCSB.adjH_smul, Complex.star_def, Complex.conj_ofReal,
      ← Matrix.exp_neg] at h1
    rw [h1, smul_neg]
  rw [← adjH_def, hadj, neg_add_cancel]

theorem lieG : LieG := by
  intro k r
  ext X
  constructor
  · intro hX
    exact adj_of_lie hX
  · intro hX t
    exact exp_mem_UH hX t

theorem col_zero {d : ℕ} {X : Matrix (Fin d) (Fin d) ℂ} (j : Fin d)
    (h : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) : X *ᵥ bvec j = 0 := by
  funext i
  have hij : X i j = 0 := by
    refine Formalism.MainNotions.BridgeCSB.entry_zero_of_const' X i j (bvec j i) fun t => ?_
    have := congrFun (h t) i
    rw [← this, Matrix.mulVec, dotProduct]
    simp [bvec, Pi.single_apply]
  rw [Matrix.mulVec, dotProduct]
  simp [bvec, Pi.single_apply, hij]

theorem lieWb : LieWb := by
  intro k r
  ext X
  constructor
  · intro hX
    refine ⟨adj_of_lie fun t => (hX t).1, fun a => ⟨?_, ?_⟩⟩
    · exact col_zero _ fun t => ((hX t).2 a).1
    · exact col_zero _ fun t => ((hX t).2 a).2
  · rintro ⟨hX, hk⟩ t
    refine ⟨exp_mem_UH hX t, fun a => ⟨?_, ?_⟩⟩
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).1, smul_zero])
    · exact exp_mulVec_of_zero _ _ (by rw [Matrix.smul_mulVec, (hk a).2, smul_zero])

end Formalism.L2.SG.Pf.BH
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormLinks
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.NormCut

section Links

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (TR : TypedRed X) {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0) in
def MassA {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (c : ColSys X w rs) : Prop :=
  ∀ q : {Λ // Λ ∈ rs}, wRow D F0 q.1 = ((Nat.card (Aset TR c q) : ℝ))⁻¹

theorem colPhase_holds (hTF : FrameTie X u u' F0 F0') : ColPhase F0 F0' TR cs cs' (scOf TR cs) (scOf TR cs') := by
  have hN := adm_norm_of_fixed_frames cs cs' hTF (Formalism.L2.SG.Pf.termK X cs cs') (Formalism.L2.SG.Pf.modGAt X)
  have hA := adm_parity_of_norm cs cs' (Formalism.L2.SG.Pf.termK X cs cs') hN
  exact colPhase_of TR cs cs' (leviCols_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA)
    (phaseAt_of TR cs cs' (Formalism.L2.SG.Pf.colLatK X cs) (Formalism.L2.SG.Pf.colLatK X cs') hA hN)

theorem colFree_steps (hK : X.LevelSubgroupCharacter) (hR : ColReps hK cs) (hCL : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u hK)
    (hO : Formalism.L2.SG.Pf.NormSteps.LeviOntoS TR cs) (hRep : Formalism.L2.SG.Pf.NormSteps.ColLatRepS cs hK)
    (hMass : MassA TR F0 cs) : ColFree F0 TR cs (Aset TR cs) (scOf TR cs) := fun q =>
  ⟨colFreeBij_of TR cs hK hR hCL (Formalism.L2.SG.Pf.colLatK X cs) hO hRep q, hMass q⟩

end Links

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProdFormula
section
noncomputable section

open MeasureTheory Topology
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

section ProdF

variable {ι : Type} [Fintype ι] {r : ℕ} {G : ι → Type} [∀ v, Group (G v)] [∀ v, MeasurableSpace (G v)]
  [∀ v, MeasurableMul₂ (G v)] [∀ v, MeasurableInv (G v)]

theorem prod_formula (mG : ∀ v, Measure (G v)) [∀ v, SigmaFinite (mG v)]
    (ν : ∀ v, Measure (Fin (r + 1) → ℂ)) [∀ v, SigmaFinite (ν v)]
    (μ μ' : ∀ v, Measure (G v)) [∀ v, SigmaFinite (μ v)] [∀ v, SigmaFinite (μ' v)]
    (h : ∀ v, (Fin (r + 1) → ℂ) → G v) (hh : ∀ v, Measurable (h v))
    (hm : ∀ v, mG v = ((ν v).prod ((μ v).prod (μ' v))).map (fun x => x.2.1 * h v x.1 * x.2.2⁻¹))
    (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂Measure.pi mG = ∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => h v (c v)) * s'⁻¹)
      ∂Measure.pi μ' ∂Measure.pi μ ∂Measure.pi ν := by
  have hFm : ∀ v, Measurable
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹) :=
    fun v => ((measurable_fst.comp measurable_snd).mul ((hh v).comp measurable_fst)).mul
      (measurable_snd.comp measurable_snd).inv
  have : ∀ v, SigmaFinite (((ν v).prod ((μ v).prod (μ' v))).map
      (fun x : (Fin (r + 1) → ℂ) × (G v × G v) => x.2.1 * h v x.1 * x.2.2⁻¹)) := fun v => by
    rw [← hm v]; infer_instance
  have hpi : Measure.pi mG = (Measure.pi fun v => (ν v).prod ((μ v).prod (μ' v))).map
      (fun y v => (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) := by
    rw [Measure.pi_map_pi (fun v => (hFm v).aemeasurable)]
    congr 1; funext v; exact hm v
  have hYm : Measurable (fun (y : (v : ι) → (Fin (r + 1) → ℂ) × (G v × G v)) (v : ι) =>
      (y v).2.1 * h v (y v).1 * (y v).2.2⁻¹) :=
    Measurable.of_eval fun v => (hFm v).comp (measurable_pi_apply v)
  have hgm : Measurable (fun z : ((v : ι) → (Fin (r + 1) → ℂ)) × (((v : ι) → G v) × ((v : ι) → G v)) =>
      φ (z.2.1 * (fun v => h v (z.1 v)) * z.2.2⁻¹)) := by
    refine hφ.comp (((measurable_fst.comp measurable_snd).mul ?_).mul
      (measurable_snd.comp measurable_snd).inv)
    exact Measurable.of_eval fun v => (hh v).comp ((measurable_pi_apply v).comp measurable_fst)
  have hE1 := measurePreserving_piProd (α := fun _ => Fin (r + 1) → ℂ) (β := fun v => G v × G v)
    ν (fun v => (μ v).prod (μ' v))
  have hE2 := (MeasurePreserving.id (Measure.pi ν)).prod
    (measurePreserving_piProd (α := G) (β := G) μ μ')
  have hE := hE2.comp hE1
  rw [hpi, lintegral_map hφ hYm]
  refine Eq.trans ?_ ((hE.lintegral_comp hgm).trans ?_)
  · rfl
  rw [lintegral_prod _ hgm.aemeasurable]
  refine lintegral_congr fun c => ?_
  exact lintegral_prod (fun y : ((v : ι) → G v) × ((v : ι) → G v) =>
    φ (y.1 * (fun v => h v (c v)) * y.2⁻¹)) (hgm.comp measurable_prodMk_left).aemeasurable

theorem dc_switch (μ μ' : Measure ((v : ι) → G v)) [SFinite μ'] (φ : ((v : ι) → G v) → ℝ≥0∞) (hφ : Measurable φ)
    (γ t t' : (v : ι) → G v) (ht : μ.map (fun x => x * t) = μ) (ht' : μ'.map (fun x => x * t') = μ') :
    ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
  have hΦ : Measurable fun a : (v : ι) → G v => ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' :=
    (hφ.comp ((measurable_fst.mul_const γ).mul measurable_snd.inv)).lintegral_prod_right'
  have inner : ∀ a : (v : ι) → G v,
      ∫⁻ s', φ (a * γ * (s' * t')⁻¹) ∂μ' = ∫⁻ s', φ (a * γ * s'⁻¹) ∂μ' := by
    intro a
    have hf : Measurable fun s' : (v : ι) → G v => φ (a * γ * s'⁻¹) :=
      hφ.comp (measurable_const.mul measurable_inv)
    rw [← lintegral_map hf (measurable_mul_const t'), ht']
  calc ∫⁻ s, ∫⁻ s', φ (s * (t * γ * t'⁻¹) * s'⁻¹) ∂μ' ∂μ
      = ∫⁻ s, ∫⁻ s', φ (s * t * γ * (s' * t')⁻¹) ∂μ' ∂μ := by
        refine lintegral_congr fun s => lintegral_congr fun s' => ?_
        congr 1; group
    _ = ∫⁻ s, ∫⁻ s', φ (s * t * γ * s'⁻¹) ∂μ' ∂μ :=
        lintegral_congr fun s => inner (s * t)
    _ = ∫⁻ s, ∫⁻ s', φ (s * γ * s'⁻¹) ∂μ' ∂μ := by
        rw [← lintegral_map hΦ (measurable_mul_const t), ht]

end ProdF

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightInvOfModular
section
noncomputable section

open MeasureTheory Topology Filter Matrix
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem inS_pres {g : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (a : ℕ) :
    ∀ y ∈ spanLt e a, g *ᵥ y ∈ spanLt e a := by
  intro y hy
  have hle : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin g) := by
    unfold spanLt
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : ℕ) < a := hb
    simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
    have e1 : g *ᵥ e b = e b + (g - 1) *ᵥ e b := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e1]
    refine Submodule.add_mem _ (Submodule.subset_span ⟨b, hb', rfl⟩) ?_
    refine Submodule.span_mono ?_ (hg.1 b)
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, lt_trans hc hb', rfl⟩
  exact hle hy

theorem inS_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : InS e z g) (hh : InS e z h) : InS e z (g * h) := by
  have key : ∀ v : Fin n → ℂ, (g * h - 1) *ᵥ v = g *ᵥ ((h - 1) *ᵥ v) + (g - 1) *ᵥ v := fun v => by
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
    abel
  refine ⟨fun a => ?_, ?_⟩
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg a.1 _ (hh.1 a)) (hg.1 a)
  · rw [key]
    exact Submodule.add_mem _ (inS_pres e z hg r _ hh.2) hg.2

theorem inS_one : InS e z (1 : Matrix (Fin n) (Fin n) ℂ) :=
  ⟨fun a => by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _,
    by rw [sub_self, Matrix.zero_mulVec]; exact Submodule.zero_mem _⟩

def SG : Subgroup (Formalism.REAL.UJ ε) where
  carrier := SLoc ε e z
  one_mem' := inS_one e z
  mul_mem' {a b} ha hb := inS_mul e z ha hb
  inv_mem' {a} ha := Formalism.L2.SG.RealObj.InfCut.inS_inv _ _ (Formalism.MainNotions.S.uMat a) (Formalism.MainNotions.S.uMat a⁻¹)
    (Formalism.L2.SG.RealObj.InfCut.uMat_inv_mul' a) ha

theorem coe_SG : (SG ε e z : Set (Formalism.REAL.UJ ε)) = SLoc ε e z := rfl

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.uMat g) :=
  ((Formalism.REAL.uJEmb n ε).1).continuous

theorem SG_closed : IsClosed (SG ε e z : Set (Formalism.REAL.UJ ε)) := by
  have hc : ∀ v : Fin n → ℂ, Continuous (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ v) := fun v =>
    ((continuous_uMat ε).sub continuous_const).matrix_mulVec continuous_const
  have e1 : (SG ε e z : Set (Formalism.REAL.UJ ε)) =
      (⋂ a : Fin r, (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ e a) ⁻¹' (spanLt e a.1 : Set (Fin n → ℂ))) ∩
        (fun g : Formalism.REAL.UJ ε => (Formalism.MainNotions.S.uMat g - 1) *ᵥ z) ⁻¹' (spanLt e r : Set (Fin n → ℂ)) := by
    ext g
    simp only [coe_SG, SLoc, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
      SetLike.mem_coe]
  rw [e1]
  exact (isClosed_iInter fun a => (Submodule.closed_of_finiteDimensional _).preimage (hc _)).inter
    ((Submodule.closed_of_finiteDimensional _).preimage (hc _))

section Sub

variable {ε e z}

end Sub

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI
end
end

