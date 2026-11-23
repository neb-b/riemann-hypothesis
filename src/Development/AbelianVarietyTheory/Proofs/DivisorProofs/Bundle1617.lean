module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBasisHyperbolicPlaneComplement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1581
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.PieriBlockIdeals.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsoluteThetaIntegralLeContinuousSeminorm
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AbsThetaSemi

variable {D : D7}

theorem continuous_coord {d m n : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Continuous (coord (D := D) (m := m) (n := n) ε) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine continuous_pi fun p => ?_
  let L : AE D →ₗ[AF D.host.F] AF D.host.F :=
    (Finsupp.lapply p.2.2).comp (Algebra.TensorProduct.basis (AF D.host.F) ε).repr.toLinearMap
  exact (IsModuleTopology.continuous_of_linearMap L).comp
    ((continuous_apply p.2.1).comp (continuous_apply p.1))

theorem continuous_invPt (B : HSp D) {a : ℕ} (ξ : Matrix (Fin B.rank) (Fin a) D.host.E) :
    Continuous fun h : GA D B => invPt B h ξ := by
  unfold invPt
  have hmt : Continuous (Formalism.L2.Theta.mt B) := Units.continuous_val.comp continuous_subtype_val
  exact (hmt.comp continuous_inv).matrix_mul continuous_const

theorem measurable_absTheta (B : HSp D) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ) :
    Measurable (absTheta B φ) := by
  haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
  haveI : Countable (Matrix (Fin B.rank) (Fin a) D.host.E) := inferInstanceAs (Countable (Fin B.rank → Fin a → D.host.E))
  exact Measurable.tsum fun ξ => (hφ.comp (continuous_invPt B ξ)).enorm.measurable

theorem measurable_descend_absTheta (B : HSp D) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ) :
    Measurable (descend (GQ B) (absTheta B φ)) :=
  measurable_from_quotient.2 (by
    rw [show descend (GQ B) (absTheta B φ) ∘ Quotient.mk'' = absTheta B φ from (leftInv_absTheta B φ).lift_descend]
    exact measurable_absTheta B hφ)

theorem absTheta_add_le (B : HSp D) {a : ℕ} (φ ψ : Mx D B.rank a → ℂ) (h : GA D B) :
    absTheta B (φ + ψ) h ≤ absTheta B φ h + absTheta B ψ h := by
  unfold absTheta
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun ξ => enorm_add_le _ _

theorem absTheta_smul (B : HSp D) {a : ℕ} (c : ℂ) (φ : Mx D B.rank a → ℂ) (h : GA D B) :
    absTheta B (c • φ) h = ‖c‖ₑ * absTheta B φ h := by
  unfold absTheta
  rw [← ENNReal.tsum_mul_left]
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul]

theorem absThetaInt_add_le (B : HSp D) (m : Measure (GA D B)) {a : ℕ} {φ : Mx D B.rank a → ℂ} (hφ : Continuous φ)
    (ψ : Mx D B.rank a → ℂ) : absThetaInt B m (φ + ψ) ≤ absThetaInt B m φ + absThetaInt B m ψ := by
  unfold absThetaInt
  rw [← lintegral_add_left (measurable_descend_absTheta B hφ)]
  exact lintegral_mono fun q => absTheta_add_le B φ ψ q.out

theorem absThetaInt_smul (B : HSp D) (m : Measure (GA D B)) {a : ℕ} (c : ℂ) (φ : Mx D B.rank a → ℂ) :
    absThetaInt B m (c • φ) = ‖c‖ₑ * absThetaInt B m φ := by
  unfold absThetaInt
  rw [← lintegral_const_mul' _ _ enorm_ne_top]
  exact lintegral_congr fun q => absTheta_smul B c φ q.out

theorem absTheta_le_liminf (B : HSp D) {a : ℕ} {ι : Type*} {u : Filter ι} [u.NeBot] {φs : ι → Mx D B.rank a → ℂ}
    {φ : Mx D B.rank a → ℂ} (hlim : ∀ x, Filter.Tendsto (fun i => φs i x) u (nhds (φ x))) (h : GA D B) :
    absTheta B φ h ≤ Filter.liminf (fun i => absTheta B (φs i) h) u := by
  unfold absTheta
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have ht : Filter.Tendsto (fun i => ∑ ξ ∈ s, ‖φs i (invPt B h ξ)‖ₑ) u (nhds (∑ ξ ∈ s, ‖φ (invPt B h ξ)‖ₑ)) :=
    tendsto_finsetSum s fun ξ _ => (hlim _).enorm
  rw [← ht.liminf_eq]
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall fun i => ENNReal.sum_le_tsum s)

theorem absThetaInt_le_liminf (B : HSp D) (m : Measure (GA D B)) {a : ℕ} {ι : Type*} {u : Filter ι} [u.NeBot]
    [u.IsCountablyGenerated] {φs : ι → Mx D B.rank a → ℂ} (hc : ∀ i, Continuous (φs i))
    {φ : Mx D B.rank a → ℂ} (hlim : ∀ x, Filter.Tendsto (fun i => φs i x) u (nhds (φ x))) :
    absThetaInt B m φ ≤ Filter.liminf (fun i => absThetaInt B m (φs i)) u := by
  unfold absThetaInt
  refine le_trans (lintegral_mono fun q => absTheta_le_liminf B hlim q.out) ?_
  exact lintegral_liminf_le fun i => measurable_descend_absTheta B (hc i)

end GlobalTheory.AbsThetaSemi

namespace GlobalTheory.AbsThetaSemi

theorem absThetaInt_le_contSeminorm : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (d : ℕ) (ε : Module.Basis (Fin d) D.host.F D.host.E), ∃ ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)), IsContSeminorm ν ∧ ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≤ ENNReal.ofReal (ν φ) := by
  intro hP D A B m hm hA hw d ε
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  have hcont : ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), Continuous (φ.1 ∘ coord ε) :=
    fun φ => (GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA D.host.F φ.2).comp (continuous_coord ε)
  have hfin : ∀ φ : WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d), absThetaInt B m (φ.1 ∘ coord ε) ≠ ⊤ :=
    fun φ => (hP D A.rank B hA hw θ hθ m hm ⟨_, _root_.GlobalTheory.SchwartzCoord.mem_schwartzA_comp_coord D θ hθ B.rank A.rank d ε φ⟩).ne
  let ν : Seminorm ℂ (WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d)) :=
    Seminorm.of (fun φ => (absThetaInt B m (φ.1 ∘ coord ε)).toReal)
      (fun φ ψ => by
        rw [← ENNReal.toReal_add (hfin φ) (hfin ψ)]
        exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin φ, hfin ψ⟩) (absThetaInt_add_le B m (hcont φ) _))
      (fun c φ => by
        show (absThetaInt B m (c • (φ.1 ∘ coord ε))).toReal = _
        rw [absThetaInt_smul, ENNReal.toReal_mul, toReal_enorm])
  refine ⟨ν, fun g => ?_, fun φ => (ENNReal.ofReal_toReal (hfin φ)).ge⟩
  let L : SchwartzMap (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ →ₗ[ℂ]
      WeilM.schA D.host.F (Fin B.rank × Fin A.rank × Fin d) :=
    { toFun := pureS g
      map_add' := fun f f' => Subtype.ext (funext fun x => by simp [pureS, WeilM.pureA, add_mul])
      map_smul' := fun c f => Subtype.ext (funext fun x => by simp [pureS, WeilM.pureA, mul_assoc]) }
  haveI := GlobalTheory.schwartzMap_barrelledSpace (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F)
  have hev : ∀ y, Continuous fun f : SchwartzMap (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ => f y :=
    fun y => ((continuous_eval_const y : Continuous fun F : BoundedContinuousFunction (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ => F y)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin B.rank × Fin A.rank × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ).continuous
  have hN : LowerSemicontinuous fun f => absThetaInt B m ((pureS g f).1 ∘ coord ε) := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro f
    exact absThetaInt_le_liminf B m (fun f' => hcont (pureS g f')) fun x => ((hev _).tendsto f).mul_const _
  refine Seminorm.continuous_of_lowerSemicontinuous (ν.comp L) fun f y hy => ?_
  by_cases hy0 : y < 0
  · exact Filter.Eventually.of_forall fun f' => hy0.trans_le ENNReal.toReal_nonneg
  · push_neg at hy0
    have h1 : ENNReal.ofReal y < absThetaInt B m ((pureS g f).1 ∘ coord ε) :=
      (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy
    filter_upwards [hN f _ h1] with f' hf'
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hf'

end GlobalTheory.AbsThetaSemi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedHyperbolicPlaneRescaleRebasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped Matrix nonZeroDivisors

theorem _root_.GlobalTheory.T.adaptedHyperbolicPlane_rescale_rebasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B₀ B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E), B.emb = B₀.emb → ∀ (n n₁ : ℕ) (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁)
    (H₀ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁) (i₀ i₁ : ℕ), i₀ < i₁ → i₁ < n → Y.L.IsFullLattice E → Y₁.L.IsFullLattice E →
    H₀.IsAdapted σ B₀ Y Y₁ i₀ i₁ → ∃ (Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁) (H : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Plane E n n₁),
      Y'.θ = Y.θ ∧ Y₁'.θ = Y₁.θ ∧ (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L (Y'.bas v)) ∧
      (∀ v : B.P, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L (Y₁'.bas v)) ∧
      H.IsAdapted σ B (GlobalTheory.ThK.reS Y Y') (GlobalTheory.ThK.reS Y₁ Y₁') i₀ i₁ := by
  intro F E _ _ _ _ _ σ hcm B₀ B hemb n n₁ Y Y₁ H₀ i₀ i₁ h01 h1n hL hL₁ hH
  classical
  have hss : ∀ a : E, σ (σ a) = a := fun a => by
    let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    apply τ.injective
    rw [hcm.2.2.2 τ, hcm.2.2.2 τ, star_star]
  have fsl : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J (s • a) b = s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J a b := fun J s a b => by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, smul_dotProduct]
  have fsr : ∀ (J : Matrix (Fin n) (Fin n) E) (s : E) (a b : Fin n → E),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b (s • a) = σ s * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ J b a := fun J s a b => by
    have : (fun i => σ ((s • a) i)) = σ s • fun i => σ (a i) := funext fun i => by simp
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hx0 : H₀.x ≠ 0 := by
    intro h; have := hH.xy; rw [h] at this; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form] at this
  have hy0 : H₀.y ≠ 0 := by
    intro h
    have h1 := hH.xy
    have h2 := fsr Y.J 0 H₀.y H₀.x
    rw [zero_smul, map_zero, zero_mul, ← h, h1] at h2
    exact one_ne_zero h2
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.PlaneSkewScale.exists_rescale_primAt F E σ hcm n Y.L hL H₀.x H₀.y hx0 hy0 B.P B.τ
  have hσc : σ c ≠ 0 := fun h => hc0 (by rw [← hss c, h, map_zero])
  set x : Fin n → E := c • H₀.x with hxdef
  set y : Fin n → E := (σ c)⁻¹ • H₀.y with hydef
  have ex : ∀ s : E, (s * c⁻¹) • x = s • H₀.x := fun s => by
    rw [hxdef, smul_smul, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
  have ey : ∀ t : E, (t * σ c) • y = t • H₀.y := fun t => by
    rw [hydef, smul_smul, mul_assoc, mul_inv_cancel₀ hσc, mul_one]
  let 𝔟 : FractionalIdeal (𝓞 E)⁰ E := FractionalIdeal.spanSingleton _ c⁻¹ * H₀.𝔟
  have h𝔟 : ∀ s : E, s ∈ 𝔟 ↔ s • x ∈ Y.L := by
    intro s
    rw [FractionalIdeal.mem_singleton_mul, hxdef, smul_smul]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mul_comm c⁻¹ t, mul_assoc, inv_mul_cancel₀ hc0, mul_one]
      exact (hH.ideal t).1 ht
    · intro h
      refine ⟨s * c, (hH.ideal _).2 h, ?_⟩
      rw [mul_comm s c, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hsplit : ∀ z ∈ Y.L, ∃ (s t : E) (u : Fin n₁ → E), s • x ∈ Y.L ∧ t • y ∈ Y.L ∧ u ∈ Y₁.L ∧
      z = s • x + H₀.ι *ᵥ u + t • y := by
    intro z hz
    obtain ⟨s, t, u, hs, ht, hu, rfl⟩ := hH.split z hz
    exact ⟨s * c⁻¹, t * σ c, u, by rw [ex]; exact hs, by rw [ey]; exact ht, hu, by rw [ex, ey]⟩
  haveI : Y₁.L.IsFullLattice E := hL₁
  have hcomap : Y.L.comap ((Matrix.mulVecLin H₀.ι).restrictScalars (𝓞 E)) = Y₁.L :=
    Submodule.ext fun u => (hH.low u).symm
  have hb₁ : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y₁.L β := fun v =>
    GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Y₁.L hcm
  choose β₁ hβ₁ using hb₁
  let bas₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GL (Fin n₁) (Fv F v) := fun v => if h : v ∈ B.P then β₁ ⟨v, h⟩ else Y₁.bas v
  have hbas₁ : ∀ v : B.P, bas₁ v = β₁ v := fun v => by simp only [bas₁, dif_pos v.2]
  have hb : ∀ v : B.P, ∃ β : GL (Fin n) (Fv F v), (∀ i : Fin n, (i.1 = i₀ → ∀ r, β.1 r i = B.τ v (x r)) ∧
      (i.1 = i₁ → ∀ r, β.1 r i = B.τ v (y r)) ∧
      ∀ j : Fin n₁, i.1 = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.skip i₀ i₁ j → ∀ r, β.1 r i = (H₀.ι.map (B.τ v) * (β₁ v).1) r j) ∧
      GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Y.L β := fun v =>
    GlobalTheory.PlaneBasis.exists_isSplitBasis_plane F E σ hcm v (B.τ v) n n₁ Y.L x y H₀.ι (β₁ v) i₀ i₁ hH.rank h01 h1n hL
      (fun z hz => by
        obtain ⟨s, t, u, hs, ht, hu, hz'⟩ := hsplit z hz
        exact ⟨s, t, u, hs, ht, (hH.low u).1 hu, hz'⟩)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).1)
      (by simp only [GlobalTheory.AdelicU.valued_apply_eq_valuation]; exact (hc v).2)
      (by rw [hcomap]; exact hβ₁ v)
  choose β hβ using hb
  let bas : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), GL (Fin n) (Fv F v) := fun v => if h : v ∈ B.P then β ⟨v, h⟩ else Y.bas v
  have hbas : ∀ v : B.P, bas v = β v := fun v => by simp only [bas, dif_pos v.2]
  let Y' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n := ⟨Y.J, Y.L, Y.θ, bas⟩
  let Y₁' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n₁ := ⟨Y₁.J, Y₁.L, Y₁.θ, bas₁⟩
  refine ⟨Y', Y₁', ⟨x, y, H₀.ι, 𝔟⟩, rfl, rfl, fun v => ?_, fun v => ?_, ?_⟩
  · rw [show Y'.bas v = β v from hbas v]; exact (hβ v).2
  · rw [show Y₁'.bas v = β₁ v from hbas₁ v]; exact hβ₁ v
  · exact
      { rank := hH.rank
        xx := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x x = 0
          rw [hxdef, fsl, fsr, hH.xx, mul_zero, mul_zero]
        yy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J y y = 0
          rw [hydef, fsl, fsr, hH.yy, mul_zero, mul_zero]
        xy := by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J x y = 1
          rw [hxdef, hydef, fsl, fsr, hH.xy, map_inv₀, hss, mul_one, mul_inv_cancel₀ hc0]
        orth := fun u => by
          show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) x = 0 ∧ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form σ Y.J (H₀.ι *ᵥ u) y = 0
          rw [hxdef, hydef, fsr, fsr, (hH.orth u).1, (hH.orth u).2, mul_zero, mul_zero]
          exact ⟨rfl, rfl⟩
        gram := hH.gram
        low := hH.low
        split := hsplit
        ideal := h𝔟
        cartan := fun w => by
          obtain ⟨hθι, c₀, hc₀, he⟩ := hH.cartan w
          rw [hemb]
          refine ⟨hθι, (B₀.emb w).1 (σ c)⁻¹ * c₀ * ((B₀.emb w).1 c)⁻¹, ?_, ?_⟩
          · have h1 : (B₀.emb w).1 (σ c)⁻¹ ≠ 0 := (map_ne_zero _).2 (inv_ne_zero hσc)
            have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            exact mul_ne_zero (mul_ne_zero h1 hc₀) (inv_ne_zero h2)
          · have h2 : (B₀.emb w).1 c ≠ 0 := (map_ne_zero _).2 hc0
            have hx' : (fun i => (B₀.emb w).1 (x i)) = (B₀.emb w).1 c • fun i => (B₀.emb w).1 (H₀.x i) :=
              funext fun i => by simp [hxdef]
            have hy' : (fun i => (B₀.emb w).1 (y i)) = (B₀.emb w).1 (σ c)⁻¹ • fun i => (B₀.emb w).1 (H₀.y i) :=
              funext fun i => by simp [hydef]
            show (fun i => (B₀.emb w).1 (y i)) = _ • Y.θ w *ᵥ fun i => (B₀.emb w).1 (x i)
            rw [hx', hy', he, Matrix.mulVec_smul, smul_smul, smul_smul]
            congr 1
            field_simp
        bas := fun v i => by
          rw [show (GlobalTheory.ThK.reS Y Y').bas v = β v from hbas v, show (GlobalTheory.ThK.reS Y₁ Y₁').bas v = β₁ v from hbas₁ v]
          exact (hβ v).1 i }

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrix
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HatPullback

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mulVec_tmul (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    GlobalTheory.UnRep.fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [GlobalTheory.UnRep.fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem fm_mul' (A B : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.fm F (A * B) = GlobalTheory.UnRep.fm F A * GlobalTheory.UnRep.fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

theorem fm_one' : GlobalTheory.UnRep.fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem fm_mulVec_mem_hat (M : Matrix (Fin n) (Fin n) E) {L L' : Set (Fin n → E)}
    (h : ∀ x ∈ L, M *ᵥ x ∈ L') {w : Fin n → GlobalTheory.AdLat.RA F E} (hw : w ∈ GlobalTheory.AdLat.hat F L) :
    GlobalTheory.UnRep.fm F M *ᵥ w ∈ GlobalTheory.AdLat.hat F L' := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [fm_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨a, ha, M *ᵥ x, h x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (A : GL (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Fin n → GlobalTheory.AdLat.RA F E),
    GlobalTheory.UnRep.fm F A.1 *ᵥ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      w ∈ GlobalTheory.AdLat.hat F ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n A Λ w
  have hmem : ∀ x : Fin n → E, x ∈ ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ A.1 *ᵥ x ∈ Λ := fun x => by
    simp [Matrix.mulVecLin_apply]
  constructor
  · intro hw
    have h2 := fm_mulVec_mem_hat (F := F) (A⁻¹).1
      (L := (Λ : Set (Fin n → E)))
      (L' := ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
        Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))
      (fun y hy => by
        rw [hmem, Matrix.mulVec_mulVec, A.mul_inv, Matrix.one_mulVec]
        exact hy) hw
    rwa [Matrix.mulVec_mulVec, ← fm_mul', A.inv_mul, fm_one', Matrix.one_mulVec] at h2
  · intro hw
    exact fm_mulVec_mem_hat (F := F) A.1 (fun x hx => (hmem x).1 hx) hw

end GlobalTheory.HatPullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped GlobalTheory.VacAny

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (γ : W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) γ →
    ∀ φ : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (co.rho ψ γ) φ
      (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo co v γ) φ) := by
  first | exact @GlobalTheory.VacBridge.rho_acts_locCo | exact GlobalTheory.VacBridge.rho_acts_locCo | (intros; apply GlobalTheory.VacBridge.rho_acts_locCo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixGluedAtInertPlacePropertiesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixGluedAtInertPlace_properties : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ P Q : Matrix ι ι (w.adicCompletion E), GlobalTheory.InertBigCell.glueW hw (P * Q) = GlobalTheory.InertBigCell.glueW hw P * GlobalTheory.InertBigCell.glueW hw Q) ∧
  GlobalTheory.InertBigCell.glueW hw (1 : Matrix ι ι (w.adicCompletion E)) = 1 ∧
  Function.Injective (GlobalTheory.InertBigCell.glueW hw (ι := ι)) ∧
  (∀ P : Matrix ι ι (w.adicCompletion E), At (evFin F v) (GlobalTheory.InertBigCell.glueW hw P - 1)) ∧
  (∀ M : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (M - 1) → ∃ P, GlobalTheory.InertBigCell.glueW hw P = M) ∧
  (∀ (P : Matrix ι ι (w.adicCompletion E)) (u : ι → w.adicCompletion E),
    GlobalTheory.InertBigCell.glueW hw P *ᵥ (fun i => GlobalTheory.InertBigCell.iotaW hw (u i)) = fun i => GlobalTheory.InertBigCell.iotaW hw ((P *ᵥ u) i)) := by
  first | exact @GlobalTheory.InertBigCell.glueW_props | exact GlobalTheory.InertBigCell.glueW_props | (intros; apply GlobalTheory.InertBigCell.glueW_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixTrivialOffInertPlaceUnitaryAtPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrix_trivial_off_inertPlace_unitary_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {v : Pl (F := F)}
    {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w) {ι : Type} [Fintype ι] [DecidableEq ι],
  (∀ (J : Matrix ι ι E) (P : Matrix ι ι (w.adicCompletion E)),
    (GlobalTheory.InertBigCell.glueW hw P)ᵀ * incM F J * (GlobalTheory.InertBigCell.glueW hw P).map (cA σ) = incM F J ↔
      Pᵀ * J.map (algebraMap E (w.adicCompletion E)) * P.map (GlobalTheory.InertBigCell.conjW σ hw) = J.map (algebraMap E (w.adicCompletion E))) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E), P * diagCols ι = diagCols ι →
    GlobalTheory.InertBigCell.glueW hw P * (diagCols ι : Matrix (ι ⊕ ι) ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = diagCols ι) ∧
  (∀ P : Matrix (ι ⊕ ι) (ι ⊕ ι) (w.adicCompletion E),
    ⅟(2 : AF F) • ((GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₁₂ +
      (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₁ + (GlobalTheory.InertBigCell.glueW hw P).toBlocks₂₂) =
    GlobalTheory.InertBigCell.glueW hw ((2 : w.adicCompletion E)⁻¹ • (P.toBlocks₁₁ + P.toBlocks₁₂ + P.toBlocks₂₁ + P.toBlocks₂₂))) := by
  first | exact @GlobalTheory.InertBigCell.glueW_read_at_place | exact GlobalTheory.InertBigCell.glueW_read_at_place | (intros; apply GlobalTheory.InertBigCell.glueW_read_at_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingMapHermitianNormLeProdBoundsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.branchingMap_hermitianNorm_le_prod_bounds : ∀ {ι : Type} [Fintype ι] {n N : ℕ} (hN : N = n + 1) (Λ : ι → DomWeight N) (σ : ι → DomWeight n),
    (∀ τ, Formalism.L2.Col.Br.Interlace hN (Λ τ) (σ τ)) → (∀ τ, Formalism.L2.Col.Br.SameShift (Λ τ) (σ τ)) → ∀ (x : VV ℂ Λ),
    (pairK σ (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) (Formalism.L2.Col.Br.brStd hN Λ σ x) (Formalism.L2.Col.Br.brStd hN Λ σ x)).re ≤
      (∏ τ, Formalism.MainNotions.PrimeDegreeVariant.brBd hN.symm (Λ τ) (σ τ) ^ 2) * (pairK Λ (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) x x).re := by
  first | exact @GlobalTheory.BranchNormBound.brStd_norm_le | exact GlobalTheory.BranchNormBound.brStd_norm_le | (intros; apply GlobalTheory.BranchNormBound.brStd_norm_le <;> assumption)
end

