module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellShellIsOpenCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryPlaceSplit

theorem mix_mul {S A : Type} [CommRing S] [Ring A] [Algebra S A] {e : S} (he : e * e = e) (x y z w : A) :
    (e • x + (1 - e) • y) * (e • z + (1 - e) • w) = e • (x * z) + (1 - e) • (y * w) := by
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h0' : (1 - e) * e = 0 := by rw [mul_comm, h0]
  have h1 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h0, sub_zero]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, he, h0, h0', h1, zero_smul, add_zero,
    zero_add]

variable {F : Type} [Field F] [NumberField F]

def idemAt (v : Pl (F := F)) : AF F := LinearMap.inr F (Ainf F) (Af F) (singleFin v 1)

theorem evFin_idemAt (v : Pl (F := F)) : evFin F v (idemAt v) = 1 := evalV_singleFin_self v 1

theorem idemAt_mul_self (v : Pl (F := F)) : idemAt v * idemAt v = idemAt v := by
  refine Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero 0) ?_
  change singleFin v 1 * singleFin v 1 = singleFin v 1
  rw [← singleFin_mul, one_mul]

theorem mul_idemAt_of_evFin (v : Pl (F := F)) {u : AF F} (hu : evFin F v u = 0) : u * idemAt v = 0 := by
  refine Prod.ext (show u.1 * (0 : Ainf F) = 0 from mul_zero _) ?_
  change u.2 * singleFin v 1 = 0
  refine af_ext fun w => ?_
  rw [map_mul, map_zero]
  by_cases h : w = v
  · subst h
    have : evalV F w u.2 = 0 := hu
    rw [this, zero_mul]
  · rw [evalV_singleFin_ne h, mul_zero]

end GlobalTheory.UnitaryPlaceSplit

end

namespace GlobalTheory.UnitaryPlaceSplit

open Matrix

theorem exists_split_at (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (g : UA σ J) :
    ∃ g₁ g₂ : UA σ J, g = g₁ * g₂ ∧ At (evFin F v) (mat g₁ - 1) ∧
      ∀ u : AF F, At (evFin F v) u → u • (mat g₂ - 1) = 0 := by
  have hee : idemAt v * idemAt v = idemAt v := idemAt_mul_self v
  set e : AF F := idemAt v with he_def
  set G : Matrix (Fin n) (Fin n) (AE F E) := ((g.1 : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
    with hG
  set Gi : Matrix (Fin n) (Fin n) (AE F E) :=
    ((g.1⁻¹ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) with hGi
  have hGGi : G * Gi = 1 := Units.mul_inv g.1
  have hGiG : Gi * G = 1 := Units.inv_mul g.1
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  set M : Matrix (Fin n) (Fin n) (AE F E) := e • G + (1 - e) • 1 with hM
  set N : Matrix (Fin n) (Fin n) (AE F E) := e • Gi + (1 - e) • 1 with hN
  have hMN : M * N = 1 := by rw [hM, hN, mix_mul hee, hGGi, mul_one, ← split]
  have hNM : N * M = 1 := by rw [hM, hN, mix_mul hee, hGiG, mul_one, ← split]
  let g1gl : GL (Fin n) (AE F E) := ⟨M, N, hMN, hNM⟩
  have hmem : g1gl ∈ UG (cA σ) (incM F J) := by
    change Mᵀ * incM F J * M.map (cA σ) = incM F J
    have hg : Gᵀ * incM F J * G.map (cA σ) = incM F J := g.2
    have hT : Mᵀ = e • Gᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [hM, transpose_add, transpose_smul, transpose_smul, transpose_one]
    have hc : M.map (cA σ) = e • G.map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [← AlgHom.mapMatrix_apply, hM, map_add (f := _), map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
    rw [hT, hc, split (incM F J), mix_mul hee, mix_mul hee, hg, one_mul, mul_one]
  let g₁ : UA σ J := ⟨g1gl, hmem⟩
  have hm1 : mat g₁ - 1 = e • (G - 1) := by
    change M - 1 = _
    rw [hM, smul_sub, sub_smul, one_smul]
    abel
  have hm2 : mat (g₁⁻¹ * g) - 1 = (1 - e) • (G - 1) := by
    change N * G - 1 = _
    conv_lhs => rw [split G]
    rw [hN, mix_mul hee, hGiG, one_mul, smul_sub, sub_smul (1 : AF F) e (1 : Matrix (Fin n) (Fin n) (AE F E)), one_smul]
    abel
  refine ⟨g₁, g₁⁻¹ * g, (mul_inv_cancel_left g₁ g).symm, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hm1, smul_smul, mul_idemAt_of_evFin v hu, zero_smul]
  · have h1 : (1 - e) • u = 0 := hu (1 - e) (by rw [map_sub, map_one, he_def, evFin_idemAt, sub_self])
    rw [hm2, smul_smul, mul_comm, ← smul_eq_mul, h1, zero_smul]

end GlobalTheory.UnitaryPlaceSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryWeylCellHaarRightTranslateInvariant
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory.WeylCell.WeylUnipotentShell

theorem cellU_haar_rightInv : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
      μ ((KU σ n).subgroupOf (cellU y)) = 1 →
    ∀ p : cellU y,
      (∀ F : GU σ n → ℂ, ∫ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫ u : cellU y, F (u : GU σ n) ∂μ) ∧
      (∀ F : GU σ n → ENNReal,
        ∫⁻ u : cellU y, F ((u * p : cellU y) : GU σ n) ∂μ = ∫⁻ u : cellU y, F (u : GU σ n) ∂μ) := by
  intro L _ _ _ ϖ σ q hU n k hk hn y hy hw _ _ μ _ _ p
  have hS := _root_.GlobalTheory.WeylCell.WeylUnipotentShell.shellU_open_compact_subgroup L ϖ σ q hU n k hk hn y hy hw
  haveI : LocallyCompactSpace (cellU y) :=
    (hS.1 0).2.1.locallyCompactSpace_of_mem_nhds_of_group ((hS.1 0).1.mem_nhds (hS.1 0).2.2.1)
  let e : cellU y ≃ᵐ cellU y := (Homeomorph.mulRight p).toMeasurableEquiv
  have he : ∀ u, e u = u * p := fun _ => rfl
  let ν : Measure (cellU y) := μ.map e
  haveI : ν.IsMulLeftInvariant := by
    have : ν = μ.map (fun x => x * p) := rfl
    rw [this]; exact isMulLeftInvariant_map_mul_right p
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun K hK => ?_⟩
    show μ.map e K < ⊤
    rw [e.map_apply]
    exact ((hK.image (Homeomorph.mulRight p).symm.continuous)).measure_lt_top.trans_le' (by
      apply le_of_eq; congr 1; ext x; simp [e, Homeomorph.mulRight, Equiv.mulRight])

  set j : ℕ := depthU k (p : GU σ n)
  have hp : p ∈ shellU k y (j : ℤ) := mem_shellU_depth k y p
  obtain ⟨ho, hc, h1, hmul, hinv⟩ := hS.1 (j : ℤ)
  have hνS : ν (shellU k y j) = 1 * μ (shellU k y j) := by
    rw [one_mul]
    show μ.map e _ = _
    rw [e.map_apply]
    congr 1
    ext u
    simp only [Set.mem_preimage, he]
    constructor
    · intro h
      simpa using hmul _ _ h (hinv p hp)
    · intro h; exact hmul _ _ h hp
  have hνμ : ν = μ := by
    have := _root_.GlobalTheory.haar_unique_of_sigmaCompact_normalised (cellU y) μ ν (fun i : ℕ => shellU k y (i : ℤ))
      (fun i => ⟨(hS.1 i).2.1, (hS.1 i).1.measurableSet⟩)
      (Set.eq_univ_of_forall fun u => Set.mem_iUnion.2 ⟨_, mem_shellU_depth k y u⟩)
      _ 1 ho hc ⟨1, h1⟩ hνS
    rwa [one_smul] at this
  have hmp : MeasurePreserving e μ μ := ⟨e.measurable, hνμ⟩
  refine ⟨fun F => ?_, fun F => ?_⟩
  · exact hmp.integral_comp' (g := fun u : cellU y => F (u : GU σ n))
  · exact hmp.lintegral_comp_emb e.measurableEmbedding (fun u : cellU y => F (u : GU σ n))

end GlobalTheory.WeylCell.WeylUnipotentShell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacTheta
section
noncomputable section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG)

namespace GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ}

structure Frame (P : Pair D cc δ t0 Q) where

  A : HSp D

  B : HSp D
  rkA : A.rank = P.a
  rkB : B.rank = P.d

  ιA : Formalism.MainNotions.StandardLatticesGL3.GA D P.a →* GA D A

  ιB : Formalism.MainNotions.StandardLatticesGL3.GA D P.d →* GA D B

  KA : Subgroup (GL (Fin A.rank) (Lev.EAf D))

  KB : Subgroup (GL (Fin B.rank) (Lev.EAf D))

  m : Measure (GA D A)

  mH : Measure (GA D B)

structure IsFrame (P : Pair D cc δ t0 Q) (Y : Frame P) : Prop where
  gramA : Y.A.gram = 1
  gramB : Y.B.gram = 1
  defA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.A
  defB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace Y.B
  injA : Function.Injective Y.ιA
  injB : Function.Injective Y.ιB
  rangeA : Y.ιA.range = GfC Y.A
  rangeB : Y.ιB.range = GfC Y.B
  ratA : ∀ x, (∃ γ ∈ GQ Y.A, finHom Y.A γ = finHom Y.A (Y.ιA x)) ↔ x ∈ ratG D P.a
  ratB : ∀ h, (∃ γ ∈ GQ Y.B, finHom Y.B γ = finHom Y.B (Y.ιB h)) ↔ h ∈ ratG D P.d
  levA : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.A Y.KA
  levB : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel Y.B Y.KB
  levA_iff : ∀ x, Lev.finE Y.A (Y.ιA x) ∈ Y.KA ↔ x ∈ intG D P.a
  levB_iff : ∀ h, Lev.finE Y.B (Y.ιB h) ∈ Y.KB ↔ h ∈ P.J
  haarA : Y.m.IsHaarMeasure
  haarB : Y.mH.IsHaarMeasure
  measA : ∃ 𝓕, Links.IsMeasDef Y.A Y.KA Y.m 𝓕
  measB : ∃ 𝓕, Links.IsMeasDef Y.B Y.KB Y.mH 𝓕

structure Data (P : Pair D cc δ t0 Q) extends Frame P where

  ψ : AddChar (AF D.host.F) ℂ

  θ : InfFam D

  χA : (AE D)ˣ →* Circle

  χB : (AE D)ˣ →* Circle

  om : GlobalTheory.Core.Rk.IP.WRep A B

  vac : WO A B → ℂ

  c₁ : ℂ

namespace Data

variable {P : Pair D cc δ t0 Q} (X : Data P)

def var (k : Formalism.MainNotions.GL3Theta.Idx D P.a P.d) : FVar D X.B.rank X.A.rank :=
  (k.1, Fin.cast X.rkB.symm k.2.1, Fin.cast X.rkA.symm k.2.2)

def fock (T : Tup D P.a P.d P.n) : WO X.A X.B → ℂ :=
  pureTensorL (aPlusAll (heisO X.ψ X.A X.B) X.θ (fun _ => cplxO 1 1) (fun _ => 1) (fun _ => 1)) X.vac
    (MvPolynomial.rename X.var (minorPol D T))

def lift (T : Tup D P.a P.d P.n) : GA D X.B → ℂ := GlobalTheory.Core.Rk.IP.up X.om X.m (X.fock T) 1

end Data

structure IsWeilOf (P : Pair D cc δ t0 Q) (X : Data P) : Prop where
  inf : IsInfFam X.θ
  weil : IsWeilDatumO X.ψ X.A X.B X.χA X.χB X.om
  vac_theta : IsThetaFunO X.ψ X.A X.B X.vac
  vac_fock : ∀ τ, IsFockVacAt (heisO X.ψ X.A X.B) X.θ τ (cplxO 1 1) X.vac
  c₁_ne : X.c₁ ≠ 0
  ker : ∀ x h T, thetaKO X.om (X.ιA x) (X.ιB h) (X.fock T) = X.c₁ * P.term x h T

  fixA : ∀ k ∈ intG D P.a, ∀ T, X.om (X.ιA k, 1) (X.fock T) = X.fock T

  eigB : ∀ j ∈ P.J, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ T, X.om (1, X.ιB j) (X.fock T) = c • X.fock T

  infB : ∀ τ, HasInfExp D X.χB τ (-((P.n τ : ℚ) + (P.d : ℚ) / 2))

def IsDict (P : Pair D cc δ t0 Q) (X : Data P) : Prop := IsFrame P X.toFrame ∧ IsWeilOf P X

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationOneUnitsNhds
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

open ValuativeRel

theorem units_valuation_eq_one_mem_nhds_one {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    {x : kˣ | ValuativeRel.valuation k (x : k) = 1} ∈ 𝓝 (1 : kˣ) := by
  have hset : {x : kˣ | ValuativeRel.valuation k (x : k) = 1} =
      (fun x : kˣ => (x : k)) ⁻¹' (𝒪[k] : Set k) ∩
        (fun x : kˣ => ((x⁻¹ : kˣ) : k)) ⁻¹' (𝒪[k] : Set k) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe,
      Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_le_one₀ (by simp [zero_lt_iff])]
    exact le_antisymm_iff
  have hopen : IsOpen {x : kˣ | ValuativeRel.valuation k (x : k) = 1} := by
    rw [hset]
    exact ((Valuation.isOpen_integer (R := k)).preimage Units.continuous_val).inter
      ((Valuation.isOpen_integer (R := k)).preimage Units.continuous_coe_inv)
  exact hopen.mem_nhds (by simp)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2
section
noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open IsDedekindDomain

namespace GlobalTheory.ArchimedeanL2

theorem lintegral_eq_of_fibres {Z X Y : Type} [AddGroup Z] [TopologicalSpace Z] [IsTopologicalAddGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] [AddGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    [AddGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [MeasurableSpace Y] [BorelSpace Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (e : Z ≃ₜ+ X × Y) (μ : Measure Z) [μ.IsAddHaarMeasure]
    (ν : Measure X) [ν.IsAddHaarMeasure] {G G' : X × Y → ENNReal} (hG : Measurable G) (hG' : Measurable G')
    (h : ∀ y, ∫⁻ x, G (x, y) ∂ν = ∫⁻ x, G' (x, y) ∂ν) : ∫⁻ z, G (e z) ∂μ = ∫⁻ z, G' (e z) ∂μ := by
  have he : Measurable e := e.continuous.measurable
  let ρ : Measure Y := Measure.addHaar
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  haveI : (ν.prod ρ).IsAddHaarMeasure := inferInstance
  rw [← lintegral_map hG he, ← lintegral_map hG' he, Measure.isAddLeftInvariant_eq_smul (μ.map e) (ν.prod ρ),
    lintegral_smul_measure, lintegral_smul_measure, lintegral_prod_symm _ hG.aemeasurable,
    lintegral_prod_symm _ hG'.aemeasurable]
  simp only [h]

theorem lintegral_sq_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (ν : Measure V) [ν.IsAddHaarMeasure] (g : SchwartzMap V ℂ) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (g x) * g x ∂ν).re := by
  have hi : Integrable (fun x => ‖g x‖ ^ 2) ν := (g.memLp 2 ν).integrable_norm_pow (by norm_num)
  have h1 : ∀ x, star (g x) * g x = ((‖g x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  rw [integral_complex_ofReal, Complex.ofReal_re,
    ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

variable {F : Type} [Field F] [NumberField F]

theorem cont_toMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  change Continuous fun x : InfiniteAdeleRing F =>
    ((fun (v : {w : InfinitePlace F // w.IsReal}) => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
     (fun (v : {w : InfinitePlace F // w.IsComplex}) => InfinitePlace.Completion.extensionEmbedding v.1 (x v)))
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)

theorem cont_ofMixed : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm


variable (F) in
def splitEquiv (κ : Type) : (κ → AF F) ≃ₜ+ (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) where
  toFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  invFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  left_inv x := funext fun i => Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl
  right_inv p := Prod.ext (funext fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply _) rfl
  map_add' x y := Prod.ext (funext fun i => map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x i).1 (y i).1) rfl
  continuous_toFun := (continuous_pi fun i => cont_toMixed.comp (continuous_fst.comp (continuous_apply i))).prodMk
    (continuous_pi fun i => continuous_snd.comp (continuous_apply i))
  continuous_invFun := continuous_pi fun i =>
    (cont_ofMixed.comp ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem lintegral_arch_eq : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : SInf F κ →ₗ[ℂ] SInf F κ) (Ω : Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ (f : SInf F κ) (h : (κ → Af F) → ℂ), Ω (pureA F f h) = pureA F (L f) h) →
    (∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
      ∫ x, star (L f₁ x) * L f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) →
    ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ schA F κ, ∫⁻ x, ‖Ω φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ L Ω hΩ hL μ hμ φ hφ
  classical
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI : MeasurableSpace (κ → Af F) := borel _
  haveI : BorelSpace (κ → Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (Af F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨n, c, g, rfl⟩ := Submodule.mem_span_set'.1 hφ
  choose f h hh hg using fun i => (g i).2
  let ν : Measure (κ → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hB : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  have hν : ν.IsAddHaarMeasure := inferInstance
  have hsq : ∀ u : SInf F κ, ∫⁻ x, ‖u x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ x, star (u x) * u x ∂ν).re := fun u =>
    @lintegral_sq_eq (κ → mixedEmbedding.mixedSpace F) _ _ _ _ hB ν hν u
  haveI : OpensMeasurableSpace ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :=
    (Prod.borelSpace (α := κ → mixedEmbedding.mixedSpace F) (β := κ → Af F)).opensMeasurable
  have hm : ∀ u : Fin n → SInf F κ, Measurable fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → Af F) =>
      ‖∑ i, c i * (u i p.1 * h i p.2)‖ₑ ^ 2 := fun u =>
    (continuous_finsetSum _ fun i _ => continuous_const.mul
      (((u i).continuous.comp continuous_fst).mul ((hh i).1.continuous.comp continuous_snd))).measurable.enorm.pow_const 2
  have hs : ∀ (u : Fin n → SInf F κ) (y : κ → Af F) (x : κ → mixedEmbedding.mixedSpace F),
      ∑ i, c i * (u i x * h i y) = (∑ i, (c i * h i y) • u i) x := fun u y x => by
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_apply, smul_eq_mul]; ring
  have key := lintegral_eq_of_fibres (splitEquiv F κ) μ ν (hm fun i => L (f i)) (hm f) fun y => by
    simp only [hs]
    have e : ∑ i, (c i * h i y) • L (f i) = L (∑ i, (c i * h i y) • f i) := by simp only [map_sum, map_smul]
    rw [e, hsq, hsq, hL ν hν]
  have e1 : Ω (∑ i, c i • (g i : (κ → AF F) → ℂ)) = ∑ i, c i • pureA F (L (f i)) (h i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hg, hΩ]
  rw [e1]
  simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact key

end GlobalTheory.ArchimedeanL2
end
end

