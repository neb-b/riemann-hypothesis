module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1692
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1544
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1558
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1691
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnitStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_norm_one_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (χ : Chr F E) (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ), At (evFin F v) ((z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) - 1) →
    piW (τ.comp σ) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) = 1 → chrW χ τ (Units.map (piW τ).toMonoidHom z) = Circle.toUnits (χ z) := by
  first | exact @GlobalTheory.ChrLocal.chrW_piW_eq | exact GlobalTheory.ChrLocal.chrW_piW_eq | (intros; apply GlobalTheory.ChrLocal.chrW_piW_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierInversionUpToConstant
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.FourierLocInv

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem inversion_circle [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1)
    (κ : Type) [Fintype κ] (μ : Measure (κ → k)) [μ.IsAddHaarMeasure] :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → k), ∀ a : κ → k,
      ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ = d * φ (-a) := by
  classical
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ := (GlobalTheory.SplitWeil.selfDual_measure k ψ hc h1).1
  haveI := hν.1
  set m : Measure (κ → k) := Measure.pi fun _ => ν with hm
  have hμ : μ = μ.addHaarScalarFactor m • m := Measure.isAddLeftInvariant_eq_smul μ m
  set r := μ.addHaarScalarFactor m with hr_def
  have hr : r ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμ
    exact NeZero.ne μ hμ
  have hr' : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr
  refine ⟨((r : ℝ) : ℂ) ^ 2, pow_ne_zero 2 hr', fun φ hφ a => ?_⟩
  have hg : (fun x => φ (x + -a)) ∈ SB (κ → k) :=
    ⟨hφ.1.comp_continuous (Homeomorph.addRight (-a)).continuous, hφ.2.comp_homeomorph (Homeomorph.addRight (-a))⟩
  have key := (GlobalTheory.SplitWeil.FourierPi.fourier_pi k κ ψ hc h1 ν hν _ hg).2
  have hinner : ∀ y, ∫ x, φ (x + -a) * (ψ (x ⬝ᵥ y) : ℂ) ∂m
      = (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) := by
    intro y
    rw [GlobalTheory.FourierLocBij.translate_fourier, neg_dotProduct, neg_neg, dotProduct_comm a y, mul_comm]
  have key' : ∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ) ∂m = φ (-a) := by
    refine Eq.trans ?_ (key.trans (congrArg φ (zero_add (-a))))
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact (hinner y).symm
  have hsm : ∀ G : (κ → k) → ℂ, ∫ y, G y ∂μ = ((r : ℝ) : ℂ) * ∫ y, G y ∂m := by
    intro G
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  have hfun : (fun y => (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ)) =
      fun y => ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) := by
    funext y
    rw [hsm, mul_assoc]
  rw [show (∫ y, (∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂μ) * (ψ (y ⬝ᵥ a) : ℂ) ∂μ) =
      ∫ y, ((r : ℝ) : ℂ) * ((∫ x, φ x * (ψ (x ⬝ᵥ y) : ℂ) ∂m) * (ψ (y ⬝ᵥ a) : ℂ)) ∂μ from congrArg _ hfun,
    integral_const_mul, hsm, key']
  ring

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem fourier_inversion : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (χ : AddChar (Fv F v) ℂ), Continuous χ → (∀ t, ‖χ t‖ = 1) →
    χ ≠ 1 → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)]
    (μ : Measure (κ → Fv F v)) [μ.IsAddHaarMeasure], ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ∈ SB (κ → Fv F v), ∀ a : κ → Fv F v,
      ∫ y, (∫ x, φ x * χ (x ⬝ᵥ y) ∂μ) * χ (y ⬝ᵥ a) ∂μ = d * φ (-a) := by
  intro F _ _ v χ hc hn h1 κ _ inst _ μ _
  letI : MeasurableSpace (Fv F v) := borel _
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := GlobalTheory.SplitWeil.secondCountable (Fv F v)
  have e : inst = MeasurableSpace.pi := by
    rw [BorelSpace.measurable_eq (α := κ → Fv F v)]
    exact (BorelSpace.measurable_eq (α := κ → Fv F v) (self := Pi.borelSpace)).symm
  subst e
  have hcont : Continuous (GlobalTheory.FourierLocBij.toCircle χ hn) := Continuous.subtype_mk hc _
  have hne : GlobalTheory.FourierLocBij.toCircle χ hn ≠ 1 := by
    intro h
    apply h1
    ext t
    simpa [GlobalTheory.FourierLocBij.coe_toCircle] using
      congrArg (fun ψ : AddChar (Fv F v) Circle => ((ψ t : Circle) : ℂ)) h
  exact inversion_circle (GlobalTheory.FourierLocBij.toCircle χ hn) hcont hne κ μ

end GlobalTheory.FourierLocInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeHermitianSkew
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SplitTraceForm
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_cA {σ : E →ₐ[F] E} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ w) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ) w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem piW_inclR {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} (τ : E →ₐ[F] Fv F v) (e : E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ (inclR (F := F) (AF F) e) = τ e := by
  change evFin F v 1 * τ e = τ e
  simp

theorem sum_four_fintype_permute {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β] (f : α → β → α → β → R) :
    ∑ a, ∑ b, ∑ c, ∑ e, f a b c e = ∑ c, ∑ e, ∑ b, ∑ a, f a b c e := by
  first
  | exact @_root_.GlobalTheory.FourTermSumReorder.sum_four_reorder
  | exact _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder
  | (apply _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> assumption)
  | (intros; apply _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FourTermSumReorder.sum_four_reorder <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FourTermSumReorder.sum_four_reorder ..)

theorem splitTrace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E},
    IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (t : E →ₐ[F] Fv F v) {n d : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (K : Matrix (Fin d) (Fin d) E), (∀ i j, σ (J j i) = J i j) → (∀ i j, σ (K j i) = -K i j) →
    ∀ (x u : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) x →
    GlobalTheory.AdelicU.evFin F v (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) =
      ∑ i, ∑ j, (x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j * (-(J.map t * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j -
        ∑ i, ∑ j, (-(J.map t * x.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (t.comp σ)) * (K.map t)ᵀ)) i j * (u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW t)) i j := by
  intro F E _ _ _ _ _ σ hcm v t n d J K hJ hK x u hx
  have hzAt : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v)
      ((-1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) * GlobalTheory.WeilM.hTens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F K) x u) := by
    intro a ha
    have h0 : ∀ i j, a • x i j = 0 := fun i j => by
      have := congrFun (congrFun (hx a ha) i) j
      simpa using this
    simp only [GlobalTheory.WeilM.hTens, Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rw [show ∀ (p q r : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), a • ((-1) * (x i j * p * q * r)) = -1 * ((a • x i j) * p * q * r) from
      fun p q r => by simp only [Algebra.smul_def]; ring, h0]
    simp
  show GlobalTheory.AdelicU.evFin F v (Algebra.trace (AF F) _ _) = _
  rw [GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v t _ hzAt, GlobalTheory.LatVac.evFin_liftV]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.WeilM.hTens, map_mul, map_neg, map_one, map_sum, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, piW_cA, piW_inclR,
    GlobalTheory.AdelicU.comp_conj_conj hcm, AlgHom.comp_apply, hJ, hK]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.neg_apply, Finset.mul_sum, Finset.sum_mul]
  rw [sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [sum_four_fintype_permute]
    simp only [neg_mul, mul_neg, one_mul, Finset.sum_mul, Finset.sum_neg_distrib, neg_neg]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun k _ => ?_
    ring
end GlobalTheory.SplitTraceForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorizationStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_norm_unramified_factorization : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (v : Pl (F := F)) (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) (z - 1) →
    At (evFin F v) (Algebra.norm (AF F) z - 1) ∧ evFin F v (Algebra.norm (AF F) z) = piW τ z * piW (τ.comp σ) z := by
  first | exact @GlobalTheory.NormLocSplit.norm_at_split | exact GlobalTheory.NormLocSplit.norm_at_split | (intros; apply GlobalTheory.NormLocSplit.norm_at_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductCompatible
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.EvOnto


open scoped Classical in
theorem ev_surjOn_SB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.SurjOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) →
    ∀ v, ∀ χ ∈ SB (κ → Fv F v), ∃ ψ ∈ SB (κ → Fv F v), ev v ψ = χ := by
  intro F _ _ κ _ e ei ev hSBev hfix he hsurj hne v χ hχ
  obtain ⟨f₀, hf₀⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let Φ₁ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ := fun w => ev w (stdInd F κ w)
  have hstdSB : ∀ w : Pl (F := F), stdInd F κ w ∈ SB (κ → Fv F w) := fun w => GlobalTheory.StdVacuum.indicator_mem_SB w
  have hΦstd : ∀ᶠ w in cofinite, Φ₁ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := hfix
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) ∈ schA F κ := by
    refine GlobalTheory.TensUniq.pure_mem_schA f₀ _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually Φ₁ v χ hΦstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hχ
    · rw [Function.update_of_ne hw]; exact hSBev w _ (hstdSB w)
  obtain ⟨Ψ, hΨ, heΨ⟩ := hsurj hmem
  obtain ⟨T, m, f, φ, hSB, hstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F _ Ψ hΨ
  have hvac : ∀ i, ∀ᶠ w in cofinite, φ i w = stdInd F κ w := by
    intro i
    filter_upwards [T.eventually_cofinite_notMem] with w hT
    exact hstd i w hT
  have hvac' : ∀ i, ∀ᶠ w in cofinite, (fun w => ev w (φ i w)) w =
      Set.indicator {x | ∀ j, x j ∈ w.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [hvac i, hfix] with w h1 h2
    rw [h1]; exact h2
  have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v χ) =
      ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← heΨ, hsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hSB i) (hvac i)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f₀ Φ₁ hΦstd
  choose r hr hrt using fun i => GlobalTheory.PureFactor.exists_rest_factor v (ei (f i)) (fun w => ev w (φ i w)) (hvac' i)
  have hrt' : ∀ i, tens (evFin F v) (ev v (φ i v)) (r i) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun w => ev w (φ i w) := by
    intro i
    rw [hrt i]
    congr 1
    exact Function.update_eq_self v (fun w => ev w (φ i w))
  have hex : ∃ x₀, r₀ x₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ (Function.update Φ₁ v fun _ => 1) = 0 := by
      rw [← hr₀t]
      funext x
      simp [tens, hc]
    have hf : f₀ = 0 := by
      refine GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f₀ _ (fun w => ?_)
        (GlobalTheory.PureFactor.update_eventually Φ₁ v _ hΦstd) h0
      by_cases hw : w = v
      · subst hw
        rw [Function.update_self]
        intro h
        exact one_ne_zero (congrFun h 0)
      · rw [Function.update_of_ne hw]; exact hne w
    exact hf₀ (by rw [hf]; rfl)
  obtain ⟨x₀, hx₀⟩ := hex
  refine ⟨∑ i, (r i x₀ / r₀ x₀) • φ i v, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hSB i v), ?_⟩
  funext y
  let z : κ → AF F := fun j => GlobalTheory.LatVac.liftV v (y j - evFin F v (x₀ j))
  have hz : At (evFin F v) z := by
    intro u hu
    funext j
    exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun j => evFin F v ((x₀ + z) j)) = y := by
    funext j
    rw [Pi.add_apply, map_add (f := _), GlobalTheory.LatVac.evFin_liftV]
    ring
  have key : χ y * r₀ x₀ = ∑ i, ev v (φ i v) y * r i x₀ := by
    have h := congrFun hid (x₀ + z)
    rw [← hr₀t, Finset.sum_apply] at h
    simp only [← hrt', tens, hev, hr₀ x₀ z hz] at h
    rw [h]
    exact Finset.sum_congr rfl fun i _ => by rw [hr i x₀ z hz]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_apply]
  apply mul_right_cancel₀ hx₀
  rw [key, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

end GlobalTheory.EvOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorsProductExtend
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.ArchBij

theorem bijective_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ → Fv F v)) →
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ v) →
    (∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    (∀ v, ev v (stdInd F κ v) ≠ 0) → Function.Bijective ei := by
  intro F _ _ κ _ e ei ev hSB hfix he hbij hne
  have hstdSB : ∀ v, stdInd F κ v ∈ SB (κ → Fv F v) := fun v => GlobalTheory.StdVacuum.indicator_mem_SB v
  have hstd0 : ∀ v, stdInd F κ v ≠ 0 := by
    intro v h0
    have h := congrFun h0 0
    have hm : (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem (v.adicCompletionIntegers F)
    simp only [stdInd, Set.indicator_of_mem hm, Pi.one_apply, Pi.zero_apply] at h
    exact one_ne_zero h
  constructor
  · refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
    have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) ∈ schA F κ :=
      GlobalTheory.TensUniq.pure_mem_schA f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl)
    have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ)) = e 0 := by
      rw [he f (stdInd F κ) hstdSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (stdInd F κ) = 0 :=
      hbij.injOn hmem (schA F κ).zero_mem h1
    exact GlobalTheory.EvInj.eq_zero_of_pure_eq_zero f (stdInd F κ) hstd0 (Filter.Eventually.of_forall fun _ => rfl) h2
  · intro h
    let Φ₁ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ := fun w => ev w (stdInd F κ w)
    have hΦ₁SB : ∀ v, Φ₁ v ∈ SB (κ → Fv F v) := fun v => hSB v _ (hstdSB v)
    have hΦ₁std : ∀ᶠ v in Filter.cofinite,
        Φ₁ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := hfix
    have h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ ∈ schA F κ := GlobalTheory.TensUniq.pure_mem_schA h Φ₁ hΦ₁SB hΦ₁std
    obtain ⟨Ψ, hΨ, heΨ⟩ := hbij.surjOn h₁
    obtain ⟨T, m, f, φ, hφSB, hφstd, hsum⟩ := GlobalTheory.SchADecomp.exists_sum_pure F κ Ψ hΨ
    have hvac : ∀ i, ∀ᶠ v in Filter.cofinite, φ i v = stdInd F κ v := fun i =>
      T.eventually_cofinite_notMem.mono fun v hT => hφstd i v hT
    have hid : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure h Φ₁ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei (f i)) fun v => ev v (φ i v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← heΨ, hsum, map_sum]
      exact Finset.sum_congr rfl fun i _ => he (f i) (φ i) (hφSB i) (hvac i)
    obtain ⟨y, hy⟩ := GlobalTheory.ArchSurj.exists_point_ne_zero Φ₁ hne hΦ₁std
    set c : ℂ := ∏ᶠ v, Φ₁ v (fun j => y j v) with hc
    have hc0 : c ≠ 0 := finprod_induction (fun a : ℂ => a ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hy
    set cs : Fin m → ℂ := fun i => ∏ᶠ v, ev v (φ i v) (fun j => y j v) with hcs
    refine ⟨∑ i, (cs i / c) • f i, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    let a : κ → AF F := fun j => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x j), y j)
    have hI : (fun j => evI F (a j)) = x := by
      funext j
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply (x j)
    have hx : h x * c = ∑ i, ei (f i) x * cs i := by
      have := congrFun hid a
      rw [Finset.sum_apply] at this
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, hI] at this
      exact this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hs : (∑ i, ei ((cs i / c) • f i)) x = ∑ i, (cs i / c) * ei (f i) x := by
      rw [SchwartzMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]; rfl
    rw [hs]
    apply mul_right_cancel₀ hc0
    rw [hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp

end GlobalTheory.ArchBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalProductActsOfAdelicProductActsFirstStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localProduct_acts_of_adelicProduct_acts_first : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (Td : ((κ ⊕ κ' → AF F) → ℂ) → (κ ⊕ κ' → AF F) → ℂ),
    (∀ Φ₁ ∈ schA F κ, ∀ Φ₂ ∈ schA F κ', Td (boxFun Φ₁ Φ₂) = boxFun (T Φ₁) Φ₂) →
    ∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), ∀ (φ₁' : (κ → Fv F v) → ℂ) (Φ' : (κ ⊕ κ' → Fv F v) → ℂ),
      Acts (evFin F v) T φ₁ φ₁' → Acts (evFin F v) Td (boxFun φ₁ φ₂) Φ' → Φ' = boxFun φ₁' φ₂ := by
  first | exact @GlobalTheory.BoxAct.boxFun_acts | exact GlobalTheory.BoxAct.boxFun_acts | (intros; apply GlobalTheory.BoxAct.boxFun_acts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeilOperatorNormalisesSchroedingerOperatorStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localWeilOperator_normalises_schroedingerOperator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (Y : Type) [AddCommGroup Y] (Xm : Y →+ Matrix (Fin a) (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      (∀ y, At (evFin F v) (Xm y)) →
      ∀ ρ : Y → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)),
      (∀ x (φ : SB (Fin a × Fin (a + a') → Fv F v)), Acts (evFin F v) (G.M.co.rho B.ψ (Xm x))
        (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) ((ρ x φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J) (ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v))),
      (∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)) (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ)) →
      ∀ actY : Γ → Y → Y, (∀ g x, actAB (cA σ) (j g) (Xm x) = Xm (actY g x)) →
      ∀ g x, ω g * ρ x = ρ (actY g x) * ω g := by
  first | exact @GlobalTheory.InertLocModel.weil_normalises_schr | exact GlobalTheory.InertLocModel.weil_normalises_schr | (intros; apply GlobalTheory.InertLocModel.weil_normalises_schr <;> assumption)
end

