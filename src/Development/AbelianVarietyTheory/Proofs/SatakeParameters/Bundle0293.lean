module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearModelFourierTransformExchange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LinearModelFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def flat (n r : ℕ) : Matrix (Fin n) (Fin r) k ≃ₜ (Fin n × Fin r → k) where
  toFun z p := z p.1 p.2
  invFun y := Matrix.of (Function.curry y)
  left_inv z := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)
  continuous_invFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)

def flatT (n r : ℕ) : Matrix (Fin r) (Fin n) k ≃ₜ (Fin n × Fin r → k) where
  toFun x p := x p.2 p.1
  invFun y := Matrix.of fun j i => y (i, j)
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := continuous_pi fun p => (continuous_apply p.1).comp (continuous_apply p.2)
  continuous_invFun := continuous_pi fun j => continuous_pi fun i => continuous_apply (i, j)

theorem trace_mul_eq_dotProduct {n r : ℕ} (x : Matrix (Fin r) (Fin n) k) (y : Matrix (Fin n) (Fin r) k) :
    trace (x * y) = flat n r y ⬝ᵥ flatT n r x := by
  simp only [trace, diag, Matrix.mul_apply, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show x j i * y i j = y i j * x j i
  ring

theorem comp_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : Y ≃ₜ X) {f : X → ℂ}
    (hf : f ∈ GlobalTheory.SplitWeil.SB X) : (f ∘ e) ∈ GlobalTheory.SplitWeil.SB Y :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

variable [MeasurableSpace k]

def fou (ψ : AddChar k Circle) (ν : Measure k) (n r : ℕ) (Φ : Matrix (Fin n) (Fin r) k → ℂ)
    (x : Matrix (Fin r) (Fin n) k) : ℂ :=
  ∫ y, Φ y * (ψ (trace (x * y)) : ℂ) ∂(volM ν (Fin n) (Fin r))

variable [BorelSpace k] {ψ : AddChar k Circle} (ν : Measure k) [ν.IsAddHaarMeasure] {n r : ℕ}

theorem fou_eq_pi (Φ : Matrix (Fin n) (Fin r) k → ℂ) (x : Matrix (Fin r) (Fin n) k) :
    fou ψ ν n r Φ x = ∫ z, (Φ ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ flatT n r x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [fou, integral_volM_eq_pi]
  congr 1
  funext z
  rw [trace_mul_eq_dotProduct]
  rfl

theorem integrable_fou (hψ : Continuous ψ) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) (x : Matrix (Fin r) (Fin n) k) :
    Integrable (fun y => f y * (ψ (trace (x * y)) : ℂ)) (volM ν (Fin n) (Fin r)) := by
  haveI := secondCountable k
  letI : MeasurableSpace (Matrix (Fin n) (Fin r) k) := GlobalTheory.SplitWeil.matrixMeasurableSpace
  haveI : BorelSpace (Matrix (Fin n) (Fin r) k) := inferInstanceAs (BorelSpace (Fin n → Fin r → k))
  haveI : (volM ν (Fin n) (Fin r)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : IsFiniteMeasureOnCompacts (volM ν (Fin n) (Fin r)) := inferInstance
  have hc : Continuous fun y : Matrix (Fin n) (Fin r) k => f y * (ψ (trace (x * y)) : ℂ) :=
    hf.1.continuous.mul (continuous_subtype_val.comp
      (hψ.comp ((continuous_const.matrix_mul continuous_id).matrix_trace)))
  exact hc.integrable_of_hasCompactSupport (μ := volM ν (Fin n) (Fin r)) hf.2.mul_right

theorem fou_mem (hψ : Continuous ψ) (h1 : ψ ≠ 1) {f : Matrix (Fin n) (Fin r) k → ℂ}
    (hf : f ∈ SB (Matrix (Fin n) (Fin r) k)) : fou ψ ν n r f ∈ SB (Matrix (Fin r) (Fin n) k) := by
  haveI := secondCountable k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ h1
  have h2 := FourierPi.fourier_mem_SB (Measure.pi fun _ : Fin n × Fin r => ν) hc
    (comp_mem_SB (flat n r).symm hf)
  have h3 : fou ψ ν n r f = (fun y => ∫ z, (f ∘ (flat n r).symm) z * (ψ (z ⬝ᵥ y) : ℂ)
      ∂(Measure.pi fun _ => ν)) ∘ flatT n r := funext fun x => fou_eq_pi ν f x
  rw [h3]
  exact comp_mem_SB _ h2

theorem nabs_det_inv {m : ℕ} (g : GL (Fin m) k) :
    nabs k (Matrix.GeneralLinearGroup.det g⁻¹) = (nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ := by
  simp [nabs, map_inv]

theorem fou_om (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ : Matrix (Fin n) (Fin r) k → ℂ) :
    fou ψ ν n r (om μ hk gk Φ) = om μ⁻¹ gk hk (fou ψ ν n r Φ) := by
  funext x
  set F : Matrix (Fin n) (Fin r) k → ℂ :=
    fun z => Φ z * (ψ (trace (((hk⁻¹ : GL (Fin r) k).val * x * gk.val) * z)) : ℂ) with hF
  have key := integral_comp_mul_mul_volM ν hk gk⁻¹ F
  have htr : ∀ y : Matrix (Fin n) (Fin r) k,
      trace ((hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val)) =
        trace (x * y) := by
    intro y
    have e : (hk⁻¹ : GL (Fin r) k).val * x * gk.val * ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) =
        (hk⁻¹ : GL (Fin r) k).val * (x * y * hk.val) := by
      calc _ = (hk⁻¹ : GL (Fin r) k).val * (x * (gk.val * (gk⁻¹ : GL (Fin n) k).val) * y * hk.val) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [Units.mul_inv, Matrix.mul_one]
    rw [e, trace_mul_comm]
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  set A : ℂ := (μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
    ((nabs k (Matrix.GeneralLinearGroup.det hk) ^ ((Fintype.card (Fin n) : ℝ) / 2) : ℝ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det gk) ^ (-(Fintype.card (Fin r) : ℝ) / 2) : ℝ) : ℂ) with hA
  have lhs : fou ψ ν n r (om μ hk gk Φ) x =
      A * ∫ y, F ((gk⁻¹ : GL (Fin n) k).val * y * hk.val) ∂(volM ν (Fin n) (Fin r)) := by
    rw [fou, ← integral_const_mul]
    congr 1
    funext y
    simp only [om, hA, hF, htr]
    ring
  have hFint : ∫ z, F z ∂(volM ν (Fin n) (Fin r)) =
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val) := rfl
  rw [lhs, key, hFint, nabs_det_inv]
  simp only [om, hA, MonoidHom.inv_apply, inv_inv, Complex.real_smul, Fintype.card_fin]
  set a := nabs k (Matrix.GeneralLinearGroup.det gk) with ha
  set b := nabs k (Matrix.GeneralLinearGroup.det hk) with hb
  have ha0 : 0 < a := nabs_pos' _
  have hb0 : 0 < b := nabs_pos' _
  have h1 : ((b ^ ((n : ℝ) / 2) : ℝ) : ℂ) * ((b ^ (-(n : ℝ)) : ℝ) : ℂ) = ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hb0]
    ring_nf
  have h2 : ((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) = ((a ^ ((r : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Real.inv_rpow ha0.le, ← Real.rpow_neg ha0.le, neg_neg, ← Complex.ofReal_mul, ← Real.rpow_add ha0]
    ring_nf
  rw [Complex.ofReal_mul]
  linear_combination
    ((μ (Matrix.GeneralLinearGroup.det hk) : ℂ) * ((μ (Matrix.GeneralLinearGroup.det gk))⁻¹ : ℂˣ) *
      fou ψ ν n r Φ ((hk⁻¹ : GL (Fin r) k).val * x * gk.val)) *
    (((a ^ (-(r : ℝ) / 2) : ℝ) : ℂ) * ((a⁻¹ ^ (-(r : ℝ)) : ℝ) : ℂ) * h1 + ((b ^ (-(n : ℝ) / 2) : ℝ) : ℂ) * h2)

def fouL (hψ : Continuous ψ) (h1 : ψ ≠ 1) :
    SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] SB (Matrix (Fin r) (Fin n) k) where
  toFun Φ := ⟨fou ψ ν n r Φ.1, fou_mem ν hψ h1 Φ.2⟩
  map_add' Φ Ψ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (Φ.1 + Ψ.1) x = fou ψ ν n r Φ.1 x + fou ψ ν n r Ψ.1 x
    simp only [fou, Pi.add_apply, add_mul]
    exact integral_add (integrable_fou ν hψ Φ.2 x) (integrable_fou ν hψ Ψ.2 x)
  map_smul' c Φ := by
    apply Subtype.ext
    funext x
    show fou ψ ν n r (c • Φ.1) x = c * fou ψ ν n r Φ.1 x
    simp only [fou, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _

theorem fouL_surjective (hψ : Continuous ψ) (h1 : ψ ≠ 1) (hν : IsSelfDual ψ ν) :
    Function.Surjective (fouL (n := n) (r := r) ν hψ h1) := by
  intro G
  obtain ⟨Φ₀, hΦ₀⟩ := (FourierSurj.hat_surjective k (Fin n × Fin r) ψ hψ h1 ν hν).2
    ⟨_, comp_mem_SB (flatT n r).symm G.2⟩
  refine ⟨⟨Φ₀.1 ∘ flat n r, comp_mem_SB _ Φ₀.2⟩, Subtype.ext (funext fun x => ?_)⟩
  show fou ψ ν n r (Φ₀.1 ∘ flat n r) x = G.1 x
  have h2 := congrFun hΦ₀ (flatT n r x)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.hat, Function.comp_apply, Homeomorph.symm_apply_apply] at h2
  rw [fou_eq_pi, ← h2]
  congr 1
  funext z
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply, dotProduct_comm]

end GlobalTheory.LinearModelFourier

theorem GlobalTheory.linearModel_fourier : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n r : ℕ), ∃ τ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin r) (Fin n) k), Function.Surjective τ ∧ ∀ (μ : kˣ →* ℂˣ) (gk : GL (Fin n) k) (hk : GL (Fin r) k) (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) k)), Φ'.1 = GlobalTheory.SplitWeil.om μ hk gk Φ.1 → (τ Φ').1 = GlobalTheory.SplitWeil.om μ⁻¹ gk hk (τ Φ).1 := by
  intro k _ _ _ _ n r
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ψ, hψ, h1, -⟩ := (conductor_exists k).2.1
  obtain ⟨ν, hν⟩ := (selfDual_measure k ψ hψ h1).1
  haveI := hν.1
  refine ⟨GlobalTheory.LinearModelFourier.fouL ν hψ h1, GlobalTheory.LinearModelFourier.fouL_surjective ν hψ h1 hν,
    fun μ gk hk Φ Φ' hΦ => ?_⟩
  show GlobalTheory.LinearModelFourier.fou ψ ν n r Φ'.1 = om μ⁻¹ gk hk (GlobalTheory.LinearModelFourier.fou ψ ν n r Φ.1)
  rw [hΦ]
  exact GlobalTheory.LinearModelFourier.fou_om ν μ gk hk Φ.1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalComponentOfIdelicCharacterAgreement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.LocMod

theorem Place.isComp_of_chrEq : ∀ (D : D7) (s : SplitPlace D.host.E) (p : GlobalTheory.LocMod.Place D (s.w.adicCompletion D.host.E)), Formalism.L2.JoinChr.IsPlIdem D p.e s.w → (∀ x : D.host.E, p.pr x = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (χ : HChar D.host.E), Formalism.IndefR.Links.ChrEq c χ → ∀ μw, GlobalTheory.NPin.IsComp χ s.w μw → p.IsComp c μw := by
  intro D s p hpl hpr c χ hc μw hμ
  have he : p.e * p.e = p.e := hpl.1
  have e_ι : ∀ x, p.e * p.ι x = p.ι x := fun x => by rw [← p.ι_π, p.π_ι]
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, e_ι]
  have ho : p.ι 1 = p.e := by rw [← p.π.map_one, p.ι_π, mul_one]
  let j0 : s.w.adicCompletion D.host.E →* Formalism.L2.Theta.AE D :=
    { toFun := fun x => p.ι x + (1 - p.e)
      map_one' := by rw [ho, add_sub_cancel]
      map_mul' := fun x y => by
        rw [hm]
        linear_combination e_ι x + e_ι y - he }
  have hj0 : Continuous j0 := p.cont_ι.add continuous_const
  let j : (s.w.adicCompletion D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map j0
  have hj : Continuous j := by
    refine Units.continuous_iff.2 ⟨hj0.comp Units.continuous_val, ?_⟩
    have : (fun u => ((j u)⁻¹ : (Formalism.L2.Theta.AE D)ˣ).val) =
        fun u : (s.w.adicCompletion D.host.E)ˣ => j0 ((u⁻¹ : (s.w.adicCompletion D.host.E)ˣ) : s.w.adicCompletion D.host.E) := by
      funext u; rw [← map_inv]; rfl
    rw [this]
    exact hj0.comp Units.continuous_coe_inv
  have hcc : Continuous c := hc.1.1
  have hF2 : Continuous fun u => ((c (j u) : Circle) : ℂ) := (continuous_subtype_val.comp hcc).comp hj
  have hμc : Continuous μw := by
    refine continuous_of_continuousAt_one μw ?_
    have hker : (μw.ker : Set (s.w.adicCompletion D.host.E)ˣ) ∈ nhds 1 := hμ.1.mem_nhds (by simp)
    have : (fun _ => (1 : ℂˣ)) =ᶠ[nhds 1] μw := Filter.mem_of_superset hker fun x hx => (MonoidHom.mem_ker.1 hx).symm
    have h2 := (continuousAt_const.congr this).tendsto
    rw [map_one] at h2
    rw [ContinuousAt, map_one]
    exact h2
  have hF1 : Continuous fun u => ((μw u : ℂˣ) : ℂ) := Units.continuous_val.comp hμc
  have hd : Dense (Set.range (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E))) := by
    rw [dense_iff_inter_open]
    rintro U hU ⟨u, hu⟩
    have hoe : Topology.IsOpenEmbedding (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) :=
      { toIsEmbedding := Units.isEmbedding_val₀
        isOpen_range := by
          have : Set.range (Units.val : (s.w.adicCompletion D.host.E)ˣ → s.w.adicCompletion D.host.E) = {0}ᶜ := by
            ext y
            exact ⟨fun ⟨u, hu⟩ => hu ▸ u.ne_zero, fun h => ⟨Units.mk0 y h, rfl⟩⟩
          rw [this]; exact isOpen_compl_singleton }
    obtain ⟨y, hy⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := D.host.E) s.w).exists_mem_open
      (hoe.isOpenMap U hU) ⟨u, u, hu, rfl⟩
    obtain ⟨v, hv, hvy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact v.ne_zero (by simpa using hvy)
    refine ⟨v, hv, Units.mk0 y hy0, Units.ext ?_⟩
    simpa using hvy.symm
  have key : ∀ x : D.host.Eˣ, ((μw (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x) : ℂˣ) : ℂ)
      = ((c (j (Units.map (algebraMap D.host.E (s.w.adicCompletion D.host.E) : D.host.E →* s.w.adicCompletion D.host.E) x)) : Circle) : ℂ) := by
    intro x
    refine (congrArg Units.val (hμ.2 x)).trans (hc.2 s.w p.e hpl x _ ?_).symm
    change p.ι (algebraMap D.host.E (s.w.adicCompletion D.host.E) x) + (1 - p.e) = _
    rw [← hpr, GlobalTheory.LocMod.Place.pr, p.ι_π, Formalism.L2.JoinChr.locE]
    ring
  have heq := Continuous.ext_on hd hF1 hF2 (by rintro _ ⟨x, rfl⟩; exact key x)
  intro x a ha
  have hja : j x = a := Units.ext ha.symm
  rw [← hja]
  exact congrFun heq x

end GlobalTheory.LocMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHeckeSplitPlaceSetIffDoubleCoset
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TSetDoubleCoset

theorem trivOutside_mul {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x y : GA L n}
    (hx : TrivOutside T x) (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro v hv
  have e : ((x * y : GA L n).1 : Matrix (Fin n) (Fin n) (AL L)) =
      (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [e, Matrix.map_mul, hx v hv, hy v hv, Matrix.mul_one]

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ a b, g.val a b ∈ O) (h2 : ∀ a b, (g⁻¹).val a b ∈ O) : g ∈ Formalism.UG.GLint (Fin n) O := by
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => by ext i j; exact congrFun (congrFun h i) j
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem loc_mem_GLint {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (s : SplitPlace L)
    {k : GA L n} (hk : k ∈ Umax L n) :
    s.loc n k ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
  apply mem_GLint_of_entries
  · intro a b
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s (hk a b)
  · intro a b
    rw [← map_inv]
    exact GlobalTheory.splitPlace_proj_mem_integers_of_integral s ((Umax L n).inv_mem hk a b)

theorem mem_tSet_iff : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (n : ℕ) (sp : SplitPlace L) (ϖ : (sp.v).adicCompletion (maximalRealSubfield L)) (k : ℕ), ∀ x₀ ∈ Formalism.AUTREP.tSet L n sp ϖ k, ∀ κ, κ ∈ Formalism.AUTREP.tSet L n sp ϖ k ↔ ∃ k₁, (k₁ ∈ Umax L n ∧ TrivOutside {sp.v} k₁) ∧ ∃ k₂, (k₂ ∈ Umax L n ∧ TrivOutside {sp.v} k₂) ∧ κ = k₁ * x₀ * k₂ := by
  intro L _ _ _ n sp ϖ k x₀ hx₀ κ
  obtain ⟨hx₀t, a₀, ha₀, b₀, hb₀, hx₀e⟩ := hx₀
  constructor
  · rintro ⟨hκt, a, ha, b, hb, hκe⟩
    obtain ⟨e, he1, he2⟩ := GlobalTheory.SplitEmb.exists_hom_trivOutside_loc L n sp
    have hg : a * a₀⁻¹ ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem ha (inv_mem ha₀)
    have hg' : b₀⁻¹ * b ∈ Formalism.UG.GLint (Fin n) (sp.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring :=
      mul_mem (inv_mem hb₀) hb
    refine ⟨e (a * a₀⁻¹), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg), he1 _⟩,
      e (b₀⁻¹ * b), ⟨GlobalTheory.SplitHeckeComm.mem_Umax_of_loc sp _ (he1 _) (by rw [he2]; exact hg'), he1 _⟩, ?_⟩
    apply GlobalTheory.SplitLocEq.eq_of_trivOutside_of_loc_eq L n sp
    · exact hκt
    · exact trivOutside_mul (trivOutside_mul (he1 _) hx₀t) (he1 _)
    · rw [map_mul, map_mul, he2, he2]
      apply Units.ext
      simp only [Units.val_mul]
      rw [hκe, hx₀e]
      simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.mul_inv_cancel_left]
  · rintro ⟨k₁, ⟨hk₁, hk₁t⟩, k₂, ⟨hk₂, hk₂t⟩, rfl⟩
    refine ⟨trivOutside_mul (trivOutside_mul hk₁t hx₀t) hk₂t, sp.loc n k₁ * a₀,
      mul_mem (loc_mem_GLint sp hk₁) ha₀, b₀ * sp.loc n k₂, mul_mem hb₀ (loc_mem_GLint sp hk₂), ?_⟩
    rw [map_mul, map_mul]
    simp only [Units.val_mul]
    rw [hx₀e]
    simp only [Matrix.mul_assoc]

end GlobalTheory.TSetDoubleCoset
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotIsSplitPlaceOfInertOverRealSubfield
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem not_isSplitPl_of_isInertAt (D : D7) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (h : Formalism.UG.IsInertAt (↥D.host.F) D.host.E (HeightOneSpectrum.under (𝓞 ↥D.host.F) Pp) Pp) : ¬ Formalism.BasicNotions.IsSplitPl D.host Pp := by
  rintro ⟨x, hx, hy⟩
  have hc : (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E)) = algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) := by
    refine RingHom.ext fun a => RingOfIntegers.ext ?_
    have key : ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E) = ((a : ↥D.host.F) : D.host.E) := rfl
    have h0 := (D.host.conjE_mem_hostF_iff _).1 (a : ↥D.host.F).2
    show (D.host.conj ((algebraMap (𝓞 ↥D.host.F) (𝓞 D.host.E) a : 𝓞 D.host.E) : D.host.E)) = _
    rw [key]; exact h0
  have hmem : NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) x ∈ Pp.asIdeal := by
    unfold Formalism.UG.IsInertAt at h
    rw [← h] at hx ⊢
    have := Ideal.mem_map_of_mem (NumberField.RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)) hx
    rwa [Ideal.map_map, hc] at this
  exact hy _ rfl hmem

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OperatorEigenGoodPlaceFirst
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.InertFormFix.mul_idem_of_trivOutside {E : Type} [Field E] [NumberField E] [IsCMField E] (F : Subfield E)
    (hF : F = maximalRealSubfield E) (P : HeightOneSpectrum (𝓞 E))
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : NG.OverPl P v) (x : AL E)
    (hx : ∀ w, w ≠ v → compAt E w x = 0) :
    ((GlobalTheory.AdelicU.singleFin (P.under (𝓞 F)) 1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (1 : E)) *
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  subst hF
  have hvv : P.under (𝓞 (maximalRealSubfield E)) = v := HeightOneSpectrum.ext hv
  subst hvv
  have hx' : x = GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x := by
    have h0 := GlobalTheory.AL_eq_zero_of_compAt E (x - GlobalTheory.CongSplit.idemAt E (P.under (𝓞 (maximalRealSubfield E))) * x)
      (fun w => by
        rw [RingHom.map_sub, RingHom.map_mul]
        by_cases hw : w = P.under (𝓞 (maximalRealSubfield E))
        · rw [hw, GlobalTheory.CongSplit.compAt_idemAt_self, one_mul, sub_self]
        · rw [GlobalTheory.CongSplit.compAt_idemAt_ne E _ hw, hx w hw, zero_mul, sub_zero])
    exact (sub_eq_zero.1 h0)
  conv_rhs => rw [hx']
  rw [RingEquiv.map_mul]
  congr 1

theorem GlobalTheory.InertFormFix.finPart_mul_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ x : AL D.host.E, (∀ w, w ≠ v → compAt D.host.E w x = 0) → Formalism.L2.Theta.finPart D f * (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm x := by
  intro D hF P e f hP v hv x hx
  have hf := GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hP rfl
  subst hf
  exact GlobalTheory.InertFormFix.mul_idem_of_trivOutside D.host.F hF P v hv x hx


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.InertFormFix.suppF_of_trivOutside : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (V : Formalism.BasicNotions.TH.HSp D) (n : ℕ) (Q : Formalism.IndefR.principalLevelFrame.RowPsi V n), Formalism.IndefR.principalLevelFrame.StdPsi hF Q → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e f : Formalism.L2.Theta.AE D), Formalism.IndefR.Mult.IsPrimeIdem P e f → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl P v → ∀ κ : GAf D.host.E n, TrivOutside {v} κ → Formalism.IndefR.Mult.SuppF V f (Q.ψ κ) := by
  intro D hF V n Q hQ P e f hP v hv κ hT
  obtain ⟨⟨β, β', hββ', hβ'β, hmat⟩, -⟩ := hQ
  rw [GlobalTheory.SphTrans.suppF_iff f (Q.into κ), hmat κ]
  have hT' : ∀ w, w ≠ v → (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E w) = 1 :=
    fun w hw => hT w (by simpa using hw)
  change Formalism.L2.Theta.finPart D f • (β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1) = β * (κ.1.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map
      (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm * β' - 1
  set M : Matrix (Fin n) (Fin n) (AL D.host.E) := κ.1.1 with hMdef
  set K := M.map (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm with hKdef
  have hcore : ∀ a b, Formalism.L2.Theta.finPart D f * (K - 1) a b = (K - 1) a b := by
    intro a b
    have hx : ∀ w, w ≠ v → compAt D.host.E w (M a b - (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) = 0 := by
      intro w hw
      have h1 := congrFun (congrFun (hT' w hw) a) b
      rw [Matrix.map_apply] at h1
      rw [RingHom.map_sub, h1]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingHom.map_zero, sub_zero]
    have h2 := GlobalTheory.InertFormFix.finPart_mul_of_trivOutside D hF P e f hP v hv _ hx
    have e3 : (K - 1) a b = (Formalism.IndefR.principalLevelFrame.tensCastR hF).symm (M a b -
        (1 : Matrix (Fin n) (Fin n) (AL D.host.E)) a b) := by
      rw [Matrix.sub_apply, hKdef, Matrix.map_apply, RingEquiv.map_sub]
      by_cases hab : a = b
      · rw [hab, Matrix.one_apply_eq, Matrix.one_apply_eq, RingEquiv.map_one]
      · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne hab, RingEquiv.map_zero]
    rw [e3, h2]
  have hK : Formalism.L2.Theta.finPart D f • (K - 1) = K - 1 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, hcore]
  have e1 : β * K * β' - 1 = β * (K - 1) * β' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hββ']
  rw [e1]
  conv_rhs => rw [← hK]
  rw [Matrix.mul_smul, Matrix.smul_mul]

end
end

