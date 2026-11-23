module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0008
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnfoldAbs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0006

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.AlgebraMapMemOv
section
noncomputable section

namespace MassDataMassesW.KCptW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures MeasureTheory NumberField IsDedekindDomain
  Topology PI.AdicCompletionValuation MassDataLevelSSteps.LatTop MassDataLevelSSteps Matrix

section Crd

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

def crd (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) : Fin (Module.finrank F E) → R :=
  (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun z

theorem crd_tens {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (z : R ⊗[F] E) (k : Fin (Module.finrank F E)) : crd R' (tensMap (E := E) φ z) k = φ (crd R z k) := by
  induction z using TensorProduct.induction_on with
  | zero => simp [crd]
  | tmul r e =>
    simp [crd, tensMap, Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy =>
    simp only [map_add (f := _)] at *
    simp only [crd, map_add (f := _), Pi.add_apply] at *
    rw [hx, hy]

def Bint (n : ℕ) : Set (Fin n → E) :=
  {x | ∀ i k, IsIntegral ℤ ((Module.finBasis F E).repr (x i) k)}

theorem algebraMap_mem_Ov (v : HeightOneSpectrum (𝓞 F)) {c : F} (hc : IsIntegral ℤ c) :
    algebraMap F (Fv F v) c ∈ v.adicCompletionIntegers F := by
  obtain ⟨x, rfl⟩ : ∃ x : 𝓞 F, (x : F) = c := ⟨⟨c, hc⟩, rfl⟩
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v x

theorem crd_mem_of_latLoc {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) {y : Fin n → Fv F v ⊗[F] E}
    (hy : y ∈ latLoc (E := E) v (Bint (F := F) n)) (i : Fin n) (k : Fin (Module.finrank F E)) :
    crd (Fv F v) (y i) k ∈ v.adicCompletionIntegers F := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    have h := algebraMap_mem_Ov v (hx i k)
    simpa [crd, ratV, inclR, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.one_def] using h
  | zero => simp [crd]
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, crd, map_add (f := _)] at ha hb ⊢
    exact add_mem ha hb
  | smul c a _ ha =>
    simp only [crd] at ha ⊢
    have e : (c • a) i = (c : Fv F v) • a i := rfl
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem c.2 ha

end Crd

end MassDataMassesW.KCptW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.CountableRatOf
section
noncomputable section

open MeasureTheory NumberField
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem countable_ratOf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (K : Subgroup (HA (AF F) σ J)) :
    Countable (ratOf (K := K)) := by
  haveI := PI.VolStabSW.um_countable_HFinIn F E σ M J
  refine Function.Injective.countable (f := fun x : ratOf (K := K) =>
    (⟨((x : K) : HA (AF F) σ J), Subgroup.mem_comap.1 x.2⟩ : HFinIn (AF F) σ J)) ?_
  intro x y hxy
  have e := congrArg Subtype.val hxy
  exact Subtype.ext (Subtype.ext e)

theorem smulInv_ratOf {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (K : Subgroup G)
    (Γ : Subgroup K) (μ : Measure K) [μ.IsMulLeftInvariant] : SMulInvariantMeasure Γ K μ := by
  first
  | exact inferInstance
  | exact ⟨fun c s _ => by
      show μ ((fun x : K => (c : K) * x) ⁻¹' s) = μ s
      exact measure_preimage_mul μ (c : K) s⟩

theorem covol_eq_of_fd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) [MeasurableMul (HA (AF F) σ J)]
    (K : Subgroup (HA (AF F) σ J)) (μ : Measure K) (hμ : μ.IsMulLeftInvariant) (𝓕 : Set K)
    (h𝓕 : IsFundamentalDomain (ratOf (K := K)) 𝓕 μ) : covol μ = (μ 𝓕).toReal := by
  haveI := hμ
  haveI := countable_ratOf σ J K
  haveI := smulInv_ratOf K (ratOf (K := K)) μ
  unfold covol
  split_ifs with h
  · congr 1
    exact h.choose_spec.measure_eq h𝓕
  · exact absurd ⟨𝓕, h𝓕⟩ h

theorem n4cov_holds : UnipotentCoveringCount := by
  intro D X u 𝓕 hN h𝓕
  exact covol_eq_of_fd _ _ _ _ hN.2.2.2.1.toIsMulLeftInvariant 𝓕 h𝓕

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.EllipticCentralizerQuotientCompact
section
noncomputable section

open MeasureTheory NumberField Set
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem prod_rect_of_ne_zero {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) (h0 : μ.prod ν ≠ 0) {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : μ.prod ν (s ×ˢ t) = μ s * ν t := by
  have hν : SFinite ν := by
    by_contra hν
    exact h0 (Measure.prod_eq_zero_of_not_sfinite hν)
  letI : SFinite ν := hν
  exact Measure.prod_prod s t

theorem tauF_eq_comm {D : D7} (X : HidaSetting D) (y : AF X.B.I.F ⊗[X.B.I.F] X.B.I.E) :
    tauF X.B.I y = Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E
      (tensMap (E := X.B.I.E) (sndA X.B.I.F) y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem toHA_fin_one {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (s : X.B.I.Ginf) :
    (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1))).2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) (s, 1)).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have e2 := congrArg (Algebra.TensorProduct.comm X.B.I.F (Af X.B.I.F) X.B.I.E).symm e
  rw [AlgEquiv.symm_apply_apply] at e2
  show tensMap (E := X.B.I.E) (sndA X.B.I.F) _ = _
  rw [← e2]
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j
  simp only [Formalism.MainNotions.S.AutInst.fmat, OneMemClass.coe_one, Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

section Split

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem eq_one_of_toHA_fin {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (p : X.B.I.GA)
    (h : (splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb p)).2 = 1) : p.2 = 1 := by
  have hbr := ((toHA_isBridge X.B.I hb) p).2
  apply Subtype.ext
  apply Units.ext
  ext i j
  have e := congrFun (congrFun hbr i) j
  simp only [ofHAFin, Matrix.map_apply] at e
  rw [tauF_eq_comm] at e
  have h2 : tensMap (E := X.B.I.E) (sndA X.B.I.F) (hmat X.B.I (toHA X.B.I hb p) i j) =
      (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Af X.B.I.F ⊗[X.B.I.F] X.B.I.E)) i j := by
    have := congrArg (fun g : HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J =>
      (HA.mat (Af X.B.I.F) X.B.I.cm.sig X.B.I.J g).val i j) h
    exact this
  rw [h2] at e
  rw [Formalism.MainNotions.S.AutInst.fmat] at e
  show _ = (1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) i j
  rw [e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem split_unitary_infinite_one (s : X.B.I.Ginf) :
    splitA X.B.I.cm.sig X.B.I.J (toHA X.B.I hb (s, 1)) = (X.toInf hb s, 1) :=
  Prod.ext rfl (toHA_fin_one X hb s)

theorem toInf_injective (hS : SplitIso) : Function.Injective (X.toInf hb) := by
  intro s t hst
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have h1 : e (toHA X.B.I hb (s, 1)) = e (toHA X.B.I hb (t, 1)) := by
    rw [he, split_unitary_infinite_one, split_unitary_infinite_one, hst]
  have h2 := (toHA X.B.I hb).injective (e.injective h1)
  exact congrArg Prod.fst h2

theorem continuous_toInf_of (hS : SplitIso) : Continuous (X.toInf hb) := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  exact continuous_fst.comp (hc.comp ((toHA X.B.I hb).continuous_toFun.comp
    (continuous_id.prodMk continuous_const)))

theorem measurable_toInf_of (hS : SplitIso) : Measurable (X.toInf hb) := by
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  exact (continuous_toInf_of X hb hS).measurable

theorem measurableSet_image_toInf (hS : SplitIso) {FdN : Set X.B.I.Ginf} (hF : MeasurableSet FdN) :
    MeasurableSet (X.toInf hb '' FdN) := by
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  let Φ : X.B.I.GA ≃ₜ* (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J × HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    (toHA X.B.I hb).trans e
  have hΦ : ∀ s, Φ (s, 1) = (X.toInf hb s, 1) := fun s => by
    show e (toHA X.B.I hb (s, 1)) = _
    rw [he]
    exact split_unitary_infinite_one X hb s
  let ψ : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J → X.B.I.GA := fun y => Φ.symm (y, 1)
  have hψc : Continuous ψ := Φ.symm.continuous_toFun.comp (continuous_id.prodMk continuous_const)
  have hset : X.toInf hb '' FdN = (fun y => (ψ y).1) ⁻¹' FdN := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      show (Φ.symm (X.toInf hb s, 1)).1 ∈ FdN
      rw [← hΦ, Φ.symm_apply_apply]
      exact hs
    · intro h1
      have h2 : (ψ y).2 = 1 := by
        apply eq_one_of_toHA_fin X hb
        have h3 : e (toHA X.B.I hb (ψ y)) = (y, 1) := Φ.apply_symm_apply _
        rw [he] at h3
        rw [h3]
      refine ⟨(ψ y).1, h1, ?_⟩
      have hp : ψ y = ((ψ y).1, 1) := Prod.ext rfl h2
      have := congrArg Φ hp
      rw [show Φ (ψ y) = (y, 1) from Φ.apply_symm_apply _, hΦ] at this
      exact (congrArg Prod.fst this).symm
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  rw [hset]
  exact (continuous_fst.comp hψc).measurable hF

end Split

theorem elliptic_centralizer_quotient_compact (hKo : KCompactOpen) : N4 := by
  intro hS D X hb u FdN hT hTie hF
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : BorelSpace (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  obtain ⟨e, he⟩ := hS X.B.I.cm.sig X.B.I.J
  have hc : Continuous (splitA X.B.I.cm.sig X.B.I.J) := by rw [← he]; exact e.continuous_toFun
  have hm : Measurable (splitA X.B.I.cm.sig X.B.I.J) :=
    (continuous_fst.comp hc).measurable.prodMk (continuous_snd.comp hc).measurable
  have hTm : MeasurableSet (X.toInf hb '' FdN) := measurableSet_image_toInf X hb hS hF.1
  have hKm : MeasurableSet (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) := (hKo X).2.measurableSet
  have hRm : MeasurableSet ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) :=
    hTm.prod hKm
  have hFd : FdA X hb u FdN = Subtype.val ⁻¹' (splitA X.B.I.cm.sig X.B.I.J ⁻¹'
      ((X.toInf hb '' FdN) ×ˢ (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))) := by
    ext n
    simp only [FdA, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_prod, Set.mem_image]
    constructor
    · rintro ⟨s, hs, h1, h2⟩
      exact ⟨⟨s, hs, h1.symm⟩, h2⟩
    · rintro ⟨⟨s, hs, h1⟩, h2⟩
      exact ⟨s, hs, h1.symm, h2⟩
  have hN := hT.2.2.2.2.2.2.2.2.2.1
  have hHaar : (X.measW u).μN.IsHaarMeasure := hT.2.2.2.1
  have h0 : (amb (X.measW u).μNinf).prod (amb (X.measW u).μNf) ≠ 0 := by
    rw [← hN]
    intro h
    have h' := congrArg (fun μ => μ Set.univ) h
    simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
      Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Measure.coe_zero, Pi.zero_apply] at h'
    exact (isOpen_univ.measure_ne_zero (X.measW u).μN Set.univ_nonempty) h'
  rw [hFd]
  erw [← Measure.map_apply measurable_subtype_coe (hm hRm)]
  rw [← Measure.map_apply hm hRm]
  change ((amb (X.measW u).μN).map (splitA X.B.I.cm.sig X.B.I.J)) _ = _
  rw [hN, prod_rect_of_ne_zero _ _ h0 hTm hKm, (hTie.2.2.2 u).1,
    Measure.map_apply (measurable_toInf_of X hb hS) hTm, Set.preimage_image_eq _ (toInf_injective X hb hS),
    Measure.map_apply measurable_subtype_coe hKm]

end MassDataMassesW
end
end

