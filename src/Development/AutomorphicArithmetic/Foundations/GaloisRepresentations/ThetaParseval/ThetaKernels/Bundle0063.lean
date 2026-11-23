module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ThMSymmApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThRatIffK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def thM_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : UA σ d.A.J ≃ᵐ HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) :=
  (Homeomorph.mk (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).toEquiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)).toMeasurableEquiv
def thE'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) : HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη g
theorem th_rat_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) (g : UA σ d.A.J) :
    g ∈ ratU σ d.A.J ↔ _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g ∈ HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := by
  rw [ratU, Subgroup.mem_subgroupOf, MonoidHom.mem_range, HeckeCharacterZeroLocus.SiegelWeilU.HFinIn, Subgroup.mem_subgroupOf,
    HeckeCharacterZeroLocus.SiegelWeilU.HFin, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨γ, ?_, hγ⟩
    have hg : (g.1 : GL (Fin d.m) (AE F E)) ∈ HeckeCharacterZeroLocus.SiegelWeilU.HR (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_mem_iff_k d hη g.1).1 g.2
    rw [← hγ] at hg
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (σ : E →+* E) (γ : Matrix (Fin d.m) (Fin d.m) E) * _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η * (γ : Matrix (Fin d.m) (Fin d.m) E) =
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η
    apply Matrix.map_injective (th_inclR_injective (F := F) (E := E))
    change HeckeCharacterZeroLocus.SiegelWeilU.cT (HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ) ((γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F))) *
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) * (γ : Matrix (Fin d.m) (Fin d.m) E).map (inclR (F := F) (E := E) (AF F)) =
      HeckeCharacterZeroLocus.SiegelWeilU.JR (AF F) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) at hg
    dsimp only
    rw [Matrix.map_mul, Matrix.map_mul, th_cT_map]
    exact hg
  · rintro ⟨γ, -, hγ⟩
    exact ⟨γ, hγ⟩
def thR_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) : HeckeCharacterZeroLocus.SiegelWeilU.HFinIn (AF F) σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) ≃ ratU σ d.A.J where
  toFun h := ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).2
    (by have e1 : _root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm h.1) = h.1 := (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1
        rw [e1]; exact h.2)⟩
  invFun g := ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE'_k d hη g.1, (_root_.PositivityTheory.SiegelWeilFormula.KWhit.th_rat_iff_k d hη _).1 g.2⟩
  left_inv h := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).apply_symm_apply h.1)
  right_inv g := Subtype.ext ((_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη).symm_apply_apply g.1)
theorem th_haar_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHaarH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) := by
  have := d.ok.haar
  exact th_haar_map d.μ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_cont_k d hη) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thE_symm_cont_k d hη)
theorem th_fd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {η : E} (hη : η ≠ 0) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsFDH F E σ d.m (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) (d.μ.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη)) (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη '' d.D) := by
  refine d.ok.dom.image_of_equiv (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).toEquiv ⟨(_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm.measurable.aemeasurable, ?_⟩ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thR_k d hη) ?_
  · change Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη).symm (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KWhit.thM_k d hη) d.μ) ≪ d.μ
    rw [MeasurableEquiv.map_symm_map]
  · intro h x
    rfl
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationPairContinuous
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_pair_continuous : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
              ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) := by
  first | exact @_root_.GlobalTheory.TransportHeisF.pres_impl_k | exact _root_.GlobalTheory.TransportHeisF.pres_impl_k | (intros; apply _root_.GlobalTheory.TransportHeisF.pres_impl_k <;> assumption)
end
end

