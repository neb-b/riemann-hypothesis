module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0060
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0047
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1781
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0063
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0061
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoCoef
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
set_option maxHeartbeats 400000
theorem stepA_k (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G}
    (hnb : IsNMap (σ := σ) (Y := d.Y) d.b nb) (x : d.G) (β : nA σ d.Y d.b) (g : UA σ d.A.J) :
    thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E,
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram (incM F X) (incM F X)))) * d.T (d.om x Φ) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) := by
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hΨg : d.S g (d.om x Φ) ∈ d.sch := d.ok.dbl.lin.pres g _ hΨ
  have hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch := d.ok.dbl.weil.2.1.pres (nb β) _ hΨg
  rw [map_mul, Module.End.mul_apply, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]
  refine tsum_congr fun X => ?_
  rw [(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]
  rfl
theorem meas_tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    AEMeasurable (fun g => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ) (d.μ.restrict d.D) :=
  ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_tr_k d hf X).enorm.measurable).aemeasurable
theorem tbdd_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∃ K : ℝ, ∀ g : UA σ d.A.J, Summable (fun X => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖) ∧ ∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ ≤ K := by
  obtain ⟨K, hK⟩ := _root_.PositivityTheory.SiegelWeilFormula.Kdil.thetaBdd_of_k hS F E σ d f hf
  exact ⟨K, hK⟩
theorem pt_bdd_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (g : UA σ d.A.J) (s : Set (Matrix (Fin d.m) (Fin d.n) E)) {K : ℝ}
    (hsum : Summable (fun X => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖)) (hle : ∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ ≤ K) :
    ∑' X : s, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ ≤ ENNReal.ofReal K := by
  calc ∑' X : s, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ ≤ ∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun X => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ)
    _ = ∑' X, ENNReal.ofReal ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ := tsum_congr fun X => (ofReal_norm _).symm
    _ = ENNReal.ofReal (∑' X, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hle
theorem lint_fin_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    (s : Set (Matrix (Fin d.m) (Fin d.n) E)) :
    ∑' X : s, ∫⁻ g in d.D, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ ∂d.μ ≠ ⊤ := by
  haveI := countable_mat (E := E) d.m d.n
  obtain ⟨K, hK⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.tbdd_k hS d hf
  have hfin : d.μ d.D < ⊤ := (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cpt_k hS d).fin d.μ d.D d.ok.haar d.ok.dom
  rw [← lintegral_tsum (f := fun (X : s) g => ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)‖ₑ) fun X => _root_.PositivityTheory.SiegelWeilFormula.Tauto.meas_tr_k d hf X.1]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    ((lintegral_mono fun g => _root_.PositivityTheory.SiegelWeilFormula.Tauto.pt_bdd_k d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)
theorem lint_fin_all_k (hS : GlobalTheory.Published.SiegelSetUnitary) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∑' X, ∫⁻ g in d.D, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ ∂d.μ ≠ ⊤ := by
  have := _root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_k hS d hf Set.univ
  rwa [tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)‖ₑ ∂d.μ)] at this
theorem continuous_tt_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : Continuous (d.tt) := by
  have h1 : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)
theorem thetaCoef_at_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
    {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = d.orb T (d.om x Φ) := by
  haveI := countable_mat (E := E) d.m d.n
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hf : d.T (d.om x Φ) ∈ d.schM := (hB F E σ d).1 _ hΨ
  have hen : ∀ a, ‖d.B.ψ a‖ₑ = 1 := fun a => by
    rw [← ofReal_norm_eq_enorm, GlobalTheory.StdCharFromIsStd.norm_psi d.std, ENNReal.ofReal_one]
  have hψc : Continuous d.B.ψ := d.std.1
  set f : Mx F E d.m d.n → ℂ := d.T (d.om x Φ) with hfdef
  set c : ℝ := (d.μ.real d.D)⁻¹ with hcdef
  set G : Matrix (Fin d.m) (Fin d.n) E → Matrix (Fin d.n) (Fin d.n) (AE F E) :=
    fun X => d.gram (incM F X) (incM F X) with hG
  set e : nA σ d.Y d.b → Matrix (Fin d.m) (Fin d.n) E → ℂ :=
    fun β X => d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * G X))) with he
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(d.tt (T.1.1 * β.1))) with hχ
  set H : Matrix (Fin d.m) (Fin d.n) E → ℂ := fun X => ∫ g in d.D, f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) ∂d.μ with hH
  have hmeas : ∀ X, AEStronglyMeasurable (fun g => f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)) (d.μ.restrict d.D) :=
    fun X => (_root_.PositivityTheory.SiegelWeilFormula.Tauto.cont_tr_k d hf X).aestronglyMeasurable
  have hcb : Continuous fun β : nA σ d.Y d.b => β.1 := continuous_subtype_val
  have hec : ∀ X, Continuous fun β => e β X := fun X =>
    hψc.comp ((continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Tauto.continuous_tt_k d).comp (hcb.matrix_mul continuous_const))).neg)
  have hχc : Continuous χ := hψc.comp (((_root_.PositivityTheory.SiegelWeilFormula.Tauto.continuous_tt_k d).comp (continuous_const.matrix_mul hcb)).neg)
  have hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X := fun β => by
    show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _
    rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
    congr 1
    have hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) :=
      fun g => _root_.PositivityTheory.SiegelWeilFormula.Tauto.stepA_k hP hT d hΦ hc.1 x β g
    simp only [hA']
    rw [integral_tsum (f := fun X g => e β X * f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X)) (fun X => (hmeas X).const_mul _) ?_]
    · exact tsum_congr fun X => integral_const_mul _ _
    · simpa only [he, enorm_mul, hen, one_mul] using _root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_all_k hS d hf
  have hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0 := fun X => by
    obtain ⟨hm, S₀, hS₀⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tauto.gram_mem_k d X T
    simp only [he, hχ, _root_.PositivityTheory.SiegelWeilFormula.Tauto.chr_comb_k]
    rw [_root_.PositivityTheory.SiegelWeilFormula.Tauto.orth_k d hc _ hm ⟨S₀, hS₀⟩]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Tauto.half_eq_iff_k]
    rfl
  have h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      c • ∑' X, e β X * χ β * H X := fun β => by
    rw [hI β, smul_mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun X => by simp only [hχ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]; ring
  have hlam : lam 𝓖 = 1 := hc.2.2.2
  have h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤ := by
    simp only [he, hχ, enorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]
    refine ne_top_of_le_ne_top (_root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_all_k hS d hf) (ENNReal.tsum_le_tsum fun X => ?_)
    exact enorm_integral_le_lintegral_enorm _
  have h3 : ∑' X, (if G X = (-2 : ℤ) • T.1.1 then (1 : ℂ) else 0) * H X =
      ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    show _ = ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [tsum_subtype {X | G X = (-2 : ℤ) • T.1.1} H]
    exact tsum_congr fun X => by simp only [Set.indicator_apply, Set.mem_setOf_eq, ite_mul, one_mul, zero_mul]
  have h4 : d.orb T (d.om x Φ) = c • ∑' X : {X : Matrix (Fin d.m) (Fin d.n) E //
      d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1}, H X.1 := by
    haveI : Countable {X : Matrix (Fin d.m) (Fin d.n) E // d.gram (incM F X) (incM F X) = (-2 : ℤ) • T.1.1} :=
      Subtype.countable
    show (⨍ g in d.D, ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)),
      f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E))) g =>
      f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X.1)) (fun X => hmeas X.1) (_root_.PositivityTheory.SiegelWeilFormula.Tauto.lint_fin_k hS d hf {X | G X = (-2 : ℤ) • T.1.1})]
  show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _
  rw [integral_congr_ae (Eventually.of_forall h1), integral_smul,
    integral_tsum (f := fun X β => e β X * χ β * H X)
      (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]
  congr 1
  exact tsum_congr fun X => by rw [integral_mul_const, hO X]
theorem thetaCoef_k (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) (hP : _root_.PositivityTheory.SiegelWeilFormula.TPar_k) (hT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k) : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k :=
  fun _ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x => _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaCoef_at_k hS hB hP hT d hΦ hc T x
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TransportAdmissibleWeilDatum
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.WeilAdmCM
variable {F : Type} [Field F] [NumberField F]
end GlobalTheory.WeilAdmCM
namespace GlobalTheory.WeilAdmCM
theorem transport_admissible_weil_datum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
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
              ∀ p, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om p ∈ (adeleClass F).adm κ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om htr p l hl
  have hP : (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
      ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) :=
    _root_.GlobalTheory.T.weil_representation_pair_continuous F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU : IsUnitaryOn (adeleClass F) om :=
    _root_.GlobalTheory.T.weil_pair_local_factor F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  refine weilAdmissible_of_heisenberg_unitary B.ψ hB.std κ (co.e.symm.trans ((GlobalTheory.WeilAdm.actLin _ p).trans co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h
end GlobalTheory.WeilAdmCM
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentFirstMatrix
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C1
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d} {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
  {𝓤 : Set (Fin L.n → AE F E)} {nb : nA σ d.Y d.b → d.G}
theorem ratV_inc_k {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : ∃ v : Fin L.n → E, u = GlobalTheory.ThK.incV F v := by
  induction hu using AddSubgroup.closure_induction with
  | mem _ h => obtain ⟨v, rfl⟩ := h; exact ⟨v, rfl⟩
  | zero => exact ⟨0, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | add _ _ _ _ h h' =>
    obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := h'; exact ⟨v + w, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
  | neg _ _ h => obtain ⟨v, rfl⟩ := h; exact ⟨-v, funext fun i => by simp [GlobalTheory.ThK.incV]⟩
theorem neg_incV_k (v : Fin L.n → E) : -GlobalTheory.ThK.incV F v = GlobalTheory.ThK.incV F (-v) := funext fun i => by simp [GlobalTheory.ThK.incV]
def unipotentFirstMatrix (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (v : Fin L.n → E) : Matrix (Fin d.n) (Fin d.n) E := 1 + ∑ j, Matrix.single L.i₀ (L.em j) (v j)
theorem Au_inc_k (v : Fin L.n → E) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (GlobalTheory.ThK.incV F v) = incM F (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) := by
  ext a b
  set_option synthInstance.maxHeartbeats 100000 in
    simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix, incM, Matrix.one_apply, Matrix.sum_apply, Matrix.single_apply, GlobalTheory.ThK.incV, map_sum, apply_ite]
theorem Apc_k (hU : L.UData uM ν 𝓤) (u : Fin L.n → AE F E) : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by
  have h1 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ = 1 := mul_eq_one_comm.1 (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.frame_blk_k d (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU u))
  have h2 : (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ = 1 := by rw [← Matrix.transpose_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_mul_k, neg_add_cancel, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_zero_k, Matrix.transpose_one]
  calc (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u).map (cA σ) * ((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ) := by rw [h2, Matrix.mul_one]
    _ = (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u))ᵀ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
theorem Ap_inc_k (hU : L.UData uM ν 𝓤) (v : Fin L.n → E) : ∃ M : Matrix (Fin d.n) (Fin d.n) E,
    _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v) = incM F M := by
  have : FiniteDimensional F E := Module.Finite.of_basis d.bs
  let e := AlgEquiv.ofBijective σ (AlgHom.bijective σ)
  refine ⟨((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm, Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d) ?_⟩
  show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU (GlobalTheory.ThK.incV F v)).map (cA σ) = (incM F (((_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v))ᵀ).map e.symm)).map (cA σ)
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k, kunf.incM_map_cA, Matrix.map_map, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k]
  have h : (⇑σ ∘ ⇑e.symm) = id := funext fun x => e.apply_symm_apply x
  rw [h, Matrix.map_id]
  rfl
theorem uM_rat_k (hU : L.UData uM ν 𝓤) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV) : uM u ∈ rat2 σ d.Y := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  refine kunf.rat_of_inFrame (b := d.b) (M := Matrix.fromBlocks (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L v) 0 0 M) ?_
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.inFrame_uM_k hU, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hM]
  simp [incM, Matrix.fromBlocks_map]
theorem cj_rat_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {u : Fin L.n → AE F E} (hu : u ∈ L.ratV)
    {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β ∈ nF σ d.Y d.b := by
  obtain ⟨v, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k hu
  obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_inc_k hU v
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 hβ
  refine kunf.mem_nF_iff.2 ⟨_root_.PositivityTheory.SiegelWeilFormula.Act.C1.unipotentFirstMatrix L (-v) * T * M, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.neg_incV_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_inc_k, hT, hM, kunf.incM_mul', kunf.incM_mul']
theorem mul_Au_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ a, X a L.i₀ = 0) (u : Fin L.n → AE F E) :
    X * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u = X := by
  have h : ∀ j, X * Matrix.single L.i₀ (L.em j) (u j) = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, zero_mul]
    · exact mul_zero _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.mul_add, Matrix.mul_one, Finset.mul_sum, h, Finset.sum_const_zero, add_zero]
theorem AuT_mul_k (X : Matrix (Fin d.n) (Fin d.n) (AE F E)) (hX : ∀ b, X L.i₀ b = 0) (u : Fin L.n → AE F E) :
    (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L u)ᵀ * X = X := by
  have h : ∀ j, (Matrix.single L.i₀ (L.em j) (u j))ᵀ * X = 0 := fun j => by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    split_ifs with h
    · rw [← h.1, hX, mul_zero]
    · exact zero_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_sum, Matrix.add_mul, Matrix.one_mul,
    Finset.sum_mul, h, Finset.sum_const_zero, add_zero]
theorem trace_cj_k (hU : L.UData uM ν 𝓤) (hN : IsNMap d.b nb) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') (u : Fin L.n → AE F E) (β : nA σ d.Y d.b) :
    Matrix.trace (T.1.1 * (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_k hU hN u β).1) = Matrix.trace (T.1.1 * β.1) := by
  have h1 : T.1.1 * _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Au_k L (-u) = T.1.1 := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.mul_Au_k _ (fun a => (hT.1 a).2) _
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1 = T.1.1 := by
    apply Matrix.map_injective (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cA_injective_k d)
    show (_root_.PositivityTheory.SiegelWeilFormula.Act.C1.Ap_k hU u * T.1.1).map (cA σ) = T.1.1.map (cA σ)
    rw [kunf.map_cA_mul, _root_.PositivityTheory.SiegelWeilFormula.Act.C1.Apc_k]
    exact _root_.PositivityTheory.SiegelWeilFormula.Act.C1.AuT_mul_k _ (fun b => by simp [(hT.1 b).1]) _
  rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C1.cj_val_k, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2]
end PositivityTheory.SiegelWeilFormula.Act.C1
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.UnipotentParamRationalMatrix
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem rel_aniso_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, _root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm
theorem unipotentParam_rational_matrix (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) : ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]
def relH_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  -(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)
theorem relH_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (_root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε β) a) b
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by
    intro x
    simp [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn
theorem relH_eq_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β)ᵀ) := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]
  rw [mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]
theorem rel_Td_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_nA_cond_k d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet
theorem relAlg_pf_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.RelAlg_k := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_eta_k d ε hε
  refine ⟨η, fun β => ⟨_root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_k d η β, _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_mem_k d ε hε η hη hση β⟩, hη, hherm, fun β => _root_.PositivityTheory.SiegelWeilFormula.KWhit.relH_eq_k d η hη β,
    fun y hy => _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_aniso_k d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η) y y = ∑ i, σ (y i) * (_root_.PositivityTheory.SiegelWeilFormula.KWhit.Jd_k d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.unipotentParam_rational_matrix d T
    exact ⟨T₀, h0, _root_.PositivityTheory.SiegelWeilFormula.KWhit.rel_Td_k d ε hε η hη hση T hT T₀ h0⟩
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

