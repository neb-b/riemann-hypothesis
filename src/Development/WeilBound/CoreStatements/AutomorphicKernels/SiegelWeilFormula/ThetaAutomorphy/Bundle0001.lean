module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.CountableMat
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0006
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0009
public import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.CayleyTransform.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ContinuousTt
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option maxHeartbeats 400000

theorem stepA (hP : TPar) (hT : TTheta) (d : SD σ) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) {nb : nA σ d.Y d.b → d.G}
    (hnb : IsNMap (σ := σ) (Y := d.Y) d.b nb) (x : d.G) (β : nA σ d.Y d.b) (g : UA σ d.A.J) :
    thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X : Matrix (Fin d.m) (Fin d.n) E,
      d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram (incM F X) (incM F X)))) * d.T (d.om x Φ) (tr d g X) := by
  have hΨ : d.om x Φ ∈ d.sch := d.ok.dbl.weil.2.1.pres x Φ hΦ
  have hΨg : d.S g (d.om x Φ) ∈ d.sch := d.ok.dbl.lin.pres g _ hΨ
  have hn : d.om (nb β) (d.S g (d.om x Φ)) ∈ d.sch := d.ok.dbl.weil.2.1.pres (nb β) _ hΨg
  rw [map_mul, Module.End.mul_apply, (hT F E σ d Φ hΦ).2 x g, ← ((hT F E σ d _ hn).1).tsum_eq]
  refine tsum_congr fun X => ?_
  rw [(hP F E σ d _ hΨg).1 (nb β) β.1 (hnb β) (incM F X), (hP F E σ d _ hΨ).2.2 g (incM F X)]
  rfl

theorem meas_tr (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    AEMeasurable (fun g => ‖f (tr d g X)‖ₑ) (d.μ.restrict d.D) :=
  ((cont_tr d hf X).enorm.measurable).aemeasurable

theorem tbdd (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∃ K : ℝ, ∀ g : UA σ d.A.J, Summable (fun X => ‖f (tr d g X)‖) ∧ ∑' X, ‖f (tr d g X)‖ ≤ K := by
  open Kdil.Tb in
  obtain ⟨Ω, hΩ, cov⟩ := (cpt hS d).cov
  obtain ⟨u, hu, hb⟩ := bound_cpt d f hf Ω hΩ
  refine ⟨∑' ξ, u ξ, fun h => ?_⟩
  obtain ⟨γ, hγ, hγΩ⟩ := cov h
  obtain ⟨e, he⟩ := reindex d f γ hγ
  have key : (fun X => ‖f (mat h⁻¹ * incM F X)‖) = (fun Y => ‖f (mat (γ * h)⁻¹ * incM F Y)‖) ∘ e := by
    funext X
    exact congrArg norm (he h X).symm
  have hs : Summable (fun Y => ‖f (mat (γ * h)⁻¹ * incM F Y)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun Y => hb _ hγΩ Y) ((xi d).summable_iff.2 hu)
  change Summable (fun X => ‖f (mat h⁻¹ * incM F X)‖) ∧
    ∑' X, ‖f (mat h⁻¹ * incM F X)‖ ≤ ∑' ξ, u ξ
  refine ⟨?_, ?_⟩
  · rw [key]; exact e.summable_iff.2 hs
  · rw [key]
    show ∑' X, ‖f (mat (γ * h)⁻¹ * incM F (e X))‖ ≤ _
    rw [e.tsum_eq (fun Y => ‖f (mat (γ * h)⁻¹ * incM F Y)‖)]
    calc ∑' Y, ‖f (mat (γ * h)⁻¹ * incM F Y)‖ ≤ ∑' Y, u (xi d Y) :=
          hs.tsum_le_tsum (fun Y => hb _ hγΩ Y) ((xi d).summable_iff.2 hu)
      _ = ∑' ξ, u ξ := (xi d).tsum_eq u

theorem pt_bdd (d : SD σ) {f : Mx F E d.m d.n → ℂ} (g : UA σ d.A.J) (s : Set (Matrix (Fin d.m) (Fin d.n) E)) {K : ℝ}
    (hsum : Summable (fun X => ‖f (tr d g X)‖)) (hle : ∑' X, ‖f (tr d g X)‖ ≤ K) :
    ∑' X : s, ‖f (tr d g X.1)‖ₑ ≤ ENNReal.ofReal K := by
  calc ∑' X : s, ‖f (tr d g X.1)‖ₑ ≤ ∑' X, ‖f (tr d g X)‖ₑ :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective (fun X => ‖f (tr d g X)‖ₑ)
    _ = ∑' X, ENNReal.ofReal ‖f (tr d g X)‖ := tsum_congr fun X => (ofReal_norm _).symm
    _ = ENNReal.ofReal (∑' X, ‖f (tr d g X)‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hsum).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hle

theorem lint_fin (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM)
    (s : Set (Matrix (Fin d.m) (Fin d.n) E)) :
    ∑' X : s, ∫⁻ g in d.D, ‖f (tr d g X.1)‖ₑ ∂d.μ ≠ ⊤ := by
  haveI := countable_mat (E := E) d.m d.n
  obtain ⟨K, hK⟩ := tbdd hS d hf
  have hfin : d.μ d.D < ⊤ := (cpt hS d).fin d.μ d.D d.ok.haar d.ok.dom
  rw [← lintegral_tsum (f := fun (X : s) g => ‖f (tr d g X.1)‖ₑ) fun X => meas_tr d hf X.1]
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
    ((lintegral_mono fun g => pt_bdd d g s (hK g).1 (hK g).2).trans (setLIntegral_const _ _).le)

theorem lint_fin_all (hS : GlobalTheory.Published.SiegelSetUnitary) (d : SD σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) :
    ∑' X, ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ ≠ ⊤ := by
  have := lint_fin hS d hf Set.univ
  rwa [tsum_univ (f := fun X => ∫⁻ g in d.D, ‖f (tr d g X)‖ₑ ∂d.μ)] at this

theorem continuous_tt (d : SD σ) : Continuous (d.tt) := by
  have h1 : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.trace (AF F) (AE F E))
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact h1.comp (continuous_finsetSum _ fun i _ => continuous_id.matrix_elem i i)

theorem thetaCoef_at (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij) (hP : TPar) (hT : TTheta) (d : SD σ)
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
  set H : Matrix (Fin d.m) (Fin d.n) E → ℂ := fun X => ∫ g in d.D, f (tr d g X) ∂d.μ with hH
  have hmeas : ∀ X, AEStronglyMeasurable (fun g => f (tr d g X)) (d.μ.restrict d.D) :=
    fun X => (cont_tr d hf X).aestronglyMeasurable
  have hcb : Continuous fun β : nA σ d.Y d.b => β.1 := continuous_subtype_val
  have hec : ∀ X, Continuous fun β => e β X := fun X =>
    hψc.comp ((continuous_const.mul ((continuous_tt d).comp (hcb.matrix_mul continuous_const))).neg)
  have hχc : Continuous χ := hψc.comp (((continuous_tt d).comp (continuous_const.matrix_mul hcb)).neg)

  have hI : ∀ β, d.I Φ (nb β * x) = c • ∑' X, e β X * H X := fun β => by
    show PositivityTheory.SiegelWeilFormula.thetaMean d.om d.S d.μ d.D Φ (nb β * x) = _
    rw [PositivityTheory.SiegelWeilFormula.thetaMean, setAverage_eq]
    congr 1
    have hA' : ∀ g, thetaSum F (d.om (nb β * x) (d.S g Φ)) = ∑' X, e β X * f (tr d g X) :=
      fun g => stepA hP hT d hΦ hc.1 x β g
    simp only [hA']
    rw [integral_tsum (f := fun X g => e β X * f (tr d g X)) (fun X => (hmeas X).const_mul _) ?_]
    · exact tsum_congr fun X => integral_const_mul _ _
    · simpa only [he, enorm_mul, hen, one_mul] using lint_fin_all hS d hf

  have hO : ∀ X, ∫ β in 𝓖, e β X * χ β ∂lam = if G X = (-2 : ℤ) • T.1.1 then 1 else 0 := fun X => by
    obtain ⟨hm, S₀, hS₀⟩ := gram_mem d X T
    simp only [he, hχ, chr_comb]
    rw [orth d hc _ hm ⟨S₀, hS₀⟩]
    simp only [half_eq_iff]
    rfl

  have h1 : ∀ β, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) =
      c • ∑' X, e β X * χ β * H X := fun β => by
    rw [hI β, smul_mul_assoc, ← tsum_mul_right]
    congr 1
    exact tsum_congr fun X => by simp only [hχ, SD.tt]; ring
  have hlam : lam 𝓖 = 1 := hc.2.2.2
  have h2 : ∑' X, ∫⁻ β in 𝓖, ‖e β X * χ β * H X‖ₑ ∂lam ≠ ⊤ := by
    simp only [he, hχ, enorm_mul, hen, one_mul, lintegral_const, Measure.restrict_apply_univ, hlam, mul_one]
    refine ne_top_of_le_ne_top (lint_fin_all hS d hf) (ENNReal.tsum_le_tsum fun X => ?_)
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
      f (tr d g X.1) ∂d.μ) = c • ∑' X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E)), H X.1
    rw [setAverage_eq, integral_tsum (f := fun (X : ({X | G X = (-2 : ℤ) • T.1.1} : Set (Matrix (Fin d.m) (Fin d.n) E))) g =>
      f (tr d g X.1)) (fun X => hmeas X.1) (lint_fin hS d hf {X | G X = (-2 : ℤ) • T.1.1})]
  show ∫ β in 𝓖, d.I Φ (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) ∂lam = _
  rw [integral_congr_ae (Eventually.of_forall h1), integral_smul,
    integral_tsum (f := fun X β => e β X * χ β * H X)
      (fun X => (((hec X).mul hχc).mul continuous_const).aestronglyMeasurable) h2, h4, ← h3]
  congr 1
  exact tsum_congr fun X => by rw [integral_mul_const, hO X]

theorem thetaCoef (hS : GlobalTheory.Published.SiegelSetUnitary) (hB : TBij) (hP : TPar) (hT : TTheta) : ThetaCoef :=
  fun _ _ _ _ _ _ _ _ d _ hΦ _ _ _ hc T x => thetaCoef_at hS hB hP hT d hΦ hc T x

end PositivityTheory.SiegelWeilFormula.Tauto

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaSumRationalInvariant
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Tauto

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}


open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in
theorem split_core {m n : ℕ} {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ : E}
    (hq : IsQuad σ δ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (hA : IsHerm σ JA)
    (hB : IsHerm σ JB)
    (d' : Darboux (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) δ) (incM F JA) (incM F (dbl JB))) κ)
    (d₀ : Matrix (Fin m) (Fin n ⊕ Fin n) E ≃ₗ[F] (κ → F) × (κ → F))
    (hd : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)))
    (χ : Chr F E) (hχ : IsHecke F E χ)
    (om' : UG (cA σ) (incM F (dbl JB)) →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsSplitting (adeleClass F) ψ d' (actB (cA σ)) om')
    (hR : SiegelRule (cA σ) (adeleClass F) ψ (inclR (F := F) (AF F) δ) (incM F JA) (incM F (dbl JB)) d' χ
      (diagCols (Fin n)) om')
    (g : UG (cA σ) (incM F (dbl JB)))
    (hg : ∃ γ₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E,
      ((g : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = incM F γ₀) :
    ∀ Ψ ∈ schA F κ, thetaSum F (om' g Ψ) = thetaSum F Ψ := by
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  have hL : IsLagr σ (dbl JB) (diagCols (Fin n)) := isLagr_diagCols (R := F) σ JB
  have hC : (diagCols (Fin n) : Matrix (Fin n ⊕ Fin n) (Fin n) E).map
      (fun z => ((1 : AF F) ⊗ₜ[F] z : AE F E)) = diagCols (Fin n) := by
    have e1 : (1 : Matrix (Fin n) (Fin n) E).map (fun z => ((1 : AF F) ⊗ₜ[F] z : AE F E)) = 1 :=
      Matrix.map_one _ (map_zero (inclR (F := F) (AF F))) (map_one (inclR (F := F) (AF F)))
    simp only [diagCols, Matrix.fromRows_map, e1]
  have hχ' : ∀ (z : E) (u : (AE F E)ˣ), (u : AE F E) = (1 : AF F) ⊗ₜ[F] z → χ u = 1 := fun z u hu => by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
      (algebraMap F (AF F)).injective).nontrivial
    have hz : z ≠ 0 := by
      rintro rfl
      exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
    rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
    exact hχ.2 _
  exact GlobalTheory.CompanionTheory.ThetaMember.split_of_eq F E σ δ (Fin m) (Fin n ⊕ Fin n) κ JA (dbl JB)
    ψ hψ.1 (PositivityTheory.ThKF0.isStd_ne_one hψ) hψ.2.1 hq hA (GlobalTheory.CompanionTheory.ThetaMember.isHerm_dbl hB)
    (incM F (dbl JB)) rfl d' d₀ hd χ (Fin n) (diagCols (Fin n)) (diagCols (Fin n)) hC om' hχ' hL hS hR g hg


omit [NumberField F] [NumberField E] in
theorem split_resc {R K : Type} [CommRing R] [CommRing K] [Algebra R K] [Invertible (2 : R)] {c : K →ₐ[R] K}
    {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
    {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {C : TestClass R} {ψ : AddChar R ℂ} {d : Darboux (symp c ξ JA JB) κ}
    {χ : Kˣ →* Circle} {Cy : Matrix β ν K} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hS : IsSplitting C ψ d (actB c) om) (hR : SiegelRule c C ψ ξ JA JB d χ Cy om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsSplitting C ψ d' (actB c) om' ∧ SiegelRule c C ψ ξ' JA' JB' d' χ Cy om' ∧
      ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  have hU : UG c (v • JB) = UG c JB := PositivityTheory.ThKF0.Resc.ug_smul hv JB
  refine ⟨⟨d.e, fun w w' => (PositivityTheory.ThKF0.Resc.symp_smul h JA JB w w').trans (d.form w w')⟩,
    om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
    fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hU.le p) t hp,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩


open PositivityTheory.ThKF0.Resc in
set_option maxHeartbeats 1000000 in
theorem theta_sum_rational_invariant (d : SD σ) (γ : d.G) (hγ : γ ∈ rat2 σ d.Y) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) :
    thetaSum F (d.om γ Ψ) = thetaSum F Ψ := by
  have hσ : IsCMExt F E σ := d.cm
  have hψ : IsStd d.B.ψ := d.std
  have h2 : Module.finrank F E = 2 := hσ.2.2.1
  haveI : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  obtain ⟨-, hS, hR⟩ := d.ok.dbl.weil

  have hYd : d.Y.J.det ≠ 0 := by
    obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
    intro hz
    have hee : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    have hM : (Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) *
        Matrix.fromBlocks 0 (((ε : ℤ) : E) • 1) 1 0 = 1 := by
      rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
      simp [smul_smul, hee]
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, ← hε, Matrix.det_mul, Matrix.det_mul, dbl, Matrix.det_fromBlocks_zero₂₁, hz] at h1
    simp at h1

  have hκ : Fintype.card d.κ = Fintype.card (Fin d.m) * Fintype.card (Fin d.n ⊕ Fin d.n) := by
    have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
    let bE : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E h2
    let bA := Algebra.TensorProduct.basis (AF F) bE
    haveI : Module.Free (AF F) (AE F E) := Module.Free.of_basis bA
    haveI : Module.Finite (AF F) (AE F E) := Module.Finite.of_basis bA
    have e := d.dd.e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_eq_card_basis bA, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card] at e
    simp only [Fintype.card_fin, Fintype.card_sum] at e ⊢
    omega
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord h2 hκ d.dd.e d.ok.dbl.rat

  obtain ⟨a, b, hab, hA, hB⟩ : ∃ a b : E, -1 = δ * a * b ∧ IsHerm σ (a • d.A.J) ∧ IsHerm σ (b • d.Y.J) := by
    rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, -δ⁻¹, by field_simp, ?_, ?_⟩
      · rw [one_smul]; exact ⟨hA.herm, (herm_det hA).isUnit⟩
      · refine ⟨fun i j => by simp [hY i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hYd
    · refine ⟨-δ⁻¹, 1, by field_simp, ?_, ?_⟩
      · refine ⟨fun i j => by simp [hA.skew i j, hq.anti], Ne.isUnit ?_⟩
        rw [Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) (skew_det hA)
      · rw [one_smul]; exact ⟨hY, hYd.isUnit⟩
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hξ : (-1 : AE F E) = inclR (F := F) (AF F) δ * inclR (F := F) (AF F) a * inclR (F := F) (AF F) b := by
    rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]
  have hJA : incM F (a • d.A.J) = inclR (F := F) (AF F) a • incM F d.A.J := by
    ext i j; simp [incM]
  have hJB : incM F (dbl (b • d.Y.J)) = inclR (F := F) (AF F) b • dbl (incM F d.Y.J) := by
    ext (i | i) (j | j) <;> simp [incM, dbl]
  obtain ⟨d', om', he, hS', hR', hgg⟩ := split_resc (c := cA σ) (C := adeleClass F) (ψ := d.B.ψ) (κ := d.κ) hξ
    (hb.isUnit.map (inclR (F := F) (AF F))) hJA hJB hS.toIsSplitting hR
  have hd' : ∀ x, d'.e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) :=
    fun x => by rw [he]; exact hd₀ x
  obtain ⟨g', hg'1, hg'2⟩ := hgg γ
  have hg : ∃ γ₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E,
      ((g' : GL (Fin d.n ⊕ Fin d.n) (AE F E)) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) = incM F γ₀ := by
    obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
    refine ⟨g₀, ?_⟩
    rw [hg'1, ← hg₀]
    rfl
  rw [← hg'2]
  exact split_core hψ hq (a • d.A.J) (b • d.Y.J) hA hB d' d₀ hd' d.χ d.ok.hecke om' hS' hR' g' hg Ψ hΨ

end PositivityTheory.SiegelWeilFormula.Tauto

end
end

