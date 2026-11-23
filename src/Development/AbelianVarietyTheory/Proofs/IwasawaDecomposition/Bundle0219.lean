module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumNormEmb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.TopIntegrand

def extId {R : Type} [CommRing R] {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (P : Matrix (Fin n) (Fin m) R)
    (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R := 1 + M * (x - 1) * P

theorem map_emb {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {m n : ℕ} (M : Matrix (Fin m) (Fin n) R)
    (P : Matrix (Fin n) (Fin m) R) (x : Matrix (Fin n) (Fin n) R) :
    (extId M P x).map f = extId (M.map f) (P.map f) (x.map f) := by
  rw [extId, extId, Matrix.map_add _ (map_add f), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub f),
    Matrix.map_one _ (map_zero f) (map_one f), Matrix.map_one _ (map_zero f) (map_one f)]

theorem sum_norm_emb {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (P : Matrix (Fin n) (Fin m) ℂ) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Matrix (Fin n) (Fin n) ℂ,
      ∑ i, ∑ j, ‖extId M P x i j‖ ≤ c * (1 + ∑ k, ∑ l, ‖x k l‖) := by
  refine ⟨∑ i, ∑ j, (‖(1 - M * P : Matrix (Fin m) (Fin m) ℂ) i j‖ + ∑ l, ∑ k, ‖M i k‖ * ‖P l j‖), by positivity, fun x => ?_⟩
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have e : extId M P x = (1 - M * P) + M * x * P := by
    rw [extId, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]; abel
  have hS : 0 ≤ ∑ k, ∑ l, ‖x k l‖ := by positivity
  have hx : ∀ k l, ‖x k l‖ ≤ 1 + ∑ k, ∑ l, ‖x k l‖ := fun k l =>
    ((Finset.single_le_sum (f := fun l => ‖x k l‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun k => ∑ l, ‖x k l‖) (fun _ _ => by positivity) (Finset.mem_univ k))).trans
      (by linarith)
  rw [e, Matrix.add_apply, add_mul]
  refine (norm_add_le _ _).trans (add_le_add (le_mul_of_one_le_right (norm_nonneg _) (by linarith)) ?_)
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_mul, mul_right_comm]
  exact mul_le_mul_of_nonneg_left (hx k l) (by positivity)

variable {D : D7} {A B : HSp D} {ι : B.V →ₗ[D.host.E] A.V} (hι : HSpace.IsIsomEmb B A ι)

abbrev emb : GA D B →* GA D A := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embA D.sp.cm B A ι hι

theorem matHom_emb (h : GA D B) : (matHom A (emb hι h)).1 =
    extId ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.embMat B A ι).map (incA D)) ((GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projMat D.sp.cm B A ι).map (incA D))
      (matHom B h).1 := rfl

theorem emb_ker {S : Type} [CommRing S] (f : AF D.host.F ⊗[D.host.F] D.host.E →+* S) (h : GA D B)
    (hh : Formalism.UG.bc f (matHom B h) = 1) : Formalism.UG.bc f (matHom A (emb hι h)) = 1 := by
  have h1 : (matHom B h).1.map f = 1 := congrArg Units.val hh
  refine Units.ext ?_
  change (matHom A (emb hι h)).1.map f = 1
  rw [matHom_emb, map_emb, h1, extId, sub_self, Matrix.mul_zero, Matrix.zero_mul, add_zero]

theorem emb_GfC {h : GA D B} (hh : h ∈ GfC B) : emb hι h ∈ GfC A := emb_ker hι _ h hh

theorem emb_GinfC {h : GA D B} (hh : h ∈ GinfC B) : emb hι h ∈ GinfC A := emb_ker hι _ h hh

theorem infMat_emb (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) : ∃ M P, ∀ h : GA D B,
    infMat D.sp.cm.sig A.gram θ (emb hι h) = extId M P (infMat D.sp.cm.sig B.gram θ h) := by
  refine ⟨?_, ?_, fun h => ?_⟩
  rotate_left 2
  change ((matHom A (emb hι h)).1.map
    (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom).map θ = _
  rw [matHom_emb, map_emb, map_emb]
  rfl

theorem normInf_emb (θ : InfF D) : ∃ c : ℝ, 0 ≤ c ∧ ∀ h : GA D B,
    normInf θ A (emb hι h) ≤ c * (1 + normInf θ B h) := by
  choose M P hMP using fun τ => infMat_emb hι (θ τ)
  choose c hc0 hc using fun τ => sum_norm_emb (M τ) (P τ)
  refine ⟨∑ τ, 2 * c τ, Finset.sum_nonneg fun τ _ => by have := hc0 τ; positivity, fun h => ?_⟩
  rw [Finset.sum_mul, normInf]
  refine Finset.sum_le_sum fun τ _ => ?_
  have h0 : ∑ i, ∑ j, (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖) ≤
      normInf θ B h := Finset.single_le_sum (f := fun τ => ∑ i, ∑ j,
        (‖infMat D.sp.cm.sig B.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig B.gram (θ τ) h⁻¹ i j‖))
      (fun _ _ => by positivity) (Finset.mem_univ τ)
  simp only [Finset.sum_add_distrib] at h0 ⊢
  rw [← map_inv, hMP, hMP]
  have h1 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h)
  have h2 := hc τ (infMat D.sp.cm.sig B.gram (θ τ) h⁻¹)
  have h3 := mul_le_mul_of_nonneg_left h0 (hc0 τ)
  have h4 := mul_nonneg (hc0 τ) (GlobalTheory.SmoothForms.normInf_nonneg (θ := θ) h)
  nlinarith

theorem emb_moderate {θ : InfF D} (hθ : IsInfFam θ) (hc : Continuous (emb hι)) (hQ : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A)
    {φ : GA D A → ℂ} (hφ : IsAutFunSm θ A φ) :
    ∃ (N : ℕ) (C : ℝ), ∀ g, ‖φ (emb hι g)‖ ≤ C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ N := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨S, C₀, M, hS⟩ := GlobalTheory.SmoothForms.reduction hθ ((_root_.GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ B) (U.comap (emb hι)) (hU.preimage hc)
  obtain ⟨N, hN⟩ := hφ.growth
  choose C hC using hN [] (by simp)
  obtain ⟨c, hc0, hc⟩ := normInf_emb hι θ
  refine ⟨M * N, (∑ x ∈ S, |C (emb hι x)|) * (c * (1 + |C₀|)) ^ N, fun g => ?_⟩
  obtain ⟨γ, hγ, x, hx, a, ha, k, hk, hk', e, hb⟩ := hS g
  rw [← hφ.left _ (hQ γ hγ), ← map_mul, e, map_mul, map_mul, hUφ _ hk (emb_GfC hι hk'), pow_mul, mul_assoc, ← mul_pow]
  have h1 : (1 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M :=
    one_le_pow₀ (by exact_mod_cast GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.one_le_height θ B g)
  have h2 : normInf θ A (emb hι a) ≤ c * (1 + |C₀|) * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ B g : ℝ) ^ M := by
    refine (hc a).trans ?_
    rw [mul_assoc, add_mul, one_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add h1 (hb.trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (zero_le_one.trans h1)))) hc0
  exact (hC _ _ (emb_GinfC hι ha)).trans (mul_le_mul ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |C (emb hι x)|) (fun _ _ => abs_nonneg _) hx))
    (pow_le_pow_left₀ (GlobalTheory.SmoothForms.normInf_nonneg _) h2 N) (pow_nonneg (GlobalTheory.SmoothForms.normInf_nonneg _) N)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _))

theorem topInt (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) : TopInt D := by
  intro θ hθ A B ι hι μ 𝓕 hq s hs φ φ' hφ hφ'
  obtain rfl : s = emb hι := funext fun h => (GlobalTheory.AutFunCompare.embRel_iff A B ι hι _ _).1 (hs h)
  obtain ⟨s, hc, hrel, hQ⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D A B ι hι
  have e : ∀ h, emb hι h = s h := fun h => (hrel h _).1 (hs h)
  have hc' : Continuous (emb hι) := by rw [show ⇑(emb hι) = s from funext e]; exact hc
  have hQ' : ∀ γ ∈ GQ B, emb hι γ ∈ GQ A := fun γ hγ => e γ ▸ hQ γ hγ
  obtain ⟨N, C, hC⟩ := emb_moderate hι hθ hc' hQ' hφ
  obtain ⟨K, hK⟩ := (GlobalTheory.CuspDecay.isRapidDecay_of_cuspForm hP hθ hφ'.1 hφ'.2).mul_bounded
    (ψ := fun g => φ (emb hι g)) (fun γ hγ g => by simp only [map_mul]; exact hφ.left _ (hQ' γ hγ) _) hC
  have : BorelSpace (GA D B) := ⟨rfl⟩
  refine Measure.integrableOn_of_bounded (M := K)
    (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol B μ 𝓕 hq.1 hq.2).ne
    (((hφ.cont.comp hc').star.mul hφ'.1.cont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
  rw [norm_mul, norm_star]
  exact hK g

end GlobalTheory.Mem.TopIntegrand

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistConeVanishing
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

def TwistConeVanishing {X : Scheme.{0}} (A N : LB X) (F : X.Modules) : Prop :=
  ∃ j₀ : ℕ, ∀ j m : ℕ, j₀ ≤ j → m ≤ j → ∀ p, 0 < p →
    Subsingleton (coh (twist F (tens (lbPow A j) (lbPow N m))) p)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.InertPlaceConj

open GlobalTheory.SelfDualGenus

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isInertAt_of_not_split (w : HeightOneSpectrum (𝓞 E))
    (hu : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) (hs : ¬ IsSplitAt w) :
    Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w := by
  classical
  haveI := w.isPrime
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have hva : v.asIdeal = w.asIdeal.under (𝓞 (maximalRealSubfield E)) := rfl
  have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) :=
    FaithfulSMul.algebraMap_injective _ _
  unfold Formalism.UG.IsInertAt
  rw [hva]
  have hle : (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal := Ideal.map_comap_le
  have h1 : Ideal.ramificationIdx' (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal = 1 := by
    letI := Localization.AtPrime.algebraOfLiesOver (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal
    exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff w.ne_bot hle).2
      ((Algebra.isUnramifiedAt_iff_map_eq (𝓞 (maximalRealSubfield E))
        (w.asIdeal.under (𝓞 (maximalRealSubfield E))) w.asIdeal).1 hu).2
  have h2 : ¬ (w.asIdeal.under (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≤ w.asIdeal ^ 2 :=
    fun h => (Ideal.ramificationIdx'_ne_one_iff hle).2 h h1
  set I := Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))
    (w.asIdeal.under (𝓞 (maximalRealSubfield E))) with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    exact v.ne_bot
  have hfac : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors I, p = w.asIdeal := by
    intro p hp
    obtain ⟨hpp, hpl⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hp
    have hp0 : p ≠ ⊥ := fun h0 => hI0 (le_bot_iff.1 (h0 ▸ hpl))
    let u : HeightOneSpectrum (𝓞 E) := ⟨p, hpp, hp0⟩
    have hu' : u.under (𝓞 (maximalRealSubfield E)) = v := by
      ext1
      exact (v.isMaximal.eq_of_le (Ideal.comap_ne_top _ hpp.ne_top)
        (Ideal.map_le_iff_le_comap.1 hpl)).symm
    by_contra hne
    exact hs ⟨u, fun h => hne (congrArg HeightOneSpectrum.asIdeal h), hu'⟩
  obtain ⟨n, hn⟩ : ∃ n, I = w.asIdeal ^ n := by
    refine ⟨Multiset.card (UniqueFactorizationMonoid.normalizedFactors I), ?_⟩
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI0]
    rw [Multiset.eq_replicate_card.2 hfac, Multiset.prod_replicate, Multiset.card_replicate]
  rcases n with _ | _ | n
  · exfalso
    rw [hn, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact w.isPrime.ne_top hle
  · simpa using hn
  · exact absurd (hn ▸ Ideal.pow_le_pow_right (by omega)) h2

theorem exists_sub_conj_notMem_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ x : 𝓞 E, x - IsCMField.ringOfIntegersComplexConj E x ∉ w.asIdeal := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have := v.isPrime
  have := w.isPrime
  have : w.asIdeal.LiesOver v.asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[maximalRealSubfield E] E) v.asIdeal w.asIdeal
  have hsq : ¬ Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal ≤ w.asIdeal ^ 2 := by
    rw [h']
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal (E ≃ₐ[maximalRealSubfield E] E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    not_ne_iff.1 (mt (Ideal.ramificationIdx'_ne_one_iff (le_of_eq h')).1 hsq)] at hcard
  by_contra hn
  push_neg at hn
  have hs : IsCMField.complexConj E ∈ w.asIdeal.inertia (E ≃ₐ[maximalRealSubfield E] E) :=
    AddSubgroup.mem_inertia.2 fun x => by
      have := w.asIdeal.neg_mem (hn x)
      rw [neg_sub] at this
      exact this
  rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
  exact IsCMField.complexConj_ne_one E hs

theorem exists_isUnramInv_of_inert (w : HeightOneSpectrum (𝓞 E))
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E (w.under (𝓞 (maximalRealSubfield E))) w) :
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧
      IsUnramInv ϖ s (Ideal.absNorm (w.under (𝓞 (maximalRealSubfield E))).asIdeal) := by
  set v := w.under (𝓞 (maximalRealSubfield E)) with hv
  have h' : Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal := h
  have hc : Mem.Chr.ConjPl (IsCMField.complexConj E).toRingEquiv w w := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = IsCMField.ringOfIntegersComplexConj E x := RingOfIntegers.ext hxy
    rw [e]
    refine ⟨GlobalTheory.InertConj.conj_mem_of_inert h, fun hx => ?_⟩
    have h2 := GlobalTheory.InertConj.conj_mem_of_inert h hx
    have e2 : IsCMField.ringOfIntegersComplexConj E (IsCMField.ringOfIntegersComplexConj E x) = x := by
      ext; simp
    rwa [e2] at h2
  obtain ⟨σ, σ1, σ2, σ3⟩ := UnramCompletion.exists_ringEquiv w _ hc
  have σ2' : ∀ x : E, σ (algebraMap E (w.adicCompletion E) x) =
      algebraMap E (w.adicCompletion E) (IsCMField.complexConj E x) := σ2
  obtain ⟨s, hs, hs2⟩ : ∃ s ∈ v.asIdeal,
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∉ w.asIdeal ^ 2 := by
    by_contra hn
    push_neg at hn
    have h1 : w.asIdeal ≤ w.asIdeal ^ 2 := by
      conv_lhs => rw [← h']
      exact Ideal.map_le_iff_le_comap.2 hn
    exact (Ideal.pow_lt_self _ w.ne_bot w.isPrime.ne_top 2 le_rfl).not_ge h1
  have hs1 : algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s ∈ w.asIdeal :=
    h' ▸ Ideal.mem_map_of_mem _ hs
  have hval : ∀ a : 𝓞 E, Valued.v (algebraMap E (w.adicCompletion E) (a : E)) =
      w.valuation E (algebraMap (𝓞 E) E a) := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hinv : ∀ x, σ (σ x) = x := by
    intro x
    refine congrFun (UnramCompletion.ringHom_ext_of_continuous w (f := fun x => σ (σ x))
      (σ1.comp σ1) continuous_id fun k => ?_) x
    simp [σ2']
  have hres : ∃ x, Valued.v x ≤ 1 ∧ Valued.v ((σ : w.adicCompletion E →+* w.adicCompletion E) x - x) = 1 := by
    obtain ⟨x, hx⟩ := exists_sub_conj_notMem_of_inert w h
    refine ⟨algebraMap E _ (x : E), ?_, ?_⟩
    · rw [hval]; exact w.valuation_le_one x
    · change Valued.v (σ _ - _) = 1
      rw [Valuation.map_sub_swap, σ2', ← map_sub]
      exact (hval (x - IsCMField.ringOfIntegersComplexConj E x)).trans
        ((HeightOneSpectrum.valuation_eq_one_iff_notMem w).2 hx)
  have hfix : (σ : w.adicCompletion E →+* w.adicCompletion E)
      (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) =
      algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E) := by
    change σ _ = _
    rw [σ2']
    congr 1
    exact IsCMField.complexConj_apply_eq_self E (s : maximalRealSubfield E)
  have hunif : IsUnifV E w (algebraMap E _ (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) s : E)) := by
    unfold IsUnifV
    rw [hval, HeightOneSpectrum.valuation_of_algebraMap]
    exact UnramCompletion.intValuation_eq_of_notMem_sq w hs1 hs2
  refine ⟨σ, _, σ2', hinv, σ3, hfix, hunif, ?_, ?_, ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := hres
    exact ⟨x, hx1, hx2⟩
  · have a : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have b : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  · have hN : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
      rw [← h', Ideal.absNorm_algebraMap,
        ← Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E]
      congr 1
      exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
        (𝓞 E) E).symm
    rw [← hN]
    exact Formalism.UG.P.tjcosets_card_residue w

theorem exists_conj_isUnramInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)),
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal → ¬ IsSplitAt w →
    ∃ (s : w.adicCompletion E →+* w.adicCompletion E) (ϖ : w.adicCompletion E) (q : ℕ),
      (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) ∧ IsUnramInv ϖ s q := by
  intro E _ _ _ w hu hs
  obtain ⟨s, ϖ, h1, h2⟩ := exists_isUnramInv_of_inert w (isInertAt_of_not_split w hu hs)
  exact ⟨s, ϖ, _, h1, h2⟩

end GlobalTheory.InertPlaceConj
end

