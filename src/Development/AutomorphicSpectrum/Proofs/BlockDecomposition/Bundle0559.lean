module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.WeylSplitting.WeylSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1289
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0518
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0532
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0046
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SubOfNonNil
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IrreducibleSmoothAdmissibleGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ParabolicInductionFiniteLength

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationParameterContinuous
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibParam

open Set Filter

theorem fibre_param_continuous : ∀ (V H Y P : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] [TopologicalSpace P] [T2Space P] [LocallyCompactSpace P] (μ : Measure V) (ν : Measure H) (f : V → Y) (ι : H → Y) (q : V → H) (U : Set V) (fam : H → Measure V), IsOpen U → Continuous q → Function.Injective ι → (∀ v, f v = ι (q v)) → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fam → ∀ ψ : P × V → ℝ, Continuous ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, p.2 ∈ U) → Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ HasCompactSupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ∧ ∀ z ∈ tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)), ∃ v, (z.1, v) ∈ tsupport ψ ∧ q v = z.2 := by
  intro V H Y P _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ ν f ι q U fam hU hq hι hf h ψ hψ hψc hψU
  have hCc : IsCompact (tsupport ψ) := hψc
  have hC₂c : IsCompact (Prod.snd '' tsupport ψ) := hCc.image continuous_snd
  have hC₂U : Prod.snd '' tsupport ψ ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact hψU x hx
  obtain ⟨ρ, hρ1, hρc, hρs, hρ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC₂c hU hC₂U
  have hzero : ∀ p v, v ∉ Prod.snd '' tsupport ψ → ψ (p, v) = 0 := fun p v hv =>
    image_eq_zero_of_notMem_tsupport (fun hh => hv ⟨_, hh, rfl⟩)
  have hsec : ∀ p, (∀ b, Integrable (fun v => ψ (p, v)) (fam b)) ∧
      Continuous (fun b => ∫ v, ψ (p, v) ∂(fam b)) := by
    intro p
    have hgc : Continuous (fun v => ψ (p, v)) := hψ.comp (continuous_const.prodMk continuous_id)
    have hsub : Function.support (fun v => ψ (p, v)) ⊆ Prod.snd '' tsupport ψ :=
      fun v hv => by_contra fun hn => hv (hzero p v hn)
    have hts : tsupport (fun v => ψ (p, v)) ⊆ Prod.snd '' tsupport ψ :=
      closure_minimal hsub hC₂c.isClosed
    have hcs : HasCompactSupport (fun v => ψ (p, v)) :=
      hC₂c.of_isClosed_subset (isClosed_tsupport _) hts
    obtain ⟨i, c⟩ := h.2.2 _ hgc hcs (hts.trans hC₂U)
    exact ⟨fun b => i b (mem_univ b), continuousOn_univ.1 c⟩
  obtain ⟨iρ, cρ⟩ := h.2.2 ρ ρ.continuous hρc hρs
  have hRc : Continuous (fun b => ∫ v, ρ v ∂(fam b)) := continuousOn_univ.1 cρ
  have hR0 : ∀ b, 0 ≤ ∫ v, ρ v ∂(fam b) := fun b => integral_nonneg fun v => (hρ01 v).1
  have hdiff : ∀ (p p' : P) (e : ℝ) (b : H), 0 ≤ e →
      (∀ v ∈ Prod.snd '' tsupport ψ, |ψ (p, v) - ψ (p', v)| ≤ e) →
      |(∫ v, ψ (p, v) ∂(fam b)) - ∫ v, ψ (p', v) ∂(fam b)| ≤ e * ∫ v, ρ v ∂(fam b) := by
    intro p p' e b he hb
    rw [← integral_sub ((hsec p).1 b) ((hsec p').1 b), ← integral_const_mul, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((iρ b (mem_univ b)).const_mul e) (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs]
    by_cases hv : v ∈ Prod.snd '' tsupport ψ
    · rw [hρ1 hv]
      simpa using hb v hv
    · rw [hzero p v hv, hzero p' v hv]
      simpa using mul_nonneg he (hρ01 v).1
  have hcont : Continuous (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) := by
    refine continuous_iff_continuousAt.2 ?_
    rintro ⟨p₀, b₀⟩
    refine Metric.continuousAt_iff'.2 fun ε hε => ?_
    set M : ℝ := (∫ v, ρ v ∂(fam b₀)) + 1 with hMdef
    have hM : 0 < M := by linarith [hR0 b₀]
    set e : ℝ := ε / (2 * M) with hedef
    have he : 0 < e := by positivity
    have ev1 : ∀ᶠ b in 𝓝 b₀, (∫ v, ρ v ∂(fam b)) < M :=
      (isOpen_lt hRc continuous_const).mem_nhds (by simp [hMdef])
    have ev2 : ∀ᶠ b in 𝓝 b₀,
        dist (∫ v, ψ (p₀, v) ∂(fam b)) (∫ v, ψ (p₀, v) ∂(fam b₀)) < ε / 2 :=
      Metric.continuousAt_iff'.1 (hsec p₀).2.continuousAt (ε / 2) (by positivity)
    have hK := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1
      ((ContinuousMap.curry (⟨ψ, hψ⟩ : C(P × V, ℝ))).continuous.tendsto p₀)) _ hC₂c
    have ev3 := Metric.tendstoUniformlyOn_iff.1 hK e he
    filter_upwards [ev3.prod_nhds (ev1.and ev2)] with z hz
    obtain ⟨hz3, hz1, hz2⟩ := hz
    have hd := hdiff z.1 p₀ e z.2 he.le fun v hv => by
      have := hz3 v hv
      have h' : dist (ψ (p₀, v)) (ψ (z.1, v)) < e := this
      rw [Real.dist_eq, abs_sub_comm] at h'
      exact h'.le
    have hbound : e * (∫ v, ρ v ∂(fam z.2)) ≤ ε / 2 := by
      have h1 : e * M = ε / 2 := by
        rw [hedef]
        field_simp
      calc e * (∫ v, ρ v ∂(fam z.2)) ≤ e * M := mul_le_mul_of_nonneg_left hz1.le he.le
        _ = ε / 2 := h1
    rw [Real.dist_eq] at hz2 ⊢
    calc |(∫ v, ψ (z.1, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam b₀)|
        = |((∫ v, ψ (z.1, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam z.2)) +
            ((∫ v, ψ (p₀, v) ∂(fam z.2)) - ∫ v, ψ (p₀, v) ∂(fam b₀))| := by
          congr 1
          ring
      _ ≤ _ := abs_add_le _ _
      _ < ε := by linarith
  have hsupp : ∀ z : P × H, (∫ v, ψ (z.1, v) ∂(fam z.2)) ≠ 0 →
      ∃ v, ψ (z.1, v) ≠ 0 ∧ q v = z.2 := by
    intro z hz
    by_contra hn
    push_neg at hn
    apply hz
    have h1 : f ⁻¹' {ι z.2} ∩ U ∈ ae (fam z.2) := mem_ae_iff.2 (h.1 z.2)
    have h2 : (fun v => ψ (z.1, v)) =ᵐ[fam z.2] 0 := by
      filter_upwards [h1] with v hv
      have hqv : q v = z.2 := hι ((hf v).symm.trans hv.1)
      by_contra h0
      exact hn v h0 hqv
    exact (integral_congr_ae h2).trans (by simp)
  have hSc : IsCompact ((fun x : P × V => (x.1, q x.2)) '' tsupport ψ) :=
    hCc.image (continuous_fst.prodMk (hq.comp continuous_snd))
  have hts : tsupport (fun z : P × H => ∫ v, ψ (z.1, v) ∂(fam z.2)) ⊆
      (fun x : P × V => (x.1, q x.2)) '' tsupport ψ := by
    refine closure_minimal (fun z hz => ?_) hSc.isClosed
    obtain ⟨v, hv, hqv⟩ := hsupp z hz
    exact ⟨(z.1, v), subset_tsupport _ hv, Prod.ext rfl hqv⟩
  refine ⟨hcont, hSc.of_isClosed_subset (isClosed_tsupport _) hts, fun z hz => ?_⟩
  obtain ⟨x, hx, rfl⟩ := hts hz
  exact ⟨x.2, hx, rfl⟩

end GlobalTheory.CompanionTheory.WeilSiegel.FibParam
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticLocalIdentity
section
noncomputable section

open NumberField IsDedekindDomain Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.G2

namespace GlobalTheory.CompanionTheory.EllLoc

theorem map_csr_left {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    (C (c (P.coeff 0)) * P).map φ = C (c' ((P.map φ).coeff 0)) * P.map φ := by
  rw [Polynomial.map_mul, Polynomial.map_C, h, Polynomial.coeff_map]

theorem map_csr_right {K L : Type} [Field K] [Field L] (φ : K →+* L) (c : K →+* K) (c' : L →+* L)
    (h : ∀ x, φ (c x) = c' (φ x)) (P : K[X]) :
    ((P.map c).reverse).map φ = ((P.map φ).map c').reverse := by
  have hcomp : φ.comp c = c'.comp φ := RingHom.ext h
  have hd : (P.map c).natDegree = ((P.map φ).map c').natDegree := by
    rw [Polynomial.natDegree_map, Polynomial.natDegree_map, Polynomial.natDegree_map]
  rw [Polynomial.reverse, Polynomial.reverse, ← hd, ← Polynomial.reflect_map, Polynomial.map_map, hcomp,
    ← Polynomial.map_map]

theorem csr_linear (a : ℂ) (ha : ‖a‖ = 1) :
    C (starRingEnd ℂ ((X - C a : ℂ[X]).coeff 0)) * (X - C a) = ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse := by
  have hmul : starRingEnd ℂ a * a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ha]; simp
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.reverse, Polynomial.natDegree_X_sub_C,
    Polynomial.reflect_sub, Polynomial.reflect_C]
  have hX : reflect 1 (X : ℂ[X]) = 1 := by
    simpa [revAt] using Polynomial.reflect_monomial (R := ℂ) 1 1
  rw [hX]
  simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, map_neg, C_neg, pow_one]
  have : (C (starRingEnd ℂ a) * C a : ℂ[X]) = 1 := by rw [← C_mul, hmul, C_1]
  linear_combination this

theorem csr_prod (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    C (starRingEnd ℂ ((s.map fun a => (X - C a : ℂ[X])).prod.coeff 0)) * (s.map fun a => (X - C a : ℂ[X])).prod =
      ((s.map fun a => (X - C a : ℂ[X])).prod.map (starRingEnd ℂ)).reverse := by
  induction s using Multiset.induction_on with
  | empty => simp [Polynomial.reverse]
  | cons a s ih =>
    have h1 := csr_linear a (hs a (Multiset.mem_cons_self a s))
    have h2 := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, Polynomial.reverse_mul_of_domain, ← h1, ← h2,
      Polynomial.mul_coeff_zero, map_mul, C_mul]
    ring

theorem csr_global {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) :
    C (IsCMField.complexConj E (P.coeff 0)) * P = (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  set σ : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom with hσ
  have hτ : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQ : (P.map τ).Monic := hP.1.map τ
  have hroots : (P.map τ) = ((P.map τ).roots.map fun a => (X - C a : ℂ[X])).prod :=
    (IsAlgClosed.splits (P.map τ)).eq_prod_roots_of_monic hQ
  have key := csr_prod (P.map τ).roots (hP.2.2.2 τ)
  rw [← hroots] at key
  apply Polynomial.map_injective τ τ.injective
  have e1 := map_csr_left τ σ (starRingEnd ℂ) hτ P
  have e2 := map_csr_right τ σ (starRingEnd ℂ) hτ P
  rw [e2, ← key, ← e1]
  rfl

theorem csr_at {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P : E[X]} (hP : P ∈ Ell E n) (w : Pl E) :
    IsCsr w (atPl w P) := by
  by_cases hs : IsSplitAt w
  · exact Or.inl hs
  right
  have hc : ∀ x, algebraMap E (w.adicCompletion E) ((IsCMField.complexConj E).toRingEquiv.toRingHom x) =
      cj w (algebraMap E (w.adicCompletion E) x) := fun x => (GlobalTheory.BCT.LocVal.cj_algebraMap w hs x).symm
  have e1 := map_csr_left (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  have e2 := map_csr_right (algebraMap E (w.adicCompletion E)) _ (cj w) hc P
  rw [atPl, ← e1, ← e2, ← csr_global hP]
  rfl

theorem ellLocal : EllLocal := by
  intro E _ _ _ a b p₁ p₂ h₁ h₂ hc w
  have hm₁ : (atPl w p₁).Monic := h₁.1.map _
  have hm₂ : (atPl w p₂).Monic := h₂.1.map _
  refine ⟨hm₁, hm₂, ?_, ?_, ?_, csr_at h₁ w, csr_at h₂ w⟩
  · rw [atPl, Polynomial.natDegree_map]; exact h₁.2.1
  · rw [atPl, Polynomial.natDegree_map]; exact h₂.2.1
  · have hs : (p₁ * p₂).Separable := h₁.2.2.1.mul h₂.2.2.1 hc
    have := hs.map (f := algebraMap E (w.adicCompletion E))
    rwa [Polynomial.map_mul] at this

end GlobalTheory.CompanionTheory.EllLoc

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyMeasurableSetPrimV
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas

theorem eventually_measurableSet_primV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, MeasurableSet (primV σ J b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  exact Filter.Eventually.of_forall fun v => measurableSet_primV F E σ hσ M J hJ d b v

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.PrimMeas
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGaloisExtensionOfEmbedding
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_gal_extending_embedding : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l),
    ∃ g : GQ l, ∀ x : ↥K.1, g (x : Om l) = μ x := by
  intro l _ K μ
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits (F := ℚ_[l]) (E := Om l) (K := Om l)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (L := K.1) μ
  refine ⟨AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ), fun x => ?_⟩
  exact DFunLike.congr_fun hφ x

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsUnder
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.UnderExists

theorem exists_isUnder : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (z : (Σ k, Bk n k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ y : CxPts (mpStr ℤ m n) σ₀, IsUnder y z :=
  fun m n z hz => (GlobalTheory.CompanionTheory.MPDict.Under.existsUnique_isUnder m n z hz).exists

end GlobalTheory.CompanionTheory.MPDict.UnderExists
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormula
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem map_cols0 {R S : Type*} [Zero R] [Zero S] {a r t n : ℕ} (f : R → S) (hf : f 0 = 0)
    (e : Fin n ≃ Fin r ⊕ Fin t) (x : Matrix (Fin a) (Fin r) R) :
    ((Matrix.fromCols x (0 : Matrix (Fin a) (Fin t) R)).submatrix id e).map f =
      (Matrix.fromCols (x.map f) (0 : Matrix (Fin a) (Fin t) S)).submatrix id e := by
  ext i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp
  · simp [hf]

theorem mul_cols0 {R : Type*} [NonUnitalNonAssocSemiring R] {a b r t n : ℕ}
    (e : Fin n ≃ Fin r ⊕ Fin t) (A : Matrix (Fin a) (Fin b) R) (x : Matrix (Fin b) (Fin r) R) :
    A * (Matrix.fromCols x (0 : Matrix (Fin b) (Fin t) R)).submatrix id e =
      (Matrix.fromCols (A * x) (0 : Matrix (Fin a) (Fin t) R)).submatrix id e := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  rcases e j with k | k
  · simp [Matrix.mul_apply]
  · simp

theorem extension_by_zero_orbit_action : Ext0 := by
  intro D n t W hn x₀ h
  have h1 : (rat (L.ext0 hn x₀) : Matrix (Fin W.rank) (Fin n) (AE D)) =
      (Matrix.fromCols (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
        (0 : Matrix (Fin W.rank) (Fin t) (AE D))).submatrix id (finSumFinEquiv.trans (finCongr hn)).symm :=
    map_cols0 (incA D) (map_zero _) _ x₀
  have h2 := mul_cols0 (t := t) (finSumFinEquiv.trans (finCongr hn)).symm (mt W h⁻¹)
    (rat x₀ : Matrix (Fin W.rank) (Fin W.rank) (AE D))
  exact (congrArg (fun M => mt W h⁻¹ * M) h1).trans h2

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorInduction
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

theorem factorStep_holds : FactorStep := by
  set_option synthInstance.maxHeartbeats 400000 in
    intro h4 E _ _ _ N W hW
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
        ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
      intro U _ _ _ _ _ _ hU
      obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
      refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
        fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
      exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
    · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
      refine ⟨Ω, hΩ, fun K hK => ?_⟩
      obtain ⟨Θ, hΘ, h'⟩ := h K hK
      refine ⟨Θ, hΘ, ?_⟩
      intro U hs ha hg hn hc hi hU
      obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
      exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorLimit
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation
open GlobalTheory.CompanionTheory.EGlue

namespace GlobalTheory.CompanionTheory.EGlue.FactorLimProof

theorem multiset_eq_of_prod_shift {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (u + ·)).prod = (m'.map (u + ·)).prod) : m = m' :=
  by apply _root_.UpperTheory.Reformulated.B.MultisetSeparation.msetSep <;> assumption

theorem factorLim_of_parts : GlobalTheory.CompanionTheory.EGlue.ConvComp → GlobalTheory.CompanionTheory.EGlue.LimTrees → GlobalTheory.CompanionTheory.EGlue.LeafBound →
    GlobalTheory.CompanionTheory.EGlue.ConvInf → GlobalTheory.CompanionTheory.EGlue.InfOfEq → GlobalTheory.CompanionTheory.EGlue.CapEquiv → GlobalTheory.CompanionTheory.EGlue.MCloseFacts →
    GlobalTheory.CompanionTheory.EGlue.FactorLim := by
  intro _ hLT hLB hCI hIE hCE hMF hTS hGr hIT E _ _ _ Θs Θf Ωs Ωf N t ψ m n B hLim hRA hRed hGood hAll hψ hψ0 hCap hB hCl
  have leaf := fun k => hLB E N (t k) (ψ k) (m k) B hIT (hGood k) (hψ k) (hψ0 k) (hCap k) (hB k)
  obtain ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, hEmb⟩ :=
    hLT hTS hGr E Θs Θf Ωs Ωf N hLim hRA N le_rfl t (2 * B) hRed hGood hAll leaf
  refine ⟨φ, t', s, hφ, hConv, hRs, hGs, hAs, hDisc, fun τ => ?_, hEmb⟩
  obtain ⟨m₀, mk, hs, hk, hprod⟩ := hCI E N t' s τ hConv hGs
  have hst : ∀ k, IsStable (t (φ k)).space := fun k =>
    hTS E N _ (disc_stable (good_disc (hGood _)))
  have hmk : ∀ k, mk k = m (φ k) τ := by
    intro k
    obtain ⟨e, he1, he2, he3⟩ := hEmb k
    have hne : e (ψ (φ k)) ≠ 0 := fun h => hψ0 _ (he2 _ (hψ _) h)
    have hc : CapEig (e (ψ (φ k))) (m (φ k)) := hCE E N _ e _ _ (hst k) he3 (hψ _) (hCap _)
    exact hIE E N (t' k) _ _ τ _ hIT (hk k) (he1 _ (hψ _)) hne hc
  have hlim : ∀ u : ℂ, Tendsto (fun k => ((m (φ k) τ).map (u + ·)).prod) atTop
      (𝓝 (((n τ).map (u + ·)).prod)) := fun u =>
    hMF.2.2 (fun k => m (φ k) τ) (n τ)
      (fun ε hε => hφ.tendsto_atTop.eventually (hCl τ ε hε)) u
  have hm₀ : m₀ = n τ := multiset_eq_of_prod_shift fun u =>
    tendsto_nhds_unique (by simpa only [hmk] using hprod u) (hlim u)
  exact hm₀ ▸ hIT E N s τ m₀ hs

end GlobalTheory.CompanionTheory.EGlue.FactorLimProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteFieldEmbeddingsDifferFrobenius
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

theorem exists_frobenius_pow_of_ringHoms : ∀ {l : ℕ} [Fact l.Prime] {k D : Type} [Field k] [Finite k] [CommRing D] [IsDomain D] [CharP D l]
    (α β : k →+* D), ∃ i : ℕ, ∀ x, β x = α x ^ l ^ i := by
  intro l _ k D _ _ _ _ _ α β
  haveI : CharP k l := α.charP α.injective l
  exact GlobalTheory.ResidueChar.exists_pow_of_finite_field l α β

end GlobalTheory.CompanionTheory.LTPer.Tilt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthOfProducts
section
noncomputable section

open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil PositivityTheory.Rg.BcN.F2

namespace GlobalTheory.CompanionTheory.ProdLen

theorem prodFinLen : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (ι : Type) [Fintype ι] [DecidableEq ι], ProdFinLen F ι := by
  intro F _ _ _ _ ι _ _ α _ _ m _ _ e X _ _ σ hs hi
  have hirr : (piTensor σ).IsIrreducible :=
    GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur σ hi fun a φ hφ =>
      GlobalTheory.SchurAdm.schur_admissible (GL (m a) F) (KO F (m a)) GlobalTheory.SplitFlip.isOpen_KO
        GlobalTheory.SplitFlip.isCompact_KO (X a) (σ a) (hi a)
        (GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible F (m a) (X a) (σ a) (hs a) (hi a)) φ hφ
  exact GlobalTheory.CompanionTheory.BZInd.inductionFiniteLength F α ι m e _ (piTensor σ) (isSmooth_piTensor hs)
    (hasFiniteLength_of_isIrreducible hirr)

end GlobalTheory.CompanionTheory.ProdLen
end
end

