module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphIso
public import GroundTheory.AutomorphicForms.CompactFormulaCountable

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
section
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

private lemma haar_unique {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure]
    (K : Set G) (h : μ K = 1) (h' : μ' K = 1) : μ' = μ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hK : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := congrArg (fun ν : Measure G => ν K) e
    simpa [h, h'] using this.symm
  have h1 : Measure.haarScalarFactor μ' μ = 1 := by exact_mod_cast hK
  rw [e, h1, one_smul]

private lemma cmp_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {m n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (D : UpperTheory.ConvolutionTheory.L1.Split (incFin E v) (galFin σ v) m)
    (w : Fin (m + 1) ≃ PlacesOver E v)
    (hD : ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1))
    (g : GL (Fin n) (CompletionsOver E v)) :
    UpperTheory.ConvolutionTheory.GM.cmp (w i) g = mapGL n (completionMap v (w i).1) (D.comp n i g) := by
  ext a b
  simp [UpperTheory.ConvolutionTheory.GM.cmp, UpperTheory.ConvolutionTheory.L1.Split.comp, hD]

theorem UpperTheory.ConvolutionTheory.L1.matchProd :
    UpperTheory.ConvolutionTheory.L1.MatchProd := by
  intro F E _ _ _ _ _ _ σ hσ m hm n v w₀ hs
  obtain ⟨D, w, hw0, hD⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  refine ⟨w, hw0, ?_⟩
  intro h hh iF bF mF hHaar hvol iE' bE' iF' bF' mE mF' hE hF' hmE hmF'
  obtain rfl : iF' = iF := by rw [bF'.measurable_eq, bF.measurable_eq]
  haveI := hHaar
  haveI := hF'
  haveI := hE
  have hmm : mF' = mF := haar_unique mF mF' _ hvol hmF'
  rw [hmm]
  have hsl := fun i => UpperTheory.ConvolutionTheory.L1.splitLoc F E v (w i) (hs (w i)) n
  set φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) → ℂ :=
    fun i g => h (w i) (mapGL n (completionMap v (w i).1) g) with hφ
  have hφc : ∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i) := by
    intro i
    obtain ⟨⟨e, he⟩, -⟩ := hsl i
    have : φ i = h (w i) ∘ e := funext fun g => by simp [hφ, he]
    rw [this]
    exact ⟨(hh _).1.comp e.continuous, (hh _).2.comp_homeomorph e.toHomeomorph⟩
  obtain ⟨c, hc, hμ, hM, hT⟩ := UpperTheory.ConvolutionTheory.L1.matchFin F E σ m v D n mE mF hE hHaar
  obtain ⟨hc1, hc2, hT'⟩ := hT φ hφc
  obtain ⟨-, -, -, hgc, hcc, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n
  have hpf : UpperTheory.ConvolutionTheory.GM.prodFn h = D.tens n φ := by
    funext g
    simp only [UpperTheory.ConvolutionTheory.GM.prodFn, UpperTheory.ConvolutionTheory.L1.Split.tens]
    rw [← finprod_comp_equiv w, finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun i _ => by rw [cmp_eq D w hD i g]
  have hU : ∀ g, g ∈ unitSet E n v ↔ ∀ i, D.comp n i g ∈ GLnLocal.integralGL (v.adicCompletion F) n := by
    intro g
    constructor
    · intro hg i
      have h1 : UpperTheory.ConvolutionTheory.GM.cmp (w i) g ∈ GLnLocal.integralGL ((w i).1.adicCompletion E) n := hg (w i)
      rw [cmp_eq D w hD i g] at h1
      exact ((hsl i).2.1 _).1 h1
    · intro hg u
      obtain ⟨i, rfl⟩ := w.surjective u
      have h1 := ((hsl i).2.1 _).2 (hg i)
      rw [← cmp_eq D w hD i g] at h1
      exact h1
  have hcomp := (UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n).1
  have hset : D.glue n ⁻¹' unitSet E n v =
      Set.pi Set.univ fun _ => (GLnLocal.integralGL (v.adicCompletion F) n : Set _) := by
    ext g
    simp [hU, hcomp]
  have hKm : MeasurableSet (GLnLocal.integralGL (v.adicCompletion F) n : Set (GL (Fin n) (v.adicCompletion F))) :=
    (GLnLocal.isOpen_integralGL _ n).measurableSet
  have hmeas : MeasurableSet (unitSet E n v) := by
    have : unitSet E n v = ⋂ i, D.comp n i ⁻¹' (GLnLocal.integralGL (v.adicCompletion F) n : Set _) := by
      ext g
      simp [hU]
    rw [this]
    exact MeasurableSet.iInter fun i => (hcc i).measurable hKm
  have hpi : Measure.pi (fun _ : Fin (m + 1) => mF)
      (Set.pi Set.univ fun _ => (GLnLocal.integralGL (v.adicCompletion F) n : Set _)) = 1 := by
    rw [Measure.pi_pi]
    simp [hvol]
  have hone : ENNReal.ofReal c = 1 := by
    have h1 := hmE
    rw [hμ, Measure.smul_apply, Measure.map_apply hgc.measurable hmeas, hset, hpi] at h1
    simpa using h1
  have hc1' : c = 1 := ENNReal.ofReal_eq_one.1 hone
  have hfin := hM (D.tens n φ) hc1 hc2
  rw [hT', hc1', ← hpf, ← hm] at hfin
  simpa using hfin
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphLaws
section
open MeasureTheory NumberField IsDedekindDomain ValuativeRel
open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

private theorem haar_uniq {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {K : Set G} {m m' : Measure G}
    (hm : m.IsHaarMeasure) (hm' : m'.IsHaarMeasure) (h : m K = 1) (h' : m' K = 1) : m = m' := by
  have e := Measure.isMulLeftInvariant_eq_smul m m'
  have e2 : m K = (Measure.haarScalarFactor m m' • m') K := by rw [← e]
  rw [h, Measure.smul_apply, h', ENNReal.smul_def, smul_eq_mul, mul_one] at e2
  have e3 : Measure.haarScalarFactor m m' = 1 := by exact_mod_cast e2.symm
  rw [e3, one_smul] at e
  exact e

private theorem gl_sc (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [SecondCountableTopology R] (n : ℕ) : SecondCountableTopology (GL (Fin n) R) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {v : HeightOneSpectrum (𝓞 K)}

private theorem sph_at [ms : MeasurableSpace (GL (Fin n) (v.adicCompletion K))]
    [bs : BorelSpace (GL (Fin n) (v.adicCompletion K))] (m : Measure (GL (Fin n) (v.adicCompletion K)))
    (hm : m.IsHaarMeasure) (h1 : m (GLnLocal.integralGL (v.adicCompletion K) n) = 1)
    {p : MvPolynomial (Fin n) ℂ} {h : GL (Fin n) (v.adicCompletion K) → ℂ} (hs : GM.IsSph v p h) :
    ∃ H : SphericalHecke m (F := v.adicCompletion K) (n := n), (∀ x, (H : HeckeAlgebra m) x = h x) ∧
      satakeTransform m H = polyEmb (n := n) (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm (Fin n) ℂ (i + 1)) p) := by
  obtain ⟨ms', bs', m', hm', h1', H, hH, S⟩ := hs
  obtain rfl : ms' = ms := bs'.measurable_eq.trans bs.measurable_eq.symm
  haveI := gl_sc (v.adicCompletion K) n
  obtain rfl := haar_uniq hm hm' h1 h1'
  exact ⟨H, hH, S⟩

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sphLaws :
    UpperTheory.ConvolutionTheory.L1.SphLaws := by
  refine ⟨?_, fun K _ _ n v => ⟨?_, ?_, ?_⟩⟩
  · intro F E _ _ _ _ _ v w hs n p h hsph
    obtain ⟨ms, bs, m, hm, hk, H, hH, S⟩ := hsph
    obtain ⟨⟨e, he⟩, hint, -, -, -⟩ := UpperTheory.ConvolutionTheory.L1.splitLoc F E v w hs n
    let c : v.adicCompletion F ≃+* w.1.adicCompletion E :=
      RingEquiv.ofBijective (completionMap v w.1) ⟨(completionMap v w.1).injective, hs⟩
    have he0 : w.1.asIdeal.ramificationIdx (𝓞 F) ≠ 0 := (Ideal.ramificationIdx_pos (R := 𝓞 F) w.1.asIdeal).ne'
    have hv : ∀ x, c x ∈ 𝒪[w.1.adicCompletion E] ↔ x ∈ 𝒪[v.adicCompletion F] := fun x => by
      have h1 : ∀ y : w.1.adicCompletion E, y ∈ 𝒪[w.1.adicCompletion E] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (w.1.adicCompletion E)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      have h2 : ∀ y : v.adicCompletion F, y ∈ 𝒪[v.adicCompletion F] ↔ Valued.v y ≤ 1 := fun y => by
        have := ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v y 1
        rw [map_one, map_one] at this
        exact (Valuation.mem_integer_iff _ _).trans this
      rw [h1, h2]
      change Valued.v (completionMap v w.1 x) ≤ 1 ↔ _
      rw [valued_completionMap]
      exact pow_le_one_iff_of_nonneg zero_le he0
    have hee : ∀ g, e g = mapIso c n g := fun g => he g
    obtain ⟨ms', bs', m', hm', h1, H', hH', S'⟩ := exists_transport e (fun g => by rw [he]; exact hint g)
      (fun g => by rw [hee]; exact iwasawaExponent_mapIso c hv g) (qF_eq_of_iso c hv) hk H
    exact ⟨ms', bs', m', hm', h1, H', fun x => (hH' x).trans ((hH _).trans (by rw [he])), S'.trans S⟩
  · rintro p h ⟨_, _, m, _, -, H, hH, -⟩
    obtain rfl : (fun x => (H : HeckeAlgebra m) x) = h := funext hH
    exact ⟨(H : HeckeAlgebra m).mem.1.continuous, (H : HeckeAlgebra m).mem.2⟩
  · intro p h h' hs hs'
    obtain ⟨ms, bs, m, hm, h1, H, hH, S⟩ := id hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    obtain rfl := satakeTransform_injective (S.trans S'.symm)
    exact funext fun x => (hH x).symm.trans (hH' x)
  · intro _ _ m hm h1 p p' h h' hs hs'
    obtain ⟨H, hH, S⟩ := sph_at m hm h1 hs
    obtain ⟨H', hH', S'⟩ := sph_at m hm h1 hs'
    refine ⟨_, inferInstance, m, hm, h1, H * H', fun x => ?_, ?_⟩
    · change ∫ y, (H : HeckeAlgebra m) y * (H' : HeckeAlgebra m) (y⁻¹ * x) ∂m = _
      simp only [hH, hH']
      rfl
    · rw [map_mul, S, S', map_mul, map_mul]
end

