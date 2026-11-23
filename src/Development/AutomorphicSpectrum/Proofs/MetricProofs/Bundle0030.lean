module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0007
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0011
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0006
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqDens
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MetricLocal
section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem metricLocal : ReciprocityTheory.ChartRestriction.G.AI.I2.MetricLocalStatement :=
  GroundTheory.Heights₂.Heights.MetricLocalB.full

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereSingularTotalMassDegree
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem AnSys.eventually_mInt_potT {e : ℕ} {σ : Type} (S : AnSys e σ) (w : Fin e → σ) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      mInt S.A (fun i => S.potT (w i) t) (fun _ => 1) = S.degNum w := by
  have hsm : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i, S.A.Smooth (S.phT (w i) t) := by
    refine Filter.eventually_all.2 fun i => ?_
    obtain ⟨h0, -, hreg⟩ := S.reg (w i)
    filter_upwards [Ioc_mem_nhdsGT h0] with t ht
    exact (hreg t ht.1 ht.2).1
  filter_upwards [hsm] with t ht
  exact massIndep S.A (fun i => S.th (w i)) (fun i => S.phT (w i) t)
    (fun i => (S.sing (w i)).1) ht

theorem AnSys.abs_one_le_log_rW {e : ℕ} {σ : Type} (S : AnSys e σ) (y : S.X) :
    |(1 : ℝ)| ≤ 1 * Real.log (rW S.L S.s y) := by
  have h : Real.exp 1 ≤ rW S.L S.s y := by
    have := S.norm_le y
    unfold rW
    linarith
  have h1 : (1 : ℝ) ≤ Real.log (rW S.L S.s y) :=
    (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) h)).2 h
  simpa using h1

theorem AnSys.mIntegrable_potH_and_mInt_eq_degNum :
    ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e σ) (w : Fin e → σ),
      MIntegrable S.A (fun i => S.potH (w i)) (fun _ => 1) ∧
        mInt S.A (fun i => S.potH (w i)) (fun _ => 1) = S.degNum w := by
  intro hC e σ S w
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hlim := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun i => S.th (w i)) (fun i => S.ph (w i)) (fun i => S.phT (w i)) S.C₅ S.C S.t₀
    (fun i => S.sing (w i)) (fun i => S.reg (w i)) (fun i => S.c2 (w i))
    (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const)
    (fun _ y _ => S.abs_one_le_log_rW y)
    (TendstoUniformlyOn.tendstoLocallyUniformlyOn (by
      refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
      exact Filter.Eventually.of_forall fun _ _ _ => by simpa using hε))
  refine ⟨hlim.1, ?_⟩
  have hT : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (mInt S.A (fun i => S.potH (w i)) (fun _ => 1))) :=
    hlim.2
  have hc : Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun _ => 1))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (S.degNum w)) :=
    tendsto_const_nhds.congr' ((S.eventually_mInt_potT w).mono fun _ h => h.symm)
  exact tendsto_nhds_unique hT hc

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSum
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.OrthSum

variable {K : Type} [Field K] [NumberField K]

theorem disjoint_of_orth (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : Disjoint F G := by
  rw [Submodule.disjoint_def]
  intro x hxF hxG
  by_contra hx
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have hli : LinearIndependent (𝓞 K) (fun _ : Unit => x) := linearIndependent_unique_iff.mpr hx
  have hpos := gramDet_pos E.metric σ hli
  have h0 := h σ x hxF x hxG
  rw [← FibreSpace.inner_equiv E.metric σ] at h0
  have h0' : inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ x) = 0 := h0
  have hz : GroundTheory.Heights₂.Heights.gramDet E.metric σ (fun _ : Unit => x) = 0 := by
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_unique, Matrix.gram_apply, h0', Complex.zero_re]
  linarith

theorem gramDet_sumElim (E : HermitianBundle.{0} K) (σ : K →+* ℂ) {a b : ℕ}
    {s : Fin a → E.carrier} {t : Fin b → E.carrier} (hs : LinearIndependent (𝓞 K) s)
    (ht : LinearIndependent (𝓞 K) t)
    (h : ∀ i j, inner ℂ (fibreVec E.metric σ (s i)) (fibreVec E.metric σ (t j)) = 0) :
    gramDet E.metric σ (Sum.elim s t) = gramDet E.metric σ s * gramDet E.metric σ t := by
  have hconj : ∀ i j, inner ℂ (fibreVec E.metric σ (t j)) (fibreVec E.metric σ (s i)) = 0 := by
    intro i j
    rw [← inner_conj_symm, h i j, map_zero]
  have hM : (Matrix.gram ℂ fun k => fibreVec E.metric σ (Sum.elim s t k)) =
      Matrix.fromBlocks (Matrix.gram ℂ fun i => fibreVec E.metric σ (s i)) 0 0
        (Matrix.gram ℂ fun j => fibreVec E.metric σ (t j)) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.gram_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, h, hconj]
  have him : ∀ {n : ℕ} (v : Fin n → FibreSpace E.metric σ), (Matrix.gram ℂ v).det.im = 0 := by
    intro n v
    have hA : (Matrix.gram ℂ v).conjTranspose = Matrix.gram ℂ v := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.gram_apply]
      exact inner_conj_symm _ _
    have hdet := Matrix.det_conjTranspose (Matrix.gram ℂ v)
    rw [hA] at hdet
    exact Complex.conj_eq_iff_im.mp hdet.symm
  unfold GroundTheory.Heights₂.Heights.gramDet
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Complex.mul_re, him, him, mul_zero, sub_zero]

theorem degree_sup (E : HermitianBundle.{0} K) {F G : Submodule (𝓞 K) E.carrier}
    (h : OrthAt E F G) : E.degree (F ⊔ G) = E.degree F + E.degree G := by
  have hd : Disjoint F G := disjoint_of_orth E h
  obtain ⟨s, hs, hsF⟩ := CoverDenseAlt.exists_fam E F
  obtain ⟨t, ht, htG⟩ := CoverDenseAlt.exists_fam E G
  have hNs : Submodule.span (𝓞 K) (Set.range s) ≤ F := CoverDenseAlt.span_le_of_mem hsF
  have hNt : Submodule.span (𝓞 K) (Set.range t) ≤ G := CoverDenseAlt.span_le_of_mem htG
  have hst : LinearIndependent (𝓞 K) (Sum.elim s t) := hs.sum_type ht (hd.mono hNs hNt)
  have hmem : ∀ i, Sum.elim s t i ∈ F ⊔ G := by
    rintro (i | i)
    · exact Submodule.mem_sup_left (hsF i)
    · exact Submodule.mem_sup_right (htG i)
  have hcard : Fintype.card (Fin (E.rank F) ⊕ Fin (E.rank G)) = E.rank (F ⊔ G) := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, CoverDenseAlt.rank_sup E hd]
  obtain ⟨hiF, hF⟩ := CoverDenseAlt.deg_eq E F hs hsF (Fintype.card_fin _)
  obtain ⟨hiG, hG⟩ := CoverDenseAlt.deg_eq E G ht htG (Fintype.card_fin _)
  obtain ⟨-, hFG⟩ := CoverDenseAlt.deg_eq E (F ⊔ G) hst hmem hcard
  have hidx : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Sum.elim s t))) (F ⊔ G) =
      CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range s)) F * CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range t)) G := by
    rw [Set.Sum.elim_range, Submodule.span_union,
      ← CoverDenseAlt.idx_mul (sup_le_sup_right hNs _) (sup_le_sup_left hNt F)]
    congr 1
    · exact CoverDenseAlt.idx_sup hNs (hd.mono_right hNt)
    · rw [sup_comm F, sup_comm F G]
      exact CoverDenseAlt.idx_sup hNt hd.symm
  have hlog : ∀ σ : K →+* ℂ, Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ (Sum.elim s t)) =
      Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ s) + Real.log (GroundTheory.Heights₂.Heights.gramDet E.metric σ t) := by
    intro σ
    have hgram := gramDet_sumElim E σ hs ht (fun i j => by
      have h1 := h σ _ (hsF i) _ (htG j)
      rw [← FibreSpace.inner_equiv E.metric σ] at h1
      exact h1)
    rw [hgram, Real.log_mul (gramDet_pos E.metric σ hs).ne' (gramDet_pos E.metric σ ht).ne']
  rw [hFG, hF, hG, hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hiF) (Nat.cast_ne_zero.mpr hiG)]
  simp only [hlog, Finset.sum_add_distrib]
  ring

theorem degree_bot (E : HermitianBundle.{0} K) : E.degree ⊥ = 0 := by
  have hrk : Fintype.card (Fin 0) = E.rank ⊥ := by
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  obtain ⟨-, hdeg⟩ := CoverDenseAlt.deg_eq E ⊥ (s := (Fin.elim0 : Fin 0 → E.carrier)) linearIndependent_empty_type
    (fun i => i.elim0) hrk
  have h1 : CoverDenseAlt.idx (Submodule.span (𝓞 K) (Set.range (Fin.elim0 : Fin 0 → E.carrier))) ⊥ = 1 := by
    rw [CoverDenseAlt.idx_eq_card]
    refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, ⟨0⟩⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Subsingleton.elim a b]
  have hg : ∀ σ : K →+* ℂ, GroundTheory.Heights₂.Heights.gramDet E.metric σ (Fin.elim0 : Fin 0 → E.carrier) = 1 := by
    intro σ
    unfold GroundTheory.Heights₂.Heights.gramDet
    rw [Matrix.det_isEmpty, Complex.one_re]
  rw [hdeg, h1]
  simp only [hg, Real.log_one, Nat.cast_one, Finset.sum_const_zero, mul_zero, sub_zero]

theorem orth_biSup (E : HermitianBundle.{0} K) {F : Submodule (𝓞 K) E.carrier} {I : Type}
    (G : I → Submodule (𝓞 K) E.carrier) (S : Finset I) (h : ∀ b ∈ S, OrthAt E F (G b)) :
    OrthAt E F (⨆ b ∈ S, G b) := by
  classical
  intro σ x hx y hy
  obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum G y).mp hy
  rw [← FibreSpace.inner_equiv E.metric σ]
  have hfv : fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier)) = ∑ b ∈ S, fibreVec E.metric σ (μ b) := by
    simpa using fibreVec_sum E.metric σ S (fun _ => 1) (fun b => (μ b : E.carrier))
  change inner ℂ (fibreVec E.metric σ x) (fibreVec E.metric σ (∑ b ∈ S, (μ b : E.carrier))) = 0
  rw [hfv, inner_sum]
  refine Finset.sum_eq_zero fun b hb => ?_
  have h1 := h b hb σ x hx _ (μ b).2
  rw [← FibreSpace.inner_equiv E.metric σ] at h1
  exact h1

theorem degree_rank_biSup (E : HermitianBundle.{0} K) {I : Type}
    (F : I → Submodule (𝓞 K) E.carrier) (h : ∀ a b, a ≠ b → OrthAt E (F a) (F b)) (S : Finset I) :
    E.degree (⨆ a ∈ S, F a) = ∑ a ∈ S, E.degree (F a) ∧
      E.rank (⨆ a ∈ S, F a) = ∑ a ∈ S, E.rank (F a) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · have hb : (⨆ a ∈ (∅ : Finset I), F a) = ⊥ := by simp
    rw [hb, Finset.sum_empty, Finset.sum_empty]
    refine ⟨degree_bot E, ?_⟩
    unfold GroundTheory.Heights₂.Heights.HermitianBundle.rank
    simp
  · intro a S ha ih
    rw [Finset.iSup_insert, Finset.sum_insert ha, Finset.sum_insert ha]
    have horth : OrthAt E (F a) (⨆ b ∈ S, F b) :=
      orth_biSup E F S fun b hb => h a b fun hab => ha (hab ▸ hb)
    refine ⟨?_, ?_⟩
    · rw [degree_sup E horth, ih.1]
    · rw [CoverDenseAlt.rank_sup E (disjoint_of_orth E horth), ih.2]

theorem normDegree_rank_iSup : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  intro K _ _ E I _ F h
  have hU : (⨆ a, F a) = ⨆ a ∈ (Finset.univ : Finset I), F a := by simp
  obtain ⟨hd, hr⟩ := degree_rank_biSup E F h Finset.univ
  rw [hU]
  refine ⟨?_, hr⟩
  unfold GroundTheory.Heights₂.Heights.HermitianBundle.normDegree
  rw [hd, Finset.sum_div]

end GlobalTheory.CompanionTheory.Ar.OrthSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PolarIdentityFromSymmetricForms
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem coefficient_identities_give_operator_identity : ∀ (σ : Type) [Fintype σ] (D : ℕ) (a : (Fin (D + 1) → σ) → ℝ) (b : (Fin D → σ) → ℝ) (κ : ℕ → ℝ) (ε : σ → ℤ) (a₀ : σ), (∀ (π : Equiv.Perm (Fin (D + 1))) w, a (w ∘ π) = a w) → (∀ (π : Equiv.Perm (Fin D)) w, b (w ∘ π) = b w) → (∀ n : σ → ℤ, n a₀ = 0 → polar (D + 1) a (fun _ x => (n x : ℝ)) = 0 ∧ ∀ k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 → polar (D + 1) a (mix (2 * k) (fun x => (ε x : ℝ)) fun x => (n x : ℝ)) = -(2 * κ k) * polar D b (mix (2 * k - 1) (fun x => (ε x : ℝ)) fun x => (n x : ℝ))) → ∀ (c : σ → ℝ), c a₀ = 0 → ∀ u : ℝ, eval (fun x => c x - u / 2 * ε x) (formPoly (D + 1) a) + eval (fun x => c x + u / 2 * ε x) (formPoly (D + 1) a) = (tsgPoly D κ (linePoly c ε (formPoly D b))).eval u :=
  @PositivityTheory.Xgp.t_thma_alg

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationFibreProductCompatible
section
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem sameSing_of_isoLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K₁ : Type) [Fintype K₁] (ι₁ : K₁ → Type) [∀ k, Fintype (ι₁ k)] (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)] (κ₁ : K₁ → K) (v₁ : (Σ k, ι₁ k) → Σ k, ι k) (κ₂ : K₂ → K) (v₂ : (Σ k, ι₂ k) → Σ k, ι k) (P : Ideal (MRing ι)) (P₁ : Ideal (MRing ι₁)) (P₂ : Ideal (MRing ι₂)) (D : ℕ) (σ₁ σ₂ : Type) (S₁ : PB.AnSys D σ₁) (S₂ : PB.AnSys D σ₂) (Re₁ : PB.Realis S₁ P₁) (Re₂ : PB.Realis S₂ P₂) (β : MRing ι) (a₁ : σ₁) (a₂ : σ₂) (A₁ : HermLine ι₁) (A₂ : HermLine ι₂) (A₁' A₂' : HermLine ι), IsBlockMap κ₁ v₁ → IsBlockMap κ₂ v₂ → IsPullHerm κ₁ v₁ A₁ A₁' → IsPullHerm κ₂ v₂ A₂ A₂' → (Re₁.ref a₁).a = A₁.a → (Re₂.ref a₂).a = A₂.a → (∀ x, Re₁.π x ∉ ReciprocityTheory.AnForm.P.bdry S₁.s → Real.log (A₁.h (Re₁.R.lift x x)) = Real.log ((Re₁.ref a₁).h (Re₁.R.lift x x)) + S₁.ph a₁ (Re₁.π x)) → (∀ x, Re₂.π x ∉ ReciprocityTheory.AnForm.P.bdry S₂.s → Real.log (A₂.h (Re₂.R.lift x x)) = Real.log ((Re₂.ref a₂).h (Re₂.R.lift x x)) + S₂.ph a₂ (Re₂.π x)) → IsMultiProjPrime P → IsoLineOn P {z | z ∈ mcPts P ∧ evC z β ≠ 0} A₁' A₂' → SameSing Re₁ Re₂ P κ₁ v₁ κ₂ v₂ β a₁ a₂ :=
  @PositivityTheory.UnitarySelfGeneration.h_samesing

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ShiftHEqTensorConstLine
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Small Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Small

theorem shiftH_eq_tensor_constLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (A : HermLine ι) (t : ℝ) :
    shiftH A t = A.tensor (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine (-t)) := by
  unfold shiftH ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor ReciprocityTheory.ChartRestriction.G.AI.I2.constLine
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight
  congr 1
  · exact (add_zero _).symm
  · funext z
    show Real.exp t * A.h z = A.h z * Real.exp (-(-t))
    rw [neg_neg, mul_comm]

theorem selfInt_shiftH : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ)
    (A : HermLine ι) (t : ℝ) (II : IntersectionSystem), IsIntersectionSystem II → IsArithVar P (D + 1) →
    IsSmoothHerm A →
    II K ι P (D + 1) (fun _ => shiftH A t) =
      II K ι P (D + 1) (fun _ => A) + ((D : ℝ) + 1) * t * geomDeg P A D := by
  intro K _ ι _ P D A t II hII hP hA
  have h := GroundTheory.Heights₂.Heights.HilbertSamuel.TopConstantTwist.proof K ι P D A (-t) II hII hP hA
  rw [shiftH_eq_tensor_constLine, h]
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegral
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.sphere_measure_stereographic_integral :
    let n : ℂ → Fin 3 → ℝ := fun a i =>
      (![2 * a.re, 2 * a.im, 1 - ‖a‖ ^ 2] : Fin 3 → ℝ) i / (1 + ‖a‖ ^ 2)
    (∀ f : (Fin 3 → ℝ) → ℝ, Measurable f →
      (Integrable (fun a : ℂ => f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) ↔
        Integrable (fun m : ReciprocityTheory.ChartRestriction.G.AI.S2 =>
          f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i))
          ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure) ∧
      (∫ a : ℂ, f (n a) * (Real.pi⁻¹ / (1 + ‖a‖ ^ 2) ^ 2)) =
        (∫ m : ReciprocityTheory.ChartRestriction.G.AI.S2,
          f (fun i => (m : ReciprocityTheory.ChartRestriction.G.AI.E3) i)
          ∂ ReciprocityTheory.ChartRestriction.G.AI.sphereMeasure)) ∧
    (∀ a₀ a₁ : ℂ, logSin 1 a₀ a₁ = (1 / 2) * Real.log ((1 - (∑ i, n a₀ i * n a₁ i)) / 2)) := by
  intro n
  exact ⟨PositivityTheory.Xgp.fib_stereo.measure_part, PositivityTheory.Xgp.fib_stereo.logSin_part⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SquareParametrizedDensityFormula
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.square_parametrized_density_formula : ∀ (d : ℕ) (σ : Type) [Fintype σ] (SY : AnSys (d + 1) σ) (a₀ : σ) (ε : σ → ℤ) (Q : AnSq SY a₀ ε) (c : σ → ℝ), c a₀ = 0 → ∀ (n k : ℕ), 1 ≤ k → 2 * k ≤ d + 2 → (∀ z : Fin (d + 1) → ℂ, Fin.tail z ∈ Q.U n → paramDens (fun r => sumPot (mix (2 * k - 1) (fun a => (ε a : ℝ)) c r) SY.potH) (Q.ΦY n) z = maDens (fun (r : Fin (d + 1)) (z' : Fin (d + 1) → ℂ) => if (r : ℕ) < 2 * k - 1 then xiPot (Q.G n (Fin.tail z')) (z' 0) else ∑ a, c a * Q.α n a (Fin.tail z')) z) ∧ ∀ i < k, ∀ z : Fin (d + 2) → ℂ, Fin.tail (Fin.tail z) ∈ Q.U n → paramDens (fun r => sumPot (Q.wcoef c k i r) Q.SW.potH) (Q.ΦW n) z = maDens (let u : ℕ → Fin 2 → ℝ := (fun (i : ℕ) (r : ℕ) (c : Fin 2) => if r = 0 then (![1, -1] : Fin 2 → ℝ) c else if r = 1 then (![0, 1] : Fin 2 → ℝ) c else if r < 2 + 2 * i then (![1, 0] : Fin 2 → ℝ) c else (![0, 1] : Fin 2 → ℝ) c) i; fun (r : Fin (d + 2)) (z' : Fin (d + 2) → ℂ) => if (r : ℕ) < 2 * k then u r 0 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 0) + u r 1 * xiPot (Q.G n (Fin.tail (Fin.tail z'))) (z' 1) else ∑ a, c a * Q.α n a (Fin.tail (Fin.tail z'))) z := by
  intro d σ _ SY a₀ ε Q c hc n k hk _
  exact ⟨fun z hz => PositivityTheory.Xgp.sq_dens.part1 Q c hc n k z hz, fun i hi z hz => PositivityTheory.Xgp.sq_dens.part2 Q c hc n k hk i hi z hz⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightTransformInjectiveLinear
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tsgPoly_linePoly_smul_toWt_injective :
    (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) :=
  PositivityTheory.Xgp.t_tsg_smul

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightedFlagDegreeLowerBound
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.LowerAny

theorem sum_sub_succ (n : ℕ) (f : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (Fin.last n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have h := ih (fun i => f i.castSucc)
    simp only [Fin.succ_castSucc, Fin.castSucc_zero] at h ⊢
    rw [h, Fin.succ_last]
    simp

theorem sum_weight_lower {n : ℕ} (a d : Fin n → ℝ) (M : ℝ) (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, d i ≤ M) :
    -((∑ i, a i) * M) ≤ ∑ i, a i * (-d i) := by
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  nlinarith [mul_le_mul_of_nonneg_left (hd i) (ha i)]

theorem step_le {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {r : ℕ} (A : SatFlag E r)
    (μ : ℝ) (N : ℝ) (hμ : 0 ≤ μ) (hE : E.slopeMax ≤ (μ : EReal)) (hN : (r : ℝ) ≤ N) (i : Fin (r + 1)) :
    E.normDegree (A.F i) ≤ N * μ := by
  have h := _root_.GlobalTheory.CompanionTheory.Ar.DegSlope.normDegree_le_rank_mul_of_slopeMax_le K E μ hE (A.F i)
  rw [A.rank i] at h
  have hi : ((i : ℕ) : ℝ) ≤ N := le_trans (by exact_mod_cast Nat.lt_succ_iff.mp i.isLt) hN
  exact h.trans (mul_le_mul_of_nonneg_right hi hμ)

theorem term_lower {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ]
    (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ)
    (τ : Ψ) (hanti : Antitone (lam τ)) (hΛ : ∀ i, |lam τ i| ≤ Λ) (hμ : 0 ≤ μ)
    (hE : E.slopeMax ≤ (μ : EReal)) (hC : |A.flatDeg τ| ≤ C) :
    -(2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C) ≤
      (∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) *
          (-E.normDegree ((A.W τ).F i.succ.castSucc))) +
        (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) *
          (-E.normDegree (A.W τ).top) +
        (∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) *
          (-E.normDegree ((A.S τ).F i.rev.succ.castSucc))) -
        lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  set N : ℝ := (j : ℝ) + 1 + ((k : ℝ) + 1) with hNdef
  have hNW : (((j + 1 : ℕ)) : ℝ) ≤ N := by push_cast; linarith
  have hNS : (((k + 1 : ℕ)) : ℝ) ≤ N := by push_cast; linarith
  have hN0 : 0 ≤ N := by linarith
  have hM : 0 ≤ N * μ := mul_nonneg hN0 hμ
  have hg : ∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) =
      lam τ (Fin.castAdd (k + 1) 0) - lam τ (Fin.castAdd (k + 1) (Fin.last j)) :=
    sum_sub_succ j (fun i => lam τ (Fin.castAdd (k + 1) i))
  have hh : ∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) =
      lam τ (Fin.natAdd (j + 1) 0) - lam τ (Fin.natAdd (j + 1) (Fin.last k)) :=
    sum_sub_succ k (fun i => lam τ (Fin.natAdd (j + 1) i))
  have h1 := sum_weight_lower
    (fun i : Fin j => lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ))
    (fun i : Fin j => E.normDegree ((A.W τ).F i.succ.castSucc)) (N * μ)
    (fun i => sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp)))
    (fun i => step_le (A.W τ) μ N hμ hE hNW _)
  have h3 := sum_weight_lower
    (fun i : Fin k => lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ))
    (fun i : Fin k => E.normDegree ((A.S τ).F i.rev.succ.castSucc)) (N * μ)
    (fun i => sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp)))
    (fun i => step_le (A.S τ) μ N hμ hE hNS _)
  rw [hg] at h1
  rw [hh] at h3
  have hb : 0 ≤ lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0) :=
    sub_nonneg.mpr (hanti (by rw [Fin.le_def]; simp))
  have htop : E.normDegree (A.W τ).top ≤ N * μ := step_le (A.W τ) μ N hμ hE hNW (Fin.last _)
  have h2 : -((lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) * (N * μ)) ≤
      (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) *
        (-E.normDegree (A.W τ).top) := by
    nlinarith [mul_le_mul_of_nonneg_left htop hb]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ (Fin.natAdd (j + 1) 0))
  have h4 : lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ ≤ Λ * C := by
    calc lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ
        ≤ |lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ| := le_abs_self _
      _ = |lam τ (Fin.natAdd (j + 1) 0)| * |A.flatDeg τ| := abs_mul _ _
      _ ≤ Λ * C := mul_le_mul (hΛ _) hC (abs_nonneg _) hΛ0
  have hfirst : lam τ (Fin.castAdd (k + 1) 0) ≤ Λ := (le_abs_self _).trans (hΛ _)
  have hlast : -Λ ≤ lam τ (Fin.natAdd (j + 1) (Fin.last k)) := (abs_le.mp (hΛ _)).1
  have h5 : (lam τ (Fin.castAdd (k + 1) 0) - lam τ (Fin.natAdd (j + 1) (Fin.last k))) * (N * μ) ≤
      (2 * Λ) * (N * μ) := mul_le_mul_of_nonneg_right (by linarith) hM
  have h6 : 2 * Λ * N * μ = (2 * Λ) * (N * μ) := by ring
  rw [h6]
  nlinarith [h1, h2, h3, h4, h5]

theorem lamDeg_lower : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ) (Λ μ C : ℝ), (∀ τ, Antitone (lam τ)) → (∀ τ i, |lam τ i| ≤ Λ) → 0 ≤ μ → E.slopeMax ≤ (μ : EReal) → (∀ τ, |A.flatDeg τ| ≤ C) → -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C)) ≤ A.lamDeg lam := by
  intro K _ _ E Ψ _ j k A lam Λ μ C hanti hΛ hμ hE hC
  rw [GlobalTheory.CompanionTheory.Ar.Decomp.lamDeg_eq]
  calc -(Fintype.card Ψ * (2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C))
      = ∑ _τ : Ψ, -(2 * Λ * (j + 1 + (k + 1)) * μ + Λ * C) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_neg]
    _ ≤ _ := Finset.sum_le_sum fun τ _ =>
        term_lower E Ψ j k A lam Λ μ C τ (hanti τ) (hΛ τ) hμ hE (hC τ)

end GlobalTheory.CompanionTheory.Ar.LowerAny
end

