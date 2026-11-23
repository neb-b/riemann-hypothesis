module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0098
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0100
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0095
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0108
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ConeChart
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0107
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartParametersAtConePoint
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par

open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp

theorem sum_pderiv_renC {σ : Type} [Fintype σ] (t₀ : σ → ℂ) (v : Fin (Fintype.card σ) → ℂ)
    (h : MvPolynomial σ ℂ) :
    ∑ j, v j * eval (renPt t₀) (pderiv j (renC σ h)) =
      ∑ q, v (Fintype.equivFin σ q) * eval t₀ (pderiv q h) := by
  rw [← Equiv.sum_comp (Fintype.equivFin σ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have ht : (renPt t₀ ∘ ⇑(Fintype.equivFin σ)) = t₀ := by
    funext x
    simp [renPt]
  rw [renC, MvPolynomial.renameEquiv_apply, MvPolynomial.pderiv_rename (Fintype.equivFin σ).injective,
    MvPolynomial.eval_rename, ht]

theorem exists_params : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)), ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ), z ∈ conePts (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) → (∀ k, z ⟨k, p k⟩ ≠ 0) → ∃ (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), ((∀ h ∈ (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p), eval (renPt (affCoord p z)) h = 0) ∧ IsRegularLocalRing (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) ∧ ringKrullDim (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) = e ∧ Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) ∧ (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) ⊔ (ReciprocityTheory.ChartRestriction.G.Geo.pC J)) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮))) := by
  intro K _ ι _ Ω _ _ y e J hA hS p z hz hzp
  classical
  have hPh : IsMultiHomogIdeal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) :=
    ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_pC hA.2.1.2.1
  have hw := (mem_conePts_iff_chartIdeal hPh p z hzp).1 hz
  have hy : ∀ k, y ⟨k, p k⟩ ≠ 0 := by
    intro k h0
    have hX : (X ⟨k, p k⟩ : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal, RingHom.mem_ker, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, aeval_X, h0]
      simp
    have h1 := hz.2 _ (Ideal.subset_span ⟨_, hX, rfl⟩)
    rw [map_X, eval_X] at h1
    exact hzp k h1
  set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hPdef
  set τ : (Σ k, ι k) → Ω := fun q => y q / y ⟨q.1, p q.1⟩ with hτ
  set t₀ := affCoord p z with ht₀
  have hker : ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval τ G = 0 → map (algebraMap ℚ ℂ) G ∈ chartIdeal P p :=
    GlobalTheory.CompanionTheory.Ar.Cmp.KerChart.map_mem_chartIdeal_of_aeval_eq_zero K ι Ω y p hy
  have hker0 : ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval τ G = 0 → eval t₀ (map (algebraMap ℚ ℂ) G) = 0 :=
    fun G hG => hw _ (hker G hG)
  obtain ⟨F, S, zz, n, hF, hFt, hSeq, hspan, hbd⟩ := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_basicOpen_of_isSncModel K ι Ω y e J hS p hy t₀ hker0
  have hrep : ∀ i, ∃ (N : ℕ) (G : MvPolynomial (Σ k, ι k) ℚ),
      ((zz i : S) : Ω) * aeval τ F ^ N = aeval τ G :=
    fun i => GlobalTheory.CompanionTheory.Ar.Cmp.exists_mul_pow_eq_aeval_of_mem_adjoin_inv Ω (Σ k, ι k) τ F S hF hSeq (zz i)
  choose N Z hZ using hrep
  set c : Fin e → ℂ := fun i => eval t₀ (map (algebraMap ℚ ℂ) (Z i)) / eval t₀ (map (algebraMap ℚ ℂ) F) ^ N i with hc
  set r₀ : Fin e → MvPolynomial (Σ k, ι k) ℂ :=
    fun i => map (algebraMap ℚ ℂ) (Z i) - C (c i) * map (algebraMap ℚ ℂ) F ^ N i with hr₀
  have hcZ : ∀ i, eval t₀ (map (algebraMap ℚ ℂ) (Z i)) = c i * eval t₀ (map (algebraMap ℚ ℂ) F) ^ N i :=
    fun i => (div_mul_cancel₀ _ (pow_ne_zero _ hFt)).symm
  have hr₀z : ∀ i, eval t₀ (r₀ i) = 0 := by
    intro i
    simp only [hr₀, map_sub, map_mul, map_pow, eval_C]
    rw [hcZ i]
    simp
  have hIt : ∀ h ∈ SncRes.ideal P p, eval (renPt t₀) h = 0 := renPt_zero _ _ hw
  have hrz : ∀ l, eval (renPt t₀) (renC (Σ k, ι k) (r₀ l)) = 0 := fun l => by
    rw [eval_renC]; exact hr₀z l
  have hd : ringKrullDim (locRing (SncRes.ideal P p) (renPt t₀)) = e :=
    (ringKrullDim_eq_of_ringEquiv (locAtEquiv _ _)).symm.trans
      (ringKrullDim_locAt_chart _ hPh e (ReciprocityTheory.ChartRestriction.G.Geo.pcEquidim K ι _ e hA) p _ hw)
  have hsp : Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt t₀))
      (renC (Σ k, ι k) (r₀ l))) =
      Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt t₀))) (ptIdeal (renPt t₀)) := by
    refine GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.span_algebraMap_eq_map_ptIdeal e (SncRes.ideal P p) (renPt t₀) _ hIt hrz fun v hv1 hv2 => ?_
    have hv₀ : (fun q => v (Fintype.equivFin (Σ k, ι k) q)) = 0 := by
      refine GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Ktan.tangent_eq_zero Ω (Σ k, ι k) τ F S e zz Z N t₀ _ c hF hSeq hspan hZ hker0 hFt ?_ hcZ ?_
      · intro G hG
        rw [← sum_pderiv_renC]
        refine hv1 _ ?_
        exact Ideal.mem_map_of_mem _ (hker G hG)
      · intro i
        rw [← sum_pderiv_renC]
        exact hv2 i
    funext j
    have := congr_fun hv₀ ((Fintype.equivFin (Σ k, ι k)).symm j)
    simpa using this
  refine ⟨fun l => renC (Σ k, ι k) (r₀ l), Finset.univ.filter fun i : Fin e => (i : ℕ) < n ∧ c i = 0,
    hIt, GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Kreg.isRegularLocalRing_locRing_of_span _ e _ _ _ hIt hd hsp, hd, hsp, ?_⟩
  intro 𝔮 h𝔮 hI𝔮 h𝔮t
  have hle₀ : chartIdeal P p ≤ 𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) :=
    Ideal.map_le_iff_le_comap.1 hI𝔮
  have hpt : ∀ g : MvPolynomial (Σ k, ι k) ℂ, renC (Σ k, ι k) g ∈ 𝔮 → eval t₀ g = 0 := by
    intro g hg
    have := h𝔮t hg
    rw [ptIdeal, RingHom.mem_ker, eval_renC] at this
    exact this
  have hprime : (𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)).IsPrime :=
    Ideal.comap_isPrime _ _
  have hkp := GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.PrimeRead.boundary_on_primes Ω (Σ k, ι k) τ F S (J : Set _) e n zz Z N hF hSeq hZ hbd
    (𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _)) hprime
    (fun G hG => hle₀ (hker G hG))
    (fun hFq => hFt (hpt (map (algebraMap ℚ ℂ) F) hFq))
  have hleft : SncRes.ideal (P ⊔ ReciprocityTheory.ChartRestriction.G.Geo.pC J) p ≤ 𝔮 ↔
      ∀ g ∈ (J : Set _), map (Int.castRingHom ℂ) g ∈
        𝔮.comap (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) := by
    rw [SncRes.ideal, Ideal.map_le_iff_le_comap]
    constructor
    · intro h g hg
      exact h (Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨g, hg, rfl⟩)))
    · intro h
      refine sup_le (sup_le (fun f hf => hle₀ (Ideal.mem_sup_left hf)) ?_)
        (fun f hf => hle₀ (Ideal.mem_sup_right hf))
      refine Ideal.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      exact h g hg
  rw [hleft, hkp]
  constructor
  · rintro ⟨i, hin, hi⟩
    have hci : c i = 0 := by
      have h0 : eval t₀ (map (algebraMap ℚ ℂ) (Z i)) = 0 := hpt _ hi
      show eval t₀ _ / _ = 0
      rw [h0, zero_div]
    refine ⟨i, by simp [hin, hci], ?_⟩
    have : r₀ i = map (algebraMap ℚ ℂ) (Z i) := by simp [hr₀, hci]
    simp only [this]
    exact hi
  · rintro ⟨i, hiJ, hi⟩
    obtain ⟨hin, hci⟩ := (Finset.mem_filter.1 hiJ).2
    refine ⟨i, hin, ?_⟩
    have : r₀ i = map (algebraMap ℚ ℂ) (Z i) := by simp [hr₀, hci]
    simp only [this] at hi
    exact hi

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularAtConePointStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_regular_at_cone_point : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (z : (Σ k, ι k) → ℂ) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)), IsMultiHomogIdeal P → IsMultiHomogIdeal D → z ∈ conePts P → (∀ k, z ⟨k, p k⟩ ≠ 0) → (∀ h ∈ (SncRes.ideal P p), eval (renPt (affCoord p z)) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (renPt (affCoord p z))) → ringKrullDim (locRing (SncRes.ideal P p) (renPt (affCoord p z))) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z))) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (renPt (affCoord p z)))) (ptIdeal (renPt (affCoord p z))) → (∀ 𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ), 𝔮.IsPrime → (SncRes.ideal P p) ≤ 𝔮 → 𝔮 ≤ ptIdeal (renPt (affCoord p z)) → ((SncRes.ideal (P ⊔ D) p) ≤ 𝔮 ↔ ∃ i ∈ Jf, r i ∈ 𝔮)) → ∃ σ : Fin e → Option (Fin (SncRes.rc P D)), Set.InjOn σ Jf ∧ (∀ l, σ l = none ↔ l ∉ Jf) ∧ (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧ ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k) ∧ ∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval z g = 0) → ∃ l ∈ Jf, σ l = some k := by
  intro K _ ι _ P D e p z r Jf hP hD hz hzp hI reg dim span hprim
  have ideal_mono {S S' : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (h : S ≤ S') (p : (k : K) → ι k) :
      SncRes.ideal S p ≤ SncRes.ideal S' p :=
    Ideal.map_mono (sup_le_sup_right h _)

  have renR_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : renR (Σ k, ι k) g ∈ SncRes.ideal S p :=
    Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)

  have renR_X_sub_one_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) (k : K) :
      renR (Σ k, ι k) (X ⟨k, p k⟩ - 1) ∈ SncRes.ideal S p :=
    Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩))

  have renR_sub_deh_mem (S : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
      (f : MvPolynomial (Σ k, ι k) ℂ) :
      renR (Σ k, ι k) f - bind₁ (SncRes.lift p) f ∈ SncRes.ideal S p := by
    classical
    have key : (Ideal.Quotient.mk (SncRes.ideal S p)).comp
          (renR (Σ k, ι k) : MvPolynomial (Σ k, ι k) ℂ →+* _) =
        (Ideal.Quotient.mk (SncRes.ideal S p)).comp
          (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [renameEquiv_apply]
      · rintro ⟨k, i⟩
        by_cases h : i = p k
        · subst h
          have h1 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
          have h2 := renR_X_sub_one_mem S p k
          rw [map_sub, map_one] at h2
          simpa [h1] using Ideal.Quotient.eq.2 h2
        · have h1 : SncRes.lift p ⟨k, i⟩ = X (Fintype.equivFin (Σ k, ι k) ⟨k, i⟩) := by
            simp [SncRes.lift, h]
          simp [h1, renameEquiv_apply]
    exact Ideal.Quotient.eq.1 (RingHom.congr_fun key f)

  have deh_mem {S : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {g : MvPolynomial (Σ k, ι k) ℂ} (hg : g ∈ S) : bind₁ (SncRes.lift p) g ∈ SncRes.ideal S p := by
    have h := (SncRes.ideal S p).sub_mem (renR_mem p hg) (renR_sub_deh_mem S p g)
    simpa using h

  have exists_compIdeal_eq {P D Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
      (hQ : Q ∈ (P ⊔ D).minimalPrimes) : ∃ k, SncRes.compIdeal P D k = Q := by
    refine ⟨(SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin
      ⟨Q, (Set.Finite.mem_toFinset _).2 hQ⟩, ?_⟩
    simp [SncRes.compIdeal]

  have compIdeal_injective (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) :
      Function.Injective (SncRes.compIdeal P D) := by
    intro a b h
    exact ((SncRes.finite_minimalPrimes (P ⊔ D)).toFinset.equivFin).symm.injective (Subtype.ext h)

  have exists_minimal_below {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k)
      {𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)} (h𝔮 : 𝔮.IsPrime)
      (hD : SncRes.ideal (P ⊔ D) p ≤ 𝔮) :
      ∃ Q ∈ (P ⊔ D).minimalPrimes,
        (∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) ∧ SncRes.ideal Q p ≤ 𝔮 := by
    classical
    have hle : P ⊔ D ≤ 𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _) :=
      fun g hg => hD (deh_mem p hg)
    have : (𝔮.comap (bind₁ (SncRes.lift p) : MvPolynomial (Σ k, ι k) ℂ →ₐ[ℂ] _)).IsPrime :=
      Ideal.comap_isPrime _ _
    obtain ⟨Q, hQ, hQle⟩ := Ideal.exists_minimalPrimes_le hle
    refine ⟨Q, hQ, fun k hX => ?_, ?_⟩
    · have h1 : bind₁ (SncRes.lift p) (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∈ 𝔮 := hQle hX
      have h2 : SncRes.lift p ⟨k, p k⟩ = 1 := by simp [SncRes.lift]
      rw [bind₁_X_right, h2] at h1
      exact h𝔮.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    · refine Ideal.map_le_iff_le_comap.2 (sup_le ?_ ?_)
      · intro f hf
        have h1 : bind₁ (SncRes.lift p) f ∈ 𝔮 := hQle hf
        have h2 := 𝔮.add_mem (hD (renR_sub_deh_mem (P ⊔ D) p f)) h1
        simpa using h2
      · rw [Ideal.span_le]
        rintro _ ⟨k, rfl⟩
        exact hD (renR_X_sub_one_mem (P ⊔ D) p k)
  have hIDc : SncRes.ideal P p ≤ SncRes.ideal (P ⊔ D) p := ideal_mono le_sup_left p
  have pr := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.primes_below_params _ e (SncRes.ideal P p) (SncRes.ideal (P ⊔ D) p) (renPt (affCoord p z)) r Jf
    hIDc hI reg dim span hprim
  have hmin := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD
  have chart_prime_and_mem_iff (Q : Ideal (MvPolynomial (Σ k, ι k) ℂ))
      (hQ : IsMultiHomogIdeal Q) (hprime : Q.IsPrime)
      (hX : ∀ k, (X ⟨k, p k⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ Q) :
      (SncRes.ideal Q p).IsPrime ∧
        ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), IsMultiHomog f a →
          (bind₁ (SncRes.lift p) f ∈ SncRes.ideal Q p ↔ f ∈ Q) := by
    have hker := SncRes.Dict.ker_theta Q hQ p hX
    refine ⟨?_, fun f a hf => ?_⟩
    · have : (chartIdeal Q p).IsPrime := hker ▸ RingHom.ker_isPrime (SncRes.Dict.theta Q p)
      exact Ideal.map_isPrime_of_equiv (renR (Σ k, ι k))
    · have hquot := Ideal.Quotient.eq.2 (renR_sub_deh_mem Q p f)
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hquot, Ideal.Quotient.eq_zero_iff_mem,
        SncRes.ideal, mem_map_renR_iff, RingEquiv.symm_apply_apply, ← hker, RingHom.mem_ker]
      exact SncRes.Dict.theta_eq_zero_iff Q p hX hf
  have step : ∀ l (_ : l ∈ Jf), ∃ k, SncRes.ideal (SncRes.compIdeal P D k) p =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r l) ∧
      ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
    intro l hl
    obtain ⟨hpr, hIq, hqt, hDq, hrl, hsep, hmn⟩ := pr l hl
    obtain ⟨Q, hQ, hX, hQle⟩ := exists_minimal_below p hpr hDq
    have hQh := hmin Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    obtain ⟨hQpr, -⟩ := chart_prime_and_mem_iff Q hQh hQp hX
    have hDQ : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal Q p := ideal_mono hQ.1.2 p
    have hIQ := hIDc.trans hDQ
    obtain ⟨j, hj, hrj⟩ := (hprim _ hQpr hIQ (hQle.trans hqt)).1 hDQ
    have hjl : j = l := by
      by_contra hne
      exact hsep j hj hne (hQle hrj)
    subst hjl
    obtain ⟨k, rfl⟩ := exists_compIdeal_eq hQ
    exact ⟨k, le_antisymm hQle (hmn _ hQpr hIQ (hQle.trans hqt) hrj), hX⟩
  classical
  choose κ hκ using step
  have hσ : ∀ l k, (if h : l ∈ Jf then some (κ l h) else none) = some k →
      ∃ h : l ∈ Jf, κ l h = k := by
    intro l k h
    by_cases hl : l ∈ Jf
    · rw [dite_eq_left hl] at h
      exact ⟨hl, Option.some.inj h⟩
    · rw [dite_eq_right hl] at h
      cases h
  refine ⟨fun l => if h : l ∈ Jf then some (κ l h) else none, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : a ∈ Jf := ha
    have hb' : b ∈ Jf := hb
    simp only [dite_eq_left ha', dite_eq_left hb'] at hab
    have hk := Option.some.inj hab
    have heq : SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r a) =
        SncRes.Par.chPrime (SncRes.ideal P p) (renPt (affCoord p z)) (r b) := by
      rw [← (hκ a ha').1, ← (hκ b hb').1, hk]
    by_contra hne
    obtain ⟨-, -, -, -, -, hsep, -⟩ := pr a ha'
    obtain ⟨-, -, -, -, hrb, -, -⟩ := pr b hb'
    exact hsep b hb' (Ne.symm hne) (heq ▸ hrb)
  · intro l
    by_cases hl : l ∈ Jf <;> simp [hl]
  · intro l k h
    obtain ⟨hl, rfl⟩ := hσ l k h
    exact hκ l hl
  · intro k hk
    have hQk := SncRes.compIdeal_mem (P := P) D k
    have hkh := hmin _ hQk
    have hkp : (SncRes.compIdeal P D k).IsPrime := hQk.1.1
    have hX : ∀ k', (X ⟨k', p k'⟩ : MvPolynomial (Σ k, ι k) ℂ) ∉ SncRes.compIdeal P D k := by
      intro k' hx
      exact hzp k' (by simpa using hk _ hx)
    obtain ⟨hkpr, hdict⟩ := chart_prime_and_mem_iff _ hkh hkp hX
    have hzc : z ∈ conePts (SncRes.compIdeal P D k) := ⟨hz.1, hk⟩
    have hpt : SncRes.ideal (SncRes.compIdeal P D k) p ≤ ptIdeal (renPt (affCoord p z)) := by
      intro h hh
      exact renPt_zero _ _ ((mem_conePts_iff_chartIdeal hkh p z hzp).1 hzc) h hh
    have hDk : SncRes.ideal (P ⊔ D) p ≤ SncRes.ideal (SncRes.compIdeal P D k) p :=
      ideal_mono hQk.1.2 p
    have hIk := hIDc.trans hDk
    obtain ⟨l, hl, hrl⟩ := (hprim _ hkpr hIk hpt).1 hDk
    obtain ⟨-, -, -, -, -, -, hmn⟩ := pr l hl
    have hle := hmn _ hkpr hIk hpt hrl
    rw [← (hκ l hl).1] at hle
    have hQ0 := SncRes.compIdeal_mem (P := P) D (κ l hl)
    obtain ⟨S, hS, hSeq⟩ := hmin _ hQ0
    have hsub : SncRes.compIdeal P D (κ l hl) ≤ SncRes.compIdeal P D k := by
      rw [hSeq, Ideal.span_le]
      intro f hf
      obtain ⟨a, ha⟩ := hS f hf
      have hfQ : f ∈ SncRes.compIdeal P D (κ l hl) := hSeq ▸ Ideal.subset_span hf
      exact (hdict f a ha).1 (hle (deh_mem p hfQ))
    have heq : SncRes.compIdeal P D (κ l hl) = SncRes.compIdeal P D k :=
      le_antisymm hsub (hQk.2 ⟨hQ0.1.1, hQ0.1.2⟩ hsub)
    refine ⟨l, hl, ?_⟩
    beta_reduce
    rw [dite_eq_left hl, compIdeal_injective P D heq]
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoiceStatement
section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_chart_regular_with_boundary_choice : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ) (p : (k : K) → ι k) (x : SncRes.Pts P) (r : Fin e → MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ) (Jf : Finset (Fin e)) (σ : Fin e → Option (Fin (SncRes.rc P D))), IsMultiHomogIdeal P → IsMultiHomogIdeal D → x ∈ SncRes.src P p → (∀ h ∈ (SncRes.ideal P p), eval (SncRes.coord P p x) h = 0) → IsRegularLocalRing (locRing (SncRes.ideal P p) (SncRes.coord P p x)) → ringKrullDim (locRing (SncRes.ideal P p) (SncRes.coord P p x)) = e → Ideal.span (Set.range fun l => algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x)) (r l)) = Ideal.map (algebraMap _ (locRing (SncRes.ideal P p) (SncRes.coord P p x))) (ptIdeal (SncRes.coord P p x)) → (∀ l, σ l = none ↔ l ∉ Jf) → (∀ l k, σ l = some k → SncRes.ideal (SncRes.compIdeal P D k) p = SncRes.Par.chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)) → (∀ k, (∀ g ∈ SncRes.compIdeal P D k, eval (SncRes.rep x) g = 0) → ∃ l ∈ Jf, σ l = some k) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∀ k, SncRes.comp P D k ∩ O = {x' ∈ O | ∃ l, σ l = some k ∧ eval (SncRes.coord P p x') (r l) = 0} := by
  intro K _ ι _ P D e p x r Jf σ hP hD hx _ _ _ _ _ hch hout
  classical
  have zero_iff {Q : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hQ : IsMultiHomogIdeal Q)
      (y : SncRes.Pts P) (hy : y ∈ SncRes.src P p) :
      (∀ f ∈ Q, eval (SncRes.rep y) f = 0) ↔
        ∀ h ∈ SncRes.ideal Q p, eval (SncRes.coord P p y) h = 0 := by
    have hchart := mem_conePts_iff_chartIdeal hQ p (SncRes.rep y) hy
    constructor
    · intro h
      exact renPt_zero _ _ (hchart.1 ⟨(SncRes.rep_mem y).1, h⟩)
    · intro h
      have hyQ : SncRes.rep y ∈ conePts Q := hchart.2 fun f hf => by
        rw [← eval_renC]
        exact h _ (Ideal.mem_map_of_mem _ hf)
      exact hyQ.2
  have norm_ne (y : SncRes.Pts P) (k : K) :
      ((∑ i, ‖SncRes.rep y ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (SncRes.Top.normSq_pos ((SncRes.rep_mem y).1 k)).ne'
  have mem_src_iff (y : SncRes.Pts P) :
      y ∈ SncRes.src P p ↔ ∀ k, y.1 ⟨k, (p k, p k)⟩ ≠ 0 := by
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep y]
    simp only [SncRes.proj, ne_eq, div_eq_zero_iff, norm_ne, or_false, mul_eq_zero,
      map_eq_zero, or_self]
  have hopen : IsOpen (SncRes.src P p) := by
    have heq : SncRes.src P p = ⋂ k, {y : SncRes.Pts P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp [mem_src_iff]
    rw [heq]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hcoord : ContinuousOn (SncRes.coord P p) (SncRes.src P p) := by
    refine continuousOn_iff_continuous_domRestrict.2 (continuous_pi fun j => ?_)
    let q := (Fintype.equivFin (Σ k, ι k)).symm j
    have hratio (y : SncRes.src P p) :
        SncRes.coord P p y.1 j = y.1.1 ⟨q.1, (q.2, p q.1)⟩ / y.1.1 ⟨q.1, (p q.1, p q.1)⟩ := by
      have hstar : starRingEnd ℂ (SncRes.rep y.1 ⟨q.1, p q.1⟩) ≠ 0 := by
        simpa using y.2 q.1
      change affCoord p (SncRes.rep y.1) q = _
      rw [← SncRes.proj_rep y.1]
      simp only [SncRes.proj, affCoord]
      rw [div_div_div_cancel_right₀ (norm_ne y.1 q.1), mul_div_mul_right _ _ hstar]
    have hv (a : Σ k, ι k × ι k) : Continuous fun y : SncRes.src P p => y.1.1 a :=
      (continuous_apply a).comp (continuous_subtype_val.comp continuous_subtype_val)
    change Continuous (fun y : SncRes.src P p => SncRes.coord P p y.1 j)
    simp only [hratio]
    exact (hv ⟨q.1, (q.2, p q.1)⟩).div (hv ⟨q.1, (p q.1, p q.1)⟩)
      (fun y => (mem_src_iff y.1).1 y.2 q.1)
  have hQ (k) : IsMultiHomogIdeal (SncRes.compIdeal P D k) :=
    MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι P D hP hD _ (SncRes.compIdeal_mem D k)
  choose s hst hsw using fun l =>
    SncRes.NearComp.exists_den_chPrime (SncRes.ideal P p) (SncRes.coord P p x) (r l)
  have hg : ∀ k, ∃ g, eval (SncRes.coord P p x) g ≠ 0 ∧
      ((∃ l, σ l = some k) ∨ g ∈ SncRes.ideal (SncRes.compIdeal P D k) p) := by
    intro k
    by_cases hk : ∃ l, σ l = some k
    · exact ⟨1, by simp, Or.inl hk⟩
    · have hn : ¬ ∀ h ∈ SncRes.ideal (SncRes.compIdeal P D k) p,
          eval (SncRes.coord P p x) h = 0 := fun h => by
        obtain ⟨l, -, hl⟩ := hout k ((zero_iff (hQ k) x hx).2 h)
        exact hk ⟨l, hl⟩
      push Not at hn
      obtain ⟨g, hg, hgt⟩ := hn
      exact ⟨g, hgt, Or.inr hg⟩
  choose g hgt hgk using hg
  let F := (∏ l, s l) * ∏ k, g k
  have hFw : ∀ w, eval w F ≠ 0 ↔ (∀ l, eval w (s l) ≠ 0) ∧ ∀ k, eval w (g k) ≠ 0 := by
    intro w
    simp only [F, map_mul, map_prod, ne_eq, mul_eq_zero, not_or, Finset.prod_eq_zero_iff,
      Finset.mem_univ, true_and, not_exists]
  refine ⟨SncRes.src P p ∩ SncRes.coord P p ⁻¹' {w | eval w F ≠ 0}, ?_,
    ⟨hx, (hFw _).2 ⟨hst, hgt⟩⟩, Set.inter_subset_left, fun k => ?_⟩
  · exact hcoord.isOpen_inter_preimage hopen
      (isOpen_ne_fun (MvPolynomial.continuous_eval F) continuous_const)
  · ext y
    constructor
    · rintro ⟨hc, ho⟩
      refine ⟨ho, ?_⟩
      have hz := (zero_iff (hQ k) y ho.1).1 hc
      rcases hgk k with ⟨l, hl⟩ | hk
      · refine ⟨l, hl, hz _ ?_⟩
        rw [hch l k hl]
        exact Ideal.mem_comap.2 (Ideal.subset_span rfl)
      · exact absurd (hz _ hk) (((hFw _).1 ho.2).2 k)
    · rintro ⟨ho, l, hl, hr⟩
      refine ⟨(zero_iff (hQ k) y ho.1).2 ?_, ho⟩
      rw [hch l k hl]
      exact hsw l _ ((zero_iff hP y ho.1).1 (SncRes.rep_mem y).2)
        (((hFw _).1 ho.2).1 l) hr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedFrameValueFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem sameOrbit_sqZ_of_flags : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (zb₂ : (Σ k, baseIdx ι M.blk k) → ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) (H U : Ψ → Matrix (Fin N) (Fin N) ℂ) (V : Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.blk (τ, a) = some k₀ → baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) → SameOrbit zb₂ (baseOf M k₀ z) → (∀ τ', IsBlockDiag j (U τ') ∧ (U τ').BlockTriangular id ∧ ∀ c, U τ' c c ≠ 0) → IsBlockDiag j V → V.BlockTriangular id → (∀ c ∈ stepCols N j a, V c c ≠ 0) → (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (H p.1 * U p.1) I (stepCols N j p.2)) → (∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (H τ * (1 + Matrix.single cb ca t) * V) I (stepCols N j a)) → SameOrbit (sqZ M F zb₂ H k₀ τ ca cb t) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ ca cb F zb₂ z H U V t hτ hz hG ho hU hV hVt hVd h1 h2
  have hval : ∀ s, valAt M.x s zb₂ = valAt M.x s (baseOf M k₀ z) := fun s =>
    CovMap.LocImg.valAt_orbit ho hz s
  have block : ∀ o : Option K, ∃ c : ℂ, c ≠ 0 ∧ ∀ m : ι (o.getD k₀),
      sqZ M F zb₂ H k₀ τ ca cb t ⟨o, m⟩ = c * z ⟨o, m⟩ := by
    rintro (_ | k)
    · have e : ∃ p, M.blk p = some k₀ := ⟨_, hτ⟩
      have hc : e.choose = (τ, a) := M.blk_inj _ _ k₀ e.choose_spec hτ
      obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le a hV hVt hVd
        (fun m : ι k₀ => sndPt k₀ z ⟨k₀, m⟩)
        (fun m I => valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z))).1 h2
      refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
      have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨none, m⟩ =
          ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) := by
        show flagZ M F zb₂ (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ = _
        refine (dif_pos e).trans ?_
        simp only [hc, Function.update_self, hval]
      have hn : z ⟨none, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) *
          minorIJ (H τ * (1 + Matrix.single cb ca t)) I (stepCols N j a) :=
        (WSq.Pts.snd_self z m).symm.trans (hm m)
      rw [hs, hn, inv_mul_cancel_left₀ hα]
    · by_cases e : ∃ p, M.blk p = some k
      · obtain ⟨α, hα, hm⟩ := (WSq.Pts.step_mul_right M.j_le e.choose.2 (hU e.choose.1).1 (hU e.choose.1).2.1
          (fun c _ => (hU e.choose.1).2.2 c) (fun m : ι k => fstPt k₀ z ⟨k, m⟩)
          (fun m I => valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z))).1 (h1 e.choose k e.choose_spec)
        refine ⟨α⁻¹, inv_ne_zero hα, fun m => ?_⟩
        have hs : sqZ M F zb₂ H k₀ τ ca cb t ⟨some k, m⟩ =
            ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
              minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := by
          show flagZ M F zb₂ H ⟨k, m⟩ = _
          refine (dif_pos e).trans ?_
          simp only [hval]
        have hn : z ⟨some k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) *
            minorIJ (H e.choose.1) I (stepCols N j e.choose.2) := hm m
        rw [hs, hn, inv_mul_cancel_left₀ hα]
      · obtain ⟨c, hc, hcz⟩ := ho
        have hk : ∀ p, M.blk p ≠ some k := fun p hp => e ⟨p, hp⟩
        refine ⟨c ⟨k, hk⟩, hc _, fun m => ?_⟩
        show flagZ M F zb₂ H ⟨k, m⟩ = _
        refine (dif_neg e).trans ?_
        rw [hcz]
        rfl
  choose c hc hcz using block
  exact ⟨c, hc, funext fun p => hcz p.1 p.2⟩

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

