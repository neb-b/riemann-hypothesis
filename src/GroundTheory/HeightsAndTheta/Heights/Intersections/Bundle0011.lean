module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsFunFieldMulEq
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def funField {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

theorem exists_funField_mul_eq {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} [P.IsPrime] {f g : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) := by
  have hv : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  exact ⟨⟨IsLocalization.mk' _ (Ideal.Quotient.mk P f) ⟨_, hv⟩,
    Subring.subset_closure ⟨f, g, a, hv, hf, hg, rfl⟩⟩, IsLocalization.mk'_spec _ _ _⟩

def regularityEmbedding_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar P 1 → (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ e : R ≃ (funField P →+* ℂ), ∀ (t : R) (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a → IsMultiHomog v a → v ∉ P → ∀ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) *
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
      e t x * eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) v) =
        eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) u)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LogNormDivSameOrbit
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem log_norm_div_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖) =
      Real.log (‖eval z' (map (Int.castRingHom ℂ) f)‖ / ‖eval z' (map (Int.castRingHom ℂ) g)‖) := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog f a hf c z', eval_smul_homog g a hg c z', norm_mul, norm_mul,
    mul_div_mul_left _ _ hc0]

theorem RegularityProductFormula.proof (hPts : regularityPointsSum_holds.Statement) (hVert : VerticalClosedPoints.Statement) :
    RegularityProductFormula.Statement := by
  intro K _ ι _ P f g a hP hf hg hfP hgP
  obtain ⟨R, hRP, hRu, hsum⟩ := hPts K ι P hP
  rw [hVert K ι P f g a R hP hf hg hfP hgP hRP hRu]
  exact (hsum _ fun z z' _ h => log_norm_div_sameOrbit hf hg h).symm

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagPull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

namespace DiagPull

section Ring

variable {R : Type*} [CommRing R]

theorem mem_minimalPrimes_of_cross {V W : Ideal R} {f g u v : R} (hrel : f * v - g * u ∈ V)
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hu : u ∉ W) (hv : v ∉ W) :
    W ∈ (V ⊔ Ideal.span {g}).minimalPrimes := by
  have hWp := hW.1.1
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hgW : g ∈ W := by
    have h : g * u ∈ W := by
      have e : g * u = f * v - (f * v - g * u) := by ring
      rw [e]
      exact W.sub_mem (W.mul_mem_right v hfW) (hVW hrel)
    exact (hWp.mem_or_mem h).resolve_right hu
  refine ⟨⟨hWp, sup_le hVW ((Ideal.span_singleton_le_iff_mem _).mpr hgW)⟩, fun Q hQ hQW => ?_⟩
  have hVQ : V ≤ Q := le_sup_left.trans hQ.2
  have hgQ : g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hfQ : f ∈ Q := by
    have h : f * v ∈ Q := by
      have e : f * v = (f * v - g * u) + g * u := by ring
      rw [e]
      exact Q.add_mem (hVQ hrel) (Q.mul_mem_right u hgQ)
    exact (hQ.1.mem_or_mem h).resolve_right fun h' => hv (hQW h')
  exact hW.2 ⟨hQ.1, sup_le hVQ ((Ideal.span_singleton_le_iff_mem _).mpr hfQ)⟩ hQW

theorem locLen_cross {V : Ideal R} (hV : V.IsPrime) {f g u v : R} (hrel : f * v - g * u ∈ V)
    (p : PrimeSpectrum R) (hVp : V ≤ p.asIdeal) (hu : u ∉ p.asIdeal) (hv : v ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {f})) p = locLen (R ⧸ (V ⊔ Ideal.span {g})) p := by
  have e : V ⊔ Ideal.span {v * f} = V ⊔ Ideal.span {u * g} := by
    apply le_antisymm
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : v * f = (f * v - g * u) + u * g := by ring
      rw [e']
      exact Ideal.add_mem _ (Ideal.mem_sup_left hrel)
        (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    · refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
      have e' : u * g = v * f - (f * v - g * u) := by ring
      rw [e']
      exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        (Ideal.mem_sup_left hrel)
  have h1 := I1.locLen_mul hV (fun h => hv (hVp h)) f p
  have h2 := I1.locLen_mul hV (fun h => hu (hVp h)) g p
  rw [e, h2, I1.locLen_quot_eq_zero p hu, I1.locLen_quot_eq_zero p hv, add_zero, add_zero] at h1
  exact h1.symm

end Ring

section Homog

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

end Homog

section Models

variable {Ω : Type*} [Field Ω] {ι ν κ : Type u} [Fintype ι] [Fintype ν] [Fintype κ]
  {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]
  (x : ι → Ω) (δ : ν → Ω) (e : Module.Basis (Fin 2) Ω E) (φ : κ → E →ₗ[Ω] Ω) (a₀ : Φ)



end Models

end DiagPull

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum
  GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

theorem C_charOf_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
  have h : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) ∈
      V.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  exact h

theorem GeoNumCut.full : GeoNumCut.Statement := by
  intro K _ ι _ V n a b t hV hp hdim ht htV
  classical
  set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf V with hp_def
  have : Fact p.Prime := ⟨hp⟩
  have hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := C_charOf_mem V
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have : V.IsPrime := hV.1

  have hQ : IsMultiProjPrime (V.map (red p)) := by
    refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩
    · rw [isMultiHomogIdeal_iff]
      obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hS f hf
      exact ⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [← isRelevant_comap_iff p, hcm]
      exact hV.2.2
  have hd : relDim (V.map (red p)) = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this.symm

  have htr : IsMultiHomog (red p t) b := by
    rw [isMultiHomog_iff]
    exact fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k
  have htrV : red p t ∉ V.map (red p) := by
    intro h
    apply htV
    rw [← hcm]
    exact h

  rw [← intNum_map_eq_geoNum p (n + 1) V hV hpV hdim,
    CutRegular.full (ZMod p) K ι (V.map (red p)) hQ n hd b (red p t) htr htrV a]
  have hcut := cycEval_divCycle_eq p (V.map (red p)) t
    (fun W => intNum (ZMod p) W a) (fun W => ReciprocityTheory.ChartRestriction.G.Geo.geoNum n W a)
    (fun W' hW' => by
      obtain ⟨hW'm, hW'd⟩ :=
        DivCycleSupport.full (ZMod p) K ι (V.map (red p)) hQ n hd b _ htr htrV W' hW'
      exact intNum_eq_geoNum_comap p n W' hW'm hW'd a)
  rw [hcm] at hcut
  exact hcut

end

end GroundTheory.Heights₂.Heights.Inter
end

