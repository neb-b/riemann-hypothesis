module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0066
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLineLatticeTrivialMod
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0152
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0154
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0070
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmTypeExteriorLatticeComparison
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSection
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0179
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.FiniteEtaleSurjectiveOfPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrModelOfNumberFieldPlace
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0157
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0220
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0219
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0167
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtIffValueAt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryPointsClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.BdSym

theorem boundary_closed_torus_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (T : Set X) (bd : Ideal (MRing J)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ centre z ∉ T)) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) ∧ (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) ∧ ∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, conjVec z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd := by
  intro X Ω _ ξ K _ J _ y T bd hT hbd
  have key := _root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt X Ω ξ K J y hT
  refine ⟨?_, ?_, ?_⟩
  · have e : ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) =
        ⋂ f ∈ bd, {w : mcPts (mCoordIdeal y) |
          MvPolynomial.eval w.1 (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
      ext w
      have hw : w.1 ∈ mcPts (mCoordIdeal y) := w.2
      rw [Set.mem_iInter₂]
      simp only [mcPts, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
      exact ⟨fun h => h.2.2, fun h => ⟨hw, hw.1, h⟩⟩
    rw [e]
    refine isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  · rintro w ⟨hw1, hw2⟩ c hc
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc : CoordsAt ξ y z (torusSmul c w) := by
      have h' := hzw
      unfold CoordsAt at h' ⊢
      refine ⟨fun k => ?_, fun k i hu => ?_⟩
      · obtain ⟨i, hi⟩ := h'.1 k
        refine ⟨i, isUnit_iff_ne_zero.2 ?_⟩
        show c k * w ⟨k, i⟩ ≠ 0
        exact mul_ne_zero (hc k) (isUnit_iff_ne_zero.1 hi)
      · have hu' : IsUnit (w ⟨k, i⟩) := by
          refine isUnit_iff_ne_zero.2 fun h0 => isUnit_iff_ne_zero.1 hu ?_
          show c k * w ⟨k, i⟩ = 0
          rw [h0, mul_zero]
        obtain ⟨hy, hr⟩ := h'.2 k i hu'
        refine ⟨hy, fun j => ?_⟩
        obtain ⟨r, hr1, hr2⟩ := hr j
        refine ⟨r, hr1, ?_⟩
        show c k * w ⟨k, j⟩ = r * (c k * w ⟨k, i⟩)
        rw [hr2]
        ring
    exact Set.mem_inter ((key _).2 ⟨z, hz, hzc⟩) ((hbd z _ hzc).2 ((hbd z w hzw).1 hw2))
  · rintro w ⟨hw1, hw2⟩
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc := GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj hzw
    have hcz : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) = centre z := GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z
    have hz' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) := by
      rw [hcz]
      exact hz
    have hT' : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) ∉ T := by
      rw [hcz]
      exact (hbd z w hzw).1 hw2
    exact Set.mem_inter ((key (conjVec w)).2 ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z, hz', hzc⟩) ((hbd _ _ hzc).2 hT')

end GlobalTheory.CompanionTheory.Ar.BdSym
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ConjugatePointSameCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.CoordConj

theorem centre_and_coords_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), centre (spMap (starRingEnd ℂ) ≫ z) = centre z ∧ (CoordsAt ξ y z w → CoordsAt ξ y (spMap (starRingEnd ℂ) ≫ z) (conjVec w)) := by
  intro X Ω _ ξ K _ J _ y z w
  exact ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z, fun h => GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj h⟩

end GlobalTheory.CompanionTheory.Ar.CoordConj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CptFlatInputsOfPropZ
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem orderAt_of_unit {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {L : Lat ξ Ω} {σ ϖ ϖ' : Ω}
    {M : ℕ} {a : ℤ} {p : Cpt ξ} (h : OrderAt L σ ϖ M a p) (hu : unitAt ξ p (ϖ / ϖ')) : OrderAt L σ ϖ' M a p := by
  obtain ⟨e, c, he, hL, hσ, hc⟩ := h
  refine ⟨e, c, he, hL, hσ, ?_⟩
  have h0 : ϖ ≠ 0 := fun h => hu.1 (by simp [h])
  have h1 : ϖ' ≠ 0 := fun h => hu.1 (by simp [h])
  have hz : ∀ n : ℤ, unitAt ξ p ((ϖ / ϖ') ^ n) := fun n => by
    cases n with
    | ofNat m => simpa using ZUnit.pow hu m
    | negSucc m => simpa using ZUnit.inv (ZUnit.pow hu (m + 1))
  have : c ^ M / ϖ' ^ a = c ^ M / ϖ ^ a * (ϖ / ϖ') ^ a := by
    rw [div_zpow]
    field_simp
  rw [this]
  exact ZUnit.mul hc (hz a)

theorem exists_orders (hZ : PropZ) {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {κ : Type} [Finite κ] {x : κ → Ω} {F' : Type} [Field F'] [NumberField F'] (ψ : F' →+* Ω)
    (hcl : ∀ x : Ω, (∃ f : Polynomial F', f ≠ 0 ∧ f.eval₂ ψ x = 0) → x ∈ Set.range ψ)
    (hall : ∀ q : X, genPt ξ ⤳ q) (ht : CoordTie ℤ ξ x) (hN : NormalCpt ξ) (L : Lat ξ Ω) (σ : Ω)
    (hL : L.IsVB 1 ⊤) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p σ)
    (hp : ∀ ℓ : ℕ, ℓ.Prime → TrivMod L (ℓ : Ω) ∨ NumTrivMod L (ℓ : Ω)) :
    ∃ r : HeightOneSpectrum (𝓞 F') →₀ ℚ, ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'),
      v.valuation F' π = WithZero.exp (-1 : ℤ) → ∃ (m : ℕ) (k : ℤ), 0 < m ∧ (k : ℚ) = m * r v ∧ ∀ p : Cpt ξ,
        (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) → OrderAt L σ (ψ π) m k p := by
  classical
  have hchar : CharZero Ω := charZero_of_injective_ringHom ψ.injective
  have hplace : ∀ (v : HeightOneSpectrum (𝓞 F')) (π : F'), v.valuation F' π = WithZero.exp (-1 : ℤ) →
      ∃ (M : ℕ) (a : ℤ), 0 < M ∧ ∀ p : Cpt ξ, (∀ a : F', v.valuation F' a ≤ 1 → ψ a ∈ regAt ξ p) →
        OrderAt L σ (ψ π) M a p := by
    intro v π hπ
    obtain ⟨O, _, _, _, _, X', ξ', s, g, ϖ, hs, hϖ, hinj, hξs, hξg, hgen', hall', hϖπ, hrange, hreg, hsurj⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.Flat.LocModel.exists_localisation X Ω ξ κ x F' ψ v π hall ht hN hπ
    obtain ⟨ℓ, hℓ, hℓv⟩ := GlobalTheory.T.exists_prime_dividing_uniformizer F' v π hπ
    obtain ⟨u, hu⟩ : ∃ u : O, algebraMap O Ω u = ψ ((ℓ : F') / π) :=
      (hrange _).2 ⟨_, hℓv, rfl⟩
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp at hπ
      exact WithZero.exp_ne_zero hπ.symm
    have hcc : ConstClosed O Ω := by
      intro a ha
      obtain ⟨f, hf, hfa⟩ := ha
      have hlift : f.map (algebraMap O Ω) ∈ Polynomial.lifts ψ := by
        rw [Polynomial.lifts_iff_coeff_lifts]
        intro n
        rw [Polynomial.coeff_map]
        obtain ⟨b, -, hb⟩ := (hrange _).1 ⟨f.coeff n, rfl⟩
        exact ⟨b, hb⟩
      obtain ⟨f', hf'⟩ := (Polynomial.mem_lifts _).1 hlift
      have hne : f' ≠ 0 := by
        rintro rfl
        rw [Polynomial.map_zero] at hf'
        exact hf ((Polynomial.map_eq_zero_iff hinj).1 hf'.symm)
      obtain ⟨b, rfl⟩ := hcl a ⟨f', hne, by
        rw [← Polynomial.eval_map, hf', Polynomial.eval_map]
        exact hfa⟩
      by_cases hb : v.valuation F' b ≤ 1
      · obtain ⟨x₀, hx₀⟩ := (hrange (ψ b)).2 ⟨b, hb, rfl⟩
        exact ⟨x₀, 1, one_ne_zero, by rw [map_one, mul_one]; exact hx₀.symm⟩
      · have hb0 : b ≠ 0 := by
          rintro rfl
          simp at hb
        have hb' : v.valuation F' b⁻¹ ≤ 1 := by
          rw [map_inv₀]
          exact inv_le_one_of_one_le₀ (le_of_not_ge hb)
        obtain ⟨y₀, hy₀⟩ := (hrange (ψ b⁻¹)).2 ⟨b⁻¹, hb', rfl⟩
        refine ⟨1, y₀, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hy₀
          exact inv_ne_zero hb0 ((map_eq_zero ψ).1 hy₀.symm)
        · rw [hy₀, ← map_mul, mul_inv_cancel₀ hb0, map_one, map_one]
    have hℓu : (ℓ : Ω) = algebraMap O Ω (ϖ * u) := by
      rw [map_mul, hϖπ, hu, ← map_mul, mul_div_cancel₀ _ hπ0, map_natCast]
    obtain ⟨M, a, hM, h⟩ := @_root_.GlobalTheory.CompanionTheory.Ar.Flat.PlaceOrd.order_at_place X X' Ω _ _ ξ ξ' g O _ _ _ _ s hs ϖ L σ ℓ u hZ hϖ hinj hξs hξg ht.gen hgen' hall'
      hN hcc hreg hL hg hℓu (hp ℓ hℓ)
    refine ⟨M, a, hM, fun p hv => ?_⟩
    have := h p (hsurj p hv)
    rwa [hϖπ] at this
  obtain ⟨s, hs1, hs2, hs3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ChartFType.main X Ω ξ κ x hall ht
  obtain ⟨n, hn, hgn⟩ := @_root_.GlobalTheory.CompanionTheory.Ar.Flat.lattice_generator_spread X Ω _ ξ ℤ _ _ _ s _ hs1 hs2 hs3 (Int.cast_injective) ht.gen L Set.univ 1 σ
    one_ne_zero (fun _ _ => trivial) hL hg
  have hn' : ((n : F'))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F') ((n : F'))⁻¹
  choose π hπ using fun v : HeightOneSpectrum (𝓞 F') => v.valuation_exists_uniformizer F'
  choose M a hM hord using fun v => hplace v (π v) (hπ v)
  let T := HeightOneSpectrum.Support (𝓞 F') ((n : F'))⁻¹
  let r₀ : HeightOneSpectrum (𝓞 F') → ℚ := fun v => if v ∈ T then (a v : ℚ) / M v else 0
  have hr₀ : (Function.support r₀).Finite := hfin.subset fun v hv => by
    by_contra h
    exact hv (if_neg h)
  refine ⟨Finsupp.ofSupportFinite r₀ hr₀, fun v π' hπ' => ?_⟩
  have hrv : (Finsupp.ofSupportFinite r₀ hr₀) v = r₀ v := rfl
  rw [hrv]
  by_cases hv : v ∈ T
  · have hMv : (M v : ℚ) ≠ 0 := by exact_mod_cast (hM v).ne'
    refine ⟨M v, a v, hM v, by simp only [r₀, if_pos hv]; field_simp, fun p hp => ?_⟩
    refine orderAt_of_unit (hord v p hp) ?_
    have h0 : π' ≠ 0 := by
      rintro rfl
      simp at hπ'
      exact WithZero.exp_ne_zero hπ'.symm
    have h1 : π v ≠ 0 := by
      intro h
      have := hπ v
      rw [h] at this
      simp at this
      exact WithZero.exp_ne_zero this.symm
    have e1 : v.valuation F' (π v / π') = 1 := by
      rw [map_div₀, hπ v, hπ', div_self (WithZero.exp_ne_zero)]
    have e2 : v.valuation F' (π v / π')⁻¹ = 1 := by rw [map_inv₀, e1, inv_one]
    rw [← map_div₀]
    exact ⟨(map_ne_zero ψ).2 (div_ne_zero h1 h0), hp _ e1.le, by rw [← map_inv₀]; exact hp _ e2.le⟩
  · refine ⟨1, 0, one_pos, by simp only [r₀, if_neg hv]; simp, fun p hp => ?_⟩
    have h1 : v.valuation F' (n : F') ≤ 1 := by
      have := v.valuation_le_one (K := F') (n : 𝓞 F')
      simpa using this
    have h2 : v.valuation F' ((n : F'))⁻¹ ≤ 1 := not_lt.1 hv
    have hu : unitAt ξ p (algebraMap ℤ Ω n) := by
      have e : algebraMap ℤ Ω n = ψ (n : F') := by simp
      rw [e]
      exact ⟨(map_ne_zero ψ).2 (by exact_mod_cast hn), hp _ h1, by rw [← map_inv₀]; exact hp _ h2⟩
    have := hgn p hu
    exact orderAt_one_zero.2 this

theorem isCoeffAt_of_smul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] {A B : Lat ξ V} {p q : ℕ} {a a' : ⋀[Ω]^p V} {b b' : ⋀[Ω]^q V} {x : Cpt ξ}
    {d₁ d₂ : Ω} (h₁ : d₁ ≠ 0) (h₂ : d₂ ≠ 0) (ea : a' = d₁ • a) (eb : b' = d₂ • b)
    (h : IsCoeffAt A B p q a' b' x 1) : IsCoeffAt A B p q a b x (d₁ / d₂)⁻¹ := by
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  rw [one_mul] at e
  subst e
  refine ⟨α * d₁, α * d₂, mul_ne_zero hα h₁, mul_ne_zero hα h₂, ?_, ?_, ?_⟩
  · rw [hA, ea, smul_smul]
  · rw [hB, eb, smul_smul]
  · field_simp

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeMetricFrameInner
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameGram

theorem inner_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (a : D.Frame σ) (x y : D.B.carrier) (c c' : Fin D.g → ℂ), D.IsVec a x c → D.IsVec a y c' → ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] y) : ℂ) = Real.pi * a.herm c' c := by
  intro E _ _ _ H L _ _ D σ a x y c c' hx hy
  obtain ⟨t', m, hP, hA⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Sl.FibrePol.exists_fibre_pol E H L D σ
  obtain ⟨hab, g, u, Hm, χ, hAH, d₁, d₂⟩ := FrameEx.exists_goodUnif E H _ D.t (emb σ) t' m hP hA
  have hp : IsGrpPullback t'.G D.t.G (emb σ) m.φ := m.cart
  obtain ⟨v, hlift, vA, hvA, hdiff⟩ := hx
  obtain ⟨w, hlift', wA, hwA, hdiff'⟩ := hy
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  let w₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk w.left (by simpa using Over.w w)
  have hl₀ : (v₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := hlift
  have hl₁ : (w₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt y).left) := hlift'
  obtain ⟨hL, hvt, hwt, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x y v₀ w₀ hl₀ hl₁
  have hp₀ : IsGrpPullback t'.G D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) m.φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm v₀
  let y₁ : epsR ℂ ⟶ t'.G := (HodgeLin.tanEquiv hp₀).symm w₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have hy₁ : HodgeLin.tanEquiv hp₀ y₁ = w₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have ty₁ : IsTangent y₁ := (HodgeLin.isTangent_iff hp₀ y₁).2 (by rw [hy₁]; exact hwt)
  have lx₁ : x₁.left ≫ m.φ = v.left := congrArg (fun r => r.left) hx₁
  have ly₁ : y₁.left ≫ m.φ = w.left := congrArg (fun r => r.left) hy₁
  obtain ⟨cx, hcx, -⟩ := d₁ x₁ tx₁
  obtain ⟨cy, hcy, -⟩ := d₁ y₁ ty₁
  have T1 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G a.A m.φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB
    hab hp a.cart d₁ d₂ hAH a.ah y₁ x₁ wA vA cy cx c' c ty₁ tx₁ (hwA.trans ly₁.symm) (hvA.trans lx₁.symm) hcy hcx
    hdiff' hdiff
  have T2 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) t'.G A' m.φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB
    hab hp hpz d₁ d₂ hAH hah' y₁ x₁ q p cy cx b' a' ty₁ tx₁ (eq'.trans ly₁.symm) (ep.trans lx₁.symm) hcy hcx dq dp
  have hH : a.herm c' c = hermForm Hm' b' a' := T1.trans T2.symm
  rw [hH]
  exact hval

end GlobalTheory.CompanionTheory.Ar.Sl.FrameGram
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicDiscOverNumberFieldRingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_disc_over_number_field_ring : ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) (q : X ⟶ Sp (𝓞 F)) (n : ℕ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ X)), IsHolTo (Metric.ball 0 1) p → ∃ τ : F →+* ℂ, ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ q = spMap (τ.comp (algebraMap (𝓞 F) F)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding | exact GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding | (intros; apply GlobalTheory.CompanionTheory.Ar.ConstEmbedding.exists_embedding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionSystemHodgeData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen

theorem gramAt_eq_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X) (w : (Σ k, J k) → ℂ) (τ : CMType H) (b : Fin Dc.N → W τ) (h : genPt Or.𝔐.ξ ⤳ centre z) (G : Matrix (Fin Dc.N) (Fin Dc.N) ℂ), CoordsAt Or.𝔐.ξ Dc.y z w → Or.𝔐.Interior z → (Lat.comap (fun p => Or.𝔐.V (Or.bg τ) p ⊔ Or.𝔐.V (Or.sm τ) p) (Or.i τ)).IsFrameAt b ⟨centre z, h⟩ → Or.𝔐.M.GramAt Or.𝔐.t.PP.L z (fun k => Or.i τ (b k)) G → gramAt (Dc.h τ) b w = G := by
  intro E _ _ _ H D l Xo c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or z w τ b h G hco hint hfr hG
  classical
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hw : w ∈ mcPts (mCoordIdeal Dc.y) :=
    (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).2 ⟨z, h, hco⟩
  have hnb : w ∉ Dc.Bd := fun hb => (Or.bd z w hco).1 hb hint
  have hex : ∃ a, InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w :=
    (Dc.h τ).cover w ⟨hw, hnb⟩
  have hsib := _root_.GlobalTheory.CompanionTheory.Ar.BlockSumFrame.frame_at E H D l Xo c Y II K J Ω W Dc Hd S₀ Or z w τ ((Dc.h τ).chart hex.choose)
    ((Dc.h τ).fr hex.choose) ((Dc.h τ).b hex.choose) h hco ((Dc.h τ).isFrame _) hex.choose_spec
  have hmem : ∀ q, b q ∈ Submodule.span (regAt Or.𝔐.ξ ⟨centre z, h⟩) (Set.range ((Dc.h τ).b hex.choose)) := by
    intro q
    rw [← hsib.2, hfr.2]
    exact Submodule.subset_span ⟨q, rfl⟩
  choose cf hcf using fun q => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem q)
  have hS : ∃ S : Matrix (Fin Dc.N) (Fin Dc.N) Ω, ∀ q, b q = ∑ p, S p q • (Dc.h τ).b hex.choose p :=
    ⟨Matrix.of fun p q => (cf q p : Ω), fun q => by rw [← hcf q]; rfl⟩
  have hreg : ∀ p q, hS.choose p q = (cf q p : Ω) := by
    intro p q
    have h0 : ∑ p, (hS.choose p q - (cf q p : Ω)) • (Dc.h τ).b hex.choose p = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hS.choose_spec q, sub_eq_zero]
      rw [← hcf q]
      rfl
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hsib.1 _ h0 p)
  choose s hs using fun p q => RingHom.mem_range.1 (cf q p).2
  have hval : ∀ p q, ValAt Or.𝔐.ξ z (hS.choose p q)
      ((Scheme.stalkClosedPointTo z).hom (s p q)) := fun p q =>
    ⟨h, s p q, by rw [hreg, hs], rfl⟩
  have hmat : (Matrix.of fun p q => valAt Dc.y (hS.choose p q) w) =
      Matrix.of fun p q => (Scheme.stalkClosedPointTo z).hom (s p q) := by
    ext p q
    exact valAt_eq hw ((_root_.GlobalTheory.CompanionTheory.Ar.valAt_iff_isValueAt_coords Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie z w h hco _ _).1 (hval p q))
  rw [gramAt, dite_eq_left hex, dite_eq_left hS, hmat]
  refine (GlobalTheory.T.gram_matrix_two_frames E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z Dc.N (fun k => Or.i τ ((Dc.h τ).b hex.choose k))
    (fun k => Or.i τ (b k)) _ G hS.choose _ (_root_.GlobalTheory.CompanionTheory.Ar.HodgeMetric.polarisedAt_of_interior E H D l Xo c Y S₀ Ω K J Dc.y Or.𝔐 z hint)
    (Or.metric τ hex.choose z w hco hint hex.choose_spec) hG ?_ hval).symm
  intro q
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hS.choose_spec q, map_sum]
  exact Finset.sum_congr rfl fun p _ => map_smul _ _ _

end GlobalTheory.CompanionTheory.Ar.Cusp.GramChosen
end

