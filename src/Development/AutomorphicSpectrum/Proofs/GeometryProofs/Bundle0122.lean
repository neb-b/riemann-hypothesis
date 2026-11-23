module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ValRPullbackTwistingSheafTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0109

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SegreProductAffineChart
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart

theorem isAffineOpen_fst_inf_snd {S X Y : Scheme.{0}} [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S) {U : X.Opens}
    {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hV
  let m := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)
  haveI : IsOpenImmersion m :=
    inferInstance
  have e : m.opensRange = pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V := by
    ext1
    refine (Scheme.Pullback.range_map _ _ _ _ _ _ _ _ _).trans ?_
    simp
  rw [← e]
  exact isAffineOpen_opensRange m

theorem spec_rat_ext {C : Type} [CommRing C] (u v : Sp C ⟶ Sp ℚ) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v]
  congr 1
  ext1
  exact Subsingleton.elim _ _

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {X Y : Scheme.{0}} (f : X ⟶ Sp ℚ) (g : Y ⟶ Sp ℚ)
  {U : X.Opens} {V : Y.Opens}

theorem val_mem_of_components (hU : IsAffineOpen U) (hV : IsAffineOpen V) (C : Subalgebra ℚ Ω)
    (p : Sp Ω ⟶ pullback f g) (hA : ⊤ ≤ (p ≫ pullback.fst f g) ⁻¹ᵁ U) (hB : ⊤ ≤ (p ≫ pullback.snd f g) ⁻¹ᵁ V)
    (mA : ∀ s, (valMap (p ≫ pullback.fst f g) U hA).hom s ∈ C)
    (mB : ∀ s, (valMap (p ≫ pullback.snd f g) V hB).hom s ∈ C)
    (h : ⊤ ≤ p ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V))
    (t : Γ(pullback f g, pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) :
    (valMap p _ h).hom t ∈ C := by
  let ι : CommRingCat.of C ⟶ CommRingCat.of Ω := CommRingCat.ofHom C.val.toRingHom
  let φA : Γ(X, U) ⟶ CommRingCat.of C := CommRingCat.ofHom ((valMap _ U hA).hom.codRestrict C mA)
  let φB : Γ(Y, V) ⟶ CommRingCat.of C := CommRingCat.ofHom ((valMap _ V hB).hom.codRestrict C mB)
  have eA : φA ≫ ι = valMap _ U hA := rfl
  have eB : φB ≫ ι = valMap _ V hB := rfl
  have hfg : (Spec.map φA ≫ hU.fromSpec) ≫ f = (Spec.map φB ≫ hV.fromSpec) ≫ g := spec_rat_ext _ _
  let q : Sp C ⟶ pullback f g := pullback.lift _ _ hfg
  have hq : Spec.map ι ≫ q = p := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ← Spec.map_comp, eA,
        specMap_valMap_fromSpec hU]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, ← Spec.map_comp, eB,
        specMap_valMap_fromSpec hV]
  have h₃ : ⊤ ≤ (q ≫ pullback.fst f g) ⁻¹ᵁ U := by
    rw [pullback.lift_fst]
    exact le_preimage_specMap_fromSpec hU φA
  have h₄ : ⊤ ≤ (q ≫ pullback.snd f g) ⁻¹ᵁ V := by
    rw [pullback.lift_snd]
    exact le_preimage_specMap_fromSpec hV φB
  have hqW : ⊤ ≤ q ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) :=
    fun y hy => ⟨h₃ hy, h₄ hy⟩
  have key : ∀ h' : ⊤ ≤ (Spec.map ι ≫ q) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V),
      valMap (Spec.map ι ≫ q) _ h' = valMap q _ hqW ≫ ι := fun h' => by
    rw [← appLE_valMap (Spec.map ι) q hqW (le_preimage_top _) h', valMap_specMap]
    simp only [valMap, Category.assoc]
  have h' : ⊤ ≤ (Spec.map ι ≫ q) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
    rw [hq]
    exact h
  have e : (valMap p _ h).hom t = (valMap (Spec.map ι ≫ q) _ h').hom t := by
    rw [← valR_eq, ← valR_eq, hq]
  rw [e, key]
  exact ((valMap q _ hqW).hom t).2

theorem closed_prod_chart {Z : Scheme.{0}} (j : Z ⟶ pullback f g) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z)
    (pX : Sp Ω ⟶ X) (pY : Sp Ω ⟶ Y) (h₁ : ζ ≫ j ≫ pullback.fst f g = pX) (h₂ : ζ ≫ j ≫ pullback.snd f g = pY)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hA : ⊤ ≤ pX ⁻¹ᵁ U) (hB : ⊤ ≤ pY ⁻¹ᵁ V) (R₁ R₂ : Set Ω)
    (e₁ : Set.range (valMap pX U hA).hom = Algebra.adjoin ℚ R₁)
    (e₂ : Set.range (valMap pY V hB).hom = Algebra.adjoin ℚ R₂) :
    IsAffineOpen ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V),
        Set.range (valMap ζ _ h).hom = Algebra.adjoin ℚ (R₁ ∪ R₂) := by
  subst h₁ h₂
  have hW := isAffineOpen_fst_inf_snd f g hU hV
  have hZ : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst f g) ⁻¹ᵁ U ⊓ (j ≫ pullback.snd f g) ⁻¹ᵁ V) :=
    fun y hy => ⟨hA hy, hB hy⟩
  have hp : ⊤ ≤ (ζ ≫ j) ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := hZ
  have hA' : ⊤ ≤ ((ζ ≫ j) ≫ pullback.fst f g) ⁻¹ᵁ U := by rwa [Category.assoc]
  have hB' : ⊤ ≤ ((ζ ≫ j) ≫ pullback.snd f g) ⁻¹ᵁ V := by rwa [Category.assoc]
  have vA : ∀ s, (valMap ((ζ ≫ j) ≫ pullback.fst f g) U hA').hom s = (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom s := by
    intro s
    rw [← valR_eq, ← valR_eq, Category.assoc]
  have vB : ∀ s, (valMap ((ζ ≫ j) ≫ pullback.snd f g) V hB').hom s = (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom s := by
    intro s
    rw [← valR_eq, ← valR_eq, Category.assoc]
  refine ⟨hW.preimage j, hZ, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨s, rfl⟩
    obtain ⟨t, rfl⟩ := j.app_surjective _ hW s
    have e : (valMap (ζ ≫ j) _ hp).hom t = (valMap ζ _ hZ).hom ((j.app _).hom t) :=
      (valR_eq _ _ hp t).symm.trans ((valR_comp ζ j _ t).trans (valR_eq ζ (j ⁻¹ᵁ (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V)) hZ _))
    rw [← e]
    refine val_mem_of_components f g hU hV _ (ζ ≫ j) hA' hB' (fun s => ?_) (fun s => ?_) hp t
    · rw [vA]
      have m : (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom s ∈ (Algebra.adjoin ℚ R₁ : Set Ω) := by
        rw [← e₁]
        exact Set.mem_range_self s
      exact Algebra.adjoin_mono Set.subset_union_left m
    · rw [vB]
      have m : (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom s ∈ (Algebra.adjoin ℚ R₂ : Set Ω) := by
        rw [← e₂]
        exact Set.mem_range_self s
      exact Algebra.adjoin_mono Set.subset_union_right m
  · let F : Z ⟶ Sp ℚ := j ≫ pullback.fst f g ≫ f
    let S : Subalgebra ℚ Ω :=
      { (valMap ζ _ hZ).hom.range with
        algebraMap_mem' := fun c => ⟨(GlobalTheory.QCoh.Qcqs.baseRingHom F _).hom c,
          RingHom.congr_fun (Subsingleton.elim
            ((valMap ζ _ hZ).hom.comp (GlobalTheory.QCoh.Qcqs.baseRingHom F _).hom) (algebraMap ℚ Ω)) c⟩ }
    have hS : Algebra.adjoin ℚ (R₁ ∪ R₂) ≤ S := by
      refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
      · intro w hw
        obtain ⟨s, rfl⟩ : w ∈ Set.range (valMap (ζ ≫ j ≫ pullback.fst f g) U hA).hom :=
          e₁.symm ▸ (Algebra.subset_adjoin hw : w ∈ (Algebra.adjoin ℚ R₁ : Set Ω))
        exact ⟨((j ≫ pullback.fst f g).appLE U _ inf_le_left).hom s,
          congrArg (fun φ => φ.hom s) (appLE_valMap ζ (j ≫ pullback.fst f g) inf_le_left hZ hA)⟩
      · intro w hw
        obtain ⟨s, rfl⟩ : w ∈ Set.range (valMap (ζ ≫ j ≫ pullback.snd f g) V hB).hom :=
          e₂.symm ▸ (Algebra.subset_adjoin hw : w ∈ (Algebra.adjoin ℚ R₂ : Set Ω))
        exact ⟨((j ≫ pullback.snd f g).appLE V _ inf_le_right).hom s,
          congrArg (fun φ => φ.hom s) (appLE_valMap ζ (j ≫ pullback.snd f g) inf_le_right hZ hB)⟩
    exact hS

theorem prod_chart (Ω : Type) [Field Ω] [CharZero Ω] (N r : ℕ) (Z : Scheme.{0})
    (j : Z ⟶ pullback (PSpace.str ℚ N) (PSpace.str ℚ r)) [IsClosedImmersion j] (ζ : Sp Ω ⟶ Z)
    (x : Fin (N + 1) → Ω) (hx : x ≠ 0) (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0)
    (h₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx) (h₂ : ζ ≫ j ≫ pullback.snd _ _ = point ℚ x' hx')
    (a : Fin (N + 1)) (l : Fin (r + 1)) (ha : x a ≠ 0) (hl : x' l ≠ 0) :
    IsAffineOpen ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) ∧
      ∃ h : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.fst _ _) ⁻¹ᵁ chart ℚ N a ⊓ (j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l),
        Set.range (valMap ζ _ h).hom =
          Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l)) :=
  closed_prod_chart _ _ j ζ _ _ h₁ h₂ (isAffineOpen_chart ℚ N a) (isAffineOpen_chart ℚ r l)
    ((le_point_preimage_iff a).2 ha) ((le_point_preimage_iff l).2 hl) _ _
    (range_valMap_point _) (range_valMap_point _)

end GlobalTheory.CompanionTheory.Ar.SncRes.ProdChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartLocalNormalForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartGeo

open Topology

theorem inFrameDomain_eventually {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (y : (Σ k, J k) → Ω) (cc : (k : K) → J k) (f : Ω) {z : (Σ k, J k) → ℂ} (hz : InFrameDomain y cc f z) :
    ∀ᶠ w in 𝓝 z, InFrameDomain y cc f w := by
  obtain ⟨hc, v, ⟨d, g, h, hg, hh, hy, hgh, hhz, rfl⟩, hv⟩ := hz
  have hgz : MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 := by
    intro h0
    apply hv
    rw [h0, zero_div]
  have c1 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hgz
  have c2 : ∀ᶠ w in 𝓝 z, MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) h) ≠ 0 :=
    (MvPolynomial.continuous_eval _).continuousAt.eventually_ne hhz
  have c3 : ∀ᶠ w : (Σ k, J k) → ℂ in 𝓝 z, ∀ k, w ⟨k, cc k⟩ ≠ 0 :=
    Filter.eventually_all.2 fun k => (continuous_apply _).continuousAt.eventually_ne (hc k)
  filter_upwards [c1, c2, c3] with w h1 h2 h3
  exact ⟨h3, _, ⟨d, g, h, hg, hh, hy, hgh, h2, rfl⟩, div_ne_zero h1 h2⟩

theorem exists_perm_prefix {n : ℕ} (A : Finset (Fin n)) :
    ∃ π : Equiv.Perm (Fin n), ∀ i, ((π i : Fin n) : ℕ) < A.card ↔ i ∈ A := by
  classical
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  let e : {x // x ∈ A} ≃ {j : Fin n // (j : ℕ) < A.card} :=
    A.equivFin.trans (Fin.castLEOrderIso hle).toEquiv
  refine ⟨e.extendSubtype, fun i => ⟨fun h => ?_, fun h => e.extendSubtype_mem i h⟩⟩
  by_contra hi
  exact e.extendSubtype_not_mem i hi h

theorem recentre_apply {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) (u : Fin n → ℂ) (i : Fin n) :
    HodgeMetric.recentre t₀ ρ π u i = t₀ i + (ρ : ℂ) * u (π i) := by
  simp [HodgeMetric.recentre]

theorem recentre_mem_ball {n : ℕ} {t₀ u : Fin n → ℂ} {ρ ε : ℝ} (hρ : 0 < ρ) (hε : ρ ≤ ε) (π : Equiv.Perm (Fin n))
    (hu : u ∈ Metric.ball (0 : Fin n → ℂ) 1) : HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball t₀ ε := by
  rw [mem_ball_iff_norm]
  refine lt_of_lt_of_le ?_ hε
  rw [pi_norm_lt_iff hρ]
  intro i
  have h1 : ‖u (π i)‖ < 1 :=
    lt_of_le_of_lt (norm_le_pi_norm u (π i)) (by simpa using hu)
  have h2 : (HodgeMetric.recentre t₀ ρ π u - t₀) i = (ρ : ℂ) * u (π i) := by
    simp [recentre_apply]
  rw [h2, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
  nlinarith

theorem exists_recentre_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] (y : (Σ k, J k) → Ω) (P : Ideal (MRing J)) (n : ℕ) (Bd : Set ((Σ k, J k) → ℂ)) (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) (cc : (k : K) → J k) (f : Ω), t₀ ∈ Metric.ball (0 : Fin n → ℂ) 1 → InFrameDomain y cc f (χ.γ t₀) → ∃ (a₀ : ℕ) (π : Equiv.Perm (Fin n)) (ρ₀ : ℝ), a₀ ≤ n ∧ 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ (∀ i : Fin n, (i : ℕ) < a₀ → ((π.symm i : Fin n) : ℕ) < χ.a ∧ t₀ (π.symm i) = 0) ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, HodgeMetric.recentre t₀ ρ π u ∈ Metric.ball (0 : Fin n → ℂ) 1 ∧ InFrameDomain y cc f (χ.γ (HodgeMetric.recentre t₀ ρ π u)) ∧ (χ.γ (HodgeMetric.recentre t₀ ρ π u) ∉ Bd ↔ u ∈ Flat.punct n a₀ 1) := by
  intro K _ J _ Ω _ y P n Bd χ t₀ cc f ht₀ hF
  classical
  let A : Finset (Fin n) := Finset.univ.filter (fun i => (i : ℕ) < χ.a ∧ t₀ i = 0)
  have hA : ∀ i, i ∈ A ↔ (i : ℕ) < χ.a ∧ t₀ i = 0 := fun i => by simp [A]
  obtain ⟨π, hπ⟩ := exists_perm_prefix A
  have hγ : ContinuousAt χ.γ t₀ := (χ.analytic t₀ ht₀).continuousAt
  have e1 : ∀ᶠ t in 𝓝 t₀, InFrameDomain y cc f (χ.γ t) :=
    hγ.eventually (inFrameDomain_eventually y cc f hF)
  have e2 : ∀ᶠ t : Fin n → ℂ in 𝓝 t₀, ∀ i : Fin n, t₀ i ≠ 0 → t i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases hi : t₀ i = 0
    · exact Filter.Eventually.of_forall fun t h => absurd hi h
    · filter_upwards [(continuous_apply i).continuousAt.eventually_ne hi] with t ht _ using ht
  have e3 : ∀ᶠ t in 𝓝 t₀, t ∈ Metric.ball (0 : Fin n → ℂ) 1 :=
    Metric.isOpen_ball.mem_nhds ht₀
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 (e1.and (e2.and e3))
  have hle : A.card ≤ n := by simpa using A.card_le_univ
  refine ⟨A.card, π, min ε 1, hle, lt_min hε one_pos, min_le_right _ _, fun i hi => ?_, fun ρ hρ hρ₀ u hu => ?_⟩
  · have : π.symm i ∈ A := (hπ _).1 (by simpa using hi)
    exact (hA _).1 this
  · obtain ⟨hF', hne, hb⟩ := hball _ (recentre_mem_ball hρ (hρ₀.trans (min_le_left _ _)) π hu)
    refine ⟨hb, hF', ?_⟩
    have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
    rw [χ.boundary _ hb]
    constructor
    · intro h
      refine ⟨by simpa using hu, fun j hj => fun h0 => h ?_⟩
      have hm : π.symm j ∈ A := (hπ _).1 (by simpa using hj)
      obtain ⟨h1, h2⟩ := (hA _).1 hm
      refine ⟨π.symm j, h1, ?_⟩
      rw [recentre_apply, h2]
      simp [h0]
    · rintro ⟨-, hu'⟩ ⟨i, hi, h0⟩
      by_cases hti : t₀ i = 0
      · have hm : i ∈ A := (hA i).2 ⟨hi, hti⟩
        have := hu' (π i) ((hπ i).2 hm)
        rw [recentre_apply, hti, zero_add] at h0
        exact (mul_ne_zero hρc this) h0
      · exact hne i hti h0

end GlobalTheory.CompanionTheory.Ar.ChartGeo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartOfSmoothCoords
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncRes

theorem exists_cover_basicOpen {Z : Scheme.{0}} {W : Z.Opens} (hW : IsAffineOpen W) {n : ℕ}
    (V : Fin n → Z.affineOpens) (hV : ∀ y : Z, ∃ j, y ∈ (V j : Z.Opens)) :
    ∃ (m : ℕ) (u c : Fin m → Γ(Z, W)), ∑ l, c l * u l = 1 ∧
      ∀ l, ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen (u l) = Z.basicOpen v := by
  classical
  let s : Set Γ(Z, W) :=
    {f | ∃ (j : Fin n) (v : Γ(Z, (V j : Z.Opens))), Z.basicOpen f = Z.basicOpen v}
  have hs : Ideal.span s = ⊤ := by
    rw [← hW.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨j, hj⟩ := hV x
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hW (V j).2 x ⟨hx, hj⟩
    exact Opens.mem_iSup.2 ⟨⟨f, j, g, e⟩, hxf⟩
  have h1 : (1 : Γ(Z, W)) ∈ Ideal.span s := hs ▸ Submodule.mem_top
  obtain ⟨c, hc, hsum⟩ := Submodule.mem_span_set.1 h1
  let e := c.support.equivFin.symm
  refine ⟨c.support.card, fun l => (e l : Γ(Z, W)), fun l => c (e l), ?_, fun l => hc (e l).2⟩
  rw [← hsum, Finsupp.sum, ← Finset.sum_coe_sort c.support]
  exact Equiv.sum_comp e fun x : c.support => c x * (x : Γ(Z, W))

theorem smooth_secAlgebra {Z : Scheme.{0}} (g : Z ⟶ Sp ℚ) (e : ℕ)
    (hsm : SmoothOfRelativeDimension e g) {D : Z.Opens} (hD : IsAffineOpen D) :
    @Algebra.Smooth ℚ _ Γ(Z, D) _ (secAlgebra g D) := by
  have h0 : Smooth g := hsm.smooth
  have h1 := Smooth.smooth_appLE (f := g) (isAffineOpen_top _) hD (fun _ _ => trivial)
  exact RingHom.Smooth.propertyIsLocal.respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).symm.commRingCatIsoToRingEquiv h1

theorem coords_of_formallyEtale {R S : Type} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    [Algebra R S] [IsScalarTower ℚ R S] [Algebra.FormallyEtale R S] {e : ℕ} (z : Fin e → R)
    (h1 : LinearIndependent R fun i => KaehlerDifferential.D ℚ R (z i))
    (h2 : Submodule.span R (Set.range fun i => KaehlerDifferential.D ℚ R (z i)) = ⊤) :
    LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = ⊤ := by
  let b := Module.Basis.mk h1 h2.ge
  let b' := (b.baseChange S).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℚ R S)
  have hb : (fun i => KaehlerDifferential.D ℚ S (algebraMap R S (z i))) = b' := by
    funext i
    simp [b', b, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply]
  rw [hb]
  exact ⟨b'.linearIndependent, b'.span_eq⟩

theorem exists_point_of_prime {Z : Scheme.{0}} {D : Z.Opens} (hD : IsAffineOpen D)
    (q : Ideal Γ(Z, D)) (hq : q.IsPrime) :
    ∃ t ∈ D, ∀ s : Γ(Z, D), s ∈ q ↔ t ∉ Z.basicOpen s := by
  refine ⟨hD.fromSpec ⟨q, hq⟩, hD.fromSpec_preimage_self.ge trivial, fun s => ?_⟩
  have h := hD.fromSpec_preimage_basicOpen s
  have h2 : (hD.fromSpec ⟨q, hq⟩ ∈ Z.basicOpen s) ↔ (⟨q, hq⟩ : PrimeSpectrum Γ(Z, D)) ∈ PrimeSpectrum.basicOpen s := by
    rw [← h]
    rfl
  rw [h2]
  simp

theorem range_valMap_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0) (D : Z.Opens)
    (hDu : D = Z.basicOpen u) :
    ∃ hD : ⊤ ≤ ζ ⁻¹ᵁ D, Set.range (valMap ζ D hD).hom =
      (Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω)) : Subalgebra ℚ Ω) := by
  subst hDu
  have hD : ⊤ ≤ ζ ⁻¹ᵁ Z.basicOpen u := (le_preimage_basicOpen_iff ζ h u).2 (isUnit_iff_ne_zero.2 hu)
  have hle : Z.basicOpen u ≤ W := Z.basicOpen_le u
  have hres : ∀ w : Γ(Z, W), (valMap ζ _ hD).hom ((Z.presheaf.map (homOfLE hle).op).hom w) = valR ζ W w :=
    fun w => by rw [← valR_eq _ _ hD, valR_res ζ hle hD]
  refine ⟨hD, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    have := hW.isLocalization_basicOpen u
    obtain ⟨k, a, ha⟩ := IsLocalization.Away.surj u x
    have h1 := congrArg (valMap ζ _ hD).hom ha
    rw [map_mul, map_pow] at h1
    have h2 : ∀ t : Γ(Z, W), (valMap ζ _ hD).hom (algebraMap Γ(Z, W) Γ(Z, Z.basicOpen u) t) = valR ζ W t :=
      hres
    rw [h2, h2] at h1
    have h3 : (valMap ζ _ hD).hom x = valR ζ W a * ((valR ζ W u)⁻¹) ^ k := by
      rw [← h1, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]
    have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ (A : Set Ω) := fun w => by
      rw [← hA, valR_eq _ _ h]; exact ⟨w, rfl⟩
    rw [h3]
    exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ (hv a)))
      (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) _)
  · intro x hx
    have hAr : ∀ a ∈ A, a ∈ Set.range (valMap ζ _ hD).hom := fun a ha => by
      have : a ∈ Set.range (valMap ζ W h).hom := by rw [hA]; exact ha
      obtain ⟨w, rfl⟩ := this
      exact ⟨_, (hres w).trans (valR_eq _ _ h _)⟩
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · have hunit : IsUnit ((Z.presheaf.map (homOfLE hle).op).hom u) :=
          RingedSpace.isUnit_res_basicOpen Z.toLocallyRingedSpace.toRingedSpace u
        obtain ⟨b, hb⟩ := hunit.exists_right_inv
        refine ⟨b, (inv_eq_of_mul_eq_one_right ?_).symm⟩
        rw [← hres u, ← map_mul, hb, map_one]
      · exact hAr x hx
    | algebraMap r => exact hAr _ (Subalgebra.algebraMap_mem _ r)
    | add x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add _ _ _⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a * b, map_mul _ _ _⟩

theorem snc_on_basicOpen {Ω : Type} [Field Ω] [CharZero Ω] {Z : Scheme.{0}} (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) {W : Z.Opens} (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W)
    (A : Subalgebra ℚ Ω) (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) (u : Γ(Z, W)) (hu : valR ζ W u ≠ 0)
    {V : Z.Opens} (hV : IsAffineOpen V) (v : Γ(Z, V)) (huv : Z.basicOpen u = Z.basicOpen v)
    (z : Fin e → Γ(Z, V)) (k : ℕ) (hk : k ≤ e) (hz : IsCoords g V z)
    (hT : (V : Set Z) ∩ T = {y | y ∈ V ∧ ∃ i : Fin e, (i : ℕ) < k ∧ y ∉ Z.basicOpen (z i)})
    (S : Subalgebra ℚ Ω) (hS : S = Algebra.adjoin ℚ (insert (valR ζ W u)⁻¹ (A : Set Ω))) :
    Algebra.Smooth ℚ S ∧ ∃ (z : Fin e → S) (n : ℕ), n ≤ e ∧
      LinearIndependent S (fun i => KaehlerDifferential.D ℚ S (z i)) ∧
      Submodule.span S (Set.range fun i => KaehlerDifferential.D ℚ S (z i)) = ⊤ ∧
      ∀ q : Ideal S, q.IsPrime →
        ((∀ s : S, (s : Ω) = valR ζ W σ → s ∈ q) ↔ ∃ i : Fin e, (i : ℕ) < n ∧ z i ∈ q) := by
  obtain ⟨hD, hr⟩ := range_valMap_basicOpen ζ hW h A hA u hu (Z.basicOpen v) huv.symm
  rw [← hS] at hr
  have hDaff : IsAffineOpen (Z.basicOpen v) := hV.basicOpen v
  have hDW : Z.basicOpen v ≤ W := huv ▸ Z.basicOpen_le u
  have hDV : Z.basicOpen v ≤ V := Z.basicOpen_le v
  letI iV := secAlgebra g V
  letI iD := secAlgebra g (Z.basicOpen v)
  let ψ := (valMap ζ (Z.basicOpen v) hD).hom
  have hψ : ∀ x, ψ x ∈ S := fun x => by
    have : ψ x ∈ Set.range ψ := ⟨x, rfl⟩
    rw [show Set.range ψ = (S : Set Ω) from hr] at this
    exact this
  let φ : Γ(Z, Z.basicOpen v) ≃+* S := RingEquiv.ofBijective (ψ.codRestrict S hψ) (by
    refine ⟨fun a b hab => valMap_injective ζ hD (congrArg Subtype.val hab), fun s => ?_⟩
    have hs : (s : Ω) ∈ Set.range ψ := by
      rw [show Set.range ψ = (S : Set Ω) from hr]
      exact s.2
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, Subtype.ext hx⟩)
  have hφ : ∀ x, (φ x : Ω) = ψ x := fun _ => rfl
  haveI hs0 : Algebra.Smooth ℚ Γ(Z, Z.basicOpen v) := smooth_secAlgebra g e hsm hDaff
  have hsmooth : Algebra.Smooth ℚ S := Algebra.Smooth.of_equiv φ.toRatAlgEquiv
  refine ⟨hsmooth, ?_⟩

  haveI := hV.isLocalization_basicOpen v
  haveI : Algebra.FormallyEtale Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers v)
  haveI : IsScalarTower ℚ Γ(Z, V) Γ(Z, Z.basicOpen v) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨c1, c2⟩ := coords_of_formallyEtale (R := Γ(Z, V)) (S := Γ(Z, Z.basicOpen v)) z hz.1 hz.2

  letI iS : Algebra Γ(Z, Z.basicOpen v) S := φ.toRingHom.toAlgebra
  haveI : Algebra.FormallyEtale Γ(Z, Z.basicOpen v) S :=
    Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := φ) fun _ => rfl)
  haveI : IsScalarTower ℚ Γ(Z, Z.basicOpen v) S :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  obtain ⟨d1, d2⟩ := coords_of_formallyEtale (R := Γ(Z, Z.basicOpen v)) (S := S) _ c1 c2
  refine ⟨_, k, hk, d1, d2, fun q hq => ?_⟩
  have hq' : (q.comap φ.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨t, htD, ht⟩ := exists_point_of_prime hDaff _ hq'
  have hmem : ∀ x, φ x ∈ q ↔ t ∉ Z.basicOpen x := ht
  have htV : t ∈ V := hDV htD
  have htW : t ∈ W := hDW htD
  have hzt : ∀ i, algebraMap Γ(Z, Z.basicOpen v) S (algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i)) ∈ q ↔
      t ∉ Z.basicOpen (z i) := fun i => by
    refine (hmem _).trans (not_congr ?_)
    have := Z.basicOpen_res (z i) (homOfLE hDV).op
    rw [show algebraMap Γ(Z, V) Γ(Z, Z.basicOpen v) (z i) =
      (Z.presheaf.map (homOfLE hDV).op).hom (z i) from rfl, this]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  let sσ : Γ(Z, Z.basicOpen v) := (Z.presheaf.map (homOfLE hDW).op).hom σ
  have hsσ : (φ sσ : Ω) = valR ζ W σ := by
    rw [hφ, ← valR_res ζ hDW hD σ, valR_eq _ _ hD]
  have hσt : φ sσ ∈ q ↔ t ∈ T := by
    refine (hmem _).trans ?_
    rw [hσ t htW, not_iff_not, Z.basicOpen_res σ (homOfLE hDW).op]
    exact ⟨fun h => h.2, fun h => ⟨htD, h⟩⟩
  have hTt : t ∈ T ↔ ∃ i : Fin e, (i : ℕ) < k ∧ t ∉ Z.basicOpen (z i) := by
    have h1 : t ∈ (V : Set Z) ∩ T ↔ t ∈ T := ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
    rw [← h1, hT]
    exact ⟨fun h => h.2, fun h => ⟨htV, h⟩⟩
  constructor
  · intro H
    obtain ⟨i, hi, hit⟩ := hTt.1 (hσt.1 (H _ hsσ))
    exact ⟨i, hi, (hzt i).2 hit⟩
  · rintro ⟨i, hi, hit⟩ s hs
    have : s = φ sσ := Subtype.ext (hs.trans hsσ.symm)
    rw [this]
    exact hσt.2 (hTt.2 ⟨i, hi, (hzt i).1 hit⟩)

theorem sncChart_of_coords (Ω : Type) [Field Ω] [CharZero Ω] (Z : Scheme.{0}) (ζ : Sp Ω ⟶ Z)
    [IsDominant ζ] [IsReduced Z] (g : Z ⟶ Sp ℚ) (e : ℕ) (T : Set Z)
    (hsm : SmoothOfRelativeDimension e g) (hc : HasSncCoords g e T) (W : Z.Opens)
    (hW : IsAffineOpen W) (h : ⊤ ≤ ζ ⁻¹ᵁ W) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ζ W h).hom = A) (σ : Γ(Z, W))
    (hσ : ∀ t ∈ W, t ∈ T ↔ t ∉ Z.basicOpen σ) : SncChart A e (valR ζ W σ) := by
  obtain ⟨n, V, hcov, hV⟩ := hc
  obtain ⟨m, u, c, hsum, hl⟩ := exists_cover_basicOpen hW V hcov
  have hv : ∀ w : Γ(Z, W), valR ζ W w ∈ A := fun w => by
    have : valR ζ W w ∈ Set.range (valMap ζ W h).hom := by
      rw [valR_eq _ _ h]
      exact ⟨w, rfl⟩
    rw [hA] at this
    exact this
  refine ⟨m, fun l => valR ζ W (u l), fun l => valR ζ W (c l), fun l => hv _, fun l => hv _, ?_,
    fun l hf S hS => ?_⟩
  · simp only [valR_eq _ _ h]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_mul, ← map_sum, hsum, map_one]
  · obtain ⟨j, v, huv⟩ := hl l
    obtain ⟨z, k, hk, hz, hT⟩ := hV j
    exact snc_on_basicOpen ζ g e T hsm hW h A hA σ hσ (u l) hf (V j).2 v huv z k hk hz hT S hS

end GlobalTheory.CompanionTheory.Ar.SncRes
end
end

