module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0008
public import Development.WeilBound.CoreStatements.CommonZeroEvaluation.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_existsUnique_equiv :
    ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E'] (M : LieModel G x E) (M' : LieModel G x E'), ∃! f : E ≃ₗ[R] E', ∀ e, M'.pt (f e) = M.pt e := by
  intro S G _ R _ x E E' _ _ _ _ M M'

  choose f hf using fun e => M'.onto (M.pt e) (M.tan e)
  choose g hg using fun e' => M.onto (M'.pt e') (M'.tan e')
  let φ : E ≃ₗ[R] E' :=
    { toFun := f
      invFun := g
      map_add' := fun e e' => M'.inj (by rw [M'.add, hf, hf, hf, M.add])
      map_smul' := fun c e => by
        show f (c • e) = c • f e
        apply M'.inj
        apply Over.OverMorphism.ext
        rw [M'.smul, hf, hf, M.smul]
      left_inv := fun e => M.inj (by rw [hg, hf])
      right_inv := fun e' => M'.inj (by rw [hf, hg]) }
  refine ⟨φ, fun e => hf e, fun ψ hψ => ?_⟩
  exact LinearEquiv.ext fun e => M'.inj ((hψ e).trans (hf e).symm)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem IsTanAt.comp_monHom {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {v : epsAt x ⟶ G} (hv : IsTanAt G x v) (f : G ⟶ G') [IsMonHom f] :
    IsTanAt G' x (v ≫ f) := by
  unfold IsTanAt at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, MonObj.one_comp]

theorem lieModel_exists_unique_diff :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (R : Type) [CommRing R]
      (x : Spec (CommRingCat.of R) ⟶ S) (E E' : Type) [AddCommGroup E] [Module R E] [AddCommGroup E']
      [Module R E'] (M : LieModel G x E) (M' : LieModel G' x E') (f : G ⟶ G') [IsMonHom f],
      ∃! A : E →ₗ[R] E', ∀ e, M'.pt (A e) = M.pt e ≫ f := by
  intro S G G' _ _ R _ x E E' _ _ _ _ M M' f _
  have hex : ∀ e, ∃ e', M'.pt e' = M.pt e ≫ f := fun e => M'.onto _ ((M.tan e).comp_monHom f)
  choose A hA using hex
  have hadd : ∀ e₁ e₂, A (e₁ + e₂) = A e₁ + A e₂ := fun e₁ e₂ => M'.inj (by
    rw [hA, M'.add, hA, hA, M.add, MonObj.mul_comp])
  have hsmul : ∀ (c : R) e, A (c • e) = c • A e := fun c e => M'.inj (by
    rw [hA]
    apply Over.OverMorphism.ext
    rw [M'.smul, hA, Over.comp_left, Over.comp_left, M.smul, Category.assoc])
  refine ⟨⟨⟨A, hadd⟩, hsmul⟩, fun e => hA e, ?_⟩
  intro B hB
  ext e
  exact M'.inj ((hB e).trans (hA e).symm)

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MaximalIdealMembershipOfLocalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maximal_ideal_membership_of_local : ∀ {K : Type} [Field K] (R : Subring K) [IsLocalRing R] (P : Ideal (integralClosure R K).toSubring), P.IsMaximal → ∀ (t : (integralClosure R K).toSubring), (t : K) ∈ R → (t ∈ P ↔ ¬ ((t : K) ≠ 0 ∧ (t : K)⁻¹ ∈ R)) := by
  first | exact @GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | exact GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem | (intros; apply GlobalTheory.CompanionTheory.IntegralClosureLocal.mem_maximal_iff_not_inv_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportionalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_of_iota_multi_proportional : ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (b e : Fin n → V) (t : Ω), LinearIndependent Ω e → t ≠ 0 → exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e → ∀ i, b i ∈ Submodule.span Ω (Set.range e) := by
  first | exact @GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | exact GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional | (intros; apply GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NumberFieldMapsLocalRingUniqueStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.number_field_maps_local_ring_unique : ∀ (K : Type) [Field K] [NumberField K] (B : Type) [CommRing B] [IsLocalRing B] (Ω : Type) [Field Ω] (π : B →+* Ω) (s t : K →+* B), π.comp s = π.comp t → s = t := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | exact GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq | (intros; apply GlobalTheory.CompanionTheory.Ggeo.TwoMaps.ringHom_eq_of_comp_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PolynomialFieldExtensionDegree
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.polynomial_field_extension_degree : ∀ (κ K L I : Type) [Field κ] [Field K] [Field L] [Algebra K L] (ψ : κ ≃+* K) (T : I → L), AlgebraicIndependent K T → ∃ φ : FractionRing (MvPolynomial I κ) →+* L, (∀ a, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.C a)) = algebraMap K L (ψ a)) ∧ (∀ i, φ (algebraMap (MvPolynomial I κ) _ (MvPolynomial.X i)) = T i) ∧ (letI := φ.toAlgebra; Module.finrank (FractionRing (MvPolynomial I κ)) L) = Module.finrank (IntermediateField.adjoin K (Set.range T)) L := by
  first | exact @ModelDimension.polynomial_fraction_field_degree | exact ModelDimension.polynomial_fraction_field_degree
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveElementPowersIndepStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_element_powers_indep : ∀ (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type) [CommRing A] [HopfAlgebra k A] [Coalgebra.IsCocomm k A] [Module.Finite k A] (f : A),
    Coalgebra.comul (R := k) f = f ⊗ₜ[k] (1 : A) + (1 : A) ⊗ₜ[k] f → f ≠ 0 →
    ∀ c : ℕ → k, ∑ i ∈ Finset.range p, c i • f ^ i = 0 → ∀ i < p, c i = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | exact GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive | (intros; apply GlobalTheory.CompanionTheory.HopfPrim.powers_indep_of_primitive <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIsLocalRingIsFractionRingStalk
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem genMap_germ_eq_stalk_closed {X : Scheme.{0}} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U)
    (hη : genPt ξ ∈ U) (r : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp r) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := U) hp p.2
  have h2 := congr(($h).hom r)
  have e : ∀ x, genMap ξ p x =
      (Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes p.2).hom x) := fun _ => rfl
  rw [e]
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem stalk_eq_germ_div_of_affine {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (b : X.presheaf.stalk x.1) :
    ∃ r t : Γ(X, U), b * X.presheaf.germ U x.1 x.2 t = X.presheaf.germ U x.1 x.2 r ∧
      IsUnit (X.presheaf.germ U x.1 x.2 t) := by
  have hl := hU.isLocalization_stalk x
  obtain ⟨⟨r, t⟩, hrt⟩ := IsLocalization.surj (hU.primeIdealOf x).asIdeal.primeCompl b
  exact ⟨r, t.1, hrt, IsLocalization.map_units (X.presheaf.stalk x.1)
    (M := (hU.primeIdealOf x).asIdeal.primeCompl) t⟩

theorem regAt_isLocalRing_isFractionRing_stalk :
    ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ →
      ∀ p : Cpt ξ, IsLocalRing (regAt ξ p) ∧ IsFractionRing (regAt ξ p) Ω ∧
        Nonempty (X.presheaf.stalk p.1 ≃+* regAt ξ p) := by
  intro X Ω _ ξ hξ p
  have hsurj : Function.Surjective (genMap ξ p).rangeRestrict := (genMap ξ p).rangeRestrict_surjective
  have hinj : Function.Injective (genMap ξ p).rangeRestrict := fun a b h =>
    hξ.inj p (congrArg Subtype.val h)
  have e : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
    RingEquiv.ofBijective (genMap ξ p).rangeRestrict ⟨hinj, hsurj⟩
  have hloc : IsLocalRing (regAt ξ p) :=
    IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict hsurj
  refine ⟨hloc, ?_, ⟨e⟩⟩
  apply IsFractionRing.of_field
  intro a
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := p.1) trivial
  have hη : genPt ξ ∈ U := p.2.mem_open U.2 hpU
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = a :=
    hξ.bij.2 a
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨_, X.presheaf.germ U p.1 hpU r, rfl⟩, ⟨_, X.presheaf.germ U p.1 hpU t, rfl⟩, ?_⟩
  show _ = genMap ξ p (X.presheaf.germ U p.1 hpU r) / genMap ξ p (X.presheaf.germ U p.1 hpU t)
  rw [genMap_germ_eq_stalk_closed ξ p U hpU hη, genMap_germ_eq_stalk_closed ξ p U hpU hη, eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SiegelLimitImagBound
section
open Filter Topology Matrix

namespace GlobalTheory.CompanionTheory.PeriodLimitSeq

open GlobalTheory.CompanionTheory.PeriodLimit

theorem int_seq_const (a : ℕ → ℤ) (L : ℂ) (h : Tendsto (fun m => (a m : ℂ)) atTop (𝓝 L)) :
    ∃ N : ℤ, L = N ∧ ∀ᶠ m in atTop, a m = N := by
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 h (1 / 2) (by norm_num)
  have key : ∀ m ≥ M, a m = a M := by
    intro m hm
    have h2 : dist (a m : ℂ) (a M : ℂ) < 1 := by
      calc dist (a m : ℂ) (a M : ℂ) ≤ dist (a m : ℂ) L + dist (a M : ℂ) L :=
            dist_triangle_right _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add (hM m hm) (hM M le_rfl)
        _ = 1 := by norm_num
    rw [Complex.dist_eq, ← Int.cast_sub, Complex.norm_intCast, ← Int.cast_abs] at h2
    have h3 : |a m - a M| < 1 := by exact_mod_cast h2
    exact sub_eq_zero.1 (Int.abs_lt_one_iff.1 h3)
  have hev : ∀ᶠ m in atTop, a m = a M := eventually_atTop.2 ⟨M, key⟩
  refine ⟨a M, ?_, hev⟩
  exact tendsto_nhds_unique h (tendsto_const_nhds.congr' (hev.mono fun m hm => by simp [hm]))

theorem mulVec_expand {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (A : Matrix (Fin g) (Fin g) ℂ)
    (t : ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((A + t • Bs.map (fun x : ℤ => (x : ℂ))) *ᵥ (fun k => (v k : ℂ))) k
      = (A *ᵥ (fun k => (v k : ℂ))) k + t * (((Bs *ᵥ v) k : ℤ) : ℂ) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib]
  push_cast
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem im_mulVec_lemma {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℤ) (k : Fin g) :
    ((M *ᵥ (fun k => (v k : ℂ))) k).im = ((M.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

theorem freq_ker {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ)
    (hσ : Tendsto σs atTop (𝓝 σ)) (ht : Tendsto (fun m => (t m).im) atTop atTop)
    (hτ : ∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ)))
    (hy : Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y))
    (v : Fin g → ℤ) (hv : ∃ᶠ m in atTop, vs m = v) :
    Bs *ᵥ v = 0 ∧ ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k := by
  have hyk : ∀ k, Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k)
      atTop (𝓝 (y k)) := fun k => tendsto_pi_nhds.1 hy k
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (v k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (v k : ℂ))) k)) := by
    intro k
    have hc : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (v k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc.tendsto σ).comp hσ
  have htpos : ∀ᶠ m in atTop, 0 < (t m).im := ht.eventually_gt_atTop 0
  have hid : ∀ m, vs m = v → ∀ k,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im + (t m).im * (((Bs *ᵥ v) k : ℤ) : ℝ) := by
    intro m hm k
    rw [Pi.add_apply, hm, hτ m, mulVec_expand]
    simp [Complex.mul_im]
  have hker : Bs *ᵥ v = 0 := by
    funext k
    have hf : Tendsto (fun m => ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im) atTop (𝓝 0) :=
      (((Complex.continuous_im.tendsto _).comp (hyk k)).sub
        ((Complex.continuous_im.tendsto _).comp (hσk k))).div_atTop ht
    have hfreq : ∃ᶠ m in atTop, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        - ((σs m *ᵥ (fun k => (v k : ℂ))) k).im) / (t m).im = (((Bs *ᵥ v) k : ℤ) : ℝ) := by
      refine (hv.and_eventually htpos).mono fun m hm => ?_
      rw [hid m hm.1 k, add_sub_cancel_left]
      exact mul_div_cancel_left₀ _ hm.2.ne'
    have h0 := tendsto_nhds_unique_of_frequently_eq hf tendsto_const_nhds hfreq
    show (Bs *ᵥ v) k = 0
    exact_mod_cast h0.symm
  refine ⟨hker, fun k => ?_⟩
  rw [← im_mulVec_lemma σ v k]
  have hfreq2 : ∃ᶠ m in atTop,
      (((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k).im
        = ((σs m *ᵥ (fun k => (v k : ℂ))) k).im := by
    refine hv.mono fun m hm => ?_
    rw [hid m hm k, hker]
    simp
  exact tendsto_nhds_unique_of_frequently_eq ((Complex.continuous_im.tendsto _).comp (hyk k))
    ((Complex.continuous_im.tendsto _).comp (hσk k)) hfreq2

private theorem cast_mulVec_lemma_2 {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) :
    Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ (fun k => (v k : ℝ)) = fun k => (((Bs *ᵥ v) k : ℤ) : ℝ) := by
  funext k
  simp [Matrix.mulVec, dotProduct]

theorem unique_value {g : ℕ} (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ)
    (c : ℝ) (hc : 0 < c) (y : Fin g → ℂ)
    (hpos : ∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 →
      c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v))
    (v v' : Fin g → ℤ) (hk : Bs *ᵥ v = 0) (hk' : Bs *ᵥ v' = 0)
    (hi : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v k : ℝ))) k)
    (hi' : ∀ k, (y k).im = ((σ.map Complex.im) *ᵥ (fun k => (v' k : ℝ))) k) : v = v' := by
  obtain ⟨w, hw⟩ : ∃ w : Fin g → ℝ, w = (fun k => (v k : ℝ)) - (fun k => (v' k : ℝ)) := ⟨_, rfl⟩
  have hBw : Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ w = 0 := by
    rw [hw, Matrix.mulVec_sub, cast_mulVec_lemma_2, cast_mulVec_lemma_2, hk, hk']
    funext k
    simp
  have hSw : (σ.map Complex.im) *ᵥ w = 0 := by
    funext k
    have e1 := hi k
    have e2 := hi' k
    rw [hw, Matrix.mulVec_sub, Pi.sub_apply, Pi.zero_apply, ← e1, ← e2, sub_self]
  have h1 := hpos w hBw
  rw [hSw, dotProduct_zero] at h1
  have h3 : 0 ≤ w ⬝ᵥ w := Finset.sum_nonneg fun i _ => mul_self_nonneg (w i)
  have h5 : w ⬝ᵥ w ≤ 0 := by
    by_contra hne
    have := mul_pos hc (not_le.1 hne)
    linarith
  have h4 : w = 0 := dotProduct_self_eq_zero.1 (le_antisymm h5 h3)
  funext k
  have h6 := congrFun h4 k
  rw [hw] at h6
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h6
  exact_mod_cast h6

theorem limit_seq : ∀ (g : ℕ) (Bs : Matrix (Fin g) (Fin g) ℤ) (σ : Matrix (Fin g) (Fin g) ℂ) (σs τs : ℕ → Matrix (Fin g) (Fin g) ℂ) (t : ℕ → ℂ) (c : ℝ) (us vs : ℕ → Fin g → ℤ) (y : Fin g → ℂ), 0 < c → Tendsto σs atTop (𝓝 σ) → Tendsto (fun m => (t m).im) atTop atTop → (∀ m, τs m = σs m + t m • Bs.map (fun x : ℤ => (x : ℂ))) → (∀ m, ((τs m).map Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) → (∀ v : Fin g → ℝ, Bs.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 → c * (v ⬝ᵥ v) ≤ v ⬝ᵥ ((σ.map Complex.im) *ᵥ v)) → Tendsto (fun m => (fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) atTop (𝓝 y) → ∃ u v : Fin g → ℤ, Bs *ᵥ v = 0 ∧ y = (fun k => (u k : ℂ)) + σ *ᵥ (fun k => (v k : ℂ)) ∧ ∀ᶠ m in atTop, us m = u ∧ vs m = v := by
  intro g Bs σ σs τs t c us vs y hc hσ ht hτ hpsd hposσ hy
  have huniq : ∀ w w' : Fin g → ℤ, (∃ᶠ m in atTop, vs m = w) → (∃ᶠ m in atTop, vs m = w') →
      w = w' := by
    intro w w' hw hw'
    obtain ⟨hk, hi⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w hw
    obtain ⟨hk', hi'⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy w' hw'
    exact unique_value Bs σ c hc y hposσ w w' hk hk' hi hi'
  have hS : Tendsto (fun m => ∑ k, ((((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ)) :
      Fin g → ℂ)) k).im ^ 2) atTop (𝓝 (∑ k, (y k).im ^ 2)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact ((Complex.continuous_im.tendsto _).comp (tendsto_pi_nhds.1 hy k)).pow 2
  have hbd : ∀ᶠ m in atTop,
      vs m ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2} := by
    filter_upwards [hS.eventually_lt_const (lt_add_one _)] with m hm
    have h1 := sq_mul_sum_sq_le ((τs m).map Complex.im) hc (hpsd m) (fun k => (vs m k : ℝ))
    simp only [im_period (τs m) (us m) (vs m)] at h1
    show ∑ k, (vs m k : ℝ) ^ 2 ≤ (∑ k, (y k).im ^ 2 + 1) / c ^ 2
    rw [le_div_iff₀ (pow_pos hc 2)]
    linarith
  have hfin := finite_sum_sq_le (g := g) ((∑ k, (y k).im ^ 2 + 1) / c ^ 2)
  have hall : ∀ᶠ m in atTop, ∀ w ∈ {w ∈ {w : Fin g → ℤ | ∑ k, (w k : ℝ) ^ 2 ≤
      (∑ k, (y k).im ^ 2 + 1) / c ^ 2} | ¬ ∃ᶠ n in atTop, vs n = w}, vs m ≠ w := by
    rw [Filter.eventually_all_finite (hfin.subset (Set.sep_subset _ _))]
    intro w hw
    exact Filter.not_frequently.1 hw.2
  have hev : ∀ᶠ m in atTop, ∃ᶠ n in atTop, vs n = vs m := by
    filter_upwards [hbd, hall] with m hm1 hm2
    by_contra hne
    exact hm2 (vs m) ⟨hm1, hne⟩ rfl
  obtain ⟨m0, hm0⟩ := hev.exists
  have hv_ev : ∀ᶠ m in atTop, vs m = vs m0 := by
    filter_upwards [hev] with m hm
    exact huniq _ _ hm hm0
  obtain ⟨hker, -⟩ := freq_ker Bs σ σs τs t us vs y hσ ht hτ hy (vs m0) hv_ev.frequently
  have hσk : ∀ k, Tendsto (fun m => (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
      (𝓝 ((σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have hc' : Continuous (fun M : Matrix (Fin g) (Fin g) ℂ => (M *ᵥ (fun k => (vs m0 k : ℂ))) k) :=
      (continuous_apply k).comp (continuous_id.matrix_mulVec continuous_const)
    exact (hc'.tendsto σ).comp hσ
  have hu : ∀ k, Tendsto (fun m => (us m k : ℂ)) atTop
      (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) := by
    intro k
    have h1 : Tendsto (fun m => ((fun k => (us m k : ℂ)) + τs m *ᵥ (fun k => (vs m k : ℂ))) k
        - (σs m *ᵥ (fun k => (vs m0 k : ℂ))) k) atTop
        (𝓝 (y k - (σ *ᵥ (fun k => (vs m0 k : ℂ))) k)) :=
      (tendsto_pi_nhds.1 hy k).sub (hσk k)
    refine h1.congr' ?_
    filter_upwards [hv_ev] with m hm
    rw [Pi.add_apply, hm, hτ m, mulVec_expand, hker]
    simp
  choose u hu1 hu2 using fun k => int_seq_const (fun m => us m k) _ (hu k)
  refine ⟨u, vs m0, hker, ?_, ?_⟩
  · funext k
    simp only [Pi.add_apply]
    rw [← hu1 k]
    ring
  · have hall2 : ∀ᶠ m in atTop, ∀ k, us m k = u k := Filter.eventually_all.2 hu2
    filter_upwards [hall2, hv_ev] with m h1 h2
    exact ⟨funext h1, h2⟩

end GlobalTheory.CompanionTheory.PeriodLimitSeq
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothMapLocalizationCompatStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_map_localization_compat : ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀] [CharZero Ω] [Algebra Ω₀ Ω] (A₀ : Subalgebra ℤ Ω₀)
    (A₁ : Subalgebra ℤ Ω) (φ : A₀ →+* A₁), (∀ a, ((φ a : A₁) : Ω) = algebraMap Ω₀ Ω a) → φ.Smooth →
    ∀ h : Ω₀, h ∈ Algebra.adjoin ℚ (A₀ : Set Ω₀) → h ≠ 0 → ∀ (S : Subalgebra ℚ Ω₀) (T : Subalgebra ℚ Ω),
      S = Algebra.adjoin ℚ (insert h⁻¹ (A₀ : Set Ω₀)) →
      T = Algebra.adjoin ℚ (insert (algebraMap Ω₀ Ω h)⁻¹ (A₁ : Set Ω)) →
      ∃ ψ : S →+* T, (∀ s, ((ψ s : T) : Ω) = algebraMap Ω₀ Ω s) ∧ ψ.Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | exact GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised | (intros; apply GlobalTheory.CompanionTheory.Ar.LocalisedSmooth.smooth_localised <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StdSmoothMvPolynomial
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieInh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

theorem stdSmooth_mvPolynomial (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  have hker : (Algebra.Generators.mvPolynomial R (Fin n)).ker = ⊥ := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val, Algebra.Generators.mvPolynomial_val]
    exact (RingHom.injective_iff_ker_eq_bot _).1 fun a b h => by
      simpa only [MvPolynomial.aeval_X_left_apply] using h
  let P : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨Algebra.Generators.mvPolynomial R (Fin n), Empty.elim, by rw [hker]; simp⟩
  let P' : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P, Empty.elim, fun a => a.elim⟩
  let P'' : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    ⟨P', by
      rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
      exact isUnit_one⟩
  refine Algebra.IsStandardSmoothOfRelativeDimension.mk ⟨Fin n, Empty, inferInstance, inferInstance, P'', ?_⟩
  simp [Algebra.Presentation.dimension]

variable {X : Scheme.{0}}

variable {R : Type} [CommRing R] (x : Spec (CommRingCat.of R) ⟶ X)

end GlobalTheory.CompanionTheory.Ar.LieInh

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ZmodTorsorBaseChangeTransportPoint
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ar

theorem unitAt_iff_of_isCptGen {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) (a : Ω) :
    unitAt ξ p a ↔ ∃ u, IsUnit u ∧ genMap ξ p u = a := by
  constructor
  · rintro ⟨h0, ⟨u, rfl⟩, ⟨v, hv⟩⟩
    refine ⟨u, IsUnit.of_mul_eq_one v (h.inj p ?_), rfl⟩
    rw [map_mul, hv, map_one, mul_inv_cancel₀ h0]
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    refine ⟨(w.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨(w⁻¹ : _ˣ), ?_⟩⟩
    exact map_units_inv _ w

end GlobalTheory.CompanionTheory.Ar
end

