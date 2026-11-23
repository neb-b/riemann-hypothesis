module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0059
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac

theorem exists_frac_field {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {W : Scheme.{0}}
    {ξ : Spec (CommRingCat.of Ω) ⟶ W} {κ : Type} {x : κ → Ω} (h : CoordTie F ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ a : Ω, ∃ r ∈ Algebra.adjoin F (Set.range fun j => x j / x c),
      ∃ s ∈ Algebra.adjoin F (Set.range fun j => x j / x c), s ≠ 0 ∧ a * s = r := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover p₀
  obtain ⟨U, hU, hq⟩ := h.affine c hc.1
  have h0 : genPt ξ ∈ U := (hq _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(W, U), (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.germ U (genPt ξ) h0 r) ∈
      Algebra.adjoin F (Set.range fun j => x j / x c) := fun r => by
    rw [h.ring c hc.1]
    intro q hqc
    have hqU : q.1 ∈ U := (hq _).2 ⟨q.2, hqc⟩
    refine ⟨W.presheaf.germ U q.1 hqU r, ?_⟩
    show (Scheme.stalkClosedPointTo ξ).hom (W.presheaf.stalkSpecializes q.2 (W.presheaf.germ U q.1 hqU r)) = _
    congr 1
    exact W.presheaf.germ_stalkSpecializes_apply hqU q.2 r
  refine ⟨c, hc.1, fun a => ?_⟩
  obtain ⟨s, rfl⟩ := h.gen.bij.2 a
  letI := W.presheaf.algebra_section_stalk (⟨genPt ξ, h0⟩ : U)
  have hl := hU.isLocalization_stalk ⟨genPt ξ, h0⟩
  obtain ⟨⟨r, t⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨genPt ξ, h0⟩).asIdeal.primeCompl
    (S := W.presheaf.stalk (genPt ξ)) s
  refine ⟨_, key r, _, key t, ?_, ?_⟩
  · have := IsLocalization.map_units (W.presheaf.stalk (genPt ξ)) t
    exact (this.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  · exact (map_mul (Scheme.stalkClosedPointTo ξ).hom _ _).symm.trans (congrArg _ e)

theorem exists_clear {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {S : Set Ω} {b : Ω}
    (hb : b ∈ Algebra.adjoin F S) :
    ∃ d : o, d ≠ 0 ∧ ∃ g ∈ Algebra.adjoin o S, algebraMap o Ω d * b = g := by
  induction hb using Algebra.adjoin_induction with
  | mem y hy => exact ⟨1, one_ne_zero, y, Algebra.subset_adjoin hy, by simp⟩
  | algebraMap f =>
    obtain ⟨⟨n, d⟩, e⟩ := IsLocalization.surj (nonZeroDivisors o) f
    refine ⟨d, nonZeroDivisors.ne_zero d.2, algebraMap o Ω n, Subalgebra.algebraMap_mem _ n, ?_⟩
    rw [IsScalarTower.algebraMap_apply o F Ω n, IsScalarTower.algebraMap_apply o F Ω d, ← map_mul, ← e, mul_comm]
  | add u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, algebraMap o Ω d₂ * g₁ + algebraMap o Ω d₁ * g₂,
      add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) m₁) (mul_mem (Subalgebra.algebraMap_mem _ _) m₂), ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring
  | mul u v _ _ hu hv =>
    obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := hu
    obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := hv
    refine ⟨d₁ * d₂, mul_ne_zero h₁ h₂, g₁ * g₂, mul_mem m₁ m₂, ?_⟩
    rw [← e₁, ← e₂, map_mul]
    ring

theorem algebraMap_ne_zero {o F : Type} [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] {Ω : Type}
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] {d : o} (hd : d ≠ 0) : algebraMap o Ω d ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply o F Ω d]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective o F)).2 hd)

theorem chartRing_frac : ∀ (o F : Type) [CommRing o] [IsDomain o] [Field F] [Algebra o F] [IsFractionRing o F] (Ω : Type)
    [Field Ω] [Algebra o Ω] [Algebra F Ω] [IsScalarTower o F Ω] (W : Scheme.{0}) (ξ' : Sp Ω ⟶ W) (κ : Type) (t : κ → Ω),
    CoordTie F ξ' t → ∃ c₀, t c₀ ≠ 0 ∧ ∀ a : Ω, ∃ g ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀),
      ∃ h ∈ Algebra.adjoin o (Set.range fun j => t j / t c₀), h ≠ 0 ∧ a = g / h := by
  intro o F _ _ _ _ _ Ω _ _ _ _ W ξ' κ t hT
  obtain ⟨c, hc, hf⟩ := exists_frac_field hT
  refine ⟨c, hc, fun a => ?_⟩
  obtain ⟨r, hr, s, hs, hs0, e⟩ := hf a
  obtain ⟨d₁, h₁, g₁, m₁, e₁⟩ := exists_clear (o := o) hr
  obtain ⟨d₂, h₂, g₂, m₂, e₂⟩ := exists_clear (o := o) hs
  have n₁ := algebraMap_ne_zero (F := F) (Ω := Ω) h₁
  have n₂ := algebraMap_ne_zero (F := F) (Ω := Ω) h₂
  have hg₂ : g₂ ≠ 0 := e₂ ▸ mul_ne_zero n₂ hs0
  refine ⟨algebraMap o Ω d₂ * g₁, mul_mem (Subalgebra.algebraMap_mem _ _) m₁,
    algebraMap o Ω d₁ * g₂, mul_mem (Subalgebra.algebraMap_mem _ _) m₂, mul_ne_zero n₁ hg₂, ?_⟩
  rw [eq_div_iff (mul_ne_zero n₁ hg₂), ← e₁, ← e₂, ← e]
  ring

end GlobalTheory.CompanionTheory.Ar.SncBase.ChartFrac
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Reindex

theorem coordTie_one_block (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ)
    (x : Fin (N + 1) → Ω) (h : CoordTie ℤ ξ x) :
    CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) := by
  have he : Function.Surjective (fun c' : Unit → Fin (N + 1) => c' ()) :=
    fun j => ⟨fun _ => j, rfl⟩
  have hfun : (fun c' : (k : Unit) → (fun _ : Unit => Fin (N + 1)) k =>
      ∏ k, (fun p : (Σ _ : Unit, Fin (N + 1)) => x p.2) ⟨k, c' k⟩) =
      fun c' : Unit → Fin (N + 1) => x (c' ()) := by
    funext c'
    simp
  rw [hfun]
  have hc : ∀ (c : Unit → Fin (N + 1)) p,
      InChart ξ (fun c' : Unit → Fin (N + 1) => x (c' ())) c p ↔ InChart ξ x (c ()) p :=
    fun c p => and_congr Iff.rfl (he.forall (p := fun c' => x c' / x (c ()) ∈ regAt ξ p)).symm
  refine ⟨h.gen, fun p => ?_, fun c h0 => ?_, fun c h0 a => ?_⟩
  · obtain ⟨c, hp⟩ := h.cover p
    exact ⟨fun _ => c, (hc _ p).2 hp⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (c ()) h0
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun _ => (hc c _).symm)⟩
  · have hr : (Set.range fun j : Unit → Fin (N + 1) => x (j ()) / x (c ())) =
        Set.range fun j => x j / x (c ()) :=
      he.range_comp fun j => x j / x (c ())
    simpa only [hc, hr] using h.ring (c ()) h0 a

end GlobalTheory.CompanionTheory.Ar.SncBase.Reindex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominantWeightGapShift
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.WtShift

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem ent_sub_smul (lam nu : Wt Ψ N) (s : ℝ) (τ : Ψ) (i : ℕ) :
    ent (lam - s • nu) τ i = ent lam τ i - s * ent nu τ i := by
  simp only [ent]
  split_ifs <;> simp

theorem abs_ent_le (nu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent nu τ i| ≤ ‖nu‖ := by
  simp only [ent]
  split_ifs with h
  · rw [← Real.norm_eq_abs]
    exact (norm_le_pi_norm (nu τ) _).trans (norm_le_pi_norm nu τ)
  · simp

theorem dominant_of_step (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → ent mu τ (i + 1) ≤ ent mu τ i) : Dominant mu := by
  intro τ a b hab
  have key : ∀ k i, i + k < N → ent mu τ (i + k) ≤ ent mu τ i := by
    intro k
    induction k with
    | zero => intro i _; simp
    | succ k ih =>
      intro i hi
      exact (h τ (i + k) (by omega)).trans (ih i (by omega))
  have hab' : (a : ℕ) ≤ b := hab
  have hk := key ((b : ℕ) - a) a (by omega)
  rw [Nat.add_sub_cancel' hab'] at hk
  simpa [ent, a.2, b.2] using hk

theorem sub_small_dominant : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (nu : Wt Ψ N) (c₀ : ℝ), 1 ≤ j → j < N →
    0 < c₀ → ∃ θ₀ > (0 : ℝ), θ₀ ≤ 1 ∧ ∀ (lam : Wt Ψ N) (θ : ℝ), ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (∀ τ, θ ≤ gap j lam τ) →
      CompactGapsGE j c₀ lam → Dominant (lam - θ ^ 2 • nu) ∧ ‖lam - θ ^ 2 • nu‖ ≤ 2 ∧
        ∀ τ, θ / 2 ≤ gap j (lam - θ ^ 2 • nu) τ := by
  intro Ψ _ _ N j nu c₀ hj hjN hc₀
  have hM0 : 0 ≤ ‖nu‖ := norm_nonneg _
  refine ⟨min 1 (min (1 / (4 * (‖nu‖ + 1))) (c₀ / (2 * (‖nu‖ + 1)))), by positivity, min_le_left _ _, ?_⟩
  intro lam θ hlam hθ hθ₀ hgap hcg
  have hθ1 : θ ≤ 1 := hθ₀.trans (min_le_left _ _)
  have hA' : θ ≤ 1 / (4 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hB' : θ ≤ c₀ / (2 * (‖nu‖ + 1)) := hθ₀.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA := (le_div_iff₀ (by positivity)).1 hA'
  have hB := (le_div_iff₀ (by positivity)).1 hB'
  have hθM : θ * ‖nu‖ ≤ 1 / 4 := by nlinarith
  have hθM' : θ * ‖nu‖ ≤ c₀ / 2 := by nlinarith
  have hdiff : ∀ τ i i', ent nu τ i - ent nu τ i' ≤ 2 * ‖nu‖ := fun τ i i' => by
    have h1 := abs_le.1 (abs_ent_le nu τ i)
    have h2 := abs_le.1 (abs_ent_le nu τ i')
    linarith [h1.2, h2.1]
  have hsq : θ ^ 2 * (2 * ‖nu‖) ≤ θ / 2 := by nlinarith
  have hsq2 : θ ^ 2 * (2 * ‖nu‖) ≤ c₀ := by nlinarith
  refine ⟨dominant_of_step _ fun τ i hi => ?_, ?_, fun τ => ?_⟩
  · rw [ent_sub_smul, ent_sub_smul]
    have hd := mul_le_mul_of_nonneg_left (hdiff τ i (i + 1)) (sq_nonneg θ)
    by_cases hij : i + 1 = j
    · subst hij
      have hg := hgap τ
      simp only [gap, Nat.add_sub_cancel] at hg
      nlinarith
    · have hc := hcg τ i hi hij
      nlinarith
  · calc ‖lam - θ ^ 2 • nu‖ ≤ ‖lam‖ + ‖θ ^ 2 • nu‖ := norm_sub_le _ _
      _ = ‖lam‖ + θ ^ 2 * ‖nu‖ := by rw [norm_smul, Real.norm_of_nonneg (sq_nonneg θ)]
      _ ≤ 2 := by nlinarith
  · have hg := hgap τ
    have hd := mul_le_mul_of_nonneg_left (hdiff τ (j - 1) j) (sq_nonneg θ)
    simp only [gap] at hg ⊢
    rw [ent_sub_smul, ent_sub_smul]
    nlinarith

end GlobalTheory.CompanionTheory.Ar.WtShift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsModelVectorBundlesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_vector_bundles : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → ∃ (X' : Scheme.{0}) (Ω' : Type) (_ : Field Ω') (_ : Algebra Ω Ω') (ξ' : Spec (CommRingCat.of Ω') ⟶ X') (f : X' ⟶ X) (N : ℕ) (x' : Fin (N + 1) → Ω') (b : ∀ s, Fin (r s) → TensorProduct Ω Ω' E), CoordTie ℤ ξ' x' ∧ (∀ q : X', genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω Ω') ∧ Smooth f ∧ Function.Surjective f ∧ IsGenericFlag (Ω' := Ω') (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom V b 1 ∧ ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω Ω' E 1).toAddMonoidHom).IsFlagVBOn Set.univ (b s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_flagBundle | exact GlobalTheory.CompanionTheory.Ar.exists_flagBundle | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_flagBundle <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariantStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_place_weight_conj_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (t : (F →+* ℂ) → ℝ), OverInt y φ → ∃ u, IsPlaceWeight y φ t u ∧ ((∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → ∀ z : (Σ k, ι k) → ℂ, u (fun p => (starRingEnd ℂ) (z p)) = u z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_placeWeight | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_placeWeight | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_placeWeight <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffRatioRegular
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

theorem iotaMulti_ne_zero_of_linearIndependent {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {r : ℕ}
    {b : Fin r → V} (hb : LinearIndependent Ω b) : exteriorPower.ιMulti Ω r b ≠ 0 := by
  have h := (exteriorPower.ιMulti_family_linearIndependent_field (n := r) hb).ne_zero
    (Set.powersetCard.ofFinEmbEquiv (OrderIso.refl (Fin r)).toOrderEmbedding)
  intro h0
  apply h
  simpa [exteriorPower.ιMulti_family] using h0

theorem exists_unit_of_span_eq {Ω W : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (R : Subring Ω) {c m : W}
    (hm : m ≠ 0) (h : Submodule.span R {c} = Submodule.span R {m}) :
    ∃ u : Ω, u ≠ 0 ∧ u ∈ R ∧ u⁻¹ ∈ R ∧ c = u • m := by
  obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self (R := R) c)
  obtain ⟨v, hv⟩ := Submodule.mem_span_singleton.1 (h.symm ▸ Submodule.mem_span_singleton_self (R := R) m)
  have hu' : (u : Ω) • m = c := hu
  have hv' : (v : Ω) • c = m := hv
  have h1 : ((v : Ω) * u - 1) • m = 0 := by
    rw [sub_smul, mul_smul, hu', hv', one_smul, sub_self]
  have h2 : (v : Ω) * u = 1 := sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hm)
  have h3 : (u : Ω) ≠ 0 := right_ne_zero_of_mul_eq_one h2
  refine ⟨u, h3, u.2, ?_, hu'.symm⟩
  rw [inv_eq_of_mul_eq_one_left h2]
  exact v.2

theorem exists_coeff_regular_of_frames : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (b₁ : Fin p → V) (b₂ : Fin q → V), IsCoeffAt A B p q a b x 1 → A.IsFrameAt b₁ x → B.IsFrameAt b₂ x → ∃ α κ : Ω, a = α • exteriorPower.ιMulti Ω p b₁ ∧ b = κ • exteriorPower.ιMulti Ω q b₂ ∧ α / κ ∈ regAt ξ x := by
  intro X Ω _ ξ V _ _ A B p q a b x b₁ b₂ hc f₁ f₂
  obtain ⟨α₀, β₀, hα, hβ, hA, hB, h1⟩ := hc
  rw [one_mul] at h1
  subst h1
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₁] at hA
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₂] at hB
  obtain ⟨u, -, hu, -, hau⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₁.1) hA.symm
  obtain ⟨t, ht0, -, hti, hbt⟩ := exists_unit_of_span_eq (regAt ξ x)
    (iotaMulti_ne_zero_of_linearIndependent f₂.1) hB.symm
  refine ⟨u / α₀, t / α₀, ?_, ?_, ?_⟩
  · rw [div_eq_inv_mul, mul_smul, ← hau, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · rw [div_eq_inv_mul, mul_smul, ← hbt, smul_smul, inv_mul_cancel₀ hα, one_smul]
  · have : u / α₀ / (t / α₀) = u * t⁻¹ := by field_simp
    rw [this]
    exact mul_mem hu hti

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectorsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_borel_change_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S), Formalism.L2.Pj.FrBor t z z' → ∀ (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q), under y = spMap ψ ≫ z.x → (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → (∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm)) → (∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F), (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧ A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧ B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelStructureProperties
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem fullLevel_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) :=
  PositivityTheory.HtPt.Mg.level_props

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFibre

variable {Y P : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isIso_stalkMap_of_lift (f : Y ⟶ P) [Mono f] (y : Y)
    (t : Spec (P.presheaf.stalk (f y)) ⟶ Y) (ht : t ≫ f = P.fromSpecStalk (f y)) :
    IsIso (f.stalkMap y) := by
  have h0 : Spec.map (f.stalkMap y) ≫ P.fromSpecStalk (f y) = Y.fromSpecStalk y ≫ f :=
    Scheme.SpecMap_stalkMap_fromSpecStalk f
  have h1 : Spec.map (f.stalkMap y) ≫ t = Y.fromSpecStalk y := by
    rw [← cancel_mono f, Category.assoc, ht, h0]
  have hc : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) = y := by
    have e1 : Spec.map (f.stalkMap y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) =
        IsLocalRing.closedPoint (P.presheaf.stalk (f y)) := Spec_closedPoint
    have e2 : (Spec.map (f.stalkMap y) ≫ t) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y := by
      rw [h1]
      exact Scheme.fromSpecStalk_closedPoint
    rw [← e1]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2
  have hs : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) ⤳ y := by rw [hc]
  have h2 : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t) ≫ Y.fromSpecStalk y = t := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  generalize Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t = τ at h2
  refine ⟨τ, ?_, ?_⟩
  · apply Spec.map_injective
    rw [← cancel_mono (P.fromSpecStalk (f y)), Spec.map_comp, Category.assoc, h0, ← Category.assoc, h2, ht,
      Spec.map_id, Category.id_comp]
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk y), Spec.map_comp, Category.assoc, h2, h1, Spec.map_id, Category.id_comp]

theorem genMap_bijective {ζ : Spec (CommRingCat.of Ω) ⟶ P} (h : IsCptGen ζ) (p : Cpt ζ) (e : p.1 = genPt ζ) :
    Function.Bijective (genMap ζ p) := by
  obtain ⟨p, hp⟩ := p
  obtain rfl : p = genPt ζ := e
  have : P.presheaf.stalkSpecializes hp = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, this]
  exact h.bij

theorem isCptGen_of_isIso_stalkMap (f : Y ⟶ P) (hf : ∀ y, IsIso (f.stalkMap y))
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have hd : Dominates ξ (ξ ≫ f) f (RingHom.id Ω) := by
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ ≫ f
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  have hb : ∀ q, Function.Bijective (f.stalkMap q).hom := fun q =>
    have := hf q
    ConcreteCategory.bijective_of_isIso (f.stalkMap q)
  have hcl : ∀ (q : Cpt ξ), genPt (ξ ≫ f) ⤳ f q.1 := fun q =>
    RegAtDom.map_genPt hd ▸ q.2.map f.continuous
  have hcomp : ∀ (q : Cpt ξ), genMap ξ q ∘ (f.stalkMap q.1).hom = genMap (ξ ≫ f) ⟨f q.1, hcl q⟩ := fun q =>
    funext fun t => RegAtDom.genMap_stalkMap hd q.1 q.2 (hcl q) t
  have hself : genMap ξ ⟨genPt ξ, specializes_rfl⟩ = (Scheme.stalkClosedPointTo ξ).hom := by
    have : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    have e : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫ Scheme.stalkClosedPointTo ξ =
        Scheme.stalkClosedPointTo ξ := by
      rw [this]
      exact Category.id_comp _
    exact congrArg (fun g => g.hom) e
  refine ⟨?_, fun q => ?_⟩
  · have e := hcomp ⟨genPt ξ, specializes_rfl⟩
    have hB := genMap_bijective h ⟨f (genPt ξ), hcl ⟨genPt ξ, specializes_rfl⟩⟩ (RegAtDom.map_genPt hd)
    rw [← e] at hB
    rw [← hself]
    exact ⟨hB.1.of_comp_right (hb _).2, hB.2.of_comp⟩
  · have hi := h.inj ⟨f q.1, hcl q⟩
    rw [← hcomp q] at hi
    exact hi.of_comp_right (hb _).2

variable {F : Type} [Field F] [NumberField F]


omit [NumberField F] in
theorem injective_of_charZero [CharZero Ω] (φ : 𝓞 F →+* Ω) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem exists_lift_field {R : CommRingCat.{0}} [IsLocalRing R] (g : Spec R ⟶ Sp (𝓞 F)) (z : Sp F)
    (hz : g (IsLocalRing.closedPoint R) = spMap (algebraMap (𝓞 F) F) z) :
    ∃ v : Spec R ⟶ Sp F, v ≫ spMap (algebraMap (𝓞 F) F) = g := by
  have hg : Spec.map (Spec.preimage g) = g := Spec.map_preimage g
  generalize Spec.preimage g = c at hg
  subst hg
  have hu : ∀ a : nonZeroDivisors (𝓞 F), IsUnit (c.hom a) := by
    intro a
    by_contra hn
    have h1 : (a : 𝓞 F) ∈ (Spec.map c (IsLocalRing.closedPoint R)).asIdeal :=
      (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hz] at h1
    have h2 : algebraMap (𝓞 F) F a ∈ PrimeSpectrum.asIdeal z := h1
    have hp : (PrimeSpectrum.asIdeal z).IsPrime := PrimeSpectrum.isPrime _
    rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z), Ideal.mem_bot] at h2
    have h3 : (a : 𝓞 F) = 0 := IsFractionRing.injective (𝓞 F) F (h2.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero a.2 h3
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors (𝓞 F)) (S := F) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem isIso_stalkMap_fst (s : P ⟶ Sp (𝓞 F)) (y : ↑(pullback s (spMap (algebraMap (𝓞 F) F)))) :
    IsIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F)) := IsLocalization.epi (nonZeroDivisors (𝓞 F)) F
  have : Mono (spMap (algebraMap (𝓞 F) F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hz : (P.fromSpecStalk (pullback.fst s (spMap (algebraMap (𝓞 F) F)) y) ≫ s) (IsLocalRing.closedPoint _) =
      spMap (algebraMap (𝓞 F) F) (pullback.snd s (spMap (algebraMap (𝓞 F) F)) y) := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [Scheme.fromSpecStalk_closedPoint]
    have e : (pullback.fst s (spMap (algebraMap (𝓞 F) F)) ≫ s) y =
        (pullback.snd s (spMap (algebraMap (𝓞 F) F)) ≫ spMap (algebraMap (𝓞 F) F)) y := by
      rw [pullback.condition]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (e.trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨v, hv⟩ := exists_lift_field _ _ hz
  exact isIso_stalkMap_of_lift _ y (pullback.lift _ v hv.symm) (pullback.lift_fst _ _ _)

theorem exists_point : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  intro F _ _ P s Ω _ _ ξ₀ h
  have hφ : Spec.map (Spec.preimage (ξ₀ ≫ s)) = ξ₀ ≫ s := Spec.map_preimage _
  generalize Spec.preimage (ξ₀ ≫ s) = φ at hφ
  have hinj : Function.Injective φ.hom := injective_of_charZero φ.hom
  have hb : (CommRingCat.ofHom (algebraMap (𝓞 F) F)) ≫ CommRingCat.ofHom (IsFractionRing.lift hinj) = φ := by
    ext a
    simp
  have hw : ξ₀ ≫ s = spMap (IsFractionRing.lift hinj) ≫ spMap (algebraMap (𝓞 F) F) :=
    hφ.symm.trans ((congrArg Spec.map hb.symm).trans (Spec.map_comp _ _))
  refine ⟨IsFractionRing.lift hinj, pullback.lift ξ₀ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  apply isCptGen_of_isIso_stalkMap (pullback.fst _ _) (isIso_stalkMap_fst s)
  rwa [pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenFibre
end
end

