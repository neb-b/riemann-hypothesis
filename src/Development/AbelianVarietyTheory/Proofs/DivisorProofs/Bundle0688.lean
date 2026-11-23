module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0672
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0670
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0096

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfIsProperOfIsHomId
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH

namespace GlobalTheory

theorem exists_lift_of_isProper_of_isHom_id :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y M : RatModel o Ω) (q : Y.Z ⟶ M.Z),
      M.IsHom Y (AlgHom.id o Ω) q → IsProper q → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z),
        ∃ y' : Sp (OO p) ⟶ Y.Z, y' ≫ q = y := by
  intro o Ω _ _ _ Y M q hq hp p _ y
  have hq' : Y.pt ≫ q = spMap (AlgHom.id o Ω).toRingHom ≫ M.pt := by
    first | exact hq | exact hq.1 | exact hq.2
  have hsurj : Function.Surjective q := by
    have hc : IsClosed (Set.range q) := q.isClosedMap.isClosed_range
    have hg : genericPoint M.Z ∈ Set.range q := by
      have w : Sp Ω := IsLocalRing.closedPoint Ω
      refine ⟨Y.pt w, ?_⟩
      have h1 : (Y.pt ≫ q) w = (spMap (AlgHom.id o Ω).toRingHom ≫ M.pt) w := by rw [hq']
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, M.pt_apply] at h1
      exact h1
    intro z
    exact (genericPoint_specializes z).mem_closed hc hg
  obtain ⟨K', _, σ, y₁, hσ, hy₁⟩ := exists_finite_ext_point_lift_of_surjective_lft q inferInstance hsurj
    (PadicAlgCl p) (gPt p ≫ y)
  have hbij : Function.Bijective σ := by
    letI := σ.toAlgebra
    haveI : Module.Finite (PadicAlgCl p) K' := hσ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := PadicAlgCl p) (K := K')
  let e := RingEquiv.ofBijective σ hbij
  have he : e.symm.toRingHom.comp σ = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have h2 : (spMap e.symm.toRingHom ≫ y₁) ≫ q = gPt p ≫ y := by
    rw [Category.assoc, hy₁, ← Category.assoc, ← ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp, he]
    have : spMap (RingHom.id (PadicAlgCl p)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  have hE : ValuativeCriterion.Existence q :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed q) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) q).1
  obtain ⟨⟨l⟩⟩ := hE
    { R := OO p, K := PadicAlgCl p, i₁ := spMap e.symm.toRingHom ≫ y₁, i₂ := y, commSq := ⟨h2⟩ }
  exact ⟨l.l, l.fac_right⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdPoly
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace GlobalTheory

theorem exists_pdPoly : ∀ (B : Type) [CommRing B], Nonempty (PDPoly B) :=
  fun B _ ↦ ⟨stdPoly B⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRed
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hs : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  first
  | exact @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | (apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step ..)

theorem exists_limit_of_steps {R σ : Type} [CommRing R] (F : ℕ → MvPowerSeries σ R)
    (hF : ∀ n (α : σ →₀ ℕ), α.degree ≠ n + 2 → coeff α (F (n + 1)) = coeff α (F n)) :
    ∃ f : MvPowerSeries σ R, ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → coeff α f = coeff α (F n) := by
  have stab : ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → ∀ m, n ≤ m →
      coeff α (F m) = coeff α (F n) := by
    intro n α hα m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hF m α (by omega), ih]
  refine ⟨fun α => coeff α (F α.degree), fun n α hα => ?_⟩
  change coeff α (F α.degree) = _
  rw [← stab α.degree α (by omega) (max n α.degree) (le_max_right _ _),
    stab n α hα _ (le_max_left _ _)]

theorem exists_quasiLog_red (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) :
    ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h,
      Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  intro c hc w
  obtain ⟨f₀, hf₀, hw, hb⟩ := _root_.GlobalTheory.WittStart.start p k d μ h c hc w
  have hq₀ : f₀ ∈ quasiInt p k (Fin d) := by
    intro α i
    obtain ⟨v, hv⟩ := hf₀ α
    exact ⟨(α i : WittVector p k) * (1 * v), by rw [hv, map_mul _ (α i : WittVector p k), map_natCast]⟩
  obtain ⟨F, hF0, hF⟩ := exists_seq_of_step
    (fun n (f : MvPowerSeries (Fin d) (Fr p k)) => f ∈ quasiInt p k (Fin d) ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < n + 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w))
    (fun n a b => ∀ α : Fin d →₀ ℕ, α.degree ≠ n + 2 → coeff α b = coeff α a) f₀ ⟨hq₀, hb⟩
    (by
      intro n a ha
      obtain ⟨g, hg0, hg1, hg2⟩ := _root_.GlobalTheory.Katz.quasiLog_approx_step p k d μ h c hc (n + 2) a (by omega) ha.1 ha.2
      exact ⟨a - g, ⟨hg1, hg2⟩, fun α hα => by rw [map_sub, hg0 α hα, sub_zero]⟩)
  obtain ⟨f, hf⟩ := exists_limit_of_steps F fun n => (hF n).2
  have hq : f ∈ quasiInt p k (Fin d) := by
    intro α i
    rw [hf α.degree α (by omega)]
    exact (hF α.degree).1.1 α i
  have hp : cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c ∈ intBy p k (Fin d ⊕ Fin d) p := by
    intro γ
    obtain ⟨v, hv⟩ := (hF γ.degree).1.2 γ (by omega)
    refine ⟨v, ?_⟩
    have h1 := ((_root_.GlobalTheory.CobLead.cob_eq_additive_lead (Fr p k) d (fun i => Katz.lift p (μ i)) (γ.degree + 2)
      (fun i α hα => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ h i α hα).2)).1 (f - F γ.degree)
      (fun α hα => by rw [map_sub, hf _ α hα, sub_self]) γ).1 (by omega)
    have h2 := formalCoboundary_add (fun i => constantCoeff_lift p (h.const i)) (f - F γ.degree) (F γ.degree)
    rw [sub_add_cancel] at h2
    rw [h2, add_sub_assoc, map_add (f := _), h1, zero_add, hv]
  obtain ⟨r1, -, r3, r4, -, r6, -⟩ := _root_.GlobalTheory.Katz.red_rules p k (Fin d ⊕ Fin d)
  have hred : Red p (cob1 (fun i => Katz.lift p (μ i)) f) c := by
    have := (r4 _ _ _ _ ((r6 _).1 hp) (r3 c)).1
    rwa [sub_add_cancel, zero_add] at this
  refine ⟨f, ⟨hq, (r1 _).2 ⟨c, hred⟩⟩, hred, ?_⟩
  have hl : lin f = lin f₀ := by
    funext i
    unfold lin
    rw [hf 0 _ (by simp), hF0]
  rw [hl]
  exact hw

end Katz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftSmoothNilpotentThickening
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift

theorem exists_section_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  refine _root_.GlobalTheory.SecLift.lift_of_nilpotent_of_sqZero ?_
  intro R R₀ _ _ π hπ hsq X X₀ i hpb hsm e₀ he₀
  have hnil : IsNilpotent (RingHom.ker π) := ⟨2, by rw [hsq]; rfl⟩
  let g₀ := e₀ ≫ i
  have hg₀ : g₀ ≫ X.hom = spMap π := by
    simp only [g₀, Category.assoc]; rw [hpb.w, ← Category.assoc, he₀, Category.id_comp]
  let J : Set R := {h | ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ h V}
  have hS2 := _root_.GlobalTheory.SecLift.exists_liftIn R R₀ π hπ hnil X hsm g₀ hg₀
  have hspan : Ideal.span J = ⊤ := by
    by_contra hne
    obtain ⟨N, hN, hJN⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨f, hf, hfJ⟩ := hS2 ⟨N, hN.isPrime⟩
    exact hf (hJN (Ideal.subset_span hfJ))
  obtain ⟨s, hsJ, hs⟩ := (Ideal.span_eq_top_iff_finite J).1 hspan
  have hV : ∀ k : s, ∃ V : X.left.Opens, IsAffineOpen V ∧ LiftIn π X g₀ k.1 V := fun k => hsJ k.2
  choose V hVa hVl using hV
  obtain ⟨e, he1, he2⟩ :=
    _root_.GlobalTheory.SecGlue.exists_lift_of_chart_lifts R R₀ π hπ hsq X hsm g₀ hg₀ s (fun k => k.1) (by simpa using hs) V hVa hVl
  exact ⟨e, he1, he2.symm⟩

end GlobalTheory.SecLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom
section
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory.AnPer.SliceTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

theorem analyticAt_shift (q : (I ⊕ Fin g → ℂ) × (Fin g → ℂ)) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      (((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) q := by
  have h1 : ∀ j, AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦ y.1 j) q := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ⊕ Fin g ↦ ℂ) j).comp
      (ContinuousLinearMap.fst ℂ (I ⊕ Fin g → ℂ) (Fin g → ℂ))).analyticAt q
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ h1 _) ?_
  exact analyticAt_snd.add (analyticAt_pi_iff.2 fun i ↦ h1 _)

theorem analyticAt_joint {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      h.fn ((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b))) (0, w) := by
  refine AnalyticAt.comp_of_eq (h.analytic _ hw) (analyticAt_shift _) ?_
  ext <;> simp

theorem analyticAt_slice {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h.fn ((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b))) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ (x, w)) (analyticAt_joint h hw)
    (analyticAt_id.prod analyticAt_const) rfl

theorem eventually_mem {W : Opens ((I → ℂ) × (Fin g → ℂ))} {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0,
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ)) ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) := by
    fun_prop
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  have e : (((fun i ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inl i)), w + fun b ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inr b)) :
      (I → ℂ) × (Fin g → ℂ)) = (0, w) := by
    ext <;> simp
  change _ ∈ W
  simp only [e]
  exact hw

end GlobalTheory.AnPer.SliceTaylor


open GlobalTheory.AnPer.SliceTaylor in
theorem GlobalTheory.AnPer.exists_sliceTaylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  intro I _ _ g D _ _ N t ht E _ _ _ W W₀ a ha hW
  have key : ∀ h : Hol W, ∃ r : D ⊗[ℂ] Hol W₀, ∀ (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) r = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
    intro h
    have han : ∀ (k : ℕ) (v : Fin k → (I ⊕ Fin g → ℂ)), AnalyticOnNhd ℂ (fun p ↦ iteratedFDeriv ℂ k
        (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) 0 v) W₀ :=
      fun k v p hp ↦
        AnalyticAt.comp_of_eq (_root_.GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv _ (a p) k v (analyticAt_joint h (hW p hp))).1 (ha p hp) rfl
    unfold GlobalTheory.PeriodFamily.taylor
    refine ⟨∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I ⊕ Fin g,
      ((k.factorial : ℂ)⁻¹ • ∏ b, t (s b)) ⊗ₜ[ℂ] Hol.mk _ (han k fun b ↦ Pi.single (s b) 1), fun p hp ↦ ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, Hol.fn_mk _ _ hp,
      AlgHom.id_apply, Algebra.ofId_apply, mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]
  choose r hr using key
  obtain ⟨hadd, -, hconst, hcongr, -, -⟩ := _root_.GlobalTheory.PeriodFamily.taylor_formal_properties N t
  have hc : ∀ c : ℂ, r (algebraMap ℂ _ c) = algebraMap ℂ _ c := fun c ↦ by
    refine _root_.GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [hr, AlgHom.commutes, ← hconst c]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_algebraMap c hx
  have hA : ∀ f h : Hol W, r (f + h) = r f + r h := fun f h ↦ by
    refine _root_.GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_add (f := _), hr, hr, hr, ← hadd _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_add f h hx
  have hM : ∀ f h : Hol W, r (f * h) = r f * r h := fun f h ↦ by
    refine _root_.GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_mul, hr, hr, hr,
      ← _root_.GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_mul f h hx
  exact ⟨{ toFun := r
           map_one' := by simpa only [map_one] using hc 1
           map_mul' := hM
           map_zero' := by simpa using hc 0
           map_add' := hA
           commutes' := hc }, hr⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMapStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_chart_pair_along_linear_map : ∀ {I₁ : Type} [Fintype I₁] {g₁ : ℕ} {Λ₁ : Type} [AddCommGroup Λ₁] {F₁ : Fam I₁ g₁ Λ₁} {B₁ : Type} [CommRing B₁] {X₁ : Scheme.{0}} {s₁ : X₁ ⟶ Sp B₁} {σ₁ : B₁ →+* Hol F₁.V} {I₂ : Type} [Fintype I₂] {g₂ : ℕ} {Λ₂ : Type} [AddCommGroup Λ₂] {F₂ : Fam I₂ g₂ Λ₂} {B₂ : Type} [CommRing B₂] {X₂ : Scheme.{0}} {s₂ : X₂ ⟶ Sp B₂} {σ₂ : B₂ →+* Hol F₂.V} (u₁ : Unif F₁ s₁ σ₁) (u₂ : Unif F₂ s₂ σ₂) (b : (I₁ → ℂ) → I₂ → ℂ) (hb : AnalyticOnNhd ℂ b F₁.V) (hbV : ∀ z ∈ F₁.V, b z ∈ F₂.V) (M : (Fin g₁ → ℂ) →ₗ[ℂ] (Fin g₂ → ℂ)) (A : Λ₁ →+ Λ₂), (∀ l, ∀ z ∈ F₁.V, F₂.τ (A l) (b z) = M (F₁.τ l z)) → ∃ (K₁ : Charts F₁) (K₂ : Charts F₂) (κ : K₁.K → K₂.K), K₁.Rich ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₁.W k, ⊤ ≤ u₁.E p ⁻¹ᵁ U) ∧ (∀ k, ∃ U, IsAffineOpen U ∧ ∀ p ∈ K₂.W k, ⊤ ≤ u₂.E p ⁻¹ᵁ U) ∧ (∀ k, ∀ p ∈ K₁.W k, ((b p.1, M p.2) : Tot I₂ g₂) ∈ K₂.W (κ k)) ∧ ∀ l k' k, K₁.le l k' k → K₂.le (A l) (κ k') (κ k) := by
  first | exact @GlobalTheory.AnPer.ChartPair.exists_pair | exact GlobalTheory.AnPer.ChartPair.exists_pair | (intros; apply GlobalTheory.AnPer.ChartPair.exists_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquareZeroMoveTensorHolomorphicStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_squareZero_move_tensor_holomorphic :
    ∀ {g : ℕ} {W₀ : Opens (Tot Empty g)} {R : Type} [CommRing R] [Algebra ℂ R]
      {C : Type} [CommRing C] (ψ : R ⊗[ℂ] Hol W₀ →+* C) (n : Fin g → C),
      (∀ a b, n a * n b = 0) → ∃ ψ' : R ⊗[ℂ] Hol W₀ →+* C,
        ∀ x, ψ' x = ψ x + ∑ a, ψ (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap x) * n a := by
  intro g W₀ R _ _ C _ ψ n hn
  have hMove := GlobalTheory.SqZeroMove.gen_hom ψ
    (fun a => (LinearMap.lTensor R (dw (W := W₀) a).toLinearMap).toAddMonoidHom)
    (fun a => GlobalTheory.SqZeroMove.lTensor_one (R := R) (dw (W := W₀) a))
    (fun a x y => GlobalTheory.SqZeroMove.lTensor_leibniz (dw (W := W₀) a) x y) n hn
  exact hMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentOfUniformisationJet
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem exists_tangent_of_jet : ∀ {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g), A.left.IsSeparated → ∀ (W : Opens (Tot Empty g)) (x : Sp (Hol W) ⟶ A.left), (∀ (p : Tot Empty g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = (u.ex p.2).left) → x ≫ A.hom = spMap (algebraMap ℂ (Hol W)) → (0 : Tot Empty g) ∈ W → ∀ (w : Fin g → ℂ) (ρ : Hol W →ₐ[ℂ] DualNumber ℂ), (∀ h, (ρ h).fst = h.fn 0 ∧ (ρ h).snd = fderiv ℂ h.fn 0 (0, w)) → ∃ v : epsR ℂ ⟶ A, v.left = spMap ρ.toRingHom ≫ x ∧ IsTangent v ∧ u.IsDiff w v := by
  intro A _ L g u hsep W x hx hxA h0 w ρ hρ
  have hw : (spMap ρ.toRingHom ≫ x) ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
    rw [Category.assoc, hxA, ← Cris.spMap_comp]
    congr 1
    exact RingHom.ext fun c ↦ ρ.commutes c
  have hfst : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = (u.ex 0).left := by
    have e : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom.comp ρ.toRingHom = (Hol.ev 0 h0).toRingHom :=
      RingHom.ext fun f ↦ (hρ f).1.trans (Hol.ev_apply 0 h0 f).symm
    rw [← Category.assoc, ← Cris.spMap_comp, e]
    exact hx 0 h0
  refine ⟨Over.homMk (spMap ρ.toRingHom ≫ x) hw, rfl, ?_, ?_⟩
  · change spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ.toRingHom ≫ x = _
    rw [hfst, (u.ker 0).2 u.Λ.zero_mem, Hom.one_def, toUnit_unit, Category.id_comp]
  · intro U h f
    change ⊤ ≤ (spMap ρ.toRingHom ≫ x) ⁻¹ᵁ U at h
    change (evalAt (spMap ρ.toRingHom ≫ x) U h f).snd = _
    have hU0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U := by
      rw [← hfst]
      exact fun q _ ↦ h (Set.mem_univ ((spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) q))
    let q₀ : Sp ℂ := (default : PrimeSpectrum ℂ)
    obtain ⟨U', hU', hq, hle⟩ := exists_isAffineOpen_mem_and_subset
      (x := (u.ex 0).left q₀) (U := U) (hU0 (Set.mem_univ q₀))
    have hU0' : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U' := fun q _ ↦ by
      have : q = q₀ := Subsingleton.elim (α := PrimeSpectrum ℂ) q q₀
      subst this
      exact hq
    let W' : Opens (Tot Empty g) :=
      W ⊓ ⟨{p | ⊤ ≤ (u.ex p.2).left ⁻¹ᵁ U'}, (u.hol U' 0).1.preimage continuous_snd⟩
    have h0' : (0 : Tot Empty g) ∈ W' := ⟨h0, hU0'⟩
    obtain ⟨x', hx'U, hx'⟩ := exists_pt_of_affine (fibUnif u) W' (fun _ _ ↦ trivial) U' hU' (fun p hp ↦ hp.2)
    let res : Hol W →ₐ[ℂ] Hol W' := Hol.comap id analyticOnNhd_id fun p hp ↦ hp.1
    have hres : ∀ (k : Hol W), ∀ p ∈ W', (res k).fn p = k.fn p := fun k p hp ↦ Hol.fn_comap _ _ _ k hp
    have hxx : spMap res.toRingHom ≫ x = x' := by
      refine point_hol_ext_of_isSeparated W' hsep _ _ fun p hp ↦ ?_
      have e : (Hol.ev p hp).toRingHom.comp res.toRingHom = (Hol.ev p hp.1).toRingHom :=
        RingHom.ext fun _ ↦ rfl
      rw [hx' p hp, ← Category.assoc, ← Cris.spMap_comp, e]
      exact hx p hp.1
    obtain ⟨ρ', hρ'⟩ := Hol.exists_jet_algHom W' 0 h0' ((0, w) : Tot Empty g)
    have hρρ : ρ'.toRingHom.comp res.toRingHom = ρ.toRingHom := RingHom.ext fun k ↦ by
      change ρ' (res k) = ρ k
      refine TrivSqZeroExt.ext ?_ ?_
      · rw [(hρ' _).1, (hρ _).1, hres k 0 h0']
      · rw [(hρ' _).2, (hρ _).2, Hol.fderiv_fn_congr _ (hres k) h0']
    have hv : spMap ρ.toRingHom ≫ x = spMap ρ'.toRingHom ≫ x' := by
      rw [← hρρ, Cris.spMap_comp, Category.assoc, hxx]
    have hx'U' : ⊤ ≤ x' ⁻¹ᵁ U := fun q hq ↦ hle (hx'U hq)
    obtain ⟨h', hev, -⟩ := GlobalTheory.EvalNat.evalAt_natural ρ'.toRingHom x' U hx'U'
    have e1 : evalAt (spMap ρ.toRingHom ≫ x) U h f = ρ' (evalAt x' U hx'U' f) := by
      refine Eq.trans ?_ (hev f)
      congr 2
    have e2 : ∀ p ∈ W', (evalAt x' U hx'U' f).fn p = valAt' (u.ex p.2).left U f := fun p hp ↦ by
      rw [(evalAt_fn_eq_valAt' W' x' U hx'U' f p hp).2, hx' p hp]
      rfl
    have hd : DifferentiableAt ℂ (fun z ↦ valAt' (u.ex z).left U f) 0 :=
      (u.hol U f).2.differentiableAt ((u.hol U f).1.mem_nhds hU0)
    rw [e1, (hρ' _).2, Hol.fderiv_fn_congr _ e2 h0']
    have hc : HasFDerivAt (fun p : Tot Empty g ↦ valAt' (u.ex p.2).left U f)
        ((fderiv ℂ (fun z ↦ valAt' (u.ex z).left U f) 0).comp (ContinuousLinearMap.snd ℂ _ _)) 0 :=
      HasFDerivAt.comp (0 : Tot Empty g) (g := fun z ↦ valAt' (u.ex z).left U f) (f := Prod.snd)
        hd.hasFDerivAt hasFDerivAt_snd
    rw [hc.fderiv]
    rfl

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHarishChandraDiscreteSeries
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section

namespace GlobalTheory.DiscreteSeriesUnitary

def unitaryModule {p q : ℕ} {T : GrpData p q} (D : DSRep T) : UGKMod p q where
  M := D.HK
  ip := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => inner ℂ (D.ι x) (D.ι y))
    (fun x y z => by simp only [map_add (f := _), inner_add_left])
    (fun c x y => by simp only [map_smul, inner_smul_left, smul_eq_mul])
    (fun x y z => by simp only [map_add (f := _), inner_add_right])
    (fun c x y => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
  herm x y := inner_conj_symm (D.ι y) (D.ι x)
  pos x hx := by
    have h : D.ι x ≠ 0 := fun h => hx (D.ι_inj (h.trans (map_zero D.ι).symm))
    exact re_inner_self_pos (𝕜 := ℂ).2 h
  adj Z x y := GlobalTheory.RealPar.DerivedAdjoint.derived_adjoint p q T D.U D.HK D.ι D.der Z x y

theorem exists_unitary : ∀ (p q : ℕ) (T : GrpData p q) (D : DSRep T),
    ∃ M : UGKMod p q, M.M = D.HK :=
  fun _ _ _ D => ⟨unitaryModule D, rfl⟩

end GlobalTheory.DiscreteSeriesUnitary

end
end

