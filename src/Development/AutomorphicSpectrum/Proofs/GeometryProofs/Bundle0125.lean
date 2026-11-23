module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0124
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0062
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0007
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterAlgRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0121
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartUnitSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_hChart_of_extendsUnitAt : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W U N : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (T t : Ω) (v : Γ(X, N)) (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsCptGen ξ → IsChart s B Y → b₁ ∈ B → (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) → N ≤ U → (∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W) → IsUnit v → (∀ (q : X) (hq : genPt ξ ⤳ q) (h : q ∈ N), genMap ξ ⟨q, hq⟩ (X.presheaf.germ N q h v) = t / T) → T ≠ 0 → ExtendsUnitAt s (RingHom.id ℂ) ξ W F t (Y b₁) → ∃ (B₂ : Set (Fin d → ℂ)) (H : (Fin d → ℂ) → ℂ), b₁ ∈ B₂ ∧ HChart s ξ W U F T B₂ Y H := by
  intro X s Ω _ ξ W U N F T t v d B Y b₁ hξ hY hb₁ hN hNU hW hv hg hT hE
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := by
    simp [spMap]
  obtain ⟨ε, h', hε, hd, h0, hrel⟩ := hE d B Y hY.isOpen hY.hol
    (fun b hb => (hY.isOver b hb).trans hid.symm) b₁ hb₁ rfl
  have hopen : IsOpen (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) :=
    hd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_compl_singleton
  have hB₂ : IsOpen (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) := hY.isOpen.inter hopen
  have hsub : B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) ⊆ B := Set.inter_subset_left
  have htop : ∀ b ∈ B, ⊤ ≤ Y b ⁻¹ᵁ N := fun b hb => (top_le_iff_centre _ _).2 (hN b hb).1
  refine ⟨B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ), fun b => h' b * valAt' (Y b) N v,
    ⟨hb₁, Metric.mem_ball_self hε, h0⟩, ?_⟩
  refine
    { chart := by
        refine { isOpen := hB₂, hol := ?_, isOver := fun b hb => hY.isOver b (hsub hb), factor := ?_ }
        · intro U f
          have e : {b ∈ B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ) | ⊤ ≤ Y b ⁻¹ᵁ U} =
              (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) ∩ {b ∈ B | ⊤ ≤ Y b ⁻¹ᵁ U} := by
            ext b
            exact ⟨fun hb => ⟨hb.1, hsub hb.1, hb.2⟩, fun hb => ⟨hb.1, hb.2.2⟩⟩
          rw [e]
          exact ⟨hB₂.inter (hY.hol U f).1, (hY.hol U f).2.mono Set.inter_subset_right⟩
        · intro m B' y oB hy ov b₀ h₀ b₂ h₂ e
          obtain ⟨ε', κ, ε0, sub, dκ, k₀, hκ⟩ := hY.factor m B' y oB hy ov b₀ h₀ b₂ (hsub h₂) e
          have c : ContinuousAt κ b₀ := (dκ.differentiableAt (ball_mem_nhds _ ε0)).continuousAt
          have m₂ : κ ⁻¹' (B ∩ (ball b₁ ε ∩ h' ⁻¹' {0}ᶜ)) ∈ 𝓝 b₀ :=
            c.preimage_mem_nhds (hB₂.mem_nhds (k₀ ▸ h₂))
          obtain ⟨δ, δ0, hδ⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem m₂ (ball_mem_nhds b₀ ε0))
          have sb : ball b₀ δ ⊆ ball b₀ ε' := fun b hb => (hδ hb).2
          exact ⟨δ, κ, δ0, sb.trans sub, dκ.mono sb, k₀, fun b hb => ⟨(hδ hb).1, (hκ b (sb hb)).2⟩⟩
      inU := fun b hb => hNU (hN b hb.1).1
      cpt := fun b hb => (hN b hb.1).2
      dense := fun O oO sO nO => hW O oO (sO.trans hsub) nO
      hol := ?_
      ne := ?_
      rel := ?_ }
  · refine DifferentiableOn.mul (hd.mono fun b hb => hb.2.1) ?_
    exact (hY.hol N v).2.mono fun b hb => ⟨hb.1, htop b hb.1⟩
  · intro b hb
    refine mul_ne_zero hb.2.2 ?_
    intro hz
    obtain ⟨u, rfl⟩ := hv
    have e := valAt'_mul (Y b) N u.val u⁻¹.val
    rw [Units.mul_inv, ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_one (Y b) N (htop b hb.1), hz, zero_mul] at e
    exact one_ne_zero e
  · intro b hb hWb r hr
    have e₁ : ValAt ξ (Y b) (t / T) (valAt' (Y b) N v) :=
      ValAt.of_section (hN b hb.1).1 (hN b hb.1).2 (hg _ _ _)
    have e₂ : ValAt ξ (Y b) t (valAt' (Y b) N v * r) := by
      have := ValAt.mul e₁ hr
      rwa [div_mul_cancel₀ _ hT] at this
    rw [hrel b ⟨hb.1, hb.2.1⟩ ((top_le_iff_centre _ _).2 hWb) _ e₂, _root_.mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AnalyticChartVanishingSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt

variable {X : Scheme.{0}}

abbrev cst (s : X ⟶ Sp ℂ) (V : X.Opens) : ℂ →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)).hom

theorem top_le_spMap (hV' : X.Opens) (hV : IsAffineOpen hV') (ψ : Γ(X, hV') →+* ℂ) :
    ⊤ ≤ (spMap ψ ≫ hV.fromSpec) ⁻¹ᵁ hV' := by
  have h : ∀ p, hV.fromSpec p ∈ hV' := fun p => by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨p, rfl⟩
  have e := h (spMap ψ (show Sp ℂ from IsLocalRing.closedPoint ℂ))
  rw [← Scheme.Hom.comp_apply] at e
  exact (top_le_iff_centre _ hV').2 e

theorem val_spMap {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) (a : Γ(X, V)) :
    valAt' (spMap ψ ≫ hV.fromSpec) V a = ψ a :=
  (valAt'_fromSpec hV _ a).trans (valAt'_spMap ψ a)

theorem eq_spMap {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V) :
    y = spMap (valHom y V h) ≫ hV.fromSpec := by
  have hr : Set.range y ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    exact h (Set.mem_univ p)
  have hl : IsOpenImmersion.lift hV.fromSpec y hr ≫ hV.fromSpec = y := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ : ∃ φ : Γ(X, V) →+* ℂ, spMap φ = IsOpenImmersion.lift hV.fromSpec y hr :=
    ⟨(Spec.preimage (IsOpenImmersion.lift hV.fromSpec y hr)).hom, Spec.map_preimage _⟩
  rw [← hφ] at hl
  have e : valHom y V h = φ := RingHom.ext fun a => by
    show valAt' y V a = φ a
    rw [← hl]
    exact val_spMap hV φ a
  rw [e, hl]

theorem fromSpec_comp_structure_map (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) : hV.fromSpec ≫ s = spMap (cst s V) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  exact (Spec.map_comp _ _).symm

theorem over_iff (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (ψ : Γ(X, V) →+* ℂ) :
    (spMap ψ ≫ hV.fromSpec) ≫ s = 𝟙 _ ↔ ψ.comp (cst s V) = RingHom.id ℂ := by
  rw [Category.assoc, fromSpec_comp_structure_map]
  constructor
  · intro h
    have e : spMap (ψ.comp (cst s V)) = spMap (RingHom.id ℂ) := (Spec.map_comp _ _).trans (h.trans (Spec.map_id _).symm)
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  · intro h
    refine (Spec.map_comp _ _).symm.trans ?_
    exact (congrArg spMap h).trans (Spec.map_id _)

theorem comp_cst (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) (y : Sp ℂ ⟶ X) (h : ⊤ ≤ y ⁻¹ᵁ V)
    (hy : y ≫ s = 𝟙 _) : (valHom y V h).comp (cst s V) = RingHom.id ℂ :=
  (over_iff s hV _).1 (by rw [← eq_spMap hV y h]; exact hy)

theorem isOpen_near {E : Type} [TopologicalSpace E] {T : Set E} (hT : IsOpen T) {n : ℕ} (v : Fin n → E → ℂ)
    (c : Fin n → ℂ) (ε : ℝ) (hv : ∀ j, ContinuousOn (v j) T) : IsOpen {b ∈ T | ∀ j, ‖v j b - c j‖ < ε} := by
  rw [isOpen_iff_mem_nhds]
  rintro b ⟨hb, hj⟩
  have h : ∀ j, ∀ᶠ y in 𝓝 b, ‖v j y - c j‖ < ε := fun j =>
    (((hv j).continuousAt (hT.mem_nhds hb)).sub continuousAt_const).norm.eventually_lt continuousAt_const (hj j)
  filter_upwards [hT.mem_nhds hb, Filter.eventually_all.2 h] with y h₁ h₂ using ⟨h₁, h₂⟩

theorem isChart_of_data (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) {D M : ℕ} (g : Fin M → Γ(X, V))
    (f : Fin D → Γ(X, V)) {B₀ : Set (Fin D → ℂ)} {ε : ℝ} (Ψ : (Fin D → ℂ) → (Γ(X, V) →+* ℂ)) (ψ₀ : Γ(X, V) →+* ℂ)
    (o : IsOpen B₀) (a₁ : ∀ b ∈ B₀, (Ψ b).comp (cst s V) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i)
    (a₂ : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B₀)
    (a₃ : ∀ ψ : Γ(X, V) →+* ℂ, ψ.comp (cst s V) = RingHom.id ℂ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
      (fun i => ψ (f i)) ∈ B₀ ∧ Ψ (fun i => ψ (f i)) = ψ) :
    IsChart s {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} (fun b => spMap (Ψ b) ≫ hV.fromSpec) := by
  have oB : IsOpen {b ∈ B₀ | ∀ j, ‖Ψ b (g j) - ψ₀ (g j)‖ < ε} :=
    isOpen_near o (fun j b => Ψ b (g j)) _ ε fun j => (a₂ (g j)).continuousOn
  refine ⟨oB, ?_, fun b hb => (over_iff s hV _).2 (a₁ b hb.1).1, ?_⟩
  · exact isHolTo_comp (isHolTo_spMap oB fun a => (a₂ a).mono fun b hb => hb.1) hV.fromSpec
  intro m B' y oB' hy ov b₀ h₀ b₁ h₁ e
  have oT : IsOpen {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := (hy V 0).1
  have dv : ∀ a : Γ(X, V), DifferentiableOn ℂ (fun b => valAt' (y b) V a) {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} := fun a => (hy V a).2
  have oT' := isOpen_near oT (fun j b => valAt' (y b) V (g j)) (fun j => ψ₀ (g j)) ε fun j => (dv (g j)).continuousOn
  have v₀ : ∀ a, valAt' (y b₀) V a = Ψ b₁ a := fun a => by rw [e]; exact val_spMap hV _ a
  have m₀ : b₀ ∈ {b ∈ {b ∈ B' | ⊤ ≤ y b ⁻¹ᵁ V} | ∀ j, ‖valAt' (y b) V (g j) - ψ₀ (g j)‖ < ε} :=
    ⟨⟨h₀, by rw [e]; exact top_le_spMap V hV _⟩, fun j => by rw [v₀]; exact h₁.2 j⟩
  obtain ⟨δ, δ0, hδ⟩ := Metric.isOpen_iff.1 oT' b₀ m₀
  refine ⟨δ, fun b i => valAt' (y b) V (f i), δ0, fun b hb => (hδ hb).1.1,
    differentiableOn_pi.2 fun i => (dv (f i)).mono fun b hb => (hδ hb).1, funext fun i => ?_, fun b hb => ?_⟩
  · show valAt' (y b₀) V (f i) = b₁ i
    rw [v₀]; exact (a₁ b₁ h₁.1).2 i
  · have t := (hδ hb).1.2
    have k := a₃ (valHom (y b) V t) (comp_cst s hV _ t (ov b (hδ hb).1.1)) (hδ hb).2
    have k₂ : Ψ (fun i => valAt' (y b) V (f i)) = valHom (y b) V t := k.2
    refine ⟨⟨k.1, fun j => ?_⟩, ?_⟩
    · rw [k₂]; exact (hδ hb).2 j
    · show y b = spMap (Ψ (fun i => valAt' (y b) V (f i))) ≫ hV.fromSpec
      rw [k₂]; exact eq_spMap hV _ t

theorem res_cst (s : X ⟶ Sp ℂ) {U V : X.Opens} (h : V ≤ U) (c : ℂ) :
    (X.presheaf.map (homOfLE h).op).hom (cst s U c) = cst s V c :=
  congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := U) (fun _ _ => trivial) (homOfLE h).op)
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c))

theorem exists_std (s : X ⟶ Sp ℂ) [Smooth s] (q : X) (M : X.Opens) (hq : q ∈ M) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V) (D : ℕ), V ≤ M ∧ q ∈ V ∧ (cst s V).IsStandardSmoothOfRelativeDimension D := by
  obtain ⟨U₀, -, U, hU, hp, hle, hsm⟩ := Smooth.exists_isStandardSmooth s q
  have hU₀ : U₀ = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have h2 : y = s q := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [h2]; exact hle hp
  subst hU₀
  obtain ⟨n, hn⟩ : ∃ n, RingHom.IsStandardSmoothOfRelativeDimension n (s.appLE ⊤ U hle).hom := by
    let _ := (s.appLE ⊤ U hle).hom.toAlgebra
    have : Algebra.IsStandardSmooth Γ(Sp ℂ, ⊤) Γ(X, U) := hsm
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := this
    exact ⟨P.dimension, _, _, _, ‹_›, P, rfl⟩
  obtain ⟨a, haM, hqa⟩ := hU.exists_basicOpen_le (V := M) ⟨q, hq⟩ hp
  refine ⟨X.basicOpen a, hU.basicOpen a, n, haM, hqa, ?_⟩
  have := hU.isLocalization_basicOpen a
  have h1 : (algebraMap Γ(X, U) Γ(X, X.basicOpen a)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway a
  have h2 : (cst s U).IsStandardSmoothOfRelativeDimension n :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv hn
  have h3 := h1.comp h2
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact (res_cst s (X.basicOpen_le a) c).symm

theorem isDomain_of_le {Z V : X.Opens} [AlgebraicGeometry.IsIntegral Z.toScheme] (h : V ≤ Z) {q : X} (hq : q ∈ V) :
    IsDomain Γ(X, V) := by
  haveI : Nonempty V.toScheme := ⟨⟨q, hq⟩⟩
  haveI : AlgebraicGeometry.IsIntegral V.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE h)
  haveI : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨q, hq⟩, trivial⟩⟩
  exact MulEquiv.isDomain Γ(V.toScheme, ⊤) (Scheme.Opens.topIso V).symm.commRingCatIsoToRingEquiv.toMulEquiv

theorem exists_chart : (∀ (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] (D : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension D ℂ A] (O : Set (Fin D → ℂ)) (Ψ : (Fin D → ℂ) → (A →+* ℂ))
    (f : Fin D → A) (a : A), IsOpen O → O.Nonempty →
    (∀ b ∈ O, (Ψ b).comp (algebraMap ℂ A) = RingHom.id ℂ ∧ ∀ i, Ψ b (f i) = b i) → (∀ b ∈ O, Ψ b a = 0) → a = 0) →
    ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (W N : X.Opens) (x : Sp ℂ ⟶ X), Smooth s →
    IsCptGen ξ → genPt ξ ∈ W → x ≫ s = 𝟙 _ → genPt ξ ⤳ centre x → centre x ∈ N →
    ∃ (d : ℕ) (B : Set (Fin d → ℂ)) (Y : (Fin d → ℂ) → (Sp ℂ ⟶ X)) (b₁ : Fin d → ℂ), IsChart s B Y ∧ b₁ ∈ B ∧
      Y b₁ = x ∧ (∀ b ∈ B, centre (Y b) ∈ N ∧ genPt ξ ⤳ centre (Y b)) ∧
      ∀ O : Set (Fin d → ℂ), IsOpen O → O ⊆ B → O.Nonempty → ∃ b ∈ O, centre (Y b) ∈ W := by
  intro hring X s Ω _ ξ W N x hs hξ hW hxs hgx hxN
  haveI := hs
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨Z, hZ, -, hZi⟩ := cpt_open_integral X Ω ξ hξ
  obtain ⟨V, hV, D, hVM, hxV, hstd⟩ := exists_std s (centre x) (N ⊓ Z) ⟨hxN, (hZ _).2 hgx⟩
  letI alg : Algebra ℂ Γ(X, V) := (cst s V).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D ℂ Γ(X, V) := hstd
  haveI : IsDomain Γ(X, V) := isDomain_of_le (hVM.trans inf_le_right) hxV
  have hxt : ⊤ ≤ x ⁻¹ᵁ V := (top_le_iff_centre x V).2 hxV
  have h₀ : (valHom x V hxt).comp (algebraMap ℂ Γ(X, V)) = RingHom.id ℂ := comp_cst s hV x hxt hxs
  obtain ⟨M, g, f, B₀, ε, Ψ, ε0, o, a₁, a₂, a₃⟩ := anChart_alg D (RingHom.id ℂ) (valHom x V hxt) h₀
  have hc := isChart_of_data s hV g f Ψ (valHom x V hxt) o a₁ a₂ a₃
  have m₁ := a₃ _ h₀ fun _ => by simpa using ε0
  have hY : ∀ b, centre (spMap (Ψ b) ≫ hV.fromSpec) ∈ V := fun b => (top_le_iff_centre _ V).1 (top_le_spMap V hV _)
  refine ⟨D, _, _, fun i => valHom x V hxt (f i), hc, ⟨m₁.1, fun j => ?_⟩, ?_, fun b _ => ⟨(hVM (hY b)).1, (hZ _).1 (hVM (hY b)).2⟩, ?_⟩
  · rw [m₁.2]; simpa using ε0
  · show spMap (Ψ fun i => valHom x V hxt (f i)) ≫ hV.fromSpec = x
    rw [m₁.2]; exact (eq_spMap hV x hxt).symm
  intro O oO sO nO
  have hgV : genPt ξ ∈ V := genPt_mem hgx hxV
  obtain ⟨a, haW, haξ⟩ := hV.exists_basicOpen_le (V := W) ⟨genPt ξ, hW⟩ hgV
  have a0 : a ≠ 0 := by
    rintro rfl
    simp at haξ
  by_contra hc'
  push_neg at hc'
  refine a0 (hring Γ(X, V) D O Ψ f a oO nO (fun b hb => a₁ b (sO hb).1) fun b hb => ?_)
  by_contra hne
  refine hc' b hb (haW ?_)
  have hv : valAt' (spMap (Ψ b) ≫ hV.fromSpec) V a ≠ 0 := by rw [val_spMap]; exact hne
  exact (valAt'_ne_zero_iff _ V (top_le_spMap V hV _) a _).1 hv

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC.ChartAt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AppLEBasicOpenIsStandardSmooth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

theorem res_top_isStandardSmooth (X : Scheme.{0}) [IsAffine X] (t : Γ(X, ⊤)) (D : X.Opens) (hD : D = X.basicOpen t) :
    (X.presheaf.map (homOfLE (le_top : D ≤ ⊤)).op).hom.IsStandardSmooth := by
  subst hD
  have := (isAffineOpen_top X).isLocalization_basicOpen t
  exact RingHom.isStandardSmooth_holdsForLocalizationAway _ t

theorem appLE_basicOpen_isStandardSmooth {X Y : Scheme.{0}} (p : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    {V : Y.Opens} (hV : IsAffineOpen V) (e : V ≤ p ⁻¹ᵁ U) (h : (p.appLE U V e).hom.IsStandardSmooth) (a : Γ(X, U))
    (e' : Y.basicOpen (p.appLE U V e a) ≤ p ⁻¹ᵁ X.basicOpen a) :
    (p.appLE (X.basicOpen a) (Y.basicOpen (p.appLE U V e a)) e').hom.IsStandardSmooth := by
  have := hV.isLocalization_basicOpen (p.appLE U V e a)
  have := hU.isLocalization_basicOpen a
  rw [hU.appLE_eq_away_map p hV]
  exact RingHom.isStandardSmooth_localizationPreserves.away _ _ _ _ h

theorem exists_chart : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (φ : R →+* ℂ), Smooth G.hom →
  ∃ (V : G.left.Opens) (r : R), IsAffineOpen V ∧ φ r ≠ 0 ∧ (GlobalTheory.CompanionTheory.Ar.Flat.ExpChart.cst G.hom V).IsStandardSmooth ∧
    ⊤ ≤ (spMap (algebraMap R (Localization.Away r)) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left) ⁻¹ᵁ V := by
  intro R _ G _ φ hsm
  set s : Sp R ⟶ G.left := (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left with hsdef
  have hs : s ≫ G.hom = 𝟙 (Sp R) := Over.w (1 : Over.mk (𝟙 (Sp R)) ⟶ G)
  let x : Sp R := (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R)
  obtain ⟨U, hU, V, hV, e, hxU, -, hUs, h⟩ :=
    GlobalTheory.LieChart.exists_isStandardSmooth_section G.hom s hs x ⊤ trivial
  obtain ⟨_, ⟨r, rfl⟩, hxr, hsub⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open
    (show (x : PrimeSpectrum R) ∈ (SetLike.coe U : Set (PrimeSpectrum R)) from hxU)
    (show IsOpen (SetLike.coe U : Set (PrimeSpectrum R)) from U.isOpen)
  have hr : φ r ≠ 0 := fun h0 => hxr (show r ∈ RingHom.ker φ from h0)
  let t : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv r
  have htr : (Sp R).basicOpen t = PrimeSpectrum.basicOpen r :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) r
  have hle : (Sp R).basicOpen t ≤ U := by
    rw [htr]; exact hsub
  let a : Γ(Sp R, U) := (Sp R).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t
  have hat : (Sp R).basicOpen a = (Sp R).basicOpen t := by
    rw [Scheme.basicOpen_res]; exact inf_eq_right.2 hle
  have e' : G.left.basicOpen (G.hom.appLE U V e a) ≤ G.hom ⁻¹ᵁ (Sp R).basicOpen a := by
    simp [Scheme.Hom.appLE]
  have h1 := appLE_basicOpen_isStandardSmooth G.hom hU hV e h a e'
  have h2 := res_top_isStandardSmooth (Sp R) t _ hat
  refine ⟨G.left.basicOpen (G.hom.appLE U V e a), r, hV.basicOpen _, hr, ?_, ?_⟩
  · have h3 : (G.hom.appLE ⊤ (G.left.basicOpen (G.hom.appLE U V e a)) (fun _ _ => trivial)).hom.IsStandardSmooth := by
      have := Scheme.Hom.map_appLE G.hom e' (homOfLE (le_top : (Sp R).basicOpen a ≤ ⊤)).op
      have e3 := congrArg CommRingCat.Hom.hom this
      rw [CommRingCat.hom_comp] at e3
      rw [← e3]
      exact h1.comp h2
    exact RingHom.isStandardSmooth_respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h3
  · intro y _
    have hz : (spMap (algebraMap R (Localization.Away r))) y ∈ (Sp R).basicOpen t := by
      rw [htr]
      have := PrimeSpectrum.localization_away_comap_range (Localization.Away r) r
      exact this.subset ⟨y, rfl⟩
    set z := (spMap (algebraMap R (Localization.Away r))) y with hzdef
    have hps : G.hom (s z) = z := by rw [← Scheme.Hom.comp_apply, hs]; rfl
    have h1 : s z ∈ V := hUs (hle hz)
    have h2 : s z ∈ G.hom ⁻¹ᵁ (Sp R).basicOpen a := by
      show G.hom (s z) ∈ (Sp R).basicOpen a
      rw [hps, hat]; exact hz
    show (spMap (algebraMap R (Localization.Away r)) ≫ s) y ∈ G.left.basicOpen (G.hom.appLE U V e a)
    rw [Scheme.Hom.comp_apply]
    show s z ∈ G.left.basicOpen (G.hom.appLE U V e a)
    simpa [Scheme.Hom.appLE, ← Scheme.preimage_basicOpen] using And.intro h1 h2

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArtinSchreierCocycleRoot
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CompanionTheory.Ar.CechP.coboundary_of_pow_coboundary : ∀ (Z : Scheme.{0}) [IsIntegral Z] (p : ℕ) [Fact p.Prime] [CharP Z.functionField p], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (J : Type) (U : J → Z.Opens) (n : ∀ a b, Γ(Z, U a ⊓ U b)) (h : ∀ a, Γ(Z, U a)) (a₀ : J) [Nonempty (U a₀)], (∀ a b, n a b ^ p = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (h a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (h b)) → (∃ r : Z.functionField, r ^ p = (Z.germToFunctionField (U a₀)).hom (h a₀)) → ∃ s : ∀ a, Γ(Z, U a), ∀ a b, n a b = (Z.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ≤ U a)).op).hom (s a) - (Z.presheaf.map (homOfLE (inf_le_right : U a ⊓ U b ≤ U b)).op).hom (s b) := by
  intro Z _ p _ _ hN J U n h a₀ _ hn ⟨r, hr⟩
  have hg : genericPoint Z ∈ U a₀ := ((genericPoint_spec Z).mem_open_set_iff (U a₀).isOpen).mpr (by
    obtain ⟨⟨z, hz⟩⟩ := ‹Nonempty (U a₀)›
    exact ⟨z, trivial, hz⟩)
  haveI : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  have hp : (p : Γ(Z, ⊤)) = 0 := by
    apply Z.germToFunctionField_injective ⊤
    rw [map_natCast, map_zero]
    exact CharP.cast_eq_zero _ p
  obtain ⟨s, hs⟩ := GlobalTheory.CechRoot.exists_root Z (fun b => (hN b).2) p hp J U h n
    (fun a b => (hn a b).symm) a₀ (genericPoint Z) hg (algebraMap Z.functionField _ r)
    (by rw [← map_pow, hr])
  exact ⟨s, fun a b => (hs a b).symm⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartIdealLocalizationMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ar.ChartHom

theorem exists_hom_chart : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (R : Type) [CommRing R] (θ : MvPolynomial (Σ k, J k) ℂ →+* R),
    (∀ g ∈ ReciprocityTheory.AnForm.R.chartIdeal (pC (mCoordIdeal y)) c, θ g = 0) →
    ∀ (F : MvPolynomial (Σ k, J k) ℚ), IsUnit (θ (map (algebraMap ℚ ℂ) F)) →
    ∀ S : Subalgebra ℚ Ω, S = Algebra.adjoin ℚ (insert (aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) F : Ω)⁻¹
        (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)) →
    ∃ ψ : S →+* R, ∀ (G : MvPolynomial (Σ k, J k) ℚ) (s : S),
      (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) G → ψ s = θ (map (algebraMap ℚ ℂ) G) := by
  intro K _ J _ Ω _ _ y c hc R _ θ hθ F hF S hS
  exact exists_hom_adjoin_inv (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩)
    (θ.comp (map (algebraMap ℚ ℂ)))
    (fun G hG => hθ _ (GlobalTheory.CompanionTheory.Ar.ChartDehom.map_mem_chartIdeal K J Ω y c hc G hG)) F hF S hS

end GlobalTheory.CompanionTheory.Ar.ChartHom
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericCharZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.CharZeroModel

theorem charZero_of_flat {X : Scheme.{0}} {R : Type} [CommRing R] [IsDomain R] [CharZero R]
    (s : X ⟶ Spec (CommRingCat.of R)) [Flat s] {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (h : Function.Injective (Scheme.stalkClosedPointTo ξ).hom) : CharZero Ω := by
  classical
  set x := ξ.base (IsLocalRing.closedPoint Ω) with hx
  have hfl : (s.stalkMap x).hom.Flat := Flat.stalkMap s x
  have hinv : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.injective
  have hgerm := germ_injective_of_isIntegral (X := Spec (CommRingCat.of R)) (U := ⊤) (x := s.base x)
    (hx := trivial)
  have hA : ∀ n : ℕ, n ≠ 0 → (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) ≠ 0 := by
    intro n hn h0
    apply (Nat.cast_ne_zero (R := R)).mpr hn
    apply hinv
    apply hgerm
    simp only [map_zero, map_natCast]
    exact h0
  have hO : ∀ n : ℕ, n ≠ 0 → (n : X.presheaf.stalk x) ≠ 0 := by
    intro n hn h0
    let _ := (s.stalkMap x).hom.toAlgebra
    have : Module.Flat ((Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) (X.presheaf.stalk x) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
      (mem_nonZeroDivisors_of_ne_zero (hA n hn))
    have h3 : (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (1 : X.presheaf.stalk x) =
        (n : (Spec (CommRingCat.of R)).presheaf.stalk (s.base x)) • (0 : X.presheaf.stalk x) := by
      rw [smul_zero, Algebra.smul_def, _root_.mul_one, map_natCast]
      exact h0
    exact one_ne_zero (hreg h3)
  exact charZero_of_inj_zero fun n hn => by
    by_contra hne
    apply hO n hne
    apply h
    rw [map_natCast, map_zero]
    exact hn

theorem charZero_function_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → CharZero Ω₀ := by
  intro E _ _ _ H D l Xo c Y Ω₀ _ ξ₀ hξ
  have := Y.flat
  exact charZero_of_flat Y.s ξ₀ hξ.bij.1

end GlobalTheory.CompanionTheory.Ar.CharZeroModel
end

