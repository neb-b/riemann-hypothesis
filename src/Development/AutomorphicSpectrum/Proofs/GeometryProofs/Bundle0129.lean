module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0056
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0053
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0118
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0122
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0116
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompComparisonRight
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VbGen

theorem flagStep_comp {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e) {r : ℕ}
    (b b' : Fin r → V) (k : ℕ) (h : flagStep Ω b k = flagStep Ω b' k) :
    flagStep Ω' (fun a => j (b a)) k = flagStep Ω' (fun a => j (b' a)) k := by
  have key : ∀ c c' : Fin r → V, flagStep Ω c k ≤ flagStep Ω c' k →
      flagStep Ω' (fun a => j (c a)) k ≤ flagStep Ω' (fun a => j (c' a)) k := by
    intro c c' hle
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    have hmem : c a ∈ flagStep Ω c' k := hle (Submodule.subset_span ⟨a, ha, rfl⟩)
    show j (c a) ∈ _
    refine Submodule.span_induction (p := fun v _ => j v ∈ flagStep Ω' (fun a => j (c' a)) k) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨d, hd, rfl⟩
      exact Submodule.subset_span ⟨d, hd, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro t x _ hx
      rw [hj]
      exact Submodule.smul_mem _ _ hx
  exact le_antisymm (key _ _ h.le) (key _ _ h.ge)

theorem span_image_span {Ω Ω' V V' : Type} [Field Ω] [Field Ω'] [AddCommGroup V] [Module Ω V] [AddCommGroup V']
    [Module Ω' V'] (i : Ω →+* Ω') (j : V →+ V') (hj : ∀ (a : Ω) (e : V), j (a • e) = i a • j e)
    (R : Subring Ω) (R' : Subring Ω') (hR : ∀ a ∈ R, i a ∈ R') {r : ℕ} (b : Fin r → V) :
    Submodule.span R' (j '' (Submodule.span R (Set.range b) : Set V)) =
      Submodule.span R' (Set.range fun a => j (b a)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction
      (p := fun v _ => j v ∈ Submodule.span R' (Set.range fun a => j (b a))) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨d, rfl⟩
      exact Submodule.subset_span ⟨d, rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add (f := _)]
      exact add_mem hx hy
    · intro t x _ hx
      have h1 : j (t • x) = (⟨i t, hR t t.2⟩ : R') • j x := hj (t : Ω) x
      rw [h1]
      exact Submodule.smul_mem _ _ hx
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨b a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩

theorem discr_inv_mem {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (p : Cpt ξ)
    (F : Type) [Field F] [NumberField F] (h : ∀ n : ℕ, 0 < n → unitAt ξ p (n : Ω)) :
    (((NumberField.discr F : ℤ) : Ω))⁻¹ ∈ regAt ξ p := by
  have hn0 : 0 < (NumberField.discr F).natAbs := Int.natAbs_pos.2 (NumberField.discr_ne_zero F)
  obtain ⟨-, -, hu⟩ := h _ hn0
  rcases Int.natAbs_eq (NumberField.discr F) with e | e
  · rw [e]; simpa using hu
  · rw [e]
    simpa using (regAt ξ p).neg_mem hu


set_option maxHeartbeats 1000000 in
theorem isFlagVBOn_genFib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (Ω₁ Ω : Type) [Field Ω₁] [Field Ω] (K₁ : Type) [Fintype K₁] (J₁ : K₁ → Type) [∀ k, Fintype (J₁ k)] (y₁ : (Σ k, J₁ k) → Ω₁) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S₀ y₁) (Fl : A.Flag) (B : HodgeCpt Y S y) (i : Ω₁ →+* Ω) (h : B.X ⟶ A.X) (jA : A.Li →+ B.Li), GlobalTheory.CompanionTheory.Ar.Dominates B.ξ A.ξ h i → B.f = h ≫ A.f → B.cst = i.comp A.cst → IsExtOver i jA → (∀ e, (B.M.pt (jA e)).left ≫ B.m.φ = spMap (dualMap i) ≫ (A.M.pt e).left ≫ A.m.φ) → (∀ a e, jA (A.ρ a e) = B.ρ a (jA e)) → B.M.lat = A.M.lat.pull B.ξ h jA → ∀ q ∈ genFib B.ξ, ∀ s, (B.V s).IsFlagVBOn {q} (fun a => jA (Fl.b s a)) := by
  intro E _ _ _ H D l Xo c Y S₀ S Ω₁ Ω _ _ K₁ _ J₁ _ y₁ K _ J _ y A Fl B i h jA hdom hf hcst hext hpt hρ hlat q hq s
  intro q' hq'
  obtain rfl : q' = q := hq'
  haveI : CharZero Ω₁ := charZero_of_injective_ringHom A.cst.injective
  have hgenA := A.tie.gen
  have hgenB := B.tie.gen
  obtain ⟨hsp, hreg, hun⟩ := RegAtDom.regAt_dominates A.X Ω₁ A.ξ B.X Ω B.ξ h i hdom q'
  have hunit : ∀ n : ℕ, 0 < n → unitAt A.ξ ⟨h q'.1, hsp⟩ (n : Ω₁) := fun n hn =>
    hun hgenB _ (natCast_mem _ n) (by simpa using hq n hn)
  have hVA : A.V s ⟨h q'.1, hsp⟩ = A.dR s ⟨h q'.1, hsp⟩ :=
    Lat.patch_of_not S₀ _ _ fun r hr hfib => hfib (hunit r (A.S_prime r hr).pos)
  have hVB : B.V s q' = B.dR s q' :=
    Lat.patch_of_not S _ _ fun r hr hfib => hfib (hq r (B.S_prime r hr).pos)
  have hdisc := discr_inv_mem ⟨h q'.1, hsp⟩ E hunit
  have hint : ∀ a, A.emb s a ∈ regAt A.ξ ⟨h q'.1, hsp⟩ := fun a =>
    _root_.GlobalTheory.CompanionTheory.Ar.IntReg.mem_regAt_of_isIntegral_of_stalk A.X Ω₁ A.ξ ⟨h q'.1, hsp⟩ hgenA (A.normal (h q'.1)).2 _
      ((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (A.emb s).toIntAlgHom)
  obtain ⟨U, hU, b, hb, hfr⟩ := Fl.sub s ⟨h q'.1, hsp⟩ trivial
  obtain ⟨hli, hbs⟩ := hfr ⟨h q'.1, hsp⟩ trivial hU
  refine ⟨⊤, trivial, fun a => jA (b a), fun k => flagStep_comp i jA hext.1 _ _ k (hb k), ?_⟩
  intro q'' hq'' _
  rw [show q'' = q' from hq'']
  refine ⟨hext.2 _ b hli, ?_⟩
  have key := _root_.GlobalTheory.CompanionTheory.Ar.EigLat.span_inf_eigSp E Ω₁ Ω i A.Li B.Li jA A.ρ B.ρ (A.emb s) _ _ (A.M.lat ⟨h q'.1, hsp⟩) hext
    (fun a e => (hρ a e).symm) hreg
    (fun a e he => _root_.GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable A.X Ω₁ A.ξ A.t.G A.Li A.M (𝓞 E) A.t.act A.ρ A.act _ a e he) hint hdisc
  have hem : B.emb s = i.comp (A.emb s) := by
    show B.cst.comp _ = i.comp (A.cst.comp _)
    rw [hcst]; rfl
  have hL : B.M.lat q' = Submodule.span (regAt B.ξ q') (jA '' (A.M.lat ⟨h q'.1, hsp⟩ : Set A.Li)) := by
    rw [hlat]
    show Lat.pull _ _ _ _ _ = _
    unfold Lat.pull
    congr 1
    ext e'
    constructor
    · rintro ⟨_, e, he, rfl⟩
      exact ⟨e, he, rfl⟩
    · rintro ⟨e, he, rfl⟩
      exact ⟨hsp, e, he, rfl⟩
  have hA : A.M.lat ⟨h q'.1, hsp⟩ ⊓ (eigSp A.ρ (A.emb s)).restrictScalars (regAt A.ξ ⟨h q'.1, hsp⟩) =
      Submodule.span (regAt A.ξ ⟨h q'.1, hsp⟩) (Set.range b) := hVA.symm.trans hbs
  rw [hVB]
  show B.M.lat q' ⊓ (eigSp B.ρ (B.emb s)).restrictScalars (regAt B.ξ q') = _
  rw [hL, hem, key, hA]
  exact span_image_span i jA hext.1 _ _ hreg b

end GlobalTheory.CompanionTheory.Ar.VbGen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicChartNearPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart

abbrev cst {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) (V : X.Opens) : K →+* Γ(X, V) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)).hom

theorem cst_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {V : X.Opens}
    (hV : IsAffineOpen V) {d : ℕ} (h : (cst s V).IsStandardSmoothOfRelativeDimension d)
    (g : Γ(X, V)) : (cst s (X.basicOpen g)).IsStandardSmoothOfRelativeDimension d := by
  have := hV.isLocalization_basicOpen g
  have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen g)).IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway g
  have h3 := h1.comp h
  rw [zero_add] at h3
  convert h3 using 1
  ext c
  exact congr($(Scheme.Hom.appLE_map s (U := ⊤) (V := V) le_top (homOfLE (X.basicOpen_le g)).op)
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv c)).symm

theorem exists_std {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {d : ℕ}
    (hs : SmoothOfRelativeDimension d s) (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ V ≤ U ∧ x ∈ V ∧
      (cst s V).IsStandardSmoothOfRelativeDimension d := by
  obtain ⟨W, -, V, hV, hxV, e, hf⟩ := hs.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : W = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    have : y = s x := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact e hxV
  obtain ⟨g, hgU, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
  refine ⟨X.basicOpen g, hV.basicOpen g, hgU, hxg, cst_basicOpen s hV ?_ g⟩
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv hf

theorem fromSpec_comp {K : Type} [Field K] {X : Scheme.{0}} (s : X ⟶ Sp K) {V : X.Opens}
    (hV : IsAffineOpen V) : hV.fromSpec ≫ s = spMap (cst s V) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top (Sp K)) hV (fun _ _ => trivial)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem exists_domain {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    [IsNoetherianRing Γ(X, V)] (ξ : X) (hξ : ξ ∈ V) [IsDomain (X.presheaf.stalk ξ)] :
    ∃ f : Γ(X, V), ξ ∈ X.basicOpen f ∧ IsDomain Γ(X, X.basicOpen f) :=
  _root_.UpperTheory.Reformulated.B.DYde8.main hV ξ hξ

end GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart


open GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart in
theorem GlobalTheory.CompanionTheory.Ar.Flat.SmoothChart.exists_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ), SmoothOfRelativeDimension d s → ∀ (x : Sp ℂ ⟶ X) (W₀ : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W₀ → IsDomain (X.presheaf.stalk (centre x)) → ∃ (V : X.Opens) (hV : IsAffineOpen V) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W₀ ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, (spMap (ψ z) ≫ hV.fromSpec) ≫ s = spMap σ) ∧ ∀ g : Γ(X, V), (∀ z ∈ ball (0 : Fin d → ℂ) 1, ψ z g = 0) → g = 0 := by
  intro K _ σ X s d hsm x W₀ hxs hW hdom
  have hξW : centre x ∈ W₀ := hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  obtain ⟨V₁, hV₁, hV₁W, hξ₁, hstd₁⟩ := exists_std s hsm W₀ (centre x) hξW
  have hnoeth : IsNoetherianRing Γ(X, V₁) := by
    letI := (cst s V₁).toAlgebra
    haveI : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, V₁) := hstd₁
    haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := Γ(X, V₁)) d
    exact Algebra.FiniteType.isNoetherianRing K _
  obtain ⟨f, hξ, hdomV⟩ := exists_domain hV₁ (centre x) hξ₁
  have hV : IsAffineOpen (X.basicOpen f) := hV₁.basicOpen f
  have hstd := cst_basicOpen s hV₁ hstd₁ f
  letI := (cst s (X.basicOpen f)).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d K Γ(X, X.basicOpen f) := hstd
  have hrange : Set.range x ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint ℂ)]
    exact hξ
  let y := IsOpenImmersion.lift hV.fromSpec x hrange
  have hy : y ≫ hV.fromSpec = x := IsOpenImmersion.lift_fac _ _ _
  let ψ₀ : Γ(X, X.basicOpen f) →+* ℂ := (Spec.preimage y).hom
  have hψ₀ : spMap ψ₀ ≫ hV.fromSpec = x := by
    rw [← hy]
    congr 1
    exact Spec.map_preimage y
  have hcomp : ∀ ψ : Γ(X, X.basicOpen f) →+* ℂ,
      (spMap ψ ≫ hV.fromSpec) ≫ s = spMap (ψ.comp (cst s (X.basicOpen f))) := by
    intro ψ
    rw [Category.assoc, fromSpec_comp s hV, ← Spec.map_comp]
    rfl
  have hσ : ψ₀.comp (algebraMap K Γ(X, X.basicOpen f)) = σ := by
    have h := hcomp ψ₀
    rw [hψ₀, hxs] at h
    have h' := Spec.map_injective h
    exact (congrArg CommRingCat.Hom.hom h').symm
  obtain ⟨Ψ, hol, h0, hbase, hvan⟩ := _root_.GlobalTheory.CompanionTheory.ChartRing.exists_polydisc_chart K Γ(X, X.basicOpen f) d σ ψ₀ hσ
  refine ⟨X.basicOpen f, hV, Ψ, (X.basicOpen_le f).trans hV₁W, hol, ?_, ?_, hvan⟩
  · rw [h0]; exact hψ₀
  · intro z hz
    rw [hcomp, ← hbase z hz]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfNonvanishingPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC

namespace GlobalTheory.CompanionTheory.Ar.Flat.GagaC

theorem exists_algHom_eq_zero_of_not_isUnit {T : Type} [CommRing T] [Algebra ℂ T] [Algebra.FiniteType ℂ T]
    (a : T) (h : ¬ IsUnit a) : ∃ χ : T →ₐ[ℂ] ℂ, χ a = 0 := by
  obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : a ∈ M := haM (Ideal.mem_span_singleton_self a)
  letI := Ideal.Quotient.field M
  haveI : Algebra.FiniteType ℂ (T ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ M) (Ideal.Quotient.mkₐ_surjective ℂ M)
  haveI : Module.Finite ℂ (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℂ (T ⧸ M)
  have hbij : Function.Bijective (algebraMap ℂ (T ⧸ M)) :=
    ⟨(algebraMap ℂ (T ⧸ M)).injective, IsSepClosed.algebraMap_surjective ℂ (T ⧸ M)⟩
  let e : ℂ ≃ₐ[ℂ] T ⧸ M := AlgEquiv.ofBijective (Algebra.ofId ℂ (T ⧸ M)) hbij
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ ℂ M), ?_⟩
  simp [Ideal.Quotient.eq_zero_iff_mem.2 hmem]

theorem fromSpec_comp_structure {X : Scheme.{0}} (s : X ⟶ Sp ℂ) {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec ≫ s = Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)) := by
  rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec s (isAffineOpen_top _) hV (fun _ _ => trivial)]
  congr 1
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

private theorem germ_comp_stalkClosedPointTo_eq {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V)
    (χ : Γ(X, V) ⟶ CommRingCat.of ℂ)
    (hp : (Spec.map χ ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V) :
    X.presheaf.germ V _ hp ≫ Scheme.stalkClosedPointTo (Spec.map χ ≫ hV.fromSpec) = χ := by
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc]
  rw [IsAffineOpen.fromSpec_app_self, Category.assoc]
  erw [TopCat.Presheaf.germ_res_assoc]
  erw [Scheme.germ_stalkClosedPointTo_Spec]
  simp

theorem isUnit_res_of_forall_point {X : Scheme.{0}} (s : X ⟶ Sp ℂ) [LocallyOfFiniteType s] {U V : X.Opens}
    (hV : IsAffineOpen V) (hVU : V ≤ U) (a : Γ(X, U))
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) :
    IsUnit (X.presheaf.map (homOfLE hVU).op a) := by
  by_contra hr
  let φ : CommRingCat.of ℂ ⟶ Γ(X, V) :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ s.appLE ⊤ V (fun _ _ => trivial)
  letI : Algebra ℂ Γ(X, V) := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, V) := by
    have h1 : (s.appLE ⊤ V (fun _ _ => trivial)).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ _
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2
    exact h1.comp h2
  obtain ⟨χ, hχ⟩ := exists_algHom_eq_zero_of_not_isUnit (X.presheaf.map (homOfLE hVU).op a) hr
  let χ' : Γ(X, V) ⟶ CommRingCat.of ℂ := CommRingCat.ofHom χ.toRingHom
  let x : Sp ℂ ⟶ X := Spec.map χ' ≫ hV.fromSpec
  have hxs : x ≫ s = 𝟙 _ := by
    have hc : φ ≫ χ' = 𝟙 _ := by
      ext z
      exact χ.commutes z
    simp only [x, Category.assoc, fromSpec_comp_structure s hV]
    rw [← Spec.map_comp]
    exact (congrArg Spec.map hc).trans (Spec.map_id _)
  have hxV : (Spec.map χ' ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈ V := by
    have hr' : (Spec.map χ' ≫ hV.fromSpec) (IsLocalRing.closedPoint (CommRingCat.of ℂ)) ∈
        Set.range hV.fromSpec := ⟨_, rfl⟩
    rwa [hV.range_fromSpec] at hr'
  have hxU : centre x ∈ U := hVU hxV
  apply h x hxs hxU
  rw [← val_germ x U hxU a]
  have e1 := congrArg (fun f => f.hom (X.presheaf.map (homOfLE hVU).op a)) (germ_comp_stalkClosedPointTo_eq hV χ' hxV)
  have e2 := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) _ hxV a
  simp only [CommRingCat.comp_apply] at e1
  erw [← e2]
  exact e1.trans hχ

theorem isUnit_of_forall_complexPoint (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (U : X.Opens) (a : Γ(X, U))
    (hs : LocallyOfFiniteType s)
    (h : ∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X.toRingedSpace U a fun p hp => ?_
  obtain ⟨V, hV, hpV, hVU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hp
  haveI := hs
  have hu := isUnit_res_of_forall_point s hV hVU a h
  have e := TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hVU) p hpV a
  have := hu.map (X.presheaf.germ V p hpV).hom
  rw [e] at this
  exact this

end GlobalTheory.CompanionTheory.Ar.Flat.GagaC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerBasisAdjoinInverse
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

theorem differentials_basis_invAdj : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : Subalgebra ℚ Ω) (g : Ω), g ∈ A → g ≠ 0 → ∀ (e : ℕ) (z : Fin e → A) (z' : Fin e → Mdl.invAdj A g), (∀ i, (z' i : Ω) = z i) → LinearIndependent A (fun i => KaehlerDifferential.D ℚ A (z i)) → Submodule.span A (Set.range fun i => KaehlerDifferential.D ℚ A (z i)) = ⊤ → LinearIndependent (Mdl.invAdj A g) (fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) ∧ Submodule.span (Mdl.invAdj A g) (Set.range fun i => KaehlerDifferential.D ℚ (Mdl.invAdj A g) (z' i)) = ⊤ := by
  intro Ω _ _ A g hg hg0 e z z' hz hli hsp
  have hAB : A ≤ Mdl.invAdj A g := fun x hx =>
    show x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)
  have hginv : g⁻¹ ∈ Mdl.invAdj A g :=
    show g⁻¹ ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) from
      Algebra.subset_adjoin (Set.mem_insert _ _)
  have hden : ∀ x ∈ Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)), ∃ n : ℕ, x * g ^ n ∈ A := by
    let S : Subalgebra ℚ Ω :=
      { carrier := {x | ∃ n : ℕ, x * g ^ n ∈ A}
        mul_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show x * y * g ^ (n + m) = (x * g ^ n) * (y * g ^ m) by ring]
          exact A.mul_mem hn hm
        one_mem' := ⟨0, by simpa using A.one_mem⟩
        add_mem' := by
          rintro x y ⟨n, hn⟩ ⟨m, hm⟩
          refine ⟨n + m, ?_⟩
          rw [show (x + y) * g ^ (n + m) = (x * g ^ n) * g ^ m + (y * g ^ m) * g ^ n by ring]
          exact A.add_mem (A.mul_mem hn (A.pow_mem hg m)) (A.mul_mem hm (A.pow_mem hg n))
        zero_mem' := ⟨0, by simpa using A.zero_mem⟩
        algebraMap_mem' := fun r => ⟨0, by simpa using A.algebraMap_mem r⟩ }
    have hle : Algebra.adjoin ℚ (insert g⁻¹ (A : Set Ω)) ≤ S := by
      refine Algebra.adjoin_le ?_
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hg0]; exact A.one_mem⟩
      · exact ⟨0, by simpa using hx⟩
    exact fun x hx => hle hx
  letI : Algebra A (Mdl.invAdj A g) := (Subalgebra.inclusion hAB).toRingHom.toAlgebra
  have hinc : ∀ a : A, ((algebraMap A (Mdl.invAdj A g) a : Mdl.invAdj A g) : Ω) = a := fun _ => rfl
  haveI : IsScalarTower ℚ A (Mdl.invAdj A g) :=
    IsScalarTower.of_algebraMap_eq (fun _ => Subtype.ext rfl)
  let g' : A := ⟨g, hg⟩
  haveI : IsLocalization (Submonoid.powers g') (Mdl.invAdj A g) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨y, n, rfl⟩
      have hu : IsUnit (algebraMap A (Mdl.invAdj A g) g') :=
        isUnit_iff_exists_inv.mpr ⟨⟨g⁻¹, hginv⟩, Subtype.ext (by
          show g * g⁻¹ = 1
          exact mul_inv_cancel₀ hg0)⟩
      show IsUnit (algebraMap A (Mdl.invAdj A g) (g' ^ n))
      rw [map_pow]
      exact hu.pow n
    · intro b
      obtain ⟨n, hn⟩ := hden b b.2
      refine ⟨(⟨(b : Ω) * g ^ n, hn⟩, ⟨g' ^ n, n, rfl⟩), ?_⟩
      apply Subtype.ext
      show (b : Ω) * ((g' ^ n : A) : Ω) = (b : Ω) * g ^ n
      simp only [SubmonoidClass.coe_pow]
      rfl
    · intro x y h
      refine ⟨1, ?_⟩
      have hxy : x = y := Subtype.ext (by simpa [hinc] using congrArg Subtype.val h)
      rw [hxy]
  haveI : Algebra.FormallyEtale A (Mdl.invAdj A g) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers g')
  have hzz : ∀ i, algebraMap A (Mdl.invAdj A g) (z i) = z' i := fun i =>
    Subtype.ext ((hinc (z i)).trans (hz i).symm)
  have key := GlobalTheory.CompanionTheory.Ar.SncRes.coords_of_formallyEtale (S := ↥(Mdl.invAdj A g)) z hli hsp
  simp only [hzz] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_finite_projective : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Module.Finite R E ∧ Module.Projective R E :=
  PositivityTheory.HtPt.Htat.lie_fin

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChange
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lieModel_isBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M : LieModel G x E) (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') (j : E →ₗ[R] E'), (∀ e, ((M'.pt (j e)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap R R')) ≫ (M.pt e).left)) → IsBaseChange R' j := by
  intro S G _ _ R R' _ _ _ x E _ _ E' _ _ _ _ M M' j hj
  refine (_root_.GlobalTheory.CompanionTheory.Ar.LieProj.lie_finite_projective_baseChange S G R x E M).2.2 R' E' M' j fun e => ?_
  have h := hj e
  change _ ≫ _ = _ ≫ _ at h
  rw [Category.comp_id] at h
  exact h

end GlobalTheory.CompanionTheory.Ar
end

