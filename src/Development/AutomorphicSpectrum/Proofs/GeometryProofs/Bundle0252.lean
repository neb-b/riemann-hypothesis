module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0058
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0250
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyHodgePrimeDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0025
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0147
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineChartBundleSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0119
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0150
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0178
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0251

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyModelPrimeBound
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamLat

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isLocalRing_regAt (q : Cpt ξ) : IsLocalRing (regAt ξ q) :=
  IsLocalRing.of_surjective' (genMap ξ q).rangeRestrict (genMap ξ q).rangeRestrict_surjective

theorem coordLat_locFree (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) (c : ∀ k, J k) (hc : mseg y c ≠ 0) :
    LocFree (chartRing O (mseg y) c) r (coordLat O y L b c) ∧ ∀ g ∈ chartRing O (mseg y) c, ∀ e : Fin r → Ω,
      (∀ q : Cpt ξ, InChart ξ (mseg y) c q → (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → g ≠ 0 → g⁻¹ ∈ regAt ξ q →
        Fintype.linearCombination Ω b e ∈ L q) → ∃ n : ℕ, g ^ n • e ∈ coordLat O y L b c := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.chart_points_over_place X Ω ξ K J y hT A hA m O c hc
  let Q : Type := {q : Cpt ξ // InChart ξ (mseg y) c q ∧ ∀ o : O, algebraMap O Ω o ∈ regAt ξ q}
  let Λ : Q → AddSubgroup (Fin r → Ω) := fun q =>
    (L q.1).toAddSubgroup.comap (Fintype.linearCombination Ω b).toAddMonoidHom
  have hcoord : coordLat O y L b c = ⨅ q, Λ q := by
    ext e
    simp only [coordLat, AddSubgroup.mem_iInf, Subtype.forall, Λ, Q]
    exact ⟨fun h q hq => h q hq.1 hq.2, fun h q h1 h2 => h q ⟨h1, h2⟩⟩
  have hinj : Function.Injective (Fintype.linearCombination Ω b) :=
    hli.fintypeLinearCombination_injective
  have hfr : ∀ q : Q, ∃ g ∈ chartRing O (mseg y) c, g ≠ 0 ∧ g⁻¹ ∈ regAt ξ q.1 ∧
      ∃ f : Fin r → (Fin r → Ω), LinearIndependent Ω f ∧ ∀ q' : Q, g⁻¹ ∈ regAt ξ q'.1 → ∀ e, e ∈ Λ q' ↔
        ∃ a : Fin r → Ω, (∀ i, a i ∈ regAt ξ q'.1) ∧ e = ∑ i, a i • f i := by
    intro q
    obtain ⟨U, hU, f, hfs, hf⟩ := hVB q.1 q.2.2
    obtain ⟨g, hg, hgu, hgU⟩ := h4 q.1 q.2.1 q.2.2 U hU
    have hmem : ∀ i, ∃ f' : Fin r → Ω, Fintype.linearCombination Ω b f' = f i := by
      intro i
      have : f i ∈ Submodule.span Ω (Set.range b) := by
        rw [hsp, ← hfs]; exact Submodule.subset_span ⟨i, rfl⟩
      obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
      exact ⟨a, by rw [Fintype.linearCombination_apply]; exact ha⟩
    choose f' hf' using hmem
    refine ⟨g, hg, hgu.1, hgu.2.2, f', ?_, fun q' hq' e => ?_⟩
    · have hl := (hf q.1 q.2.2 hU).1
      have : (Fintype.linearCombination Ω b) ∘ f' = f := funext hf'
      rw [← this] at hl
      exact hl.of_comp _
    · have hu : unitAt ξ q'.1 g := ⟨hgu.1, h1 g hg q'.1 q'.2.1 q'.2.2, hq'⟩
      have hq'U := hgU q'.1 q'.2.1 q'.2.2 hu
      have hfrm := (hf q'.1 q'.2.2 hq'U).2
      show Fintype.linearCombination Ω b e ∈ L q'.1 ↔ _
      rw [hfrm]
      constructor
      · intro he
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).1 he
        refine ⟨fun i => (a i : Ω), fun i => (a i).2, hinj ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← ha, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
      · rintro ⟨a, ha, rfl⟩
        refine (Submodule.mem_span_range_iff_exists_fun (regAt ξ q'.1)).2 ⟨fun i => ⟨a i, ha i⟩, ?_⟩
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, hf']
        rfl
  have key := _root_.GlobalTheory.CompanionTheory.Ar.Num.SecAlg.locFree_and_extend (chartRing O (mseg y) c) Q (fun q => regAt ξ q.1) r Λ (fun q => isLocalRing_regAt q.1)
    (fun q a ha => h1 a ha q.1 q.2.1 q.2.2)
    (fun P hP => by
      obtain ⟨q, hq1, hq2, hq⟩ := h2 P hP
      refine ⟨⟨q, hq1, hq2⟩, fun s => ?_⟩
      rw [hq s]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h1 _ s.2 q hq1 hq2, h.2⟩⟩)
    (fun q a ha => by
      obtain ⟨s, hs, hu, hsa⟩ := h3 q.1 q.2.1 q.2.2 a ha
      exact ⟨s, hs, hu.1, hu.2.2, hsa⟩)
    hfr
  rw [hcoord]
  refine ⟨key.1, fun g hg e he => key.2 g hg e fun q h h' => ?_⟩
  exact he q.1 q.2.1 q.2.2 h h'

theorem coordLat_family (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K]
    [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (hT : CoordTie ℤ ξ (mseg y)) (A : Type)
    [CommRing A] [Algebra A Ω] (hA : HasConstants ℤ A y) (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω]
    (V : Type) [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (r : ℕ) (Vg : Submodule Ω V) (b : Fin r → V)
    (hli : LinearIndependent Ω b) (hsp : Submodule.span Ω (Set.range b) = Vg)
    (hVB : L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt ξ q} r Vg) :
    IsLatFamily O y (coordLat O y L b) := by
  have key := coordLat_locFree X Ω ξ K J y hT A hA m O V L r Vg b hli hsp hVB
  refine ⟨fun s hs a ha v hv => (key s hs).1.1 a ha v hv, fun s t hs ht v hv => ?_⟩
  have hg : mseg y s / mseg y t ∈ chartRing O (mseg y) t := Algebra.subset_adjoin ⟨s, rfl⟩
  refine (key t ht).2 _ hg v fun q hq hO hg0 hgi => ?_
  have hqs : InChart ξ (mseg y) s q := by
    refine ⟨hs, fun c' => ?_⟩
    have e : mseg y c' / mseg y s = mseg y c' / mseg y t * (mseg y s / mseg y t)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hq.2 c') hgi
  have := (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hqs) hO)
  exact this

theorem coordLat_mono {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → L q ≤ L' q) :
    coordLat O y L b c ≤ coordLat O y L' b c := by
  intro v hv
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  exact h q hO (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)

theorem coordLat_le_divLat {O : Type} [CommRing O] [Algebra O Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) {V : Type} [AddCommGroup V] [Module Ω V] {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V)
    (c : ∀ k, J k) (a : Ω) (h : ∀ q : Cpt ξ, (∀ o : O, algebraMap O Ω o ∈ regAt ξ q) → ∀ e ∈ L' q, a • e ∈ L q) :
    coordLat O y L' b c ≤ divLat a (coordLat O y L b c) := by
  intro v hv
  show a • v ∈ coordLat O y L b c
  refine AddSubgroup.mem_iInf.2 fun q => AddSubgroup.mem_iInf.2 fun hq => AddSubgroup.mem_iInf.2 fun hO => ?_
  have := h q hO _ (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv q) hq) hO)
  show Fintype.linearCombination Ω b (a • v) ∈ L q
  rw [map_smul]
  exact this

theorem mem_dotDual' {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} (L : AddSubgroup (Fin n → Ω))
    (v : Fin n → Ω) : v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf]
  rfl

theorem dotDual_anti {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ} {L L' : AddSubgroup (Fin n → Ω)}
    (h : L ≤ L') : dotDual R L' ≤ dotDual R L := fun v hv =>
  (mem_dotDual' R L v).2 fun l hl => (mem_dotDual' R L' v).1 hv l (h hl)

theorem dotDual_le_divLat {o : Type} [CommRing o] [Algebra o Ω] (R : Subalgebra o Ω) {n : ℕ}
    {L L' : AddSubgroup (Fin n → Ω)} (a : Ω) (h : L' ≤ divLat a L) : dotDual R L ≤ divLat a (dotDual R L') := by
  intro v hv
  show a • v ∈ dotDual R L'
  refine (mem_dotDual' R L' _).2 fun l hl => ?_
  have h2 := (mem_dotDual' R L v).1 hv _ (show a • l ∈ L from h hl)
  rwa [dotProduct_smul, ← smul_dotProduct]

theorem unit_of_place {A : Type} [CommRing A] [Algebra A Ω] {m : Ideal A} [m.IsPrime] {O : Type} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] {p : ℕ} (hpm : (p : A) ∈ m) (hp : p.Prime) {q : Cpt ξ}
    (hO : ∀ o : O, algebraMap O Ω o ∈ regAt ξ q) : q ∈ overPrime ξ p := by
  intro r hr hrp hf
  have hco : IsCoprime (r : ℤ) (p : ℤ) := by
    exact Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hr hp).2 hrp)
  obtain ⟨a, b, hab⟩ := hco
  have hpO : (p : O) ∈ IsLocalRing.maximalIdeal O := by
    have := (IsLocalization.AtPrime.to_map_mem_maximal_iff O m (p : A)).2 hpm
    simpa using this
  have hrO : IsUnit (r : O) := by
    by_contra hn
    have hr' : (r : O) ∈ IsLocalRing.maximalIdeal O := hn
    have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : (1 : O) = (a : O) * (r : O) + (b : O) * (p : O) := by
        have := congrArg (Int.cast : ℤ → O) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hr') (Ideal.mul_mem_left _ _ hpO)
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal O).ne_top this
  obtain ⟨u, hu⟩ := hrO.exists_right_inv
  have hu' : (r : Ω) * algebraMap O Ω u = 1 := by
    have := congrArg (algebraMap O Ω) hu
    simpa using this
  have hr0 : (r : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hu'
  refine hf ⟨hr0, natCast_mem _ r, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hu']
  exact hO u

theorem lat_main : GlobalTheory.CompanionTheory.Ar.HT.FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ w : O, HT.IsCp p (algebraMap O Ω w) → ∀ t : CMType H ⊕ CMType H, IsLatFamily O y (fun c' => coordLat O y (𝔐.dR t) (b t) c') ∧ IsLatFamily O y (fun c' => coordLat O y (𝔐.HT p t) (b t) c') ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ IsLatFamily O y (fun c' => dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ ∀ c' : ∀ k, J k, mseg y c' ≠ 0 → LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c')) ∧ LocFree (CR O y c') (labelRk D t) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) ∧ coordLat O y (𝔐.dR t) (b t) c' ≤ coordLat O y (𝔐.HT p t) (b t) c' ∧ coordLat O y (𝔐.HT p t) (b t) c' ≤ divLat (algebraMap O Ω w) (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c') ≤ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ∧ dotDual (CR O y c') (coordLat O y (𝔐.dR t) (b t) c') ≤ divLat (algebraMap O Ω w) (dotDual (CR O y c') (coordLat O y (𝔐.HT p t) (b t) c')) := by
  intro hF E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hvar hpq p _ hpS hfree hp2 hdisc b hb A _ _ _ m _ hpm O _ _ _ _
    _ _ _ w hw t
  have hpp : p.Prime := Fact.out
  have hG : Nonempty (GenTors 𝔐 p) := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.nonempty_genTors E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar hpq p hpS hfree hp2 hdisc
  obtain ⟨κ, hκ, hS⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.ModelSandwich.sandwich_of_htFree hF E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hpq hfree
  obtain ⟨-, -, -, hcon, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hvar A
  have hE := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.htLattice_eq_dR_of_charZero E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hG hdisc
  obtain ⟨hV1, hV2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.hodgeLattices_isVBOn_overPrime E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hdisc hE t
  have hT : CoordTie ℤ 𝔐.ξ (mseg y) := 𝔐.tie
  have hO : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → q ∈ overPrime 𝔐.ξ p :=
    fun q h => unit_of_place (A := A) (m := m) (O := O) hpm hpp h
  have hres : ∀ (L : Lat 𝔐.ξ 𝔐.Li), L.IsVBOn (overPrime 𝔐.ξ p) (labelRk D t) (𝔐.Vgen t) →
      L.IsVBOn {q | ∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q} (labelRk D t) (𝔐.Vgen t) := by
    intro L hL q hq
    obtain ⟨U, hU, f, hf, hfr⟩ := hL q (hO q hq)
    exact ⟨U, hU, f, hf, fun q' hq' hq'U => hfr q' (hO q' hq') hq'U⟩
  have hdF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1)
  have hhF := coordLat_family _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2)
  have hdL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.dR t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.dR t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV1) c' hc').1
  have hhL : ∀ c', mseg y c' ≠ 0 → LocFree (chartRing O (mseg y) c') (labelRk D t) (coordLat O y (𝔐.HT p t) (b t) c') :=
    fun c' hc' => (coordLat_locFree _ Ω 𝔐.ξ K J y hT A hcon m O _ (𝔐.HT p t) _ _ (b t) (hb t).1 (hb t).2 (hres _ hV2) c' hc').1
  obtain ⟨hdD, hdDL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily O Ω K J y _ _ hdF hdL
  obtain ⟨hhD, hhDL⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.dotDual_latFamily O Ω K J y _ _ hhF hhL
  have hpt : ∀ q : Cpt 𝔐.ξ, (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) →
      𝔐.dR t q ≤ 𝔐.HT p t q ∧ ∀ e ∈ 𝔐.HT p t q, algebraMap O Ω w • e ∈ 𝔐.dR t q := by
    intro q hq
    by_cases hf : InFibre 𝔐.ξ p q
    · exact _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.SandPt.sandwich_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 p hpS hp2 hdisc κ _ hκ hw hS q hf (hq w) t
    · have hall : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q := fun r hr => by
        by_cases hrp : r = p
        · exact hrp ▸ hf
        · exact hO q hq r hr hrp
      rw [hE t q hall]
      exact ⟨le_rfl, fun e he => (𝔐.dR t q).smul_mem (⟨_, hq w⟩ : regAt 𝔐.ξ q) he⟩
  refine ⟨hdF, hhF, hdD, hhD, fun c' hc' => ⟨hdL c' hc', hhL c' hc', hdDL c' hc', hhDL c' hc', ?_, ?_, ?_, ?_⟩⟩
  · exact coordLat_mono y (b t) c' fun q hq => (hpt q hq).1
  · exact coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2
  · exact dotDual_anti _ (coordLat_mono y (b t) c' fun q hq => (hpt q hq).1)
  · exact dotDual_le_divLat _ _ (coordLat_le_divLat y (b t) c' _ fun q hq => (hpt q hq).2)

end GlobalTheory.CompanionTheory.Ar.Num.FamLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_intersection_height : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (B : ℕ) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ Or.𝔐.X) (P : AbPart Or.𝔐.t (spMap (algebraMap (𝓞 L) L) ≫ z)) (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (MV : LieModel P.tK.G (𝟙 (Sp L)) V) (A : LinPt E L (CMType H) V) (w : (Σ k, J k) → L) (r k : ℕ) (v : Fin r → V) (q : CMType H → Fin k → A.Λ), Or.Good → CoordsAt Or.𝔐.ξ Dc.y (spMap (algebraMap (𝓞 L) L) ≫ z) w → Or.𝔐.IsLinPtOf z P MV A → IsOFamily A.ρ A.I v → (∀ τ, A.IsAdapted (Or.sm τ) v (q τ) ∧ ∀ i, (q τ i : V) ∈ A.eig (Or.sm τ)) → ∃ x : (L →+* ℂ) → ℝ, (∀ e : L →+* ℂ, Or.PhiWeight (spMap e ≫ spMap (algebraMap (𝓞 L) L) ≫ z) (fun p => e (w p)) (x e)) ∧ Ht.ptHt (fun k => (muTwDeg Hd B k : ℝ)) (twW (D := Dc) B fun _ => 0) L w + (∑ e : L →+* ℂ, x e) / Module.finrank ℚ L = -A.phiDeg Or.sm (fun τ => Or.𝔐.FibLat (Or.𝔐.VS (S₀ ∪ Dc.SB B) (Or.sm τ)) z P MV) v q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height | exact GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.g_height <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompare
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_vecs {S : Scheme.{0}} {G : Over S} {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ S) (f : R →+* R')
    (y : Sp R' ⟶ S) (hy : y = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    ∃ u' : Fin n → (epsAt y ⟶ G), ∀ i, (u' i).left = spMap (dualMap f) ≫ (u i).left :=
  ⟨fun i => LieCarrier.epsHom f x y hy.symm ≫ u i, fun i => rfl⟩

theorem extendsUnitAt_resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ b₂ X' π s' d ξ' W' W jW F hβ hpq hτ hσ hΦ hb₁ hs₁ hb₂ hs₂ hπ hsm hsnc hξ hgen hj hjs hWW' hF hgen1 x h hx
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' (Z.ξ₀ ≫ Y.j) π (RingHom.id Z.Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) = 𝟙 _ := Spec.map_id _
    show ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    rw [hξ, e, Category.id_comp]
  obtain ⟨hp, -, hpull⟩ := pull_reg_and_gen _ _ _ _ _ _ π _ hd ⟨centre x, h⟩
  let p₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨π (centre x), hp⟩
  have hp₀ : p₀ ∈ Z.genFib := ⟨pullback.lift π s' hπ (centre x), by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  obtain ⟨hVB₁, hVB₂, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨A, hA, EB, _, _, MB, e₁, e₂, v₁, v₂, hp₀A, hfr, heig, hval⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Flat.LocalFrames.exists_affine_eigenframes E H D l Xo c O β Y U Z τ σ b₁ b₂ p₀ hβ hτ hb₁ hs₁ hb₂ hs₂ hp₀
  obtain ⟨hv₁, hv₂⟩ := hfr p₀ hp₀A
  obtain ⟨α, κ, hα, hκ, hαe, hκe, hgen0⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div _ _ _ _ (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q _ _ Z.genFib
    b₁ v₁ b₂ v₂ p₀ hp₀ hVB₁ hVB₂ hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  refine ⟨α / κ, hpull _ _ hgen0, ?_⟩
  intro m B y hB hy hyσ b₀ hb₀ hyx
  have hxA : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) := fun q _ => by
    have : q = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hp₀A
  obtain ⟨ε, hh, hε, hdiff, hne, key⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.flat_unit_along_families E H D l Xo c O β Y τ σ Φ X' π s' d W' jW A hA EB MB e₁ e₂ x hpq hτ hσ hΦ hπ hsm hsnc hj hjs hx hxA heig m B y hB hy hyσ b₀ hb₀ hyx
  refine ⟨ε, hh, hε, hdiff, hne, fun b hbB hbW r hr => ?_⟩
  obtain ⟨f, hf, hk⟩ := key b hbB
  have hc : genPt ξ' ⤳ centre (y b) := hr.choose
  have hW' : ⊤ ≤ y b ⁻¹ᵁ W' := fun q hq => hWW' (hbW hq)
  have hrange : Set.range (y b) ⊆ Set.range W'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact hW' (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let y₀ : Sp ℂ ⟶ W'.toScheme := IsOpenImmersion.lift W'.ι (y b) hrange
  have e₀ : y₀ ≫ W'.ι = y b := IsOpenImmersion.lift_fac _ _ _
  let yy : Sp ℂ ⟶ Xo.XF c := y₀ ≫ jW
  have hyj : yy ≫ Y.j = y b ≫ π := by
    show (y₀ ≫ jW) ≫ Y.j = _
    rw [Category.assoc, hj, ← Category.assoc, e₀]
  have hys : yy ≫ pullback.snd _ _ = spMap σ := by
    show (y₀ ≫ jW) ≫ _ = _
    rw [Category.assoc, hjs, ← Category.assoc, e₀, hyσ b hbB.1]
  obtain ⟨v, w, hfrvw, ⟨hvv, hww⟩, hFe⟩ := hF (y b) yy (hyσ b hbB.1) hbW hc hyj hys
  have hyf : yy ≫ Y.j = spMap f ≫ hA.fromSpec := hyj.trans hf.symm
  obtain ⟨u₁, hu₁⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₁ i))
  obtain ⟨u₂, hu₂⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₂ i))
  have hover : (yy ≫ Y.j) ≫ Y.s = spMap (σ.comp β) := by
    rw [hyj, Category.assoc, hπ, ← Category.assoc, hyσ b hbB.1, ← Spec.map_comp]
    rfl
  obtain ⟨hE₁, hE₂⟩ := heig f (yy ≫ Y.j) u₁ u₂ hyf hover hu₁ hu₂
  have hspec : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    have e : centre (yy ≫ Y.j) = π (centre (y b)) := by
      rw [hyj]; rfl
    rw [e, ← RegAtDom.map_genPt hd]
    exact hc.map π.continuous
  obtain ⟨hV₁, hV₂⟩ := hval f (yy ≫ Y.j) u₁ u₂ hyf hspec hu₁ hu₂
  choose a₁ ha₁ using fun i => exists_sameVec_left Y yy (u₁ i)
  choose a₂ ha₂ using fun i => exists_sameVec_left Y yy (u₂ i)
  have hfr₀ : IsFramed Set.univ τ σ yy a₁ a₂ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model E H D l Xo c O β Y τ σ yy a₁ a₂ u₁ u₂ hys ha₁ ha₂ hE₁ hE₂
  have h₁ := (hk hW') yy a₁ a₂ u₁ u₂ hyj hys ha₁ ha₂ hu₁ hu₂
  have hqA : ∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → q.1 ∈ A := fun q hq => by
    rw [hq, hyf, ← SetLike.mem_coe, ← hA.range_fromSpec]
    exact ⟨_, rfl⟩
  have h₂ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare E H D l Xo c O β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' (y b) yy v a₁ w a₂ α κ r hξ hgen hyj hΦ hfrvw hfr₀ hvv hww
    (fun i => ⟨_, hV₁ i, ha₁ i⟩) (fun j => ⟨_, hV₂ j, ha₂ j⟩) (fun q hq => hfr q (hqA q hq))
    (fun i => hs₁ ▸ Submodule.subset_span ⟨i, rfl⟩) (fun j => hs₂ ▸ Submodule.subset_span ⟨j, rfl⟩)
    hα hκ hαe hκe hr
  rw [hFe, h₂, h₁]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgField

theorem exists_compositum (κ Ω₁ Ω' : Type) [Field κ] [Field Ω₁] [Field Ω'] (i₁ : κ →+* Ω₁) (i₂ : κ →+* Ω')
    (h : i₂.Finite) :
    ∃ (Ω : Type) (_ : Field Ω) (a : Ω₁ →+* Ω) (b : Ω' →+* Ω), a.Finite ∧ a.comp i₁ = b.comp i₂ := by
  letI := i₁.toAlgebra
  letI := i₂.toAlgebra
  haveI : Module.Finite κ Ω' := h
  haveI : Module.Finite Ω₁ (TensorProduct κ Ω₁ Ω') := inferInstance
  haveI : Nontrivial (TensorProduct κ Ω₁ Ω') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct κ Ω₁ Ω')
  let q := Ideal.Quotient.mk m
  refine ⟨TensorProduct κ Ω₁ Ω' ⧸ m, Ideal.Quotient.field m,
    q.comp (algebraMap Ω₁ (TensorProduct κ Ω₁ Ω')),
    q.comp (Algebra.TensorProduct.includeRight : Ω' →ₐ[κ] TensorProduct κ Ω₁ Ω').toRingHom, ?_, ?_⟩
  · exact RingHom.Finite.comp (RingHom.Finite.of_surjective q Ideal.Quotient.mk_surjective)
      (RingHom.finite_algebraMap.2 inferInstance)
  · ext x
    have e : algebraMap Ω₁ (TensorProduct κ Ω₁ Ω') (i₁ x) = (1 : Ω₁) ⊗ₜ[κ] (i₂ x) := by
      have h1 : i₁ x = x • (1 : Ω₁) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
      have h2 : i₂ x = x • (1 : Ω') := by rw [Algebra.smul_def, _root_.mul_one]; rfl
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h1, h2,
        TensorProduct.smul_tmul]
    simp only [RingHom.comp_apply]
    rw [e]
    rfl

theorem exists_root (K : Type) [Field K] [CharZero K] (N : ℕ) (hN : N ≠ 0) :
    ∃ (L : Type) (_ : Field L) (j : K →+* L), j.Finite ∧ ∃ ζ : L, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN⟩
  haveI : NeZero ((N : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hN⟩
  haveI : Module.Finite K (CyclotomicField N K) := by
    first
      | exact IsCyclotomicExtension.finiteDimensional {N} K _
      | exact IsCyclotomicExtension.finite {N} K _
      | exact Polynomial.IsSplittingField.finiteDimensional _ (Polynomial.cyclotomic N K)
  exact ⟨CyclotomicField N K, inferInstance, algebraMap _ _, RingHom.finite_algebraMap.2 inferInstance,
    IsCyclotomicExtension.zeta N K _, IsCyclotomicExtension.zeta_spec N K _⟩

theorem fullTorsion_ext {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (j : Ω →+* Ω') {n : ℕ} (hf : FullTorsion G ξ n) :
    FullTorsion G (spMap j ≫ ξ) n := by
  intro k _ i g hg
  have hs : spMap (i.comp j) = spMap i ≫ spMap j := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : spMap i ≫ spMap j ≫ ξ = spMap (i.comp j) ≫ ξ := by
    rw [hs, Category.assoc]
  revert g
  rw [e]
  intro g hg
  obtain ⟨x, hx⟩ := hf k (i.comp j) g hg
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  refine ⟨Over.homMk (spMap j ≫ x.left) ?_, ?_⟩
  · simp only [Over.mk_hom, Category.assoc, hxw]
  · show g.left = spMap i ≫ spMap j ≫ x.left
    rw [hx, hs]
    exact Category.assoc _ _ _

theorem exists_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : X)
    (h : genPt ξ = e) : ∃ i : X.residueField e →+* Ω, ξ = spMap i ≫ X.fromSpecResidueField e := by
  subst h
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ξ)).hom,
    ((Scheme.SpecToEquivOfField Ω X).left_inv ξ).symm⟩

theorem exists_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₁ : Type) [Field Ω₁] [CharZero Ω₁] (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ Y.X) (S : Finset ℕ), GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (i : Ω₁ →+* Ω), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) ∧ (∀ p ∈ S, FullTorsion Y.t.G (spMap i ≫ ξ₁) (p ^ 4)) ∧ ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4) := by
  intro E _ _ _ H D l Xo c Y Ω₁ _ _ ξ₁ S he hS
  have hN0 : (∏ p ∈ S, p ^ 4) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  obtain ⟨Ω', _, _, n, x, M, f, y, t, m, z, ev, -, hfin, hfe, -, -, htor, -⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.XR.levelCover E H D l Xo c Y _ he (∏ p ∈ S, p ^ 4) (Nat.one_le_iff_ne_zero.2 hN0)
  haveI := hfin
  obtain ⟨i₁, h₁⟩ := exists_factor ξ₁ _ rfl
  obtain ⟨i₂, h₂⟩ := exists_factor (M.ξ ≫ f) (genPt ξ₁) (by
    rw [← hfe]
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Ar.genPt])
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates M.ξ (Y.X.fromSpecResidueField (genPt ξ₁)) f i₂ := h₂
  have hi₂ : i₂.Finite := HodgeExists.finite_of_dominates M.tie.gen f hdom
  obtain ⟨Ω₂, _, a, b, ha, hab⟩ := exists_compositum _ Ω₁ Ω' i₁ i₂ hi₂
  haveI : CharZero Ω₂ := charZero_of_injective_ringHom a.injective
  obtain ⟨Ω, _, j, hj, ζ, hζ⟩ := exists_root Ω₂ _ hN0
  haveI : CharZero Ω := charZero_of_injective_ringHom j.injective
  have hsp : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (u : R →+* R') (v : R' →+* R''),
      spMap (v.comp u) = spMap v ≫ spMap u := by
    intro R R' R'' _ _ _ u v
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hpt : spMap (j.comp a) ≫ ξ₁ = spMap (j.comp b) ≫ M.ξ ≫ f := by
    rw [h₂]
    conv_lhs => rw [h₁]
    rw [← Category.assoc, ← Category.assoc, ← hsp, ← hsp, RingHom.comp_assoc, RingHom.comp_assoc, hab]
  have hdvd : ∀ p ∈ S, p ^ 4 ∣ ∏ p ∈ S, p ^ 4 := fun p hp => Finset.dvd_prod_of_mem (fun p => p ^ 4) hp
  refine ⟨Ω, inferInstance, inferInstance, j.comp a, RingHom.Finite.comp hj ha, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hpt]
    exact fullTorsion_ext (j.comp b) (HodgeExists.fullTorsion_push m.cart (hdvd p hp) htor)
  · obtain ⟨d, hd⟩ := hdvd p hp
    exact ⟨ζ ^ d, hζ.pow (Nat.pos_of_ne_zero hN0) (by rw [hd, mul_comm])⟩

end GlobalTheory.CompanionTheory.Ar.ChgField
end
end

