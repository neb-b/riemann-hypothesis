module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0033
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0032
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.Bundle0003
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0030
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AugmentationLengthsExistStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.augmentation_lengths_exist : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) → ∀ AA : HopfOrder (C := C) R N, ∃ cA cN cO : NNReal, cA ≠ 0 ∧ cN ≠ 0 ∧ cO ≠ 0 ∧ HasLen v R (AFQuot p AA.carrier) cA ∧ HasColen R v AA.carrier cN ∧ HasLen v R (OmAA AA.carrier) cO := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.lens_exist | exact GlobalTheory.CompanionTheory.Ar.GR.lens_exist | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.lens_exist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartRingsNoetherianFraction
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

theorem isNoetherianRing_chartRing {O Ω σ : Type} [CommRing O] [IsNoetherianRing O] [Field Ω] [Algebra O Ω]
    [Finite σ] (y : σ → Ω) (c : σ) : IsNoetherianRing (chartRing O y c) := by
  have hfg : (chartRing O y c).FG := ⟨(Set.finite_range _).toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩
  have : Algebra.FiniteType O (chartRing O y c) := (Subalgebra.fg_iff_finiteType _).1 hfg
  exact Algebra.FiniteType.isNoetherianRing O _

variable {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

theorem fnField_le_closure [DecidableEq K] [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hr : ∀ (k : K) (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ chartRing O (mseg x) c := fun k i => by
    rw [PositivityTheory.HtPt.Hcptgen.ratio_eq x c hc k i]
    exact div_mem_chartRing _ _ _
  refine (Subfield.closure_le).2 ?_
  rintro _ (⟨r, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure ((chartRing O (mseg x) c).algebraMap_mem r)
  · have hk : x ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
    have e : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) :=
      (div_div_div_cancel_right₀ hk _ _).symm
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [e]
    exact div_mem (Subfield.subset_closure (hr k i)) (Subfield.subset_closure (hr k j))

theorem isFractionRing_of_closure_eq_top (A : Subalgebra O Ω)
    (h : Subfield.closure (A : Set Ω) = ⊤) : IsFractionRing A Ω := by
  refine IsFractionRing.of_field A Ω fun z => ?_
  have hz : z ∈ Subfield.closure (A : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have hs : Subring.closure (A : Set Ω) = A.toSubring := by
    have := Subring.closure_eq A.toSubring
    simpa using this
  rw [hs] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

variable {K' : Type} [Fintype K'] {ι' : K' → Type}

theorem mseg_joinCoord [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) s = mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
  unfold mseg
  rw [Fintype.prod_sum_type]
  rfl

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)


omit [Fintype K] [Fintype K'] in
theorem fnField_le_join (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) :
    fnField O x ≤ fnField O (joinCoord x z) := by
  refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
  rintro _ ⟨⟨k, i, j⟩, rfl⟩
  exact ⟨⟨.inl k, i, j⟩, rfl⟩

theorem chartRing_le_join [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord x z) s ≠ 0) :
    chartRing O (mseg x) (restrictChart s) ≤ chartRing O (mseg (joinCoord x z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_joinCoord] at hs
    exact right_ne_zero_of_mul hs
  refine Algebra.adjoin_le ?_
  rintro _ ⟨t, rfl⟩
  have h : mseg x t / mseg x (restrictChart s) =
      mseg (joinCoord x z) (comb t s) / mseg (joinCoord x z) s := by
    rw [mseg_joinCoord x z (comb t s), mseg_joinCoord x z s]
    exact (mul_div_mul_right _ _ hw).symm
  show mseg x t / mseg x (restrictChart s) ∈ chartRing O (mseg (joinCoord x z)) s
  rw [h]
  exact div_mem_chartRing _ _ _

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_chartRing _ c, fun htop c hc => ?_, fun K' _ _ ι' _ z =>
    ⟨fun htop => top_le_iff.1 (htop ▸ fnField_le_join x z), fun c hc => ⟨?_, chartRing_le_join x z c hc⟩⟩⟩
  · exact isFractionRing_of_closure_eq_top _ (top_le_iff.1 (htop ▸ fnField_le_closure x c hc))
  · rw [mseg_joinCoord] at hc
    exact left_ne_zero_of_mul hc

end GlobalTheory.CompanionTheory.Ar.Num.ChartNoethFrac
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHolds
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 (IsFractionRing.injective A K)
  rw [← (TensorProduct.isBaseChange A (Module.Dual A M) K).finrank_eq,
    ← (TensorProduct.isBaseChange A M K).finrank_eq]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange A M M K LinearMap.id).1

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chartSequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hdiv hT hproj
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right _ _) hdiv
  have h1 := _root_.GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints A K E c hc p R N Ω D κ hκR hproj hT
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hnorm : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hsplit⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HT.dualMap_exists_unique_split A K hAK E c hc p R N Ω D κ σ d m hnorm hd hdiv h1.2 hP2
  have hq := _root_.GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow A K hAK E c hc p R N Ω D κ σ m (hnorm σ) hdiv h1.2
  have hq' := _root_.GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hnorm _) hdiv h1.2
  have hcomp := _root_.GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod A K E c hc p R N Ω D κ σ d d' m i hdiv hd hd' h1.2 hP1 hP2 hT hi
  refine ⟨i, hi, hsplit i hi, fun x => ⟨?_, ?_⟩, hq.2.2⟩
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu'⟩ := hu.pow m
      refine ⟨0, ((u⁻¹ : Aˣ) : A) • x, ?_⟩
      rw [map_zero, zero_add, ← hu', smul_smul, Units.mul_inv, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hq.2.1
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) := Module.Finite.iff_fg.2 hq'.2.1
      haveI := hP1
      haveI := hP2
      have hrank := _root_.GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 hT
      rw [← finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom))] at hrank
      obtain ⟨r, hr⟩ := hsplit i hi
      let qL : (Fin N → A) →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ) (qLin D σ) hq.1
      refine _root_.GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m)
        i r qL (by rw [add_comm]; exact hrank) hr ?_ ?_ x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      · rintro ⟨y, hy⟩
        obtain ⟨x, y', hy', e⟩ := hq.2.2 y hy
        exact ⟨x, ⟨y', hy'⟩, Subtype.ext e⟩
      · intro w
        obtain ⟨y, hy, e⟩ := hcomp w
        exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y, hy, hy'⟩ := hcomp w
    refine ⟨y + D.q σ x', add_mem hy (hq.1 x'), ?_⟩
    have e1 := (qLin D σ).map_add (i w) (((p : A) ^ m) • x')
    have e2 := (qLin D σ).map_smul ((p : A) ^ m) x'
    change D.q σ _ = _
    change (qLin D σ) _ = _
    rw [e1, e2]
    change D.q σ (i w) + _ = _
    rw [hy', smul_add]
    rfl

end GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentIdealAutomorphismInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_differentIdeal_ringEquiv_iff :
    ∀ (E : Type) [Field E] [NumberField E] (s : 𝓞 E ≃+* 𝓞 E) (d : 𝓞 E),
      s d ∈ differentIdeal ℤ (𝓞 E) ↔ d ∈ differentIdeal ℤ (𝓞 E) :=
  @PositivityTheory.UnitarySelfGeneration.map_mem_differentIdeal_iff

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerCompatibility
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.HT

open Coalgebra Bialgebra PositivityTheory.HtPt.Gi PositivityTheory.HtPt.Twpdiv in
theorem tower_end_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), (∀ (φ : La →+ La) (dφ : L →ₗ[O] L), X.Acts φ dφ → ∃ f : G ⟶ G, (∀ a, tateMap G G O f (τ a) = τ (φ a)) ∧ ∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) ∧ ∀ (H : PDivGroup p O) (f f' : G ⟶ H), (∀ a, tateMap G H O f (τ a) = tateMap G H O f' (τ a)) → f = f' := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre
  let ev (n : ℕ) (t : LevGrp La p n) : G.A n →ₐ[O] O :=
    (evalAt (X.A n) t).comp (e n).toAlgHom
  have ev_apply (n : ℕ) (t : LevGrp La p n) (g : G.A n) : ev n t g = (e n g).1 t := rfl
  have sep (n : ℕ) : Sep (ev n) := fun _ _ h => (e n).injective (Subtype.ext (funext h))
  have ev_lev (n : ℕ) (a : La) : ev n (lev p n a) = (τ a).pt n :=
    AlgHom.ext fun g => (hre.pt a n g).symm
  refine ⟨?_, ?_⟩
  · intro φ dφ h
    have exists_pullback (n : ℕ) (g : G.A n) :
        ∃ g' : G.A n, ∀ t, ev n t g' = ev n (levMap p n φ t) g := by
      refine ⟨(e n).symm ⟨fun t => (e n g).1 (levMap p n φ t), ?_⟩, ?_⟩
      · exact (h n (e n g).1 _ fun _ => rfl).1 (e n g).2
      · intro t
        rw [ev_apply, AlgEquiv.apply_symm_apply]
        rfl
    let pull (n : ℕ) : G.A n →ₐ[O] G.A n :=
      Ord.liftTo (ev n) (sep n) (fun t => ev n (levMap p n φ t)) (exists_pullback n)
    have comp_pull (n : ℕ) (t : LevGrp La p n) :
        (ev n t).comp (pull n) = ev n (levMap p n φ t) := Ord.ev_liftTo _ _ _ _ t
    have ev_pull (n : ℕ) (t : LevGrp La p n) (g : G.A n) :
        ev n t (pull n g) = ev n (levMap p n φ t) g := DFunLike.congr_fun (comp_pull n t) g
    have ev_one (n : ℕ) (g : G.A n) : ev n 1 g = counit (R := O) g := by
      rw [← lev_zero, ev_lev, map_zero]
      rfl
    have ev_mul (n : ℕ) (s t : LevGrp La p n) (g : G.A n) :
        pair (ev n s) (ev n t) (comul (R := O) g) = ev n (s * t) g := by
      obtain ⟨a, rfl⟩ := lev_surjective p n s
      obtain ⟨b, rfl⟩ := lev_surjective p n t
      rw [← lev_add, ev_lev, ev_lev, ev_lev, map_add (f := τ)]
      exact (AlgHom.convMul_apply ((τ a).conv n) ((τ b).conv n) g).symm
    let app (n : ℕ) : G.A n →ₐc[O] G.A n :=
      BialgHom.ofAlgHom (pull n)
        (AlgHom.ext fun g => by
          change counit (R := O) (pull n g) = counit (R := O) g
          rw [← ev_one, ← ev_one, ev_pull, map_one])
        (AlgHom.ext fun g => (sep n).pair (sep n) _ _ fun z => by
          change pair (ev n z.1) (ev n z.2)
              (Algebra.TensorProduct.map (pull n) (pull n) (comul (R := O) g)) =
            pair (ev n z.1) (ev n z.2) (comul (R := O) (pull n g))
          rw [pair_map, comp_pull, comp_pull, ev_mul, ev_mul, ev_pull, map_mul])
    let f : G ⟶ G := {
      app := app
      comm n := BialgHom.ext fun g => sep n _ _ fun t => by
        obtain ⟨a, rfl⟩ := lev_surjective p n t
        change (e n (G.res n (pull (n + 1) g))).1 _ = ev n _ (pull n (G.res n g))
        rw [hre.res, ← ev_apply, ev_pull, levMap_lev, ev_apply, ev_pull, levMap_lev,
          ev_apply, hre.res, map_nsmul] }
    have app_eval (n : ℕ) (g : G.A n) (a : La) :
        (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a)) :=
      ev_pull n (lev p n a) g
    refine ⟨f, fun a => TateOver.ext (funext fun n => AlgHom.ext fun g => ?_), app_eval⟩
    rw [tateMap_pt, hre.pt, hre.pt, app_eval]
  · intro H f f' hf
    refine PDivGroup.Hom.ext (funext fun n => BialgHom.ext fun g => sep n _ _ fun t => ?_)
    obtain ⟨a, rfl⟩ := lev_surjective p n t
    rw [ev_lev, ← tateMap_pt, ← tateMap_pt, hf]

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerDualStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
open Coalgebra WithConv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_dual : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ), (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingExtends B ζ → ∃ lam : G ⟶ G.dual, ∀ (a b : La) n, (e n (charElem (tateMap G G.dual O lam (τ a)) n)).1 (lev p n b) = ((ζ n ^ B a b : Oˣ) : O) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ La _ _ _ L _ _ X G e τ hre B ζ _ hζ hB
  have sep : ∀ n (f g : G.A n), (∀ a, (τ a).pt n f = (τ a).pt n g) → f = g := fun n f g h =>
    (e n).injective (Subtype.ext (funext fun t => by
      obtain ⟨a, rfl⟩ : ∃ a, lev p n a = t :=
        Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)
      rw [← hre.pt, ← hre.pt, h]))
  have key : ∀ n, ∃ (lam : CartierDual O (G.A n) →ₐc[O] G.A n) (u : La → G.A n),
      (∀ a φ, (τ a).pt n (lam φ) = φ (u a)) ∧
      ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) := by
    intro n
    obtain ⟨s, hs, hsv⟩ := hB n
    obtain ⟨l, u, h1, h2⟩ := PositivityTheory.HtPt.Twpol.exists_linear
      (X.A n) (e n) (lev p n) (fun a => (τ a).pt n) (fun a f => hre.pt a n f) s hs
    have h3 : ∀ a b, (τ b).pt n (u a) = ((ζ n ^ B a b : Oˣ) : O) :=
      fun a b => (h2 a b).trans (hsv a b)
    obtain ⟨lam, hlam⟩ := PositivityTheory.HtPt.Twpol.exists_bialgHom
      (fun a => (τ a).pt n) (sep n)
      (by
        change toConv ((τ 0).pt n).toLinearMap = 1
        rw [map_zero]; rfl)
      (fun a b => by
        change toConv ((τ (a + b)).pt n).toLinearMap = _
        rw [map_add (f := _)]; rfl)
      l u h1 (fun b => by simp [h3]) (fun a => by rw [h3]; simp)
      (fun a a' b => by simp [h3, zpow_add])
      (fun a b b' => by rw [h3, h3, h3]; simp [zpow_add])
    exact ⟨lam, u, fun a φ => by rw [hlam, h1], h3⟩
  choose lam u h1 h2 using key
  refine ⟨⟨lam, fun n => BialgHom.ext fun φ => sep n _ _ fun a => ?_⟩, fun a b n => ?_⟩
  · change (τ a).pt n (G.res n (lam (n + 1) φ)) = (τ a).pt n (lam n (CartierDual.map (G.mulP n) φ))
    rw [h1, hre.pt, hre.res, ← hre.pt, h1, CartierDual.map_apply]
    refine congrArg _ (sep _ _ _ fun b => ?_)
    rw [TateOver.pt_mulP, h2, h2, ← hζ n, ← zpow_natCast, ← zpow_mul, map_nsmul,
      LinearMap.smul_apply, nsmul_eq_mul]
  · rw [← hre.pt, ← h2]
    refine congrArg _ (CartierDual.eq_of_forall_apply (R := O) fun φ => ?_)
    rw [apply_charElem, tateMap_pt]
    exact h1 n a φ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DivisibleGroupTowerFreeStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisible_group_tower_free : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L) [Module.Free O L] [Module.Finite O L] (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate) (hre : X.Realises G e τ), ∃ j : G.omega ≃ₗ[O] Module.Dual O L, (∀ (χ : G.dual.Tate) n, X.der n (e n (charElem χ n)).1 (j (dlog G χ))) ∧ ∀ (φ : La →+ La) (dφ : L →ₗ[O] L) (f : G ⟶ G), X.Acts φ dφ → (∀ n (g : G.A n) (a : La), (e n (f.app n g)).1 (lev p n a) = (e n g).1 (lev p n (φ a))) → ∀ w, j (omegaMap G G f w) = j w ∘ₗ dφ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hO La _ _ _ L _ _ X _ _ G e τ hre
  have counit_eq (n : ℕ) (a : G.A n) :
      Bialgebra.counitAlgHom O (G.A n) a = (e n a).1 1 := by
    have h := hre.pt 0 n a
    rw [map_zero] at h
    exact h
  have mem_sq_iff (n : ℕ) (a : G.A n) :
      a ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 ↔
        e n a ∈ BT.augIdeal (X.A n) ^ 2 := by
    have hker : (BT.augIdeal (X.A n)).comap (e n) =
        RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) := by
      ext b
      rw [Ideal.mem_comap, OrderApi.mem_augIdeal, RingHom.mem_ker, counit_eq]
    have hmap : (RingHom.ker (Bialgebra.counitAlgHom O (G.A n))).map (e n) =
        BT.augIdeal (X.A n) := by
      rw [← hker, Ideal.map_comap_of_surjective _ (e n).surjective]
    rw [← hmap, ← Ideal.map_pow]
    constructor
    · exact Ideal.mem_map_of_mem _
    · intro h
      obtain ⟨b, hb, hab⟩ := (Ideal.mem_map_iff_of_surjective _ (e n).surjective).1 h
      rwa [← (e n).injective hab]
  have dUnit_eq_zero_iff (n : ℕ) (a : G.A n) :
      PDiv.dUnit (R := O) a = 0 ↔ X.der n (e n a).1 0 := by
    rw [PDiv.dUnit, AugCot.d_eq_zero_iff, mem_sq_iff, map_sub, AlgEquiv.commutes]
    set c := Bialgebra.counitAlgHom O (G.A n) a with hc
    have hc' : X.der n (algebraMap O (X.A n) c).1 0 := X.der_const n c
    constructor
    · intro h
      have hd := PositivityTheory.HtPt.Twomega.der_of_mem_sq X n _ h
      simpa using X.der_add n _ _ _ _ hd hc'
    · intro h
      have hd := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ h hc'
      rw [sub_zero] at hd
      refine X.der_zero n ⟨e n a - algebraMap O (X.A n) c, ?_⟩ hd
      rw [OrderApi.mem_augIdeal, hc, counit_eq]
      exact sub_self _
  have dUnit_eq_iff (n : ℕ) (a b : G.A n) (w : Module.Dual O L)
      (h : X.der n (e n a).1 w) : PDiv.dUnit (R := O) b = PDiv.dUnit (R := O) a ↔ X.der n (e n b).1 w := by
    rw [← sub_eq_zero, PDiv.dUnit, PDiv.dUnit, ← map_sub]
    refine (dUnit_eq_zero_iff n (b - a)).trans ?_
    rw [map_sub]
    constructor
    · intro hd
      simpa using X.der_add n _ _ _ _ hd h
    · intro hd
      have hsub := PositivityTheory.HtPt.Twomega.der_sub X n _ _ _ _ hd h
      rwa [sub_self] at hsub
  have exists_der (n : ℕ) (w : Module.Dual O L) : ∃ a : G.A n, X.der n (e n a).1 w := by
    obtain ⟨f, hf, h⟩ := X.der_onto n w
    exact ⟨(e n).symm ⟨f, hf⟩, by rwa [AlgEquiv.apply_symm_apply]⟩
  let cls (n : ℕ) (w : Module.Dual O L) := PDiv.dUnit (R := O) (exists_der n w).choose
  have dUnit_eq_cls (n : ℕ) (a : G.A n) (w : Module.Dual O L) :
      PDiv.dUnit (R := O) a = cls n w ↔ X.der n (e n a).1 w :=
    dUnit_eq_iff n _ a w (exists_der n w).choose_spec
  have der_res (n : ℕ) (a : G.A (n + 1)) (w : Module.Dual O L)
      (h : X.der (n + 1) (e (n + 1) a).1 w) : X.der n (e n (G.res n a)).1 w :=
    X.der_res n _ _ w h (hre.res n a)
  let toOmega : Module.Dual O L →ₗ[O] G.omega :=
    { toFun := fun w => ⟨fun n => cls n w, fun n => by
        obtain ⟨a, ha⟩ := exists_der (n + 1) w
        change PDiv.cotMap (G.res n) (cls (n + 1) w) = cls n w
        rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.cotMap_d, dUnit_eq_cls]
        exact der_res n a w ha⟩
      map_add' := fun w w' => Subtype.ext (funext fun n => by
        obtain ⟨a, ha⟩ := exists_der n w
        obtain ⟨b, hb⟩ := exists_der n w'
        change cls n (w + w') = cls n w + cls n w'
        rw [← (dUnit_eq_cls _ a w).2 ha, ← (dUnit_eq_cls _ b w').2 hb,
          PDiv.dUnit, PDiv.dUnit, ← map_add (f := _), eq_comm]
        refine (dUnit_eq_cls _ _ _).2 ?_
        rw [map_add (f := _)]
        exact X.der_add n _ _ _ _ ha hb)
      map_smul' := fun r w => Subtype.ext (funext fun n => by
        obtain ⟨a, ha⟩ := exists_der n w
        change cls n (r • w) = r • cls n w
        rw [← (dUnit_eq_cls _ a w).2 ha, PDiv.dUnit, ← map_smul, eq_comm]
        refine (dUnit_eq_cls _ _ _).2 ?_
        rw [map_smul]
        exact PositivityTheory.HtPt.Twomega.der_smul X n r _ _ ha) }
  have toOmega_val (w : Module.Dual O L) (n : ℕ) : (toOmega w).1 n = cls n w := rfl
  have toOmega_bijective : Function.Bijective toOmega := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro w hw
      refine PositivityTheory.HtPt.Twomega.eq_zero_of_cong hO w fun n => ?_
      have h0 : PDiv.dUnit (R := O) (0 : G.A n) = 0 := map_zero _
      have h1 : cls n w = 0 := congrArg (fun x : G.omega => x.1 n) hw
      exact (X.der_unique n _ 0 w ((dUnit_eq_zero_iff n 0).1 h0)).1
        ((dUnit_eq_cls n 0 w).1 (h0.trans h1.symm))
    · intro ω
      choose a ha using fun n => AugCot.d_surjective _ (ω.1 n)
      choose w hw using fun n => X.der_ex n (e n (a n)).1 (e n (a n)).2
      obtain ⟨W, hW⟩ := PositivityTheory.HtPt.Twomega.exists_lim hO w fun n => by
        refine (X.der_unique n _ _ _ (hw n)).1 ?_
        refine (dUnit_eq_iff n _ _ _ (der_res n _ _ (hw (n + 1)))).1 ?_
        rw [← PDiv.cotMap_d, PDiv.dUnit, PDiv.dUnit, ha, ha]
        exact (ω.2 n).symm
      refine ⟨W, Subtype.ext (funext fun n => ?_)⟩
      rw [toOmega_val, ← ha, eq_comm]
      exact (dUnit_eq_cls n _ W).2 ((X.der_unique n _ _ _ (hw n)).2 (hW n))
  let k := LinearEquiv.ofBijective toOmega toOmega_bijective
  have hk (ω : G.omega) (n : ℕ) : ω.1 n = cls n (k.symm ω) :=
    congrArg (fun x : G.omega => x.1 n) (k.apply_symm_apply ω).symm
  refine ⟨k.symm, fun χ n => ?_, fun φ dφ f hφ hf ω => ?_⟩
  · exact (dUnit_eq_cls n _ _).1 (hk (dlog G χ) n)
  · rw [LinearEquiv.symm_apply_eq]
    refine Subtype.ext (funext fun n => ?_)
    obtain ⟨a, ha⟩ := exists_der n (k.symm ω)
    rw [omegaMap_val, hk ω n, ← (dUnit_eq_cls n a _).2 ha, PDiv.cotMap_d]
    exact (dUnit_eq_cls n _ _).2 ((hφ n _ _ (hf n a)).2 _ ha)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestrictionStatement
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hopf_order_retract_restriction : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], ∀ AA : HopfOrder (C := C) R N, ∀ (N' : Type) [AddCommGroup N'] [Fintype N'] [DecidableEq N'], ∀ (ι : N' →+ N) (π : N →+ N'), (∀ y, π (ι y) = y) → (∀ g ∈ AA.carrier, (fun x => g (ι (π x))) ∈ AA.carrier) → (∃ A' : HopfOrder (C := C) R N', A'.carrier = AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) ∧ (∀ h ∈ AA.carrier.map (LinearMap.funLeft R C (ι : N' → N)), (fun x => h (π x)) ∈ AA.carrier) ∧ ∀ K' : AddSubgroup N', GenAF p AA.carrier (K'.map ι) → GenAF p (AA.carrier.map (LinearMap.funLeft R C (ι : N' → N))) K' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor | exact GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.ret_hopf_factor <;> assumption)
end

