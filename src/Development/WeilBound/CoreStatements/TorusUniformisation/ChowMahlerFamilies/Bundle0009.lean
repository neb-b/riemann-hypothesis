module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeGeneratorCodimOne
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem PositivityTheory.Xgn.line_lattice_generator_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (p : Cpt ξ) (t : Ω), L.IsVBOn T 1 ⊤ → (∀ q : Cpt ξ, q.1 ⤳ p.1 → q ∈ T) → t ≠ 0 → (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → L.IsGenAt q t) → L.IsGenAt p t := by
  intro X Ω _ ξ _ hg hn L T p t hL hT ht hq
  obtain ⟨U, hU, b, -, h⟩ := hL p (hT p specializes_rfl)
  have hr : Set.range b = {b 0} := by
    ext x
    simp [Fin.exists_fin_one, eq_comm]
  have hgen : ∀ q : Cpt ξ, q.1 ⤳ p.1 → b 0 ≠ 0 ∧ L q = Submodule.span (regAt ξ q) {b 0} := by
    intro q hqp
    obtain ⟨h1, h2⟩ := h q (hT q hqp) (hqp.mem_open U.2 hU)
    exact ⟨h1.ne_zero 0, by rw [h2, hr]⟩
  obtain ⟨he, hp⟩ := hgen p specializes_rfl
  have hu : ∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → unitAt ξ q (t / b 0) := by
    intro q hqp hd
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht ((hq q hqp hd).2.symm.trans (hgen q hqp).2)
    rwa [e, smul_eq_mul, mul_div_cancel_right₀ _ he]
  have h1 : t / b 0 ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.1
  have h2 : (t / b 0)⁻¹ ∈ regAt ξ p :=
    mem_regAt_of_codim_one X Ω ξ hg hn p _ fun q hqp hd => (hu q hqp hd).2.2
  refine ⟨ht, ?_⟩
  rw [hp]
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · refine ⟨⟨_, h2⟩, ?_⟩
    change (t / b 0)⁻¹ * t = b 0
    field_simp
  · refine ⟨⟨_, h1⟩, ?_⟩
    change (t / b 0) * b 0 = t
    field_simp
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineLatticeSpread
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeSpread

theorem exists_common {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] [QuasiSober α]
    {O : Type*} [CommRing O] [IsDomain O] (f : α → PrimeSpectrum O) (hf : Continuous f) (C : Set α)
    (hC : IsClosed C) (h : ∀ x ∈ C, ∃ o : O, o ≠ 0 ∧ o ∈ (f x).asIdeal) :
    ∃ n : O, n ≠ 0 ∧ ∀ x ∈ C, n ∈ (f x).asIdeal := by
  classical
  obtain ⟨S, hS, hcl, hirr, hU⟩ := TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have key : ∀ Z ∈ S, ∃ o : O, o ≠ 0 ∧ ∀ x ∈ Z, o ∈ (f x).asIdeal := by
    intro Z hZ
    obtain ⟨η, hη⟩ := QuasiSober.sober (hirr Z hZ) (hcl Z hZ)
    obtain ⟨o, ho, hm⟩ := h η (by rw [hU]; exact ⟨Z, hZ, hη.mem⟩)
    refine ⟨o, ho, fun x hx => ?_⟩
    exact (PrimeSpectrum.le_iff_specializes _ _).2 ((hη.specializes hx).map hf) hm
  choose! o ho hm using key
  refine ⟨∏ Z ∈ hS.toFinset, o Z, Finset.prod_ne_zero_iff.2 fun Z hZ => ho Z (hS.mem_toFinset.1 hZ), ?_⟩
  intro x hx
  rw [hU] at hx
  obtain ⟨Z, hZ, hxZ⟩ := hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem o (hS.mem_toFinset.2 hZ)
  rw [hc]
  exact Ideal.mul_mem_right _ _ (hm Z hZ x hxZ)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem isGenAt_iff (L : Lat ξ Ω) (b : Fin 1 → Ω) (q : Cpt ξ) (hb : L.IsFrameAt b q) (t : Ω) :
    L.IsGenAt q t ↔ unitAt ξ q (t / b 0) := by
  have h0 : b 0 ≠ 0 := hb.1.ne_zero 0
  have hr : Set.range b = {b 0} := Set.range_unique
  have hL : L q = Submodule.span (regAt ξ q) {b 0} := by rw [hb.2, hr]
  constructor
  · rintro ⟨ht, e⟩
    have e' := hL.symm.trans e
    refine ⟨div_ne_zero ht h0, ?_, ?_⟩
    · have : t ∈ Submodule.span (regAt ξ q) {b 0} := e' ▸ Submodule.mem_span_singleton_self t
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * b 0 = t := hr
      rw [← hr', mul_div_cancel_right₀ _ h0]
      exact r.2
    · have : b 0 ∈ Submodule.span (regAt ξ q) {t} := e' ▸ Submodule.mem_span_singleton_self (b 0)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
      have hr' : (r : Ω) * t = b 0 := hr
      rw [inv_div, ← hr', mul_div_cancel_right₀ _ ht]
      exact r.2
  · rintro ⟨h1, h2, h3⟩
    have ht : t ≠ 0 := fun h => h1 (by rw [h, zero_div])
    refine ⟨ht, hL.trans (le_antisymm ?_ ?_)⟩
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h3⟩, ?_⟩
      show (t / b 0)⁻¹ * t = b 0
      field_simp
    · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
      refine ⟨⟨_, h2⟩, ?_⟩
      show (t / b 0) * b 0 = t
      field_simp

end PositivityTheory.Xgn.LineLatticeSpread

open PositivityTheory.Xgn.LineLatticeSpread in
theorem PositivityTheory.Xgn.line_lattice_spread : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsNoetherianRing O] [LocallyOfFiniteType s] [QuasiCompact s], ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → Function.Injective (algebraMap O Ω) → IsCptGen ξ → ∀ (L : Lat ξ Ω) (T : Set (Cpt ξ)) (n₀ : O) (t : Ω), n₀ ≠ 0 → (∀ p, unitAt ξ p (algebraMap O Ω n₀) → p ∈ T) → L.IsVBOn T 1 ⊤ → (∀ p ∈ genFibre O ξ, L.IsGenAt p t) → ∃ n : O, n ≠ 0 ∧ ∀ p, unitAt ξ p (algebraMap O Ω n) → L.IsGenAt p t := by
  intro X Ω _ ξ O _ _ _ s _ _ _ hs _ hc L T n₀ t hn₀ hT hL hgen
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  haveI : IsNoetherian X := {}
  have hu : ∀ (p : Cpt ξ) (o : O), unitAt ξ p (algebraMap O Ω o) ↔ o ∉ (s p.1).asIdeal := fun p o =>
    (ConstReg.regular_const X Ω ξ O s hs p o).2 hc
  let W : Set X := ⋃ (U : X.Opens) (_ : ∀ q : Cpt ξ, q.1 ∈ U → L.IsGenAt q t), (U : Set X)
  have hW : IsOpen W := isOpen_iUnion fun U => isOpen_iUnion fun _ => U.isOpen
  obtain ⟨n, hn, H⟩ := exists_common (O := O) (fun x : X => s x) s.continuous (closure {genPt ξ} ∩ Wᶜ)
    (isClosed_closure.inter hW.isClosed_compl) (by
      rintro x ⟨hx, hxW⟩
      by_contra hcon
      let p : Cpt ξ := ⟨x, specializes_iff_mem_closure.2 hx⟩
      have hp : p ∈ genFibre O ξ := fun o ho => (hu p o).2 fun hm => hcon ⟨o, ho, hm⟩
      obtain ⟨U, hpU, b, -, hb⟩ := hL p (hT p (hp n₀ hn₀))
      have h1 := (isGenAt_iff L b p (hb p (hT p (hp n₀ hn₀)) hpU) t).1 (hgen p hp)
      obtain ⟨U₁, hp₁, H₁⟩ := (regAt_unitAt_open X Ω ξ p _).2 h1
      obtain ⟨U₂, hp₂, H₂⟩ := (regAt_unitAt_open X Ω ξ p _).2 (hp n₀ hn₀)
      refine hxW (Set.mem_iUnion₂.2 ⟨U ⊓ U₁ ⊓ U₂, ?_, ⟨⟨hpU, hp₁⟩, hp₂⟩⟩)
      rintro q ⟨⟨hq, hq₁⟩, hq₂⟩
      exact (isGenAt_iff L b q (hb q (hT q (H₂ q hq₂)) hq) t).2 (H₁ q hq₁))
  refine ⟨n, hn, fun p hp => ?_⟩
  have hpW : p.1 ∈ W := by
    by_contra hW'
    exact (hu p n).1 hp (H p.1 ⟨specializes_iff_mem_closure.1 p.2, hW'⟩)
  obtain ⟨U, hU, hpU⟩ := Set.mem_iUnion₂.1 hpW
  exact hU p hpU
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XBundleOfFamily
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem PositivityTheory.Xgn.t_bundle_of_family : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V], (∀ Γ : (∀ k, ι k) → AddSubgroup V, IsLatFamily O x Γ → (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) → ∃ E : ChartBundle O (mseg x) N V, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧ ∀ E : ChartBundle O (mseg x) N V, IsLatFamily O x E.lat ∧ ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
  classical
  intro O _ Ω _ _ K _ _ ι _ x N V _ _
  refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
  refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
            stable := ?_
            frame := ?_
            overlap := ?_ }, ?_⟩
  · intro s a ha e he
    by_cases h : mseg x s = 0
    · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
      rw [he, smul_zero]
    · simp only [h, if_false] at he ⊢
      exact hfam.1 s h a ha e he
  · intro s hs
    simp only [hs, if_false]
    exact (hloc s hs).2
  · intro s t hs ht e he
    simp only [hs, ht, if_false] at he ⊢
    exact hfam.2 s t hs ht e he
  · intro s hs
    simp only [hs, if_false]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XChartNoethFrac
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_chart_noeth_frac

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type}

theorem ratio_eq [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) (k : K) (i : ι k) :
    mseg x (Function.update c k i) / mseg x c = x ⟨k, i⟩ / x ⟨k, c k⟩ := by
  have h1 : mseg x (Function.update c k i) = x ⟨k, i⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : mseg x c = x ⟨k, c k⟩ * ∏ l ∈ Finset.univ.erase k, x ⟨l, c l⟩ := by
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  rw [h2] at hc
  rw [h1, h2, mul_div_mul_right _ _ (right_ne_zero_of_mul hc)]

theorem mseg_join {K' : Type} [Fintype K'] {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord x z) c = mseg x (restrictChart c) * mseg z (fun k => c (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type]
  rfl

def comb {K' : Type} {ι' : K' → Type} (t : ∀ k, ι k) (c : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => c (.inr k)

variable [∀ k, Fintype (ι k)]

theorem fnField_le [DecidableEq K] (x : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : mseg x c ≠ 0) :
    fnField O x ≤ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
  have hk : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc k (Finset.mem_univ k)
  have hm : ∀ k (i : ι k), x ⟨k, i⟩ / x ⟨k, c k⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω) := by
    intro k i
    rw [← ratio_eq x c hc k i]
    exact Subfield.subset_closure (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _)
  unfold fnField
  rw [Subfield.closure_le]
  rintro _ (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have h : x ⟨k, i⟩ / x ⟨k, j⟩ = (x ⟨k, i⟩ / x ⟨k, c k⟩) / (x ⟨k, j⟩ / x ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hk k)]
    show x ⟨k, i⟩ / x ⟨k, j⟩ ∈ Subfield.closure (chartRing O (mseg x) c : Set Ω)
    rw [h]
    exact div_mem (hm k i) (hm k j)

theorem isFractionRing_of_closure (R : Subalgebra O Ω) (h : Subfield.closure (R : Set Ω) = ⊤) :
    IsFractionRing R Ω := by
  refine IsFractionRing.of_field R Ω fun z => ?_
  have hz : z ∈ Subfield.closure (R : Set Ω) := h ▸ Subfield.mem_top z
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.1 hz
  have e : Subring.closure (R : Set Ω) = R.toSubring := Subring.closure_eq R.toSubring
  rw [e] at ha hb
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, rfl⟩

end PositivityTheory.Xgn.A_chart_noeth_frac

open PositivityTheory.Xgn.A_chart_noeth_frac in
theorem PositivityTheory.Xgn.t_chart_noeth_frac : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), (∀ c, IsNoetherianRing (chartRing O (mseg x) c)) ∧ (fnField O x = ⊤ → ∀ c, mseg x c ≠ 0 → IsFractionRing (chartRing O (mseg x) c) Ω) ∧ ∀ (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω), (fnField O x = ⊤ → fnField O (joinCoord x z) = ⊤) ∧ ∀ c, mseg (joinCoord x z) c ≠ 0 → mseg x (restrictChart c) ≠ 0 ∧ (chartRing O (mseg x) (restrictChart c)) ≤ (chartRing O (mseg (joinCoord x z)) c) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x
  refine ⟨fun c => isNoetherianRing_of_fg (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩), fun h c hc => ?_,
    fun K' _ _ ι' _ z => ⟨fun h => ?_, fun c hc => ?_⟩⟩
  · exact isFractionRing_of_closure _ (top_le_iff.1 (h ▸ fnField_le x c hc))
  · rw [eq_top_iff, ← h]
    unfold fnField
    refine Subfield.closure_mono (Set.union_subset_union_right _ ?_)
    rintro _ ⟨⟨k, i, j⟩, rfl⟩
    exact ⟨⟨.inl k, i, j⟩, rfl⟩
  · have hc' := hc
    rw [mseg_join] at hc'
    refine ⟨left_ne_zero_of_mul hc', ?_⟩
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : mseg x t / mseg x (restrictChart c) =
        mseg (joinCoord x z) (comb t c) / mseg (joinCoord x z) c := by
      rw [mseg_join x z (comb t c), mseg_join x z c]
      exact (mul_div_mul_right _ _ (right_ne_zero_of_mul hc')).symm
    simp only
    rw [h]
    exact ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := O) _ _ _
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFamConstr
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace PositivityTheory.Xgn.A_fam_constr

open ReciprocityTheory.ChartRestriction.G.Geo (exists_pow_mul_mem_chartRing div_mem_chartRing)

variable {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} {x : (Σ k, ι k) → Ω}
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]

theorem mono {Γ : (∀ k, ι k) → AddSubgroup V} (h : IsLatFamily o x Γ) {s t : ∀ k, ι k}
    (ht : mseg x t ≠ 0) {v : V} {m m' : ℕ} (hm : m ≤ m') (hv : (mseg x s / mseg x t) ^ m • v ∈ Γ t) :
    (mseg x s / mseg x t) ^ m' • v ∈ Γ t := by
  rw [← Nat.sub_add_cancel hm, pow_add, mul_smul]
  exact h.1 t ht _ (pow_mem (div_mem_chartRing (mseg x) t s) _) _ hv

theorem fam_sub (U : Submodule Ω V) : IsLatFamily o x (fun _ => U.toAddSubgroup) :=
  ⟨fun _ _ a _ _ hv => U.smul_mem a hv, fun _ _ _ _ _ hv => ⟨0, U.smul_mem _ hv⟩⟩

theorem fam_top : IsLatFamily o x (fun _ => (⊤ : AddSubgroup V)) :=
  ⟨fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => ⟨0, trivial⟩⟩

theorem fam_bot : IsLatFamily o x (fun _ => (⊥ : AddSubgroup V)) := fam_sub ⊥

theorem fam_sup {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊔ B c) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (hA.1 s hs a ha y hy) (hB.1 s hs a ha z hz)
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    obtain ⟨m', hm'⟩ := hB.2 s t hs ht z hz
    refine ⟨m + m', ?_⟩
    rw [smul_add]
    exact AddSubgroup.add_mem_sup (mono hA ht (Nat.le_add_right _ _) hm)
      (mono hB ht (Nat.le_add_left _ _) hm')

theorem fam_inf {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => A c ⊓ B c) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha v hv.1, hB.1 s hs a ha v hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht v hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht v hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem fam_map {A : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).map f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨_, hA.1 s hs a ha y hy, hf a y⟩
  · obtain ⟨y, hy, rfl⟩ := hv
    obtain ⟨m, hm⟩ := hA.2 s t hs ht y hy
    exact ⟨m, _, hm, hf _ y⟩

theorem fam_comap {A : (∀ k, ι k) → AddSubgroup V₁} (hA : IsLatFamily o x A) (f : V →+ V₁)
    (hf : ∀ (a : Ω) v, f (a • v) = a • f v) : IsLatFamily o x (fun c => (A c).comap f) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · rw [AddSubgroup.mem_comap, hf]
    exact hA.1 s hs a ha _ hv
  · obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv
    exact ⟨m, by rw [AddSubgroup.mem_comap, hf]; exact hm⟩

theorem fam_prod {A : (∀ k, ι k) → AddSubgroup V} {B : (∀ k, ι k) → AddSubgroup V₁}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x (fun c => (A c).prod (B c)) := by
  refine ⟨fun s hs a ha v hv => ⟨hA.1 s hs a ha _ hv.1, hB.1 s hs a ha _ hv.2⟩,
    fun s t hs ht v hv => ?_⟩
  obtain ⟨m, hm⟩ := hA.2 s t hs ht _ hv.1
  obtain ⟨m', hm'⟩ := hB.2 s t hs ht _ hv.2
  exact ⟨m + m', mono hA ht (Nat.le_add_right _ _) hm, mono hB ht (Nat.le_add_left _ _) hm'⟩

theorem mem_stdLat (R : Subalgebra o Ω) {J : Type} (v : J → Ω) : v ∈ stdLat R J ↔ ∀ j, v j ∈ R :=
  ⟨fun h j => h j trivial, fun h j _ => h j⟩

theorem fam_std (J : Type) [Fintype J] :
    IsLatFamily o x (fun c => stdLat (chartRing o (mseg x) c) J) := by
  refine ⟨fun s _ a ha v hv => ?_, fun s t hs _ v hv => ?_⟩
  · rw [mem_stdLat] at hv ⊢
    exact fun j => mul_mem ha (hv j)
  · rw [mem_stdLat] at hv
    choose m hm using fun j => exists_pow_mul_mem_chartRing (mseg x) s t hs (hv j)
    refine ⟨∑ q, m q, (mem_stdLat _ _).2 fun q => ?_⟩
    have hle : m q ≤ ∑ q, m q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [Pi.smul_apply, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add, mul_assoc]
    exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hm q)

theorem mem_dotDual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (w : Fin m → Ω) :
    w ∈ dotDual R L ↔ ∀ v ∈ L, v ⬝ᵥ w ∈ R := by
  simp only [dotDual, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

def FG (R : Subalgebra o Ω) (L : AddSubgroup V) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (g : I → V), (∀ i, g i ∈ L) ∧
    ∀ e ∈ L, ∃ a : I → Ω, (∀ i, a i ∈ R) ∧ ∑ i, a i • g i = e

theorem fg_of_locFree {R : Subalgebra o Ω} {r : ℕ} {L : AddSubgroup V} (h : LocFree R r L) :
    FG R L := by
  let L' : Submodule R V := { L with smul_mem' := fun a e he => h.1 a a.2 e he }
  obtain ⟨k, φ, v, hφ, hv⟩ := LocFreeProj.exists_dualBasis (L := L') (r := r) h
  exact ⟨_, inferInstance, fun i => v i, fun i => (v i).2,
    fun e he => ⟨fun i => φ i e, fun i => hφ i e he, hv e⟩⟩

theorem fg_comap {R : Subalgebra o Ω} {L : AddSubgroup V₁} (h : FG R L) (f : V →ₗ[Ω] V₁)
    (hf : Function.Injective f) (hS : Summand L (LinearMap.range f)) :
    FG R (L.comap f.toAddMonoidHom) := by
  obtain ⟨I, hI, g, hg, hL⟩ := h
  obtain ⟨ρ, h1, h2, h3⟩ := hS
  choose y hy using fun i => h1 (g i)
  refine ⟨I, hI, y, fun i => ?_, fun e he => ?_⟩
  · change f (y i) ∈ L
    rw [hy]
    exact h3 _ (hg i)
  · obtain ⟨a, ha, hs⟩ := hL (f e) he
    refine ⟨a, ha, hf ?_⟩
    rw [← h2 (f e) ⟨e, rfl⟩, ← hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hy]

theorem fam_dual {m : ℕ} {A : (∀ k, ι k) → AddSubgroup (Fin m → Ω)} (hA : IsLatFamily o x A)
    (hfg : ∀ c, mseg x c ≠ 0 → FG (chartRing o (mseg x) c) (A c)) :
    IsLatFamily o x (fun c => dotDual (chartRing o (mseg x) c) (A c)) := by
  refine ⟨fun s _ a ha w hw => ?_, fun s t hs ht w hw => ?_⟩
  · rw [mem_dotDual] at hw ⊢
    intro v hv
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha (hw v hv)
  · rw [mem_dotDual] at hw
    obtain ⟨I, hI, g, hg, hL⟩ := hfg t ht
    have key : ∀ i, ∃ k : ℕ, (mseg x s / mseg x t) ^ k * (g i ⬝ᵥ w) ∈ chartRing o (mseg x) t := by
      intro i
      obtain ⟨k, hk⟩ := hA.2 t s ht hs _ (hg i)
      obtain ⟨k', hk'⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs (hw _ hk)
      refine ⟨k', ?_⟩
      have hu : (mseg x s / mseg x t) ^ k * (mseg x t / mseg x s) ^ k = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (mseg x s), div_self (mul_ne_zero ht hs), one_pow]
      rw [smul_dotProduct, smul_eq_mul] at hk'
      have : (mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w) = (mseg x s / mseg x t) ^ k *
          ((mseg x s / mseg x t) ^ k' * ((mseg x t / mseg x s) ^ k * (g i ⬝ᵥ w))) := by
        linear_combination (-(mseg x s / mseg x t) ^ k' * (g i ⬝ᵥ w)) * hu
      rw [this]
      exact mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) hk'
    choose k hk using key
    refine ⟨∑ q, k q, (mem_dotDual _ _ _).2 fun v hv => ?_⟩
    obtain ⟨a, ha, rfl⟩ := hL v hv
    rw [sum_dotProduct]
    refine sum_mem fun q _ => ?_
    have hle : k q ≤ ∑ q, k q :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ q)
    rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← Nat.sub_add_cancel hle, pow_add,
      mul_assoc]
    exact mul_mem (ha q) (mul_mem (pow_mem (div_mem_chartRing (mseg x) t s) _) (hk q))

theorem linMap_inj {F : Type} [Zero F] [One F] (n : ℕ) (χ : F → Ω) (h0 : χ 0 = 0) (h1 : χ 1 = 1) :
    Function.Injective (linMap n χ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro l hl
  funext j
  have := congrFun hl (Pi.single j 1)
  rw [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Finset.sum_eq_single j] at this
  · simpa [h1] using this
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi, h0]
  · simp

end PositivityTheory.Xgn.A_fam_constr

open PositivityTheory.Xgn.A_fam_constr in
theorem PositivityTheory.Xgn.t_fam_constr : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  classical
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D hD
  have hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) :=
    fam_sup hD.famM (fam_map (fam_std _) _ fun a v => smul_comm _ _ _)
  refine ⟨hl1, fun τ => ?_⟩
  obtain ⟨hlie, -, -, -, -, hDel, hTh⟩ := hD.fam τ
  have haf : IsLatFamily O x
      (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) :=
    fam_comap hl1 _ fun a v => (linMap n (fun a => algebraMap O Ω (χ τ a))).map_smul a v
  refine ⟨haf, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hG => ?_⟩
  · exact fam_comap (fam_sup hD.famM (fam_sub _)) _
      fun a v => (LinearMap.toSpanSingleton Ω _ _).map_smul a v
  · exact fam_comap (fam_sup hTh (fam_prod (fam_sub _) fam_bot)) _
      fun a v => Prod.ext ((LinearMap.toSpanSingleton Ω _ _).map_smul a v.1) rfl
  · exact fam_map (fam_inf hTh (fam_prod (fam_sub _) fam_top)) _ fun a v => rfl
  · exact fam_dual hlie fun c hc => fg_of_locFree ((hD.base c hc).free τ).1
  · have hh : IsLatFamily O x
        (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) := by
      refine fam_dual haf fun c hc => fg_comap (fg_of_locFree (hG c hc).l1) _
        (linMap_inj n _ ?_ ?_) ((hG c hc).lin τ)
      · simp [(hD.char.2.2.2.2 τ).1]
      · simp [(hD.char.2.2.2.2 τ).2]
    exact ⟨hh, fam_map (fam_inf hDel (fam_prod hh fam_top)) _ fun a v => rfl⟩
end

