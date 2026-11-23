module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.HermitianLattices.StatementLat
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.HostCM

theorem valuation_eq_of_unram (K : Type) [Field K] [NumberField K] [IsCMField K]
    (hunr : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      ¬ ∀ x : 𝓞 K, IsCMField.complexConj K • x - x ∈ P)
    (P : HeightOneSpectrum (𝓞 K)) (x : maximalRealSubfield K) :
    P.valuation K (algebraMap (maximalRealSubfield K) K x) =
      (P.under (𝓞 (maximalRealSubfield K))).valuation (maximalRealSubfield K) x := by
  have hp := P.isPrime
  have hp' := (P.under (𝓞 (maximalRealSubfield K))).isPrime
  have : P.asIdeal.LiesOver (P.under (𝓞 (maximalRealSubfield K))).asIdeal := ⟨rfl⟩
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[maximalRealSubfield K] K)
    (P.under (𝓞 (maximalRealSubfield K))).asIdeal P.asIdeal
  have h1 : Nat.card (P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨1, one_mem _⟩⟩⟩
    have key : ∀ z : P.asIdeal.inertia (K ≃ₐ[maximalRealSubfield K] K),
        (z : K ≃ₐ[maximalRealSubfield K] K) = 1 := by
      intro z
      rcases Eta.cases K z.1 with hz | hz
      · exact hz
      · exfalso
        have hm := AddSubgroup.mem_inertia.mp z.2
        rw [hz] at hm
        exact hunr P.asIdeal hp P.ne_bot hm
    rw [key x, key y]
  rw [h1, Ideal.ramificationIdxIn_eq_ramificationIdx _ P.asIdeal (K ≃ₐ[maximalRealSubfield K] K)] at hcard
  rw [← HeightOneSpectrum.valuation_liesOver K (P.under (𝓞 (maximalRealSubfield K))) P x,
    ← hcard, pow_one]


open Classical in
theorem host_cm_embedding_properties : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ (IsTotallyReal H.F ∧ IsTotallyComplex H.E ∧ Module.finrank H.F H.E = 2 ∧ c ≠ 1 ∧ Function.Bijective fun g => InfinitePlace.mk (embPsi H g)) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  have hcm : IsCMField H.E := H.isCMField_hostE
  have hc : ∀ x, IsCMField.complexConj H.E x = H.conj x := fun x => bridge_star_holds R H x
  have hmem : ∀ g : R.Psi, embPsi H g ∈ H.cmType := fun g => ((factEmb R H).2 g).2 g.2
  have hT := H.der.cmType.1
  refine ⟨IsCMField.complexConj H.E, hc, ⟨inferInstance, inferInstance,
    Algebra.IsQuadraticExtension.finrank_eq_two _ _, IsCMField.complexConj_ne_one _,
    ?_, ?_⟩, ?_, hmem, ?_⟩
  · intro g g' h
    rcases InfinitePlace.mk_eq_iff.1 h with h | h
    · exact Subtype.ext ((factEmb R H).1.1 h)
    · have h' := hmem g'
      rw [← h] at h'
      exact absurd h' ((hT _).1 (hmem g))
  · intro w
    by_cases hw : w.embedding ∈ H.cmType
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 w.embedding
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw)⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_embedding]
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 (ComplexEmbedding.conjugate w.embedding)
      have hw' : ComplexEmbedding.conjugate w.embedding ∈ H.cmType := by
        by_contra h'
        exact hw ((hT _).2 h')
      refine ⟨⟨g, ((factEmb R H).2 g).1 (hg ▸ hw')⟩, ?_⟩
      show InfinitePlace.mk (H.emb g) = w
      rw [hg, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  · intro P k
    have := valuation_eq_of_unram H.E (fun P hP h0 hx => H.der.unramEF P hP h0 fun x => by
      have e : H.conj • x = IsCMField.complexConj H.E • x := Subtype.ext (hc x).symm
      rw [e]
      exact hx x) P k
    unfold ordF
    rw [← this]
    rfl
  · rw [← Nat.card_eq_fintype_card]
    exact (factCardPsi R H).1


open Classical in
theorem host_cm : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ c : H.E ≃ₐ[H.F] H.E, (∀ x, c x = H.conj x) ∧ CMData H.F c (embPsi H) ∧ (∀ (P : HeightOneSpectrum (𝓞 H.E)) (k : (H.F)ˣ), ordF P (upF H.F k) = ordF (P.under (𝓞 H.F)) k) ∧ (∀ g : R.Psi, embPsi H g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ)) ∧ Fintype.card (R.Psi) = R.f := by
  intro R H
  obtain ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩ := host_cm_embedding_properties R H
  exact ⟨c, hc, ⟨h1, h2, h3, h4, h5⟩, h⟩

end GlobalTheory.Mem.HostCM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Filter Topology

namespace GlobalTheory.Mem.LocTriv

variable {L : Type} [Field L] [NumberField L]

theorem tendsto_finiteAdele {ι : Type} {l : Filter ι} (f : ι → FiniteAdeleRing (𝓞 L) L) (b : FiniteAdeleRing (𝓞 L) L)
    (hf : ∀ i v, f i v ∈ v.adicCompletionIntegers L) (hb : ∀ v, b v ∈ v.adicCompletionIntegers L)
    (h : ∀ v, Tendsto (fun i => f i v) l (𝓝 (b v))) : Tendsto f l (𝓝 b) := by
  first
  | exact @_root_.GlobalTheory.TendstoOfIntegrals.target_check
  | exact _root_.GlobalTheory.TendstoOfIntegrals.target_check
  | (apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply _root_.GlobalTheory.TendstoOfIntegrals.target_check <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TendstoOfIntegrals.target_check <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TendstoOfIntegrals.target_check ..)

def ev (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def part (a : GlobalTheory.Mem.Chr.Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : GlobalTheory.Mem.Chr.Ideles L :=
  ∏ v ∈ S, GlobalTheory.Mem.Chr.localIdele L v (Units.map (ev v) a)

theorem part_inv (a : GlobalTheory.Mem.Chr.Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S)⁻¹ = part a⁻¹ S := by
  simp only [part, map_inv, Finset.prod_inv_distrib]

theorem ev_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    ev v (GlobalTheory.Mem.Chr.localIdele L v x : AdeleRing (𝓞 L) L) = x := by
  classical
  have := Function.update_self (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_local_ne {v w : HeightOneSpectrum (𝓞 L)} (hw : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    ev w (GlobalTheory.Mem.Chr.localIdele L v x : AdeleRing (𝓞 L) L) = 1 := by
  classical
  have := Function.update_of_ne (β := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) hw
    (x : v.adicCompletion L) (fun _ => 1)
  convert this
  rfl

theorem ev_part_mem (a : GlobalTheory.Mem.Chr.Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ S) :
    ev w (part a S : AdeleRing (𝓞 L) L) = ev w (a : AdeleRing (𝓞 L) L) := by
  rw [part, Units.coe_prod, map_prod, Finset.prod_eq_single_of_mem w hw (fun v _ hv => ev_local_ne hv.symm _),
    ev_local_self]
  rfl

theorem ev_part_not_mem (a : GlobalTheory.Mem.Chr.Ideles L) {S : Finset (HeightOneSpectrum (𝓞 L))} {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∉ S) : ev w (part a S : AdeleRing (𝓞 L) L) = 1 := by
  rw [part, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun v hv => ev_local_ne (fun e : w = v => hw (e ▸ hv)) _

theorem part_fst (a : GlobalTheory.Mem.Chr.Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))) : (part a S : AdeleRing (𝓞 L) L).1 = 1 := by
  have h : finPartI L (part a S) = part a S := by
    rw [part, map_prod]
    exact Finset.prod_congr rfl fun v _ => Units.ext rfl
  rw [← h]
  rfl

theorem tendsto_part_val {a : GlobalTheory.Mem.Chr.Ideles L} (ha : a ∈ unitIdl L) (h1 : (a : AdeleRing (𝓞 L) L).1 = 1) :
    Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L)) atTop (𝓝 (a : AdeleRing (𝓞 L) L)) := by
  have h2 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).2) atTop (𝓝 (a : AdeleRing (𝓞 L) L).2) := by
    refine tendsto_finiteAdele _ _ (fun S v => ?_) (fun v => (ha v).le) fun v => ?_
    · show ev v (part a S : AdeleRing (𝓞 L) L) ∈ _
      by_cases hv : v ∈ S
      · rw [ev_part_mem a hv]
        exact (ha v).le
      · rw [ev_part_not_mem a hv]
        exact one_mem _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ({v} : Finset _)] with S hS
      exact (ev_part_mem a (hS (Finset.mem_singleton_self v))).symm
  have h3 : Tendsto (fun S => (part a S : AdeleRing (𝓞 L) L).1) atTop (𝓝 (a : AdeleRing (𝓞 L) L).1) := by
    rw [h1]
    exact tendsto_const_nhds.congr fun S => (part_fst a S).symm
  exact h3.prodMk_nhds h2

theorem tendsto_part {a : GlobalTheory.Mem.Chr.Ideles L} (ha : a ∈ unitIdl L) (h1 : ∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) :
    Tendsto (part a) atTop (𝓝 a) := by
  have e : finPartI L a = a := finPartI_eq_self h1
  have e' : finPartI L a⁻¹ = a⁻¹ := by rw [map_inv, e]
  have t1 := tendsto_part_val ha (by rw [← e]; rfl)
  have t2 := tendsto_part_val ((unitIdl L).inv_mem ha) (by rw [← e']; rfl)
  simp only [← part_inv] at t2
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  exact t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp t2)


open Classical in
theorem eq_one_of_local : ∀ (L : Type) [Field L] [NumberField L] (ψ : GlobalTheory.Mem.Chr.Ideles L →* ℂˣ), Continuous ψ → ∀ a : GlobalTheory.Mem.Chr.Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (GlobalTheory.Mem.Chr.localIdele L v x) = 1) → ψ a = 1 := by
  intro L _ _ ψ hψ a ha h1 hl
  have t := (hψ.tendsto a).comp (tendsto_part ha h1)
  have e : ψ ∘ part a = fun _ => 1 := funext fun S => by
    show ψ (part a S) = 1
    rw [part, map_prod]
    exact Finset.prod_eq_one fun v _ => hl v _ rfl
  rw [e] at t
  exact tendsto_nhds_unique t tendsto_const_nhds

end GlobalTheory.Mem.LocTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMap
section
open NumberField IsDedekindDomain IsLocalRing TensorProduct

namespace GlobalTheory.LidxBaseChange

theorem length_eq_of_residue (R O M : Type*) [CommRing R] [CommRing O] [IsLocalRing O] [Algebra R O]
    [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower R O M]
    (h1 : Module.length R (ResidueField O) = 1) : Module.length R M = Module.length O M := by
  have step : ∀ {p q : Submodule O M}, p ⋖ q → Module.length R q = Module.length R p + 1 := by
    intro p q h
    let f : p →ₗ[O] q := Submodule.inclusion h.le
    have key : IsSimpleModule O (q ⧸ f.range) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple h.le]
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    rw [eq_maximalIdeal hm] at e
    let g : q →ₗ[O] ResidueField O := e.comp f.range.mkQ
    have : Function.Injective f := Submodule.inclusion_injective _
    have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
    have : Function.Exact f g := LinearMap.exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
    rw [Module.length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R)
      (by simpa) (by simpa) (by simpa), h1]
  by_cases h : IsFiniteLength O M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, Module.length R (s k) = k by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact Module.length_top.symm
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => simpa [hi] using step (s.step i)
  · have : ¬ IsFiniteLength R M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
    rw [← Module.length_ne_top_iff, not_ne_iff] at h this
    rw [h, this]

theorem length_residue_atPrime {R : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] :
    Module.length R (ResidueField (Localization.AtPrime P)) = 1 := by
  rw [Module.length_eq_of_surjective (S := R) (R := ResidueField (Localization.AtPrime P))
    (Ideal.algebraMap_residueField_surjective P)]
  simp

theorem mem_localization_iff {R W : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P X ↔ x ∈ Submodule.span (Localization.AtPrime P) (X : Set W) := by
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
    have : x = (↑u⁻¹ : Localization.AtPrime P) • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime P) s x]
      change x = _ • (algebraMap R (Localization.AtPrime P) ((⟨s, hs⟩ : P.primeCompl) : R)) • x
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, P.primeCompl.one_mem, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨s, hs, hy⟩ := hy
      obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj P.primeCompl c
      refine ⟨s * t, P.primeCompl.mul_mem hs t.2, ?_⟩
      have : (s * (t : R)) • c • y = a • s • y := by
        rw [mul_smul, ← algebraMap_smul (Localization.AtPrime P) (t : R), smul_smul _ c, mul_comm _ c]
        dsimp only at h
        rw [h, algebraMap_smul, smul_comm]
      rw [this]
      exact X.smul_mem a hy

theorem length_localized_eq₂ {R W : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X Y : Submodule R W) :
    Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ P X) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P Y).comap (Formalism.HermitianLatticesTheory.localization₂ P X).subtype) =
      Module.length (Localization.AtPrime P) (↥(Submodule.span (Localization.AtPrime P) (X : Set W)) ⧸
        (Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype) := by
  rw [← length_eq_of_residue R _ _ (length_residue_atPrime P)]
  have hX : Formalism.HermitianLatticesTheory.localization₂ P X = (Submodule.span (Localization.AtPrime P) (X : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P X x
  have hY : Formalism.HermitianLatticesTheory.localization₂ P Y = (Submodule.span (Localization.AtPrime P) (Y : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P Y x
  rw [hX, hY]
  exact (Submodule.Quotient.restrictScalarsEquiv R ((Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype)).length_eq

theorem span_image_inf {A O V W : Type*} [CommRing A] [CommRing O] [Algebra A O] [Module.Flat A O]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [Module O W] [IsScalarTower A O W]
    (φ : V →ₗ[A] W) (h : Function.Injective (φ.liftBaseChange O)) (M N : Submodule A V) :
    Submodule.span O (φ '' (M : Set V)) ⊓ Submodule.span O (φ '' (N : Set V)) =
      Submodule.span O (φ '' ((M ⊓ N : Submodule A V) : Set V)) := by
  have key : ∀ X : Submodule A V,
      Submodule.span O (φ '' (X : Set V)) = (X.baseChange O).map (φ.liftBaseChange O) := fun X => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => by simp
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ h]

theorem exists_lidx_eq_mul (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    {d d' : ℕ} (ψ : (Fin d → K) →ₗ[K] (Fin d' → K')) (hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)))
    (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')) [P'.asIdeal.LiesOver P.asIdeal] :
    ∃ e : ℕ, 0 < e ∧ ∀ A B : Submodule (𝓞 K) (Fin d → K),
      Formalism.HermitianLatticesTheory.lidx P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (A : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (B : Set (Fin d → K)))) = Formalism.HermitianLatticesTheory.lidx P.asIdeal A B * e := by
  have hPm := P.isMaximal
  have hPm' := P'.isMaximal
  let O := Localization.AtPrime P.asIdeal
  let O' := Localization.AtPrime P'.asIdeal
  letI : Algebra O K := IsLocalization.localizationAlgebraOfSubmonoidLe O K P.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) P.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K) O K := IsLocalization.localization_isScalarTower_of_submonoid_le O K _ _ _
  letI : Algebra O' K' := IsLocalization.localizationAlgebraOfSubmonoidLe O' K' P'.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K')) P'.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K') O' K' := IsLocalization.localization_isScalarTower_of_submonoid_le O' K' _ _ _
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl O K
  have : IsFractionRing O' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P'.asIdeal.primeCompl O' K'
  have : IsScalarTower (𝓞 K) O' K' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') O', ← IsScalarTower.algebraMap_apply (𝓞 K') O' K',
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra O O' := Localization.AtPrime.algebraOfLiesOver P.asIdeal P'.asIdeal
  have : Localization.AtPrime.IsLiesOverAlgebra P.asIdeal P'.asIdeal := inferInstance
  have : IsScalarTower (𝓞 K) O O' := inferInstance
  have : IsLocalHom (algebraMap O O') := inferInstance
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot _
  have : IsDiscreteValuationRing O' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K') P'.ne_bot _
  have : FaithfulSMul O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  have : IsLocalHom (algebraMap O O) := inferInstance
  refine ⟨(maximalIdeal O').ramificationIdx O, ramificationIdx_maximalIdeal_pos O O', ?_⟩
  have hlen : ∀ M N : Submodule (𝓞 K) (Fin d → K), N ≤ M →
      Formalism.HermitianLatticesTheory.locLen P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (M : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (N : Set (Fin d → K)))) =
        Formalism.HermitianLatticesTheory.locLen P.asIdeal M N * (maximalIdeal O').ramificationIdx O := by
    intro M N hNM
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [length_localized_eq₂, length_localized_eq₂, Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    have h1 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O' K') ψ _ hψ N M hNM
    have h2 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O K)
      (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) (Pi.basisFun K (Fin d))
      (Pi.basisFun K (Fin d)).linearIndependent N M hNM
    rw [length_fibre_eq_ramificationIdx O O'] at h1
    have h3 : Module.length O (O ⧸ (maximalIdeal O).map (algebraMap O O)) = 1 := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      have h4 := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O 1
      rw [pow_one] at h4
      exact_mod_cast h4
    rw [h3, mul_one, LinearMap.id_coe, Set.image_id, Set.image_id] at h2
    rw [h1, h2, ENat.toNat_mul, ENat.toNat_coe]
  intro A B
  have hinj := Formalism.BasicNotions.FBC.liftBaseChange_injective_top (A := 𝓞 K) (IsFractionRing.injective (𝓞 K') K') ψ _ hψ
  have hinf := span_image_inf _ hinj A B
  unfold Formalism.HermitianLatticesTheory.lidx
  erw [hinf]
  erw [hlen A _ inf_le_left, hlen B _ inf_le_right]
  push_cast
  ring

theorem lidx_ne_zero_iff : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  intro K K' _ _ _ _ φ d d' G hG P P' hP A B _ _
  letI : Algebra K K' := φ.toAlgebra
  have : P'.asIdeal.LiesOver P.asIdeal := ⟨Ideal.ext fun x => hP x (algebraMap (𝓞 K) (𝓞 K') x) rfl⟩
  let ψ : (Fin d → K) →ₗ[K] (Fin d' → K') :=
    (G.mulVecLin.restrictScalars K) ∘ₗ (Algebra.linearMap K K').compLeft (Fin d)
  have hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)) := by
    have h := (Pi.basisFun K' (Fin d)).linearIndependent.map' G.mulVecLin (LinearMap.ker_eq_bot.2 hG.1)
    have e : ψ ∘ Pi.basisFun K (Fin d) = G.mulVecLin ∘ Pi.basisFun K' (Fin d) := by
      funext i
      simp only [ψ, Function.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    rw [e]
    exact h
  obtain ⟨e, he, h⟩ := exists_lidx_eq_mul K K' ψ hψ P P'
  have h' := h A B
  have hf : (fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) = ψ := rfl
  rw [hf, h']
  simp [he.ne']

end GlobalTheory.LidxBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbTiePosDef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dotProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem hAt_single_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

theorem posDef_map_of_posAt [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : PosAt H v) : (H.map v.embedding).PosDef := by
  have herm : (H.map v.embedding).IsHermitian := by
    ext i j
    have := h.1 (Pi.single j 1) (Pi.single i 1)
    rw [hAt_single_single, hAt_single_single] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [this]
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have psd : (H.map v.embedding).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun z => ?_
    induction z using hd.induction_on with
    | hp =>
      refine isClosed_le continuous_const ?_
      exact Continuous.dotProduct (continuous_star) (Continuous.matrix_mulVec continuous_const continuous_id)
    | ih y =>
      have hy : Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) y = fun i => v.embedding (y i) := rfl
      rw [hy, ← hAt_eq_dotProduct]
      have hs := h.1 y y
      have him : (hAt H v y y).im = 0 := by
        have := congrArg Complex.im hs
        simp at this
        linarith
      rw [Complex.nonneg_iff]
      refine ⟨?_, him.symm⟩
      by_cases hy0 : y = 0
      · subst hy0
        simp [hAt]
      · exact (h.2 y hy0).le
  rw [psd.posDef_iff_det_ne_zero]
  show (v.embedding.mapMatrix H).det ≠ 0
  rw [← RingHom.map_det]
  intro h0
  rw [map_eq_zero] at h0
  obtain ⟨y, hy0, hHy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : hAt H v y y = 0 := by
    rw [hAt_eq_dotProduct]
    have : (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) = 0 := by
      funext i
      have := RingHom.map_mulVec v.embedding H y i
      rw [hHy] at this
      simpa [Function.comp_def] using this.symm
    rw [this, dotProduct_zero]
  have := h.2 y hy0
  rw [hz] at this
  simp at this

end GlobalTheory.AmbTiePosDef
end

