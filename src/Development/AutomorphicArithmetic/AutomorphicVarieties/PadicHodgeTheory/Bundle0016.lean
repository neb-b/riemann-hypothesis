module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import GroundTheory.LocalFields.MainTheorem
public import GroundTheory.LocalFields.PrincipalUnitsRank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.Bundle0001
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.LocalFields.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalClassFieldTheoryOfOpenEmbedding
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology

private theorem ag_lift {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CommGroup C]
    [TopologicalSpace C] [T2Space C] (q : G →* C) (hq : Continuous q) :
    ∃ F : TopologicalAbelianization G →* C, Continuous F ∧ ∀ g : G, F g = q g := by
  have hle : (commutator G).topologicalClosure ≤ q.ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker q)
      (isClosed_singleton.preimage hq)
  refine ⟨QuotientGroup.lift _ q hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 hq

private theorem ag_map {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] (f : G →* G') (hf : Continuous f) :
    ∃ F : TopologicalAbelianization G →* TopologicalAbelianization G', Continuous F ∧ ∀ g : G, F g = (f g : G') := by
  set M := (commutator G').topologicalClosure
  have hker : ((QuotientGroup.mk' M).comp f).ker = M.comap f := by
    ext x
    simp
  have hle : (commutator G).topologicalClosure ≤ M.comap f := by
    apply Subgroup.topologicalClosure_minimal
    · rw [← hker]
      exact Abelianization.commutator_subset_ker _
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hf
  refine ⟨QuotientGroup.map _ M f hle, ?_, fun g => rfl⟩
  exact continuous_coinduced_dom.2 (continuous_quotient_mk'.comp hf)

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem ag_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ε : G ≃* (Ω ≃ₐ[K] Ω))
    (hε : Continuous ε) (hε' : Continuous ε.symm) :
    ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative ProfiniteInteger),
      Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧
      (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex →
        ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧
      Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((ord (y : K) : ℤ) : ProfiniteInteger)) ∧
      ∀ g : G, D (QuotientGroup.mk' _ g) = unramifiedDegree K Ω (ε g) := by
  obtain ⟨F, hF, hFe⟩ := ag_map (ε : G →* (Ω ≃ₐ[K] Ω)) hε
  obtain ⟨F', hF', hF'e⟩ := ag_map (ε.symm : (Ω ≃ₐ[K] Ω) →* G) hε'
  have hFF' : ∀ b, F (F' b) = b := by
    intro b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    rw [hF'e, hFe]
    simp
  have hF'F : ∀ a, F' (F a) = a := by
    intro a
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    rw [hFe, hF'e]
    simp
  obtain ⟨U, hU, hUe⟩ := ag_lift (unramifiedDegree K Ω) continuous_unramifiedDegree
  set L := localReciprocityLimit K Ω
  have hLart : ∀ x, localArtinMap K Ω x = topologicalAbelianizationEquiv K Ω (L x) :=
    fun x => localArtinMap_apply x
  have hLc : Continuous L := by
    have h : (L : Kˣ → _) = (topologicalAbelianizationEquiv K Ω).symm ∘ localArtinMap K Ω := by
      funext x
      simp [hLart]
    rw [h]
    exact (topologicalAbelianizationEquiv K Ω).symm.continuous.comp continuous_localArtinMap
  have hLi : Function.Injective L := by
    intro x y hxy
    apply injective_localArtinMap (K := K) (Ω := Ω)
    rw [hLart, hLart, hxy]
  have hU' : ∀ x : Kˣ, U (L x) = Multiplicative.ofAdd ((ord (x : K) : ℤ) : ProfiniteInteger) := by
    intro x
    obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (L x)
    rw [← hg, hUe]
    exact unramifiedDegree_of_mk_eq_localReciprocityLimit hg
  refine ⟨F'.comp L, U.comp F, hF'.comp hLc, ?_, ?_, ?_, hU.comp hF, ?_, ?_⟩
  · intro x y hxy
    apply hLi
    have := congrArg F hxy
    simpa [hFF'] using this
  · exact (Function.Surjective.denseRange (fun a => ⟨F a, hF'F a⟩)).comp
      (denseRange_localReciprocityLimit (K := K) (Ω := Ω)) hF'
  · intro H hHo hHf
    let H' : openFiniteIndex Kˣ := ⟨H, hHo, hHf⟩
    let ψ := ((artinCoord K Ω H').comp
      (topologicalAbelianizationEquiv K Ω).toMulEquiv.toMonoidHom).comp F
    have hψ : Continuous ψ :=
      (continuous_artinCoord H').comp ((topologicalAbelianizationEquiv K Ω).continuous.comp hF)
    haveI := openCompletion.discreteTopology_quotient H'
    refine ⟨ψ.ker, ?_, ?_⟩
    · exact (isOpen_discrete ({1} : Set (Kˣ ⧸ (H : Subgroup Kˣ)))).preimage hψ
    · ext y
      simp only [Subgroup.mem_comap, MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, hFF']
      change artinCoord K Ω H' (topologicalAbelianizationEquiv K Ω (L y)) = 1 ↔ y ∈ H
      rw [← hLart, artinCoord_localArtinMap]
      exact QuotientGroup.eq_one_iff y
  · intro y
    simp [hFF', hU']
  · intro g
    simp [hFe, hUe]

open GroundTheory.LocalField ValuativeRel IsLocalRing in
private theorem ag_char (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Algebra ℚ_[l] k] [ValuativeExtension ℚ_[l] k] : CharP 𝓀[k] l := by
  rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
  have hnu : ¬ IsUnit ((l : 𝒪[k])) := by
    rintro ⟨u, hu⟩
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * (l : 𝒪[k]) = 1 := by
      rw [← hu]
      simp
    have h2 : ((((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k)) = algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) := by
      have := congrArg (fun x : 𝒪[k] => (x : k)) h1
      simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one] at this
      rw [map_inv₀, map_natCast]
      exact eq_inv_of_mul_eq_one_left this
    have h3 : algebraMap ℚ_[l] k ((l : ℚ_[l])⁻¹) ∈ (ValuativeRel.valuation k).integer := by
      rw [← h2]
      exact (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k])).2
    rw [algebraMap_mem_integer_iff, PadicRank.mem_integer_padic_iff] at h3
    rw [norm_inv, Padic.norm_p, inv_inv] at h3
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    linarith
  have hmem : (l : 𝒪[k]) ∈ maximalIdeal 𝒪[k] := (mem_maximalIdeal _).2 hnu
  rw [← map_natCast (residue 𝒪[k]) l]
  exact (residue_eq_zero_iff _).2 hmem

theorem UpperTheory.local_class_field_theory_of_open_embedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), ∃ (K : Type) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K) (_ : IsNonarchimedeanLocalField K) (_ : Algebra ℚ_[l] K) (_ : ValuativeExtension ℚ_[l] K) (_ : FiniteDimensional ℚ_[l] K), φ.range.index = Module.finrank ℚ_[l] K ∧ ∃ (θ : Kˣ →* TopologicalAbelianization G) (D : TopologicalAbelianization G →* Multiplicative GroundTheory.LocalField.Abstract.ProfiniteInteger), Continuous θ ∧ Function.Injective θ ∧ DenseRange θ ∧ (∀ H : Subgroup Kˣ, IsOpen (H : Set Kˣ) → H.FiniteIndex → ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ V.comap θ = H) ∧ Continuous D ∧ (∀ y : Kˣ, D (θ y) = Multiplicative.ofAdd ((GroundTheory.LocalField.ord (y : K) : ℤ) : GroundTheory.LocalField.Abstract.ProfiniteInteger)) ∧ ∀ g : G, φ g ∈ Iq l ↔ D (QuotientGroup.mk' _ g) = 1 := by
  intro l _ G _ _ _ φ hφ
  obtain ⟨K, e, he, he', hcomp, -, hidx, -⟩ := openField φ hφ
  haveI hfin : FiniteDimensional ℚ_[l] K.1 := K.2
  obtain ⟨vr, tp, hloc, hext⟩ :=
    GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] K.1
  letI := vr
  letI := tp
  haveI := hloc
  haveI := hext
  haveI : Algebra.IsAlgebraic K.1 (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) K.1
  haveI : IsAlgClosure K.1 (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure K.1 (Om l) := inferInstance
  obtain ⟨hc1, hc2⟩ := GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let ε : G ≃* Gal(Om l/K.1) := e.trans K.1.fixingSubgroupEquiv
  have hε : Continuous ε := hc1.comp he
  have hε' : Continuous ε.symm := he'.comp hc2
  obtain ⟨θ, D, h1, h2, h3, h4, h5, h6, hD⟩ := ag_field K.1 (Om l) ε hε hε'
  refine ⟨K.1, inferInstance, vr, tp, hloc, inferInstance, hext, hfin, hidx, θ, D,
    h1, h2, h3, h4, h5, h6, ?_⟩
  intro g
  have hεg : ∀ x, (ε g) x = φ g x := by
    intro x
    rw [← hcomp]
    rfl
  haveI := ag_char l K.1
  rw [hD g, GroundTheory.LocalField.unramifiedDegree_eq_one_iff]
  simp only [Iq, MaximalUnramifiedExtension, GroundTheory.LocalField.mem_fixingSubgroup_adjoin_iff,
    GroundTheory.LocalField.mem_unramifiedRoots_iff, hεg]
  constructor
  · rintro h ξ ⟨m, hm, hξ⟩
    apply h
    refine ⟨m, ?_, ?_, hξ⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hpos
      · simp at hm
      · exact hpos
    · intro hdvd
      exact hm ((CharP.cast_eq_zero_iff _ l m).2 hdvd)
  · rintro h ξ ⟨m, -, hml, hξ⟩
    apply h
    exact ⟨m, fun h0 => hml ((CharP.cast_eq_zero_iff _ l m).1 h0), hξ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MuNone
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc Topology

private theorem mn_sep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (h : TopologicalAbelianization G) (hh : h ≠ 1) :
    ∃ V : Subgroup (TopologicalAbelianization G), IsOpen (V : Set (TopologicalAbelianization G)) ∧ h ∉ V := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective h
  have hg : g ∉ (commutator G).topologicalClosure := fun hm => hh ((QuotientGroup.eq_one_iff g).2 hm)
  have hS : IsOpen {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} :=
    (Subgroup.isClosed_topologicalClosure _).isOpen_compl.preimage (continuous_mul_const g)
  have h1 : (1 : G) ∈ {x : G | x * g ∉ ((commutator G).topologicalClosure : Set G)} := by
    show 1 * g ∉ ((commutator G).topologicalClosure : Set G)
    rw [one_mul]
    exact hg
  obtain ⟨W, hW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hS h1
  refine ⟨(W : Subgroup G).map (QuotientGroup.mk' _), ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ W.isOpen
  · rintro ⟨w, hw, he⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at he
    exact hW (inv_mem hw) he

private theorem mn_core {A M : Type} [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [CommGroup M] (r : M →* A) (hr : DenseRange r) {q : ℕ} (hq : q ≠ 0)
    (hM : ∀ x : M, x ^ q = 1 → x = 1)
    (hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set A, IsOpen V ∧ 1 ∈ V ∧ ∀ x, r x ∈ V → ∃ z, x = z ^ n)
    (a : A) (ha : a ^ q = 1) (n : ℕ) (hn : n ≠ 0) : ∃ z, a = z ^ n := by
  have hP : IsClosed (Set.range fun z : A => z ^ n) := (isCompact_range (continuous_pow n)).isClosed
  obtain ⟨V, hVo, hV1, hV⟩ := hopen (q * n) (mul_ne_zero hq hn)
  suffices hs : a ∈ closure (Set.range fun z : A => z ^ n) by
    rw [hP.closure_eq] at hs
    obtain ⟨z, hz⟩ := hs
    exact ⟨z, hz.symm⟩
  rw [mem_closure_iff]
  intro o ho hao
  have hW : IsOpen (o ∩ {y : A | y ^ q ∈ V}) := ho.inter (hVo.preimage (continuous_pow q))
  have haW : a ∈ o ∩ {y : A | y ^ q ∈ V} := ⟨hao, by show a ^ q ∈ V; rw [ha]; exact hV1⟩
  obtain ⟨x, hx1, hx2⟩ := hr.exists_mem_open hW ⟨a, haW⟩
  have hx3 : r (x ^ q) ∈ V := by
    rw [map_pow]
    exact hx2
  obtain ⟨z, hz⟩ := hV (x ^ q) hx3
  have hxz : x = z ^ n := by
    have h1 : (x * (z ^ n)⁻¹) ^ q = 1 := by
      rw [mul_pow, inv_pow, ← pow_mul, mul_comm n q, ← hz, mul_inv_cancel]
    exact mul_inv_eq_one.mp (hM _ h1)
  exact ⟨r x, hx1, r z, by rw [hxz, map_pow]⟩

open GroundTheory.LocalField ValuativeRel GroundTheory.LocalField.Abstract in
private theorem mn_field (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    {q : ℕ} (hq : q ≠ 0) (hM : ∀ x : Kˣ, x ^ q = 1 → x = 1)
    (a : TopologicalAbelianization (Ω ≃ₐ[K] Ω)) (ha : a ^ q = 1) : a = 1 := by
  haveI : IsClosed ((commutator (Ω ≃ₐ[K] Ω)).topologicalClosure : Set (Ω ≃ₐ[K] Ω)) :=
    Subgroup.isClosed_topologicalClosure _
  have hopen : ∀ n : ℕ, n ≠ 0 → ∃ V : Set (TopologicalAbelianization (Ω ≃ₐ[K] Ω)), IsOpen V ∧ 1 ∈ V ∧
      ∀ x, localReciprocityLimit K Ω x ∈ V → ∃ z, x = z ^ n := by
    intro n hn
    haveI : Finite (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) := finite_quotient_range_pow_of_charZero hn
    let H : openFiniteIndex Kˣ := ⟨(powMonoidHom n : Kˣ →* Kˣ).range,
      isOpen_range_pow (Nat.cast_ne_zero.mpr hn), Subgroup.finiteIndex_of_finite_quotient⟩
    haveI := openCompletion.discreteTopology_quotient H
    refine ⟨(fun b => artinCoord K Ω H (topologicalAbelianizationEquiv K Ω b)) ⁻¹' {1}, ?_, ?_, ?_⟩
    · exact (isOpen_discrete _).preimage
        ((continuous_artinCoord H).comp (topologicalAbelianizationEquiv K Ω).continuous)
    · show artinCoord K Ω H (topologicalAbelianizationEquiv K Ω 1) = 1
      rw [map_one, map_one]
    · intro x hx
      have hx' : artinCoord K Ω H (topologicalAbelianizationEquiv K Ω (localReciprocityLimit K Ω x)) = 1 := hx
      rw [← localArtinMap_apply, artinCoord_localArtinMap, QuotientGroup.eq_one_iff] at hx'
      obtain ⟨z, hz⟩ := hx'
      exact ⟨z, hz.symm⟩
  have hall : ∀ n : ℕ, n ≠ 0 → ∃ z, a = z ^ n := fun n hn =>
    mn_core (localReciprocityLimit K Ω) denseRange_localReciprocityLimit hq hM hopen a ha n hn
  by_contra hne
  obtain ⟨V, hVo, haV⟩ := mn_sep a hne
  haveI : Finite (TopologicalAbelianization (Ω ≃ₐ[K] Ω) ⧸ V) := Subgroup.quotient_finite_of_isOpen V hVo
  haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨z, hz⟩ := hall V.index Subgroup.FiniteIndex.index_ne_zero
  exact haV (hz ▸ Subgroup.pow_index_mem V z)

private theorem mn_map {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : G →* H) (hf : Continuous f) {g : G}
    (hg : g ∈ (commutator G).topologicalClosure) : f g ∈ (commutator H).topologicalClosure := by
  have hc : commutator G ≤ (commutator H).comap f := by
    rw [← Subgroup.map_le_iff_le_comap, commutator_def, commutator_def, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hcl : (commutator G).topologicalClosure ≤ ((commutator H).topologicalClosure).comap f :=
    Subgroup.topologicalClosure_minimal _ (hc.trans (Subgroup.comap_mono (Subgroup.le_topologicalClosure _)))
      ((Subgroup.isClosed_topologicalClosure _).preimage hf)
  exact hcl hg

private theorem mn_cyc {l : ℕ} [Fact l.Prime] (σ : GQ l) {ζ : Om l} (h1 : ζ ^ l = 1) (h2 : ζ ≠ 1)
    (h : σ ζ = ζ) : PadicInt.toZMod ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have hp : l.Prime := Fact.out
  have hprim : IsPrimitiveRoot ζ l := by
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) h2
    · exact h
  have hs := cyclotomicCharacter.spec (L := Om l) l (n := 1)
    (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ (by rw [pow_one]; exact h1)
  have hcyc : (cyc l l σ : ℤ_[l]ˣ) =
      cyclotomicCharacter (Om l) l (MulSemiringAction.toRingAut (GQ l) (Om l) σ) := rfl
  rw [← hcyc] at hs
  set x : ℤ_[l] := ((cyc l l σ : ℤ_[l]ˣ) : ℤ_[l]) with hx
  have hσ : (MulSemiringAction.toRingAut (GQ l) (Om l) σ) ζ = ζ := h
  have hs' : ζ ^ (PadicInt.toZModPow 1 x).val = ζ ^ 1 := by
    calc _ = _ := hs.symm
      _ = ζ := hσ
      _ = ζ ^ 1 := (pow_one ζ).symm
  have hlt : (PadicInt.toZModPow 1 x).val < l :=
    lt_of_lt_of_eq (ZMod.val_lt (PadicInt.toZModPow (p := l) 1 x)) (pow_one l)
  have hk : (PadicInt.toZModPow 1 x).val = 1 := hprim.pow_inj hlt hp.one_lt hs'
  have hk' : PadicInt.toZModPow 1 x = 1 := by
    rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow 1 x), hk, Nat.cast_one]
  have hmem : x - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 1) := by
    rw [RingHom.mem_ker, RingHom.map_sub, hk', map_one, sub_self]
  rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hmem
  exact hmem

theorem UpperTheory.V.Loc.muNone :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ), (∃ g : G, PadicInt.toZMod ((cyc l l (φ g) : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∀ g : G, (QuotientGroup.mk' _ g : TopologicalAbelianization G) ∈ CommGroup.primaryComponent (TopologicalAbelianization G) l → g ∈ (commutator G).topologicalClosure := by
  intro l _ G _ _ _ φ hφ hex g hg
  obtain ⟨g0, hg0⟩ := hex
  have hp : l.Prime := Fact.out
  obtain ⟨K, e, he1, he2, hφe, -⟩ := openField φ hφ
  haveI : FiniteDimensional ℚ_[l] K.1 := K.2
  set L : IntermediateField ℚ_[l] (Om l) := K.1 with hL
  haveI : Algebra.IsAlgebraic L (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) L
  haveI : IsAlgClosure L (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : IsSepClosure L (Om l) := inferInstance
  obtain ⟨vr, ts, hloc, -⟩ := GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension ℚ_[l] L
  let ψ : G →* Gal(Om l/L) := L.fixingSubgroupEquiv.toMonoidHom.comp e.toMonoidHom
  have hψ : Continuous ψ := (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).1.comp he1
  let ψi : Gal(Om l/L) →* G := e.symm.toMonoidHom.comp L.fixingSubgroupEquiv.symm.toMonoidHom
  have hψi : Continuous ψi := he2.comp (GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) L).2
  have hψψ : ψi (ψ g) = g :=
    (congrArg e.symm (L.fixingSubgroupEquiv.symm_apply_apply (e g))).trans (e.symm_apply_apply g)
  obtain ⟨n, hn⟩ := hg
  have hgn : g ^ (l ^ n) ∈ (commutator G).topologicalClosure := by
    rw [← map_pow, QuotientGroup.mk'_apply] at hn
    exact (QuotientGroup.eq_one_iff _).1 hn
  have hM : ∀ x : Lˣ, x ^ (l ^ n) = 1 → x = 1 := by
    intro x hx
    by_contra hx1
    obtain ⟨m, hmn, hm⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hx)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hx1 (orderOf_eq_one_iff.1 (by rw [hm, pow_zero]))
    set y := x ^ (l ^ (m - 1)) with hy
    have hy1 : y ^ l = 1 := by
      rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0), ← hm, pow_orderOf_eq_one]
    have hy2 : y ≠ 1 := by
      intro h
      have h3 := orderOf_dvd_of_pow_eq_one h
      rw [hm, Nat.pow_dvd_pow_iff_le_right hp.one_lt] at h3
      omega
    have hz1 : (((y : L) : Om l)) ^ l = 1 := by
      have h4 := congrArg (fun u : Lˣ => ((u : L) : Om l)) hy1
      simpa using h4
    have hz2 : (((y : L) : Om l)) ≠ 1 := by
      intro h
      apply hy2
      apply Units.ext
      apply Subtype.ext
      simpa using h
    have hσ : φ g0 ∈ GK K := by
      rw [← hφe]
      exact (e g0).2
    have hfix : (φ g0) ((y : L) : Om l) = ((y : L) : Om l) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (y : L).2
    exact hg0 (mn_cyc (φ g0) hz1 hz2 hfix)
  have hψn : ψ g ^ (l ^ n) ∈ (commutator Gal(Om l/L)).topologicalClosure := by
    rw [← map_pow]
    exact mn_map ψ hψ hgn
  have ha : QuotientGroup.mk' (commutator Gal(Om l/L)).topologicalClosure (ψ g) = 1 := by
    refine mn_field L (Om l) (pow_ne_zero n hp.ne_zero) hM _ ?_
    rw [← map_pow, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hψn
  rw [← hψψ]
  exact mn_map ψi hψi ((QuotientGroup.eq_one_iff _).1 ha)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.V00
section
open Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc Topology NumberField IsDedekindDomain

theorem UpperTheory.V.Loc.v00 :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω] (U : Subgroup (G F Ω)) [U.Normal], IsOpen (U : Set (G F Ω)) → ∀ (g : G F Ω) (Sg : Finset (HeightOneSpectrum (𝓞 F))) (M : ℕ), M ≠ 0 → ∃ (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) (p : ℕ) (σ : G F Ω), w ∉ Sg ∧ p.Prime ∧ ¬ p ∣ M ∧ ¬ (p : ℤ) ∣ discr F ∧ ((p : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ normV w = p ∧ locDeg w = 1 ∧ IsPlaceOver A w ∧ Ine (F := F) A ≤ U ∧ Formalism.ConjugateSelfDual.IsFrob (F := F) A p σ ∧ σ⁻¹ * g ∈ U := by
  intro F Ω _ _ _ _ _ _ U hU hUo g Sg M hM
  classical
  set N : ℕ := M * (discr F).natAbs with hNdef
  have hN0 : N ≠ 0 := Nat.mul_ne_zero hM (Int.natAbs_ne_zero.mpr (discr_ne_zero F))
  have hI : (Ideal.span {(N : 𝓞 F)} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN0
  have hfin := Ideal.finite_factors hI
  obtain ⟨v, hvA, hinert, hram, B, hB, hBU, σ, hσ, hσg⟩ :=
    GlobalTheory.Published.cheb_holds F Ω U hUo hU g (Sg ∪ hfin.toFinset)
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hp : (normV v).Prime := by
    rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hinert
  have hpv : ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    rw [hnorm]; exact Ideal.absNorm_mem _
  have hNv : (N : 𝓞 F) ∉ v.asIdeal := by
    intro h
    apply hvA
    apply Finset.mem_union_right
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_le,
      Set.singleton_subset_iff]
    exact h
  have hdvd : ∀ k : ℕ, normV v ∣ k → (k : 𝓞 F) ∈ v.asIdeal := by
    rintro k ⟨c, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpv
  refine ⟨v, B, normV v, σ, fun h => hvA (Finset.mem_union_left _ h), hp, ?_, ?_, hpv, rfl,
    ?_, hB, hBU, hσ, ?_⟩
  · intro h
    exact hNv (hdvd N (dvd_mul_of_dvd_left h _))
  · intro h
    apply hNv
    apply hdvd
    apply dvd_mul_of_dvd_right
    exact Int.natCast_dvd.mp h
  · simp [locDeg, hram, hinert]
  · have h1 : g * σ⁻¹ ∈ U := by
      have := U.inv_mem hσg
      simpa using this
    have h2 := hU.conj_mem _ h1 σ⁻¹
    simpa [mul_assoc] using h2
end

