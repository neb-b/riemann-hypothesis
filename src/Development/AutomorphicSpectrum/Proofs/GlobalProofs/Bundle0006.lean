module

public import Mathlib
public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.ContinuousCochains
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0002
public import GroundTheory.AutomorphicForms.MeasuresGL

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteContinuousCrossedHomomorphisms
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Cocycles

section Algebra

variable {k G V : Type} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {f : G → V}

theorem cocycle_map_one (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : f 1 = 0 := by
  simpa using hf 1 1

theorem cocycle_map_inv (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (a : G) :
    f a⁻¹ = -ρ a⁻¹ (f a) := by
  have h := hf a⁻¹ a
  rw [inv_mul_cancel, cocycle_map_one hf] at h
  exact eq_neg_of_add_eq_zero_left h.symm

def cocycleKer (ρ : Representation k G V) (f : G → V)
    (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) : Subgroup G where
  carrier := {g | ρ g = 1 ∧ f g = 0}
  one_mem' := ⟨map_one ρ, cocycle_map_one hf⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
    rw [hf, ha', hb', map_zero, add_zero]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    have h1 : ρ a⁻¹ = 1 := by
      have h2 : ρ a⁻¹ * ρ a = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      rwa [ha, mul_one] at h2
    refine ⟨h1, ?_⟩
    rw [cocycle_map_inv hf, ha', map_zero, neg_zero]

theorem mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) :
    g ∈ cocycleKer ρ f hf ↔ ρ g = 1 ∧ f g = 0 := by
  exact Iff.rfl

theorem cocycle_mul_mem (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) (g : G) {c : G}
    (hc : c ∈ cocycleKer ρ f hf) : f (g * c) = f g := by
  have hc' := ((mem_cocycleKer hf c).1 hc).2
  rw [hf, hc', map_zero, add_zero]

theorem inv_mul_mem_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) {a b : G}
    (h1 : f a = f b) (h2 : ρ a = ρ b) : a⁻¹ * b ∈ cocycleKer ρ f hf := by
  refine (mem_cocycleKer hf _).2 ⟨?_, ?_⟩
  · rw [map_mul, ← h2, ← map_mul, inv_mul_cancel, map_one]
  · rw [hf, cocycle_map_inv hf, h1, neg_add_cancel]

theorem injective_out_cocycleKer (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    Function.Injective fun q : G ⧸ cocycleKer ρ f hf =>
      ((f q.out, ⇑(ρ q.out)) : V × (V → V)) := by
  intro q₁ q₂ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h2' : ρ q₁.out = ρ q₂.out := LinearMap.coe_injective h2
  rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂, QuotientGroup.eq]
  exact inv_mul_mem_cocycleKer hf h1 h2'

theorem index_cocycleKer [Finite V] (hf : ∀ g h : G, f (g * h) = f g + ρ g (f h)) :
    (cocycleKer ρ f hf).index ≠ 0 ∧
      (cocycleKer ρ f hf).index ≤ Nat.card (V × (V → V)) := by
  have hinj := injective_out_cocycleKer hf
  haveI : Finite (G ⧸ cocycleKer ρ f hf) := Finite.of_injective _ hinj
  exact ⟨Subgroup.index_ne_zero_of_finite, Nat.card_le_card_of_injective _ hinj⟩

theorem finite_right_invariant [Finite V] (H : Subgroup G) (hH : H.index ≠ 0) :
    {f : G → V | ∀ g, ∀ c ∈ H, f (g * c) = f g}.Finite := by
  haveI : Finite (G ⧸ H) := Nat.finite_of_card_ne_zero hH
  refine (Set.finite_range (fun φ : G ⧸ H → V => φ ∘ (QuotientGroup.mk : G → G ⧸ H))).subset ?_
  intro f₀ hf₀
  simp only [Set.mem_ofPred_eq] at hf₀
  refine ⟨fun q => f₀ q.out, ?_⟩
  funext g
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul H g
  simp only [Function.comp_apply]
  rw [hc]
  exact hf₀ g c c.2

end Algebra

theorem isOpen_cocycleKer {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A] [Finite A.V] {f : G → A.V}
    (hlc : IsLocallyConstant f) (hf : ∀ g h : G, f (g * h) = f g + A.ρ g (f h)) :
    IsOpen (cocycleKer A.ρ f hf : Set G) := by
  have hU : IsOpen ((⋂ v : A.V, (stabilizer A.ρ v : Set G)) ∩ {g | f g = 0}) :=
    (isOpen_iInter_of_finite fun v => IsDiscreteRep.isOpen_stabilizer v).inter (hlc.isOpen_fiber 0)
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  refine Filter.mem_of_superset (hU.mem_nhds ⟨Set.mem_iInter.2 fun v => ?_, cocycle_map_one hf⟩) ?_
  · rw [SetLike.mem_coe, mem_stabilizer, map_one]
    rfl
  · rintro g ⟨hg1, hg2⟩
    refine ⟨LinearMap.ext fun v => ?_, hg2⟩
    exact (mem_stabilizer A.ρ v g).1 (Set.mem_iInter.1 hg1 v)

theorem finite_cocycles : ∀ (k G : Type) [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (A : Rep.{0} k G) [IsDiscreteRep A], Finite A.V →
    (∀ N : ℕ, {H : Subgroup G | IsOpen (H : Set G) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite) →
    {f : G → A.V | IsLocallyConstant f ∧ ∀ g h : G, f (g * h) = f g + A.ρ g (f h)}.Finite := by
  intro k G _ _ _ _ A _ hV hN
  refine ((hN (Nat.card (A.V × (A.V → A.V)))).biUnion (fun H hH => finite_right_invariant H hH.2.1)).subset ?_
  rintro f ⟨hlc, hf⟩
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  exact ⟨cocycleKer A.ρ f hf, ⟨isOpen_cocycleKer A hlc hf, index_cocycleKer hf⟩,
    fun g c hc => cocycle_mul_mem hf g hc⟩

end GlobalTheory.CompanionTheory.Cocycles
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FinitelyManyOpenSubgroupsBoundedIndex
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

theorem openSubgroups_finite_of_fields_finite :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
      (S : Set (HeightOneSpectrum (𝓞 F))),
      (∀ N : ℕ, {E : IntermediateField F Ω | FiniteDimensional F E ∧ IsUnramifiedOutside S E ∧
        Module.finrank F E ≤ N}.Finite) →
      ∀ N : ℕ, {H : Subgroup (galUnramifiedOutside F Ω S) |
        IsOpen (H : Set (galUnramifiedOutside F Ω S)) ∧ H.index ≠ 0 ∧ H.index ≤ N}.Finite := by
  intro F Ω _ _ _ _ _ S hfin N
  haveI : IsGalois F Ω := IsSepClosure.isGalois
  let K := maxUnramifiedOutside F Ω S
  let φ : Subgroup (galUnramifiedOutside F Ω S) → IntermediateField F Ω :=
    fun H => IntermediateField.lift (F := K) (IntermediateField.fixedField (H : Subgroup Gal(K/F)))
  have key : ∀ H : Subgroup Gal(K/F), IsOpen (H : Set Gal(K/F)) →
      (IntermediateField.fixedField H).fixingSubgroup = H := fun H hH =>
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
  apply Set.Finite.of_finite_image (f := φ)
  · apply (hfin N).subset
    rintro _ ⟨H, ⟨hHo, -, hHN⟩, rfl⟩
    have hfix := key H hHo
    have hfd : FiniteDimensional F (IntermediateField.fixedField (H : Subgroup Gal(K/F))) :=
      (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfix]; exact hHo)
    let e : (IntermediateField.fixedField (H : Subgroup Gal(K/F))) ≃ₐ[F] (φ H) :=
      IntermediateField.equivMap _ (IntermediateField.val K)
    haveI : FiniteDimensional F (φ H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine ⟨inferInstance, (isUnramifiedOutside_iff_le_maxUnramifiedOutside S).2
      (IntermediateField.lift_le _), ?_⟩
    rw [← e.toLinearEquiv.finrank_eq, IntermediateField.finrank_eq_fixingSubgroup_index, hfix]
    exact hHN
  · intro H₁ h₁ H₂ h₂ h
    have h' := IntermediateField.lift_injective K h
    exact (key H₁ h₁.1).symm.trans ((congrArg IntermediateField.fixingSubgroup h').trans (key H₂ h₂.1))

end GlobalTheory.CompanionTheory.GlobalFiniteness
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
section
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open scoped Pointwise IntermediateField

namespace GlobalTheory.CompanionTheory.Glob.InertiaLift

section

variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]


omit [NumberField F] [NumberField K] in
theorem restrictScalars_smul (h : Ω ≃ₐ[K] Ω) (A : ValuationSubring Ω) :
    (h.restrictScalars F) • A = h • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl


omit [NumberField K] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] in
theorem mem_inertia_of_integers [IsAlgClosure F Ω] {A : ValuationSubring Ω} {σ : Ω ≃ₐ[F] Ω}
    (hd : σ • A = A) (hb : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) :
    σ ∈ Inertia (F := F) A := by
  refine ⟨hd, fun x hx => ?_⟩
  have hD : σ ∈ Dec (F := F) A := hd
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    refine not_lt.mp fun h => ?_
    have := (valuation_apply_lt_one_iff hD s).1 h
    rw [hs1] at this
    exact lt_irrefl _ this
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s * σ s * (σ x - x) = s * (σ t - t) + t * (s - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s * σ s * (σ x - x)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, hs1, one_mul]
      exact hb t ht
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation t * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) :=
            mul_le_mul_left hvt _
        _ < 1 := by rw [one_mul]; exact hb s hs
  rwa [Valuation.map_mul, Valuation.map_mul, hs1, hσs, one_mul, one_mul] at hv

noncomputable def actInt (g : Ω ≃ₐ[F] Ω) : IntCl K Ω ≃+* IntCl K Ω where
  toFun b := ⟨g b, ((isIntegral_int_of_isIntegral (F := K) b.2).map
    (g.toAlgHom.restrictScalars ℤ)).tower_top⟩
  invFun b := ⟨(g⁻¹ : Ω ≃ₐ[F] Ω) b, ((isIntegral_int_of_isIntegral (F := K) b.2).map
    ((g⁻¹ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)).tower_top⟩
  left_inv b := Subtype.ext (by
    show (g⁻¹ * g) (b : Ω) = b
    simp)
  right_inv b := Subtype.ext (mul_inv_apply (σ := g) (b : Ω))
  map_mul' a b := Subtype.ext (map_mul g (a : Ω) b)
  map_add' a b := Subtype.ext (map_add g (a : Ω) b)

theorem exists_residue_correction [IsAlgClosure K Ω] {A : ValuationSubring Ω}
    (w : HeightOneSpectrum (𝓞 K))
    (hA : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal)
    {σ₁ : Ω ≃ₐ[F] Ω} (hd : σ₁ ∈ Dec (F := F) A)
    (hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1) :
    ∃ h : Ω ≃ₐ[K] Ω, h • A = A ∧ ∀ b : IntCl K Ω, A.valuation (h (b : Ω) - σ₁ b) < 1 := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : IsGalois K Ω := {}
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set P := primeBelow (F := K) A with hPdef
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : P.LiesOver w.asIdeal := ⟨(under_primeBelow hA).symm⟩
  haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := 𝓞 K) P
    (by rw [show Ideal.under (𝓞 K) P = w.asIdeal from under_primeBelow hA]
        exact w.isMaximal)
  let e : IntCl K Ω ≃+* IntCl K Ω := actInt σ₁
  have hP : P = P.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
    exact (valuation_apply_lt_one_iff ((Dec (F := F) A).inv_mem hd) _).symm
  let φr : (IntCl K Ω ⧸ P) ≃+* (IntCl K Ω ⧸ P) := Ideal.quotientEquiv P P e hP
  let φ : (IntCl K Ω ⧸ P) ≃ₐ[𝓞 K ⧸ w.asIdeal] (IntCl K Ω ⧸ P) := AlgEquiv.ofRingEquiv (f := φr) (by
    intro r
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective r
    show φr (Ideal.Quotient.mk P (algebraMap (𝓞 K) (IntCl K Ω) z)) =
      Ideal.Quotient.mk P (algebraMap (𝓞 K) (IntCl K Ω) z)
    rw [Ideal.quotientEquiv_mk]
    refine Ideal.Quotient.eq.2 ?_
    exact hz z)
  obtain ⟨⟨h, hhP⟩, hh⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) w.asIdeal P φ
  have hhP' : h • P = P := hhP
  refine ⟨h, ?_, fun b => ?_⟩
  · refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (h • A) ↔ b' ∈ P
    rw [primeBelow_smul, hhP']
  · have h1 : Ideal.Quotient.mk P (h • b) = Ideal.Quotient.mk P (e b) :=
      DFunLike.congr_fun hh (Ideal.Quotient.mk P b)
    exact Ideal.Quotient.eq.1 h1

theorem exists_inertia_lift [IsAlgClosure F Ω] [IsAlgClosure K Ω] [Normal F K]
    (w : HeightOneSpectrum (𝓞 K)) {τ : K ≃ₐ[F] K} (hτ : τ ∈ w.asIdeal.inertia (K ≃ₐ[F] K)) :
    ∃ (A : ValuationSubring Ω) (σ : Ω ≃ₐ[F] Ω),
      (∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal) ∧
      σ ∈ Inertia (F := F) A ∧ ∀ x : K, σ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : IsGalois K Ω := {}
  have : IsGalois F Ω := {}
  obtain ⟨A, hA⟩ := exists_valuationSubring_over (Ω := Ω) w
  let σ₀ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω
  have hσ₀ : ∀ x : K, σ₀ (algebraMap K Ω x) = algebraMap K Ω (τ x) := fun x =>
    AlgEquiv.liftNormal_commutes τ Ω x
  have hτ' : ∀ z : 𝓞 K, τ • z - z ∈ w.asIdeal := fun z => AddSubgroup.mem_inertia.1 hτ z
  have hτi : ∀ z : 𝓞 K, τ⁻¹ • z - z ∈ w.asIdeal := fun z =>
    AddSubgroup.mem_inertia.1 (Subgroup.inv_mem _ hτ) z
  have hσ₀i : ∀ x : K, (σ₀⁻¹ : Ω ≃ₐ[F] Ω) (algebraMap K Ω x) = algebraMap K Ω ((τ⁻¹ : K ≃ₐ[F] K) x) := by
    intro x
    have h1 : algebraMap K Ω x = σ₀ (algebraMap K Ω ((τ⁻¹ : K ≃ₐ[F] K) x)) := by
      rw [hσ₀]
      congr 1
      show x = (τ * τ⁻¹) x
      simp
    rw [h1]
    show (σ₀⁻¹ * σ₀) _ = _
    simp
  have hA' : ∀ x : 𝓞 K, (σ₀ • A).valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ w.asIdeal := by
    intro x
    rw [smul_valuation_lt_one_iff, hσ₀i]
    have := hA (τ⁻¹ • x)
    refine (Iff.trans (by exact this) ?_)
    constructor
    · intro h
      have := w.asIdeal.sub_mem h (hτi x)
      simpa using this
    · intro h
      have := w.asIdeal.add_mem (hτi x) h
      simpa using this
  obtain ⟨h, hh⟩ := exists_smul_eq_of_over hA' hA
  let σ₁ : Ω ≃ₐ[F] Ω := h.restrictScalars F * σ₀
  have hσ₁ : ∀ x : K, σ₁ (algebraMap K Ω x) = algebraMap K Ω (τ x) := by
    intro x
    show (h.restrictScalars F) (σ₀ (algebraMap K Ω x)) = _
    rw [hσ₀]
    exact h.commutes _
  have hd : σ₁ ∈ Dec (F := F) A := by
    show σ₁ • A = A
    rw [mul_smul, restrictScalars_smul, hh]
  have hz : ∀ z : 𝓞 K, A.valuation (σ₁ (algebraMap K Ω (z : K)) - algebraMap K Ω (z : K)) < 1 := by
    intro z
    rw [hσ₁, ← map_sub]
    exact (hA (τ • z - z)).2 (hτ' z)
  obtain ⟨g, hgA, hg⟩ := exists_residue_correction (F := F) w hA hd hz
  let g' : Ω ≃ₐ[F] Ω := g.restrictScalars F
  have hgD : g' ∈ Dec (F := F) A := by
    show g' • A = A
    rw [restrictScalars_smul, hgA]
  refine ⟨A, g'⁻¹ * σ₁, hA, ?_, fun x => ?_⟩
  · refine mem_inertia_of_integers ((Dec (F := F) A).mul_mem ((Dec (F := F) A).inv_mem hgD) hd) ?_
    intro b hb
    have e : (g'⁻¹ * σ₁) b - b = (g'⁻¹ : Ω ≃ₐ[F] Ω) (σ₁ b - g' b) := by
      rw [map_sub]
      have : (g'⁻¹ : Ω ≃ₐ[F] Ω) (g' b) = b := by
        show (g'⁻¹ * g') b = b
        simp
      rw [this]
      rfl
    rw [e, valuation_apply_lt_one_iff ((Dec (F := F) A).inv_mem hgD), Valuation.map_sub_swap]
    exact hg ⟨b, hb.tower_top⟩
  · show (g'⁻¹ : Ω ≃ₐ[F] Ω) (σ₁ (algebraMap K Ω x)) = _
    rw [hσ₁]
    have : g' (algebraMap K Ω (τ x)) = algebraMap K Ω (τ x) := g.commutes _
    conv_lhs => rw [← this]
    show (g'⁻¹ * g') _ = _
    simp

end

theorem fixingSubgroup_le_NS : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (S : Set (HeightOneSpectrum (𝓞 F))),
    (maxUnramifiedOutside F Ω S).fixingSubgroup ≤ NS Ω S := by
  intro F Ω _ _ _ _ _ S
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ F).injective
  have : IsGalois F Ω := {}
  have key : IntermediateField.fixedField (NS Ω S) ≤ maxUnramifiedOutside F Ω S := by
    intro x hx
    obtain ⟨M, hxM⟩ := exists_finiteGalois_mem (K := F) x
    have hE : F⟮x⟯ ≤ M.toIntermediateField := IntermediateField.adjoin_simple_le_iff.2 hxM
    have : FiniteDimensional F F⟮x⟯ := finiteDimensional_of_le hE
    have hEK : F⟮x⟯ ≤ IntermediateField.fixedField (NS Ω S) :=
      IntermediateField.adjoin_simple_le_iff.2 hx
    refine le_maxUnramifiedOutside S (E := F⟮x⟯) (fun v hv => ?_)
      (IntermediateField.mem_adjoin_simple_self F x)
    rw [isUnramifiedIn_iff_inertia hE v]
    intro Q hQ hQv τ hτ y hy
    have : NumberField M.toIntermediateField := NumberField.of_module_finite F _
    have : IsAlgClosure M.toIntermediateField Ω :=
      ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) _⟩
    let w : HeightOneSpectrum (𝓞 M.toIntermediateField) :=
      ⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    obtain ⟨A, σ, hA, hσ, hres⟩ := exists_inertia_lift (Ω := Ω) w hτ
    have hAv : IsPlaceOver A v := by
      intro a
      have h1 := hA (algebraMap (𝓞 F) (𝓞 M.toIntermediateField) a)
      refine Iff.trans (by exact h1) ?_
      exact (Ideal.mem_of_liesOver Q v.asIdeal a).symm
    have hNS : σ ∈ NS Ω S := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hv, A, hAv, hσ⟩
    have hfix : σ y = y :=
      (IntermediateField.mem_fixedField_iff (NS Ω S) y).1 (hEK hy) σ hNS
    apply Subtype.ext
    have := hres ⟨y, hE hy⟩
    exact (this.symm.trans hfix)
  have hc := InfiniteGalois.fixingSubgroup_fixedField (⟨NS Ω S, isClosed_NS Ω S⟩ : ClosedSubgroup (Ω ≃ₐ[F] Ω))
  have := IntermediateField.fixingSubgroup_antitone key
  rw [show (IntermediateField.fixedField (NS Ω S)).fixingSubgroup = NS Ω S from hc] at this
  exact this

end GlobalTheory.CompanionTheory.Glob.InertiaLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeneralLinearUnimodularHaar
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.HaarGL

theorem exists_haar_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro F _ _ _ _ O ϖ nrm q hLF n
  obtain ⟨hKo, hKc, hlc, _hsc, ht2, -, -⟩ := _root_.GlobalTheory.CompanionTheory.QLTop.gl_topology hLF n
  haveI := hlc
  haveI := ht2
  haveI : BorelSpace (GL (Fin n) F) := GlobalTheory.CompanionTheory.QL.instBorelGL n
  refine ⟨?_, fun μ hμ => ?_⟩
  · let μ₀ : Measure (GL (Fin n) F) := Measure.haar
    have hpos : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ 0 :=
      hKo.measure_ne_zero μ₀ ⟨1, (GLint O n).one_mem⟩
    have hfin : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ ⊤ := hKc.measure_lt_top.ne
    refine ⟨(μ₀ (GLint O n : Set (GL (Fin n) F)))⁻¹ • μ₀, inferInstance, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · haveI := hμ
    exact ⟨GroundTheory.Automorphic.Measures.isMulRightInvariant_GL F n μ,
      ⟨GroundTheory.Automorphic.Measures.inv_eq_self_GL F n μ⟩⟩

end GlobalTheory.CompanionTheory.QL.HaarGL
end

