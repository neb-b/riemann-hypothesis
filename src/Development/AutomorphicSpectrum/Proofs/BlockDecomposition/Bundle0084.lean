module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import GroundTheory.LocalFields.Integers

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConvergenceOfParabolic
section
noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis.UnitaryConv

open PositivityTheory.RgEis

variable {G : Type} [Group G]

theorem cos_mk_eq_iff {P Γ : Subgroup G} (a b : Γ) :
    (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = Quotient.mk _ b ↔
      (b : G) * (a : G)⁻¹ ∈ P := by
  constructor
  · intro h
    have h1 : b * a⁻¹ ∈ P.subgroupOf Γ := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    simpa using Subgroup.mem_subgroupOf.mp h1
  · intro h
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    apply Subgroup.mem_subgroupOf.mpr
    simpa using h

theorem cos_eq_of_rep {P Γ : Subgroup G} {q q' : Cos P Γ} (h : rep q' * (rep q)⁻¹ ∈ P) : q = q' := by
  have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) (Quotient.out q) (Quotient.out q')).mpr h
  rw [Quotient.out_eq, Quotient.out_eq] at h'
  exact h'

theorem rep_mk {P Γ : Subgroup G} (a : Γ) :
    ∃ p ∈ Γ, p ∈ P ∧ rep (Quotient.mk (QuotientGroup.rightRel (P.subgroupOf Γ)) a : Cos P Γ) = p * a := by
  refine ⟨rep (Quotient.mk _ a : Cos P Γ) * (a : G)⁻¹, ?_, ?_, ?_⟩
  · exact Γ.mul_mem (Quotient.out (Quotient.mk _ a : Cos P Γ)).2 (Γ.inv_mem a.2)
  · exact (cos_mk_eq_iff (P := P) (Γ := Γ) a (Quotient.out (Quotient.mk _ a : Cos P Γ))).mp
      (Quotient.out_eq _).symm
  · exact (inv_mul_cancel_right _ _).symm

theorem conv_comap {G' : Type} [Group G'] (φ : G' →* G) {Γ P : Subgroup G} {Γ' P' : Subgroup G'} {l : G → ℝ}
    (hΓ : ∀ γ ∈ Γ', φ γ ∈ Γ) (hP : ∀ γ ∈ Γ', φ γ ∈ P → γ ∈ P')
    (hl : ∀ γ ∈ Γ, γ ∈ P → ∀ g, l (γ * g) = l g) (hc : Conv Γ P l) :
    Conv Γ' P' fun g => l (φ g) := by
  intro g'
  have hinj : Function.Injective (fun q' : Cos P' Γ' =>
      (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ)) := by
    intro q₁ q₂ h
    have h' := (cos_mk_eq_iff (P := P) (Γ := Γ) _ _).mp h
    apply cos_eq_of_rep
    have hmem : rep q₂ * (rep q₁)⁻¹ ∈ Γ' :=
      Γ'.mul_mem (Quotient.out q₂).2 (Γ'.inv_mem (Quotient.out q₁).2)
    refine hP _ hmem ?_
    rw [map_mul, map_inv]
    exact h'
  refine ((hc (φ g')).comp_injective hinj).congr fun q' => ?_
  obtain ⟨p, hpΓ, hpP, hp⟩ := rep_mk (P := P) (Γ := Γ) ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩
  show Real.exp (l (rep (Quotient.mk _ ⟨φ (rep q'), hΓ (rep q') (Quotient.out q').2⟩ : Cos P Γ) * φ g')) =
    Real.exp (l (φ (rep q' * g')))
  rw [hp, map_mul, mul_assoc, hl p hpΓ hpP]

theorem conv_inf {Γ P₁ P₂ : Subgroup G} {l₁ l₂ : G → ℝ}
    (h₁ : ∀ γ ∈ Γ, γ ∈ P₁ → ∀ g, l₁ (γ * g) = l₁ g) (h₂ : ∀ γ ∈ Γ, γ ∈ P₂ → ∀ g, l₂ (γ * g) = l₂ g)
    (c₁ : Conv Γ P₁ l₁) (c₂ : Conv Γ P₂ l₂) : Conv Γ (P₁ ⊓ P₂) fun g => l₁ g + l₂ g := by
  intro g
  have hinj : Function.Injective (fun q : Cos (P₁ ⊓ P₂) Γ =>
      ((Quotient.mk _ (Quotient.out q) : Cos P₁ Γ), (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ))) := by
    intro q q' h
    have e1 := (cos_mk_eq_iff (P := P₁) (Γ := Γ) _ _).mp (congrArg Prod.fst h)
    have e2 := (cos_mk_eq_iff (P := P₂) (Γ := Γ) _ _).mp (congrArg Prod.snd h)
    exact cos_eq_of_rep (Subgroup.mem_inf.mpr ⟨e1, e2⟩)
  have hprod : Summable fun x : Cos P₁ Γ × Cos P₂ Γ =>
      Real.exp (l₁ (rep x.1 * g)) * Real.exp (l₂ (rep x.2 * g)) := by
    exact Summable.mul_of_nonneg (c₁ g) (c₂ g) (fun _ => (Real.exp_pos _).le)
      (fun _ => (Real.exp_pos _).le)
  refine (hprod.comp_injective hinj).congr fun q => ?_
  obtain ⟨p₁, hp₁Γ, hp₁P, hp₁⟩ := rep_mk (P := P₁) (Γ := Γ) (Quotient.out q)
  obtain ⟨p₂, hp₂Γ, hp₂P, hp₂⟩ := rep_mk (P := P₂) (Γ := Γ) (Quotient.out q)
  show Real.exp (l₁ (rep (Quotient.mk _ (Quotient.out q) : Cos P₁ Γ) * g)) *
      Real.exp (l₂ (rep (Quotient.mk _ (Quotient.out q) : Cos P₂ Γ) * g)) =
    Real.exp (l₁ (rep q * g) + l₂ (rep q * g))
  rw [hp₁, hp₂, mul_assoc, mul_assoc, h₁ p₁ hp₁Γ hp₁P, h₂ p₂ hp₂Γ hp₂P, Real.exp_add]
  rfl

theorem convU_of_parLaw : ParLaw → ConvU := by
  intro hPar E R _ _ _ _ _ _ _ A hA hGr ι _ _ ε s hIwa
  have inv : ∀ {H : Type} [Group H] [TopologicalSpace H] {Γ K P : Subgroup H} {η : H → ℝ} (c : ℝ),
      IsHt Γ K P η → ∀ γ ∈ Γ, γ ∈ P → ∀ g, c * η (γ * g) = c * η g := by
    intro H _ _ Γ K P η c h γ hγ hγP g
    rw [h.left γ hγP g, h.rat γ hγ hγP, zero_add]
  have hconv : ∀ (t : Set ι) (x : ℝ), (∀ g : A.U ε ι, A.uH ε t g = A.htGL (Sum.inl '' t) g.1) →
      IsHt (A.ratGL (ι ⊕ ι)) (A.kGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (A.htGL (Sum.inl '' t)) →
      Conv (A.ratGL (ι ⊕ ι)) (stab R (Sum.inl '' t)) (fun g => x * A.htGL (Sum.inl '' t) g) →
      Conv (A.uΓ ε ι) (A.uQ ε t) fun g => x * A.uH ε t g := by
    intro t x heq hHt hc
    have h := conv_comap (A.uSub ε ι).subtype (Γ := A.ratGL (ι ⊕ ι)) (P := stab R (Sum.inl '' t))
      (Γ' := A.uΓ ε ι) (P' := A.uQ ε t) (l := fun g => x * A.htGL (Sum.inl '' t) g)
      (fun γ hγ => Subgroup.mem_subgroupOf.mp hγ) (fun γ _ hγ => Subgroup.mem_subgroupOf.mpr hγ)
      (inv x hHt) hc
    have hfun : (fun g : A.U ε ι => x * A.uH ε t g) =
        fun g => x * A.htGL (Sum.inl '' t) ((A.uSub ε ι).subtype g) := by
      funext g
      exact congrArg (fun r => x * r) (heq g)
    rw [hfun]
    exact h
  have hIwaU : Iwa (A.uQ ε (Set.univ : Set ι) ⊓ A.uQ ε Set.univ) (A.uK ε ι) := by
    intro g
    obtain ⟨p, hp, k, hk, hg⟩ := hIwa g
    exact ⟨p, Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hp).2, (Subgroup.mem_inf.mp hp).2⟩, k, hk, hg⟩
  obtain ⟨Rs, hRs⟩ := hGr (ι ⊕ ι) (Sum.inl '' s)
  obtain ⟨Ru, hRu⟩ := hGr (ι ⊕ ι) (Sum.inl '' (Set.univ : Set ι))
  have hs := (hPar E R A hA ι ε s).2 hIwa
  have hu := (hPar E R A hA ι ε Set.univ).2 hIwaU
  have hGs := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' s)).1.2.2.2.1
  have hGu := (hPar E R A hA (ι ⊕ ι) ε (Sum.inl '' (Set.univ : Set ι))).1.2.2.2.1
  refine ⟨max Rs Ru, fun y hy => ?_, fun x y hx hy => ?_⟩
  · exact hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy))
  · exact conv_inf (l₁ := fun g => x * A.uH ε s g) (l₂ := fun g => y * A.uH ε Set.univ g)
      (inv x hs.2.1) (inv y hu.2.1)
      (hconv s x hs.2.2 hGs (hRs x (lt_of_le_of_lt (le_max_left _ _) hx)))
      (hconv Set.univ y hu.2.2 hGu (hRu y (lt_of_le_of_lt (le_max_right _ _) hy)))

end GlobalTheory.CompanionTheory.RgEis.UnitaryConv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedDictionaryPartB
section
open ValuativeRel PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.Unram

theorem sub_mem_span_pow {O : Type*} [CommRing O] (τ : O →+* O) (π : O) (q : ℕ)
    (hτπ : τ π = π) (hq : (q : O) ∈ Ideal.span {π})
    (hpow : ∀ x : O, x ^ q - x ∈ Ideal.span {π})
    (h1 : ∀ x : O, τ x - x ∈ Ideal.span {π}) (m : ℕ) (hm : 1 ≤ m) :
    ∀ x : O, τ x - x ∈ (Ideal.span {π}) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => simpa using h1
  | succ m hm ih =>
    intro x
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp (hpow x)
    have e1 : τ (x ^ q - x) = τ z * π := by rw [← hz, map_mul, hτπ]
    rw [map_sub, map_pow] at e1
    have hsum : ∑ i ∈ Finset.range q, (τ x) ^ i * x ^ (q - 1 - i) ∈ Ideal.span {π} := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      have hab : Ideal.Quotient.mk (Ideal.span {π}) (τ x) = Ideal.Quotient.mk (Ideal.span {π}) x :=
        Ideal.Quotient.eq.mpr (h1 x)
      simp only [map_mul, map_pow, hab]
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [← pow_add, show i + (q - 1 - i) = q - 1 by have := Finset.mem_range.mp hi; omega]),
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [show ((q : ℕ) : O ⧸ Ideal.span {π}) = Ideal.Quotient.mk (Ideal.span {π}) (q : O) by simp,
        Ideal.Quotient.eq_zero_iff_mem.mpr hq, zero_mul]
    have hA : (τ x) ^ q - x ^ q ∈ (Ideal.span {π}) ^ (m + 1) := by
      rw [← geom_sum₂_mul, pow_succ']
      exact Ideal.mul_mem_mul hsum (ih x)
    have hB : (τ z - z) * π ∈ (Ideal.span {π}) ^ (m + 1) := by
      rw [pow_succ]
      exact Ideal.mul_mem_mul (ih z) (Ideal.mem_span_singleton_self π)
    have e2 : τ x - x = ((τ x) ^ q - x ^ q) - (τ z - z) * π := by
      linear_combination (-1 : O) * e1 - hz
    rw [e2]
    exact Ideal.sub_mem _ hA hB

section Local

variable (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]

theorem lt_one_of_mem_maximal (x : 𝒪[E]) (hx : x ∈ IsLocalRing.maximalIdeal 𝒪[E]) :
    valuation E (x : E) < 1 := by
  have hle : valuation E (x : E) ≤ 1 := x.2
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hunit : IsUnit x := (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one.mpr heq
  exact ((IsLocalRing.mem_maximalIdeal _).mp hx) hunit

theorem residue_card_facts : ∃ q : ℕ, valuation E (q : E) < 1 ∧
    ∀ x : 𝒪[E], valuation E (((x ^ q - x : 𝒪[E])) : E) < 1 := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField 𝒪[E]) := Fintype.ofFinite _
  refine ⟨Fintype.card (IsLocalRing.ResidueField 𝒪[E]), ?_, ?_⟩
  · have hmem : ((Fintype.card (IsLocalRing.ResidueField 𝒪[E]) : ℕ) : 𝒪[E]) ∈ IsLocalRing.maximalIdeal 𝒪[E] := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
      exact FiniteField.cast_card_eq_zero _
    have := lt_one_of_mem_maximal E _ hmem
    simpa using this
  · intro x
    apply lt_one_of_mem_maximal E
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_pow, FiniteField.pow_card, sub_self]

end Local

section Ext

variable (k E : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E]

theorem integral_basis
    (hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k) :
    ∃ b : Module.Basis (Fin (Module.finrank k E)) k E, (∀ i, b i ∈ intO E) ∧
      ∀ x : E, x ∈ intO E ↔ ∀ i, b.repr x i ∈ intO k := by
  haveI := GroundTheory.LocalField.free_integer k E
  haveI := GroundTheory.LocalField.finite_integer k E
  haveI := GroundTheory.LocalField.isIntegralClosure k E
  haveI : IsLocalization (Algebra.algebraMapSubmonoid 𝒪[E] (nonZeroDivisors 𝒪[k])) E :=
    IsIntegralClosure.isLocalization 𝒪[k] k E 𝒪[E]
  let bO := Module.finBasisOfFinrankEq 𝒪[k] 𝒪[E] (GroundTheory.LocalField.finrank_integer k E)
  let b := bO.localizationLocalization k (nonZeroDivisors 𝒪[k]) E
  have hb : ∀ i, b i = ((bO i : 𝒪[E]) : E) := fun i => Module.Basis.localizationLocalization_apply _ _ _ _ _
  refine ⟨b, fun i => by rw [hb]; exact (bO i).2, fun x => ⟨fun hx i => ?_, fun h => ?_⟩⟩
  · have hx' : x = algebraMap 𝒪[E] E ⟨x, hx⟩ := rfl
    rw [hx', Module.Basis.localizationLocalization_repr_algebraMap]
    exact (bO.repr ⟨x, hx⟩ i).2
  · rw [← b.sum_repr x]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def, hb]
    exact Subring.mul_mem _ ((hint _).mpr (h i)) (bO i).2

variable {k E}

theorem val_le_iff (a b : k) :
    valuation k a ≤ valuation k b ↔
      valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) := by
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le, ValuativeExtension.vle_iff_vle]

theorem uniformiser_of_unramified (hU : IsUnramifiedLoc k E) :
    ∃ π : k, IsUniformiser π ∧ IsUniformiser (algebraMap k E π) := by
  obtain ⟨π, hπ1, hπ2⟩ := hU
  have hk1 : ∀ x : k, valuation k x < 1 ↔ valuation E (algebraMap k E x) < 1 := by
    intro x
    have h := val_le_iff (E := E) (1 : k) x
    simp only [map_one] at h
    rw [← not_le, ← not_le, h]
  have hne : π ≠ 0 := by
    rintro rfl
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (GroundTheory.LocalField.maximalIdeal_ne_bot E)
    have hlt := lt_one_of_mem_maximal E y hy
    have h0 := hπ2 _ hlt
    rw [map_zero, map_zero] at h0
    exact hy0 (Subtype.ext ((Valuation.zero_iff _).mp (le_antisymm h0 zero_le')))
  refine ⟨π, ⟨(hk1 π).mpr hπ1, hne, ?_⟩, ⟨hπ1, (map_ne_zero _).mpr hne, hπ2⟩⟩
  intro x hx
  exact (val_le_iff x π).mpr (hπ2 _ ((hk1 x).mp hx))

theorem exists_moved (hU : IsUnramifiedLoc k E) (τ : E ≃ₐ[k] E) (hτ : τ ≠ 1)
    (hval : ∀ x : E, valuation E (τ x) = valuation E x) :
    ∃ x : E, x ∈ intO E ∧ valuation E (τ x - x) = 1 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨π, -, hπE⟩ := uniformiser_of_unramified hU
  obtain ⟨hπ1, hπ0, hπmax⟩ := hπE
  haveI := GroundTheory.LocalField.isDiscreteValuationRing E
  have hint : ∀ x : 𝒪[E], ((τ : E →+* E).comp (𝒪[E]).subtype) x ∈ 𝒪[E] := by
    intro x
    show valuation E (τ x) ≤ 1
    rw [hval]
    exact x.2
  let τO : 𝒪[E] →+* 𝒪[E] := ((τ : E →+* E).comp (𝒪[E]).subtype).codRestrict 𝒪[E] hint
  have hτO : ∀ x : 𝒪[E], ((τO x : 𝒪[E]) : E) = τ x := fun x => rfl
  let πO : 𝒪[E] := ⟨algebraMap k E π, hπ1.le⟩
  have hτπ : τO πO = πO := Subtype.ext (by rw [hτO]; exact τ.commutes π)
  have hspan : ∀ y : 𝒪[E], valuation E (y : E) < 1 → y ∈ Ideal.span {πO} := by
    intro y hy
    rw [Ideal.mem_span_singleton']
    have hle := hπmax _ hy
    refine ⟨⟨(y : E) / algebraMap k E π, ?_⟩, ?_⟩
    · show valuation E ((y : E) / algebraMap k E π) ≤ 1
      rw [div_eq_mul_inv, map_mul, map_inv₀]
      calc valuation E (y : E) * (valuation E (algebraMap k E π))⁻¹
          ≤ valuation E (algebraMap k E π) * (valuation E (algebraMap k E π))⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff _).mpr hπ0)
    · exact Subtype.ext (div_mul_cancel₀ (y : E) hπ0)
  obtain ⟨q, hq1, hq2⟩ := residue_card_facts E
  have hqmem : (q : 𝒪[E]) ∈ Ideal.span {πO} := hspan _ (by simpa using hq1)
  have hpowmem : ∀ x : 𝒪[E], x ^ q - x ∈ Ideal.span {πO} := fun x => hspan _ (hq2 x)
  have h1 : ∀ x : 𝒪[E], τO x - x ∈ Ideal.span {πO} := by
    intro x
    apply hspan
    have hle : valuation E ((τO x - x : 𝒪[E]) : E) ≤ 1 := (τO x - x).2
    exact lt_of_le_of_ne hle (hcon x x.2)
  have hnt : Ideal.span {πO} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have := (Valuation.integer.integers (valuation E)).isUnit_iff_valuation_eq_one.mp hu
    exact (ne_of_lt hπ1) this
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {πO}) hnt
  have hall : ∀ x : 𝒪[E], τO x = x := by
    intro x
    have hmem : τO x - x ∈ ⨅ i, (Ideal.span {πO}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp
      · exact sub_mem_span_pow τO πO q hτπ hqmem hpowmem h1 i hi x
    rw [hbot] at hmem
    exact sub_eq_zero.mp ((Submodule.mem_bot _).mp hmem)
  apply hτ
  refine AlgEquiv.ext fun y => ?_
  show τ y = y
  by_cases hy : valuation E y ≤ 1
  · have := congrArg Subtype.val (hall ⟨y, hy⟩)
    rw [hτO] at this
    exact this
  · have hy0 : y ≠ 0 := by
      rintro rfl
      exact hy (by rw [map_zero]; exact zero_le')
    have hy' : valuation E y⁻¹ ≤ 1 := ((Valuation.one_lt_val_iff _ hy0).mp (not_le.mp hy)).le
    have := congrArg Subtype.val (hall ⟨y⁻¹, hy'⟩)
    rw [hτO] at this
    simp only [map_inv₀] at this
    exact inv_injective this

end Ext

theorem unramifiedDictionary_part_b : D0a → IntegralBasisUnramified := by
  intro hA k E _ _ _ _ _ _ _ _ _ _ _ _ hU σ hσ
  obtain ⟨hval, hint, -⟩ := hA k E hU σ hσ
  refine ⟨integral_basis k E hint, uniformiser_of_unramified hU, ?_⟩
  intro j hj0 hjn
  have hord : orderOf σ = Module.finrank k E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hσ, IsGalois.card_aut_eq_finrank]
  have hne : σ ^ j ≠ 1 := pow_ne_one_of_lt_orderOf hj0.ne' (hord ▸ hjn)
  obtain ⟨x, hx, hx1⟩ := exists_moved hU (σ ^ j) hne (hval (σ ^ j))
  exact ⟨x, hx, hx1⟩

end GlobalTheory.CompanionTheory.Unram
end

