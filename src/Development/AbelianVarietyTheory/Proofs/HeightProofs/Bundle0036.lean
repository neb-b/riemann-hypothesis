module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsIntegralIffMemSpanOneTmulIntegralClosure
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemIntegralClosureOfMemSpan

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.LengthQuotientLeOfOrderBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory

theorem mem_span_one_tmul_of_order_bound (R R' F F' : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F]
    [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F']
    [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F']
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')))
    (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    [Algebra R L] [IsScalarTower R F L] (n : AddValuation L (WithTop ℤ) → ℤ) (η : L) (hη0 : η ≠ 0)
    (hη : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R L, w η = ((n w : ℤ) : WithTop ℤ))
    (x : F' ⊗[F] L)
    (hx : ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R L,
      ∀ u : AddValuation (F' ⊗[F] L) (WithTop ℤ), (∀ g : L, u ((1 : F') ⊗ₜ[F] g) = w g) →
        (∀ r : R', 0 ≤ u (algebraMap R' F' r ⊗ₜ[F] (1 : L))) →
          0 ≤ u x + ((n w : ℤ) : WithTop ℤ)) :
    x ∈ Submodule.span R' ((fun l : L => (1 : F') ⊗ₜ[F] l) ''
      {l | ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R L, 0 ≤ w l + ((n w : ℤ) : WithTop ℤ)}) := by
  have hB := isIntegral_iff_mem_span_one_tmul_integralClosure R R' F F' hmax hres L
  obtain ⟨w', h1, h2, -, -⟩ := exists_unique_place_baseChange R R' F F' hmax hres L hB
  have hint : IsIntegral R' (x * (1 : F') ⊗ₜ[F] η) := by
    rw [h2]
    intro w
    rw [AddValuation.map_mul, h1, hη w.1 w.2]
    refine hx w.1 w.2 (w' w) (h1 w) fun r => ?_
    exact (h2 _).1 (isIntegral_algebraMap (R := R') (A := F' ⊗[F] L) (x := r)) w
  have hmem := (hB _).1 hint
  haveI := integralClosure.isDedekindDomain R F L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F L
  have hxe : x = (x * (1 : F') ⊗ₜ[F] η) * (1 : F') ⊗ₜ[F] η⁻¹ := by
    rw [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hη0,
      ← Algebra.TensorProduct.one_def, mul_one]
  rw [hxe]
  generalize x * (1 : F') ⊗ₜ[F] η = y at hmem
  induction hmem using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, rfl⟩ := hy
    refine Submodule.subset_span ⟨b * η⁻¹, fun w hw => ?_, ?_⟩
    · rw [← hη w hw, ← AddValuation.map_mul, inv_mul_cancel_right₀ hη0]
      exact (ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.mem_integralClosure_iff R F b).1 hb w hw
    · simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => simp
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul a b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

theorem length_subquot_le_of_injective {A M V : Type} [Ring A] [AddCommGroup M] [Module A M]
    [AddCommGroup V] [Module A V] (Φ : M →ₗ[A] V) (hΦ : Function.Injective Φ)
    (M₀ T : Submodule A M) (N B : Submodule A V) (hN : ∀ a ∈ M₀, Φ a ∈ N) (hB : T.map Φ = B) :
    Module.length A (↥M₀ ⧸ T.comap M₀.subtype) ≤ Module.length A (↥N ⧸ B.comap N.subtype) := by
  have hc : T.comap M₀.subtype = (B.comap N.subtype).comap (Φ.restrict hN) := by
    ext a
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.coe_restrict_apply, ← hB]
    exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨y, hy, h⟩ => hΦ h ▸ hy⟩
  refine Module.length_le_of_injective
    (Submodule.mapQ _ (B.comap N.subtype) (Φ.restrict hN) hc.le) ?_
  rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, ← hc, Submodule.mkQ_map_self]

theorem length_quotient_le_of_order_bound :
    ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Fintype ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (n : ∀ c, AddValuation (L c) (WithTop ℤ) → ℤ), (∀ c, ∃ η : L c, η ≠ 0 ∧ ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R (L c), w η = ((n c w : ℤ) : WithTop ℤ)) → ∀ (δ δ' : Type) (e : δ ≃ δ') (b : δ → ∀ c, L c) (M : Type) [AddCommGroup M] [Module R' M] (M₀ : Submodule R' M) (t : δ' → M) (Ψ : M →ₗ[R'] ∀ c, F' ⊗[F] L c), Function.Injective Ψ → (∀ k c, Ψ (t (e k)) c = (1 : F') ⊗ₜ[F] b k c) → (∀ a ∈ M₀, ∀ c, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R (L c), ∀ u : AddValuation (F' ⊗[F] L c) (WithTop ℤ), (∀ g : L c, u ((1 : F') ⊗ₜ[F] g) = w g) → (∀ r : R', 0 ≤ u (algebraMap R' F' r ⊗ₜ[F] (1 : L c))) → 0 ≤ u (Ψ a c) + ((n c w : ℤ) : WithTop ℤ)) → ∀ S : Set (∀ c, L c), (∀ y : ∀ c, L c, (∀ c, ∀ w ∈ ReciprocityTheory.ChartRestriction.G.T0.ValPl.PlacesOver R (L c), 0 ≤ w (y c) + ((n c w : ℤ) : WithTop ℤ)) → y ∈ S) → Module.length R' (↥M₀ ⧸ (Submodule.span R' (Set.range t)).comap M₀.subtype) ≤ Module.length R (↥(Submodule.span R S) ⧸ (Submodule.span R (Set.range b)).comap (Submodule.span R S).subtype) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres ι _ L _ _ _ _ _ _ n hη δ δ' e b
    M _ _ M₀ t Ψ hΨ ht hM₀ S hS
  classical
  let E : (F' ⊗[F] (∀ c, L c)) ≃ₗ[R'] (∀ c, F' ⊗[F] L c) :=
    (TensorProduct.piRight F F' F' L).restrictScalars R'
  have hE : ∀ v : ∀ c, L c, E ((1 : F') ⊗ₜ[F] v) = fun c => (1 : F') ⊗ₜ[F] v c := fun v => rfl
  have hspan : ∀ X : Set (∀ c, L c),
      Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) '' (Submodule.span R X : Set _))
        = Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) '' X) := by
    intro X
    refine le_antisymm (Submodule.span_le.2 ?_)
      (Submodule.span_mono (Set.image_mono Submodule.subset_span))
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem v hv => exact Submodule.subset_span ⟨v, hv, rfl⟩
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [TensorProduct.tmul_add]
      exact Submodule.add_mem _ ha hb
    | smul r v _ hv =>
      have : (1 : F') ⊗ₜ[F] (r • v) = algebraMap R R' r • ((1 : F') ⊗ₜ[F] v) := by
        rw [TensorProduct.smul_tmul', ← IsScalarTower.algebraMap_smul F r v,
          ← TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def,
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
      simp only [this]
      exact Submodule.smul_mem _ _ hv
  refine le_trans (length_subquot_le_of_injective (E.symm.toLinearMap ∘ₗ Ψ)
    (E.symm.injective.comp hΨ) M₀ _
    (Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) '' (Submodule.span R S : Set _)))
    (Submodule.span R' ((fun v : (∀ c, L c) => (1 : F') ⊗ₜ[F] v) ''
      (Submodule.span R (Set.range b) : Set _))) ?_ ?_) (le_of_eq ?_)
  · intro a ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hspan, LinearMap.comp_apply, ← Finset.univ_sum_single (Ψ a), map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨η, hη0, hη⟩ := hη c
    have hx := mem_span_one_tmul_of_order_bound R R' F F' hmax hres (L c) (n c) η hη0 hη
      (Ψ a c) (hM₀ a ha c)
    generalize Ψ a c = x at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨Pi.single c l, hS _ fun c' w hw => ?_, ?_⟩
      · rcases eq_or_ne c' c with rfl | hc
        · rw [Pi.single_eq_same]; exact hl w hw
        · rw [Pi.single_eq_of_ne hc, AddValuation.map_zero, top_add]; exact le_top
      · refine (LinearEquiv.eq_symm_apply E).2 ?_
        rw [hE]
        funext c'
        rcases eq_or_ne c' c with rfl | hc
        · simp only [Pi.single_eq_same]
        · simp only [Pi.single_eq_of_ne hc, TensorProduct.tmul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · rw [hspan, Submodule.map_span, ← Set.range_comp, ← Set.range_comp,
      ← e.surjective.range_comp]
    congr 2
    funext k
    refine (LinearEquiv.symm_apply_eq E).2 ?_
    funext c
    exact ht k c
  · exact (spanBaseChangeSubquotEquiv F R' F' (Submodule.span R S)
      (Submodule.span R (Set.range b))).length_eq.symm.trans
      (ReciprocityTheory.ChartRestriction.G.T0.length_baseChange_eq hmax _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ValuationEqOrdAndEqZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.OrdVal

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A]


omit [IsDomain O] [IsDiscreteValuationRing O] in
theorem nonneg_of_isIntegral (u : AddValuation A (WithTop ℤ))
    (hu : ∀ r : O, 0 ≤ u (algebraMap O A r)) {x : A} (hx : IsIntegral O x) : 0 ≤ u x := by
  let v : Valuation A (Multiplicative (WithTop ℤ)ᵒᵈ) := u
  let f : O →+* v.integer := (algebraMap O A).codRestrict v.integer (fun r => hu r)
  have h1 : IsIntegral v.integer x := by
    obtain ⟨p, hp, hz⟩ := hx
    refine ⟨p.map f, hp.map f, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hz
  exact (Valuation.integer.integers v).mem_of_integral h1

def centre (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    Ideal ↥(As O A) where
  carrier := {a | 0 < u (a : A)}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    have := u.map_add (a : A) b
    exact lt_of_lt_of_le (lt_min ha hb) this
  smul_mem' := fun c a ha => by
    change 0 < u ((c : A) * a)
    rw [u.map_mul]
    exact lt_of_lt_of_le ha (le_add_of_nonneg_left (hu c))

theorem centre_isPrime (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A)) :
    (centre u hu).IsPrime := by
  refine ⟨fun h => ?_, fun {a b} h => ?_⟩
  · have : (1 : ↥(As O A)) ∈ centre u hu := h ▸ Submodule.mem_top
    change 0 < u (1 : A) at this
    simp at this
  · change 0 < u ((a : A) * b) at h
    by_contra hn
    rw [not_or] at hn
    have ha : u (a : A) = 0 := le_antisymm (not_lt.1 hn.1) (hu a)
    have hb : u (b : A) = 0 := le_antisymm (not_lt.1 hn.2) (hu b)
    rw [u.map_mul, ha, hb] at h
    simp at h

theorem centre_isMaximal (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    {ϖ : O} (hϖ : Irreducible ϖ) (hpos : 0 < u (algebraMap O A ϖ)) :
    (centre u hu).IsMaximal := by
  haveI := centre_isPrime u hu
  refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) _ ?_
  have hle : IsLocalRing.maximalIdeal O ≤ (centre u hu).comap (algebraMap O ↥(As O A)) := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
    exact hpos
  have := (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle
  change ((centre u hu).comap (algebraMap O ↥(As O A))).IsMaximal
  rw [← this]
  infer_instance

theorem le_of_vL_le (u : AddValuation A (WithTop ℤ)) (hu : ∀ a : ↥(As O A), 0 ≤ u (a : A))
    (ζ : Pts O A) [IsDVRAt ζ] (hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0)
    {a b : ↥(As O A)} (hab : vL ζ a ≤ vL ζ b) : u (a : A) ≤ u (b : A) := by
  rw [vL_eq_addVal, vL_eq_addVal, IsDiscreteValuationRing.addVal_le_iff_dvd] at hab
  obtain ⟨z, hz⟩ := hab
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl z
  have h1 : algebraMap _ (Loc ζ) (b * s) = algebraMap _ (Loc ζ) (a * x) := by
    simp only at hs
    rw [map_mul, map_mul, hz, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists ζ.asIdeal.primeCompl (Loc ζ)).1 h1
  have h2 : ((c : ↥(As O A)) : A) * ((b : A) * ((s : ↥(As O A)) : A))
      = ((c : ↥(As O A)) : A) * ((a : A) * (x : A)) := congrArg Subtype.val hc
  have h3 := congrArg u h2
  rw [u.map_mul, u.map_mul, u.map_mul, u.map_mul, hζ _ c.2, hζ _ s.2, zero_add, zero_add,
    add_zero] at h3
  rw [h3]
  exact le_add_of_nonneg_right (hu x)

theorem exists_vL_eq_one (ζ : Pts O A) [IsDVRAt ζ] : ∃ a : ↥(As O A), vL ζ a = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Loc ζ)
  obtain ⟨⟨x, s⟩, hs⟩ := IsLocalization.surj ζ.asIdeal.primeCompl π
  refine ⟨x, ?_⟩
  have h0 := (vL_eq_zero_iff ζ s).2 s.2
  rw [vL_eq_addVal] at h0
  simp only at hs
  rw [vL_eq_addVal, ← hs, IsDiscreteValuationRing.addVal_mul, h0,
    IsDiscreteValuationRing.addVal_uniformizer hπ, add_zero]

theorem exists_ord_eq [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ)
    (u : AddValuation A (WithTop ℤ)) (hO : ∀ r : O, 0 ≤ u (algebraMap O A r))
    (hpos : 0 < u (algebraMap O A ϖ)) (hone : ∃ a, u a = 1) :
    ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a := by
  have hu : ∀ a : ↥(As O A), 0 ≤ u (a : A) := fun a => nonneg_of_isIntegral u hO a.2
  let ζ : Pts O A := ⟨centre u hu, centre_isMaximal u hu h.irreducible hpos⟩
  have hζ : ∀ a : ↥(As O A), a ∉ ζ.asIdeal → u (a : A) = 0 :=
    fun a ha => le_antisymm (not_lt.1 ha) (hu a)
  obtain ⟨a₀, ha₀⟩ := exists_vL_eq_one ζ
  have hfin : ∀ (b : ↥(As O A)) (m : ℕ), vL ζ b = m → u (b : A) = m • u (a₀ : A) := by
    intro b m hb
    have e : vL ζ (a₀ ^ m) = vL ζ b := by rw [vL_pow, ha₀, hb]; simp
    have := le_antisymm (le_of_vL_le u hu ζ hζ e.ge) (le_of_vL_le u hu ζ hζ e.le)
    rw [this, SubmonoidClass.coe_pow, u.map_pow]
  have htop : ∀ b : ↥(As O A), vL ζ b = ⊤ → u (b : A) = ⊤ := by
    intro b hb
    have := le_of_vL_le u hu ζ hζ (a := 0) (b := b) (by rw [hb]; exact le_top)
    simpa using this
  have hϖ : u (algebraMap O A ϖ) = ep ϖ ζ • u (a₀ : A) :=
    hfin (algebraMap O ↥(As O A) ϖ) _ (coe_ep ζ h).symm
  have hϖfin : u (algebraMap O A ϖ) ≠ ⊤ := by
    obtain ⟨y, hy⟩ := h.isUnit.exists_right_inv
    intro ht
    have := congrArg u hy
    rw [u.map_mul, ht, u.map_one] at this
    simp at this
  have ha₀fin : u (a₀ : A) ≠ ⊤ := by
    intro ht
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ep_pos ζ h).ne'
    rw [hϖ, ht, hk, succ_nsmul] at hϖfin
    simp at hϖfin
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 ha₀fin
  have hq0 : 0 ≤ q := by
    have := hu a₀
    rw [← hq] at this
    exact_mod_cast this
  have key : ∀ x : A, (Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = ⊤ ∧ u x = ⊤) ∨
      ∃ k : ℤ, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ x = (k : WithTop ℤ) ∧ u x = ((k * q : ℤ) : WithTop ℤ) := by
    intro x
    obtain ⟨n, hn⟩ := h.denom x
    have e1 : u (ϖ ^ n • x) = ((n * (ep ϖ ζ * q) : ℤ) : WithTop ℤ) + u x := by
      rw [Algebra.smul_def, map_pow, u.map_mul, u.map_pow, hϖ, ← hq, ← WithTop.coe_nsmul,
        ← WithTop.coe_nsmul, nsmul_eq_mul, nsmul_eq_mul]
    rw [ord_eq ζ h hn, ordAt]
    cases hv : vL ζ ⟨ϖ ^ n • x, hn⟩ with
    | top =>
      left
      refine ⟨by simp, ?_⟩
      have := htop _ hv
      change u (ϖ ^ n • x) = ⊤ at this
      rw [e1, WithTop.add_eq_top] at this
      exact this.resolve_left WithTop.coe_ne_top
    | coe m =>
      right
      refine ⟨m + -(n * ep ϖ ζ), by rw [ENat.map_natCast, ← WithTop.coe_add], ?_⟩
      have := hfin _ m hv
      change u (ϖ ^ n • x) = _ at this
      rw [e1, ← hq, ← WithTop.coe_nsmul, nsmul_eq_mul] at this
      have hx : u x ≠ ⊤ := by
        intro ht
        rw [ht, add_top] at this
        exact WithTop.top_ne_coe this
      obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hx
      rw [← ht, ← WithTop.coe_add, WithTop.coe_inj] at this
      rw [← ht, WithTop.coe_inj]
      linarith
  have hq1 : q = 1 := by
    obtain ⟨a, ha⟩ := hone
    rcases key a with ⟨_, h2⟩ | ⟨k, _, h2⟩
    · rw [ha] at h2
      exact absurd h2 WithTop.one_ne_top
    · rw [ha, ← WithTop.coe_one, WithTop.coe_inj] at h2
      exact Int.eq_one_of_mul_eq_one_left hq0 h2.symm
  refine ⟨ζ, fun a => ?_⟩
  rcases key a with ⟨h1, h2⟩ | ⟨k, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hq1, mul_one]

theorem eq_zero_of_ord_eq_top [∀ ζ : Pts O A, IsDVRAt ζ] {ϖ : O} (h : IsUnif A ϖ) (a : A)
    (ha : ∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) : a = 0 := by
  obtain ⟨n, hn⟩ := h.denom a
  have key : (⟨ϖ ^ n • a, hn⟩ : ↥(As O A)) ∈ (⊥ : Ideal ↥(As O A)) := by
    have h0 : ∀ ζ : Pts O A, algebraMap ↥(As O A) (Loc ζ) ⟨ϖ ^ n • a, hn⟩ ∈
        Ideal.map (algebraMap ↥(As O A) (Loc ζ)) ⊥ := by
      intro ζ
      have h1 := ha ζ
      rw [ord_eq ζ h hn, ordAt, WithTop.add_eq_top] at h1
      have h2 : vL ζ ⟨ϖ ^ n • a, hn⟩ = ⊤ := by
        simpa using h1.resolve_right WithTop.coe_ne_top
      rw [(vL_eq_top_iff ζ _).1 h2]
      exact Submodule.zero_mem _
    exact Ideal.mem_of_localization_maximal (fun P hP => h0 ⟨P, hP⟩)
  have h2 : ϖ ^ n • a = 0 := congrArg Subtype.val (Ideal.mem_bot.1 key)
  rw [Algebra.smul_def, map_pow] at h2
  exact ((h.isUnit.pow n).mul_right_eq_zero).1 h2

theorem valuation_eq_ord_and_eq_zero :
    ∀ (O A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] [∀ ζ : Pts O A, IsDVRAt ζ] (ϖ : O), IsUnif A ϖ → (∀ u : AddValuation A (WithTop ℤ), (∀ r : O, 0 ≤ u (algebraMap O A r)) → 0 < u (algebraMap O A ϖ) → (∃ a, u a = 1) → ∃ ζ : Pts O A, ∀ a : A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = u a) ∧ ∀ a : A, (∀ ζ : Pts O A, Formalism.MainNotions.Gaps.EtaleWeightGaps.ord ϖ ζ a = ⊤) → a = 0 :=
  fun _ _ _ _ _ _ _ _ _ h => ⟨exists_ord_eq h, eq_zero_of_ord_eq_top h⟩

end GlobalTheory.OrdVal
end

