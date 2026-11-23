module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
public import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.BaseCh
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem rank_span_range_le_of_linearForm_comp_mem {X k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k]
    (W₀ : Submodule k₀ (X → k₀)) (n : ℕ) (hW₀ : Module.rank k₀ W₀ ≤ n) (z : X → k)
    (hz : ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) :
    Module.rank k₀ (Submodule.span k₀ (Set.range z)) ≤ n := by
  apply rank_le
  intro s hs
  have hy : LinearIndependent k₀ (fun i : s => (((i : Submodule.span k₀ (Set.range z))) : k)) :=
    hs.map' (Submodule.span k₀ (Set.range z)).subtype (Submodule.ker_subtype _)
  have hφ : ∀ j : s, ∃ φ : k →ₗ[k₀] k₀, ∀ i : s,
      φ (((i : Submodule.span k₀ (Set.range z))) : k) = if i = j then 1 else 0 := by
    intro j
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hy).coord j)
    refine ⟨g, fun i => ?_⟩
    have h1 := LinearMap.congr_fun hg (Module.Basis.span hy i)
    rw [Module.Basis.span_apply] at h1
    rw [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1, ← Module.Basis.span_apply hy i, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  choose φ hφ using hφ
  have hw : LinearIndependent k₀ (fun j : s => (⟨fun x => φ j (z x), hz (φ j)⟩ : W₀)) := by
    rw [linearIndependent_iff']
    intro t c hc j hj
    have hψz : ∀ x, (∑ i ∈ t, c i • φ i) (z x) = 0 := by
      intro x
      have := congrArg (fun v : W₀ => (v : X → k₀) x) hc
      simpa [LinearMap.sum_apply, Finset.sum_apply] using this
    have hψL : Submodule.span k₀ (Set.range z) ≤ LinearMap.ker (∑ i ∈ t, c i • φ i) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      exact hψz x
    have h2 := hψL (j : Submodule.span k₀ (Set.range z)).2
    rw [LinearMap.mem_ker, LinearMap.sum_apply] at h2
    simp only [LinearMap.smul_apply, hφ, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, hj, ite_true] at h2
    exact h2
  have hc := hw.cardinal_le_rank
  rw [Cardinal.mk_coe_finset] at hc
  exact_mod_cast hc.trans hW₀

private theorem mem_span_image_algebraMap_of_linearForm_comp_mem {X k₀ k : Type} [Field k₀] [Field k] [Algebra k₀ k]
    (W₀ : Submodule k₀ (X → k₀)) (n : ℕ) (hW₀ : Module.rank k₀ W₀ ≤ n) (z : X → k)
    (hz : ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) :
    z ∈ Submodule.span k ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) := by
  have hr := rank_span_range_le_of_linearForm_comp_mem W₀ n hW₀ z hz
  haveI : Module.Finite k₀ (Submodule.span k₀ (Set.range z)) :=
    Module.rank_lt_aleph0_iff.1 (hr.trans_lt Cardinal.natCast_lt_aleph0)
  set L := Submodule.span k₀ (Set.range z)
  let e := Module.finBasis k₀ L
  have hext : ∀ j, ∃ φ : k →ₗ[k₀] k₀, φ ∘ₗ L.subtype = e.coord j :=
    fun j => LinearMap.exists_extend (e.coord j)
  choose φ hφ using hext
  have hzx : ∀ x, z x = ∑ j, φ j (z x) • ((e j : L) : k) := by
    intro x
    have hx : z x ∈ L := Submodule.subset_span ⟨x, rfl⟩
    have h1 := congrArg L.subtype (e.sum_repr ⟨z x, hx⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    show L.subtype ⟨z x, hx⟩ = _
    rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Submodule.subtype_apply]
    congr 1
    have := LinearMap.congr_fun (hφ j) ⟨z x, hx⟩
    rw [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply] at this
    exact this.symm
  have hzeq : z = ∑ j, ((e j : L) : k) • (fun x => algebraMap k₀ k (φ j (z x))) := by
    funext x
    rw [hzx x, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
  rw [hzeq]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨_, hz (φ j), rfl⟩

theorem UpperTheory.V.Ws.rank_le_of_linearForm_comp_mem_of_rank_le :
    ∀ (X k₀ k : Type) [Field k₀] [Field k] [Algebra k₀ k] (W₀ : Submodule k₀ (X → k₀)) (W : Submodule k (X → k)) (n : ℕ), Module.rank k₀ W₀ ≤ n → (∀ z ∈ W, ∀ φ : k →ₗ[k₀] k₀, (fun x => φ (z x)) ∈ W₀) → Module.rank k W ≤ n := by
  intro X k₀ k _ _ _ W₀ W n hW₀ hW
  have hWS : W ≤ Submodule.span k
      ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) :=
    fun z hz => mem_span_image_algebraMap_of_linearForm_comp_mem W₀ n hW₀ z (hW z hz)
  let A : (X → k₀) →ₗ[k₀] (X → k) :=
    LinearMap.pi fun x => (Algebra.linearMap k₀ k).comp (LinearMap.proj x)
  let b := Module.Free.chooseBasis k₀ W₀
  have hsub : Submodule.span k
      ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀))) ≤
      Submodule.span k (Set.range fun i => A (b i : X → k₀)) := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    have h1 : A w ∈ Submodule.map (A ∘ₗ W₀.subtype) ⊤ := ⟨⟨w, hw⟩, trivial, rfl⟩
    rw [← b.span_eq, Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_le_restrictScalars k₀ k _ h1
  calc Module.rank k W
      ≤ Module.rank k (Submodule.span k
          ((fun w : X → k₀ => fun x => algebraMap k₀ k (w x)) '' (W₀ : Set (X → k₀)))) :=
        Submodule.rank_mono hWS
    _ ≤ Module.rank k (Submodule.span k (Set.range fun i => A (b i : X → k₀))) :=
        Submodule.rank_mono hsub
    _ ≤ Cardinal.mk (Set.range fun i => A (b i : X → k₀)) := rank_span_le _
    _ ≤ Cardinal.mk (Module.Free.ChooseBasisIndex k₀ W₀) := Cardinal.mk_range_le
    _ = Module.rank k₀ W₀ := (Module.Free.rank_eq_card_chooseBasisIndex k₀ W₀).symm
    _ ≤ n := hW₀
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CcConj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem emb_twist {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (i j : Ω →+* ℂ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ x, j (g x) = i x := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let iA : Ω →ₐ[ℚ] ℂ := i.toRatAlgHom
  let K : IntermediateField ℚ ℂ := jA.fieldRange
  let r : Ω →+* K :=
    { toFun := fun x => ⟨jA x, jA.mem_fieldRange.2 ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hr : Function.Bijective r := by
    constructor
    · intro x y hxy
      have : jA x = jA y := congrArg Subtype.val hxy
      exact jA.toRingHom.injective this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := jA.mem_fieldRange.1 hz
      exact ⟨x, rfl⟩
  haveI : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω K (RingEquiv.ofBijective r hr)
  have hi : ∀ x, ∃ y, j y = i x := by
    intro x
    have h1 : IsIntegral ℚ (iA x) := (Algebra.IsIntegral.isIntegral x).map iA
    have h2 : IsIntegral K (iA x) := h1.tower_top
    have h3 := minpoly.mem_range_of_degree_eq_one K (iA x)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h2))
    obtain ⟨k, hk⟩ := h3
    obtain ⟨y, hy⟩ := jA.mem_fieldRange.1 k.2
    refine ⟨y, ?_⟩
    have : jA y = iA x := by rw [hy]; exact hk
    exact this
  choose φ hφ using hi
  let h0 : Ω →+* Ω :=
    { toFun := φ
      map_one' := j.injective (by rw [hφ, map_one, map_one])
      map_mul' := fun x y => j.injective (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_zero' := j.injective (by rw [hφ, map_zero, map_zero])
      map_add' := fun x y => j.injective (by rw [hφ, map_add (f := _), map_add (f := _), hφ, hφ]) }
  let hA : Ω →ₐ[ℚ] Ω := h0.toRatAlgHom
  have hb : Function.Bijective hA := Algebra.IsAlgebraic.algHom_bijective hA
  exact ⟨AlgEquiv.ofBijective hA hb, fun x => hφ x⟩

theorem UpperTheory.V.Ws.isConj_of_isComplexConjugation :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (σ τ : G ℚ Ω), IsCC σ → IsCC τ → IsConj σ τ := by
  intro Ω _ _ _ σ τ hσ hτ
  obtain ⟨jσ, hjσ⟩ := hσ
  obtain ⟨jτ, hjτ⟩ := hτ
  obtain ⟨g, hg⟩ := emb_twist jσ jτ
  rw [isConj_iff]
  refine ⟨g, AlgEquiv.ext fun y => jτ.injective ?_⟩
  have e1 : jσ (g⁻¹ y) = jτ y := by
    rw [← hg]
    congr 1
    exact AlgEquiv.apply_symm_apply g y
  show jτ (g (σ (g⁻¹ y))) = jτ (τ y)
  rw [hg, hjσ, e1, hjτ]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ClosedInf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem addClosed_index (l : ℕ) [Fact l.Prime] (A : AddSubgroup ℤ_[l])
    (hA : IsClosed (A : Set ℤ_[l])) (a : ℤ_[l]) (ha : a ∈ A) (h0 : a ≠ 0) : A.index ≠ 0 := by
  have key : ∀ x : ℤ_[l], a * x ∈ A := by
    intro x
    refine PadicInt.denseRange_intCast.induction_on x ?_ ?_
    · exact hA.preimage (continuous_const.mul continuous_id)
    · intro m
      have hm : a * (m : ℤ_[l]) = m • a := by rw [zsmul_eq_mul, mul_comm]
      rw [hm]
      exact A.zsmul_mem ha m
  have hspec := PadicInt.unitCoeff_spec h0
  set w := PadicInt.unitCoeff h0
  set n := a.valuation
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let f := (PadicInt.toZModPow (p := l) n).toAddMonoidHom
  have hle : f.ker ≤ A := by
    intro x hx
    have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hx
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hw : (w : ℤ_[l]) * ↑w⁻¹ = 1 := Units.mul_inv w
    have heq : (l : ℤ_[l]) ^ n * y = a * (↑w⁻¹ * y) := by
      conv_rhs => rw [hspec]
      linear_combination (-((l : ℤ_[l]) ^ n * y)) * hw
    rw [heq]
    exact key _
  have hfin : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  intro hA0
  apply hfin
  exact Nat.eq_zero_of_zero_dvd (hA0 ▸ AddSubgroup.index_dvd_of_le hle)

open GroundTheory.Global.Cyclotomic in
theorem UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → (∃ u ∈ H, ¬ IsOfFinOrder u) → H.index ≠ 0 := by
  intro l _ H hH hu
  obtain ⟨u, huH, hu⟩ := hu
  set L := padicUnitsLog l with hL
  have hB : IsClosed ((H.map L : Subgroup (Multiplicative ℤ_[l])) : Set (Multiplicative ℤ_[l])) := by
    rw [Subgroup.coe_map]
    exact ((hH.isCompact).image (continuous_padicUnitsLog l)).isClosed
  let A : AddSubgroup ℤ_[l] := Subgroup.toAddSubgroup' (H.map L)
  have hAc : IsClosed (A : Set ℤ_[l]) := hB
  have haA : Multiplicative.toAdd (L u) ∈ A := by
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨u, huH, rfl⟩
  have ha0 : Multiplicative.toAdd (L u) ≠ 0 := by
    intro h
    apply hu
    have h1 : L u = 1 := by
      rw [← ofAdd_toAdd (L u), h]
      rfl
    rw [hL, padicUnitsLog_eq_one_iff] at h1
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, torsionExponent_pos l, h1⟩
  have hAi : A.index ≠ 0 := addClosed_index l A hAc _ haA ha0
  have hMi : (H.map L).index ≠ 0 := hAi
  have hK : (H ⊔ L.ker).index ≠ 0 := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ (padicUnitsLog_surjective l)]
    exact hMi
  have hker : L.ker ≤ rootsOfUnity (torsionExponent l) ℤ_[l] := by
    intro x hx
    rw [mem_rootsOfUnity]
    rw [MonoidHom.mem_ker, hL, padicUnitsLog_eq_one_iff] at hx
    exact hx
  have hcard : Nat.card L.ker ≠ 0 := by
    haveI : NeZero (torsionExponent l) := ⟨(torsionExponent_pos l).ne'⟩
    haveI : Finite L.ker := Finite.of_injective (Subgroup.inclusion hker) (Subgroup.inclusion_injective hker)
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have hrel : H.relIndex (H ⊔ L.ker) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_right]
    intro h0
    apply hcard
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_card H L.ker)
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ L.ker)]
  exact mul_ne_zero hrel hK
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.CocycleCardEulerFormula
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

theorem UpperTheory.V.Ws.cocycle_card_euler_formula :
    ∀ (R Γ M : Type) [CommRing R] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M), ContAction ρ → Finite (H1 ρ) → Finite (Z1 ρ) ∧ Nat.card (Z1 ρ) * Nat.card (H0 ρ) = Nat.card (H1 ρ) * Nat.card M := by
  intro R Γ M _ _ _ _ _ _ _ _ ρ hρ hH1
  have hB1Z1 : B1 ρ ≤ Z1 ρ := by
    intro f hf
    obtain ⟨m, rfl⟩ := LinearMap.mem_range.1 hf
    rw [mem_Z1_iff_cocycle]
    have hfun : (d0 ρ m) = fun g => ρ g m - m := funext fun g => amitsur_d0_apply ρ m g
    refine ⟨?_, fun g h => ?_⟩
    · rw [hfun]
      exact (hρ.comp (Continuous.prodMk continuous_id continuous_const)).sub continuous_const
    · simp only [amitsur_d0_apply, map_mul, Module.End.mul_apply, map_sub]
      abel
  have hker : LinearMap.ker (d0 ρ) = H0 ρ := by
    ext m
    rw [LinearMap.mem_ker, mem_riemannRochSpace_iff_regularAt_everywhere]
    constructor
    · intro h g
      have := congrFun h g
      rw [amitsur_d0_apply, Pi.zero_apply, sub_eq_zero] at this
      exact this
    · intro h
      funext g
      rw [amitsur_d0_apply, h g, sub_self, Pi.zero_apply]
  have hq : Nat.card (M ⧸ LinearMap.ker (d0 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (d0 ρ).quotKerEquivRange.toEquiv
  have hM := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (d0 ρ))
  rw [hq, hker] at hM
  have hB : Nat.card (Submodule.comap (Z1 ρ).subtype (B1 ρ)) = Nat.card (B1 ρ) :=
    Nat.card_congr (Submodule.comapSubtypeEquivOfLe hB1Z1).toEquiv
  have hZ := Submodule.card_eq_card_quotient_mul_card (Submodule.comap (Z1 ρ).subtype (B1 ρ))
  rw [hB] at hZ
  have hMpos : Nat.card M ≠ 0 := Nat.card_pos.ne'
  have hB1pos : Nat.card (B1 ρ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hM
    exact hMpos hM
  have hH1pos : Nat.card (H1 ρ) ≠ 0 := Nat.card_pos.ne'
  refine ⟨Nat.finite_of_card_ne_zero ?_, ?_⟩
  · rw [hZ]
    exact mul_ne_zero hB1pos hH1pos
  · rw [hZ, hM]
    change Nat.card (B1 ρ) * Nat.card (H1 ρ) * Nat.card (H0 ρ) =
      Nat.card (H1 ρ) * (Nat.card (H0 ρ) * Nat.card (B1 ρ))
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.DescGS
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem continuous_of_right_invariant_open_subgroup {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (H : Subgroup Γ) (hH : IsOpen (H : Set Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ H, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_const_mul g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht (hH.mem_nhds H.one_mem)] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.exists_descent_to_galoisGroupUnramifiedOutside :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (ρ : Representation R (G F Ω) M) (K : Subgroup (G F Ω)) (N : ℕ), (∀ v, v ∈ plDvd F N → v ∈ S) → (∀ σ ∈ ineOff F Ω N, ∀ m, ρ σ m = m) → IsOpen (K : Set (G F Ω)) → (∀ σ ∈ K, ∀ m, ρ σ m = m) → ∃ ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M, (∀ g m, ρS (toGS Ω _ g) m = ρ g m) ∧ ContAction ρS ∧ ∀ z ∈ cocOff ρ (ineOff F Ω N), ∃ y ∈ Z1 ρS, ∀ g, y (toGS Ω _ g) = z g := by
  intro F Ω _ _ _ _ _ R M _ _ _ _ _ _ S ρ K N hS hine hK hKρ
  have hN : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ (S : Set (HeightOneSpectrum (𝓞 F))) →
      ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Inertia A, σ ∈ ineOff F Ω N := by
    intro v hv A hA σ hσ
    refine ⟨A, ?_, hσ⟩
    intro hlt
    apply hv
    apply hS
    have h1 := (hA (N : 𝓞 F)).1
    simp only [plDvd, Set.mem_setOf_eq]
    apply h1
    simpa using hlt
  have hNS : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ ρ.ker := by
    have hker : ∀ g, g ∈ ρ.ker ↔ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h m
        rw [h]
        rfl
      · intro h
        exact LinearMap.ext h
    have hopen : IsOpen (ρ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      apply Filter.mem_of_superset (hK.mem_nhds K.one_mem)
      intro σ hσ
      exact (hker σ).2 (hKρ σ hσ)
    apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
    apply Subgroup.normalClosure_le_normal
    intro σ hσ
    simp only [Set.mem_iUnion] at hσ
    obtain ⟨v, hv, A, hA, hσ⟩ := hσ
    exact (hker σ).2 (hine σ (hN v hv A hA σ hσ))
  let ρS : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    QuotientGroup.lift _ ρ hNS
  have hρS : ∀ g m, ρS (toGS Ω _ g) m = ρ g m := by
    intro g m
    rfl
  refine ⟨ρS, hρS, ?_, ?_⟩
  · show Continuous fun p : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) × M => ρS p.1 p.2
    rw [continuous_prod_of_discrete_right]
    intro m
    rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    apply continuous_of_right_invariant_open_subgroup K hK
    intro g h hh
    show ρ (g * h) m = ρ g m
    rw [map_mul, Module.End.mul_apply, hKρ h hh]
  · intro z hz
    obtain ⟨hzlc, hzc, hz0⟩ := hz
    have hz1 : z 1 = 0 := by
      have := hzc 1 1
      simp only [mul_one, map_one, Module.End.one_apply] at this
      simpa using this
    let φ : G F Ω →* Function.End M :=
      { toFun := fun g m => ρ g m + z g
        map_one' := by
          funext m
          show ρ 1 m + z 1 = m
          rw [hz1, map_one]
          simp
        map_mul' := by
          intro g h
          funext m
          show ρ (g * h) m + z (g * h) = ρ g (ρ h m + z h) + z g
          rw [hzc, map_mul, Module.End.mul_apply, map_add (f := _)]
          abel }
    have hkerφ : ∀ g, g ∈ φ.ker ↔ z g = 0 ∧ ∀ m, ρ g m = m := by
      intro g
      rw [MonoidHom.mem_ker]
      constructor
      · intro h
        have h' : ∀ m, ρ g m + z g = m := fun m => congrFun h m
        have h0 : z g = 0 := by simpa using h' 0
        refine ⟨h0, fun m => ?_⟩
        simpa [h0] using h' m
      · rintro ⟨h0, h1⟩
        funext m
        show ρ g m + z g = m
        rw [h0, h1, add_zero]
    have hopen : IsOpen (φ.ker : Set (G F Ω)) := by
      apply Subgroup.isOpen_of_mem_nhds (g := 1)
      have hU : z ⁻¹' {0} ∈ nhds (1 : G F Ω) :=
        (hzlc.isOpen_fiber 0).mem_nhds (by simpa using hz1)
      apply Filter.mem_of_superset (Filter.inter_mem (hK.mem_nhds K.one_mem) hU)
      rintro σ ⟨hσK, hσz⟩
      exact (hkerφ σ).2 ⟨hσz, hKρ σ hσK⟩
    have hNSφ : NS Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≤ φ.ker := by
      apply Subgroup.topologicalClosure_minimal _ _ (Subgroup.isClosed_of_isOpen _ hopen)
      apply Subgroup.normalClosure_le_normal
      intro σ hσ
      simp only [Set.mem_iUnion] at hσ
      obtain ⟨v, hv, A, hA, hσ⟩ := hσ
      have hm := hN v hv A hA σ hσ
      exact (hkerφ σ).2 ⟨hz0 σ hm, hine σ hm⟩
    let φS := QuotientGroup.lift _ φ hNSφ
    let y : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) → M := fun q => φS q 0
    have hy : ∀ g, y (toGS Ω _ g) = z g := by
      intro g
      show ρ g 0 + z g = z g
      simp
    refine ⟨y, ⟨?_, ?_⟩, hy⟩
    · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
      have : (y ∘ QuotientGroup.mk) = z := funext hy
      rw [this]
      exact hzlc.continuous
    · intro q₁ q₂
      induction q₁ using QuotientGroup.induction_on with
      | H g =>
        induction q₂ using QuotientGroup.induction_on with
        | H h =>
          have e := hy (g * h)
          rw [map_mul] at e
          show y (toGS Ω _ g * toGS Ω _ h) = y (toGS Ω _ g) + ρS (toGS Ω _ g) (y (toGS Ω _ h))
          rw [e, hy, hy, hρS, hzc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RealPlaceConjugation.ExistsZmodPrimeRepresentationOfTorsion
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem UpperTheory.V.Ws.exists_zmod_representation (n : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R]
    [AddCommGroup M] [Module R M] [Module (ZMod n) M] (ρ : Representation R Γ M) :
    ∃ ρ' : Representation (ZMod n) Γ M, ∀ g m, ρ' g m = ρ g m := by
  refine ⟨{ toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap n
            map_one' := ?_
            map_mul' := ?_ }, ?_⟩
  · ext m
    simp
  · intro g h
    ext m
    simp
  · intro g m
    rfl

theorem UpperTheory.V.Ws.exists_zmod_prime_representation_of_torsion :
    ∀ (l : ℕ) (Γ : Type) [Group Γ] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M], (∀ m : M, l • m = 0) → ∀ ρ : Representation R Γ M, ∃ (_ : Module (ZMod (l ^ 1)) M) (ρ' : Representation (ZMod (l ^ 1)) Γ M), ∀ g m, ρ' g m = ρ g m := by
  intro l Γ _ R M _ _ _ hl ρ
  letI : Module (ZMod (l ^ 1)) M := AddCommGroup.zmodModule (fun m => by simpa using hl m)
  obtain ⟨ρ', hρ'⟩ := UpperTheory.V.Ws.exists_zmod_representation (l ^ 1) Γ R M ρ
  exact ⟨this, ρ', hρ'⟩
end

