module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCyclotomicBlockCocyclesLeSha

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.RedMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

theorem UpperTheory.V.Ws.Bl.redMem :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T) (n : ℕ) z y, IsZn ρ c N H P (n + 1) z y → IsZn ρ c N H P n (fun g => redn A T n (z g)) (redn A T n y) ∧
          (Prim z → 0 < n → Prim fun g => redn A T n (z g)) ∧ (Prim (fun g => redn A T n (z g)) → Prim z) := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P n z y hz
  have eqv : ∀ (g : Γ) (w : T ⧸ lev A T (n + 1)),
      redn A T n (modRep ρ (n + 1) g w) = modRep ρ n g (redn A T n w) := by
    intro g w
    obtain ⟨x, rfl⟩ := (lev A T (n + 1)).mkQ_surjective w
    rw [modRep_mk, redn_mk, redn_mk, modRep_mk]
  have img : ∀ (Q : Submodule A T) (w : T ⧸ lev A T (n + 1)), w ∈ Q.map (lev A T (n + 1)).mkQ →
      redn A T n w ∈ Q.map (lev A T n).mkQ := by
    rintro Q _ ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  refine ⟨⟨hz.lc.comp (redn A T n), fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_, ?_⟩
  · rw [hz.coc, map_add (f := _), eqv]
  · rw [hz.cz, map_zero]
  · rw [hz.kill g hg, map_zero]
  · have := img P _ (hz.loc h hh)
    rw [map_sub, map_sub, eqv] at this
    exact this
  · rintro ⟨g, hg⟩ hn
    refine ⟨g, fun hm => hg ?_⟩
    obtain ⟨x, hx⟩ := (lev A T (n + 1)).mkQ_surjective (z g)
    obtain ⟨x', hx', e⟩ := hm
    have e' : (lev A T n).mkQ x' = (lev A T n).mkQ x := by rw [e, ← redn_mk, hx]
    have hd : x' - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e'
    have hle : lev A T n ≤ lev A T 1 := Submodule.smul_mono_left (Ideal.pow_le_pow_right hn)
    refine ⟨x, ?_, hx⟩
    have := (lev A T 1).sub_mem hx' (hle hd)
    rwa [sub_sub_cancel] at this
  · rintro ⟨g, hg⟩
    exact ⟨g, fun hm => hg (img _ _ hm)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.SelToZc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem exists_norm {Γ R M : Type} [Group Γ] [TopologicalSpace Γ] [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M] (ρ : Representation R Γ M) (hρ : ContAction ρ)
    (h2 : Function.Surjective fun m : M => m + m) (c : Γ) (hc : ∀ m, ρ c m = -m) (x : H1 ρ) :
    ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 c = 0 := by
  obtain ⟨z0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m, hm⟩ := h2 (-(z0.1 c))
  have hB : d0 ρ m ∈ Z1 ρ := coboundaries_le_cocycles ρ hρ (LinearMap.mem_range_self _ m)
  refine ⟨z0 - ⟨d0 ρ m, hB⟩, ?_, ?_⟩
  · rw [Submodule.Quotient.eq, Submodule.mem_comap, sub_sub_cancel_left, map_neg]
    exact Submodule.neg_mem _ ⟨m, rfl⟩
  · show z0.1 c - d0 ρ m c = 0
    rw [amitsur_d0_apply, hc]
    have hm' : m + m = -(z0.1 c) := hm
    calc z0.1 c - (-m - m) = z0.1 c + (m + m) := by abel
      _ = 0 := by rw [hm']; abel

theorem UpperTheory.V.Ws.Bl.selToZc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (ρ : Representation R (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M), ContAction ρ → (Function.Bijective fun m : M => m + m) →
          ∀ c : G ℚ Ω, (∀ m, ρ (toGS Ω _ c) m = -m) → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) →
          ∀ v0 : S, ((l : ℕ) : 𝓞 ℚ) ∈ v0.1.asIdeal → ∀ (P : Set M) (K : Subgroup (G ℚ Ω)), (∀ g ∈ K, ∀ m, ρ (toGS Ω _ g) m = m) →
          ∀ L : LocCond ρ (locFam S Av), (∀ v, v ≠ v0 → L v ≤ H1ur (ρ.comp (locFam S Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) →
          (∀ z : Z1 (ρ.comp (locFam S Av v0)), (Submodule.Quotient.mk z : H1 (ρ.comp (locFam S Av v0))) ∈ L v0 → ∃ y, ∀ h, z.1 h - (ρ (locFam S Av v0 h) y - y) ∈ P) →
          ∃ f : Sel ρ (locFam S Av) (continuous_locFam S Av) L → Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P, Function.Injective f := by
  intro Ω _ _ _ l _ R M _ _ _ _ _ S ρ hρ hbij c hcneg Av hAv v0 hlv0 P K hK L hL hP
  have val_top {Ω : Type} [Field Ω] {x : Ω} (h : (⊤ : ValuationSubring Ω).valuation x < 1) : x = 0 := by
    by_contra hx
    have h1 : (⊤ : ValuationSubring Ω).valuation x⁻¹ ≤ 1 :=
      (ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _)
    have h2 := mul_lt_one_of_nonneg_of_lt_one_left zero_le h h1
    rw [← map_mul, mul_inv_cancel₀ hx, map_one] at h2
    exact lt_irrefl _ h2

  have int_le {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {b : Ω} (hb : IsIntegral ℤ b) :
      A.valuation b ≤ 1 := by
    have h : IsIntegral A b := hb.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [A.valuation_le_one_iff, ← hy]
    exact y.2

  have exists_place (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
      (A : ValuationSubring Ω) (hA : A ≠ ⊤) : ∃ v : HeightOneSpectrum (𝓞 K),
        ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ v.asIdeal := by
    have hm : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x =>
      (A.valuation_le_one_iff _).1 (int_le A (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom))
    let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hm
    let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
    have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
      (A.valuation_lt_one_iff (f x)).symm
    refine ⟨⟨P, inferInstance, fun h0 => hA ?_⟩, hP⟩
    rw [eq_top_iff]
    intro x _
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
    have h1 : Algebra.IsAlgebraic ℤ K := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := K)).2 inferInstance
    have h2 : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ K Ω
    obtain ⟨n, hn, hi⟩ := (h2.isAlgebraic x).exists_integral_multiple
    have h3 : ¬ A.valuation (algebraMap K Ω ((n : 𝓞 K) : K)) < 1 := by
      rw [hP, h0, Ideal.mem_bot]
      exact Int.cast_ne_zero.2 hn
    have h4 : A.valuation (n : Ω) = 1 :=
      le_antisymm (int_le A (isIntegral_algebraMap (R := ℤ) (x := n))) (by simpa using h3)
    have h5 := int_le A hi
    rw [zsmul_eq_mul, map_mul, h4, one_mul] at h5
    exact (A.valuation_le_one_iff x).1 h5

  have placeDict : Ine (F := ℚ) (⊤ : ValuationSubring Ω) = ⊥ ∧
      (∀ A : ValuationSubring Ω, A ≠ ⊤ → ∃ v : HeightOneSpectrum (𝓞 ℚ), IsPlaceOver A v) := by
    refine ⟨?_, fun A hA => exists_place ℚ Ω A hA⟩
    rw [eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    ext x
    have h := hg.2 x ((ValuationSubring.valuation_le_one_iff _ _).2 (ValuationSubring.mem_top _))
    exact sub_eq_zero.1 (val_top h)
  have hex : ∀ x : H1 ρ, ∃ z : Z1 ρ, (Submodule.Quotient.mk z : H1 ρ) = x ∧ z.1 (toGS Ω _ c) = 0 :=
    fun x => exists_norm ρ hρ hbij.2 (toGS Ω _ c) hcneg x
  have hA : ∀ x : H1 ρ, x ∈ Sel ρ (locFam S Av) (continuous_locFam S Av) L → ∀ z : Z1 ρ,
      (Submodule.Quotient.mk z : H1 ρ) = x → z.1 (toGS Ω _ c) = 0 →
      (fun g => z.1 (toGS Ω _ g)) ∈ Zc (fun g m => ρ (toGS Ω _ g) m) c (neSet l K) (Dec (F := ℚ) (Av v0)) P := by
    intro x hx z hzx hzc
    subst hzx
    have hcoc : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := ((mem_Z1_iff_cocycle _ _).mp z.2).2
    have hz1 : z.1 1 = 0 := by
      have h := hcoc 1 1
      rw [one_mul, map_one, Module.End.one_apply] at h
      simpa using h
    have hmemv : ∀ v, (Submodule.Quotient.mk (restrictCocycles1 ρ (locFam S Av v) (continuous_locFam S Av v) z) :
        H1 (ρ.comp (locFam S Av v))) ∈ L v := fun v => (mem_Sel _ _ _ _ _).mp hx v
    obtain ⟨y, hy⟩ := hP _ (hmemv v0)
    refine ⟨y, ⟨?_, ?_, hzc, ?_, ?_⟩⟩
    · exact ((IsLocallyConstant.iff_continuous _).mpr ((mem_Z1_iff_cocycle _ _).mp z.2).1).comp_continuous
        continuous_quot_mk
    · intro g h
      show z.1 (toGS Ω _ (g * h)) = z.1 (toGS Ω _ g) + ρ (toGS Ω _ g) (z.1 (toGS Ω _ h))
      rw [map_mul]
      exact hcoc _ _
    · rintro g ⟨hgK, A, hAl, hgA⟩
      show z.1 (toGS Ω _ g) = 0
      by_cases hAtop : A = ⊤
      · subst hAtop
        rw [(placeDict).1, Subgroup.mem_bot] at hgA
        rw [hgA, map_one, hz1]
      obtain ⟨v, hAv'⟩ := (placeDict).2 A hAtop
      by_cases hvS : v ∈ S
      · set w : S := ⟨v, hvS⟩
        have hne : w ≠ v0 := by
          intro hw
          apply hAl
          have h := (hAv' (l : 𝓞 ℚ)).mpr (by rw [show v = v0.1 from congrArg Subtype.val hw]; exact hlv0)
          simpa using h
        obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver (hAv w) hAv'
        rw [← hσ] at hgA
        have hgA' : σ⁻¹ * g * σ ∈ Ine (F := ℚ) (Av w) := GlobalTheory.Cut.ShaBound.conj_mem_Ine' hgA
        have hur := hL w hne (hmemv w)
        rw [H1ur, LinearMap.mem_ker] at hur
        have hur' := (Submodule.Quotient.mk_eq_zero _).mp hur
        rw [Submodule.mem_comap] at hur'
        obtain ⟨m, hm⟩ := hur'
        have hj := congrFun hm ⟨⟨σ⁻¹ * g * σ, Ine_le_Dec _ hgA'⟩, hgA'⟩
        rw [amitsur_d0_apply] at hj
        have hconj : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = 0 := by
          have hj' : z.1 (toGS Ω _ (σ⁻¹ * g * σ)) = ρ (toGS Ω _ (σ⁻¹ * g * σ)) m - m := hj.symm
          rw [hj']
          rw [map_mul, map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply,
            show ρ (toGS Ω _ g) (ρ (toGS Ω _ σ) m) = ρ (toGS Ω _ σ) m from hK g hgK _,
            ← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel, map_one, Module.End.one_apply, sub_self]
        set a := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) σ
        set b := toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g
        have hb : ∀ m, ρ b m = m := hK g hgK
        rw [map_mul, map_mul, map_inv] at hconj
        have e1 := hcoc (a⁻¹ * b) a
        have e2 := hcoc a⁻¹ b
        have e3 := hcoc a⁻¹ a
        rw [inv_mul_cancel, hz1] at e3
        rw [map_mul, Module.End.mul_apply, hb, e2, hconj] at e1
        have hinv0 : ρ a⁻¹ (z.1 b) = 0 := by
          have : (0 : M) = ρ a⁻¹ (z.1 b) + (z.1 a⁻¹ + ρ a⁻¹ (z.1 a)) := by rw [e1]; abel
          rw [← e3, add_zero] at this
          exact this.symm
        have : z.1 b = ρ a (ρ a⁻¹ (z.1 b)) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
        rw [this, hinv0, map_zero]
      · have hgN : g ∈ NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) :=
          Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure
            (Set.mem_iUnion₂.mpr ⟨v, hvS, Set.mem_iUnion₂.mpr ⟨A, hAv', hgA⟩⟩))
        rw [show toGS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ))) g = 1 from (QuotientGroup.eq_one_iff g).mpr hgN, hz1]
    · intro h hh
      exact hy ⟨h, hh⟩
  choose zc hzc using hex
  refine ⟨fun x => ⟨fun g => (zc x.1).1 (toGS Ω _ g), hA x.1 x.2 (zc x.1) (hzc x.1).1 (hzc x.1).2⟩, ?_⟩
  intro x x' hxx
  have hfun : (fun g => (zc x.1).1 (toGS Ω _ g)) = (fun g => (zc x'.1).1 (toGS Ω _ g)) :=
    congrArg Subtype.val hxx
  have hz : zc x.1 = zc x'.1 := by
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) q
    exact congrFun hfun g
  apply Subtype.ext
  rw [← (hzc x.1).1, ← (hzc x'.1).1, hz]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistFlag
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem UpperTheory.V.Ws.Bl.sup_mul_up {R : Type} [CommRing R] {N U : M4 R} (hN : IsSUp N) (hU : IsUp U) :
    IsSUp (N * U) := by
  intro i j h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases e : k ≤ i
  · rw [hN i k e, zero_mul]
  · rw [hU k j (lt_of_le_of_lt h (not_le.mp e)), mul_zero]

theorem UpperTheory.V.Ws.Bl.twistFlag :
    ∀ (R : Type) [CommRing R] (X X' Z y u : M4 R), IsBlock X → IsBlock X' → X' * X = 1 → Z ∈ uM R → y ∈ uM R → IsGSp 1 u → IsUp (adj u * X * u) → IsSUp (adj u * (Z - (X * y * X' - y)) * u) →
          IsUp (adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u)) ∧ ∀ i, (adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u) : M4 R) i i = (adj u * X * u : M4 R) i i := by
  intro R _ X X' Z y u hX hX' hX'X hZM hyM hu hUp hS
  have g := grp R
  have hZ : Z ∈ hAB R := hZM.1
  have hy : y ∈ hAB R := hyM.1
  have hys : adj y = -y := hyM.2
  have hP : X * y * X' ∈ hAB R := hAB_mul_mul hX hy hX'
  have hyZ : y * Z = 0 := hAB_mul_hAB hy hZ
  have hyP : y * (X * y * X') = 0 := hAB_mul_hAB hy hP
  have hZP : Z * (X * y * X') = 0 := hAB_mul_hAB hZ hP
  have adjneg : ∀ W : M4 R, adj (-W) = -adj W := by
    intro W
    rw [← neg_one_smul R W, g.2.2.2.1, neg_one_smul]
  have huu : u * adj u = 1 := by
    have h : adj u * u = 1 := by
      have h0 : adj u * u = (1 : R) • 1 := hu
      rw [h0, one_smul]
    exact mul_eq_one_comm.mp h
  have e0 : (1 + y) * (1 + Z) = 1 + y + Z := by
    rw [add_mul, one_mul, mul_add, mul_one, hyZ, add_zero]
    abel
  have e1 : X * (1 + -y) = (1 - X * y * X') * X := by
    rw [sub_mul, one_mul, mul_assoc (X * y), hX'X, mul_one, mul_add, mul_one, mul_neg, sub_eq_add_neg]
  have e2 : (1 + y + Z) * (1 - X * y * X') = 1 + (Z - (X * y * X' - y)) := by
    rw [mul_sub, mul_one, add_mul, add_mul, one_mul, hyP, hZP]
    abel
  have hmid : (1 + y) * ((1 + Z) * X) * (1 + -y) = (1 + (Z - (X * y * X' - y))) * X := by
    calc (1 + y) * ((1 + Z) * X) * (1 + -y) = ((1 + y) * (1 + Z)) * (X * (1 + -y)) := by
          simp only [mul_assoc]
      _ = (1 + y + Z) * ((1 - X * y * X') * X) := by rw [e0, e1]
      _ = ((1 + y + Z) * (1 - X * y * X')) * X := (mul_assoc _ _ _).symm
      _ = (1 + (Z - (X * y * X' - y))) * X := by rw [e2]
  have key : adj ((1 - y) * u) * ((1 + Z) * X) * ((1 - y) * u)
      = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by
    rw [show (1 : M4 R) - y = 1 + -y from sub_eq_add_neg 1 y, g.1, g.2.2.1, g.2.2.2.2.1, adjneg, hys, neg_neg]
    calc adj u * (1 + y) * ((1 + Z) * X) * ((1 + -y) * u)
          = adj u * ((1 + y) * ((1 + Z) * X) * (1 + -y)) * u := by simp only [mul_assoc]
      _ = adj u * ((1 + (Z - (X * y * X' - y))) * X) * u := by rw [hmid]
      _ = adj u * X * u + adj u * ((Z - (X * y * X' - y)) * X) * u := by
          rw [add_mul, one_mul, mul_add, add_mul]
      _ = adj u * X * u + (adj u * (Z - (X * y * X' - y)) * u) * (adj u * X * u) := by
          congr 1
          simp only [mul_assoc]
          rw [← mul_assoc u (adj u), huu, one_mul]
  rw [key]
  constructor
  · intro i j hji
    rw [Matrix.add_apply, hUp i j hji, sup_mul_up hS hUp i j hji.le, add_zero]
  · intro i
    rw [Matrix.add_apply, sup_mul_up hS hUp i i le_rfl, add_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistPt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem ent_eq {R : Type} [CommRing R] {X Z : M4 R} (hX : IsBlock X) (hZ : Z ∈ hAB R) (i j : Fin 4)
    (h : ¬ lamW i < lamW j) : ((1 + Z) * X) i j = X i j := by
  have hZX : (Z * X) i j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hik : lamW i < lamW k
    · rw [hX k j (fun e => h (e ▸ hik)), mul_zero]
    · rw [hZ i k hik, zero_mul]
  rw [add_mul, one_mul, Matrix.add_apply, hZX, add_zero]

theorem UpperTheory.V.Ws.Bl.twistPt :
    ∀ (R : Type) [CommRing R] (X Z : M4 R), IsBlock X → Z ∈ uM R → (∀ ν Y, IsGSp ν Y → IsGSp ν ((1 + Z) * Y)) ∧ (∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0) ∧
          ((1 + Z) * X).submatrix ixB ixB = X.submatrix ixB ixB ∧ ((1 + Z) * X).charpoly = X.charpoly := by
  intro R _ X Z hX hZ
  have hZa : Z ∈ hAB R := hZ.1
  have hZs : adj Z = -Z := hZ.2
  have hZZ : Z * Z = 0 := hAB_mul_hAB hZa hZa
  have hlow : ∀ i j, lamW j < lamW i → ((1 + Z) * X) i j = 0 := by
    intro i j hij
    rw [ent_eq hX hZa i j (fun h => lt_asymm h hij)]
    exact hX i j hij.ne'
  refine ⟨?_, hlow, ?_, ?_⟩
  · intro ν Y hY
    have g := grp R
    have h1 : (1 + -Z) * (1 + Z) = 1 := by
      rw [add_mul, one_mul, neg_mul, mul_add, mul_one, hZZ, add_zero]
      abel
    show adj ((1 + Z) * Y) * ((1 + Z) * Y) = ν • 1
    rw [g.1, g.2.2.1, g.2.2.2.2.1, hZs, mul_assoc, ← mul_assoc (1 + -Z), h1, one_mul]
    exact hY
  · ext a b
    exact ent_eq hX hZa _ _ (by fin_cases a <;> fin_cases b <;> decide)
  · have hT : ((1 + Z) * X).BlockTriangular lamW := fun _ _ h => hlow _ _ h
    have hTX : X.BlockTriangular lamW := fun _ _ h => hX _ _ h.ne'
    rw [hT.charpoly, hTX.charpoly]
    refine Finset.prod_congr rfl fun a _ => ?_
    congr 1
    ext i j
    simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
    exact ent_eq hX hZa _ _ (by rw [i.2, j.2]; exact lt_irrefl a)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UMFacts
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private def uMat {R : Type} [CommRing R] (v : Fin 3 → R) : UpperTheory.V.GradeZeroInterpolatingElement.M4 R :=
  !![0, 0, 0, 0; v 0, 0, v 1, 0; 0, 0, 0, 0; v 2, 0, -v 0, 0]

private theorem uMat_mem {R : Type} [CommRing R] (v : Fin 3 → R) : uMat v ∈ uM R := by
  show uMat v ∈ hAB R ⊓ sp4 R
  rw [Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · show ∀ i j, ¬ lamW i < lamW j → uMat v i j = 0
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [uMat, lamW]
  · show adj (uMat v) = -uMat v
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, uMat, Fin.rev]

private theorem uMat_eq {R : Type} [CommRing R] (Y : uM R) : uMat ![Y.1 1 0, Y.1 1 2, Y.1 3 0] = Y.1 := by
  obtain ⟨Y, hY⟩ := Y
  have hA := (Submodule.mem_inf.mp hY).1
  have hS := (Submodule.mem_inf.mp hY).2
  change ∀ i j, ¬ lamW i < lamW j → Y i j = 0 at hA
  change adj Y = -Y at hS
  have h32 := congrFun (congrFun hS 3) 2
  simp [adj_apply, sgn, Fin.rev] at h32
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> first
    | exact (hA _ _ (by decide)).symm
    | (rw [h32]; ring)
    | skip

private theorem uMat_add {R : Type} [CommRing R] (v w : Fin 3 → R) : uMat (v + w) = uMat v + uMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> ring

private theorem uMat_smul {R : Type} [CommRing R] (c : R) (v : Fin 3 → R) : uMat (c • v) = c • uMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat]

private def uEq (R : Type) [CommRing R] : (Fin 3 → R) ≃ₗ[R] uM R where
  toFun v := ⟨uMat v, uMat_mem v⟩
  map_add' v w := Subtype.ext (uMat_add v w)
  map_smul' c v := Subtype.ext (uMat_smul c v)
  invFun Y := ![Y.1 1 0, Y.1 1 2, Y.1 3 0]
  left_inv v := by
    ext i
    fin_cases i <;> rfl
  right_inv Y := Subtype.ext (uMat_eq Y)

theorem UpperTheory.V.Ws.Bl.uMFacts :
    ∀ (R : Type) [CommRing R], Module.Finite R (uM R) ∧ Module.Free R (uM R) ∧ ∀ (I : Ideal R) (Y : uM R), Y ∈ (I • ⊤ : Submodule R (uM R)) ↔ ∀ i j, Y.1 i j ∈ I := by
  intro R _
  refine ⟨Module.Finite.equiv (uEq R), Module.Free.of_equiv (uEq R), ?_⟩
  intro I Y
  constructor
  · intro hY i j
    refine Submodule.smul_induction_on hY ?_ ?_
    · intro r hr n _
      simpa using I.mul_mem_right (n.1 i j) hr
    · intro x y hx hy
      simpa using I.add_mem hx hy
  · intro h
    have hv : (uEq R).symm Y = ∑ k : Fin 3, ((uEq R).symm Y k) • Pi.single k 1 := by
      simpa using ((Pi.basisFun R (Fin 3)).sum_repr ((uEq R).symm Y)).symm
    have hY : Y = ∑ k : Fin 3, ((uEq R).symm Y k) • (uEq R) (Pi.single k 1) := by
      calc Y = uEq R ((uEq R).symm Y) := ((uEq R).apply_symm_apply Y).symm
        _ = _ := by
          conv_lhs => rw [hv]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum]
          simp only [map_smul]
    rw [hY]
    refine Submodule.sum_mem _ (fun k _ => Submodule.smul_mem_smul ?_ Submodule.mem_top)
    fin_cases k
    · exact h 1 0
    · exact h 1 2
    · exact h 3 0
end

