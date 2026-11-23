module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.HomExt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.homExt :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (U : Subgroup (G F Ω)) (M : Type) [AddCommGroup M] (φ : cycU l U → M), IsClosed (U : Set (G F Ω)) → IsLocallyConstant φ → (∀ a b, φ (a * b) = φ a + φ b) →
    ∃ (n : ℕ) (ψ : levU l U n → M), IsLocallyConstant ψ ∧ (∀ a b, ψ (a * b) = ψ a + ψ b) ∧ ∀ u : cycU l U, ψ ⟨u.1, cycU_le_levU l U n u.2⟩ = φ u := by
  intro F Ω _ _ _ _ _ l _ U M _ φ hU hφ hmul
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI hroots : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hlp : l.Prime := Fact.out
  have hφ1 : φ 1 = 0 := by
    have h := hmul 1 1
    simpa using h
  have hprinc : ∀ (x : ℤ_[l]ˣ) (n : ℕ), x ∈ KStar.TotallyRealRoots.princ l n ↔ PadicInt.toZModPow n (x : ℤ_[l]) = 1 := by
    intro x n
    simp only [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
      Units.val_one, MonoidHom.coe_coe]
    exact Iff.rfl
  have hopen_n : ∀ n, IsOpen ((Subgroup.comap (cycZ F Ω l) (KStar.TotallyRealRoots.princ l n) : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro n
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
    haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hlp.ne_zero⟩
    apply Subgroup.isOpen_of_mem_nhds _ (g := 1)
    rw [krullTopology_mem_nhds_one_iff]
    refine ⟨IntermediateField.adjoin F {ζ}, IntermediateField.adjoin.finiteDimensional
      ((hζ.isIntegral (Nat.pos_of_neZero _)).tower_top), ?_⟩
    intro σ hσ
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [hprinc]
    rcases Nat.eq_zero_or_pos n with h0 | hn0
    · subst h0
      haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero l)
      exact Subsingleton.elim _ _
    show (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω σ)).val.toZModPow n = 1
    rw [cyclotomicCharacter.toZModPow, eq_comm]
    apply modularCyclotomicCharacter.unique
    intro t ht
    obtain ⟨i, hi, rfl⟩ := (hζ.isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
    rw [ZMod.val_one'', pow_one]
    · exact hσ ⟨ζ ^ i, pow_mem (IntermediateField.mem_adjoin_simple_self F ζ) _⟩
    · exact (one_lt_pow₀ hlp.one_lt hn0.ne').ne'
  have hprinc_anti : ∀ (x : ℤ_[l]ˣ) (n m : ℕ), n ≤ m → x ∈ KStar.TotallyRealRoots.princ l m → x ∈ KStar.TotallyRealRoots.princ l n := by
    intro x n m hnm hx
    rw [hprinc] at hx ⊢
    rw [← PadicInt.cast_toZModPow n m hnm, hx]
    exact ZMod.cast_one (pow_dvd_pow l hnm)
  have hlev_anti : ∀ n m : ℕ, n ≤ m → (levU l U m : Set (G F Ω)) ⊆ levU l U n := by
    intro n m hnm x hx
    simp only [levU, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_comap] at hx ⊢
    exact ⟨hx.1, hprinc_anti _ n m hnm hx.2⟩
  have hclosed : ∀ n, IsClosed ((levU l U n : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro n
    simp only [levU, Subgroup.coe_inf]
    exact hU.inter (Subgroup.isClosed_of_isOpen _ (hopen_n n))
  obtain ⟨O, hOo, hOeq⟩ := isOpen_induced_iff.mp (hφ.isOpen_fiber (φ 1))
  have h1O : (1 : G F Ω) ∈ O := by
    have h : (1 : cycU l U) ∈ Subtype.val ⁻¹' O := by rw [hOeq]; rfl
    simpa using h
  obtain ⟨E, hEfin, hEnorm, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω O).mp (hOo.mem_nhds h1O)
  haveI := hEfin
  haveI := hEnorm
  have hNnorm : (E.fixingSubgroup : Subgroup (G F Ω)).Normal := by
    rw [← IntermediateField.restrictNormalHom_ker]
    exact MonoidHom.normal_ker _
  have hNopen : IsOpen ((E.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := E.fixingSubgroup_isOpen
  have hNker : ∀ c : cycU l U, (c : G F Ω) ∈ E.fixingSubgroup → φ c = 0 := by
    intro c hc
    have h : c ∈ Subtype.val ⁻¹' O := hEsub hc
    rw [hOeq] at h
    rw [← hφ1]
    exact h
  have hwd : ∀ (c c' : cycU l U) (w w' : G F Ω), w ∈ E.fixingSubgroup → w' ∈ E.fixingSubgroup →
      (c : G F Ω) * w = c' * w' → φ c = φ c' := by
    intro c c' w w' hw hw' h
    have hmem : ((c'⁻¹ * c : cycU l U) : G F Ω) ∈ E.fixingSubgroup := by
      have e : ((c'⁻¹ * c : cycU l U) : G F Ω) = w' * w⁻¹ := by
        simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
        rw [eq_mul_inv_iff_mul_eq, mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [e]
      exact Subgroup.mul_mem _ hw' (Subgroup.inv_mem _ hw)
    have h0 := hNker _ hmem
    rw [hmul] at h0
    have hinv : φ c'⁻¹ + φ c' = 0 := by rw [← hmul]; simp [hφ1]
    have e1 : φ c'⁻¹ = -φ c' := eq_neg_of_add_eq_zero_left hinv
    rw [e1] at h0
    exact (neg_add_eq_zero.mp h0).symm
  have hinter : ∀ x ∈ ⋂ n, (levU l U n : Set (G F Ω)), x ∈ cycU l U := by
    intro x hx
    simp only [Set.mem_iInter, levU, SetLike.mem_coe, Subgroup.mem_inf, Subgroup.mem_comap] at hx
    simp only [cycU, Subgroup.mem_inf, MonoidHom.mem_ker]
    refine ⟨(hx 0).1, ?_⟩
    apply Units.ext
    apply (PadicInt.ext_of_toZModPow).mp
    intro n
    rw [(hprinc _ n).mp (hx n).2, Units.val_one, map_one]
  obtain ⟨n, hn⟩ := exists_subset_nhds_of_compactSpace (X := G F Ω) (ι := ℕ)
    (V := fun n => (levU l U n : Set (G F Ω)))
    (fun i j => ⟨max i j, hlev_anti _ _ (le_max_left _ _), hlev_anti _ _ (le_max_right _ _)⟩)
    hclosed
    (U := {a | ∃ c ∈ cycU l U, ∃ w ∈ E.fixingSubgroup, a = c * w})
    (by
      apply mem_nhdsSet_iff_forall.mpr
      intro x hx
      have hxc := hinter x hx
      refine Filter.mem_of_superset
        (IsOpen.mem_nhds (hNopen.preimage (continuous_const_mul x⁻¹)) (by simpa using Subgroup.one_mem _))
        (fun a ha => ⟨x, hxc, x⁻¹ * a, ha, by group⟩))
  have hex : ∀ y : levU l U n, ∃ c : cycU l U, ∃ w ∈ E.fixingSubgroup, (y : G F Ω) = c * w := by
    intro y
    obtain ⟨c, hc, w, hw, e⟩ := hn y.2
    exact ⟨⟨c, hc⟩, w, hw, e⟩
  choose cf wf hwf hcw using hex
  refine ⟨n, fun y => φ (cf y), ?_, ?_, ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro y
    refine ⟨{z : levU l U n | (y : G F Ω)⁻¹ * z ∈ E.fixingSubgroup},
      hNopen.preimage (continuous_const.mul continuous_subtype_val), by simpa using Subgroup.one_mem _, ?_⟩
    intro z hz
    exact hwd (cf z) (cf y) (wf z) (wf y * ((y : G F Ω)⁻¹ * z)) (hwf z)
      (Subgroup.mul_mem _ (hwf y) hz)
      (by rw [← hcw z, ← mul_assoc, ← hcw y]; group)
  · intro a b
    rw [← hmul]
    have hv : ((cf b : G F Ω)⁻¹ * wf a * cf b) * wf b ∈ E.fixingSubgroup := by
      refine Subgroup.mul_mem _ ?_ (hwf b)
      have := hNnorm.conj_mem _ (hwf a) ((cf b : G F Ω)⁻¹)
      simpa using this
    refine hwd (cf (a * b)) (cf a * cf b) (wf (a * b)) _ (hwf _) hv ?_
    rw [← hcw (a * b), Subgroup.coe_mul, hcw a, hcw b, Subgroup.coe_mul]
    group
  · intro u
    exact hwd _ u (wf _) 1 (hwf _) (Subgroup.one_mem _) (by rw [← hcw, mul_one])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClMap
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem intValuation_mapRingEquiv {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    (τ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v).intValuation
      (RingOfIntegers.mapRingEquiv τ x) = v.intValuation x := by
  set ρ := RingOfIntegers.mapRingEquiv τ
  have hw : (HeightOneSpectrum.equivOfRingEquiv ρ v).asIdeal = Ideal.map ρ v.asIdeal := by
    ext y
    rw [Ideal.mem_map_of_equiv]
    show ρ.symm y ∈ v.asIdeal ↔ _
    constructor
    · intro h
      exact ⟨_, h, ρ.apply_symm_apply y⟩
    · rintro ⟨z, hz, rfl⟩
      rwa [ρ.symm_apply_apply]
  by_cases hx : x = 0
  · subst hx
    simp
  have hx' : ρ x ≠ 0 := (map_ne_zero_iff ρ ρ.injective).mpr hx
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ hx']
  have hm : multiplicity (HeightOneSpectrum.equivOfRingEquiv ρ v).asIdeal (Ideal.span {ρ x}) =
      multiplicity v.asIdeal (Ideal.span {x}) := by
    apply multiplicity_eq_of_emultiplicity_eq
    rw [emultiplicity_eq_emultiplicity_iff]
    intro k
    have hs : Ideal.span {ρ x} = Ideal.map ρ (Ideal.span {x}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [Ideal.dvd_iff_le, Ideal.dvd_iff_le, hw, hs, ← Ideal.map_pow]
    constructor
    · intro h
      have h2 := Ideal.comap_mono (f := ρ) h
      rwa [Ideal.comap_map_of_bijective _ ρ.bijective, Ideal.comap_map_of_bijective _ ρ.bijective] at h2
    · exact Ideal.map_mono
  rw [hm]

private theorem ordv_units_map_ringEquiv {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']
    (τ : K ≃+* K') (v : HeightOneSpectrum (𝓞 K)) (a : Kˣ) :
    ordv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v)
      (Units.map τ.toMonoidHom a) = ordv v a := by
  have hτ : ∀ z : 𝓞 K, τ (algebraMap (𝓞 K) K z) =
      algebraMap (𝓞 K') K' (RingOfIntegers.mapRingEquiv τ z) := fun z =>
    (RingOfIntegers.mapRingEquiv_apply τ z).symm
  have hval : (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ) v).valuationOfNeZero
      (Units.map τ.toMonoidHom a) = v.valuationOfNeZero a := by
    rw [← WithZero.coe_inj, HeightOneSpectrum.valuationOfNeZero_eq,
      HeightOneSpectrum.valuationOfNeZero_eq]
    obtain ⟨x, y, -, hxy⟩ := IsFractionRing.div_surjective (𝓞 K) (a : K)
    show HeightOneSpectrum.valuation K' _ (τ (a : K)) = HeightOneSpectrum.valuation K v (a : K)
    rw [← hxy, map_div₀, map_div₀, map_div₀, hτ, hτ, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, intValuation_mapRingEquiv, intValuation_mapRingEquiv]
  unfold ordv
  rw [hval]

theorem UpperTheory.V.Kum.radClMap :
    ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (τ : K ≃+* K') (n : ℕ) (a : Kˣ), clMap τ (radCl n a) = radCl n (Units.map τ.toMonoidHom a) := by
  intro K K' _ _ _ _ τ n a
  have hinv : ∀ w : 𝓞 K, RingOfIntegers.mapRingEquiv τ.symm (RingOfIntegers.mapRingEquiv τ w) = w :=
    fun w => RingOfIntegers.ext (by simp [RingOfIntegers.mapRingEquiv_apply])
  have hback : ∀ I, clMap τ.symm (clMap τ (ClassGroup.mk0 I)) = ClassGroup.mk0 I := by
    intro I
    rw [class_map_mk0, class_map_mk0]
    congr 1
    apply Subtype.ext
    show Ideal.map (RingOfIntegers.mapRingEquiv τ.symm)
      (Ideal.map (RingOfIntegers.mapRingEquiv τ) (I : Ideal (𝓞 K))) = I
    ext y
    rw [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Ideal.mem_map_of_equiv] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rwa [hinv]
    · intro hy
      exact ⟨RingOfIntegers.mapRingEquiv τ y, (Ideal.mem_map_of_equiv _ _).mpr ⟨y, hy, rfl⟩, hinv y⟩
  have hinj : Function.Injective (clMap τ) := by
    intro x y hxy
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective x
    obtain ⟨J, rfl⟩ := ClassGroup.mk0_surjective y
    rw [← hback I, ← hback J, hxy]
  unfold radCl
  rw [MonoidHom.map_finprod_of_injective _ hinj,
    ← finprod_comp_equiv (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv τ))]
  refine finprod_congr (fun v => ?_)
  rw [map_zpow, ordv_units_map_ringEquiv]
  congr 1
  show clMap τ (ClassGroup.mk0 _) = ClassGroup.mk0 _
  rw [class_map_mk0]
  congr 1
  apply Subtype.ext
  show Ideal.map (RingOfIntegers.mapRingEquiv τ) v.asIdeal = _
  ext y
  rw [Ideal.mem_map_of_equiv]
  show _ ↔ (RingOfIntegers.mapRingEquiv τ).symm y ∈ v.asIdeal
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [RingEquiv.symm_apply_apply]
  · intro h
    exact ⟨_, h, RingEquiv.apply_symm_apply _ y⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClSurj
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

private theorem exists_frac_of_mem {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (c : ClassGroup (𝓞 K)) (hc : c ∈ clSub S) :
    ∃ J : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K J = c ∧
      ∀ v ∉ S, FractionalIdeal.count K v J.1 = 0 := by
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    refine ⟨FractionalIdeal.mk0 K ⟨w.asIdeal, mem_nonZeroDivisors_of_ne_zero w.ne_bot⟩,
      ClassGroup.mk_mk0 _ _, fun v hv => ?_⟩
    rw [FractionalIdeal.coe_mk0]
    exact FractionalIdeal.count_maximal_coprime K v (fun h : w = v => hv (h ▸ hw))
  | one => exact ⟨1, map_one _, fun v _ => FractionalIdeal.count_one K v⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, rfl, hI⟩ := hx
    obtain ⟨J, rfl, hJ⟩ := hy
    refine ⟨I * J, map_mul _ _ _, fun v hv => ?_⟩
    rw [Units.val_mul, FractionalIdeal.count_mul K v I.ne_zero J.ne_zero, hI v hv, hJ v hv, add_zero]
  | inv x _ hx =>
    obtain ⟨I, rfl, hI⟩ := hx
    refine ⟨I⁻¹, map_inv _ _, fun v hv => ?_⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI v hv, neg_zero]

private theorem mk_finprod_congr {K : Type} [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K)))
    (f g : HeightOneSpectrum (𝓞 K) → ℤ) (hf : {v | f v ≠ 0}.Finite) (hg : {v | g v ≠ 0}.Finite)
    (h : ∀ v ∉ S, f v = g v) :
    (QuotientGroup.mk (∏ᶠ v, primeCl v ^ f v) : ClS S) = QuotientGroup.mk (∏ᶠ v, primeCl v ^ g v) := by
  have hfm : ∀ f : HeightOneSpectrum (𝓞 K) → ℤ, {v | f v ≠ 0}.Finite →
      Function.HasFiniteMulSupport (fun v => primeCl v ^ f v) := by
    intro f hf
    unfold Function.HasFiniteMulSupport
    apply hf.subset
    intro v hv
    simp only [Set.mem_setOf_eq]
    intro h0
    exact hv (by simp [h0])
  have e1 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm f hf)
  have e2 := (QuotientGroup.mk' (clSub S)).map_finprod (hfm g hg)
  simp only [QuotientGroup.mk'_apply] at e1 e2
  rw [e1, e2]
  apply finprod_congr
  intro v
  by_cases hv : v ∈ S
  · have h1 : (QuotientGroup.mk (primeCl v) : ClS S) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (Subgroup.subset_closure ⟨v, hv, rfl⟩)
    simp [QuotientGroup.mk_zpow, h1]
  · rw [h v hv]

theorem UpperTheory.V.Kum.radClSurj :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → ∀ c : ClS S, c ^ n = 1 → ∃ a ∈ SelK S n, QuotientGroup.mk (radCl n a) = c := by
  intro K _ _ S n hn c hc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨I, rfl⟩ : ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ, ClassGroup.mk K I = x :=
    ClassGroup.induction K (fun I => ⟨I, rfl⟩) x
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hc
  obtain ⟨J, hJ, hJS⟩ := exists_frac_of_mem S _ hc
  have hP : ClassGroup.mk K (I ^ n * J⁻¹) = 1 := by
    rw [map_mul, map_pow, map_inv, hJ, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at hP
  obtain ⟨y, hy⟩ := @Submodule.IsPrincipal.principal _ _ _ _ _ _ hP
  have hx' : ((I ^ n * J⁻¹ : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = FractionalIdeal.spanSingleton _ y :=
    FractionalIdeal.coeToSubmodule_injective (hy.trans (FractionalIdeal.coe_spanSingleton _ y).symm)
  have hy0 : y ≠ 0 := by
    intro h0
    apply Units.ne_zero (I ^ n * J⁻¹)
    rw [hx', h0, FractionalIdeal.spanSingleton_zero]
  let a : Kˣ := Units.mk0 y hy0
  have hcount : ∀ v ∉ S, ordv v a = n * FractionalIdeal.count K v (I : FractionalIdeal _ K) := by
    intro v hv
    rw [← (clProd K).2.1 v a]
    show FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) = _
    rw [← hx', Units.val_mul, FractionalIdeal.count_mul K v (Units.ne_zero _) (Units.ne_zero _),
      Units.val_pow_eq_pow_val, FractionalIdeal.count_pow, Units.val_inv_eq_inv_val,
      FractionalIdeal.count_inv, hJS v hv, neg_zero, add_zero]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn
  refine ⟨a, fun v hv => ⟨FractionalIdeal.count K v (I : FractionalIdeal _ K), hcount v hv⟩, ?_⟩
  rw [(clProd K).1 I]
  unfold radCl
  apply mk_finprod_congr S
  · apply ((clProd K).2.2.1 a).subset
    intro v hv h0
    apply hv
    simp [h0]
  · have hf := FractionalIdeal.finite_factors (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    rw [Filter.eventually_cofinite] at hf
    exact hf
  · intro v hv
    rw [hcount v hv, Int.mul_ediv_cancel_left _ hn']
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadExists
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

theorem UpperTheory.V.Kum.radExists :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (n : ℕ) [NeZero n] (ζ : Ω) (η z : G K Ω → ZMod n), IsPrimitiveRoot ζ n → (∀ g : G K Ω, g ζ = ζ ^ (η g).val) → IsLocallyConstant z → (∀ g h, z (g * h) = z g + η g * z h) →
    ∃ (β : Ω) (a : Kˣ), β ^ n = algebraMap K Ω a ∧ ∀ g : G K Ω, g β = ζ ^ (z g).val * β := by
  intro K Ω _ _ _ _ _ n _ ζ η z hζ hη hz hc
  have hmod : ∀ m : ℕ, ζ ^ (m % n) = ζ ^ m := fun m => (pow_eq_pow_mod m hζ.pow_eq_one).symm
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (NeZero.ne n)
  obtain ⟨β, hβ0, hβ⟩ := UpperTheory.V.Kum.h90 K Ω (fun g => ζ ^ (z g).val)
    (hz.comp fun x : ZMod n => ζ ^ x.val) (fun g => pow_ne_zero _ hζ0) (fun g h => by
      show ζ ^ (z (g * h)).val = ζ ^ (z g).val * g (ζ ^ (z h).val)
      rw [hc, ZMod.val_add, hmod, pow_add, ZMod.val_mul, hmod, map_pow, hη, ← pow_mul])
  haveI : IsGalois K Ω := {}
  have hfix : ∀ g : Ω ≃ₐ[K] Ω, g (β ^ n) = β ^ n := fun g => by
    rw [map_pow, hβ g, mul_pow, ← pow_mul, mul_comm _ n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (β ^ n)).2 hfix
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact pow_ne_zero n hβ0 ha.symm
  exact ⟨β, Units.mk0 a ha0, ha.symm, hβ⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ResInfMem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open Pointwise

private theorem UpperTheory.V.Kum.coc_conj_triv {R Γ M : Type} [CommRing R] [Group Γ] [AddCommGroup M] [Module R M]
    (ρ : Representation R Γ M) (f : Γ → M) (hf : ∀ g h, f (g * h) = f g + ρ g (f h)) (g h k : Γ)
    (e : k * g = g * h) (hk : ∀ m, ρ k m = m) : f k = ρ g (f h) := by
  have h1 := hf k g
  rw [e, hf, hk, add_comm] at h1
  exact (add_right_cancel h1).symm

theorem UpperTheory.V.Kum.resInfMem :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (D : LData F Ω l) (e : ℤ), (Sha D e).map (resInf D e) ≤ EqHom l (Uinf F Ω l) (qzG F Ω l e) := by
  intro F Ω _ _ _ _ _ l _ D e
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨p1, p2, p3, p4⟩ := placeDict F Ω
  have hchi : ∀ g : G F Ω, D.chi (toGS Ω _ g) = cycZ F Ω l g := fun g => DFunLike.congr_fun D.hchi g
  have htriv : ∀ g : G F Ω, cycZ F Ω l g = 1 → ∀ m, qzTw D e (toGS Ω _ g) m = m := fun g hg m => by
    rw [qzTw_apply, hchi, hg, one_zpow, Units.val_one, one_smul]
  have hz : ∀ a b, z.1 (a * b) = z.1 a + qzTw D e a (z.1 b) := z.2.2
  have hconj : ∀ g h k : G F Ω, k * g = g * h → cycZ F Ω l k = 1 →
      z.1 (toGS Ω _ k) = qzTw D e (toGS Ω _ g) (z.1 (toGS Ω _ h)) := fun g h k e1 hk =>
    coc_conj_triv _ _ hz _ _ _ (by rw [← map_mul, ← map_mul, e1]) (htriv k hk)
  have h1 : z.1 1 = 0 := by
    have := hz 1 1
    rw [one_mul, map_one] at this
    exact left_eq_add.1 this
  have hdec : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ u : Uinf F Ω l, u.1 ∈ Dec (F := F) A →
      z.1 (toGS Ω _ u.1) = 0 := by
    intro A hA u hu
    obtain ⟨v, hv⟩ := p2 A (p3 A l (Fact.out : l.Prime).ne_zero hA)
    have hvS : v ∈ D.S := by
      have := (p4 A v l hv).1 hA
      rw [← D.hS] at this
      exact this
    obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) (D.hA ⟨v, hvS⟩) hv
    obtain ⟨m, hm⟩ := (res_mk_eq_zero_iff D e ⟨v, hvS⟩ z).1 ((mem_Sha_iff D e _).1 hx ⟨v, hvS⟩)
    have hc : g⁻¹ * u.1 * g ∈ Dec (F := F) (D.A ⟨v, hvS⟩) := by
      have h : u.1 • g • D.A ⟨v, hvS⟩ = g • D.A ⟨v, hvS⟩ := hu
      show (g⁻¹ * u.1 * g) • D.A ⟨v, hvS⟩ = D.A ⟨v, hvS⟩
      rw [mul_smul, mul_smul, h, inv_smul_smul]
    have hu1 : cycZ F Ω l u.1 = 1 := u.2.2
    have h2 := hm ⟨_, hc⟩
    rw [htriv _ (by simp [hu1]), sub_self] at h2
    rw [hconj g (g⁻¹ * u.1 * g) u.1 (by group) hu1, h2, map_zero]
  refine ⟨⟨?_, fun a b => ?_, fun A u hu => ?_, hdec⟩, (Submodule.mem_iInf _).2 fun g u u' h => ?_⟩
  · exact (IsLocallyConstant.iff_continuous _).2
      (z.2.1.comp ((continuous_toGS Ω _).comp continuous_subtype_val))
  · rw [resInf_mk, resInf_mk, resInf_mk, Subgroup.coe_mul, map_mul, hz, htriv _ a.2.2]
  · rw [resInf_mk]
    by_cases hA : A = ⊤
    · subst hA
      rw [p1, Subgroup.mem_bot] at hu
      rw [hu, map_one, h1]
    obtain ⟨v, hv⟩ := p2 A hA
    by_cases hl : A.valuation (l : Ω) < 1
    · exact hdec A hl u (Ine_le_Dec A hu)
    have hvS : v ∉ (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      rw [D.hS]
      exact fun h => hl ((p4 A v l hv).2 h)
    have hn : u.1 ∈ NS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) := by
      apply Subgroup.le_topologicalClosure
      apply Subgroup.subset_normalClosure
      simp only [Set.mem_iUnion]
      exact ⟨v, hvS, A, hv, hu⟩
    have : toGS Ω (D.S : Set (HeightOneSpectrum (𝓞 F))) u.1 = 1 := (QuotientGroup.eq_one_iff _).2 hn
    rw [this, h1]
  · rw [resInf_mk, resInf_mk, hconj g u.1 u'.1 (AlgEquiv.ext h) u'.2.2, qzTw_apply, hchi]
    rfl
end

