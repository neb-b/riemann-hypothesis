module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0007
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem sop_mod (S : Type) [CommRing S] [IsLocalRing S] [IsNoetherianRing S] (J : Ideal S)
    (hle : J ≤ maximalIdeal S) :
    ∃ (n : ℕ) (x : Fin n → S), (∀ i, x i ∈ maximalIdeal S) ∧ ringKrullDim (S ⧸ J) = n ∧
      maximalIdeal S ≤ (Ideal.span (Set.range x) ⊔ J).radical := by
  have hne : J ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ hle))
  haveI : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI : IsLocalRing (S ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set π := Ideal.Quotient.mk J with hπ
  have hsurj : Function.Surjective π := Ideal.Quotient.mk_surjective
  haveI : IsLocalHom π := IsLocalHom.of_surjective π hsurj
  obtain ⟨s, hs, hcard⟩ :=
    Ideal.exists_finset_card_eq_height_of_isNoetherianRing (maximalIdeal (S ⧸ J))
  choose g hg using hsurj
  have hrad : maximalIdeal (S ⧸ J) ≤ (Ideal.span (s : Set (S ⧸ J))).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro J ⟨hJ, hJ'⟩
    exact hs.2 ⟨hJ', hJ⟩ (le_maximalIdeal hJ'.ne_top)
  refine ⟨s.card, fun i => g (s.equivFin.symm i), fun i => ?_, ?_, ?_⟩
  · have h1 : π (g (s.equivFin.symm i)) ∈ maximalIdeal (S ⧸ J) := by
      rw [hg]
      exact hs.1.2 (Ideal.subset_span (s.equivFin.symm i).2)
    rw [mem_maximalIdeal, mem_nonunits_iff] at h1 ⊢
    exact fun h => h1 (h.map π)
  · rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hcard]
    rfl
  · intro y hy
    obtain ⟨N, hN⟩ := hrad (map_nonunit π y hy)
    have h2 : Ideal.span (s : Set (S ⧸ J)) ≤
        (Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π := by
      rw [Ideal.span_le]
      intro y hy
      rw [← hg y]
      refine Ideal.mem_map_of_mem π (Ideal.subset_span ⟨s.equivFin ⟨y, hy⟩, ?_⟩)
      simp
    refine ⟨N, ?_⟩
    have h3 : y ^ N ∈ ((Ideal.span (Set.range fun i => g (s.equivFin.symm i))).map π).comap π := by
      rw [Ideal.mem_comap, map_pow]
      exact h2 hN
    rwa [Ideal.comap_map_of_surjective π Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, hπ, Ideal.mk_ker] at h3

private theorem inj_of_finite {A B : Type} [CommRing A] [Nontrivial A] [NoZeroDivisors A] [CommRing B] (φ : A →+* B)
    (h : φ.Finite) (d : ℕ) (hA : ringKrullDim A = d) (hB : ringKrullDim B = d) :
    Function.Injective φ := by
  haveI : IsDomain A := NoZeroDivisors.to_isDomain A
  letI := φ.toAlgebra
  haveI : Module.Finite A B := h
  exact inj_dim A B d hA hB

private theorem nn_field (k : Type) [Field k] (R : Type) [CommRing R] [Algebra k R] [IsLocalRing R]
    (h : IsCL k R) : ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) k →ₐ[k] R),
      Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d := by
  haveI := h.noeth
  obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R ⊥ bot_le
  haveI : IsAdicComplete (maximalIdeal k) k := by
    rw [maximalIdeal_eq_bot]; infer_instance
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps k R h (Fin d) x hx
    (hrad.trans (Ideal.radical_mono (sup_le_sup_left bot_le _)))
  have hR : ringKrullDim R = d := by
    rw [← hd]; exact (ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)).symm
  exact ⟨d, φ, inj_of_finite φ.toRingHom hfin d (cl_cm.2 k d).2 hR, hfin, hloc, hR⟩

private theorem isCL_field (O k R : Type) [CommRing O] [Field k] [CommRing R] [IsLocalRing R]
    [Algebra O k] [Algebra O R] [Algebra k R] [IsScalarTower O k R] (h : IsCL O R) : IsCL k R := by
  have := h.res_fin
  exact ⟨h.noeth, h.complete, inferInstance,
    Module.Finite.of_restrictScalars_finite O k (ResidueField R)⟩

theorem UpperTheory.V.CA.cl_nn :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R] [IsDomain R], IsCL O R → (Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) O →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = (d + 1 : ℕ)) ∧ (¬ Function.Injective (algebraMap O R) → ∃ (d : ℕ) (φ : MvPowerSeries (Fin d) (ResidueField O) →ₐ[O] R), Function.Injective φ ∧ φ.toRingHom.Finite ∧ IsLocalHom φ ∧ ringKrullDim R = d) := by
  intro O _ _ _ _ R _ _ _ _ h
  haveI := h.noeth
  haveI := h.isLocalHom
  refine ⟨fun hinj => ?_, fun hninj => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hm : maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    have ha : algebraMap O R ϖ ∈ maximalIdeal R := map_nonunit _ _ hϖ.not_isUnit
    have ha0 : algebraMap O R ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    obtain ⟨d, x, hx, hd, hrad⟩ := sop_mod R (Ideal.span {algebraMap O R ϖ})
      ((Ideal.span_singleton_le_iff_mem _).2 ha)
    obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R h (Fin d) x hx
      (by rwa [hm, Ideal.map_span, Set.image_singleton])
    have hR : ringKrullDim R = (d + 1 : ℕ) := by
      rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors
        (mem_nonZeroDivisors_of_ne_zero ha0) ha, hd]
      rfl
    exact ⟨d, φ, inj_of_finite φ.toRingHom hfin (d + 1) (cl_cm.1 O d).2 hR, hfin, hloc, hR⟩
  · have hk0 : RingHom.ker (algebraMap O R) ≠ ⊥ := fun e =>
      hninj ((RingHom.injective_iff_ker_eq_bot _).2 e)
    have hk : RingHom.ker (algebraMap O R) = maximalIdeal O :=
      eq_maximalIdeal (Ideal.IsPrime.isMaximal (RingHom.ker_isPrime _) hk0)
    let ψ : ResidueField O →+* R := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O R)
      (fun a ha => by rwa [← hk] at ha)
    letI : Algebra (ResidueField O) R := ψ.toAlgebra
    haveI : IsScalarTower O (ResidueField O) R := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have h' : IsCL (ResidueField O) R := isCL_field O (ResidueField O) R h
    obtain ⟨d, φ, h1, h2, h3, h4⟩ := nn_field (ResidueField O) R h'
    exact ⟨d, φ.restrictScalars O, h1, h2, ⟨fun a ha => h3.1 a ha⟩, h4⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.KStableHighestWeightVector
section
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

private theorem dim_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have hl : (maximalIdeal B).LiesOver (maximalIdeal A) :=
    ⟨Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance))
      (by rw [← hm]; exact Ideal.le_comap_map)⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [hm, Ideal.map_quotient_self] at h
  simp at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim, h]

private theorem dim_quot_eq_of_flat {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    (hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) (J : Ideal A) :
    ringKrullDim (B ⧸ J.map (algebraMap A B)) = ringKrullDim (A ⧸ J) := by
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Ideal.map_top]
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  have hJm : J ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hJ
  have hIm : J.map (algebraMap A B) ≤ maximalIdeal B := hm ▸ Ideal.map_mono hJm
  have hI : J.map (algebraMap A B) ≠ ⊤ :=
    ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance) hIm
  haveI : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  haveI : Nontrivial (B ⧸ J.map (algebraMap A B)) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI : IsLocalRing (A ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ J.map (algebraMap A B)) :=
    .of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : Module.Flat (A ⧸ J) (B ⧸ J.map (algebraMap A B)) := by
    have e : (B ⧸ J.map (algebraMap A B)) ≃ₗ[A] TensorProduct A (A ⧸ J) B :=
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B J).toLinearEquiv.restrictScalars A).trans
        (TensorProduct.comm A B (A ⧸ J))
    haveI := Module.Flat.baseChange A (A ⧸ J) B
    exact Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective e)
  apply dim_eq_of_flat
  have hmA : maximalIdeal (A ⧸ J) = (maximalIdeal A).map (Ideal.Quotient.mk J) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hJm))).symm
  have hmB : maximalIdeal (B ⧸ J.map (algebraMap A B)) =
      (maximalIdeal B).map (Ideal.Quotient.mk (J.map (algebraMap A B))) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIm))).symm
  rw [hmA, hmB, Ideal.map_map, ← hm, Ideal.map_map]
  congr 1

theorem UpperTheory.V.CA.c3c :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → (∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I) ∧ ∀ (I : Ideal C) (q : Ideal R), I ≤ q.comap (algebraMap C R) → ringKrullDim (R ⧸ q) ≤ dimAt x I := by
  intro C R _ _ _ _ _ x _ hR
  obtain ⟨_, ⟨e⟩, hmap⟩ := cpl_uniq x hR
  haveI := hR.noeth
  haveI : IsNoetherianRing (Cpl x) := isNoetherianRing_of_ringEquiv R e.toRingEquiv
  have hmapI : ∀ I : Ideal C,
      I.map (algebraMap C (Cpl x)) = (I.map (algebraMap C R)).map (e.toRingEquiv : R →+* Cpl x) := by
    intro I
    rw [Ideal.map_map]
    congr 1
    ext c
    simp
  have h1 : x.map (algebraMap C (Cpl x)) =
      (maximalIdeal (Localization.AtPrime x)).map (algebraMap (Localization.AtPrime x) (Cpl x)) := by
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime x) (Cpl x), ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal]
  have hm : (maximalIdeal (Localization.AtPrime x)).map
      (algebraMap (Localization.AtPrime x) (Cpl x)) = maximalIdeal (Cpl x) := by
    rw [← h1, hmapI, hmap]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.toRingEquiv)
  have key : ∀ I : Ideal C, ringKrullDim (R ⧸ I.map (algebraMap C R)) = dimAt x I := by
    intro I
    unfold dimAt
    rw [← dim_quot_eq_of_flat hm (I.map (algebraMap C (Localization.AtPrime x))), Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
    exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ e.toRingEquiv (hmapI I))
  refine ⟨key, fun I q hq => ?_⟩
  rw [← key I]
  have hle : I.map (algebraMap C R) ≤ q := Ideal.map_le_iff_le_comap.mpr hq
  exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UniversalDeformationRingLocalCharacters
section
open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private def toMat {G R : Type} [Group G] [CommRing R] (ψ : G →* Rˣ) : G →* Matrix Unit Unit R where
  toFun g := Matrix.of fun _ _ => (ψ g : R)
  map_one' := by ext a b; simp
  map_mul' g h := by ext a b; simp [Matrix.mul_apply]

private noncomputable def ofMat {G R : Type} [Group G] [CommRing R] (ρ : G →* Matrix Unit Unit R) : G →* Rˣ :=
  MonoidHom.toHomUnits
    { toFun := fun g => ρ g () ()
      map_one' := by simp
      map_mul' := fun g h => by simp [Matrix.mul_apply] }

private theorem lc_of_open {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker f h

private theorem eq_one_of_pow {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l] (x : k) (m : ℕ)
    (h : x ^ l ^ m = 1) : x = 1 := by
  have h2 : (x - 1) ^ l ^ m = 0 := by rw [sub_pow_char_pow, h]; simp
  exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero m (Fact.out : l.Prime).ne_zero) |>.1 h2)

private theorem psib_th {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v) :
    ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) = residue O (r.th v i g) := by
  obtain ⟨m, hm⟩ := (CommGroup.primaryComponent.isPGroup (G := TopologicalAbelianization (F.Gv v)) (p := l))
    ⟨QuotientGroup.mk' _ (g : F.Gv v), g.2⟩
  have h1 : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure ((g : F.Gv v) ^ l ^ m)) = 1 := by
    rw [map_pow]; exact congrArg Subtype.val hm
  have h2 : (g : F.Gv v) ^ l ^ m ∈ (commutator (F.Gv v)).topologicalClosure := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
  have h4 : r.psib v i g ^ l ^ m = 1 := by rw [← map_pow]; exact h3 h2
  have h5 : r.th v i g ^ l ^ m = 1 := by rw [← map_pow]; exact r.th_comm v i _ h2
  rw [eq_one_of_pow l ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) m
      (by rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]),
    eq_one_of_pow l (residue O (r.th v i g)) m
      (by rw [← map_pow, ← Units.val_pow_eq_pow_val, h5, Units.val_one, map_one])]

theorem UpperTheory.V.CA.universalDeformationRing_localCharacters :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] {n : ℕ} (r : Resid F O n) (v : F.Vl) (i : Fin n), PhiCond (F.Gv v) l → ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (ψ : F.Gv v →* Rˣ), r.IsPsi v i ψ ∧ ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (ψ' : F.Gv v →* R'ˣ), r.IsPsi v i ψ' → ∃! f : R →ₐ[O] R', pushCh (f : R →+* R') ψ = ψ' := by
  intro l _ F O _ _ _ _ _ _ _ n r v i hΦ
  have hlc : IsLocallyConstant (r.psib v i) := lc_of_open _ (r.psib_open v i)
  have hlc' : IsLocallyConstant (toMat (r.psib v i)) :=
    hlc.comp fun x => (Matrix.of fun _ _ => (x : ResidueField O) : Matrix Unit Unit (ResidueField O))
  obtain ⟨R₀, _, _, _, u, hu⟩ := univ_lift l O (F.Gv v) Unit (toMat (r.psib v i)) hΦ hlc'
  let P : Cond O (toMat (r.psib v i)) := fun R _ _ _ s =>
    ∀ g : F.mu v, s.hom g () () = algebraMap O R (r.th v i g)
  have hP : P.IsClosed := fun R _ _ _ s => by
    refine ⟨Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)),
      fun R' _ _ _ f => ⟨fun h x hx => ?_, fun h g => ?_⟩⟩
    · have : Ideal.span (Set.range fun g : F.mu v => s.hom g () () - algebraMap O R (r.th v i g)) ≤
          RingHom.ker f := by
        rw [Ideal.span_le]
        rintro _ ⟨g, rfl⟩
        show f _ = 0
        rw [map_sub, AlgHom.commutes, sub_eq_zero]
        exact h g
      exact this hx
    · have := h _ (Ideal.subset_span ⟨g, rfl⟩)
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
  haveI := (co_res O).1
  have hres : ∀ x : ResidueField O, res O (ResidueField O) x = x := fun x => by
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact (res O (ResidueField O)).commutes a
  let r₁ : Lift O (toMat (r.psib v i)) (ResidueField O) :=
    { hom := toMat (r.psib v i)
      cont := fun a b N => hlc.comp fun x => Ideal.Quotient.mk _ (x : ResidueField O)
      red := fun g a b => hres _ }
  obtain ⟨R, _, _, _, p, -, hR⟩ := univ_cond O (F.Gv v) Unit _ R₀ u _ P hu hP
    ⟨ResidueField O, inferInstance, inferInstance, inferInstance, r₁, trivial, fun g => psib_th r v i g⟩
  refine ⟨R, inferInstance, inferInstance, inferInstance, ofMat (u.map p).hom,
    ⟨(u.map p).cont () (), fun g => (u.map p).red g () (), ((hR R).1 (AlgHom.id O R)).2⟩, fun R' _ _ _ ψ' h' => ?_⟩
  let s : Lift O (toMat (r.psib v i)) R' :=
    { hom := toMat ψ'
      cont := fun a b => h'.cont
      red := fun g a b => h'.red g }
  obtain ⟨f, hf, huniq⟩ := (hR R').2 s ⟨trivial, h'.mu⟩
  refine ⟨f, ?_, fun f' hf' => huniq f' ?_⟩
  · ext g
    exact congrArg (fun t : Lift O (toMat (r.psib v i)) R' => t.hom g () ()) hf
  · ext g a b
    exact congrArg (fun t : F.Gv v →* R'ˣ => ((t g : R'ˣ) : R')) hf'
end

