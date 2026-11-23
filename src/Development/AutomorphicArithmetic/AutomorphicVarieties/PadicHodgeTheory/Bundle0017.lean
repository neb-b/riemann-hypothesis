module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0036
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0050
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.RingKrullDimEqHeightKerSectionAddOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem ptc_field {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    {K : Type} [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K) (a : R) (ha : a ∈ maximalIdeal R) :
    IsIntegral ℤ_[l] (x a) ∧ ∃ n : ℕ, ∃ b, IsIntegral ℤ_[l] b ∧ x a ^ n = (l : K) * b :=
  _root_.UpperTheory.Reformulated.B.IntegralOfNormBounded.ptc_field x a ha

private theorem ptc_field' {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R)
    {K : Type} [Field K] [Algebra ℚ_[l] K] [Module.Finite ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    (x : R →ₐ[ℤ_[l]] K) (a : R) : IsIntegral ℤ_[l] (x a) := by
  obtain ⟨c, hc, hm⟩ := hR a
  have := (ptc_field x _ hm).1.add (hc.map x)
  simpa using this

private theorem ptc_finite {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra ℤ_[l] R] (hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R)
    {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B]
    (x : R →ₐ[ℤ_[l]] B) : Module.Finite ℤ_[l] x.range := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite ℚ_[l] B
  haveI : IsNoetherianRing x.range := isNoetherianRing_of_surjective R _ x.rangeRestrict.toRingHom
    x.rangeRestrict_surjective
  have hfin : ∀ m : MaximalSpectrum B, Module.Finite ℤ_[l] (integralClosure ℤ_[l] (B ⧸ m.asIdeal)) := fun m => by
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact IsIntegralClosure.finite ℤ_[l] ℚ_[l] (B ⧸ m.asIdeal) _
  have hint : ∀ (m : MaximalSpectrum B) (z : x.range),
      ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp x.range.val) z ∈ integralClosure ℤ_[l] (B ⧸ m.asIdeal) := by
    rintro m ⟨_, a, rfl⟩
    haveI := m.isMaximal
    letI := Ideal.Quotient.field m.asIdeal
    exact ptc_field' hR ((Ideal.Quotient.mkₐ ℤ_[l] m.asIdeal).comp x) a
  let g : x.range →ₐ[ℤ_[l]] ∀ m : MaximalSpectrum B, integralClosure ℤ_[l] (B ⧸ m.asIdeal) :=
    Pi.algHom _ _ fun m => AlgHom.codRestrict _ _ (hint m)
  haveI : Module.Finite ℤ_[l] g.range :=
    Module.Finite.of_injective g.range.val.toLinearMap Subtype.val_injective
  refine Module.finite_of_surjective_of_ker_le_nilradical g.rangeRestrict g.rangeRestrict_surjective ?_
    (IsNoetherian.noetherian _)
  intro z hz
  have hz' : g z = 0 := congrArg Subtype.val hz
  have hj : (z : B) ∈ Ideal.jacobson (⊥ : Ideal B) := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro I ⟨-, hI⟩
    have := congrArg Subtype.val (congrFun hz' ⟨I, hI⟩)
    exact Ideal.Quotient.eq_zero_iff_mem.1 this
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
  refine ⟨n, Subtype.ext ?_⟩
  have := Ideal.pow_mem_pow hj n
  rw [hn] at this
  simpa using this

private theorem ptc_pow {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Type} [CommRing A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (y : R →+* A) (hy : Function.Surjective y) :
    ∃ N : ℕ, ∀ k : ℕ, ∀ a ∈ maximalIdeal R ^ (N * k), ∃ b : A, y a = (l : ℤ_[l]) ^ k • b := by
  have h1 : (maximalIdeal R).map y ≤ (Ideal.span {(l : A)}).radical := by
    rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro P ⟨hP, hPp⟩
    have hc : (P.comap (algebraMap ℤ_[l] A)).IsMaximal := by
      have : maximalIdeal ℤ_[l] ≤ P.comap (algebraMap ℤ_[l] A) := by
        rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
        show algebraMap ℤ_[l] A l ∈ P
        rw [map_natCast]
        exact hP (Ideal.subset_span rfl)
      rw [← (maximalIdeal.isMaximal _).eq_of_le (Ideal.IsPrime.ne_top inferInstance) this]
      infer_instance
    haveI : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) P hc
    have := eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective y hy (K := P))
    rw [Ideal.map_le_iff_le_comap, this]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h1 (Ideal.FG.map (IsNoetherian.noetherian _) y)
  refine ⟨N, fun k a ha => ?_⟩
  have h2 := Ideal.mem_map_of_mem y ha
  rw [Ideal.map_pow, pow_mul] at h2
  have h3 := Ideal.pow_right_mono hN k h2
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h3
  obtain ⟨b, hb⟩ := h3
  exact ⟨b, by rw [hb, Algebra.smul_def, map_pow, map_natCast]⟩

private theorem ptc_bdd {l : ℕ} [Fact l.Prime] {A : Type} [AddCommGroup A] [Module ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (φ : A →ₗ[ℤ_[l]] ℚ_[l]) : ∃ C : ℝ, ∀ b, ‖φ b‖ ≤ C := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := A)
  refine ⟨∑ i, ‖φ (s i)‖, fun b => ?_⟩
  have hb : b ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, Algebra.smul_def, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (PadicInt.norm_le_one (c i))

private theorem ptc_cont {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Type} [CommRing A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (y : R →+* A) (hy : Function.Surjective y) (φ : A →ₗ[ℤ_[l]] ℚ_[l])
    {X : Type} [TopologicalSpace X] (f : X → R) (hf : AdicCont (maximalIdeal R) f) :
    Continuous fun g => φ (y (f g)) := by
  obtain ⟨N, hN⟩ := ptc_pow (l := l) y hy
  obtain ⟨C, hC⟩ := ptc_bdd φ
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hl : ‖((l : ℕ) : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const C
  rw [zero_mul] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  filter_upwards [(hf (N * k)).eventually_eq g] with g' hg'
  obtain ⟨b, hb⟩ := hN k _ (Ideal.Quotient.eq.1 hg')
  rw [dist_eq_norm, ← map_sub, ← map_sub, hb, map_smul, Algebra.smul_def, map_pow, map_natCast, norm_mul, norm_pow]
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hC b) (by positivity)) hk

theorem UpperTheory.V.Loc.ptCont :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (x : R →ₐ[O] B), (∀ (X : Type) [TopologicalSpace X] (f : X → R), AdicCont (maximalIdeal R) f → QCont l fun g => x (f g)) ∧ (IsField B → (∀ a, IsIntegral ℤ_[l] (x a)) ∧ ∀ a ∈ maximalIdeal R, ∃ n : ℕ, ∃ b, IsIntegral ℤ_[l] b ∧ x a ^ n = (l : B) * b) := by
  intro l _ O _ _ _ _ _ _ _ R _ _ _ B _ _ _ _ _ _ _ x
  letI : Algebra ℤ_[l] R := ((algebraMap O R).comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hR : ∀ a : R, ∃ c, IsIntegral ℤ_[l] c ∧ a - c ∈ maximalIdeal R := fun a => by
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    exact ⟨_, (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) c).algebraMap, hc⟩
  let x' : R →ₐ[ℤ_[l]] B := x.restrictScalars ℤ_[l]
  refine ⟨fun X _ f hf => ?_, fun hB => ?_⟩
  · haveI := ptc_finite hR x'
    letI : TopologicalSpace B := moduleTopology ℚ_[l] B
    haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
    haveI : ContinuousAdd B := IsModuleTopology.toContinuousAdd ℚ_[l] B
    let e := (Module.finBasis ℚ_[l] B).equivFun
    have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
    have h1 : Continuous fun g => e (x (f g)) := continuous_pi fun i =>
      ptc_cont x'.rangeRestrict.toRingHom x'.rangeRestrict_surjective
        ((((LinearMap.proj i).comp e.toLinearMap).restrictScalars ℤ_[l]).comp x'.range.val.toLinearMap) f hf
    have h2 := he.comp h1
    simpa [QCont, Function.comp_def] using h2
  · letI := hB.toField
    exact ⟨ptc_field' hR x', fun a ha => (ptc_field x' a ha).2⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtFinFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem ptFin_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

private theorem ptFin_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow m hres n

private theorem ptFin_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P
      (by change (P.comap (algebraMap O S)).IsMaximal; rw [h2]; infer_instance)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := ptFin_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

theorem UpperTheory.V.Loc.ptFin :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (F : R →ₐ[O] DualNumber (PadicAlgCl l)), IsLocPt (dualFst F) → ∃ E' : FinExt l, ∀ a, (F a).fst ∈ E'.1 ∧ (F a).snd ∈ E'.1 := by
  intro l _ O _ _ _ _ _ _ _ _ _ R _ _ _ F hF
  classical
  set f := dualFst F with hf
  have hfa : ∀ a, (F a).fst = f a := fun a => rfl
  have hO : ∀ a : O, IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := ((ptFin_int _).2 (hF _ hc).le).tower_top
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  haveI : Module.Finite O f.range := ptFin_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := f.range)
  choose b hb using fun i => hg (s i)
  obtain ⟨r', o, ho⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  obtain ⟨P, hP⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let T : Set (PadicAlgCl l) := Set.range (fun i => algebraMap O (PadicAlgCl l) (o i)) ∪ Set.range (fun i => f (b i)) ∪
    Set.range (fun i => (F (b i)).snd) ∪ (fun p => (F p).snd) '' (P : Set R)
  have hT : T.Finite :=
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (P.finite_toSet.image _)
  haveI : Finite T := hT
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] T
  have hE : FiniteDimensional ℚ_[l] E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTE : T ⊆ E := IntermediateField.subset_adjoin _ _
  have hOE : ∀ c : O, algebraMap O (PadicAlgCl l) c ∈ E := by
    intro c
    have hc : c ∈ Submodule.span ℤ_[l] (Set.range o) := ho ▸ Submodule.mem_top
    obtain ⟨u, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact mul_mem (E.algebraMap_mem _) (hTE (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
  have hdec : ∀ a : R, ∃ u : Fin r → O, a - ∑ i, u i • b i ∈ RingHom.ker f := by
    intro a
    have hc : g a ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    refine ⟨u, ?_⟩
    have h1 : g (a - ∑ i, u i • b i) = 0 := by simp [hb, hu]
    exact congrArg Subtype.val h1
  have h1 : ∀ a, f a ∈ E := by
    intro a
    obtain ⟨u, hu⟩ := hdec a
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hu, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
  have h2 : ∀ a ∈ Ideal.span (P : Set R), (F a).snd ∈ E := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz => exact hTE (Or.inr ⟨z, hz, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact add_mem hx hy
    | smul c x hx0 hx =>
      have h0 : (F x).fst = 0 := by
        have : x ∈ RingHom.ker f := hP ▸ hx0
        exact this
      rw [smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero]
      exact mul_mem (h1 c) hx
  refine ⟨⟨E, hE⟩, fun a => ⟨h1 a, ?_⟩⟩
  obtain ⟨u, hu⟩ := hdec a
  have h3 := h2 _ (hP ▸ hu)
  have h4 : (F (∑ i, u i • b i)).snd ∈ E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, TrivSqZeroExt.snd_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inr ⟨i, rfl⟩)))
  have h5 := add_mem h3 h4
  rwa [← TrivSqZeroExt.snd_add, ← map_add, sub_add_cancel] at h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SmoothCompl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem sc_pi (E : Type) [Field E] (n k : ℕ) :
    ∃ π : (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ (k + 2)) →ₐ[E] E,
      (∀ g, π (Ideal.Quotient.mk _ g) = MvPowerSeries.constantCoeff g) ∧ ∀ a, π a = 0 → IsNilpotent a := by
  let cc : MvPowerSeries (Fin n) E →ₐ[E] E :=
    { (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) E →+* E) with
      commutes' := fun a => by simp [MvPowerSeries.algebraMap_apply] }
  refine ⟨Ideal.Quotient.liftₐ _ cc fun g hg => (sc_max E n g).1 (Ideal.pow_le_self (by omega) hg),
    fun g => rfl, fun a ha => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨k + 2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow ((sc_max E n g).2 ha) _

private theorem sc_inj {O E R : Type} [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ) (φ : R →ₐ[O] MvPowerSeries (Fin n) E)
    (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I)
    (N : ℕ) : ∀ a, φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ N →
      ∃ e : O, e ≠ 0 ∧ e • a ∈ RingHom.ker x ^ N ⊔ I := by
  have hmap : ∀ k, ∀ b ∈ RingHom.ker x ^ k ⊔ I, φ b ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k := by
    intro k
    have : RingHom.ker x ^ k ⊔ I ≤ (maximalIdeal (MvPowerSeries (Fin n) E) ^ k).comap (φ : R →+* _) := by
      refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) k) (Ideal.le_comap_pow _ k)) fun y hy => ?_
      · refine (sc_max E n (φ y)).2 ?_
        rw [hconst, show x y = 0 from hy, map_zero]
      · show φ y ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ k
        rw [show φ y = 0 from hI hy]
        exact zero_mem _
    exact fun b hb => this hb
  induction N with
  | zero => exact fun a _ => ⟨1, one_ne_zero, by simp⟩
  | succ N ih =>
    intro a ha
    obtain ⟨e, he, h1⟩ := ih a (Ideal.pow_le_pow_right (Nat.le_succ N) ha)
    obtain ⟨b, hb, i, hi, hbi⟩ := Submodule.mem_sup.1 h1
    obtain ⟨e', h, he', hh, h2⟩ := UpperTheory.exists_homogeneous_lift_mod_ker_pow_succ_sup O R I x n t ht0 hspan N b hb
    have hφb : φ b = e • φ a := by
      rw [← map_smul, ← hbi, map_add (f := _), show φ i = 0 from hI hi, add_zero]
    have h3 : MvPolynomial.aeval (fun j => φ (t j)) h ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) := by
      have h4 := hmap _ _ h2
      rw [map_sub, map_smul, hφb, MvPolynomial.comp_aeval_apply] at h4
      have h5 : e' • e • φ a ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ (N + 1) :=
        Submodule.smul_of_tower_mem _ _ (Submodule.smul_of_tower_mem _ _ ha)
      simpa using sub_mem h5 h4
    have h0 := UpperTheory.eq_zero_of_homogeneous_aeval_mem_maximalIdeal_pow_succ O E n _ c hc ht N h hh h3
    rw [h0, map_zero, sub_zero] at h2
    refine ⟨e' * e, mul_ne_zero he' he, ?_⟩
    rw [mul_smul, ← hbi, smul_add]
    exact add_mem h2 (Ideal.mem_sup_right (Submodule.smul_of_tower_mem _ _ hi))

private theorem sc_dim {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ringKrullDim (R ⧸ RingHom.ker φ) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have : IsCO O (R ⧸ RingHom.ker φ) :=
    co_quot O R _ (Ideal.Quotient.mkₐ O _) Ideal.Quotient.mk_surjective
  have hPx : ∀ a ∈ RingHom.ker φ, x a = 0 := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨x', hx'⟩ : ∃ x' : (R ⧸ RingHom.ker φ) →ₐ[O] O, ∀ a, x' (Ideal.Quotient.mk _ a) = x a :=
    ⟨Ideal.Quotient.liftₐ _ x hPx, fun _ => rfl⟩
  obtain ⟨φ', hφ'⟩ : ∃ φ' : (R ⧸ RingHom.ker φ) →ₐ[O] MvPowerSeries (Fin n) E,
      ∀ a, φ' (Ideal.Quotient.mk _ a) = φ a := ⟨Ideal.Quotient.liftₐ _ φ fun _ h => h, fun _ => rfl⟩
  have h1 := UpperTheory.ringKrullDim_mvPowerSeries_fin_field O E _ x' n φ' (fun i => Ideal.Quotient.mk _ (t i)) c hc
    (fun a => by obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a; rw [hφ', hx', hconst])
    (fun i => by rw [hφ']; exact ht i)
  have h2 := UpperTheory.height_ker_section_le_of_cotangent_generators O _ x' n (fun i => Ideal.Quotient.mk _ (t i)) (fun i => by rw [hx', ht0])
    (fun a ha => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨e, o, he, h⟩ := hspan a (by rw [← hx', ha])
      refine ⟨e, o, he, ?_⟩
      have hle : RingHom.ker x ^ 2 ⊔ I ≤ (RingHom.ker x' ^ 2).comap (Ideal.Quotient.mk (RingHom.ker φ)) := by
        refine sup_le (le_trans (Ideal.pow_right_mono (fun y hy => ?_) 2) (Ideal.le_comap_pow _ 2)) fun y hy => ?_
        · exact (hx' y).trans hy
        · rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 (hI hy)]
          exact zero_mem _
      have h3 : Ideal.Quotient.mkₐ O (RingHom.ker φ) (e • a - ∑ i, o i • t i) ∈ RingHom.ker x' ^ 2 := hle h
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sub, map_sum, map_smul, Ideal.Quotient.mkₐ_eq_mk] using h3)
  rw [UpperTheory.ringKrullDim_eq_height_ker_section_add_one O _ x', le_antisymm h2 h1]
  norm_cast

private theorem sc_end {O E R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Field E] [Algebra O E] [IsFractionRing O E]
    [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O) (hIx : I ≤ RingHom.ker x) (n : ℕ)
    (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (t : Fin n → R) (c : O) (hc : c ≠ 0) (hI : I ≤ RingHom.ker φ)
    (hconst : ∀ a, MvPowerSeries.constantCoeff (φ a) = algebraMap O E (x a)) (ht0 : ∀ i, x (t i) = 0)
    (ht : ∀ i, φ (t i) - c • MvPowerSeries.X i ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2)
    (hspan : ∀ a, x a = 0 → ∃ (e : O) (o : Fin n → O), e ≠ 0 ∧ e • a - ∑ i, o i • t i ∈ RingHom.ker x ^ 2 ⊔ I) :
    ∃ P : Ideal R, UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧
      (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧
      ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  have : IsDomain (MvPowerSeries (Fin n) E) := NoZeroDivisors.to_isDomain _
  have hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hinj := sc_inj I x n φ t c hc hI hconst ht0 ht hspan
  have hPx : RingHom.ker φ ≤ RingHom.ker x := fun a ha => by
    refine IsFractionRing.injective O E ?_
    rw [← hconst, show φ a = 0 from ha, map_zero, map_zero]
  obtain ⟨y, hy, hyP⟩ := UpperTheory.exists_not_mem_mul_mem_ideal_of_forall_prime_pow_sup R I (RingHom.ker x) (RingHom.ker φ) (RingHom.ker_isPrime _) hIx
    fun a ha N => by
      obtain ⟨e, he, h⟩ := hinj N a (by rw [show φ a = 0 from ha]; exact zero_mem _)
      refine ⟨algebraMap O R e, fun h' => he ?_, by rwa [← Algebra.smul_def]⟩
      simpa using h'
  have hle : ∀ Q : Ideal R, Q.IsPrime → I.radical ≤ Q → Q ≤ RingHom.ker x → RingHom.ker φ ≤ Q :=
    fun Q hQ h1 h2 a ha => (hQ.mem_or_mem (h1 (Ideal.le_radical (hyP a ha)))).resolve_left fun h => hy (h2 h)
  have hrad : I.radical ≤ RingHom.ker φ := hP.radical_le_iff.2 hI
  refine ⟨RingHom.ker φ, ⟨rfl, hconst, UpperTheory.power_series_approximation_mod_maximal O E R n φ t c hc ht, fun N a ha => ?_⟩, hI, ⟨y, hy, hyP⟩,
    fun Q hQ => ⟨fun h => ?_, fun h => h ▸ hPx⟩, ⟨⟨hP, hrad⟩, fun Q hQ h => hle Q hQ.1 hQ.2 (h.trans hPx)⟩,
    sc_dim I x n φ t c hc hI hconst ht0 ht hspan⟩
  · obtain ⟨e, he, h⟩ := hinj N a ha
    exact ⟨e, he, sup_le_sup_left hI _ h⟩
  · have h1 := hle Q hQ.1.1 hQ.1.2 h
    exact le_antisymm (hQ.2 ⟨hP, hrad⟩ h1) h1

theorem UpperTheory.V.Loc.smoothCompl :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (I : Ideal R) (x : R →ₐ[O] O), I ≤ RingHom.ker x → (∀ (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (B' : Type) [CommRing B'] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] [Algebra O B'] [Algebra ℤ_[l] B'] [IsScalarTower ℤ_[l] O B'] [IsScalarTower ℤ_[l] ℚ_[l] B'] [Algebra E B'] [IsScalarTower O E B'] [IsScalarTower ℚ_[l] E B'] (π' : B' →ₐ[E] E) (hπ' : ∀ a, π' a = 0 → IsNilpotent a) (p : B →ₐ[E] B'), Function.Surjective p → π'.comp p = π → ∀ f' : R →ₐ[O] B', I ≤ RingHom.ker f' → (∀ a, π' (f' a) = algebraMap O E (x a)) → ∃ f : R →ₐ[O] B, I ≤ RingHom.ker f ∧ ∀ a, p (f a) = f' a) → ∃ (n : ℕ) (P : Ideal R) (φ : R →ₐ[O] MvPowerSeries (Fin n) E), UpperTheory.V.Loc.IsCompl P x φ ∧ I ≤ P ∧ (∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a ∈ I) ∧ (∀ Q ∈ I.radical.minimalPrimes, Q ≤ RingHom.ker x ↔ Q = P) ∧ P ∈ I.radical.minimalPrimes ∧ ringKrullDim (R ⧸ P) = (n + 1 : ℕ) := by
  intro l _ O _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ R _ _ _ I x hIx H
  obtain ⟨n, D, t, c, hc, hD, hDI, ht0, htD, hspan⟩ := UpperTheory.exists_derivations_dual_to_cotangent_parameters O E R I x hIx
  obtain ⟨f₀, hf₀⟩ := sc_first x n D hD
  have : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) E)) (MvPowerSeries (Fin n) E) := by
    rw [← sc_span]; infer_instance
  have hfin : ∀ k, Module.Finite ℚ_[l] (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
    fun k => by
      have : Module.Finite E (MvPowerSeries (Fin n) E ⧸ maximalIdeal (MvPowerSeries (Fin n) E) ^ k) :=
        GlobalTheory.FormalIsogeny.finite_quotient_of_pow_le (N := k) (by rw [sc_span])
      exact Module.Finite.trans E _
  have hc0 : ∀ a g, Ideal.Quotient.mk _ g = f₀ a → MvPowerSeries.constantCoeff g = algebraMap O E (x a) := by
    intro a g hg
    rw [hf₀, Ideal.Quotient.eq] at hg
    have := (sc_max E n _).1 (Ideal.pow_le_self (by omega) hg)
    simpa [sub_eq_zero] using this
  obtain ⟨φ, hφI, hφ⟩ := sc_tower (maximalIdeal (MvPowerSeries (Fin n) E)) I f₀
    (fun a ha => by
      rw [RingHom.mem_ker, hf₀, show x a = 0 from hIx ha]
      simp [hDI _ a ha])
    (fun N f' h1 h2 => by
      obtain ⟨π, hπ, hn⟩ := sc_pi E n (N + 1)
      obtain ⟨π', hπ', hn'⟩ := sc_pi E n N
      have := hfin (N + 1 + 2)
      have := hfin (N + 2)
      refine H _ π hn _ π' hn' (Ideal.Quotient.factorₐ E (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2)))
        (Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right (by omega : N + 2 ≤ N + 1 + 2))) (AlgHom.ext fun b => ?_) f' h1 fun a => ?_
      · obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact (hπ' g).trans (hπ g).symm
      · obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective (f' a)
        rw [← hg, hπ']
        refine hc0 a g ?_
        rw [← h2, ← hg, Ideal.Quotient.factor_mk])
  obtain ⟨P, hP⟩ := sc_end I x hIx n φ t c hc hφI (fun a => hc0 a _ (hφ a)) ht0 (fun i => by
    have h := hφ (t i)
    rw [hf₀, Ideal.Quotient.eq] at h
    simpa [ht0, htD, apply_ite, Algebra.smul_def, MvPowerSeries.algebraMap_apply] using h) hspan
  exact ⟨n, P, φ, hP⟩
end

