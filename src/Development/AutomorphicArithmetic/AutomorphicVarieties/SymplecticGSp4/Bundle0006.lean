module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0009
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0066
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section SlopeTestRemainingChoices

open Polynomial

private theorem cop_intIff {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
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

private theorem cop_norm_lt {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ_[l] R]
    (y : R →ₐ[ℤ_[l]] PadicAlgCl l) (a : R) (ha : a ∈ maximalIdeal R) : ‖y a‖ < 1 :=
  _root_.UpperTheory.Reformulated.B.MonicNormLtOne.mc_norm_lt y a ha

private theorem cop_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h => ?_⟩
  exact ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 ((cop_intIff _).2 h), rfl⟩

private theorem cop_geom {R κ : Type} [CommRing R] [IsNoetherianRing R] [NormedField κ] [IsUltrametricDist κ]
    (m : Ideal R) (y : R →+* κ) (h1 : ∀ x, ‖y x‖ ≤ 1) (hm : ∀ x ∈ m, ‖y x‖ < 1) :
    ∃ a : ℝ, a < 1 ∧ 0 ≤ a ∧ ∀ n, ∀ x ∈ m ^ n, ‖y x‖ ≤ a ^ n :=
  _root_.UpperTheory.Reformulated.B.CoproductGeometry.cop_geom m y h1 hm

private theorem cop_bdd {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] [Algebra ℤ_[l] R]
    (F : R →ₐ[ℤ_[l]] DualNumber (PadicAlgCl l)) (c : Coef l) (h1 : ∀ x, ‖(F x).fst‖ ≤ 1)
    (hc : ∀ x, (F x).fst ∈ c.O) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖(F x).snd‖ ≤ C := by
  classical
  let f : R →ₐ[ℤ_[l]] c.O := ((TrivSqZeroExt.fstHom ℤ_[l] _ _).comp F).codRestrict c.O hc
  haveI : Module.Finite ℤ_[l] f.range := Module.Finite.of_injective f.range.val.toLinearMap Subtype.val_injective
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := f.range)
  choose b hb using fun i => f.rangeRestrict_surjective (s i)
  obtain ⟨P, hP⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let C : NNReal := P.sup fun x => ‖(F x).snd‖₊
  have h2 : ∀ a ∈ Ideal.span (P : Set R), ‖(F a).snd‖ ≤ C := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz => exact Finset.le_sup (f := fun x => ‖(F x).snd‖₊) hz
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
    | smul c x hx0 hx =>
      have h0 : (F x).fst = 0 := by
        have : x ∈ RingHom.ker f := hP ▸ hx0
        exact congrArg Subtype.val this
      rw [smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (h1 c)).trans hx
  refine ⟨C + ∑ i, ‖(F (b i)).snd‖, by positivity, fun a => ?_⟩
  have hc : f.rangeRestrict a ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
  have h3 : f.rangeRestrict (a - ∑ i, u i • b i) = 0 := by simp [hb, hu]
  have h4 : a - ∑ i, u i • b i ∈ RingHom.ker f := congrArg Subtype.val h3
  have h5 := h2 _ (hP ▸ h4)
  have h6 : ‖(F (∑ i, u i • b i)).snd‖ ≤ ∑ i, ‖(F (b i)).snd‖ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, TrivSqZeroExt.snd_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) ((cop_intIff _).1 isIntegral_algebraMap)
  have h7 : (F a).snd = (F (a - ∑ i, u i • b i)).snd + (F (∑ i, u i • b i)).snd := by
    rw [← TrivSqZeroExt.snd_add, ← map_add (f := _), sub_add_cancel]
  rw [h7]
  exact (norm_add_le _ _).trans (add_le_add h5 h6)

private theorem cop_snd {R κ : Type} [CommRing R] [NormedField κ] [IsUltrametricDist κ]
    (m : Ideal R) (F : R →+* DualNumber κ) {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C)
    (h1 : ∀ n, ∀ x ∈ m ^ n, ‖(F x).fst‖ ≤ a ^ n) (h2 : ∀ x, ‖(F x).snd‖ ≤ C) (n : ℕ) :
    ∀ x ∈ m ^ (n + 1), ‖(F x).snd‖ ≤ a ^ n * C := by
  induction n with
  | zero => intro x _; simpa using h2 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun u hu v hv => ?_) fun u v hu hv => ?_
    · rw [map_mul, DualNumber.snd_mul]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul]
        exact mul_le_mul (h1 _ u hu) (h2 v) (norm_nonneg _) (by positivity)
      · rw [norm_mul]
        have h3 := h1 1 v (by rwa [pow_one])
        calc _ ≤ (a ^ n * C) * a ^ 1 := mul_le_mul (ih u hu) h3 (norm_nonneg _) (by positivity)
          _ = _ := by ring
    · rw [map_add (f := _), TrivSqZeroExt.snd_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)

private theorem cop_main {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O]
    [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R]
    (F : R →ₐ[O] DualNumber (PadicAlgCl l)) :
    (∃ c' : Coef l, ∀ x, (F x).fst ∈ c'.O) ∧
    (∃ a : ℝ, a < 1 ∧ 0 ≤ a ∧ ∀ n, ∀ x ∈ maximalIdeal R ^ n, ‖(F x).fst‖ ≤ a ^ n) ∧
    (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, (F x).fst ∈ K ∧ (F x).snd ∈ K) ∧
    ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ maximalIdeal R ^ n, ‖(F x).snd‖ ≤ ε := by
  letI : Algebra ℤ_[l] R := ((algebraMap O R).comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : R →ₐ[O] PadicAlgCl l := UpperTheory.V.U3.dualFst F
  have hm : ∀ x ∈ maximalIdeal R, ‖(F x).fst‖ < 1 := cop_norm_lt (f.restrictScalars ℤ_[l])
  have h1 : ∀ x, ‖(F x).fst‖ ≤ 1 := by
    intro x
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) x
    have h2 : f x = f (x - algebraMap O R c) + algebraMap O _ c := by simp
    have h3 : IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) c) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) c).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))
    show ‖f x‖ ≤ 1
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hm _ hc).le ((cop_intIff _).1 h3))
  obtain ⟨E, hE⟩ := UpperTheory.V.Loc.ptFin (l := l) R F hm
  haveI : FiniteDimensional ℚ_[l] E.1 := E.2
  obtain ⟨c', hc'⟩ := cop_coef E.1
  have hc : ∀ x, (F x).fst ∈ c'.O := fun x => hc' _ (hE x).1 (h1 x)
  obtain ⟨a, ha1, ha0, ha⟩ := cop_geom (maximalIdeal R) (f : R →+* PadicAlgCl l) h1 hm
  refine ⟨⟨c', hc⟩, ⟨a, ha1, ha0, ha⟩, ⟨E.1, E.2, hE⟩, fun ε hε => ?_⟩
  obtain ⟨C, hC0, hC⟩ := cop_bdd (F.restrictScalars ℤ_[l]) c' h1 hc
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const C
  rw [zero_mul] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact ⟨k + 1, fun x hx =>
    (cop_snd (maximalIdeal R) (F : R →+* DualNumber (PadicAlgCl l)) ha0 hC0 ha hC k x hx).trans hk.le⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.GradeZeroInterpolatingElement.coPt :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R], (∀ y : R →ₐ[c.O] PadicAlgCl l, (∃ c' : Coef l, c.O ≤ c'.O ∧ ∀ x, y x ∈ c'.O) ∧ ∃ a : ℝ, a < 1 ∧ 0 ≤ a ∧ ∀ n, ∀ x ∈ maximalIdeal R ^ n, ‖y x‖ ≤ a ^ n) ∧ ∀ y : R →ₐ[c.O] DualNumber (PadicAlgCl l), (∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x, (y x).fst ∈ K ∧ (y x).snd ∈ K) ∧ ∀ ε : ℝ, 0 < ε → ∃ n, ∀ x ∈ maximalIdeal R ^ n, ‖(y x).snd‖ ≤ ε := by
  intro l _ c R _ _ _
  refine ⟨fun y => ?_, fun y => (cop_main R y).2.2⟩
  obtain ⟨⟨c', hc'⟩, h2, -⟩ := cop_main R ((TrivSqZeroExt.inlAlgHom c.O (PadicAlgCl l) (PadicAlgCl l)).comp y)
  refine ⟨⟨c', fun x hx => ?_, hc'⟩, h2⟩
  have h : y (algebraMap c.O R ⟨x, hx⟩) ∈ c'.O := hc' _
  rwa [AlgHom.commutes] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PhiGam
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private def permR (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) :
    Representation R Γ (Γ ⧸ H → R) where
  toFun g := LinearMap.funLeft R R fun x => g⁻¹ • x
  map_one' := by ext f x; simp
  map_mul' g h := by ext f x; simp [mul_smul]

private theorem permR_apply (R : Type) [CommRing R] {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (f : Γ ⧸ H → R)
    (x : Γ ⧸ H) : permR R H g f x = f (g⁻¹ • x) := rfl

private theorem sec_mem {Γ : Type} [Group Γ] (H : Subgroup Γ) (g : Γ) (x : Γ ⧸ H) :
    (x.out)⁻¹ * g * (g⁻¹ • x).out ∈ H := by
  have h : ((g⁻¹ * x.out : Γ) : Γ ⧸ H) = (((g⁻¹ • x).out : Γ) : Γ ⧸ H) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, ← MulAction.Quotient.smul_mk, QuotientGroup.out_eq']
  simpa [mul_assoc] using QuotientGroup.eq.1 h

private theorem phi_condition_of_finite_cohomology {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (n : ℕ)
    [NeZero n]
    (h : ∀ (M : Type) [AddCommGroup M] [Module (ZMod n) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M]
      (ρ : Representation (ZMod n) Γ M), ContAction ρ → Finite (H1 ρ)) : PhiCond Γ n := by
  intro H hH
  haveI : DiscreteTopology (Γ ⧸ H) := QuotientGroup.discreteTopology hH
  haveI : Finite (Γ ⧸ H) := finite_of_compact_of_discrete
  letI : TopologicalSpace (ZMod n) := ⊥
  haveI : DiscreteTopology (ZMod n) := ⟨rfl⟩
  have hs : ∀ x : Γ ⧸ H, Continuous fun g : Γ => g⁻¹ • x := fun x => continuous_inv.smul continuous_const
  have hc : ContAction (permR (ZMod n) H) := by
    refine continuous_pi fun x => ?_
    have h1 : Continuous fun p : (Γ ⧸ H → ZMod n) × (Γ ⧸ H) => p.1 p.2 := continuous_of_discreteTopology
    exact h1.comp (continuous_snd.prodMk ((hs x).comp continuous_fst))
  haveI h1 := h _ _ hc
  haveI : Finite (Z1 (permR (ZMod n) H)) := by
    have hB : Finite (B1 (permR (ZMod n) H)) := (Set.finite_range _).to_subtype
    have hB' : Finite ((B1 (permR (ZMod n) H)).comap (Z1 (permR (ZMod n) H)).subtype).toAddSubgroup :=
      Finite.of_injective (fun z => (⟨z.1.1, z.2⟩ : B1 (permR (ZMod n) H)))
        fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab))
    exact @Finite.of_addSubgroup_quotient _ _ _ hB' h1
  have hφ : ∀ φ : H →* Multiplicative (ZMod n), IsOpen (φ.ker : Set H) → Continuous φ := fun φ hφ =>
    continuous_of_continuousAt_one φ (by
      rw [ContinuousAt, map_one, nhds_discrete (Multiplicative (ZMod n)), Filter.tendsto_pure]
      exact hφ.mem_nhds φ.ker.one_mem)
  let c : {φ : H →* Multiplicative (ZMod n) // IsOpen (φ.ker : Set H)} → Z1 (permR (ZMod n) H) := fun φ =>
    ⟨fun g x => Multiplicative.toAdd (φ.1 ⟨_, sec_mem H g x⟩), by
      refine ⟨continuous_pi fun x => continuous_toAdd.comp ((hφ φ.1 φ.2).comp (Continuous.subtype_mk ?_ _)), fun g g' => ?_⟩
      · exact (continuous_const.mul continuous_id).mul
          ((continuous_of_discreteTopology (f := fun y : Γ ⧸ H => y.out)).comp (hs x))
      · funext x
        rw [Pi.add_apply, permR_apply, ← toAdd_mul, ← map_mul]
        refine congrArg (fun u => Multiplicative.toAdd (φ.1 u)) (Subtype.ext ?_)
        simp [mul_smul, mul_assoc]⟩
  refine Finite.of_injective c fun φ φ' e => Subtype.ext (MonoidHom.ext fun u => ?_)
  let x : Γ ⧸ H := ((1 : Γ) : Γ ⧸ H)
  have hx : x.out ∈ H := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' x).symm
    simpa using this
  have hfix : (x.out * u * (x.out)⁻¹)⁻¹ • x = x := by
    change (((x.out * u * (x.out)⁻¹)⁻¹ * 1 : Γ) : Γ ⧸ H) = ((1 : Γ) : Γ ⧸ H)
    rw [QuotientGroup.eq]
    simpa using H.mul_mem (H.mul_mem hx u.2) (H.inv_mem hx)
  have hu : (⟨_, sec_mem H (x.out * u * (x.out)⁻¹) x⟩ : H) = u := by
    apply Subtype.ext
    simp only [hfix]
    group
  have := congrFun (congrFun (congrArg Subtype.val e) (x.out * u * (x.out)⁻¹)) x
  simp only [c, hu] at this
  exact Multiplicative.toAdd.injective this

private theorem fin_above {n : ℕ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 ℚ) | ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((n : ℕ) : 𝓞 ℚ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]; exact hv

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.phiGam :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → CohomologyHyp → PhiCond D.Gam l := by
  intro Ω _ _ _ l hl c D hD hP
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have hfin : D.SP.Finite := by
    refine (D.S.finite_toSet.biUnion fun p hp => fin_above (hD.S_prime p hp).ne_zero).subset ?_
    rintro v ⟨p, hp, hv⟩
    exact Set.mem_biUnion hp hv
  have hS : ContainsAbove hfin.toFinset l := fun v hv => hfin.mem_toFinset.2 ⟨l, hD.l_mem, hv⟩
  haveI hK : CompactSpace (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) := inferInstance
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  have key : PhiCond (GS Ω (hfin.toFinset : Set (HeightOneSpectrum (𝓞 ℚ)))) (l ^ 1) :=
    phi_condition_of_finite_cohomology (l ^ 1) fun M _ _ _ _ _ ρ hρ => by
      obtain ⟨-, f1, -⟩ := hP.gf ℚ Ω l 1 M hfin.toFinset ρ one_pos hS hρ
      exact f1
  rw [pow_one, hfin.coe_toFinset] at key
  exact key
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtActInternal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.ptAct_internal {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] [AddCommGroup X]
    [DecidableEq X] (𝒜 : X → Submodule O R) [SetLike.GradedMonoid 𝒜] (h : iSupIndep 𝒜) :
    DirectSum.IsInternal fun j => (𝒜 j).comap (gradedSub 𝒜).val.toLinearMap := by
  set f := (gradedSub 𝒜).val.toLinearMap with hf
  have hinj : Function.Injective f := fun a b hab => Subtype.ext hab
  have hind : iSupIndep fun j => (𝒜 j).comap f := by
    intro i
    rw [disjoint_iff_inf_le]
    have h1 : (⨆ (j) (_ : j ≠ i), (𝒜 j).comap f) ≤ (⨆ (j) (_ : j ≠ i), 𝒜 j).comap f :=
      iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => 𝒜 j) j hj)
    calc (𝒜 i).comap f ⊓ ⨆ (j) (_ : j ≠ i), (𝒜 j).comap f
        ≤ (𝒜 i).comap f ⊓ (⨆ (j) (_ : j ≠ i), 𝒜 j).comap f := inf_le_inf_left _ h1
      _ = (𝒜 i ⊓ ⨆ (j) (_ : j ≠ i), 𝒜 j).comap f := (Submodule.comap_inf _ _ _).symm
      _ = ⊥ := by rw [(h i).eq_bot, Submodule.comap_bot, LinearMap.ker_eq_bot.2 hinj]
      _ ≤ ⊥ := le_rfl
  have hr : LinearMap.range f = ⨆ j, 𝒜 j := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have htop : ⨆ j, (𝒜 j).comap f = ⊤ := by
    apply Submodule.map_injective_of_injective hinj
    rw [Submodule.map_iSup, Submodule.map_top]
    simp_rw [Submodule.map_comap_eq, hr]
    exact le_antisymm (iSup_le fun j => inf_le_left)
      (iSup_le fun j => le_trans (le_inf (le_iSup 𝒜 j) le_rfl) (le_iSup (fun k => (⨆ j, 𝒜 j) ⊓ 𝒜 k) j))
  exact (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨hind, htop⟩

private def UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr {K : Type} [CommRing K] (t : Kˣ × Kˣ) : Multiplicative (ℤ × ℤ) →* Kˣ where
  toFun w := wv t w.toAdd
  map_one' := by simp [wv]
  map_mul' a b := by
    simp only [wv, toAdd_mul, Prod.fst_add, Prod.snd_add, zpow_add]
    exact mul_mul_mul_comm _ _ _ _

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptAct :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ (K : Type) [CommRing K] [Algebra c.O K] (ξ : M.SS →ₐ[c.O] K) (t : Kˣ × Kˣ), ∃ ξ' : M.SS →ₐ[c.O] K, (∀ g, M.rep ξ' g = tconj t (M.rep ξ g)) ∧ ∀ w (f : M.SS), f.1 ∈ M.sPart w → ξ' f = (wv t w : K) * ξ f := by
  intro Ω _ _ _ l _ c D hD M K _ _ ξ t
  let 𝒜' : ℤ × ℤ → Submodule c.O M.SS := fun j => (M.sPart j).comap M.SS.val.toLinearMap
  have hint : DirectSum.IsInternal 𝒜' := UpperTheory.V.GradeZeroInterpolatingElement.ptAct_internal M.sPart (sInternal D hD M).1
  letI hgm : SetLike.GradedMonoid 𝒜' :=
    { one_mem := by
        show ((1 : M.SS) : M.S) ∈ M.sPart 0
        exact SetLike.GradedOne.one_mem
      mul_mem := fun i j a b ha hb => by
        show ((a * b : M.SS) : M.S) ∈ M.sPart (i + j)
        exact SetLike.GradedMul.mul_mem ha hb }
  letI : DirectSum.Decomposition 𝒜' := hint.chooseDecomposition
  letI : GradedAlgebra 𝒜' := { hgm, (inferInstance : DirectSum.Decomposition 𝒜') with }
  have key : ∀ w (f : M.SS), f.1 ∈ M.sPart w →
      act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ f = (wv t w : K) * ξ f :=
    fun w f hf => act_of_mem 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ (j := w) hf
  refine ⟨act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ, fun g => ?_, key⟩
  ext i j
  show act 𝒜' (UpperTheory.V.GradeZeroInterpolatingElement.ptAct_chr t) ξ (M.ent g i j) = (wv t (wt i j) : K) * ξ (M.ent g i j)
  exact key _ _ (M.entry_mem g i j)
end

