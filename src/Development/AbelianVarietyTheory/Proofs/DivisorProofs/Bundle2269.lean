module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1959
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqBasicOpen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0194
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootsOfPeriods
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerRoot

open IsDedekindDomain Polynomial

theorem exists_ord (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ v : (FractionRing V)ˣ →* Multiplicative ℤ,
      (∀ x : (FractionRing V)ˣ, 0 ≤ (v x).toAdd → ∃ a : V, algebraMap V _ a = (x : FractionRing V)) ∧
      ∀ (x : (FractionRing V)ˣ) (a : V), algebraMap V _ a = (x : FractionRing V) →
        (0 < (v x).toAdd ↔ a ∈ maximalIdeal V) := by
  let w := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hw : ∀ x : (FractionRing V)ˣ, w x ≠ 0 := fun x => by simp [w]
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd (-WithZero.log (w x))) fun x y => ?_, fun x hx => ?_,
    fun x a ha => ?_⟩
  · rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hw x) (hw y), neg_add]
  · refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_nonneg] at hx
    exact (WithZero.log_le_log (hw x) one_ne_zero).1 (by simpa using hx)
  · simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_pos]
    have h1 : WithZero.log (w x) < 0 ↔ w x < 1 := by
      simpa using WithZero.log_lt_log (hw x) one_ne_zero
    rw [h1, ← ha]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem _ a

theorem exists_nthRoots_ext (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {I : Type} [Fintype I] (a : I → V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (f : V →+* W) (s : I → W),
      Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ ∀ k, s k ^ n = f (a k) := by
  classical
  let K := FractionRing V
  haveI : CharZero K := algebraRat.charZero _
  let p : I → K[X] := fun k => X ^ n - C (algebraMap V K (a k))
  have hp : ∀ k, (p k).Monic := fun k => monic_X_pow_sub_C _ (by omega)
  let L := (∏ k, p k).SplittingField
  have hsp : ((∏ k, p k).map (algebraMap K L)).Splits := SplittingField.splits _
  have hroot : ∀ k, ∃ t : L, t ^ n = algebraMap K L (algebraMap V K (a k)) := fun k => by
    have h0 : (∏ k, p k).map (algebraMap K L) ≠ 0 :=
      ((monic_prod_of_monic _ _ fun k _ => hp k).map _).ne_zero
    have h1 : ((p k).map (algebraMap K L)).Splits :=
      hsp.of_dvd h0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
    obtain ⟨t, ht⟩ := h1.exists_eval_eq_zero (by
      rw [(hp k).degree_map, degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : n ≠ 0))
    refine ⟨t, ?_⟩
    simpa [p, sub_eq_zero] using ht
  choose t ht using hroot
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hs : ∀ k, t k ∈ Set.range (algebraMap W L) := fun k => hint _
    ⟨X ^ n - C (a k), monic_X_pow_sub_C _ (by omega), by simp [ht]⟩
  choose s hs using hs
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V W, s, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, fun k => IsFractionRing.injective W L ?_⟩
  rw [map_pow, hs, ht]
  exact (RingHom.congr_fun hc (a k)).symm

theorem exists_form {G X : Type} [CommGroup G] [AddCommGroup X] (v : G →* Multiplicative ℤ) (q : X → X → G)
    (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃ β : LinearMap.BilinForm ℤ X, ∀ x y, β x y = (v (q x y)).toAdd := by
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  let F : X → X →ₗ[ℤ] ℤ := fun x =>
    (AddMonoidHom.mk' (fun y => (v (q x y)).toAdd) fun y y' => by simp [hadd']).toIntLinearMap
  exact ⟨(AddMonoidHom.mk' F fun x x' => LinearMap.ext fun y => by simp [F, hadd]).toIntLinearMap,
    fun x y => rfl⟩

theorem isSymBasis_of_basis {X I : Type} [AddCommGroup X] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) X)) :
    IsSymBasis fun k => (ε k : LinearMap.BilinForm ℤ X) := by
  refine ⟨fun k => mem_balForms_int.1 (ε k).2, ε.linearIndependent.map' (Submodule.subtype _) (by simp),
    fun β hβ => ?_⟩
  have h := Submodule.mem_map_of_mem (f := (balForms (id : ℤ → ℤ) X).subtype)
    (ε.mem_span ⟨β, mem_balForms_int.2 hβ⟩)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

theorem exists_roots_of_periods : ∀ (g n : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → 1 ≤ n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (r : ℕ), r ≤ g → ∀ (q : (Fin r → ℤ) → (Fin r → ℤ) → (FractionRing V)ˣ), (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V, w ≠ 0 ∧ (q a a : FractionRing V) = algebraMap V _ w) → ∃ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))), IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x) ∧ ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (fK : FractionRing V →+* FractionRing V') (s : Fin m ⊕ Fin N → V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ ∀ a b, fK (q a b : FractionRing V) = ∏ k, algebraMap V' _ (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) := by
  intro g n φ hφ hn V _ _ _ hV hD r hr q hsym hadd hpos
  obtain ⟨-, -, hcomp, hchar⟩ := hV
  obtain ⟨v, hv1, hv2⟩ := exists_ord V
  obtain ⟨β, hβ⟩ := exists_form v q hsym hadd
  have hβs : ∀ x y, β x y = β y x := fun x y => by rw [hβ, hβ, hsym]
  have hβp : ∀ x, x ≠ 0 → 0 < β x x := fun x hx => by
    obtain ⟨w, hw, -, h⟩ := hpos x hx
    rw [hβ]
    exact (hv2 _ w h.symm).2 hw
  have hβn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hβp x hx).le
  obtain ⟨m, ga, c, hga, hc, hβc⟩ := GlobalTheory.ConeInterior.exists_pos_comb_int g φ hφ r hr β hβs
    (GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hβs) hβn)
  obtain ⟨N, ε, hε⟩ := hga.basis
  have hεga : ∀ k, (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) = ga k := fun k => by rw [hε]
  have hsb := isSymBasis_of_basis ε
  obtain ⟨u, hu, -⟩ := existsUnique_coeff hsb q hsym hadd
  have hβv : ∀ x y, β x y = ∑ j, (c j : ℤ) * ga j x y := fun x y => by
    rw [hβc]; simp [LinearMap.sum_apply]
  have hvu : (fun k => v (u k)) = fun k => Multiplicative.ofAdd (Sum.elim (fun j => (c j : ℤ)) 0 k) := by
    refine eq_of_prod_zpow hsb _ _ fun x y => ?_
    simp_rw [← map_zpow, ← map_prod, ← hu]
    apply Multiplicative.toAdd.injective
    rw [← hβ, hβv, toAdd_prod, Fintype.sum_sum_type]
    simp [hεga, mul_comm]
  have hvk : ∀ k, (v (u k)).toAdd = Sum.elim (fun j => (c j : ℤ)) 0 k := fun k => by
    rw [congrFun hvu k]; rfl
  choose a ha using fun k => hv1 (u k) (by rw [hvk]; cases k <;> simp)
  have ha0 : ∀ k, a k ≠ 0 := fun k h => (u k).ne_zero (by rw [← ha, h, map_zero])
  obtain ⟨W, _, _, _, _, f, s, hinj, hfin, hloc, hs⟩ := exists_nthRoots_ext V a hn
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hinj
  have hfK : ∀ b, IsFractionRing.lift (K := FractionRing V) hinj' (algebraMap V _ b) =
      algebraMap W (FractionRing W) (f b) := fun b => IsFractionRing.lift_algebraMap hinj' b
  refine ⟨m, N, ε, by simpa only [hεga] using hga, fun x hx => ?_, W, inferInstance, inferInstance, inferInstance, f,
    IsFractionRing.lift hinj', s, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, inferInstance, hinj, hfin, hloc,
    hfK, fun k => ⟨?_, fun h => ?_⟩, fun k => ?_, fun x y => ?_⟩
  · by_contra h
    push_neg at h
    have h1 := hβp x hx
    rw [hβv] at h1
    exact h1.not_ge (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hεga j ▸ h j))
  · exact charZero_of_injective_ringHom hinj
  · have h1 : a (.inl k) ∈ maximalIdeal V := (hv2 _ _ (ha _)).1 (by rw [hvk]; simpa using hc k)
    intro h
    exact h1 (isUnit_of_map_unit f _ (hs _ ▸ h.pow n))
  · refine ha0 (.inl k) (hinj ?_)
    rw [← hs, h, map_zero, zero_pow (by omega)]
  · have h1 : a (.inr k) ∉ maximalIdeal V := fun h => by
      have := (hv2 _ _ (ha _)).2 h
      rw [hvk] at this
      simp at this
    have h2 : IsUnit (s (.inr k) ^ n) := hs _ ▸ (not_not.1 h1 : IsUnit (a (.inr k))).map f
    exact (isUnit_pow_iff (by omega)).1 h2
  · rw [hu, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, hfK, ← hs, map_pow, zpow_mul, zpow_natCast]

end GlobalTheory.PerRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingBasicOpenOfNearGenerato
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LBGerm GlobalTheory.AmpleOverBase

namespace GlobalTheory.GenNearExtend

theorem exists_sec_of_gen_near : ∀ (Z X : Scheme.{0}) (e : X ⟶ Z), IsOpenImmersion e → CompactSpace X →
    QuasiSeparatedSpace X → ∀ (M : LB Z), M.IsLB → ∀ (r : Γ(X, ⊤)) (O : Z.Opens),
    (∀ x ∈ X.basicOpen r, e x ∈ O) → ∀ t : LB.Gen (M.pull O.ι), t.IsGen →
    ∃ σ : LB.Sec (M.pull e), X.basicOpen r ≤ nonzeroLocus σ := by
  intro Z X e _ _ _ M hM r O hO t ht
  have hL : (M.pull e).IsLB := LB.isLB_pull hM e
  let f : (X.basicOpen r).toScheme ⟶ X := (X.basicOpen r).ι
  have hrange : Set.range (f ≫ e).base ⊆ Set.range O.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hO _ y.2
  let ψ : (X.basicOpen r).toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι (f ≫ e) hrange
  have hψ : ψ ≫ O.ι = f ≫ e := IsOpenImmersion.lift_fac _ _ _
  have hpt : ∀ y, O.ι (ψ y) = e (f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, hψ, Scheme.Hom.comp_apply]
  let a : ChartPull (lbPow ((M.pull e).pull f) 1) (M.pull O.ι) ψ :=
    { idx := fun J _ => J PUnit.unit PUnit.unit PUnit.unit
      le := fun J y hy => by
        have h1 := mem_pull.1 (mem_pull.1 (mem_powChart.1 hy))
        show ψ y ∈ (M.pull O.ι).U _
        rw [mem_pull, hpt]
        exact h1
      g := fun y J J' hJ hJ' => by
        have h1 := mem_powChart.1 hJ
        have h2 := mem_powChart.1 hJ'
        have h1' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J PUnit.unit PUnit.unit) := mem_pull.1 h1
        have h2' : (𝟙 _ ≫ f) y ∈ (M.pull e).U (J' PUnit.unit PUnit.unit) := mem_pull.1 h2
        have h3 : ψ y ∈ (M.pull O.ι).U (fun _ => J PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h1)
        have h4 : ψ y ∈ (M.pull O.ι).U (fun _ => J' PUnit.unit PUnit.unit PUnit.unit) := by
          rw [mem_pull, hpt]; exact mem_pull.1 (mem_pull.1 h2)
        refine (gm_lbPow_g 1 (𝟙 _) y J J' hJ hJ').trans ?_
        rw [pow_one, gm_pull_g ((M.pull e)) f (𝟙 _) y _ _ h1 h2, gm_pull_g M e (𝟙 _ ≫ f) y _ _ h1' h2',
          gm_pull_g M O.ι ψ y _ _ h3 h4, hψ, Category.id_comp] }
  let s0 : (M.pull O.ι).Sec := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  let t' := chartSec a s0
  have ht' : ∀ y, y ∈ nonzeroLocus t' := fun y => by
    obtain ⟨i, hi⟩ := exists_chart hM (e (f y))
    have hJ : y ∈ (lbPow ((M.pull e).pull f) 1).U (fun _ _ _ => i) :=
      mem_powChart.2 (mem_pull.2 (mem_pull.2 hi))
    rw [mem_nonzeroLocus_iff_isUnit t' hJ, gs_chartSec a s0 (𝟙 _) y _ hJ]
    have hm : (𝟙 _ ≫ ψ) y ∈ (M.pull O.ι).U (a.idx (fun _ _ _ => i)) := a.le _ hJ
    rw [gs_unit _ y _ hm]
    exact Units.isUnit _
  have hr : X.basicOpen r = f.opensRange := (Scheme.Opens.opensRange_ι _).symm
  have hs₀ : nonzeroLocus (secOfFn (M.pull e) r) = f.opensRange := (nonzeroLocus_secOfFn hL r).trans hr
  obtain ⟨T, hT, hTu⟩ := exists_push f (nonzeroLocus (secOfFn (M.pull e) r)) hs₀ t'
  obtain ⟨N, hN⟩ := exists_sec_eq_pow_mul hL (secOfFn (M.pull e) r) T hT
  obtain ⟨u, hu⟩ := hN N le_rfl
  have key : ∀ (y' : (X.basicOpen r).toScheme) (J : PUnit → (M.pull e).ι), f y' ∈ powChart (M.pull e) J →
      (f y' ∈ nonzeroLocus u ↔ y' ∈ nonzeroLocus t') := fun y' J hJ => by
    have hs : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) := hs₀ ▸ ⟨y', rfl⟩
    have hy : f y' ∈ nonzeroLocus (secOfFn (M.pull e) r) ⊓ powChart (M.pull e) J := ⟨hs, hJ⟩
    have e' := congrArg (gs (𝟙 X) (f y') _) (hu J)
    rw [gs_res (𝟙 X) (f y') _ hy, gs_mul (𝟙 X) (f y') _ hy, gs_pow (𝟙 X) (f y') _ hy,
      gs_res (𝟙 X) (f y') _ hy] at e'
    rw [mem_nonzeroLocus_iff_powFn u hJ, e', IsUnit.mul_iff, hTu y' J hJ]
    exact and_iff_right (((mem_nonzeroLocus_iff_powFn _ hJ).1 hs).pow N)
  refine ⟨secOfPowOne (secCast (by omega) u), ?_⟩
  rw [nonzeroLocus_secOfPowOne, nonzeroLocus_secCast]
  intro x hx
  obtain ⟨y, rfl⟩ : ∃ y, f y = x := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨i, hi⟩ := exists_chart hL (f y)
  exact (key y (fun _ => i) (mem_powChart.2 hi)).2 (ht' y)

end GlobalTheory.GenNearExtend
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingWhereSingleCoefficient
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem exists_sec_sum_nonzero :
    ∀ (X : Scheme.{0}) (L : LB X) (κ : Type) [Fintype κ] (r : κ → Γ(X, ⊤)) (σ : κ → LB.Sec L),
      ∃ s : LB.Sec L, ∀ (z : X) (i : κ), z ∈ X.basicOpen (r i) → z ∈ nonzeroLocus (σ i) →
        (∀ j, j ≠ i → z ∉ X.basicOpen (r j)) → z ∈ nonzeroLocus s := by
  intro X L κ _ r σ
  classical
  have hres : ∀ {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (a : Γ(X, U)),
      (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom a) =
        (X.presheaf.map (homOfLE (h2.trans h1)).op).hom a := by
    intro U V W h1 h2 a
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
  let s : LB.Sec L :=
    { f := fun m => ∑ j, (X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j) * (σ j).f m
      compat := fun m n => by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, Finset.mul_sum, hres]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [(σ j).compat m n]
        ring }
  refine ⟨s, fun z i hri hσi hrj => ?_⟩
  obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.1 hσi
  have hzm : z ∈ L.U m := X.basicOpen_le _ hm
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨m, ?_⟩
  rw [Scheme.mem_basicOpen X _ z hzm] at hm ⊢
  have hgerm : ∀ j, (X.presheaf.germ (L.U m) z hzm).hom
      ((X.presheaf.map (homOfLE (le_top : L.U m ≤ ⊤)).op).hom (r j)) =
        (X.presheaf.germ ⊤ z trivial).hom (r j) := fun j =>
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [s, map_sum, map_mul, hgerm]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hu : IsUnit ((X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m)) :=
    ((Scheme.mem_basicOpen_top X _ z).1 hri).mul hm
  have hmax : ∑ j ∈ Finset.univ.erase i, (X.presheaf.germ ⊤ z trivial).hom (r j) *
      (X.presheaf.germ (L.U m) z hzm).hom ((σ j).f m) ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    refine Ideal.sum_mem _ fun j hj => Ideal.mul_mem_right _ _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen_top]
    exact hrj j (Finset.ne_of_mem_erase hj)
  by_contra hn
  have : (X.presheaf.germ ⊤ z trivial).hom (r i) * (X.presheaf.germ (L.U m) z hzm).hom ((σ i).f m) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk z) := by
    have h2 : _ ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) := (IsLocalRing.mem_maximalIdeal _).2 hn
    simpa using Ideal.sub_mem _ h2 hmax
  exact (IsLocalRing.mem_maximalIdeal _).1 this hu

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunction
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGAGA

variable {A : Over (Sp ℂ)} [GrpObj A] {M : LB A.left} {g : ℕ}

theorem top_le_of_lbPow (u : HolUnif A M g) (k : ℕ) (j : (lbPow M k).ι) {z : Fin g → ℂ}
    (hz : ⊤ ≤ (u.ex z).left ⁻¹ᵁ (lbPow M k).U j) : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) :=
  GlobalTheory.top_le_preimage_mono _ (GlobalTheory.Cartier.lbPow_U M k j).le hz

def powFrame (u : HolUnif A M g) (k : ℕ) : HolUnif A (lbPow M k) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr j z := u.fr (j PUnit.unit) z ^ k
  fr_hol j := ((u.fr_hol (j PUnit.unit)).mono fun _ hz => top_le_of_lbPow u k j hz).pow k
  fr_ne j z hz := pow_ne_zero _ (u.fr_ne _ z (top_le_of_lbPow u k j hz))
  fr_compat i j z hz := GlobalTheory.ThetaBundleSec.fr_pow_compat u z k i j
    ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).1 ((GlobalTheory.top_le_preimage_inf _ _ _).1 hz).2

theorem exists_isFnPow : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → ∀ (k : ℕ) (θ : (Fin g → ℂ) → ℂ), u.IsThetaFn Hm χ k θ → ∃ s, u.IsFnPow k s θ := by
  intro g A _ hA M u Hm χ hM hAH k θ hθ
  have := hA.comm
  have hp : IsProjOver A.hom := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver A.hom).1
    (GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme ℂ A hA)
  obtain ⟨s, hs⟩ := GlobalTheory.HolUnifSec.exists_isFn (powFrame u k) hA hp (GlobalTheory.isLB_lbPow hM k) hθ.1 (by
    intro l hl j z hz
    have hz' : ⊤ ≤ (u.ex z).left ⁻¹ᵁ M.U (j PUnit.unit) := top_le_of_lbPow u k j hz
    have h1 := hθ.2 ⟨l, hl⟩ z
    have h2 := hAH.2.2.2 ⟨l, hl⟩ _ z hz'
    change θ (z + l) * u.fr (j PUnit.unit) (z + l) ^ k = θ z * u.fr (j PUnit.unit) z ^ k
    simp only [hermForm] at h1
    change θ (z + l) = _ at h1
    change u.fr (j PUnit.unit) z = _ * u.fr (j PUnit.unit) (z + l) at h2
    rw [h1, h2, mul_pow]
    ring)
  exact ⟨s, hs⟩

end GlobalTheory.ThetaGAGA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfExpansionDvd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SecDiv

theorem resTop_map {Y : Scheme.{0}} {V W : Y.Opens} (h : W ≤ V) (c : Γ(Y, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom (ReciprocityTheory.ChartRestriction.G.Out.resTop V c) = ReciprocityTheory.ChartRestriction.G.Out.resTop W c := by
  unfold ReciprocityTheory.ChartRestriction.G.Out.resTop
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_secIsMul {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) {L : LB Y}
    (a : R) (τ : LB.Sec L) : ∃ σ : LB.Sec L, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul p a σ τ := by
  unfold ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul
  refine ⟨⟨fun j => ReciprocityTheory.ChartRestriction.G.Out.resTop (L.U j) (scal p a) * τ.f j, fun i j => ?_⟩, fun j => rfl⟩
  simp only [map_mul, resTop_map]
  rw [τ.2 i j]
  ring

theorem exists_expT_of_dvd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 → U.ExpT (𝟙_ _) 1 σ f → (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) → ∃ τ : U.SecGT (𝟙_ _) 1, U.ExpT (𝟙_ _) 1 τ g := by
  intro R _ _ _ hB D A G _ _ U σ f g q hq hσ hfg
  have hB' : AdmBase R (maximalIdeal R) ∧ CharZero R := hB
  have h1 : IsNoetherianRing R ∧ IsDomain R ∧ IsIntegrallyClosed R ∧ IsAdicComplete (maximalIdeal R) R := hB'.1
  obtain ⟨hN, -, hIC, hC⟩ := h1
  haveI := hN
  haveI := hIC
  have hs := U.semi
  haveI := hs.smooth
  haveI := hs.geomConnected
  haveI : IsIso (λ_ G).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ G)).hom)
  have hSm : Smooth (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    rw [← Over.w (λ_ G).hom]
    infer_instance
  have hGC : GeometricallyConnected (𝟙_ (Over (Sp R)) ⊗ G).hom := by
    have hsq : IsPullback (λ_ G).hom.left (𝟙_ (Over (Sp R)) ⊗ G).hom G.hom (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq inferInstance
  have he : (η[G].left ≫ (λ_ G).inv.left) ≫ (𝟙_ (Over (Sp R)) ⊗ G).hom = 𝟙 _ := by
    simp only [Category.assoc, Over.w]
    rfl
  have hLB : (LB.LinComb U.P.L.L (K := Fin 1) (fun _ : Fin 1 => (snd (𝟙_ (Over (Sp R))) G).left)
      (fun _ => ((1 : ℕ) : ℤ))).IsLB := by
    first
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U.P.L.isLB _ _
    | exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ _ _
  have hloc := _root_.GlobalTheory.ClosedFibreDvd.germ_dvd_of_expT_dvd R hB D A G U σ f g q hσ hfg
  have hall := _root_.GlobalTheory.DivSpread.dvd_everywhere R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hSm hGC _ he _ hLB σ q hq hloc
  have hflat : Flat (𝟙_ (Over (Sp R)) ⊗ G).hom := inferInstance
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.Mum.exists_secIsMul_of_germ_dvd R _ (𝟙_ (Over (Sp R)) ⊗ G).hom hflat _ σ q hq hall
  have hEga : GlobalTheory.LN.AlgSt ∧ GlobalTheory.LN.MorAlgSt ∧ GlobalTheory.LN.SecAlgSt ∧ GlobalTheory.LN.PicardZeroDegenerationCondition := GlobalTheory.LN.ega_holds
  obtain ⟨h, hh⟩ := GlobalTheory.CompleteBaseExpansion.exists_expT hEga.2.2.1 hC U 1 τ
  choose f' hf' using fun α => exists_secIsMul (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom q (h α)
  have hσf' : U.ExpT (𝟙_ _) 1 σ f' := _root_.GlobalTheory.UU.expT_scale R (maximalIdeal R) D A G U 1 q σ τ f' h hτ hf' hh
  have hjac : maximalIdeal R ≤ Ideal.jacobson ⊥ := (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hff' : f' = f := GlobalTheory.CompleteBaseExpansion.expT_unique hjac U 1 σ f' f hσf' hσ
  have hflatD : Flat (𝟙_ (Over (Sp R)) ⊗ D.P.A).hom := by
    haveI : IsIso (λ_ D.P.A).hom.left := inferInstanceAs (IsIso ((Over.forget _).mapIso (λ_ D.P.A)).hom)
    haveI : Smooth D.P.A.hom := D.P.isAb.smooth
    rw [← Over.w (λ_ D.P.A).hom]
    infer_instance
  have hhg : h = g := by
    funext α
    have hfa := hf' α
    rw [hff'] at hfa
    exact _root_.GlobalTheory.Mum.secIsMul_cancel R _ _ hflatD _ q hq (f α) (h α) (g α) hfa (hfg α)
  refine ⟨τ, ?_⟩
  rw [← hhg]
  exact hh

end GlobalTheory.SecDiv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedThetaCoefficientSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_translatedThetaCoefficient_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (th : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (χ : D.X) (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), u.IsGen → ∀ b : R, ∃ g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 χ, GlobalTheory.PsiRing.Coef D χ u th g b := by
  first | exact @GlobalTheory.PsiCoefMk.exists_sec_coef | exact GlobalTheory.PsiCoefMk.exists_sec_coef | (intros; apply GlobalTheory.PsiCoefMk.exists_sec_coef <;> assumption)
end

