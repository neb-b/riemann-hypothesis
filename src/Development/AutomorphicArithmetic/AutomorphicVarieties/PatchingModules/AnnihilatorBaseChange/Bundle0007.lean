module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UGenApprox
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.EventuallyTraceInertiaCongruenceOfAdapted
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_push {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : E.map f = D.comap φ) (i : ℕ) (y : MonoidAlgebra R H) :
    f (E.lam i y) = D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  congr 2
  change (D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)).coeff =
    (D.D (Polynomial S) _).coeff
  ext k
  have hcomm : ∀ z : MonoidAlgebra S H,
      MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.mapRingHom H Polynomial.C z) =
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp
  congr 1
  rw [map_sub]
  rw [hcomm]
  simp

theorem UpperTheory.V.Pa.Core.eventually_trace_inertia_congruence_of_adapted :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (w : L.St) (g : L.Gu w) (ga h : Ph0 Λ), g ∈ L.Ju w → πo0 Λ ga = Λ.G.φu w g → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single ga 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m had w g ga h hg hga j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φu_lim V] with N hk hφ
  obtain ⟨g', hg', hgv⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ga : Λ.Ph) (hφ w g)
    (congrArg Subtype.val hga)
  have hm : g' ∈ Ph0 Λ := by
    simpa using mul_mem ga.2 (hV0 hgv)
  let gN : Ph0 Λ := ⟨g', hm⟩
  have e0 : πN0 Λ N gN = (T.GN N).φu w g := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1)), hV 1 _ _ ?_, Or.inl ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ga =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) gN := QuotientGroup.eq.2 hgv
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, e]
  · have e1 : πN0 Λ N gN ∈ (A.A N).rN.Ip w := by
      rw [e0]
      refine ⟨⟨g, hg, rfl⟩, Subgroup.mem_iInf.2 fun i => ?_⟩
      have h1 : G0.φu w g ∈ r.Ip w := by
        rw [had.2]
        exact ⟨g, hg, rfl⟩
      rw [MonoidHom.mem_ker, (A.A N).compat.1 i, MonoidHom.comp_apply, (T.h N).p₀_φu]
      exact Subgroup.mem_iInf.1 h1.2 i
    have hl := lam_push (m.ρ_maps N).1 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single gN 1 - 1))
    simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapRingHom_single, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single] at hl
    exact hl.trans ((A.A N).p.I w _ e1 _)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.MapRingHomSingleMulCharpolyElement
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem lam_dom {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (D : GDet n S G) (φ : H →* G)
    (i : ℕ) (z : MonoidAlgebra S H) : (D.comap φ).lam i z = D.lam i (MonoidAlgebra.mapDomainRingHom S φ z) := by
  unfold GDet.lam
  congr 2
  change (D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)).coeff =
    (D.D (Polynomial S) _).coeff
  ext k
  have hcomm : ∀ z : MonoidAlgebra S H,
      MonoidAlgebra.mapDomainRingHom (Polynomial S) φ (MonoidAlgebra.mapRingHom H Polynomial.C z) =
        MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.mapDomainRingHom S φ z) := by
    intro z
    induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp
  congr 1
  rw [map_sub]
  rw [hcomm]
  simp

private theorem mapDomain_single_mul_charpoly_element {n : ℕ} {S H G : Type} [CommRing S] [Group H] [Group G] (φ : H →* G) (h g : H)
    (U : Fin n → S) : MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single (φ h) 1 * q1El (φ g) U := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn]
  congr 1
  · simp
  · congr 2
    funext i
    rw [Function.comp_apply, map_sub]
    simp

private theorem mapRingHom_single_mul_charpoly_element {n : ℕ} {R S H : Type} [CommRing R] [CommRing S] [Group H] (f : R →+* S) (h g : H)
    (U : Fin n → R) : MonoidAlgebra.mapRingHom H f (MonoidAlgebra.single h 1 * q1El g U) =
      MonoidAlgebra.single h 1 * q1El g fun i => f (U i) := by
  rw [map_mul, q1El, q1El, map_list_prod, List.map_ofFn, MonoidAlgebra.mapRingHom_single, map_one]
  congr 3
  funext i
  simp

theorem UpperTheory.V.Pa.Core.t3Q1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (ph h : Ph0 Λ), πo0 Λ ph = Λ.ph a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q1El ph (W.t.U a)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a ph h hph j
  obtain ⟨V, hV0, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V] with N hk hc
  obtain ⟨g', hg', hgV⟩ := (closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (ph : Λ.Ph) (hc a)
    (congrArg Subtype.val hph)
  have hmem : g' ∈ Ph0 Λ := by
    have := mul_mem ph.2 (hV0 hgV)
    rwa [mul_inv_cancel_left] at this
  let p' : Ph0 Λ := ⟨g', hmem⟩
  have hp' : πN0 Λ N p' = T.ph N a := Subtype.ext hg'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a)), hV 1 _ _ ?_, Or.inr fun x => ?_⟩
  · have e : QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) ph =
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) p' :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hgV)
    rw [mapDomain_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, e]
  · obtain ⟨hD, -, -, hU, -⟩ := m.ρ_maps N
    have e : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 * q1El (T.ph N a) ((A.A N).U a)) := by
      have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q1El p' (W.t.U a))).2 1
      rw [hD, lam_dom, mapRingHom_single_mul_charpoly_element, mapDomain_single_mul_charpoly_element, hp', funext (hU a)] at h1
      exact h1.symm
    rw [e]
    exact (A.m N).rel1 a _ x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.MapRingHomSingleMulPartialCharpolyElement
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem mapDomain_partial_charpoly_power_zero {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (φ : G →* H) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single (φ h) 1 * q2El (φ ph) (φ ta) u i y := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapDomainRingHom R φ (MonoidAlgebra.single g c) =
      MonoidAlgebra.single (φ g) c := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem mapRingHom_single_mul_partial_charpoly_element {n : ℕ} {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (h ph ta : G)
    (u : Fin n → R) (i : Fin n) (y : R) :
    MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single h 1 * q2El ph ta u i y) =
      MonoidAlgebra.single h 1 * q2El ph ta (fun k => f (u k)) i (f y) := by
  have hs : ∀ (g : G) (c : R), MonoidAlgebra.mapRingHom G f (MonoidAlgebra.single g c) =
      MonoidAlgebra.single g (f c) := fun g c => by simp
  simp only [q2El, map_mul, map_sub, map_one, map_list_prod, List.map_ofFn, hs]
  congr 4
  funext k
  by_cases hk : k = i
  · simp only [Function.comp_apply, if_pos hk, map_one]
  · simp only [Function.comp_apply, if_neg hk, map_sub, hs, map_one]

private theorem comap_tr {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H] (D : GDet n R H) (φ : G →* H)
    (z : MonoidAlgebra R G) : (D.comap φ).tr z = D.tr (MonoidAlgebra.mapDomainRingHom R φ z) := by
  have hc : (D.comap φ).chi z = D.chi (MonoidAlgebra.mapDomainRingHom R φ z) := by
    change D.D _ (MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _) = D.D _ _
    congr 1
    rw [map_sub]
    congr 1
    · simp
    · induction z using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), ha, hb]
      | single g r => simp
  simp only [GDet.tr, GDet.lam, hc]

theorem UpperTheory.V.Pa.Core.t3Q2 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (a : Fin T.q) (i : Fin n) (ph ta h : Ph0 Λ), πo0 Λ ph = Λ.ph a → πo0 Λ ta = Λ.ta a → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph ta (W.t.U a) i (W.t.y a i)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ a i ph ta h hph hta j
  obtain ⟨V, hV0, hV⟩ := UpperTheory.V.Pa.Core.phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.ph_lim V, Λ.ta_lim V] with N hk h1 h2
  have lift : ∀ (g : Ph0 Λ) (x : (T.GN N).G₀) (b : Λ.G.G₀), Close (Λ.π N) Λ.πo V.toSubgroup (x : (T.GN N).Γ) (b : Λ.G.Γ) →
      πo0 Λ g = b → ∃ g' : Ph0 Λ, πN0 Λ N g' = x ∧
        QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g = QuotientGroup.mk' (V.toSubgroup.subgroupOf (Ph0 Λ)) g' := by
    intro g x b hc hg
    obtain ⟨g', e, hv⟩ := (UpperTheory.V.Pa.Core.closeLift _ _ _ (Λ.π N) Λ.πo V.toSubgroup hk).1 _ _ (g : Λ.Ph) hc
      (congrArg Subtype.val hg)
    have hm : g' ∈ Ph0 Λ := by
      have := (Ph0 Λ).mul_mem g.2 (hV0 hv)
      rwa [mul_inv_cancel_left] at this
    exact ⟨⟨g', hm⟩, Subtype.ext e, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 hv)⟩
  obtain ⟨ph', e1, q1⟩ := lift ph _ _ (h1 a) hph
  obtain ⟨ta', e2, q2⟩ := lift ta _ _ (h2 a) hta
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i)), ?_, Or.inr fun x => ?_⟩
  · apply hV 1
    rw [mapDomain_partial_charpoly_power_zero, mapDomain_partial_charpoly_power_zero, q1, q2]
  · obtain ⟨hD, -, -, hU, hy⟩ := m.ρ_maps N
    have key : m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))) =
        (A.A N).p.D.tr (MonoidAlgebra.single (πN0 Λ N h) 1 *
          q2El (T.ph N a) (T.ta N a) ((A.A N).U a) i ((A.A N).s (MvPowerSeries.X (a, i)))) := by
      have h3 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
        (MonoidAlgebra.single h 1 * q2El ph' ta' (W.t.U a) i (W.t.y a i))).2 1
      refine h3.symm.trans ?_
      rw [hD, mapRingHom_single_mul_partial_charpoly_element, hy a i, funext (hU a)]
      refine (comap_tr _ _ _).trans ?_
      rw [mapDomain_partial_charpoly_power_zero, e1, e2]
    rw [key]
    exact (A.m N).rel2 a i _ x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedTraceLocalCharPolyApproxAnnihilated
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem gDet_chi_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).chi (MonoidAlgebra.mapRingHom G f x) = (D.chi x).map f := by
  unfold GDet.chi GDet.map
  dsimp only
  letI : Algebra R (Polynomial R') := ((algebraMap R' (Polynomial R')).comp f).toAlgebra
  let g : Polynomial R →ₐ[R] Polynomial R' :=
    { Polynomial.mapRingHom f with
      commutes' := fun c => by
        simp [RingHom.algebraMap_toAlgebra, Polynomial.algebraMap_apply] }
  have h := D.nat (Polynomial R) (Polynomial R') g
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C x)
  refine Eq.trans ?_ h
  congr 1
  rw [map_sub]
  congr 1
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Polynomial.mapRingHom]
  · ext a
    simp [g, MonoidAlgebra.mapRingHom, Polynomial.mapRingHom]

private theorem gDet_tr_map_mapRingHom {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G]
    (D : GDet n R G) (f : R →+* R') (x : MonoidAlgebra R G) :
    (D.map f).tr (MonoidAlgebra.mapRingHom G f x) = f (D.tr x) := by
  unfold GDet.tr GDet.lam
  rw [gDet_chi_map_mapRingHom, Polynomial.coeff_map]
  simp

private theorem gDet_tr_comap_eq_tr_mapDomainRingHom {n : ℕ} {R G H : Type} [CommRing R] [Group G] [Group H]
    (D : GDet n R G) (φ : H →* G) (x : MonoidAlgebra R H) :
    (D.comap φ).tr x = D.tr (MonoidAlgebra.mapDomainRingHom R φ x) := by
  unfold GDet.tr GDet.lam GDet.chi GDet.comap
  dsimp only
  rw [MonoidHom.comp_apply]
  congr 3
  congr 1
  show MonoidAlgebra.mapDomainRingHom (Polynomial R) φ _ = _
  rw [map_sub]
  congr 1
  · simp [MonoidAlgebra.mapDomainRingHom_apply]
  · ext a
    simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapRingHom]
    rw [Finsupp.mapDomain_mapRange _ _ _ _ (fun a b => Polynomial.C_add)]
    simp

theorem UpperTheory.V.Pa.Core.patched_trace_local_charPoly_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), Adapted T (r := r) → ∀ (v : L.Vl) (g : Fin n → L.Gv v) (ga : Fin n → Ph0 Λ) (h : Ph0 Λ), (∀ i, πo0 Λ (ga i) = Λ.G.φ v (g i)) → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i => MonoidAlgebra.single (ga i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hT v g ga h hga j
  obtain ⟨V, hVle, hsees⟩ := phSees l L G0 T Λ n O r B u J D A W j
  filter_upwards [Λ.ker_lim V, Λ.φ_lim V] with N hker hφ
  have hπo : ∀ i, Λ.πo (ga i) = ((Λ.G.φ v (g i) : Λ.G.G₀) : Λ.G.Γ) := fun i =>
    congrArg Subtype.val (hga i)
  have lift : ∀ i, ∃ x : Λ.Ph, Λ.π N x = (((T.GN N).φ v (g i) : (T.GN N).G₀) : (T.GN N).Γ) ∧
      (ga i : Λ.Ph)⁻¹ * x ∈ (V.toOpenSubgroup : Subgroup Λ.Ph) := fun i =>
    (closeLift _ _ _ (Λ.π N) Λ.πo _ hker).1 _ _ (ga i) (hφ v (g i)) (hπo i)
  choose x hx1 hx2 using lift
  have hmem : ∀ i, x i ∈ Ph0 Λ := fun i => by
    have := (Ph0 Λ).mul_mem (ga i).2 (hVle (hx2 i))
    simpa using this
  let gb : Fin n → Ph0 Λ := fun i => ⟨x i, hmem i⟩
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (List.ofFn fun i =>
    MonoidAlgebra.single (gb i) (1 : W.R) - MonoidAlgebra.single 1 ((W.t.ψ v i (g i) : W.Rˣ) : W.R)).prod), ?_, Or.inl ?_⟩
  · refine hsees 1 _ _ ?_
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single]
    congr 2
    congr 1
    funext i
    congr 2
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact hx2 i
  · show (m.ρ N).toRingHom _ = 0
    rw [← gDet_tr_map_mapRingHom, (m.ρ_maps N).1, gDet_tr_comap_eq_tr_mapDomainRingHom]
    refine Eq.trans ?_ ((A.A N).p.Ord v g (πN0 Λ N h))
    congr 1
    unfold GFrame.oEl
    simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, map_sub, MonoidAlgebra.mapDomainRingHom_apply,
      MonoidAlgebra.mapDomain_single, MonoidAlgebra.mapRingHom_single, map_one]
    congr 2
    congr 1
    funext i
    rw [← (m.ρ_maps N).2.1 v i]
    congr 2
    exact Subtype.ext (hx1 i)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedTraceSingleMulSubOneApproxAnnihilated
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem tr_zero {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (hn : 1 ≤ n) : D.tr 0 = 0 := by
  have h1 : (MonoidAlgebra.single (1 : G) (Polynomial.X : Polynomial A))
      = (Polynomial.X : Polynomial A) • (1 : MonoidAlgebra (Polynomial A) G) := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single', mul_one]
  have hchi : D.chi 0 = Polynomial.X ^ n := by
    simp only [GDet.chi, map_zero, sub_zero]
    rw [h1, D.homog, map_one, mul_one]
  simp only [GDet.tr, GDet.lam, hchi, Polynomial.coeff_X_pow]
  rw [if_neg (by omega)]
  simp

theorem UpperTheory.V.Pa.Core.patched_trace_single_mul_sub_one_approx_annihilated :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W), 1 ≤ n → Adapted T (r := r) → ∀ (h k : Ph0 Λ), πo0 Λ k = 1 → ∀ j : ℕ, ∀ᶠ N in (Λ.U : Filter ℕ), ∃ a' : W.R, W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1)) - a' ∈ maximalIdeal W.R ^ j ∧ (m.ρ N a' = 0 ∨ ∀ x : (A.A N).M, (fEl (T.Nq N) (A.A N).U * m.ρ N a') ^ A.ex • x = 0) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m hn _ h k hk j
  obtain ⟨V, hVle, hV⟩ := phSees l L G0 T Λ n O r B u J D A W j
  refine (Λ.ker_lim V).mono fun N hN => ?_
  have hk1 : Λ.πo (k : Λ.Ph) = 1 := congrArg Subtype.val hk
  have hkmem : (k : Λ.Ph) ∈ (Λ.π N).ker ⊔ (V.toOpenSubgroup : Subgroup Λ.Ph) := by
    rw [hN]
    exact Subgroup.mem_sup_left hk1
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.1 hkmem
  have haPh : a ∈ Ph0 Λ := by
    have : a = (k : Λ.Ph) * b⁻¹ := by rw [← hab]; group
    rw [this]
    exact (Ph0 Λ).mul_mem k.2 ((Ph0 Λ).inv_mem (hVle hb))
  set k' : Ph0 Λ := ⟨a, haPh⟩ with hk'
  refine ⟨W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)), ?_, Or.inl ?_⟩
  · have hq : (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))) k
        = QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ)) k' := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : ((k⁻¹ * k' : Ph0 Λ) : Λ.Ph) = b⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hk']
        rw [← hab]
        group
      rw [this]
      exact inv_mem hb
    have hxy : (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k 1 - 1))
        = (MonoidAlgebra.mapDomainRingHom W.R
          (QuotientGroup.mk' ((V.toOpenSubgroup : Subgroup Λ.Ph).subgroupOf (Ph0 Λ))))
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
      simp only [map_mul, map_sub, map_one, MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, hq]
    exact hV 1 _ _ hxy
  · have hπ : πN0 Λ N k' = 1 := Subtype.ext (MonoidHom.mem_ker.1 ha)
    have hmaps := (m.ρ_maps N).1
    have h1 := ((UpperTheory.V.CA.d_gmap W.t.D).2.2.1 (m.ρ N).toRingHom
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))).2 1
    have hy : (MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
        (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
        = MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1) := by
      simp
    have h2 := (comap_lam n _ _ _ (πN0 Λ N) (A.A N).p.D).2.2.1
      (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))
    have h3 : (MonoidAlgebra.mapDomainRingHom (A.A N).R (πN0 Λ N))
        (MonoidAlgebra.single h (1 : (A.A N).R) * (MonoidAlgebra.single k' (1 : (A.A N).R) - 1)) = 0 := by
      rw [map_mul, map_sub, map_one]
      simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single, hπ]
      rw [← MonoidAlgebra.one_def, sub_self, mul_zero]
    calc m.ρ N (W.t.D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)))
        = (m.ρ N).toRingHom (W.t.D.lam 1 (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := rfl
      _ = (W.t.D.map (m.ρ N).toRingHom).lam 1 ((MonoidAlgebra.mapRingHom (Ph0 Λ) (m.ρ N).toRingHom)
          (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1))) := h1.symm
      _ = ((A.A N).p.D.comap (πN0 Λ N)).tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single k' 1 - 1)) := by
          rw [hy, hmaps]
          rfl
      _ = 0 := by rw [h2, h3]; exact tr_zero _ hn
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrGen
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.rrGen :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A), GenBy O ({b | ∃ i g, b = W.t.D.lam i (MonoidAlgebra.single g 1)} ∪ {b | ∃ v i g, b = ((W.t.ψ v i g : W.Rˣ) : W.R)} ∪ {b | ∃ j i, b = W.t.U j i ∨ b = W.t.y j i} ∪ {W.t.s}) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W N x
  refine UpperTheory.V.CA.u_gen O W.R _ (fun R' _ _ _ f f' h => ?_) N x
  refine UpperTheory.V.Pa.Core.rrExt l L G0 T Λ n O r B u J D A W R' f f' (fun i g => h _ ?_) (fun v i g => h _ ?_)
    (h _ ?_) (fun j i => h _ ?_) (fun j i => h _ ?_)
  · exact .inl (.inl (.inl ⟨i, g, rfl⟩))
  · exact .inl (.inl (.inr ⟨v, i, g, rfl⟩))
  · exact .inr rfl
  · exact .inl (.inr ⟨j, i, .inl rfl⟩)
  · exact .inl (.inr ⟨j, i, .inr rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpoCo
section
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

theorem UpperTheory.V.Pa.Core.spoCo :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T), Adapted T (r := r) → (IsCO O (Spo A) ∧ Module.Free B (Spo A) ∧ Module.Finite B (Spo A) ∧ Algebra.adjoin B (Set.range fun p : Fin T.q × Fin n => (Sp.u _ _ p.1 p.2 : Spo A)) = ⊤) ∧ ∀ N, IsCO O (SpAt u (fun j => (T.h N).p₀ (T.ph N j)) A.ut) := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A hA
  refine ⟨spCo O B T.q n _ _ fun j => chiRes l G0.frame n O r B u (T.sg j) (A.ut j) (A.ut_res j), fun N => ?_⟩
  exact (spCo O B T.q n _ _ fun j => chiRes l G0.frame n O r B u ((T.h N).p₀ (T.ph N j)) (A.ut j) fun i => by
    have h1 := hA.1 ((T.h N).p₀ (T.ph N j) * (T.sg j)⁻¹) (T.ph_H N j) i
    have h2 := ((r.chib i).map_mul _ _).symm.trans h1
    have h3 := (congrArg (r.chib i ((T.h N).p₀ (T.ph N j)) * ·) ((r.chib i).map_inv (T.sg j))).symm.trans h2
    exact (A.ut_res j i).trans (congrArg Units.val (mul_inv_eq_one.1 h3).symm)).1
end

