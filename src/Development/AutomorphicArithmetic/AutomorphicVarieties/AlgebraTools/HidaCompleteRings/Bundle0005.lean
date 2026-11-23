module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.AdmFin
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem isMax_of_le {R : Type*} [CommRing R] (I : Ideal R) [IsArtinianRing (R ⧸ I)]
    (P : Ideal R) [hP : P.IsPrime] (h : I ≤ P) : P.IsMaximal := by
  have h1 : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have h2 : (P.map (Ideal.Quotient.mk I)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have h3 := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (K := P.map (Ideal.Quotient.mk I))
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.2 h] at h3

private theorem art_pow {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] (k : ℕ) : IsArtinianRing (R ⧸ I ^ k) := by
  rw [isArtinianRing_iff_krullDimLE_zero, Ring.krullDimLE_zero_iff]
  intro p hp
  have h0 : I ^ k ≤ p.comap (Ideal.Quotient.mk (I ^ k)) := by
    intro x hx
    simp [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  have h1 : (p.comap (Ideal.Quotient.mk (I ^ k))).IsMaximal :=
    isMax_of_le I _ (Ideal.IsPrime.le_of_pow_le h0)
  have h2 := Ideal.map_comap_of_surjective (Ideal.Quotient.mk (I ^ k)) Ideal.Quotient.mk_surjective p
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk (I ^ k))
    Ideal.Quotient.mk_surjective h1 with h | h
  · exact absurd (h2 ▸ h) hp.ne_top
  · exact h2 ▸ h

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.tateH1FinitenessAtPlacesOver :
    ∀ {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] [IsArtinianRing (R ⧸ I)] [Module.Finite R M], OrdAdm (M := M) I := by
  intro R _ M _ _ _ I _ _ _
  refine ⟨UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.completeFin I, fun k => ?_⟩
  haveI := art_pow I k
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  refine ⟨inferInstance, ?_⟩
  haveI : Module.Finite (R ⧸ I ^ k) (M ⧸ (I ^ k • ⊤ : Submodule R M)) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact isArtinian_of_surjective_algebraMap (R := R ⧸ I ^ k) Ideal.Quotient.mk_surjective
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOrdInt
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I : Ideal R}
    {U e : Module.End R M} (h : IsOrdProj I U e) : ∃ V : Module.End R M, V * U * e = e := by
  have hm : ∀ x ∈ LinearMap.range e, U x ∈ LinearMap.range e := fun x hx => h.bij.mapsTo hx
  have hb : Function.Bijective (U.restrict hm) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (h.bij.injOn x.2 y.2 (congrArg Subtype.val hxy))
    · intro y
      obtain ⟨x, hx, hxy⟩ := h.bij.surjOn y.2
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let E := LinearEquiv.ofBijective _ hb
  let V : Module.End R M := (LinearMap.range e).subtype ∘ₗ E.symm.toLinearMap ∘ₗ e.rangeRestrict
  have hc : ∀ x, U (e x) = e (U x) := fun x => LinearMap.congr_fun h.comm.eq x
  have hV : ∀ z, e z = z → V (U z) = z := by
    intro z hz
    have : e.rangeRestrict (U z) = E ⟨z, z, hz⟩ := Subtype.ext (by
      show e (U z) = U z
      rw [← hc, hz])
    simp only [V, LinearMap.comp_apply, this]
    simp
  refine ⟨V, LinearMap.ext fun x => ?_⟩
  exact hV (e x) (LinearMap.congr_fun h.idem.eq x)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt :
    ∀ {O K : Type*} [CommRing O] [Field K] [Algebra O K] [IsLocalRing O] [IsAlgClosed K] {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M] {U e : Module.End O M}, IsOrdProj (IsLocalRing.maximalIdeal O) U e → LinearMap.range (e.baseChange K) = ⨆ μ ∈ {μ : K | μ ≠ 0 ∧ IsIntegral O μ ∧ IsIntegral O μ⁻¹}, Module.End.maxGenEigenspace (U.baseChange K) μ := by
  intro O K _ _ _ _ _ M _ _ _ U e h
  refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigSum (U.baseChange K) (e.baseChange K) _ ?_ ?_ ?_ ?_
  · show _ * _ = _
    rw [← LinearMap.baseChange_mul, h.idem.eq]
  · show _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, h.comm.eq]
  · intro μ y hy he hU
    obtain ⟨V, hV⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt_inv h
    exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigUnitInt U V e hV μ y hy he hU
  · rintro μ y hy he hU ⟨h0, -, hi⟩
    obtain ⟨n, hn⟩ := h.nil 1
    have hp : ∀ k : ℕ, (U ^ k).baseChange K y = μ ^ k • y := by
      intro k
      induction k with
      | zero => rw [pow_zero, pow_zero, LinearMap.baseChange_one, one_smul, Module.End.one_apply]
      | succ k ih =>
        rw [pow_succ, LinearMap.baseChange_mul, Module.End.mul_apply, hU, map_smul, ih, smul_smul,
          pow_succ']
    refine UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigNilInt (U ^ n * (1 - e)) ?_ (μ ^ n) y hy ?_ (pow_ne_zero n h0) ?_
    · rintro _ ⟨x, rfl⟩
      have := hn x
      rw [pow_one] at this
      exact this
    · rw [LinearMap.baseChange_mul, Module.End.mul_apply, LinearMap.baseChange_sub,
        LinearMap.baseChange_one, LinearMap.sub_apply, he, sub_zero, Module.End.one_apply, hp]
    · rw [← inv_pow]
      exact hi.pow n
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocIdem
section
open IsLocalRing UpperTheory.V.Hi

private theorem coe_mem_smul_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (Y : Submodule A M) (J : Ideal A) (y : Y) :
    (y : M) ∈ J • Y ↔ y ∈ J • (⊤ : Submodule A Y) :=
  (Submodule.mem_smul_top_iff J Y y).symm

private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {t : Module.End A Y} {f : Module.End A M} (h : Restr t f) (n : ℕ) :
    Restr (t ^ n) (f ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih =>
    intro y
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem mem_iSup_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {t : Module.End A Y} {f : Module.End A M} (h : Restr t f) (J : Ideal A) (y : Y) :
    (y : M) ∈ (⨆ n : ℕ, (J • Y).comap (f ^ n)) ↔ ∃ n : ℕ, (t ^ n) y ∈ J • (⊤ : Submodule A Y) := by
  have hf : ∀ x ∈ J • Y, f x ∈ J • Y := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      have := h ⟨z, hz⟩
      simp only at this
      rw [← this]
      exact (t ⟨z, hz⟩).2
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Submodule.add_mem _ ha hb
  have hmono : Monotone fun n : ℕ => (J • Y).comap (f ^ n) := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ hx
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, ← restr_pow h n y, coe_mem_smul_iff]

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∃ e ∈ heckeAlg Y op, IsIdempotentElem e ∧ (∀ y : Y, (y : M) ∈ locPart Y op a ↔ e y = y) ∧ ∀ φ : Module.End A Y, (∀ i t, Restr t (op i) → φ * t = t * φ) → φ * e = e * φ := by
  intro A M ι _ _ _ _ Y _ op a h
  obtain ⟨T, _, _, j, t, -, hr, ht, htop, hfin⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel A M ι Y op h
  haveI : Module.Finite A T := hfin inferInstance inferInstance
  obtain ⟨e, he, h1, h2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a htop
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ x,
      (j : T →+* Module.End A Y) μ x ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    have hμ' : μ ∈ maximalIdeal A • (⊤ : Submodule A T) := by
      rw [Ideal.smul_top_eq_map]
      exact hμ
    intro x
    change j μ x ∈ _
    refine Submodule.smul_induction_on hμ' ?_ ?_
    · intro r hr z _
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro b c hb hc
      rw [map_add (f := _), LinearMap.add_apply]
      exact Submodule.add_mem _ hb hc
  have hchar := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _
    (fun i => t i - algebraMap A T (a i)) e hI he h1 h2
  have hres : ∀ i, Restr (j (t i - algebraMap A T (a i))) (op i - algebraMap A _ (a i)) := by
    intro i y
    rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub,
      ht i y, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
  have hmem : j e ∈ heckeAlg Y op := by
    rw [← hr]
    exact ⟨e, rfl⟩
  refine ⟨j e, hmem, he.map j, fun y => ?_, fun φ hφ => ?_⟩
  · refine Iff.trans ?_ (hchar y).symm
    unfold locPart
    rw [Submodule.mem_inf, and_iff_right y.2, Submodule.mem_iInf]
    refine forall_congr' fun i => ?_
    rw [Submodule.mem_iInf]
    refine forall_congr' fun k => ?_
    exact mem_iSup_iff (hres i) _ y
  · refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hmem ?_
    rintro s ⟨i, hi⟩
    exact hφ i s hi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OneVar
section
open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.oneVar :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Field K] (ι : O →+* K), Function.Injective ι → ∀ (g : PowerSeries O) (Z : Set K), Z.Infinite → (∀ z ∈ Z, ∃ y : PowerSeries O →+* K, (∀ a, y (PowerSeries.C a) = ι a) ∧ y PowerSeries.X = z ∧ y g = 0) → g = 0 := by
  intro O K _ _ _ _ _ ι hι g Z hZ h
  by_contra hg
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, P, U, -, hP, -, hU, hfac⟩ := UpperTheory.V.abelian₂.weier O ϖ hϖ g hg
  have hmon : (P.map ι).Monic := hP.monic.map ι
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hι (by rw [h0, map_zero]))
  refine hmon.ne_zero (Polynomial.eq_zero_of_infinite_isRoot _ (hZ.mono ?_))
  intro z hz
  obtain ⟨y, hyC, hyX, hy0⟩ := h z hz
  have hyP : y (P : PowerSeries O) = (P.map ι).eval z := by
    have e : y.comp Polynomial.coeToPowerSeries.ringHom = Polynomial.eval₂RingHom ι z := by
      apply Polynomial.ringHom_ext
      · intro a
        simp [hyC]
      · simp [hyX]
    have := RingHom.congr_fun e P
    simpa [Polynomial.eval_map] using this
  rw [hfac, map_mul, map_mul, map_pow, hyC, hyP] at hy0
  have hyU : y U ≠ 0 := (hU.map y).ne_zero
  show (P.map ι).IsRoot z
  rcases mul_eq_zero.1 hy0 with h1 | h1
  · rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 (pow_ne_zero m hϖ0)
    · exact h2
  · exact absurd h1 hyU
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.PointEig
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig :
    ∀ {Λ T K M : Type*} [CommRing Λ] [CommRing T] [Algebra Λ T] [Field K] [Algebra Λ K] [AddCommGroup M] [Module Λ M] [Module T M] [IsScalarTower Λ T M] [Module.Finite Λ M] [FaithfulSMul T M] (x : T →ₐ[Λ] K), ∃ y : K ⊗[Λ] M, y ≠ 0 ∧ ∀ t : T, (Algebra.lsmul Λ Λ M t).baseChange K y = x t • y := by
  intro Λ T K M _ _ _ _ _ _ _ _ _ _ _ x
  letI : Algebra T K := x.toRingHom.toAlgebra
  haveI : IsScalarTower Λ T K := IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm
  haveI : Module.Finite T M := Module.Finite.of_restrictScalars_finite Λ T M
  have hne : Nontrivial (K ⊗[T] M) := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe
  let φ : K ⊗[Λ] M →ₗ[K] K ⊗[T] M := TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.restrictScalarsₗ Λ T M (K ⊗[T] M) K).comp
      (TensorProduct.AlgebraTensorModule.mk T K K M))
  have hφt : ∀ (k : K) (m : M), φ (k ⊗ₜ[Λ] m) = k ⊗ₜ[T] m := by
    intro k m
    simp [φ]
  let A : T → Module.End K (K ⊗[Λ] M) := fun t => (Algebra.lsmul Λ Λ M t).baseChange K
  have hA : ∀ (t : T) (k : K) (m : M), A t (k ⊗ₜ[Λ] m) = k ⊗ₜ[Λ] (t • m) := by
    intro t k m
    simp [A]
  have hc : ∀ s t, Commute (A s) (A t) := by
    intro s t
    show A s * A t = A t * A s
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [Module.End.mul_apply, Module.End.mul_apply, hA, hA, hA, hA, smul_comm]
    | add a b ha hb =>
      rw [Module.End.mul_apply, Module.End.mul_apply] at ha hb ⊢
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hφA : ∀ t y, φ (A t y) = x t • φ y := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [hA, hφt, hφt, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), smul_add]
  have hφ0 : φ ≠ 0 := by
    intro h0
    have hall : ∀ p : K ⊗[T] M, p = 0 := by
      intro p
      induction p using TensorProduct.induction_on with
      | zero => rfl
      | tmul k m => rw [← hφt, h0, LinearMap.zero_apply]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨p, hp⟩ := exists_ne (0 : K ⊗[T] M)
    exact hp (hall p)
  exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot A hc (fun t => x t) φ hφ0 hφA
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.QuotOfEig
section
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.quotOfEig :
    ∀ {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (y : Y), y ≠ 0 → (∀ i, A i y = x i • y) → ∃ φ : Module.Dual K Y, φ ≠ 0 ∧ ∀ i z, φ (A i z) = x i * φ z := by
  intro K Y ι _ _ _ _ A hA x y hy hAy
  have hc : ∀ i j, Commute (A i).dualMap (A j).dualMap := by
    intro i j
    show (A i).dualMap * (A j).dualMap = (A j).dualMap * (A i).dualMap
    refine LinearMap.ext fun ψ => LinearMap.ext fun z => ?_
    have h := LinearMap.congr_fun (hA j i).eq z
    simp only [Module.End.mul_apply] at h
    simp only [Module.End.mul_apply, LinearMap.dualMap_apply]
    rw [h]
  have hne : Module.Dual.eval K Y y ≠ 0 := by
    intro h0
    apply hy
    refine (Module.forall_dual_apply_eq_zero_iff K y).mp ?_
    intro ψ
    exact LinearMap.congr_fun h0 ψ
  obtain ⟨ψ, hψ, hψA⟩ := eigOfQuot (fun i => (A i).dualMap) hc x (Module.Dual.eval K Y y) hne (by
    intro i ψ
    simp [LinearMap.dualMap_apply, hAy])
  refine ⟨ψ, hψ, fun i z => ?_⟩
  have := LinearMap.congr_fun (hψA i) z
  simpa [LinearMap.dualMap_apply] using this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.RepEigSum
section
open GlobalTheory.PRep Matrix UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite
open scoped ComplexOrder

private theorem map_smooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type}
    [AddCommGroup N] [Module k N] [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation k G V) (σ : Representation k G N) (hσ : IsSmooth σ) (f : N →ₗ[k] V)
    (hf : ∀ g v, f (σ g v) = ρ g (f v)) (n : N) : f n ∈ smoothPart ρ := by
  let T : Subgroup G :=
    { carrier := {g | ρ g (f n) = f n}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  refine T.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((hσ n).mem_nhds (by simp)) ?_)
  intro g hg
  have hg' : σ g n = n := hg
  show ρ g (f n) = f n
  rw [← hf, hg']

private theorem smoothRep_smooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) : IsSmooth (smoothRep ρ) := by
  intro v
  have h : IsOpen {g : G | ρ g v.1 = v.1} := v.2
  convert h using 3 with g
  exact Subtype.ext_iff

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.repEigSum :
    ∀ {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V] {N : Type} [AddCommGroup N] [Module k N] [CharZero k] [TopologicalSpace G] [IsTopologicalGroup G] (ρ : Representation k G V) (σ : Representation k G N), IsSmooth σ → ∀ (Y : Submodule k V) (K : Subgroup G) (χ : K →* kˣ), IsCompact (K : Set G) → IsOpen {x : K | χ x = 1} → copies ρ Y σ ⊓ eig ρ K χ = ⨆ f : Into ρ Y σ, (eig σ K χ).map f.1 := by
  intro k G V _ _ _ _ N _ _ _ _ _ ρ σ hσ Y K χ hK hχ
  have hE : (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ≤ copies ρ Y σ ⊓ eig ρ K χ := by
    refine iSup_le fun f => ?_
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨Submodule.mem_iSup_of_mem f ⟨n, rfl⟩, fun h => ?_⟩
    rw [← f.2.1, hn h, map_smul]
  refine le_antisymm ?_ hE
  have hC := (repEigCompl σ K χ hσ hK hχ).1
  have hD := (repEigCompl (smoothRep ρ) K χ (smoothRep_smooth ρ) hK hχ).1
  have hT : ∀ f : Into ρ Y σ, ∀ n ∈ twKer σ K χ,
      f.1 n ∈ (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype := by
    intro f
    refine (Submodule.span_le (p := Submodule.comap f.1 ((twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype))).2 ?_
    rintro _ ⟨x, n, rfl⟩
    refine ⟨_, Submodule.subset_span ⟨x, ⟨f.1 n, map_smooth ρ σ hσ f.1 f.2.1 n⟩, rfl⟩, ?_⟩
    rw [map_sub, map_sub, map_smul, map_smul, f.2.1]
    rfl
  have hle : copies ρ Y σ ≤ (⨆ f : Into ρ Y σ, (eig σ K χ).map f.1) ⊔
      (twKer (smoothRep ρ) K χ).map (smoothPart ρ).subtype := by
    refine iSup_le fun f => ?_
    rintro _ ⟨n, rfl⟩
    have hn : n ∈ eig σ K χ ⊔ twKer σ K χ := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hn
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (Submodule.mem_iSup_of_mem f ⟨a, ha, rfl⟩) (hT f t ht)
  rintro v ⟨hv, hv'⟩
  obtain ⟨e, he, _, ⟨t, ht, rfl⟩, rfl⟩ := Submodule.mem_sup.1 (hle hv)
  have ht' : (t : V) ∈ eig ρ K χ := by
    have := Submodule.sub_mem _ hv' (hE he).2
    simpa using this
  have ht'' : t ∈ eig (smoothRep ρ) K χ := fun h => Subtype.ext (ht' h)
  have h0 : t = 0 := (Submodule.disjoint_def.1 hD.disjoint) t ht'' ht
  subst h0
  simpa using he
end

