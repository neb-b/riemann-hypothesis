module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.ExistsOfInLat
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

section

variable {L F : Type} [Field L] [NumberField L] [Field F] [NumberField F] [Algebra L F] {J : Type}

private theorem coe_add' (y y' : J → 𝓞 F) :
    (fun j => ((y + y') j : F)) = (fun j => (y j : F)) + fun j => (y' j : F) := by
  funext j
  simp

end

theorem UpperTheory.V.ZK.Cl.cInt :
    UpperTheory.V.ZK.Cl.CInt := by
  intro L F _ _ _ _ _ J _ b
  classical
  refine ⟨inferInstance, ?_, ?_⟩
  · haveI : Module.FinitePresentation (𝓞 L) (J → 𝓞 F) := Module.finitePresentation_of_finite _ _
    exact Module.Flat.projective_of_finitePresentation
  have hadd : ∀ u w : 𝓞 F, ((u + w : 𝓞 F) : F) = (u : F) + (w : F) := fun u w => by simp
  have hmul : ∀ u w : 𝓞 F, ((u * w : 𝓞 F) : F) = (u : F) * (w : F) := fun u w => by simp
  have hone1 : ((1 : 𝓞 F) : F) = 1 := by simp
  have hint : ∀ y : J → F, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔ ∀ j, ∃ a : 𝓞 F, (a : F) = y j := by
    intro y
    constructor
    · intro hy j
      obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F (y j)
        (fun P => by simpa using hy j P)
      exact ⟨a, ha⟩
    · intro hy j P
      obtain ⟨a, ha⟩ := hy j
      rw [← ha]
      simpa using HeightOneSpectrum.valuation_le_one (K := F) P a
  let φ : GG L F J → (J → 𝓞 F) → (J → 𝓞 F) := fun g x j =>
    if hx : ∃ a : 𝓞 F, (a : F) = g (fun i => (x i : F)) j then hx.choose else 0
  have hφ : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x j,
      ((φ g x j : 𝓞 F) : F) = g (fun i => (x i : F)) j := by
    intro g hg x j
    have hg' : ∀ y, InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) y ↔
        InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (g y) := hg
    have h1 : InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ) (fun i => (x i : F)) :=
      (hint _).2 (fun i => ⟨x i, rfl⟩)
    have h2 := (hint _).1 ((hg' _).1 h1) j
    simp only [φ, dif_pos h2]
    exact h2.choose_spec
  have hφf : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x,
      (fun i => ((φ g x i : 𝓞 F) : F)) = g (fun i => (x i : F)) := fun g hg x => funext (hφ g hg x)
  have hcomp : ∀ g1 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)),
      ∀ g2 ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x, φ g1 (φ g2 x) = φ (g1 * g2) x := by
    intro g1 hg1 g2 hg2 x
    funext j
    apply RingOfIntegers.ext
    rw [hφ g1 hg1, hφf g2 hg2, hφ _ (Subgroup.mul_mem _ hg1 hg2)]
    rfl
  have hone : ∀ x, φ 1 x = x := by
    intro x
    funext j
    apply RingOfIntegers.ext
    rw [hφ 1 (Subgroup.one_mem _)]
    rfl
  have hsmul : ∀ (a : 𝓞 L) (z : 𝓞 F), ((a • z : 𝓞 F) : F) = (a : L) • (z : F) := by
    intro a z
    rw [Algebra.smul_def, Algebra.smul_def]
    rfl
  have hlin : ∀ g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)), ∀ x y,
      φ g (x + y) = φ g x + φ g y ∧ ∀ a : 𝓞 L, φ g (a • x) = a • φ g x := by
    intro g hg x y
    constructor
    · funext j
      apply RingOfIntegers.ext
      rw [Pi.add_apply, hadd, hφ g hg, hφ g hg, hφ g hg, coe_add', map_add (f := _), Pi.add_apply]
    · intro a
      funext j
      apply RingOfIntegers.ext
      have e : (fun i => ((a • x) i : F)) = (a : L) • fun i => (x i : F) := by
        funext i
        rw [Pi.smul_apply, Pi.smul_apply, hsmul]
      rw [Pi.smul_apply, hsmul, hφ g hg, hφ g hg, e, map_smul, Pi.smul_apply]
  let E : ∀ g : GG L F J, g ∈ StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ)) →
      ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F) := fun g hg =>
    { toFun := φ g
      invFun := φ g⁻¹
      map_add' := fun x y => (hlin g hg x y).1
      map_smul' := fun a x => (hlin g hg x x).2 a
      left_inv := by
        intro x
        show φ g⁻¹ (φ g x) = x
        rw [hcomp _ (Subgroup.inv_mem _ hg) _ hg, inv_mul_cancel, hone]
      right_inv := by
        intro x
        show φ g (φ g⁻¹ x) = x
        rw [hcomp _ hg _ (Subgroup.inv_mem _ hg), mul_inv_cancel, hone] }
  let α : ↥((StabP L (InLat (0 : J → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf (GLoc F J b)) →*
      ((J → 𝓞 F) ≃ₗ[𝓞 L] J → 𝓞 F) :=
    { toFun := fun h => E _ (Subgroup.mem_subgroupOf.1 h.2)
      map_one' := by
        apply LinearEquiv.ext
        intro x
        exact hone x
      map_mul' := by
        intro h1 h2
        apply LinearEquiv.ext
        intro x
        exact (hcomp _ (Subgroup.mem_subgroupOf.1 h1.2) _ (Subgroup.mem_subgroupOf.1 h2.2) x).symm }
  refine ⟨α, ?_⟩
  intro k _ r hr μ hμ
  have hfix : ∀ (σ : Gal(F/L)) (a : 𝓞 L), actO σ (algebraMap (𝓞 L) (𝓞 F) a) = algebraMap (𝓞 L) (𝓞 F) a := by
    intro σ a
    apply RingOfIntegers.ext
    show σ ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F)
    have e : ((algebraMap (𝓞 L) (𝓞 F) a : 𝓞 F) : F) = algebraMap L F (a : L) := by
      have := hsmul a 1
      simpa [Algebra.smul_def] using this
    rw [e]
    exact σ.commutes _
  let π : (J → 𝓞 F) →+ (Gal(F/L) × J → k) :=
    { toFun := fun x p => r (actO p.1 (x p.2))
      map_zero' := by
        funext p
        simp
      map_add' := by
        intro x y
        funext p
        simp }
  have huniq : ∀ (y : F) (u u' : k), ResF r y u → ResF r y u' → u = u' := by
    rintro y u u' ⟨a, c, hc, hyc, hu⟩ ⟨a', c', hc', hyc', hu'⟩
    have e : a * c' = a' * c := by
      apply RingOfIntegers.ext
      rw [hmul, hmul, ← hyc, ← hyc']
      ring
    have e2 := congrArg r e
    rw [map_mul, map_mul, hu, hu'] at e2
    have hcc : r c * r c' ≠ 0 := mul_ne_zero hc hc'
    apply mul_right_cancel₀ hcc
    linear_combination e2
  have hR : ∀ z : J → 𝓞 F, RedV L r (fun i => (z i : F)) (π z) := by
    intro z σ j
    refine ⟨actO σ (z j), 1, by simp, ?_, ?_⟩
    · rw [hone1, mul_one]
      rfl
    · show r (actO σ (z j)) = r (actO σ (z j)) * r 1
      rw [map_one, mul_one]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · intro a x
    funext p
    show r (actO p.1 ((a • x) p.2)) = (r.comp (algebraMap (𝓞 L) (𝓞 F))) a • r (actO p.1 (x p.2))
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, hfix, smul_eq_mul]
    rfl
  · intro v
    choose a ha using fun j => hr.1 (fun σ => v (σ, j))
    exact ⟨a, funext fun p => ha p.2 p.1⟩
  · intro x hx
    have hj : ∀ j, x j ∈ Ideal.map (algebraMap (𝓞 L) (𝓞 F)) (RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) :=
      fun j => hr.2 (x j) (fun σ => congrFun hx (σ, j))
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro j _
    have h1 : x j ∈ ((RingHom.ker (r.comp (algebraMap (𝓞 L) (𝓞 F)))) • ⊤ : Submodule (𝓞 L) (𝓞 F)) := by
      rw [Ideal.smul_top_eq_map]
      exact hj j
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.single (𝓞 L) (fun _ : J => 𝓞 F) j) h1
    rw [Submodule.map_smul'', LinearMap.single_apply] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  · intro h x
    funext p
    have hloc : InLoc b (fun i => (x i : F)) := by
      intro j P _
      exact HeightOneSpectrum.valuation_le_one (K := F) P (x j)
    have hred := hμ (h : ↥(GLoc F J b)) (fun i => (x i : F)) (π x) hloc (hR x)
    have hα := hR (α h x)
    have hc : (fun i => ((α h x i : 𝓞 F) : F)) = ((h : ↥(GLoc F J b)) : GG L F J) (fun i => (x i : F)) :=
      hφf _ (Subgroup.mem_subgroupOf.1 h.2) x
    rw [hc] at hα
    exact huniq _ _ _ (hα p.1 p.2) (hred p.1 p.2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.MemPowEqv
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem mem_eqv {R : Type} [CommRing R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) :
    y ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ↔ e.symm y ∈ P.asIdeal := Iff.rfl

private theorem mem_pow_eqv {R : Type} [CommRing R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) (n : ℕ) :
    e y ∈ (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal ^ n ↔ y ∈ P.asIdeal ^ n := by
  have h : (HeightOneSpectrum.equivOfRingEquiv e P).asIdeal = Ideal.map (e : R →+* R) P.asIdeal := by
    rw [Ideal.map_comap_of_equiv]
    rfl
  rw [h, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  simp

private theorem intVal_eqv {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (P : HeightOneSpectrum R) (y : R) :
    (HeightOneSpectrum.equivOfRingEquiv e P).intValuation (e y) = P.intValuation y := by
  set Q := HeightOneSpectrum.equivOfRingEquiv e P
  have key : ∀ n : ℕ, Q.intValuation (e y) ≤ WithZero.exp (-(n : ℤ)) ↔
      P.intValuation y ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
      Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
      Ideal.span_singleton_le_iff_mem]
    exact mem_pow_eqv e P y n
  by_cases hy : y = 0
  · simp [hy]
  have hey : e y ≠ 0 := by simpa using hy
  have form : ∀ (v : HeightOneSpectrum R) (r : R), r ≠ 0 →
      ∃ m : ℕ, v.intValuation r = WithZero.exp (-(m : ℤ)) :=
    fun v r hr => ⟨_, by rw [HeightOneSpectrum.intValuation_def, if_neg hr]⟩
  obtain ⟨m1, h1⟩ := form Q _ hey
  obtain ⟨m2, h2⟩ := form P _ hy
  rw [h1, h2] at key ⊢
  have a := (key m1).1 le_rfl
  have b := (key m2).2 le_rfl
  rw [WithZero.exp_le_exp] at a b
  have : m1 = m2 := by omega
  rw [this]

theorem UpperTheory.V.ZK.Cl.cAct :
    UpperTheory.V.ZK.Cl.CAct := by
  intro L F _ _ _ _ _
  have val : ∀ (σ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) (x : F),
      HeightOneSpectrum.valuation F (actP σ P) (σ x) = HeightOneSpectrum.valuation F P x := by
    intro σ P x
    obtain ⟨p, q, -, hpq⟩ := IsFractionRing.div_surjective (𝓞 F) x
    have hpq' : (p : F) / q = x := hpq
    have hσ : ∀ a : 𝓞 F, σ (a : F) = ((RingOfIntegers.mapRingEquiv σ.toRingEquiv a : 𝓞 F) : F) :=
      fun a => by rw [RingOfIntegers.mapRingEquiv_apply]; rfl
    rw [← hpq', map_div₀, hσ, hσ, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    unfold actP
    rw [intVal_eqv, intVal_eqv]
  have sym : ∀ (σ : Gal(F/L)) (y : 𝓞 F),
      (((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y : 𝓞 F) : F) = σ.symm (y : F) := by
    intro σ y
    apply σ.injective
    rw [AlgEquiv.apply_symm_apply]
    have := RingOfIntegers.mapRingEquiv_apply σ.toRingEquiv
      ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this.symm
  have memA : ∀ (σ : Gal(F/L)) (P : HeightOneSpectrum (𝓞 F)) (y : 𝓞 F),
      y ∈ (actP σ P).asIdeal ↔ (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y ∈ P.asIdeal :=
    fun σ P y => mem_eqv _ P y
  refine ⟨val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ τ P
    apply HeightOneSpectrum.ext
    ext y
    rw [memA, memA, memA]
    have h : (((RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm y : 𝓞 F) : F) =
        (((RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
          ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y) : 𝓞 F) : F) := by
      rw [sym, sym, sym]
      rfl
    rw [show (RingOfIntegers.mapRingEquiv (σ * τ).toRingEquiv).symm y =
        (RingOfIntegers.mapRingEquiv τ.toRingEquiv).symm
          ((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm y) from by exact_mod_cast h]
  · intro P
    apply HeightOneSpectrum.ext
    ext y
    rw [memA]
    have h : (((RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm y : 𝓞 F) : F) =
        (y : F) := by
      rw [sym]
      rfl
    rw [show (RingOfIntegers.mapRingEquiv (1 : Gal(F/L)).toRingEquiv).symm y = y from by
      exact_mod_cast h]
  · intro σ P b
    rw [memA]
    have h1 : algebraMap (𝓞 L) F b = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 F) F]
    have h2 : algebraMap (𝓞 L) F b = algebraMap L F (b : L) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 L) L F]
    have hc : ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) = algebraMap L F (b : L) := by
      rw [← h1, h2]
    have h : (((RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm (algebraMap (𝓞 L) (𝓞 F) b) : 𝓞 F) : F)
        = ((algebraMap (𝓞 L) (𝓞 F) b : 𝓞 F) : F) := by
      rw [sym, hc, AlgEquiv.commutes]
    rw [show (RingOfIntegers.mapRingEquiv σ.toRingEquiv).symm (algebraMap (𝓞 L) (𝓞 F) b) =
        algebraMap (𝓞 L) (𝓞 F) b from by exact_mod_cast h]
  · intro σ P α
    unfold ordP
    have : ((actU σ α : Fˣ) : F) = σ (α : F) := rfl
    rw [this, val]
  · intro P α β
    unfold ordP
    rw [Units.val_mul, map_mul, WithZero.log_mul (by simp) (by simp)]
    ring
  · intro P α n
    unfold ordP
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, WithZero.log_zpow, smul_eq_mul]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.RedApplyMap
section
open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

private theorem red_apply_map {R k : Type} [CommRing R] [Field k] (r : R →+* k) (N : ℕ) (g : GL (Fin N) R)
    (x : Fin N → R) : red r N g (r ∘ x) = r ∘ (g : Matrix (Fin N) (Fin N) R).mulVec x := by
  funext j
  simp [red, RingHom.map_mulVec]

private theorem exists_ibar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (hr : Function.Surjective r) (i : M →ₗ[R] (Fin N → R)) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) (h2 : Function.Surjective π)
    (h3 : ∀ x, π x = 0 → x ∈ RingHom.ker r • (⊤ : Submodule R M)) :
    ∃ ib : V →ₗ[k] (Fin N → k), ∀ x, ib (π x) = r ∘ i x := by
  have key : ∀ z ∈ RingHom.ker r • (⊤ : Submodule R M), r ∘ i z = 0 := by
    intro z hz
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha m _
      funext j
      simp [(RingHom.mem_ker).1 ha]
    · intro z w hz hw
      funext j
      have e₁ := congrFun hz j
      have e₂ := congrFun hw j
      simp only [Function.comp_apply, Pi.zero_apply] at e₁ e₂ ⊢
      rw [map_add (f := _), Pi.add_apply, map_add (f := _), e₁, e₂, add_zero]
  have wd : ∀ x y : M, π x = π y → r ∘ i x = r ∘ i y := by
    intro x y hxy
    have hz : x - y ∈ RingHom.ker r • (⊤ : Submodule R M) := h3 _ (by rw [map_sub, hxy, sub_self])
    have e := key _ hz
    funext j
    have ej := congrFun e j
    simp only [map_sub, Function.comp_apply, Pi.sub_apply, Pi.zero_apply] at ej
    exact sub_eq_zero.1 ej
  choose pre hpre using h2
  refine ⟨{ toFun := fun v => r ∘ i (pre v), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro v w
    have e : π (pre (v + w)) = π (pre v + pre w) := by rw [map_add (f := _), hpre, hpre, hpre]
    rw [wd _ _ e, map_add (f := _)]
    funext j
    simp
  · intro c v
    obtain ⟨a, rfl⟩ := hr c
    have e : π (pre (r a • v)) = π (a • pre v) := by rw [h1, hpre, hpre]
    rw [wd _ _ e, map_smul]
    funext j
    simp
  · intro x
    exact wd _ _ (hpre _)

private theorem exists_sbar {R k M V : Type} [CommRing R] [Field k] [AddCommGroup M] [Module R M] [AddCommGroup V]
    [Module k V] {N : ℕ} (r : R →+* k) (s : (Fin N → R) →ₗ[R] M) (π : M →+ V)
    (h1 : ∀ a x, π (a • x) = r a • π x) :
    ∃ sb : (Fin N → k) →ₗ[k] V, ∀ x, sb (r ∘ x) = π (s x) := by
  refine ⟨(Pi.basisFun k (Fin N)).constr k (fun j => π (s (Pi.single j 1))), fun x => ?_⟩
  rw [Module.Basis.constr_apply_fintype]
  have hx : x = ∑ j, x j • (Pi.single j 1 : Fin N → R) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hx, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, h1]
  simp

theorem UpperTheory.V.ZK.Cl.cFree :
    UpperTheory.V.ZK.Cl.CFree := by
  intro R _ M _ _ _ _ H _ α
  obtain ⟨N, s, hs⟩ := Module.Finite.exists_fin' R M
  obtain ⟨i, hi⟩ := Module.projective_lifting_property s LinearMap.id hs
  have hsi : ∀ y, s (i y) = y := fun y => LinearMap.congr_fun hi y
  let E : H →* Module.End R (Fin N → R) :=
    { toFun := fun h => i ∘ₗ (α h).toLinearMap ∘ₗ s + (LinearMap.id - i ∘ₗ s)
      map_one' := LinearMap.ext fun x => by simp
      map_mul' := fun g h => LinearMap.ext fun x => by
        simp [hsi, map_mul, Module.End.mul_apply] }
  let lam : H →* GL (Fin N) R :=
    (Units.map (LinearMap.toMatrixAlgEquiv' :
      Module.End R (Fin N → R) ≃ₐ[R] Matrix (Fin N) (Fin N) R).toMonoidHom).comp E.toHomUnits
  refine ⟨N, lam, ?_⟩
  intro k _ r hr V _ _ π μ h1 h2 h3 h4
  obtain ⟨ib, hib⟩ := exists_ibar r hr i π h1 h2 h3
  obtain ⟨sb, hsb⟩ := exists_sbar r s π h1
  have sbib : ∀ v, sb (ib v) = v := by
    intro v
    obtain ⟨x, rfl⟩ := h2 v
    rw [hib, hsb, hsi]
  let f : (V × LinearMap.ker sb) →ₗ[k] (Fin N → k) := LinearMap.coprod ib (LinearMap.ker sb).subtype
  have hfa : ∀ w : V × LinearMap.ker sb, f w = ib w.1 + (w.2 : Fin N → k) := fun w => rfl
  have hf : Function.Bijective f := by
    constructor
    · intro w w' hww
      rw [hfa, hfa] at hww
      have e1 : w.1 = w'.1 := by
        have := congrArg sb hww
        rwa [map_add, map_add, sbib, sbib, LinearMap.mem_ker.1 w.2.2, LinearMap.mem_ker.1 w'.2.2,
          add_zero, add_zero] at this
      rw [e1] at hww
      exact Prod.ext e1 (Subtype.ext (add_left_cancel hww))
    · intro y
      refine ⟨(sb y, ⟨y - ib (sb y), ?_⟩), ?_⟩
      · rw [LinearMap.mem_ker, map_sub, sbib, sub_self]
      · rw [hfa]
        simp
  let φ := LinearEquiv.ofBijective f hf
  refine ⟨LinearMap.ker sb, φ, ?_⟩
  refine MonoidHom.ext fun h => LinearEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ : ∃ x : Fin N → R, r ∘ x = y :=
    ⟨fun j => (hr (y j)).choose, funext fun j => (hr (y j)).choose_spec⟩
  have rhs : (cj φ) ((sumRep μ 1) h) (r ∘ x) =
      f ((μ h (φ.symm (r ∘ x)).1, (φ.symm (r ∘ x)).2)) := rfl
  have hfw : f (φ.symm (r ∘ x)) = r ∘ x := φ.apply_symm_apply (r ∘ x)
  simp only [MonoidHom.comp_apply]
  rw [rhs]
  obtain ⟨w, hw⟩ : ∃ w, φ.symm (r ∘ x) = w := ⟨_, rfl⟩
  rw [hw] at hfw ⊢
  have hyw : r ∘ x = ib w.1 + (w.2 : Fin N → k) := by
    rw [← hfa]
    exact hfw.symm
  have hv : π (s x) = w.1 := by
    rw [← hsb, hyw, map_add (f := _), sbib, LinearMap.mem_ker.1 w.2.2, add_zero]
  rw [red_apply_map]
  have hlam : ((lam h : GL (Fin N) R) : Matrix (Fin N) (Fin N) R).mulVec x = E h x := by
    show (LinearMap.toMatrix' (E h)).mulVec x = E h x
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  rw [hlam]
  have e1 : E h x = i (α h (s x)) + (x - i (s x)) := rfl
  have e2 : ∀ a b : Fin N → R, r ∘ (a + (x - b)) = r ∘ a + (r ∘ x - r ∘ b) := by
    intro a b
    funext j
    simp
  rw [e1, e2, ← hib, ← hib, h4, hv, hfa, hyw]
  abel
end

