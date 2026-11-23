module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0012
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.CorGSumLog
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private lemma corG_sum_log (n : ℤ) (hn : n ≠ 0) (Ls : Finset Nat.Primes) :
    ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) ≤ Real.log |(n : ℝ)| := by
  classical
  have hdvd : ∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) ∣ n := by
    apply Finset.prod_dvd_of_coprime
    · intro a _ b _ hab
      simp only [Function.onFun]
      apply IsCoprime.pow
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes a.2 b.2).mpr (fun h => hab (Subtype.ext h))
    · intro l _
      haveI : Fact (Nat.Prime l) := ⟨l.2⟩
      exact padicValInt_dvd n
  have hP : (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) ≤ |(n : ℝ)| := by
    have h1 := Int.le_of_dvd (abs_pos.mpr hn) ((dvd_abs _ _).mpr hdvd)
    have h2 : ((∏ l ∈ Ls, ((l : ℕ) : ℤ) ^ (padicValInt l n) : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by
      exact_mod_cast h1
    push_cast at h2
    exact h2
  have hpos : ∀ l ∈ Ls, (0 : ℝ) < ((l : ℕ) : ℝ) ^ (padicValInt l n) :=
    fun l _ => pow_pos (by exact_mod_cast l.2.pos) _
  calc ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ)
      = ∑ l ∈ Ls, Real.log (((l : ℕ) : ℝ) ^ (padicValInt l n)) := by
        apply Finset.sum_congr rfl
        intro l _
        rw [Real.log_pow]
        ring
    _ = Real.log (∏ l ∈ Ls, ((l : ℕ) : ℝ) ^ (padicValInt l n)) :=
        (Real.log_prod (fun l hl => (hpos l hl).ne')).symm
    _ ≤ Real.log |(n : ℝ)| := Real.log_le_log (Finset.prod_pos hpos) hP

theorem UpperTheory.V.U3.corGK :
    PropGK → CorGK := by
  intro hP K _ _
  obtain ⟨c₅, A, hK⟩ := hP K
  refine ⟨c₅, A, ?_⟩
  intro Ω _ _ _ _ e N _ H p p' hp hp' hne hd hd' c Ls hL
  rcases Ls.eq_empty_or_nonempty with rfl | ⟨l₀, hl₀⟩
  · refine ⟨by simp, ?_⟩
    rw [Finset.sum_empty]
    have h1 := Real.log_natCast_nonneg p
    have h2 := Real.log_natCast_nonneg p'
    positivity
  have he : 1 ≤ e := by
    obtain ⟨ψ, _, h⟩ := hL l₀ hl₀
    exact h.e_pos
  obtain ⟨n, hn, hb, h⟩ := hK e N H p he hp hd
  obtain ⟨n', hn', hb', h'⟩ := hK e N H p' he hp' hd'
  have key : ∀ l ∈ Ls, (∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤ 2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ) := by
    intro l hl
    have a1 : (0 : ℝ) ≤ (padicValInt l n : ℝ) := Nat.cast_nonneg _
    have a2 : (0 : ℝ) ≤ (padicValInt l n' : ℝ) := Nat.cast_nonneg _
    by_cases hlp : (l : ℕ) = p
    · have hlp' : (l : ℕ) ≠ p' := fun x => hne (hlp.symm.trans x)
      obtain ⟨b1, b2⟩ := h' Ω l hlp' (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
    · obtain ⟨b1, b2⟩ := h Ω l hlp (c l) (hL l hl)
      exact ⟨b1, by linarith⟩
  refine ⟨fun l hl => (key l hl).1, ?_⟩
  have s1 := corG_sum_log n hn Ls
  have s2 := corG_sum_log n' hn' Ls
  calc _ ≤ ∑ l ∈ Ls, Real.log (l : ℕ) * (2 * (padicValInt l n : ℝ) + 2 * (padicValInt l n' : ℝ)) :=
        Finset.sum_le_sum fun l hl => mul_le_mul_of_nonneg_left (key l hl).2 (Real.log_natCast_nonneg _)
    _ = 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n : ℝ) + 2 * ∑ l ∈ Ls, Real.log (l : ℕ) * (padicValInt l n' : ℝ) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ _ := by nlinarith
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DatLoc
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.V.U3.dat_loc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D.ι.range = Dec (F := ℚ) A ∧ (Loc.Iq l).map D.ι = Ine (F := ℚ) A ∧
        Function.Injective D.ι ∧ (∀ x : Ω, x ∈ A ↔ ‖D.j x‖ ≤ 1) ∧ (∀ σ, cycZ ℚ Ω l (D.ι σ) = Loc.cyc l l σ) ∧
        ∀ A' : ValuationSubring Ω, A'.valuation (l : Ω) < 1 → ∃ g : G ℚ Ω,
          (∀ s, s ∈ Dec (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Dec (F := ℚ) A) ∧ ∀ s, s ∈ Ine (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  have hι : D.ι = Loc.iota D.j := by
    ext σ x
    apply D.j.injective
    rw [Loc.iota_spec, ← D.ι_spec]
  obtain ⟨hemb, hrange, -, hmap, hcyc, -, -⟩ := Loc.iotaFacts D.j
  have hmem : ∀ x : Ω, x ∈ Loc.placeJ D.j ↔ Valued.v (D.j x) ≤ 1 := fun x => Iff.rfl
  have hA : (Loc.placeJ D.j).valuation (l : Ω) < 1 := by
    have hnot : (l : Ω)⁻¹ ∉ Loc.placeJ D.j := by
      rw [hmem, map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, not_le]
      have hl : (1 : NNReal) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      simpa using hl
    by_contra h
    push_neg at h
    apply hnot
    have hle : (Loc.placeJ D.j).valuation (l : Ω) ≤ 1 :=
      ((Loc.placeJ D.j).valuation_le_one_iff _).2 (natCast_mem _ l)
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, le_antisymm hle h, inv_one]
  refine ⟨Loc.placeJ D.j, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hι]; exact hrange
  · rw [hι]; exact hmap
  · rw [hι]; exact hemb.injective
  · intro x
    rw [hmem, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  · intro σ
    rw [hι]
    exact DFunLike.congr_fun (hcyc l) σ
  · intro A' hA'
    obtain ⟨-, -, -, -, -, -, -, hconj, -, hact⟩ := ML.placeBasic Ω
    obtain ⟨g, rfl⟩ := hconj (Loc.placeJ D.j) A' l Fact.out hA hA'
    exact ⟨g, (hact _ g).1, (hact _ g).2.1⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDat
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

private theorem dx_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] :
    ∃ σ : G ℚ Ω, ∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x) := by
  obtain ⟨σ, h⟩ := exists_isConjOm (E := ℚ) (Ω := Ω)
  exact ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [eq_ratCast (algebraMap ℚ Ω), map_ratCast], h⟩

private theorem dx_ker (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (σ : G ℚ Ω) : AlgEquiv.restrictNormalHom (F := ℚ) K σ = 1 ↔ σ ∈ galOf ℚ K Ω := by
  have h : ∀ x : K, algebraMap K Ω (AlgEquiv.restrictNormalHom (F := ℚ) K σ x) = σ (algebraMap K Ω x) :=
    fun x => AlgEquiv.restrictNormal_commutes σ K x
  refine ⟨fun h1 x => ?_, fun h1 => AlgEquiv.ext fun x => (algebraMap K Ω).injective ?_⟩
  · rw [← h, h1]; rfl
  · rw [h, h1]; rfl

private theorem dx_eta (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Field K] [NumberField K] [Algebra K Ω]
    [IsGalois ℚ K] (h2 : Module.finrank ℚ K = 2) : ∃ η : G ℚ Ω →* ℤˣ, η.ker = galOf ℚ K Ω := by
  have hc : Nat.card Gal(K/ℚ) = 2 := by rw [IsGalois.card_aut_eq_finrank, h2]
  have hz : Nat.card ℤˣ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
  let e : Gal(K/ℚ) ≃* ℤˣ := mulEquivOfPrimeCardEq hc hz
  refine ⟨e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) K), Subgroup.ext fun σ => ?_⟩
  rw [← dx_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
  exact map_eq_one_iff e e.injective

private theorem dx_unr (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K]
    [Algebra K Ω] [IsGalois ℚ K] (l : ℕ) [hl : Fact l.Prime] (h : ¬ (l : ℤ) ∣ discr K) (A : ValuationSubring Ω)
    (hA : A.valuation (l : Ω) < 1) : Ine (F := ℚ) A ≤ galOf ℚ K Ω := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨p1, p2, p3, -⟩ := places K Ω l A
  obtain ⟨w, hw⟩ := p1 fun ht => (p2 ht).2 hA
  have hm : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal := (p3 w hw).1 hA
  have hb := (CF.unramIff.1 K l hl.out).1 ((CF.unramIff.2.1 K l hl.out).2 h) w hm
  intro σ hσ
  have h1 := Subgroup.mem_map_of_mem (CF.resTo ℚ K Ω) hσ
  rw [CF.ineAbs ℚ K Ω A w hw, hb, Subgroup.mem_bot] at h1
  exact (dx_ker Ω K σ).1 h1

private theorem dx_lc {Γ M : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group M] (f : Γ →* M)
    (h : IsOpen (f.ker : Set Γ)) : IsLocallyConstant f := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : Γ => x⁻¹ * y := by fun_prop
  have h1 : (fun y : Γ => x⁻¹ * y) ⁻¹' (f.ker : Set Γ) ∈ nhds x :=
    (h.preimage hc).mem_nhds (by simp)
  filter_upwards [h1] with y hy
  have h2 : f (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

private theorem dx_zpow {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R)
    (Ψ : Γ → Rˣ) (h : AdicCont I fun g => (Ψ g : R)) (j : ℤ) : AdicCont I fun g => ((Ψ g ^ j : Rˣ) : R) := by
  classical
  intro N
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((Ψ g ^ j : Rˣ) : R)) =
      (fun x : R ⧸ I ^ N => if hx : IsUnit x then ((hx.unit ^ j : (R ⧸ I ^ N)ˣ) : R ⧸ I ^ N) else 0) ∘
        fun g => Ideal.Quotient.mk (I ^ N) (Ψ g : R) := by
    funext g
    have hx : IsUnit (Ideal.Quotient.mk (I ^ N) (Ψ g : R)) := (Ψ g).isUnit.map _
    have e : hx.unit = Units.map (Ideal.Quotient.mk (I ^ N)).toMonoidHom (Ψ g) := Units.ext rfl
    simp only [Function.comp_apply, dif_pos hx]
    rw [e, ← map_zpow]
    rfl
  rw [key]
  exact (h N).comp _

private theorem dx_alg {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] R]
    (I : Ideal R) (hI : (l : R) ∈ I) (f : Γ → ℤ_[l]) (hf : Continuous f) :
    AdicCont I fun g => algebraMap ℤ_[l] R (f g) := by
  intro n
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [hf.continuousAt.eventually (Metric.closedBall_mem_nhds (f x) hpos)] with y hy
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton'] at hy
  obtain ⟨a, ha⟩ := hy
  rw [Ideal.Quotient.eq, ← map_sub, ← ha, map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hI n)

private theorem dx_lmem (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Module.Finite ℤ_[l] O] : (l : O) ∈ IsLocalRing.maximalIdeal O := by
  have h : (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ_[l] O) = IsLocalRing.maximalIdeal ℤ_[l] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[l]) _)
  have h1 : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  rw [← h, Ideal.mem_comap, map_natCast] at h1
  exact h1

private theorem dx_dir (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter O N) : IsLocallyConstant (Chr.dirG ℚ Ω ψ) :=
  (dx_lc _ (Chr.clsFacts ℚ Ω N).1).comp ψ.toUnitHom

private theorem dx_cont (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    {N : ℕ} [NeZero N] (e : ℕ) (ψ : DirichletCharacter O N) : CharCont (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) := by
  refine dx_zpow _ _ fun n => ?_
  have h1 : AdicCont (IsLocalRing.maximalIdeal O) fun g => (chiO ℚ Ω l O g : O) :=
    dx_alg _ (dx_lmem l O) (fun g => (cycZ ℚ Ω l g : ℤ_[l])) (Units.continuous_val.comp (contTw ℚ Ω l).1)
  have h2 := dx_zpow _ _ h1 (e : ℤ) n
  have h3 := (dx_dir Ω ψ).comp fun u : Oˣ => Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n) (u : O)
  have h4 := h2.mul h3
  convert h4 using 1
  rfl

private theorem dx_place {Ω : Type} [Field Ω] [CharZero Ω] {l : ℕ} [hl : Fact l.Prime] (j : Ω →+* Om l) :
    (Loc.placeJ j).valuation (l : Ω) < 1 := by
  have h0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have h1 : (l : Ω)⁻¹ ∉ Loc.placeJ j := by
    intro h
    have h2 : ‖j (l : Ω)⁻¹‖ ≤ 1 := h
    have h3 : j (l : Ω)⁻¹ = algebraMap ℚ_[l] (Om l) (l : ℚ_[l])⁻¹ := by simp
    rw [h3, PadicAlgCl.norm_extends, norm_inv, Padic.norm_p, inv_inv] at h2
    exact absurd hl.out.one_lt (by exact_mod_cast h2.not_gt)
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 h0)] at h1
  exact h1

theorem UpperTheory.V.U3.exists_dat :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}, GD Ω K l e ψ → Nonempty (Dat Ω K c e ψ) := by
  intro Ω _ _ _ K _ _ _ l hl c N _ e ψ h
  haveI : Algebra.IsQuadraticExtension ℚ K := ⟨h.quad⟩
  haveI : IsGalois ℚ K := inferInstance
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨η, hη⟩ := dx_eta Ω K h.quad
  obtain ⟨cc, hcc⟩ := dx_cc Ω
  obtain ⟨j⟩ := Loc.exists_emb (Ω := Ω) (v := l)
  obtain ⟨i1, -, i3, -, i5, -⟩ := Loc.iotaFacts j
  have hA : (Loc.placeJ j).valuation (l : Ω) < 1 := dx_place j
  have hI : ∀ g ∈ Loc.Iq l, Loc.iota j g ∈ Ine (F := ℚ) (Loc.placeJ j) := fun g hg => by
    rw [← i3] at hg; exact hg
  have hopen : IsOpen (((η.comp (Loc.iota j)).ker : Subgroup (GQ l)) : Set (GQ l)) := by
    have h1 := (galEmbTop ℚ K Ω).2.1
    rw [← hη] at h1
    exact h1.preimage i1.continuous
  obtain ⟨Kv, -, -, -, -, hKv, -⟩ := Loc.openField (η.comp (Loc.iota j)).ker.subtype hopen.isOpenEmbedding_subtypeVal
  rw [Subgroup.range_subtype] at hKv
  have hd : ¬ (l : ℤ) ∣ discr K := fun hd => h.l_cop (Dvd.dvd.mul_right (Int.natCast_dvd.1 hd) _)
  exact ⟨{
    gd := h
    η := η
    η_ker := hη
    cc := cc
    conj := hcc
    j := j
    ι := Loc.iota j
    ι_cont := i1.continuous
    ι_spec := fun σ x => (Loc.iota_spec j σ x).symm
    Kv := Kv
    Kv_spec := fun g => by rw [← hKv]; rfl
    η_unr := fun g hg => by
      have h1 := dx_unr Ω K l hd _ hA (hI g hg)
      rw [← hη] at h1
      exact h1
    τ_open := ((dx_dir Ω (comp l ψ)).comp_continuous i1.continuous).isOpen_fiber 1
    Ψ_cont := dx_cont Ω e ψ
    Ψ_I := fun g hg => by
      rw [← ((compIne Ω N l hl.out _ hA).2 c.O ψ).1 _ (hI g hg), Chr.Psi, MonoidHom.mul_apply, zpow_natCast,
        MonoidHom.pow_apply, Loc.cycA, ← i5 l]
      rfl }⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ExistsDecompositionFieldFrobeniusData
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

section SlopeTestRemainingChoices

open Formalism.GaloisCohomology

private theorem df_locConst {Γ A : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group A] (ψ : Γ →* A)
    (h : IsOpen (ψ.ker : Set Γ)) : IsLocallyConstant ψ :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker ψ h

private theorem df_exists_prime (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : n ≠ 0) (h : (n : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ (p : 𝓞 ℚ) ∈ v.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qj5.df_exists_prime v n hn h

private theorem df_not_both (v : HeightOneSpectrum (𝓞 ℚ)) {a b : ℕ} (hab : a.Coprime b) (ha : (a : 𝓞 ℚ) ∈ v.asIdeal)
    (hb : (b : 𝓞 ℚ) ∈ v.asIdeal) : False := by
  obtain ⟨x, y, h⟩ : IsCoprime (a : 𝓞 ℚ) (b : 𝓞 ℚ) := hab.cast
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ ha) (v.asIdeal.mul_mem_left _ hb)))

private theorem df_val {Ω : Type} [Field Ω] [CharZero Ω] {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 ℚ)} (hv : IsPlaceOver A v) (n : ℕ) :
    A.valuation (n : Ω) < 1 ↔ ((n : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
  have h := hv ((n : ℕ) : 𝓞 ℚ)
  have e : algebraMap ℚ Ω (((n : ℕ) : 𝓞 ℚ) : ℚ) = (n : Ω) := by simp
  rw [e] at h
  exact h

private theorem df_order {q n m : ℕ} (hq : 1 < q) (hn : 0 < n) (hm : m + 1 = q ^ n) (u : (ZMod m)ˣ)
    (hu : (u : ZMod m) = q) : orderOf u = n := by
  rw [orderOf_eq_iff hn]
  refine ⟨Units.ext ?_, fun k hk hk0 h => ?_⟩
  · rw [Units.val_pow_eq_pow_val, hu, ← Nat.cast_pow, ← hm]
    simp
  · have h1 : ((q ^ k : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
      rw [Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h]
      simp
    have h2 : 1 < q ^ k := Nat.one_lt_pow hk0.ne' hq
    have h3 : q ^ k < q ^ n := Nat.pow_lt_pow_right hq hk
    have h4 := (Nat.modEq_iff_dvd' h2.le).1 ((ZMod.natCast_eq_natCast_iff _ _ _).1 h1).symm
    have h5 := Nat.le_of_dvd (by omega) h4
    omega

private theorem df_frob (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : IsPlaceOver A v) (D I : Subgroup (G ℚ Ω)) (hD : D = Dec (F := ℚ) A) (hI : I = Ine (F := ℚ) A) :
    ∃ φ : D, (I.subgroupOf D ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤ ∧
      ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I.subgroupOf D, d s = 1) ∧
        d φ = Multiplicative.ofAdd 1 := by
  subst hD hI
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨γ, hγ⟩ := exists_isFrob hv
  refine ⟨⟨γ, hγ.1⟩, ?_, fun n hn => ?_⟩
  · have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω)
      ⟨(Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure, Subgroup.isClosed_topologicalClosure _⟩
    have h1 : Dec (F := ℚ) A ≤ (Ine (F := ℚ) A ⊔ Subgroup.zpowers γ).topologicalClosure := by
      refine le_trans (le_sInf ?_) key.ge
      rintro N ⟨hNo, hN⟩
      have h := (Subgroup.le_topologicalClosure _).trans hN
      exact Kum.decGen ℚ Ω A _ γ N hv hγ hNo (le_sup_left.trans h)
        (h (Subgroup.mem_sup_right (Subgroup.mem_zpowers γ)))
    have h2 : ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔
        Subgroup.zpowers (⟨γ, hγ.1⟩ : Dec (F := ℚ) A)).map (Dec (F := ℚ) A).subtype =
        Ine (F := ℚ) A ⊔ Subgroup.zpowers γ := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, MonoidHom.map_zpowers, inf_eq_left.2 (Ine_le_Dec A)]
      rfl
    rw [eq_top_iff]
    intro x _
    have h3 := h1 x.2
    rw [← h2] at h3
    exact closure_subtype.2 h3
  · have hq : normV v = Ideal.absNorm v.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq1 : 1 < normV v := by
      rw [hq]
      have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
      have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
      omega
    have hqv : ((normV v : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := hq ▸ Ideal.absNorm_mem _
    obtain ⟨p, hp, hpq, hpv⟩ := df_exists_prime v _ (by omega) hqv
    haveI : Fact p.Prime := ⟨hp⟩
    have h1 : 1 < normV v ^ n := Nat.one_lt_pow hn.ne' hq1
    obtain ⟨m, hm⟩ : ∃ m, m + 1 = normV v ^ n := ⟨normV v ^ n - 1, by omega⟩
    haveI : NeZero m := ⟨by omega⟩
    have hmp : m.Coprime p := by
      refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_).symm
      have h2 : p ∣ m + 1 := hm ▸ hpq.trans (dvd_pow_self _ hn.ne')
      exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h).1 h2))
    have hA := (df_val hv p).2 hpv
    obtain ⟨hopen, -, -, -, hIne⟩ := Chr.clsFacts ℚ Ω m
    have hI := hIne A fun h => df_not_both v hmp ((df_val hv m).1 h) hpv
    have hu : ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m) = normV v := by
      haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
      obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
      have hv1 : A.valuation ζ ≤ 1 := by
        have h1 : A.valuation ζ ^ m = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
        exact ((pow_eq_one_iff_left (NeZero.ne m)).1 h1).le
      have h2 : γ ζ = ζ ^ normV v := by
        refine (LDataCardLeFinrank.ineFixRoots ℚ Ω p A hA m hmp (ζ ^ normV v) ?_).1 (γ ζ) ?_ (hγ.2 ζ hv1)
        · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
        · rw [← map_pow, hζ.pow_eq_one, map_one]
      rw [Chr.cls_spec m γ ζ hζ.pow_eq_one, pow_eq_pow_mod (normV v) hζ.pow_eq_one] at h2
      have h3 := hζ.pow_inj (ZMod.val_lt _) (Nat.mod_lt _ (NeZero.pos m)) h2
      rw [← ZMod.natCast_zmod_val ((Chr.cls ℚ Ω m γ : (ZMod m)ˣ) : ZMod m), h3, ZMod.natCast_mod]
    have hord := df_order hq1 hn hm _ hu
    have hle : Dec (F := ℚ) A ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) := by
      have hk : (Chr.cls ℚ Ω m).ker ≤ (Subgroup.zpowers (Chr.cls ℚ Ω m γ)).comap (Chr.cls ℚ Ω m) :=
        Subgroup.ker_le_comap _ _
      exact Kum.decGen ℚ Ω A _ γ _ hv hγ (Subgroup.isOpen_mono hk hopen) (hI.trans hk) (Subgroup.mem_zpowers _)
    let f : Dec (F := ℚ) A →* Subgroup.zpowers (Chr.cls ℚ Ω m γ) :=
      ((Chr.cls ℚ Ω m).comp (Dec (F := ℚ) A).subtype).codRestrict _ fun x => hle x.2
    have hg : ∀ x : Subgroup.zpowers (Chr.cls ℚ Ω m γ), x ∈ Subgroup.zpowers (f ⟨γ, hγ.1⟩) := by
      rintro ⟨_, k, rfl⟩
      exact ⟨k, rfl⟩
    have hc : Nat.card (Subgroup.zpowers (Chr.cls ℚ Ω m γ)) = n := by rw [Nat.card_zpowers, hord]
    have hf1 : ∀ s : Dec (F := ℚ) A, Chr.cls ℚ Ω m s = 1 → f s = 1 := fun s hs => Subtype.ext hs
    refine ⟨(zmodMulEquivOfGenerator hg hc).symm.toMonoidHom.comp f, df_locConst _ ?_, fun s hs => ?_, ?_⟩
    · refine Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω m).ker.subgroupOf _) (fun s hs => ?_)
        (hopen.preimage continuous_subtype_val)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hf1 s hs, map_one]
    · rw [MonoidHom.comp_apply, hf1 s (hI hs), map_one]
    · exact zmodMulEquivOfGenerator_symm_apply_generator hg hc

end SlopeTestRemainingChoices

open Formalism.GaloisCohomology in
theorem UpperTheory.exists_decompositionField_frobenius_data :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 ℚ)), IsPlaceOver A v →
          CompactSpace (Dec (F := ℚ) A) ∧ ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A)).Normal ∧ IsClosed (Ine (F := ℚ) A : Set (G ℚ Ω)) ∧
          (∃ fr : Dec (F := ℚ) A, ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) ∧
          ∀ n : ℕ, 0 < n → ∃ U : Subgroup (Dec (F := ℚ) A), IsOpen (U : Set (Dec (F := ℚ) A)) ∧ (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ≤ U ∧ U.index = n := by
  intro Ω _ _ _ A v hv
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨φ, h1, h2⟩ := df_frob Ω A v hv _ _ rfl rfl
  refine ⟨isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact, inferInstance, isClosed_Ine A, ⟨φ, h1⟩,
    fun n hn => ?_⟩
  obtain ⟨d, hd, hI, hφ⟩ := h2 n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  refine ⟨d.ker, hd {1}, fun s hs => hI s hs, ?_⟩
  have hs : d.range = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine ⟨φ ^ (Multiplicative.toAdd x).val, ?_⟩
    rw [map_pow, hφ, ← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [Subgroup.index_ker, hs, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.GlobalEulerCharRatOfNeTwo
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

theorem UpperTheory.global_euler_char_rat_of_ne_two :
    GlobalFiniteness → GlobalEulerChar → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k M : Type) [Field k] [Finite k] [CharP k l] [AddCommGroup M] [Module k M] [Module.Finite k M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M] [ContinuousConstSMul k M], l ≠ 2 → ∀ (S : Finset (HeightOneSpectrum (𝓞 ℚ))), ContainsAbove S l →
          ∀ ρ : Representation k (GS Ω (S : Set (HeightOneSpectrum (𝓞 ℚ)))) M, ContAction ρ → ∀ σ : G ℚ Ω, (∃ φ : Ω →+* ℂ, ∀ x, φ (σ x) = starRingEnd ℂ (φ x)) →
          Module.Finite k (H1 ρ) ∧ Module.Finite k (H2 ρ) ∧
          Module.finrank k (H0 ρ) + Module.finrank k (H2 ρ) + Module.finrank k M = Module.finrank k (H1 ρ) + Module.finrank k (LinearMap.ker (ρ (toGS Ω _ σ) - 1)) := by
  intro hf he Ω _ _ _ l _ k M _ _ _ _ _ _ _ _ _ _ hl S hS ρ hρ σ hσ
  haveI : Finite M := Module.finite_of_finite k
  have hcc : IsCC σ := hσ
  obtain ⟨h1, h2, h3⟩ := UpperTheory.global_euler_characteristic_rationals_odd_prime hf he Ω l hl k M S ρ hS hρ σ hcc
  exact ⟨h1, h2, h3.symm⟩
end

