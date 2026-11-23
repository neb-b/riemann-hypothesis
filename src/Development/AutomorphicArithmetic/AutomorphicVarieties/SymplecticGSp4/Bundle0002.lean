module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0036
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.AGraded
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem wcomp_self_eq_of_mem_wtPart {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp]
  by_cases h1 : Finsupp.weight wt n = j
  · rw [if_pos h1]
  · rw [if_neg h1]
    exact (hf' n h1).symm

private theorem wcomp_eq_zero_of_mem_wtPart_of_ne {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) {j' : X} (hj : j' ≠ j) : wcomp O wt j' f = 0 := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp, map_zero]
  by_cases h1 : Finsupp.weight wt n = j'
  · rw [if_pos h1]
    exact hf' n (by rw [h1]; exact hj)
  · rw [if_neg h1]

private theorem aGraded_internal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (M : Model D) : DirectSum.IsInternal M.gr := by
  set_option synthInstance.maxHeartbeats 200000 in
    have key : ∀ (n : ℤ) (x : M.R), x ∈ M.aPart n → x ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) → x = 0 := by
      intro n x hx hx'
      have hle : (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) ≤
          Submodule.map M.W.π.toLinearMap
            (LinearMap.ker (M.W.π.toLinearMap ∘ₗ wcomp c.O M.W.wt ((0 : ℤ), n))) := by
        refine iSup₂_le fun m hm => ?_
        rintro y ⟨h, hh, rfl⟩
        refine ⟨h, ?_, rfl⟩
        change M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) h) = 0
        rw [wcomp_eq_zero_of_mem_wtPart_of_ne hh, map_zero]
        intro h'
        exact hm (Prod.ext_iff.mp h').2.symm
      obtain ⟨g, hg, hgx⟩ := hle hx'
      obtain ⟨f, hf, rfl⟩ := hx
      have hker : f - g ∈ RingHom.ker M.W.π := by
        rw [RingHom.mem_ker, map_sub]
        exact sub_eq_zero.mpr hgx.symm
      have h2 := M.W.homog _ hker ((0 : ℤ), n)
      rw [RingHom.mem_ker, map_sub, map_sub] at h2
      have hg' : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) = 0 := hg
      have h3 : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) = M.W.π f := by
        rw [wcomp_self_eq_of_mem_wtPart hf]
      change M.W.π f = 0
      calc M.W.π f = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) := h3.symm
        _ = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) := sub_eq_zero.mp h2
        _ = 0 := hg'
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    constructor
    · rw [iSupIndep_def]
      intro n
      rw [Submodule.disjoint_def]
      intro x hx hx'
      have h1 : (x : M.R) ∈ M.aPart n := hx
      have h2 : (x : M.R) ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) := by
        have := Submodule.mem_map_of_mem (f := M.A.val.toLinearMap) hx'
        simp only [Submodule.map_iSup] at this
        exact (iSup₂_mono fun m _ => Submodule.map_comap_le _ _) this
      exact Subtype.ext (key n _ h1 h2)
    · refine eq_top_iff.mpr fun x _ => ?_
      obtain ⟨y, hy⟩ := x
      have main : ∀ (z : M.R) (hz : z ∈ ⨆ n, M.aPart n), (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n := by
        intro z hz
        refine Submodule.iSup_induction' M.aPart
          (motive := fun z hz => (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n) ?_ ?_ ?_ hz
        · intro n w hw
          exact Submodule.mem_iSup_of_mem n hw
        · exact zero_mem _
        · intro a b ha hb iha ihb
          exact add_mem iha ihb
      exact main y hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aGraded :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, Nonempty (GradedAlgebra M.gr) := by
  intro Ω _ _ _ l _ c D _ M
  exact ⟨{ (inferInstance : SetLike.GradedMonoid M.gr), (aGraded_internal M).chooseDecomposition with }⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.AVal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.aElt :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ g, ∃ a ∈ M.gr 0, M.x0 a = 0 ∧ ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ) := by
  intro Ω _ _ _ l _ c D _ M g
  choose f hf hπ using fun i : Fin 4 => M.hom g i i
  have hf0 : ∀ i, f i ∈ M.aPart 0 := by
    intro i
    have h := hf i
    rw [(wt_eq_zero i i).mpr rfl] at h
    exact h
  let fA : Fin 4 → M.A := fun i => ⟨f i, M.aPart_le (hf0 i)⟩
  have hx0 : ∀ i, M.x0 (fA i) = D.r0 g i i := fun i => M.at0 g i i (f i) (hπ i)
  have hss : ∀ i, M.toSS (fA i) = M.ent g i i := fun i => Subtype.ext (hπ i)
  refine ⟨∑ i, fA i - algebraMap c.O M.A (Matrix.trace (D.r0 g)), ?_, ?_, ?_⟩
  · apply Submodule.sub_mem
    · exact Submodule.sum_mem _ fun i _ => hf0 i
    · rw [Algebra.algebraMap_eq_smul_one]
      apply Submodule.smul_mem
      show (1 : M.R) ∈ M.aPart 0
      exact SetLike.GradedOne.one_mem
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, AlgHom.commutes]
    simp only [hx0, Algebra.algebraMap_self, RingHom.id_apply, Matrix.trace, Matrix.diag]
    exact sub_self _
  · intro ξ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sub, map_sum, map_sum, AlgHom.commutes, AlgHom.commutes]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hss, Raw.aVal, Matrix.trace, Matrix.diag, map_sum]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CommOfIntegral
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem comm_of_integral {k : Type} [Field k] {p : ℕ} (hp : p.Prime) (hk : (p : k) = 0) (f g : k →+* k)
    {x : k} (hx : IsIntegral ℤ x) : f (g x) = g (f x) := by
  haveI hchar : CharP k p := (CharP.charP_iff_prime_eq_zero hp).mpr hk
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxi : IsIntegral (ZMod p) x := hx.tower_top
  haveI := Algebra.finite_adjoin_simple_of_isIntegral hxi
  haveI hF : Finite (Algebra.adjoin (ZMod p) {x}) := Module.finite_of_finite (ZMod p)
  have hxmem : x ∈ Algebra.adjoin (ZMod p) {x} := Algebra.subset_adjoin (Set.mem_singleton x)
  have hfin : (Set.range (fun n : ℕ => x ^ n)).Finite := by
    refine Set.Finite.subset (s := ((Algebra.adjoin (ZMod p) {x} : Subalgebra (ZMod p) k) : Set k))
      (Set.finite_coe_iff.mp hF) ?_
    rintro _ ⟨n, rfl⟩
    exact Subalgebra.pow_mem _ hxmem n
  have hni : ¬ Function.Injective (fun n : ℕ => x ^ n) := fun hinj =>
    (Set.infinite_range_of_injective hinj) hfin
  simp only [Function.Injective, not_forall] at hni
  obtain ⟨i, j, heq', hij⟩ := hni
  obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ x ^ N = 1 := by
    rcases lt_or_gt_of_ne hij with h | h
    · refine ⟨j - i, by omega, ?_⟩
      have h2 : x ^ i * x ^ (j - i) = x ^ i * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, heq']
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
    · refine ⟨i - j, by omega, ?_⟩
      have h2 : x ^ j * x ^ (i - j) = x ^ j * 1 := by
        rw [← pow_add, Nat.add_sub_cancel' h.le, mul_one, heq']
      exact mul_left_cancel₀ (pow_ne_zero _ hx0) h2
  haveI : NeZero N := ⟨hN0.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := rootsOfUnity N k)
  have mem : ∀ y : k, y ^ N = 1 → ∃ a : ℤ, y = ((ζ : kˣ) : k) ^ a := by
    intro y hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow hN0.ne'] at hy
      exact zero_ne_one hy
    have hu : Units.mk0 y hy0 ∈ rootsOfUnity N k := by
      rw [mem_rootsOfUnity]
      ext
      simp [hy]
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hζ ⟨_, hu⟩)
    refine ⟨a, ?_⟩
    have h3 := congrArg (fun u : rootsOfUnity N k => ((u : kˣ) : k)) ha
    simp only [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, Units.val_mk0] at h3
    exact h3.symm
  have hzN : ((ζ : kˣ) : k) ^ N = 1 := by
    have h1 : (ζ : kˣ) ^ N = 1 := (mem_rootsOfUnity _ _).mp ζ.2
    have h2 := congrArg Units.val h1
    simpa using h2
  obtain ⟨a, ha⟩ := mem (f ((ζ : kˣ) : k)) (by rw [← map_pow, hzN, map_one])
  obtain ⟨b, hb⟩ := mem (g ((ζ : kˣ) : k)) (by rw [← map_pow, hzN, map_one])
  obtain ⟨c, hc⟩ := mem x hN
  rw [hc]
  simp only [map_zpow₀, ha, hb]
  rw [← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

section

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {A : ValuationSubring Ω}

private def resA {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A) : A →+* A where
  toFun x := ⟨σ x, (apply_mem_iff_of_mem_Dec hσ _).2 x.2⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' a b := Subtype.ext (map_mul σ (a : Ω) b)
  map_zero' := Subtype.ext (map_zero σ)
  map_add' a b := Subtype.ext (map_add σ (a : Ω) b)

private theorem resA_local {σ : G ℚ Ω} (hσ : σ ∈ Dec (F := ℚ) A) : IsLocalHom (resA hσ) := by
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have h1 : A.valuation (a : Ω) < 1 := (A.valuation_lt_one_iff a).1 h
  have h2 : A.valuation (σ a) < 1 := (valuation_apply_lt_one_iff hσ _).2 h1
  exact (A.valuation_lt_one_iff (resA hσ a)).2 h2 ha

private theorem comm_mem_Ine {p : ℕ} (hp : p.Prime) (hA : A.valuation (p : Ω) < 1) {g h : G ℚ Ω}
    (hg : g ∈ Dec (F := ℚ) A) (hh : h ∈ Dec (F := ℚ) A) : g * h * g⁻¹ * h⁻¹ ∈ Ine (F := ℚ) A := by
  haveI := resA_local hg
  haveI := resA_local hh
  have hkp : ((p : ℕ) : IsLocalRing.ResidueField A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    simpa using hA
  have hint : ∀ z : Ω, IsIntegral ℤ z → ∀ hz : z ∈ A,
      IsIntegral ℤ (IsLocalRing.residue A ⟨z, hz⟩) := by
    intro z hz hzA
    have h1 : IsIntegral ℤ (⟨z, hzA⟩ : A) := by
      rw [← isIntegral_algHom_iff (A.toSubring.subtype.toIntAlgHom) Subtype.val_injective]
      exact hz
    exact h1.map_of_comp_eq (RingHom.id ℤ) (IsLocalRing.residue A) (RingHom.ext_int _ _)
  have comm : ∀ w : A,
      IsLocalRing.ResidueField.map (resA hg) (IsLocalRing.ResidueField.map (resA hh)
        (IsLocalRing.residue A w)) =
      IsLocalRing.ResidueField.map (resA hh) (IsLocalRing.ResidueField.map (resA hg)
        (IsLocalRing.residue A w)) := by
    intro w
    obtain ⟨s, t, hs, ht, hvs, hst⟩ := exists_den ℚ A (A.valuation_le_one w)
    have hsA := mem_of_isIntegral_int A hs
    have htA := mem_of_isIntegral_int A ht
    have hsunit : IsLocalRing.residue A ⟨s, hsA⟩ ≠ 0 := by
      rw [Ne, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
      simp [hvs]
    have hw : IsLocalRing.residue A w
        = IsLocalRing.residue A ⟨t, htA⟩ / IsLocalRing.residue A ⟨s, hsA⟩ := by
      rw [eq_div_iff hsunit, ← map_mul]
      congr 1
      apply Subtype.ext
      show (w : Ω) * s = t
      rw [mul_comm]
      exact hst
    rw [hw, map_div₀, map_div₀, map_div₀, map_div₀,
      comm_of_integral hp hkp _ _ (hint t ht htA), comm_of_integral hp hkp _ _ (hint s hs hsA)]
  have key : ∀ y : Ω, y ∈ A → A.valuation (g (h y) - h (g y)) < 1 := by
    intro y hy
    have c := comm ⟨y, hy⟩
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue] at c
    have c2 : IsLocalRing.residue A
        (resA hg (resA hh ⟨y, hy⟩) - resA hh (resA hg ⟨y, hy⟩)) = 0 := by
      rw [map_sub, c, sub_self]
    rw [IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at c2
    exact c2
  have hDec : g * h * g⁻¹ * h⁻¹ ∈ Dec (F := ℚ) A :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg))
      (Subgroup.inv_mem _ hh)
  show _ ∈ Inertia (F := ℚ) A
  simp only [Inertia, Set.mem_setOf_eq]
  refine ⟨hDec, fun x hx => ?_⟩
  have hxA : x ∈ A := (A.valuation_le_one_iff x).1 hx
  have hyA : g⁻¹ (h⁻¹ x) ∈ A :=
    (apply_mem_iff_of_mem_Dec (Subgroup.inv_mem _ hg) _).2
      ((apply_mem_iff_of_mem_Dec (Subgroup.inv_mem _ hh) _).2 hxA)
  have e : (g * h * g⁻¹ * h⁻¹) x - x = g (h (g⁻¹ (h⁻¹ x))) - h (g (g⁻¹ (h⁻¹ x))) := by
    simp only [AlgEquiv.mul_apply]
    congr 1
    rw [← AlgEquiv.mul_apply g g⁻¹, mul_inv_cancel, AlgEquiv.one_apply,
      ← AlgEquiv.mul_apply h h⁻¹, mul_inv_cancel, AlgEquiv.one_apply]
  rw [e]
  exact key _ hyA

end

theorem UpperTheory.V.GradeZeroInterpolatingElement.abP :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ p ∈ D.Sb, (∃ τ ∈ D.Ip p, D.ψ τ ≠ 1 ∧ ∀ s ∈ D.Ip p, ∃ n : ℕ, D.ψ s = D.ψ τ ^ n) ∧ ∀ g ∈ D.Gp p, ∀ h ∈ D.Gp p, g * h * g⁻¹ * h⁻¹ ∈ D.Ip p ⊓ D.ψ.ker := by
  intro Ω _ _ _ l _ c D hD p hp
  unfold Raw.Sb at hp
  obtain ⟨hpS, hpl, hldvd⟩ := Finset.mem_filter.mp hp
  have hpp : p.Prime := hD.S_prime p hpS
  have hv := hD.pl_over p hpp
  refine ⟨?_, ?_⟩
  · haveI : Finite (G ℚ Ω ⧸ D.ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hD.psi_open
    haveI : Finite D.ψ.range :=
      Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange D.ψ).toEquiv
    haveI hfin : Finite (Subgroup.map D.ψ (D.Ip p)) :=
      Finite.of_injective (Subgroup.inclusion (Subgroup.map_le_range D.ψ _))
        (Subgroup.inclusion_injective _)
    haveI : IsCyclic (Subgroup.map D.ψ (D.Ip p)) := isCyclic_subgroup_units _
    obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Subgroup.map D.ψ (D.Ip p))
    obtain ⟨τ, hτI, hτγ⟩ := Subgroup.mem_map.mp γ.2
    refine ⟨τ, hτI, ?_, ?_⟩
    · intro h1
      have hγ1 : γ = 1 := Subtype.ext (by rw [← hτγ, h1]; rfl)
      have hsub : ∀ x : Subgroup.map D.ψ (D.Ip p), x = 1 := by
        intro x
        obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hγ x)
        rw [← hz, hγ1, one_zpow]
      have hcard : Nat.card (Subgroup.map D.ψ (D.Ip p)) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (hsub a).trans (hsub b).symm⟩, ⟨1⟩⟩
      rw [hcard] at hldvd
      exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.mp hldvd)
    · intro s hs
      have hsH : (⟨D.ψ s, Subgroup.mem_map_of_mem _ hs⟩ : Subgroup.map D.ψ (D.Ip p))
          ∈ Submonoid.powers γ := mem_powers_iff_mem_zpowers.2 (hγ _)
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp hsH
      refine ⟨n, ?_⟩
      have h2 := congrArg Subtype.val hn
      simp only [SubgroupClass.coe_pow] at h2
      rw [hτγ]
      exact h2.symm
  · intro g hg h hh
    refine ⟨comm_mem_Ine hpp hv hg hh, ?_⟩
    show g * h * g⁻¹ * h⁻¹ ∈ D.ψ.ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (D.ψ g), mul_assoc (D.ψ h), mul_inv_cancel, mul_one, mul_inv_cancel]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_mul {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K) {x y : M4 K}
    (hx : x ∈ Submodule.span K (Set.range r)) (hy : y ∈ Submodule.span K (Set.range r)) :
    x * y ∈ Submodule.span K (Set.range r) := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨g, rfl⟩ := ha
      obtain ⟨h, rfl⟩ := hb
      exact Submodule.subset_span ⟨g * h, map_mul r g h⟩
    | zero => simp
    | add b c _ _ hb hc => rw [mul_add]; exact add_mem hb hc
    | smul c b _ hb => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hb
  | zero => simp
  | add b c _ _ hb hc => rw [add_mul]; exact add_mem hb hc
  | smul c b _ hb => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ hb

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_top {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule K (Matrix n n K)) (h : ∀ i j, Matrix.single i j (1 : K) ∈ S) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [Matrix.matrix_eq_sum_single x]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have := S.smul_mem (x i j) (h i j)
  simpa [Matrix.smul_single] using this

private theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg_iff {H : Type} [Group H] {K : Type} [Field K] (r : H →* M4 K)
    (he : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) (i j : Fin 4) :
    Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r) := by
  constructor
  · rintro ⟨g, hg⟩
    have h1 := geAlg_mul r (geAlg_mul r (he i) (Submodule.subset_span ⟨g, rfl⟩)) (he j)
    have h2 := Submodule.smul_mem _ (r g i j)⁻¹ h1
    rw [Matrix.single_mul_mul_single, Matrix.smul_single] at h2
    simpa [hg] using h2
  · intro h
    by_contra hn
    have hz : ∀ g, r g i j = 0 := fun g => by
      by_contra h'
      exact hn ⟨g, h'⟩
    have key : ∀ x ∈ Submodule.span K (Set.range r), x i j = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem a ha => obtain ⟨g, rfl⟩ := ha; exact hz g
      | zero => rfl
      | add b c _ _ hb hc => simp [hb, hc]
      | smul c b _ hb => simp [hb]
    simpa using key _ h

theorem UpperTheory.V.GradeZeroInterpolatingElement.geAlg :
    ∀ {H : Type} [Group H] (K : Type) [Field K] (r : H →* M4 K) (ν : H → K), (∀ g, IsGSp (ν g) (r g)) → (∀ i, Matrix.single i i (1 : K) ∈ Submodule.span K (Set.range r)) → (∀ i j, Ge r i j ↔ Matrix.single i j (1 : K) ∈ Submodule.span K (Set.range r)) ∧ (∀ i, Ge r i i) ∧ (∀ i j k, Ge r i j → Ge r j k → Ge r i k) ∧ (∀ i j, Ge r i j → Ge r j.rev i.rev) ∧ (Irr r ↔ ∀ i j, Ge r i j) ∧ (Ge r 0 2 → Ge r 2 0 → (∀ g, IsBlock (r g)) → Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) = ⊤) := by
  intro H _ K _ r ν hν he
  have hiff := geAlg_iff r he
  refine ⟨hiff, fun i => (hiff i i).2 (he i), ?_, ?_, ?_, ?_⟩
  · intro i j k hij hjk
    have := geAlg_mul r ((hiff i j).1 hij) ((hiff j k).1 hjk)
    rw [Matrix.single_mul_single_same, mul_one] at this
    exact (hiff i k).2 this
  · rintro i j ⟨g, hg⟩
    refine ⟨g⁻¹, fun h0 => hg ?_⟩
    have h1 : adj (r g) = ν g • r g⁻¹ := by
      have h2 : adj (r g) * r g * r g⁻¹ = ν g • (1 : M4 K) * r g⁻¹ := by rw [hν g]
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one, smul_mul_assoc, one_mul] at h2
    have h3 := congrFun (congrFun h1 j.rev) i.rev
    rw [adj_apply, Fin.rev_rev, Fin.rev_rev, Matrix.smul_apply, h0, smul_zero] at h3
    have h4 : ∀ a b : Fin 4, sgn a * sgn b = 1 ∨ sgn a * sgn b = -1 := by decide
    rcases h4 j.rev i.rev with h | h <;> rw [h] at h3 <;> simpa using h3
  · constructor
    · intro h i j
      rw [hiff, h]
      trivial
    · intro h
      exact geAlg_top _ fun i j => (hiff i j).1 (h i j)
  · intro h02 h20 _
    let f : M4 K →ₗ[K] Matrix (Fin 2) (Fin 2) K :=
      { toFun := fun x => x.submatrix ixA ixA
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hm : ∀ x ∈ Submodule.span K (Set.range r),
        f x ∈ Submodule.span K (Set.range fun g => (r g).submatrix ixA ixA) := by
      intro x hx
      have := Submodule.mem_map_of_mem (f := f) hx
      rwa [Submodule.map_span, ← Set.range_comp] at this
    have hs : ∀ a b : Fin 2, f (Matrix.single (ixA a) (ixA b) (1 : K)) = Matrix.single a b 1 := by
      intro a b
      ext c d
      have hinj : ∀ a b : Fin 2, ixA a = ixA b ↔ a = b := by decide
      show Matrix.single (ixA a) (ixA b) (1 : K) (ixA c) (ixA d) = _
      simp only [Matrix.single_apply, hinj]
    refine geAlg_top _ fun a b => ?_
    rw [← hs]
    apply hm
    fin_cases a <;> fin_cases b
    · exact he 0
    · exact (hiff 0 2).1 h02
    · exact (hiff 2 0).1 h20
    · exact he 2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.IrrIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem irrIff_stable {H K : Type} [Group H] [Field K] {n : ℕ} (r : H →* Matrix (Fin n) (Fin n) K)
    (h : Submodule.span K (Set.range r) = ⊤) (W : Submodule K (Fin n → K))
    (hW : ∀ g, ∀ v ∈ W, (r g).mulVec v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  _root_.UpperTheory.Reformulated.B.StableSubmoduleBotOrTopOfSpanEqTop.irrIff_stable r h W hW

theorem UpperTheory.V.GradeZeroInterpolatingElement.irrIff :
    ∀ {H : Type} [Group H] (K : Type) [Field K] [IsAlgClosed K], (∀ r : H →* M4 K, Irr r ↔ Af.IsIrr r.toHomUnits) ∧ ∀ r r' : H →* M4 K, IsConj4 r r' ↔ Af.RepIso r.toHomUnits r'.toHomUnits := by
  intro H _ K _ _
  refine ⟨fun r => ⟨fun h => ?_, fun h => ?_⟩, fun r r' => ⟨?_, ?_⟩⟩
  · exact ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun W _ hW => irrIff_stable r h W hW⟩
  · exact KStar.Schema.span_eq_top_of_irreducible r fun N hN => h.2.2 N le_top hN
  · rintro ⟨u, hu⟩
    exact ⟨u, fun s => Units.ext (hu s)⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, fun s => congrArg Units.val (hu s)⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Nval
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.nval :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l), IsNVal c.O (PadicAlgCl l) fun x => -Real.log ‖x‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  intro l _ c
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hL : 0 < Real.log l := Real.log_pos hl
  have he : (0 : ℝ) ≤ ((eO l c.O).toNat : ℝ) := Nat.cast_nonneg _
  have anti : ∀ a b : PadicAlgCl l, a ≠ 0 → ‖a‖ ≤ ‖b‖ →
      -Real.log ‖b‖ * ((eO l c.O).toNat : ℝ) / Real.log l ≤
        -Real.log ‖a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
    intro a b ha hab
    have hlog : Real.log ‖a‖ ≤ Real.log ‖b‖ := Real.log_le_log (norm_pos_iff.mpr ha) hab
    apply div_le_div_of_nonneg_right _ hL.le
    exact mul_le_mul_of_nonneg_right (by linarith) he
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)]
    ring
  · intro x y hx hy hxy
    have h := IsUltrametricDist.norm_add_le_max x y
    rcases le_total ‖x‖ ‖y‖ with h1 | h1
    · rw [max_eq_right h1] at h
      exact (min_le_right _ _).trans (anti _ _ hxy h)
    · rw [max_eq_left h1] at h
      exact (min_le_left _ _).trans (anti _ _ hxy h)
  · intro a ha
    have h := normO l c.O a ha
    have h2 := congrArg Real.log h
    rw [Real.log_pow, Real.log_pow, Real.log_inv] at h2
    show -Real.log ‖(a : PadicAlgCl l)‖ * ((eO l c.O).toNat : ℝ) / Real.log l = _
    field_simp
    linarith
end

