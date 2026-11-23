module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
public import ReciprocityTheory.GroupCohomology.ImportsAlt
public import Mathlib.Algebra.Module.Lattice
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsRealSplitPrimitiveElementPadicFiniteExt
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0038
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantLatticeOpenEmbedding
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_pow_mul_norm_le {l : ℕ} [Fact l.Prime] (C : ℝ) :
    ∃ m : ℕ, ∀ a : ℚ_[l], ‖a‖ ≤ C → ‖(l : ℚ_[l]) ^ m * a‖ ≤ 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C h1
  refine ⟨m, fun a ha => ?_⟩
  have hp : (0 : ℝ) < (l : ℝ) ^ m := by positivity
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hp, mul_one]
  exact ha.trans hm.le

private theorem exists_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    ∃ L : Submodule ℤ_[l] V, Submodule.IsLattice ℚ_[l] L ∧ ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
  classical
  let b := Module.finBasis ℚ_[l] V
  let S : Set V := Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)
  have hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i)) := by
    refine continuous_pi fun i => ?_
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp
      (h.comp (continuous_id.prodMk continuous_const))
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) C
  have hl : ((l : ℚ_[l]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  refine ⟨Submodule.span ℤ_[l] S, ⟨?_, ?_⟩, ?_⟩
  · let N : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine hN.of_le ?_
    rw [Submodule.span_le]
    rintro _ ⟨⟨g, i⟩, rfl⟩
    have e := b.sum_repr (ρ g (b i))
    simp only [SetLike.mem_coe]
    rw [← e]
    refine Submodule.sum_mem _ fun k _ => ?_
    have hk : ‖b.repr (ρ g (b i)) k‖ ≤ C :=
      ((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans
        (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, hm _ hk⟩
    have : b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k) := by
      rw [← algebraMap_smul ℚ_[l] z, smul_smul]
      congr 1
      change _ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _
      field_simp
    rw [this]
    exact N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).mp hli
  · intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨g', i⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * g', i), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx

theorem UpperTheory.exists_invariant_lattice_openEmbedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∃ (ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l])) (j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT ∧ IsOpenEmbedding j ∧ (∀ g x, j (ρT g x) = ρ g (j x)) ∧ ∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  have hex : ∃ L : Submodule ℤ_[l] V, Submodule.IsFullLattice ℚ_[l] L ∧
      ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
    classical
    let b := Module.finBasis ℚ_[l] V
    let S : Set V := Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)
    have hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i)) := by
      refine continuous_pi fun i => ?_
      exact (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp
        (h.comp (continuous_id.prodMk continuous_const))
    obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) C
    have hl : ((l : ℚ_[l]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    refine ⟨Submodule.span ℤ_[l] S, { toIsLattice := ⟨?_, ?_⟩, span_eq_top := ?_ }, ?_⟩
    · let N : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)
      have hN : N.FG := Submodule.fg_span (Set.finite_range _)
      refine hN.of_le ?_
      rw [Submodule.span_le]
      rintro _ ⟨⟨g, i⟩, rfl⟩
      have e := b.sum_repr (ρ g (b i))
      simp only [SetLike.mem_coe]
      rw [← e]
      refine Submodule.sum_mem _ fun k _ => ?_
      have hk : ‖b.repr (ρ g (b i)) k‖ ≤ C :=
        ((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans
          (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)
      let z : ℤ_[l] := ⟨_, hm _ hk⟩
      have : b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k) := by
        rw [← algebraMap_smul ℚ_[l] z, smul_smul]
        congr 1
        change _ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _
        field_simp
      rw [this]
      exact N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).mp hli
    · rw [eq_top_iff, ← b.span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨(1, i), by simp⟩
    · intro g x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨g', i⟩, rfl⟩ := hx
        exact Submodule.subset_span ⟨(g * g', i), by simp⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  
  obtain ⟨L, hL, hst⟩ := hex
  letI : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L
  letI : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L
  have hr : finrank ℤ_[l] L = finrank ℚ_[l] V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' ℚ_[l] L]
  let bL : Basis (Fin (finrank ℚ_[l] V)) ℤ_[l] L := Module.finBasisOfFinrankEq ℤ_[l] L hr
  let b : Basis (Fin (finrank ℚ_[l] V)) ℚ_[l] V := bL.extendOfIsFullLattice ℚ_[l]
  let j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V := L.subtype ∘ₗ bL.equivFun.symm.toLinearMap
  have hj : ∀ x, j x = b.equivFun.symm (fun i => (x i : ℚ_[l])) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [j, b, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply, map_sum, map_smul,
      Submodule.subtype_apply, Basis.extendOfIsFullLattice_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ℚ_[l] (x i) _).symm
  let e : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₜ V :=
    { toEquiv := b.equivFun.symm.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap }
  have hjo : IsOpenEmbedding j := by
    have : (j : _ → V) = e ∘ Pi.map (fun _ => ((↑) : ℤ_[l] → ℚ_[l])) := funext hj
    rw [this]
    exact e.isOpenEmbedding.comp (IsOpenEmbedding.piMap fun _ => PadicInt.isOpenEmbedding_coe)
  let r : G → L →ₗ[ℤ_[l]] L := fun g => ((ρ g).restrictScalars ℤ_[l]).restrict (hst g)
  let ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l]) :=
    { toFun := fun g => bL.equivFun.toLinearMap ∘ₗ r g ∘ₗ bL.equivFun.symm.toLinearMap
      map_one' := by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        change ρ 1 _ = _
        rw [map_one]; rfl
      map_mul' := fun g g' => by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          Module.End.mul_apply]
        change ρ (g * g') _ = _
        rw [map_mul]; rfl }
  have hρ : ∀ g x, j (ρT g x) = ρ g (j x) := fun g x => by
    change L.subtype (bL.equivFun.symm (bL.equivFun (r g (bL.equivFun.symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  refine ⟨ρT, j, ?_, hjo, hρ, fun y => ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [hjo.isEmbedding.continuous_iff]
    have : (j ∘ fun p : G × (Fin (finrank ℚ_[l] V) → ℤ_[l]) => ρT p.1 p.2) = fun p => ρ p.1 (j p.2) :=
      funext fun p => hρ _ _
    rw [this]
    exact h.comp (continuous_fst.prodMk (hjo.continuous.comp continuous_snd))
  · obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) ‖b.equivFun y‖
    refine ⟨m, fun i => ⟨_, hm _ (norm_le_pi_norm (b.equivFun y) i)⟩, ?_⟩
    refine (hj _).trans ?_
    rw [LinearEquiv.symm_apply_eq, ← algebraMap_smul ℚ_[l] ((l : ℤ_[l]) ^ m) y, map_smul]
    funext i
    change (l : ℚ_[l]) ^ m * b.equivFun y i = _
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsTotallyImaginaryGeneratorOfIsCMField
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K :=
  _root_.UpperTheory.Reformulated.B.Qh8.isCM_of_conj K h

open Polynomial in
private theorem exists_sqrt (l : ℕ) [hl : Fact l.Prime] :
    ∃ d : ℚ_[l], d ^ 2 = 1 - 4 * (l : ℚ_[l]) := by
  have h3 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := l) (R := ℤ_[l]) (F := X ^ 2 - X + C (l : ℤ_[l])) (a := 0) (by
    have e1 : aeval (0 : ℤ_[l]) (X ^ 2 - X + C (l : ℤ_[l]) : ℤ_[l][X]) = ((l : ℕ) : ℤ_[l]) := by
      simp
    have e2 : aeval (0 : ℤ_[l]) (derivative (X ^ 2 - X + C (l : ℤ_[l]) : ℤ_[l][X])) = -1 := by
      simp
    rw [e1, e2, norm_neg, norm_one, one_pow]
    exact h3)
  have h4 : z ^ 2 - z + (l : ℤ_[l]) = 0 := by simpa using hz
  have h5 : (z : ℚ_[l]) ^ 2 - z + (l : ℚ_[l]) = 0 := by
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) h4
    simpa using this
  exact ⟨2 * z - 1, by linear_combination 4 * h5⟩

private theorem conj_of_sq (w : ℂ) (r : ℝ) (hr : r < 0) (h : w ^ 2 = r) : starRingEnd ℂ w = -w := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : w.re = 0 := by
    by_contra h0
    have : w.im = 0 := by
      have : w.re * w.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg w.re]
  apply Complex.ext <;> simp [h3]

open Polynomial in
private theorem conj_of_root (g : ℚ[X]) (hg : g ≠ 0) (hs : (g.map (algebraMap ℚ ℝ)).Splits) (w : ℂ)
    (h : aeval w g = 0) : starRingEnd ℂ w = w := by
  have h1 : g.map (algebraMap ℚ ℝ) ≠ 0 := Polynomial.map_ne_zero hg
  have h2 : w ∈ ((g.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).roots := by
    rw [mem_roots (Polynomial.map_ne_zero h1), IsRoot.def, eval_map_algebraMap, aeval_map_algebraMap]
    exact h
  rw [hs.roots_map] at h2
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h2
  exact Complex.conj_ofReal r

theorem UpperTheory.exists_totally_imaginary_generator_of_isCMField :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (f : M →+* Om l), IntermediateField.adjoin ℚ_[l] (Set.range f) = K.1 ∧ ∃ (δ : M) (d : ℚ_[l]), δ ≠ 0 ∧ f δ = algebraMap ℚ_[l] (Om l) d ∧ ∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ := by
  intro l hl K
  obtain ⟨β, g, hgm, hgs, hβ, hK⟩ := UpperTheory.exists_real_split_primitive_element_padic_finite_ext l K
  obtain ⟨d, hd⟩ := exists_sqrt l
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
  set D : Om l := algebraMap ℚ_[l] (Om l) d with hD
  have hD2 : D ^ 2 = 1 - 4 * (l : Om l) := by
    rw [hD, ← map_pow, hd]; simp [map_ofNat]
  have hβi : IsIntegral ℚ β := ⟨g, hgm, hβ⟩
  have hDi : IsIntegral ℚ D := by
    apply IsIntegral.of_pow two_pos
    rw [hD2]
    have : (1 - 4 * (l : Om l)) = algebraMap ℚ (Om l) (1 - 4 * l) := by simp
    rw [this]
    exact isIntegral_algebraMap
  let M : IntermediateField ℚ (Om l) := IntermediateField.adjoin ℚ {β, D}
  have hfd : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact hβi
    · exact hDi)
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  let b : M := ⟨β, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let δ : M := ⟨D, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hδ2 : δ ^ 2 = 1 - 4 * (l : M) := by
    apply (algebraMap M (Om l)).injective
    rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_natCast]
    exact hD2
  have hb : Polynomial.aeval b g = 0 := by
    apply (algebraMap M (Om l)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hβ
  have hδφ2 : ∀ φ : M →+* ℂ, φ δ ^ 2 = ((1 - 4 * l : ℝ) : ℂ) := fun φ => by
    rw [← map_pow, hδ2]; simp [map_ofNat]
  have hδc : ∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ := fun φ =>
    conj_of_sq _ _ (by linarith) (hδφ2 φ)
  have hδ0 : ∀ φ : M →+* ℂ, φ δ ≠ 0 := fun φ h => by
    have := hδφ2 φ
    rw [h, zero_pow two_ne_zero] at this
    have : (1 - 4 * l : ℝ) = 0 := by exact_mod_cast this.symm
    linarith
  have hbc : ∀ φ : M →+* ℂ, starRingEnd ℂ (φ b) = φ b := fun φ => by
    refine conj_of_root g hgm.ne_zero hgs _ ?_
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom b g
    rw [hb, map_zero] at this
    exact this
  have htc : IsTotallyComplex M := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 : starRingEnd ℂ (w.embedding δ) = w.embedding δ := RingHom.congr_fun h δ
    rw [hδc] at h1
    exact hδ0 w.embedding (by linear_combination (-1 / 2 : ℂ) * h1)⟩
  have hCM : IsCMField M := by
    refine isCM_of_conj _ ?_
    rintro ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨b, fun φ => (hbc φ).symm⟩
      · exact ⟨-δ, fun φ => by rw [map_neg]; exact (hδc φ).symm⟩
    | algebraMap a =>
      refine ⟨algebraMap ℚ M a, fun φ => ?_⟩
      change φ (algebraMap ℚ M a) = starRingEnd ℂ (φ (algebraMap ℚ M a))
      simp
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun φ => ?_⟩
      rw [map_add (f := _), ha, hb, ← map_add (f := _), ← map_add (f := _)]
      rfl
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨a⁻¹, fun φ => ?_⟩
      rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a * b, fun φ => ?_⟩
      rw [map_mul, ha, hb, ← map_mul, ← map_mul]
      rfl
  refine ⟨M, inferInstance, hNF, hCM, algebraMap M (Om l), ?_, δ, d, ?_, rfl, hδc⟩
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      have hβK : β ∈ K.1 := hK ▸ IntermediateField.mem_adjoin_simple_self _ β
      have hle : M.toSubfield ≤ K.1.toSubfield := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro y (⟨q, rfl⟩ | rfl | rfl)
        · simp
        · exact hβK
        · exact K.1.algebraMap_mem d
      exact hle x.2
    · rw [← hK, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩
  · intro h
    have φ : M →+* ℂ := Classical.choice inferInstance
    exact hδ0 φ (by rw [h, map_zero])
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankCoinvariantsEqFinrankLatticeCoinvariants
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G T V : Type} [Group G] [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℚ_[l] G V) (ρT : Representation ℤ_[l] G T) (j : T →ₗ[ℤ_[l]] V), Function.Injective j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) = finrank ℤ_[l] (T ⧸ coSub χ ρT) := by
  intro l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs
  set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN
  have hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l] := fun m =>
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) =
      ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x := by
    intro g x
    rw [map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]
    rfl
  have hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v := fun g c v => by
    rw [← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]
  let q : V →ₗ[ℤ_[l]] (V ⧸ N) := N.mkQ.restrictScalars ℤ_[l]
  have hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    change N.mkQ (j _) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]
    exact Submodule.subset_span ⟨g, j x, rfl⟩
  let f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N) := (coSub χ ρT).liftQ (q ∘ₗ j) hle
  have key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, x, rfl⟩ := hy
      obtain ⟨m, t, ht⟩ := hs x
      refine ⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩
      rw [hgen, ht, hρs, smul_sub, smul_comm]
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_mem hc hd, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) a
      refine ⟨c * s, mul_mem hc s.2, ?_⟩
      have : (s : ℤ_[l]) • a • x = r • x := by
        rw [← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by
    refine ⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨v, rfl⟩ := N.mkQ_surjective y
      obtain ⟨m, t, ht⟩ := hs v
      refine ⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩
      change (l : ℤ_[l]) ^ m • q v = q (j t)
      rw [ht, map_smul]
    · intro x y h
      obtain ⟨x, rfl⟩ := (coSub χ ρT).mkQ_surjective x
      obtain ⟨y, rfl⟩ := (coSub χ ρT).mkQ_surjective y
      have h' : j x - j y ∈ N := (Submodule.Quotient.eq N).1 h
      obtain ⟨c, hc, t, ht, e⟩ := key _ h'
      rw [← map_sub, ← map_smul] at e
      obtain rfl := hj e
      refine ⟨⟨c, hc⟩, ?_⟩
      change c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y
      rw [← map_smul, ← map_smul]
      refine (Submodule.Quotient.eq _).2 ?_
      rw [← smul_sub]; exact ht
  rw [IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsFirstOrderDeformationOfRZero
section
noncomputable section

namespace UpperTheory.V.Loc

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV IsLocalRing

def wtDer {O R X : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : X → Submodule O R) (x : R →ₐ[O] O)
    (E : Type) [Field E] [Algebra O E] (j : X) : Submodule E (R →ₗ[O] E) where
  carrier := {D | D ∈ PtDer ((Algebra.ofId O E).comp x) E ∧ HasWt 𝒜 j D}
  zero_mem' := ⟨zero_mem _, fun _ _ _ _ => rfl⟩
  add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun i hi f hf => by
    rw [LinearMap.add_apply, ha.2 i hi f hf, hb.2 i hi f hf, add_zero]⟩
  smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun i hi f hf => by
    rw [LinearMap.smul_apply, ha.2 i hi f hf, smul_zero]⟩

def dimsL (w : ℤ × ℤ) : ℕ :=
  if w = wAl ∨ w = wBe ∨ w = wPs ∨ w = wTh ∨ w = 0 then 2 else if w ∈ wts then 1 else 0

def dimsP (w : ℤ × ℤ) : ℕ := if w = 0 then 2 else if w ∈ wts then 1 else 0

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
  {B : Type} [CommRing B] [Algebra c.O B]

def EqL (r : D.Gp l →* M4 B) : Prop :=
  (∀ g : D.Gp l, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    Ord ((D.Ip l).subgroupOf (D.Gp l)) (fun i g => algebraMap c.O B (D.ps i g)) D.s0 r

def EqP (p : ℕ) (r : D.Gp p →* M4 B) : Prop :=
  (∀ g : D.Gp p, IsGSp (algebraMap c.O B (D.th g)) (r g)) ∧
    ∀ g : D.Gp p, (g : G ℚ Ω) ∈ D.Ip p ⊓ D.ψ.ker → r g = 1

structure IsContinuousLiftOfRZero [Algebra ℚ_[l] B] {E : Type} [CommRing E] [Algebra c.O E] (π : B →+* E) (v : ℕ)
    (r : D.Gp v →* M4 B) : Prop where
  red : mapRep π r = mapRep (algebraMap c.O E) (D.r0At v)
  cont : ∀ a b, QCont l fun g => r g a b

def IsFirstOrderDeformationOfRZero {E : Type} [CommRing E] [Algebra c.O E] (v : ℕ) (γ : D.Gp v → M4 E) (r' : D.Gp v →* M4 (DualNumber E)) :
    Prop :=
  ∀ g a b, r' g a b = ⟨algebraMap c.O E (D.r0At v g a b), (γ g * (D.r0At v g).map (algebraMap c.O E)) a b⟩

def FlagIn {H K : Type} [Group H] [CommRing K] (r : H →* M4 K) (h : (M4 K)ˣ) (κ : Fin 4 → H →* Kˣ) : Prop :=
  ∀ g, (∀ i j, j < i → ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i j = 0) ∧
    ∀ i, ((h⁻¹ : (M4 K)ˣ) * r g * h : M4 K) i i = (κ i g : K)

def PtOn {v : ℕ} (P : Cond c.O (D.rbarAt v)) {K : Type} [CommRing K] [Algebra c.O K] (r : D.Gp v →* M4 K) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : Algebra c.O R) (_ : IsCO c.O R) (ρ : Lift c.O (D.rbarAt v) R) (y : R →ₐ[c.O] K),
    OnComp P (D.r0At v) ρ ∧ r = mapRep (y : R →+* K) ρ.hom

end UpperTheory.V.Loc
end
end

