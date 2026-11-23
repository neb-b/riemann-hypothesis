module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0079

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsKMultiplicativeUnitOneHaarScaling
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open scoped Pointwise NNReal ENNReal

namespace GlobalTheory.JR.Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] (A : Et F E)

theorem secondCountable_K : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : A.K ≃ₜ (Fin (Module.finrank F A.K) → F) := ⟨e.toEquiv, h1, h2⟩
  exact h.isEmbedding.secondCountableTopology

theorem absK_unit (x : A.Kˣ) : A.absK (x : A.K) = (distribHaarChar A.K x : ℝ) := by
  unfold absK
  rw [dite_eq_left x.isUnit]
  congr 2
  ext; rfl

theorem absK_mul (s t : A.K) : A.absK (s * t) = A.absK s * A.absK t := by
  by_cases hs : IsUnit s
  · by_cases ht : IsUnit t
    · have e1 := A.absK_unit (hs.unit * ht.unit)
      have e2 := A.absK_unit hs.unit
      have e3 := A.absK_unit ht.unit
      simp only [Units.val_mul, IsUnit.unit_spec] at e1 e2 e3
      rw [e1, e2, e3, map_mul, NNReal.coe_mul]
    · have : ¬ IsUnit (s * t) := fun h => ht (IsUnit.mul_iff.1 h).2
      simp [absK, this, ht]
  · have : ¬ IsUnit (s * t) := fun h => hs (IsUnit.mul_iff.1 h).1
    simp [absK, this, hs]

theorem distribHaarChar_le_one_of_mem_OK (u : A.Kˣ) (hu : (u : A.K) ∈ A.OK) : distribHaarChar A.K u ≤ 1 := by
  haveI := A.secondCountable_K
  obtain ⟨-, -, -, -, -, -, -, -, -, hO, hC, R, hR⟩ := _root_.GlobalTheory.JR.EtFacts.main F E A
  let μ : Measure A.K := Measure.addHaar
  have h0 : (0 : A.K) ∈ A.OK := by rw [← hR]; exact R.zero_mem
  have hm0 : μ A.OK ≠ 0 := hO.measure_ne_zero μ ⟨0, h0⟩
  have hmt : μ A.OK ≠ ⊤ := hC.measure_lt_top.ne
  have hsub : u • A.OK ⊆ A.OK := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← hR] at hz hu ⊢
    exact R.mul_mem hu hz
  have hle : (distribHaarChar A.K u : ℝ≥0∞) * μ A.OK ≤ 1 * μ A.OK := by
    rw [distribHaarChar_mul μ u A.OK, one_mul]; exact measure_mono hsub
  have := (ENNReal.mul_le_mul_iff_left hm0 hmt).1 hle
  exact_mod_cast this

theorem absK_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s t : A.K, A.absK (s * t) = A.absK s * A.absK t) ∧ (∀ s s' : A.K, s ∈ A.OK → s' ∈ A.OK → s * s' = 1 → A.absK s = 1) ∧ (∀ (μ : Measure A.K), μ.IsAddHaarMeasure → ∀ (x : A.Kˣ) (a : A.K) (S : Set A.K), MeasurableSet S → μ {a' : A.K | (x : A.K) * a' - a ∈ S} = ENNReal.ofReal (A.absK (x : A.K))⁻¹ * μ S)) := by
  intro F E _ _ _ _ _ A
  refine ⟨A.absK_mul, ?_, ?_⟩
  · intro s s' hs hs' h
    let u : A.Kˣ := ⟨s, s', h, by rw [mul_comm]; exact h⟩
    have h1 := A.distribHaarChar_le_one_of_mem_OK u hs
    have h2 := A.distribHaarChar_le_one_of_mem_OK u⁻¹ hs'
    have hprod : distribHaarChar A.K u * distribHaarChar A.K u⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have : distribHaarChar A.K u = 1 := by
      refine le_antisymm h1 ?_
      calc (1 : ℝ≥0) = distribHaarChar A.K u * distribHaarChar A.K u⁻¹ := hprod.symm
        _ ≤ distribHaarChar A.K u * 1 := mul_le_mul_of_nonneg_left h2 zero_le'
        _ = distribHaarChar A.K u := mul_one _
    have e := A.absK_unit u
    change A.absK s = 1
    rw [show s = (u : A.K) from rfl, e, this, NNReal.coe_one]
  · intro μ hμ x a S _
    haveI := A.secondCountable_K
    have hset : {a' : A.K | (x : A.K) * a' - a ∈ S} = x⁻¹ • ((fun z => z + -a) ⁻¹' S) := by
      ext a'
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
      simp [Units.smul_def, sub_eq_add_neg]
    rw [hset, ← distribHaarChar_mul μ x⁻¹, measure_preimage_add_right, A.absK_unit, map_inv,
      ← NNReal.coe_inv, ENNReal.ofReal_coe_nnreal]

end GlobalTheory.JR.Et
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapDetRestrict
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.LatIndexDet

theorem val_algebraMap (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] {d : O} (hd : d ≠ 0) :
    val O (algebraMap O E d) = ((IsDiscreteValuationRing.addVal O d).toNat : ℤ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd hϖ
  have h1 : (IsDiscreteValuationRing.maximalIdeal O).intValuation ϖ = WithZero.exp (-1 : ℤ) :=
    (IsDiscreteValuationRing.maximalIdeal O).intValuation_singleton hϖ.ne_zero hϖ.maximalIdeal_eq
  have h2 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 := by
    refine le_antisymm ((IsDiscreteValuationRing.maximalIdeal O).intValuation_le_one _) (not_lt.1 fun h => ?_)
    have := ((IsDiscreteValuationRing.maximalIdeal O).intValuation_lt_one_iff_mem _).1 h
    exact (IsLocalRing.mem_maximalIdeal _).1 this u.isUnit
  rw [IsDiscreteValuationRing.addVal_def' u hϖ n]
  simp only [val, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, map_mul, map_pow, h1, h2,
    one_mul, ← WithZero.exp_nsmul, WithZero.log_exp, ENat.toNat_coe]
  simp

end GlobalTheory.LatIndexDet

namespace GlobalTheory.LatIndexDet

variable (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E]
  {V : Type} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]


include E in
theorem isTorsionFree_lat (N : Submodule O V) : Module.IsTorsionFree O N := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun r x h => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  · refine Or.inr (Subtype.ext ?_)
    have h' : r • (x : V) = 0 := congrArg Subtype.val h
    rw [← algebraMap_smul E r (x : V)] at h'
    have hr' : algebraMap O E r ≠ 0 := fun h0 => hr (IsFractionRing.injective O E (by rw [h0, map_zero]))
    exact (smul_eq_zero.1 h').resolve_left hr'

theorem algebraMap_det_restrict (N : Submodule O V) [Module.Free O N] [Module.Finite O N]
    (hspan : Submodule.span E (N : Set V) = ⊤) (T : V →ₗ[E] V) (hT : ∀ x ∈ N, T x ∈ N) :
    algebraMap O E (LinearMap.det ((T.restrictScalars O).restrict hT)) = LinearMap.det T := by
  classical
  let b := Module.Free.chooseBasis O N
  let bV : Module.Free.ChooseBasisIndex O N → V := fun i => (b i : V)
  have hliO : LinearIndependent O bV :=
    b.linearIndependent.map' N.subtype (Submodule.ker_subtype N)
  have hli : LinearIndependent E bV := (LinearIndependent.iff_fractionRing O E).1 hliO
  have hNle : (N : Set V) ⊆ Submodule.span E (Set.range bV) := by
    intro x hx
    have hx'' : x = ∑ i, b.repr ⟨x, hx⟩ i • bV i := by
      have h0 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h0
      simp only [Submodule.coe_smul] at h0
      exact h0.symm
    rw [hx'']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul E]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span E (Set.range bV) := by
    rw [← hspan]; exact Submodule.span_le.2 hNle
  let BE := Module.Basis.mk hli hsp
  let T' := (T.restrictScalars O).restrict hT
  have hmat : LinearMap.toMatrix BE BE T = (LinearMap.toMatrix b b T').map (algebraMap O E) := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply]
    have h1 : T (BE j) = ∑ k, algebraMap O E (b.repr (T' (b j)) k) • BE k := by
      have h2 : T' (b j) = ∑ k, b.repr (T' (b j)) k • b k := (b.sum_repr _).symm
      have h3 := congrArg Subtype.val h2
      simp only [Module.Basis.mk_apply, BE, bV]
      rw [show T (b j : V) = ((T' (b j) : N) : V) from rfl]
      conv_lhs => rw [h3]
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, algebraMap_smul]
    rw [h1, BE.repr_sum_self]
  rw [← LinearMap.det_toMatrix BE, hmat, ← LinearMap.det_toMatrix b T', RingHom.map_det]
  rfl

end GlobalTheory.LatIndexDet

namespace GlobalTheory.LatIndexDet

theorem card_quot_eq_pow_val : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (E : Type) [Field E] [Algebra O E] [IsFractionRing O E] (V : Type) [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V] [FiniteDimensional E V] (N : Submodule O V), N.FG → Submodule.span E (N : Set V) = ⊤ → ∀ T : V →ₗ[E] V, LinearMap.det T ≠ 0 → (∀ x ∈ N, T x ∈ N) → (Nat.card (↥N ⧸ (N.map (T.restrictScalars O)).comap N.subtype) : ℚ) = (Nat.card (IsLocalRing.ResidueField O) : ℚ) ^ val O (LinearMap.det T) := by
  intro O _ _ _ _ E _ _ _ V _ _ _ _ _ N hfg hspan T hdet hT
  haveI := isTorsionFree_lat O E N
  haveI : Module.Finite O N := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O N := Module.free_of_finite_type_torsion_free'
  let T' : N →ₗ[O] N := (T.restrictScalars O).restrict hT
  have hdetT : algebraMap O E (LinearMap.det T') = LinearMap.det T := algebraMap_det_restrict O E N hspan T hT
  have hdet' : LinearMap.det T' ≠ 0 := fun h => hdet (by rw [← hdetT, h, map_zero])
  have hrange : (N.map (T.restrictScalars O)).comap N.subtype = LinearMap.range T' := by
    ext ⟨x, hx⟩
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_map, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyx⟩
    · rintro ⟨⟨y, hy⟩, hyx⟩
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  rw [hrange, GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det T' hdet', ← hdetT, val_algebraMap O E hdet']
  push_cast
  rw [zpow_natCast]

end GlobalTheory.LatIndexDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOverExtIntegralReductionPow
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

theorem charpoly_overExt_integral_reduction : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (hO : ∀ y : K'.O, ψ (algebraMap K'.O K'.E y) ∈ Algebra.adjoin K.O ({B.g} : Set B.A)) (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))), B.P.Separable → IsIntegral K.O B.g → ∀ s : K'.O, @IsLocalRing.residue _ _ hl ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩ = @IsLocalRing.residue _ _ hl ⟨ψ (algebraMap K'.O K'.E s), hO s⟩ → ∃ Q : K'.O[X], Q.map (algebraMap K'.O K'.E) = (overExt φ B ψ hψ hσ).P ∧ Q.map (IsLocalRing.residue K'.O) = (X - C (IsLocalRing.residue K'.O s)) ^ Q.natDegree := by
  intro K K' d φ hU B ψ hψ hσ hO hl hsep hint s hres
  set S := Algebra.adjoin K.O ({B.g} : Set B.A) with hSdef
  letI : Algebra K'.E B.A := ψ.toAlgebra
  letI : Algebra K'.O B.A := (ψ.comp (algebraMap K'.O K'.E)).toAlgebra
  haveI : IsScalarTower K'.O K'.E B.A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite K'.E B.A := (overExt φ B ψ hψ hσ).fd
  let f0 : K'.O →+* S := (ψ.comp (algebraMap K'.O K'.E)).codRestrict S hO
  letI : Algebra K'.O S := f0.toAlgebra
  let ι : S →ₐ[K'.O] B.A := { S.val.toRingHom with commutes' := fun _ => rfl }
  have hinj : Function.Injective ι := Subtype.val_injective
  haveI : Module.Finite K.O S := Algebra.finite_adjoin_simple_of_isIntegral hint
  haveI : Module.Finite K'.O S := by
    obtain ⟨T, hT⟩ := (inferInstance : Module.Finite K.O S).fg_top
    refine ⟨⟨T, eq_top_iff.2 fun y hy0 => ?_⟩⟩
    clear hy0
    have hy : y ∈ Submodule.span K.O (T : Set S) := hT ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul a x _ hx =>
      obtain ⟨y', hy'⟩ := GlobalTheory.T.unramifiedInvolutionExt_maps_integers_to_integers K K' d φ hU a
      have h : a • x = y' • x := by
        apply Subtype.ext
        rw [Algebra.smul_def, Algebra.smul_def, MulMemClass.coe_mul, MulMemClass.coe_mul]
        change algebraMap K.O B.A a * (x : B.A) = ψ (algebraMap K'.O K'.E y') * (x : B.A)
        rw [hy', hψ, ← IsScalarTower.algebraMap_apply]
      rw [h]; exact Submodule.smul_mem _ _ hx
  have hspan : Submodule.span K'.E (Set.range ι) = ⊤ := by
    refine eq_top_iff.2 fun y hy0 => ?_
    clear hy0
    have hy : y ∈ Submodule.span K.E (Set.range fun i : ℕ => B.g ^ i) := GlobalTheory.T.span_pow_generator_eq_top_of_charpoly_separable K B hsep ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨B.g ^ i, pow_mem (Algebra.self_mem_adjoin_singleton K.O B.g) i⟩, rfl⟩
    | zero => exact zero_mem _
    | add x z _ _ hx hz => exact add_mem hx hz
    | smul e x _ hx =>
      have h : e • x = (φ e) • x := by
        rw [Algebra.smul_def, Algebra.smul_def, ← hψ e]; rfl
      rw [h]; exact Submodule.smul_mem _ _ hx
  haveI : IsLocalRing S := hl
  obtain ⟨n, b, hb⟩ := GlobalTheory.T.charpoly_mulLeft_eq_map_of_span_range_eq K'.O K'.E B.A S ι hinj hspan
  let x0 : S := ⟨B.g, Algebra.self_mem_adjoin_singleton K.O B.g⟩
  refine ⟨(LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0)).charpoly, (hb x0).symm, ?_⟩
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, ← Matrix.charpoly_map]
  set t : S := x0 - algebraMap K'.O S s with ht
  have htm : t ∈ IsLocalRing.maximalIdeal S := by
    rw [ht, ← Ideal.Quotient.eq]; exact hres
  have hsplit : LinearMap.toMatrix b b (LinearMap.mulLeft K'.O x0) =
      LinearMap.toMatrix b b (LinearMap.mulLeft K'.O t) + Matrix.scalar (Fin n) s := by
    have : LinearMap.mulLeft K'.O x0 = LinearMap.mulLeft K'.O t + s • LinearMap.id := by
      ext y; simp [ht, Algebra.smul_def, sub_mul]
    rw [this, map_add (f := _), map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal]; rfl
  rw [hsplit, Matrix.map_add _ (map_add _)]
  have hsc : (Matrix.scalar (Fin n) s).map (IsLocalRing.residue K'.O) = Matrix.scalar (Fin n) (IsLocalRing.residue K'.O s) := by
    ext i j; simp [Matrix.scalar_apply, Matrix.diagonal_apply]; split_ifs <;> simp
  rw [hsc]
  exact _root_.GlobalTheory.charpoly_nilpotent_add_scalar _ n _ _ (_root_.GlobalTheory.isNilpotent_residue_toMatrix_mulLeft K'.O S n b t htm)

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitPadicComplex
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

theorem eventually_apply_eq {l : ℕ} [Fact l.Prime] (x : Om l) (g₀ : GQ l) :
    ∀ᶠ g : GQ l in nhds g₀, g x = g₀ x := by
  have hS := stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x
  have hc : Continuous fun g : GQ l => g₀⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GQ l => g₀⁻¹ * g) g₀ ∈ (MulAction.stabilizer (GQ l) x : Set (GQ l)) := by
    simp
  filter_upwards [hc.continuousAt.preimage_mem_nhds (hS.mem_nhds hmem)] with g hg
  have hg' : (g₀⁻¹ * g) x = x := hg
  have := congrArg g₀ hg'
  simpa [AlgEquiv.mul_apply] using this

theorem IsActC.continuous_orbit (l : ℕ) [Fact l.Prime]
    (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (h : IsActC act) (y : PadicComplex l) :
    Continuous (fun g => act g y) := by
  obtain ⟨hext, hiso⟩ := h
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨x, hx⟩ : ∃ x : Om l, dist y (x : PadicComplex l) < ε / 2 :=
    UniformSpace.Completion.denseRange_coe.exists_dist_lt y (half_pos hε)
  filter_upwards [eventually_apply_eq x g₀] with g hg
  have h1 : act g y - act g₀ y = act g (y - x) - act g₀ (y - x) := by
    rw [map_sub, map_sub, hext g x, hext g₀ x, hg]
    ring
  rw [dist_eq_norm, h1]
  calc ‖act g (y - x) - act g₀ (y - x)‖ ≤ ‖act g (y - x)‖ + ‖act g₀ (y - x)‖ := norm_sub_le _ _
    _ = 2 * ‖y - x‖ := by rw [hiso, hiso]; ring
    _ < ε := by rw [← dist_eq_norm]; linarith

end GlobalTheory.Cyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem
section
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr GlobalTheory.WachTie

noncomputable section

namespace GlobalTheory.WachTie

theorem coord_injective_range_mem : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) {l : ℕ} (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧) (jE : (ZMod n → R.EE) →ₐ[O] W.EE) (T : LocLat G Qp LL O) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)), FrTie W R j → EETie W R j jE → (∀ k, (b k : W.DD T) ∈ W.NΔ T) → IsCrys PD T.ρ → Function.Injective (coord W R jE T (fun k => (b k : W.DD T))) ∧ LinearMap.range (coord W R jE T (fun k => (b k : W.DD T))) = DDinv W T ∧ ∀ x, coord W R jE T (fun k => (b k : W.DD T)) x ∈ W.NΔ T ↔ ∀ i, x i ∈ R.N0 r := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W l R j jE T r b
    hF hE hb hc
  obtain ⟨-, hFr, -⟩ := hF
  obtain ⟨hext, hinj, hEr, -⟩ := hE
  let c : Module.Basis (Fin r) W.EE (W.DD T) := (W.N_base T hc).basis b
  have hcb : ∀ k, c k = (b k : W.DD T) := fun k => IsBaseChange.basis_apply b (W.N_base T hc) k
  have huniq : ∀ y y' : Fin r → W.EE,
      ∑ k, y k • (b k : W.DD T) = ∑ k, y' k • (b k : W.DD T) → y = y' := by
    intro y y' h
    apply c.equivFun.symm.injective
    simp only [Module.Basis.equivFun_symm_apply, hcb]
    exact h
  have hex : ∀ m : W.DD T, ∃ y : Fin r → W.EE, ∑ k, y k • (b k : W.DD T) = m := by
    intro m
    refine ⟨c.repr m, ?_⟩
    simp only [← hcb]
    exact c.sum_repr m
  have hγ : ∀ δ ∈ W.DelF, ∀ y : Fin r → W.EE, W.γD T δ (∑ k, y k • (b k : W.DD T)) =
      ∑ k, W.γE δ (y k) • (b k : W.DD T) := by
    intro δ hδ y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [W.γD_smul, (hb k).2 δ hδ]
  have hinv : ∀ x, ∀ δ ∈ W.DelF, W.γD T δ (coord W R jE T (fun k => (b k : W.DD T)) x) =
      coord W R jE T (fun k => (b k : W.DD T)) x := by
    intro x δ hδ
    rw [coord_apply, hγ δ hδ]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hEr _).1 ⟨_, rfl⟩ δ hδ]
  refine ⟨?_, ?_, ?_⟩
  · intro x x' h
    have := huniq _ _ h
    funext i k
    exact congrFun (hinj (congrFun this k)) i
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hinv x
    · intro m hm
      obtain ⟨y, rfl⟩ := hex m
      have hy : ∀ k, ∃ x, jE x = y k := fun k => (hEr _).2 fun δ hδ =>
        congrFun (huniq _ _ ((hγ δ hδ y).symm.trans (hm δ hδ))) k
      choose x hx using hy
      refine ⟨fun i k => x k i, ?_⟩
      rw [coord_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← hx k]
  · intro x
    constructor
    · rintro ⟨hN, -⟩
      set a := b.repr ⟨_, hN⟩ with ha
      have h1 : ∑ k, algebraMap (LetA O n) W.EE (a k) • (b k : W.DD T) =
          ∑ k, jE (fun i => x i k) • (b k : W.DD T) := by
        have := congrArg (W.N T).subtype (b.sum_repr ⟨_, hN⟩)
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum] at this
        simp only [algebraMap_smul]
        exact this
      have h2 := huniq _ _ h1
      intro i k _
      have h3 : algebraMap (LetA O n) W.EE (a k) = jE (fun i => x i k) := congrFun h2 k
      have h4 : ∀ i', ∃ a', j a' = a k i' := fun i' => (hFr _).2 fun δ hδ => by
        have h5 := (hEr _).1 ⟨_, h3.symm⟩ δ hδ
        rw [W.γE_ext] at h5
        exact congrFun (W.EE_inj h5) i'
      choose a' ha' using h4
      have h6 : jE (fun i => R.ι (a' i)) = jE (fun i => x i k) := by
        rw [hext, ← h3]
        congr 1
        funext i'
        exact ha' i'
      exact ⟨a' i, congrFun (hinj h6) i⟩
    · intro hx
      refine ⟨?_, hinv x⟩
      rw [coord_apply]
      refine Submodule.sum_mem _ fun k _ => ?_
      have h4 : ∀ i, ∃ a', R.ι a' = x i k := fun i => hx i k (Set.mem_univ _)
      choose a' ha' using h4
      have : (fun i => x i k) = fun i => R.ι (a' i) := funext fun i => (ha' i).symm
      rw [this, hext, algebraMap_smul]
      exact (W.N T).smul_mem _ (b k).2

end GlobalTheory.WachTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupOrbitRootSameStabilizerStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decompositionGroup_orbit_root_same_stabilizer : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (β β' : Ω) (S : Finset Ω), (∀ x, x ∈ S ↔ ∃ d ∈ Dec (F := E) A, d β = x) → ∀ g : Polynomial E, g.Monic → g.natDegree = S.card → aeval β' g = 0 → (∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β) → (∀ σ : G E Ω, ∃ d ∈ Dec (F := E) A, σ β' = d β') ∧ (∀ σ ∈ Dec (F := E) A, σ β = β → σ β' = β') := by
  first | exact @GlobalTheory.Count.decOrbit_root_count | exact GlobalTheory.Count.decOrbit_root_count | (intros; apply GlobalTheory.Count.decOrbit_root_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetTracePowAddMulUnitNeZero
section
open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.TraceDet

theorem det_trace_pow_mul_ne_zero : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ u : B.A, IsUnit u →
    (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
      Algebra.trace K.E B.A (B.g ^ ((k : ℕ) + (l : ℕ)) * u)).det ≠ 0 := by
  intro K B hsep u hu hdet
  classical
  obtain ⟨e, he⟩ := _root_.GlobalTheory.UnitLemma.exists_basis_pow_of_separable K B hsep
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  set w : B.A := ∑ l, v l • e l with hw
  have hk : ∀ k, Algebra.trace K.E B.A ((w * u) * e k) = 0 := by
    intro k
    have := congrFun hv k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, hw, Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, map_smul, smul_eq_mul, he, he, pow_add]
    rw [mul_comm (v l)]
    congr 1
    congr 1
    ring
  have hz : w * u = 0 := by
    apply GlobalTheory.UnitLemma.Centraliser.eq_zero_of_trace_mul B hsep
    intro y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr y, Finset.mul_sum, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_smul_comm, map_smul, hk k, smul_zero]
  have hw0 : w = 0 := (hu.mul_left_eq_zero).1 hz
  apply hv0
  exact (Fintype.linearIndependent_iff.1 e.linearIndependent) v hw0 |> funext

end GlobalTheory.UnitLemma.TraceDet
end

