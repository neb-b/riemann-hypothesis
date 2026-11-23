module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeFourthProperty
section
open MeasureTheory Polynomial

namespace GlobalTheory.CompanionTheory.TfLoc

open PositivityTheory.Rg.Tf.Loc

theorem commute_aeval_right {K : Type*} [Field K] {n : ℕ} {A M : Matrix (Fin n) (Fin n) K}
    (hc : Commute A M) (p : K[X]) : Commute A (aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using hp.add_right hq
  | monomial m a =>
    rw [aeval_monomial]
    exact (Algebra.commute_algebraMap_right a A).mul_right (hc.pow_right m)

theorem transport_open_trace : D0a → T0 → A1 → MeasureTransportOpenSet := by
  intro hD _ hA
  unfold D0a at hD
  unfold A1 at hA
  unfold MeasureTransportOpenSet
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hur σ hgen n _ _ _ _ SE Sk hSE hSk δ γ h μδ μγ hreg hN hmap y z hz
  have hinc : Continuous (fun g : GL (Fin n) k => (incl g : GL (Fin n) E)) :=
    (hD k E hur σ hgen).2.2.2.2.2 n
  have hcf : Continuous (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) :=
    (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hci : Continuous (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) :=
    hinc.comp continuous_subtype_val

  have hsep : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly.Separable := by
    have h0 := hreg
    unfold IsTwRegSemisimple at h0
    rw [hN, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj] at h0
    exact h0
  obtain ⟨p, hp⟩ := hA E n _ hsep (z : Matrix (Fin n) (Fin n) E) hz

  have hzt : ∀ t : Subgroup.centralizer {γ},
      z * incl (t : GL (Fin n) k) = incl (t : GL (Fin n) k) * z := by
    intro t
    have ht : (t : GL (Fin n) k) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.mp t.2
    have hc : Commute ((incl (t : GL (Fin n) k) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)
        ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) := by
      have := congrArg (fun g => ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) ht
      simpa [Commute, SemiconjBy, map_mul, Units.val_mul] using this
    have hc2 := commute_aeval_right hc p
    rw [← hp] at hc2
    exact Units.ext hc2.symm.eq
  set S' : Set (GL (Fin n) E) := {w | (z * incl y)⁻¹ * w * (z * incl y) ∈ SE} with hS'
  have hopen : IsOpen S' :=
    hSE.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  have hmeas : MeasurableSet S' := hopen.measurableSet
  have e1 : μδ {x | (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) ∈ SE} =
      Measure.map (fun x : twCent (sigmaGL σ) δ => h⁻¹ * (x : GL (Fin n) E) * h) μδ S' := by
    rw [Measure.map_apply hcf.measurable hmeas]
    congr 1
    ext x
    have : (h * z * incl y)⁻¹ * (x : GL (Fin n) E) * (h * z * incl y) =
        (z * incl y)⁻¹ * (h⁻¹ * (x : GL (Fin n) E) * h) * (z * incl y) := by group
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this]
  have e2 : Measure.map (fun t : Subgroup.centralizer {γ} => incl (t : GL (Fin n) k)) μγ S' =
      μγ {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ Sk} := by
    rw [Measure.map_apply hci.measurable hmeas]
    congr 1
    ext t
    have : (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y) =
        incl (y⁻¹ * (t : GL (Fin n) k) * y) := by
      calc (z * incl y)⁻¹ * incl (t : GL (Fin n) k) * (z * incl y)
          = (incl y)⁻¹ * (z⁻¹ * (incl (t : GL (Fin n) k) * z)) * incl y := by group
        _ = (incl y)⁻¹ * (z⁻¹ * (z * incl (t : GL (Fin n) k))) * incl y := by rw [hzt t]
        _ = (incl y)⁻¹ * incl (t : GL (Fin n) k) * incl y := by group
        _ = incl (y⁻¹ * (t : GL (Fin n) k) * y) := by simp only [map_mul, map_inv]
    simp only [Set.mem_preimage, hS', Set.mem_ofPred_eq, this, hSk]
  rw [e1, hmap, e2]

end GlobalTheory.CompanionTheory.TfLoc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedExtensionIntegralBasis
section
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.UnramDict

section
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem t2Space_isNonarchimedeanLocalField_singleBlock : T2Space K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance

theorem exists_pow_lt_value {a γ : ValueGroupWithZero K} (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ m < γ := by
  have e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have : MulArchimedean (ValueGroupWithZero K) := .comap e.toMonoidHom e.strictMono
  exact exists_pow_lt₀ ha (Units.mk0 γ hγ)

variable {K}

theorem exists_value_eq_zpow {π : K} (h0 : valuation K π ≠ 0) (h1 : valuation K π < 1)
    (hmax : ∀ x : K, valuation K x < 1 → valuation K x ≤ valuation K π) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation K x = valuation K π ^ m := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hb0 : e (valuation K π) ≠ 0 := by
    intro h
    exact h0 (e.injective (h.trans (map_zero e).symm))
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have hey : e (valuation K y) = WithZero.exp (-1 : ℤ) := by rw [hy]; simp
  have hy1 : valuation K y < 1 := by
    rw [← e.strictMono.lt_iff_lt, hey, map_one, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hle : e (valuation K y) ≤ e (valuation K π) := e.strictMono.monotone (hmax y hy1)
  have hlt : e (valuation K π) < 1 := by simpa using e.strictMono h1
  have hb : e (valuation K π) = WithZero.exp (-1 : ℤ) := by
    obtain ⟨b, hbe⟩ : ∃ b : ℤ, e (valuation K π) = WithZero.exp b := ⟨_, (WithZero.exp_log hb0).symm⟩
    rw [hbe] at hle hlt ⊢
    rw [hey, WithZero.exp_le_exp] at hle
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
    congr 1
    omega
  have hx0 : e (valuation K x) ≠ 0 := by
    intro h
    exact (Valuation.ne_zero_iff _).2 hx (e.injective (h.trans (map_zero e).symm))
  refine ⟨-WithZero.log (e (valuation K x)), e.injective ?_⟩
  have hz : (WithZero.exp (-1 : ℤ)) ^ (-WithZero.log (e (valuation K x))) =
      e (valuation K x) := by
    rw [← WithZero.exp_zsmul]
    simpa using WithZero.exp_log hx0
  show e (valuation K x) = e (valuation K π ^ (-WithZero.log (e (valuation K x))))
  rw [map_zpow₀ e, hb, hz]

end

section Matrices

theorem mem_unitGL_iff {F : Type*} [Field F] [ValuativeRel F] {n : ℕ} (g : GL (Fin n) F) :
    g ∈ unitGL (n := Fin n) F ↔
      (∀ i j, (g : Matrix (Fin n) (Fin n) F) i j ∈ intO F) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ intO F := by
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨fun i j => ((h : Matrix (Fin n) (Fin n) (intO F)) i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact (((h⁻¹ : GL (Fin n) (intO F)) : Matrix (Fin n) (Fin n) (intO F)) i j).2
  · rintro ⟨hA, hB⟩
    let f : intO F →+* F := (intO F).subtype
    let A : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hA i j⟩
    let B : Matrix (Fin n) (Fin n) (intO F) := fun i j => ⟨_, hB i j⟩
    have hinj : Function.Injective (f.mapMatrix (m := Fin n)) :=
      Matrix.map_injective Subtype.val_injective
    have hAf : f.mapMatrix A = (g : Matrix (Fin n) (Fin n) F) := by ext i j; rfl
    have hBf : f.mapMatrix B = ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
      ext i j; rfl
    have hAB : A * B = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.mul_inv g)
    have hBA : B * A = 1 := hinj (by rw [map_mul, hAf, hBf, map_one]; exact Units.inv_mul g)
    exact ⟨⟨A, B, hAB, hBA⟩, Units.ext hAf⟩

end Matrices

section Extension

variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]

theorem value_algebraMap_le_iff [ValuativeExtension k E] (a b : k) :
    valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔
      valuation k a ≤ valuation k b := by
  rw [← Valuation.Compatible.vle_iff_le, ← Valuation.Compatible.vle_iff_le,
    ValuativeExtension.vle_iff_vle]

theorem tendsto_pow_zero {x : E} (hx : valuation E x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E hx hγ
  filter_upwards [eventually_ge_atTop m] with n hn
  show valuation E (x ^ n) < γ
  rw [map_pow]
  exact (pow_le_pow_right_of_le_one' hx.le hn).trans_lt hm

theorem continuous_algebraMap_of_lt_one [ValuativeExtension k E] {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1) :
    Continuous (algebraMap k E) := by
  refine continuous_of_continuousAt_zero (algebraMap k E) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero' E).tendsto_right_iff]
  intro γ hγ
  obtain ⟨m, hm⟩ := exists_pow_lt_value E h1 hγ
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at h0
  have hmem : {a : k | valuation k a < valuation k (π ^ m)} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_of_mem (by simpa using pow_ne_zero m hπ0)
  filter_upwards [hmem] with a ha
  have h2 : valuation E (algebraMap k E a) < valuation E (algebraMap k E (π ^ m)) := by
    rw [← not_le, value_algebraMap_le_iff, not_le]
    exact ha
  show valuation E (algebraMap k E a) < γ
  refine h2.trans_le ?_
  rw [map_pow, map_pow]
  exact hm.le

theorem continuous_linearMap [FiniteDimensional k E] [ContinuousSMul k E] (f : E →ₗ[k] E) :
    Continuous f := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField k := Valued.toNontriviallyNormedField k (ValueGroupWithZero k)
  haveI := t2Space_isNonarchimedeanLocalField_singleBlock E
  exact f.continuous_of_finiteDimensional

theorem value_lt_one_of_continuous (τ : E ≃ₐ[k] E) (hτ : Continuous τ) {x : E}
    (hx : valuation E x < 1) : valuation E (τ x) < 1 := by
  have ht : Tendsto (fun n : ℕ => τ (x ^ n)) atTop (𝓝 0) := by
    have h := (hτ.tendsto 0).comp (tendsto_pow_zero hx)
    rw [map_zero] at h
    exact h
  have hmem : {y : E | valuation E y < 1} ∈ 𝓝 (0 : E) :=
    (IsValuativeTopology.hasBasis_nhds_zero' E).mem_of_mem one_ne_zero
  obtain ⟨n, hn, hn0⟩ := ((ht.eventually hmem).and (eventually_gt_atTop 0)).exists
  by_contra hc
  have h1 : 1 ≤ valuation E (τ x) ^ n := one_le_pow₀ (not_lt.1 hc)
  have h2 : valuation E (τ (x ^ n)) < 1 := hn
  rw [map_pow, map_pow] at h2
  exact absurd h2 (not_lt.2 h1)

theorem value_le_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x ≤ 1) : valuation E (τ x) ≤ 1 := by
  by_contra h
  have h1 : 1 < valuation E (τ x) := not_le.1 h
  have hy0 : valuation E (τ x) ≠ 0 := (zero_lt_one.trans h1).ne'
  have h2 : valuation E (τ x)⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ h1
  have h3 := value_lt_one_of_continuous τ.symm (hc _) h2
  rw [map_inv₀, AlgEquiv.symm_apply_apply, map_inv₀] at h3
  have hx0 : valuation E x ≠ 0 := by
    intro h0
    have : x = 0 := (Valuation.zero_iff _).1 h0
    simp [this] at hy0
  exact absurd ((inv_lt_one₀ (zero_lt_iff.2 hx0)).1 h3) (not_lt.2 hx)

theorem value_eq_one_of_continuous (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) (τ : E ≃ₐ[k] E) {x : E}
    (hx : valuation E x = 1) : valuation E (τ x) = 1 := by
  refine le_antisymm (value_le_one_of_continuous hc τ hx.le) ?_
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 : valuation E x⁻¹ ≤ 1 := by rw [map_inv₀, hx, inv_one]
  have h2 := value_le_one_of_continuous hc τ h1
  rw [map_inv₀, map_inv₀] at h2
  have hy0 : valuation E (τ x) ≠ 0 := by simpa using hx0
  exact (inv_le_one₀ (zero_lt_iff.2 hy0)).1 h2

theorem value_map_eq (hc : ∀ τ : E ≃ₐ[k] E, Continuous τ) {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1)
    (hmax : ∀ x : E, valuation E x < 1 → valuation E x ≤ valuation E (algebraMap k E π))
    (τ : E ≃ₐ[k] E) (x : E) : valuation E (τ x) = valuation E x := by
  by_cases hx : x = 0
  · simp [hx]
  obtain ⟨m, hm⟩ := exists_value_eq_zpow h0 h1 hmax hx
  set p := algebraMap k E π with hp
  have hy : valuation E (x * p ^ (-m)) = 1 := by
    rw [map_mul, map_zpow₀, hm, ← zpow_add₀ h0]
    simp
  have h2 := value_eq_one_of_continuous hc τ hy
  rw [map_mul, map_zpow₀ τ, hp, τ.commutes, ← hp, map_mul, map_zpow₀, zpow_neg,
    mul_inv_eq_one₀ (zpow_ne_zero _ h0)] at h2
  rw [h2, hm]

end Extension

theorem unramifiedDictionary_a : PositivityTheory.Rg.Tf.Loc.D0a := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ hun σ _
  obtain ⟨π, h1, hmax⟩ := hun
  have h0 : valuation E (algebraMap k E π) ≠ 0 := by
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation E)
    intro h
    have := hmax r hr1
    rw [h] at this
    exact hr0 ((Valuation.zero_iff _).1 (le_antisymm this zero_le'))
  have hcont := continuous_algebraMap_of_lt_one h0 h1
  haveI : ContinuousSMul k E := continuousSMul_of_algebraMap k E hcont
  have hc : ∀ τ : E ≃ₐ[k] E, Continuous τ := fun τ => continuous_linearMap τ.toLinearMap
  have hval := value_map_eq hc h0 h1 hmax
  have hint : ∀ a : k, algebraMap k E a ∈ intO E ↔ a ∈ intO k := by
    intro a
    have := value_algebraMap_le_iff (E := E) a 1
    simpa [Valuation.mem_integer_iff] using this
  refine ⟨hval, hint, ?_, ?_, hcont, ?_⟩
  · intro n g
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hint _) (forall₂_congr fun i j => hint _)
  · intro τ n g
    have hτ : ∀ x : E, τ x ∈ intO E ↔ x ∈ intO E := by
      intro x
      simp only [Valuation.mem_integer_iff, hval]
    rw [mem_unitGL_iff, mem_unitGL_iff, ← map_inv]
    exact and_congr (forall₂_congr fun i j => hτ _) (forall₂_congr fun i j => hτ _)
  · intro n
    exact Continuous.units_map _ (continuous_id.matrix_map hcont)

end GlobalTheory.CompanionTheory.UnramDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuotientCard
section
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens

private def mulPow {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : R →+ R ⧸ lev ϖ (k + 1) :=
  ((Ideal.Quotient.mk (lev ϖ (k + 1))).toAddMonoidHom).comp (AddMonoidHom.mulLeft (ϖ ^ k))

private theorem mulPow_apply {R : Type} [CommRing R] (ϖ : R) (k : ℕ) (a : R) :
    mulPow ϖ k a = Ideal.Quotient.mk (lev ϖ (k + 1)) (ϖ ^ k * a) := rfl

private theorem lev_succ_le {R : Type} [CommRing R] (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k := by
  exact Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ϖ (Nat.le_succ k))

private theorem mulPow_ker {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    (mulPow ϖ k).ker = (lev ϖ 1).toAddSubgroup := by
  ext a
  rw [AddMonoidHom.mem_ker, mulPow_apply, Ideal.Quotient.eq_zero_iff_mem, Submodule.mem_toAddSubgroup]
  simp only [lev, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hinj : Function.Injective (fun y : R => ϖ ^ k • y) := hr.pow k
    apply hinj
    show ϖ ^ k • a = ϖ ^ k • (ϖ ^ 1 * c)
    rw [smul_eq_mul, smul_eq_mul, hc]
    ring
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc]; ring⟩

theorem card_quot_lev_succ {R : Type} [CommRing R] {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) :
    Nat.card (R ⧸ lev ϖ (k + 1)) = Nat.card (R ⧸ lev ϖ 1) * Nat.card (R ⧸ lev ϖ k) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : R ⧸ lev ϖ (k + 1) →+ R ⧸ lev ϖ k,
      ∀ a, φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a :=
    ⟨(Ideal.Quotient.lift (lev ϖ (k + 1)) (Ideal.Quotient.mk (lev ϖ k))
      (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (lev_succ_le ϖ k ha))).toAddMonoidHom,
      fun a => by simp⟩
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ a, hφ a⟩
  have hker : φ.ker = (mulPow ϖ k).range := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [AddMonoidHom.mem_ker, hφ, AddMonoidHom.mem_range, Ideal.Quotient.eq_zero_iff_mem]
    constructor
    · intro ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
      exact ⟨c, by rw [mulPow_apply, ← hc]⟩
    · rintro ⟨c, hc⟩
      rw [mulPow_apply, Ideal.Quotient.eq] at hc
      have h1 : ϖ ^ k * c - a ∈ lev ϖ k := lev_succ_le ϖ k hc
      have h2 : ϖ ^ k * c ∈ lev ϖ k := Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
      have := sub_mem h2 h1
      simpa using this
  have e1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker
  have e2 : Nat.card ((R ⧸ lev ϖ (k + 1)) ⧸ φ.ker) = Nat.card (R ⧸ lev ϖ k) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  have e3 : Nat.card φ.ker = Nat.card (R ⧸ lev ϖ 1) := by
    rw [hker]
    have := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (mulPow ϖ k)).toEquiv
    rw [← this, mulPow_ker hr]
    rfl
  rw [e1, e2, e3]
  ring

theorem card_quot_lev : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ k : ℕ, Nat.card (R ⧸ lev ϖ k) = q ^ (2 * k) := by
  intro R _ σ ϖ q ε hR k
  induction k with
  | zero =>
    have htop : lev ϖ 0 = ⊤ := by
      show Ideal.span {ϖ ^ 0} = ⊤
      rw [pow_zero]
      exact Ideal.span_singleton_one
    rw [Nat.mul_zero, pow_zero]
    exact Nat.card_eq_one_iff_unique.mpr ⟨Ideal.Quotient.subsingleton_iff.mpr htop, ⟨0⟩⟩
  | succ k ih =>
    rw [card_quot_lev_succ hR.reg k, ih, hR.card]
    ring

end GlobalTheory.CompanionTheory.UnrDens
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationOfLocalDichotomy
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.Idem

theorem val_of_dich : ∀ {S : Type} [CommRing S] (ϖ : S),
    (∀ m : Ideal S, m.IsMaximal → Dich (Ideal.Quotient.mk (compI m) ϖ)) → Val ϖ := by
  intro S _ ϖ hD f g hfg
  obtain ⟨N, hN⟩ := hfg
  let Q : S → Prop := fun e => ∃ d, IsIdempotentElem d ∧ d * e = d ∧ d * f ∈ Ideal.span {g} ∧
    (e - d) * g ∈ Ideal.span {f}
  have hQ1 : Q 1 := by
    apply GlobalTheory.CompanionTheory.Idem.glue_idempotent_property Q
    · exact ⟨0, IsIdempotentElem.zero, by simp, by simp, by simp⟩
    · rintro e e' he he' ⟨d, hd, hde, hdf, hdg⟩
      refine ⟨d * e', hd.mul he', ?_, ?_, ?_⟩
      · calc d * e' * (e * e') = (d * e) * (e' * e') := by ring
          _ = d * e' := by rw [hde, he'.eq]
      · rw [mul_comm d e', mul_assoc]
        exact Ideal.mul_mem_left _ _ hdf
      · have h3 : (e * e' - d * e') * g = e' * ((e - d) * g) := by ring
        rw [h3]
        exact Ideal.mul_mem_left _ _ hdg
    · rintro e e' he he' hee ⟨d, hd, hde, hdf, hdg⟩ ⟨d', hd', hde', hdf', hdg'⟩
      have hdd : d * d' = 0 := by
        calc d * d' = (d * e) * (d' * e') := by rw [hde, hde']
          _ = (d * d') * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h1 : d * e' = 0 := by
        calc d * e' = (d * e) * e' := by rw [hde]
          _ = d * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      have h2 : d' * e = 0 := by
        calc d' * e = (d' * e') * e := by rw [hde']
          _ = d' * (e * e') := by ring
          _ = 0 := by rw [hee, mul_zero]
      refine ⟨d + d', ?_, ?_, ?_, ?_⟩
      · show (d + d') * (d + d') = d + d'
        calc (d + d') * (d + d') = d * d + d' * d' + 2 * (d * d') := by ring
          _ = d + d' := by rw [hd.eq, hd'.eq, hdd, mul_zero, add_zero]
      · calc (d + d') * (e + e') = d * e + d * e' + (d' * e + d' * e') := by ring
          _ = d + d' := by rw [hde, hde', h1, h2]; ring
      · rw [add_mul]
        exact Ideal.add_mem _ hdf hdf'
      · have h3 : (e + e' - (d + d')) * g = (e - d) * g + (e' - d') * g := by ring
        rw [h3]
        exact Ideal.add_mem _ hdg hdg'
    · intro m hm
      have hprime := hm.isPrime
      have hspan : (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) ϖ) ^ N ∈
          Ideal.span {Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) f, Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m) g} := by
        rw [← map_pow]
        have h4 := Ideal.mem_map_of_mem (Ideal.Quotient.mk (CrystallineSemistableComparison.R.compI m)) hN
        rwa [Ideal.map_span, Set.image_pair] at h4
      rcases hD m hm _ _ ⟨N, hspan⟩ with hgf | hfg'
      · obtain ⟨c, hc⟩ := hgf
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : f - g * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have hef : e * f = e * (g * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, e, he, he.eq, ?_, by simp⟩
        rw [hef]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self g))
      · obtain ⟨c, hc⟩ := hfg'
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hmem : g - f * a ∈ CrystallineSemistableComparison.R.compI m := by
          rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc, sub_self]
        obtain ⟨e, he, hem, hex⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff m hprime _).1 hmem
        have heg : e * g = e * (f * a) := by
          rw [mul_sub] at hex
          exact sub_eq_zero.1 hex
        refine ⟨e, he, hem, 0, IsIdempotentElem.zero, by simp, by simp, ?_⟩
        rw [sub_zero, heg]
        exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
  obtain ⟨d, hd, -, hdf, hdg⟩ := hQ1
  exact ⟨d, hd, hdf, hdg⟩

end GlobalTheory.CompanionTheory.Idem
end

