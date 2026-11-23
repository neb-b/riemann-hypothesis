module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0122
public import Formalism.LocalToGlobal.Columns.HeckeInertComm
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0115
public import Formalism.GL3MeanSquares.Bundle0002
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.CyclotomicNorms.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0123
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKummerFieldOfPowerIdealRoots
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.FieldsEx

variable {E : Type} [Field E] [NumberField E]

theorem exists_finite_units_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set (𝓞 E)ˣ, S.Finite ∧ ∀ u : (𝓞 E)ˣ, ∃ s ∈ S, ∃ w : (𝓞 E)ˣ, u = s * w ^ h := by
  have : Group.FG (𝓞 E)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
  have := Subgroup.finiteIndex_range_powMonoidHom_of_fg (𝓞 E)ˣ h0
  have : Finite ((𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Set.range (Quotient.out : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range → (𝓞 E)ˣ),
    @Set.finite_range _ _ _ this, fun u => ?_⟩
  obtain ⟨⟨_, w, rfl⟩, hw⟩ := QuotientGroup.mk_out_eq_mul (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range u
  refine ⟨_, ⟨(u : (𝓞 E)ˣ ⧸ (powMonoidHom h : (𝓞 E)ˣ →* (𝓞 E)ˣ).range), rfl⟩, w⁻¹, ?_⟩
  rw [hw]
  simp

theorem exists_finite_mod_units_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ (x : E) (u : (𝓞 E)ˣ),
      y = x ^ h * s * ((u : 𝓞 E) : E) := by
  classical
  have key : ∀ y : powIdealElts E h, ∃ 𝔞 : (FractionalIdeal (𝓞 E)⁰ E)ˣ,
      FractionalIdeal.spanSingleton (𝓞 E)⁰ (y : E) = (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ^ h := by
    rintro ⟨y, hy, 𝔞, ha⟩
    refine ⟨Units.mk0 𝔞 ?_, ha⟩
    rintro rfl
    rw [zero_pow h0, FractionalIdeal.spanSingleton_eq_zero_iff] at ha
    exact hy ha
  choose A hA using key
  let c : powIdealElts E h → ClassGroup (𝓞 E) := fun y => ClassGroup.mk E (A y)
  let r : Set.range c → E := fun t => (t.2.choose : E)
  refine ⟨Set.range r, Set.finite_range _, fun y hy => ⟨_, ⟨⟨c ⟨y, hy⟩, _, rfl⟩, rfl⟩, ?_⟩⟩
  have ht : c ⟨y, hy⟩ ∈ Set.range c := ⟨_, rfl⟩
  have h1 : c ht.choose = c ⟨y, hy⟩ := ht.choose_spec
  change ∃ (x : E) (u : (𝓞 E)ˣ), y = x ^ h * (ht.choose : E) * ((u : 𝓞 E) : E)
  generalize ht.choose = s at h1
  have h2 : ClassGroup.mk E (A ⟨y, hy⟩ * (A s)⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
    exact h1.symm
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 (ClassGroup.mk_eq_one_iff.1 h2)
  have h3 : ((A ⟨y, hy⟩ : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      FractionalIdeal.spanSingleton (𝓞 E)⁰ x * A s := by
    rw [← hx, ← Units.val_mul, inv_mul_cancel_right]
  have h4 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x ^ h * s) = FractionalIdeal.spanSingleton (𝓞 E)⁰ y := by
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_pow, hA s, ← mul_pow,
      ← h3]
    exact (hA ⟨y, hy⟩).symm
  obtain ⟨u, hu⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.1 h4
  refine ⟨x, u, ?_⟩
  rw [← hu, Units.smul_def, Algebra.smul_def, mul_comm]

theorem exists_finite_mod_pow {h : ℕ} (h0 : h ≠ 0) :
    ∃ S : Set E, S.Finite ∧ ∀ y ∈ powIdealElts E h, ∃ s ∈ S, ∃ x : E, y = x ^ h * s := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_units_pow (E := E) h0
  obtain ⟨T, hT, H'⟩ := exists_finite_units_mod_pow (E := E) h0
  refine ⟨Set.image2 (fun s (t : (𝓞 E)ˣ) => s * ((t : 𝓞 E) : E)) S T, hS.image2 _ hT, fun y hy => ?_⟩
  obtain ⟨s, hs, x, u, rfl⟩ := H y hy
  obtain ⟨t, ht, w, rfl⟩ := H' u
  refine ⟨_, ⟨s, hs, t, ht, rfl⟩, x * ((w : 𝓞 E) : E), ?_⟩
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, RingOfIntegers.coe_eq_algebraMap]
  ring

theorem finiteDimensional_kummerField (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ) (h0 : h ≠ 0) :
    FiniteDimensional ℚ (kummerField φ h) := by
  obtain ⟨S, hS, H⟩ := exists_finite_mod_pow (E := E) h0
  let R : Set ℂ := ⋃ s ∈ insert 1 S, {z | z ^ h = φ s}
  have hR : R.Finite := (hS.insert 1).biUnion fun s _ =>
    ((Polynomial.nthRoots h (φ s)).finite_toSet).subset fun z hz =>
      (Polynomial.mem_nthRoots (Nat.pos_of_ne_zero h0)).2 hz
  have : Finite R := hR
  have h1 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ R) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    obtain ⟨s, -, hs⟩ := Set.mem_iUnion₂.1 hz
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero h0) ?_
    rw [show z ^ h = φ s from hs]
    exact (Algebra.IsIntegral.isIntegral s).map φ.toRatAlgHom
  have h2 : FiniteDimensional ℚ (imField φ) :=
    (AlgEquiv.ofInjectiveField φ.toRatAlgHom).toLinearEquiv.finiteDimensional
  have h3 : FiniteDimensional ℚ (imField φ ⊔ IntermediateField.adjoin ℚ R : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_sup _ _
  have hE : ∀ x, φ x ∈ imField φ ⊔ IntermediateField.adjoin ℚ R := fun x =>
    (le_sup_left : imField φ ≤ _) ⟨x, rfl⟩
  have hz : ∀ s ∈ insert 1 S, ∀ z : ℂ, z ^ h = φ s → z ∈ imField φ ⊔ IntermediateField.adjoin ℚ R :=
    fun s hs z hz => (le_sup_right : IntermediateField.adjoin ℚ R ≤ _)
      (IntermediateField.subset_adjoin ℚ R (Set.mem_iUnion₂.2 ⟨s, hs, hz⟩))
  have hle : kummerField φ h ≤ imField φ ⊔ IntermediateField.adjoin ℚ R := by
    refine (kummerField_le_iff φ).2 ⟨hE, hz 1 (Set.mem_insert _ _) _ ?_, fun y hy z hzy => ?_⟩
    · rw [map_one]
      exact (Complex.isPrimitiveRoot_exp h h0).pow_eq_one
    · obtain ⟨s, hs, x, rfl⟩ := H y hy
      have hx : φ x ≠ 0 := by
        rw [map_ne_zero]
        rintro rfl
        exact hy.1 (by rw [zero_pow h0, zero_mul])
      have h4 := hz s (Set.mem_insert_of_mem _ hs) (z / φ x) (by
        rw [div_pow, hzy, map_mul, map_pow, mul_div_cancel_left₀ _ (pow_ne_zero _ hx)])
      simpa [hx] using mul_mem h4 (hE x)
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

end GlobalTheory.Mem.FieldsEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasis
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem prod_zsum_expand {A : Type*} [CommRing A] {L : Type*} [Fintype L] [DecidableEq L]
    {α β : L → Type*} [∀ s, Fintype (β s)] (f : ∀ s, α s → A) (g : ∀ s, β s → A)
    (c : ∀ s, α s → β s → ℤ) (h : ∀ s j, f s j = ∑ k, c s j k • g s k) (j : ∀ s, α s) :
    ∏ s, f s (j s) = ∑ κ : (∀ s, β s), (∏ s, c s (j s) (κ s)) • ∏ s, g s (κ s) := by
  simp only [h, zsmul_eq_mul]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib]
  push_cast
  rfl

theorem norm_dual_zsum_le_one (p : ℕ) [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module ℂ_[p] M]
    (φ : Module.Dual ℂ_[p] M) {κ : Type*} [Fintype κ] (n : κ → ℤ) (x : κ → M)
    (hx : ∀ k, ‖φ (x k)‖ ≤ 1) : ‖φ (∑ k, n k • x k)‖ ≤ 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_zsmul, zsmul_eq_mul, norm_mul]
  calc ‖(n k : ℂ_[p])‖ * ‖φ (x k)‖ ≤ 1 * 1 :=
        mul_le_mul (IsUltrametricDist.norm_intCast_le_one _ _) (hx k) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem integral_minors_iff_basis : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  intro p _ Lt _ N nu hY ι _ b c d hc hd φ
  classical
  let Ψ : Lt → MvPolynomial (Fin N × Fin N) ℚ →+* MvPolynomial (Lt × ℕ × Fin N) ℂ_[p] := fun s =>
    (MvPolynomial.map (algebraMap ℚ ℂ_[p])).comp (MvPolynomial.rename (sig N s)).toRingHom
  have hF : ∀ J : WeylLatticeDuality.ColChoice N nu,
      MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J) =
        ∏ s, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) (J s)) := by
    intro J
    have h1 : Int.castRingHom ℂ_[p] = (algebraMap ℚ ℂ_[p]).comp (Int.castRingHom ℚ) := RingHom.ext_int _ _
    rw [h1, ← MvPolynomial.map_map, map_nablaX ℚ N nu hY J, map_prod]
    rfl
  have hG : ∀ κ : (∀ s, ι s), MvPolynomial.map (algebraMap ℚ ℂ_[p])
      (∏ s, MvPolynomial.rename (sig N s) (b s (κ s))) = ∏ s, Ψ s (b s (κ s)) := by
    intro κ
    rw [map_prod]
    rfl
  have hc' : ∀ s J, Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) = ∑ k, c s J k • Ψ s (b s k) := by
    intro s J
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  have hd' : ∀ s k, Ψ s (b s k) = ∑ J, d s k J • Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) := by
    intro s k
    conv_lhs => rw [hd]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← map_zsmul, Int.cast_smul_eq_zsmul]
  constructor
  · intro h κ
    rw [hG, prod_zsum_expand (fun s k => Ψ s (b s k)) _ d hd' κ]
    refine norm_dual_zsum_le_one p φ _ _ fun J => ?_
    exact (le_of_eq (congrArg (fun x => ‖φ x‖) (hF J)).symm).trans (h J)
  · intro h J
    rw [hF, prod_zsum_expand (fun s J => Ψ s (GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J)) _ c hc' J]
    refine norm_dual_zsum_le_one p φ _ _ fun κ => ?_
    have := h κ
    rw [hG] at this
    exact this

end GlobalTheory.WeylLatDualProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAbsolutelyIrreducibleSplitRepOfConstituentMode
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.SplitCrit

variable {k L : Type} [Field k] [Field L]

abbrev ext (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) : Submodule L (Fin a → L) :=
  Submodule.span L ((fun v => f ∘ v) '' (W : Set (Fin a → k)))

theorem map_mulVec_comp (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k) (v : Fin n → k) :
    (M.map f).mulVec (f ∘ v) = f ∘ M.mulVec v := by
  funext i; exact (RingHom.map_mulVec f M v i).symm

theorem ext_le_comap (f : k →+* L) {m n : ℕ} (M : Matrix (Fin m) (Fin n) k)
    (U : Submodule k (Fin n → k)) (U' : Submodule k (Fin m → k)) (h : ∀ v ∈ U, M.mulVec v ∈ U') :
    ext f U ≤ (ext f U').comap (M.map f).mulVecLin := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨v, hv, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
  rw [map_mulVec_comp]
  exact Submodule.subset_span ⟨_, h v hv, rfl⟩

theorem ext_ne_bot (f : k →+* L) {a : ℕ} {W : Submodule k (Fin a → k)} (hW : W ≠ ⊥) : ext f W ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  intro h
  have : f ∘ v ∈ ext f W := Submodule.subset_span ⟨v, hv, rfl⟩
  rw [h, Submodule.mem_bot] at this
  apply hv0; funext i
  have := congrFun this i
  simpa using this

theorem finrank_ext_le (f : k →+* L) {a : ℕ} (W : Submodule k (Fin a → k)) :
    Module.finrank L (ext f W) ≤ Module.finrank k W := by
  let e := Module.finBasis k W
  have hle : ext f W ≤ Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    have hv' : v = ∑ i, (e.repr ⟨v, hv⟩ i) • (e i : Fin a → k) := by
      have := congrArg Subtype.val (e.sum_repr ⟨v, hv⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have : f ∘ v = ∑ i, f (e.repr ⟨v, hv⟩ i) • (f ∘ (e i : Fin a → k)) := by
      conv_lhs => rw [hv']
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Finset.sum_apply, map_sum]
    show f ∘ v ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  calc Module.finrank L (ext f W)
      ≤ Module.finrank L (Submodule.span L (Set.range fun i => f ∘ (e i : Fin a → k))) :=
        Submodule.finrank_mono hle
    _ ≤ Fintype.card (Fin (Module.finrank k W)) := finrank_range_le_card _
    _ = Module.finrank k W := Fintype.card_fin _

theorem range_ne_bot {K : Type} [Field K] {m n : ℕ} {X : Matrix (Fin m) (Fin n) K} (hX : X ≠ 0) :
    LinearMap.range X.mulVecLin ≠ ⊥ := by
  intro h
  apply hX
  refine Matrix.ext_of_mulVec_single fun i => ?_
  have : X.mulVecLin (Pi.single i 1) ∈ LinearMap.range X.mulVecLin := LinearMap.mem_range_self _ _
  rw [h, Submodule.mem_bot, Matrix.mulVecLin_apply] at this
  rw [this, Matrix.zero_mulVec]

end GlobalTheory.SplitCrit

namespace GlobalTheory.SplitCrit

theorem splitRep_of_models : ∀ {k Γ L : Type} [Field k] [Group Γ] [Field L] [IsAlgClosed L] (f : k →+* L) {a : ℕ} (ρ : Γ →* GL (Fin a) k), (∀ V, IsIrrSub (mapRep f ρ) V → ∃ (b : ℕ) (σ : Γ →* GL (Fin b) k) (C : Matrix (Fin a) (Fin b) L), Function.Injective C.mulVec ∧ LinearMap.range C.mulVecLin = V ∧ ∀ g, ((mapRep f ρ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * C = C * ((mapRep f σ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)) → GlobalTheory.SplitCoef.SplitRep ρ := by
  intro k Γ L _ _ _ _ f a ρ hmod W hW
  obtain ⟨hW0, hWi, hWmin⟩ := hW

  have hLi : IsInv (mapRep f ρ) (ext f W) := fun g v hv =>
    ext_le_comap f (ρ g : Matrix (Fin a) (Fin a) k) W W (hWi g) hv
  obtain ⟨V, hVle, hV⟩ := GlobalTheory.SemisimpleDecomp.exists_irr_le hLi (ext_ne_bot f hW0)
  obtain ⟨b, σ, C, hCinj, hCr, hCint⟩ := hmod V hV

  obtain ⟨W', hc⟩ := Submodule.exists_isCompl W
  let φ : (Fin a → k) →ₗ[k] (Fin a → k) := W'.subtype.comp (W'.projectionOnto W hc.symm)
  have hφ : ∀ v, φ v = 0 ↔ v ∈ W := by
    intro v
    have hk := Submodule.ker_projectionOnto hc.symm
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, ZeroMemClass.coe_eq_zero]
    rw [← LinearMap.mem_ker, hk]
  let Q := LinearMap.toMatrix' φ
  have hQ : ∀ v, Q.mulVec v = 0 ↔ v ∈ W := fun v => by
    simp only [Q, LinearMap.toMatrix'_mulVec]; exact hφ v

  have hQL : ext f W ≤ LinearMap.ker (Q.map f).mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    rw [map_mulVec_comp, (hQ v).2 hv]
    funext i; simp
  have hQC : Q.map f * C = 0 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    have : C.mulVec (Pi.single j 1) ∈ V := hCr ▸ LinearMap.mem_range_self C.mulVecLin _
    have := hQL (hVle this)
    simpa using this
  have hC0 : C ≠ 0 := by
    intro h; apply hV.1; rw [← hCr, h]
    ext x; simp
  have hint : ∀ g, ((ρ g : Matrix (Fin a) (Fin a) k)).map f * C = C * ((σ g : Matrix (Fin b) (Fin b) k)).map f :=
    fun g => hCint g
  obtain ⟨X, hX0, hXint, hQX⟩ := _root_.GlobalTheory.matrix_system_nonzero_solution_descends f (fun g => (ρ g : Matrix (Fin a) (Fin a) k))
    (fun g => (σ g : Matrix (Fin b) (Fin b) k)) Q C hC0 hint hQC

  have hXW : LinearMap.range X.mulVecLin ≤ W := by
    rintro _ ⟨w, rfl⟩
    rw [← hQ, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQX, Matrix.zero_mulVec]
  have hXi : IsInv ρ (LinearMap.range X.mulVecLin) := by
    rintro g _ ⟨w, rfl⟩
    refine ⟨(σ g : Matrix (Fin b) (Fin b) k).mulVec w, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hXint g]
  have hXeq : LinearMap.range X.mulVecLin = W :=
    (hWmin _ hXW hXi).resolve_left (range_ne_bot hX0)
  have hWb : Module.finrank k W ≤ b := by
    rw [← hXeq]
    exact (LinearMap.finrank_range_le _).trans (Module.finrank_fin_fun k).le
  have hVb : Module.finrank L V = b := by
    rw [← hCr, LinearMap.finrank_range_of_inj hCinj, Module.finrank_fin_fun]
  have hVeq : V = ext f W :=
    Submodule.eq_of_le_of_finrank_le hVle ((finrank_ext_le f W).trans (hWb.trans hVb.ge))
  have hV' : IsIrrSub (mapRep f ρ) (ext f W) := hVeq ▸ hV
  exact _root_.GlobalTheory.AbsIrrOfAlgClosed.absIrrSub_of_isIrrSub_map f ρ W hWi hV'

end GlobalTheory.SplitCrit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationHermitianDualEqStatement
section
open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Formalism.L2.Col GlobalTheory.InertExchange
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localization_hermitianDual_eq : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (Q : HeightOneSpectrum (𝓞 E)) (A B : Submodule (𝓞 E) (Sp E n)), Submodule.IsLattice E A → Submodule.IsLattice E B → localization₂ (conjPrime₂ Q).asIdeal A = localization₂ (conjPrime₂ Q).asIdeal B → localization₂ Q.asIdeal (dual (hStd E n) A) = localization₂ Q.asIdeal (dual (hStd E n) B) := by
  first | exact @GlobalTheory.DualLoc.use₅ | exact GlobalTheory.DualLoc.use₅ | (intros; apply GlobalTheory.DualLoc.use₅ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
section
open Finset ArithmeticFunction Filter Topology

noncomputable section

namespace GlobalTheory.MangoldtSeries

theorem sum_not_coprime_le (q N : ℕ) (hq : q ≠ 0) :
    ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n ≤ Nat.log 2 N * Real.log q := by
  classical
  set S := (Icc 1 N).filter (fun n => ¬ n.Coprime q) with hS
  set L := Nat.log 2 N with hL
  have hT0 : ∀ p n : ℕ, 0 ≤ (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro p n; split_ifs
    · exact Real.log_natCast_nonneg p
    · exact le_rfl
  have hpt : ∀ n ∈ S, Λ n ≤ ∑ p ∈ q.primeFactors,
      (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnN⟩, hnc⟩ := hn
    rw [ArithmeticFunction.vonMangoldt_apply]
    split_ifs with hpp
    · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
      have hmin : (p ^ k).minFac = p := by rw [Nat.pow_minFac hk.ne', hp.minFac_eq]
      have hpq : p ∣ q := by
        by_contra h
        exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 h))
      have hpmem : p ∈ q.primeFactors := Nat.mem_primeFactors.2 ⟨hp, hpq, hq⟩
      have hkL : k ∈ Icc 1 L := by
        rw [Finset.mem_Icc]
        refine ⟨hk, Nat.le_log_of_pow_le (by norm_num) ?_⟩
        exact (Nat.pow_le_pow_left hp.two_le k).trans hnN
      have hTp : (if p ^ k ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) = Real.log p :=
        if_pos (Finset.mem_image.2 ⟨k, hkL, rfl⟩)
      rw [hmin, ← hTp]
      exact Finset.single_le_sum (f := fun p' : ℕ => if p ^ k ∈ (Icc 1 L).image (p' ^ ·) then Real.log p' else 0)
        (fun p' _ => hT0 p' (p ^ k)) hpmem
    · exact Finset.sum_nonneg (fun p _ => hT0 p n)
  have hcard : ∀ p : ℕ, ((S ∩ (Icc 1 L).image (p ^ ·)).card : ℝ) ≤ L := by
    intro p
    have h1 := Finset.card_le_card (Finset.inter_subset_right (s₁ := S) (s₂ := (Icc 1 L).image (p ^ ·)))
    have h2 := Finset.card_image_le (s := Icc 1 L) (f := (p ^ ·))
    have h3 : (Icc 1 L).card = L := by simp
    exact_mod_cast (h1.trans h2).trans h3.le
  calc ∑ n ∈ S, Λ n ≤ ∑ n ∈ S, ∑ p ∈ q.primeFactors,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_le_sum hpt
    _ = ∑ p ∈ q.primeFactors, ∑ n ∈ S,
        (if n ∈ (Icc 1 L).image (p ^ ·) then Real.log p else 0) := Finset.sum_comm
    _ ≤ ∑ p ∈ q.primeFactors, (L : ℝ) * Real.log p := by
        apply Finset.sum_le_sum
        intro p _
        rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (hcard p) (Real.log_natCast_nonneg p)
    _ = (L : ℝ) * Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [← Finset.mul_sum, Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    _ ≤ (L : ℝ) * Real.log q := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.log_le_log
        · apply Finset.prod_pos
          intro p hp
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q))

theorem norm_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
      ∑ n ∈ Icc 1 N, ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤
      Nat.log 2 N * Real.log q := by
  rw [← Finset.sum_sub_distrib,
    ← Finset.sum_filter_add_sum_filter_not (Icc 1 N) (fun n => ¬ n.Coprime q)]
  rw [Finset.sum_eq_zero (s := (Icc 1 N).filter (fun n => ¬¬ n.Coprime q)) ?_, add_zero]
  · calc _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q),
          ‖((Λ n : ℝ) : ℂ) * χ (n : ZMod q) -
            ((Λ n : ℝ) : ℂ) * χ.primitiveCharacter (n : ZMod χ.conductor)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ (Icc 1 N).filter (fun n => ¬ n.Coprime q), Λ n := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_filter] at hn
          have hχ0 : χ (n : ZMod q) = 0 := by
            apply MulChar.map_nonunit
            rw [ZMod.isUnit_iff_coprime]
            exact hn.2
          rw [hχ0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
          calc Λ n * ‖χ.primitiveCharacter (n : ZMod χ.conductor)‖ ≤ Λ n * 1 :=
                mul_le_mul_of_nonneg_left (DirichletCharacter.norm_le_one _ _)
                  ArithmeticFunction.vonMangoldt_nonneg
            _ = Λ n := mul_one _
      _ ≤ _ := sum_not_coprime_le q N (NeZero.ne q)
  · intro n hn
    rw [Finset.mem_filter, not_not] at hn
    have h := χ.primitiveCharacter_apply_of_isCoprime (a := (n : ℤ)) (Nat.isCoprime_iff_coprime.2 hn.2)
    push_cast at h
    rw [h, sub_self]

end GlobalTheory.MangoldtSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaLebUnique
section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.OmegaLebUnique

theorem omegaLeb_unique :
    ∀ (P Q : ℕ) (l l' : Measure (lieU P Q)), IsOmegaLeb l → IsOmegaLeb l' → l = l' :=
  fun _ _ _ _ h h' => GlobalTheory.CompactDualUnique.isOmegaLeb_unique h h'

end GlobalTheory.OmegaLebUnique
end

