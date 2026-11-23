module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenInfOfSeparatedOverAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits

namespace GlobalTheory.SepAffInf

theorem isAffineOpen_inf_of_le_preimage {X Z : Scheme.{0}} (h : Z ⟶ X) [IsSeparated h]
    (U : X.affineOpens) (Ω₁ Ω₂ : Z.affineOpens)
    (h₁ : Ω₁.1 ≤ h ⁻¹ᵁ U.1) (h₂ : Ω₂.1 ≤ h ⁻¹ᵁ U.1) : IsAffineOpen (Ω₁.1 ⊓ Ω₂.1) := by
  haveI : IsAffine U.1 := U.2
  haveI : (h ⁻¹ᵁ U.1).toScheme.IsSeparated := by
    constructor
    rw [← terminal.comp_from (h ∣_ U.1)]
    infer_instance
  have key : ∀ Ω : Z.Opens, Ω ≤ h ⁻¹ᵁ U.1 →
      (h ⁻¹ᵁ U.1).ι ''ᵁ ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω) = Ω := by
    intro Ω hΩ
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hΩ
  have a₁ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₁.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₁]
    exact Ω₁.2
  have a₂ : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ Ω₂.1) := by
    rw [← Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (h ⁻¹ᵁ U.1).ι, key _ h₂]
    exact Ω₂.2
  have a : IsAffineOpen ((h ⁻¹ᵁ U.1).ι ⁻¹ᵁ (Ω₁.1 ⊓ Ω₂.1)) := a₁.inf a₂
  rw [← key _ (inf_le_left.trans h₁)]
  exact a.image_of_isOpenImmersion _

end GlobalTheory.SepAffInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSubringIsAlgebraic
section
namespace GlobalTheory


open Algebra in
theorem isAlgebraic_of_subring_isAlgebraic {L : Type} [Field L] [Algebra ℂ L]
    (S : Subalgebra ℂ L) (B : Subring L) (z : L)
    (hB : ∀ b ∈ B, IsAlgebraic S b) (hz : IsAlgebraic B z) : IsAlgebraic S z := by
  set T := adjoin ℂ ((S : Set L) ∪ (B : Set L)) with hT
  have hBT : ∀ b ∈ B, b ∈ T := fun b hb => subset_adjoin (Or.inr hb)
  let f : B →+* T :=
    { toFun := fun b => ⟨b.1, hBT b.1 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let _ : Algebra B T := f.toAlgebra
  have : IsScalarTower B T L := .of_algebraMap_eq fun _ => rfl
  have hinj : Function.Injective (algebraMap B T) := by
    intro a b h
    apply Subtype.ext
    have := congrArg Subtype.val h
    exact this
  have hzT : IsAlgebraic T z := hz.extendScalars hinj
  have hSle : S ≤ adjoin ℂ (S : Set L) := subset_adjoin
  have key : IsAlgebraic (adjoin ℂ (S : Set L)) z := by
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := ℂ) (s := (S : Set L) ∪ (B : Set L)) ?_ hzT
    intro x hx
    rcases hx.1 with h | h
    · exact absurd h hx.2
    · exact (hB x h).tower_top_of_subalgebra_le hSle
  rwa [Algebra.adjoin_eq] at key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArtinianRingKummerAdjoinRootQuotientRoot
section
open IsLocalRing Polynomial

namespace GlobalTheory

theorem artinian_quot_root_adjoin_kummer (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (u : Aˣ) (m k : ℕ) (hϖ : Irreducible ϖ) (hm : IsUnit (m : A)) (hk : 0 < k) :
    IsArtinianRing (AdjoinRoot (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A))) ⧸ Ideal.span {AdjoinRoot.root (Polynomial.X ^ k - Polynomial.C (AdjoinRoot.of (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A) ϖ * AdjoinRoot.root (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)) : Polynomial (AdjoinRoot (Polynomial.X ^ m - Polynomial.C (u : A) : Polynomial A)))}) := by
  set f : A[X] := X ^ m - C (u : A) with hf
  set R1 := AdjoinRoot f
  set g : R1[X] := X ^ k - C (AdjoinRoot.of f ϖ * AdjoinRoot.root f) with hg
  set R := AdjoinRoot g
  set I : Ideal R := Ideal.span {AdjoinRoot.root g}
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hfm : f.Monic := monic_X_pow_sub_C _ hm0
  have hgm : g.Monic := monic_X_pow_sub_C _ hk.ne'
  haveI : Module.Finite A R1 := (AdjoinRoot.powerBasis' hfm).finite
  haveI : Module.Finite R1 R := (AdjoinRoot.powerBasis' hgm).finite
  haveI : Module.Finite A R := Module.Finite.trans R1 R
  haveI : Module.Finite A (R ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap Ideal.Quotient.mk_surjective

  have hzero : algebraMap A (R ⧸ I) ϖ = 0 := by
    have h1 : (AdjoinRoot.root g) ^ k = AdjoinRoot.of g (AdjoinRoot.of f ϖ * AdjoinRoot.root f) := by
      have := AdjoinRoot.eval₂_root g
      rw [hg] at this
      simpa [eval₂_sub, sub_eq_zero] using this
    have h2 : (AdjoinRoot.root f) ^ m = AdjoinRoot.of f (u : A) := by
      have := AdjoinRoot.eval₂_root f
      rw [hf] at this
      simpa [eval₂_sub, sub_eq_zero] using this
    let q : R →+* R ⧸ I := Ideal.Quotient.mk I
    have ht : q (AdjoinRoot.root g) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    have h3 : q (AdjoinRoot.of g (AdjoinRoot.of f ϖ)) * q (AdjoinRoot.of g (AdjoinRoot.root f)) = 0 := by
      rw [← map_mul, ← map_mul, ← h1, map_pow, ht, zero_pow hk.ne']
    have hu : IsUnit (q (AdjoinRoot.of g (AdjoinRoot.root f))) := by
      have : IsUnit (q (AdjoinRoot.of g (AdjoinRoot.root f)) ^ m) := by
        rw [← map_pow, ← map_pow, h2]
        exact (u.isUnit.map (AdjoinRoot.of f)).map _ |>.map _
      exact (isUnit_pow_iff hm0).mp this
    have h4 : q (AdjoinRoot.of g (AdjoinRoot.of f ϖ)) = 0 := by
      simpa [hu.mul_left_eq_zero] using h3
    exact h4
  have hmax : (Ideal.span {ϖ} : Ideal A).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  let K := A ⧸ (Ideal.span {ϖ} : Ideal A)
  letI : Field K := Ideal.Quotient.field _
  let φ : K →+* R ⧸ I := Ideal.Quotient.lift _ (algebraMap A (R ⧸ I)) (by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hzero])
  letI : Algebra K (R ⧸ I) := φ.toAlgebra
  haveI : IsScalarTower A K (R ⧸ I) := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI : Module.Finite K (R ⧸ I) := Module.Finite.of_restrictScalars_finite A K (R ⧸ I)
  exact IsArtinianRing.of_finite K (R ⧸ I)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenBasicOpenSpecProdSelfFirstIdempotent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.AlgConn

abbrev twoπ (O : Type) [CommRing O] : Spec (.of (O × O)) ⟶ Spec (.of O) :=
  Spec.map (CommRingCat.ofHom (algebraMap O (O × O)))

abbrev fst1 (O : Type) [CommRing O] : Γ(Spec (.of (O × O)), ⊤) :=
  (Scheme.ΓSpecIso (.of (O × O))).inv.hom ((1, 0) : O × O)

theorem isProper_twoπ (O : Type) [CommRing O] : IsProper (twoπ O) := by
  haveI : IsFinite (twoπ O) := (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  infer_instance

theorem isClopen_basicOpen_specProdSelfFirstIdempotent (O : Type) [CommRing O] :
    IsClopen (((Spec (.of (O × O))).basicOpen (fst1 O) : (Spec (.of (O × O))).Opens) :
      Set (Spec (.of (O × O)))) := by
  rw [basicOpen_eq_of_affine]
  exact PrimeSpectrum.isClopen_iff.2 ⟨((1, 0) : O × O), by ext <;> simp [IsIdempotentElem], rfl⟩

end GlobalTheory.AlgConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPreimageQuadraticMapNoNullVectors
section
open Matrix Polynomial

namespace GlobalTheory


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem quadratic_preimage_compact_on_subspace
    (K : Type) [NontriviallyNormedField K] [ProperSpace K] [StarRing K]
    (hstar : ∀ x : K, ‖star x‖ = ‖x‖) (m : ℕ) (S : Submodule K (Matrix (Fin m) (Fin m) K))
    (q : Matrix (Fin m) (Fin m) K → Matrix (Fin m) (Fin m) K) (hq : Continuous q)
    (hhom : ∀ (c : K) w, q (c • w) = (c * star c) • q w) (hnull : ∀ w ∈ S, q w = 0 → w = 0)
    (Q : Set (Matrix (Fin m) (Fin m) K)) (hQ : IsCompact Q) :
    ∃ B : Set (Matrix (Fin m) (Fin m) K), IsCompact B ∧ ∀ w ∈ S, q w ∈ Q → w ∈ B := by
  haveI : ProperSpace (Matrix (Fin m) (Fin m) K) := FiniteDimensional.proper K _
  obtain ⟨c₀, hc₀⟩ := NormedField.exists_one_lt_norm K
  have hc₀pos : 0 < ‖c₀‖ := lt_trans one_pos hc₀
  obtain ⟨R, hR⟩ := hQ.isBounded.subset_closedBall 0
  set Sh : Set (Matrix (Fin m) (Fin m) K) :=
    (S : Set _) ∩ {w | 1 / ‖c₀‖ ≤ ‖w‖ ∧ ‖w‖ ≤ 1} with hShdef
  have hSclosed : IsClosed (S : Set (Matrix (Fin m) (Fin m) K)) :=
    Submodule.closed_of_finiteDimensional S
  have hShc : IsCompact Sh := by
    refine (isCompact_closedBall (0 : Matrix (Fin m) (Fin m) K) 1).of_isClosed_subset ?_ ?_
    · refine hSclosed.inter ?_
      exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw
      simpa [Metric.mem_closedBall, dist_zero_right] using hw.2.2

  have hresc : ∀ w ∈ S, w ≠ 0 → ∃ d : K, d ≠ 0 ∧ d • w ∈ Sh ∧ ‖d • w‖ < 1 := by
    intro w hwS hw0
    obtain ⟨d, hd0, hlt, hge, -⟩ := rescale_to_shell hc₀ one_pos hw0
    exact ⟨d, hd0, ⟨S.smul_mem d hwS, hge, hlt.le⟩, hlt⟩
  by_cases hne : Sh.Nonempty
  · obtain ⟨w₀, hw₀, hmin⟩ := hShc.exists_isMinOn hne
      (f := fun w => ‖q w‖) (continuous_norm.comp hq).continuousOn
    set μ := ‖q w₀‖ with hμ
    have hμpos : 0 < μ := by
      rw [hμ, norm_pos_iff]
      intro h0
      have := hnull w₀ hw₀.1 h0
      have h1 := hw₀.2.1
      rw [this, norm_zero] at h1
      exact absurd h1 (not_le.mpr (by positivity))
    refine ⟨Metric.closedBall 0 (max 1 (R / μ)), isCompact_closedBall _ _, ?_⟩
    intro w hwS hwQ
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases hw0 : w = 0
    · rw [hw0, norm_zero]; exact le_trans zero_le_one (le_max_left _ _)
    obtain ⟨d, hd0, hdSh, hdlt⟩ := hresc w hwS hw0
    have hqw : ‖q w‖ ≤ R := by
      have := hR hwQ
      rwa [Metric.mem_closedBall, dist_zero_right] at this
    have hmu_le : μ ≤ ‖d‖ ^ 2 * ‖q w‖ := by
      have h := isMinOn_iff.mp hmin _ hdSh
      rw [hhom, norm_smul, norm_mul, hstar] at h
      nlinarith [h]
    have hdw : ‖d‖ * ‖w‖ < 1 := by rwa [norm_smul] at hdlt
    have hd2 : ‖d‖ ^ 2 * ‖w‖ ^ 2 ≤ 1 := by
      have h0 : 0 ≤ ‖d‖ * ‖w‖ := by positivity
      nlinarith
    have key : μ * ‖w‖ ^ 2 ≤ R := by
      have hq0 : 0 ≤ ‖q w‖ := norm_nonneg _
      calc μ * ‖w‖ ^ 2 ≤ ‖d‖ ^ 2 * ‖q w‖ * ‖w‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hmu_le (by positivity)
        _ = (‖d‖ ^ 2 * ‖w‖ ^ 2) * ‖q w‖ := by ring
        _ ≤ 1 * ‖q w‖ := mul_le_mul_of_nonneg_right hd2 hq0
        _ ≤ R := by linarith
    by_cases h1 : ‖w‖ ≤ 1
    · exact le_trans h1 (le_max_left _ _)
    · push_neg at h1
      refine le_trans ?_ (le_max_right _ _)
      rw [le_div_iff₀ hμpos]
      have h2 : ‖w‖ * μ ≤ ‖w‖ ^ 2 * μ := by
        apply mul_le_mul_of_nonneg_right _ hμpos.le
        nlinarith
      linarith
  · refine ⟨{0}, isCompact_singleton, ?_⟩
    intro w hwS _
    by_contra hw0
    obtain ⟨d, -, hdSh, -⟩ := hresc w hwS hw0
    exact hne ⟨_, hdSh⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFractionRingTensorOfFractionFields
section
open scoped TensorProduct

namespace GlobalTheory

theorem tensor_fractionRing_of_tensor
    {k R B K κ L : Type} [Field k] [CommRing R] [CommRing B] [Field K] [Field κ]
    [Field L] [Algebra k R] [Algebra k B] [Algebra k K] [Algebra k κ] [Algebra R K] [Algebra B κ]
    [IsScalarTower k R K] [IsScalarTower k B κ] [IsFractionRing R K] [IsFractionRing B κ]
    [Algebra (K ⊗[k] κ) L] [IsFractionRing (K ⊗[k] κ) L] :
    Function.Injective ((algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom) ∧
    ∀ z : L, ∃ x y : R ⊗[k] B,
      (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom y ≠ 0 ∧
      z * (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom y =
      (algebraMap (K ⊗[k] κ) L).comp (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ)).toRingHom x := by
  set f := Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom k R K) (IsScalarTower.toAlgHom k B κ) with hfdef
  set g := algebraMap (K ⊗[k] κ) L

  have key : ∀ w : K ⊗[k] κ, ∃ (x : R ⊗[k] B) (s : nonZeroDivisors R) (t : nonZeroDivisors B),
      w * (algebraMap R K (s : R) ⊗ₜ[k] algebraMap B κ (t : B)) = f x := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, 1, 1, by simp⟩
    | tmul a b =>
      obtain ⟨⟨r, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors R) a
      obtain ⟨⟨c, t⟩, ht⟩ := IsLocalization.surj (nonZeroDivisors B) b
      refine ⟨r ⊗ₜ[k] c, s, t, ?_⟩
      simp only [Algebra.TensorProduct.tmul_mul_tmul] at *
      rw [hs, ht, hfdef, Algebra.TensorProduct.map_tmul]
      rfl
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨x₁, s₁, t₁, e₁⟩ := h₁
      obtain ⟨x₂, s₂, t₂, e₂⟩ := h₂
      refine ⟨x₁ * ((s₂ : R) ⊗ₜ[k] (t₂ : B)) + x₂ * ((s₁ : R) ⊗ₜ[k] (t₁ : B)), s₁ * s₂, t₁ * t₂, ?_⟩
      have hm : ∀ (s : R) (t : B), f (s ⊗ₜ[k] t) = algebraMap R K s ⊗ₜ[k] algebraMap B κ t := by
        intro s t; rw [hfdef, Algebra.TensorProduct.map_tmul]; rfl
      rw [map_add (f := _), map_mul, map_mul, hm, hm, ← e₁, ← e₂]
      simp only [Submonoid.coe_mul, map_mul, ← Algebra.TensorProduct.tmul_mul_tmul]
      ring

  have unit_st : ∀ (s : nonZeroDivisors R) (t : nonZeroDivisors B),
      IsUnit (algebraMap R K (s : R) ⊗ₜ[k] algebraMap B κ (t : B)) := by
    intro s t
    have hs : IsUnit (algebraMap R K (s : R)) :=
      IsLocalization.map_units K s
    have ht : IsUnit (algebraMap B κ (t : B)) :=
      IsLocalization.map_units κ t
    have : algebraMap R K (s : R) ⊗ₜ[k] algebraMap B κ (t : B) =
        Algebra.TensorProduct.includeLeft (R := k) (S := k) (B := κ) (algebraMap R K (s : R)) *
        Algebra.TensorProduct.includeRight (R := k) (A := K) (algebraMap B κ (t : B)) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]
    exact (hs.map _).mul (ht.map _)
  refine ⟨?_, ?_⟩
  · refine (IsFractionRing.injective (K ⊗[k] κ) L).comp ?_
    change Function.Injective (TensorProduct.map (IsScalarTower.toAlgHom k R K).toLinearMap
      (IsScalarTower.toAlgHom k B κ).toLinearMap)
    exact TensorProduct.map_injective_of_flat_flat _ _
      (IsFractionRing.injective R K) (IsFractionRing.injective B κ)
  · intro z
    obtain ⟨⟨u, v⟩, huv⟩ := IsLocalization.surj (nonZeroDivisors (K ⊗[k] κ)) z
    obtain ⟨xu, su, tu, eu⟩ := key u
    obtain ⟨xv, sv, tv, ev⟩ := key (v : K ⊗[k] κ)
    refine ⟨xu * ((sv : R) ⊗ₜ[k] (tv : B)), xv * ((su : R) ⊗ₜ[k] (tu : B)), ?_, ?_⟩
    all_goals
      have hm : ∀ (s : R) (t : B), f (s ⊗ₜ[k] t) = algebraMap R K s ⊗ₜ[k] algebraMap B κ t := by
        intro s t; rw [hfdef, Algebra.TensorProduct.map_tmul]; rfl
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_mul, hm]
    · rw [← ev]; simp only [map_mul]
      refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
      · exact (IsLocalization.map_units L v).ne_zero
      · exact ((unit_st sv tv).map g).ne_zero
      · exact ((unit_st su tu).map g).ne_zero
    · rw [← ev, ← eu]; simp only [map_mul]
      have huv' : z * g (v : K ⊗[k] κ) = g u := huv
      linear_combination (g (algebraMap R K ↑sv ⊗ₜ[k] algebraMap B κ ↑tv) *
        g (algebraMap R K ↑su ⊗ₜ[k] algebraMap B κ ↑tu)) * huv'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HilbertSch

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

def IsHilbRep {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) : Prop :=
  ∃ (H : Scheme.{0}) (h : H ⟶ S) (U : Scheme.{0}) (u : U ⟶ pullback z h), IsProper h ∧ IsClosedImmersion u ∧
    IsFinite (u ≫ pullback.snd z h) ∧ Flat (u ≫ pullback.snd z h) ∧ (∀ y, (u ≫ pullback.snd z h).finrank y = r) ∧
    ∀ (T : Scheme.{0}) (g : T ⟶ S) (V : Scheme.{0}) (v : V ⟶ pullback z g), IsClosedImmersion v →
      IsFinite (v ≫ pullback.snd z g) → Flat (v ≫ pullback.snd z g) → (∀ y, (v ≫ pullback.snd z g).finrank y = r) →
      ∃! f : T ⟶ H, ∃ hf : f ≫ h = g, ∃ w : V ⟶ U,
        IsPullback v w (pullback.map z g z h (𝟙 Z) f (𝟙 S) (by simp) (by rw [Category.comp_id, hf])) u

end GlobalTheory.HilbertSch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralConeRingOfForallValuationSubring
section
open MvPolynomial

namespace GlobalTheory

theorem isIntegral_coneRing_of_forall_valuationSubring :
    ∀ (F K : Type) [Field F] [Field K] (φ : F →+* K) (r e : ℕ) (w : Fin r → K) (τ : K), (∀ V : ValuationSubring K, (∀ c, φ c ∈ V) → ∃ i, w i ≠ 0 ∧ τ / w i ^ e ∈ V) → ∃ (m : ℕ) (b : Fin m → MvPolynomial (Fin r) F), (Polynomial.C τ * Polynomial.X ^ e) ^ m + ∑ k, MvPolynomial.eval₂ (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X) (b k) * (Polynomial.C τ * Polynomial.X ^ e) ^ (k : ℕ) = 0 := by
  intro F K _ _ φ r e w τ h
  classical
  let L := FractionRing (Polynomial K)
  let j : Polynomial K →+* L := algebraMap (Polynomial K) L
  let g : MvPolynomial (Fin r) F →+* Polynomial K :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ) (fun i => Polynomial.C (w i) * Polynomial.X)
  let y : Polynomial K := Polynomial.C τ * Polynomial.X ^ e
  have hjinj : Function.Injective j := IsFractionRing.injective _ _
  have hx : j y ∈ (integralClosure (Subring.closure (Set.range (j.comp g))) L).toSubring := by
    rw [← iInf_valuationSubring_superset, Subring.mem_iInf]
    intro V
    obtain ⟨W, hW⟩ := V
    change j y ∈ W
    let U : ValuationSubring K := W.comap (j.comp Polynomial.C)
    have hU : ∀ c, φ c ∈ U := by
      intro c
      have : j (g (MvPolynomial.C c)) ∈ W := hW ⟨_, rfl⟩
      simpa [g, U] using this
    obtain ⟨i, hi, hτ⟩ := h U hU
    have h1 : j (Polynomial.C (w i) * Polynomial.X) ∈ W := by
      have : j (g (MvPolynomial.X i)) ∈ W := hW ⟨_, rfl⟩
      simpa [g] using this
    have h2 : j (Polynomial.C (τ / w i ^ e)) ∈ W := hτ
    have hy : y = Polynomial.C (τ / w i ^ e) * (Polynomial.C (w i) * Polynomial.X) ^ e := by
      rw [mul_pow, ← mul_assoc, ← Polynomial.C_pow, ← Polynomial.C_mul,
        div_mul_cancel₀ _ (pow_ne_zero _ hi)]
    rw [hy, map_mul, map_pow]
    exact mul_mem h2 (pow_mem h1 _)
  have hcl : Subring.closure (Set.range (j.comp g)) = (j.comp g).range := by
    rw [← RingHom.coe_range]; exact Subring.closure_eq _
  rw [hcl] at hx
  have hint : IsIntegral (j.comp g).range (j y) := hx
  obtain ⟨p, hp, hpx⟩ := hint
  have hb : ∀ k : Fin p.natDegree, ∃ b : MvPolynomial (Fin r) F, j (g b) = (p.coeff k : L) :=
    fun k => (p.coeff k).2
  choose b hb using hb
  refine ⟨p.natDegree, b, hjinj ?_⟩
  have e1 := hpx
  rw [hp.as_sum] at e1
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_finsetSum, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_mul, Polynomial.eval₂_C] at e1
  rw [Finset.sum_range (fun k => algebraMap (j.comp g).range L (p.coeff k) * j y ^ k)] at e1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← e1, map_add (f := _), map_sum, map_pow]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow]
  exact congrArg (· * j y ^ (k : ℕ)) (hb k)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIdempotentElem
section
open TensorProduct

namespace GlobalTheory.IdempotentTensorOne

theorem isIntegral_of_isIdempotentElem {S B : Type} [CommRing S] [CommRing B] [Algebra S B]
    {e : B} (he : IsIdempotentElem e) : IsIntegral S e := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)), ?_⟩
  simp [sq, he.eq]

theorem exists_idempotent_tmul_one_eq (R A : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [Algebra R A] (hA : Algebra.Smooth R A)
    (ε : A ⊗[R] FractionRing R) (hε : IsIdempotentElem ε) :
    ∃ a : A, IsIdempotentElem a ∧ a ⊗ₜ[R] (1 : FractionRing R) = ε := by
  have : Algebra.Smooth R A := hA

  have hint : ε ∈ integralClosure A (A ⊗[R] FractionRing R) := isIntegral_of_isIdempotentElem hε
  obtain ⟨t, ht⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := R) (S := A) (B := FractionRing R)).2 ⟨ε, hint⟩
  have hε' : Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val t = ε :=
    congrArg Subtype.val ht
  have hdesc : ∀ u : A ⊗[R] integralClosure R (FractionRing R), ∃ a : A,
      a ⊗ₜ[R] (1 : FractionRing R) =
        Algebra.TensorProduct.map (AlgHom.id A A) (integralClosure R (FractionRing R)).val u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x y =>
      obtain ⟨r, hr⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := FractionRing R)).1
        ((mem_integralClosure_iff _ _).1 y.2)
      refine ⟨r • x, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u w hu hw =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hw
      exact ⟨a + b, by rw [TensorProduct.add_tmul, ha, hb, map_add (f := _)]⟩
  obtain ⟨a, ha⟩ := hdesc t
  rw [hε'] at ha
  refine ⟨a, ?_, ha⟩

  have hinj : Function.Injective (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  show (a * a) ⊗ₜ[R] (1 : FractionRing R) = a ⊗ₜ[R] (1 : FractionRing R)
  rw [← mul_one (1 : FractionRing R), ← Algebra.TensorProduct.tmul_mul_tmul, mul_one, ha, hε.eq]

end GlobalTheory.IdempotentTensorOne
end

