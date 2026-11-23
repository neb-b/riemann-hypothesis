module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0005
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0067
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0021

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFlatLocalRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing TensorProduct
open scoped Pointwise

section Flat

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem lid_rTensor_subtype_mem_smul_top (I : Ideal A) (t : I ⊗[A] M) :
    TensorProduct.lid A M (I.subtype.rTensor M t) ∈ I • (⊤ : Submodule A M) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul i m => simpa using Submodule.smul_mem_smul i.2 Submodule.mem_top
  | add s t hs ht => rw [map_add (f := _), map_add (f := _)]; exact add_mem hs ht

theorem exists_lid_rTensor_subtype_eq (I : Ideal A) {x : M} (hx : x ∈ I • (⊤ : Submodule A M)) :
    ∃ t : I ⊗[A] M, TensorProduct.lid A M (I.subtype.rTensor M t) = x := by
  refine Submodule.smul_induction_on hx (fun a ha m _ => ⟨⟨a, ha⟩ ⊗ₜ m, by simp⟩) ?_
  rintro x x' ⟨s, rfl⟩ ⟨s', rfl⟩
  exact ⟨s + s', by rw [map_add (f := _), map_add (f := _)]⟩

theorem mem_colon_smul_top_of_flat [Module.Flat A M] (J : Ideal A) (a : A) {v : M}
    (hv : a • v ∈ J • (⊤ : Submodule A M)) :
    v ∈ LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) • (⊤ : Submodule A M) := by
  set g : A →ₗ[A] A ⧸ J := J.mkQ ∘ₗ LinearMap.mulRight A a
  have hex := Module.Flat.rTensor_exact M (LinearMap.exact_subtype_ker_map g)
  have h0 : g.rTensor M ((1 : A) ⊗ₜ v) = 0 := by
    apply (TensorProduct.quotTensorEquivQuotSMul M J).injective
    rw [map_zero, LinearMap.rTensor_tmul]
    have : g 1 = Ideal.Quotient.mk J a := by simp [g, Ideal.Quotient.mk_eq_mk]
    rw [this, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, Submodule.Quotient.mk_eq_zero]
    exact hv
  obtain ⟨t, ht⟩ := (hex ((1 : A) ⊗ₜ v)).mp h0
  have := lid_rTensor_subtype_mem_smul_top (LinearMap.ker g) t
  rwa [ht, TensorProduct.lid_tmul, one_smul] at this

end Flat

theorem exists_not_mem_forall_mul_mem {R : Type} [CommRing R] (m J : Ideal R) (hJ : J ≠ ⊤)
    (h : ∃ n, m ^ n ≤ J) : ∃ a ∉ J, ∀ r ∈ m, r * a ∈ J := by
  classical
  have hkJ : m ^ Nat.find h ≤ J := Nat.find_spec h
  have hk0 : Nat.find h ≠ 0 := by
    intro h0
    apply hJ
    rw [h0, pow_zero, Ideal.one_eq_top] at hkJ
    exact top_le_iff.mp hkJ
  obtain ⟨a, ha, haJ⟩ := SetLike.not_le_iff_exists.mp
    (Nat.find_min h (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos))
  refine ⟨a, haJ, fun r hr => hkJ ?_⟩
  have : r * a ∈ m ^ (1 + (Nat.find h - 1)) := by
    rw [pow_add, pow_one]
    exact Ideal.mul_mem_mul hr ha
  rwa [Nat.add_sub_cancel' (Nat.pos_of_ne_zero hk0)] at this

section Local

variable {A B M : Type} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

theorem mem_smul_top_iff_mem_map_smul_top (I : Ideal A) (x : M) :
    x ∈ I • (⊤ : Submodule A M) ↔ x ∈ I.map (algebraMap A B) • (⊤ : Submodule B M) := by
  rw [← Submodule.restrictScalars_mem A (I.map (algebraMap A B) • (⊤ : Submodule B M)) x,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top]

theorem smul_mem_smul_top_of_mem (I : Ideal A) (y : B) {x : M}
    (hx : x ∈ I • (⊤ : Submodule A M)) : y • x ∈ I • (⊤ : Submodule A M) := by
  rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hx ⊢
  exact Submodule.smul_mem _ y hx

variable [IsNoetherianRing A] [IsLocalRing A] [Module.Flat A M]

theorem smul_regular_mod_of_pow_le (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (J : Ideal A) :
    (∃ n, maximalIdeal A ^ n ≤ J) →
      ∀ z : M, y • z ∈ J • (⊤ : Submodule A M) → z ∈ J • (⊤ : Submodule A M) := by
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro hpow z hz
  by_cases hJ : J = ⊤
  · subst hJ
    rw [Submodule.top_smul]
    exact Submodule.mem_top
  obtain ⟨a, haJ, hma⟩ := exists_not_mem_forall_mul_mem (maximalIdeal A) J hJ hpow
  have hlt : J < J ⊔ Ideal.span {a} :=
    lt_of_le_of_ne le_sup_left fun h =>
      haJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))
  have hz' := ih _ hlt (hpow.imp fun n hn => hn.trans le_sup_left) z
    (Submodule.smul_mono_left le_sup_left hz)
  rw [Submodule.sup_smul, Submodule.mem_sup] at hz'
  obtain ⟨w, hw, v, hv, rfl⟩ := hz'
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hv
  obtain ⟨u, -, rfl⟩ := hv
  have hyw := smul_mem_smul_top_of_mem J y hw
  have hau : a • (y • u) ∈ J • (⊤ : Submodule A M) := by
    rw [smul_comm]
    have : y • (a • u) = y • (w + a • u) - y • w := by rw [smul_add]; abel
    rw [this]
    exact sub_mem hz hyw
  have hK : LinearMap.ker (J.mkQ ∘ₗ LinearMap.mulRight A a) ≤ maximalIdeal A := by
    intro r hr
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.mulRight_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hr
    by_contra hrm
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hrm
    obtain ⟨r', rfl⟩ := hrm
    apply haJ
    have := J.mul_mem_left (↑r'⁻¹ : A) hr
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  have hu := h0 u (Submodule.smul_mono_left hK (mem_colon_smul_top_of_flat J a hau))
  refine add_mem hw ?_
  refine Submodule.smul_induction_on hu (fun r hr m _ => ?_) (fun x x' hx hx' => ?_)
  · rw [smul_smul, mul_comm]
    exact Submodule.smul_mem_smul (hma r hr) Submodule.mem_top
  · rw [smul_add]
    exact add_mem hx hx'

variable [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [Module.Finite B M]

theorem smul_regular_mod_ideal (y : B)
    (h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M)) (I : Ideal A) (z : M)
    (hz : y • z ∈ I • (⊤ : Submodule A M)) : z ∈ I • (⊤ : Submodule A M) := by
  set P : Submodule B M := I.map (algebraMap A B) • ⊤
  have hle : (maximalIdeal A).map (algebraMap A B) ≤ Ideal.jacobson ⊥ :=
    (IsLocalRing.map_maximalIdeal_le _).trans (IsLocalRing.maximalIdeal_le_jacobson _)
  have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M ⧸ P) _
    (by simpa only [Ideal.jacobson_bot] using hle)
  rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero P]
  have hmem : Submodule.Quotient.mk (p := P) z ∈
      (⨅ i : ℕ, ((maximalIdeal A).map (algebraMap A B)) ^ i • (⊤ : Submodule B (M ⧸ P))) := by
    rw [Submodule.mem_iInf]
    intro n
    have hn := smul_regular_mod_of_pow_le y h0 (I ⊔ maximalIdeal A ^ n) ⟨n, le_sup_right⟩ z
      (Submodule.smul_mono_left le_sup_left hz)
    rw [Submodule.sup_smul, Submodule.mem_sup] at hn
    obtain ⟨w, hw, v, hv, rfl⟩ := hn
    rw [mem_smul_top_iff_mem_map_smul_top (B := B)] at hw hv
    rw [Ideal.map_pow] at hv
    rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero P).mpr hw, zero_add]
    have hmap : (((maximalIdeal A).map (algebraMap A B)) ^ n • (⊤ : Submodule B M)).map P.mkQ ≤
        ((maximalIdeal A).map (algebraMap A B)) ^ n • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem hv)
  rw [hK] at hmem
  exact (Submodule.mem_bot B).mp hmem

end Local

theorem FlatLocalRegularElement.proof : FlatLocalRegularElement.Statement := by
  intro A B _ _ _ _ _ _ _ hloc M _ _ _ _ _ _ y _ hreg
  have h0 : ∀ u : M, y • u ∈ maximalIdeal A • (⊤ : Submodule A M) →
      u ∈ maximalIdeal A • (⊤ : Submodule A M) := by
    intro u hu
    rw [mem_smul_top_iff_mem_map_smul_top (B := B), ← Submodule.Quotient.mk_eq_zero] at hu ⊢
    refine hreg ?_
    show y • Submodule.Quotient.mk u = y • (0 : M ⧸ _)
    rw [smul_zero, ← Submodule.Quotient.mk_smul, hu]
  have hR := smul_regular_mod_ideal (B := B) y h0
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hab' : y • a = y • b := hab
    have h := hR ⊥ (a - b) (by rw [Submodule.bot_smul, Submodule.mem_bot, smul_sub, hab', sub_self])
    rw [Submodule.bot_smul, Submodule.mem_bot] at h
    exact sub_eq_zero.mp h
  · rw [Module.Flat.iff_rTensor_injective']
    intro I
    let π : M →ₗ[A] QuotSMulTop y M := (Submodule.mkQ (y • (⊤ : Submodule B M))).restrictScalars A
    let Y : M →ₗ[A] M := (LinearMap.lsmul B M y).restrictScalars A
    let μM : I ⊗[A] M →ₗ[A] M := TensorProduct.lid A M ∘ₗ I.subtype.rTensor M
    let μN : I ⊗[A] QuotSMulTop y M →ₗ[A] QuotSMulTop y M :=
      TensorProduct.lid A (QuotSMulTop y M) ∘ₗ I.subtype.rTensor (QuotSMulTop y M)
    have hμM : Function.Injective μM :=
      (TensorProduct.lid A M).injective.comp
        (Module.Flat.rTensor_preserves_injective_linearMap I.subtype Subtype.val_injective)
    have natπ : μN ∘ₗ π.lTensor I = π ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μN, μM, π]
    have natY : μM ∘ₗ Y.lTensor I = Y ∘ₗ μM :=
      TensorProduct.ext' fun i m => by simp [μM, Y, smul_comm (i : A) y m]
    have hπY : π ∘ₗ Y = 0 := LinearMap.ext fun m =>
      (Submodule.Quotient.mk_eq_zero _).mpr
        (Submodule.smul_mem_pointwise_smul m y ⊤ Submodule.mem_top)
    refine Function.Injective.of_comp (f := TensorProduct.lid A (QuotSMulTop y M)) ?_
    change Function.Injective μN
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro t ht
    have hπs : Function.Surjective π := Submodule.mkQ_surjective (y • (⊤ : Submodule B M))
    obtain ⟨s, rfl⟩ := LinearMap.lTensor_surjective I hπs t
    have h1 : π (μM s) = 0 := by
      rw [← LinearMap.comp_apply π μM, ← natπ, LinearMap.comp_apply]
      exact ht
    have h2 : μM s ∈ y • (⊤ : Submodule B M) := (Submodule.Quotient.mk_eq_zero _).mp h1
    obtain ⟨z, -, hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h2
    have h3 : y • z ∈ I • (⊤ : Submodule A M) := hz ▸ lid_rTensor_subtype_mem_smul_top I s
    obtain ⟨s', hs'⟩ := exists_lid_rTensor_subtype_eq I (hR I z h3)
    have h4 : s = Y.lTensor I s' := by
      apply hμM
      rw [← LinearMap.comp_apply μM (Y.lTensor I), natY, LinearMap.comp_apply]
      change μM s = y • μM s'
      rw [show μM s' = z from hs', hz]
    rw [h4, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hπY, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericNoetherNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Polynomial MvPolynomial Ideal Nat RingHom List

namespace GenericNoetherNormalisation

section Nagata

variable {A : Type*} [CommRing A] [IsDomain A] {n : ℕ} (f : MvPolynomial (Fin (n + 1)) A)
variable (v w : Fin (n + 1) →₀ ℕ)



end Nagata

section Combination

variable {A D : Type*} [CommRing A] [CommRing D] [Algebra A D] {m : ℕ}

variable {c : A} {z : Fin m → D} {s : Finset D}

end Combination

universe u

theorem proof : GenericNoetherNormalisation.Statement.{u} :=
  _root_.UpperTheory.Reformulated.B.GenericNoetherNormalisationCapelliIdentities.proof

end GenericNoetherNormalisation

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGenericProjectionFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Matrix

noncomputable section

def entries {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : Fin a × Fin b → ℂ := fun ij => A ij.1 ij.2

def rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  bind₁ (fun ij : Fin d × Fin n => ∑ l, C (F (s ij.1) l) * X (l, ij.2)) p

theorem eval_rowsPoly {n d : ℕ} (F : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (p : MvPolynomial (Fin d × Fin n) ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
    eval (entries U) (rowsPoly F s p) = eval (entries ((F * U).submatrix s id)) p := by
  change eval₂Hom (RingHom.id ℂ) (entries U) (bind₁ _ p) = eval₂Hom (RingHom.id ℂ) _ p
  rw [eval₂Hom_bind₁]
  congr 2
  funext ij
  simp [entries, Matrix.mul_apply]

theorem exists_rows_eq {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) (A : Matrix (Fin d) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ, (F * U).submatrix s id = A := by
  refine ⟨star F * Matrix.of (Function.extend s (fun i => A i) 0), ?_⟩
  rw [← Matrix.mul_assoc, mem_unitaryGroup_iff.mp hF, Matrix.one_mul]
  ext i j
  simp [hs.extend_apply]

theorem rowsPoly_ne_zero {n d : ℕ} {F : Matrix (Fin n) (Fin n) ℂ} (hF : F ∈ unitaryGroup (Fin n) ℂ)
    {s : Fin d → Fin n} (hs : Function.Injective s) {p : MvPolynomial (Fin d × Fin n) ℂ}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : eval (entries A) p ≠ 0) : rowsPoly F s p ≠ 0 := by
  obtain ⟨U, hU⟩ := exists_rows_eq hF hs A
  intro h
  apply hA
  rw [← hU, ← eval_rowsPoly, h, map_zero]

theorem GenericProjectionFinite.proof (hO : FiniteProjectionsContainOpen.Statement)
    (hU : UnitaryZariskiDense.Statement) :
    GenericProjectionFinite.Statement := by
  classical
  intro n d J hJ hd
  obtain ⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, hW⟩ := hO n d J hJ hd
  have good : ∀ A : Matrix (Fin d) (Fin n) ℂ, (∃ p ∈ S, eval (entries A) p ≠ 0) →
      IsFiniteProjection J A := fun A hA => hW (by rw [hS]; exact hA)
  have hA₀' := hA₀
  rw [hS] at hA₀'
  obtain ⟨p, hpS, hp⟩ := hA₀'
  have hdn : d ≤ n := by
    have h := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
    exact_mod_cast h
  refine ⟨⟨W, ⟨S, hS⟩, ⟨A₀, hA₀⟩, fun A hA => hW hA⟩, ⟨A₀, hW hA₀⟩, fun D hD hcl => ?_, fun m F => ?_⟩
  · obtain ⟨U, hUu, hUp⟩ := hU n (rowsPoly 1 (Fin.castLE hdn) p)
      (rowsPoly_ne_zero (one_mem _) (Fin.castLE_injective hdn) hp)
    have hUp' : eval (entries (U.submatrix (Fin.castLE hdn) id)) p ≠ 0 := by
      have := eval_rowsPoly 1 (Fin.castLE hdn) p U
      rw [Matrix.one_mul] at this
      exact this ▸ hUp
    have hAo : U.submatrix (Fin.castLE hdn) id ∈ orthoRows d n := by
      show _ * _ = _
      rw [conjTranspose_submatrix, ← submatrix_mul _ _ _ _ _ Function.bijective_id,
        ← star_eq_conjTranspose, mem_unitaryGroup_iff.mp hUu,
        submatrix_one _ (Fin.castLE_injective hdn)]
    have hopen : IsOpen {B : Matrix (Fin d) (Fin n) ℂ | eval (entries B) p ≠ 0} :=
      isOpen_ne_fun ((MvPolynomial.continuous_eval p).comp
        (continuous_pi fun ij => continuous_id.matrix_elem ij.1 ij.2)) continuous_const
    obtain ⟨B, hBp, hBD⟩ := mem_closure_iff.mp (hcl hAo) _ hopen hUp'
    exact ⟨B, hBD, good B ⟨p, hpS, hBp⟩⟩
  · have hQ : (∏ ks : Fin m × (Fin d ↪ Fin n), rowsPoly (F ks.1 : Matrix (Fin n) (Fin n) ℂ) ks.2 p) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun ks _ => rowsPoly_ne_zero (F ks.1).2 ks.2.injective hp
    obtain ⟨U, hUu, hUQ⟩ := hU n _ hQ
    refine ⟨U, hUu, fun k s => good _ ⟨p, hpS, ?_⟩⟩
    rw [map_prod] at hUQ
    have := Finset.prod_ne_zero_iff.mp hUQ (k, s) (Finset.mem_univ _)
    change eval (entries U) (rowsPoly _ _ p) ≠ 0 at this
    rwa [eval_rowsPoly] at this

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermFiniteProjection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem eventually_eq_zero_of_lines {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hl : ∀ v : Fin d → ℂ, ∀ᶠ t in 𝓝 (0 : ℂ), h (a + t • v) = 0) :
    ∀ᶠ y in 𝓝 a, h y = 0 := by
  obtain ⟨r, hr, han⟩ := ha.exists_ball_analyticOnNhd
  filter_upwards [Metric.ball_mem_nhds a hr] with y hy
  by_cases hv : y - a = 0
  · have hya : y = a := sub_eq_zero.1 hv
    have h0 := (hl 0).self_of_nhds
    simpa [hya] using h0
  have hvpos : 0 < ‖y - a‖ := norm_pos_iff.2 hv
  have hmaps : ∀ t ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖), a + t • (y - a) ∈ Metric.ball a r := by
    intro t ht
    rw [Metric.mem_ball, dist_zero_right, lt_div_iff₀ hvpos] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    exact ht
  have hg : AnalyticOnNhd ℂ (fun t : ℂ => h (a + t • (y - a))) (Metric.ball (0 : ℂ) (r / ‖y - a‖)) := by
    intro t ht
    have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • (y - a)) t := by fun_prop
    exact AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • (y - a)) (han _ (hmaps t ht)) h1
  have h1 : (1 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := by
    rw [Metric.mem_ball, dist_zero_right, norm_one, one_lt_div hvpos, ← dist_eq_norm]
    exact hy
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (r / ‖y - a‖) := Metric.mem_ball_self (div_pos hr hvpos)
  have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball (0 : ℂ) _).isPreconnected h0
    (by filter_upwards [hl (y - a)] with t ht using ht) h1
  simpa using hz

theorem exists_line_eventually_ne_zero {d : ℕ} {h : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ}
    (ha : AnalyticAt ℂ h a) (hne : ¬ ∀ᶠ y in 𝓝 a, h y = 0) :
    ∃ v : Fin d → ℂ, ∀ᶠ t in 𝓝[≠] (0 : ℂ), h (a + t • v) ≠ 0 := by
  by_contra hcon
  refine hne (eventually_eq_zero_of_lines ha fun v => ?_)
  have h1 : AnalyticAt ℂ (fun t : ℂ => a + t • v) 0 := by fun_prop
  have ha' : AnalyticAt ℂ h (a + (0 : ℂ) • v) := by simpa using ha
  rcases (AnalyticAt.comp (g := h) (f := fun s : ℂ => a + s • v) ha' h1).eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · exact h0
  · exact absurd ⟨v, h0⟩ hcon

theorem exists_proj_fibres_line {d : ℕ} (v : Fin d → ℂ) (hv : v ≠ 0) :
    ∃ π : (Fin d → ℂ) →L[ℂ] (Fin (d - 1) → ℂ), ∀ y y', π y = π y' → ∃ t : ℂ, y = y' + t • v := by
  have hrank : Module.finrank ℂ ((Fin d → ℂ) ⧸ (ℂ ∙ v)) = Module.finrank ℂ (Fin (d - 1) → ℂ) := by
    have h1 := Submodule.finrank_quotient_add_finrank (ℂ ∙ v)
    rw [finrank_span_singleton hv, Module.finrank_fin_fun] at h1
    rw [Module.finrank_fin_fun]
    omega
  let e := LinearEquiv.ofFinrankEq _ _ hrank
  refine ⟨LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (ℂ ∙ v).mkQ), fun y y' hyy => ?_⟩
  have hq : (ℂ ∙ v).mkQ y = (ℂ ∙ v).mkQ y' := e.injective hyy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_span_singleton] at hq
  obtain ⟨t, ht⟩ := hq
  exact ⟨t, by rw [ht]; abel⟩

theorem GermFiniteProjection.proof : GermFiniteProjection.Statement := by
  intro σ _ X w _ hirr
  classical
  have hw : w ∈ X := hirr.1
  have hP : ∃ d : ℕ, ∃ A : (σ → ℂ) →L[ℂ] (Fin d → ℂ), ∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w := by
    let e : (σ → ℂ) ≃ₗ[ℂ] (Fin (Fintype.card σ) → ℂ) :=
      LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm
    exact ⟨Fintype.card σ, LinearMap.toContinuousLinearMap e.toLinearMap, Set.univ, univ_mem,
      fun x _ hx => e.injective hx⟩
  obtain ⟨A, W, hW, hAW⟩ := Nat.find_spec hP
  refine ⟨Nat.find hP, A, ⟨W, hW, hAW⟩, fun h hh hXh => ?_⟩
  by_contra hne
  have hAw : h (A w) = 0 := hXh.self_of_nhds hw
  obtain ⟨v, hv⟩ := exists_line_eventually_ne_zero hh hne
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨t, ht⟩ := hv.exists
    simp [hAw] at ht
  have hd : Nat.find hP - 1 < Nat.find hP := by
    have : 0 < Nat.find hP := Nat.pos_of_ne_zero fun h0 => hv0 (funext fun i => (Fin.cast h0 i).elim0)
    omega
  obtain ⟨π, hπ⟩ := exists_proj_fibres_line v hv0
  obtain ⟨ε, hε, hεv⟩ := Metric.mem_nhdsWithin_iff.1 hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  have hcont : ∀ᶠ x in 𝓝 w, A x ∈ Metric.ball (A w) (ε * ‖v‖) :=
    A.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (mul_pos hε hvpos))
  refine Nat.find_min hP hd ⟨π.comp A, W ∩ {x | (x ∈ X → h (A x) = 0) ∧ A x ∈ Metric.ball (A w) (ε * ‖v‖)},
    inter_mem hW (hXh.and hcont), ?_⟩
  rintro x ⟨hxX, hxW, hxh, hxb⟩ hπx
  apply hAW x ⟨hxX, hxW⟩
  obtain ⟨t, ht⟩ := hπ (A x) (A w) hπx
  by_cases ht0 : t = 0
  · simpa [ht0] using ht
  exfalso
  have htε : t ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    have hb : ‖t • v‖ < ε * ‖v‖ := by
      rw [Metric.mem_ball, dist_eq_norm, ht, add_sub_cancel_left] at hxb
      exact hxb
    rw [norm_smul] at hb
    exact lt_of_mul_lt_mul_right hb hvpos.le
  exact hεv ⟨htε, ht0⟩ (by rw [← ht]; exact hxh hxX)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIrreducibleGermProjectionOpenNear
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

theorem IrreducibleGermProjectionOpenNear.proof (hiso : IsolatedFibreNear.Statement)
    (himg : IrreducibleGermProjectionImageNear.Statement) (hopen : FiniteGermProjectionOpenAt.Statement) :
    IrreducibleGermProjectionOpenNear.Statement := by
  intro σ _ X w d A hX hirr hisow hinj
  obtain ⟨N₁, hN₁, h₁⟩ := hiso σ X w d A hX hisow
  obtain ⟨N₂, hN₂, h₂⟩ := himg σ X w d A hX hirr hisow hinj
  obtain ⟨N, k, f, hNo, hwN, hf, hXN⟩ := hX
  refine ⟨N₁ ∩ N₂ ∩ N, Filter.inter_mem (Filter.inter_mem hN₁ hN₂) (hNo.mem_nhds hwN), ?_⟩
  rintro x ⟨hxX, ⟨hx₁, hx₂⟩, hxN⟩ V hV

  have hXx : IsAnalyticNear X x := ⟨N, k, f, hNo, hxN, hf, hXN⟩
  exact hopen σ X x d A hXx (h₁ x ⟨hxX, hx₁⟩) (h₂ x ⟨hxX, hx₂⟩) V hV

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

