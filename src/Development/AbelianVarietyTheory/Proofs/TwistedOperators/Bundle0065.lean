module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianTraceFormOfTraceFormPerfect
section
noncomputable section

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS

section

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem form_conj_symm (σ : A →+* A) (hσ : ∀ x, σ (σ x) = x) {J : Matrix n n A}
    (hJ : IsHerm σ J) (a b : n → A) : σ (form σ J b a) = form σ J a b := by
  have hJij : ∀ i j, σ (J i j) = J j i := fun i j => by
    have := congrFun (congrFun hJ j) i
    simpa [cT] using this
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [form, hform, map_sum, map_mul, hσ, hJij]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem eq_zero_of_form_eq_zero (σ : A →+* A) {J : Matrix n n A} (hJ : IsUnit J.det)
    (a : n → A) (h0 : ∀ w, form σ J a w = 0) : a = 0 := by
  have hJa : J *ᵥ a = 0 := by
    funext i
    have := h0 (Pi.single i 1)
    have hs : (fun k => σ ((Pi.single i (1 : A) : n → A) k)) = Pi.single i 1 := by
      funext k; by_cases hk : k = i
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rw [form, hform_eq, hs] at this
    simpa [dotProduct, Pi.single_apply] using this
  calc a = (J⁻¹ * J) *ᵥ a := by rw [Matrix.nonsing_inv_mul _ hJ, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hJa, Matrix.mulVec_zero]

end

theorem traceClause_of_tracePerfect (hP : TracePerfect) : TraceClause := by
  intro F E _ _ _ _ n _ _ σ J γ h hA
  haveI := quad_finite h.quad
  haveI := genAlg_isReduced h hA
  obtain ⟨b⟩ := hA.2.2.1
  haveI : Module.Free E (genAlg (γ : Matrix n n E)) := Module.Free.of_basis b
  haveI : Module.Finite E (genAlg (γ : Matrix n n E)) := Module.Finite.of_basis b
  obtain ⟨v, hv⟩ := hA.2.2.2.1
  obtain ⟨τ, hτ, hττ, hτE, hplus⟩ := exists_adjEquiv h hA
  have hP' := hP F E (genAlg (γ : Matrix n n E))
  let φ : genAlg (γ : Matrix n n E) →ₗ[E] E :=
    { toFun := fun y => form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v
      map_add' := fun a b => by
        simp only [form, hform_eq, Subalgebra.coe_add, Matrix.add_mulVec, Matrix.mulVec_add,
          dotProduct_add]
      map_smul' := fun c a => by
        simp only [form, hform_eq, Subalgebra.coe_smul, Matrix.smul_mulVec,
          Matrix.mulVec_smul, dotProduct_smul, RingHom.id_apply, smul_eq_mul] }
  obtain ⟨x, hx⟩ := hP'.2 φ
  have hxy : ∀ y, Algebra.trace E _ (x * y) = form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) v :=
    fun y => by
      have := LinearMap.congr_fun hx y
      rwa [Algebra.traceForm_apply] at this

  have hK : ∀ y y' : genAlg (γ : Matrix n n E),
      form (σ : E →+* E) J ((y : Matrix n n E) *ᵥ v) ((y' : Matrix n n E) *ᵥ v) =
        Algebra.trace E _ (x * (τ y' * y)) := fun y y' => by
    rw [hxy, form_adj _ h.nondeg, ← hτ, Matrix.mulVec_mulVec]
    rfl

  let σE : E ≃+* E := RingEquiv.ofBijective (σ : E →+* E) (Function.Involutive.bijective h.quad.invol)
  have hTr : ∀ z, Algebra.trace E _ (τ z) = σ (Algebra.trace E (genAlg (γ : Matrix n n E)) z) := by
    intro z
    have he : (algebraMap E (genAlg (γ : Matrix n n E))).comp (σE : E →+* E) =
        (τ.toRingEquiv : genAlg (γ : Matrix n n E) →+* genAlg (γ : Matrix n n E)).comp
          (algebraMap E (genAlg (γ : Matrix n n E))) := RingHom.ext fun e => (hτE e).symm
    have := Algebra.trace_eq_of_equiv_equiv σE τ.toRingEquiv he z
    rw [this]
    exact (σE.apply_symm_apply _).symm

  have hxτ : τ x = x := by
    refine hP'.1 (LinearMap.ext fun y => ?_)
    simp only [Algebra.traceForm_apply]
    have e1 : τ x * y = τ (x * (τ y * 1)) := by rw [mul_one, map_mul, hττ]
    rw [e1, hTr, ← hK]
    have hs := form_conj_symm (σ : E →+* E) h.quad.invol h.herm
      ((y : Matrix n n E) *ᵥ v) (((1 : genAlg (γ : Matrix n n E)) : Matrix n n E) *ᵥ v)
    simp only [RingHom.coe_coe] at hs
    rw [hs, hK, map_one, one_mul]
  have hxplus : x ∈ plusAlg σ J (γ : Matrix n n E) := (hplus x).2 hxτ

  have hinj : ∀ y : genAlg (γ : Matrix n n E), x * y = 0 → y = 0 := by
    intro y hy
    have h0 : (y : Matrix n n E) *ᵥ v = 0 := by
      refine eq_zero_of_form_eq_zero (σ : E →+* E) h.nondeg _ fun w => ?_
      obtain ⟨y', rfl⟩ := hv.2 w
      simp only
      rw [hK, mul_left_comm, hy, mul_zero, map_zero]
    refine hv.1 ?_
    simp only [h0, ZeroMemClass.coe_zero, Matrix.zero_mulVec]

  let xp : plusAlg σ J (γ : Matrix n n E) := ⟨x, hxplus⟩
  haveI : Module.Finite F (genAlg (γ : Matrix n n E)) := Module.Finite.trans E _
  have hsurj : Function.Surjective (LinearMap.mulLeft F xp) := by
    refine LinearMap.injective_iff_surjective.1 fun a c hac => ?_
    have : x * ((a : genAlg (γ : Matrix n n E)) - c) = 0 := by
      have := congrArg Subtype.val hac
      simp only [LinearMap.mulLeft_apply] at this
      rw [mul_sub]; exact sub_eq_zero.2 this
    exact Subtype.ext (sub_eq_zero.1 (hinj _ this))
  obtain ⟨w, hw⟩ := hsurj 1
  have hu : IsUnit xp := ⟨⟨xp, w, hw, by rw [mul_comm]; exact hw⟩, rfl⟩
  refine ⟨hu.unit, v, hv, fun y y' => ⟨τ y', hτ y', ?_⟩⟩
  rw [hK]
  congr 1
  change x * (τ y' * y) = x * y * τ y'
  ring

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LaurentPolynomialCharacterIsMonomial
section
noncomputable section

namespace GlobalTheory.RegSS

def monomialChar (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (s : ℕ) (a : Fin s → ℤ) :
    (Fin s → Fˣ) →* Ω where
  toFun t := algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, map_mul]

theorem characterMonomial : CharacterMonomial := by
  classical
  intro F Ω _ _ _ s f S c hf
  by_contra hno

  have hdiff : ∀ a, monomialChar F Ω s a ≠ f := by
    intro a hEq
    refine hno ⟨a, fun t => ?_⟩
    rw [← hEq]
    rfl

  let l : ((Fin s → Fˣ) →* Ω) →₀ Ω :=
    Finsupp.single f 1 - ∑ a ∈ S, Finsupp.single (monomialChar F Ω s a) (c a)
  have hvanish : Finsupp.linearCombination Ω
      (fun φ : (Fin s → Fˣ) →* Ω => (φ : (Fin s → Fˣ) → Ω)) l = 0 := by
    funext t
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [l, map_sub, map_sum, Finsupp.linearCombination_single, one_smul,
      Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hf t]
    rw [sub_eq_zero]
    refine Finset.sum_congr rfl fun a _ => ?_
    show _ = c a * algebraMap F Ω ((∏ j, t j ^ a j : Fˣ) : F)
    rw [Algebra.smul_def, mul_comm]
  have hl0 : l = 0 := (linearIndependent_iff.mp (linearIndependent_monoidHom _ Ω)) l hvanish
  have hlf : l f = 1 := by
    simp only [l, Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne' (hdiff a), sub_zero]
  rw [hl0, Finsupp.zero_apply] at hlf
  exact zero_ne_one hlf

end GlobalTheory.RegSS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentral
section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem subtorusNotCentral_of (hU : UnitaryCommutant) (hL : SubtorusLaurent)
    (hC : CharacterMonomial) : SubtorusNotCentral := by
  intro F E _ _ _ _ n _ _ σ J γ hreg hE s hs A
  by_contra hcon
  push Not at hcon
  have hfield : IsField (E ⊗[F] F) :=
    MulEquiv.isField hE (Algebra.TensorProduct.rid F F E).toMulEquiv
  haveI : Nontrivial (E ⊗[F] F) := hfield.nontrivial
  haveI : CharZero (E ⊗[F] F) := charZero_of_injective_algebraMap (algebraMap F (E ⊗[F] F)).injective
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  let t₀ : Fin s → Fˣ := fun _ => Units.mk0 2 h2
  have hsq : A.hom F (t₀ * t₀) = 1 := by
    refine Units.ext ?_
    ext i j
    have hH : IsHerm (sigR σ F) (J.map (inclE (F := F) F)) := by
      have h : cT (σ : E →+* E) J = J := hreg.herm
      change cT _ _ = _
      conv_rhs => rw [← h]
      ext a b
      simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
      exact (inclE_conj σ F _).symm
    have hdet : IsUnit (J.map (inclE (F := F) F)).det := isUnit_det_map _ hreg.nondeg
    have hsc : ∀ t, (A.hom F t : Matrix n n (E ⊗[F] F)) =
        ((A.hom F t : Matrix n n (E ⊗[F] F)) i i) • (1 : Matrix n n (E ⊗[F] F)) := by
      intro t
      obtain ⟨c, hc⟩ := hU (E ⊗[F] F) hfield (sigR σ F) (sigR_sigR hreg.quad.invol F) n _ hH hdet
        (A.hom F t : Matrix n n (E ⊗[F] F)) (fun g hg => congrArg Units.val (hcon g hg t))
      rw [hc]; simp
    letI := hfield.toField
    let f : (Fin s → Fˣ) →* E ⊗[F] F :=
      { toFun := fun t => (A.hom F t : Matrix n n (E ⊗[F] F)) i i
        map_one' := by simp
        map_mul' := fun a b => by
          rw [map_mul, Units.val_mul, hsc a, smul_mul_assoc, one_mul]
          simp }
    obtain ⟨S, C, hSC⟩ := hL F E n σ J γ s A
    obtain ⟨a, ha⟩ := hC F (E ⊗[F] F) s f S (fun a => C a i i) (fun t => by
      change (A.hom F t : Matrix n n (E ⊗[F] F)) i i = _
      rw [hSC t, Matrix.sum_apply]
      rfl)
    have hfix : sigR σ F (f t₀) = f t₀ := by
      rw [ha]; simp [sigR]
    have hmem := (mem_UJ_iff_mul_adj (sigR σ F) hdet (A.hom F t₀)).1 (A.mem F t₀).1
    have hadj : adj (sigR σ F) (J.map (inclE (F := F) F)) (A.hom F t₀ : Matrix n n (E ⊗[F] F)) =
        (A.hom F t₀ : Matrix n n (E ⊗[F] F)) := by
      rw [hsc t₀, adj_smul, adj_one _ hdet]
      exact congrArg (· • (1 : Matrix n n (E ⊗[F] F))) hfix
    rw [hadj] at hmem
    rw [map_mul, Units.val_mul, hmem, Units.val_one]
  have h1 : t₀ * t₀ = 1 := A.inj F (by rw [hsq, map_one])
  have h4 := congrArg Units.val (congrFun h1 ⟨0, hs⟩)
  simp only [t₀, Pi.mul_apply, Units.val_mul, Units.val_mk0, Pi.one_apply, Units.val_one] at h4
  norm_num at h4

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneBoundedOfUnitBoundedOfAdelicLattice
section
open GlobalTheory.RegSS Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem normOne_bounded_of_unit_bounded {B X : Type} [CommRing B] [CommRing X]
    [TopologicalSpace X] [IsTopologicalRing X] (i : B →+* X) (τ : B →+* B) (s : X →+* X)
    (hs : Continuous s) (hi : ∀ b, i (τ b) = s (i b))
    (hfin : ∀ D : Set X, IsCompact D → {β : B | i β ∈ D}.Finite)
    (D : Set X) (hD : IsCompact D)
    (h : ∀ u : X, u * s u = 1 → ∃ β : B, IsUnit β ∧ u * i β ∈ D) :
    ∃ D' : Set X, IsCompact D' ∧
      ∀ u : X, u * s u = 1 → ∃ β : B, β * τ β = 1 ∧ u * i β ∈ D' := by
  classical

  set K : Set X := (fun x => x * s x) '' D with hK
  have hKc : IsCompact K := hD.image (continuous_id.mul hs : Continuous fun x : X => x * s x)

  set T : Set B := {γ : B | i γ ∈ K} with hT
  have hTf : T.Finite := hfin K hKc

  let c : B → B := fun γ =>
    if h : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = γ then (Classical.choose h).2 else 0
  refine ⟨⋃ γ ∈ T, (fun x => x * i (c γ)) '' D,
    hTf.isCompact_biUnion fun γ _ => hD.image (continuous_mul_const _), ?_⟩
  intro u hu
  obtain ⟨β, hβ, hβD⟩ := h u hu
  obtain ⟨β', hβ'⟩ := hβ.exists_right_inv
  have hex : ∃ p : B × B, p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := ⟨(β, β'), hβ', rfl⟩
  set p := Classical.choose hex with hpdef
  have hp : p.1 * p.2 = 1 ∧ p.1 * τ p.1 = β * τ β := Classical.choose_spec hex
  have hc : c (β * τ β) = p.2 := by
    show (if h : ∃ q : B × B, q.1 * q.2 = 1 ∧ q.1 * τ q.1 = β * τ β
      then (Classical.choose h).2 else 0) = p.2
    rw [dite_eq_left hex]

  refine ⟨β * p.2, ?_, ?_⟩
  · calc β * p.2 * τ (β * p.2) = (β * τ β) * (p.2 * τ p.2) := by rw [map_mul]; ring
      _ = (p.1 * τ p.1) * (p.2 * τ p.2) := by rw [hp.2]
      _ = (p.1 * p.2) * τ (p.1 * p.2) := by rw [map_mul τ p.1 p.2]; ring
      _ = 1 := by rw [hp.1, map_one, one_mul]
  · have hmem : β * τ β ∈ T := by
      show i (β * τ β) ∈ K
      refine ⟨u * i β, hβD, ?_⟩
      show u * i β * s (u * i β) = i (β * τ β)
      rw [map_mul s, map_mul i, hi]
      calc u * i β * (s u * s (i β)) = (u * s u) * (i β * s (i β)) := by ring
        _ = i β * s (i β) := by rw [hu, one_mul]
    refine Set.mem_biUnion hmem ⟨u * i β, hβD, ?_⟩
    show u * i β * i (c (β * τ β)) = u * i (β * p.2)
    rw [hc, map_mul i, mul_assoc]

theorem normOfUnitBounded_of_tensorLattice :
    GlobalTheory.RegSS.TensorLattice → GlobalTheory.RegSS.NormOfUnitBounded := by
  intro hL F B _ _ _ _ _ τ hU
  let _ : TopologicalSpace (B ⊗[F] AdeleRing (𝓞 F) F) :=
    Formalism.BasicNotions.tensTopL (F := F) (E := B) (AdeleRing (𝓞 F) F)
  obtain ⟨hTR, -, -, -, -, hfin, -⟩ := hL F B
  have := hTR
  obtain ⟨D, hD, hDu⟩ := hU
  exact normOne_bounded_of_unit_bounded (inclE (F := F) (AdeleRing (𝓞 F) F)) (τ : B →+* B)
    (sigR τ (AdeleRing (𝓞 F) F)) (continuous_sigR τ _) (fun b => inclE_conj τ _ b) hfin D hD hDu

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.RegSS
open scoped NNReal ENNReal

namespace GlobalTheory.RegSS

theorem measure_le_of_sub_mem_imp_eq {X : Type} [AddCommGroup X] [MeasurableSpace X]
    [MeasurableAdd X] (μ : Measure X) [μ.IsAddLeftInvariant] (Λ : AddSubgroup X) [Countable Λ]
    (C S : Set X) (hCm : MeasurableSet C) (hC : ∀ x, ∃ l ∈ Λ, x - l ∈ C) (hS : MeasurableSet S)
    (h : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ → x = y) : μ S ≤ μ C := by
  let A : Λ → Set X := fun l => (fun x => (l : X) + x) ⁻¹' S ∩ C
  have hAm : ∀ l, MeasurableSet (A l) := fun l =>
    ((measurable_const_add (l : X)) hS).inter hCm
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro l m hlm
    rw [Function.onFun, Set.disjoint_left]
    rintro x ⟨hx, -⟩ ⟨hx', -⟩
    apply hlm
    have := h _ hx _ hx' (by simpa using Λ.sub_mem l.2 m.2)
    exact Subtype.ext (add_right_cancel this)
  have hcov : S ⊆ ⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l := by
    intro x hx
    obtain ⟨l, hl, hxl⟩ := hC x
    refine Set.mem_iUnion.2 ⟨⟨l, hl⟩, ?_, ?_⟩
    · simpa using hx
    · simpa [neg_add_eq_sub] using hxl
  calc μ S ≤ μ (⋃ l : Λ, (fun x => -(l : X) + x) ⁻¹' A l) := measure_mono hcov
    _ ≤ ∑' l : Λ, μ ((fun x => -(l : X) + x) ⁻¹' A l) := measure_iUnion_le _
    _ = ∑' l : Λ, μ (A l) := by simp_rw [measure_preimage_add]
    _ = μ (⋃ l, A l) := (measure_iUnion hdisj hAm).symm
    _ ≤ μ C := measure_mono (Set.iUnion_subset fun l => Set.inter_subset_right)

theorem measure_preimage_mul_of_norm_one {X : Type} [CommRing X] [TopologicalSpace X]
    [IsTopologicalRing X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [μ.IsAddHaarMeasure] [μ.Regular] (τ : X →+* X) (hτ : Continuous τ)
    (hττ : ∀ x, τ (τ x) = x) (u : X) (hu : u * τ u = 1) (S : Set X) :
    μ ((fun x => u * x) ⁻¹' S) = μ S := by
  let T : X ≃ₜ+ X :=
    { toFun := τ, invFun := τ, left_inv := hττ, right_inv := hττ, map_add' := map_add τ,
      continuous_toFun := hτ, continuous_invFun := hτ }
  let M : X ≃ₜ+ X :=
    { toFun := fun x => u * x, invFun := fun x => τ u * x,
      left_inv := fun x => by simp only [← mul_assoc, mul_comm (τ u) u, hu, one_mul],
      right_inv := fun x => by simp only [← mul_assoc, hu, one_mul],
      map_add' := mul_add u,
      continuous_toFun := continuous_const_mul u, continuous_invFun := continuous_const_mul _ }
  have h1 : T.trans T = ContinuousAddEquiv.refl X := by
    ext x; exact hττ x
  have h2 : (T.trans M).trans (T.trans M) = ContinuousAddEquiv.refl X := by
    ext x
    change u * τ (u * τ x) = x
    rw [map_mul, hττ, ← mul_assoc, hu, one_mul]
  have e1 := congrArg addEquivAddHaarChar h1
  have e2 := congrArg addEquivAddHaarChar h2
  simp only [addEquivAddHaarChar_trans, addEquivAddHaarChar_refl] at e1 e2
  have e3 : addEquivAddHaarChar M * addEquivAddHaarChar M = 1 := by
    rw [← e2, mul_mul_mul_comm, e1, one_mul]
  have e4 : addEquivAddHaarChar M = 1 := by
    have := (pow_eq_one_iff_of_nonneg (a := addEquivAddHaarChar M) zero_le two_ne_zero).1
      (by rw [sq, e3])
    exact this
  have := addEquivAddHaarChar_smul_preimage μ (X := S) M
  rw [e4, one_smul] at this
  exact this

theorem normOnePacking : NormOnePacking := by
  intro X _ _ _ _ _ _ _ τ hτ hττ Λ hΛ ⟨C, hCc, hC⟩
  borelize X
  let μ : Measure X := addHaar
  have huniv : μ Set.univ = ∞ := measure_univ_of_isAddLeftInvariant μ
  obtain ⟨K, -, hKc, hK⟩ := isOpen_univ.exists_lt_isCompact (μ := μ) (r := μ C)
    (by rw [huniv]; exact hCc.measure_lt_top)
  refine ⟨(fun p : X × X => p.1 - p.2) '' (K ×ˢ K), (hKc.prod hKc).image (by fun_prop), ?_⟩
  intro u hu
  by_contra hcon
  have hle := measure_le_of_sub_mem_imp_eq μ Λ C ((fun x => u * x) ⁻¹' K) hCc.measurableSet hC
    ((continuous_const_mul u).measurable hKc.measurableSet) (by
      intro x hx y hy hxy
      by_contra hne
      exact hcon ⟨x - y, hxy, sub_ne_zero.2 hne, (u * x, u * y), ⟨hx, hy⟩, (mul_sub u x y).symm⟩)
  rw [measure_preimage_mul_of_norm_one μ τ hτ hττ u hu] at hle
  exact absurd hK (not_lt.2 hle)

end GlobalTheory.RegSS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFieldsBaseChangeIsFieldIff
section
open GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

theorem isField_pi_fin_iff {k : ℕ} (A : Fin k → Type) [∀ i, CommRing (A i)]
    [∀ i, Nontrivial (A i)] : IsField (∀ i, A i) ↔ k = 1 ∧ ∀ i, IsField (A i) := by
  constructor
  · intro h

    have hk : k = 1 := by
      rcases Nat.lt_trichotomy k 1 with hlt | heq | hgt
      · obtain ⟨a, b, hab⟩ := h.exists_pair_ne
        have hk0 : k = 0 := by omega
        subst hk0
        exact absurd (funext fun i => i.elim0) hab
      · exact heq
      · let i₀ : Fin k := ⟨0, by omega⟩
        let i₁ : Fin k := ⟨1, hgt⟩
        have hne : i₁ ≠ i₀ := by
          intro hij
          have := congrArg Fin.val hij
          simp [i₀, i₁] at this
        have hx : (Pi.single i₀ (1 : A i₀) : ∀ i, A i) ≠ 0 := by
          intro hx
          have := congrFun hx i₀
          simp at this
        obtain ⟨y, hy⟩ := h.mul_inv_cancel hx
        have := congrFun hy i₁
        rw [Pi.mul_apply, Pi.single_eq_of_ne hne, zero_mul, Pi.one_apply] at this
        exact absurd this zero_ne_one
    refine ⟨hk, ?_⟩
    subst hk
    intro i
    have hdef : IsField (A default) := (RingEquiv.piUnique A).symm.toMulEquiv.isField h
    exact (Unique.eq_default i).symm ▸ hdef
  · rintro ⟨rfl, h⟩
    exact (RingEquiv.piUnique A).toMulEquiv.isField (h default)

theorem tensorFieldIff : TensorFieldIff := by
  intro F E _ _ _ _ P _ _ k K _ _ ⟨e⟩

  let φ : P ⊗[F] E ≃ₐ[F] ∀ i, K i ⊗[F] E :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans
      ((Algebra.TensorProduct.comm F _ E).trans
        ((Algebra.TensorProduct.piRight F F E K).trans
          (AlgEquiv.piCongrRight fun i => Algebra.TensorProduct.comm F E (K i))))

  have : ∀ i, Nontrivial (K i ⊗[F] E) := fun i =>
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right (R := F) (M := K i) (N := E)
      (Algebra.linearMap F (K i)) (algebraMap F (K i)).injective
  rw [φ.toRingEquiv.toMulEquiv.isField_congr]
  exact isField_pi_fin_iff _

end GlobalTheory.RegSS
end

