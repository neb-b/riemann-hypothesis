module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
public import GroundTheory.Brauer.TensorSimple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittaker
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.CutTransfer

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem proj_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (finGL E n (locGL E n w g)) = g := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 := congrArg (fun z => (GeneralLinearGroup.map (pLoc E w) z).val i j) (pFin_finGL (E := E) (locGL E n w g))
  simp only [pLoc_locGL] at h1
  exact h1

theorem gl_ext_pLoc {x y : GL (Fin n) (Af E)}
    (h : ∀ v, GeneralLinearGroup.map (pLoc E v) x = GeneralLinearGroup.map (pLoc E v) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

variable [_root_.NumberField.IsTotallyComplex E]

theorem comm_of_proj_eq_one (w : HeightOneSpectrum (𝓞 E)) {x : GA E n}
    (hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1) (g : GL (Fin n) (w.adicCompletion E)) :
    x * finGL E n (locGL E n w g) = finGL E n (locGL E n w g) * x := by
  have hxw : GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i j) hx
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_finGL, mul_one, one_mul]
  · simp only [map_mul, pFin_finGL]
    refine gl_ext_pLoc fun v => ?_
    simp only [map_mul]
    by_cases hv : v = w
    · subst hv
      rw [hxw, one_mul, mul_one]
    · rw [pLoc_locGL_of_ne hv, one_mul, mul_one]

theorem superDiag_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    GlobalTheory.Whittaker.superDiag (finGL E n (locGL E n w u)) = sFin E (sLoc E w (GlobalTheory.Whittaker.superDiag u)) := by
  unfold GlobalTheory.Whittaker.superDiag
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := by
    intro h
    subst h
    simp at hj
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
      sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = _
  simp [Matrix.one_apply_ne hij]

theorem psiN_finGL_locGL (w : HeightOneSpectrum (𝓞 E)) (u : GL (Fin n) (w.adicCompletion E)) :
    psiN (finGL E n (locGL E n w u)) = psiLoc w (GlobalTheory.Whittaker.superDiag u) := by
  unfold psiN psiLoc
  rw [superDiag_finGL_locGL]

theorem finGL_locGL_mem_NA' (w : HeightOneSpectrum (𝓞 E)) {u : GL (Fin n) (w.adicCompletion E)}
    (hu : u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n)) : finGL E n (locGL E n w u) ∈ NA (E := E) (a := n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j)) = 0
    simp [Matrix.one_apply_ne hij.ne', h1 i j hij]
  · change (1 : Matrix (Fin n) (Fin n) (Ad E)) i i - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i) +
      sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i i - sLoc E w ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i) +
        sLoc E w ((u : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i i)) = 1
    simp [h2 i]

end GlobalTheory.JSW.CutTransfer

namespace GlobalTheory.JSW.CutTransfer

theorem transfer : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w x)) : ℂ)) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  intro E _ _ _ m w ψ hψ K U hU X A hcut
  classical
  obtain ⟨T₀, hT₀⟩ := hcut
  let Φ : GL (Fin (m + 1)) (w.adicCompletion E) →* GA E (m + 1) := (finGL E (m + 1)).comp (locGL E (m + 1) w)
  have hΦ : ∀ g, Φ g = finGL E (m + 1) (locGL E (m + 1) w g) := fun _ => rfl
  refine ⟨T₀.mapDomain Φ, ?_, ?_⟩
  · intro k hk
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hk)
    exact ⟨g, rfl⟩
  · intro W hN hK y hy
    set yw := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y with hyw
    set x := y * (Φ yw)⁻¹ with hxdef
    have hx : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x = 1 := by
      rw [hxdef, map_mul, map_inv, hΦ, proj_finGL_locGL, ← hyw, mul_inv_cancel]
    have hcomm : ∀ g, x * Φ g = Φ g * x := fun g => comm_of_proj_eq_one w hx g
    have hxy : ∀ g, x * Φ (yw * g) = y * Φ g := by
      intro g
      rw [map_mul, hxdef, mul_assoc, ← mul_assoc (Φ yw)⁻¹, inv_mul_cancel, one_mul]
    let f : GL (Fin (m + 1)) (w.adicCompletion E) → ℂ := fun g => W (x * Φ g)
    have hf1 : GlobalTheory.JSW.KirFin.Eqv ψ f := by
      intro u hu g
      show W (x * Φ (u * g)) = ψ (GlobalTheory.Whittaker.superDiag u) * W (x * Φ g)
      rw [map_mul, ← mul_assoc, hcomm u, mul_assoc, hΦ u, hN _ (finGL_locGL_mem_NA' w hu), psiN_finGL_locGL, hψ]
      rfl
    have hf2 : ∀ u ∈ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))), ∀ g, f (g * u) = f g := by
      intro u hu g
      show W (x * Φ (g * u)) = W (x * Φ g)
      rw [map_mul, ← mul_assoc, hΦ u, hK _ (hU u hu)]
    have key := hT₀ f hf1 hf2 yw hy
    have hact : GlobalTheory.JSW.Cut.act (T₀.mapDomain Φ) W y = GlobalTheory.JSW.Cut.act T₀ f yw := by
      unfold GlobalTheory.JSW.Cut.act
      rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      show _ * W (y * Φ k) = _ * W (x * Φ (yw * k))
      rw [hxy]
    rw [hact, key]
    by_cases h : yw ∈ X
    · have h' : y ∈ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
      show W (x * Φ yw) = W y
      rw [hxdef, mul_assoc, inv_mul_cancel, mul_one]
    · have h' : y ∉ {z : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) z ∈ X} := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']

end GlobalTheory.JSW.CutTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMapInjectivity
section
open NumberField IsDedekindDomain GlobalTheory.LKMid GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped TensorProduct

namespace GlobalTheory.HTGroupLocInj
variable {p : ℕ} [Fact p.Prime] (G : HTGroup p)

noncomputable def iotaZ : ℚ_[p] ⊗[ℚ] G.F →ₐ[ℚ_[p]] ℚ_[p] ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem locW_iotaZ (i : Fin G.m) (z : ℚ_[p] ⊗[ℚ] G.F) :
    G.locW i (iotaZ G z) = algebraMap (G.Fw i) (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) (G.liftW i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    change (Algebra.ofId ℚ_[p] (Matrix (Fin G.n) (Fin G.n) (G.Fw i)) a) * (G.rho i (algebraMap G.F G.C y)) =
      algebraMap (G.Fw i) _ (algebraMap ℚ_[p] (G.Fw i) a * G.embW i y)
    rw [G.rho_F, Algebra.ofId_apply, map_mul, ← IsScalarTower.algebraMap_apply]
    congr 1
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem starT_iotaZ (z : ℚ_[p] ⊗[ℚ] G.F) :
    (starT G.star ℚ_[p] (iotaZ G z)).unop = iotaZ G (conjT G.F ℚ_[p] z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp [iotaZ, starT_tmul, G.star_F]
  | add x y hx hy => simp only [map_add (f := _), MulOpposite.unop_add, hx, hy]

theorem inj_Z (z : ℚ_[p] ⊗[ℚ] G.F) (h1 : ∀ i, G.liftW i z = 0) (h2 : ∀ i, G.liftW i (conjT G.F ℚ_[p] z) = 0) :
    z = 0 := by
  have hJ : z ∈ (⊥ : Ideal (ℚ_[p] ⊗[ℚ] G.F)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    obtain ⟨i, hi | hi⟩ := GlobalTheory.MaxIdealTensorPadic.main p G M hM <;> rw [hi, RingHom.mem_ker]
    · exact h1 i
    · exact h2 i
  haveI : IsArtinianRing (ℚ_[p] ⊗[ℚ] G.F) := IsArtinianRing.of_finite ℚ_[p] _
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := ℚ_[p] ⊗[ℚ] G.F)
  have hk0 : z ^ k = 0 := by
    have := Ideal.pow_mem_pow hJ k
    rw [hk] at this
    simpa using this
  haveI := GlobalTheory.padic_tensor_numberField_isReduced p G.F
  exact IsReduced.eq_zero _ ⟨k, hk0⟩

theorem iotaZ_comm (d : ℚ_[p] ⊗[ℚ] G.C) (z : ℚ_[p] ⊗[ℚ] G.F) : Commute d (iotaZ G z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _)]; exact hx.add_right hy
  | tmul a y =>
    induction d using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => exact hx.add_left hy
    | tmul b c =>
      simp only [iotaZ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (b ⊗ₜ c) * (a ⊗ₜ algebraMap G.F G.C y) = (a ⊗ₜ algebraMap G.F G.C y) * (b ⊗ₜ c)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm b a,
        Algebra.commutes]

theorem locW_inj (x : ℚ_[p] ⊗[ℚ] G.C) (h1 : ∀ i, G.locW i x = 0)
    (h2 : ∀ i, G.locW i (starT G.star ℚ_[p] x).unop = 0) : x = 0 := by
  classical
  letI algD : Algebra G.F (ℚ_[p] ⊗[ℚ] G.C) :=
    RingHom.toAlgebra' ((iotaZ G).toRingHom.comp (Algebra.TensorProduct.includeRight.toRingHom)) (by
      intro c d
      show iotaZ G ((1 : ℚ_[p]) ⊗ₜ c) * d = d * iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
      exact (iotaZ_comm G d _).symm.eq)
  letI algZ : Algebra G.F (ℚ_[p] ⊗[ℚ] G.F) := Algebra.TensorProduct.rightAlgebra
  let f : G.C →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).toRingHom with
      commutes' := fun c => by
        show (1 : ℚ_[p]) ⊗ₜ algebraMap G.F G.C c = iotaZ G ((1 : ℚ_[p]) ⊗ₜ c)
        simp [iotaZ] }
  let g : (ℚ_[p] ⊗[ℚ] G.F) →ₐ[G.F] ℚ_[p] ⊗[ℚ] G.C :=
    { (iotaZ G).toRingHom with
      commutes' := fun c => rfl }
  let Φ := Algebra.TensorProduct.lift f g (fun c z => iotaZ_comm G _ _)
  have hΦ1 : ∀ z, Φ ((1 : G.C) ⊗ₜ z) = iotaZ G z := fun z => by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have hΦs : Function.Surjective Φ := by
    intro d
    induction d using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a c =>
      refine ⟨c ⊗ₜ (a ⊗ₜ (1 : G.F)), ?_⟩
      rw [Algebra.TensorProduct.lift_tmul]
      show ((1 : ℚ_[p]) ⊗ₜ c) * iotaZ G (a ⊗ₜ 1) = a ⊗ₜ c
      simp [iotaZ, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
  let ψ : ℚ_[p] ⊗[ℚ] G.C →+* ((i : Fin G.m) → Matrix (Fin G.n) (Fin G.n) (G.Fw i)) ×
      ((i : Fin G.m) → (Matrix (Fin G.n) (Fin G.n) (G.Fw i))ᵐᵒᵖ) :=
    RingHom.prod (RingHom.pi fun i => (G.locW i).toRingHom)
      (RingHom.pi fun i => (RingHom.op (G.locW i).toRingHom).comp (starT G.star ℚ_[p]))
  have hψ : ∀ d, ψ d = 0 ↔ (∀ i, G.locW i d = 0) ∧ ∀ i, G.locW i (starT G.star ℚ_[p] d).unop = 0 := by
    intro d
    simp only [ψ, Prod.ext_iff, funext_iff, RingHom.prod_apply, Pi.ringHom_apply, Prod.fst_zero, Prod.snd_zero,
      Pi.zero_apply, RingHom.comp_apply]
    refine and_congr Iff.rfl (forall_congr' fun i => ?_)
    rw [← MulOpposite.unop_inj]
    rfl
  let J : TwoSidedIdeal (G.C ⊗[G.F] (ℚ_[p] ⊗[ℚ] G.F)) := TwoSidedIdeal.ker (ψ.comp Φ.toRingHom)
  have hJ : J = ⊥ := by
    by_contra hne
    obtain ⟨z, hz0, hz⟩ := GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot J hne
    apply hz0
    rw [TwoSidedIdeal.mem_ker, RingHom.comp_apply] at hz
    change ψ (Φ ((1 : G.C) ⊗ₜ z)) = 0 at hz
    rw [hΦ1, hψ] at hz
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    apply inj_Z G z
    · intro i
      have := hz.1 i
      rw [locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
    · intro i
      have := hz.2 i
      rw [starT_iotaZ, locW_iotaZ] at this
      exact (FaithfulSMul.algebraMap_injective (G.Fw i) _) (this.trans (map_zero _).symm)
  obtain ⟨y, rfl⟩ := hΦs x
  have hy : y ∈ J := by
    rw [TwoSidedIdeal.mem_ker]
    exact (hψ _).2 ⟨h1, h2⟩
  rw [hJ, TwoSidedIdeal.mem_bot] at hy
  rw [hy, map_zero]

end GlobalTheory.HTGroupLocInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditive
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem exp_point_zero {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
    (σ : Type) : expPt G (0 : Fin d → MvPowerSeries σ C) = 0 := by
  funext i
  have h0 : ∀ j, constantCoeff ((0 : Fin d → MvPowerSeries σ C) j) = 0 := fun _ => by simp
  have hs : HasSubst (0 : Fin d → MvPowerSeries σ C) := hasSubst_of_constantCoeff_zero h0
  ext e
  simp only [expPt, Pi.zero_apply]
  rw [coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [coeff_zero_eq_constantCoeff_apply, (isExp_expOf G).1 i]
  · obtain ⟨s, hsm⟩ : ∃ s, m s ≠ 0 := by
      by_contra hc; push_neg at hc; exact hm (Finsupp.ext hc)
    have : (m.prod fun s n => ((0 : Fin d → MvPowerSeries σ C) s) ^ n) = 0 := by
      rw [Finsupp.prod]
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hsm)
      simp [zero_pow hsm]
    rw [this, map_zero, smul_zero]

theorem log_sum_additive_preserves_integrality : AddSt := by
  intro C _ v d G σ _
  have hadd : ∀ w w' : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      (∀ i, constantCoeff (w' i) = 0) →
      expPt G (w + w') = fun i => subst (Sum.elim (expPt G w) (expPt G w')) (G.F i) := by
    intro w w' hw hw'
    set a : Fin d ⊕ Fin d → MvPowerSeries σ C := Sum.elim (expPt G w) (expPt G w') with ha_def
    have ha0 : ∀ s, constantCoeff (a s) = 0 := by
      rintro (b | b)
      · exact cc_expPt G hw b
      · exact cc_expPt G hw' b
    have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
    have hF : HasSubst G.F := hasSubst_of_constantCoeff_zero G.F_const
    set y : Fin d → MvPowerSeries σ C := fun i => subst a (G.F i) with hy_def
    have hy0 : ∀ i, constantCoeff (y i) = 0 := fun i =>
      constantCoeff_subst_eq_zero ha ha0 (G.F_const i)
    have hlg : lgPt G y = w + w' := by
      funext i
      have h1 := subst_comp_subst_apply hF ha (G.lg i)
      have hXl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      have hXr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
        hasSubst_of_constantCoeff_zero (fun b => by simp)
      rw [G.lg_F, subst_add ha, subst_comp_subst_apply hXl ha, subst_comp_subst_apply hXr ha] at h1
      have hl : (fun s : Fin d => subst a (X (Sum.inl s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w := by
        funext s; rw [subst_X ha]; rfl
      have hr : (fun s : Fin d => subst a (X (Sum.inr s) : MvPowerSeries (Fin d ⊕ Fin d) C)) = expPt G w' := by
        funext s; rw [subst_X ha]; rfl
      rw [hl, hr] at h1
      have e1 : subst (expPt G w) (G.lg i) = w i := by
        have := congrFun (lgPt_expPt G hw) i; exact this
      have e2 : subst (expPt G w') (G.lg i) = w' i := by
        have := congrFun (lgPt_expPt G hw') i; exact this
      show subst y (G.lg i) = w i + w' i
      rw [hy_def, ← h1, e1, e2]
    rw [← hlg, expPt_lgPt G hy0]
  refine ⟨⟨fun i => by simp, fun i => ?_⟩, hadd, ?_⟩
  · rw [exp_point_zero G σ]; intro α; simp [IsIntV]
  · intro w w' hw hw'
    refine ⟨fun i => by simp [hw.1 i, hw'.1 i], fun i => ?_⟩
    rw [hadd w w' hw.1 hw'.1]
    refine ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (G.F_int i) ?_ ?_
    · rintro (b | b)
      · exact hw.2 b
      · exact hw'.2 b
    · rintro (b | b)
      · exact cc_expPt G hw.1 b
      · exact cc_expPt G hw'.1 b

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkIffOfRel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem inv_form_of_rel {S : Type*} [Ring S] [Algebra ℚ S] (b b' y : Sˣ) (z : S) (s : ℚ)
    (h : (b' : S) = algebraMap ℚ S s * (y * b * z)) :
    s • (z * ((b'⁻¹ : Sˣ) : S) * y) = ((b⁻¹ : Sˣ) : S) := by
  have h1 : algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S) = 1 := by rw [← h, Units.mul_inv]
  calc s • (z * ((b'⁻¹ : Sˣ) : S) * y)
      = ((b⁻¹ : Sˣ) : S) * ((y⁻¹ : Sˣ) : S) * (algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S)) * y := by
        simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [h1, mul_one, mul_assoc, Units.inv_mul, mul_one]

theorem form_of_rel {p : ℕ} [Fact p.Prime] {G : HTGroup p} (b b' y : G.Cˣ) (s : ℚ)
    (h : (b' : G.C) = algebraMap ℚ G.C s * (y * b * sh G y)) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) :
    (star x ⬝ᵥ ((G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re =
      (s : ℝ) * (star (G.psi v y *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v y *ᵥ x))).re := by
  have hu : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have e : G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C) =
      (s : ℂ) • ((G.psi v y)ᴴ * (G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) * G.psi v y) := by
    rw [← inv_form_of_rel b b' y _ s h, map_rat_smul, map_mul, map_mul, sh, G.psi_star, Matrix.mul_smul,
      ← Rat.cast_smul_eq_qsmul ℂ]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, ← Complex.ofReal_ratCast, Complex.re_ofReal_mul]

theorem mark_iff_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (μ : ℂ),
    P.Rel Q → (P.Mark μ ↔ Q.Mark μ) := by
  rintro p _ G P Q μ ⟨y, s, hs, hβ, hγ⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v y *ᵥ x, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← map_mul, hγ, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ] at hpos
      exact (mul_pos_iff_of_pos_left hs').1 hpos
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x, ?_, ?_⟩
    · have e : P.γ * y⁻¹ = y⁻¹ * Q.γ := by rw [hγ]; group
      rw [Matrix.mulVec_mulVec, ← map_mul, ← Units.val_mul, e, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ, Matrix.mulVec_mulVec x (G.psi v y), ← map_mul, Units.mul_inv, map_one,
        Matrix.one_mulVec]
      exact mul_pos hs' hpos

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedRootRealSignatureOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem eval_eq_zero_of_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (μ : ℂ) (hx : x ≠ 0)
    (hM : M *ᵥ x = μ • x) (q : Polynomial ℂ) (hq : Polynomial.aeval M q = 0) : q.eval μ = 0 := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector hv (p := q)
  have h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q) := by
    exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q
  rw [h2, hq, map_zero, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hx

theorem mark_isRoot_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → P.pol.eval₂ v.embedding μ = 0 := by
  intro p _ G P μ ha hm v hv
  obtain ⟨v₀, hv₀, x, hx, hpos⟩ := hm
  have hvv : v = v₀ := by
    unfold HTGroup.a at ha
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 ha
    have e1 := hw ⟨v, hv⟩
    have e2 := hw ⟨v₀, hv₀⟩
    exact congrArg Subtype.val (e1.trans e2.symm)
  subst hvv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0 := by
    have h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0 := by
      rw [Pair.pol, minpoly.aeval, map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    have e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C) := by
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [e]
    exact h0
  have := eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq
  rwa [Polynomial.eval_map] at this

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRingOfIntegersActionSumEmbeddingsEigenspaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_ringOfIntegers_action_sum_embeddings_eigenspace : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ) (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F), (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  first | (exact @GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (exact GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp) | (intros; apply GlobalTheory.UPel.HT.LieType.trace_eq_sum_finrank_eigSp  <;> assumption)
end

