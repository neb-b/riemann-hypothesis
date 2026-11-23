module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndMapRangeField
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.Bundle0001
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1812
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinIndOfBasis
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

open Formalism.IndefR.Bridge

theorem linInd_of_basis {K C X M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup M] [Module C M]
    (φ : K →+* C) (f : X →ₛₗ[φ] M) (b : Module.Basis I K X) (h : LinearIndependent C fun i => f (b i))
    (n : ℕ) (x : Fin n → X) (hx : LinearIndependent K x) : LinearIndependent C fun a => f (x a) := by
  classical
  have h1 : LinearIndependent K fun a => b.repr (x a) :=
    hx.map' b.repr.toLinearMap (LinearMap.ker_eq_bot.2 b.repr.injective)
  have h2 := GlobalTheory.LatBC.linInd_mapRange φ φ.injective h1
  have h3 := h2.map' (Finsupp.linearCombination C fun i => f (b i)) (LinearMap.ker_eq_bot.2 h)
  refine (funext fun a => ?_ : (fun a => f (x a)) = _) ▸ h3
  simp only [Function.comp_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.sum_mapRange_index (by simp)]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← b.linearCombination_repr (x a), Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  simp only [map_smulₛₗ, Finsupp.sum]

theorem exists_avatar {K C X W M I : Type} [Field K] [Field C] [AddCommGroup X] [Module K X] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup M] [Module C M] [Fintype I] (io : C ≃+* ℂ) {σ : K →+* ℂ} {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x)
    (b : Module.Basis I K X) (c0 : X →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (b i))
    (hsp : Submodule.span ℂ (Set.range fun i => c0 (b i)) = ⊤) (Φ : X →ₛₗ[e0] M) (hΦ : LinearIndependent C fun i => Φ (b i)) :
    ∃ θ : W →+ M, (∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w) ∧ (∀ x, θ (c0 x) = Φ x) ∧ Function.Injective θ := by
  classical
  let B : Module.Basis I ℂ W := Module.Basis.mk hli hsp.ge
  have hB : ∀ i, B i = c0 (b i) := fun i => Module.Basis.mk_apply _ _ i
  let θ : W →+ M :=
    { toFun := fun w => ∑ i, io.symm (B.repr w i) • Φ (b i)
      map_zero' := by simp
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib] }
  have hθ : ∀ w, θ w = ∑ i, io.symm (B.repr w i) • Φ (b i) := fun _ => rfl
  have hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w := fun a w => by
    simp [hθ, Finset.smul_sum, mul_smul]
  have hb : ∀ i, θ (c0 (b i)) = Φ (b i) := fun i => by
    rw [← hB, hθ, B.repr_self, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Finsupp.single_apply, hj.symm]
    · simp
  refine ⟨θ, hs, fun x => ?_, (injective_iff_map_eq_zero θ).2 fun w hw => ?_⟩
  · rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smulₛₗ, hs, hb, ← h, RingEquiv.symm_apply_apply]
  · have := Fintype.linearIndependent_iff.1 hΦ _ ((hθ w).symm.trans hw)
    refine B.ext_elem fun i => ?_
    simpa using this i

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {K : Type} [Field K] [NumberField K] [StarRing K] {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G}
  {χ : J →* ℂˣ}

theorem exists_reading (P : ClassPres ι S σ ρ J χ) {C M : Type} [Field C] [AddCommGroup M] [Module C M] (io : C ≃+* ℂ)
    {e0 : K →+* C} (h : ∀ x, io (e0 x) = σ x) (θ : W →+ M) (hs : ∀ (a : ℂ) w, θ (a • w) = io.symm a • θ w)
    (hinj : Function.Injective θ) (Λ : G →* Module.End C M) (hΛ : ∀ γ w, θ (ρ γ w) = Λ (ι γ) (θ w)) :
    ∃ rd : S.Forms →ₛₗ[e0] (G → M),
      (∀ f γ g, rd f (ι γ * g) = rd f g) ∧
      (∀ f (k : J) g, Λ k (rd f (g * k)) = io.symm (χ k : ℂ) • rd f g) ∧
      (∀ (n : ℕ) (f : Fin n → S.Forms), LinearIndependent K f → LinearIndependent C fun a => rd (f a)) ∧
      (∀ (f f' : S.Forms) (A : Finset G), P.ext f' = dcOp A (P.ext f) → (∀ a ∈ A, Λ a = 1) → ∀ g, rd f' g = ∑ s ∈ A, rd f (g * s)) ∧
      ∀ (f : S.Forms) c, rd f (P.y c) = Λ (P.y c)⁻¹ (θ (P.coef ((f : S.Cl → S.V) c))) := by
  let rd : S.Forms →ₛₗ[e0] (G → M) :=
    { toFun := fun f g => Λ g⁻¹ (θ (P.extL f g))
      map_add' := fun f f' => by funext g; simp only [map_add (f := _), Pi.add_apply]
      map_smul' := fun a f => by
        funext g
        simp only [map_smulₛₗ, Pi.smul_apply, hs, ← h, RingEquiv.symm_apply_apply, RingHom.id_apply] }
  have hrd : ∀ f g, rd f g = Λ g⁻¹ (θ (P.ext f g)) := fun _ _ => rfl
  have hm : ∀ a b z, Λ a (Λ b z) = Λ (a * b) z := fun a b z => by rw [map_mul]; rfl
  refine ⟨rd, fun f γ g => ?_, fun f k g => ?_, fun n f hf => ?_, fun f f' A hA h1 g => ?_, fun f c => ?_⟩
  · have := P.extMem_holds f γ g 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    rw [hrd, hrd, this, hΛ, hm]
    congr 2
    group
  · have := P.extMem_holds f 1 g k
    simp only [one_mul, map_one, Module.End.one_apply] at this
    rw [hrd, hrd, this, hs, hm, map_smul]
    congr 3
    group
  · have h1 := linInd_of_basis σ P.extL S.basis P.extBij_holds.1 n f hf
    rw [Fintype.linearIndependent_iff] at h1 ⊢
    intro a ha i
    have h2 := h1 (fun i => io (a i)) (funext fun g => hinj ?_) i
    · simpa using h2
    have h3 := congrArg (fun F => Λ g (F g)) ha
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, hrd, map_sum, map_smul, hm, mul_inv_cancel, map_one, Module.End.one_apply,
      Pi.zero_apply, map_zero] at h3
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, map_sum, hs, RingEquiv.symm_apply_apply, Pi.zero_apply, map_zero]
    exact h3
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hrd, hA, dcOp, map_sum, map_sum]
      refine Finset.sum_congr rfl fun s hs' => ?_
      have e : Λ s⁻¹ = 1 := by
        have := map_mul Λ s⁻¹ s
        rw [h1 s hs', mul_one, inv_mul_cancel, map_one] at this
        exact this.symm
      rw [hrd, mul_inv_rev, map_mul, e, one_mul]
  · rw [hrd, P.ext_rep]

end GlobalTheory.FrameRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInfiniteScaling
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.TorusTheta

variable (F : Type) [Field F] [NumberField F]

theorem infScale_mul' (a b : ℝ) : infScale F a * infScale F b = infScale F (a * b) := by
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ = _
    rw [← map_mul, ← map_mul]
    rfl
  · show (1 : FiniteAdeleRing (𝓞 F) F) * 1 = 1
    exact mul_one 1

theorem infScale_one' : infScale F 1 = 1 := by
  simp only [infScale, map_one]
  rfl

theorem norm_infScale_fst (t : ℝ) (w : InfinitePlace F) : ‖(infScale F t).1 w‖ = |t| := by
  rw [← GroundTheory.Global.normAtPlace_homeomorphMixedSpace, GroundTheory.Global.homeomorphMixedSpace_apply]
  simp only [infScale, RingEquiv.apply_symm_apply]
  exact mixedEmbedding.normAtPlace_real w t

theorem distribHaarChar_infScale (t : ℝ) (ht : 0 < t) (a : (AF F)ˣ) (ha : (a : AF F) = infScale F t) :
    (distribHaarChar (AF F) a : ℝ) = t ^ Module.finrank ℚ F := by
  rw [GlobalTheory.ModuAdele.distribHaarChar_adeleRing, GroundTheory.Global.IdeleGroup.ideleModule_eq]
  have h2 : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((a : AdeleRing (𝓞 F) F)).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha]
    simp [infScale]
  rw [h2, mul_one]
  simp_rw [show (a : AdeleRing (𝓞 F) F) = infScale F t from ha, norm_infScale_fst, abs_of_pos ht]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

theorem lintegral_infScale_pi : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (u : κ → ℝ), (∀ j, 0 < u j) →
    ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (f : (κ → AF F) → ℝ≥0∞), ∫⁻ x, f (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) ∂μ =
      (ENNReal.ofReal (∏ j, u j ^ Module.finrank ℚ F))⁻¹ * ∫⁻ x, f x ∂μ := by
  intro F _ _ κ _ u hu μ hμ f
  letI : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hμ
  let s : (κ → AF F)ˣ :=
    { val := fun j => infScale F (u j)
      inv := fun j => infScale F (u j)⁻¹
      val_inv := funext fun j => by
        show infScale F (u j) * infScale F (u j)⁻¹ = 1
        rw [infScale_mul', mul_inv_cancel₀ (hu j).ne', infScale_one']
      inv_val := funext fun j => by
        show infScale F (u j)⁻¹ * infScale F (u j) = 1
        rw [infScale_mul', inv_mul_cancel₀ (hu j).ne', infScale_one'] }
  have hχ : ((distribHaarChar (κ → AF F) s : ℝ≥0) : ℝ) = ∏ j, u j ^ Module.finrank ℚ F := by
    rw [GlobalTheory.ModuPiLocal.distribHaarChar_pi (fun _ : κ => AF F), NNReal.coe_prod]
    exact Finset.prod_congr rfl fun j _ => distribHaarChar_infScale F (u j) (hu j) _ rfl
  have h1 : μ.map (fun x => s • x) = DomMulAct.mk s⁻¹ • μ := by
    ext A hA
    rw [Measure.map_apply (measurable_const_smul s) hA, Measure.domSMul_apply, Equiv.symm_apply_apply,
      Set.preimage_smul]
  have h2 : μ.map (fun x => s • x) = ((distribHaarChar (κ → AF F) s)⁻¹ : ℝ≥0) • μ := by
    rw [h1, Measure.isAddLeftInvariant_eq_smul (DomMulAct.mk s⁻¹ • μ) μ,
      addHaarScalarFactor_smul_eq_distribHaarChar, map_inv]
  have h3 : ∫⁻ x, f (fun j => infScale F (u j) * x j) ∂μ = ∫⁻ y, f y ∂(μ.map (fun x => s • x)) :=
    (lintegral_map_equiv f (Homeomorph.smul s).toMeasurableEquiv).symm
  rw [h3, h2, ENNReal.smul_def, lintegral_smul_measure, smul_eq_mul, ← hχ, ENNReal.ofReal_coe_nnreal,
    ENNReal.coe_inv (distribHaarChar_pos).ne']

end GlobalTheory.TorusTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLattice
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisDual

open Formalism.HermitianLatticesTheory Formalism.UG Formalism.L2.Forms
open scoped Matrix

theorem natCast_notMem {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {l s : ℕ}
    (hl : l.Prime) (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (hs : ¬ l ∣ s) : (s : 𝓞 K) ∉ w.asIdeal := by
  intro h
  have hcop : Nat.Coprime l s := (hl.coprime_iff_not_dvd).2 hs
  obtain ⟨a, b, e⟩ := (Nat.isCoprime_iff_coprime.2 hcop).map (Int.castRingHom (𝓞 K))
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
  · simpa using hlw
  · simpa using h

theorem isBasisAt_tauLat {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} {n : ℕ}
    (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) {l : ℕ} (hl : l.Prime)
    (hlw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) (M : Submodule (𝓞 E) (Fin n → E)) (B : GL (Fin n) E)
    (hB : IsLocBasis l (M : Set (Fin n → E)) B) : IsBasisAt w (tauLat emb τ M) (bc (emb τ) B) := by
  have h1 : ¬ l ∣ 1 := fun h => hl.one_lt.ne' (Nat.dvd_one.1 h)
  unfold IsBasisAt
  apply le_antisymm
  · rw [← localized_localized w (colLat _)]
    refine localization_mono _ ?_
    unfold tauLat
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s', hs', hint⟩ := (hB x).1 ⟨1, h1, by simpa using hx⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    rw [lc_mem_colLat]
    intro a
    have e : ((s' : 𝓞 K) • fun b => emb τ (x b)) = fun b => emb τ (((s' : E) • x) b) := by
      funext b
      simp [Algebra.smul_def]
    rw [e, Formalism.L2.Col.vl_bc_inv_mulVec, Matrix.mulVec_smul]
    obtain ⟨r, hr⟩ := hint a
    exact du_map_mem_one (emb τ) (Submodule.mem_one.2 ⟨r, by rw [hr]; rfl⟩)
  · rw [← localized_localized w (tauLat emb τ M)]
    refine localization_mono _ ?_
    unfold colLat
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    obtain ⟨s', hs', hmem⟩ := (hB (fun a => (B : Matrix (Fin n) (Fin n) E) a j)).2 ⟨1, h1, fun a => by
      have e : (((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ fun a => (B : Matrix (Fin n) (Fin n) E) a j) a =
          (1 : Matrix (Fin n) (Fin n) E) a j := by
        have h2 : ((B⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) * (B : Matrix (Fin n) (Fin n) E) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [← h2]
        rfl
      rw [e, Matrix.one_apply]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩⟩
    refine ⟨(s' : 𝓞 K), natCast_notMem w hl hlw hs', ?_⟩
    refine Submodule.subset_span ⟨_, hmem, ?_⟩
    funext b
    simp [Algebra.smul_def, bc_coe]

end GlobalTheory.LocBasisDual

namespace GlobalTheory.LocBasisDual

theorem basisAt_dualFr_tauLat : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  intro E K _ _ _ _ ι _ n emb τ w l hl hlw M hM
  have : Fact l.Prime := ⟨hl⟩
  refine ⟨Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis l E M hM.fg (Submodule.IsFullLattice.span_eq_top (self := hM)),
    (Formalism.L2.DIV.dualFr_tauLat_isLattice emb τ M hM).toIsLattice, fun B hB => ?_⟩
  exact pb_isBasisAt_dualFr w _ (tauLatticeLattice_holds E K ι n emb τ M hM).fg _
    (isBasisAt_tauLat emb τ w hl hlw M B hB)

end GlobalTheory.LocBasisDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisIntegralRelativeAdelicPoint
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocBasisInt

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_isIntegral' {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_inc_le_one (inc : E →+* PadicAlgCl l) (r : 𝓞 E) : ‖inc (r : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' ((RingOfIntegers.isIntegral_coe r).map inc.toIntAlgHom)

theorem norm_natCast_eq_one' {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : PadicAlgCl l)‖ = 1 := by
  have h : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact ((Fact.out : l.Prime).coprime_iff_not_dvd).mpr hm

theorem norm_ev_latHat_le_one (inc : E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 F) F ⊗[F] E →+* PadicAlgCl l) (hev : EvOk inc ev) {M : ℕ}
    (L : Set (Fin M → E)) (hL : ∀ x ∈ L, ∀ i, x i ∈ (algebraMap (𝓞 E) E).range)
    (z : Fin M → FiniteAdeleRing (𝓞 F) F ⊗[F] E) (hz : z ∈ StandardLattice.latHat F E L) (a : Fin M) :
    ‖ev (z a)‖ ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    obtain ⟨r, hr⟩ := hL x hx a
    have e : c ⊗ₜ[F] x a = (c ⊗ₜ[F] (1 : E)) * ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x a) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    show ‖ev (c ⊗ₜ[F] x a)‖ ≤ 1
    rw [e, map_mul, norm_mul, hev.1, ← hr]
    exact mul_le_one₀ (hev.2.1 c hc) (norm_nonneg _) (norm_inc_le_one inc r)
  | zero => simp
  | add y w _ _ hy hw =>
    show ‖ev (y a + w a)‖ ≤ 1
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hy hw)
  | neg y _ hy =>
    show ‖ev (-(y a))‖ ≤ 1
    rwa [map_neg, norm_neg]

end General

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem selfDualLattice_frame_span_integral_coordinates (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    (x : Fin V.rank → D.host.E) (hx : x ∈ StandardLattice.L0c D V) (i : Fin V.rank) :
    x i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have hx' : ∑ j, x j • V.frame j ∈ V.L0 := hx
  rw [hL0, Submodule.mem_span_range_iff_exists_fun] at hx'
  obtain ⟨c, hc⟩ := hx'
  have hc' : ∑ j, ((c j : D.host.E)) • V.frame j = ∑ j, x j • V.frame j := by
    rw [← hc]; refine Finset.sum_congr rfl fun j _ => ?_
    exact (algebraMap_smul D.host.E (c j) (V.frame j))
  have h2 := congrArg (fun v => V.frame.repr v i) hc'
  simp only [Module.Basis.repr_sum_self] at h2
  exact ⟨c i, h2⟩

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

section Space

variable {D : D7}

theorem norm_ev_hLat_le_one (V : Formalism.BasicNotions.TH.HSp D) (hL0 : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l)
    (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l) (hev : EvOk inc ev)
    (y : Bridge.Gf V) (x : Fin V.rank → D.host.E) (hx : x ∈ Bridge.hLat V y) (a : Fin V.rank) :
    ‖ev (Matrix.mulVec ((y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E))⁻¹).val
      (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) a)‖ ≤ 1 := by
  unfold Bridge.hLat at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    have hx' := hx
    simp only [Set.mem_ofPred, Subgroup.coe_inv] at hx'
    exact norm_ev_latHat_le_one inc ev hev (StandardLattice.L0c D V) (fun x hx i => selfDualLattice_frame_span_integral_coordinates V hL0 x hx i) _ hx' a
  | zero =>
    simp only [Pi.zero_apply, TensorProduct.tmul_zero]
    rw [show (fun _ : Fin V.rank => (0 : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)) = 0 from rfl]
    simp
  | add x w _ _ hx hw =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (x + w) i) =
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) +
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] w i) := by
      funext i; simp [TensorProduct.tmul_add]
    rw [e, Matrix.mulVec_add, Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hw)
  | smul r x _ hx =>
    have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r • x) i) =
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (r : D.host.E)) •
          (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x i) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
      congr 1
    rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1]
    exact mul_le_one₀ (norm_inc_le_one inc r) (norm_nonneg _) hx

end Space

end GlobalTheory.LocBasisInt

namespace GlobalTheory.LocBasisInt

theorem locBasis_integral : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  intro D V l _ inc ev hev hL0 y B hB a b
  obtain ⟨s, hs, hmem⟩ := (hB (fun k => B.val k b)).2 ⟨1, fun h => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h), fun c => by
    have e : Matrix.mulVec (B⁻¹).val (fun k => B.val k b) c = ((B⁻¹).val * B.val) c b := rfl
    rw [e, Units.inv_mul, Matrix.one_apply]
    split_ifs
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩⟩
  have h := norm_ev_hLat_le_one V hL0 inc ev hev y _ hmem a
  have e : (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (((s : D.host.E) • fun k => B.val k b) i)) =
      ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] (s : D.host.E)) •
        (fun i => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] B.val i b) := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rw [e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul, norm_mul, hev.1, map_natCast,
    norm_natCast_eq_one' hs, one_mul] at h
  rw [← map_inv, Units.val_mul, Matrix.mul_apply]
  refine le_of_eq_of_le (congrArg norm ?_) h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, hev.1]
  rfl

end GlobalTheory.LocBasisInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UsedRunCuspFormReadingMemModelCuspFormsStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn GlobalTheory.ShareOn.Reading
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.usedRunCuspForm_reading_mem_modelCuspForms : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {r : TwoRuns p.T p.P.Gp} (h : RunsOk (fw2 p) r) {i : Fin D.R.m} {C : Type} [MulAction p.P.Gp C] {M : TwoLevels D.host.E D.R.r p.P.Gp C} {ka : Wt M.Ψ D.R.r} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {e : C ≃ ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).Comp} (ha : ∀ c, (M.comp c).toData = ((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)) (hb : ∀ c τ (h1 : τ ∈ M.Ψ) (h2 : τ ∈ (((r.used v).full.U ((i : ℕ) + 1) (r.used v).full.σ₀).X (e c)).Ψ) a, ka ⟨τ, h1⟩ a = laR (r.used v).full.toTop ((i : ℕ) + 1) (p.κ i) (e c) ⟨τ, h2⟩ a) (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)), rdFun h ha F ∈ M.SS ka := by
  first | exact @GlobalTheory.ShareOn.Reading.rdFun_mem_SS | exact GlobalTheory.ShareOn.Reading.rdFun_mem_SS | (intros; apply GlobalTheory.ShareOn.Reading.rdFun_mem_SS <;> assumption)
end

