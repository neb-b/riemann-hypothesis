module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0884
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasGaussIntegralHermitianQuadraticCharacter
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.GaussMain

section Scalar

variable {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E]
  (c : E →ₐ[F] E) {δ : E} (hE : IsQuad c δ)

def sgnHom : Fˣ →* ℂ where
  toFun := sgn E
  map_one' := by simp only [sgn]; exact if_pos (one_mem _)
  map_mul' s t := _root_.GlobalTheory.KSp.sgn_mul_of_isQuad F E c δ hE s t

theorem sgn_inv (t : Fˣ) : sgn E t⁻¹ = sgn E t := by
  have h := (Units.map (Algebra.norm F : E →* F)).range.inv_mem_iff (x := t)
  unfold sgn
  by_cases ht : t ∈ (Units.map (Algebra.norm F : E →* F)).range
  · rw [if_pos ht, if_pos (h.mpr ht)]
  · rw [if_neg ht, if_neg (mt h.mp ht)]

variable {ν : Type} [Fintype ν] [DecidableEq ν]

theorem det_herm (a : GL ν E) (D : ν → Fˣ) :
    ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det =
      (Matrix.GeneralLinearGroup.det a : E) * c (Matrix.GeneralLinearGroup.det a : E) *
        algebraMap F E ((∏ j, D j : Fˣ) : F) := by
  have hm : ((a : Matrix ν ν E).map c).det = c (a : Matrix ν ν E).det := (RingHom.map_det (c : E →+* E) _).symm
  rw [det_mul, det_mul, det_transpose, det_diagonal, hm]
  simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod, map_prod]
  ring


include hE in
theorem sc_det_inv (χ : Eˣ →* Circle) (m : ℕ) (hχ : ResEtaPow (R := F) ⊥ χ m) (a : GL ν E) (D : ν → Fˣ) :
    sc F χ m ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det a)) : ℝ)⁻¹ ^ m : ℝ) : ℂ) *
        (∏ j, (sgn E (D j) * ((nabs F (D j))⁻¹ : ℝ))) ^ m := by
  obtain ⟨-, hmul, -, -, -, halg, hzc⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE m χ hχ
  set d : Eˣ := Matrix.GeneralLinearGroup.det a with hd
  have hdet : ((a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ).det⁻¹ =
      ((d⁻¹ : Eˣ) : E) * c ((d⁻¹ : Eˣ) : E) * algebraMap F E (((∏ j, D j)⁻¹ : Fˣ) : F) := by
    rw [det_herm c a D]
    simp only [hd, Units.val_inv_eq_inv_val, map_inv₀, mul_inv]
  have e1 : nabs F (Units.map (Algebra.norm F : E →* F) d⁻¹) =
      ((distribHaarChar F (Units.map (Algebra.norm F : E →* F) d)) : ℝ)⁻¹ := by
    simp [nabs, map_inv]
  have e2 : sgn E (∏ j, D j)⁻¹ = ∏ j, sgn E (D j) := by
    rw [sgn_inv]; exact map_prod (sgnHom c hE) D Finset.univ
  have e3 : nabs F (∏ j, D j)⁻¹ = ∏ j, (nabs F (D j))⁻¹ := by
    simp [nabs, map_prod, map_inv]
  rw [hdet, hmul, hzc, halg, e1, e2, e3, Finset.prod_mul_distrib]
  push_cast
  ring

end Scalar

section Equiv

variable {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E]
  {α ν : Type} [Fintype α] [DecidableEq α] [Fintype ν] [DecidableEq ν]

def glT (u : GL α E) : GL α E :=
  ⟨(u : Matrix α α E)ᵀ, ((u⁻¹ : GL α E) : Matrix α α E)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one], by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

def sandwich (U : GL α E) (A : GL ν E) : Matrix α ν E ≃ₜ+ Matrix α ν E where
  toFun x := (U : Matrix α α E) * x * (A : Matrix ν ν E)
  invFun y := ((U⁻¹ : GL α E) : Matrix α α E) * y * ((A⁻¹ : GL ν E) : Matrix ν ν E)
  left_inv x := by
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  right_inv y := by
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  map_add' x y := by simp only [Matrix.mul_add, Matrix.add_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

end Equiv

theorem hasGauss_herm : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ γ₀ : ℂ, ∀ b : Matrix ν ν E, (b.map c)ᵀ = b → b.det ≠ 0 → HasGauss μ (fun x => ψ (2⁻¹ * pr c Q x (x * b))) (γ₀ * sc F χ (Fintype.card α) b.det⁻¹) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ hψ1 hψ0 χ hχc hχ _ _ μ _
  haveI : IsTopologicalRing E := (_root_.GlobalTheory.quadExt_topology F E c δ hE).2.1
  obtain ⟨u, D', hQd⟩ := _root_.GlobalTheory.KSp.exists_gl_diagonal_hermitian F E c δ hE α Q (Matrix.ext fun i j => hQ.1 i j) hQ.2.ne_zero
  obtain ⟨g0, hg0⟩ := _root_.GlobalTheory.KSp.hasGauss_diag_norm F E c δ hE α ν ψ hψ hψ1 hψ0 μ
  let s : α → Fˣ := fun i =>
    Units.mk0 (2⁻¹ * (D' i : F)) (mul_ne_zero (inv_ne_zero two_ne_zero) (D' i).ne_zero)
  let U : GL α E := glT u
  refine ⟨g0 * (((distribHaarChar F (Units.map (Algebra.norm F : E →* F) (Matrix.GeneralLinearGroup.det U)) : ℝ)⁻¹ ^
    Fintype.card ν : ℝ) : ℂ) * (∏ i, (sgn E (s i) * ((nabs F (s i))⁻¹ : ℝ))) ^ Fintype.card ν, ?_⟩
  intro b hb hdet
  obtain ⟨a, D, rfl⟩ := _root_.GlobalTheory.KSp.exists_gl_diagonal_hermitian F E c δ hE ν b hb hdet
  let t : α → ν → Fˣ := fun i j => s i * D j
  have hfun : (fun x : Matrix α ν E => ψ (2⁻¹ * pr c Q x (x * ((a : Matrix ν ν E) *
      diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ)))) =
      fun x => (fun y : Matrix α ν E => ψ (∑ i, ∑ j, (t i j : F) * Algebra.norm F (y i j))) (sandwich U a x) := by
    funext x
    rw [_root_.GlobalTheory.KSp.pr_diag_norm F E c δ hE α ν Q hQ (u : Matrix α α E) (fun i => (D' i : F)) (a : Matrix ν ν E)
      (fun j => (D j : F)) hQd x]
    congr 1
  have key := GlobalTheory.T.hasGaussIntegral_comp_addEquiv_rescale (Matrix α ν E) (Matrix α ν E) μ μ (sandwich U a) _ _ _
    (_root_.GlobalTheory.KSp.map_twoSided_haar F E c δ hE α ν μ U a) (hg0 t)
  rw [hfun]
  convert key using 1
  rw [sc_det_inv c hE χ _ hχ a D]
  have ht : ∀ i j, sgn E (t i j) * (((nabs F (t i j))⁻¹ : ℝ) : ℂ) =
      (sgn E (s i) * (((nabs F (s i))⁻¹ : ℝ) : ℂ)) * (sgn E (D j) * (((nabs F (D j))⁻¹ : ℝ) : ℂ)) := by
    intro i j
    simp only [t]
    rw [_root_.GlobalTheory.KSp.sgn_mul_of_isQuad F E c δ hE, GlobalTheory.SplitWeil.nabs_mul F, mul_inv]
    push_cast
    ring
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ht i j]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Finset.prod_pow]
  push_cast
  ring

end GlobalTheory.KSp.GaussMain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeChoiceClausesOfWeakCharacterisationAtFaceAl
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapBridge

theorem heckeChoiceClauses_of_weakCharacterisation_at_face : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.Hk3.Core R.toRealDat F.lv2 ∧ R.toRealDat.tup_mu_off ∧ R.toRealDat.tup_mu_used := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hC hE
  have h := RealDat3.characterisation_of_weak hC hE
  exact ⟨⟨h.lev, h.grp, h.fam, h.models, h.chain, h.thP⟩, h.tup.mu_off, h.tup.mu_used⟩

end GlobalTheory.OneMapBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.CMSplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem exists_aut_comp {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] (τ₀ τ₁ : E →+* ℂ) :
    ∃ g : E ≃ₐ[ℚ] E, ∀ x, τ₀ (g x) = τ₁ x := by
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E ℂ := IsScalarTower.of_algebraMap_eq fun q => by
    show algebraMap ℚ ℂ q = τ₀ (algebraMap ℚ E q)
    rw [eq_ratCast (algebraMap ℚ ℂ), eq_ratCast (algebraMap ℚ E), map_ratCast]
  exact ⟨(τ₁.toRatAlgHom).restrictNormal' E, fun x => (τ₁.toRatAlgHom).restrictNormal_commutes E x⟩

theorem not_isOfFinOrder_val_of_tame (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (hgal : IsGalois ℚ E) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (χ : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ) (ht : ∀ v, χ.TameAt v) (hinf : χ.HasInf (fun w => (τ w).1) n)
    (hn : ∀ w, n w ≠ 0) (p : ℕ) (hp : p.Prime) (W : HeightOneSpectrum (𝓞 E)) (hN : Ideal.absNorm W.asIdeal = p)
    (hsq : (p : 𝓞 E) ∉ W.asIdeal ^ 2) : ¬ IsOfFinOrder (χ.val W) := by
  intro hfin
  classical
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht W (Formalism.L2.Host.unif W)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val W ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  set τ₀ : E →+* ℂ := (τ w₀).1 with hτ₀
  choose g hg using fun w => exists_aut_comp τ₀ (τ w).1
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 = τ₀ (∏ w, (g w z / g w (σ z)) ^ n w) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : τ₀ (g w (σ z)) = starRingEnd ℂ (τ₀ (g w z)) := by
      rw [hg, hg]
      exact hcm.2.2.2 _ _
    have e' : (τ w).1 z = τ₀ (g w z) := (hg w z).symm
    have h0 : τ₀ (g w z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ w, (g w z / g w (σ z)) ^ n w) ^ a = 1 := by
    apply τ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := W) ha (by rw [h6, map_one])
  have hg0 : ∀ x, g w₀ x = x := fun x => τ₀.injective (hg w₀ x)
  have hres : ∀ w, (∀ f : F, τ₀ (algebraMap F E f) = w.embedding f) → w = w₀ := by
    intro w hw
    have e : w.embedding = w₀.embedding := by
      ext f
      rw [← hw f]
      exact (RingHom.congr_fun (τ w₀).2 f)
    rw [← InfinitePlace.mk_embedding w, e, InfinitePlace.mk_embedding]
  have hc : ∀ w, W.valuation E (g w (σ z)) = 1 := by
    intro w
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 ((g w : E →+* E).comp (σ : E →+* E)) fun e => ?_
    have hw : w = w₀ := hres w fun f => by
      have := RingHom.congr_fun e (algebraMap F E f)
      change g w (σ (algebraMap F E f)) = algebraMap F E f at this
      rw [← this, hg, AlgHom.commutes]
      exact RingHom.congr_fun (τ w).2 f
    subst hw
    obtain ⟨x, hx⟩ := GlobalTheory.AdelicU.exists_cm_conj_ne hcm
    have := RingHom.congr_fun e x
    change g w (σ x) = x at this
    rw [hg0] at this
    exact hx this
  have hgw : ∀ w, w ≠ w₀ → W.valuation E (g w z) = 1 := by
    intro w hw
    refine GlobalTheory.SplitValue.val_map_eq_one hp hN hsq h2 (g w : E →+* E) fun e => hw (hres w fun f => ?_)
    have := RingHom.congr_fun e (algebraMap F E f)
    change g w (algebraMap F E f) = algebraMap F E f at this
    rw [← this, hg]
    exact RingHom.congr_fun (τ w).2 f
  rw [map_prod, Finset.prod_eq_single w₀ (fun w _ h => by rw [map_zpow₀, map_div₀, hgw w h, hc w, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hg0, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn w₀ h
  · omega
  · omega

end GlobalTheory.CMSplitValue

namespace GlobalTheory.CMSplitValue

theorem not_isOfFinOrder_val : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → IsGalois ℚ E → ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Formalism.L2.Host.HChar E) (n : InfinitePlace F → ℤ), H.HasInf (fun w => (τ w).1) n → (∀ w, n w ≠ 0) → ∀ (p : ℕ), p.Prime → ∀ W : HeightOneSpectrum (𝓞 E), Ideal.absNorm W.asIdeal = p → (p : 𝓞 E) ∉ W.asIdeal ^ 2 → ¬ IsOfFinOrder (H.val W) := by
  intro F E _ _ _ _ _ σ hcm hgal τ H n hinf hn p hp W hN hsq hfin
  obtain ⟨N, hN0, hunr⟩ := GlobalTheory.Corev.UnrPow.exists_pow_unrAt E H
  have ht : ∀ v, (H ^ N).TameAt v := fun v x hx _ => hunr v x hx
  have hinf' : (H ^ N).HasInf (fun w => (τ w).1) (fun w => (N : ℤ) * n w) := by
    intro k
    rw [GlobalTheory.SplitValuePow.inf_pow, Units.val_pow_eq_pow_val, hinf k, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  refine not_isOfFinOrder_val_of_tame F E σ hcm hgal τ (H ^ N) _ ht hinf'
    (fun w => mul_ne_zero (by exact_mod_cast hN0.ne') (hn w)) p hp W hN hsq ?_
  rw [GlobalTheory.SplitValuePow.val_pow]
  exact hfin.pow

end GlobalTheory.CMSplitValue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianOneByOneIsScalar
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin

theorem gl_one_conj {R : Type} [CommRing R] (x a : GL (Fin 1) R) : x * a * x⁻¹ = a := by
  have hc : x * a = a * x := by
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, mul_comm]
  rw [hc, mul_inv_cancel_right]

theorem toQr_fst_entry {p : ℕ} [Fact p.Prime] {G : HTGroup p} (P : Pair G) (r : ℕ) (z : Gr G r) (w : P.cent) :
    (((P.toQr r z w).1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 =
      algebraMap ℚ_[p] (Qr p r) ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) := by
  simp only [Pair.toQr, carry, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Subgroup.coe_subtype, Prod.fst_mul, Prod.fst_inv]
  rw [gl_one_conj]
  have e1 : (locC G w).1 = Units.map (algebraMap ℚ ℚ_[p]).toMonoidHom (w : G.Cˣ × ℚˣ).2 := rfl
  have e2 : ((inclG G r) ((locC G) ↑w)).1 =
      GeneralLinearGroup.scalar (Fin 1) (Units.map (algebraMap ℚ_[p] (Qr p r)).toMonoidHom (locC G w).1) := rfl
  rw [e2, e1]
  simp [GeneralLinearGroup.scalar]

theorem sim_norm_le_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (r : ℕ) (z : Gr G r)
    (K : Subgroup (Gr G r)) (g : Gr G r), 0 < r → Subgroup.Commensurable K (KHT p G.m G.n r G.Fw) →
    ∀ w : P.cent, P.toQr r z w ∈ K.map (MulAut.conj g).toMonoidHom →
      ‖(((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])‖ ≤ 1 := by
  intro p _ G P r z K g _ hK w hw
  obtain ⟨m, hm0, hmem⟩ := exists_pow_mem_conj K (KHT p G.m G.n r G.Fw) g _ hK hw
  rw [← map_pow] at hmem
  obtain ⟨k, hk, hkeq⟩ := hmem
  have hk1 : k.1 = (P.toQr r z (w ^ m)).1 := by
    have h := congrArg Prod.fst hkeq
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv] at h
    rw [← h, gl_one_conj]
  have hent := toQr_fst_entry P r z (w ^ m)
  rw [← hk1] at hent
  obtain ⟨M, hM⟩ := (Subgroup.mem_prod.1 hk).1
  have h00 : (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) =
      ((k.1 : GL (Fin 1) (Qr p r)) : Matrix (Fin 1) (Fin 1) (Qr p r)) 0 0 := by
    rw [← hM]; rfl
  have hO : algebraMap (Qr p r) (PadicAlgCl p)
      (((M : Matrix (Fin 1) (Fin 1) _) 0 0 : GlobalTheory.LKLoc.intR p (Q0 p) r) : Qr p r) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p :=
    ((M : Matrix (Fin 1) (Fin 1) (GlobalTheory.LKLoc.intR p (Q0 p) r)) 0 0).2
  rw [h00, hent, ← IsScalarTower.algebraMap_apply, ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff,
    PadicAlgCl.norm_extends] at hO
  have hpow : ((((w ^ m : P.cent) : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p]) = ((((w : G.Cˣ × ℚˣ).2 : ℚ) : ℚ_[p])) ^ m := by
    push_cast; rfl
  rw [hpow, norm_pow] at hO
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hm0.ne').1 hO

end GlobalTheory.StabFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleFrobeniusTwistOrderFixedPointsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (r : ℕ), 0 < r → (∀ g : Gr G r, (⇑(sigG G r))^[r] g = g) ∧ (∀ γ : Gp G, sigG G r (inclG G r γ) = inclG G r γ) ∧ Function.Injective (inclG G r) ∧ ∀ g : Gr G r, sigG G r g = g → g ∈ (inclG G r).range := by
  first | (exact @GlobalTheory.LKMid.SigIter.main) | (exact GlobalTheory.LKMid.SigIter.main) | (intros; apply GlobalTheory.LKMid.SigIter.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTripleTrivializationsDifferByGroupPointStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianTripleTrivializations_differ_by_group_point : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C) (x x' : (R ⊗[ℚ] G.C)ˣ) (t t' : Rˣ), Triv G R β x t → Triv G R β x' t' → ∃ g : UPts G.star R, (g : (R ⊗[ℚ] G.C)ˣ × Rˣ).1 = x' * x⁻¹ := by
  first | (exact @GlobalTheory.LKMid.triv_quot) | (exact GlobalTheory.LKMid.triv_quot) | (intros; apply GlobalTheory.LKMid.triv_quot  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtensionStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_of_frobenius_norm_one_tensor_Qr : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ (B : Type) [CommRing B] [Algebra ℚ_[p] B] [Module.Finite ℚ_[p] B] (a : (B ⊗[ℚ_[p]] Qr p r)ˣ), nrmG (Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom) r a = 1 → ∃ g : (B ⊗[ℚ_[p]] Qr p r)ˣ, a = g⁻¹ * Units.map (Algebra.TensorProduct.map (AlgHom.id ℚ_[p] B) (frobQ p r)).toRingHom.toMonoidHom g := by
  first | (exact @GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (exact GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic) | (intros; apply GlobalTheory.LKMid.hilbert90_frobenius_tensor_unramified_padic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousComponentInRangeEmbedding
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair.GradR

theorem detR_isHomogeneous (P Q R : ℕ) (h : P ≤ R) : (detR P Q R h).IsHomogeneous P := by
  unfold detR
  rw [Matrix.det_apply']
  refine IsHomogeneous.sum _ _ _ fun σ _ => ?_
  have h1 : (∏ i : Fin P, (Matrix.of fun a c : Fin P =>
      (X (Sum.inl a, Sum.inl (Fin.castLE h c)) : Pol P Q R 0)) (σ i) i).IsHomogeneous (∑ _i : Fin P, 1) :=
    IsHomogeneous.prod _ _ _ fun i _ => isHomogeneous_X ℂ _
  have h0 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Pol P Q R 0).IsHomogeneous 0 := by
    have := isHomogeneous_C (Ix P Q × Ix R 0) (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ)
    rwa [map_intCast] at this
  simpa using h0.mul h1

end GlobalTheory.CharPair.GradR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormVanishingCombinationChartIndep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.formVanish_chart_indep : ∀ (Rg : Type) [CommRing Rg] (A₀ T X : Scheme.{0}) (N : LB A₀) (mA mB : ℕ) (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (t : T ⟶ Sp Rg) (c : Fin mA → Fin mB → Γ(T, ⊤)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), F.IsHomogeneous d → ∀ (z : X) (q q' : N.ι), φ z ∈ N.U q → φ z ∈ N.U q' → (MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0 ↔ MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q') F = 0) := by
  intro Rg _ A₀ T X N mA mB a φ p t c d F hF z q q' hq hq'
  have hV : φ z ∈ N.U q ⊓ N.U q' := ⟨hq, hq'⟩
  have hsec : ∀ i, gs φ z (N.U q) ((a i).f q) =
      (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * gs φ z (N.U q') ((a i).f q') := by
    intro i
    rw [← gs_res φ z (inf_le_left : N.U q ⊓ N.U q' ≤ N.U q) hV, (a i).compat q q', gs_mul φ z _ hV,
      gs_unit φ z _ hV, gs_res φ z (inf_le_right : N.U q ⊓ N.U q' ≤ N.U q') hV]
  have hcomb : comb a φ p c z q = fun j => (gm φ z (N.U q ⊓ N.U q') (N.g q q')).val * comb a φ p c z q' j := by
    funext j
    simp only [comb, hsec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hev : ∀ (w : X.presheaf.stalk z) (y : Fin mB → X.presheaf.stalk z),
      MvPolynomial.eval₂Hom (gc (p ≫ t) z) (fun j => w * y j) F = w ^ d * MvPolynomial.eval₂Hom (gc (p ≫ t) z) y F := by
    intro w y
    simp only [MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hd := hF (MvPolynomial.mem_support_iff.mp hm)
    have hs : ∑ i ∈ m.support, m i = d := by
      rw [← hd]; simp [Finsupp.weight_apply, Finsupp.sum]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hs]
    ring
  rw [hcomb, hev]
  exact IsUnit.mul_right_eq_zero ((gm φ z (N.U q ⊓ N.U q') (N.g q q')).isUnit.pow d)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraExtra
section
namespace GlobalTheory.ClosingLemmaThird

theorem main : (let d1 : {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → {κ : Type} → [Fintype κ] → ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) → (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → Prop := @(fun {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) (Φ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) ↦ ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), Φ = ∑ k : Fin m, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ (k : Fin m) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), φ k v ∈ GlobalTheory.WeilM.SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (∀ (k : Fin m), ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) in Filter.cofinite, φ k v = vac v) ∧ ∀ (k : Fin m), φ k v₁ = φ₀); ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {κ : Type} [inst_2 : Fintype κ] {vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ} {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)} {φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ} {Φ Ψ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ}, d1 vac v₁ φ₀ Φ → d1 vac v₁ φ₀ Ψ → d1 vac v₁ φ₀ (Φ + Ψ)) := by
  intro d1 F _ _ κ _ vac v₁ φ₀ Φ Ψ hΦ hΨ
  obtain ⟨m, f, φ, hΦe, h1, h2, h3⟩ := hΦ
  obtain ⟨m', g, ψ, hΨe, g1, g2, g3⟩ := hΨ
  refine ⟨m + m', Fin.append f g, Fin.append φ ψ, ?_, ?_, ?_, ?_⟩
  · rw [hΦe, hΨe, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro k v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h1 i v
    · simpa only [Fin.append_right] using g1 i v
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h2 i
    · simpa only [Fin.append_right] using g2 i
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h3 i
    · simpa only [Fin.append_right] using g3 i

end GlobalTheory.ClosingLemmaThird
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirectionsStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_act_integralChart_eigenDirections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), ∀ a : 𝓞 E, IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧ ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  first | exact @GlobalTheory.ChartAct.isIntHom_actX_and_eigen | exact GlobalTheory.ChartAct.isIntHom_actX_and_eigen | (intros; apply GlobalTheory.ChartAct.isIntHom_actX_and_eigen <;> assumption)
end

