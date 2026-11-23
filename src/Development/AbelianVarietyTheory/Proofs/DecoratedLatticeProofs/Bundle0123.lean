module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.BoxSlice

open GlobalTheory.MixModel.OrthDec

variable {D : D7} {S A B : HSp D} (d : GlobalTheory.MixModel.OrthDec S A B)

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp only [heisO, GlobalTheory.MixModel.symplOH_zero_right, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem resS_symm_left (T : HSp D) (u : WO A T) :
    (d.resS T).symm (u, 0) = GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA u := by
  rw [resS_symm_apply, GlobalTheory.MixModel.sandwich_apply, Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem isThetaFunO_slice_left {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (v : WO B T) : IsThetaFunO ψ A T fun u => f ((d.resS T).symm (u, v)) := {
  quasi γ u := by
    have e0 : (d.resS T).symm (ratW T A γ, 0) = ratW T S (γ * d.qA) := by
      rw [resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq, ratW_eq, rat_mul]; rfl
    have e : ((ratW T A γ + u, v) : WO A T × WO B T) = (ratW T A γ, (0 : WO B T)) + (u, v) := by simp
    show f ((d.resS T).symm (ratW T A γ + u, v)) = ψ (-(symplOH A T (ratW T A γ) u)) * f ((d.resS T).symm (u, v))
    rw [e, map_add (f := _), e0, hf.quasi, ← e0, d.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
      GlobalTheory.MixModel.symplOH_zero_left, add_zero]
  level := by
    obtain ⟨U, hU, k⟩ := hf.level
    refine ⟨U.comap (GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA),
      hU.preimage (GlobalTheory.MixModel.continuous_sandwich _ _), fun u hu h0 => ?_⟩
    funext w
    have e1 := congrFun (k _ hu (GlobalTheory.MixModel.map_sandwich _ _ _ h0)) ((d.resS T).symm (w, v))
    rw [← resS_symm_left] at e1
    simp only [heisO] at e1 ⊢
    rw [← e1, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero, d.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  cont := hf.cont.comp ((d.continuous_resS_symm T).comp (continuous_id.prodMk continuous_const))
  smooth k L hL h0 w := by
    have e : ∀ t, (d.resS T).symm (w + L t, v) =
        (d.resS T).symm (w, v) + ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L) t := by
      intro t
      rw [AddMonoidHom.comp_apply, ← resS_symm_left, ← map_add (d.resS T).symm, Prod.mk_add_mk, add_zero]
    simp only [e]
    exact hf.smooth k ((GlobalTheory.MixModel.sandwich (1 : Mx D T.rank T.rank) d.pA).comp L)
      ((GlobalTheory.MixModel.continuous_sandwich _ _).comp hL) (fun t => GlobalTheory.MixModel.map_sandwich _ _ _ (h0 t)) _ }

theorem isThetaFunO_slice_right {ψ : AddChar (AF D.host.F) ℂ} {T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (u : WO A T) : IsThetaFunO ψ B T fun v => f ((d.resS T).symm (u, v)) := by
  have h := isThetaFunO_slice_left d.symm hf u
  have e : ∀ v, (d.symm.resS T).symm (v, u) = (d.resS T).symm (u, v) := fun v => by
    rw [resS_symm_apply, resS_symm_apply, add_comm]; rfl
  simp only [e] at h
  exact h

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), (∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → IsThetaFunO ψ S T (o.boxS T fA fB)) ∧ (∀ fA fB, o.boxS T fA fB 0 = fA 0 * fB 0) ∧ (∀ fA fB, (∀ u, heisO ψ S T ((o.resS T).symm (u, 0)) (o.boxS T fA fB) = o.boxS T (heisO ψ A T u fA) fB) ∧ ∀ v, heisO ψ S T ((o.resS T).symm (0, v)) (o.boxS T fA fB) = o.boxS T fA (heisO ψ B T v fB)) ∧ ∀ f, IsThetaFunO ψ S T f → (∀ v, IsThetaFunO ψ A T fun u => f ((o.resS T).symm (u, v))) ∧ ∀ u, IsThetaFunO ψ B T fun v => f ((o.resS T).symm (u, v)) := by
  intro D ψ _ S A B T o
  refine ⟨fun fA fB hA hB => o.isThetaFunO_boxS hA hB, fun fA fB => o.boxS_zero T fA fB,
    fun fA fB => ⟨fun u => ?_, fun v => ?_⟩, fun f hf => ⟨fun v => isThetaFunO_slice_left o hf v,
      fun u => isThetaFunO_slice_right o hf u⟩⟩
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']
  · rw [o.heisO_boxS, AddEquiv.apply_symm_apply, heisO_zero']

end GlobalTheory.BoxSlice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionalInvarianceProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open GlobalTheory.PlaceModel

namespace GlobalTheory.ProdForm

def iterForm {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
  ℓA ∘ₗ LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))

theorem iterForm_boxS {D : D7} {S A B T : HSp D} (o : OrthDec S A B) (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ)
    (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ) (fA : WO A T → ℂ) (fB : WO B T → ℂ) :
    iterForm o ℓA ℓB (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  have h : (LinearMap.pi fun a => ℓB ∘ₗ LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b)))
      (o.boxS T fA fB) = ℓB fB • fA := by
    funext a
    have : (LinearMap.funLeft ℂ ℂ (fun b => (o.resS T).symm (a, b))) (o.boxS T fA fB) = fA a • fB := by
      funext b
      simp [LinearMap.funLeft_apply, OrthDec.boxS]
    simp [this, mul_comm]
  rw [iterForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.ProdForm

namespace GlobalTheory.ProdForm

theorem exists_product_form : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ e, IsSplitIdem D e → ∀ (ℓA : (WO A T → ℂ) →ₗ[ℂ] ℂ) (ℓB : (WO B T → ℂ) →ₗ[ℂ] ℂ), (∀ u : WO A T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ A T f → ℓA (heisO ψ A T u f) = ℓA f) → (∀ u : WO B T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ B T f → ℓB (heisO ψ B T u f) = ℓB f) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ∀ fA fB, IsThetaFunO ψ A T fA → IsThetaFunO ψ B T fB → ℓ (o.boxS T fA fB) = ℓA fA * ℓB fB := by
  intro D ψ hψ S A B T o e hs ℓA ℓB hA hB
  classical
  obtain ⟨he, hec, v, ε, hε, heq⟩ := id hs
  have hs' := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have he' : cA D e * cA D e = cA D e := hs'.1
  have heε' : algebraMap (AF D.host.F) (AE D) ε * cA D e = cA D e := by rw [← heq]; linear_combination he' + hec
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.LatVac.cA_cA, hec]

  have hresA : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).1 i j = (o.resS T u).1 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  have hresB : ∀ u : WO S T, u ∈ half S T (cA D e) → ∀ i j, cA D e * (o.resS T u).2 i j = (o.resS T u).2 i j := by
    intro u hu i j
    have hu' : ∀ i j, cA D e * u i j = u i j := (isHalf_iff S T).2 hu
    simp only [OrthDec.resS_apply, Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, hu']
  set l0 := iterForm o ℓA ℓB with hl0
  let gen : Set (WO S T → ℂ) := {f | ∃ fA fB, IsThetaFunO ψ A T fA ∧ IsThetaFunO ψ B T fB ∧ f = o.boxS T fA fB}
  let P : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ gen

  have hPst : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, heisL S T ψ u p ∈ P := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      refine Submodule.subset_span ⟨_, _, GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfA (o.resS T u).1,
        GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hfB (o.resS T u).2, ?_⟩
      exact o.heisO_boxS ψ T fA fB u
    | zero => rw [map_zero]; exact P.zero_mem
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact P.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact P.smul_mem c ha
  have hl0P : ∀ u ∈ half S T (cA D e), ∀ p ∈ P, l0 (heisL S T ψ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨fA, fB, hfA, hfB, rfl⟩ := hf
      change l0 (heisO ψ S T u (o.boxS T fA fB)) = _
      rw [o.heisO_boxS ψ T fA fB u, hl0, iterForm_boxS, iterForm_boxS, hA _ (hresA u hu) fA hfA,
        hB _ (hresB u hu) fB hfB]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]

  let K : Submodule ℂ (WO S T → ℂ) :=
    Submodule.span ℂ {m | ∃ u ∈ half S T (cA D e), ∃ g ∈ {g | IsThetaFunO ψ S T g}, m = heisL S T ψ u g - g}
  have hsm : ∀ u ∈ half S T (cA D e), ∀ g ∈ {g | IsThetaFunO ψ S T g}, ∃ k : ℕ, 0 < k ∧ heisL S T ψ (k • u) g = g := by
    intro u hu g hg
    obtain ⟨U, hU, h⟩ := (show IsThetaFunO ψ S T g from hg).level
    obtain ⟨k, hk, hkU⟩ := GlobalTheory.SplitScalar.exists_nsmul_mem U hU (infPart_half hε heε' hu)
    exact ⟨k, hk, h _ hkU (infPart_half hε heε' ((half S T (cA D e)).nsmul_mem hu k))⟩
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, hi0⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero (heisL_half S T ψ c2)
      (GlobalTheory.SplitScalar.heisO_zero ψ S T) hsm hmK
    have h1 : l0 (∑ j ∈ s, heisL S T ψ (y j) m) = (s.card : ℂ) * l0 m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc

  let fP : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : (WO S T → ℂ) →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : WO S T → ℂ) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : WO S T → ℂ) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu f hf => ?_, fun fA fB hfA hfB => ?_⟩
  · have huY : u ∈ half S T (cA D e) := (isHalf_iff S T).1 hu
    have hk : heisO ψ S T u f - f ∈ K := Submodule.subset_span ⟨u, huY, f, hf, rfl⟩
    have hz : heisO ψ S T u f - f ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (heisO ψ S T u f - f) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp : o.boxS T fA fB ∈ P := Submodule.subset_span ⟨fA, fB, hfA, hfB, rfl⟩
    have hz : o.boxS T fA fB ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 (o.boxS T fA fB) + 0 = _
    rw [add_zero, hl0, iterForm_boxS]

end GlobalTheory.ProdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaHeisenbergConjugationNegHermitianSpace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

open scoped ContDiff

namespace GlobalTheory.CjNeg

variable {D : D7}

theorem inv_neg_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have hn : ‖ψ a‖ = 1 := hψ.1.2.1 a
  have h1 : ψ a * ψ (-a) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h2 : starRingEnd ℂ (ψ a) * ψ a = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]; simp
  calc starRingEnd ℂ (ψ a) = starRingEnd ℂ (ψ a) * (ψ a * ψ (-a)) := by rw [h1, mul_one]
    _ = ψ (-a) := by rw [← mul_assoc, h2, one_mul]

theorem symplOH_negT (S T : HSp D) (x y : WO S T) :
    symplOH S (GlobalTheory.ChiGrid.negSp T) x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

theorem symplOH_negS (S T : HSp D) (x y : WO S T) :
    symplOH (GlobalTheory.ChiGrid.negSp S) T x y = -symplOH S T x y := by
  simp only [symplOH, symplO, hO, GlobalTheory.ChiGrid.negSp_gram, inv_neg_mat, Matrix.neg_apply, map_neg, neg_mul, mul_neg,
    Finset.sum_neg_distrib]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (cj id f) = cj id (heisO ψ S T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ S (GlobalTheory.ChiGrid.negSp T) w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem heis_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) :
    heisO ψ S T w (cj id f) = cj id (heisO ψ (GlobalTheory.ChiGrid.negSp S) T w f) := by
  funext x
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id_eq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]

theorem contDiff_conj {k : ℕ} {g : (Fin k → ℝ) → ℂ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun t => starRingEnd ℂ (g t) :=
  Complex.conjCLE.contDiff.comp hg

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negT]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negT' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) f) : IsThetaFunO ψ S T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH S (GlobalTheory.ChiGrid.negSp T) (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negT, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negT' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negS {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    rw [hf.quasi, map_mul, conj_psi hψ, symplOH_negS]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger in
theorem theta_negS' {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T f) : IsThetaFunO ψ S T (cj id f) := {
  quasi γ w := by
    show starRingEnd ℂ (f (ratW T S γ + w)) = ψ (-(symplOH S T (ratW T S γ) w)) * starRingEnd ℂ (f w)
    have hq : f (ratW T S γ + w) = ψ (-(symplOH (GlobalTheory.ChiGrid.negSp S) T (ratW T S γ) w)) * f w := hf.quasi γ w
    rw [hq, map_mul, conj_psi hψ, symplOH_negS, neg_neg]
  level := by
    obtain ⟨U, hU, h⟩ := hf.level
    exact ⟨U, hU, fun u hu hu0 => by rw [heis_negS' hψ, h u hu hu0]⟩
  cont := Complex.continuous_conj.comp hf.cont
  smooth k L hL hL0 w := contDiff_conj (hf.smooth k L hL hL0 w) }

theorem cj_id_cj_id {S T : HSp D} (f : WO S T → ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = f :=
  GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj_cj id id (fun _ => rfl) f

theorem theta_heis_neg : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ f : WO S T → ℂ, (IsThetaFunO ψ S (GlobalTheory.ChiGrid.negSp T) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f) ∧ (IsThetaFunO ψ (GlobalTheory.ChiGrid.negSp S) T (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) ↔ IsThetaFunO ψ S T f)) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ S (GlobalTheory.ChiGrid.negSp T) w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) ∧ heisO ψ (GlobalTheory.ChiGrid.negSp S) T w (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (heisO ψ S T w f) := by
  intro D ψ hψ S T
  refine ⟨fun f => ⟨⟨fun h => ?_, theta_negT hψ⟩, ⟨fun h => ?_, theta_negS hψ⟩⟩, fun w f => ⟨heis_negT hψ S T w f, heis_negS hψ S T w f⟩⟩
  · simpa only [cj_id_cj_id] using theta_negT' hψ h
  · simpa only [cj_id_cj_id] using theta_negS' hψ h

end GlobalTheory.CjNeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicEqComponentAtPlaceMulOffPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

section Mix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

theorem mix_mul_decompAt (e : A) (hee : e * e = e) (a b : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (e • b + (1 - e) • 1) = e • (a * b) + (1 - e) • 1 := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, hee, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul]

theorem cT_mix_decompAt (s : A →+* A) (e : A) (hs : s e = e) (a : Matrix n n A) :
    Formalism.UG.cT s (e • a + (1 - e) • (1 : Matrix n n A)) = e • Formalism.UG.cT s a + (1 - e) • 1 := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, map_add, map_mul, map_sub, map_one, hs]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

theorem mix_mem_decompAt (s : A →+* A) (J : Matrix n n A) (e : A) (hee : e * e = e) (hs : s e = e) (g : GL n A)
    (hg : g ∈ Formalism.UG.UJ s J) :
    ∃ g' ∈ Formalism.UG.UJ s J, (g' : Matrix n n A) = e • (g : Matrix n n A) + (1 - e) • 1 := by
  refine ⟨⟨e • (g : Matrix n n A) + (1 - e) • 1, e • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [mix_mul_decompAt e hee, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul]
  · rw [mix_mul_decompAt e hee, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]
  · have hg' : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
    show Formalism.UG.cT s (e • (g : Matrix n n A) + (1 - e) • 1) * J * (e • (g : Matrix n n A) + (1 - e) • 1) = J
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
    rw [cT_mix_decompAt s e hs]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one] at hg' ⊢
    rw [hg', hee, h1, h2, h3, zero_smul, zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]

theorem map_mk_decompAt (I : Ideal A) (g : GL n A) (hg : ∀ i j, ((g : Matrix n n A) - 1) i j ∈ I) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1 := by
  ext i j
  have key : (1 : Matrix n n (A ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix n n A) i j) := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
  rw [key]
  exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using hg i j)

end Mix

theorem sigR_algebraMap_decompAt {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]


set_option maxHeartbeats 1000000 in
theorem decompAt : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v),
    h = hv * h' := by
  intro D S h v
  obtain ⟨ε, α, hε, hv1, hv0⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have hea : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  set e : AE D := algebraMap (AF D.host.F) (AE D) ε with he_def
  have c1 : compAt D v e = 1 := by rw [hc, hv1]; rfl
  have c0 : ∀ w, w ≠ v → compAt D w e = 0 := fun w hw => by rw [hc, hv0 w hw, TensorProduct.zero_tmul]
  have heAt : e ∈ idAt D (· = v) := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ e).2 ⟨h0, fun w hw => c0 w hw⟩
  have hee : e * e = e := (mem_supportedAtPlace_iff_placeIdempotent_mul D v e h0 c1 c0 e).1 heAt
  have heOff : 1 - e ∈ idOff D (· = v) := by
    refine (Submodule.mem_iInf _).2 fun w => ?_
    rcases w with ⟨w, hw⟩
    change w = v at hw
    subst hw
    rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, c1, sub_self]
  have hee' : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have hσ : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' e = e := by
    intro σ'
    exact sigR_algebraMap_decompAt (AF D.host.F) σ' ε
  have hσ' : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' (1 - e) = 1 - e := by
    intro σ'; rw [map_sub, map_one, hσ]
  have hmem : h.1 ∈ Formalism.UG.UJ (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) := h.2
  obtain ⟨g₁, hg₁, hg₁v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) e hee
    (hσ _) h.1 hmem
  obtain ⟨g₂, hg₂, hg₂v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) (1 - e)
    hee' (hσ' _) h.1 hmem
  have hcong : ∀ (I : Ideal (AE D)) (g : GA D S), (∀ i j, (mt S g - 1) i j ∈ I) → g ∈ congGrp S I := by
    intro I g hg
    rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_mk_decompAt I _ hg
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  refine ⟨⟨g₁, hg₁⟩, hcong _ _ ?_, ⟨g₂, hg₂⟩, hcong _ _ ?_, ?_⟩
  · intro i j
    show (g₁.val - 1) i j ∈ _
    have : e • h.1.val + (1 - e) • 1 - 1 = e • (h.1.val - 1) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hg₁v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heAt
  · intro i j
    show (g₂.val - 1) i j ∈ _
    have : (1 - e) • h.1.val + (1 - (1 - e)) • 1 - 1 =
        (1 - e) • (h.1.val - 1) := by
      rw [smul_sub, sub_smul (1 : AE D) (1 - e), one_smul]; abel
    rw [hg₂v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heOff
  · apply Subtype.ext
    apply Units.ext
    show h.1.val = g₁.val * g₂.val
    rw [hg₁v, hg₂v, sub_sub_cancel]
    simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hee, hee', h1, h2, zero_smul, zero_add,
      add_zero]
    rw [add_comm, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.FinPl
end

