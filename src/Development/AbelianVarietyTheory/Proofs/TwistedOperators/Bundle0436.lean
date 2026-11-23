module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.InvVolConjLevelOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsFunForm
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulBrStdOfEquivariant
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0276
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEquivEqSmul
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.BrUnique

variable {ι : Type} [Fintype ι] {N n : ℕ}

def uGL (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin n) ℂ := fun τ => GlobalTheory.Branching.unitaryIncl n (u τ)

def diagU (hN : N = n + 1) (u : ι → Matrix.unitaryGroup (Fin n) ℂ) : ι → GL (Fin N) ℂ :=
  fun τ => Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm (GlobalTheory.Branching.unitaryIncl n (u τ))

theorem invTrK_invTrK {K : Type} [Field K] (g : ι → GL (Fin n) K) : invTrK (invTrK g) = g := by
  funext τ
  apply Units.ext
  have hu : IsUnit ((g τ : Matrix (Fin n) (Fin n) K)).det := (Matrix.isUnit_iff_isUnit_det _).1 (g τ).isUnit
  simp [invTrK, inside₂, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hu]

theorem pairBK_rhoK (σ : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) (x y : VV ℂ σ) :
    pairBK σ (rhoK σ g x) (rhoK σ (invTrK g) y) = pairBK σ x y := by
  rw [pairBK_apply, pairBK_apply, rhoK_coe, rhoK_coe]
  have h := pairingBInvariantK_holds ℂ ι n σ (invTrK g) x.1 y.1
  rwa [invTrK_invTrK] at h

theorem unitaryEquiv_eq_smul (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ)) (φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ)
    (hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ), φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v)) :
    ∃ c : ℂ, φ = c • Br.brStd hN Λ σ :=
  _root_.GlobalTheory.BranchMultOne.eq_smul_brStd_of_equivariant hN hn Λ σ hI hS φ (GlobalTheory.T.equivariant_GL_of_equivariant_unitary_coefficientSpace hN Λ σ φ hφ)

theorem brPair_unique (hN : N = n + 1) (hn : 1 ≤ n) {Λ : ι → DomWeight N} {σ : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (Λ τ) (σ τ)) (hS : ∀ τ, Br.SameShift (Λ τ) (σ τ))
    (B : VV ℂ Λ →ₗ[ℂ] (VV ℂ fun τ => (σ τ).dual) →ₗ[ℂ] ℂ)
    (hB : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ) (f : VV ℂ fun τ => (σ τ).dual),
      B (rhoK Λ (diagU hN u) v) (rhoK (fun τ => (σ τ).dual) (uGL u) f) = B v f) :
    ∃ c : ℂ, B = c • GlobalTheory.FunObj.brPair σ hN Λ := by
  haveI : FiniteDimensional ℂ (VV ℂ σ) := Module.Finite.of_basis (bVV ℂ σ)
  have hnd := pairingBNondegenerate_holds ℂ ι n σ
  let φ : VV ℂ Λ →ₗ[ℂ] VV ℂ σ :=
    (LinearMap.BilinForm.toDual (pairBK σ) hnd).symm.toLinearMap ∘ₗ B.compl₂ (GlobalTheory.FunObj.funEquiv σ).toLinearMap
  have hp : ∀ v y, pairBK σ (φ v) y = B v (GlobalTheory.FunObj.funEquiv σ y) := fun v y => by
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.BilinForm.apply_toDual_symm_apply,
      LinearMap.compl₂_apply]
  have hinv : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) v F,
      B (rhoK Λ (diagU hN u) v) F = B v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F) := fun u v F => by
    have h := hB u v (rhoK (fun τ => (σ τ).dual) (uGL u)⁻¹ F)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
  have hφ : ∀ (u : ι → Matrix.unitaryGroup (Fin n) ℂ) (v : VV ℂ Λ),
      φ (rhoK Λ (diagU hN u) v) = rhoK σ (uGL u) (φ v) := fun u v => by
    refine sub_eq_zero.1 (hnd.1 _ fun y => ?_)
    rw [map_sub, LinearMap.sub_apply, sub_eq_zero, hp, hinv]
    obtain ⟨y', rfl⟩ : ∃ y', y = rhoK σ (invTrK (uGL u)) y' :=
      ⟨rhoK σ (invTrK (uGL u))⁻¹ y, by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]⟩
    rw [pairBK_rhoK, hp, GlobalTheory.FunObj.funEquiv_rhoK, ← Module.End.mul_apply, ← map_mul, invTrK_invTrK, inv_mul_cancel,
      map_one, Module.End.one_apply]
  obtain ⟨c, hc⟩ := unitaryEquiv_eq_smul hN hn hI hS φ hφ
  refine ⟨c, LinearMap.ext₂ fun v f => ?_⟩
  have e : f = GlobalTheory.FunObj.funEquiv σ (GlobalTheory.FunObj.covOf σ f) := by rw [GlobalTheory.BrRat.covOf_eq, LinearEquiv.apply_symm_apply]
  rw [e, ← hp, hc, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, LinearMap.smul_apply,
    ← e]
  simp only [GlobalTheory.FunObj.brPair, LinearMap.compl₁₂_apply]

end GlobalTheory.BrUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecMulEntry
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section
namespace GlobalTheory.FrameScale

theorem vecMul_entry {E k ι : Type} [Field E] [Field k] [Fintype ι] {n c : ℕ} (φ : E →+* k) (σ : E →+* E)
    (a : Matrix (Fin n) (Fin c) E) (g : Matrix (Fin n) (Fin n) E) (b : Matrix (Fin n) ι k) (x : k) (q r : Fin c) (m : ι)
    (hb : ∀ i, b i m = x * φ (a i r)) :
    ((fun i => φ (σ (a i q))) ᵥ* (g.map φ * b)) m = x * φ ((Formalism.UG.cT σ a * g * a) q r) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, hb, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring

end GlobalTheory.FrameScale
end

theorem GlobalTheory.FrameScale.clauses : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h' : 2 * σ + 2 ≤ D.R.m)
  (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (β : GlobalTheory.FinPl.Frame p (G.V (.grid (2 * σ + 2) 0)) (Fin (G.V (.grid (2 * σ + 2) 0)).rank))
  (j : Fin (2 * σ + 2 - 1) → Fin (G.V (.grid (2 * σ + 2) 0)).rank) (ϖ : k) (e : ℕ), ϖ ≠ 0 → Function.Injective j →
  (∀ r i, β.b i (j r) = ϖ ^ (e * (r.1 + 1)) * p.pr (incA D ((G.colDec (2 * σ + 2) (by omega) h').a i r))) →
  (∀ m, m ∉ Set.range j → ∀ r, ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i r)))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) m = 0) →
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (q.1 + 1)) * (p.pr (incA D (-D.host.xi0)))⁻¹ ^ (q.1 + 1)) •
      (β.b' *ᵥ fun i => p.pr (xFB F σ h' i q)) = Pi.single (j ⟨q.1, by omega⟩) 1) ∧
  (∀ q : Fin (σ + 1), (ϖ ^ (e * (2 * σ + 1 - q.1)) * p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) *
      (if q.1 = σ then -1 else 1))⁻¹ • ((fun i => p.pr (cA D (xFB F σ h' i q))) ᵥ* (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
      Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1) := by
  intro D _ T L _ _ sc G W _ _ F hF σ h' k _ _ _ _ p β j ϖ e hϖ hj hb hout
  have hne : (-D.host.xi0) ≠ 0 := neg_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hc : p.pr (incA D (-D.host.xi0)) ≠ 0 := ((hne.isUnit.map (incA D)).map p.pr).ne_zero
  have hc' : p.pr (incA D (star (-D.host.xi0))) ≠ 0 :=
    (((star_ne_zero.2 hne).isUnit.map (incA D)).map p.pr).ne_zero
  have hcol : ∀ (q : Fin (σ + 1)) i, xFB F σ h' i q = incA D ((-D.host.xi0) ^ (q.1 + 1)) * incA D ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩) := by
    intro q i
    have := congrFun (GlobalTheory.CharXFB.xFB_col F hF σ h' q) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [this]
    rfl
  have key : ∀ m, β.b' *ᵥ (fun i => β.b i m) = Pi.single m 1 := by
    intro m
    have : (fun i => β.b i m) = β.b *ᵥ Pi.single m 1 := by
      funext i; simp [Matrix.mulVec_single]
    rw [this, Matrix.mulVec_mulVec, β.b'b, Matrix.one_mulVec]
  refine ⟨fun q => ?_, fun q => ?_⟩
  · have hv : (fun i => p.pr (xFB F σ h' i q)) =
        (p.pr (incA D (-D.host.xi0)) ^ (q.1 + 1) * (ϖ ^ (e * (q.1 + 1)))⁻¹) • fun i => β.b i (j ⟨q.1, by omega⟩) := by
      funext i
      rw [hcol]
      simp only [map_mul, map_pow, Pi.smul_apply, smul_eq_mul, hb]
      field_simp
    rw [hv, Matrix.mulVec_smul, key, smul_smul]
    convert one_smul k _
    rw [inv_pow]
    field_simp
  · have hv : (fun i => p.pr (cA D (xFB F σ h' i q))) = p.pr (incA D (star (-D.host.xi0))) ^ (q.1 + 1) •
        fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩))) := by
      funext i
      rw [hcol]
      simp only [map_mul, GlobalTheory.DualPairCheck.cA_incA, star_pow, map_pow, Pi.smul_apply, smul_eq_mul]
    have hsm : ∀ (x : k) (u : Fin (G.V (.grid (2 * σ + 2) 0)).rank → k)
        (M : Matrix (Fin (G.V (.grid (2 * σ + 2) 0)).rank) (Fin (G.V (.grid (2 * σ + 2) 0)).rank) k),
        (x • u) ᵥ* M = x • (u ᵥ* M) := by
      intro x u M
      funext m
      simp only [Matrix.vecMul, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
    have hg := (G.colDec (2 * σ + 2) (by omega) h').gram
    have hw : ((fun i => p.pr (incA D (star ((G.colDec (2 * σ + 2) (by omega) h').a i ⟨q.1, by omega⟩)))) ᵥ*
        (((G.V (.grid (2 * σ + 2) 0)).gram.map (fun c => p.pr (incA D c))) * β.b)) =
        (ϖ ^ (e * (2 * σ + 1 - q.1)) * (if q.1 = σ then -1 else 1)) • Pi.single (j ⟨2 * σ - q.1, by omega⟩) 1 := by
      funext m
      by_cases hm : m ∈ Set.range j
      · obtain ⟨r, rfl⟩ := hm
        refine (GlobalTheory.FrameScale.vecMul_entry (p.pr.comp (incA D)) (D.sp.cm.sig : D.host.E →+* D.host.E)
          (G.colDec (2 * σ + 2) (by omega) h').a _ β.b _ ⟨q.1, by omega⟩ r (j r) (hb r)).trans ?_
        rw [hg]
        simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.ChiGrid.antiDiagonalSignGramMatrix, RingHom.coe_comp, Function.comp_apply]
        by_cases hr : r = ⟨2 * σ - q.1, by omega⟩
        · subst hr
          have e1 : 2 * σ - q.1 + 1 = 2 * σ + 1 - q.1 := by omega
          rw [Pi.single_eq_same, if_pos (by simp only; omega), e1]
          by_cases hq : q.1 = σ
          · rw [if_pos (Fin.ext (by simp only; omega)), if_pos hq]
            simp
          · rw [if_neg (fun h => hq (by have := congrArg Fin.val h; simp only at this; omega)), if_neg hq]
            simp
        · rw [Pi.single_eq_of_ne (hj.ne hr), if_neg (fun h => hr (Fin.ext (by simp only; omega)))]
          simp
      · rw [hout m hm ⟨q.1, by omega⟩, Pi.smul_apply, Pi.single_eq_of_ne (fun h => hm ⟨_, h.symm⟩), smul_zero]
    have hs : (if q.1 = σ then (-1 : k) else 1) ≠ 0 := by split_ifs <;> norm_num
    rw [hv, hsm, hw, smul_smul, smul_smul]
    refine (congrArg (· • Pi.single (j ⟨2 * σ - q.1, by omega⟩) (1 : k)) ?_).trans (one_smul k _)
    field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepSchrodingerModelHalfSubstitution
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchrodSubst

open GlobalTheory.PlaceModel GlobalTheory.PlaceDatum

variable {D : D7} {S T : HSp D}

private lemma isSBHalf_psi_mul_halfInd {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    {y : WO S T} (hy : y ∈ half S T (cA D e)) {m : ℕ} (hm : 0 < m) (hmy : m • y ∈ Λ) :
    IsSBHalf e Λ (fun t => ψ (symplO S T t y) * halfInd e Λ t) := by
  have h0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  unfold IsSBHalf at h0 ⊢
  obtain ⟨hsupp, k, hk, hinv, hlat⟩ := h0
  have hχ : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b y
      rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
    · intro a b y
      rw [GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]
    · intro y
      rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
    · intro y
      rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
  refine ⟨fun t ht => hsupp t (right_ne_zero_of_mul ht), m * k, Nat.mul_pos hm hk, ?_, ?_⟩
  · intro u hu hue t
    have huh : u ∈ half S T e := (GlobalTheory.PlaceModel.isHalf_iff S T).1 hue
    have hmu : IsHalf e (m • u) := (GlobalTheory.PlaceModel.isHalf_iff S T).2 ((half S T e).nsmul_mem huh m)
    have hI : halfInd e Λ (t + (m * k) • u) = halfInd e Λ t := by
      rw [mul_comm, ← smul_smul]
      exact hinv (m • u) (Λ.nsmul_mem hu m) hmu t
    have hone : ψ (symplO S T ((m * k) • u) y) = 1 := by
      have hs := hχ.nsmul m (k • u) y
      rw [← smul_smul, hs]
      exact hLL' (k • u) ⟨Λ.nsmul_mem hu k, (half S T e).nsmul_mem huh k⟩ (m • y)
        ⟨hmy, (half S T (cA D e)).nsmul_mem hy m⟩
    have hsplit := hχ.left t ((m * k) • u) y
    beta_reduce
    rw [hI, hsplit, hone, mul_one]
  · intro t ht
    rw [← smul_smul]
    exact Λ.nsmul_mem (hlat t (right_ne_zero_of_mul ht)) m

theorem placeModel_wave {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {Λ : AddSubgroup (WO S T)}
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hden : ∀ y ∈ half S T (cA D e), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    {f₀ : WO S T → ℂ} {T₁ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (h₁ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ T₁) {x y : WO S T} (hx : IsHalf e x)
    (hy' : IsHalf (cA D e) y) :
    T₁ (wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y) =
      heisO ψ S T x (heisO ψ S T y f₀) := by
  obtain ⟨m, hm, hmy⟩ := hden y ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy')
  have hΦ0 : IsSBHalf e Λ (halfInd e Λ) := GlobalTheory.isSBHalf_halfInd e Λ
  have hΨ := isSBHalf_psi_mul_halfInd hLL' ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy') hm hmy
  have hwave : wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y =
      fun t => ψ (symplO S T (t + x) y) * halfInd e Λ (t + x) := by
    funext t
    simp only [GlobalTheory.PlaceModel.wave, GlobalTheory.PlaceModel.halfInd_eq_ind]
  have hvac : T₁ (halfInd e Λ) = f₀ := by simpa using h₁.vac
  rw [hwave, h₁.trans _ hΨ x hx, h₁.modul _ hΦ0 y hy', hvac]

theorem wave_actO (ψ : AddChar (AF D.host.F) ℂ) (e : AE D) {Λ : AddSubgroup (WO S T)} {g : GA D S} {h : GA D T}
    (hΛ : ∀ u, u ∈ Λ ↔ actO S T g h u ∈ Λ) (x y : WO S T) :
    (fun t => wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) x y (actO S T g⁻¹ h⁻¹ t)) =
      wave (fun x y : WO S T => ψ (symplO S T x y)) (Λ ⊓ half S T e) (actO S T g h x) (actO S T g h y) := by
  funext t
  have ht : actO S T g h (actO S T g⁻¹ h⁻¹ t) = t := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO g⁻¹ h⁻¹ t
  have hadd : t + actO S T g h x = actO S T g h (actO S T g⁻¹ h⁻¹ t + x) := by
    have := map_add (GlobalTheory.SplitHecke.actAdd S T g h) (actO S T g⁻¹ h⁻¹ t) x
    change actO S T g h (actO S T g⁻¹ h⁻¹ t + x) = actO S T g h (actO S T g⁻¹ h⁻¹ t) + actO S T g h x at this
    rw [this, ht]
  have hhalf : ∀ w : WO S T, actO S T g h w ∈ half S T e ↔ w ∈ half S T e := by
    intro w
    simp only [← GlobalTheory.PlaceModel.isHalf_iff]
    constructor
    · intro hw
      simpa [GlobalTheory.SplitHecke.actO_inv_actO] using GlobalTheory.SplitHecke.isHalf_actO g⁻¹ h⁻¹ hw
    · exact GlobalTheory.SplitHecke.isHalf_actO g h
  have hmem : ∀ w : WO S T, actO S T g h w ∈ Λ ⊓ half S T e ↔ w ∈ Λ ⊓ half S T e := by
    intro w
    simp only [AddSubgroup.mem_inf, hhalf, ← hΛ w]
  simp only [GlobalTheory.PlaceModel.wave]
  rw [hadd, GlobalTheory.SplitHecke.symplO_actO]
  simp only [GlobalTheory.PlaceModel.ind]
  by_cases hw : actO S T g⁻¹ h⁻¹ t + x ∈ Λ ⊓ half S T e
  · rw [if_pos hw, if_pos ((hmem _).2 hw)]
  · rw [if_neg hw, if_neg (fun hw' => hw ((hmem _).1 hw'))]

theorem om_placeModel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (a : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsSelfDualC S ΛS → IsSelfDualC T ΛT → a * a = a → infPart D a = 0 → IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) a (latO S T ΛS ΛT fun _ => True) 1 f₀ Tm → ∀ (g : GA D S) (h : GA D T) (c : ℂ), (∀ u, u ∈ (latO S T ΛS ΛT fun _ => True) ↔ actO S T g h u ∈ (latO S T ΛS ΛT fun _ => True)) → om (g, h) f₀ = c • f₀ → ∀ Φ, IsSBHalf a (latO S T ΛS ΛT fun _ => True) Φ → om (g, h) (Tm Φ) = c • Tm fun x => Φ (actO S T g⁻¹ h⁻¹ x) := by
  intro D ψ S T χS χT om ΛS ΛT a f₀ Tm hW hS hT ha hinf hth hTm g h c hΛ hc Φ hΦ
  have hstd : IsStdChar D ψ (-1) := hW.std
  have hψ : IsCharAF D.host.F ψ := by
    unfold IsStdChar at hstd
    exact hstd.1
  have hdual := (_root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hstd hS hT).1
  have hsm : ∀ w : AE D, w * w = w → ∀ u ∈ (latO S T ΛS ΛT fun _ => True),
      w • u ∈ (latO S T ΛS ΛT fun _ => True) := by
    intro w hw u hu
    refine GlobalTheory.LatticeStable.smul_mem_latO D S T ΛS ΛT (fun _ => True) w ?_ u hu
    exact GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, hw])
  have hfm := GlobalTheory.LatFinMod.latO_finite_mod D S T ΛS ΛT hS.1.fg hT.1.fg (fun _ => True)
  have hnm : ∀ t : WO S T, t.map (infPart D) = 0 → ∃ k : ℕ, 0 < k ∧ k • t ∈ (latO S T ΛS ΛT fun _ => True) :=
    fun t ht => GlobalTheory.PlaceDatum.exists_nsmul_mem_latO'
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT) t ht
  generalize (latO S T ΛS ΛT fun _ => True) = Λ at hdual hsm hfm hnm hTm hΛ hΦ ⊢
  have hcA : cA D a * cA D a = cA D a := by rw [← map_mul, ha]
  have hinf' : infPart D (cA D a) = 0 := GlobalTheory.PlaceDatum.infPart_cA hinf
  have hLL : ∀ u ∈ Λ ⊓ half S T a, ∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T u y) = 1 := by
    intro u hu y hy
    rw [AddSubgroup.mem_inf] at hu hy
    exact (hdual u (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2))).1 hu.1 y hy.1
  have hden : ∀ y ∈ half S T (cA D a), ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ := fun y hy =>
    hnm y (GlobalTheory.PlaceDatum.infPart_of_half hinf' ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hy))
  have hXd : ∀ x ∈ half S T a, (∀ y ∈ Λ ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) →
      x ∈ Λ ⊓ half S T a := by
    intro x hx hxy
    refine AddSubgroup.mem_inf.2 ⟨?_, hx⟩
    refine (hdual x (GlobalTheory.PlaceDatum.infPart_of_half hinf ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hx))).2 ?_
    intro u' hu'
    have hmem : cA D a • u' ∈ Λ ⊓ half S T (cA D a) := by
      refine AddSubgroup.mem_inf.2 ⟨hsm _ hcA u' hu', ?_⟩
      rw [GlobalTheory.PlaceModel.mem_half, smul_smul, hcA]
    have heq : symplO S T x u' = symplO S T x (cA D a • u') := by
      rw [← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 hx]
    rw [heq]
    exact hxy _ hmem
  have hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T a, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T a, t = r + k • u := by
    intro k hk
    obtain ⟨R, hR, hRt⟩ := hfm k hk
    refine ⟨(fun r => a • r) '' R, hR.image _, ?_⟩
    intro t ht
    rw [AddSubgroup.mem_inf] at ht
    obtain ⟨r, hr, u, hu, rfl⟩ := hRt t ht.1
    refine ⟨a • r, Set.mem_image_of_mem _ hr, a • u, AddSubgroup.mem_inf.2 ⟨hsm a ha u hu, ?_⟩, ?_⟩
    · rw [GlobalTheory.PlaceModel.mem_half, smul_smul, ha]
    · have h2 := (GlobalTheory.PlaceModel.mem_half S T).1 ht.2
      rw [smul_add, smul_comm a k u] at h2
      exact h2.symm
  have htf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk =>
    Function.LeftInverse.injective (g := fun t : WO S T => incA D (k : D.host.E)⁻¹ • t)
      (fun t => GlobalTheory.PlaceModel.inv_smul_nsmul S T hk t)
  have hspan : Φ ∈ GlobalTheory.PlaceModel.waveSpan (fun x y : WO S T => ψ (symplO S T x y)) (half S T a)
      (half S T (cA D a)) (Λ ⊓ half S T a) := by
    unfold IsSBHalf at hΦ
    obtain ⟨hsupp, k, hk, hinv, hlat⟩ := hΦ
    have hχ : IsBichar (fun x y : WO S T => ψ (symplO S T x y)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x x' y
        rw [GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul]
      · intro x y y'
        rw [GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul]
      · intro y
        rw [GlobalTheory.PlaceModel.symplO_zero_left, AddChar.map_zero_eq_one]
      · intro y
        rw [GlobalTheory.PlaceModel.symplO_zero_right, AddChar.map_zero_eq_one]
    refine GlobalTheory.PlaceDatum.mem_waveSpan (L' := Λ ⊓ half S T (cA D a)) hχ
      inf_le_right inf_le_right hLL hXd (fun k hk x hx => GlobalTheory.PlaceModel.half_div S T a k hk x hx)
      (fun k hk y hy => GlobalTheory.PlaceModel.half_div S T (cA D a) k hk y hy) htf hfin Φ
      (fun t ht => (GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k hk ?_ ?_
    · intro u hu t
      rw [AddSubgroup.mem_inf] at hu
      exact hinv u hu.1 ((GlobalTheory.PlaceModel.isHalf_iff S T).2 hu.2) t
    · intro t ht
      exact AddSubgroup.mem_inf.2 ⟨hlat t ht,
        (half S T a).nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 (hsupp t ht)) k⟩
  clear hΦ
  unfold GlobalTheory.PlaceModel.waveSpan at hspan
  induction hspan using Submodule.span_induction with
  | mem Ψ hΨ =>
    obtain ⟨x, hx, y, hy, rfl⟩ := hΨ
    have hxH : IsHalf a x := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hx
    have hyH : IsHalf (cA D a) y := (GlobalTheory.PlaceModel.isHalf_iff S T).2 hy
    have hthy : IsThetaFunO ψ S T (heisO ψ S T y f₀) :=
      by
        simpa using GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ f₀ hth
          Unit {()} (fun _ => y) (fun _ => 1)
          (fun _ _ => GlobalTheory.PlaceDatum.infPart_of_half hinf' hyH)
    rw [placeModel_wave hLL hden hTm hxH hyH, hW.om_heis g h x _ hthy, hW.om_heis g h y f₀ hth, hc,
      GlobalTheory.SplitScalar.heisO_smul, GlobalTheory.SplitScalar.heisO_smul, wave_actO ψ a hΛ x y,
      placeModel_wave hLL hden hTm (GlobalTheory.SplitHecke.isHalf_actO g h hxH) (GlobalTheory.SplitHecke.isHalf_actO g h hyH)]
  | zero =>
    rw [show (fun x => (0 : WO S T → ℂ) (actO S T g⁻¹ h⁻¹ x)) = 0 from rfl]
    simp only [map_zero, smul_zero]
  | add Ψ₁ Ψ₂ _ _ ih₁ ih₂ =>
    rw [show (fun x => (Ψ₁ + Ψ₂) (actO S T g⁻¹ h⁻¹ x)) =
      (fun x => Ψ₁ (actO S T g⁻¹ h⁻¹ x)) + (fun x => Ψ₂ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_add (f := _), ih₁, ih₂, smul_add]
  | smul r Ψ _ ih =>
    rw [show (fun x => (r • Ψ) (actO S T g⁻¹ h⁻¹ x)) = r • (fun x => Ψ (actO S T g⁻¹ h⁻¹ x)) from rfl]
    simp only [map_smul, ih]
    exact smul_comm r c _

end GlobalTheory.SchrodSubst

end
end

