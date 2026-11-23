module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAlgebraMapEqOfValVLeOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModuliPointIntegralFrameAfterFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0369
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompHS

open NumberField IsDedekindDomain TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.AllWt GlobalTheory.FlagTan
open scoped ENNReal Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Tri

variable {K S : Type} [Field K] [Algebra c.F K] [CommRing S] [Algebra c.F S]

def Reframes (φ : K →ₐ[c.F] S) (y : FrPt Xo c K) (t : Ix Dw → Sˣ) (z : FrPt Xo c S) : Prop :=
  ∃ w, FrMap φ y w ∧ FrBor t w z

theorem Reframes.evR_eq [IsLocalRing S] {φ : K →ₐ[c.F] S} {y : FrPt Xo c K} {t : Ix Dw → Sˣ} {z : FrPt Xo c S}
    (h : Reframes φ y t z) {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) :
    evR Xo c f z = ((∏ i, t i ^ e i : Sˣ) : S) * φ (evR Xo c f y) := by
  obtain ⟨w, h₁, h₂⟩ := h
  rw [evR_frBor hf h₂, evR_frMap hf.1 h₁]

theorem Reframes.liesOn {φ : K →ₐ[c.F] S} {y : FrPt Xo c K} {t : Ix Dw → Sˣ} {z : FrPt Xo c S}
    (h : Reframes φ y t z) {Z : Comp Xo c} (hy : LiesOn Z y) : LiesOn Z z := fun s => by
  obtain ⟨w, h₁, h₂⟩ := h
  have e : ptF z = CategoryTheory.CategoryStruct.comp (spMap φ.toRingHom) (ptF y) := by
    apply CategoryTheory.Limits.pullback.hom_ext
    · simp only [ptF, CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst]
      exact h₂.1.trans h₁.1
    · simp only [ptF, CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd]
      rw [← AlgebraicGeometry.Spec.map_comp]
      exact congrArg spMap φ.comp_algebraMap.symm
  rw [e, AlgebraicGeometry.Scheme.Hom.comp_apply]
  exact hy _

end Tri

section Fin

variable {K : Type} [Field K] [NumberField K] [Algebra c.F K]


omit [Algebra c.F K] in
theorem nrmOf_nonneg (la : HeightOneSpectrum (𝓞 K)) (w : EReal) : 0 ≤ nrmOf la w := by
  simp only [nrmOf]
  split_ifs
  exacts [le_rfl, by positivity]


omit [Algebra c.F K] in
theorem nrmOf_anti (la : HeightOneSpectrum (𝓞 K)) {w w' : EReal} (hw : w ≠ ⊥) (h : w ≤ w') :
    nrmOf la w' ≤ nrmOf la w := by
  by_cases ht : w' = ⊤
  · rw [ht, nrmOf, if_pos rfl]; exact nrmOf_nonneg _ _
  rw [nrmOf, nrmOf, if_neg ht, if_neg (ne_top_of_le_ne_top ht h)]
  exact Real.rpow_le_rpow_of_exponent_le (one_lt_absNorm_real la).le (neg_le_neg (EReal.toReal_le_toReal h hw ht))

structure FinFr (y : FrPt Xo c K) (v : FinitePlace K) : Type 1 where

  T : CDVR

  io : c.F →+* T.Fr

  φ : CoefHom c io K

  e : ℕ

  lies : letI := io.toAlgebra; OverLa v.maximalIdeal T.V φ.toRingHom e

  fin : T.FinRes

  pt : IntFr Xo c T io

  t : Ix Dw → T.Frˣ

  tri : letI := io.toAlgebra; Reframes φ y t pt.1

instance FinFr.nonempty (y : FrPt Xo c K) (v : FinitePlace K) : Nonempty (FinFr y v) := by
  have hE : IntFrExt Xo c := (Nat.eq_zero_or_pos (Dw.p + Dw.q)).elim
    (GlobalTheory.RankZeroFrames.intFrExt_of_rank_zero E H Dw l Xo c) (GlobalTheory.AnyLevelFrame.intFrExt E H Dw l Xo c)
  obtain ⟨T₀, j, ho, hf, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K v.maximalIdeal
  letI := (j.comp (algebraMap c.F K)).toAlgebra
  obtain ⟨w₀, h₀⟩ := exists_frMap (⟨j, fun _ => rfl⟩ : K →ₐ[c.F] T₀.Fr) y
  obtain ⟨T, i, r, hr, hi, hf', y₁, hx⟩ := hE T₀ _ hf w₀.x w₀.x_over
  letI := (i.comp (j.comp (algebraMap c.F K))).toAlgebra
  let φ : K →ₐ[c.F] T.Fr := ⟨i.comp j, fun _ => rfl⟩
  obtain ⟨w, hw⟩ := exists_frMap (⟨i, fun _ => rfl⟩ : T₀.Fr →ₐ[c.F] T.Fr) w₀
  have hReframe : Formalism.L2.PjFree.ReFrame Xo c :=
    Formalism.L2.PjFree.reFrame_of
      (fun S _ x _ v hv _ w A N w' hw hw' =>
        GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo S x v hv w A N w' hw hw')
      (GlobalTheory.IntRebase.intRebase GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c)
  obtain ⟨t, z, hz⟩ := hReframe T _ y₁ w (hw.1.trans hx.symm)
  exact ⟨⟨T, _, φ, _, ho.bc i hr hi, hf', z, t, w, frMap_comp h₀ hw fun _ => rfl, hz⟩⟩

namespace FinFr

variable {y : FrPt Xo c K} {v : FinitePlace K} (F : FinFr y v)

def abs : AbsoluteValue F.T.Fr ℝ where
  toFun a := nrmOf v.maximalIdeal (nval F.T.V F.e a)
  map_mul' a b := by
    have h1 := one_lt_absNorm_real v.maximalIdeal
    by_cases ha : a = 0
    · simp [ha, nval_zero, nrmOf]
    by_cases hb : b = 0
    · simp [hb, nval_zero, nrmOf]
    rw [nval_mul, nval_of_ne ha, nval_of_ne hb, ← EReal.coe_add]
    simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe]
    rw [neg_add, Real.rpow_add (by linarith)]
  nonneg' a := nrmOf_nonneg _ _
  eq_zero' a := by
    have h1 := one_lt_absNorm_real v.maximalIdeal
    by_cases ha : a = 0
    · simp [ha, nval_zero, nrmOf]
    rw [nval_of_ne ha]
    simp only [nrmOf, EReal.coe_ne_top, if_false, ha, iff_false]
    exact (Real.rpow_pos_of_pos (by linarith) _).ne'
  add_le' a b := by
    rcases min_le_iff.1 (nval_add (V := F.T.V) F.e a b) with h | h
    · exact (nrmOf_anti _ (nval_ne_bot _ _) h).trans (le_add_of_nonneg_right (nrmOf_nonneg _ _))
    · exact (nrmOf_anti _ (nval_ne_bot _ _) h).trans (le_add_of_nonneg_left (nrmOf_nonneg _ _))

theorem abs_apply (a : F.T.Fr) : F.abs a = nrmOf v.maximalIdeal (nval F.T.V F.e a) := rfl

theorem abs_φ (a : K) : F.abs (F.φ a) = v a := by
  by_cases ha : a = 0
  · simp [ha]
  have h := nrmOf_smul v.maximalIdeal ha (nval_ne_bot (V := F.T.V) F.e (1 : F.T.Fr))
  rw [← nval_smul F.lies ha, mul_one, FinitePlace.mk_maximalIdeal, ← abs_apply, ← abs_apply, map_one, mul_one] at h
  exact h

theorem ofReal_abs (a : F.T.Fr) :
    ENNReal.ofReal (F.abs a) = normOfOrd (Ideal.absNorm v.maximalIdeal.asIdeal) (nval F.T.V F.e a) := by
  have h1 := one_lt_absNorm_real v.maximalIdeal
  by_cases ha : a = 0
  · rw [ha, map_zero, nval_zero, normOfOrd, EReal.top_mul_coe_of_pos (Real.log_pos h1)]
    simp
  rw [abs_apply, nval_of_ne ha, normOfOrd, ← EReal.coe_mul, ← EReal.coe_neg, EReal.exp_coe]
  simp only [nrmOf, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  rw [Real.rpow_def_of_pos (by linarith)]
  congr 2
  ring

def nrm (f : Rul Xo c) : ℝ := F.abs (evI F.pt f)

def fac (e : Ix Dw → ℤ) : ℝ := F.abs ((∏ i, F.t i ^ e i : F.T.Frˣ) : F.T.Fr)

theorem fac_pos (e : Ix Dw → ℤ) : 0 < F.fac e := F.abs.pos (Units.ne_zero _)

theorem fac_add (e e' : Ix Dw → ℤ) : F.fac (e + e') = F.fac e * F.fac e' := by
  simp only [fac, Pi.add_apply, zpow_add, Finset.prod_mul_distrib, Units.val_mul, map_mul]

theorem nrm_eq {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) : F.nrm f = F.fac e * v (evR Xo c f y) := by
  let _ := F.io.toAlgebra
  rw [← F.abs_φ, fac, ← map_mul, ← F.tri.evR_eq hf]
  rfl

def latMax (C : Submodule c.F (Rul Xo c)) : ℝ := ⨆ w : supLat C, F.nrm w.1

variable {ι : Type} [Fintype ι]

def wedgeNrm (s : ι → RulK Xo c K) : ℝ≥0∞ :=
  normOfOrd (Ideal.absNorm v.maximalIdeal.asIdeal) (wedgeOrd (psiSet H) F.e F.φ F.pt s)

end FinFr

end Fin

section Primes

variable {K : Type} [Field K] [NumberField K]

def primeWt (S : Finset ℕ) (b : ℕ → ℝ) (v : FinitePlace K) : ℝ := ∑ p ∈ S, b p * -Real.log (v (p : K))

theorem finite_support_log {a : K} (ha : a ≠ 0) : (Function.support fun v : FinitePlace K => Real.log (v a)).Finite :=
  (FinitePlace.hasFiniteMulSupport ha).subset fun v hv h => hv (by simp only at h ⊢; rw [h, Real.log_one])

theorem finsum_log_natCast {p : ℕ} (hp : p ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (v (p : K)) = -(Module.finrank ℚ K * Real.log p) := by
  have h0 : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp
  rw [← Real.log_finprod fun v : FinitePlace K => FinitePlace.pos_iff.2 h0, FinitePlace.prod_eq_inv_abs_norm h0,
    show (p : K) = algebraMap ℚ K p from (map_natCast _ p).symm, Algebra.norm_algebraMap]
  simp

theorem finsum_primeWt {S : Finset ℕ} (hS : 0 ∉ S) (b : ℕ → ℝ) :
    (∑ᶠ v, primeWt (K := K) S b v) / (Module.finrank ℚ K : ℝ) = ∑ p ∈ S, b p * Real.log p := by
  have h0 : ∀ p ∈ S, p ≠ 0 := fun p hp e => hS (e ▸ hp)
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  unfold primeWt
  rw [finsum_sum_comm S (fun v p => b p * -Real.log (v (p : K))) fun p hp => (finite_support_log (K := K) (a := p) (Nat.cast_ne_zero.2 (h0 p hp))).subset
    fun v hv e => hv (by simp only at e ⊢; rw [e, neg_zero, mul_zero]), Finset.sum_div]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← mul_finsum, finsum_neg_distrib, finsum_log_natCast (h0 p hp)]
  field_simp

variable [Algebra c.F K] {y : FrPt Xo c K} {v : FinitePlace K} (F : FinFr y v)

namespace FinFr

end FinFr

end Primes

section Inf

variable {K : Type} [Field K] [Algebra c.F K] {r : ℕ}


variable (c) in
abbrev baseEmb (τ : K →+* ℂ) : c.F →+* ℂ := goodOf c (τ.comp (algebraMap c.F K))


variable (c) in
def goodHom (τ : K →+* ℂ) : K →ₐ[c.F] CAt (baseEmb c τ) :=
  if h : GoodEmb c (τ.comp (algebraMap c.F K)) then
    ⟨τ, fun a => (DFunLike.congr_fun (if_pos h : baseEmb c τ = _) a).symm⟩
  else ⟨(starRingEnd ℂ).comp τ, fun a => (DFunLike.congr_fun (if_neg h : baseEmb c τ = _) a).symm⟩

theorem norm_goodHom (τ : K →+* ℂ) (a : K) : ‖toC (goodHom c τ a)‖ = ‖τ a‖ := by
  unfold goodHom
  split_ifs
  · rfl
  · exact Complex.norm_conj _

structure InfFr (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (y : FrPt Xo c K) (τ : K →+* ℂ) : Type where

  k : (U (baseEmb c τ)).Comp

  z : ((U (baseEmb c τ)).X k).dom

  t : Ix Dw → (CAt (baseEmb c τ))ˣ

  tri : Reframes (goodHom c τ) y t ((U (baseEmb c τ)).un k z)

variable {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {y : FrPt Xo c K} {τ : K →+* ℂ}

theorem InfFr.nonempty (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (y : FrPt Xo c K) (τ : K →+* ℂ) :
    Nonempty (InfFr U y τ) := by
  obtain ⟨w, hw⟩ := exists_frMap (goodHom c τ) y
  obtain ⟨k, z, t, h⟩ := (hU _ (goodEmb_goodOf c _)).2.2.1 w
  exact ⟨⟨k, z, t⁻¹, w, hw, (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c _).2.2.1 _ _ _ h⟩⟩

namespace InfFr

variable (F : InfFr U y τ) (x : ℝ)

abbrev pt : Σ k, FD.Frame ((U (baseEmb c τ)).X k).Ψ r := ⟨F.k, F.z.1⟩

theorem mem_framesOn {Z : Comp Xo c} (hy : LiesOn Z y) : F.pt ∈ framesOn (U (baseEmb c τ)) Z :=
  ⟨F.z.2, F.tri.liesOn hy⟩

def nrm (G : WTZ E) (f : Rul Xo c) : ℝ := homN (U (baseEmb c τ)) x G f F.pt

def fac (G : WTZ E) : ℝ :=
  lieFacZ Dw x G * ((U (baseEmb c τ)).X F.k).nfac (modelWt (U (baseEmb c τ)) G F.k) F.z.1 *
    ‖toC ((∏ i, F.t i ^ exZ Dw G i : (CAt (baseEmb c τ))ˣ) : CAt (baseEmb c τ))‖

theorem fac_pos (G : WTZ E) : 0 < F.fac x G :=
  mul_pos (mul_pos (lieFacZ_pos _ _) (FD.BoundedSectionAlgebra.nfac_pos _ F.z.2 _))
    (norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) _))

theorem fac_add {G G' : WTZ E} (hG : Even G.2) (hG' : Even G'.2) : F.fac x (G + G') = F.fac x G * F.fac x G' := by
  have e : ∀ a b : CAt (baseEmb c τ), ‖toC (a * b)‖ = ‖toC a‖ * ‖toC b‖ := fun a b => norm_mul (toC a) (toC b)
  simp only [fac, lieFacZ_add, modelWt_add _ hG hG', FD.BoundedSectionAlgebra.nfac_add _ F.z.2, exZ_add, zpow_add,
    Finset.prod_mul_distrib, Units.val_mul, e]
  ring

theorem nrm_eq {G : WTZ E} {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) :
    F.nrm x G f = F.fac x G * ‖τ (evR Xo c f y)‖ := by
  haveI : IsLocalRing (CAt (baseEmb c τ)) := inferInstanceAs (IsLocalRing ℂ)
  have e : rdU (U (baseEmb c τ)) f F.k F.z.1 = toC (evR Xo c f ((U (baseEmb c τ)).un F.k F.z)) := dif_pos F.z.2
  have e' : ∀ a b : CAt (baseEmb c τ), ‖toC (a * b)‖ = ‖toC a‖ * ‖toC b‖ := fun a b => norm_mul (toC a) (toC b)
  show _ * (‖rdU (U (baseEmb c τ)) f F.k F.z.1‖ * FD.Data.nfac _ _ _) = _
  rw [e, F.tri.evR_eq hf, e', norm_goodHom, fac]
  ring

end InfFr

end Inf

section Berg

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (Z : Comp Xo c)

def bergCusp (G : WTZ E) (σ : c.F →+* ℂ) (z : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r) : ℝ≥0∞ :=
  ⨆ f ∈ cuspOn U Z G, ENNReal.ofReal (homN (U (goodOf c σ)) x G f z) ^ 2 / ENNReal.ofReal (petOn U x V dict Z G σ f) ^ 2

variable {U x V dict Z}

theorem bergCusp_le_iff {G : WTZ E} {σ : c.F →+* ℂ} {z : Σ k, FD.Frame ((U (goodOf c σ)).X k).Ψ r} {B : ℝ}
    (hB : 0 ≤ B) : bergCusp U x V dict Z G σ z ≤ ENNReal.ofReal B ↔
      ∀ f ∈ cuspOn U Z G, homN (U (goodOf c σ)) x G f z ^ 2 ≤ B * petOn U x V dict Z G σ f ^ 2 := by
  simp only [bergCusp, iSup_le_iff]
  refine forall₂_congr fun f _ => ?_
  have hp : 0 ≤ petOn U x V dict Z G σ f := petAt_nonneg _ _ _ _ _ _ _
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)),
    ← ENNReal.ofReal_pow (homN_nonneg _ _ _ _ _), ← ENNReal.ofReal_pow hp, ← ENNReal.ofReal_mul hB,
    ENNReal.ofReal_le_ofReal_iff (by positivity)]

theorem bergCusp_le_bergOn {G : WTZ E} {σ : c.F →+* ℂ}
    (hd : ∀ g, (dict (goodOf c σ) g).2 ∈ ((U (goodOf c σ)).X (dict (goodOf c σ) g).1).dom)
    (z : FPt (U (goodOf c σ)).X) : bergCusp U x V dict Z G σ ⟨z.1, z.2.1⟩ ≤
      bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z := by
  by_cases h : bergOn (U (goodOf c σ)) (V (goodOf c σ)) (dict (goodOf c σ)) Z G z = ⊤
  · exact h ▸ le_top
  rw [← ENNReal.ofReal_toReal h, bergCusp_le_iff ENNReal.toReal_nonneg]
  exact fun f hf => homN_sq_le _ x _ _ _ (muPart_univ_le _ _ _) hd z ENNReal.toReal_nonneg
    (ENNReal.ofReal_toReal h).ge ((mem_cuspW.1 hf.1).2 _ (goodEmb_goodOf c σ))

end Berg

section Statements

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : Formalism.BasicNotions.D7} (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D)
  (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (Z : Comp Xo c) (P : WtPar Dw)



def WtPar.tauWt : AllWt.Weight Dw := (dimFlag Dw + 3) • P.u₁ - P.uc

section At

variable {K : Type} [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K)

def TauBd (m : ℕ) (τ : Rul Xo c) (t : FinitePlace K → ℝ) (A : (K →+* ℂ) → ℝ) : Prop :=
  (∀ v (F : FinFr y v), F.nrm τ ≤ Real.exp (t v) * F.latMax (Cusp Z U P.u₁) ^ (m * (dimFlag Dw + 3))) ∧
    ∀ ρ : K →+* ℂ, Nonempty (InfFr U y ρ) ∧ ∀ F : InfFr U y ρ,
      bergCusp U x V dict Z (wtOf Dw P.u₁ 0) (ρ.comp (algebraMap c.F K)) F.pt ≠ ⊤ ∧
      F.nrm x (wtOf Dw (m • P.tauWt) 0) τ ≤ A ρ *
        √(bergCusp U x V dict Z (wtOf Dw P.u₁ 0) (ρ.comp (algebraMap c.F K)) F.pt).toReal ^ (m * (dimFlag Dw + 3))

def TauPtAt (X : ℝ) : Prop :=
  ∃ (m : ℕ) (τ : Rul Xo c) (t : FinitePlace K → ℝ) (A : (K →+* ℂ) → ℝ), 1 ≤ m ∧
    τ ∈ secZ Xo c (exOf Dw (m • P.tauWt) 0) ∧ evR Xo c τ y ≠ 0 ∧ (Function.support t).Finite ∧ (∀ ρ, 0 < A ρ) ∧
    TauBd U x V dict Z P y m τ t A ∧ (∑ᶠ v, t v) / (Module.finrank ℚ K : ℝ) + meanLog K A ≤ m * X

variable {U x V dict Z P y}

end At

def SupBdWt (la : AllWt.Weight Dw) (β : ℝ) : Prop :=
  ∀ (σ : c.F →+* ℂ), ∀ z ∈ framesOn (U (goodOf c σ)) Z, ∀ f ∈ Cusp Z U la,
    homN (U (goodOf c σ)) x (wtOf Dw la 0) f z ^ 2 ≤ β * petOn U x V dict Z (wtOf Dw la 0) σ f ^ 2

variable {U x V dict Z P}

theorem supBdWt_iff {la : AllWt.Weight Dw} {β : ℝ} (hβ : 0 ≤ β) : SupBdWt U x V dict Z la β ↔
    ∀ σ, ∀ z ∈ framesOn (U (goodOf c σ)) Z, bergCusp U x V dict Z (wtOf Dw la 0) σ z ≤ ENNReal.ofReal β :=
  forall₃_congr fun _ _ _ => (bergCusp_le_iff hβ).symm

theorem SupBdWt.of_bergOn {la : AllWt.Weight Dw} {β : ℝ} (hβ : 0 ≤ β)
    (hd : ∀ σ, GoodEmb c σ → ∀ g, (dict σ g).2 ∈ ((U σ).X (dict σ g).1).dom)
    (h : ∀ σ, GoodEmb c σ → ∀ z : FPt (U σ).X, (⟨z.1, z.2.1⟩ : Σ k, FD.Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z →
      bergOn (U σ) (V σ) (dict σ) Z (wtOf Dw la 0) z ≤ ENNReal.ofReal β) : SupBdWt U x V dict Z la β :=
  (supBdWt_iff hβ).2 fun σ z hz => (bergCusp_le_bergOn (hd _ (goodEmb_goodOf c σ)) ⟨z.1, z.2, hz.1⟩).trans
    (h _ (goodEmb_goodOf c σ) ⟨z.1, z.2, hz.1⟩ hz)

end Statements

end GlobalTheory.CompHS
