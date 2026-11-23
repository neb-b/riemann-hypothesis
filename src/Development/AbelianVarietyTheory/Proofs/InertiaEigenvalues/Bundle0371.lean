module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SpanSingletonEqTopIffIsUnitOfIsBaseChange
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorLiftOfIsAdicComplete
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)

theorem ghost_eq (n : ℕ) (x : _root_.WittVector l C) :
    _root_.WittVector.ghostComponent n x =
      ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * x.coeff i ^ l ^ (n - i) := by
  rw [_root_.WittVector.ghostComponent_apply, aeval_wittPolynomial]

theorem ghost_mem_pow (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C)
    (hx : ∀ i, x.coeff i ∈ J) : _root_.WittVector.ghostComponent n x ∈ J ^ n := by
  rw [ghost_eq]
  refine Ideal.sum_mem _ fun i _ => ?_
  have h1 : (l : C) ^ i ∈ J ^ i := Ideal.pow_mem_pow hlJ i
  have h2 : x.coeff i ^ l ^ (n - i) ∈ J ^ (l ^ (n - i)) := Ideal.pow_mem_pow (hx i) _
  have h3 : (l : C) ^ i * x.coeff i ^ l ^ (n - i) ∈ J ^ (i + l ^ (n - i)) := by
    rw [pow_add]; exact Ideal.mul_mem_mul h1 h2
  refine Ideal.pow_le_pow_right ?_ h3
  have : n - i < l ^ (n - i) := Nat.lt_pow_self hl.out.one_lt
  omega

def liftW (y : _root_.WittVector l (C ⧸ J)) : _root_.WittVector l C :=
  _root_.WittVector.mk l (fun i => Function.surjInv Ideal.Quotient.mk_surjective (y.coeff i))

theorem map_liftW (y : _root_.WittVector l (C ⧸ J)) :
    _root_.WittVector.map (Ideal.Quotient.mk J) (liftW l J y) = y := by
  ext i
  rw [_root_.WittVector.map_coeff]
  simp only [liftW, _root_.WittVector.coeff_mk]
  exact Function.surjInv_eq Ideal.Quotient.mk_surjective _

def gh (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l (C ⧸ J) →+* C ⧸ J ^ n :=
  RingHom.liftOfRightInverse (_root_.WittVector.map (Ideal.Quotient.mk J)) (liftW l J) (map_liftW l J)
    ⟨(Ideal.Quotient.mk (J ^ n)).comp (_root_.WittVector.ghostComponent n), fun x hx => by
      rw [RingHom.mem_ker] at hx ⊢
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      refine ghost_mem_pow l J hlJ n x fun i => ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← _root_.WittVector.map_coeff, hx,
        _root_.WittVector.zero_coeff]⟩

theorem gh_map (hlJ : (l : C) ∈ J) (n : ℕ) (x : _root_.WittVector l C) :
    gh l J hlJ n (_root_.WittVector.map (Ideal.Quotient.mk J) x) =
      Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n x) :=
  RingHom.liftOfRightInverse_comp_apply _ _ _ _ x

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable (k : Type) [CommRing k] [CharP k l] [PerfectRing k l]

theorem symm_iter_pow (n : ℕ) (x : k) :
    (iterateFrobeniusEquiv k l (n + 1)).symm x ^ l = (iterateFrobeniusEquiv k l n).symm x := by
  apply (iterateFrobeniusEquiv k l n).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_def, ← pow_mul, ← pow_succ',
    ← iterateFrobeniusEquiv_def k l (n + 1), RingEquiv.apply_symm_apply]

theorem symm_iter_zero (x : k) : (iterateFrobeniusEquiv k l 0).symm x = x := by
  apply (iterateFrobeniusEquiv k l 0).injective
  rw [RingEquiv.apply_symm_apply, iterateFrobeniusEquiv_zero_apply]

variable {k} (ψ : k →+* C ⧸ J)

def wn (n : ℕ) : _root_.WittVector l k →+* _root_.WittVector l (C ⧸ J) :=
  _root_.WittVector.map (ψ.comp (iterateFrobeniusEquiv k l n).symm.toRingHom)

def yh (n : ℕ) (w : _root_.WittVector l k) : _root_.WittVector l C := liftW l J (wn l J ψ n w)

theorem mk_yh_coeff (n : ℕ) (w : _root_.WittVector l k) (i : ℕ) :
    Ideal.Quotient.mk J ((yh l J ψ n w).coeff i) = ψ ((iterateFrobeniusEquiv k l n).symm (w.coeff i)) := by
  rw [← _root_.WittVector.map_coeff, yh, map_liftW, wn, _root_.WittVector.map_coeff]
  rfl

def fn (hlJ : (l : C) ∈ J) (n : ℕ) : _root_.WittVector l k →+* C ⧸ J ^ n :=
  (gh l J hlJ n).comp (wn l J ψ n)

theorem fn_apply (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    fn l J ψ hlJ n w = Ideal.Quotient.mk (J ^ n) (_root_.WittVector.ghostComponent n (yh l J ψ n w)) := by
  rw [fn, RingHom.comp_apply, ← gh_map l J hlJ n, yh, map_liftW]

theorem step (hlJ : (l : C) ∈ J) (n : ℕ) (w : _root_.WittVector l k) :
    _root_.WittVector.ghostComponent (n + 1) (yh l J ψ (n + 1) w) -
      _root_.WittVector.ghostComponent n (yh l J ψ n w) ∈ J ^ n := by
  set y := yh l J ψ (n + 1) w with hy
  let z : _root_.WittVector l C := _root_.WittVector.mk l (fun i => y.coeff i ^ l)
  have hz : _root_.WittVector.map (Ideal.Quotient.mk J) z = wn l J ψ n w := by
    ext i
    rw [_root_.WittVector.map_coeff, _root_.WittVector.coeff_mk, map_pow, hy, mk_yh_coeff, ← map_pow,
      symm_iter_pow, wn, _root_.WittVector.map_coeff]
    rfl
  have h1 : _root_.WittVector.ghostComponent n (yh l J ψ n w) - _root_.WittVector.ghostComponent n z ∈ J ^ n := by
    rw [← Ideal.Quotient.eq, ← fn_apply, ← gh_map l J hlJ, hz, fn, RingHom.comp_apply]
  have h2 : _root_.WittVector.ghostComponent (n + 1) y - _root_.WittVector.ghostComponent n z =
      (l : C) ^ (n + 1) * y.coeff (n + 1) := by
    have ha : _root_.WittVector.ghostComponent (n + 1) y =
        (∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i)) +
          (l : C) ^ (n + 1) * y.coeff (n + 1) := by
      rw [ghost_eq, Finset.sum_range_succ, Nat.sub_self, pow_zero, pow_one]
    have hb : _root_.WittVector.ghostComponent n z =
        ∑ i ∈ Finset.range (n + 1), (l : C) ^ i * y.coeff i ^ l ^ (n + 1 - i) := by
      rw [ghost_eq]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.mp hi
      simp only [z, _root_.WittVector.coeff_mk]
      rw [← pow_mul, ← pow_succ']
      congr 3
      omega
    rw [ha, hb]; ring
  have h3 : (l : C) ^ (n + 1) * y.coeff (n + 1) ∈ J ^ n :=
    Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlJ _))
  rw [← h2] at h3
  have := Ideal.sub_mem _ h3 h1
  convert this using 1
  abel

theorem compat (hlJ : (l : C) ∈ J) (w : _root_.WittVector l k) {m n : ℕ} (hle : m ≤ n) :
    _root_.WittVector.ghostComponent n (yh l J ψ n w) -
      _root_.WittVector.ghostComponent m (yh l J ψ m w) ∈ J ^ m := by
  induction n, hle using Nat.le_induction with
  | base => rw [sub_self]; exact Ideal.zero_mem _
  | succ n hmn ih =>
    have := Ideal.add_mem _ (Ideal.pow_le_pow_right hmn (step l J ψ hlJ n w)) ih
    convert this using 1
    abel

end GlobalTheory.WittLift

namespace GlobalTheory.WittLift

variable (l : ℕ) [hl : Fact l.Prime] {C : Type} [CommRing C] (J : Ideal C)
variable {k : Type} [CommRing k] [CharP k l] [PerfectRing k l] (ψ : k →+* C ⧸ J)

theorem fn_compat (hlJ : (l : C) ∈ J) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow J hle).comp (fn l J ψ hlJ n) = fn l J ψ hlJ m := by
  refine RingHom.ext fun w => ?_
  rw [RingHom.comp_apply, fn_apply, fn_apply, Ideal.Quotient.factor_mk, Ideal.Quotient.eq]
  exact compat l J ψ hlJ w hle

end GlobalTheory.WittLift

namespace GlobalTheory

theorem exists_wittVector_lift_of_isAdicComplete :
    ∀ (l : ℕ) [Fact l.Prime] (k : Type) [CommRing k] [CharP k l] [PerfectRing k l] (C : Type) [CommRing C]
      (J : Ideal C), (l : C) ∈ J → IsAdicComplete J C → ∀ ψ : k →+* C ⧸ J,
      ∃ ω : WittVector l k →+* C, ∀ w, Ideal.Quotient.mk J (ω w) = ψ (w.coeff 0) := by
  intro l _ k _ _ _ C _ J hlJ hC ψ
  haveI := hC
  refine ⟨IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ), fun w => ?_⟩
  have h0 : Ideal.Quotient.mk (J ^ 1)
      (IsAdicComplete.liftRingHom J (WittLift.fn l J ψ hlJ) (WittLift.fn_compat l J ψ hlJ) w) =
      Ideal.Quotient.mk (J ^ 1) (_root_.WittVector.ghostComponent 1 (WittLift.yh l J ψ 1 w)) := by
    rw [IsAdicComplete.mk_liftRingHom, WittLift.fn_apply]
  have h1 := Ideal.Quotient.eq.mp h0
  rw [pow_one] at h1
  rw [Ideal.Quotient.eq.mpr h1, WittLift.ghost_eq, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, one_mul, Nat.sub_zero, pow_one, Nat.sub_self, map_add (f := _), map_mul, map_pow]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hlJ, zero_mul, add_zero, WittLift.mk_yh_coeff, ← map_pow,
    WittLift.symm_iter_pow, WittLift.symm_iter_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpStarOfLowTermsRemoved
section
noncomputable section

namespace GlobalTheory.ExpImage.LowTerms

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem oB_mem_zero {AI : LocAinf l P} (T : LocTied l P AI) (x : Om l) : oB P x ∈ FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om x
  exact (GlobalTheory.ThetaTie.fil_zero T _).2 ⟨y, h1.symm⟩

theorem tD_pow_mem_zero (j : ℕ) : tD P ^ j ∈ FilB P 0 :=
  FilB_anti (by simp) (FilB_pow (tD_mem (P := P)) j)

theorem act_term (g : GQ l) (c : ℚ_[l]) {x : Om l} (hx : g x = x) (j : ℕ) :
    P.actQdR g (qB P c * (oB P x * tD P ^ j)) =
      qB P (c * (P.χQ g : ℚ_[l]) ^ j) * (oB P x * tD P ^ j) := by
  rw [map_mul, map_mul, map_pow, act_tD, P.actQdR_Om, hx, AlgEquiv.commutes, map_mul, map_pow,
    mul_pow]
  ring

theorem Ks_le_Kinf (K : FinExt l) (s : ℕ) : Ks K s ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ fun _ hx => Exists.intro s hx) _

theorem expStar_of_sum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), IsGen (LT l).χQ K s g → ∀ w : ℕ → Om l, (∀ j, w j ∈ Ks K s) → ∀ b ∈ FilB (LT l) 0, (∀ h ∈ Hinf K, NearZ (LT l) (e + 1) ((LT l).actQdR h b - b)) → NearZ (LT l) (e + 1) (∑ j ∈ Finset.range (e + 1), oB (LT l) (w j) * tD (LT l) ^ j + (qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g b - b)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((LT l).χQ g : ℚ_[l]))⁻¹ * w e) := by
  intro LT l _ AI T K s hs e g hg w hw b hb hH hN
  have hχ : IsCyc (LT l).χQ := (LT l).χQ_cyc
  obtain ⟨hn, -, hker⟩ := GlobalTheory.Cyc.cyc_basic l _ hχ
  obtain ⟨-, -, hint, hlog⟩ := GlobalTheory.PadicLogUnits.logZl_hom l
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  set u : ℚ_[l] := ((LT l).χQ g : ℚ_[l]) with hu
  have hu0 : u ≠ 0 := Units.ne_zero _
  have hL : logZl l u ≠ 0 := by
    rw [← norm_pos_iff, hlog s hs.1 hs.2 u hg.2.le, hg.2]
    exact zpow_pos hl _
  have hLc : ((logChi LT g : ℤ_[l]) : ℚ_[l]) = logZl l u :=
    congrArg Subtype.val (dif_pos (hint _ (hn g)))
  have hne : ∀ j ∈ Finset.range e, u ^ ((j : ℤ) - e) - 1 ≠ 0 := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    rw [← norm_pos_iff, GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l s hs u hg.2 _ (by omega)]
    exact zpow_pos hl _
  set c : ℕ → ℚ_[l] := fun j => (u ^ ((j : ℤ) - e) - 1)⁻¹ with hc
  set S : (LT l).R.BdR :=
    ∑ j ∈ Finset.range e, qB (LT l) (c j) * (oB (LT l) (w j) * tD (LT l) ^ j) with hS
  have hS0 : S ∈ FilB (LT l) 0 :=
    Submodule.sum_mem _ fun j _ =>
      qB_mul_mem _ (FilB_zero_mul (oB_mem_zero T _) (tD_pow_mem_zero j))
  have hSH : ∀ h ∈ Hinf K, (LT l).actQdR h S = S := by
    intro h hh
    have h1 : (LT l).χQ h = 1 := (hker K h (Hinf_le_fix hh)).2.1 hh
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [act_term h _ (hh ⟨w j, Ks_le_Kinf K s (hw j)⟩), h1]
    simp
  have hSg : qB (LT l) (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (LT l).actQdR g S - S =
      ∑ j ∈ Finset.range e, oB (LT l) (w j) * tD (LT l) ^ j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [act_term g _ (hg.1 ⟨w j, hw j⟩), ← mul_assoc, ← map_mul, ← sub_mul, ← map_sub]
    have : (((LT l).χQ g ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) * (c j * u ^ j) - c j = 1 := by
      have h2 : u ^ ((j : ℤ) - e) = u ^ (-(e : ℤ)) * u ^ j := by
        rw [sub_eq_neg_add, zpow_add₀ hu0, zpow_natCast]
      have h3 : (u ^ ((j : ℤ) - e) - 1) * c j = 1 := mul_inv_cancel₀ (hne j hj)
      rw [Units.val_zpow_eq_zpow_val, ← hu]
      rw [h2] at h3
      linear_combination h3
    rw [this, map_one, one_mul]
  refine _root_.GlobalTheory.ExpImage.integral_cocycle_of_gen LT l AI T K s hs e g hg _
    (mul_mem (IntermediateField.algebraMap_mem _ _) (hw e)) (b + S) (add_mem hb hS0)
    (fun h hh => ?_) ?_
  · have := hH h hh
    rwa [map_add, hSH h hh, add_sub_add_right_eq_sub]
  · have h4 : qB (LT l) (logZl l u) * oB (LT l) (algebraMap ℚ_[l] (Om l) (logZl l u)⁻¹) = 1 := by
      rw [← IsScalarTower.algebraMap_apply, ← map_mul, mul_inv_cancel₀ hL, map_one]
    convert hN using 1
    rw [hLc, Finset.sum_range_succ, ← hSg, map_add (f := _), map_mul]
    linear_combination (oB (LT l) (w e) * tD (LT l) ^ e) * h4

end GlobalTheory.ExpImage.LowTerms
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentElementsPushout
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem ff_descent_elem_pushout : ∀ (A B D : Type) [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (p q : B →+* D), f.FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom f) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → Function.Injective f ∧ ∀ b, p b = q b → b ∈ f.range := by
  intro A B D _ _ _ f p q hf hpo
  refine ⟨hf.injective, fun b hb => ?_⟩
  letI : Algebra A B := f.toAlgebra
  haveI : Module.FaithfullyFlat A B := hf

  have hw : CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B))) =
      CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom f)
        (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom) := by
    ext a
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := B) a
  have e := congrArg (fun x => (hpo.desc _ _ hw).hom x) hb
  have e1 := congrArg (fun g => g.hom b) (hpo.inl_desc _ _ hw)
  have e2 := congrArg (fun g => g.hom b) (hpo.inr_desc _ _ hw)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e e1 e2

  have key : b ∈ (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := B)).eqLocus
      (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := B)).toRingHom :=
    e1.symm.trans (e.trans e2)
  have hmem := (Algebra.IsEffective.of_faithfullyFlat A B).eqLocus_includeLeft_includeRight ▸
    SetLike.mem_coe.mpr key
  obtain ⟨a, ha⟩ := hmem
  exact ⟨a, ha⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FaithfullyFlatDescentFreeModuleCocycle
section
open TensorProduct

namespace GlobalTheory.CocycleDescent

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {d : ℕ}

noncomputable def defect (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) :
    (Fin d → B) →ₗ[A] (Fin d → B ⊗[A] B) :=
  (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toLinearMap.compLeft (Fin d) -
    (ε.mulVecLin.restrictScalars A) ∘ₗ
      (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toLinearMap.compLeft (Fin d)

theorem defect_apply (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (z : Fin d → B) :
    defect ε z = (fun i => z i ⊗ₜ[A] (1 : B)) - ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i := rfl

theorem lTensor_defect (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (x : B ⊗[A] (Fin d → B)) :
    piRight A A B (fun _ : Fin d => B ⊗[A] B) ((defect ε).lTensor B x) =
      (fun i => Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)
          (piRight A A B (fun _ : Fin d => B) x i)) -
      (ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B))).mulVec
        (fun i => Algebra.TensorProduct.map (AlgHom.id A B)
          (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)
            (piRight A A B (fun _ : Fin d => B) x i)) := by
  induction x with
  | add x y hx hy =>
    rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _)]
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Pi.sub_apply, map_add (f := _), mul_add,
      Finset.sum_add_distrib]
    abel
  | tmul b z =>
    ext i
    simp [defect_apply, Matrix.mulVec, dotProduct, tmul_sub, tmul_sum]

theorem isBaseChange [Module.Flat A B] (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (hε : IsUnit ε)
    (hc : ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) *
      ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) =
      ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B))) :
    IsBaseChange B (LinearMap.ker (defect ε)).subtype := by
  set N := LinearMap.ker (defect ε) with hN
  set e := piRight A A B (fun _ : Fin d => B) with he
  have hεinj : Function.Injective ε.mulVec := Matrix.mulVec_injective_of_isUnit hε
  have key : ∀ x : B ⊗[A] N, (fun i => (N.subtype.liftBaseChange B x) i ⊗ₜ[A] (1 : B)) =
      ε.mulVec (e (N.subtype.lTensor B x)) := by
    intro x
    induction x with
    | add x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), Matrix.mulVec_add, ← hx, ← hy]
      ext i
      simp [add_tmul]
    | tmul b n =>
      have hn : defect ε n.1 = 0 := n.2
      rw [defect_apply, sub_eq_zero] at hn
      have h1 : e (N.subtype.lTensor B (b ⊗ₜ n)) =
          (b ⊗ₜ[A] (1 : B)) • fun i => (1 : B) ⊗ₜ[A] n.1 i := by
        ext i
        simp [he]
      rw [h1, Matrix.mulVec_smul, ← hn]
      ext i
      simp
  have hleft : ∀ z w : Fin d → B,
      (fun i => z i ⊗ₜ[A] (1 : B)) = (fun i => w i ⊗ₜ[A] (1 : B)) → z = w := by
    intro z w h
    ext i
    simpa using congrArg (Algebra.TensorProduct.lmul' A (S := B)) (congrFun h i)
  change Function.Bijective (N.subtype.liftBaseChange B)
  constructor
  · intro x y hxy
    have h := key x
    rw [hxy, key y] at h
    exact (Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
      (e.injective (hεinj h))).symm
  · intro z
    obtain ⟨y, hy⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hε (fun i => z i ⊗ₜ[A] (1 : B))
    have hex := Module.Flat.lTensor_exact B (LinearMap.exact_subtype_ker_map (defect ε))
    have h0 : (defect ε).lTensor B (e.symm y) = 0 := by
      apply (piRight A A B (fun _ : Fin d => B ⊗[A] B)).injective
      rw [lTensor_defect, map_zero, sub_eq_zero, ← he, e.apply_symm_apply]
      set i₁₂ := Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B) with h12
      set i₁₃ := Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B) with h13
      have hu : IsUnit (ε.map i₁₂) := hε.map (i₁₂.toRingHom.mapMatrix)
      apply Matrix.mulVec_injective_of_isUnit hu
      rw [Matrix.mulVec_mulVec, hc]
      ext i
      have a := RingHom.map_mulVec i₁₂.toRingHom ε y i
      have b := RingHom.map_mulVec i₁₃.toRingHom ε y i
      refine a.symm.trans (Eq.trans ?_ b)
      rw [hy]
      simp [h12, h13, ← Algebra.TensorProduct.one_def]
    obtain ⟨x, hx⟩ := (hex _).mp h0
    refine ⟨x, hleft _ _ ?_⟩
    rw [key, ← hy]
    congr 1
    rw [← e.apply_symm_apply y, ← hx]

theorem descent (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    (d : ℕ) (ε : Matrix (Fin d) (Fin d) (B ⊗[A] B)) (hε : IsUnit ε)
    (hc : ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)) *
      ε.map (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)) =
      ε.map (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)))
    (N : Submodule A (Fin d → B))
    (hN : ∀ z, z ∈ N ↔ (fun i => z i ⊗ₜ[A] (1 : B)) = ε.mulVec fun i => (1 : B) ⊗ₜ[A] z i) :
    Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  have hk : N = LinearMap.ker (defect ε) := by
    ext z
    rw [hN, LinearMap.mem_ker, defect_apply, sub_eq_zero]
  have hb : IsBaseChange B N.subtype := hk ▸ isBaseChange ε hε hc
  have : Module.Finite B (B ⊗[A] N) := Module.Finite.equiv hb.equiv.symm
  have : Module.Projective B (B ⊗[A] N) := Module.Projective.of_equiv hb.equiv.symm
  exact ⟨GlobalTheory.Descent.finite B, GlobalTheory.Descent.projective B, hb⟩

end GlobalTheory.CocycleDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1Reduction
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.CocycleModPow

theorem finite_H1Q_lpow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)), Finite (QuotientCohomology LA _ hI) := by
  intro hT l _ K LL _ _ _ O _ _ hO A LA r hI
  obtain ⟨⟨hdom, hdvr, hfrac⟩, hrest⟩ := id hO
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl : ((l : ℕ) : O) ≠ 0 := by
    intro h0
    have h1 : algebraMap O LL ((l : ℕ) : O) = 0 := by rw [h0, map_zero]
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[l] LL)] at h1
    have h2 : ((l : ℕ) : ℚ_[l]) = 0 := (algebraMap ℚ_[l] LL).injective (by rw [h1, map_zero])
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h2
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible (pow_ne_zero r hl) hϖ
  have hspan : Ideal.span {((l : ℕ) : O) ^ r} = Ideal.span {ϖ ^ m} :=
    Ideal.span_singleton_eq_span_singleton.2 hm
  have key : ∀ (I : Submodule O ↥LA.T) (hI' : StableSub LA I),
      I = (Ideal.span {ϖ ^ m} • ⊤ : Submodule O ↥LA.T) → Finite (QuotientCohomology LA I hI') := by
    rintro I hI' rfl
    have hZ := finite_Z1Q hT l K LL O hO A LA ϖ hϖ m hI'
    have : Finite ↥(quotientCocycles LA _ hI') := hZ.to_subtype
    exact Finite.of_surjective _ (Submodule.mkQ_surjective _)
  exact key _ hI (by rw [hspan])

end GlobalTheory.CocycleModPow
end

