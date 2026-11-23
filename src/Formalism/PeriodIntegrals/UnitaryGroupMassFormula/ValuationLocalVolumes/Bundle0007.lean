module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OrbAllOfOrthoB

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.CountPOf
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def clsP (a : ℕ) (ϖ : Fv F v) (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    Set (lamA v Λ a ⧸ (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a)) :=
  QuotientAddGroup.mk '' {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
    (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ T}

def MeasP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    MeasurableAdd (TupV (E := E) v n a) ∧ MeasurableSet (LamT v Λ a) ∧
      MeasurableSet (lamP v Λ a ϖ : Set (TupV (E := E) v n a))

def IdxP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lamP v Λ a ϖ).relIndex (lamA v Λ a) = (Ideal.absNorm v.asIdeal) ^ (2 * n * a)

def ClsP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodP σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ℝ) =
      qv v ^ (2 * n * a - a ^ 2) * prodEtaB (E := E) v n a

theorem countP_of (a : ℕ) (Y : TupV (E := E) v n a) (hM : MeasP σ J ψ v Λ a Y)
    (hI : IdxP σ J ψ v Λ a Y) (hC : ClsP σ J ψ v Λ a Y) (hPC : PrimCos σ J ψ v Λ a) : CountP σ J ψ v Λ a Y := by
  intro hG hμ ϖ hϖ
  obtain ⟨hMA, hL, hP⟩ := hM hG ϖ hϖ
  have hSD : IsSDLoc σ J v Λ := hG.2.2.1
  have hcos : ∀ x ∈ PrimT v Λ a, ∀ Z ∈ LamT v Λ a, x + sc (E := E) v ϖ • Z ∈ PrimT v Λ a := by
    intro x hx Z hZ
    apply hPC hG.1 hG.2.1 hSD hG.2.2.2.1 ϖ hϖ x hx
    refine (PI.VolStabSW.mem_smulSub _ _ _).2 ⟨Z, hZ, ?_⟩
    funext i p
    show ϖ ^ (0 + 1) • Z i p = sc (E := E) v ϖ * Z i p
    rw [zero_add, pow_one, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have ha : a ≤ n := hG.2.2.2.2.1
  have hq := qv_pos v
  set μ := dX σ J ψ v a with hμdef
  have : μ.IsAddHaarMeasure := by
    rw [hμdef, dX, dite_eq_left hμ]
    exact hμ.choose_spec.1
  have hPL : lamP v Λ a ϖ ≤ lamA v Λ a := by
    rintro _ ⟨Z, hZ, rfl⟩ i
    have : (sc (E := E) v ϖ • Z) i = sc (E := E) v ϖ • Z i := rfl
    show (sc (E := E) v ϖ • Z) i ∈ latLoc (E := E) v Λ
    rw [this]
    have e : sc (E := E) v ϖ • Z i = (⟨ϖ, unif_int v hϖ⟩ : v.adicCompletionIntegers F) • Z i := by
      ext p
      simp only [Pi.smul_apply, smul_eq_mul]
      show _ = ϖ • Z i p
      rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
      rfl
    rw [e]
    exact (latLoc (E := E) v Λ).smul_mem _ (hZ i)
  have hIdx := hI hG ϖ hϖ
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    intro h0
    have : qv v = 0 := by simp [qv, h0]
    linarith
  have hfin : (lamP v Λ a ϖ).relIndex (lamA v Λ a) ≠ 0 := by
    rw [hIdx]; exact pow_ne_zero _ hN0
  have eL := PI.VolStabSW.measure_eq_relIndex_mul μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hL hP hfin
  have eS := measure_image_cosets μ (lamP v Λ a ϖ) (lamA v Λ a) hPL hP hfin
    {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
      (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)}
    (by
      rintro x hx y ⟨Z, hZ, hZe⟩
      simp only [Set.mem_setOf_eq]
      rw [AddSubgroup.coe_add, ← hZe]
      exact ⟨hcos _ hx.1 Z hZ, nearT_add σ J v Λ hSD hϖ _ _ _ x.2 hZ hx.2⟩)
  have himg : ((↑) : lamA v Λ a → TupV (E := E) v n a) ''
      {x : lamA v Λ a | (x : TupV (E := E) v n a) ∈ PrimT v Λ a ∧
        (x : TupV (E := E) v n a) ∈ NearT v σ J ϖ (gramR (Fv F v) σ J Y)} =
      PrimT v Λ a ∩ NearT v σ J ϖ (gramR (Fv F v) σ J Y) := by
    ext X
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · rintro ⟨h1, h2⟩
      exact ⟨⟨X, h1.1⟩, ⟨h1, h2⟩, rfl⟩
  rw [himg] at eS
  have eL' : μ (LamT v Λ a) = (((lamP v Λ a ϖ).relIndex (lamA v Λ a) : ℕ) : ENNReal) *
      μ (lamP v Λ a ϖ) := eL
  rw [eS, eL', ← mul_assoc]
  congr 1
  have hcard := hC hG ϖ hϖ
  change (Nat.card (clsP σ J v Λ a ϖ (gramR (Fv F v) σ J Y)) : ENNReal) = _
  rw [← ENNReal.ofReal_natCast, hcard, hIdx, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul]
  · congr 1
    have hqv : ((Ideal.absNorm v.asIdeal ^ (2 * n * a) : ℕ) : ℝ) = qv v ^ (2 * n * a) := by
      simp [qv]
    rw [hqv]
    have hle : a ^ 2 ≤ 2 * n * a := by nlinarith
    have e3 : qv v ^ (2 * n * a) = qv v ^ (2 * n * a - a ^ 2) * qv v ^ (a ^ 2) := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [e3]
    have e4 : qv v ^ (-((a : ℤ) ^ 2)) * qv v ^ (a ^ 2) = 1 := by
      rw [zpow_neg, show ((a : ℤ) ^ 2) = ((a ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
      exact inv_mul_cancel₀ (pow_ne_zero _ hq.ne')
    linear_combination (-(qv v ^ (2 * n * a - a ^ 2) * prodEtaB (E := E) v n a)) * e4
  · have hP0 : 0 ≤ prodEtaB (E := E) v n a := by
      unfold prodEtaB
      refine Finset.prod_nonneg fun j _ => ?_
      have hq1 : (1 : ℝ) ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
      have habs : |((etaV (E := E) v : ℤ) : ℝ)| = 1 := by
        unfold etaV; split_ifs <;> norm_num
      have h1 : ((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) ≤ 1 := by
        calc _ ≤ |((etaV (E := E) v : ℤ) : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))| :=
              le_abs_self _
          _ = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ)) := by
              rw [abs_mul, abs_pow, habs, one_pow, one_mul, abs_of_nonneg (zpow_nonneg (by linarith) _)]
          _ ≤ 1 := zpow_le_one_of_nonpos₀ hq1 (by omega)
      linarith
    exact mul_nonneg (zpow_nonneg hq.le _) hP0

end PI.OmVd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulRight
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))

theorem sigR_alg (c : Fv F v) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (algebraMap (Fv F v) (Fv F v ⊗[F] E) c) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sigR_tmul_one]

theorem hR_smul_right (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_smul_left (c : Fv F v) (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (c • x) y = c • hR (Fv F v) σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def, Finset.mul_sum, map_mul, sigR_alg]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hR_add_right (x y y' : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (y + y') = hR (Fv F v) σ J x y + hR (Fv F v) σ J x y' := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hR_add_left (x x' y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (x + x') y = hR (Fv F v) σ J x y + hR (Fv F v) σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hR_zero_right (x : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J x 0 = 0 := by
  simp [hR, Formalism.UG.hform]

theorem hR_zero_left (y : Fin n → Fv F v ⊗[F] E) : hR (Fv F v) σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]

theorem oev_smul {c : v.adicCompletionIntegers F} {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) :
    (c : Fv F v) • w ∈ OEv (E := E) v :=
  Submodule.smul_mem _ c hw

theorem hR_mem_of (Λ : Set (Fin n → E))
    (hL : ∀ a ∈ Λ, ∀ b ∈ Λ, ∃ o : 𝓞 E, hE σ J a b = (o : E))
    {x y : Fin n → Fv F v ⊗[F] E} (hx : x ∈ latLoc (E := E) v Λ) (hy : y ∈ latLoc (E := E) v Λ) :
    hR (Fv F v) σ J x y ∈ OEv (E := E) v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, hb, rfl⟩ := hy
      obtain ⟨o, ho⟩ := hL a ha b hb
      have h' : hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) =
          inclR (Fv F v) (hE σ J a b) := hR_ratTup (Fv F v) σ J ![a, b] 0 1
      change hR (Fv F v) σ J (fun i => inclR (Fv F v) (a i)) (fun i => inclR (Fv F v) (b i)) ∈ _
      rw [h', ho]
      exact Submodule.subset_span ⟨o, trivial, rfl⟩
    | zero => rw [hR_zero_right]; exact Submodule.zero_mem _
    | add y y' _ _ h1 h2 => rw [hR_add_right]; exact Submodule.add_mem _ h1 h2
    | smul c y _ h =>
      change hR (Fv F v) σ J _ ((c : Fv F v) • y) ∈ _
      rw [hR_smul_right]; exact oev_smul v h
  | zero => rw [hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv F v) σ J ((c : Fv F v) • x) _ ∈ _
    rw [hR_smul_left]; exact oev_smul v h

end Gen

variable {D : D7} (X : HidaSetting D)

theorem hE_L (a : Fin X.B.I.n → X.B.I.E) (ha : a ∈ abelian₂ X) (b : Fin X.B.I.n → X.B.I.E) (hb : b ∈ abelian₂ X) :
    ∃ o : 𝓞 X.B.I.E, hE X.B.I.cm.sig X.B.I.J a b = (o : X.B.I.E) := by
  obtain ⟨o, ho⟩ := (X.B.I.L_dual b).1 hb a ha
  exact ⟨o, ho.symm⟩

theorem omVSD_fwd (v : PlX X) {x y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E}
    (hx : x ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) (hy : y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v :=
  hR_mem_of X.B.I.cm.sig X.B.I.J v (abelian₂ X) (hE_L X) hx hy

def OmVSDBwd : Prop :=
  ∀ (v : PlX X) (y : Fin X.B.I.n → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E),
    (∀ x ∈ latLoc (E := X.B.I.E) v (abelian₂ X), hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J x y ∈ OEv (E := X.B.I.E) v) →
      y ∈ latLoc (E := X.B.I.E) v (abelian₂ X)

theorem omVSD_of (h : OmVSDBwd X) : OmVSD X := fun v y =>
  ⟨fun hy x hx => omVSD_fwd X v hx hy, h v y⟩

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.InclRMemOEv
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def piv (r : ℕ) (a : Fin (r + 1 + r)) : Fin (r + 1 + r) :=
  ⟨if a.val < r then a.val + (r + 1) else if a.val = r then r else a.val - (r + 1), by
    have := a.2; split_ifs <;> omega⟩

theorem piv_e (r : ℕ) (i : Fin r) : piv r (Fin.castAdd r i.castSucc) = Fin.natAdd (r + 1) i := by
  apply Fin.ext; simp [piv]; omega

theorem pivot_castAdd_last (r : ℕ) : piv r (Fin.castAdd r (Fin.last r)) = Fin.castAdd r (Fin.last r) := by
  apply Fin.ext; simp [piv]

theorem piv_f (r : ℕ) (i : Fin r) : piv r (Fin.natAdd (r + 1) i) = Fin.castAdd r i.castSucc := by
  apply Fin.ext
  simp only [piv, Fin.val_natAdd, Fin.val_castAdd, Fin.val_castSucc]
  rw [if_neg (by omega), if_neg (by omega)]
  omega

theorem piv_invol (r : ℕ) : Function.Involutive (piv r) := by
  intro a
  refine Fin.addCases (fun a => ?_) (fun i => by rw [piv_f, piv_e]) a
  exact Fin.lastCases (by rw [pivot_castAdd_last, pivot_castAdd_last]) (fun i => by rw [piv_e, piv_f]) a

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem hT_hv (a b : Fin (D.R.rS + 1 + D.R.rS)) :
    (VS D).hT (hv X u' a) (hv X u' b) =
      if b = piv D.R.rS a then (if a.val = D.R.rS then -((Tw u' : ℕ) : D.host.E) else 1) else 0 := by
  have hs := (VS D).herm
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) b
  · refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [pivot_castAdd_last, if_pos rfl, if_pos (by simp)]
      simp only [hv, Fin.append_left, Fin.snoc_last]
      rw [X.zu_norm]; rfl
    · rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]
      exact (hs.eq_iff).1 (X.zu_orth u' j).1
    · rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_last, Fin.snoc_castSucc]
      exact (X.zu_orth u' i).1
    · rw [piv_e, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.snoc_castSucc]
      exact X.ee i j
  · refine Fin.lastCases ?_ (fun i => ?_) a
    · rw [pivot_castAdd_last, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]
      exact (hs.eq_iff).1 (X.zu_orth u' b).2
    · rw [piv_e]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
      rw [X.ef]
      by_cases h : i = b
      · subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega)]
      · rw [if_neg h, if_neg (fun e => h ((Fin.natAdd_inj _).1 e).symm)]
  · refine Fin.lastCases ?_ (fun j => ?_) b
    · rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_last]
      exact (X.zu_orth u' a).2
    · rw [piv_f]
      simp only [hv, Fin.append_left, Fin.append_right, Fin.snoc_castSucc]
      rw [← (LinearMap.isSymm_def.1 hs) (X.eX j) (X.fY a), X.ef]
      by_cases h : j = a
      · subst h; rw [if_pos rfl, if_pos rfl, if_neg (by simp <;> omega), map_one]
      · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_inj.1 (Fin.castAdd_inj.1 e))), map_zero]
  · rw [piv_f, if_neg (fun h => by have := congrArg Fin.val h; simp at this <;> omega)]
    simp only [hv, Fin.append_right]
    exact X.ff a b

def cD (a : Fin (D.R.rS + 1 + D.R.rS)) : X.B.I.E := if a.val = D.R.rS then -((Tw u' : ℕ) : X.B.I.E) else 1

theorem gram_eq : gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) =
    diagonal (cD X u') * (Function.Involutive.toPerm _ (piv_invol D.R.rS)).permMatrix X.B.I.E := by
  ext a b
  rw [diagonal_mul]
  show hE _ _ (tupH (frameOf X u') a) (tupH (frameOf X u') b) = _
  rw [tupH_eq, tupH_eq, hE_crdOf, hT_hv]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,
    Option.some.injEq, Function.Involutive.coe_toPerm, cD]
  by_cases h : b = piv D.R.rS a
  · have h' : piv D.R.rS a = b := h.symm
    rw [if_pos h]
    simp only [h', if_true, mul_one]
    split_ifs <;> simp
  · have h' : ¬ piv D.R.rS a = b := fun e => h e.symm
    simp [h, h']

theorem prod_cD : ∏ a, cD X u' a = -((Tw u' : ℕ) : X.B.I.E) := by
  rw [Finset.prod_eq_single (⟨D.R.rS, by omega⟩ : Fin (D.R.rS + 1 + D.R.rS))]
  · simp [cD]
  · intro b _ hb
    have : b.val ≠ D.R.rS := fun e => hb (Fin.ext e)
    simp [cD, this]
  · simp

theorem det_gram : ∃ s : ℤ, s * s = 1 ∧
    (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).det = (((-(Tw u' : ℤ)) * s : ℤ) : X.B.I.E) := by
  refine ⟨((Equiv.Perm.sign (Function.Involutive.toPerm _ (piv_invol D.R.rS)) : ℤˣ) : ℤ), ?_, ?_⟩
  · rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  · rw [gram_eq, det_mul, det_diagonal, det_permutation, prod_cD]
    push_cast
    rfl

theorem val_natCast_eq_one {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t : ℕ)
    (ht : ((t : 𝓞 F)) ∉ v.asIdeal) : Valued.v ((t : ℕ) : Fv F v) = 1 := by
  have h1 : ((t : ℕ) : Fv F v) = algebraMap (𝓞 F) (Fv F v) (t : 𝓞 F) := by simp
  rw [h1]
  refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (t : 𝓞 F)).trans ?_
  erw [HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 ht

theorem inclR_mem_OEv (v : PlX X) (x : 𝓞 X.B.I.E) :
    inclR (Fv X.B.I.F v) (x : X.B.I.E) ∈ OEv (E := X.B.I.E) v :=
  Submodule.subset_span ⟨x, trivial, rfl⟩

theorem omVDet_holds : OmVDet X u' := by
  intro v hT
  obtain ⟨s, hs, hd⟩ := det_gram X u'
  have hdet : (localGramMatrixFrame X u' v).det = inclR (Fv X.B.I.F v) ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
    rw [localGramMatrixFrame, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hd]
    push_cast; rfl
  set t : Fv X.B.I.F v := ((Tw u' : ℕ) : Fv X.B.I.F v) with ht_def
  have hv1 : Valued.v t = 1 := val_natCast_eq_one v _ hT
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  refine ⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E),
    Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_, ?_⟩
  · rw [hdet]; exact inclR_mem_OEv X v _
  · rw [hdet]
    have e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
        algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ *
          inclR (Fv X.B.I.F v) (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
      rw [← Algebra.smul_def]; rfl
    rw [e1, mul_left_comm, ← map_mul]
    have e2 : ((((-(Tw u' : ℤ)) * s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) * (((-s : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
        ((Tw u' : ℕ) : X.B.I.E) := by
      have : (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ) := by
        calc (-(Tw u' : ℤ)) * s * (-s) = (Tw u' : ℤ) * (s * s) := by ring
          _ = (Tw u' : ℤ) := by rw [hs, mul_one]
      rw [← map_mul (algebraMap (𝓞 X.B.I.E) X.B.I.E)]
      rw [← Int.cast_mul, this]; simp
    rw [e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul,
      inv_mul_cancel₀ ht0, map_one]

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OrbPOf
section
noncomputable section

namespace PI.OmVd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU
  PI.OmLocU.Orb
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def ExtP (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  ∀ h : a ≤ n, GoodP σ J ψ v Λ a Y → ∃ G : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E),
    ∀ X ∈ PrimT v Λ a, gramR (Fv F v) σ J X = gramR (Fv F v) σ J Y →
    ∃ Z : Fin n → Fin n → Fv F v ⊗[F] E, IsOBas v Λ Z ∧ (∀ i, Z (eSp h (Sum.inl i)) = X i) ∧
      gramR (Fv F v) σ J Z = G ∧ IsUnit (colM v Z).det

theorem orbP_of (a : ℕ) (Y : TupV (E := E) v n a) (hE : ExtP σ J ψ v Λ a Y) :
    OrbP σ J ψ v Λ a Y := by
  intro hG X hX hXY
  have h : a ≤ n := hG.2.2.2.2.1
  obtain ⟨G, hGe⟩ := hE h hG
  obtain ⟨ZX, hbX, heX, hgX, hdX⟩ := hGe X hX hXY
  obtain ⟨ZY, hbY, heY, hgY, hdY⟩ := hGe Y hG.2.2.2.2.2 rfl
  set uX := Matrix.nonsingInvUnit (colM v ZX) hdX with huX
  set uY := Matrix.nonsingInvUnit (colM v ZY) hdY with huY
  set k : GL (Fin n) (Fv F v ⊗[F] E) := uX * uY⁻¹ with hk
  have hkY : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * colM v ZY = colM v ZX := by
    have : k * uY = uX := by rw [hk, inv_mul_cancel_right]
    exact congrArg Units.val this
  have hYN : colM v ZY * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 := by
    have : uY * uY⁻¹ = 1 := mul_inv_cancel uY
    exact congrArg Units.val this
  have hkval : (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = colM v ZX * ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hgXY : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX =
      cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY := by
    rw [← gram_eq_colM, ← gram_eq_colM, hgX, hgY]
  have hkU : k ∈ HR (Fv F v) σ J := by
    show cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) =
      JR (Fv F v) J
    rw [hkval]
    set N := ((uY⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    calc cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (colM v ZX * N) * JR (Fv F v) J * (colM v ZX * N)
        = cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) N * (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (colM v ZX) * JR (Fv F v) J * colM v ZX) * N := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) N * (cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (colM v ZY) * JR (Fv F v) J * colM v ZY) * N := by
          rw [hgXY]
      _ = cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (colM v ZY * N) * JR (Fv F v) J * (colM v ZY * N) := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = JR (Fv F v) J := by rw [hYN, cT_one, Matrix.one_mul, Matrix.mul_one]
  let g : HA (Fv F v) σ J := (⟨k, hkU⟩ : ↥(HR (Fv F v) σ J))
  have hgm : ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) := rfl
  have hinv : ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) * (k : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = 1 :=
    congrArg Units.val (inv_mul_cancel k)
  refine ⟨g, ?_, ?_⟩
  · show ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ
    intro x
    rw [hgm]
    constructor
    · intro hx
      obtain ⟨c, hc, rfl⟩ := (hbY x).1 hx
      refine (hbX _).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM, sum_eq_colM, mulVec_mulVec, hkY]
    · intro hx
      obtain ⟨c, hc, hxc⟩ := (hbX _).1 hx
      refine (hbY x).2 ⟨c, hc, ?_⟩
      rw [sum_eq_colM] at hxc ⊢
      rw [← hkY, ← mulVec_mulVec] at hxc
      have := congrArg (fun y => ((k⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ y) hxc
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, hinv, one_mulVec, Matrix.one_mul] using this
  · funext i
    show X i = ((HA.mat (Fv F v) σ J g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) *ᵥ Y i
    rw [hgm, ← heX i, ← heY i, col_eq_colM v ZX, col_eq_colM v ZY, mulVec_mulVec, hkY]

end PI.OmVd
end
end

