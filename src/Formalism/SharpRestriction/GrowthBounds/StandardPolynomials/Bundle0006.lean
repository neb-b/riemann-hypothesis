module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MultidegAdd
public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.MonomialSumEqProdTensor

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.IdentityLiftWeightedHomog
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

abbrev VarH (X : Loc) := (X.TT × Bool) × Fin (X.m + 1)

def wN (X : Loc) : VarH X → ℕ := fun v =>
  if (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1) then 1 else 0

def dX {X : Loc} (x l : X.TT × Bool) : ℕ := if x = l then 1 else 0

def wL (X : Loc) (l : X.TT × Bool) : VarH X → ℕ := fun v => dX v.1 l

section Grad

variable {X : Loc}

theorem wN_pos {v : VarH X} (h : (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1)) : wN X v = 1 := if_pos h

theorem wN_neg {v : VarH X} (h : ¬ ((v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1))) : wN X v = 0 := if_neg h

theorem ndM_eq (m : MonH X) : ndM X m = Finsupp.weight (wN X) m := by
  classical
  unfold ndM degUS
  rw [Finsupp.weight_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases h : (v.1.2 = true ∧ 1 ≤ v.2.val) ∨ (v.1.2 = false ∧ v.2.val < 1)
  · have h' : ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) := h
    rw [if_pos h', wN_pos h, smul_eq_mul, mul_one]
  · have h' : ¬ (((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1)) := h
    rw [if_neg h', wN_neg h, smul_eq_mul, mul_zero]

theorem multideg_eq (m : MonH X) (l : X.TT × Bool) : multideg m l = Finsupp.weight (wL X l) m := by
  classical
  unfold multideg
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun _ => by simp), Fintype.sum_prod_type,
    Finset.sum_eq_single l]
  · simp [wL, dX]
  · intro b _ hb
    simp [wL, dX, hb]
  · intro h; exact absurd (Finset.mem_univ l) h

variable {K : Type} [CommRing K]

theorem mem_Pol_iff {d : X.TT × Bool → ℕ} {P : MvPolynomial (VarH X) K} :
    P ∈ Pol K (ι := X.TT × Bool) (X.m + 1) d ↔ ∀ l, IsWeightedHomogeneous (wL X l) P (d l) := by
  unfold Pol
  rw [MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h l m hm
    rw [← multideg_eq]
    exact h (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 hm)) l
  · intro h m hm l
    rw [multideg_eq]
    exact h l (MvPolynomial.mem_support_iff.1 (Finset.mem_coe.1 hm))

theorem ndHom_iff {o : ℕ} {P : MvPolynomial (VarH X) K} :
    (∀ m ∈ P.support, ndM X m = o) ↔ IsWeightedHomogeneous (wN X) P o := by
  constructor
  · intro h m hm
    rw [← ndM_eq]
    exact h m (MvPolynomial.mem_support_iff.2 hm)
  · intro h m hm
    rw [ndM_eq]
    exact h (MvPolynomial.mem_support_iff.1 hm)

end Grad

section Int

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem X_int (v : σ) : (MvPolynomial.X v : MvPolynomial σ (KK O)) ∈ intSub O σ := X_mem_goodSub v rfl

end Int

section Lift

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O]

theorem identity_lift_X (w : O) (v : VarH X) :
    lift1 X O w (MvPolynomial.X v) = (w ^ wN X v) • (MvPolynomial.X v : RHH O X) := by
  obtain ⟨x, b⟩ := v
  show liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 (MvPolynomial.X (x, b)) = _
  rw [liftSubst_one_hh]
  by_cases h : (x.2 = true ∧ 1 ≤ (b : ℕ)) ∨ (x.2 = false ∧ (b : ℕ) < 1)
  · rw [if_pos h, C_mul_eq_smul, wN_pos (v := (x, b)) h, pow_one]
  · rw [if_neg h, wN_neg (v := (x, b)) h, pow_zero, one_smul]

theorem identity_lift_monomial (w : O) (M : MonH X) :
    lift1 X O w (monomial M 1) = (w ^ ndM X M) • (monomial M 1 : RHH O X) := by
  classical
  induction M using Finsupp.induction_linear with
  | zero =>
    have : ndM X (0 : MonH X) = 0 := degUS_zero _ _
    rw [this]
    simp
  | add f g hf hg =>
    have e : (monomial (f + g) 1 : RHH O X) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [e, map_mul, hf, hg, ndM_add, pow_add, smul_mul_smul_comm]
  | single a b =>
    have e : (monomial (Finsupp.single a b) 1 : RHH O X) = MvPolynomial.X a ^ b := (X_pow_eq_monomial).symm
    have hn : ndM X (Finsupp.single a b) = b * wN X a := by
      rw [ndM_eq, Finsupp.weight_apply, Finsupp.sum_single_index (by simp)]
      simp
    rw [e, map_pow, identity_lift_X, smul_pow, hn, ← pow_mul, mul_comm]

theorem identity_lift_eq_sum (w : O) (P : RHH O X) :
    lift1 X O w P = ∑ m ∈ P.support, monomial m (algebraMap O (KK O) (w ^ ndM X m) * P.coeff m) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (monomial m (P.coeff m) : RHH O X) = C (P.coeff m) * monomial m 1 := by
    rw [C_mul_monomial, mul_one]
  rw [e, map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, identity_lift_monomial, ← C_mul_eq_smul, C_mul_monomial,
    C_mul_monomial, mul_one, mul_comm]

theorem identity_lift_weighted_homog (w : O) {wt : VarH X → ℕ} {n : ℕ} {P : RHH O X} (h : IsWeightedHomogeneous wt P n) :
    IsWeightedHomogeneous wt (lift1 X O w P) n := by
  rw [identity_lift_eq_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  exact isWeightedHomogeneous_monomial wt m _ (h (MvPolynomial.mem_support_iff.1 hm))

theorem identity_lift_mem_Pol (w : O) {d : X.TT × Bool → ℕ} {P : RHH O X}
    (h : P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d) :
    lift1 X O w P ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) d :=
  mem_Pol_iff.2 fun l => identity_lift_weighted_homog w (mem_Pol_iff.1 h l)

theorem identity_lift_normal_homog (w : O) {o : ℕ} {P : RHH O X} (h : IsWeightedHomogeneous (wN X) P o) :
    lift1 X O w P = (w ^ o) • P := by
  rw [identity_lift_eq_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [ndM_eq, h (MvPolynomial.mem_support_iff.1 hm), ← C_mul_eq_smul, C_mul_monomial]

end Lift

section FacCalc

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem inWjRg_zero_of_inA (w : O) {f : RHH O X} (hf : InA f)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g) :
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f 0 := by
  intro m
  obtain ⟨a, ha⟩ := lift_substitution_coeff_divisible X.p X.n' O w (hhLetters X.TT) 1 g hg f hf m
  exact ⟨w ^ degUS (hhLetters X.TT) 1 m * a, by rw [ha, pow_zero, one_mul]⟩

theorem IsFac.one (w : O) : IsFac (X := X) w (1 : RHH O X) 0 1 := by
  have hInt : InA (1 : RHH O X) := (inA_iff_wj w).2 (inWj_one w)
  refine ⟨hInt, ?_, ?_, hInt⟩
  · intro g _
    unfold InWjRg
    rw [map_one]
    exact inWj_one w
  · rw [map_one, pow_zero, one_smul, sub_self]
    exact (wjSub w _).zero_mem

theorem IsFac.pow {w : O} {f sg : RHH O X} {o : ℕ} (h : IsFac w f o sg) (u : ℕ) : IsFac w (f ^ u) (u * o) (sg ^ u) := by
  induction u with
  | zero => simpa using IsFac.one (X := X) w
  | succ u ih =>
    have := ih.mul h
    rw [pow_succ, pow_succ]
    have e : u * o + o = (u + 1) * o := by ring
    rwa [e] at this

theorem IsFac.congr_sg {w : O} {f sg sg' : RHH O X} {o : ℕ} (h : IsFac w f o sg) (h' : InWj w (sg - sg') 1)
    (hi : InA sg') : IsFac w f o sg' := by
  refine ⟨h.inA, h.ord, ?_, hi⟩
  have e : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg' =
      (liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f - (w ^ o) • sg) + (w ^ o) • (sg - sg') := by
    rw [smul_sub]; abel
  rw [e]
  have := wj_smul_pow h' o
  rw [add_comm 1 o] at this
  exact (wjSub w (o + 1)).add_mem h.sym this

theorem IsFac.of_exact {w : O} {f sg r : RHH O X} {o e : ℕ} (hA : InA f)
    (hord : ∀ g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g →
      InWjRg X.p X.n' O w 1 (hhLetters X.TT) g f o)
    (he : 1 ≤ e) (hs : InA sg) (hr : InA r)
    (hl : liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1 f = (w ^ o) • (sg + (w ^ e) • r)) : IsFac w f o sg := by
  refine ⟨hA, hord, ?_, hs⟩
  rw [hl, smul_add, add_sub_cancel_left, smul_smul, ← pow_add]
  have := wj_smul_pow ((inA_iff_wj w).1 hr) (o + e)
  rw [zero_add] at this
  exact wj_mono (by omega) this

end FacCalc

structure SoftOK {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (w : O) (f : RHH O X) (od : ℕ) (sg : RHH O X) (dg : X.TT × Bool → ℕ) : Prop where
  fac : IsFac w f od sg
  sgHom : ∀ m ∈ sg.support, ndM X m = od
  liftPol : lift1 X O w f ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg
  sgPol : sg ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SumMulLe
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mu : ℝ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 mu X β} {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

abbrev PreSys.κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : Type :=
  (Σ j, P.ιC j) ⊕ ((Σ j, Fin (BDk C0 CE1 CE2 mu X β j).T.t) ⊕ P.ιM)

def PreSys.mult (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun _ => 1) (Sum.elim (fun x => L.lv x.1 x.2) P.multM)

def PreSys.f (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.fC x.1 x.2) (Sum.elim (fun x => P.fH x.1 x.2) P.fM)

def PreSys.sg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → RHH O X :=
  Sum.elim (fun x => P.sgC x.1 x.2) (Sum.elim (fun x => P.sgH x.1 x.2) (fun a => monomial (P.aM a) 1))

def PreSys.od (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → ℕ :=
  Sum.elim (fun x => P.oC x.1 x.2) (Sum.elim (fun x => P.oH x.1 x.2) P.oM)

def PreSys.dg (P : PreSys C0 CE1 CE2 X O w mu β L G Std) : P.κ → X.TT × Bool → ℕ :=
  Sum.elim (fun x => P.dgC x.1 x.2) (Sum.elim (fun x => P.dgH x.1 x.2) P.dgM)

theorem PreSys.prod_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → RHH O X) :
    ∏ a, F a = (∏ j, ∏ a, F (Sum.inl ⟨j, a⟩)) * ((∏ j, ∏ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) * ∏ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_sigma]

theorem PreSys.sum_κ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (F : P.κ → ℕ) :
    ∑ a, F a = (∑ j, ∑ a, F (Sum.inl ⟨j, a⟩)) + ((∑ j, ∑ i, F (Sum.inr (Sum.inl ⟨j, i⟩))) + ∑ a, F (Sum.inr (Sum.inr a))) := by
  simp only [Fintype.sum_sum_type, Fintype.sum_sigma]

theorem sum_mul_le {κ : Type} [Fintype κ] (u d : κ → ℕ) (Q : ℕ) (h : ∀ a, d a ≤ Q) : ∑ a, u a * d a ≤ (∑ a, u a) * Q := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (h a)

theorem PreSys.sgNd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) : HomW (ndHom X) (P.od a) (P.sg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.homC j i
  · exact P.homH j i
  · show HomW (ndHom X) (P.oM a) (monomial (P.aM a) (1 : KK O))
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm)
    subst hm'
    exact P.homM a

theorem PreSys.sgMd (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) :
    P.sg a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dg a) := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.polC j i
  · exact P.polH j i
  · show monomial (P.aM a) (1 : KK O) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (P.dgM a)
    rw [Pol, MvPolynomial.mem_restrictSupport_iff]
    intro m hm
    have hm' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm))
    subst hm'
    exact P.polM a

theorem PreSys.dgQ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (l : X.TT × Bool) : P.dg a l ≤ X.p ^ X.G' := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCQ j i l
  · exact P.dgHQ j i l
  · exact P.dgMQ a l

theorem PreSys.dgY (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (a : P.κ) (j' : Fin (numSeg X.TT)) :
    P.dg a (topEnd X j', false) = 0 := by
  rcases a with ⟨j, i⟩ | ⟨j, i⟩ | a
  · exact P.dgCY j i j'
  · exact P.dgHY j i j'
  · exact P.dgMY a j'

theorem PreSys.ordκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    P.oR + ∑ a, P.mult a * P.od a = ordFam C0 CE1 CE2 X β := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.od, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.ordEq

theorem PreSys.degκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std) (l : X.TT × Bool) :
    P.dR l + ∑ a, P.mult a * P.dg a l = hhDegs X.TT X.aT X.bT l := by
  rw [P.sum_κ]
  simp only [PreSys.mult, PreSys.dg, Sum.elim_inl, Sum.elim_inr, one_mul]
  exact P.degEq l

theorem PreSys.fprod (P : PreSys C0 CE1 CE2 X O w mu β L G Std) :
    ∏ a, P.f a ^ P.mult a = (∏ j, ∏ a, P.fC j a) * ((∏ j, ∏ i, P.fH j i ^ L.lv j i) * ∏ a, P.fM a ^ P.multM a) := by
  rw [P.prod_κ]
  simp only [PreSys.f, PreSys.mult, Sum.elim_inl, Sum.elim_inr, pow_one]

theorem PreSys.symκ (P : PreSys C0 CE1 CE2 X O w mu β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j) :
    P.sgR * ∏ a, P.sg a ^ P.mult a = symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) := by
  have hsym : symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j)) =
      (∏ j, L.head O j (L.lv j) (G j)) * monomial Std 1 := by
    rw [hStd, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => L.ioBlock_word O j (G j))
  have h1 := P.ident (fun _ _ => 1) L.lv P.multM 0
  have h2 : P.R + ((∑ j, ∑ a, (1 : ℕ) • P.pl j a) + ∑ a, P.multM a • P.aM a) + 0 = Std := by
    refine Eq.trans ?_ P.stdEq.symm
    simp
  have h3 : ∀ j, ∏ a, P.Kc j a ^ (1 : ℕ) = G j := fun j => by simp [P.Kprod j]
  rw [h2] at h1
  simp only [h3] at h1
  rw [hsym, ← h1, P.prod_κ]
  simp [PreSys.mult, PreSys.sg]

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
end
end

