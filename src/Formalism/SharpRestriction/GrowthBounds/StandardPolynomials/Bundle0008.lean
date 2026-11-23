module

public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.CanonicalTranslateJetIdentity
public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.EqEmptyIffSplit
public import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColDef
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

def lamS (X : Loc) (j : Fin (numSeg X.TT)) : Fin (2 * segS X.TT j + 1 + 1) → X.TT × Bool :=
  Fin.cons (topStart X j, true) (fun a : Fin (2 * segS X.TT j + 1) =>
    if h : (a : ℕ) < 2 * segS X.TT j then (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0))
    else (topEnd X j, true))

def posS (X : Loc) (j : Fin (numSeg X.TT)) : Fin (2 * segS X.TT j + 1 + 1) → ℤ :=
  Fin.cons ((segStart X.TT j).val : ℤ) (fun a : Fin (2 * segS X.TT j + 1) =>
    if h : (a : ℕ) < 2 * segS X.TT j then ((segStart X.TT j).val : ℤ) + ((segDists X.TT j).get (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) : ℕ)
    else ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ))

def LLseg (X : Loc) (j : Fin (numSeg X.TT)) : LiftLetters (Fin (2 * segS X.TT j + 1 + 1)) where
  vec := fun i => (lamS X j i).2
  pos := posS X j

def zS (X : Loc) (j : Fin (numSeg X.TT)) : ℤ := ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ)

def phiS (X : Loc) (j : Fin (numSeg X.TT)) :
    Fin (2 * segS X.TT j + 1 + 1) × Fin (1 + X.m) → (X.TT × Bool) × Fin (X.m + 1) :=
  fun v => (lamS X j v.1, Fin.cast (Nat.add_comm 1 X.m) v.2)

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.NormalWeightCovectorZero
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section Wts

variable {X : Loc}

theorem normal_weight_vector_zero_eq_zero (x : X.TT) : wN X ((x, true), 0) = 0 := by
  simp [wN]
theorem wN_vecS (x : X.TT) (c : Fin X.m) : wN X ((x, true), c.succ) = 1 := by
  simp [wN, Fin.val_succ]
theorem normal_weight_covector_zero (x : X.TT) : wN X ((x, false), 0) = 1 := by
  simp [wN]
theorem wN_covS (x : X.TT) (c : Fin X.m) : wN X ((x, false), c.succ) = 0 := by
  simp [wN, Fin.val_succ]

theorem wN_pair (x : X.TT) (a : Fin (X.m + 1)) : wN X ((x, true), a) + wN X ((x, false), a) = 1 := by
  unfold wN
  split_ifs <;> simp_all <;> omega

variable {K : Type} [CommRing K] {σ : Type}

theorem wh_powX (wt : σ → ℕ) (v1 v2 : σ) (a : ℕ) :
    IsWeightedHomogeneous wt ((MvPolynomial.X v1 : MvPolynomial σ K) ^ a * MvPolynomial.X v2) (a * wt v1 + wt v2) := by
  exact ((isWeightedHomogeneous_X K wt v1).pow a).mul (isWeightedHomogeneous_X K wt v2)

theorem wh_Xpow (wt : σ → ℕ) (v1 v2 : σ) (a : ℕ) :
    IsWeightedHomogeneous wt ((MvPolynomial.X v1 : MvPolynomial σ K) * MvPolynomial.X v2 ^ a) (wt v1 + a * wt v2) := by
  exact (isWeightedHomogeneous_X K wt v1).mul ((isWeightedHomogeneous_X K wt v2).pow a)

theorem wh_sub {wt : σ → ℕ} {n : ℕ} {P Q : MvPolynomial σ K} (hP : IsWeightedHomogeneous wt P n)
    (hQ : IsWeightedHomogeneous wt Q n) : IsWeightedHomogeneous wt (P - Q) n := by
  intro d hd
  rw [coeff_sub] at hd
  by_cases h : AddMonoidAlgebra.coeff P d = 0
  · rw [h, zero_sub, neg_ne_zero] at hd
    exact hQ hd
  · exact hP h

end Wts

section Soft

variable {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF X.p X.n') O]

theorem SoftOK.pow {w : O} {f sg : RHH O X} {od : ℕ} {dg : X.TT × Bool → ℕ} (h : SoftOK w f od sg dg) (u : ℕ) :
    SoftOK w (f ^ u) (u * od) (sg ^ u) (fun l => u * dg l) :=
  { fac := h.fac.pow u
    sgHom := ndHom_iff.2 (by simpa [smul_eq_mul] using (ndHom_iff.1 h.sgHom).pow u)
    liftPol := mem_Pol_iff.2 fun l => by
      rw [map_pow]
      simpa [smul_eq_mul] using (mem_Pol_iff.1 h.liftPol l).pow u
    sgPol := mem_Pol_iff.2 fun l => by simpa [smul_eq_mul] using (mem_Pol_iff.1 h.sgPol l).pow u }

def sgKS (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : RHH O X :=
  MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), 0)

def dgKS (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT × Bool → ℕ := fun l =>
  X.p ^ (segDists X.TT j).get i * dX (topStart X j, true) l + dX (topOdd X j i, false) l

theorem two_le_pd (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    1 ≤ X.p ^ (segDists X.TT j).get i - 1 := by
  have hp5 : 5 ≤ X.p := hD.2.1
  have key : ∀ d ∈ segDists X.TT j, 0 < d := by
    intro d hd
    unfold segDists at hd
    simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hd
    obtain ⟨s, hs, rfl⟩ := hd
    exact hs.2.2.1
  have hpos := key _ (List.get_mem _ i)
  have : X.p ≤ X.p ^ (segDists X.TT j).get i := Nat.le_self_pow hpos.ne' X.p
  omega

theorem kS_pol (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    kSkey O X j i ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgKS X j i) := by
  rw [mem_Pol_iff]
  intro l
  unfold kSkey
  refine IsWeightedHomogeneous.sum _ _ _ (fun a _ => ?_)
  exact wh_powX (K := KK O) (wL X l) ((topStart X j, true), a) ((topOdd X j i, false), a)
    (X.p ^ (segDists X.TT j).get i)

theorem kS_inA (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : InA (kSkey O X j i) := by
  intro m
  refine ⟨(∑ a : Fin (X.m + 1), (MvPolynomial.X ((topStart X j, true), a) : MvPolynomial (VarH X) O) ^
    (X.p ^ (segDists X.TT j).get i) * MvPolynomial.X ((topOdd X j i, false), a)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [kSkey, map_sum, map_mul, map_pow, map_X]

theorem softKS (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) :
    SoftOK S.w (kSkey O X j i) 1 (sgKS O X j i) (dgKS X j i) :=
  { fac := by
      refine IsFac.of_exact (e := X.p ^ (segDists X.TT j).get i - 1)
        (r := ∑ c : Fin X.m, MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i) *
          MvPolynomial.X ((topOdd X j i, false), c.succ)) (kS_inA j i)
        (fun g hg => (key3Ord X O S hS hD j i g hg).1) (two_le_pd hD j i) ?_ ?_ ?_
      · exact (mem_intSub O _).1 (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_int _) _) (X_int _))
      · exact (mem_intSub O _).1 (Subalgebra.sum_mem _ fun a _ =>
          Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (X_int _) _) (X_int _))
      · rw [key3One_S, pow_one]; rfl
    sgHom := ndHom_iff.2 (by
      have := wh_powX (K := KK O) (wN X) ((topStart X j, true), 0) ((topOdd X j i, false), 0)
        (X.p ^ (segDists X.TT j).get i)
      rwa [normal_weight_vector_zero_eq_zero, normal_weight_covector_zero, mul_zero, zero_add] at this)
    liftPol := identity_lift_mem_Pol _ (kS_pol j i)
    sgPol := mem_Pol_iff.2 fun l => wh_powX (wL X l) _ _ _ }

theorem softKSP (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (P : ℕ) : SoftOK S.w (kSkey O X j i ^ P) P (sgKS O X j i ^ P) (fun l => P * dgKS X j i l) := by
  have h := (softKS S hS hD j i).pow P
  rwa [mul_one] at h

def sgKW (O : Type) [CommRing O] [IsDomain O] (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin X.m) :
    RHH O X :=
  MvPolynomial.X ((topOdd X j i, true), c.succ) * MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i)

def dgKW (X : Loc) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : X.TT × Bool → ℕ := fun l =>
  dX (topOdd X j i, true) l + X.p ^ (segDists X.TT j).get i * dX (topStart X j, true) l

theorem kW_pol (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin (X.m + 1)) :
    kWkey O X j i c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgKW X j i) := by
  rw [mem_Pol_iff]
  intro l
  unfold kWkey
  exact wh_sub (wh_Xpow (K := KK O) (wL X l) _ _ _) (wh_Xpow (K := KK O) (wL X l) _ _ _)

theorem kW_inA (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) (c : Fin (X.m + 1)) : InA (kWkey O X j i c) := by
  intro m
  refine ⟨((MvPolynomial.X ((topOdd X j i, true), c) : MvPolynomial (VarH X) O) *
      MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ (segDists X.TT j).get i) -
    MvPolynomial.X ((topOdd X j i, true), 0) *
      MvPolynomial.X ((topStart X j, true), c) ^ (X.p ^ (segDists X.TT j).get i)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [kWkey, map_sub, map_mul, map_pow, map_X]

theorem softKW (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (j : Fin (numSeg X.TT)) (i : Fin (segS X.TT j))
    (c : Fin X.m) : SoftOK S.w (kWkey O X j i c.succ) 1 (sgKW O X j i c) (dgKW X j i) :=
  { fac := by
      refine IsFac.of_exact (e := X.p ^ (segDists X.TT j).get i - 1)
        (r := -(MvPolynomial.X ((topOdd X j i, true), 0) *
          MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ (segDists X.TT j).get i))) (kW_inA j i _)
        (fun g hg => (key3Ord X O S hS hD j i g hg).2 c) (two_le_pd hD j i) ?_ ?_ ?_
      · exact (mem_intSub O _).1 (Subalgebra.mul_mem _ (X_int _) (Subalgebra.pow_mem _ (X_int _) _))
      · exact (mem_intSub O _).1 (Subalgebra.neg_mem _ (Subalgebra.mul_mem _ (X_int _) (Subalgebra.pow_mem _ (X_int _) _)))
      · rw [key_lift_identity_lower, pow_one, smul_neg, ← sub_eq_add_neg]; rfl
    sgHom := ndHom_iff.2 (by
      have := wh_Xpow (K := KK O) (wN X) ((topOdd X j i, true), c.succ) ((topStart X j, true), 0)
        (X.p ^ (segDists X.TT j).get i)
      rwa [normal_weight_vector_zero_eq_zero, wN_vecS, mul_zero, add_zero] at this)
    liftPol := identity_lift_mem_Pol _ (kW_pol j i _)
    sgPol := mem_Pol_iff.2 fun l => wh_Xpow (wL X l) _ _ _ }

def sgLoc (O : Type) [CommRing O] [IsDomain O] (X : Loc) : RHH O X :=
  ∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), 0) ^ (X.p ^ segG X.TT j - 1)

def dgLoc (X : Loc) : X.TT × Bool → ℕ := fun l =>
  ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) * dX (topStart X j, true) l

theorem wh_prodStart (wt : VarH X → ℕ) (c : Fin (X.m + 1)) :
    IsWeightedHomogeneous wt
      (∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : RHH O X) ^ (X.p ^ segG X.TT j - 1))
      (∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) * wt ((topStart X j, true), c)) := by
  refine IsWeightedHomogeneous.prod _ _ _ (fun j _ => ?_)
  exact (isWeightedHomogeneous_X (KK O) wt ((topStart X j, true), c)).pow _

theorem loc_pol (c : Fin (X.m + 1)) : locC O X c ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dgLoc X) := by
  rw [mem_Pol_iff]
  intro l
  unfold locC
  exact wh_sub (wh_prodStart (O := O) (wL X l) 0) (wh_prodStart (O := O) (wL X l) c)

theorem prodStart_int (c : Fin (X.m + 1)) :
    (∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : RHH O X) ^ (X.p ^ segG X.TT j - 1)) ∈
      intSub O (VarH X) := by
  have hX : ∀ v : VarH X, (MvPolynomial.X v : RHH O X) ∈ intSub O (VarH X) := by
    intro v m
    refine ⟨if Finsupp.single v 1 = m then 1 else 0, ?_⟩
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  exact Subalgebra.prod_mem _ fun j _ => Subalgebra.pow_mem _ (hX _) _

theorem loc_inA (c : Fin (X.m + 1)) : InA (locC O X c) := by
  intro m
  refine ⟨((∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), 0) : MvPolynomial (VarH X) O) ^
      (X.p ^ segG X.TT j - 1)) -
    ∏ j : Fin (numSeg X.TT), (MvPolynomial.X ((topStart X j, true), c) : MvPolynomial (VarH X) O) ^
      (X.p ^ segG X.TT j - 1)).coeff m, ?_⟩
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp [locC, map_sub, map_prod, map_pow, map_X]

theorem one_le_Mp (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) : 1 ≤ ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1) := by
  have hn' : 2 ≤ X.n' := hD.2.2.1
  have hp5 : 5 ≤ X.p := hD.2.1
  have hj : ∀ j, 1 ≤ X.p ^ segG X.TT j - 1 := by
    intro j
    have hg : 1 ≤ segG X.TT j := by
      unfold segG
      split_ifs with h
      · omega
      · omega
    have : X.p ≤ X.p ^ segG X.TT j := Nat.le_self_pow (by omega) X.p
    omega
  have j0 : Fin (numSeg X.TT) := ⟨0, by omega⟩
  calc 1 ≤ X.p ^ segG X.TT j0 - 1 := hj j0
    _ ≤ ∑ j, (X.p ^ segG X.TT j - 1) :=
      Finset.single_le_sum (f := fun j => X.p ^ segG X.TT j - 1) (fun j _ => Nat.zero_le _)
        (Finset.mem_univ j0)

theorem softLoc (w : O) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (c : Fin X.m) :
    SoftOK w (locC O X c.succ) 0 (sgLoc O X) (dgLoc X) :=
  { fac := by
      refine IsFac.of_exact (e := ∑ j : Fin (numSeg X.TT), (X.p ^ segG X.TT j - 1))
        (r := -(∏ j : Fin (numSeg X.TT), MvPolynomial.X ((topStart X j, true), c.succ) ^ (X.p ^ segG X.TT j - 1)))
        (loc_inA _) (fun g hg => inWjRg_zero_of_inA w (loc_inA _) g hg) (one_le_Mp hD h2) ?_ ?_ ?_
      · exact (mem_intSub O _).1 (prodStart_int 0)
      · exact (mem_intSub O _).1 (Subalgebra.neg_mem _ (prodStart_int _))
      · rw [loc4One, pow_zero, one_smul, smul_neg, ← sub_eq_add_neg]; rfl
    sgHom := ndHom_iff.2 (by
      have := wh_prodStart (O := O) (wN X) 0
      simp only [normal_weight_vector_zero_eq_zero, mul_zero, Finset.sum_const_zero] at this
      exact this)
    liftPol := identity_lift_mem_Pol _ (loc_pol _)
    sgPol := mem_Pol_iff.2 fun l => wh_prodStart (wL X l) 0 }

theorem locPow_ord (S : UniformizedDVR X.p O) (hS : S.SqP) (hD : D1num X) (h2 : 2 ≤ numSeg X.TT) (j0 : Fin (numSeg X.TT))
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hg : IsGLW g)
    (hne : ratPlane X.p X.n' 1 g ≠ ratPlane X.p X.n' 1 1) (n : ℕ) :
    InWjRg X.p X.n' O S.w 1 (hhLetters X.TT) g (locR O X j0 ^ n) n := by
  have := inWjRg_pow (loc4Ord_of (loc4Div_of loc4Res) X O S hS hD h2 j0 g hg hne) n
  rwa [mul_one] at this

end Soft

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ZeroOfMultideg
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Glue

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mm : ℝ} {n : ℕ} {β : GlobalTheory X}
  {L : LvDat C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β}
  {G : ∀ j, MvPolynomial (Fin (2 * segS X.TT j + 1) × Fin X.m) (KK O)} {Std : MonH X}

theorem zero_of_multideg {l : X.TT × Bool} {M : MonH X} (h : multideg M l = 0) (c : Fin (X.m + 1)) : M (l, c) = 0 :=
  (Finset.sum_eq_zero_iff.1 h) c (Finset.mem_univ c)

theorem PreSys.core (D : Formalism.BasicNotions.D7) [CharZero (KK O)]
    (P : PreSys C0 CE1 CE2 X O w (mm + (n : ℝ) * ka1 X) β L G Std)
    (hT : TCoreBody C0 Cde CE1 CE2 X O mm n β L Std) (hG0 : ∀ j, G j ≠ 0)
    (hGY : ∀ j k, G j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
      ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k))
    (hcov : ∀ j, ∑ i, (if (L.LL j).vec i then 0 else 1) ≤ X.N1)
    (u : P.κ → ℕ) (hu : ∀ a, u a ≤ P.mult a) (M : MonH X) (e : ℕ) (he1 : 1 ≤ e) (hsum : ∑ a, u a ≤ e) (hen : e < n)
    (hdeg : ∀ l, multideg M l = ∑ a, u a * P.dg a l) (hnd : ndM X M ≤ ∑ a, u a * P.od a + e) :
    P.sgR * (∏ a, P.sg a ^ (P.mult a - u a)) * monomial M 1 ∈
      SSe C0 Cde CE1 CE2 X O mm n (ordFam C0 CE1 CE2 X β) e := by
  classical
  set uC : ∀ j, P.ιC j → ℕ := fun j a => u (Sum.inl ⟨j, a⟩) with huCdef
  set uH : ∀ j, Fin (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.t → ℕ := fun j i => u (Sum.inr (Sum.inl ⟨j, i⟩)) with huHdef
  set uM : P.ιM → ℕ := fun a => u (Sum.inr (Sum.inr a)) with huMdef
  have huC : ∀ j a, uC j a ≤ 1 := fun j a => hu (Sum.inl ⟨j, a⟩)
  have huM : ∀ a, uM a ≤ P.multM a := fun a => hu (Sum.inr (Sum.inr a))
  have hsum' : (∑ j, ∑ a, uC j a) + ((∑ j, ∑ i, uH j i) + ∑ a, uM a) ≤ e := by
    rw [← P.sum_κ u]; exact hsum
  set B : MonH X := (∑ j, ∑ a, (1 - uC j a) • P.pl j a) + ∑ a, (P.multM a - uM a) • P.aM a with hB
  set Brem : MonH X := (∑ j, ∑ a, uC j a • P.pl j a) + ∑ a, uM a • P.aM a with hBrem
  have key : P.sgR * (∏ a, P.sg a ^ (P.mult a - u a)) * monomial M 1 =
      (∏ j, L.head O j (fun i => L.lv j i - uH j i) (∏ a, P.Kc j a ^ (1 - uC j a))) * monomial (P.R + B + M) 1 := by
    rw [P.prod_κ]
    exact P.ident (fun j a => 1 - uC j a) (fun j i => L.lv j i - uH j i) (fun a => P.multM a - uM a) M
  have hSB : Std = (P.R + B) + Brem := by
    refine P.stdEq.trans ?_
    have h1 : (∑ j, ∑ a, P.pl j a) = (∑ j, ∑ a, (1 - uC j a) • P.pl j a) + ∑ j, ∑ a, uC j a • P.pl j a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.sub_add_cancel (huC j a), one_smul]
    have h2 : (∑ a, P.multM a • P.aM a) = (∑ a, (P.multM a - uM a) • P.aM a) + ∑ a, uM a • P.aM a := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← add_smul, Nat.sub_add_cancel (huM a)]
    rw [h1, h2, hB, hBrem]
    abel
  have hSv : ∀ v, Std v = (P.R + B) v + Brem v := fun v => by
    rw [← Finsupp.add_apply]; exact DFunLike.congr_fun hSB v
  have hAv : ∀ v, (P.R + B + M) v = (P.R + B) v + M v := fun v => Finsupp.add_apply _ _ v
  have hmdB : ∀ l, multideg Brem l = (∑ j, ∑ a, uC j a * multideg (P.pl j a) l) + ∑ a, uM a * multideg (P.aM a) l := by
    intro l
    have : (mdHom X l) Brem = (∑ j, ∑ a, uC j a * (mdHom X l) (P.pl j a)) + ∑ a, uM a * (mdHom X l) (P.aM a) := by
      rw [hBrem]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_add (f := _), map_sum, map_nsmul, smul_eq_mul]
    exact this
  rw [key]
  refine hT e he1 hen (fun j i => L.lv j i - uH j i) (fun j i => Nat.sub_le _ _)
    (fun j => ∏ a, P.Kc j a ^ (1 - uC j a)) (fun j i => ∑ a, (1 - uC j a) * P.dK j a i) ?_ ?_ ?_ ?_ (P.R + B + M) ?_ ?_ ?_ ?_ ?_
  · exact fun j => glIntProd _ _ fun a _ => glIntPow (P.KInt j a) _
  · exact fun j => chain_pol_prod (KK O) Finset.univ (fun a i => (1 - uC j a) * P.dK j a i) _
      fun a _ => chain_pol_pow (KK O) (P.KPol j a) _
  · intro j i
    rw [← P.dKsum j i]
    refine Finset.sum_le_sum fun a _ => ?_
    calc (1 - uC j a) * P.dK j a i ≤ 1 * P.dK j a i := Nat.mul_le_mul_right _ (Nat.sub_le 1 _)
      _ = P.dK j a i := one_mul _
  · intro j k
    have hprod : (∏ a, P.Kc j a ^ (1 - uC j a)) * (∏ a, P.Kc j a ^ uC j a) = G j := by
      rw [← Finset.prod_mul_distrib, ← P.Kprod j]
      refine Finset.prod_congr rfl fun a _ => ?_
      rw [← pow_add, Nat.sub_add_cancel (huC j a), pow_one]
    refine ycond_factor D (L.LL j) _ _ _ (∏ a, P.Kc j a ^ uC j a) (fun i => ∑ a, uC j a * P.dK j a i)
      (chain_pol_prod (KK O) Finset.univ (fun a i => uC j a * P.dK j a i) _
        fun a _ => chain_pol_pow (KK O) (P.KPol j a) _) ?_ ?_ (X.N1 * e) ?_
    · intro h0
      apply hG0 j
      rw [← hprod, h0, mul_zero]
    · rw [hprod]; exact hGY j k
    · have hCj : ∑ a, uC j a ≤ e := by
        have h1 : ∑ a, uC j a ≤ ∑ j, ∑ a, uC j a :=
          Finset.single_le_sum (f := fun j => ∑ a, uC j a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        omega
      calc ∑ i, (if (L.LL j).vec i then 0 else ∑ a, uC j a * P.dK j a i)
          ≤ ∑ i, (if (L.LL j).vec i then 0 else 1) * ∑ a, uC j a := by
            refine Finset.sum_le_sum fun i _ => ?_
            by_cases hv : (L.LL j).vec i = true
            · simp [hv]
            · simp only [hv, if_false, one_mul, Bool.false_eq_true]
              refine Finset.sum_le_sum fun a _ => ?_
              calc uC j a * P.dK j a i ≤ uC j a * 1 := Nat.mul_le_mul_left _ (P.digit_le_one j a i)
                _ = uC j a := mul_one _
        _ = (∑ i, (if (L.LL j).vec i then 0 else 1)) * ∑ a, uC j a := (Finset.sum_mul _ _ _).symm
        _ ≤ X.N1 * e := Nat.mul_le_mul (hcov j) hCj
  · intro l
    calc ∑ c, (Std (l, c) - (P.R + B + M) (l, c)) ≤ ∑ c, Brem (l, c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [hSv, hAv]; omega
      _ = multideg Brem l := rfl
      _ = (∑ j, ∑ a, uC j a * multideg (P.pl j a) l) + ∑ a, uM a * multideg (P.aM a) l := hmdB l
      _ ≤ (∑ j, ∑ a, uC j a) * X.p ^ X.G' + (∑ a, uM a) * X.p ^ X.G' := by
          refine Nat.add_le_add ?_ (sum_mul_le _ _ _ fun a => by rw [P.polM a l]; exact P.dgMQ a l)
          rw [Finset.sum_mul]
          exact Finset.sum_le_sum fun j _ => sum_mul_le _ _ _ fun a => P.plQ j a l
      _ = ((∑ j, ∑ a, uC j a) + ∑ a, uM a) * X.p ^ X.G' := (Nat.add_mul _ _ _).symm
      _ ≤ e * X.p ^ X.G' := Nat.mul_le_mul_right _ (by omega)
      _ = X.p ^ X.G' * e := Nat.mul_comm _ _
  · intro l
    calc ∑ c, ((P.R + B + M) (l, c) - Std (l, c)) ≤ ∑ c, M (l, c) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [hSv, hAv]; omega
      _ = multideg M l := rfl
      _ = ∑ a, u a * P.dg a l := hdeg l
      _ ≤ (∑ a, u a) * X.p ^ X.G' := sum_mul_le _ _ _ fun a => P.dgQ a l
      _ ≤ e * X.p ^ X.G' := Nat.mul_le_mul_right _ hsum
      _ = X.p ^ X.G' * e := Nat.mul_comm _ _
  · intro j c
    have hM0 : multideg M (topEnd X j, false) = 0 := by
      rw [hdeg]
      exact Finset.sum_eq_zero fun a _ => by rw [P.dgY a j, mul_zero]
    have hB0 : multideg Brem (topEnd X j, false) = 0 := by
      rw [hmdB]
      have h1 : (∑ j', ∑ a, uC j' a * multideg (P.pl j' a) (topEnd X j, false)) = 0 :=
        Finset.sum_eq_zero fun j' _ => Finset.sum_eq_zero fun a _ => by rw [P.plY j' a j, mul_zero]
      have h2 : (∑ a, uM a * multideg (P.aM a) (topEnd X j, false)) = 0 :=
        Finset.sum_eq_zero fun a _ => by rw [P.polM a, P.dgMY a j, mul_zero]
      rw [h1, h2]
    rw [hSv, hAv, zero_of_multideg hM0 c, zero_of_multideg hB0 c]
  · rw [← key]
    refine mem_Pol_iffW.2 fun l => ?_
    have h1 := hom_total (mdHom X l) P.sg (fun a => P.dg a l) (fun a => mem_Pol_iffW.1 (P.sgMd a) l)
      (mem_Pol_iffW.1 P.rigPol l) P.mult u M
    have h2 : P.dR l + ∑ a, (P.mult a - u a) * P.dg a l + (mdHom X l) M = hhDegs X.TT X.aT X.bT l := by
      have h3 : (mdHom X l) M = ∑ a, u a * P.dg a l := hdeg l
      rw [h3, add_assoc, sum_split _ _ _ hu, P.degκ l]
    rw [h2] at h1
    exact h1
  · rw [← key]
    intro m hm
    have h1 := hom_total (ndHom X) P.sg P.od P.sgNd P.rigHom P.mult u M m hm
    have h1' : ndM X m = P.oR + ∑ a, (P.mult a - u a) * P.od a + ndM X M := h1
    have h2 := sum_split P.mult u P.od hu
    have h3 := P.ordκ
    omega

def PreSys.toFacSys (D : Formalism.BasicNotions.D7) [CharZero (KK O)]
    (P : PreSys C0 CE1 CE2 X O w (mm + (n : ℝ) * ka1 X) β L G Std)
    (hStd : (monomial Std (1 : KK O) : RHH O X) = ∏ j, L.stdPoly O j)
    (hT : TCoreBody C0 Cde CE1 CE2 X O mm n β L Std) (hG0 : ∀ j, G j ≠ 0)
    (hGY : ∀ j k, G j ∈ YCond (KK O) (r := X.m) (L.LL j) ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.J k)
      ((BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k))
    (hcov : ∀ j, ∑ i, (if (L.LL j).vec i then 0 else 1) ≤ X.N1) :
    FacSys C0 Cde CE1 CE2 X O w mm n (ordFam C0 CE1 CE2 X β)
      (symFam (KK O) X.p C0 CE1 CE2 X β (fun j => L.word O j (G j))) where
  κ := P.κ
  fin := inferInstance
  mult := P.mult
  f := P.f
  sg := P.sg
  od := P.od
  dg := P.dg
  fR := P.fR
  sgR := P.sgR
  oR := P.oR
  fac := by
    rintro (⟨j, a⟩ | ⟨j, i⟩ | a)
    · exact P.facC j a
    · exact P.facH j i
    · exact P.facM a
  sgHom := fun a m hm => P.sgNd a m hm
  liftPol := by
    rintro (⟨j, a⟩ | ⟨j, i⟩ | a)
    · exact P.liftC j a
    · exact P.liftH j i
    · exact P.liftM a
  sgPol := P.sgMd
  rigA := P.rigA
  rigLift := P.rigLift
  rigInt := P.rigInt
  clean := fun g' hg' hne => by rw [P.fprod]; exact P.clean g' hg' hne
  total := by rw [P.fprod]; exact P.total
  ordEq := P.ordκ
  symEq := P.symκ hStd
  core := fun u hu M e he1 hsum hen hdeg hnd => P.core D hT hG0 hGY hcov u hu M e he1 hsum hen hdeg hnd

end Glue

end Formalism.MainNotions.ColumnSystems.Pf
end
end

