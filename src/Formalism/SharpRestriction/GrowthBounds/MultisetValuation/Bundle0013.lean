module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntRPsubst
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0012

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.InParamMap
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Gen

variable (p : ℕ) [hp : Fact p.Prime] (K' : Type) [Field K'] [Algebra (K0 p) K']

theorem lgF_const : PowerSeries.constantCoeff (lgF K' p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF, PowerSeries.coeff_mk]
  simp

private theorem cc_subst_lemma {Kf : Type} [Field Kf] {ρ : Type} (a : MvPowerSeries ρ Kf) (f : PowerSeries Kf)
    (ha : MvPowerSeries.constantCoeff a = 0) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← PowerSeries.coe_substAlgHom hs, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hs, map_mul,
    ha, zero_mul]

theorem log_at {τ : Type} (vp : K') (μ : PowerSeries K') (h0 : PowerSeries.constantCoeff μ = 0)
    (h1 : (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X)
    (L : MvPowerSeries τ K') (hL : MvPowerSeries.constantCoeff L = 0) :
    PowerSeries.subst (PowerSeries.subst L (PowerSeries.C vp * μ) : MvPowerSeries τ K') (lgF K' p) =
      MvPowerSeries.C vp * L := by
  have hμ : PowerSeries.HasSubst μ := PowerSeries.HasSubst.of_constantCoeff_zero h0
  have hL' : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL
  have hvμ : PowerSeries.HasSubst (PowerSeries.C vp * μ) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by rw [map_mul]; exact mul_eq_zero_of_right _ h0)
  have hvX : PowerSeries.HasSubst (vp • PowerSeries.X : PowerSeries K') :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp; exact Or.inr (PowerSeries.constantCoeff_X (R := K')))
  have hres : PowerSeries.rescale vp (lgF K' p) = vp • lamF p vp := by
    ext n
    rcases n with _ | n
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, lamF, PowerSeries.coeff_mk,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, lgF_const p K']
      simp
    · rw [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, lamF, PowerSeries.coeff_mk]
      simp only [Nat.add_sub_cancel, smul_eq_mul]
      ring
  have hsub : PowerSeries.subst (PowerSeries.C vp * μ) (lgF K' p) = vp • PowerSeries.subst μ (lamF p vp) := by
    have hvμe : PowerSeries.C vp * μ = PowerSeries.subst μ (vp • PowerSeries.X : PowerSeries K') := by
      rw [← PowerSeries.coe_substAlgHom hμ, map_smul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X hμ,
        PowerSeries.smul_eq_C_mul]
    rw [hvμe, ← PowerSeries.subst_comp_subst_apply hvX hμ, ← PowerSeries.rescale_eq_subst, hres,
      ← PowerSeries.coe_substAlgHom hμ, map_smul]
  rw [← PowerSeries.subst_comp_subst_apply hvμ hL', hsub, h1, ← PowerSeries.coe_substAlgHom hL', map_smul,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hL', MvPowerSeries.smul_eq_C_mul]

theorem genInt {σ τ : Type} [Finite σ] (R' : Subring K') (vp : K') (hvp : vp ^ (p ^ 2 - 1) = (p : K'))
    (hRp : Rp p K' vp ≤ R') (U : MvPowerSeries σ K') (hU : IntR R' (inParamK p K' U))
    (L : σ → MvPowerSeries τ K') (hL0 : ∀ i, MvPowerSeries.constantCoeff (L i) = 0) (hL : ∀ i, IntR R' (L i)) :
    IntR R' (MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U) := by
  obtain ⟨μ, h0, hμ, h1⟩ := exists_mu (p := p) (K' := K') vp hvp
  have hlg : PowerSeries.map (algebraMap (K0 p) K') (logF p) = lgF K' p := map_logF (p := p) (K' := K')
  let M : σ → MvPowerSeries τ K' := fun i => PowerSeries.subst (L i) (PowerSeries.C vp * μ)
  have hvμ0 : PowerSeries.constantCoeff (PowerSeries.C vp * μ) = 0 := by simp [h0]
  have hM0 : ∀ i, MvPowerSeries.constantCoeff (M i) = 0 := fun i => cc_subst_lemma _ _ (hL0 i) hvμ0
  have hvp_mem : vp ∈ R' := hRp (Subring.subset_closure (Or.inr rfl))
  have hvμI : IntR R' (PowerSeries.C vp * μ : PowerSeries K') := by
    intro n
    rw [← PowerSeries.smul_eq_C_mul, MvPowerSeries.coeff_smul]
    refine R'.mul_mem hvp_mem (hRp ?_)
    have hn : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by cases u; simp
    rw [hn]
    exact hμ (n ())
  have hMint : ∀ i, IntR R' (M i) := fun i =>
    IntR_subst (K := K') (R := R') (fun _ : Unit => L i) (fun _ => hL0 i) (fun _ => hL i) hvμI
  have hMs : MvPowerSeries.HasSubst M := MvPowerSeries.hasSubst_of_constantCoeff_zero hM0
  have hMeq : ∀ i, PowerSeries.subst (M i) (lgF K' p) = MvPowerSeries.C vp * L i := fun i =>
    log_at p K' vp μ h0 h1 (L i) (hL0 i)
  have key : MvPowerSeries.subst (fun i => MvPowerSeries.C vp * L i) U =
      MvPowerSeries.subst M (inParamK p K' U) := by
    have hXs : MvPowerSeries.HasSubst
        (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K') (lgF K' p)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
        cc_subst_lemma _ _ (MvPowerSeries.constantCoeff_X i) (lgF_const p K')
    rw [inParamK, hlg, MvPowerSeries.subst_comp_subst_apply hXs hMs]
    congr 1
    funext i
    rw [← hMeq i]
    have hXi : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K')) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X i
    show _ = MvPowerSeries.subst M (MvPowerSeries.subst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ K'))
      (lgF K' p))
    rw [MvPowerSeries.subst_comp_subst_apply hXi hMs, MvPowerSeries.subst_X hMs]
    rfl
  rw [key]
  exact IntR_subst (K := K') (R := R') M hM0 hMint hU

theorem inParam_map {σ : Type} [Finite σ] (K1 : Type) [Field K1] [Algebra (K0 p) K1] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (R1 : Subring K1) (R' : Subring K') (hR1 : ∀ x ∈ R1, algebraMap K1 K' x ∈ R')
    (U : MvPowerSeries σ K1) (hU : IntR R1 (inParamK p K1 U)) :
    IntR R' (inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U)) := by
  have hXs1 : MvPowerSeries.HasSubst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ K1)
      (PowerSeries.map (algebraMap (K0 p) K1) (logF p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      cc_subst_lemma _ _ (MvPowerSeries.constantCoeff_X i) (by rw [map_logF (p := p) (K' := K1)]; exact lgF_const p K1)
  have e : inParamK p K' (MvPowerSeries.map (algebraMap K1 K') U) =
      MvPowerSeries.map (algebraMap K1 K') (inParamK p K1 U) := by
    rw [inParamK, inParamK, MvPowerSeries.map_subst hXs1]
    congr 1
    funext i
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)),
      MvPowerSeries.map_X]
    congr 1
    ext n
    simp [PowerSeries.coeff_map, IsScalarTower.algebraMap_apply (K0 p) K1 K']
  rw [e]
  intro n
  rw [MvPowerSeries.coeff_map]
  exact hR1 _ (hU n)

end Gen

theorem restSInt (p : ℕ) [Fact p.Prime] : RestSInt p := by
  intro n' r0 r1 B K1 _ _ R1 U hU K' _ _ _ _ R' vp hvp hRp hR1
  have hc : coordZ (r0 := r0) (r1 := r1) B K' vp = fun x => MvPowerSeries.C vp * coordZ B K' 1 x := by
    funext x
    rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;> simp [coordZ, Finset.mul_sum, map_mul, mul_assoc]
  have hLint : ∀ x, IntR R' (coordZ (r0 := r0) (r1 := r1) B K' 1 x) := by
    intro x n
    rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
      simp only [coordZ, one_mul, map_sum] <;>
      refine R'.sum_mem fun s _ => ?_ <;>
      rw [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X] <;>
      split_ifs <;> simp only [mul_one, mul_zero]
    all_goals first | exact hRp (Subring.subset_closure (Or.inl ⟨_, rfl⟩)) | exact R'.zero_mem
  unfold ThZ
  rw [hc]
  exact genInt p K' R' vp hvp hRp (MvPowerSeries.map (algebraMap K1 K') U) (inParam_map p K' K1 R1 R' hR1 U hU)
    (coordZ B K' 1) (coordZ_const (p := p) B K' 1) hLint

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelProductForm
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section IntRL

variable {ι K : Type} [Field K] {R : Subring K}

theorem en_IntR_mul {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

theorem en_IntR_one : IntR R (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem en_IntR_X (i : ι) : IntR R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem en_IntR_pow {f : MvPowerSeries ι K} (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact en_IntR_one
  | succ k ih => rw [pow_succ]; exact en_IntR_mul ih hf

theorem en_IntR_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∏ a ∈ s, f a) :=
  Finset.prod_induction f (IntR R) (fun _ _ => en_IntR_mul) en_IntR_one h

end IntRL

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem en_places_add (j : ℕ) (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ) (hLow : ∀ v, LowAtI X Y j v (i0 v) (gP v))
    (U1 : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc) (hU1 : IntR Y.Oc (inParamK p Y.Kc U1)) (I : X.ColCh j) :
    geP Y (applyD (X.PI j I i0) (X.ThZA Y.Kc j ((∏ v, en_F X Y j v) * U1))) ((∑ v, gP v : ℚ) : ℝ) := by
  classical
  have e1 : X.ThZA Y.Kc j ((∏ v, en_F X Y j v) * U1) = (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) *
      MvPowerSeries.subst (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) (inParamK p Y.Kc U1) := by
    rw [en_ThZA_mul, en_ThZA_prod]
    congr 1
    conv_lhs => rw [← en_Ec_inParamK p Y.Kc U1]
    unfold Sys.ThZA
    rw [MvPowerSeries.subst_comp_subst_apply (en_Ec_hs p Y.Kc) (en_coordZA_hs X Y.Kc j)]
  have ha : MvPowerSeries.HasSubst (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      MvPowerSeries.constantCoeff_subst_eq_zero (en_coordZA_hs X Y.Kc j) (en_coordZA_zero X Y.Kc j)
        (en_Ec_zero p Y.Kc i)
  rw [en_applyD_eq, e1]
  obtain ⟨B, hB⟩ := Gen.jp_subst_expand (en_mapP Y.Kc (X.ZA j) (X.FrI j) (X.PI j I i0))
    (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) ha (inParamK p Y.Kc U1)
  rw [hB]
  refine valuation_coeff_ge_sum Y _ _ _ fun β _ => valuation_coeff_ge_smul Y (hU1 β) ?_
  set Ub : X.Pl → MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc := fun v =>
    ∏ i ∈ β.support.filter (fun i => en_pi X j i = v), (en_Ec p Y.Kc i) ^ (β i) with hUb
  have e2 : (β.prod fun i e => X.ThZA Y.Kc j (en_Ec p Y.Kc i) ^ e) = ∏ v, X.ThZA Y.Kc j (Ub v) := by
    unfold Finsupp.prod
    rw [← Finset.prod_fiberwise β.support (en_pi X j)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hUb, en_ThZA_prod]
    exact Finset.prod_congr rfl fun i _ => (en_ThZA_pow X Y.Kc j _ _).symm
  have e3 : (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) * ∏ v, X.ThZA Y.Kc j (Ub v) =
      ∏ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => (en_ThZA_mul X Y.Kc j _ _).symm
  have hG : ∀ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v := fun v =>
    en_ThZA_supp X Y.Kc j v (Subring.mul_mem _ (en_F_supp X Y j v) (Subring.prod_mem _ fun i hi =>
      Subring.pow_mem _ (by
        have := en_Ec_supp p Y.Kc (en_pi X j) i
        rw [(Finset.mem_filter.1 hi).2] at this
        exact this) _))
  have e4 : ∏ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) =
      ∏ v, Gen.atP v (Gen.resP v (X.ThZA Y.Kc j (en_F X Y j v * Ub v))) :=
    Finset.prod_congr rfl fun v _ => Gen.eq_atP v _ (hG v)
  have e5 : en_mapP Y.Kc (X.ZA j) (X.FrI j) (X.PI j I i0) =
      ∏ v, MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
    rw [PI_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun v _ => en_mapP_PIvS X Y j I i0 v
  rw [e2, e3, e4, e5, Gen.jp_prod]
  refine valuation_coeff_ge_prod_rat Y _ _ _ fun v _ => ?_
  have e6 : Gen.jp (en_Ploc X Y j I i0 v) (Gen.resP v (X.ThZA Y.Kc j (en_F X Y j v * Ub v))) =
      applyD (PIvS X j I (fun _ => i0 v) v) (X.ThZA Y.Kc j (en_F X Y j v * Ub v)) := by
    rw [en_applyD_eq, ← PIvS_congr, en_mapP_PIvS]
    conv_rhs => rw [Gen.eq_atP v _ (hG v)]
    rw [Gen.jp_rename]
  rw [e6]
  have hint : IntR Y.Oc (inParamK p Y.Kc (Ub v)) := by
    rw [hUb, en_inParamK_prod]
    refine en_IntR_prod _ _ fun i _ => ?_
    rw [en_inParamK_pow, en_inParamK_Ec]
    exact en_IntR_pow (en_IntR_X i) _
  exact fun n => hLow v (Ub v) hint I n

def KernelProductForm (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La'), ∃ U1 : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U1) ∧
      Y.ThA j La La' φ = (∏ v, en_F X Y j v) * U1

variable {X Y}

theorem restPlaces_of (D : Formalism.BasicNotions.D7) (h : KernelProductForm X Y D) : RestPlaces X Y D := by
  intro hA j hj i0 gP hLow La La' h1 h2 φ I n
  obtain ⟨U1, hU1, e⟩ := h hA j hj La La' h1 h2 φ
  rw [e]
  have := en_places_add X Y j i0 gP hLow U1 hU1 I n
  push_cast at this
  exact this

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LatAtZeroUpd
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def nC (v : X.Pl) (i l : ℕ) : ℕ :=
  (p ^ X.G.P.n' v) ^ ((i - l) * (X.t + 1 - l)) * Formalism.G0.gaussBinom (p ^ X.G.P.n' v) (X.t + 1) l

theorem latAt_succ_upd (v : X.Pl) (j : ℕ) (L' : (X.Pj (j + 1)).Tup)
    (L1 : Submodule ((X.Pj (j + 1)).W (X.vJ (j + 1) v)) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq (X.vJ (j + 1) v))) :
    X.latAt v (j + 1) (Function.update L' (X.vJ (j + 1) v) L1) = L1 :=
  Function.update_self (β := fun u => Submodule ((X.Pj (j + 1)).W u) (Fin ((X.Pj (j + 1)).m + 1) → (X.Pj (j + 1)).Qq u))
    (X.vJ (j + 1) v) L1 L'

theorem latAt_zero_upd (v : X.Pl) (L' : (X.Pj 0).Tup)
    (L1 : Submodule ((X.Pj 0).W (X.vJ 0 v)) (Fin ((X.Pj 0).m + 1) → (X.Pj 0).Qq (X.vJ 0 v))) :
    X.latAt v 0 (Function.update L' (X.vJ 0 v) L1) = L1 :=
  Function.update_self (β := fun u => Submodule ((X.Pj 0).W u) (Fin ((X.Pj 0).m + 1) → (X.Pj 0).Qq u))
    (X.vJ 0 v) L1 L'

theorem countG (hC : CountLoc) (v : X.Pl) (j i : ℕ) (L : (X.Pj j).Tup) (L' : (X.Pj (j + 1)).Tup)
    (hL : (X.Pj j).IsLatTup L) (hL' : (X.Pj (j + 1)).IsLatTup L') :
    ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.ind v j L (Function.update L' (X.vJ (j + 1) v) L1) =
      ∑ l ∈ range (i + 1), nC X v i l •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) (L (X.vJ j v)), X.ind v j (Function.update L (X.vJ j v) A1) L' := by
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply]
  cases j with
  | zero =>
    have key := count_fun hC p (X.G.P.n' v) (X.G.P.setting v).frac_alt (X.G.P.setting v).p_unif (X.G.P.setting v).res_card
      (X.G.P.m + 1) (X.G.P.m + (0 + 1) * (X.Fl.t + 1) + 1) (X.Fl.t + 1) i (by ring) (L v) (L' v) (hL v) (hL' v)
      (EE (X.Pj (0 + 1)) (X.vJ (0 + 1) v) i (L' v)) (fun B1 => mem_EE _)
      (fun k => UP (X.Pj (0)) (X.vJ (0) v) k (L v)) (fun k A1 => mem_UP _) x
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun L1 _ => ?_
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl
    · symm
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul]
      refine congrArg₂ _ rfl (Finset.sum_congr rfl fun A1 _ => ?_)
      unfold Sys.ind
      rw [latAt_zero_upd]
      rfl
  | succ j =>
    have key := count_fun hC p (X.G.P.n' v) (X.G.P.setting v).frac_alt (X.G.P.setting v).p_unif (X.G.P.setting v).res_card
      (X.G.P.m + (j + 1) * (X.Fl.t + 1) + 1) (X.G.P.m + ((j + 1) + 1) * (X.Fl.t + 1) + 1) (X.Fl.t + 1) i (by ring) (L v) (L' v) (hL v) (hL' v)
      (EE (X.Pj ((j + 1) + 1)) (X.vJ ((j + 1) + 1) v) i (L' v)) (fun B1 => mem_EE _)
      (fun k => UP (X.Pj ((j + 1))) (X.vJ ((j + 1)) v) k (L v)) (fun k A1 => mem_UP _) x
    refine Eq.trans ?_ (key.trans ?_)
    · refine Finset.sum_congr rfl fun L1 _ => ?_
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl
    · symm
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [nsmul_eq_mul]
      refine congrArg₂ _ rfl (Finset.sum_congr rfl fun A1 _ => ?_)
      unfold Sys.ind
      rw [latAt_succ_upd]
      rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcIotaInj
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

abbrev nc_iota (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : Formalism.MainNotions.G.HH D :=
  t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)

include hL ht0 in
theorem nc_n_eq : (D.gat u w hg).P.n' (Y.vOf u w hg t0) = addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  exact (h t0 ht0).1

include hL ht0 in
theorem nc_iota_inj : Function.Injective (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  intro s s' hss
  have hs := lt_of_lt_of_eq s.isLt hn
  have hs' := lt_of_lt_of_eq s'.isLt hn
  exact Fin.ext (nsmul_injOn_Iio_addOrderOf hs hs' (add_left_cancel hss))

include hL ht0 in
theorem nc_topsOn : Formalism.MainNotions.G.topsOn X (D.what₂.places.resChar w) t0 =
    ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).image (nc_iota Y u w hg t0) := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have h0 := hL u w hg
  dsimp only at h0
  obtain ⟨-, -, -, -, -, -, h⟩ := h0
  have hsg : ¬ G.IsSg D (D.what₂.places.resChar w) := by
    unfold G.IsSg
    rw [hg.2.2.1]
    decide
  have hst : G.stepP D (D.what₂.places.resChar w) = G.hP D (D.what₂.places.resChar w) := by
    unfold G.stepP
    exact ite_eq_right hsg
  let step := G.hP D (D.what₂.places.resChar w)
  have hiter (t : G.HH D) (i : ℕ) : X.bs step (t + i • step) = X.bs step t := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]
  have hr : t0 ∈ Finset.univ.image (X.bs step) := by
    simpa only [G.reps, hst] using ht0
  have hb : X.bs step t0 = t0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, hi⟩ := X.bs_orb step t
    simpa only [hi] using (hiter (X.bs step t) i).symm
  have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := addOrderOf_pos _
  ext t
  simp only [Formalism.MainNotions.G.topsOn, Finset.mem_filter, Finset.mem_image, hst]
  constructor
  · rintro ⟨htT, hbt⟩
    obtain ⟨i, hi⟩ := X.bs_orb (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) t
    rw [hbt] at hi
    have hlt : i % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) <
        (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by
      rw [hn]; exact Nat.mod_lt _ hpos
    refine ⟨⟨_, hlt⟩, ?_, ?_⟩
    · rw [((h t0 ht0).2 _).2.1]
      simp only [mod_addOrderOf_nsmul, hi]
      exact htT
    · simp only [nc_iota, mod_addOrderOf_nsmul, hi]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨((h t0 ht0).2 s).2.1.1 hs, ?_⟩
    simp only [nc_iota]
    change X.bs step (t0 + s.val • step) = t0
    rw [hiter, hb]

include hL ht0 in
theorem nc_isV (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) :
    Formalism.MainNotions.G.IsV X (D.what₂.places.resChar w) (nc_iota Y u w hg t0 s) ↔ ¬ IsOddPos s := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have hsg : ¬ G.IsSg D (D.what₂.places.resChar w) := by
    unfold G.IsSg
    rw [hg.2.2.1]
    decide
  have hst : G.stepP D (D.what₂.places.resChar w) = G.hP D (D.what₂.places.resChar w) := by
    unfold G.stepP
    exact ite_eq_right hsg
  let step := G.hP D (D.what₂.places.resChar w)
  have hiter (t : G.HH D) (i : ℕ) : X.bs step (t + i • step) = X.bs step t := by
    induction i with
    | zero => simp
    | succ i ih => rw [succ_nsmul, ← add_assoc, X.bs_step, ih]
  have hr : t0 ∈ Finset.univ.image (X.bs step) := by
    simpa only [G.reps, hst] using ht0
  have hb : X.bs step t0 = t0 := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨i, hi⟩ := X.bs_orb step t
    simpa only [hi] using (hiter (X.bs step t) i).symm
  have hnP : Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) =
      addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by
    simp only [Formalism.MainNotions.G.nP, ite_eq_right hsg]
  have hs := lt_of_lt_of_eq s.isLt hn
  have key : ¬ IsOddPos s ↔ Even s.val := by
    show ¬ (s.val % 2 = 1) ↔ _
    rw [← Nat.odd_iff, Nat.not_odd_iff_even]
  rw [key]
  have hbs : X.bs (G.hP D (D.what₂.places.resChar w))
      (t0 + s.val • G.hP D (D.what₂.places.resChar w)) = t0 := (hiter t0 s.val).trans hb
  simp only [Formalism.MainNotions.G.IsV, hst, hnP, nc_iota, hbs]
  constructor
  · rintro ⟨i, hi, hev, heq⟩
    have hi' := nsmul_injOn_Iio_addOrderOf hi hs (add_left_cancel heq)
    rw [← hi']
    exact hev
  · intro hev
    exact ⟨s.val, hs, hev, rfl⟩

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

