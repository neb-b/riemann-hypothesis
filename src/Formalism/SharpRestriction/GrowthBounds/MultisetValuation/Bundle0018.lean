module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0017
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0002
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ExpansionAllPlacesOfPlace
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser eq_of_low)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Rename₂

variable {κ σ R : Type} [Finite κ] [CommRing R] (φ : κ → σ)

theorem th_ren_eq (f : MvPowerSeries κ R) : ren φ f = MvPowerSeries.substAlgHom (th_ren_hasSubst (R := R) φ) f := by
  unfold ren
  rw [MvPowerSeries.coe_substAlgHom]

theorem th_ren_sum {α : Type} (s : Finset α) (f : α → MvPowerSeries κ R) :
    ren φ (∑ a ∈ s, f a) = ∑ a ∈ s, ren φ (f a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [th_ren_eq φ, map_sum]

theorem th_ren_mul (f g : MvPowerSeries κ R) : ren φ (f * g) = ren φ f * ren φ g := by
  simp only [th_ren_eq φ, map_mul]

theorem th_ren_neg (f : MvPowerSeries κ R) : ren φ (-f) = -ren φ f := by
  simp only [th_ren_eq φ, map_neg]

theorem th_ren_pow (f : MvPowerSeries κ R) (n : ℕ) : ren φ (f ^ n) = ren φ f ^ n := by
  simp only [th_ren_eq φ, map_pow]

theorem th_ren_C (r : R) : ren φ (MvPowerSeries.C r : MvPowerSeries κ R) = MvPowerSeries.C r := by
  first
  | (unfold ren; exact MvPowerSeries.subst_C (th_ren_hasSubst φ) r)
  | (rw [th_ren_eq φ]; exact (MvPowerSeries.substAlgHom (th_ren_hasSubst (R := R) φ)).commutes r)

theorem th_ren_X (k : κ) : ren φ (MvPowerSeries.X k : MvPowerSeries κ R) = MvPowerSeries.X (φ k) := by
  unfold ren
  exact MvPowerSeries.subst_X (th_ren_hasSubst φ) k

theorem th_subst_ren {τ : Type} {T : σ → MvPowerSeries τ R} (hT : MvPowerSeries.HasSubst T) (f : MvPowerSeries κ R) :
    MvPowerSeries.subst T (ren φ f) = MvPowerSeries.subst (fun k => T (φ k)) f := by
  unfold ren
  rw [MvPowerSeries.subst_comp_subst_apply (th_ren_hasSubst φ) hT f]
  congr 1
  funext k
  exact MvPowerSeries.subst_X hT (φ k)

theorem th_ren_subst {ρ : Type} {t : ρ → MvPowerSeries κ R} (ht : MvPowerSeries.HasSubst t) (f : MvPowerSeries ρ R) :
    ren φ (MvPowerSeries.subst t f) = MvPowerSeries.subst (fun x => ren φ (t x)) f := by
  unfold ren
  exact MvPowerSeries.subst_comp_subst_apply ht (th_ren_hasSubst φ) f

theorem th_ren_psubst {L : MvPowerSeries κ R} (hL : MvPowerSeries.constantCoeff L = 0) (f : PowerSeries R) :
    ren φ (PowerSeries.subst L f) = PowerSeries.subst (ren φ L) f := by
  have hL' := (PowerSeries.HasSubst.of_constantCoeff_zero hL).const
  exact th_ren_subst φ hL' f

theorem th_ren_ren {ρ : Type} [Finite σ] (ψ : σ → ρ) (f : MvPowerSeries κ R) :
    ren ψ (ren φ f) = ren (fun k => ψ (φ k)) f := th_subst_ren φ (th_ren_hasSubst ψ) f

theorem th_map_ren {S : Type} [CommRing S] (h : R →+* S) (f : MvPowerSeries κ R) :
    MvPowerSeries.map h (ren φ f) = ren φ (MvPowerSeries.map h f) := by
  unfold ren
  rw [MvPowerSeries.map_subst (th_ren_hasSubst φ)]
  congr 1
  funext k
  exact MvPowerSeries.map_X h (φ k)

end Rename₂

section RenField

variable {κ σ K : Type} [Finite κ] [Field K] (φ : κ → σ)

theorem th_ren_expK {f : MvPowerSeries κ K} (hf : MvPowerSeries.constantCoeff f = 0) :
    ren φ (expK f) = expK (ren φ f) :=
  th_subst_expK _ (fun _ => MvPowerSeries.constantCoeff_X _) hf

theorem th_IntR_ren {R : Subring K} {f : MvPowerSeries κ K} (hf : IntR R f) : IntR R (ren φ f) :=
  IntR_subst _ (fun _ => MvPowerSeries.constantCoeff_X _) (fun _ => IntR_X _) hf

theorem th_expK_sum [CharZero K] {ι α : Type} (s : Finset α) (a : α → MvPowerSeries ι K)
    (h : ∀ v ∈ s, MvPowerSeries.constantCoeff (a v) = 0) : expK (∑ v ∈ s, a v) = ∏ v ∈ s, expK (a v) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.prod_empty, th_expK_zero]
  | insert v s hv ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert hv, Finset.prod_insert hv,
      expK_add (h v (Finset.mem_insert_self _ _))
        (by rw [map_sum]; exact Finset.sum_eq_zero fun v' hv' => h v' (Finset.mem_insert_of_mem hv')),
      ih fun v' hv' => h v' (Finset.mem_insert_of_mem hv')]

def altS (p : ℕ) {ι : Type} [DecidableEq ι] (x : ℕ → ι) : MvPowerSeries ι K :=
  fun n => ∑ l ∈ range (n.degree + 1), if n = Finsupp.single (x l) (p ^ (2 * l)) then (-1) ^ l else 0

def altPart (p : ℕ) {ι : Type} (x : ℕ → ι) (M : ℕ) : MvPowerSeries ι K :=
  ∑ l ∈ range M, MvPowerSeries.C ((-1 : K) ^ l) * MvPowerSeries.X (x l) ^ (p ^ (2 * l))

theorem th_low_alt {p : ℕ} (hp : 2 ≤ p) {ι : Type} [DecidableEq ι] (x : ℕ → ι) (M : ℕ) :
    Low M (altS (K := K) p x - altPart p x M) := by
  intro d hd
  rw [map_sub, sub_eq_zero]
  show (∑ l ∈ range (d.degree + 1), if d = Finsupp.single (x l) (p ^ (2 * l)) then ((-1 : K) ^ l) else 0) = _
  unfold altPart
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun l _ hl => if_neg fun h => ?_
  have h1 : d.degree = p ^ (2 * l) := by rw [h, Finsupp.degree_single]
  have h2 : l < (p ^ 2) ^ l := Nat.lt_pow_self (by nlinarith)
  rw [← pow_mul] at h2
  simp only [mem_range] at hl
  omega

theorem th_ren_altS [DecidableEq κ] [DecidableEq σ] {p : ℕ} (hp : 2 ≤ p) (x : ℕ → κ) :
    ren φ (altS (K := K) p x) = altS p (fun l => φ (x l)) := by
  refine eq_of_low fun M => ?_
  have e : ren φ (altS (K := K) p x) - altS p (fun l => φ (x l)) =
      ren φ (altS (K := K) p x - altPart p x M) - (altS p (fun l => φ (x l)) - altPart p (fun l => φ (x l)) M) := by
    have : ren φ (altPart (K := K) p x M) = altPart p (fun l => φ (x l)) M := by
      unfold altPart
      simp only [th_ren_sum, th_ren_mul, th_ren_C, th_ren_pow, th_ren_X]
    rw [th_ren_sub, this]
    ring
  rw [e]
  exact low_sub (Formalism.DworkPowerSeriesWeights.low_subst_of_low (fun _ => MvPowerSeries.constantCoeff_X _) (th_low_alt hp x M))
    (th_low_alt hp _ M)

end RenField

section Places

variable {p : ℕ} [hp : Fact p.Prime]

theorem th_Gt_sigma {Pl : Type} [Fintype Pl] (E : Pl → Type) [∀ v, Fintype (E v)] (c c' : K0 p) :
    Gt p (Σ v, E v) c c' = ∑ v, ren (Sum.map (Sigma.mk v) (Sigma.mk v)) (Gt p (E v) c c') := by
  unfold Gt
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [th_ren_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [th_ren_ren]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem th_Gt_const (E : Type) [Fintype E] (c c' : K0 p) : MvPowerSeries.constantCoeff (Gt p E c c') = 0 := by
  unfold Gt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun e _ => th_ren_const _ (th_Gser_const c c')

variable (X : Sys p)

theorem th_hhA_eq (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') :
    X.hhA K' j v u = ren (fun z => (⟨v, z⟩ : X.ZA j)) (hhS p K' u) := by
  have hs : ∀ (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))),
      ren (fun z => (⟨v, z⟩ : X.ZA j)) (sSer p K' e a b) = X.sSA K' j v e a b := fun e a b =>
    th_ren_altS (K := K') (fun z => (⟨v, z⟩ : X.ZA j)) hp.out.two_le (fun l => (posSub e (2 * l), a, b))
  unfold Sys.hhA hhS
  simp only [th_ren_sum, th_ren_mul, th_ren_C, th_ren_pow, hs]

theorem th_coordZA_eq (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (v : X.Pl)
    (x : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) ⊕
      Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) :
    X.coordZA K' j (Sum.map (Sigma.mk v) (Sigma.mk v) x) =
      ren (fun z => (⟨v, z⟩ : X.ZA j)) (coordZ (X.om v) K' 1 x) := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  · simp only [Sum.map_inl, Sum.map_inr, Sys.coordZA, coordZ, th_ren_sum, th_ren_mul, th_ren_C, th_ren_X, one_mul]

theorem restGcA_of (hG : RestGc p) : RestGcA X := by
  intro c hc j K' _ _ vp hvp μ h0 h1
  have hcz := charZero_K' p K'
  choose u hu V hV hEq using fun v : X.Pl => hG (X.std v).five_le c hc (X.G.P.n' v) (NN X.G.P.m X.t j)
    (NN X.G.P.m X.t (j + 1)) (X.std v).two_le (X.std v).even (X.om v) K' vp hvp μ h0 h1
  refine ⟨u, hu, ∏ v, ren (fun z => (⟨v, z⟩ : X.ZA j)) (V v),
    IntR_prod _ _ fun v _ => th_IntR_ren _ (hV v), ?_⟩
  have hT0 := th_tOf_const vp μ h0 (X.coordZA K' j) (coordZA_const X K' j)
  have hT := MvPowerSeries.hasSubst_of_constantCoeff_zero hT0
  have hmG : ∀ v : X.Pl, MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap (K0 p) K')
      (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (wK p c) (wK p (sigW p c)))) = 0 := by
    intro v
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, th_Gt_const, map_zero]
  have e1 : expK (-(MvPowerSeries.map (algebraMap (K0 p) K') (Gt p (X.EA j) (wK p c) (wK p (sigW p c))))) =
      ∏ v : X.Pl, ren (Sum.map (Sigma.mk v) (Sigma.mk v)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
        (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (wK p c) (wK p (sigW p c)))))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [th_Gt_sigma, map_sum, ← Finset.sum_neg_distrib, th_expK_sum]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [th_ren_expK _ (by rw [map_neg, hmG v, neg_zero]), th_ren_neg, th_map_ren]
    · intro v _
      rw [map_neg, th_map_ren, th_ren_const _ (hmG v), neg_zero]
  rw [e1, ← MvPowerSeries.coe_substAlgHom hT, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hT, th_subst_ren _ hT]
  have e2 : (fun k => tOf vp μ (X.coordZA K' j) (Sum.map (Sigma.mk v) (Sigma.mk v) k)) =
      fun k => ren (fun z => (⟨v, z⟩ : X.ZA j)) (tOf vp μ (coordZ (X.om v) K' 1) k) := by
    funext k
    unfold tOf
    rw [th_coordZA_eq, th_ren_psubst _ (coordZ_const (X.om v) K' 1 k)]
  rw [e2, ← th_ren_subst _ (MvPowerSeries.hasSubst_of_constantCoeff_zero
    (th_tOf_const vp μ h0 _ (coordZ_const (X.om v) K' 1))), hEq v, th_ren_mul,
    th_ren_expK _ (by rw [map_neg, map_mul, hhS_const, mul_zero, neg_zero]), th_ren_neg, th_ren_mul, th_ren_C,
    th_hhA_eq]

end Places

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntegralExpParamOfEquivZero
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable (p : ℕ) [hp : Fact p.Prime]

theorem sx_logF_eq : logF p = lgF (K0 p) p := by
  ext n
  simp only [logF, lgF, PowerSeries.coeff_mk, pow_mul]

theorem sx_logF_const : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

def sx_lX {σ : Type} (i : σ) : MvPowerSeries σ (K0 p) :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)

private theorem constantCoeff_subst_X_logF_eq_zero {σ : Type} (i : σ) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [sx_logF_const]
  · simp [MvPowerSeries.constantCoeff_X, zero_pow hd.ne']

private theorem hs_lemma_2 {σ : Type} [Finite σ] :
    MvPowerSeries.HasSubst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => constantCoeff_subst_X_logF_eq_zero p i)

theorem sx_inParam_X {σ : Type} [Finite σ] (i : σ) : inParam p (MvPowerSeries.X i) = sx_lX p i := by
  unfold inParam sx_lX
  exact MvPowerSeries.subst_X (hs_lemma_2 p) i

theorem sx_inParam_add {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f + g) = inParam p f + inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_add (hs_lemma_2 p) f g

theorem sx_inParam_mul {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f * g) = inParam p f * inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_mul (hs_lemma_2 p) f g

theorem sx_inParam_C_mul {σ : Type} [Finite σ] (a : K0 p) (g : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.C a * g) = MvPowerSeries.C a * inParam p g := by
  unfold inParam
  rw [MvPowerSeries.subst_mul (hs_lemma_2 p), MvPowerSeries.subst_C]

theorem sx_subst_ps {σ τ : Type} {a : σ → MvPowerSeries τ (K0 p)} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ (K0 p)} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries (K0 p)) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha f

theorem sx_inParam_subst {σ τ : Type} [Finite σ] [Finite τ] (a a' : σ → MvPowerSeries τ (K0 p))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, PowerSeries.subst (a' i) (logF p) = inParam p (a i)) (f : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.subst a f) = MvPowerSeries.subst a' (inParam p f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  unfold inParam
  rw [MvPowerSeries.subst_comp_subst_apply hA (hs_lemma_2 p), MvPowerSeries.subst_comp_subst_apply (hs_lemma_2 p) hA']
  congr 1
  funext s
  rw [sx_subst_ps p hA' (by simp) (logF p), MvPowerSeries.subst_X hA']
  exact (h s).symm

theorem sx_simeq_of {σ : Type} [Finite σ] {f g : MvPowerSeries σ (K0 p)} (h : Simeq p f g) :
    Formalism.InvariantFactorPaths.G7.Simeq (inParam p f) (inParam p g) := by
  obtain ⟨h0, w, _, hw⟩ := h
  have h1 : MvPowerSeries.constantCoeff (inParam p (f - g)) = 0 := th_inParam_const p h0
  rw [th_inParam_sub] at h1 hw
  refine ⟨h1, ?_⟩
  rw [← sx_expS_eq p h1, sx_integral_iff, hw]
  exact ⟨1 + w, by rw [map_add (f := _), map_one]⟩

theorem integralExp_of_equiv {σ : Type} {f g : MvPowerSeries σ (K0 p)} (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : E0 p (f - g) := by
  obtain ⟨h0, h1⟩ := h
  rw [← sx_expS_eq p h0, sx_integral_iff] at h1
  obtain ⟨w, hw⟩ := h1
  refine ⟨h0, w - 1, ?_, ?_⟩
  · have h2 : MvPowerSeries.constantCoeff (expS p (f - g)) = 1 := by
      rw [sx_expS_eq p h0]
      exact Formalism.InvariantFactorPaths.G7.DworkIntegrality.constantCoeff_mvExp h0
    rw [hw] at h2
    have h3 : algebraMap (WW p) (K0 p) (MvPowerSeries.constantCoeff w) = 1 := by
      rw [← h2, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_map]
    have h4 : MvPowerSeries.constantCoeff w = 1 :=
      IsFractionRing.injective (WW p) (K0 p) (by rw [h3, map_one])
    rw [map_sub, h4, map_one, sub_self]
  · show expS p (f - g) = _
    rw [hw, map_sub, map_one]
    ring

theorem equiv_zero_of_integralExp {σ : Type} {f : MvPowerSeries σ (K0 p)} (h : E0 p f) : Formalism.InvariantFactorPaths.G7.Simeq f 0 := by
  obtain ⟨h0, w, _, hw⟩ := h
  rw [Formalism.InvariantFactorPaths.G7.Simeq, sub_zero]
  refine ⟨h0, ?_⟩
  rw [← sx_expS_eq p h0, sx_integral_iff]
  exact ⟨1 + w, by rw [map_add (f := _), map_one]; exact hw⟩

theorem integralExp_param_of_equiv_zero {σ : Type} [Finite σ] {f : MvPowerSeries σ (K0 p)} (h : Simeq p f 0) : E0 p (inParam p f) := by
  have := integralExp_of_equiv p (sx_simeq_of p h)
  have e : inParam p (0 : MvPowerSeries σ (K0 p)) = 0 := by
    have := th_inParam_sub p (0 : MvPowerSeries σ (K0 p)) 0
    simpa using this
  rwa [e, sub_zero] at this

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcSize
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_Size (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  (∀ s, (al ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) s : ℝ) ≤ (2 * L.sc.a) ^ 2) ∧
  (∀ s, (lsz (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
    ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j s : ℝ) ≤ (2 * L.sc.a) ^ 4)

theorem nc_a_ge : (1 : ℝ) ≤ L.sc.a := by
  have hx : 1 < L.sc.x := L.sc.one_lt_alt
  have hL : 0 ≤ L.sc.L := by
    simp only [Formalism.BasicNotions.Scale.L]
    exact Real.rpow_nonneg (by linarith) _
  have hb : 1 ≤ L.sc.b := by
    simp only [Formalism.BasicNotions.Scale.b]
    exact Real.one_le_exp hL
  simp only [Formalism.BasicNotions.Scale.a]
  exact one_le_mul_of_one_le_of_one_le hx.le hb

theorem nc_de (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts) (hT : GatTies D)
    (hL : Formalism.MainNotions.G.LatTied hT X Y) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w)) (j : ℕ) (hj : j ∈ SizeData₂.lifts D)
    (h1 : 9 ≤ K.dl1) (h2 : 9 ≤ K.dl2) (hlog : 1 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a))
    (hS : nc_Size D L Y u w hg t0 j) : nc_De D L X Y K u w hg t0 j := by
  have hp : 2 ≤ D.what₂.places.resChar w := hg.1.two_le
  have hA : (1 : ℝ) ≤ 2 * L.sc.a := by have := nc_a_ge (L := L); linarith
  have hmt := (hL u w hg)
  have ht : (Y.Fl u w hg).t = D.R.t := hmt.2.1
  have hk := hT.gat_k u w hg
  have hjm : j ≤ D.R.m := (Finset.mem_Icc.1 hj).2
  have hN1 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t j : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + j * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hjm) _
    exact_mod_cast this
  have hN0 : (NN (D.gat u w hg).P.m (Y.Fl u w hg).t (j - 1) : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    unfold NN Ranks.N
    rw [ht]
    have : (D.gat u w hg).P.m + 1 + (j - 1) * (D.R.t + 1) ≤ D.R.k + D.R.m * (D.R.t + 1) := by
      rw [hk]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
    exact_mod_cast this
  have hde := nc_de_le (D.what₂.places.resChar w) (Y.Fl u w hg).t _ _ _ j hp (2 * L.sc.a) (D.R.N D.R.m : ℝ) hA hlog
    hN1 hN0 hS.1 hS.2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hNv : (Formalism.MainNotions.G.Nv X (D.what₂.places.resChar w) t0 : ℝ) = ((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card := by
    unfold Formalism.MainNotions.G.Nv
    rw [nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj]
  have hnP : (Formalism.MainNotions.G.nP D (D.what₂.places.resChar w) : ℝ) = ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) := by
    unfold Formalism.MainNotions.G.nP
    rw [if_neg (nc_notSg hg), nc_n_eq X Y hT hL u w hg t0 ht0]
  unfold nc_De Formalism.MainNotions.G.dl Formalism.MainNotions.G.Nm
  rw [hNv, hnP]
  have hl0 : 0 ≤ Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by linarith
  have hc1 : (0 : ℝ) ≤ ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℕ) * (D.R.N D.R.m : ℝ) ^ 2 *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) := by positivity
  have hc2 : (0 : ℝ) ≤ (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ) *
      Real.logb (D.what₂.places.resChar w) (2 * L.sc.a) ^ 2 := by positivity
  nlinarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

