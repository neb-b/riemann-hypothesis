module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.GainOfCapacityLoss
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0020
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TwoSumsCondition
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaDegreeMapDomain
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section Res

variable {ι κ R : Type} [CommRing R] (f : κ → ι)

theorem ea_coeff_resV (a : MvPowerSeries ι R) (n : κ →₀ ℕ) :
    MvPowerSeries.coeff n (resV f a) = MvPowerSeries.coeff (n.mapDomain f) a := rfl

variable {f} (hf : Function.Injective f)

include hf

theorem ea_resV_mul (a b : MvPowerSeries ι R) : resV f (a * b) = resV f a * resV f b := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  simp_rw [ea_coeff_resV]
  symm
  refine Finset.sum_nbij' (fun q => (q.1.mapDomain f, q.2.mapDomain f))
    (fun q => (q.1.comapDomain f hf.injOn, q.2.comapDomain f hf.injOn)) ?_ ?_ ?_ ?_ ?_
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.mapDomain_add, hq]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq ⊢
    rw [← Finsupp.comapDomain_add_of_injective hf, hq, Finsupp.comapDomain_mapDomain f hf]
  · intro q _
    simp only [Finsupp.comapDomain_mapDomain f hf]
  · intro q hq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hs : ∀ m : ι →₀ ℕ, m ≤ n.mapDomain f → (↑m.support : Set ι) ⊆ Set.range f := by
      intro m hm x hx
      have hx' : x ∈ (n.mapDomain f).support := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff] at hx
        rw [Finsupp.mem_support_iff]
        have := hm x
        omega
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx')
      exact ⟨y, rfl⟩
    have h1 : q.1 ≤ n.mapDomain f := hq ▸ le_self_add
    have h2 : q.2 ≤ n.mapDomain f := hq ▸ le_add_self
    ext1
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h1)
    · exact Finsupp.mapDomain_comapDomain f hf _ (hs _ h2)
  · intro q _
    rfl

theorem ea_resV_C (c : R) : resV f (MvPowerSeries.C c : MvPowerSeries ι R) = MvPowerSeries.C c := by
  classical
  ext n
  rw [ea_coeff_resV, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  have h : n.mapDomain f = 0 ↔ n = 0 := by
    constructor
    · intro h
      exact Finsupp.mapDomain_injective hf (by rw [h, Finsupp.mapDomain_zero])
    · rintro rfl
      exact Finsupp.mapDomain_zero
  by_cases hn : n = 0
  · rw [if_pos (h.2 hn), if_pos hn]
  · rw [if_neg (mt h.1 hn), if_neg hn]

def ea_resHom : MvPowerSeries ι R →+* MvPowerSeries κ R where
  toFun := resV f
  map_one' := by
    have := ea_resV_C hf (1 : R)
    rwa [map_one, map_one] at this
  map_mul' := ea_resV_mul hf
  map_zero' := rfl
  map_add' _ _ := rfl

theorem ea_resHom_apply (a : MvPowerSeries ι R) : ea_resHom hf a = resV f a := rfl

omit hf in
theorem ea_resV_atPi (vp : R) (a : MvPowerSeries ι R) : resV f (atPi vp a) = atPi vp (resV f a) := by
  ext n
  rw [ea_coeff_resV]
  simp only [atPi, MvPowerSeries.coeff_apply, resV, Finsupp.degree_mapDomain]

end Res

theorem ea_atPi_subst {σ R : Type} [CommRing R] (vp : R) (a : MvPowerSeries σ R) :
    MvPowerSeries.subst (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) a = atPi vp a := by
  have h : (fun x => MvPowerSeries.C vp * (MvPowerSeries.X x : MvPowerSeries σ R)) =
      (Function.const σ vp) • MvPowerSeries.X := by
    funext x
    simp [MvPowerSeries.smul_eq_C_mul]
  rw [h, ← MvPowerSeries.rescale_eq_subst]
  ext n
  rw [MvPowerSeries.coeff_rescale]
  simp only [Finsupp.prod, Function.const_apply, Finset.prod_pow_eq_pow_sum, atPi,
    MvPowerSeries.coeff_apply, Finsupp.degree]
  rfl

theorem ea_eS_posSub {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν) (s : Fin n') (d : ℕ) :
    ea_eS hn (posSub s d) = ea_eS hn s - (d : ZMod (2 * ν)) := by
  subst hn
  have hd : d ≤ (s : ℕ) + 2 * ν * d :=
    le_add_left (Nat.le_mul_of_pos_left d (by have := NeZero.pos ν; omega))
  show ((((s : ℕ) + 2 * ν * d - d) % (2 * ν) : ℕ) : ZMod (2 * ν)) = ((s : ℕ) : ZMod (2 * ν)) - (d : ZMod (2 * ν))
  have h0 : ((2 * ν : ℕ) : ZMod (2 * ν)) = 0 := ZMod.natCast_self _
  rw [ZMod.natCast_mod, Nat.cast_sub hd]
  push_cast at h0 ⊢
  rw [h0]
  ring

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem ea_eps_inj (v : X.Pl) (j : ℕ) : Function.Injective (ea_eps X v j) := by
  intro y z h
  simp only [ea_eps, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact Prod.ext ((ea_e X v).symm.injective h1) (Prod.ext h2 h3)

theorem ea_res_sSA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (s : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) :
    resV (ea_eps X v j) (X.sSA K' j v s a b) = Formalism.InvariantFactorPaths.G7.sPos p (ea_e X v s) (a, b) := by
  classical
  have key : ∀ l : ℕ, ea_eps X v j (ea_e X v s - 2 * (l : ZMod _), a, b) =
      (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) := by
    intro l
    simp only [ea_eps, Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and, and_true]
    rw [Equiv.symm_apply_eq]
    simp only [ea_e]
    rw [ea_eS_posSub]
    push_cast
    ring
  ext n
  rw [ea_coeff_resV]
  simp only [Sys.sSA, Formalism.InvariantFactorPaths.G7.sPos, MvPowerSeries.coeff_apply, Finsupp.degree_mapDomain]
  refine Finset.sum_congr rfl fun l _ => ?_
  have hs : (Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))) =
      Finsupp.mapDomain (ea_eps X v j) (Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)) := by
    rw [Finsupp.mapDomain_single, key l, pow_mul]
  have hiff : Finsupp.mapDomain (ea_eps X v j) n = Finsupp.single (⟨v, (posSub s (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l)) ↔
      n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l) := by
    rw [hs]
    exact (Finsupp.mapDomain_injective (ea_eps_inj X v j)).eq_iff
  by_cases h : n = Finsupp.single (ea_e X v s - 2 * (l : ZMod _), (a, b)) ((p ^ 2) ^ l)
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (mt hiff.1 h), if_neg h]

theorem ea_res_hhA (K' : Type) [Field K'] (v : X.Pl) (j : ℕ) (u : Fin (X.G.P.n' v) → K') :
    resV (ea_eps X v j) (X.hhA K' j v u) = Formalism.InvariantFactorPaths.G7.hhS p fun s => u ((ea_e X v).symm s) := by
  rw [← ea_resHom_apply (ea_eps_inj X v j)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sys.hhA, map_sum, map_mul, map_pow, ea_resHom_apply, ea_resV_C (ea_eps_inj X v j),
    ea_res_sSA]
  simp only [Formalism.InvariantFactorPaths.G7.hhS, Fintype.sum_prod_type]
  refine Fintype.sum_equiv (ea_e X v) _ _ (fun s => ?_)
  rw [Equiv.symm_apply_apply]
  simp only [ea_e, ea_eS_posAdd, Nat.cast_one]

theorem ea_brClass : ea_BrClass X := by
  intro v j K' _ _ vp u F hF
  obtain ⟨g, hg, hc⟩ := hF
  rw [ea_atPi_subst, ← ea_resV_atPi, ← ea_res_hhA]
  refine ⟨fun i => resV (ea_eps X v j) (g i), fun i n => ?_, fun n => ?_⟩
  · rw [ea_coeff_resV]
    exact hg i _
  · rw [ea_coeff_resV, hc, Finsupp.degree_mapDomain]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [← ea_resHom_apply (ea_eps_inj X v j), ← map_pow, ← map_mul]
    rw [ea_resHom_apply, ea_coeff_resV]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EbBrJet
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

def eb_Pc (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K') :=
  ∏ s : ea_S X v, Formalism.DworkPowerSeriesWeights.minorProd
    (fun (i : Fin (NN X.G.P.m X.t j)) (b : Fin (NN X.G.P.m X.t (j + 1))) =>
      (∑ a : Fin (NN X.G.P.m X.t j), MvPolynomial.C (MvPolynomial.X (s, i, a)) * MvPolynomial.X (s, a, b) :
        MvPolynomial (Formalism.DworkPowerSeriesWeights.ZV (2 * (X.G.P.n' v / 2)) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (MvPolynomial (ea_S X v × Fin (NN X.G.P.m X.t j) × Fin (NN X.G.P.m X.t j)) K')))
    (ea_hts X v j s) (ea_hp X v j s) (ea_Ic X v j I s)

theorem eb_poly (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (I : X.ColCh j) :
    MvPolynomial.map (MvPolynomial.map (Int.castRingHom K')) (X.PIv j I v) =
      MvPolynomial.rename (ea_eps X v j) (MvPolynomial.map
        (MvPolynomial.rename (eb_phi X v j) : MvPolynomial _ K' →ₐ[K'] MvPolynomial _ K').toRingHom
        (eb_Pc X v j K' I)) := by
  unfold Sys.PIv eb_Pc Formalism.DworkPowerSeriesWeights.minorProd
  simp only [map_prod]
  refine (Fintype.prod_equiv (ea_e X v).symm _ _ fun s => ?_).symm
  rw [Finset.prod_range]
  exact Finset.prod_congr rfl fun c _ => eb_fac X v j K' I s c

theorem eb_jet (v : X.Pl) (j : ℕ) (K' : Type) [Field K'] (F : MvPowerSeries (X.ZA j) K') (I : X.ColCh j) :
    applyD (X.PIv j I v) F = MvPolynomial.rename (eb_phi X v j)
      (Formalism.DworkPowerSeriesWeights.frameJet (ea_colN X v j) (ea_hts X v j) (ea_hp X v j) (ea_Ic X v j I) (resV (ea_eps X v j) F)) := by
  rw [eb_applyD, eb_poly, eb_J_rename _ (eb_eps_inj X v j), eb_J_map]
  rfl

theorem eb_brJet : ea_BrJet X := by
  intro v j K' _ F I n
  rw [eb_jet]
  by_cases h : ∃ n', Finsupp.mapDomain (eb_phi X v j) n' = n
  · obtain ⟨n', rfl⟩ := h
    exact Or.inr ⟨n', MvPolynomial.coeff_rename_mapDomain _ (eb_phi_inj X v j) _ n'⟩
  · exact Or.inl (MvPolynomial.coeff_rename_eq_zero _ _ _ fun u hu => absurd ⟨u, hu⟩ h)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FrobeniusCongruenceWitt
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF altF)

variable {p : ℕ} [hp : Fact p.Prime]

theorem sx_dual_even {n' : ℕ} (B : OmBasis p n') (i i' : Fin (n' / 2)) :
    ∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r) = if i = i' then 1 else 0 := by
  classical
  have hAB : (Matrix.of fun (r j : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.om r)) *
      (Matrix.of fun (j r' : Fin (n' / 2)) => (sigW p)^[2 * j.val] (B.omS r')) = 1 := by
    refine Matrix.ext fun r r' => ?_
    rw [Matrix.mul_apply, Matrix.one_apply, ← B.dual r r']
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.of_apply, Matrix.of_apply, iterate_map_mul]
  have hBA := mul_eq_one_comm.mp hAB
  have h := congrFun (congrFun hBA i) i'
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  simpa using h

theorem sx_dual {n' : ℕ} (B : OmBasis p n') (hev : Even n') (a b : Fin n') (hab : a.val % 2 = b.val % 2) :
    ∑ r, (sigW p)^[a.val] (B.omS r) * (sigW p)^[b.val] (B.om r) = if a = b then 1 else 0 := by
  classical
  obtain ⟨k, hk⟩ := hev
  have ha := a.isLt
  have hb := b.isLt
  let i : Fin (n' / 2) := ⟨a.val / 2, by omega⟩
  let i' : Fin (n' / 2) := ⟨b.val / 2, by omega⟩
  have hE := sx_dual_even B i i'
  have hii : (i = i') ↔ (a = b) := by
    simp only [i, i', Fin.ext_iff]
    constructor
    · intro h
      omega
    · intro h
      rw [h]
  rcases Nat.mod_two_eq_zero_or_one a.val with h0 | h1
  · have e1 : (sigW p)^[a.val] = (sigW p)^[2 * i.val] := by
      congr 1
      show a.val = 2 * (a.val / 2)
      omega
    have e2 : (sigW p)^[b.val] = (sigW p)^[2 * i'.val] := by
      congr 1
      show b.val = 2 * (b.val / 2)
      omega
    rw [e1, e2, hE]
    by_cases h : a = b
    · rw [if_pos h, if_pos (hii.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (hii.mp h'))]
  · have e1 : (sigW p)^[a.val] = (sigW p) ∘ (sigW p)^[2 * i.val] := by
      rw [← Function.iterate_succ']
      congr 1
      show a.val = 2 * (a.val / 2) + 1
      omega
    have e2 : (sigW p)^[b.val] = (sigW p) ∘ (sigW p)^[2 * i'.val] := by
      rw [← Function.iterate_succ']
      congr 1
      show b.val = 2 * (b.val / 2) + 1
      omega
    rw [e1, e2]
    simp only [Function.comp_apply]
    have hsig : ∑ r, sigW p ((sigW p)^[2 * i.val] (B.omS r)) * sigW p ((sigW p)^[2 * i'.val] (B.om r)) =
        sigW p (∑ r, (sigW p)^[2 * i.val] (B.omS r) * (sigW p)^[2 * i'.val] (B.om r)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun r _ => (map_mul _ _ _).symm
    rw [hsig, hE]
    by_cases h : a = b
    · rw [if_pos h, if_pos (hii.mpr h), map_one]
    · rw [if_neg h, if_neg (fun h' => h (hii.mp h')), map_zero]

theorem frobenius_congruence_witt (a : WW p) : ∃ y : WW p, sigW p a = a ^ p + p * y := by
  obtain ⟨y, hy⟩ := Formalism.InvariantFactorPaths.G7.WModel.frob_sub_pow p a
  exact ⟨y, by unfold sigW; linear_combination hy⟩

theorem sx_lift {ι K' : Type} [Field K'] {R : Subring K'} {f : MvPowerSeries ι K'} (hf : IntR R f) :
    ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = f := by
  refine ⟨fun m => ⟨MvPowerSeries.coeff m f, hf m⟩, ?_⟩
  ext m
  rfl

theorem sx_sum_pow {A α : Type} [CommRing A] (s : Finset α) (x : α → A) :
    ∃ r : A, (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + (p : A) * r := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [zero_pow hp.out.ne_zero]⟩
  | insert a s ha ih =>
    obtain ⟨r1, hr1⟩ := ih
    obtain ⟨r2, hr2⟩ := exists_add_pow_prime_eq hp.out (x a) (∑ i ∈ s, x i)
    refine ⟨r1 + x a * (∑ i ∈ s, x i) * r2, ?_⟩
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hr2, hr1]
    ring

theorem sx_frob_sum {ι α K' : Type} [Field K'] (R : Subring K') (s : Finset α) (x : α → MvPowerSeries ι K')
    (hx : ∀ i ∈ s, IntR R (x i)) :
    ∃ Y, IntR R Y ∧ (∑ i ∈ s, x i) ^ p = ∑ i ∈ s, x i ^ p + MvPowerSeries.C (p : K') * Y := by
  classical
  have hlift : ∀ i ∈ s, ∃ f0 : MvPowerSeries ι R, MvPowerSeries.map R.subtype f0 = x i :=
    fun i hi => sx_lift (hx i hi)
  choose y hy using hlift
  let y' : α → MvPowerSeries ι R := fun i => if h : i ∈ s then y i h else 0
  obtain ⟨r, hr⟩ := sx_sum_pow (p := p) s y'
  refine ⟨MvPowerSeries.map R.subtype r, fun n => ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff n r).2
  · have hsum : ∀ i ∈ s, MvPowerSeries.map R.subtype (y' i) = x i := fun i hi => by
      simp only [y', dif_pos hi]
      exact hy i hi
    have h2 := congrArg (MvPowerSeries.map R.subtype) hr
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_pow, map_sum, map_add (f := _), map_mul, map_natCast] at h2
    have e3 : ∑ i ∈ s, (MvPowerSeries.map R.subtype (y' i)) ^ p = ∑ i ∈ s, x i ^ p :=
      Finset.sum_congr rfl fun i hi => by rw [hsum i hi]
    rw [Finset.sum_congr rfl hsum, e3] at h2
    rw [h2, map_natCast]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NdLszLe
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

section Local

variable {p : ℕ} {G : Formalism.MainNotions.G.GAtP p} (Fl : Formalism.MainNotions.G.Fills G) (v : Fin G.P.nV)

theorem nd_al_le (s : Fin (G.P.n' v)) (hs : s ∈ Fl.TT v) (hm : 2 ≤ G.P.m) :
    al (Fl.TT v) (G.P.lam0 v) s ≤ Fl.a v s + (Fl.c : ℤ) := by
  unfold al
  rw [if_pos hs, lambda_index_one v s hm, lambda_index_two v s hm]
  have hb := (Fl.base v s).1 hs
  have := (abs_le.1 (hb.2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).1
  have h0 : G.P.lam0 v s ⟨0, by omega⟩ = Fl.a v s := hb.1
  omega

theorem nd_c_le_w (s : Fin (G.P.n' v)) (l : ℕ) (hl : 1 ≤ l) : (Fl.c : ℤ) ≤ Fl.w v l s :=
  le_trans (le_trans (le_max_left _ _) (Fl.w_ge v s)) (nc_w_ge Fl v s l hl)

theorem nd_lam_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ G.P.m + 1)
    (h : s ∈ Fl.TT v → 2 ≤ i) : lamI (G.P.lam0 v) s i ≤ (Fl.c : ℤ) := by
  unfold lamI
  rw [dite_eq_left ⟨h1, h2⟩]
  have hb := Fl.base v s
  by_cases hs : s ∈ Fl.TT v
  · have h3 := (abs_le.1 ((hb.1 hs).2.2 ⟨1, by omega⟩ (by simp) (by simp; omega))).2
    have hd : Antitone (G.P.lam0 v s) := G.P.dom v s
    have h4 := hd (show (⟨1, by omega⟩ : Fin (G.P.m + 1)) ≤ ⟨i - 1, by omega⟩ by
      rw [Fin.le_def]; have := h hs; simp only; omega)
    omega
  · exact (abs_le.1 (hb.2 hs _)).2

theorem nd_lsz_le (s : Fin (G.P.n' v)) (hm : 2 ≤ G.P.m) (j : ℕ) (hj : 1 ≤ j) :
    lsz Fl.t (Fl.TT v) (G.P.lam0 v) (Fl.w v) j s ≤ (NN G.P.m Fl.t j : ℤ) * ((Fl.c : ℤ) + Fl.w v j s) := by
  unfold lsz
  have h1N : 1 ∈ Icc 1 (NN G.P.m Fl.t j) := Finset.mem_Icc.2 ⟨le_rfl, by unfold NN; omega⟩
  have e : ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), nu Fl.t (G.P.lam0 v) (Fl.w v) j s i - al (Fl.TT v) (G.P.lam0 v) s =
      ∑ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq' _ 1, if_pos h1N]
  rw [e]
  have hb : ∀ i ∈ Icc 1 (NN G.P.m Fl.t j), (nu Fl.t (G.P.lam0 v) (Fl.w v) j s i -
        if i = 1 then al (Fl.TT v) (G.P.lam0 v) s else 0) ≤ (Fl.c : ℤ) + Fl.w v j s := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    unfold nu
    by_cases hik : i ≤ G.P.m + 1
    · rw [if_pos ⟨hi.1, hik⟩]
      by_cases hi1 : i = 1
      · subst hi1
        rw [if_pos rfl]
        unfold al
        by_cases hs : s ∈ Fl.TT v
        · rw [if_pos hs]
          have := nd_lam_le Fl v s hm 2 (by omega) (by omega) (fun _ => le_rfl)
          omega
        · rw [if_neg hs]
          have := nd_lam_le Fl v s hm 1 le_rfl (by omega) (fun h => absurd h hs)
          omega
      · rw [if_neg hi1]
        have := nd_lam_le Fl v s hm i hi.1 hik (fun _ => by omega)
        omega
    · rw [if_neg (fun h => hik h.2), if_pos ⟨by omega, hi.2⟩, if_neg (by omega)]
      have := nd_c_le_w Fl v s ((i - (G.P.m + 2)) / (Fl.t + 1) + 1) (Nat.le_add_left 1 _)
      have hc : (0 : ℤ) ≤ (Fl.c : ℤ) := Int.natCast_nonneg _
      omega
  have := Finset.sum_le_sum hb
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at this
  simpa using this

end Local

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

