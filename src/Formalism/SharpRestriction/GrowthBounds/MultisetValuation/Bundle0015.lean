module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0014
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0008

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoupledSumOfEntries
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset Formalism.MainNotions.G.LatticeSystems

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

def ThEq (a a' : X.G.Kf) (v : X.Pl) (j : ℕ) : Prop :=
  ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    Y.ThF j La La' = (a ^ (Y.len v j La.2) * a' ^ (Y.len v (j + 1) La'.2) *
      (p : X.G.Kf) ^ (-(((X.G.P.n' v / 2 : ℕ) : ℤ) * Y.volE v j La.2 La'.2))) •
      Y.Xi v j (Y.aw v j La La') (X.ind v j La.2 La'.2)

variable {Y}

theorem kernel_eq_theta {a a' : X.G.Kf} {v : X.Pl} {j : ℕ} (hTh : ThEq Y a a' v j) (La : X.Lt j) (La' : X.Lt (j + 1))
    (h1 : (X.Pj j).IsLatTup La.2) (h2 : (X.Pj (j + 1)).IsLatTup La'.2) (G : (X.Pj j).Xsp) :
    Y.ker j La La' G = T0 Y a a' v j La La' (X.ind v j La.2 La'.2) G := by
  unfold Pend.ker Pend.kerF T0 Traw
  rw [hTh La La' h1 h2]
  rfl

theorem ker_sum (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) {ι : Type} (s : Finset ι) (G : ι → (X.Pj j).Xsp) :
    Y.ker j La La' (∑ x ∈ s, G x) = ∑ x ∈ s, Y.ker j La La' (G x) := by
  unfold Pend.ker Pend.kerF
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply, Finset.smul_sum]

theorem cC_ne (hp : (p : X.G.Kf) ≠ 0) {a : X.G.Kf} (ha : a ≠ 0) (v : X.Pl) (j k : ℕ) : cC X a v j k ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ hp) (mul_ne_zero (zpow_ne_zero _ ha) (zpow_ne_zero _ hp))

theorem ker_dn_sum (hC : CountLoc) (hp : (p : X.G.Kf) ≠ 0) {a a' : X.G.Kf} (ha : a ≠ 0) (ha' : a' ≠ 0) {v : X.Pl}
    {j : ℕ} (hTh : ThEq Y a a' v j) (La : X.Lt j) (hLa : (X.Pj j).IsLatTup La.2) (c' : X.Lv.comp (j + 1))
    (L' : (X.Pj (j + 1)).Tup) (hL' : (X.Pj (j + 1)).IsLatTup L') (i : ℕ) (G : (X.Pj j).Xsp) :
    ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        Y.ker j La (c', Function.update L' (X.vJ (j + 1) v) L1) G =
      cA X a' v j i • ∑ l ∈ range (i + 1), (nC X v i l : X.G.Kf) •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) (La.2 (X.vJ j v)),
          (cC X a v j (i - l))⁻¹ • Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) (c', L') G := by
  have e1 : ∀ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      Y.ker j La (c', Function.update L' (X.vJ (j + 1) v) L1) G =
        cA X a' v j i • T0 Y a a' v j La (c', L') (X.ind v j La.2 (Function.update L' (X.vJ (j + 1) v) L1)) G := by
    intro L1 hL1
    have hE := (mem_EE _).1 hL1
    rw [kernel_eq_theta hTh La _ hLa (hk_latTup_update _ hL' _ L1 hE.1)]
    exact kernel_target_identity Y hp a a' ha' v j La c' L' i L1 hE _ G
  rw [Finset.sum_congr rfl e1, ← Finset.smul_sum, ← integral_span_coordinates, countG X hC v j i La.2 L' hLa hL', integral_span_coordinates]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [kernel_nsmul, integral_span_coordinates]
  congr 1
  refine Finset.sum_congr rfl fun A1 hA1 => ?_
  have hE := (mem_UP _).1 hA1
  rw [kernel_eq_theta hTh (La.1, Function.update La.2 (X.vJ j v) A1) (c', L') (hk_latTup_update _ hLa _ A1 hE.2.1) hL']
  have := kernel_source_identity Y hp a a' ha v j La (c', L') (i - l) A1 hE
    (X.ind v j (Function.update La.2 (X.vJ j v) A1) L') G
  rw [this, smul_smul, inv_mul_cancel₀ (cC_ne hp ha v j (i - l)), one_smul]

theorem hk_adj (D : Formalism.BasicNotions.D7) (h5b : MinkowskiCounting D X Y) (h6 : adm6 D X Y) (v : X.Pl) (j : ℕ) (hj : j < X.mm) (k : ℕ)
    (F : X.Fm j) (hF : F ∈ X.FQ j) (La' : X.Lt (j + 1)) (hLa' : (X.Pj (j + 1)).IsLatTup La'.2) :
    ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
          Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2) =
      ∑ La ∈ Y.Rep j, ((X.stab j La : X.G.Kf))⁻¹ • Y.ker j La La' (X.Tm v k j F La.1 La.2) := by
  classical
  apply MvPolynomial.ext
  intro n
  let φ : X.Lv.comp j → (X.Pj j).Tup → (X.Pj j).Tup → Y.Kc := fun c L L1 =>
    if (X.Pj j).IsLatTup L1 then AddMonoidAlgebra.coeff (Y.ker j (c, L1) La' (F c L)) n else 0
  have hφ : ∀ c (γ : (X.Lv.lev j c).Γ) L L1,
      φ c ((X.Lv.lev j c).smul γ L) ((X.Lv.lev j c).smul γ L1) = φ c L L1 := by
    intro c γ L L1
    simp only [φ]
    by_cases h : (X.Pj j).IsLatTup L1
    · rw [if_pos h, if_pos ((latTup_smul _ _ γ L1).2 h), (Eqv_of_FQ X hF).2 c γ L,
        h5b j hj c L1 La' γ (F c L) (vt_FQ X hF c L) h hLa']
    · rw [if_neg h, if_neg (fun h' => h ((latTup_smul _ _ γ L1).1 h'))]
  have key := h6 j hj.le (X.vJ j v) k φ hφ
  have hs : ∀ (La : X.Lt j) (z : Y.Kc), ((X.stab j La : X.G.Kf))⁻¹ • z = ((X.stab j La : Y.Kc))⁻¹ * z := by
    intro La z
    rw [Algebra.smul_def, map_inv₀, map_natCast]
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum]
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl fun La hLa => ?_
    have hlat := Y.Rep_lat j La hLa
    rw [MvPolynomial.coeff_smul, hs, MvPolynomial.coeff_sum]
    congr 1
    refine Eq.trans ?_ (finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))).symm
    refine Finset.sum_congr rfl fun A1 hA1 => ?_
    have hE := (mem_UP _).1 hA1
    simp only [φ]
    rw [if_pos (hk_latTup_update _ hlat _ A1 hE.2.1)]
  · refine Finset.sum_congr rfl fun La hLa => ?_
    have hlat := Y.Rep_lat j La hLa
    rw [MvPolynomial.coeff_smul, hs]
    congr 1
    refine Eq.trans (finsum_mem_eq_finite_toFinset_sum _ (edges_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))) ?_
    have e : X.Tm v k j F La.1 La.2 = ∑ L0 ∈ EE (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
        F La.1 (Function.update La.2 (X.vJ j v) L0) := Tminus_eq (X.Pj j) (X.vJ j v) k (F La.1) La.2
    rw [e, ker_sum, MvPolynomial.coeff_sum]
    refine Finset.sum_congr rfl fun L0 _ => ?_
    simp only [φ]
    rw [if_pos hlat]

def KAdj (Y : Pend X) (j : ℕ) (Cl Yb : Type) [Fintype Cl] [Fintype Yb] (wt : Cl → ℕ) (La : Cl → Yb → X.Lt j) : Prop :=
  ∀ (v : X.Pl) (k : ℕ), ∀ F ∈ X.FQ j, ∀ La' : X.Lt (j + 1), (X.Pj (j + 1)).IsLatTup La'.2 →
    ∑ x : Cl, ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k ((La x y).2 (X.vJ j v)),
        Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) La' (F (La x y).1 (La x y).2) =
      ∑ x : Cl, ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, Y.ker j (La x y) La' (X.Tm v k j F (La x y).1 (La x y).2)

theorem up_finsum (j : ℕ) (v : X.Pl) (k : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G : (X.Pj j).Xsp) :
    ∑ᶠ (L1 : Submodule ((X.Pj j).W (X.vJ j v)) (Fin ((X.Pj j).m + 1) → (X.Pj j).Qq (X.vJ j v)))
        (_ : IsEdge p ((X.Pj j).n' (X.vJ j v)) k ⟨La.2 (X.vJ j v), L1⟩),
        Y.ker j (La.1, Function.update La.2 (X.vJ j v) L1) La' G =
      ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
        Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' G :=
  finsum_mem_eq_finite_toFinset_sum _ (up_fin (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)))

theorem kadj_entry (D : Formalism.BasicNotions.D7) (h5b : MinkowskiCounting D X Y) (h6 : adm6 D X Y) (j : ℕ) (hj : j < X.mm) :
    KAdj Y j {La // La ∈ Y.Rep j} Unit (fun x => X.stab j x.1) (fun x _ => x.1) := by
  intro v k F hF La' hLa'
  have h := hk_adj D h5b h6 v j hj k F hF La' hLa'
  have hs : ∀ (n : ℕ) (z : XspC (X.Pj (j + 1)) Y.Kc), ((n : X.G.Kf))⁻¹ • z = ((n : Y.Kc))⁻¹ • z := by
    intro n z
    rw [← algebraMap_smul Y.Kc ((n : X.G.Kf))⁻¹ z, map_inv₀, map_natCast]
  simp only [hs] at h
  simp only [Finset.univ_unique, Finset.sum_singleton]
  exact ((Finset.sum_coe_sort (Y.Rep j) (fun La => ((X.stab j La : Y.Kc))⁻¹ •
      ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) k (La.2 (X.vJ j v)),
        Y.ker j (La.1, Function.update La.2 (X.vJ j v) A1) La' (F La.1 La.2))).trans h).trans
    (Finset.sum_coe_sort (Y.Rep j) (fun La => ((X.stab j La : Y.Kc))⁻¹ •
      Y.ker j La La' (X.Tm v k j F La.1 La.2))).symm

theorem ksa_of_adm (D : Formalism.BasicNotions.D7) (h4 : ArchimedeanSignatureMatching D X Y) (h5b : MinkowskiCounting D X Y) (h6 : adm6 D X Y) {j : ℕ} (hj : j < X.mm) :
    ∃ (cK : Y.Kc) (Cl Yb : Type) (_ : Fintype Cl) (_ : Fintype Yb) (wt : Cl → ℕ) (La : Cl → Yb → X.Lt j),
      KSum Y j cK Cl Yb wt La ∧ KAdj Y j Cl Yb wt La := by
  rcases Nat.lt_or_ge (j + 1) X.mm with h | h
  · obtain ⟨cK, _, _, h4'⟩ := h4.1 j h
    exact ⟨cK, _, _, inferInstance, inferInstance, _, _, ksum_entry Y hj.le h4', kadj_entry D h5b h6 j hj⟩
  · obtain ⟨cK, _, _, Cl, Yb, iC, iY, wt, La, h1, h2, h3, h5⟩ := h4.2 j (by omega)
    refine ⟨cK, Cl, Yb, iC, iY, wt, La, ⟨h1, h2, h3⟩, fun v k F hF La' hLa' => ?_⟩
    have := h5 v k F hF La' hLa'
    simp only [up_finsum] at this
    exact this

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpV
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime]

def ea_RestSExpV (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be → ∀ (j : ℕ) (v : X.Pl),
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin (X.G.P.n' v) → K', (∀ s, u s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-(
            ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
              sub2 p be (MvPowerSeries.X (Sum.inl ⟨v, e⟩)) (MvPowerSeries.X (Sum.inr ⟨v, e⟩)) :
            MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p))))))) =
          expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V

theorem ea_restSU_of (X : Sys p) (Y : Pend X) (hE : ea_RestSExpV X) : ea_RestSU X Y := by
  intro hD hbe v j U hU K' _ _ _ _ R' vp hvp hRp hOc
  obtain ⟨u, hu, V, hV, heq⟩ := hE hD Y.be hbe j v Y.Kc K' vp hvp
  have heq' : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K')
      (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v))))) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v u)) * V := heq
  refine ⟨u, fun s => hRp (hu s), ?_⟩
  rw [ThZA_mul, map_mul, atPi_mul, heq', mul_assoc]
  have hW : IntR R' (atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) :=
    restSIntA (X := X) j Y.Kc Y.Oc U hU K' R' vp hvp hRp hOc
  have hVW := IntR_mul (fun n => hRp (hV n)) hW
  have hp0 : (p : K') ≠ 0 := by
    rw [← map_natCast (algebraMap (K0 p) K') p]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  exact inClass_of_exp hp0 (fun k => hRp (piFact (p := p) (vp := vp) (hvp := hvp) (k := k))) (X.hhA K' j v u) (hhA_const (X := X) K' j v u) hVW

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.IntegralExpRename
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF expSum eq_of_low Gser)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff low_mul_sub)

section ExpFormal

variable {K : Type} [Field K]

theorem th_expK_zero {ι : Type} : expK (0 : MvPowerSeries ι K) = 1 := by
  ext n
  rw [coeff_expK, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    simp at h

theorem th_subst_expSum {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    (f : MvPowerSeries σ K) (M : ℕ) : MvPowerSeries.subst a (expSum f M) = expSum (MvPowerSeries.subst a f) M := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [expSum, expSum, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom ha, MvPowerSeries.subst_C]

theorem th_subst_expK {σ τ : Type} [Finite σ] (a : σ → MvPowerSeries τ K)
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) {f : MvPowerSeries σ K}
    (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst a (expK f) = expK (MvPowerSeries.subst a f) := by
  have ha : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hsf : MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero ha ha0 hf
  refine eq_of_low fun M => ?_
  have h1 := Formalism.DworkPowerSeriesWeights.low_subst_of_low ha0 (low_expK_sub hf M)
  have h2 := low_expK_sub hsf M
  have e : MvPowerSeries.subst a (expK f) - expK (MvPowerSeries.subst a f) =
      MvPowerSeries.subst a (expK f - expSum f M) -
        (expK (MvPowerSeries.subst a f) - expSum (MvPowerSeries.subst a f) M) := by
    rw [← th_subst_expSum ha, ← MvPowerSeries.coe_substAlgHom ha, map_sub]
    ring
  rw [e]
  exact low_sub h1 h2

theorem th_map_expK {ι K2 : Type} [Field K2] (φ : K →+* K2) (f : MvPowerSeries ι K) :
    MvPowerSeries.map φ (expK f) = expK (MvPowerSeries.map φ f) := by
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPowerSeries.coeff_map, coeff_expK, coeff_expK, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_inv₀, map_natCast, ← map_pow, MvPowerSeries.coeff_map]

end ExpFormal

section Param

variable (p : ℕ) [hp : Fact p.Prime]

def E0 {ι : Type} (f : MvPowerSeries ι (K0 p)) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ ∃ h : MvPowerSeries ι (WW p), MvPowerSeries.constantCoeff h = 0 ∧
    expK f = 1 + MvPowerSeries.map (algebraMap (WW p) (K0 p)) h

theorem integralExp_zero {ι : Type} : E0 p (0 : MvPowerSeries ι (K0 p)) := by
  refine ⟨map_zero _, 0, map_zero _, ?_⟩
  rw [th_expK_zero, map_zero, add_zero]

theorem integralExp_add {ι : Type} {f g : MvPowerSeries ι (K0 p)} (hf : E0 p f) (hg : E0 p g) : E0 p (f + g) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  obtain ⟨hg0, h', hh0', hge⟩ := hg
  refine ⟨by rw [map_add (f := _), hf0, hg0, add_zero], h + h' + h * h', by simp [hh0, hh0'], ?_⟩
  rw [expK_add hf0 hg0, hfe, hge, map_add (f := _), map_add (f := _), map_mul]
  ring

theorem integralExp_sum {ι α : Type} (s : Finset α) (f : α → MvPowerSeries ι (K0 p)) (h : ∀ a ∈ s, E0 p (f a)) :
    E0 p (∑ a ∈ s, f a) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty]
    exact integralExp_zero p
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact integralExp_add p (h a (Finset.mem_insert_self a s)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

def ren {κ σ R : Type} [CommRing R] (φ : κ → σ) (f : MvPowerSeries κ R) : MvPowerSeries σ R :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ R)) f

theorem integralExp_rename {κ σ : Type} [Finite κ] (φ : κ → σ) {f : MvPowerSeries κ (K0 p)} (hf : E0 p f) :
    E0 p (ren φ f) := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  have hXK : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have hXW : ∀ k, MvPowerSeries.constantCoeff (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p)) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X _
  have haW : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (WW p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXW
  have haK : MvPowerSeries.HasSubst (fun k => (MvPowerSeries.X (φ k) : MvPowerSeries σ (K0 p))) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hXK
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero haK hXK hf0, ren φ h,
    MvPowerSeries.constantCoeff_subst_eq_zero haW hXW hh0, ?_⟩
  unfold ren
  rw [← th_subst_expK _ hXK hf0, hfe, ← MvPowerSeries.coe_substAlgHom haK, map_add (f := _), map_one,
    MvPowerSeries.coe_substAlgHom haK, MvPowerSeries.map_subst haW]
  simp only [MvPowerSeries.map_X]

theorem exp_neg_integral {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : E0 p f) :
    ∃ w : MvPowerSeries ι (WW p), expK (-f) = MvPowerSeries.map (algebraMap (WW p) (K0 p)) w := by
  obtain ⟨hf0, h, hh0, hfe⟩ := hf
  refine ⟨MvPowerSeries.invOfUnit (1 + h) 1, ?_⟩
  have hinv : (1 + h) * MvPowerSeries.invOfUnit (1 + h) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by simp [hh0])
  have hneg : expK (-f) * expK f = 1 := by
    rw [← expK_add (by simp [hf0]) hf0, neg_add_cancel, th_expK_zero]
  calc expK (-f) = expK (-f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        ((1 + h) * MvPowerSeries.invOfUnit (1 + h) 1) := by rw [hinv, map_one, mul_one]
    _ = (expK (-f) * expK f) * MvPowerSeries.map (algebraMap (WW p) (K0 p))
        (MvPowerSeries.invOfUnit (1 + h) 1) := by
      rw [hfe, map_mul, map_add (f := _), map_one]
      ring
    _ = _ := by rw [hneg, one_mul]

end Param

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcModsub
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

theorem nc_modsub (a b e' n : ℕ) (ha : a < n) (hb : b < n) (he : e' < n) (h : (a + e') % n = b) :
    (b + n - a) % n = e' := by
  rcases Nat.lt_or_ge (a + e') n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at h
    subst h
    have : a + e' + n - a = e' + n := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt he]
  · have h2 : (a + e') % n = a + e' - n := by
      rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
    rw [h2] at h
    subst h
    have : a + e' - n + n - a = e' := by omega
    rw [this, Nat.mod_eq_of_lt he]

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem nc_shift (s s' : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ) :
    nc_iota Y u w hg t0 s + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' ↔
      (s.val + e) % (D.gat u w hg).P.n' (Y.vOf u w hg t0) = s'.val := by
  have hn := nc_n_eq X Y hT hL u w hg t0 ht0
  have key : ∀ (a b : ℕ), b < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) →
      (t0 + a • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) + e • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
        t0 + b • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) ↔
      (a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) = b) := by
    intro a b hb
    have hpos : 0 < addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) := by omega
    rw [add_assoc, ← add_nsmul, show (a + e) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) =
      ((a + e) % addOrderOf (Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) by
        rw [mod_addOrderOf_nsmul]]
    constructor
    · intro h
      exact nsmul_injOn_Iio_addOrderOf (show (a + e) % _ ∈ Set.Iio _ from Nat.mod_lt _ hpos)
        (show b ∈ Set.Iio _ from hb) (add_left_cancel h)
    · intro h; rw [h]
  have := key s.val s'.val (by rw [← hn]; exact s'.isLt)
  rw [← hn] at this
  exact this

include hL ht0 in
theorem nc_excl (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) (e : ℕ)
    (he : 2 * e + 1 ∈ dSet ((Y.Fl u w hg).TT (Y.vOf u w hg t0)) s) :
    Formalism.MainNotions.G.Excl D (D.what₂.places.resChar w) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) (2 * e + 1) := by
  have hloc := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  unfold dSet at he
  obtain ⟨s', hs', hd⟩ := Finset.mem_image.1 he
  rw [Finset.mem_filter] at hs'
  have hpos : 0 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by have := s.isLt; omega
  have hlt : 2 * e + 1 < (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by rw [← hd]; exact Nat.mod_lt _ hpos
  have hne : s' ≠ s := fun h => hs'.2 (by rw [h])
  refine ⟨⟨e, rfl⟩, nc_iota Y u w hg t0 s', ((hloc s').2.1).1 hs'.1, fun h => hne (hinj h), ?_⟩
  refine ⟨by omega, ?_, ?_⟩
  · rw [nc_partner hg]
    congr 1
    show nc_iota Y u w hg t0 s + (2 * e + 1) • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s'
    refine (nc_shift X Y hT hL u w hg t0 ht0 s s' (2 * e + 1)).2 ?_
    rw [← hd]
    have := s.isLt
    have := s'.isLt
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have : s.val + (s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) - s.val) =
        s'.val + (D.gat u w hg).P.n' (Y.vOf u w hg t0) := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt s'.isLt]
  · intro e' he0 he1 hp
    rw [nc_partner hg] at hp
    have hp' : nc_iota Y u w hg t0 s + e' • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w) = nc_iota Y u w hg t0 s' :=
      (Prod.mk.inj hp).2
    have h1 := (nc_shift X Y hT hL u w hg t0 ht0 s s' e').1 hp'
    have h2 := nc_modsub s.val s'.val e' _ s.isLt s'.isLt (by omega) h1
    rw [hd] at h2
    omega

end Orbit

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

