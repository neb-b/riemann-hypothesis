module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0008
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.YEPEComm

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.AllPlacesOfRestrictions
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem sSA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) : MvPowerSeries.constantCoeff (X.sSA K' j v e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : X.ZA j →₀ ℕ).degree + 1),
    if (0 : X.ZA j →₀ ℕ) = Finsupp.single (⟨v, (posSub e (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))
      then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') :
    MvPowerSeries.constantCoeff (X.hhA K' j v u) = 0 := by
  unfold Sys.hhA
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sSA_const, mul_zero, Finset.sum_const_zero]

theorem coordZA_const (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)) f g

theorem all_places_of_restrictions (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExpA X) (hI : RestSIntA X) : ExpansionsMultiply D X Y := by
  intro j hj La La' h1 h2 φ K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  obtain ⟨u, hu, V, hV, hEq⟩ := hE (hA.1 p) Y.be hbe j Ph hPh Y.Kc K' vp hvp
  refine ⟨u, fun v s => hRp (hu v s), fun h' hh' => ?_⟩
  choose h0' G hG hGE using hh'
  have hW := hI j Y.Kc Y.Oc U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j (Y.ThA j La La' φ))) =
      (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * h' v))) *
        ((∏ v, expK (MvPowerSeries.C (vp ^ (p + 1)) * G v)) * V *
          atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) := by
    rw [hTh, ThZA_mul, map_mul, atPi_mul, hEq,
      Finset.prod_congr rfl fun v _ => exp_change K' (vp ^ (p + 1)) (X.hhA K' j v (u v)) (h' v) (G v)
        (hhA_const X K' j v (u v)) (h0' v) (hGE v), Finset.prod_mul_distrib]
    ring
  rw [e1]
  exact inProd_of_exp (pK'_ne p K') hc h' h0'
    (IntR_mul (IntR_mul (IntR_prod _ _ fun v _ => IntR_expK hc (hG v)) (IntR_mono hRp hV)) hW)

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FacEmbDomain
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

namespace Gen

theorem fac_embDomain {σ τ : Type} (e : σ ↪ τ) (κ : σ →₀ ℕ) : fac (Finsupp.embDomain e κ) = fac κ := by
  classical
  unfold fac
  rw [Finsupp.support_embDomain, Finset.prod_map]
  simp [Finsupp.embDomain_apply]

theorem jp_rename {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] {ι : Pl → Type} (v : Pl)
    (P : MvPolynomial (ι v) A) (g : MvPowerSeries (ι v) K) :
    jp (MvPolynomial.rename (Sigma.mk v) P) (atP v g) = jp P g := by
  classical
  have hinj : Function.Injective (Sigma.mk v : ι v → Σ v, ι v) := sigma_mk_injective
  unfold jp atP
  rw [MvPolynomial.support_rename_of_injective hinj,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have he : Finsupp.mapDomain (Sigma.mk v) κ = Finsupp.embDomain (Function.Embedding.sigmaMk v) κ :=
    by rw [Finsupp.embDomain_eq_mapDomain]; rfl
  rw [MvPolynomial.coeff_rename_mapDomain _ hinj, he, fac_embDomain, MvPowerSeries.coeff_embDomain_rename]

end Gen

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def en_mapP (Kc σ τ : Type) [Field Kc] :
    MvPolynomial σ (MvPolynomial τ ℤ) →+* MvPolynomial σ (MvPolynomial τ Kc) :=
  MvPolynomial.map (MvPolynomial.map (Int.castRingHom Kc))

theorem en_applyD_eq {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    applyD P f = Gen.jp (en_mapP Kc σ τ P) f := by
  classical
  unfold applyD Gen.jp en_mapP
  symm
  refine (Finset.sum_subset (MvPolynomial.support_map_subset _ P) ?_).trans ?_
  · intro n _ hn
    simp only [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn, smul_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.coeff_map]
    unfold Gen.fac
    push_cast
    rfl

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_Ploc (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (MvPolynomial (X.FrI j) Y.Kc) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (X.FrI j) Y.Kc)) ^ (X.colExp j I i0 v s c) *
    Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
      ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X ((s, a, I v s c i'.val) :
            Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))))

theorem en_mapP_PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    en_mapP Y.Kc (X.ZA j) (X.FrI j) (PIvS X j I i0 v) =
      MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
  unfold en_mapP PIvS en_Ploc Sys.colFac
  simp only [map_prod, map_mul, map_pow, map_natCast, RingHom.map_det, AlgHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 2
  ext i i'
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.of_apply, map_sum, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.FormValuationGeNegDegree
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime]

theorem Tm_add (X : Sys p) (v : X.Pl) (i J : ℕ) (F F' : X.Fm J) :
    X.Tm v i J (F + F') = X.Tm v i J F + X.Tm v i J F' := by
  funext c L
  show (X.Pj J).Tminus (X.vJ J v) i (F c + F' c) L =
    (X.Pj J).Tminus (X.vJ J v) i (F c) L + (X.Pj J).Tminus (X.vJ J v) i (F' c) L
  rw [tm_eq, tm_eq, tm_eq, ← Finset.sum_add_distrib]
  rfl

theorem Tm_smul (X : Sys p) (v : X.Pl) (i J : ℕ) (a : X.G.Kf) (F : X.Fm J) :
    X.Tm v i J (a • F) = a • X.Tm v i J F := by
  funext c L
  show (X.Pj J).Tminus (X.vJ J v) i (a • F c) L = a • (X.Pj J).Tminus (X.vJ J v) i (F c) L
  rw [tm_eq, tm_eq, Finset.smul_sum]
  rfl

theorem Tt_add (X : Sys p) (v : X.Pl) (i J : ℕ) (F F' : X.Fm J) :
    X.Tt v i J (F + F') = X.Tt v i J F + X.Tt v i J F' := by
  unfold Sys.Tt
  split_ifs
  · rfl
  · rw [Tm_add, smul_add]

theorem Tt_smul (X : Sys p) (v : X.Pl) (i J : ℕ) (a : X.G.Kf) (F : X.Fm J) :
    X.Tt v i J (a • F) = a • X.Tt v i J F := by
  unfold Sys.Tt
  split_ifs
  · rfl
  · rw [Tm_smul, smul_comm]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.LiftBoundOfIntegrality
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem sum_Icc_shift (f : ℕ → ℝ) (m : ℕ) : ∑ j ∈ Icc 1 m, f j = ∑ j ∈ range m, f (j + 1) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem sum_ind {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset ι) (f : ι → ℝ) :
    ∑ v ∈ A, f v = ∑ v, if v ∈ A then f v else 0 := by
  rw [← Finset.sum_filter]
  congr 1
  ext v
  simp

theorem basic₂ {ι : Type} [Fintype ι] [DecidableEq ι] (mm : ℕ) (VV BB : Finset ι) (hBB : BB ⊆ VV)
    (Gn G0n PRn Prr : ι → ℕ → ℝ) (S : ι → ℝ) (dG : ℕ → ℝ) (inB : ℕ → ι → Prop) [∀ j v, Decidable (inB j v)]
    (hin : ∀ j v, inB j v ↔ v ∈ BB ∧ G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    (hPR : ∀ v ∈ VV, ∀ j < mm, Prr v (j + 1) ≤ PRn v (j + 1))
    (hS : ∀ v ∈ VV, ∑ j ∈ range mm, max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 ≤ S v) :
    ∑ j ∈ range mm, (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) +
        ∑ v ∈ univ \ VV, G0n v (j + 1)) - ∑ j ∈ range mm, dG j ≤
      ∑ v ∈ VV \ BB, S v + ∑ j ∈ range mm, (∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1)) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
  have hS' : ∑ j ∈ range mm, ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0)
      ≤ ∑ v ∈ VV \ BB, S v := by
    rw [Finset.sum_comm, sum_ind (VV \ BB) S]
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV \ BB
    · simp only [hv, ↓reduceIte]
      exact hS v (Finset.mem_sdiff.1 hv).1
    · simp [hv]
  have key : ∀ j ∈ range mm,
      (∑ v ∈ VV, max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) + ∑ v ∈ univ \ VV, G0n v (j + 1)) - dG j ≤
      ∑ v, (if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
      ((∑ v, (if inB j v then Gn v (j + 1) else G0n v (j + 1))) - dG j -
        ∑ v, (if inB j v then Prr v (j + 1) else 0)) := by
    intro j hj
    have hj' : j < mm := Finset.mem_range.1 hj
    suffices h : ∑ v, ((if v ∈ VV then max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) else 0) +
        (if v ∈ univ \ VV then G0n v (j + 1) else 0) + (if inB j v then Prr v (j + 1) else 0)) ≤
        ∑ v, ((if v ∈ VV \ BB then max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 else 0) +
        (if inB j v then Gn v (j + 1) else G0n v (j + 1))) by
      rw [sum_ind VV, sum_ind (univ \ VV)]
      simp only [Finset.sum_add_distrib] at h
      linarith
    refine Finset.sum_le_sum fun v _ => ?_
    by_cases hv : v ∈ VV
    · have hv2 : v ∉ univ \ VV := by simp [hv]
      by_cases hb : v ∈ BB
      · have hv3 : v ∉ VV \ BB := by simp [hb]
        by_cases hi : inB j v
        · have h1 := ((hin j v).1 hi).2
          have h2 := hPR v hv j hj'
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_left h1]
          linarith
        · have h1 : ¬ (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1)) := fun h => hi ((hin j v).2 ⟨hb, h⟩)
          simp only [hv, hv2, hv3, hi, ↓reduceIte]
          rw [max_eq_right (le_of_lt (not_le.1 h1))]
          linarith
      · have hv3 : v ∈ VV \ BB := Finset.mem_sdiff.2 ⟨hv, hb⟩
        have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
        simp only [hv, hv2, hv3, hi, ↓reduceIte]
        have hm : max (Gn v (j + 1) - PRn v (j + 1)) (G0n v (j + 1)) ≤
            max (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0 + G0n v (j + 1) := by
          have := le_max_left (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          have := le_max_right (Gn v (j + 1) - PRn v (j + 1) - G0n v (j + 1)) 0
          exact max_le (by linarith) (by linarith)
        linarith
    · have hv2 : v ∈ univ \ VV := by simp [hv]
      have hb : v ∉ BB := fun h => hv (hBB h)
      have hv3 : v ∉ VV \ BB := by simp [hv]
      have hi : ¬ inB j v := fun h => hb ((hin j v).1 h).1
      simp only [hv, hv2, hv3, hi, ↓reduceIte]
      linarith
  have hsum := Finset.sum_le_sum key
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum ⊢
  linarith

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem PrZ_cast (v : X.Pl) (j : ℕ) :
    ((PrZ X.t X.G.P.r (X.G.P.lam0 v) (X.w v) j : ℤ) : ℝ) = X.Conclusion₂ v j := by
  simp only [Sys.Conclusion₂, PrZ, Pr]
  push_cast
  congr 1
  obtain ⟨k, hk⟩ := (X.G.P.setting v).even
  rw [hk]
  have h2 : ((k + k : ℕ) : ℤ) / 2 = (k : ℤ) := by omega
  rw [h2]
  push_cast
  ring

theorem lift_bound_of_integrality (D : Formalism.BasicNotions.D7) {Y : Pend X} (hfr : IsFractionRing X.G.O X.G.Kf) (hp : (p : X.G.Kf) ≠ 0)
    (hL : LinD X) (hF : FormB X Y) (hE : EntCondition X Y) (h4 : Conclusion4 D X)
    (hy : ∀ v, ∀ F ∈ X.Int 0, X.yv v F ∈ X.Int 0) : LowTermBound D X Y := by
  intro Gn G0n PRn S VV hG hLow hPr hS F hF
  choose u m hu hm hrest using h4
  have hπ : (algebraMap X.G.O X.G.Kf X.vp) ≠ 0 := by
    intro h0
    exact X.unif.ne_zero ((IsFractionRing.injective X.G.O X.G.Kf) (h0.trans (map_zero _).symm))
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨BB, hBB, Lv, hnd, hLv, F0, hF0, rfl⟩ := hx
    obtain ⟨F1, hF1, rfl⟩ := hF0
    let Q : ℕ → X.Pl → Bool := fun j v => decide (G0n v (j + 1) ≤ Gn v (j + 1) - PRn v (j + 1))
    have hmemL : ∀ v, v ∈ Lv ↔ v ∈ BB := fun v => by rw [← hLv, List.mem_toFinset]
    have h1 : ∀ v ∈ Lv, ∀ j < X.mm, Gn v (j + 1) ≤ X.gv v (j + 1) := fun v hv j hj =>
      hG v (hBB ((hmemL v).1 hv)) (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    have hmi := main_ind hfr hp hL hF hE u m hu (fun v j hj => (hrest v j hj).2.1)
      (fun v j hj => (hrest v j hj).2.2.1) (fun v j hj => (hrest v j hj).1) hy Lv hnd Gn G0n Q h1 hLow
      X.mm le_rfl F1 hF1
    have hnum : (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) ≤ ∑ v ∈ VV \ BB, S v + ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j := by
      rw [sum_Icc_shift]
      have hb := basic₂ X.mm VV BB hBB Gn G0n PRn (fun v j => X.Conclusion₂ v j) S (fun j => (X.dG j : ℝ))
        (fun j v => v ∈ Lv.filter (Q j))
        (fun j v => by simp only [List.mem_filter, hmemL, Q, decide_eq_true_eq])
        (fun v hv j hj => hPr v hv (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩))
        (fun v hv => by rw [← sum_Icc_shift (fun j => max (Gn v j - PRn v j - G0n v j) 0)]; exact hS v hv)
      refine hb.trans (le_of_eq ?_)
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [bbJ, PrS]
      push_cast [PrZ_cast]
      rfl
    unfold Sys.vGe scale at hmi ⊢
    obtain ⟨I, hI, hIeq⟩ := hmi
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply] at hIeq ⊢
    rw [fold_eq hL]
    set g := ∑ j ∈ range X.mm, bbJ X Lv Gn G0n Q j with hg
    set T : ℝ := (∑ j ∈ Icc 1 X.mm, (∑ v ∈ VV, max (Gn v j - PRn v j) (G0n v j) + ∑ v ∈ univ \ VV, G0n v j) -
        ∑ j ∈ range X.mm, (X.dG j : ℝ)) with hT
    have hceil : ⌈T * (X.eO : ℝ)⌉ ≤ ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ := by
      rw [Int.ceil_le]
      push_cast
      have h8 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
      have h6 : (∑ v ∈ VV \ BB, S v) * (X.eO : ℝ) ≤ ∑ v ∈ VV \ BB, (⌈S v * (X.eO : ℝ)⌉ : ℝ) := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun v _ => Int.le_ceil _
      have h7 := Int.le_ceil (g * (X.eO : ℝ))
      have h9 := mul_le_mul_of_nonneg_right hnum h8
      nlinarith
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = ⌈g * (X.eO : ℝ)⌉ + ∑ v ∈ VV \ BB, ⌈S v * (X.eO : ℝ)⌉ - ⌈T * (X.eO : ℝ)⌉ :=
      ⟨_, Int.toNat_of_nonneg (by omega)⟩
    refine ⟨X.vp ^ n • I, Submodule.smul_mem _ _ hI, ?_⟩
    simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    rw [map_smul, map_smul, ← hIeq, ← algebraMap_smul X.G.Kf (X.vp ^ n) I, smul_smul, smul_smul]
    congr 1
    unfold Sys.vsc
    rw [map_pow, ← zpow_natCast, ← zpow_add₀ hπ, ← zpow_add₀ hπ, hn]
    congr 1
    ring
  | zero =>
    unfold Sys.vGe
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    unfold Sys.vGe at *
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    unfold Sys.vGe at *
    rw [← algebraMap_smul X.G.Kf a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

