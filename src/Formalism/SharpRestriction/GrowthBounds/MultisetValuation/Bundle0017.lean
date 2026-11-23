module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0016
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0003

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.DworkExponentialRestrictions
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser Aser Aser')

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

abbrev wK (p : ℕ) [Fact p.Prime] (c : WW p) : K0 p := algebraMap (WW p) (K0 p) c

def RestBeta (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
    ∃ c : WW p, (sigW p)^[2] c = c ∧ E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))

def RestGc (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → ∀ c : WW p, (sigW p)^[2] c = c → ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      MvPowerSeries.subst (tOf vp μ (coordZ B K' 1)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
          (Gt p (Eidx n' r0 r1) (wK p c) (wK p (sigW p c)))))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestGcA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ c : WW p, (sigW p)^[2] c = c → ∀ (j : ℕ)
    (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∀ μ : PowerSeries K', PowerSeries.constantCoeff μ = 0 →
      (PowerSeries.subst μ (lamF p vp) : PowerSeries K') = PowerSeries.X →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        MvPowerSeries.subst (tOf vp μ (X.coordZA K' j)) (expK (-(MvPowerSeries.map (algebraMap (K0 p) K')
            (Gt p (X.EA j) (wK p c) (wK p (sigW p c)))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

section

variable {p : ℕ} [hp : Fact p.Prime]

theorem th_Gser_const (c c' : K0 p) : MvPowerSeries.constantCoeff (Gser p c c') = 0 := by
  have hA : MvPowerSeries.constantCoeff (Aser (K0 p) p) = 0 := by
    show Aser (K0 p) p 0 = 0
    simp [Aser]
  have hA' : MvPowerSeries.constantCoeff (Aser' (K0 p) p) = 0 := by
    show Aser' (K0 p) p 0 = 0
    simp [Aser']
  simp [Gser, hA, hA']

theorem th_be_const {be : MvPowerSeries (Fin 2) (K0 p)} (h : BeProp p be) :
    MvPowerSeries.constantCoeff be = 0 := by
  by_contra hne
  have hh := (h.ab 0 hne).1
  simp at hh

theorem th_coordZ_eq {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') :
    coordZ (r0 := r0) (r1 := r1) B K' vp = fun x => MvPowerSeries.C vp * coordZ B K' 1 x := by
  funext x
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
    simp only [coordZ, Finset.mul_sum, one_mul, map_mul, mul_assoc]

theorem th_coordZ_int {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : IntR (Rp p K' vp) (coordZ B K' 1 x) := by
  intro n
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩
  all_goals
    simp only [coordZ, map_sum, one_mul]
    refine Subring.sum_mem _ fun s _ => ?_
    rw [MvPowerSeries.coeff_C_mul]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)) ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

theorem th_coordZA_int (X : Sys p) (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K') (j : ℕ)
    (x : X.EA j ⊕ X.EA j) : IntR (Rp p K' vp) (X.coordZA K' j x) := by
  intro n
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩
  all_goals
    simp only [Sys.coordZA, map_sum]
    refine Subring.sum_mem _ fun s _ => ?_
    rw [MvPowerSeries.coeff_C_mul]
    refine Subring.mul_mem _ (Subring.subset_closure (Set.mem_union_left _ ⟨_, rfl⟩)) ?_
    rw [MvPowerSeries.coeff_X]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _

private theorem constantCoeff_coordZ_eq_zero {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K']
    (vp : K') (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;> simp [coordZ]

theorem restSExp_of (hB : RestBeta p) (hG : RestGc p) : RestSExp p := by
  intro h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' _ _ vp hvp
  obtain ⟨c, hc, hE⟩ := hB h5 hD be hbe
  obtain ⟨μ, hμ0, hμR, hμ1⟩ := exists_mu (p := p) K' vp hvp
  obtain ⟨u, hu, V, hV, hGeq⟩ := hG h5 c hc n' r0 r1 h2 hev B K' vp hvp μ hμ0 hμ1
  obtain ⟨V', hV', hred⟩ := th_reduce (p := p) be (th_be_const hbe) (wK p c) (wK p (sigW p c))
    (th_Gser_const _ _) (fun _ => hE) Ph hPh K' vp μ hμ0 hμR hμ1 (coordZ B K' 1)
    (fun i => constantCoeff_coordZ_eq_zero B K' 1 i) (fun i => th_coordZ_int B K' vp i)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  unfold ThZ
  rw [th_coordZ_eq B K' vp, hred, hGeq, mul_assoc]

private theorem constantCoeff_coordZA_eq_zero (X : Sys p) (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ)
    (x : X.EA j ⊕ X.EA j) : MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA]

private theorem mvPowerSeries_map_algebraMap_map_algebraMap (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] {σ : Type} (F : MvPowerSeries σ (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) F) =
      MvPowerSeries.map (algebraMap (K0 p) K') F := by
  ext n
  simp [MvPowerSeries.coeff_map, IsScalarTower.algebraMap_apply (K0 p) K1 K']

theorem restSExpA_of (X : Sys p) (hB : RestBeta p) (hG : RestGcA X) : RestSExpA X := by
  intro hD be hbe j Ph hPh K1 _ _ K' _ _ _ _ vp hvp
  obtain ⟨c, hc, hE⟩ : ∃ c : WW p, (sigW p)^[2] c = c ∧
      (X.EA j → E0 p (inParam p be - Gser p (wK p c) (wK p (sigW p c)))) := by
    by_cases h5 : 5 ≤ p
    · obtain ⟨c, hc, hE⟩ := hB h5 hD be hbe
      exact ⟨c, hc, fun _ => hE⟩
    · refine ⟨0, ?_, fun e => absurd (X.std e.1).five_le h5⟩
      first
        | exact Function.iterate_fixed (map_zero (sigW p)) 2
        | simp
  obtain ⟨μ, hμ0, hμR, hμ1⟩ := exists_mu (p := p) K' vp hvp
  obtain ⟨u, hu, V, hV, hGeq⟩ := hG c hc j K' vp hvp μ hμ0 hμ1
  obtain ⟨V', hV', hred⟩ := th_reduce (p := p) be (th_be_const hbe) (wK p c) (wK p (sigW p c))
    (th_Gser_const _ _) hE Ph hPh K' vp μ hμ0 hμR hμ1 (X.coordZA K' j)
    (fun i => constantCoeff_coordZA_eq_zero X K' j i) (fun i => th_coordZA_int X K' vp j i)
  refine ⟨u, hu, V * V', IntR_mul hV hV', ?_⟩
  rw [atPi_map_ThZA (X := X), mvPowerSeries_map_algebraMap_map_algebraMap, hred, hGeq, mul_assoc]

theorem baseChange_preserves_unitary_of (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hB : RestBeta p) (hG : RestGc p) :
    Conclusion1 D X Y :=
  kernel_expansion_of_restrictions D X Y hA (restSExp_of hB hG) (restSInt p)

theorem expansion_all_places_of_computation (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hB : RestBeta p) (hG : RestGcA X) :
    ExpansionsMultiply D X Y :=
  all_places_of_restrictions (hA := hA) (hE := restSExpA_of X hB hG) (hI := restSIntA (X := X))

end

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.HeckeConditionOfAdm
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem hk_point (Y : Pend X) (hC : CountLoc) (hT : RestTmFQ X)
    (hp : (p : X.G.Kf) ≠ 0) {a a' : X.G.Kf} {cK : Y.Kc} (ha : a ≠ 0) (ha' : a' ≠ 0) (v : X.Pl) (j : ℕ)
    (hTh : ThEq Y a a' v j) {Cl Yb : Type} [Fintype Cl] [Fintype Yb] {wt : Cl → ℕ} {La : Cl → Yb → X.Lt j}
    (hS : KSum Y j cK Cl Yb wt La) (hAd : KAdj Y j Cl Yb wt La)
    (i : ℕ) (F : X.Fm j) (hF : F ∈ X.FQ j) (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup)
    (hL' : (X.Pj (j + 1)).IsLatTup L') :
    X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ l ∈ range (i + 1), (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) •
        X.Kz j (X.Tm v (i - l) j F) c' L' := by
  obtain ⟨hlat, _, h4⟩ := hS
  apply MvPolynomial.map_injective (algebraMap X.G.Kf Y.Kc) (algebraMap X.G.Kf Y.Kc).injective
  have eT : X.Tm v i (j + 1) (X.Kz j F) c' L' =
      ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
        X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1) :=
    Tminus_eq (X.Pj (j + 1)) (X.vJ (j + 1) v) i (X.Kz j F c') L'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [eT, map_sum, map_sum]
  have eL : ∀ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' (Function.update L' (X.vJ (j + 1) v) L1)) =
        ∑ x : Cl, (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
          Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) := by
    intro L1 hL1
    exact h4 F hF c' _ (hk_latTup_update _ hL' _ L1 ((mem_EE _).1 hL1).1)
  rw [Finset.sum_congr rfl eL, Finset.sum_comm]
  have eL2 : ∀ x ∈ (Finset.univ : Finset Cl), ∑ L1 ∈ EE (X.Pj (j + 1)) (X.vJ (j + 1) v) i (L' (X.vJ (j + 1) v)),
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb,
        Y.ker j (La x y) (c', Function.update L' (X.vJ (j + 1) v) L1) (F (La x y).1 (La x y).2) =
      (((wt x : Y.Kc))⁻¹ * cK) • ∑ y : Yb, (cA X a' v j i • ∑ l ∈ range (i + 1), (nC X v i l : X.G.Kf) •
        ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          (cC X a v j (i - l))⁻¹ •
            Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro x _
    rw [← Finset.smul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    exact ker_dn_sum hC hp ha ha' hTh (La x y) (hlat x y) c' L' hL' i _
  rw [Finset.sum_congr rfl eL2]
  have eR : ∀ l ∈ range (i + 1), MvPolynomial.map (algebraMap X.G.Kf Y.Kc)
      ((cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • X.Kz j (X.Tm v (i - l) j F) c' L') =
      (cA X a' v j i * (nC X v i l : X.G.Kf) * (cC X a v j (i - l))⁻¹) • (cK • ∑ x : Cl,
        ((wt x : Y.Kc))⁻¹ • ∑ y : Yb, ∑ A1 ∈ UP (X.Pj j) (X.vJ j v) (i - l) ((La x y).2 (X.vJ j v)),
          Y.ker j ((La x y).1, Function.update (La x y).2 (X.vJ j v) A1) (c', L') (F (La x y).1 (La x y).2)) := by
    intro l _
    rw [map_smulK Y, h4 _ (hT v (i - l) j F hF) c' L' hL', hAd v (i - l) F hF (c', L') hL',
      Finset.smul_sum (r := cK)]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [smul_smul, mul_comm]
  rw [Finset.sum_congr rfl eR]
  have hs : ∀ (r : X.G.Kf) (z : XspC (X.Pj (j + 1)) Y.Kc), r • z = algebraMap X.G.Kf Y.Kc r • z :=
    fun r z => (algebraMap_smul Y.Kc r z).symm
  simp only [hs, Finset.smul_sum, smul_smul]
  symm
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_comm.trans ?_
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun A1 _ => ?_
  congr 1
  simp only [map_mul, map_inv₀, map_natCast]
  ring

theorem heckeCondition_of_adm (D : Formalism.BasicNotions.D7) (X : Sys p) (Y : Pend X) (hA : admitted D X Y) (hC : CountLoc) (hT : RestTmFQ X) :
    RestHecke X := by
  obtain ⟨_, _, _, _, _, h3b, h4, h5, h5b, h6, _, _, _⟩ := hA
  intro v
  have hfr := frac_of_place X v
  have he := eO_pos X v
  have hp : (p : X.G.Kf) ≠ 0 := pKf_ne Y
  have h5' : ∀ j, ∃ a a' : X.G.Kf, j < X.mm → (X.vEqK a 0 ∧ X.vEqK a' 0 ∧ ThEq Y a a' v j) := by
    intro j
    by_cases hj : j < X.mm
    · obtain ⟨u, u', h1, h2, h3⟩ := h5 v j hj
      exact ⟨u, u', fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨1, 1, fun h => absurd h hj⟩
  choose a a' H using h5'
  refine ⟨fun l => (a (l - 1) * a' (l - 1))⁻¹, fun l => a (l - 1) * (p : X.G.Kf) ^ (X.vm v l), ?_, ?_, ?_⟩
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, h2, _⟩ := H (l - 1) (by omega)
    have := vEqK_inv X hfr (vEqK_mul X hfr h1 h2)
    simpa using this
  · intro l hl
    rw [Finset.mem_Icc] at hl
    obtain ⟨h1, _, _⟩ := H (l - 1) (by omega)
    have := vEqK_mul X hfr h1 (vEqK_ppow X hfr he (X.vm v l))
    simpa using this
  · intro j hj i F hF
    obtain ⟨h1, h2, hTh⟩ := H j hj
    obtain ⟨cK, Cl, Yb, iC, iY, wt, La, hS, hAd⟩ := ksa_of_adm D h4 h5b h6 hj
    have ha := vEqK.ne_zero X h1
    have ha' := vEqK.ne_zero X h2
    show X.ecal v i (j + 1) (X.Kz j F) = ((a j * a' j)⁻¹ ^ i) • X.Kz j (∑ l ∈ range (i + 1),
      (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
        (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F)
    funext c' L'
    by_cases hL' : (X.Pj (j + 1)).IsLatTup L'
    · have eR : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) =
          ∑ l ∈ range (i + 1),
            ((MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
              (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
              (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ))))) •
              X.Kz j (X.Tm v (i - l) j F) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        unfold Sys.ecal
        rw [map_smul, map_smul, smul_smul]
        rfl
      rw [eR]
      show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
        X.Tm v i (j + 1) (X.Kz j F) c' L' = _
      rw [hk_point Y hC hT hp ha ha' v j hTh hS hAd i F hF c' L' hL']
      simp only [Pi.smul_apply, Finset.sum_apply, Finset.smul_sum, smul_smul]
      refine Finset.sum_congr rfl fun l hl => ?_
      congr 1
      have := hk_coef X hp (a j) (a' j) ha v j i l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
      rw [mul_assoc ((a j * a' j)⁻¹ ^ i)] at this
      rw [← this]
      ring
    · have e1 : X.Tm v i (j + 1) (X.Kz j F) c' L' = 0 :=
        (restTmEquiv X (j + 1) v i _ (Eqv_of_FQ X (h3b j hj F hF))).1 c' L' hL'
      have e2 : X.ecal v i (j + 1) (X.Kz j F) c' L' = 0 := by
        show ((p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i)))) •
          X.Tm v i (j + 1) (X.Kz j F) c' L' = 0
        rw [e1, smul_zero]
      rw [e2]
      have hmem : X.Kz j (∑ l ∈ range (i + 1),
          (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a j * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
            (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) • X.ecal v (i - l) j F) ∈ X.FQ (j + 1) :=
        h3b j hj _ (Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
          (Submodule.smul_mem _ _ (hT v (i - l) j F hF)))
      rw [Pi.smul_apply, Pi.smul_apply, FQ_zero_off X hmem c' L' hL', smul_zero]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcLgpLe
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_lgp_le (p : ℕ) (hp : 2 ≤ p) (x : ℤ) (A : ℝ) (c : ℕ) (_hA : 1 ≤ A) (hx : (x : ℝ) ≤ A ^ c)
    (hl : 1 ≤ Real.logb p A) : (lgp p x : ℝ) ≤ (c + 1) * Real.logb p A := by
  unfold lgp
  split_ifs with h
  · push_cast
    have : 0 ≤ Real.logb p A := by linarith
    nlinarith
  · push_cast
    have hx0 : 0 < x := by omega
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
    have h1 : (Nat.log p x.toNat : ℝ) ≤ Real.logb p (x.toNat : ℝ) := Real.natLog_le_logb _ _
    have h2 : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0.le
      exact_mod_cast this
    rw [h2] at h1
    have h3 : Real.logb p (x : ℝ) ≤ Real.logb p (A ^ c) :=
      Real.logb_le_logb_of_le hp1 (by exact_mod_cast hx0) hx
    rw [Real.logb_pow] at h3
    nlinarith

variable {n' k1 : ℕ}

theorem nc_de_le (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (A : ℝ) (NM : ℝ) (hA : 1 ≤ A) (hl : 1 ≤ Real.logb p A) (hN1 : (NN k1 t j : ℝ) ≤ NM)
    (hN0 : (NN k1 t (j - 1) : ℝ) ≤ NM) (hal : ∀ s, (al TT lam0 s : ℝ) ≤ A ^ 2)
    (hls : ∀ s, (lsz t TT lam0 w j s : ℝ) ≤ A ^ 4) :
    de p t TT lam0 w j ≤ 8 * (n' : ℝ) * NM ^ 2 * Real.logb p A + 9 * (TT.card : ℝ) * Real.logb p A ^ 2 := by
  unfold de
  set ℓ := Real.logb p A with hℓ
  have hN1' : (1 : ℝ) ≤ NN k1 t j := by unfold NN; push_cast; nlinarith
  have hNM : 1 ≤ NM := le_trans hN1' hN1
  have hN0' : (0 : ℝ) ≤ NN k1 t (j - 1) := by positivity
  have hα : ∀ s, (lgp p (al TT lam0 s) : ℝ) ≤ 3 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 2 hA (hal s) hl; push_cast at this; linarith
  have hlz : ∀ s, (lgp p (lsz t TT lam0 w j s) : ℝ) ≤ 5 * ℓ := fun s => by
    have := nc_lgp_le p hp _ A 4 hA (hls s) hl; push_cast at this; linarith
  have hα0 : ∀ s, (0 : ℝ) ≤ lgp p (al TT lam0 s) := fun s => by positivity
  have hlz0 : ∀ s, (0 : ℝ) ≤ lgp p (lsz t TT lam0 w j s) := fun s => by positivity
  have h1 : ∑ s : Fin n', ((NN k1 t j : ℝ) * lgp p (al TT lam0 s) +
      (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s)) ≤
      ∑ _s : Fin n', (8 * NM ^ 2 * ℓ) := by
    apply Finset.sum_le_sum
    intro s _
    have e1 : (NN k1 t j : ℝ) * lgp p (al TT lam0 s) ≤ NM * (3 * ℓ) :=
      mul_le_mul hN1 (hα s) (hα0 s) (by linarith)
    have e2 : (NN k1 t (j - 1) : ℝ) * (NN k1 t j : ℝ) * lgp p (lsz t TT lam0 w j s) ≤ NM * NM * (5 * ℓ) :=
      mul_le_mul (mul_le_mul hN0 hN1 (by positivity) (by linarith)) (hlz s) (hlz0 s) (by nlinarith)
    have e3 : NM * (3 * ℓ) ≤ NM * NM * (3 * ℓ) := by
      have : 0 ≤ NM * (3 * ℓ) := by positivity
      nlinarith
    nlinarith
  have h2 : ∑ s ∈ TT, ((lgp p (al TT lam0 s) : ℝ)) ^ 2 ≤ ∑ _s ∈ TT, (9 * ℓ ^ 2) := by
    apply Finset.sum_le_sum
    intro s _
    have := hα s
    have := hα0 s
    nlinarith
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  nlinarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

