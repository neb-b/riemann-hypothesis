module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
open GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

structure CoreTies (L : SizeData₂ D) (EX : ErrX D) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) : Prop where
  laws : LawsCore J.toCore
  canon : J.Q.Canon
  rank : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q
  halfEX : HalfEX J.toCore EX
  field₁ : FieldOK0 D D.host.pde
  field₂ : FieldOK0 D D.host.pde'
  small : FieldSmall D L
  level : J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal
  oneHalf : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
    ∀ PP ∈ placesOver R (R.mu v) (ownAt D v),
      (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal
  delVal : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D
  delVal' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D

def OwnPin {J : CoreJ D} (r : TwoRuns J G) : Prop :=
  ∀ v (j n : ℕ), InR D j → ((r.used v).full.dδ j n).pd = ownAt D v

def PageNum {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (x₁ : ℝ) : Prop :=
  SizesAt L ∧ Pm.CnW = 10 ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) ∧ 1000 ≤ Tp.CP ∧ Tp.CP ^ 20 ≤ zBase L ∧ x₁ ≤ L.sc.x

def RunsHold {L : SizeData₂ D} {Pm : ParameterChoice' D L} (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (CK : ℝ) {J : CoreJ D}
    (r : TwoRuns J G) : Prop :=
  ∀ v (h : LawsP (r.used v).full.toTop) (hinj : Function.Injective D.what₂.OtoLL) (j : ℕ) (hj : InR D j),
    HypC L (recPJ h j hj) ⟨CK, 20, Tp.CP, Tp.eP, Tp.CP, Tp.eP, 7⟩ Tp.CP Tp.eP 7 0 L.Ct
        (scalOfP (recB h.toLawsCore) hinj EX (ownAt D v) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO) (kaR Tp hK j) (lR Tp hK j)
        (fR Tp hK j) Tp.TO Tp.nP Tp.nWn (LevelStarExponents.h0 L - 4) (nusR h j (lR Tp hK j)) ∧
      Concl (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX (ownAt D v) (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO)
        (kaR Tp hK j) (lR Tp hK j) (fR Tp hK j) Tp.TO (nusR h j (lR Tp hK j))
        ((recPJ h j hj).rk (kaR Tp hK j) ((recB h.toLawsCore).Mlat j (kaR Tp hK j)) * D.R.f * D.R.m * L.sc.b * L.de2)

theorem isDelta_delAt_ownAt (C : Formalism.L2.Host.CharFrame D) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    Formalism.L2.Host.IsDelta (H := D.host) (ownAt D v) (C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) := by
  unfold ownAt Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [C.isDel', C.isDel]

namespace CoreTies

variable {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F}

theorem inj (h : CoreTies L EX J R) : Function.Injective D.what₂.OtoLL := h.field₁.full.1

theorem fieldAt (h : CoreTies L EX J R) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : FieldOK0 D (ownAt D v) := by
  unfold ownAt
  split_ifs
  exacts [h.field₂, h.field₁]

theorem delAt_mem (h : CoreTies L EX J R) (l : ℕ) (x) : (((R.C.delAt l).1 x : ℂˣ) : ℂ) ∈ FO D := by
  unfold Formalism.L2.Host.CharFrame.delAt
  split_ifs
  exacts [h.delVal' x, h.delVal x]

end CoreTies


omit [Group G] [Fintype G] in
theorem ownPin_of {J : CoreJ D} {r : TwoRuns J G} (h₁ : ∀ j n : ℕ, InR D j → (r.first.full.dδ j n).pd = D.host.pde)
    (h₂ : ∀ j n : ℕ, InR D j → (r.second.full.dδ j n).pd = D.host.pde') : OwnPin r := by
  intro v j n hj
  by_cases h : Formalism.EigenvalueLevelCeiling.plc v = D.host.pde
  · rw [show r.used v = r.second from if_pos h, show ownAt D v = D.host.pde' from if_pos h]
    exact h₂ j n hj
  · rw [show r.used v = r.first from if_neg h, show ownAt D v = D.host.pde from if_neg h]
    exact h₁ j n hj

end GlobalTheory.BigOn

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid

namespace GlobalTheory.FunObj.SqNum.Model

variable (D : D7)

theorem e_add_v (τ : D.what₂.Tau) (j : Fin D.R.m) :
    0 < (D.hc τ).e j + (D.hc τ).v ⟨0, by have := D.R.m_add_three_le_k; omega⟩ := by
  set P := D.hc τ
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have ht : (0 : ℚ) ≤ D.R.t := by positivity
  have h1 : ∀ a (h : a < D.R.m), P.b ⟨0, by omega⟩ ≤ P.b ⟨a, h⟩ := by
    intro a; induction a with
    | zero => intro _; exact le_rfl
    | succ a ih =>
      intro h; have := ih (by omega); have := P.gap_be ⟨a, by omega⟩; have := P.gap_eb ⟨a, by omega⟩ h
      simp only at *; linarith
  have h2 : ∀ a (h : a < D.R.k - 1), P.u ⟨a + 1, by omega⟩ < P.v ⟨0, by omega⟩ := by
    intro a; induction a with
    | zero => intro h; exact P.v_gt_u ⟨0, h⟩
    | succ a ih =>
      intro h; have := ih (by omega); have := P.v_gt_u ⟨a + 1, h⟩; have := P.u_gt_v ⟨a + 1, h⟩
      simp only at *; linarith
  have h3 := P.u_last_gt (by omega) (by omega)
  have h4 := h2 (D.R.k - 2) (by omega)
  have e : (⟨D.R.k - 2 + 1, by omega⟩ : Fin D.R.k) = ⟨D.R.k - 1, by omega⟩ := Fin.ext (by simp only; omega)
  rw [e] at h4
  have h5 := h1 j.1 j.2
  have h6 := P.gap_be j
  simp only [Fin.eta] at h5
  linarith

theorem gap_le (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) :
    (gap D C : ℤ) ≤ (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) := by
  have h := e_add_v D τ j
  have s := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  have s0 := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) 0
  rw [s.2.2, s0.1] at h
  rw [← sub_le_iff_le_add', cen, Int.le_floor]
  simp only [GlobalTheory.SignedHC.GridData.mid, GlobalTheory.SignedHC.GridData.a]
  have hi := i.2
  have e1 : ((D.R.m - i - 1 : ℕ) : ℚ) = D.R.m - i - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  have e2 : ((D.R.m - i : ℕ) : ℚ) = D.R.m - i := by rw [Nat.cast_sub (by omega)]
  rw [e1, e2]
  have g0 : (0 : ℚ) ≤ gap D C := by positivity
  have i0 : (0 : ℚ) ≤ (i : ℕ) := by positivity
  have := mul_nonneg g0 i0
  change _ ≤ (_ + 1 / 2 + ((D.R.m : ℚ) + 1 - _) * (gap D C : ℚ) +
    (_ + 1 / 2 + ((D.R.m : ℚ) + 1 - _) * (gap D C : ℚ))) / 2
  simp only [zero_add] at h
  push_cast
  unfold num
  nlinarith

theorem kap_add (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ halfRank D i j) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := gap_le D C i j τ
  have h2 := (isLeast_gap D C).1.2.1
  have h3 : halfRank D i j ≤ bigN D := by
    have a : rankV D (i + 1) (j + 1) ≤ bigN D := by
      have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
      have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
      simp only [rankV, bigN, Ranks.r, mul_add] at *
      omega
    have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
    unfold halfRank; omega
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

variable {D} {T : Type} {L : LevCh D T} {sc : Consts}


open Classical in
theorem expIn_condF (P : Places L) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.CMVal.expIn (condF P) v = if v ∈ P.S0 then condExp P v else 0 := by
  have key : ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), v ∉ S →
      ¬ v.asIdeal ∣ ∏ u ∈ S, u.asIdeal ^ condExp P u := fun S hS h => by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty] at h
      exact v.prime.2.1 (isUnit_iff_dvd_one.2 h)
    | @insert u S hu ih =>
      rw [Finset.prod_insert hu] at h
      rcases v.prime.2.2 _ _ h with h | h
      · have h2 := v.prime.dvd_of_dvd_pow h
        have : v = u := HeightOneSpectrum.ext (associated_iff_eq.1 (v.irreducible.associated_of_dvd u.irreducible h2))
        exact hS (this ▸ Finset.mem_insert_self _ _)
      · exact ih (fun hv => hS (Finset.mem_insert_of_mem hv)) h
  show multiplicity v.asIdeal (∏ u ∈ P.S0, u.asIdeal ^ condExp P u) = _
  split_ifs with h
  · rw [← Finset.mul_prod_erase _ _ h]
    refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) fun h' => ?_
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero _ v.ne_bot)] at h'
    exact key _ (Finset.notMem_erase _ _) h'
  · exact multiplicity_eq_zero_of_not_dvd (key _ h)

theorem levelLe_mono {χ : HChar D.host.E} {v : HeightOneSpectrum (𝓞 D.host.E)} {m n : ℕ} (h : χ.LevelLe v m)
    (hmn : m ≤ n) : χ.LevelLe v n := fun x hx hx' =>
  h x hx (hx'.trans (WithZero.exp_le_exp.2 (by omega)))

theorem expAt_div (G : GridData L sc) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ D.R.m) {θ : HChar D.host.E} (ht : ∀ P, θ.TameAt P)
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → θ.UnrAt P)
    (P : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.CMVal.ExpAt (θ / G.ch.chiH k) P (GlobalTheory.CMVal.expIn (condF G.pl) (P.under (𝓞 D.host.F))) := by
  have back : ∀ n, θ.LevelLe P n → (θ / G.ch.chiH k).LevelLe P n → (G.ch.chiH k).LevelLe P n := fun n a b => by
    have := a.mul b.inv
    rwa [inv_div, mul_div_cancel] at this
  have fwd : ∀ n, θ.LevelLe P n → (G.ch.chiH k).LevelLe P n → (θ / G.ch.chiH k).LevelLe P n := fun n a b => by
    rw [div_eq_mul_inv]; exact a.mul b.inv
  rw [expIn_condF]
  intro n
  split_ifs with h
  · by_cases e : P.under (𝓞 D.host.F) = G.pl.v0
    · have l := G.ch.lev0 k h1 h2 P e
      have u := hu P (e ▸ G.ch.basePlace_not_mem_chiGridBadPlaces)
      rw [condExp, if_pos e]
      refine ⟨fun hn => ?_, fun hn => levelLe_mono (fwd 1 (ht P) l.1) hn⟩
      by_contra c
      obtain rfl : n = 0 := by omega
      exact l.2 ((HChar.unrAt_iff _ _).2 (back 0 (u.levelLe 0) hn))
    · have l := G.ch.lev1 k h1 h2 P ((G.pl.mem_S0_of_sum_eq.1 h).resolve_left e)
      rw [condExp, if_neg e]
      refine ⟨fun hn => ?_, fun hn => levelLe_mono (fwd 2 (levelLe_mono (ht P) (by omega)) l.1) hn⟩
      by_contra c
      exact l.2 (back 1 (ht P) (levelLe_mono hn (by omega)))
  · refine ⟨fun _ => Nat.zero_le _, fun _ => fwd n ((hu P fun c => h (G.pl.mem_S0_of_sum_eq.2 (Or.inr c))).levelLe n)
      ((G.ch.unr k h1 h2 P h).levelLe n)⟩

theorem isValChar_twist {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j)
    {ξ : HChar D.host.E} (hf : ∃ n, 0 < n ∧ ξ.OrderDvd n) (htr : ξ.TrivOn D.host.F) (ht : ∀ P, ξ.TameAt P)
    (hu : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.under (𝓞 D.host.F) ∉ S1 D → ξ.UnrAt P) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j * ξ) := by
  obtain ⟨n, hn, hf⟩ := hf
  have hm := L.C.isMu0 j
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have e : nuH G μ₀ i j * ξ = L.C.mu0 j * ξ / G.ch.chiH (D.R.m - i) := by
    rw [nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]
  refine ⟨(GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (chrEq_nu G μ₀ i j hL)).mul (HChar.isUnitary_of_order hn hf), ?_, ?_,
    fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty _), fun _ => ?_⟩⟩
  · rw [e, div_eq_mul_inv]
    exact (hm.triv.mul htr).mul (G.ch.triv _ a1 a2).inv
  · intro k
    obtain ⟨n', hn', hinf⟩ := hm.inf
    have hk : ∀ τ, embTau D τ (k : D.host.E) ≠ 0 := fun τ => by simp
    rw [e, div_eq_mul_inv, HChar.inf_mul, HChar.inf_mul, HChar.inf_inv, GlobalTheory.TypeValues.inf_eq_one ξ hn hf, mul_one,
      Units.val_mul, Units.val_inv_eq_inv_val, hinf k, G.ch.inf _ a1 a2 k, ← D.eTau.prod_comp, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have h1 : n' (D.eTau τ) = -(2 * (num D sc.cGap τ).e (j + 1)) := by
      have := hn' (D.eTau τ)
      beta_reduce at this
      rw [Formalism.L2.Host.eExp, Equiv.symm_apply_apply,
        (GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D sc.cGap) (cen D sc.cGap τ)).2.2] at this
      have h2 : ((n' (D.eTau τ) : ℤ) : ℚ) = ((-(2 * (num D sc.cGap τ).e (j + 1)) : ℤ) : ℚ) := by
        rw [this]; push_cast; unfold num; ring
      exact_mod_cast h2
    beta_reduce
    rw [h1, (kap_add D sc.cGap i j τ hs).1]
    have hz : (cmPhi D τ (k : D.host.E) / ((‖cmPhi D τ (k : D.host.E)‖ : ℝ) : ℂ)) =
        (embTau D τ (k : D.host.E) / ((‖embTau D τ (k : D.host.E)‖ : ℝ) : ℂ))⁻¹ := by
      have : cmPhi D τ (k : D.host.E) = starRingEnd ℂ (embTau D τ (k : D.host.E)) := rfl
      rw [this, RCLike.norm_conj, inv_div, div_eq_div_iff (by simpa using hk τ) (hk τ), Complex.conj_mul']
      ring
    have hne : (embTau D τ (k : D.host.E) / ((‖embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ≠ 0 :=
      div_ne_zero (hk τ) (by simpa using hk τ)
    rw [hz, inv_zpow', ← zpow_neg]
    change (embTau D τ (k : D.host.E) / ((‖embTau D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ _ * _ = _
    rw [← zpow_add₀ hne]
    congr 1
    ring
  · obtain rfl : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
    rw [e]
    refine expAt_div G a1 a2 (fun Q => HChar.LevelLe.mul (hm.tame Q) (ht Q)) (fun Q hQ => HChar.UnrAt.mul
      (hm.unr Q fun k hk => hQ ((S1_mem_OmF D).2 ?_)) (hu Q hQ)) P
    have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := by
      show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
      rw [map_natCast]; exact hk
    fin_cases k
    · exact Or.inl this
    · exact Or.inr (Or.inl this)

theorem isValChar_nu {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (i j : Fin D.R.m) {s : ℕ} (hs : s ≤ halfRank D i j) :
    GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) ∧
      ∀ c, GlobalTheory.CMVal.IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j * delOf L c) := by
  have up : ∀ (p : ℕ) (Q : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.Host.OverP D.host p Q →
      ((p : ℕ) : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal := fun p Q h => by
    show algebraMap _ (𝓞 D.host.E) _ ∈ Q.asIdeal
    rw [map_natCast]; exact h
  refine ⟨?_, fun c => ?_⟩
  · simpa using isValChar_twist hL G i j hs (ξ := 1) ⟨1, one_pos, one_pow 1⟩ (hL.xi_base ▸ hL.xi_triv μ₀)
      (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
  · cases c
    · have h := L.C.isDel
      exact isValChar_twist hL G i j hs h.fin h.triv h.tame fun Q hQ => h.unr Q fun o =>
        hQ ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inl (up _ Q o)))))
    · have h := L.C.isDel'
      exact isValChar_twist hL G i j hs h.fin h.triv h.tame fun Q hQ => h.unr Q fun o =>
        hQ ((S1_mem_OmF D).2 (Or.inr (Or.inr (Or.inr (up _ Q o)))))

theorem bot_ranks (i j : Fin D.R.m) : 2 ≤ botSmall D i j ∧ botSmall D i j < botBig D i j ∧
    Even (botBig D i j + botSmall D i j) ∧ botBig D i j + botSmall D i j ≤ 2 * bigN D := by
  obtain ⟨h1, h2, h3⟩ := ranks_exact D i j
  have e : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have a : rankV D (i + 1) (j + 1) ≤ bigN D := by
    have h1 : (j + 1) * D.R.t ≤ D.R.m * D.R.t := Nat.mul_le_mul_right _ j.2
    have h2 : (i + 1) * sLen D ≤ D.R.m * sLen D := Nat.mul_le_mul_right _ i.2
    simp only [rankV, bigN, Ranks.r, mul_add] at *
    omega
  have h4 : D.R.r ≤ rankV D i j := by simp only [rankV]; omega
  have h5 := D.R.m_add_three_le_k
  have h6 : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h7 : sLen D = D.R.r + 6 := rfl
  refine ⟨by omega, by omega, Nat.even_iff.2 (by omega), by omega⟩

end GlobalTheory.FunObj.SqNum.Model
end
end

