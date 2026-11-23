module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnConditionsOfNumericBounds
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateIndexInjective : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective (X.row j x) ∧ ∀ i, X.row j x i ∈ X.F.letters j ∧ Even (X.row j x i) ∧ X.row j x i < x

def EllDegreeLePowerBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j e, X.IsEll p K j e →
    X.dS K j e + X.dV K j e ≤ (r + K) * X.Ns * p ^ X.Rj p K j

def PowerExceedsMaxMultiplicity (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, X.mStar < p ^ X.Rj p K j

def ThresholdPowerLowerBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j b, X.Step2 p K j b → ∀ x ∈ X.toLate j,
      X.th p j x ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) * (X.thc p K j b x - (((r + K) * X.Ns : ℕ) : ℝ))

theorem mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    x ∈ X.toLate j ↔ x ∈ X.F.letters j ∧ ¬ X.F.IsW j x := by
  simp only [Dat.toLate, Finset.mem_filter]

section AG

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)
  [NeZero K] {R : Type} [Field R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (S : Set ℤ)

include hV

theorem vg_ellP : ((-(X.dS K j e : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.ellP K R j e) := by
  have h := vg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin r, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin r) R) ^ e (x, Fin.castAdd K c))
    (fun x => ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1))
    (fun x _ => vg_prod D hV S Finset.univ _ _ (fun c _ => vg_pow D hV S (vg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1)) =
      -(X.dS K j e : ℤ) := by
    unfold Dat.dS
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem lg_ellN : lam1S LZ S (X.ellN K R j e) ≤ (((X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  have h := lg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin K, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin K) R) ^ e (x, Fin.natAdd r c))
    (fun x => ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0))
    (fun x _ => lg_prod D hV S Finset.univ _ _ (fun c _ => lg_pow D hV S (lg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0)) =
      (X.dV K j e : ℤ) := by
    unfold Dat.dV
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem vg_DlSeg (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S) :
    (((X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.DlSeg p K R j) := by
  classical
  have h := vg_prod D hV (R := R) S (X.toLate j) (fun x' => X.detPl R j x' ^ X.sg p K j x')
    (fun x' => if x' = x then (X.sg p K j x : ℤ) else 0) (fun x' hx' => by
      by_cases hxx : x' = x
      · subst hxx
        rw [if_pos rfl]
        have h1 : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.detPl R j x') := by
          unfold Dat.detPl valS
          rw [sDegs_det LZ S _ (X.row j x') hinj (fun i => ⟨hS i, by simp [LZ, hev x' hx' i]⟩)]
          simp
        have := vg_pow D hV S h1 (X.sg p K j x')
        simpa using this
      · rw [if_neg hxx]
        have := vg_pow D hV S (vg_det D hV (R := R) S (X.row j x') (hev x' hx')) (X.sg p K j x')
        simpa [Dat.detPl] using this)
  rw [Finset.sum_ite_eq' (X.toLate j) x, if_pos hx] at h
  exact h

theorem vg_Aw (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S)
    (nu : Fin (segN X.F j + 1) → Fin r → ℤ) (I' : ℤ → Finset (Fin r)) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (segRen X.F j R r (Psi R nu I'))) :
    ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + -(X.dS K j e : ℤ) + (X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LZ S (X.Aw p K R j e nu I') := by
  unfold Dat.Aw
  exact vg_mul D hV S (vg_mul D hV S (vg_pow D hV S ha _) (vg_ellP D hV X K j e S))
    (vg_DlSeg D hV X p K j S hev x hx hinj hS)

theorem lg_Gw (ka : Fin (segN X.F j + 1) → Fin K → ℤ) (I'' : ℤ → Finset (Fin K)) (a : ℤ)
    (ha : lam1S LZ S (segRen X.F j R K (Psi R ka I'')) ≤ (a : WithBot ℤ)) :
    lam1S LZ S (X.Gw p K R j e ka I'') ≤ ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + (X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  unfold Dat.Gw
  exact lg_mul D hV S (lg_pow D hV S ha _) (lg_ellN D hV X K j e S)

end AG

theorem int_ineq (Q κ ν dS dV s mS kN : ℤ) (hQ : 0 ≤ Q) (h : κ + (kN + 1) ≤ ν) (hd : dS + dV ≤ kN * Q)
    (hm : mS < Q) : Q * κ + dV + (mS + s) ≤ Q * ν + -dS + s := by
  nlinarith [mul_le_mul_of_nonneg_left h hQ]

theorem geR_of_le {v : WithTop ℤ} {a : ℤ} {t : ℝ} (h : (a : WithTop ℤ) ≤ v) (ht : t ≤ (a : ℝ)) : geR v t := by
  unfold geR
  intro z hz
  rw [hz] at h
  have h' : a ≤ z := WithTop.coe_le_coe.mp h
  exact ht.trans (by exact_mod_cast h')

theorem column_conditions_of_numeric_bounds (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ)
    (hRow : LateIndexInjective) (hN0 : EllDegreeLePowerBound) (hN1 : PowerExceedsMaxMultiplicity C₀) (hN2 : ThresholdPowerLowerBound C₀) : ColumnConditionsWithMargin C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' ⊢
  have hF3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ),
      Formalism.MainNotions.CovariantDegrees.A3at (FF O) N n LL B th M := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  rw [← h1] at hI' hcond ⊢
  rw [← h2] at hI'' hcond ⊢
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (hF3 _ r _ b') P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (hF3 _ K _ b'') P2 I'' hI''
  obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi (FF O) P1.mu I') i
  obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi (FF O) P2.mu I'') i
  obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hM : X.Mw p K j e P2.mu (segE X.F j i) = ((p ^ X.Rj p K j : ℕ) : ℤ) *
      (if Even (segE X.F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) + (X.dV K j e : ℤ) :=
    (segE_strictMono X.F j).injective.extend_apply _ _ i
  have hrows := hRow p n' r K X hc.hX j
  have hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i) := fun x' hx' i => ((hrows x' hx').2 i).2.1
  have hinj := (hrows _ hxl).1
  have hlt : ∀ a, X.row j (segE X.F j i) a < segE X.F j i := fun a => ((hrows _ hxl).2 a).2.2
  have n0 := hN0 p n' r K X hc.hX j e hc.he
  have n1 := hN1 p n' r K X hc.hX hc.hLa hc.hk j
  have n2 := hN2 p n' r K X hc.hX hc.hLa hc.hk j b hc.h2 _ hxl
  have n0' : (X.dS K j e : ℤ) + (X.dV K j e : ℤ) ≤ (((r + K) * X.Ns : ℕ) : ℤ) * ((p ^ X.Rj p K j : ℕ) : ℤ) := by
    exact_mod_cast n0
  have n1' : (X.mStar : ℤ) < ((p ^ X.Rj p K j : ℕ) : ℤ) := by exact_mod_cast n1
  have hm0 : (X.m0 K : ℤ) = (((r + K) * X.Ns : ℕ) : ℤ) + 1 := by unfold Dat.m0; push_cast; ring
  have vlt := vg_Aw D hV X p K (R := FF O) j e {y | y < segE X.F j i} hev _ hxl hinj hlt P1.mu I'
    (P1.mu i.castSucc (lastIdx r)) (by rw [sA2]; exact (u1.2 i.castSucc).1)
  have vle := vg_Aw D hV X p K (R := FF O) j e {y | y ≤ segE X.F j i} hev _ hxl hinj (fun a => (hlt a).le) P1.mu I'
    (P1.mu i.succ (lastIdx r)) (by rw [sA1]; exact (u1.2 i.succ).1)
  refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
  · rw [hM, if_pos he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG3]; exact (u2.2 i.succ).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
    rw [hM, if_pos he]
    unfold Dat.mg
    have hce := (cE he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · rw [hM, if_neg he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG4]; exact (u2.2 i.castSucc).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
    rw [hM, if_neg he]
    unfold Dat.mg
    have hce := (cO he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · refine geR_of_le vlt ?_
    push_cast
    have hQ : (0 : ℝ) ≤ ((p : ℝ) ^ X.Rj p K j) := by positivity
    have n0r : (X.dS K j e : ℝ) + (X.dV K j e : ℝ) ≤ (((r : ℝ) + K) * X.Ns) * (p : ℝ) ^ X.Rj p K j := by
      exact_mod_cast n0
    have hdV : (0 : ℝ) ≤ (X.dV K j e : ℝ) := Nat.cast_nonneg _
    have hs : (0 : ℝ) ≤ (X.sg p K j (segE X.F j i) : ℝ) := Nat.cast_nonneg _
    push_cast at n2
    have := mul_le_mul_of_nonneg_left cR hQ
    nlinarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.LamSatRestrict
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem lam_sat_restrict {O σ : Type} [CommRing O] [IsDomain O] (s : Set (σ →₀ ℕ)) (f : MvPolynomial σ O) (a : O)
    (ha : a ≠ 0) (h : a • f ∈ restrictSupport O s) : f ∈ restrictSupport O s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at h ⊢
  intro m hm
  apply h
  have hm' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hm)
  refine Finset.mem_coe.mpr (MvPolynomial.mem_support_iff.mpr ?_)
  rw [coeff_smul, smul_eq_mul]
  exact mul_ne_zero ha hm'

theorem lam_dvd_of_res {O σ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) (P : MvPolynomial σ O) (h : MvPolynomial.map (IsLocalRing.residue O) P = 0) :
    ∃ z : MvPolynomial σ O, P = ϖ • z := by
  have hd : C ϖ ∣ P := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h1 : IsLocalRing.residue O (AddMonoidAlgebra.coeff P m) = 0 := by
      rw [← MvPolynomial.coeff_map, h]
      simp
    rw [IsLocalRing.residue_eq_zero_iff, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.mem_span_singleton] at h1
    exact h1
  obtain ⟨z, hz⟩ := hd
  exact ⟨z, by rw [hz, smul_eq_C_mul]⟩

theorem restLamA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestLamA := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX j b hb
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hsatX := (h12 p O Sd n' r K X.F X.L₁ X.N₁ j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) hX.valid hNK
    (fun _ => by positivity)).2.2.1
  have hsat : ∀ (f : SegRing O r K) (a : O), a ≠ 0 → a • f ∈ X.Mj p K O j b → f ∈ X.Mj p K O j b := by
    intro f a ha h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨⟨hsatX f a ha h1, lam_sat_restrict _ f a ha h2⟩, lam_sat_restrict _ f a ha h3⟩
  have hfin : Module.Finite O (X.Mj p K O j b) := restFin p n' r K X O j b hb
  have hfree : Module.Free O (X.Mj p K O j b) := Module.free_of_finite_type_torsion_free'
  let bs := Module.finBasis O (X.Mj p K O j b)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  refine ⟨fun i => (bs i : SegRing O r K), fun i => (bs i).2, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro cb hcb i
  choose c hc using fun i => IsLocalRing.residue_surjective (cb i)
  have h1 : MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • (bs i : SegRing O r K)) = 0 := by
    rw [sel_red_sum, ← hcb]
    exact Finset.sum_congr rfl fun i _ => by rw [hc]
  obtain ⟨z, hz⟩ := lam_dvd_of_res hϖ _ h1
  have hzM : z ∈ X.Mj p K O j b := by
    refine hsat z ϖ hϖ.ne_zero ?_
    rw [← hz]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bs i).2
  have h2 : ∑ i, c i • bs i = ϖ • (⟨z, hzM⟩ : X.Mj p K O j b) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact hz
  have h3 := congrArg (fun v => bs.repr v i) h2
  simp only [Module.Basis.repr_sum_self, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
  rw [← hc i, h3, map_mul]
  have : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  rw [this, zero_mul]

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.WindowSmall
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem two_N_lt_K (H : HypT N n0 r K LL B od bb a La p) : 2 * N < K := by
  have h := H.H4
  have hr := H.r1
  have hk : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by omega
    exact_mod_cast this
  have : (2 * N : ℝ) < (K : ℝ) := by linarith
  exact_mod_cast this

theorem dplus_le_beA (_H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) (hs : s ≤ n0) : dplus LL dd s ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = true
  · rw [if_pos hl, if_pos (by omega), hdd l (by omega)]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem dminus_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) : dminus LL dd s ≤ beA n0 B := by
  unfold dminus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = false
  · have hln : l.val < n0 := by
      by_contra hcon
      have := H.vec_true_of_late l (by omega)
      rw [hl.2] at this
      exact absurd this (by simp)
    rw [if_pos hl, if_pos hln, hdd l hln]
  · rw [if_neg hl]; exact Nat.zero_le _

theorem path_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin (r + K)), P.mu ⟨s, hs⟩ m ≤ (beA n0 B : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, P.zero]; simp
  | succ s ih =>
    intro hs m
    by_cases hsn : s + 1 ≤ n0
    · refine le_trans (mu_le_dplus P (s + 1) hs m) ?_
      exact_mod_cast dplus_le_beA H hP.degs (s + 1) hsn
    · have hsN : s < N := by omega
      have hv : LL.vec ⟨s, hsN⟩ = true := H.vec_true_of_late ⟨s, hsN⟩ (by simp only; omega)
      by_cases hm : m.val = 0
      · have := hP.head ⟨s, hsN⟩ m (by simp only; omega) (by omega)
        exact le_of_eq this
      · have h := step_vec P ⟨s, hsN⟩ hv
        have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := h.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) _)

theorem beA_le (H : HypT N n0 r K LL B od bb a La p) : (beA n0 B : ℝ) ≤ 2 * a * (N : ℝ) := by
  unfold beA
  push_cast
  have ha : (0 : ℝ) ≤ 2 * a := by have := H.a3; linarith
  calc ∑ i : Fin N, (if i.val < n0 then (B i : ℝ) else 0) ≤ ∑ _i : Fin N, 2 * a := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i.val < n0
        · rw [if_pos hi]; exact (H.H1 i hi).2
        · rw [if_neg hi]; exact ha
    _ = 2 * a * (N : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end

def code (N r K : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Fin N × Fin (2 * N) → ℕ := fun v =>
  if h : v.2.val < N ∧ v.2.val < r + K then (μ v.1.succ ⟨v.2.val, h.2⟩).toNat
  else if h' : r + K - 2 * N + v.2.val < r + K then (-μ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).toNat else 0

theorem path_count_finite : PathCountFinite := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hK := two_N_lt_K H
  set M := beA n0 B with hM
  let t : Finset (Fin N × Fin (2 * N) → ℕ) := Fintype.piFinset fun _ => Finset.range (M + 1)
  have hshape : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ∀ (s : Fin (N + 1)) (m : Fin (r + K)),
      (m.val + N < r + K → 0 ≤ μ s m) ∧ (N ≤ m.val → μ s m ≤ 0) ∧ μ s m ≤ (M : ℤ) ∧ -(M : ℤ) ≤ μ s m := by
    rintro μ ⟨dd, hP⟩ s m
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨fun h => mu_nonneg P s.val s.2 m (by have := s.2; omega),
      fun h => mu_nonpos P s.val s.2 m (by have := s.2; omega), path_le_beA H P hP s.val s.2 m, ?_⟩
    refine le_trans ?_ (neg_dminus_le_mu P s.val s.2 m)
    have := dminus_le_beA H hP.degs s.val
    have h' : (dminus LL dd s.val : ℤ) ≤ (M : ℤ) := by exact_mod_cast this
    linarith
  have hmaps : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, code N r K μ ∈ (t : Set (Fin N × Fin (2 * N) → ℕ)) := by
    intro μ hμ
    simp only [t, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro v
    unfold code
    split_ifs with h h'
    · have := (hshape μ hμ v.1.succ ⟨v.2.val, h.2⟩).2.2.1
      omega
    · have := (hshape μ hμ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).2.2.2
      omega
    · omega
  have hinj : Set.InjOn (code N r K) (SP (r := r) (K := K) LL n0 B) := by
    intro μ hμ μ' hμ' hc
    funext s m
    induction s using Fin.cases with
    | zero =>
      obtain ⟨dd, hP⟩ := hμ
      obtain ⟨dd', hP'⟩ := hμ'
      obtain ⟨P, rfl⟩ := hP.path
      obtain ⟨P', rfl⟩ := hP'.path
      rw [P.zero, P'.zero]
    | succ i =>
      have h1 := hshape μ hμ i.succ m
      have h2 := hshape μ' hμ' i.succ m
      by_cases hm : m.val < N
      · have hcv := congrFun hc (i, ⟨m.val, by omega⟩)
        unfold code at hcv
        rw [dite_eq_left ⟨hm, m.2⟩, dite_eq_left ⟨hm, m.2⟩] at hcv
        have e1 := h1.1 (by omega)
        have e2 := h2.1 (by omega)
        have hcv' : (μ i.succ m).toNat = (μ' i.succ m).toNat := hcv
        omega
      · by_cases hm2 : m.val + N < r + K
        · have e1 := h1.1 hm2
          have e2 := h2.1 hm2
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
        · have hidx : m.val - (r + K - 2 * N) < 2 * N := by have := m.2; omega
          have hcv := congrFun hc (i, ⟨m.val - (r + K - 2 * N), hidx⟩)
          unfold code at hcv
          have hn1 : ¬ ((m.val - (r + K - 2 * N)) < N ∧ (m.val - (r + K - 2 * N)) < r + K) := by omega
          have hn2 : r + K - 2 * N + (m.val - (r + K - 2 * N)) < r + K := by have := m.2; omega
          rw [dite_eq_right hn1, dite_eq_right hn1, dite_eq_left hn2, dite_eq_left hn2] at hcv
          have hme : (⟨r + K - 2 * N + (m.val - (r + K - 2 * N)), hn2⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only; omega)
          rw [hme] at hcv
          have hcv' : (-μ i.succ m).toNat = (-μ' i.succ m).toNat := hcv
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
  have hfin : (SP (r := r) (K := K) LL n0 B).Finite :=
    Set.Finite.of_injOn (fun μ hμ => hmaps μ hμ) hinj t.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn (code N r K) hmaps hinj t.finite_toSet
  rw [Set.ncard_coe_finset] at hle
  have hcard : t.card = (M + 1) ^ (N * (2 * N)) := by
    simp [t, Fintype.card_piFinset]
  rw [hcard] at hle
  have hA : (0 : ℝ) < 1 + 2 * a * (N : ℝ) := by
    have := H.a3
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 1 + 2 * a * (N : ℝ) := by
    have := beA_le H
    push_cast
    linarith
  calc ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ (((M + 1) ^ (N * (2 * N)) : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((M + 1 : ℕ) : ℝ) ^ (N * (2 * N)) := by push_cast; rfl
    _ ≤ (1 + 2 * a * (N : ℝ)) ^ (N * (2 * N)) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a) := by
        unfold ell0
        rw [← Real.exp_log hA, ← Real.exp_nat_mul, Real.log_exp]
        congr 1
        push_cast
        ring

end Formalism.MainNotions.SelectionLemmas.Pf.T
end
end

