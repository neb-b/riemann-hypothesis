module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0019
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0021
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DistAddTwoLeOfSameVec
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Bundle0018

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BetaRatioBound
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem beta_ratio_bound : BetaRatioBound 1088 := by
  intro p n' r K _ _ _ X hX hLa hk j b hA
  classical
  have hV := hX.valid
  have B := basics hX
  have hr : 0 < r := NeZero.pos r
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hp2 : 2 ≤ p := hX.prime.two_le
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have ha0 : 0 < X.a := by have := TE.four_hundred_sixteen_le_a hX; linarith

  have hL1 : 1 ≤ X.L₁ := by
    by_contra h
    have h0 : X.L₁ = 0 := by omega
    have hP2 := hX.P2
    rw [h0] at hP2
    have e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by simp
    rw [e1] at hP2
    have e2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ B.p1
    have e3 : (1 : ℝ) ≤ 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 := by
      have k5 := B.k5
      unfold Dat.k at k5
      have a1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := by nlinarith
      have a2 : (1 : ℝ) ≤ X.Y ^ 2 := by nlinarith [B.Y1]
      have a3 := B.Ns1
      have a4 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) := by nlinarith
      nlinarith
    linarith
  have hP2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ (X.L₁ - 1) := by
    have h := hX.P2
    have e : ((X.L₁ : ℤ) - 1) = ((X.L₁ - 1 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast] at h
    exact h
  set D1 := X.F.dist j (X.F.fr j 0) with hD1
  set s := (X.F.letters j).filter (· < X.F.fr j 0) with hs
  have hfr0 : X.F.fr j 0 ∈ X.F.letters j := k_fr_mem_letters X.F hV j hr
  have hD1c := TE.dist_cast hfr0

  have hU1 : ∀ x ∈ s, D1 + X.L₁ + 1 ≤ X.F.dist j x := by
    intro x hx
    have hne : s.Nonempty := ⟨x, hx⟩
    have hmax := Finset.max'_mem s hne
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hmax
    have hgap := hV.2.2.2.2.2.2.1 j |>.2.2 (s.max' hne) hm1 hm2 (fun z hz hzlt =>
      Finset.le_max' s z (Finset.mem_filter.mpr ⟨hz, hzlt⟩))
    have hle := Finset.le_max' s x hx
    have hxc := TE.dist_cast (Finset.mem_filter.mp hx).1
    omega

  have hA1 : (X.beS p K j (X.restr j b) : ℝ) ≤ 4 * X.a / (p : ℝ) ^ (X.Rj p K j + D1 + X.L₁ + 1) := by
    unfold Dat.beS
    push_cast
    have h1 : ∀ x ∈ s, (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        2 * X.a / (p : ℝ) ^ X.Rj p K j * (1 / (p : ℝ) ^ X.F.dist j x) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have b1 := (TE.Bdeg_bounds hX hk h41 j b hA x hx1 hx2).2
      have b2 := (TE.c_bounds hX h41 j x hx1).2.2
      refine le_trans b1 ?_
      rw [pow_add]
      have hq1 : (0 : ℝ) < (p : ℝ) ^ X.F.dist j x := by positivity
      have hq2 : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
      rw [div_mul_div_comm, mul_one, mul_comm ((p : ℝ) ^ X.Rj p K j)]
      exact div_le_div_of_nonneg_right b2 (by positivity)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    have hinj : Set.InjOn (X.F.dist j) (s : Set ℤ) := by
      intro x hx y hy hxy
      have c1 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      have c2 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
      have : (X.F.dist j x : ℤ) = (X.F.dist j y : ℤ) := by exact_mod_cast hxy
      omega
    have h2 : ∑ x ∈ s, (1 / (p : ℝ) ^ X.F.dist j x) = ∑ D ∈ s.image (X.F.dist j), (1 / (p : ℝ) ^ D) :=
      (Finset.sum_image (f := fun D : ℕ => 1 / (p : ℝ) ^ D) hinj).symm
    have h3 := Formalism.InvariantFactorPaths.BranchingDimensions.geometricSumDistinct p (D1 + X.L₁ + 1) (s.image (X.F.dist j)) hp2 (by
      intro D hD
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
      exact hU1 x hx)
    rw [h2]
    have hc : 0 ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left h3 hc) ?_
    rw [div_mul_div_comm, ← pow_add]
    have e : X.Rj p K j + (D1 + X.L₁ + 1) = X.Rj p K j + D1 + X.L₁ + 1 := by ring
    rw [e]
    apply le_of_eq
    ring

  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) := by
    have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hV (by omega : j < j + 1)
    exact ⟨(X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdist : X.F.dist (j + 1) (X.F.fr j 0) = D1 + d := by
    have : ((X.F.dist (j + 1) (X.F.fr j 0) : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j 0 := by
      unfold Frames.dist
      exact Int.toNat_of_nonneg (by omega)
    omega
  have hB1 : X.a / (8 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) <
      (p : ℝ) ^ X.Rj p K (j + 1) := by
    have h := lt_pow_Rj hX (j + 1)
    unfold Tj at h
    rw [add_sub_cancel_right, hdist, pow_add ((p : ℝ)) D1 d, pow_succ ((p : ℝ)) (X.Rj p K (j + 1))] at h
    unfold Dat.k at h
    have hden : 0 < 8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have k5 := B.k5
      unfold Dat.k at k5
      have := B.Ns1
      have := B.Y1
      positivity
    rw [div_lt_iff₀ hden] at h
    have hden2 : 0 < 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have e : 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) =
          (p : ℝ) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := by ring
      rw [e]; exact mul_pos hp0 hden
    rw [div_lt_iff₀ hden2]
    calc X.a < (p : ℝ) ^ X.Rj p K (j + 1) * (p : ℝ) *
          (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := h
      _ = _ := by ring
  have hcore := (Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio p (r + K) X.Ns D1 X.L₁ (X.Rj p K j) (X.Rj p K (j + 1)) X.a X.Y
    ((p : ℝ) ^ d) (X.beS p K j (X.restr j b) : ℝ) hp2 (by omega)
    (by have := B.Ns1; exact_mod_cast this) B.Y1 ha0 (by positivity) hL1 hA1 hB1 hP2).2.2

  have hexp := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have hmono : X.F.fr (j - 1) 0 ≤ X.F.fr j 0 := (mem_letters_bounds hfr0).1
  have hQ : ((X.Qc p K j : ℕ) : ℝ) = (p : ℝ) ^ d * (p : ℝ) ^ X.Rj p K (j + 1) / (p : ℝ) ^ X.Rj p K j := by
    unfold Dat.Qc
    rw [eq_div_iff (by positivity)]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    have : (((X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat : ℕ) : ℤ) =
        X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    omega
  rw [← hQ] at hcore
  have hQpos : (0 : ℝ) < ((X.Qc p K j : ℕ) : ℝ) := by
    rw [hQ]; positivity
  rw [div_le_div_iff₀ hQpos (by have := B.Y1; positivity)] at hcore
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerTimesMonomial
section
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

variable (D : Formalism.BasicNotions.D7) (hV : admB2 D) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

theorem mem_vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  have h := ((hV R ℤ n LZ S).1 P Q).1
  rw [h, WithTop.coe_add]
  exact add_le_add hP hQ

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have h := sDegs_C (R := R) LZ S (lastIdx n) c k hk
  rw [Set.mem_singleton_iff] at h
  subst h
  exact le_rfl

theorem mem_vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using mem_vg_C (R := R) (n := n) S 1
  | succ k ih =>
    have e : (((k + 1 : ℕ) : ℤ) * a : ℤ) = (k : ℤ) * a + a := by push_cast; ring
    rw [e, pow_succ]
    exact mem_vg_mul D hV S ih hP

theorem mem_vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using mem_vg_C (R := R) (n := n) S 1
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mem_vg_mul D hV S (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_X (v : ℤ × Fin n) (he : Even v.1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have hk0 : (0 : ℤ) ≤ k := by
    by_cases hS : v.1 ∈ S
    · have hv : LZ.vec v.1 = true := by simp [LZ, he]
      have h := sDegs_X_vec (R := R) LZ S (lastIdx n) v.1 v.2 hS hv k hk
      have h01 : k = 0 ∨ k = 1 := by simpa using h
      rcases h01 with h | h <;> simp [h]
    · have h := sDegs_X_out (R := R) LZ S (lastIdx n) v hS k hk
      rw [Set.mem_singleton_iff] at h
      simp [h]
  exact WithTop.coe_le_coe.mpr hk0

theorem mem_vg_monom {κ : Type} (s : Finset κ) (v : κ → ℤ × Fin n) (e : κ → ℕ) (he : ∀ i ∈ s, Even (v i).1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
  have h0 : ∀ i ∈ s, (((fun _ => (0 : ℤ)) i : ℤ) : WithTop ℤ) ≤
      valS LZ S ((X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
    intro i hi
    simpa using mem_vg_pow D hV S (mem_vg_X (R := R) S (v i) (he i hi)) (e i)
  simpa using mem_vg_prod D hV S s (fun i => (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) (fun _ => 0) h0

end Kit

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerTimesMonomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat)


omit [NeZero n'] [NeZero r] in
def memMu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ u v

def memPl (O : Type) [CommRing O] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) :
    MvPolynomial (ℤ × Fin r) O :=
  segRen X.F j O r (Psi O (plPart μ) (Ican (plPart μ)))

def memA (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin r) O :=
  X.discPowerTimesMonomial p K O j b * X.memMu O j q.2.2 * X.memPl K O j q.1

def memG (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin K) O :=
  segRen X.F j O K (Psi O (tanPart q.1) q.2.1)

def memM [NeZero K] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => if Even (segE X.F j i) then tanPart μ i.succ 0 else tanPart μ i.castSucc 0) 0

theorem famEl_eq (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    X.famEl p K O j b q = plEmb O r K (X.memA p K O j b q) * nmEmb O r K (X.memG K O j q) := by
  first
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def, plVar, tanVar]
     ring)
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def]
     ring_nf)

end Dat

def RestMemA (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      X.memA p K O j b q.1 ∈ supported O {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
      X.memG K O j q.1 ∈ supported O {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} ∧
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.memA p K O j b q.1)) ∧
        (¬ Even x → lam1S LZ {y | y < x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.memA p K O j b q.1)) ∧
        geR (valS LZ {y | y < x} (X.memA p K O j b q.1)) (X.thc p K j b x)

def RestMemB (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      ∀ mm ∈ (plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1)).support,
        ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.oc p K j x

def RestMemC (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ Pol O (r + K) b

def RestMemD (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ restrictSupport O (X.resSet p K j)

theorem restMem_of_rests (C₀ : ℝ) (hA : RestMemA C₀) (hB : RestMemB C₀) (hC : RestMemC C₀) (hD : RestMemD C₀) :
    RestMem C₀ := by
  intro p n' r K _ _ _ X O _ _ _ hS hX hCLa hCk j b hb q
  have hA' := hA p n' r K X O hS hX hCLa hCk j b hb q
  have hB' := hB p n' r K X O hS hX hCLa hCk j b hb q
  have hC' := hC p n' r K X O hS hX hCLa hCk j b hb q
  have hD' := hD p n' r K X O hS hX hCLa hCk j b hb q
  rw [X.famEl_eq p K O j b q.1]
  simp only [Dat.Mj, XX', Submodule.mem_inf]
  refine ⟨⟨⟨Submodule.subset_span ⟨X.memA p K O j b q.1, X.memG K O j q.1, X.memM K j q.1.1,
    hA'.1, hA'.2.1, hA'.2.2, rfl⟩, ?_⟩, hC'⟩, hD'⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  exact hB' mm hmm

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeightAlt
section
noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem good_path_weight (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : GoodPathWeight 1088 :=
  good_path_weight_of_top_count D hAdm (top_count_lower_bounds 1088 (by norm_num))

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

