module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0012
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudCount
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem RS.pK_ne : (p : R.Kf) ≠ 0 := by
  obtain ⟨hS, hw, -, -⟩ := R.std
  haveI := hS.frac_O
  have hO : (p : R.O) ≠ 0 := by
    rw [← hS.w_sq]
    exact pow_ne_zero _ hw.ne_zero
  intro h
  apply hO
  apply IsFractionRing.injective R.O R.Kf
  rw [map_zero, map_natCast]
  exact h

theorem be_pull (lam mu : Fin n' → Fin (m + 1) → ℤ) (f : Vsp R.Kf lam →ₗ[R.Kf] Vsp R.Kf mu)
    (g : Module.Dual R.Kf (Vsp R.Kf mu)) (v : Vsp R.Kf lam) :
    be p 1 lam v (((p : R.Kf) ^ (Ar 1 mu - Ar 1 lam)) • (g ∘ₗ f)) = be p 1 mu (f v) g := by
  unfold be
  rw [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← zpow_add₀ R.pK_ne, sub_add_cancel]

theorem cloud_count (hS : LemmaSMat) (hRet : LatRetract) (hBP : BePerfect) (hD3 : DualHeightBasis)
    (H Hp lam : Fin n' → Fin (m + 1) → ℤ) (hdH : IsDominant H) (hdHp : IsDominant Hp)
    (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (t c₂ c₃ : ℕ) (hc : c₃ ≤ c₂) (D₁ : ℝ) (hD : 0 ≤ D₁)
    (hDc : 4 * D₁ < c₂) (nb kk : ℕ) (io : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf Hp)
    (U : Fin nb → Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf lam) (L : Fin nb → Vsp R.Kf lam →ₗ[R.Kf] Vsp R.Kf Hp)
    (ka : Fin nb → ℕ) (hka : ∀ b, ka b ≤ kk)
    (h24 : ∀ a b F, L a (U b F) = if a = b then ((p : R.Kf) ^ ka b) • io F else 0)
    (hiso : ∀ F, io F ∈ Re p R.ι R.σ R.w 1 Hp e ↔ F ∈ Re p R.ι R.σ R.w 1 H e)
    (hio : ∀ F ∈ CCL R H t c₂ e, io F ∈ CCL R Hp t c₂ e)
    (hU : ∀ b, ∀ F ∈ CCL R H t c₂ e, U b F ∈ CCL R lam t c₂ e)
    (hL : ∀ a, ∀ g ∈ CCL' R Hp t c₂ e, ((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (g ∘ₗ L a) ∈ CCL' R lam t c₃ e)
    (n1 n2 : ℕ) (f1 : FacL R H t c₂ e n1 D₁) (f2 : FacL R Hp t c₂ e n2 D₁) :
    ∃ r : ℕ, (n1 : ℝ) + n2 - dL R Hp ≤ r ∧ FacL R lam t c₃ e (nb * r) (2 * D₁ + kk) := by
  classical
  have : IsFractionRing R.O R.Kf := R.std.1.frac_O
  obtain ⟨x1, y1, z1, hx1, hy1, hz1, hv1, hG1⟩ := wit_of_factors R H hD f1
  obtain ⟨x2, y2, z2, hx2, hy2, hz2, hv2, hG2⟩ := wit_of_factors R Hp hD f2
  have hw0 := R.w_ne

  obtain ⟨bH, πH, -, -, -, -, hReH, -⟩ :=
    hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 H hdH e he
  obtain ⟨bP, πP, -, -, -, -, hReP, -⟩ :=
    hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 Hp hdHp e he
  let cH := bH.isUnitSMul (w := fun i => algebraMap R.O R.Kf R.w ^ (-order 1 H (πH i)))
    (fun i => (zpow_ne_zero _ hw0).isUnit)
  let cP := bP.isUnitSMul (w := fun i => algebraMap R.O R.Kf R.w ^ (-order 1 Hp (πP i)))
    (fun i => (zpow_ne_zero _ hw0).isUnit)
  have hcH : Submodule.span R.O (Set.range cH) = Re p R.ι R.σ R.w 1 H e := by
    rw [← hReH]
    congr 2
    funext i
    exact Module.Basis.isUnitSMul_apply _ _
  have hcP : Submodule.span R.O (Set.range cP) = Re p R.ι R.σ R.w 1 Hp e := by
    rw [← hReP]
    congr 2
    funext i
    exact Module.Basis.isUnitSMul_apply _ _
  obtain ⟨ret, hret1, hret2⟩ := hRet R.O R.Kf _ _ _ _ cH cP io (by intro F; rw [hcH, hcP]; exact hiso F)
  rw [hcH, hcP] at hret2

  let tt : Fin n1 → Module.Dual R.Kf (Vsp R.Kf Hp) := fun l => ((p : R.Kf) ^ (Ar 1 H - Ar 1 Hp)) • (y1 l ∘ₗ ret)
  have htt : ∀ F l, be p 1 Hp F (tt l) = be p 1 H (ret F) (y1 l) := fun F l => be_pull R Hp H ret (y1 l) F
  have httm : ∀ l, tt l ∈ Re' p R.ι R.σ R.w 1 Hp e := fun l =>
    ((hBP p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 Hp hdHp e he).1 (tt l)).2 fun F hF => by
      rw [htt]
      obtain ⟨b, hb⟩ := be_Re R H e (hret2 F hF) (hy1 l).1.2
      exact ⟨b, hb.symm⟩
  have hGt : ∀ k k', be p 1 Hp (io (x1 k)) (tt k') =
      algebraMap R.O R.Kf ((z1 • (1 : Matrix (Fin n1) (Fin n1) R.O)) k k') := by
    intro k k'
    rw [htt, hret1, hG1, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i b, ∃ g : R.O, be p 1 Hp (io (x1 i)) (y2 b) = algebraMap R.O R.Kf g :=
    fun i b => be_Re R Hp e (hio _ (hx1 i)).1.2 (hy2 b).1.2
  choose Nm hNm using hNint
  have hBint : ∀ a l, ∃ g : R.O, be p 1 Hp (x2 a) (tt l) = algebraMap R.O R.Kf g :=
    fun a l => be_Re R Hp e (hx2 a).1.2 (httm l)
  choose Bm hBm using hBint
  obtain ⟨r, s, hrs, ⟨P, Q, hPQ⟩, ⟨P', P'', M, hPP, hblk⟩⟩ :=
    hS R.O n1 n2 z1 z2 hz1 hz2 (Matrix.of Nm) (Matrix.of Bm)
  have hz12 : z1 * z2 ≠ 0 := mul_ne_zero hz1 hz2
  have hv12 : vLEO p (z1 * z2) (2 * D₁) := by
    have := vLEO_mul hz1 hz2 hv1 hv2
    rwa [← two_mul] at this

  let Xb : Fin s ⊕ Fin n2 → Vsp R.Kf Hp :=
    Sum.elim (fun i => ∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) x2
  let Yb : Fin s ⊕ Fin n2 → Module.Dual R.Kf (Vsp R.Kf Hp) := Sum.elim (fun l => ∑ k, P'' k l • tt k) y2
  have hXb : ∀ i, Xb i ∈ CCL R Hp t c₂ e := by
    rintro (i | a)
    · refine Submodule.sum_mem _ fun k _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (hio _ (hx1 k))
    · exact hx2 a
  have hYb : ∀ i, Yb i ∈ Re' p R.ι R.σ R.w 1 Hp e := by
    rintro (l | b)
    · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (httm k)
    · exact (hy2 b).1.2
  have hGb : ∀ i j, be p 1 Hp (Xb i) (Yb j) = algebraMap R.O R.Kf
      (Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) R.O)) (P' * Matrix.of Nm) (Matrix.of Bm * P'')
        (z2 • (1 : Matrix (Fin n2) (Fin n2) R.O)) i j) := by
    rintro (i | a) (l | b)
    · show be p 1 Hp (∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) (∑ k, P'' k l • tt k) = _
      rw [be_mat R Hp (fun k => io (x1 k)) tt _ hGt P' P'' i l, Matrix.fromBlocks_apply₁₁]
      congr 1
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    · show be p 1 Hp (∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) (y2 b) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [be_sum_left, Matrix.fromBlocks_apply₁₂, Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hNm, map_mul, Matrix.of_apply]
    · show be p 1 Hp (x2 a) (∑ k, P'' k l • tt k) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [be_sum, Matrix.fromBlocks_apply₂₁, Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hBm, map_mul, Matrix.of_apply]
    · show be p 1 Hp (x2 a) (y2 b) = _
      rw [hG2, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
  have hbadF : FactorsLE p (be (Kf := R.Kf) p 1 Hp) (CCL R Hp t c₂ e) (Re' p R.ι R.σ R.w 1 Hp e)
      (Fintype.card (Fin s ⊕ Fin n2)) (2 * D₁) := by
    refine factorsLE_of_fintype p _ _ _ Xb (fun j => ∑ l, M l j • Yb l) hXb
      (fun j => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hYb l)) (z1 * z2) hz12 hv12 fun i j => ?_
    rw [be_sum]
    have : ∑ l, be p 1 Hp (Xb i) (Yb l) * algebraMap R.O R.Kf (M l j) = algebraMap R.O R.Kf
        ((Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) R.O)) (P' * Matrix.of Nm) (Matrix.of Bm * P'')
          (z2 • (1 : Matrix (Fin n2) (Fin n2) R.O)) * M) i j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hGb, map_mul]
    rw [this, hblk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbad : ((s + n2 : ℕ) : ℝ) ≤ dL R Hp := by
    have hcard : Fintype.card (Fin s ⊕ Fin n2) = s + n2 := by simp
    rw [hcard] at hbadF
    exact nLeD R Hp hdHp t c₂ (s + n2) (2 * D₁) (by linarith) (by linarith) e he hbadF

  refine ⟨r, ?_, ?_⟩
  · have h1 : ((r + s : ℕ) : ℝ) = n1 := by exact_mod_cast hrs
    push_cast at h1 hbad
    linarith
  let Fg : Fin r → Vsp R.Kf H := fun i => ∑ k, algebraMap R.O R.Kf (P i k) • x1 k
  let gg : Fin r → Module.Dual R.Kf (Vsp R.Kf Hp) := fun j => ∑ b, Q b j • y2 b
  have hFg : ∀ i, Fg i ∈ CCL R H t c₂ e := fun i => by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hx1 k)
  have hgg : ∀ j, gg j ∈ CCL' R Hp t c₂ e := fun j =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hy2 b)
  have hFgg : ∀ i j, be p 1 Hp (io (Fg i)) (gg j) = if i = j then algebraMap R.O R.Kf (z1 * z2) else 0 := by
    intro i j
    have e1 : io (Fg i) = ∑ k, algebraMap R.O R.Kf (P i k) • io (x1 k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fg, map_sum, map_smul]
    rw [e1, be_mat R Hp (fun k => io (x1 k)) y2 (Matrix.of Nm) (fun k k' => hNm k k') P Q i j, hPQ,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hcardg : Fintype.card (Fin nb × Fin r) = nb * r := by simp
  rw [← hcardg]
  refine factorsLE_of_fintype p _ _ _ (fun x : Fin nb × Fin r => U x.1 (Fg x.2))
    (fun y : Fin nb × Fin r => ((p : R.O) ^ (kk - ka y.1)) •
      (((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (gg y.2 ∘ₗ L y.1)))
    (fun x => CCL_anti_c R lam hc t e (hU x.1 _ (hFg x.2)))
    (fun y => Submodule.smul_mem _ _ (hL y.1 _ (hgg y.2)))
    ((p : R.O) ^ kk * (z1 * z2)) (mul_ne_zero (pow_ne_zero _ R.p_ne) hz12)
    (vLEO_pow_mul R.p_ne R.p_not_unit hz12 kk hv12) ?_
  rintro ⟨b, i⟩ ⟨a, j⟩
  show be p 1 lam (U b (Fg i)) (((p : R.O) ^ (kk - ka a)) •
      (((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (gg j ∘ₗ L a))) = _
  rw [be_smul, be_pull, h24]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, be_smulK_left, hFgg]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      simp only [map_mul, map_pow, map_natCast]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hka a)]
    · have : ((a, i) : Fin nb × Fin r) ≠ (a, j) := fun h => hij (Prod.mk.inj h).2
      rw [if_neg hij, if_neg this, mul_zero, mul_zero]
  · have : ((b, i) : Fin nb × Fin r) ≠ (a, j) := fun h => hab (Prod.mk.inj h).1.symm
    rw [if_neg hab, if_neg this]
    simp [be]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility MvPolynomial

theorem dualWeyl_mul (R : Type*) [CommRing R] (r n : ℕ) (ν ν' : Fin n → ℕ) {F G : MvPolynomial (Fin r × Fin n) R}
    (hF : F ∈ dualWeyl R r n ν) (hG : G ∈ dualWeyl R r n ν') : F * G ∈ dualWeyl R r n (ν + ν') := by
  rw [dualWeyl, Submodule.mem_inf] at hF hG ⊢
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2
    (((mem_weightedHomogeneousSubmodule _ _ _ _).1 hF.1).mul
      ((mem_weightedHomogeneousSubmodule _ _ _ _).1 hG.1)), ?_⟩
  have hF2 := hF.2
  have hG2 := hG.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    sub_eq_zero] at hF2 hG2 ⊢
  intro l j hlj
  rw [map_mul, map_mul, hF2 l j hlj, hG2 l j hlj]

theorem one_mem_dualWeyl (R : Type*) [CommRing R] (r n : ℕ) : (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  rw [dualWeyl, Submodule.mem_inf]
  refine ⟨(mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_one _ _), ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    map_one, sub_self, implies_true]

section Ten

variable {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] {S : Type*} [Fintype S] {k n : ℕ}

theorem tensorLat_mul (M N L : S → Submodule R (MvPolynomial (Fin k × Fin n) K))
    (h : ∀ s, ∀ F ∈ M s, ∀ G ∈ N s, F * G ∈ L s) :
    ∀ P ∈ tensorLat R K M, ∀ Q ∈ tensorLat R K N, P * Q ∈ tensorLat R K L := by
  intro P hP Q hQ
  have hmem : P * Q ∈ tensorLat R K M * tensorLat R K N := Submodule.mul_mem_mul hP hQ
  rw [tensorLat, tensorLat, Submodule.span_mul_span] at hmem
  refine (Submodule.span_le.2 ?_) hmem
  rintro x ⟨a, ⟨F, hF, rfl⟩, b, ⟨G, hG, rfl⟩, rfl⟩
  apply Submodule.subset_span
  refine ⟨fun s => F s * G s, fun s => h s _ (hF s) _ (hG s), ?_⟩
  simp [map_mul, Finset.prod_mul_distrib]

end Ten

theorem nuOf_zero (m : ℕ) : nuOf (0 : Fin (m + 1) → ℤ) = 0 := by
  funext t
  simp [nuOf]

theorem Vsp_eq (Kf : Type) [Field Kf] {n' m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lam0) :
    Vsp Kf lam0 = tensorLat Kf Kf (fun s => dualWeyl Kf (m + 1) (m + 1) (nuOf (lamAt lam0 s))) := by
  unfold Vsp
  congr 1
  funext s
  rw [if_pos (kp_lamAt_antitone lam0 hdom s)]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ProdSmulPowT
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def ExistsIO : Prop :=
  ∀ (K : Type) [Field K] (S α : Type) [Fintype S] [DecidableEq S] (TT : Finset S)
    (i : TT → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K),
    ∃ IO : MvPolynomial (S × α) K →ₗ[K] MvPolynomial ((TT × Bool) × α) K, ∀ P : S → MvPolynomial α K,
      (∀ s, s ∉ TT → P s = 1) → IO (∏ s, rename (fun v => (s, v)) (P s)) =
        ∏ s : TT, rename (fun v : Bool × α => ((s, v.1), v.2)) (i s (P s.val))

def ExistsPR : Prop :=
  ∀ (K : Type) [Field K] (S α : Type) [Fintype S] [DecidableEq S] (TT : Finset S)
    (pr : TT → MvPolynomial (Bool × α) K →ₗ[K] MvPolynomial α K),
    ∃ PR : MvPolynomial ((TT × Bool) × α) K →ₗ[K] MvPolynomial (S × α) K, ∀ Y : TT → MvPolynomial (Bool × α) K,
      PR (∏ s : TT, rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) =
        ∏ s : TT, rename (fun v => (s.val, v)) (pr s (Y s))

def RegroupP : Prop :=
  ∀ (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (T α : Type) [Fintype T] [DecidableEq T]
    (N : T × Bool → Submodule R (MvPolynomial α K)) (y : T → MvPolynomial (Bool × α) K),
    (∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K, (∀ b, F b ∈ N (s, b)) ∧
      P = ∏ b, rename (fun v => (b, v)) (F b)}) →
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K, (∀ x, F x ∈ N x) ∧
        P = ∏ x, rename (fun v => (x, v)) (F x)}

section Abs

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {n' k n : ℕ} (TT : Finset (Fin n'))

theorem prodSmulPowT {σ ι : Type} [Fintype ι] (c : K) (w : ι → MvPolynomial σ K) :
    ∏ s, (c • w s) = c ^ Fintype.card ι • ∏ s, w s := by
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    map_pow]

theorem genRegroupT (F : TT × Bool → MvPolynomial (Fin k × Fin n) K) :
    ∏ x, blockEmb K x (F x) =
      ∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (∏ b, blockEmb K b (F (s, b))) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ =>
    (MvPolynomial.rename_rename (R := K) (fun v : Fin k × Fin n => (b, v))
      (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (F (s, b))).symm

theorem prodTopsT (G : TT → MvPolynomial (Fin k × Fin n) K) :
    ∏ s : TT, rename (fun v => (s.val, v)) (G s) =
      ∏ s : Fin n', blockEmb K s (if h : s ∈ TT then G ⟨s, h⟩ else 1) := by
  symm
  rw [← Finset.prod_subset (Finset.subset_univ TT)]
  · rw [← Finset.prod_coe_sort TT]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [dite_eq_left s.2]
    rfl
  · intro s _ hs
    rw [dif_neg hs, map_one]

theorem ioMem (hK2 : RegroupP) (i : TT → MvPolynomial (Fin k × Fin n) K →ₗ[K] MvPolynomial (Bool × (Fin k × Fin n)) K)
    (IO : MvPolynomial (Fin n' × (Fin k × Fin n)) K →ₗ[K] MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K)
    (hIO : ∀ P : Fin n' → MvPolynomial (Fin k × Fin n) K, (∀ s, s ∉ TT → P s = 1) →
      IO (∏ s, rename (fun v => (s, v)) (P s)) =
        ∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (i s (P s.val)))
    (Nv : Fin n' → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (N2 : TT × Bool → Submodule A (MvPolynomial (Fin k × Fin n) K)) (c : K)
    (h1 : ∀ s : TT, ∀ y ∈ Nv s.val, c • i s y ∈ tensorLat A K (fun b => N2 (s, b)))
    (h0 : ∀ s, s ∉ TT → ∀ y ∈ Nv s, ∃ a : A, y = C (algebraMap A K a)) :
    ∀ y ∈ tensorLat A K Nv, c ^ TT.card • IO y ∈ tensorLat A K N2 := by
  have hcomm : ∀ (a : A) (z : MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K),
      c ^ TT.card • a • z = a • c ^ TT.card • z := fun a z => by
    rw [← algebraMap_smul K a z, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    classical
    let a' : Fin n' → A := fun s =>
      if h : s ∈ TT then 1 else Classical.choose (h0 s h (F s) (hF s))
    let P : Fin n' → MvPolynomial (Fin k × Fin n) K := fun s => if s ∈ TT then F s else 1
    have hP : ∀ s, s ∉ TT → P s = 1 := fun s hs => if_neg hs
    have hPF : ∀ s : TT, P s.val = F s.val := fun s => if_pos s.2
    have hterm : ∀ s, blockEmb K s (F s) =
        MvPolynomial.C (algebraMap A K (a' s)) * rename (fun v : Fin k × Fin n => (s, v)) (P s) := by
      intro s
      by_cases h : s ∈ TT
      · simp [a', P, h, blockEmb]
      · have e := Classical.choose_spec (h0 s h (F s) (hF s))
        simp only [a', P, dif_neg h, if_neg h, map_one, mul_one]
        conv_lhs => rw [e]
        exact MvPolynomial.rename_C _ _
    have hy : ∏ s, blockEmb K s (F s) =
        (∏ s, a' s) • ∏ s, rename (fun v : Fin k × Fin n => (s, v)) (P s) := by
      rw [Finset.prod_congr rfl fun s _ => hterm s, Finset.prod_mul_distrib, Algebra.smul_def,
        MvPolynomial.algebraMap_apply]
      simp only [map_prod]
    have hmem := hK2 A K TT (Fin k × Fin n) N2 (fun s => c • i s (P s.val))
      (fun s => by
        simp only [hPF s]
        exact h1 s (F s.val) (hF s.val))
    have hc : ∀ w : TT → MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K,
        c ^ TT.card • ∏ s, w s = ∏ s, c • w s := fun w => by
      rw [prodSmulPowT, Fintype.card_coe]
    rw [hy, LinearMap.map_smul_of_tower, hcomm]
    refine Submodule.smul_mem _ _ ?_
    rw [hIO P hP, hc]
    simp only [map_smul] at hmem
    exact hmem
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [LinearMap.map_smul_of_tower, hcomm]
    exact Submodule.smul_mem _ a ih

theorem prMem (pr : TT → MvPolynomial (Bool × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
    (PR : MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin n' × (Fin k × Fin n)) K)
    (hPR : ∀ Y : TT → MvPolynomial (Bool × (Fin k × Fin n)) K,
      PR (∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (Y s)) =
        ∏ s : TT, rename (fun v => (s.val, v)) (pr s (Y s)))
    (Nv : Fin n' → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (N2 : TT × Bool → Submodule A (MvPolynomial (Fin k × Fin n) K)) (c : K)
    (h1 : ∀ s : TT, ∀ x ∈ tensorLat A K (fun b => N2 (s, b)), c • pr s x ∈ Nv s.val)
    (h0 : ∀ s, s ∉ TT → (1 : MvPolynomial (Fin k × Fin n) K) ∈ Nv s) :
    ∀ x ∈ tensorLat A K N2, c ^ TT.card • PR x ∈ tensorLat A K Nv := by
  have hcomm : ∀ (a : A) (z : MvPolynomial (Fin n' × (Fin k × Fin n)) K),
      c ^ TT.card • a • z = a • c ^ TT.card • z := fun a z => by
    rw [← algebraMap_smul K a z, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  have hc : ∀ w : TT → MvPolynomial (Fin n' × (Fin k × Fin n)) K,
      c ^ TT.card • ∏ s, w s = ∏ s, c • w s := fun w => by
    rw [prodSmulPowT, Fintype.card_coe]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have ht := prodTopsT TT (fun s => c • pr s (∏ b, blockEmb K b (F (s, b))))
    simp only [map_smul] at ht
    rw [genRegroupT, hPR, hc, ht]
    refine Submodule.subset_span ⟨fun s => if h : s ∈ TT then
      c • pr ⟨s, h⟩ (∏ b, blockEmb K b (F (⟨s, h⟩, b))) else 1, fun s => ?_, rfl⟩
    dsimp only
    by_cases h : s ∈ TT
    · rw [dite_eq_left h]
      exact h1 ⟨s, h⟩ _ (Submodule.subset_span ⟨fun b => F (⟨s, h⟩, b), fun b => hF _, rfl⟩)
    · rw [dif_neg h]
      exact h0 s h
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [LinearMap.map_smul_of_tower, hcomm]
    exact Submodule.smul_mem _ a ih

end Abs

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.SingleWeightLatticeComparison
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def wtPQ (m P Q : ℕ) : Fin (m + 1) → ℤ := fun i => if i = 0 then (P : ℤ) else if i = Fin.last m then -(Q : ℤ) else 0

def twoLat (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] (m P Q : ℕ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf fun b : Bool => H0 O m (letterWt m (if b then P else Q) b) Λ

def twoSp (Kf : Type) [Field Kf] (m P Q : ℕ) : Submodule Kf (MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat Kf Kf fun b : Bool => dualWeyl Kf (m + 1) (m + 1) (nuOf (letterWt m (if b then P else Q) b))

def SingleWeightLatticeComparison : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (a P Q : ℕ), P + Q + 1 ≤ 8 * a →
    ∃ (i : ℕ → MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf →ₗ[R.Kf]
        MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf)
      (pr : ℕ → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf →ₗ[R.Kf]
        MvPolynomial (Fin (m + 1) × Fin (m + 1)) R.Kf),
      (∀ x ∈ twoSp R.Kf m P Q, ∑ j ∈ Finset.range (min P Q + 1), i j (pr j x) = x) ∧
      (∀ j ≤ min P Q,
        (∀ x ∈ twoSp R.Kf m P Q, pr j x ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j)))) ∧
        (∀ y ∈ dualWeyl R.Kf (m + 1) (m + 1) (nuOf (wtPQ m (P - j) (Q - j))), i j y ∈ twoSp R.Kf m P Q)) ∧
      ∀ Λ : Submodule R.O (Fin (m + 1) → R.Kf), IsLattice R.O Λ → ∀ j ≤ min P Q,
        (∀ x ∈ twoLat R.O m P Q Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • pr j x ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ) ∧
        (∀ y ∈ H0 R.O m (wtPQ m (P - j) (Q - j)) Λ,
          ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) • i j y ∈ twoLat R.O m P Q Λ)

end Formalism.MainNotions.flipOneThree.Pf

end
end

