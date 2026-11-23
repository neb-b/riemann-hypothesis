module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0059
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GflagSwap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0031
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0060
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0017

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormTG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.NGCut.NormalIntegrality

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem zhat_int {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) :
    ∃ FinalForm : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E),
      Zhat F F' = FinalForm.map (algebraMap (𝓞 D.host.E) D.host.E) := by
  have hmem : ∀ a b, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = Zhat F F' a b := by
    intro a b
    have hx : F'.fvec b ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by
      rw [show Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ from hun]
      exact hF' b
    unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual at hx
    have h1 := (Submodule.mem_iInf _).mp hx (F.fvec a)
    have h2 := (Submodule.mem_iInf _).mp h1 (hF a)
    rw [Submodule.mem_comap] at h2
    exact Submodule.mem_one.mp h2
  choose FinalForm hZo using hmem
  exact ⟨Matrix.of FinalForm, by ext a b; exact (hZo a b).symm⟩

theorem yv_mem {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hun : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    (n : ℕ) {T' : D.host.E} (F : FlagG (VS D) D.R.rS (n : D.host.E)) (F' : FlagG (VS D) D.R.rS T')
    (hF : ∀ b, F.fvec b ∈ Λ) (hF' : ∀ b, F'.fvec b ∈ Λ) : NormalVectorPairings.yv F F' ∈ Λ := by
  obtain ⟨FinalForm, hZo⟩ := zhat_int hun F F' hF hF'
  have hadj : (Zhat F F').adjugate = FinalForm.adjugate.map (algebraMap (𝓞 D.host.E) D.host.E) := by
    rw [hZo]
    exact (RingHom.map_adjugate _ _).symm
  have hD : Dl F F' (D.R.rS + 1) = algebraMap (𝓞 D.host.E) D.host.E
      ((FinalForm.submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl)).det) := by
    unfold Dl leadMinorE
    rw [dite_eq_left le_rfl, hZo, Matrix.submatrix_map, RingHom.map_det]
    rfl
  unfold NormalVectorPairings.yv NormalVectorPairings.omp
  refine Λ.add_mem ?_ ?_
  · rw [Nat.cast_smul_eq_nsmul]
    refine nsmul_mem (Λ.sum_mem fun b _ => ?_) n
    rw [hadj, Matrix.map_apply, algebraMap_smul]
    exact Λ.smul_mem _ (hF' b)
  · rw [hD, algebraMap_smul]
    have hz : F.z = F.fvec (Fin.last _) := by simp [FlagG.fvec]
    rw [hz]
    exact Λ.smul_mem _ (hF _)

theorem yv_orth_X {T T' : D.host.E} (F : FlagG (VS D) D.R.rS T) (F' : FlagG (VS D) D.R.rS T') :
    ∀ x ∈ F.X, brS (VS D) (NormalVectorPairings.yv F F') x = 0 := by
  have key : ∀ a : Fin D.R.rS, (VS D).hT (F.e a) (NormalVectorPairings.yv F F') = 0 := by
    intro a
    have hz : ∀ b, (VS D).hT (F.e a) (F'.fvec b) = Zhat F F' a.castSucc b := by
      intro b
      simp [Zhat, brS, FlagG.fvec, Fin.snoc_castSucc]
    have hm := congrFun (congrFun (Matrix.mul_adjugate (Zhat F F')) a.castSucc) (Fin.last _)
    rw [Matrix.mul_apply] at hm
    simp only [Matrix.smul_apply, Matrix.one_apply, Fin.castSucc_ne_last, if_false, smul_zero] at hm
    unfold NormalVectorPairings.yv NormalVectorPairings.omp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_smul, map_smul, F.z_orth a, smul_zero, add_zero, map_sum]
    simp only [map_smul, smul_eq_mul, hz]
    rw [show ∑ b, (Zhat F F').adjugate b (Fin.last D.R.rS) * Zhat F F' a.castSucc b =
        ∑ b, Zhat F F' a.castSucc b * (Zhat F F').adjugate b (Fin.last D.R.rS) from
      Finset.sum_congr rfl fun b _ => mul_comm _ _, hm, mul_zero]
  intro x hx
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y (NormalVectorPairings.yv F F') = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    exact key a
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem X_iso {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : ∀ x ∈ F.X, ∀ x' ∈ F.X, brS (VS D) x x' = 0 := by
  intro x hx x' hx'
  simp only [brS]
  refine Submodule.span_induction (p := fun y _ => (VS D).hT y x = 0) ?_ ?_ ?_ ?_ hx'
  · rintro _ ⟨b, rfl⟩
    refine Submodule.span_induction (p := fun y _ => (VS D).hT (F.e b) y = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, rfl⟩
      exact F.e_iso b a
    · simp
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro c y _ hy
      simp [hy]
  · simp
  · intro y z _ _ hy hz
    simp [hy, hz]
  · intro c y _ hy
    simp [hy]

theorem abs_norm_TG (n : ℕ) (g : D.host.E) :
    |((Algebra.norm ℚ ((n : D.host.E) * g) : ℚ) : ℝ)| =
      (n : ℝ) ^ (2 * D.R.f) * (∏ w : InfinitePlace D.host.E, w g) ^ 2 := by
  have hc : ∀ w : InfinitePlace D.host.E, w.mult = 2 := by
    intro w
    have hnr : ¬ w.IsReal := by
      intro hw
      have hr := InfinitePlace.isReal_iff.mp hw
      have h2 : starRingEnd ℂ (w.embedding D.host.sqq) = w.embedding D.host.sqq :=
        RingHom.congr_fun hr _
      have h1 : w.embedding D.host.sqq ^ 2 = w.embedding (-(D.host.q : D.host.E)) := by
        rw [← map_pow, D.host.sqq_sq]
      have h3 := Complex.conj_eq_iff_re.mp h2
      rw [← h3, map_neg, map_natCast] at h1
      have h4 := congrArg Complex.re h1
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.neg_re, Complex.natCast_re] at h4
      have hq0 : 0 < D.host.q := by have := D.host.qd_big.1; omega
      have hq : (0 : ℝ) < D.host.q := by exact_mod_cast hq0
      nlinarith [mul_self_nonneg (w.embedding D.host.sqq).re]
    simp [InfinitePlace.mult, hnr]
  have hprod := InfinitePlace.prod_eq_abs_norm g
  simp only [hc, Finset.prod_pow] at hprod
  rw [← map_natCast (algebraMap ℚ D.host.E) n, map_mul, Algebra.norm_algebraMap,
    Formalism.MainNotions.BridgeLemma.szf_finrankE D, hprod]
  push_cast
  rw [abs_mul, abs_pow, Nat.abs_cast]

end Formalism.L2.SG.NGCut.NormalIntegrality
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CardPiOfUnique
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount

namespace Formalism.L2.SG.Pf.FrameGlobalPatching

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_pi_of_unique {ι : Type*} {α : ι → Type*} (T : Finset ι) (h : ∀ i ∉ T, Nonempty (Unique (α i))) :
    Nat.card (∀ i, α i) = ∏ᶠ i, Nat.card (α i) := by
  haveI : ∀ i : {i // i ∉ T}, Unique (α i) := fun i => (h i.1 i.2).some
  rw [Nat.card_congr (Equiv.piEquivPiSubtypeProd (fun i => i ∈ T) α), Nat.card_prod,
    Nat.card_unique (α := ∀ i : {i // i ∉ T}, α i), mul_one, Nat.card_pi]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
  · exact (Finset.prod_coe_sort T (fun i => Nat.card (α i)))
  · intro i hi
    by_contra hT
    haveI := (h i hT).some
    exact hi Nat.card_unique

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u))
  (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def LocFullC : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 → kind w' = kind w →
  ∀ Z : PairVal.MatR D, AtMat w' Z →
  ∀ (F'₂ : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E))
    (φ : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (tLoc Zd p γ).f)
    (φ' : ∀ p, (locH Zd p).Wb (tLoc Zd p γ).f' ≃ₗ[(D.s.atP p).Ep] (locH Zd p).Wb (locF' Zd p F'₂)),
    ZhatL (lf D F0) F'₂ = Z →
    (∀ p, LsDatumA.LocalCountHypotheses (locH Zd p) (tLoc Zd p γ) (tLoc Zd p γ).f (locF' Zd p F'₂) (φ p) (φ' p)) →
    ∀ p, ∀ M ∈ locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p),
      ∃ Λ' : Submodule (𝓞 D.host.E) (VS D).V, Submodule.IsFullLattice D.host.E Λ' ∧ M = lattice₂ D Zd.M p Λ'

variable {Zd u u' F0 what₂}

theorem patchC_of (hP : LatPatch) (hL : LocFullC Zd u u' F0 what₂) : PatchC Zd u u' F0 what₂ := by
  intro γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT hC
  obtain ⟨Λ₀, hΛ₀, hfin⟩ := hC
  have hfull := hL γ w hγ w' hG' hk Z hZ F'₂ φ φ' hF hT
  set S : ∀ p : PlF D, Set (Submodule (Zd.M p).L.O (Vp D p)) :=
    fun p => locSet Zd p (tLoc Zd p γ) (locF' Zd p F'₂) (φ p) (φ' p) with hS
  have hex : ∀ f : ∀ p, S p, ∃! Λ : Submodule (𝓞 D.host.E) (VS D).V,
      Submodule.IsFullLattice D.host.E Λ ∧ ∀ p, lattice₂ D Zd.M p Λ = (f p).1 := fun f =>
    hP D Zd Λ₀ hΛ₀ (fun p => (f p).1) (fun p => hfull p _ (f p).2)
      (hfin.subset fun p hp hS' => hp (Set.mem_singleton_iff.1 ((Set.ext_iff.1 hS' (f p).1).1 (f p).2)))
  let e : GlobSet Zd γ F'₂ φ φ' ≃ ∀ p, S p :=
    { toFun := fun Λ p => ⟨lattice₂ D Zd.M p Λ.1, Λ.2.2 p⟩
      invFun := fun f => ⟨(hex f).choose, (hex f).choose_spec.1.1, fun p => by
        rw [(hex f).choose_spec.1.2 p]; exact (f p).2⟩
      left_inv := fun Λ => by
        apply Subtype.ext
        exact (hex _).unique (hex _).choose_spec.1 ⟨Λ.2.1, fun p => rfl⟩
      right_inv := fun f => by
        funext p
        exact Subtype.ext ((hex f).choose_spec.1.2 p) }
  rw [Nat.card_congr e]
  obtain ⟨T, hTs⟩ := hfin.exists_finset
  refine card_pi_of_unique (α := fun p => S p) T (fun p hp => ?_)
  have hsing : S p = {lattice₂ D Zd.M p Λ₀} := by
    by_contra hne
    exact hp ((hTs p).2 hne)
  rw [hsing]
  exact ⟨Set.uniqueSingleton _⟩

end Formalism.L2.SG.Pf.FrameGlobalPatching
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CrossTranspose
section
noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

variable {K K' : Type*} [CommRing K] [CommRing K'] {r : ℕ}

def ld (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : K := (A.submatrix Fin.castSucc Fin.castSucc).det

def Ec (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then 1 else 0

theorem ld_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) : ld (A + t • Ec r) = ld A := by
  unfold ld
  congr 1
  ext a b
  simp [Ec, Fin.castSucc_ne_last]

theorem det_add_corner (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (t : K) :
    (A + t • Ec r).det = A.det + t * ld A := by
  have hE : A + t • Ec r = A.updateRow (Fin.last r) (A (Fin.last r) + t • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb; simp [Ec]
      · simp [Ec, hb]
    · simp [Ec, ha]
  rw [hE, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  have h0 : ∀ j : Fin r, (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)) (Fin.last r) j.castSucc = 0 := by
    intro j
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]
  simp only [h0, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Matrix.updateRow_self,
    Pi.single_eq_same, mul_one, Fin.succAbove_last]
  have hs : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix Fin.castSucc Fin.castSucc =
      A.submatrix Fin.castSucc Fin.castSucc := by
    ext a b
    simp only [Matrix.submatrix_apply]
    rw [Matrix.updateRow_ne (Fin.castSucc_ne_last a)]
  rw [hs, ld]
  have hpow : ((-1 : K) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := Even.neg_one_pow ⟨_, rfl⟩
  rw [hpow, one_mul]

theorem ld_smul (c : K) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (c • A) = c ^ r * ld A := by
  unfold ld
  rw [show (c • A).submatrix Fin.castSucc Fin.castSucc = c • A.submatrix Fin.castSucc Fin.castSucc from rfl,
    Matrix.det_smul, Fintype.card_fin]

theorem ld_transpose (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld Aᵀ = ld A := by
  unfold ld
  rw [← Matrix.det_transpose]
  rfl

theorem ld_map (f : K →+* K') (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : ld (A.map f) = f (ld A) := by
  unfold ld
  rw [RingHom.map_det]
  rfl

def Cross (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : Prop := ld A * A'.det = ld A' * A.det

theorem cross_shift {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c t : K) :
    Cross (c • A + t • Ec r) (c • A' + t • Ec r) := by
  unfold Cross at h ⊢
  rw [ld_add_corner, ld_add_corner, det_add_corner, det_add_corner, ld_smul, ld_smul, Matrix.det_smul,
    Matrix.det_smul, Fintype.card_fin]
  linear_combination c ^ r * c ^ (r + 1) * h

theorem cross_transpose {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') : Cross Aᵀ A'ᵀ := by
  unfold Cross at h ⊢
  rw [ld_transpose, ld_transpose, Matrix.det_transpose, Matrix.det_transpose]
  exact h

theorem cross_map (f : K →+* K') {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (A.map f) (A'.map f) := by
  unfold Cross at h ⊢
  have e1 : (A'.map f).det = f A'.det := (RingHom.map_det f A').symm
  have e2 : (A.map f).det = f A.det := (RingHom.map_det f A).symm
  rw [ld_map, ld_map, e1, e2, ← map_mul, ← map_mul, h]

theorem cross_scale (x y : Fin (r + 1) → K) {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') :
    Cross (Matrix.of fun a b => y b * x a * A a b) (Matrix.of fun a b => y b * x a * A' a b) := by
  have e : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      (Matrix.of fun a b => y b * x a * B a b) = Matrix.diagonal x * B * Matrix.diagonal y := by
    intro B; ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]; ring
  have el : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) K,
      ld (Matrix.diagonal x * B * Matrix.diagonal y) = (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * ld B := by
    intro B
    unfold ld
    have : (Matrix.diagonal x * B * Matrix.diagonal y).submatrix Fin.castSucc Fin.castSucc =
        Matrix.diagonal (fun i : Fin r => x i.castSucc) * B.submatrix Fin.castSucc Fin.castSucc *
          Matrix.diagonal (fun i : Fin r => y i.castSucc) := by
      ext a b; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
    rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
    ring
  unfold Cross at h ⊢
  rw [e, e, el, el, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
  linear_combination (∏ i : Fin r, x i.castSucc) * (∏ i : Fin r, y i.castSucc) * (Matrix.diagonal x).det *
    (Matrix.diagonal y).det * h

theorem kappa_eq {A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : Cross A A') (c : K)
    (hu : IsUnit (A + c • (Ec (K := K) r)).det) (hu' : IsUnit (A' + c • (Ec (K := K) r)).det) :
    (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) = (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) := by
  have k1 := SplitCoefficientComponents.inv_last_mul_det (A + c • (Ec (K := K) r)) hu
  have k2 := SplitCoefficientComponents.inv_last_mul_det (A' + c • (Ec (K := K) r)) hu'
  have l1 : ((A + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A := ld_add_corner A c
  have l2 : ((A' + c • (Ec (K := K) r)).submatrix Fin.castSucc Fin.castSucc).det = ld A' := ld_add_corner A' c
  rw [l1, det_add_corner] at k1
  rw [l2, det_add_corner] at k2
  rw [det_add_corner] at hu hu'
  unfold Cross at h
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hu'
  have key : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
      (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    have e1 : (A + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A * (A'.det + c * ld A') := by rw [← mul_assoc, k1]
    have e2 : (A' + c • (Ec (K := K) r))⁻¹ (Fin.last r) (Fin.last r) * ((A.det + c * ld A) * (A'.det + c * ld A')) =
        ld A' * (A.det + c * ld A) := by rw [mul_comm (A.det + _), ← mul_assoc, k2]
    rw [e1, e2]
    linear_combination h
  have hunit : IsUnit ((A.det + c * ld A) * (A'.det + c * ld A')) := by
    rw [← hv, ← hv']; exact (v * v').isUnit
  exact hunit.mul_right_cancel key

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNG
section
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut Formalism.L2.SG.LsDatumB
  Formalism.L2.SG.TermLoc Formalism.L2.SG.Pf.PCount Formalism.L2.SG.Pf.FrameGlobalPatching

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D) {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

section Place

variable (p : PlF D) (γ : TermDef.Term D u u' F0 what₂)
  (hu : ∀ a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a))

include hu in
theorem baseChangeAt_frame_eq (a : Fin (D.R.rS + 1)) :
    baseChange₂ D p (frame (lf D F0) a) = ((hu a).unit⁻¹ : ((D.s.atP p).Ep)ˣ) • (tLoc Zd p γ).f a := by
  rw [tf, Units.smul_def, smul_smul, (hu a).val_inv_mul, one_smul]

include hu in
theorem bcP_X {x : (VS D).V} (hx : x ∈ Xsp (lf D F0)) : baseChange₂ D p x ∈ (locH Zd p).X (tLoc Zd p γ).f := by
  change x ∈ Submodule.span D.host.E (Set.range F0.e) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [← frame_cs, baseChangeAt_frame_eq Zd p γ hu, Units.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [(baseChange₂ D p).map_add]; exact add_mem ha hb
  | smul c x _ hx => rw [Formalism.L2.SG.Pf.LocalDenominators.baseChange_smul₂]; exact Submodule.smul_mem _ _ hx

theorem baseChange_mem_perp_sup {m : (VS D).V} (hm : m ∈ orth (VS D) (Xsp (lf D F0))) :
    baseChange₂ D p m ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f) := by
  show ∀ w ∈ (locH Zd p).X (tLoc Zd p γ).f, (locH Zd p).h (baseChange₂ D p m) w = 0
  intro w hw
  rw [h_eq]
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    simp only
    rw [tf, frame_cs, LocFacts.localForm_smul_right, ← h_eq, localForm_baseChange,
      (PI.UnitaryGroupMassFormula.BetaLUniq.mem_orth (VS D)).1 hm _ (Submodule.subset_span ⟨i, rfl⟩), map_zero, mul_zero]
  | zero => exact LocFacts.localForm_zero_right Zd p _
  | add a b _ _ ha hb => rw [LocFacts.localForm_add_right, ha, hb, add_zero]
  | smul c w _ hw => rw [LocFacts.localForm_smul_right, hw, mul_zero]

theorem h_X_perp {w v : Vp D p} (hw : w ∈ (locH Zd p).X (tLoc Zd p γ).f)
    (hv : v ∈ (locH Zd p).perp ((locH Zd p).X (tLoc Zd p γ).f)) : (locH Zd p).h w v = 0 := by
  rw [(locH Zd p).h_herm v w, (show (locH Zd p).h v w = 0 from hv w hw), map_zero]

end Place

theorem pair_int (γ : TermDef.Term D u u' F0 what₂) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (hSD₁ : ∀ p, (locH Zd p).IsSelfDual (lattice₂ D Zd.M p Λ₁))
    (hL : ∀ p, (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f ⊆
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₁) (tLoc Zd p γ).f)
    {x m : (VS D).V} (hx : x ∈ Λ₂) (hxo : x ∈ orth (VS D) (Xsp (lf D F0))) (hm : m ∈ Λ₁)
    (hmo : m ∈ orth (VS D) (Xsp (lf D F0))) : IsIntegral ℤ ((VS D).hT m x) := by
  refine int_of_loc Zd fun p => ?_
  rw [← localForm_baseChange]
  have hv := baseChange_mem_perp_sup Zd p γ hxo
  have hmem : (locH Zd p).mkW (tLoc Zd p γ).f ⟨baseChange₂ D p x, hv⟩ ∈
      (locH Zd p).Lset (lattice₂ D Zd.M p Λ₂) (tLoc Zd p γ).f := ⟨⟨baseChange₂ D p x, hv⟩, baseChange_mem_localLattice Zd hx p, rfl⟩
  obtain ⟨x'', hx''Λ, hx''eq⟩ := hL p hmem
  have hdiff : (baseChange₂ D p x) - (x'' : Vp D p) ∈ (locH Zd p).X (tLoc Zd p γ).f := by
    have := (Submodule.Quotient.eq _).1 hx''eq.symm
    simpa using this
  have e : baseChange₂ D p x = (x'' : Vp D p) + ((baseChange₂ D p x) - (x'' : Vp D p)) := by abel
  rw [e, (locH Zd p).h_add_left, h_X_perp Zd p γ hdiff (baseChange_mem_perp_sup Zd p γ hmo), add_zero]
  exact ((hSD₁ p).2.2 x'').1 hx''Λ (baseChange₂ D p m) (baseChange_mem_localLattice Zd hm p)

theorem memX (γ : TermDef.Term D u u' F0 what₂) {Λa Λb : Submodule (𝓞 D.host.E) (VS D).V}
    (ha : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λa) (tLoc Zd p γ).f)
    (hb : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λb) (tLoc Zd p γ).f) (hΛb : Submodule.IsFullLattice D.host.E Λb)
    (hu : ∀ p a, IsUnit (TermLoc.sgnP D p a * frFac Zd.δ p a)) {x : (VS D).V} (hx : x ∈ Xsp (lf D F0))
    (hxa : x ∈ Λa) : x ∈ Λb := by
  refine mem_of_bcP Zd hΛb fun p => ?_
  have h1 : baseChange₂ D p x ∈ Submodule.span (D.s.atP p).Ep (Set.range (tLoc Zd p γ).f) :=
    Submodule.span_mono (Set.range_comp_subset_range _ _) (bcP_X Zd p γ (hu p) hx)
  have h2 := (ha p).2.2 _ (baseChange_mem_localLattice Zd hxa p) h1
  exact Submodule.span_le.2 (Set.range_subset_iff.2 fun a => (hb p).1 a) h2

theorem z_mem (γ : TermDef.Term D u u' F0 what₂) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Submodule.IsFullLattice D.host.E Λ) (h : ∀ p, (locH Zd p).Prim (lattice₂ D Zd.M p Λ) (tLoc Zd p γ).f) :
    F0.z ∈ Λ :=
  mem_of_bcP Zd hΛ fun p => by rw [← tf_last Zd p γ]; exact (h p).1 _

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.BwdNP
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPf
section
namespace Formalism.L2.SG.Pf.StabIntSh

theorem stabIntShape (D : Formalism.BasicNotions.D7) : StabIntShapeC D :=
  stabIntShape_of locShapeL locShapeG locGlob shapeNZ

end Formalism.L2.SG.Pf.StabIntSh
end

