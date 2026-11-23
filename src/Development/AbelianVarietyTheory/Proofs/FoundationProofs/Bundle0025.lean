module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBasisOnZetaPowMulQPow
section
noncomputable section
open Polynomial
namespace GlobalTheory.K5.OnFree

section General

variable {R : Type*} [CommRing R] (f : R[X]) (m : ℕ) (c : R)

abbrev relIdeal : Ideal R[X][X] := Ideal.span {C f, X ^ m - C (C c)}

abbrev topPoly : (AdjoinRoot f)[X] := X ^ m - C (algebraMap R (AdjoinRoot f) c)

def toAdj : (R[X][X] ⧸ relIdeal f m c) →ₐ[R] AdjoinRoot (topPoly f m c) :=
  Ideal.Quotient.liftₐ (relIdeal f m c)
    (Polynomial.eval₂AlgHom
      (Polynomial.aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
      (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) (by
      have h : relIdeal f m c ≤ RingHom.ker (Polynomial.eval₂AlgHom
          (Polynomial.aeval (R := R) (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)))
          (AdjoinRoot.root (topPoly f m c)) (fun _ => Commute.all _ _)) := by
        rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
        constructor
        · have h1 : aeval (AdjoinRoot.of (topPoly f m c) (AdjoinRoot.root f)) f = 0 := by
            rw [← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, AdjoinRoot.aeval_eq,
              AdjoinRoot.mk_self, map_zero]
          simpa [RingHom.mem_ker] using h1
        · have h2 := AdjoinRoot.eval₂_root (topPoly f m c)
          simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h2
          simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_pow]
          change eval₂ _ _ X ^ m - eval₂ _ _ (C (C c)) = 0
          rw [eval₂_X, eval₂_C, RingHom.coe_coe, aeval_C,
            IsScalarTower.algebraMap_apply R (AdjoinRoot f)]
          exact h2
      exact fun a ha => h ha)

def baseToQuot : AdjoinRoot f →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId R _) (Ideal.Quotient.mk (relIdeal f m c) (C X)) (by
    have h : (Ideal.Quotient.mkₐ R (relIdeal f m c)) (C f) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    have h2 : aeval ((Ideal.Quotient.mkₐ R (relIdeal f m c)) (CAlgHom (R := R) (X : R[X]))) f = 0 := by
      rw [aeval_algHom_apply, aeval_algHom_apply, aeval_X_left_apply]
      exact h
    exact h2)

def toQuot : AdjoinRoot (topPoly f m c) →ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AdjoinRoot.liftAlgHom (topPoly f m c) (baseToQuot f m c)
    (Ideal.Quotient.mk (relIdeal f m c) X) (by
    have h : (Ideal.Quotient.mk (relIdeal f m c)) (X ^ m - C (C c)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (by simp))
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, RingHom.coe_coe, AlgHom.commutes]
    rw [map_sub, map_pow] at h
    exact h)

theorem toQuot_root : toQuot f m c (AdjoinRoot.root _) = Ideal.Quotient.mk (relIdeal f m c) X := by
  simp [toQuot]

theorem toQuot_of_root : toQuot f m c (AdjoinRoot.of _ (AdjoinRoot.root f)) =
    Ideal.Quotient.mk (relIdeal f m c) (C X) := by
  have h : baseToQuot f m c (AdjoinRoot.root f) = Ideal.Quotient.mk (relIdeal f m c) (C X) :=
    AdjoinRoot.liftAlgHom_root _ _ _ _
  rw [← h]
  simp [toQuot]

theorem toAdj_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) X) = AdjoinRoot.root _ := by
  change eval₂ _ _ X = _
  rw [eval₂_X]

theorem toAdj_C_X : toAdj f m c (Ideal.Quotient.mk (relIdeal f m c) (C X)) =
    AdjoinRoot.of _ (AdjoinRoot.root f) := by
  change eval₂ _ _ (C X) = _
  rw [eval₂_C, RingHom.coe_coe, aeval_X]

def adjEquiv : AdjoinRoot (topPoly f m c) ≃ₐ[R] (R[X][X] ⧸ relIdeal f m c) :=
  AlgEquiv.ofAlgHom (toQuot f m c) (toAdj f m c)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      refine Polynomial.algHom_ext' ?_ ?_
      · refine Polynomial.algHom_ext ?_
        have := toQuot_of_root f m c
        rw [← toAdj_C_X] at this
        exact this
      · have := toQuot_root f m c
        rw [← toAdj_X] at this
        exact this)
    (by
      refine AdjoinRoot.algHom_ext' ?_ ?_
      · refine AdjoinRoot.algHom_ext ?_
        have := toAdj_C_X f m c
        rw [← toQuot_of_root] at this
        exact this
      · have := toAdj_X f m c
        rw [← toQuot_root] at this
        exact this)

theorem exists_basis [Nontrivial R] (hf : f.Monic) (d : ℕ) (hd : f.natDegree = d) (hd0 : 0 < d)
    (hm : m ≠ 0) :
    ∃ b : Module.Basis (Fin d × Fin m) R (R[X][X] ⧸ relIdeal f m c),
      ∀ i j, b (i, j) = (Ideal.Quotient.mk (relIdeal f m c) (C X)) ^ (i : ℕ) *
        (Ideal.Quotient.mk (relIdeal f m c) X) ^ (j : ℕ) := by
  let b₁ : Module.Basis (Fin d) R (AdjoinRoot f) :=
    (AdjoinRoot.powerBasis' hf).basis.reindex (finCongr hd)
  have hb₁ : ∀ i, b₁ i = AdjoinRoot.root f ^ (i : ℕ) := by
    intro i
    simp only [b₁, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  haveI : Nontrivial (AdjoinRoot f) := nontrivial_of_ne _ _ (b₁.ne_zero ⟨0, hd0⟩)
  have hg : (topPoly f m c).Monic := monic_X_pow_sub_C _ hm
  have hgd : (topPoly f m c).natDegree = m := natDegree_X_pow_sub_C _
  let b₂ : Module.Basis (Fin m) (AdjoinRoot f) (AdjoinRoot (topPoly f m c)) :=
    (AdjoinRoot.powerBasis' hg).basis.reindex (finCongr hgd)
  have hb₂ : ∀ j, b₂ j = AdjoinRoot.root (topPoly f m c) ^ (j : ℕ) := by
    intro j
    simp only [b₂, Module.Basis.reindex_apply, PowerBasis.coe_basis]
    rfl
  refine ⟨(b₁.smulTower b₂).map (adjEquiv f m c).toLinearEquiv, fun i j => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.smulTower_apply, hb₁, hb₂, Algebra.smul_def,
    AdjoinRoot.algebraMap_eq, ← toQuot_of_root, ← toQuot_root, ← map_pow (toQuot f m c),
    ← map_pow (toQuot f m c), ← map_mul, map_pow]
  rfl

end General

theorem on_free (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    ∃ b : Module.Basis (Fin (Nat.totient (p ^ n)) × Fin (p ^ n)) (O0 p) (On p n),
      ∀ i j, b (i, j) = xn p n ^ (i : ℕ) * yn p n ^ (j : ℕ) := by
  rcases subsingleton_or_nontrivial (O0 p) with h | h
  · haveI : Subsingleton (On p n) := Module.subsingleton (O0 p) _
    exact ⟨Module.Basis.ofRepr (LinearEquiv.ofSubsingleton _ _), fun _ _ => Subsingleton.elim _ _⟩
  · have hpos : 0 < p ^ n := pow_pos hp.out.pos n
    exact exists_basis (cyclotomic (p ^ n) (O0 p)) (p ^ n) (qO p) (cyclotomic.monic _ _) _
      (natDegree_cyclotomic _ _) (Nat.totient_pos.2 hpos) hpos.ne'

end GlobalTheory.K5.OnFree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualOddFrameCuspForms
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.OddFrame.DualFrame

theorem mdiff_det {n : ℕ} {M : ℍ → Matrix (Fin n) (Fin n) ℂ} (hM : ∀ a b, MDiff fun τ => M τ a b) :
    MDiff fun τ => (M τ).det := by
  have : (fun τ => (M τ).det) =
      ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) • ∏ a, (fun τ => M τ (σ a) a) := by
    ext τ; simp [Matrix.det_apply', Finset.sum_apply, Finset.prod_apply]
  rw [this]
  exact MDifferentiable.sum fun σ _ => (MDifferentiable.prod fun a _ => hM _ _).const_smul _

variable {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ)

def dualEntry (i j : Fin r) : ℍ → ℂ := fun τ => ModularForm.discriminant τ * (evM s w F τ)⁻¹ j i

variable {s w F}

theorem evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ}
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (i k : Fin r) :
    evM s w F (y • τ) i k = c i * evM s w F τ (π i) k * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  simp only [evM, Matrix.of_apply]
  calc (F k ∣[w k] s i) (y • τ)
      = (F k ∣[w k] s i) (y • τ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w k) * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [mul_assoc, ← zpow_add₀ hJ]; simp
    _ = c i * (F k ∣[w k] s (π i)) τ * denom (y : GL (Fin 2) ℝ) τ ^ w k := by
        rw [← slash_mul_apply, hc]; simp [smul_eq_mul]

theorem inv_evM_smul {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (τ : ℍ) (hA : (evM s w F τ).det ≠ 0)
    (i j : Fin r) :
    (evM s w F (y • τ))⁻¹ j i = denom (y : GL (Fin 2) ℝ) τ ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i) := by
  set J := denom (y : GL (Fin 2) ℝ) τ with hJdef
  have hJ : J ≠ 0 := denom_ne_zero _ _
  have key : (Matrix.of fun j i => J ^ (-w j) * c i * (evM s w F τ)⁻¹ j (π i)) * evM s w F (y • τ) = 1 := by
    ext j k
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, evM_smul hc, ← hJdef]
    have h1 : ∀ l, J ^ (-w j) * c l * (evM s w F τ)⁻¹ j (π l) * (c l * evM s w F τ (π l) k * J ^ w k)
        = (J ^ (-w j) * J ^ w k) * ((evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k) := by
      intro l
      linear_combination (J ^ (-w j) * (evM s w F τ)⁻¹ j (π l) * evM s w F τ (π l) k * J ^ w k) * hcc l
    rw [Finset.sum_congr rfl fun l _ => h1 l, ← Finset.mul_sum, Equiv.sum_comp π (fun l => (evM s w F τ)⁻¹ j l * evM s w F τ l k), ← Matrix.mul_apply,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)]
    rcases eq_or_ne j k with rfl | hjk
    · rw [← zpow_add₀ hJ]; simp
    · simp [Matrix.one_apply_ne hjk]
  rw [Matrix.inv_eq_left_inv key]; rfl

theorem discriminant_smul (y : SL(2, ℤ)) (τ : ℍ) :
    ModularForm.discriminant (y • τ) = ModularForm.discriminant τ * denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) := by
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  have h := congrFun (SlashInvariantForm.slash_action_generators_SL2Z ModularForm.discriminant_S_invariant
    ModularForm.discriminant_T_invariant y) τ
  rw [ModularForm.SL_slash_apply] at h
  rw [← h, mul_assoc, ← zpow_add₀ hJ]; simp

theorem dualEntry_slash {y : SL(2, ℤ)} {π : Equiv.Perm (Fin r)} {c : Fin r → ℂ} (hcc : ∀ i, c i * c i = 1)
    (hc : ∀ i j, F j ∣[w j] (s i * y) = c i • F j ∣[w j] s (π i)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (i j : Fin r) : dualEntry s w F i j ∣[12 - w j] y = c i • dualEntry s w F (π i) j := by
  ext τ
  have hJ : denom (y : GL (Fin 2) ℝ) τ ≠ 0 := denom_ne_zero _ _
  rw [ModularForm.SL_slash_apply]
  simp only [dualEntry, Pi.smul_apply, smul_eq_mul, discriminant_smul, inv_evM_smul hcc hc τ (hA τ)]
  have hJJ : denom (y : GL (Fin 2) ℝ) τ ^ (12 : ℤ) * denom (y : GL (Fin 2) ℝ) τ ^ (-w j) *
      denom (y : GL (Fin 2) ℝ) τ ^ (-(12 - w j)) = 1 := by
    rw [← zpow_add₀ hJ, ← zpow_add₀ hJ, show (12 : ℤ) + -w j + -(12 - w j) = 0 by ring, zpow_zero]
  linear_combination (c i * ModularForm.discriminant τ * (evM s w F τ)⁻¹ j (π i)) * hJJ

theorem dualEntry_slash_of_eq {Γ : Subgroup SL(2, ℤ)} (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    {y γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {i i' : Fin r} (hy : s i * y = γ * s i') (j : Fin r) :
    dualEntry s w F i j ∣[12 - w j] y = dualEntry s w F i' j := by
  classical
  obtain ⟨π, hπ⟩ := hs.exists_perm y
  choose g hg hdec using hπ
  let c : Fin r → ℂ := fun l => if s l * y = g l * s (π l) then 1 else -1
  have hcc : ∀ l, c l * c l = 1 := by
    intro l; simp only [c]; split_ifs <;> norm_num
  have hc : ∀ l j, F j ∣[w j] (s l * y) = c l • F j ∣[w j] s (π l) := by
    intro l j
    by_cases hp : s l * y = g l * s (π l)
    · simp only [c, if_pos hp]
      rw [hp, (hF j).2.slash_mul (hg l), one_smul]
    · simp only [c, if_neg hp]
      rw [(hdec l).resolve_left hp, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul (hg l), neg_one_smul]
  have hπi : π i = i' := by
    apply hs.2 (π i) i' ((g i)⁻¹ * γ) (Γ.mul_mem (Γ.inv_mem (hg i)) hγ)
    rcases hdec i with h | h
    · left; rw [mul_assoc, ← hy, h, inv_mul_cancel_left]
    · right; rw [mul_assoc, ← hy, h, mul_neg, neg_neg, inv_mul_cancel_left]
  have hp : s i * y = g i * s (π i) := by
    by_contra hp
    have h := (hdec i).resolve_left hp
    rw [hy, hπi, ← neg_mul] at h
    have h2 : γ = -g i := mul_right_cancel h
    apply hΓ
    have h3 : (-1 : SL(2, ℤ)) = γ * (g i)⁻¹ := by rw [h2, neg_mul, mul_inv_cancel]
    rw [h3]
    exact Γ.mul_mem hγ (Γ.inv_mem (hg i))
  rw [dualEntry_slash hcc hc hA, hπi]
  simp only [c, if_pos hp, one_smul]

theorem mdiff_dualEntry (hF : ∀ j, MDiff (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0) (i j : Fin r) :
    MDiff (dualEntry s w F i j) := by
  have e : dualEntry s w F i j = ModularForm.discriminant * ((fun τ => (evM s w F τ).det)⁻¹ *
      fun τ => ((evM s w F τ).updateRow i (Pi.single j 1)).det) := by
    ext τ
    simp [dualEntry, Matrix.inv_def, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine CuspForm.discriminant.holo'.mul (((mdiff_det_evM s w hF).inv hA).mul (mdiff_det fun a b => ?_))
  by_cases h : a = i
  · simp only [Matrix.updateRow_apply, if_pos h]
    exact mdifferentiable_const
  · simp only [Matrix.updateRow_apply, if_neg h]
    exact mdiff_slash (hF b) _ _

theorem exists_dual_cuspForms (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ)
    (F : Fin r → ℍ → ℂ) (hΓ : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) (hA : ∀ τ, (evM s w F τ).det ≠ 0)
    (hT : Tendsto (fun τ => ModularForm.discriminant τ • (evM s w F τ)⁻¹) atImInfty (𝓝 0)) :
    ∃ G : Fin r → ℍ → ℂ, (∀ j, IsCF Γ (12 - w j) (G j)) ∧
      ∀ τ, (evM s (fun j => 12 - w j) G τ).det ≠ 0 := by
  let G : Fin r → ℍ → ℂ := fun j => dualEntry s w F j j ∣[12 - w j] (s j)⁻¹
  have hodd : ∀ j, Odd (12 - w j) := fun j => by
    obtain ⟨k, hk⟩ := (hF j).1
    exact ⟨5 - k, by omega⟩
  have hpos : ∀ j i, ∀ γ ∈ Γ, G j ∣[12 - w j] (γ * s i) = dualEntry s w F i j := by
    intro j i γ hγ
    simp only [G]
    rw [← SlashAction.slash_mul]
    exact dualEntry_slash_of_eq hΓ hs hF hA hγ (mul_inv_cancel_left _ _) j
  have hzero : ∀ i j, IsZeroAtImInfty (dualEntry s w F i j) := fun i j =>
    tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hT j) i
  refine ⟨G, fun j => ⟨fun γ hγ => ?_, mdiff_slash (mdiff_dualEntry (fun j => (hF j).2.2.1) hA j j) _ _,
    fun x => ?_⟩, fun τ => ?_⟩
  · obtain ⟨i, g, hg, h | h⟩ := hs.1 1
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (γ * g * s i) := by rw [mul_assoc, ← h, mul_one]
        _ = G j ∣[12 - w j] (g * s i) := by rw [hpos j i _ (Γ.mul_mem hγ hg), hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
    · calc G j ∣[12 - w j] γ = G j ∣[12 - w j] (-(γ * g * s i)) := by
            rw [mul_assoc, ← mul_neg, ← h, mul_one]
        _ = G j ∣[12 - w j] (-(g * s i)) := by
            rw [slash_neg_of_odd (hodd j), slash_neg_of_odd (hodd j), hpos j i _ (Γ.mul_mem hγ hg),
              hpos j i g hg]
        _ = G j := by rw [← h, SlashAction.slash_one]
  · obtain ⟨i, g, hg, rfl | rfl⟩ := hs.1 x
    · rw [hpos j i g hg]; exact hzero i j
    · rw [slash_neg_of_odd (hodd j), hpos j i g hg]; exact (hzero i j).neg
  · have e : evM s (fun j => 12 - w j) G τ = (ModularForm.discriminant τ • (evM s w F τ)⁻¹).transpose := by
      ext i j
      have h := hpos j i 1 Γ.one_mem
      rw [one_mul] at h
      change (G j ∣[12 - w j] s i) τ = _
      rw [h]; rfl
    rw [e, Matrix.det_transpose, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero (pow_ne_zero _ (ModularForm.discriminant_ne_zero τ)) (inv_ne_zero (hA τ))

end GlobalTheory.OddFrame.DualFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGamma
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.EisSep

open EisensteinSeries Complex

def pt (n : ℕ) : ℍ := UpperHalfPlane.mk (((n : ℂ) + 1) * Complex.I) (by simp; positivity)

theorem coe_pt (n : ℕ) : ((pt n : ℍ) : ℂ) = ((n : ℂ) + 1) * Complex.I := rfl

def lim0 (v : Fin 2 → ℤ) : ℂ := if v 0 = 0 then (v 1 : ℂ) ^ (-3 : ℤ) else 0

theorem re_im_summand (v : Fin 2 → ℤ) (n : ℕ) :
    ((v 0 : ℂ) * (pt n : ℂ) + v 1).re = v 1 ∧ ((v 0 : ℂ) * (pt n : ℂ) + v 1).im = v 0 * ((n : ℝ) + 1) := by
  rw [coe_pt]; constructor <;> simp

theorem norm_le (v : Fin 2 → ℤ) (n : ℕ) : ‖eisSummand 3 v (pt n)‖ ≤ ‖v‖ ^ (-(3 : ℝ)) := by
  obtain ⟨hre, him⟩ := re_im_summand v n
  set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1 with hw
  have hvw : ‖v‖ ≤ ‖w‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    fin_cases i
    · have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul] at h1
      have h2 : |(v 0 : ℝ)| ≤ |(v 0 : ℝ)| * |(n : ℝ) + 1| := by
        have : (1 : ℝ) ≤ |(n : ℝ) + 1| := by rw [abs_of_pos (by positivity)]; simp
        nlinarith [abs_nonneg (v 0 : ℝ)]
      simp only [Int.norm_eq_abs]
      simpa using h2.trans h1
    · have h1 := Complex.abs_re_le_norm w
      rw [hre] at h1
      simpa [Int.norm_eq_abs] using h1
  have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
  rw [he, norm_zpow, Real.rpow_neg (norm_nonneg _), zpow_neg]
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · have : v = 0 := norm_eq_zero.1 h0.symm
    have hw0 : w = 0 := by simp [hw, this]
    simp [hw0]
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, zpow_ofNat]
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le hvw _)

theorem tendsto_term (v : Fin 2 → ℤ) : Tendsto (fun n => eisSummand 3 v (pt n)) atTop (𝓝 (lim0 v)) := by
  by_cases h : v 0 = 0
  · have : ∀ n, eisSummand 3 v (pt n) = (v 1 : ℂ) ^ (-3 : ℤ) := fun n => by simp [eisSummand, h]
    simp only [this, lim0, h, if_true]
    exact tendsto_const_nhds
  · simp only [lim0, h, if_false]
    refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨_, him⟩ := re_im_summand v n
    set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
    have hw : (n : ℝ) + 1 ≤ ‖w‖ := by
      have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h1
      have : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h
      nlinarith
    have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
    rw [he, norm_zpow, zpow_neg, one_div]
    have hw1 : (1 : ℝ) ≤ ‖w‖ := hn.trans hw
    have : ‖w‖ ≤ ‖w‖ ^ (3 : ℤ) := by
      rw [zpow_ofNat]; nlinarith [mul_le_mul hw1 hw1 zero_le_one (by linarith)]
    exact inv_anti₀ (by positivity) (hw.trans this)

theorem tendsto_eis {M : ℕ} (c : Fin 2 → ZMod M) :
    Tendsto (fun n => eisensteinSeries c 3 (pt n)) atTop (𝓝 (∑' v : gammaSet M 1 c, lim0 v)) :=
  tendsto_tsum_of_dominated_convergence (bound := fun v : gammaSet M 1 c => ‖v.1‖ ^ (-(3 : ℝ)))
    ((summable_one_div_norm_rpow (by norm_num)).subtype _) (fun v => tendsto_term v.1)
    (Eventually.of_forall fun n v => norm_le v.1 n)

theorem eq_of_zero {M : ℕ} {c : Fin 2 → ZMod M} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet M 1 c) (h0 : v 0 = 0) :
    v = ![0, 1] ∨ v = ![0, -1] := by
  have h := hv.2
  rw [h0, Int.gcd_zero_left, Int.natAbs_eq_iff] at h
  rcases h with h | h
  · left; ext i; fin_cases i <;> simp [h0, h]
  · right; ext i; fin_cases i <;> simp [h0, h]

theorem cast_zero_one (M : ℕ) : ((↑) : ℤ → ZMod M) ∘ (![0, 1] : Fin 2 → ℤ) = ![0, 1] := by
  ext i; fin_cases i <;> simp

theorem lim_one {M : ℕ} (hM : 3 ≤ M) : ∑' v : gammaSet M 1 (![0, 1] : Fin 2 → ZMod M), lim0 v = 1 := by
  haveI : Fact (2 < M) := ⟨by omega⟩
  have hm : (![0, 1] : Fin 2 → ℤ) ∈ gammaSet M 1 (![0, 1] : Fin 2 → ZMod M) := ⟨cast_zero_one M, by simp⟩
  rw [tsum_eq_single ⟨_, hm⟩]
  · simp [lim0]
  · intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hv (Subtype.ext h)
    · have h1 := congrFun v.2.1 1
      rw [h] at h1
      exact ZMod.neg_one_ne_one (n := M) (by simpa using h1)

theorem lim_ne {M : ℕ} {c : Fin 2 → ZMod M} (hc : c ≠ ![0, 1]) : ∑' v : gammaSet M 1 c, lim0 v ≠ 1 := by
  have key : ∀ v : gammaSet M 1 c, v.1 ≠ ![0, -1] → lim0 v = 0 := by
    intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hc (by rw [← v.2.1, h, cast_zero_one])
    · exact hv h
  by_cases hm : (![0, -1] : Fin 2 → ℤ) ∈ gammaSet M 1 c
  · rw [tsum_eq_single ⟨_, hm⟩ fun v hv => key v fun h => hv (Subtype.ext h)]
    simp only [lim0]
    norm_num
  · rw [tsum_congr fun v => key v fun h => hm (h ▸ v.2)]
    simp

theorem eq_of_eis_eq {M : ℕ} (hM : 3 ≤ M) {c : Fin 2 → ZMod M}
    (h : eisensteinSeries c 3 = eisensteinSeries (![0, 1] : Fin 2 → ZMod M) 3) : c = ![0, 1] := by
  by_contra hc
  have h1 := tendsto_eis c
  rw [h] at h1
  exact lim_ne hc ((tendsto_nhds_unique h1 (tendsto_eis _)).trans (lim_one hM))

theorem exists_isMF_slash_ne : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M →
    ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  intro M hM x hx
  haveI : NeZero M := ⟨by omega⟩
  have hMF : ∀ a : Fin 2 → ZMod M, IsMF (CongruenceSubgroup.Gamma M) 3 (eisensteinSeries a 3) := fun a =>
    isMF_coe (ModularForm.eisensteinSeriesMF le_rfl a)
  rw [CongruenceSubgroup.Gamma_mem] at hx
  by_cases hrow : ((x 1 0 : ℤ) : ZMod M) = 0 ∧ ((x 1 1 : ℤ) : ZMod M) = 1
  · refine ⟨3, _, hMF ![-1, 0], fun h => ?_⟩
    have h2 := congrArg (fun f => f ∣[(3 : ℤ)] ModularGroup.S) h
    simp only [eisensteinSeries_slash_apply] at h2
    have hS0 : ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = !![0, -1; 1, 0] := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_S]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hS : Matrix.vecMul (![-1, 0] : Fin 2 → ZMod M) ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = ![0, 1] := by
      rw [hS0]; ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [hS, hS0] at h2
    have h3 := eq_of_eis_eq hM h2
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hx ⟨h31, h30, hrow⟩
  · refine ⟨3, _, hMF ![0, 1], fun h => ?_⟩
    rw [eisensteinSeries_slash_apply] at h
    have h3 := eq_of_eis_eq hM h
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hrow ⟨h30, h31⟩

end GlobalTheory.EisSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevFiniteIndex
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem lev_finiteIndex : ∀ (N l : ℕ), 0 < N → 0 < l → (GlobalTheory.Hk.lev N l).FiniteIndex := by
  intro N l hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

end GlobalTheory.Hk
end

