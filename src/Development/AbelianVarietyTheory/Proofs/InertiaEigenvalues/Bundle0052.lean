module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0006
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallEqDominantIndex
section
open Polynomial
open Classical

namespace GlobalTheory

theorem dominantIndex_prod_X_sub_C (K : Type) [NormedField K] [IsUltrametricDist K]
    (ρ : ℝ) (hρ : 0 < ρ) (s : Multiset K) :
    ∀ c : K, c ≠ 0 →
      (∀ j, ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j ≤
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ)) ∧
      ∀ j, Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) < j →
        ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j <
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro c hc
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.filter_zero,
      Multiset.card_zero, pow_zero, coeff_C_zero]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp
      · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp h)]; simp
    · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp hj)]; simp [hc]
  | cons a s ih =>
    intro c hc
    obtain ⟨h1, h2⟩ := ih c hc
    have heq : C c * ((a ::ₘ s).map fun a => X - C a).prod =
        (X - C a) * (C c * (s.map fun a => X - C a).prod) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm]
    rw [heq, Multiset.filter_cons]
    by_cases ha : ‖a‖ ≤ ρ
    · rw [if_pos ha, Multiset.singleton_add, Multiset.card_cons]
      exact _root_.GlobalTheory.newton_step_root_in_disc K _ a ρ _ hρ ha h1 h2
    · rw [if_neg ha, zero_add]
      exact _root_.GlobalTheory.newton_step_root_outside_disc K _ a ρ _ hρ (not_le.mp ha) h1 h2

theorem card_roots_closedBall_eq_dominantIndex :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  intro K _ _ _ f ρ hρ hf
  have key := dominantIndex_prod_X_sub_C K ρ hρ f.roots f.leadingCoeff
    (leadingCoeff_ne_zero.mpr hf)
  rw [C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMonoidAlgebraLiftEqOfCharpolyEq
section
open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
open Polynomial in
private lemma det_generic_sum_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (g : Fin m → G) :
    (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (ρ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det =
      (∑ i, (MvPolynomial.X i : MvPolynomial (Fin m) k) • (σ (g i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin m) k)).det := by
  ext d
  let T : Subalgebra k (Bool → k) :=
    AlgHom.equalizer (Pi.evalAlgHom k (fun _ : Bool => k) true) (Pi.evalAlgHom k (fun _ : Bool => k) false)
  have key := _root_.GlobalTheory.coeff_det_generic_sum_mem_of_charpoly_coeff_mem T n
    (fun b => if b then ρ else σ) (by intro g j; simp [T, AlgHom.mem_equalizer, h]) m g d
  simpa [T, AlgHom.mem_equalizer] using key

open scoped BigOperators in
open Polynomial in
private lemma charpoly_sum_smul_eq_of_charpoly_eq {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k) (h : ∀ g, (ρ g).charpoly = (σ g).charpoly)
    (m : ℕ) (c : Fin m → k) (g : Fin m → G) :
    (∑ i, c i • ρ (g i)).charpoly = (∑ i, c i • σ (g i)).charpoly := by
  have hd := det_generic_sum_eq_of_charpoly_eq n ρ σ h (m + 1) (Fin.cons 1 g)
  have key : ∀ τ : G →* Matrix (Fin n) (Fin n) k, (∑ i, c i • τ (g i)).charpoly =
      MvPolynomial.aeval (Fin.cons (X : k[X]) (fun i => -C (c i)) : Fin (m + 1) → k[X])
        (∑ i, (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) k) •
          (τ ((Fin.cons 1 g : Fin (m + 1) → G) i)).map (MvPolynomial.C : k →+* MvPolynomial (Fin (m + 1)) k)).det := by
    intro τ
    rw [AlgHom.map_det]
    unfold Matrix.charpoly
    congr 1
    ext i j
    simp [Fin.sum_univ_succ, Matrix.charmatrix_apply, Matrix.sum_apply, Matrix.one_apply,
      Matrix.diagonal_apply]
    split_ifs <;> simp [sub_eq_add_neg]
  rw [key ρ, key σ, hd]

open scoped BigOperators in
open Polynomial in
theorem _root_.GlobalTheory.charpoly_lift_eq_of_charpoly_eq : ∀ {k G : Type} [Field k] [Monoid G] (n : ℕ)
    (ρ σ : G →* Matrix (Fin n) (Fin n) k), (∀ g, (ρ g).charpoly = (σ g).charpoly) →
    ∀ a : MonoidAlgebra k G,
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G ρ a).charpoly =
      (MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G σ a).charpoly := by
  intro k G _ _ n ρ σ h a
  have hsum : ∀ τ : G →* Matrix (Fin n) (Fin n) k,
      MonoidAlgebra.lift k (Matrix (Fin n) (Fin n) k) G τ a =
        ∑ i, a.coeff (a.coeff.support.equivFin.symm i) • τ (a.coeff.support.equivFin.symm i) := by
    intro τ
    rw [MonoidAlgebra.lift_apply, Finsupp.sum, ← Finset.sum_coe_sort a.coeff.support]
    exact (Equiv.sum_comp a.coeff.support.equivFin.symm (fun x : a.coeff.support => a.coeff x • τ x)).symm
  rw [hsum ρ, hsum σ]
  exact charpoly_sum_smul_eq_of_charpoly_eq n ρ σ h _ _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleEqAddUniformizerSmulAddCoboundary
section
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem cocycle_lift_mod_uniformizer
    {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G]
    (ρ : Representation O G M) (hρ : ContAction ρ) (ϖ : O)
    (hemb : Topology.IsEmbedding (fun m : M => ϖ • m)) (s : Finset (Z1 ρ))
    (hs : ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈
      LinearMap.range (LinearMap.lsmul O M ϖ))
    (c : Z1 ρ) : ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M),
      (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  classical
  obtain ⟨i, his, x, hx⟩ := hs c
  let d : Z1 ρ := ⟨d0 ρ x, coboundaries_le_cocycles ρ hρ ⟨x, rfl⟩⟩
  let E : Z1 ρ := c - i - d
  have hE : ∀ g, (E : G → M) g = (c : G → M) g - (i : G → M) g - (ρ g x - x) := fun g => rfl
  have hx' : ∀ g, ∃ y : M, ϖ • y = (E : G → M) g := by
    intro g
    obtain ⟨y, hy⟩ := hx g
    exact ⟨y, by rw [hE]; simpa using hy⟩
  choose f hf using hx'
  have hfE : (fun g => ϖ • f g) = (E : G → M) := funext hf
  have hfc : Continuous f := by
    rw [hemb.continuous_iff]
    change Continuous (fun g => ϖ • f g)
    rw [hfE]
    exact E.2.1
  have hfco : ∀ g h, f (g * h) = f g + ρ g (f h) := by
    intro g h
    apply hemb.injective
    change ϖ • f (g * h) = ϖ • (f g + ρ g (f h))
    rw [smul_add, ← map_smul, hf, hf, hf]
    exact E.2.2 g h
  refine ⟨fun j => if j = i then 1 else 0, ⟨f, hfc, hfco⟩, x, ?_⟩
  have hsum : ∑ j ∈ s, (if j = i then (1 : O) else 0) • (j : G → M) = (i : G → M) := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' s i (fun j => (j : G → M))]
    simp [his]
  rw [hsum]
  funext g
  have := hf g
  rw [hE] at this
  simp only [Pi.add_apply, Pi.smul_apply, amitsur_d0_apply]
  rw [this]
  abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompanionMatrixOfCoeffsPowMulVecFirstBasisVector
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

section Alg
variable {k : Type} [CommRing k] {r : ℕ}

def e1 : Fin r → k := fun i => if (i : ℕ) = 0 then 1 else 0

theorem companionMatrixOfCoeffs_pow_mulVec_firstBasisVector (p : Fin r → k) : ∀ (j : ℕ) (hj : j < r),
    (companion p ^ j) *ᵥ e1 = Pi.single (⟨j, hj⟩ : Fin r) 1
  | 0, hj => by
    ext i; simp [e1, Pi.single_apply, Fin.ext_iff]
  | j + 1, hj => by
    rw [pow_succ', ← mulVec_mulVec, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector p j (by omega), Matrix.mulVec_single_one]
    funext i
    have hj' : j + 1 ≠ r := Nat.ne_of_lt hj
    simp [Matrix.col_apply, companion, Pi.single_apply, Fin.ext_iff, hj']

theorem mom_sec_add (a : Inv r k) (n : ℕ) (j : Fin r) :
    mom (sec a) (n + j) = (a.2.1 ᵥ* (companion a.1 ^ n)) j := by
  have h1 : mom (sec a) (n + j) = a.2.1 ⬝ᵥ ((companion a.1 ^ n) *ᵥ ((companion a.1 ^ (j : ℕ)) *ᵥ e1)) := by
    simp only [mom, sec, pow_add, ← mulVec_mulVec]; rfl
  rw [h1, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector a.1 j j.2, dotProduct_mulVec, dotProduct_single_one]

theorem hankel_apply' (a : Inv r k) (i j : Fin r) : hankel a i j = (a.2.1 ᵥ* (companion a.1 ^ (i : ℕ))) j :=
  mom_sec_add a i j

theorem hankel_isSymm (a : Inv r k) : (hankel a).IsSymm := by
  ext i j; simp [hankel, add_comm]

def hankelShift (a : Inv r k) : Matrix (Fin r) (Fin r) k := Matrix.of fun i j => mom (sec a) ((i : ℕ) + (j : ℕ) + 1)

theorem hankelShift_isSymm (a : Inv r k) : (hankelShift a).IsSymm := by
  ext i j; simp [hankelShift]; ring_nf

theorem hankel_mul_companion (a : Inv r k) : hankel a * companion a.1 = hankelShift a := by
  ext i j
  have h2 : hankelShift a i j = mom (sec a) (((i : ℕ) + 1) + j) := by simp [hankelShift]; ring_nf
  rw [h2, mom_sec_add, Matrix.mul_apply, pow_succ, ← Matrix.vecMul_vecMul]
  simp only [Matrix.vecMul, dotProduct, hankel_apply']

theorem companion_map {k' : Type} [CommRing k'] (φ : k →+* k') (p : Fin r → k) :
    (companion p).map φ = companion (fun i => φ (p i)) := by
  ext i j; simp only [companion, Matrix.map_apply, Matrix.of_apply]; split_ifs <;> simp

end Alg

section Herm
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem map_isSelfAdjoint {N : Matrix (Fin r) (Fin r) F} (hN : N.IsSymm) :
    IsSelfAdjoint (N.map (algebraMap F E)) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose]
  ext i j
  simp [Matrix.conjTranspose_apply, Unram.star_fix, hN.apply i j]

theorem conjTranspose_map (N : Matrix (Fin r) (Fin r) F) :
    (N.map (algebraMap F E))ᴴ = Nᵀ.map (algebraMap F E) := by
  ext i j; simp [Matrix.conjTranspose_apply, Unram.star_fix]

def mkX (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : Hn r F E :=
  (⟨star h⁻¹ * (hankelShift a).map (algebraMap F E) * h⁻¹, by
      have h1 := (map_isSelfAdjoint (E := E) (hankelShift_isSymm a)).conjugate (star h⁻¹)
      rw [star_star] at h1
      exact h1⟩, h *ᵥ e1, a.2.2)

theorem mkX_snd_fst (a : Inv r F) (h : Matrix (Fin r) (Fin r) E) : (mkX a h).2.1 = h *ᵥ e1 := rfl

variable {a : Inv r F} {h : Matrix (Fin r) (Fin r) E}

theorem mkX_fst (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    (mkX a h).1.1 = h * (companion a.1).map (algebraMap F E) * h⁻¹ := by
  have hd' : IsUnit hᴴ.det := by rw [Matrix.det_conjTranspose]; exact hd.star
  simp only [mkX]
  rw [← hankel_mul_companion, Matrix.map_mul, ← hh, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_nonsing_inv,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd', Matrix.one_mul]

theorem pow_mulVec_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    ((mkX a h).1.1 ^ (j : ℕ)) *ᵥ (h *ᵥ e1) = h *ᵥ Pi.single j 1 := by
  rw [mkX_fst hh hd]
  have key : ∀ n : ℕ, (h * (companion a.1).map (algebraMap F E) * h⁻¹) ^ n =
      h * ((companion a.1).map (algebraMap F E)) ^ n * h⁻¹ := by
    intro n; induction n with
    | zero => simp [Matrix.mul_nonsing_inv _ hd]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [key, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, ← Matrix.mulVec_mulVec,
    companion_map, companionMatrixOfCoeffs_pow_mulVec_firstBasisVector _ j j.2]

theorem bm_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) :
    Bm (mkX a h).toGl = h := by
  ext i j
  simp only [Bm, Hn.toGl, Matrix.of_apply]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.mulVec_single_one]; rfl

theorem mom_mkX (hh : hᴴ * h = (hankel a).map (algebraMap F E)) (hd : IsUnit h.det) (j : Fin r) :
    mom (mkX a h).toGl j = algebraMap F E (a.2.1 j) := by
  have h0 : 0 < r := j.pos
  simp only [mom, Hn.toGl]
  rw [mkX_snd_fst, pow_mulVec_mkX hh hd, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hh]
  have he : star (e1 : Fin r → E) = Pi.single (⟨0, h0⟩ : Fin r) 1 := by
    ext i; by_cases hi : (i : ℕ) = 0 <;> simp [e1, hi, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one, single_one_dotProduct]
  simp only [Matrix.col_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hankel_apply']
  simp
end Herm

section Top
variable {k : Type} [CommRing k] [TopologicalSpace k] [IsTopologicalRing k] {r : ℕ}

theorem continuous_companion : Continuous (fun p : Fin r → k => companion p) :=
  continuous_matrix fun i j => by
    simp only [companion, Matrix.of_apply]
    split_ifs
    · exact (continuous_apply i).neg
    · exact continuous_const
    · exact continuous_const

theorem continuous_mom_sec (n : ℕ) : Continuous (fun a : Inv r k => mom (sec a) n) := by
  simp only [mom, sec]
  exact (continuous_fst.comp continuous_snd).dotProduct
    (((continuous_companion.comp continuous_fst).pow n).matrix_mulVec continuous_const)

theorem continuous_hankel : Continuous (fun a : Inv r k => hankel a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_hankelShift : Continuous (fun a : Inv r k => hankelShift a) :=
  continuous_matrix fun _ _ => continuous_mom_sec _

theorem continuous_delta : Continuous (fun a : Inv r k => Delta a) :=
  continuous_hankel.matrix_det

end Top

section Unit
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}


omit [Unram F E] in
theorem continuousStar (F : Type) [NontriviallyNormedField F] [NormedAlgebra F E] [Unram F E] : ContinuousStar E :=
  ⟨(Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← star_sub, Unram.norm_star (F := F)]).continuous⟩

theorem bm_actU (g : Matrix.unitaryGroup (Fin r) E) (X : Hn r F E) : Bm (actU g X).toGl = g.1 * Bm X.toGl := by
  have hg : star g.1 * g.1 = 1 := (Matrix.mem_unitaryGroup_iff').1 g.2
  have key : ∀ n : ℕ, (g.1 * X.1.1 * star g.1) ^ n * g.1 = g.1 * X.1.1 ^ n := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, ← Matrix.mul_assoc, Matrix.mul_assoc _ (star g.1), hg, Matrix.mul_one,
        Matrix.mul_assoc, ← pow_succ']
  ext i j
  simp only [Bm, Hn.toGl, actU, Matrix.of_apply]
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec]
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

end Unit

end GlobalTheory.JR.ImgSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceSubgroupsGLPadic
section
namespace GlobalTheory

theorem norm_mul_sub_one_le_of_norm_sub_one_le {E : Type} [NormedField E] [IsUltrametricDist E]
    {n : Type} [Fintype n] [DecidableEq n] (X Y : Matrix n n E) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ t) (hY : ∀ i j, ‖(Y - 1) i j‖ ≤ t) :
    ∀ i j, ‖(X * Y - 1) i j‖ ≤ t := by
  intro i j
  have hXY : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]; abel
  have hp := _root_.GlobalTheory.matrix_mul_entry_norm_le_ultrametric E n (X - 1) (Y - 1) t t h0 h0 hX hY i j
  have htt : t * t ≤ t := by nlinarith
  rw [hXY, Matrix.add_apply, Matrix.add_apply]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp.trans htt))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hX i j) (hY i j))

theorem congruenceSubgroups_GL_padic : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n],
    ∃ Γ : ℕ → Subgroup (GL n ℚ_[l]), ∀ k X, X ∈ Γ k ↔
      ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l _ n _ _
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have ht : ∀ k : ℕ, 0 ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) ∧ (l : ℝ) ^ (-((k : ℤ) + 2)) < 1 := by
    intro k
    refine ⟨zpow_nonneg (by linarith) _, zpow_lt_one_of_neg₀ hl (by omega)⟩
  refine ⟨fun k => {
    carrier := {X | ∀ i j, ‖((X : Matrix n n ℚ_[l]) - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2))}
    one_mem' := by
      intro i j
      simpa using (ht k).1
    mul_mem' := by
      intro X Y hX hY
      simp only [Set.mem_setOf_eq, Units.val_mul] at *
      exact norm_mul_sub_one_le_of_norm_sub_one_le _ _ _ (ht k).1 (ht k).2.le hX hY
    inv_mem' := by
      intro X hX
      simp only [Set.mem_setOf_eq] at *
      exact _root_.GlobalTheory.matrix_inv_near_one ℚ_[l] n (X : Matrix n n ℚ_[l]) ((X⁻¹ : GL n ℚ_[l]) : Matrix n n ℚ_[l]) _
        (ht k).1 (ht k).2 (Units.inv_mul X) hX }, fun k X => Iff.rfl⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjTransposeVecMulVecSelf
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitWitt

variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem vecMulVec_mulVec_eq (w v z : Fin r → E) : vecMulVec w v *ᵥ z = (v ⬝ᵥ z) • w := by
  ext i
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem conjTranspose_vecMulVec_self (w : Fin r → E) : (vecMulVec w (star w))ᴴ = vecMulVec w (star w) := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]

theorem vecMulVec_self_mul (w : Fin r → E) :
    vecMulVec w (star w) * vecMulVec w (star w) = (star w ⬝ᵥ w) • vecMulVec w (star w) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem refl_mem (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) :
    (1 - a⁻¹ • vecMulVec w (star w)) ∈ unitaryGroup (Fin r) E := by
  rw [mem_unitaryGroup_iff']
  have hs : star (1 - a⁻¹ • vecMulVec w (star w)) = 1 - (star a)⁻¹ • vecMulVec w (star w) := by
    rw [star_sub, star_one, star_smul, star_inv₀]
    congr 2
    exact conjTranspose_vecMulVec_self w
  have ha' : star a ≠ 0 := by simpa using ha
  rw [hs]
  have key : (star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w) = 0 := by
    rw [hN]; field_simp; ring
  calc (1 - (star a)⁻¹ • vecMulVec w (star w)) * (1 - a⁻¹ • vecMulVec w (star w))
      = 1 - ((star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w)) • vecMulVec w (star w) := by
        rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, vecMulVec_self_mul,
          smul_smul, sub_smul, add_smul]
        abel
    _ = 1 := by rw [key, zero_smul, sub_zero]

theorem refl_mulVec (w u : Fin r → E) (a : E) (ha : star w ⬝ᵥ u = a) (ha0 : a ≠ 0) :
    (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = u - w := by
  have h1 : (a⁻¹ • vecMulVec w (star w)) *ᵥ u = a⁻¹ • (vecMulVec w (star w) *ᵥ u) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [sub_mulVec, one_mulVec, h1, vecMulVec_mulVec_eq, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem star_dot (x y : Fin r → E) : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, star_sum, mul_comm]

theorem exists_of_ne (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v) (ha : star (u - v) ⬝ᵥ u ≠ 0) :
    ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  have hN : star (u - v) ⬝ᵥ (u - v) = star (u - v) ⬝ᵥ u + star (star (u - v) ⬝ᵥ u) := by
    rw [star_dot]
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    rw [← hc]
    ring
  refine ⟨⟨_, refl_mem (u - v) _ ha hN⟩, ?_⟩
  show (1 - (star (u - v) ⬝ᵥ u)⁻¹ • vecMulVec (u - v) (star (u - v))) *ᵥ u = v
  rw [refl_mulVec (u - v) u _ rfl ha]
  abel

theorem exists_unitary_mulVec (h2 : (2 : E) ≠ 0) (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v)
    (h0 : star u ⬝ᵥ u ≠ 0) : ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  by_cases ha : star (u - v) ⬝ᵥ u = 0
  · have hvu : star v ⬝ᵥ u = star u ⬝ᵥ u := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at ha; exact ha.symm
    have hc' : star (-u) ⬝ᵥ (-u) = star v ⬝ᵥ v := by simpa using hc
    have ha' : star (-u - v) ⬝ᵥ (-u) ≠ 0 := by
      have : star (-u - v) ⬝ᵥ (-u) = 2 * (star u ⬝ᵥ u) := by
        simp only [star_sub, star_neg, sub_dotProduct, neg_dotProduct, dotProduct_neg, hvu]
        ring
      rw [this]; exact mul_ne_zero h2 h0
    obtain ⟨g, hg⟩ := exists_of_ne (-u) v hc' ha'
    refine ⟨⟨-g.1, ?_⟩, ?_⟩
    · rw [mem_unitaryGroup_iff', star_neg, neg_mul_neg]; exact mem_unitaryGroup_iff'.1 g.2
    · show (-g.1) *ᵥ u = v
      rw [← hg, neg_mulVec, mulVec_neg]
  · exact exists_of_ne u v hc ha

end GlobalTheory.UnitWitt

theorem GlobalTheory.unitary_transitive_of_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (u v : Fin r → E), star u ⬝ᵥ u = star v ⬝ᵥ v →
    star u ⬝ᵥ u ≠ 0 → ∃ g : Matrix.unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  intro F E _ _ _ _ hU r u v hc h0
  haveI : CharZero F := hU.charZero
  have h2 : (2 : E) ≠ 0 := by
    intro h
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]; exact h
  exact GlobalTheory.UnitWitt.exists_unitary_mulVec h2 u v hc h0
end

