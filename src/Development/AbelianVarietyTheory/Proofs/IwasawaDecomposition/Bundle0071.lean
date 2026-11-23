module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRGaloisInvariantsEqFinExt
section
namespace GlobalTheory.MemLoc.InvDR
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section Abstract
variable {R F G : Type} [CommRing R] [IsDomain R] [Field F]

theorem inv_ker_eq_zero (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hsep : ∀ y, (∀ n : ℕ, t ^ n ∣ y) → y = 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (z : R) (hz : θ z = 0) (hinv : ∀ g, σ g z = z) : z = 0 := by
  have key : ∀ m : ℕ, t ^ (m + 1) ∣ z := by
    intro m
    induction m with
    | zero => simpa using hker z hz
    | succ m ih =>
      obtain ⟨w, hw⟩ := ih
      have h1 : ∀ g, σ g w * c g ^ (m + 1) = w := by
        intro g
        have h := hinv g
        rw [hw, map_mul, map_pow, hσt] at h
        apply mul_left_cancel₀ (pow_ne_zero (m + 1) ht)
        rw [← h]
        ring
      have h2 : θ w = 0 := by
        refine tate ((m + 1 : ℕ) : ℤ) _ (by omega) fun g => ?_
        rw [zpow_natCast, ← hθ, ← map_pow, ← map_mul, h1]
      obtain ⟨v, hv⟩ := hker w h2
      exact ⟨v, by rw [hw, hv]; ring⟩
  exact hsep z fun n => (pow_dvd_pow t (Nat.le_succ n)).trans (key n)

theorem eigen_eq (θ : R →+* F) (σ : G → R →+* R) (τ : G → F →+* F) (c : G → R) (t : R) (ht : t ≠ 0)
    (hker : ∀ y, θ y = 0 → t ∣ y) (hc : ∀ g, θ (c g) ≠ 0)
    (hθ : ∀ g y, θ (σ g y) = τ g (θ y)) (hσt : ∀ g, σ g t = c g * t)
    (tate : ∀ (i : ℤ) (x : F), i ≠ 0 → (∀ g, τ g x * θ (c g) ^ i = x) → x = 0)
    (n : ℕ) : ∀ y : R, (∀ g, σ g y = c g ^ n * y) → ∃ w, y = t ^ n * w ∧ ∀ g, σ g w = w := by
  induction n with
  | zero => intro y hy; exact ⟨y, by simp, fun g => by simpa using hy g⟩
  | succ n ih =>
    intro y hy
    have h2 : θ y = 0 := by
      refine tate (-((n + 1 : ℕ) : ℤ)) _ (by omega) fun g => ?_
      rw [zpow_neg, zpow_natCast, ← hθ, hy, map_mul, map_pow]
      have := pow_ne_zero (n + 1) (hc g)
      field_simp
    obtain ⟨v, hv⟩ := hker y h2
    obtain ⟨w, hw, hw'⟩ := ih v fun g => by
      have h := hy g
      rw [hv, map_mul, hσt] at h
      have hc0 : c g ≠ 0 := fun h0 => hc g (by rw [h0, map_zero])
      apply mul_left_cancel₀ (mul_ne_zero hc0 ht)
      rw [h]
      ring
    exact ⟨w, by rw [hv, hw]; ring, hw'⟩

end Abstract

variable {l : ℕ} [Fact l.Prime]

theorem j_alg (C : Core l) (a : Per.Ainf l) :
    C.j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [GlobalTheory.RingIface.tower, C.j_cris.on0, aDp, RingHom.comp_apply, SubalgebraClass.coe_algebraMap]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem invariants_BdR (l : ℕ) [Fact l.Prime] (C : Core l) (K : FinExt l) (b : Per.BdR l)
    (hb : ∀ g ∈ GK K, Per.σD g b = b) :
    ∃ y ∈ K.1, algebraMap (Per.BdRp l) (Per.BdR l) (C.o y) = b := by
  have he := GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨hdom, hinj, -, hfrac⟩ := _root_.GlobalTheory.MemLoc.BdRField.bdR_isField l
  obtain ⟨hfil, hreg, hcompl, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l C.ε he
  obtain ⟨-, hker, hunit, -, hθ⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  obtain ⟨-, ht1, ht2, -⟩ := _root_.GlobalTheory.MemLoc.core_t_unit_fil l C
  obtain ⟨-, -, hoσ⟩ := _root_.GlobalTheory.MemLoc.SecUniq.main l C.o C.o_sec
  obtain ⟨-, hjσ, -⟩ := _root_.GlobalTheory.MemLoc.crisP_unique_equivariant l C.j C.j_cris
  have hσD := (GlobalTheory.MemLoc.ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.1
  have hact := _root_.GlobalTheory.MemLoc.TAct.t_act l C
  have htate := _root_.GlobalTheory.MemLoc.tate_twist_invariants l C K
  have hast := _root_.GlobalTheory.MemLoc.invariants_finExt l K
  generalize hx : aDp l (xi C.ε) = x at *
  obtain ⟨n, y0, hy0⟩ := hfrac C.ε he b
  rw [hx] at hy0
  generalize htt : C.j C.t = t at *
  obtain ⟨u, hu⟩ := (hfil 1 t).1 ht1
  rw [pow_one] at hu
  have huu : IsUnit u := by
    refine hunit u fun h0 => ht2 ?_
    obtain ⟨v, hv⟩ := (hfil 1 u).1 ((hker u).1 h0)
    exact (hfil 2 t).2 ⟨v, by rw [hu, hv]; ring⟩
  have ht0 : t ≠ 0 := fun h0 => ht2 (h0 ▸ zero_mem _)
  have htx : t ∣ x := by rw [hu]; exact huu.mul_right_dvd.2 dvd_rfl
  have hxt : x ∣ t := ⟨u, hu⟩
  let c : ↥(GK K) → Per.BdRp l := fun g => C.o (algebraMap ℚ_[l] (Om l) ((C.χ g.1 : ℤ_[l]) : ℚ_[l]))
  have hθc : ∀ g, Per.θD l (c g) = algebraMap ℚ_[l] ℂ_[l] ((C.χ g.1 : ℤ_[l]) : ℚ_[l]) := fun g =>
    (C.o_sec.th _).trans rfl
  have hc : ∀ g, Per.θD l (c g) ≠ 0 := fun g => by
    rw [hθc, map_ne_zero]
    exact fun h => (C.χ g.1).ne_zero (PadicInt.coe_eq_zero.1 h)
  have hσt : ∀ g : ↥(GK K), Per.σDp g.1 t = c g * t := fun g => by
    rw [← htt, ← hjσ, hact, map_mul, j_alg, ← C.o_sec.z]
  have hker' : ∀ y, Per.θD l y = 0 → t ∣ y := fun y hy =>
    htx.trans (by simpa using (hfil 1 y).1 ((hker y).1 hy))
  have hsep : ∀ y : Per.BdRp l, (∀ n : ℕ, t ^ n ∣ y) → y = 0 := fun y hy => by
    refine hcompl.toIsHausdorff.haus y fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact (pow_dvd_pow_of_dvd hxt n).trans (hy n)
  have tate : ∀ (i : ℤ) (x : ℂ_[l]), i ≠ 0 →
      (∀ g : ↥(GK K), Per.σC g.1 x * Per.θD l (c g) ^ i = x) → x = 0 := fun i x hi h =>
    htate i x hi fun g hg => by simpa only [hθc] using h ⟨g, hg⟩
  have hy : b * algebraMap (Per.BdRp l) (Per.BdR l) t ^ n =
      algebraMap (Per.BdRp l) (Per.BdR l) (y0 * u ^ n) := by
    rw [hu, map_mul, map_mul, map_pow, ← hy0]
    ring
  generalize y0 * u ^ n = y at hy
  have hyσ : ∀ g : ↥(GK K), Per.σDp g.1 y = c g ^ n * y := fun g => by
    apply hinj
    rw [← hσD, ← hy, map_mul, map_pow, hσD, hσt, hb g.1 g.2, map_mul, map_mul, map_pow, ← hy]
    ring
  obtain ⟨w, hw, hw'⟩ := eigen_eq (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
    hker' hc (fun g y => hθ g.1 y) hσt tate n y hyσ
  obtain ⟨k, hk, hkθ⟩ := hast (Per.θD l w) fun g hg => by rw [← hθ, hw' ⟨g, hg⟩]
  have hz : w - C.o k = 0 := by
    refine inv_ker_eq_zero (Per.θD l) (fun g : ↥(GK K) => Per.σDp g.1) (fun g => Per.σC g.1) c t ht0
      hker' hsep (fun g y => hθ g.1 y) hσt tate _ ?_ fun g => ?_
    · rw [map_sub, C.o_sec.th, hkθ, sub_self]
    · have hg : g.1 k = k := g.2 ⟨k, hk⟩
      rw [map_sub, hw' g, hoσ, hg]
  refine ⟨k, hk, ?_⟩
  rw [← sub_eq_zero.1 hz]
  haveI : IsDomain (Per.BdR l) := (_root_.GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1.isDomain
  have ht' : algebraMap (Per.BdRp l) (Per.BdR l) t ^ n ≠ 0 :=
    pow_ne_zero n ((map_ne_zero_iff _ hinj).2 ht0)
  apply mul_right_cancel₀ ht'
  rw [hy, hw, map_mul, map_pow, mul_comm]

end GlobalTheory.MemLoc.InvDR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetTwistedConjugateIsKTypeOfReversed
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConjTwist

variable {k : ℕ}

theorem Jm_allPos (k : ℕ) : Formalism.REAL.Jm (allPos k) = 1 := by
  simp [Formalism.REAL.Jm, allPos]

theorem mem_U_iff (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [Jm_allPos, Matrix.mul_one]

theorem mem_K_iff (g : Matrix (Fin k) (Fin k) ℂ) :
    g ∈ Formalism.REAL.Kset (allPos k) ↔ g ∈ UJset (allPos k) := by
  rw [mem_U_iff]
  show (g ∈ Matrix.unitaryGroup (Fin k) ℂ ∧ g * Formalism.REAL.Jm (allPos k) = Formalism.REAL.Jm (allPos k) * g) ↔ _
  rw [Jm_allPos, Matrix.mul_one, Matrix.one_mul, Matrix.mem_unitaryGroup_iff']
  simp [Matrix.star_eq_conjTranspose]

theorem map_star_mul (g h : Matrix (Fin k) (Fin k) ℂ) :
    (g * h).map star = g.map star * h.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

theorem map_star_one : (1 : Matrix (Fin k) (Fin k) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

theorem map_star_star (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext a b
  simp

theorem map_star_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_U_iff] at hg ⊢
  have h : (g.map star)ᴴ = gᴴ.map star := by
    ext a b
    simp
  rw [h, ← map_star_mul, hg, map_star_one]

theorem norm_det {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : ‖g.det‖ = 1 := by
  rw [mem_U_iff] at hg
  have h := congrArg (fun M => ‖Matrix.det M‖) hg
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, Matrix.det_one,
    norm_one] at h
  nlinarith [norm_nonneg g.det]

theorem det_ne_zero {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) : g.det ≠ 0 := by
  intro h
  have := norm_det hg
  rw [h, norm_zero] at this
  exact zero_ne_one this

abbrev tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_map_star (θ : Fin k → ℝ) : (tor θ).map star = tor (fun a => -θ a) := by
  rw [tor, Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  show (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  simp

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ UJset (allPos k) := by
  rw [mem_U_iff, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  show (starRingEnd ℂ) _ * _ = _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

theorem tor_det_zpow (θ : Fin k → ℝ) (x : ℤ) :
    (tor θ).det ^ x = Complex.exp (((∑ a, (x : ℝ) * θ a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.det_diagonal, ← Complex.exp_sum, ← Complex.exp_int_mul]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

def revMat (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := Matrix.of fun a b => if Fin.rev a = b then 1 else 0

theorem revMat_mul_self : revMat k * revMat k = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev a)]
  · simp [revMat, Matrix.one_apply]
  · intro c _ hc
    simp [revMat, hc.symm]
  · simp

theorem revMat_conjTranspose : (revMat k)ᴴ = revMat k := by
  ext a b
  simp only [revMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · have h' : ¬ Fin.rev b = a := fun h' => h (by rw [← h', Fin.rev_rev])
    simp [h, h']

theorem revMat_mem : revMat k ∈ UJset (allPos k) := by
  rw [mem_U_iff, revMat_conjTranspose, revMat_mul_self]

theorem tor_mul_revMat (θ : Fin k → ℝ) :
    tor θ * revMat k = revMat k * tor (fun a => θ (Fin.rev a)) := by
  ext a b
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, revMat, Matrix.of_apply]
  by_cases h : Fin.rev a = b
  · subst h
    simp
  · simp [h]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem isWtOn_rev (hσ : IsURepOn (UJset (allPos k)) σ) {μ : Fin k → ℝ} {v : H}
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) σ μ v) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => μ (Fin.rev a)) (σ (revMat k) v) := by
  intro θ _
  have h1 : σ (tor θ) (σ (revMat k) v) = σ (revMat k) (σ (tor fun a => θ (Fin.rev a)) v) := by
    have h2 := hσ.1.2 _ (tor_mem θ) _ revMat_mem
    have h3 := hσ.1.2 _ revMat_mem _ (tor_mem fun a => θ (Fin.rev a))
    rw [tor_mul_revMat, h3] at h2
    exact (congrArg (fun f : H →L[ℂ] H => f v) h2).symm
  refine h1.trans ?_
  rw [hv _ ((mem_K_iff _).2 (tor_mem _)), map_smul]
  congr 4
  rw [← Equiv.sum_comp Fin.revPerm]
  simp

theorem rev_ne_zero (hσ : IsURepOn (UJset (allPos k)) σ) {v : H} (hv : v ≠ 0) :
    σ (revMat k) v ≠ 0 := by
  rw [← norm_ne_zero_iff, hσ.2.1 _ revMat_mem, norm_ne_zero_iff]
  exact hv

theorem exp_split (x : ℤ) (μ θ : Fin k → ℝ) :
    Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) =
      (tor θ).det ^ x * Complex.exp (((∑ a, ((x : ℝ) - μ a) * -θ a : ℝ) : ℂ) * Complex.I) := by
  rw [tor_det_zpow, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add, ← Finset.sum_add_distrib]
  congr 3
  exact Finset.sum_congr rfl fun a _ => by ring

theorem isWtOn_twist_iff (x : ℤ) (μ : Fin k → ℝ) (v : H) :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) μ v ↔
      IsWtOn (Formalism.REAL.Kset (allPos k)) σ (fun a => (x : ℝ) - μ a) v := by
  constructor
  · intro h θ _
    have h1 : (tor fun a => -θ a).det ^ x • σ ((tor fun a => -θ a).map star) v = _ :=
      h (fun a => -θ a) ((mem_K_iff _).2 (tor_mem _))
    rw [exp_split x, ← smul_smul, tor_map_star] at h1
    simp only [neg_neg] at h1
    exact smul_right_injective H (zpow_ne_zero x (det_ne_zero (tor_mem _))) h1
  · intro h θ _
    show (tor θ).det ^ x • σ ((tor θ).map star) v = _
    rw [exp_split x, ← smul_smul, tor_map_star, h _ ((mem_K_iff _).2 (tor_mem _))]

theorem stable_twist_iff (x : ℤ) (S : Submodule ℂ H) :
    IsKStableOn (allPos k) (fun g => g.det ^ x • σ (g.map star)) S ↔ IsKStableOn (allPos k) σ S := by
  constructor
  · intro h g hg v hv
    have hg' := map_star_mem ((mem_K_iff g).1 hg)
    have h1 : (g.map star).det ^ x • σ ((g.map star).map star) v ∈ S :=
      h _ ((mem_K_iff _).2 hg') v hv
    rw [map_star_star] at h1
    exact (S.smul_mem_iff (zpow_ne_zero x (det_ne_zero hg'))).1 h1
  · intro h g hg v hv
    exact S.smul_mem _ (h _ ((mem_K_iff _).2 (map_star_mem ((mem_K_iff g).1 hg))) v hv)

theorem isURepOn_twist (hσ : IsURepOn (UJset (allPos k)) σ) (x : ℤ) :
    IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) := by
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · simp only [Matrix.det_one, _root_.one_zpow, one_smul, map_star_one, hσ.1.1]
  · simp only [Matrix.det_mul, mul_zpow, map_star_mul]
    rw [hσ.1.2 _ (map_star_mem ha) _ (map_star_mem hb)]
    ext v
    simp [smul_smul, mul_comm]
  · simp only [ContinuousLinearMap.smul_apply, norm_smul, norm_zpow, norm_det hg, _root_.one_zpow,
      one_mul, hσ.2.1 _ (map_star_mem hg)]
  · simp only [ContinuousLinearMap.smul_apply]
    refine ContinuousOn.smul ?_ ?_
    · exact (continuous_id.matrix_det.continuousOn).zpow₀ x fun g hg => Or.inl (det_ne_zero hg)
    · exact (hσ.2.2 v).comp (continuous_id.matrix_map continuous_star).continuousOn
        fun g hg => map_star_mem hg

theorem cdom_rev (x : ℤ) (Λ μ : Fin k → ℝ)
    (h : CDom (allPos k) (fun a => (x : ℝ) - μ (Fin.rev a)) Λ) :
    CDom (allPos k) μ (fun a => (x : ℝ) - Λ (Fin.rev a)) := by
  obtain ⟨c, hc, he⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b hab => ⟨?_, rfl⟩, ?_⟩
  · exact Fin.rev_lt_rev.1 (hc _ _ hab).1
  · funext i
    have h1 := congrFun he (Fin.rev i)
    simp only [Pi.sub_apply, Fin.rev_rev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : ∑ a, ∑ b, (c (Fin.rev b) (Fin.rev a) : ℝ) * Formalism.REAL.root a b i =
        -∑ a, ∑ b, (c a b : ℝ) * Formalism.REAL.root a b (Fin.rev i) := by
      rw [Finset.sum_comm, ← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Equiv.sum_comp Fin.revPerm, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, Formalism.REAL.root, Pi.sub_apply, Pi.single_apply,
        Fin.rev_eq_iff]
      ring
    rw [h2, ← h1]
    ring

theorem conj_twist_isKTypeOf : ∀ (k : ℕ) (Λ : Fin k → ℝ) (x : ℤ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → IsURepOn (UJset (allPos k)) (fun g => g.det ^ x • σ (g.map star)) ∧ IsKTypeOf (allPos k) (fun g => g.det ^ x • σ (g.map star)) (fun a => (x : ℝ) - Λ (Fin.rev a)) ⊤ := by
  intro k Λ x H _ _ _ σ hσ hK
  obtain ⟨hfd, -, hirr, ⟨v, -, hv0, hv⟩, hdom⟩ := hK
  refine ⟨isURepOn_twist hσ x, hfd, fun _ _ _ _ => trivial,
    fun S hS hst => hirr S hS ((stable_twist_iff x S).1 hst),
    ⟨σ (revMat k) v, trivial, rev_ne_zero hσ hv0, ?_⟩, fun μ w _ hw0 hw => ?_⟩
  · rw [isWtOn_twist_iff]
    simpa only [sub_sub_cancel] using isWtOn_rev hσ hv
  · rw [isWtOn_twist_iff] at hw
    exact cdom_rev x Λ μ (hdom _ _ trivial (rev_ne_zero hσ hw0) (isWtOn_rev hσ hw))

end GlobalTheory.ConjTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstituentImage
section
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory.ConstituentImage

theorem exists_constituent_image : ∀ {Γ L : Type} [Group Γ] [Field L] {a n : ℕ} (τ τ₀ : Γ →* GL (Fin a) L) (P : GL (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * (P : Matrix (Fin a) (Fin a) L) = (P : Matrix (Fin a) (Fin a) L) * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) → IsSSRep τ → ∀ (Vs : Fin n → Submodule L (Fin a → L)), iSup Vs = ⊤ → (∀ j, IsIrrSub τ₀ (Vs j)) → ∀ V, IsIrrSub τ V → ∃ (j : Fin n) (M : Matrix (Fin a) (Fin a) L), (∀ g, ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) * M = M * ((τ₀ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)) ∧ Submodule.map M.mulVecLin (Vs j) = V ∧ Disjoint (LinearMap.ker M.mulVecLin) (Vs j) := by
  intro Γ L _ _ a n τ τ₀ P hP hss Vs hVs hirr V hV
  obtain ⟨W', hW'i, hc⟩ := hss V hV.2.1
  set p : (Fin a → L) →ₗ[L] (Fin a → L) := V.subtype ∘ₗ Submodule.linearProjOfIsCompl V W' hc with hpdef
  have hpV : ∀ x, p x ∈ V := fun x => (Submodule.linearProjOfIsCompl V W' hc x).2
  have hpid : ∀ x ∈ V, p x = x := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨x, hx⟩)
  have hp0 : ∀ x ∈ W', p x = 0 := fun x hx =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨x, hx⟩)
  have hcomm : ∀ g v, p ((τ g : Matrix (Fin a) (Fin a) L).mulVec v) = (τ g : Matrix (Fin a) (Fin a) L).mulVec (p v) := by
    intro g v
    set q := v - p v
    have hq : q ∈ W' := by
      rw [← Submodule.linearProjOfIsCompl_apply_eq_zero_iff hc, map_sub]
      have := Submodule.linearProjOfIsCompl_apply_left hc ⟨p v, hpV v⟩
      rw [this, sub_eq_zero]; rfl
    have hv : v = p v + q := by simp [q]
    conv_lhs => rw [hv]
    rw [Matrix.mulVec_add, map_add (f := _), hpid _ (hV.2.1 g _ (hpV v)), hp0 _ (hW'i g _ hq), add_zero]
  set π : Matrix (Fin a) (Fin a) L := LinearMap.toMatrix' p with hπ
  have hπv : ∀ v, π.mulVec v = p v := fun v => by simp [hπ, LinearMap.toMatrix'_mulVec]
  have hπc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * π = π * (τ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply, Matrix.toLin'_apply, hπv, hcomm]
  set M : Matrix (Fin a) (Fin a) L := π * (P : Matrix (Fin a) (Fin a) L) with hM
  have hMc : ∀ g, (τ g : Matrix (Fin a) (Fin a) L) * M = M * (τ₀ g : Matrix (Fin a) (Fin a) L) := by
    intro g
    rw [hM, ← Matrix.mul_assoc, hπc g, Matrix.mul_assoc, hP g, Matrix.mul_assoc]
  have hMv : ∀ g v, (τ g : Matrix (Fin a) (Fin a) L).mulVec (M.mulVec v) = M.mulVec ((τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v) := by
    intro g v
    rw [Matrix.mulVec_mulVec, hMc g, ← Matrix.mulVec_mulVec]
  have hMV : ∀ v, M.mulVec v ∈ V := fun v => by
    rw [hM, ← Matrix.mulVec_mulVec, hπv]; exact hpV _

  have hex : ∃ j, Submodule.map M.mulVecLin (Vs j) ≠ ⊥ := by
    by_contra hne
    push_neg at hne
    obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.1
    have hsup : Submodule.map M.mulVecLin ⊤ = ⊥ := by
      rw [← hVs, Submodule.map_iSup]; simp [hne]
    have hmem : M.mulVec (((P⁻¹ : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).mulVec x) ∈ Submodule.map M.mulVecLin ⊤ :=
      ⟨_, Submodule.mem_top, rfl⟩
    rw [hsup, Submodule.mem_bot, hM, ← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec (M := (P : Matrix (Fin a) (Fin a) L)),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, hπv, hpid x hxV] at hmem
    exact hx0 hmem
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, M, hMc, ?_, ?_⟩
  · have hinv : IsInv τ (Submodule.map M.mulVecLin (Vs j)) := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨(τ₀ g : Matrix (Fin a) (Fin a) L).mulVec v, (hirr j).2.1 g v hv, ?_⟩
      simp only [Matrix.mulVecLin_apply]
      exact (hMv g v).symm
    have hle : Submodule.map M.mulVecLin (Vs j) ≤ V := by
      rintro _ ⟨v, _, rfl⟩; exact hMV v
    rcases hV.2.2 _ hle hinv with h | h
    · exact absurd h hj
    · exact h
  · have hinv : IsInv τ₀ (LinearMap.ker M.mulVecLin ⊓ Vs j) := by
      rintro g v ⟨hk, hv⟩
      refine ⟨?_, (hirr j).2.1 g v hv⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk ⊢
      rw [← hMv, hk, Matrix.mulVec_zero]
    rcases (hirr j).2.2 _ inf_le_right hinv with h | h
    · exact disjoint_iff.2 h
    · exfalso
      apply hj
      rw [eq_bot_iff]
      rintro _ ⟨v, hv, rfl⟩
      have hk : v ∈ LinearMap.ker M.mulVecLin := (h ▸ (inf_le_left : LinearMap.ker M.mulVecLin ⊓ Vs j ≤ _)) hv
      simpa using hk

end GlobalTheory.ConstituentImage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.UG

namespace GlobalTheory.Mem.Col2

def FunKilled {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (π : 𝓞 E) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (t t' : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))),
    t'.1 = inclE (F := F) (v.adicCompletion F) (π : E) • t.1 → S.fT v hv t' = 0

end GlobalTheory.Mem.Col2
end

