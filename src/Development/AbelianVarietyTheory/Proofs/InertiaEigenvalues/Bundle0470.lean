module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinApproxRootImageIndep
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem scaleRoots_derivative_eval₂_mul {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (P : Polynomial W)
    (s : W) (t : R) :
    c s * Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) =
      c s ^ P.natDegree * Polynomial.eval₂ c t (Polynomial.derivative P) := by
  have h : (P.scaleRoots s).comp (Polynomial.C s * Polynomial.X) = Polynomial.C s ^ P.natDegree * P := by
    have h0 := Polynomial.scaleRoots_eval₂_mul (p := P) (Polynomial.C : W →+* Polynomial W) Polynomial.X s
    rw [Polynomial.eval₂_C_X] at h0
    exact h0
  have h1 := congrArg (fun r => Polynomial.eval₂ c t (Polynomial.derivative r)) h
  simp only [Polynomial.derivative_comp, ← Polynomial.C_pow, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_comp, Polynomial.eval₂_X] at h1
  rw [h1, map_pow]

theorem exists_mul_derivative_scaleRoots_sub_mem {W R : Type} [CommRing W] [CommRing R] (c : W →+* R) (I : Ideal R)
    (P a b : Polynomial W) (s z : W) (hab : a * P + b * Polynomial.derivative P = Polynomial.C z) (t x : R)
    (ht : Polynomial.eval₂ c t P ∈ I) (hx : x - c s * t ∈ I) :
    ∃ b' : R, b' * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x - c s ^ P.natDegree * c z ∈ I := by
  refine ⟨Polynomial.eval₂ c t b * c s, ?_⟩
  obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub x (c s * t) (Polynomial.derivative ((P.scaleRoots s).map c))
  have h1 := scaleRoots_derivative_eval₂_mul c P s t
  have h2 := congrArg (Polynomial.eval₂ c t) hab
  rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_C] at h2
  have h3 : (Polynomial.derivative ((P.scaleRoots s).map c)).eval (c s * t) =
      Polynomial.eval₂ c (c s * t) (Polynomial.derivative (P.scaleRoots s)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map]
  rw [h3] at hw
  have h4 : Polynomial.eval₂ c t b * c s * (Polynomial.derivative ((P.scaleRoots s).map c)).eval x -
      c s ^ P.natDegree * c z = (Polynomial.eval₂ c t b * c s * w) * (x - c s * t) -
        (c s ^ P.natDegree * Polynomial.eval₂ c t a) * Polynomial.eval₂ c t P := by
    linear_combination (Polynomial.eval₂ c t b * c s) * hw + Polynomial.eval₂ c t b * h1 +
      c s ^ P.natDegree * h2
  rw [h4]
  exact I.sub_mem (I.mul_mem_left _ hx) (I.mul_mem_left _ ht)

theorem eval₂_C_X_powerSeries {W : Type} [CommRing W] (P : Polynomial W) :
    Polynomial.eval₂ (PowerSeries.C : W →+* W⟦X⟧) X P = (P : W⟦X⟧) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add, hp, hq, Polynomial.coe_add]
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_C, Polynomial.coe_X]

theorem approxRoot_image_indep_general_rings {W R : Type} [CommRing W] [CommRing R] (l n m c : ℕ) (P a b : Polynomial W)
    (hab : a * P + b * Polynomial.derivative P = Polynomial.C ((l : W) ^ c)) (q : W⟦X⟧)
    (h1 : (P : W⟦X⟧) ∣ q - (l : W⟦X⟧) ^ m * X)
    (h2 : (P : W⟦X⟧) ^ n ∣ Polynomial.eval₂ PowerSeries.C q (P.scaleRoots ((l : W) ^ m)))
    (I : Ideal R) (f g : W⟦X⟧ →+* R) (hC : ∀ w, f (PowerSeries.C w) = g (PowerSeries.C w)) (hX : f X - g X ∈ I)
    (hI : I = Ideal.span {f P}) (hI' : I = Ideal.span {g P}) :
    ∃ k : ℕ, f P ^ n ∣ (l : R) ^ k * (f q - g q) := by
  have hfE : f P ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hgE : g P ∈ I := by rw [hI']; exact Ideal.mem_span_singleton_self _
  have hcomp : f.comp PowerSeries.C = g.comp PowerSeries.C := RingHom.ext hC
  have hroot : ∀ h : W⟦X⟧ →+* R, h P ∈ I →
      ((P.scaleRoots ((l : W) ^ m)).map (h.comp PowerSeries.C)).eval (h q) ∈ I ^ n := by
    intro h hE
    obtain ⟨y, hy⟩ := h2
    rw [Polynomial.eval_map, ← Polynomial.hom_eval₂, hy, map_mul, map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hE n)
  have hcong : ∀ h : W⟦X⟧ →+* R, h P ∈ I → h q - (l : R) ^ m * h X ∈ I := by
    intro h hE
    obtain ⟨y, hy⟩ := h1
    have := congrArg h hy
    rw [map_sub, map_mul, map_mul, map_pow, map_natCast] at this
    rw [this]
    exact Ideal.mul_mem_right _ _ hE
  have hxy : f q - g q ∈ I := by
    have : f q - g q = (f q - (l : R) ^ m * f X) - (g q - (l : R) ^ m * g X) + (l : R) ^ m * (f X - g X) := by ring
    rw [this]
    exact I.add_mem (I.sub_mem (hcong f hfE) (hcong g hgE)) (I.mul_mem_left _ hX)
  obtain ⟨b', hb'⟩ := exists_mul_derivative_scaleRoots_sub_mem (f.comp PowerSeries.C) I P a b
    ((l : W) ^ m) _ hab (f X) (f q)
    (by rw [← Polynomial.hom_eval₂, eval₂_C_X_powerSeries]; exact hfE)
    (by rw [map_pow, map_natCast]; exact hcong f hfE)
  have hg := hroot g hgE
  rw [← hcomp] at hg
  have key := _root_.GlobalTheory.pow_mul_sub_mem_of_roots_mod_pow R I _ _ _ _ _ n (hroot f hfE) hg hxy hb'
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton, map_pow, map_pow, map_natCast, ← pow_mul, ← pow_add,
    ← pow_mul] at key
  exact ⟨_, key⟩

theorem approx_root_indep : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n m : ℕ) (q : bk.S), bk.E ∣ q - (l : bk.S) ^ m * X → bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ m)) → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ n ∣ (l : B.A) ^ k * (BK.hf f q - BK.hf g q)) := by
  intro l _ K bk n m q h1 h2 B f g
  obtain ⟨hC, hX, hI⟩ := GlobalTheory.BSP.IdealSubMembership.main l K bk B f g
  obtain ⟨-, -, hI'⟩ := GlobalTheory.BSP.IdealSubMembership.main l K bk B g f
  obtain ⟨c, a, b, hab⟩ := _root_.GlobalTheory.BSP.bezout_Ep_derivative l K bk
  exact approxRoot_image_indep_general_rings l n m c bk.Ep a b hab q h1 h2 B.I (BK.hf f) (BK.hf g) hC hX hI hI'

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaBoundedDenominators
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaBd

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} {N d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}

theorem isBeta_scale {bk : BK K} (F : Frame bk N d ρ) {m k : ℕ} {β : Matrix (Fin d) (Fin d) bk.S}
    (hβ : F.IsBeta m k β) (j : ℕ) : F.IsBeta m (k + j) ((l : bk.S) ^ j • β) := by
  refine ⟨fun p q => ?_, fun g p q => ?_⟩
  · have : ((l : bk.S) ^ j • β - (l : bk.S) ^ (k + j) • (1 : Matrix (Fin d) (Fin d) bk.S)) p q =
        (l : bk.S) ^ j * (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) p q := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, pow_add]; ring
    rw [this]; exact dvd_mul_of_dvd_right (hβ.1 p q) _
  · have h2 : ((l : bk.S) ^ j • β).map bk.ev = (l : Ainf l) ^ j • β.map bk.ev := by
      ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    have h1 : (((l : bk.S) ^ j • β).map bk.ev).map (Per.σA (g : GQ l)) =
        (l : Ainf l) ^ j • (β.map bk.ev).map (Per.σA (g : GQ l)) := by
      rw [h2]; ext p q; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, map_natCast]
    rw [h1, h2, Matrix.mul_smul, ← smul_sub, Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_right (hβ.2 g p q) _

end GlobalTheory.BKLim.BetaBd


open GlobalTheory.BKLim.BetaBd in
theorem GlobalTheory.BKLim.beta_bdd_denominators : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m : ℕ), ∃ c : ℕ, ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k : ℕ) (β : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → ∃ β', F.IsBeta m c β' := by
  intro l _ K bk m
  obtain ⟨g, z, ⟨w, hw, hzw⟩, hz⟩ := _root_.GlobalTheory.BKLim.exists_isZ_not_root l K bk
  have hu : ∀ i, 1 ≤ i → Per.θ l w ^ i - 1 ≠ 0 := by
    intro i hi h
    apply hz i hi
    have h1 : ((Per.θ l w : OC l) : ℂ_[l]) ^ i = 1 := by
      have := congrArg (fun t : OC l => (t : ℂ_[l])) (sub_eq_zero.1 h)
      simpa using this
    rw [(thetaD_props l).2.2.2.1 w] at hzw
    calc z ^ i = z ^ i * ((Per.θ l w : ℂ_[l]) ^ i) := by rw [h1, mul_one]
      _ = (z * (Per.θ l w : ℂ_[l])) ^ i := (mul_pow _ _ _).symm
      _ = 1 := by rw [hzw, one_pow]
  choose a ha using fun i : {i : ℕ // 1 ≤ i} => exists_dvd_bound _ (hu i.1 i.2)
  let A : ℕ → ℕ := fun i => if h : 1 ≤ i then a ⟨i, h⟩ else 0
  let S : ℕ → ℕ := fun i => ∑ j ∈ Finset.range i, A j
  have hSs : ∀ i, S (i + 1) = S i + A i := fun i => Finset.sum_range_succ _ _
  have hSm : ∀ i j, i ≤ j → S i ≤ S j := fun i j h =>
    Finset.sum_le_sum_of_subset (Finset.range_mono h)
  refine ⟨S m, fun N d ρ F k β hβ => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨(l : bk.S) ^ S 0 • 1, fun p q => by simp, fun g p q => by simp⟩
  by_cases hk : k < S m
  · refine ⟨(l : bk.S) ^ (S m - k) • β, ?_⟩
    have := isBeta_scale F hβ (S m - k)
    rwa [Nat.add_sub_cancel' hk.le] at this
  push_neg at hk
  have key : ∀ i, 1 ≤ i → i ≤ m → ∃ γ : Matrix (Fin d) (Fin d) bk.S,
      ∀ p q, bk.E ^ i ∣ (β - (l : bk.S) ^ (k - S i) • γ) p q := by
    intro i
    induction i with
    | zero => intro h; omega
    | succ i ih =>
      intro _ him
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · refine ⟨(l : bk.S) ^ S 1 • 1, fun p q => ?_⟩
        have hS : S 1 ≤ k := le_trans (hSm 1 m him) hk
        rw [smul_smul, ← pow_add, Nat.sub_add_cancel hS, pow_one]
        exact hβ.1 p q
      · obtain ⟨γ, hγ⟩ := ih hi0 (by omega)
        obtain ⟨δ, hδ1, hδ2⟩ := GlobalTheory.T.breuilKisin_beta_next_coeff_theta_mem l K bk N d ρ F g w hw m k β hβ i (k - S i) him γ hγ
        have hAi : A i = a ⟨i, hi0⟩ := dif_pos hi0
        have hS1 : S (i + 1) ≤ k := le_trans (hSm _ _ him) hk
        have hle : a ⟨i, hi0⟩ ≤ k - S i := by rw [hSs] at hS1; omega
        have hexp : k - S i - a ⟨i, hi0⟩ = k - S (i + 1) := by rw [hSs, hAi]; omega
        have hlift : ∀ p q, ∃ s' t : bk.S, δ p q = (l : bk.S) ^ (k - S (i + 1)) * s' + bk.E * t := by
          intro p q
          obtain ⟨y, hy⟩ := hδ2 p q
          obtain ⟨y', hy'⟩ := ha ⟨i, hi0⟩ _ y _ hy hle
          rw [hexp] at hy'
          exact _root_.GlobalTheory.LiftDiv.dvd_mod_E l K bk _ _ y' hy'
        choose δ' t ht using hlift
        refine ⟨(l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ', fun p q => ?_⟩
        have hpow : (l : bk.S) ^ (k - S (i + 1)) * (l : bk.S) ^ A i = (l : bk.S) ^ (k - S i) := by
          rw [← pow_add]; congr 1; rw [hSs] at hS1 ⊢; omega
        have e : (β - (l : bk.S) ^ (k - S (i + 1)) • ((l : bk.S) ^ A i • γ + bk.E ^ i • Matrix.of δ')) p q =
            (β - (l : bk.S) ^ (k - S i) • γ - bk.E ^ i • δ) p q + bk.E ^ (i + 1) * t p q := by
          simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
          linear_combination (bk.E ^ i) * ht p q - γ p q * hpow
        rw [e]
        exact dvd_add (hδ1 p q) (dvd_mul_right _ _)
  obtain ⟨γ, hγ⟩ := key m hm le_rfl
  refine ⟨γ, ?_⟩
  have := GlobalTheory.T.breuilKisin_isBeta_sub_of_lpow_smul l K bk N d ρ F m k (k - S m) β γ hβ hm (Nat.sub_le k (S m)) hγ
  rwa [Nat.sub_sub_self hk] at this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinChangeOfBasisNoPoleAtE
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.NoPole

theorem mul_eq_smul_one_comm {R : Type*} [CommRing R] [IsDomain R] {d : ℕ}
    (X X' : Matrix (Fin d) (Fin d) R) (c : R) (hc : c ≠ 0)
    (h : X * X' = c • (1 : Matrix (Fin d) (Fin d) R)) : X' * X = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : X.det * X'.det = c ^ d := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hX : X.det ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hdet; exact pow_ne_zero _ hc hdet.symm
  have key : X.det • (X' * X) = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc X.det • (X' * X) = (X.adjugate * X) * (X' * X) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = X.adjugate * (X * X') * X := by simp only [Matrix.mul_assoc]
      _ = c • (X.adjugate * X) := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
      _ = X.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
          rw [Matrix.adjugate_mul, smul_comm]
  ext i j
  have := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hX this

theorem map_smul_ring {R S : Type*} [CommRing R] [CommRing S] {a b : Type*} (F : R →+* S) (c : R)
    (M : Matrix a b R) : (c • M).map F = F c • M.map F := by
  ext i j; simp

end GlobalTheory.NoPole

namespace GlobalTheory.NoPole

theorem core {S B : Type*} [CommRing S] [CommRing B] {d m : ℕ} (F G : S →+* B) (E : S) (v : B)
    (ℓ N c₂ k₀ : ℕ) (s : Matrix (Fin d) (Fin m) S) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) S)
    (Q : Matrix (Fin m) (Fin d) S) (Q' : Matrix (Fin d) (Fin m) S)
    (hs : ∀ r i, F E ^ (2 * N) ∣ (ℓ : B) ^ k₀ * (F (s r i) - G (s r i)))
    (hv : v * F E = G E)
    (hX'X : X' * X = ((ℓ : S) ^ c₂ * E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) S))
    (hX : X = (s * Matrix.diagonal fun i => E ^ n i) * Q + E ^ (2 * N) • R)
    (hQ' : (ℓ : S) ^ c₂ • (s * Matrix.diagonal fun i => E ^ n i) = X * Q') :
    ∀ i j, F E ^ (2 * N) ∣ (ℓ : B) ^ (k₀ + c₂) * (X'.map F * X.map G) i j := by
  classical
  let π := Ideal.Quotient.mk (Ideal.span {F E ^ (2 * N)})
  let F' := π.comp F
  let G' := π.comp G
  have hFE : F' E ^ (2 * N) = 0 := by
    have h0 : π (F E ^ (2 * N)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    simpa only [F', RingHom.comp_apply, map_pow] using h0
  have hGE : G' E = π v * F' E := by
    simp only [G', F', RingHom.comp_apply]; rw [← map_mul, hv]
  have hGE0 : G' E ^ (2 * N) = 0 := by rw [hGE, mul_pow, hFE, mul_zero]
  have e2 : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • s.map G' = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • s.map F' := by
    ext r i
    have h : π ((ℓ : B) ^ k₀ * (F (s r i) - G (s r i))) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (hs r i))
    simp only [map_mul, map_sub, map_pow, map_natCast] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, F', G', RingHom.comp_apply]
    linear_combination (-1 : B ⧸ Ideal.span {F E ^ (2 * N)}) * h
  have hd : (Matrix.diagonal fun i => G' (E ^ n i)) =
      Matrix.diagonal (fun i => F' E ^ n i) * Matrix.diagonal (fun i => π v ^ n i) := by
    rw [Matrix.diagonal_mul_diagonal]; congr 1; funext i; rw [map_pow, hGE, mul_pow]; ring
  have e1 : X.map G' = (s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) *
      (Matrix.diagonal (fun i => π v ^ n i) * Q.map G') := by
    rw [hX, Matrix.map_add _ (map_add G'), map_smul_ring, map_pow, hGE0, zero_smul, add_zero, Matrix.map_mul, Matrix.map_mul,
      Matrix.diagonal_map (map_zero _), hd]
    simp only [Matrix.mul_assoc]
  have e3 : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i)) = X.map F' * Q'.map F' := by
    have : ((ℓ : S) ^ c₂ • (s * Matrix.diagonal fun i => E ^ n i)).map F' = (X * Q').map F' := by rw [hQ']
    rw [map_smul_ring, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero _), map_pow, map_natCast]
      at this
    simpa only [map_pow] using this
  have e4 : X'.map F' * X.map F' = 0 := by
    rw [← Matrix.map_mul, hX'X, map_smul_ring, map_mul, map_pow F' E, hFE, mul_zero, zero_smul]
  have hsuff : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ (k₀ + c₂)) • (X'.map F' * X.map G') = 0 := by
    have e2' : ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) =
        ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i)) := by
      rw [← Matrix.smul_mul, e2, Matrix.smul_mul]
    rw [e1]
    calc ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ (k₀ + c₂)) • (X'.map F' * ((s.map G' * Matrix.diagonal (fun i => F' E ^ n i)) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G')))
        = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map G' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring
      _ = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by rw [e2']
      _ = ((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ k₀) • (X'.map F' * ((((ℓ : B ⧸ Ideal.span {F E ^ (2 * N)}) ^ c₂) • (s.map F' * Matrix.diagonal (fun i => F' E ^ n i))) *
          (Matrix.diagonal (fun i => π v ^ n i) * Q.map G'))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring
      _ = 0 := by
          rw [e3]; simp only [← Matrix.mul_assoc, e4, Matrix.zero_mul, smul_zero]
  intro i j
  have := congrFun (congrFun hsuff i) j
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [Matrix.mul_apply, map_sum, F', G', π] using this

end GlobalTheory.NoPole


open GlobalTheory.NoPole in
theorem GlobalTheory.seed_nopole : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d m N c₂ : ℕ) (s : Matrix (Fin d) (Fin m) (bk.S)) (n : Fin m → ℕ) (X X' R : Matrix (Fin d) (Fin d) (bk.S)) (Q : Matrix (Fin m) (Fin d) (bk.S)) (Q' : Matrix (Fin d) (Fin m) (bk.S)), (∀ r i, (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (BK.hf f (s r i) - BK.hf g (s r i)))) → X * X' = ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) • (1 : Matrix (Fin d) (Fin d) (bk.S)) → X = (s * Matrix.diagonal fun i => bk.E ^ n i) * Q + bk.E ^ (2 * N) • R → (l : bk.S) ^ c₂ • (s * Matrix.diagonal fun i => bk.E ^ n i) = X * Q' → (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), ∃ k : ℕ, ∀ i j, BK.hf f bk.E ^ (2 * N) ∣ (l : B.A) ^ k * (X'.map (BK.hf f) * X.map (BK.hf g)) i j) := by
  intro l _ K bk d m N c₂ s n X X' R Q Q' hs hXX' hX hQ' B f g
  classical
  have hl0 : (l : bk.S) ≠ 0 := by
    intro h0
    have h1 : bk.str.symm (Ideal.Quotient.mk _ (l : bk.S)) = 0 := by rw [h0, map_zero, map_zero]
    rw [map_natCast, map_natCast] at h1
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) h1
  have hc : ((l : bk.S) ^ c₂ * bk.E ^ (2 * N)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ bk.E_ne_zero)
  have hX'X := mul_eq_smul_one_comm X X' _ hc hXX'
  choose k hk using fun (p : Fin d × Fin m) => hs p.1 p.2 B f g
  obtain ⟨v, hv⟩ : ∃ v, v * BK.hf f bk.E = BK.hf g bk.E := by
    have h1 := (_root_.GlobalTheory.BSP.IdealSubMembership.main l K bk B f g).2.2
    have h2 := (_root_.GlobalTheory.BSP.IdealSubMembership.main l K bk B g f).2.2
    have : BK.hf g bk.E ∈ B.I := by rw [h2]; exact Ideal.mem_span_singleton_self _
    rw [h1] at this
    exact Ideal.mem_span_singleton'.1 this
  refine ⟨Finset.univ.sup k + c₂, GlobalTheory.NoPole.core (BK.hf f) (BK.hf g) bk.E v l N c₂ _ s n X X' R Q Q' ?_ hv
    hX'X hX hQ'⟩
  intro r i
  have hle : k (r, i) ≤ Finset.univ.sup k := Finset.le_sup (Finset.mem_univ _)
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact Dvd.dvd.mul_left (hk (r, i)) _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCrystalBasisAndSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKBasis

set_option maxHeartbeats 1000000

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∃ b : ι → E.M (ϖ.prism a), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) ∧ ∀ x : E.M (ϖ.prism a), ∃ (N : ℕ) (c : ι → Fin N → O) (s : ι → Fin N → (ϖ.prism a).A), x = ∑ j, ∑ q, s j q • (oE (c j q)).u (ϖ.prism a) (b j) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  letI := zlLat T
  intro E jA H him oE hoE
  obtain ⟨J, hJ⟩ : ∃ J : E.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (E.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (E.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  obtain ⟨c, hc, hcJ, hs⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hi : Function.Injective J := by
    have := E.proj (ainfObj (ϖ.field a))
    have := E.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact GlobalTheory.BKCoord.semiBC_injective (E.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  have hci : Function.Injective c := fun x y hxy => hi (by rw [hcJ, hcJ]; simp only [hxy])
  have hsm : ∀ (w : (ϖ.prism a).A) (x : E.M (ϖ.prism a)),
      c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i := fun w x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg jA ((E.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hom : ∀ (o : O) (x : E.M (ϖ.prism a)),
      c ((oE o).u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i := fun o x => by
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have hk : ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T,
        kappa T ((OfCrystal.mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero, smul_zero]
      | tmul v z => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) z
      | add y y' hy hy' => simp only [map_add (f := _), smul_add, hy, hy']
    have h4 := (congrArg (kappa T) h3).trans (hk _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hbas : ∀ j, (bas j : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    change (Pi.single j (1 : K⟦X⟧) : ι → K⟦X⟧) i ∈ A O K
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      exact one_mem _
    · rw [Pi.single_eq_of_ne h]
      exact zero_mem _
  choose b hb using fun j => hs _ (hbas j)
  refine ⟨b, fun j => ⟨hbas j, ?_⟩, fun x => ?_⟩
  · rw [← hJ, hcJ]
    have e1 : (⟨c (b j), mem_ME_of_mem_M (hc _)⟩ : ME P) = ⟨bas j, mem_ME_of_mem_M (hbas j)⟩ :=
      Subtype.ext (hb j)
    rw [e1]
  · let o := Module.finBasis ℤ_[l] O
    have hf : ∀ i, ∃ s : Fin (Module.finrank ℤ_[l] O) → (Wq l a)⟦X⟧,
        (fun τ => (⟨c x τ i, mem_tot.1 (hc x) τ i⟩ : A O K)) = ∑ q, o q • toAc t K (s q) :=
      fun i => exists_eq_sum_toAc t K o _
    choose s hs' using hf
    refine ⟨Module.finrank ℤ_[l] O, fun _ q => o q, s, hci ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hsm, hom, hb]
    funext τ i
    have h6 := congrArg (fun f : ZMod a → A O K => (f τ : K⟦X⟧)) (hs' i)
    simp only [Finset.sum_apply, Pi.smul_apply, AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h6
    rw [h6]
    simp only [Finset.sum_apply]
    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl fun q _ => ?_
      have h7 := hsm (s i q) ((oE (o q)).u (ϖ.prism a) (b i))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_same, mul_one, Algebra.smul_def, algebraMap_eq_C]
      exact mul_comm _ _
    · intro j _ hj
      refine Finset.sum_eq_zero fun q _ => ?_
      have h7 := hsm (s j q) ((oE (o q)).u (ϖ.prism a) (b j))
      erw [h7, hom, hb]
      simp only [bas, Pi.single_eq_of_ne (Ne.symm hj), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
end GlobalTheory.BKBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  first | exact @GlobalTheory.BKGal.StableFix.main | exact GlobalTheory.BKGal.StableFix.main | (intros; apply GlobalTheory.BKGal.StableFix.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 → Function.Injective (toDisc l (s X) ρ) ∧ (∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s) ∧ ∀ ρ' : ℝ≥0, 0 < ρ' → ρ' ≤ ρ → ∀ R : Disc l (s X) ρ →+* Disc l (s X) ρ', IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R → Function.Injective R := by
  first | exact @GlobalTheory.BSP.toDisc_injective_of_topBasis | exact GlobalTheory.BSP.toDisc_injective_of_topBasis | (intros; apply GlobalTheory.BSP.toDisc_injective_of_topBasis <;> assumption)
end

