module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0510
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0746
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveClassFunctionExpansionRootSumsStatement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaOfDiscCocycle
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.BetaDR

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem map_mk_eq_iff {R : Type} [CommRing R] {d : ℕ} (e : R) (P P' : Matrix (Fin d) (Fin d) R) :
    P.map (Ideal.Quotient.mk (Ideal.span {e})) = P'.map (Ideal.Quotient.mk (Ideal.span {e})) ↔
      ∀ a b, e ∣ P a b - P' a b := by
  constructor
  · intro h a b
    have h1 := congrFun (congrFun h a) b
    simp only [Matrix.map_apply] at h1
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  · intro h
    ext a b
    simp only [Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h a b))

theorem map_smul_mat {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R') (c : R)
    (P : Matrix (Fin d) (Fin d) R) : (c • P).map f = f c • P.map f := by
  ext a b; simp

theorem map_sub_mat {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R')
    (P P' : Matrix (Fin d) (Fin d) R) : (P - P').map f = P.map f - P'.map f := by
  ext a b; simp

theorem map_mul_three {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R')
    (P₁ P₂ P₃ : Matrix (Fin d) (Fin d) R) : (P₁ * P₂ * P₃).map f = P₁.map f * P₂.map f * P₃.map f := by
  simp only [Matrix.map_mul]

theorem map_entry_sub_smul_one {R R' : Type} [CommRing R] [CommRing R'] {d : ℕ} (f : R →+* R') (c : R)
    (P : Matrix (Fin d) (Fin d) R) (a b : Fin d) :
    f ((P - c • (1 : Matrix (Fin d) (Fin d) R)) a b) = (P.map f) a b - (f c • (1 : Matrix (Fin d) (Fin d) R')) a b := by
  rcases eq_or_ne a b with rfl | hab
  · simp
  · simp [Matrix.one_apply_ne hab]

theorem mat_approx (bk : BK K) (m : ℕ) {d : ℕ} (x : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) :
    ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ a b,
      toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ (l : bk.DS bk.ρ₀) ^ k * x a b - toDisc l (X : bk.S) bk.ρ₀ (s a b) := by
  choose k s hs using fun p : Fin d × Fin d => GlobalTheory.BKLim.WApprox.exists_congr_pow_E l K bk m (x p.1 p.2)
  refine ⟨∑ p, k p, fun a b => (l : bk.S) ^ (∑ p, k p - k (a, b)) * s (a, b), fun a b => ?_⟩
  have hle : k (a, b) ≤ ∑ p, k p := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (a, b))
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hle
  have hc' : ∑ p, k p - k (a, b) = c := by omega
  show toDisc l (X : bk.S) bk.ρ₀ bk.E ^ m ∣ (l : bk.DS bk.ρ₀) ^ (∑ p, k p) * x a b -
    toDisc l (X : bk.S) bk.ρ₀ ((l : bk.S) ^ (∑ p, k p - k (a, b)) * s (a, b))
  rw [hc', hc, pow_add, map_mul, map_pow, map_natCast]
  have h := dvd_mul_of_dvd_right (hs (a, b)) ((l : bk.DS bk.ρ₀) ^ c)
  convert h using 1
  ring

theorem mat_lift (bk : BK K) (m : ℕ) {d : ℕ} (x : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) :
    ∃ (k : ℕ) (γ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, toDisc l (X : bk.S) bk.ρ₀ bk.E ∣
      toDisc l (X : bk.S) bk.ρ₀ (γ a b) - (l : bk.DS bk.ρ₀) ^ k * x a b) ∧
      ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ Per.σA (g : GQ l) (bk.ev (γ a b)) - bk.ev (γ a b) := by
  obtain ⟨k₀, s, hs⟩ := mat_approx bk 1 x
  obtain ⟨k₁, hk₁⟩ := _root_.GlobalTheory.BSP.BK.exists_inv_lift l K bk m
  choose γ hγ1 hγ2 using fun p : Fin d × Fin d => hk₁ (s p.1 p.2)
  refine ⟨k₁ + k₀, fun a b => γ (a, b), fun a b => ?_, fun g a b => hγ2 (a, b) g⟩
  have h1 := map_dvd (toDisc l (X : bk.S) bk.ρ₀) (hγ1 (a, b))
  have hs1 := hs a b
  rw [pow_one] at hs1
  have h2 := dvd_mul_of_dvd_right hs1 ((l : bk.DS bk.ρ₀) ^ k₁)
  have h3 := dvd_sub h1 h2
  convert h3 using 1
  simp only [map_sub, map_mul, map_pow, map_natCast]
  ring

theorem dvd_gal_E (bk : BK K) (g : GQ l) : bk.ev bk.E ∣ Per.σA g (bk.ev bk.E) := by
  rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
  have h : Per.θ l (bk.ev bk.E) = 0 := by
    rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
  rw [h, map_zero]

theorem dvd_of_iS_dvd (bk : BK K) (s : bk.S) (h : bk.iS bk.E ∣ bk.iS s) : bk.E ∣ s := by
  have h2 : bk.ev bk.E ^ 1 ∣ bk.ev s :=
    (GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk (bk.ev s)).1 1 (by rw [pow_one]; exact h)
  have h3 := (_root_.GlobalTheory.AinfEPow.ePow_facts l K bk 1).2.1 s h2
  rwa [pow_one] at h3

end GlobalTheory.BKLim.BetaDR


open GlobalTheory.BKLim.BetaDR in
theorem GlobalTheory.BKLim.exists_beta_of_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d N : ℕ) (κ : ↥(GK K) → Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (φε : ↥(GK K) → Matrix (Fin d) (Fin d) (Ainf l)) (H : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → IsUnit H → (∀ m : ℕ, ∃ (k : ℕ) (Λ : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (Λ - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∀ a b, bk.iS bk.E ^ m ∣ (κ g * (Λ.map bk.iS).map G - Λ.map bk.iS) a b) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA) = bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) → ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), (∀ a b, bk.E ∣ (β - (l : bk.S) ^ k • (1 : Matrix (Fin d) (Fin d) bk.S)) a b) ∧ ∀ (g : ↥(GK K)) a b, bk.ev bk.E ^ m ∣ (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b := by
  intro l _ K bk d N κ φε H i hi hH hΛ hmain m₀
  obtain ⟨hmap, hgal, -, hρ0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  set m := m₀ + 1 with hm

  obtain ⟨u, hu⟩ := isUnit_toDisc_frobS_E l K bk
  obtain ⟨U, hU⟩ := hH
  set v : bk.DS bk.ρ₀ := ((u⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) with hv
  set H₁ : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := v ^ N • H with hH₁
  set H₁' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀) := (u : bk.DS bk.ρ₀) ^ N • ((U⁻¹ : (Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀))ˣ) : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) with hH₁'
  have hvu : v * (u : bk.DS bk.ρ₀) = 1 := Units.inv_mul u
  have hH11 : H₁ * H₁' = 1 := by
    rw [hH₁, hH₁', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_pow, hvu, one_pow, one_smul, ← hU, Units.mul_inv]
  have hH12 : H₁' * H₁ = 1 := by
    rw [hH₁, hH₁', Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← mul_pow, mul_comm, hvu, one_pow, one_smul, ← hU,
      Units.inv_mul]

  have hmapt : ∀ P : Matrix (Fin d) (Fin d) bk.S, (P.map (toDisc l (X : bk.S) bk.ρ₀)).map i = P.map bk.iS := by
    intro P; ext a b; exact hi.ext _
  set A := H₁.map i with hA
  set A' := H₁'.map i with hA'
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Matrix.map_mul, hH11, Matrix.map_one _ (map_zero i) (map_one i)]
  have hA'A : A' * A = 1 := by rw [hA, hA', ← Matrix.map_mul, hH12, Matrix.map_one _ (map_zero i) (map_one i)]
  have hiv : i v * bk.iS (frobS l bk.a bk.E) = 1 := by
    have e : bk.iS (frobS l bk.a bk.E) = i (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) := (hi.ext _).symm
    rw [e, ← hu, ← map_mul, hvu, map_one]
  have key : ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
      A * (φε g).map bk.iA = κ g * A.map G := by
    intro g G hG
    have hGiv : G (i v) * G (bk.iS (frobS l bk.a bk.E)) = 1 := by rw [← map_mul, hiv, map_one]
    have e1 : A = i v ^ N • H.map i := by rw [hA, hH₁, map_smul_mat, map_pow]
    have e2 : A.map G = G (i v) ^ N • (H.map i).map G := by rw [e1, map_smul_mat, map_pow]
    calc A * (φε g).map bk.iA = i v ^ N • (H.map i * (φε g).map bk.iA) := by rw [e1, Matrix.smul_mul]
      _ = (i v ^ N * G (i v) ^ N) • (G (bk.iS (frobS l bk.a bk.E)) ^ N • (H.map i * (φε g).map bk.iA)) := by
          rw [smul_smul, mul_assoc, ← mul_pow, hGiv, one_pow, mul_one]
      _ = (i v ^ N * G (i v) ^ N) • (bk.iS (frobS l bk.a bk.E) ^ N • (κ g * (H.map i).map G)) := by
          rw [hmain g G hG]
      _ = G (i v) ^ N • (κ g * (H.map i).map G) := by
          rw [smul_smul, mul_comm (i v ^ N), mul_assoc, ← mul_pow, hiv, one_pow, mul_one]
      _ = κ g * A.map G := by rw [e2, Matrix.mul_smul]
  obtain ⟨k₁, Λ, hΛE, hΛinv⟩ := hΛ m
  obtain ⟨k₂, Hs, hHsE, hHsinv⟩ := mat_lift bk m H₁
  obtain ⟨k₃, β, hβ⟩ := mat_approx bk m (H₁' * Λ.map (toDisc l (X : bk.S) bk.ρ₀) * Hs.map (toDisc l (X : bk.S) bk.ρ₀))
  have hM : (H₁' * Λ.map (toDisc l (X : bk.S) bk.ρ₀) * Hs.map (toDisc l (X : bk.S) bk.ρ₀)).map i =
      A' * Λ.map bk.iS * Hs.map bk.iS := by
    rw [Matrix.map_mul, Matrix.map_mul, hmapt, hmapt]
  set L := Λ.map bk.iS with hL
  set Hm := Hs.map bk.iS with hHm
  set B := β.map bk.iS with hB
  have hβD : ∀ a b, bk.iS bk.E ^ m ∣ ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)) a b - B a b := by
    intro a b
    have h := map_dvd i (hβ a b)
    rw [map_pow, hi.ext, map_sub, map_mul, map_pow, map_natCast, hi.ext] at h
    rw [← hM]
    exact h
  refine ⟨k₁ + k₂ + k₃, β, fun a b => ?_, fun g a b => ?_⟩
  · apply dvd_of_iS_dvd bk
    rw [map_entry_sub_smul_one]
    set q := Ideal.Quotient.mk (Ideal.span {bk.iS bk.E}) with hq
    have hE1 : bk.iS bk.E ∣ bk.iS bk.E ^ m := dvd_pow_self _ (by omega)
    have eL : L.map q = (q (l : bk.DA bk.ρ₀) ^ k₁) • 1 := by
      have h : L.map q = ((bk.iS ((l : bk.S) ^ k₁)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))).map q :=
        (map_mk_eq_iff _ _ _).2 fun a b => by rw [← map_entry_sub_smul_one]; exact map_dvd bk.iS (hΛE a b)
      rw [h, map_smul_mat, Matrix.map_one _ (map_zero q) (map_one q)]
      simp only [map_pow, map_natCast]
    have eH : Hm.map q = (q (l : bk.DA bk.ρ₀) ^ k₂) • A.map q := by
      have h : Hm.map q = ((l : bk.DA bk.ρ₀) ^ k₂ • A).map q :=
        (map_mk_eq_iff _ _ _).2 fun a b => by
          have h1 := map_dvd i (hHsE a b)
          rw [hi.ext, map_sub, map_mul, map_pow, map_natCast, hi.ext] at h1
          exact h1
      rw [h, map_smul_mat, map_pow]
    have eB : B.map q = ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map q :=
      ((map_mk_eq_iff _ _ _).2 fun a b => dvd_trans hE1 (hβD a b)).symm
    have hq0 : (bk.iS ((l : bk.S) ^ (k₁ + k₂ + k₃)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))).map q = B.map q := by
      rw [eB, map_smul_mat q, map_smul_mat q, map_mul_three, eL, eH, Matrix.map_one _ (map_zero q) (map_one q)]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
      rw [← Matrix.map_mul, hA'A, Matrix.map_one _ (map_zero q) (map_one q)]
      congr 1
      simp only [map_pow, map_natCast]
      ring
    exact (map_mk_eq_iff _ _ _).1 hq0.symm a b
  · obtain ⟨G, hG⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
    set q := Ideal.Quotient.mk (Ideal.span {bk.iS bk.E ^ m}) with hq
    have hGE : bk.iS bk.E ∣ G (bk.iS bk.E) := by
      obtain ⟨w, hw⟩ := dvd_gal_E bk (g : GQ l)
      show bk.iS bk.E ∣ G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev bk.E))
      rw [hG.ext, hw, map_mul]
      exact dvd_mul_right _ _
    have hGd : ∀ x, bk.iS bk.E ^ m ∣ x → bk.iS bk.E ^ m ∣ G x := by
      rintro x ⟨y, rfl⟩
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hGE m) _
    have hGm : ∀ P P' : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), (∀ a b, bk.iS bk.E ^ m ∣ P a b - P' a b) →
        ∀ a b, bk.iS bk.E ^ m ∣ (P.map G) a b - (P'.map G) a b := by
      intro P P' h a b
      simp only [Matrix.map_apply]
      rw [← map_sub]
      exact hGd _ (h a b)
    have hφA : (φε g).map bk.iA * A'.map G = A' * κ g := by
      have hAG : A.map G * A'.map G = 1 := by
        rw [← Matrix.map_mul, hAA', Matrix.map_one _ (map_zero G) (map_one G)]
      calc (φε g).map bk.iA * A'.map G = A' * (A * (φε g).map bk.iA) * A'.map G := by
            rw [← Matrix.mul_assoc A', hA'A, Matrix.one_mul]
        _ = A' * κ g * (A.map G * A'.map G) := by rw [key g G hG]; simp only [Matrix.mul_assoc]
        _ = A' * κ g := by rw [hAG, Matrix.mul_one]
    have eΛ : (κ g * L.map G).map q = L.map q := (map_mk_eq_iff _ _ _).2 (hΛinv g G hG)
    have eH : (Hm.map G).map q = Hm.map q := (map_mk_eq_iff _ _ _).2 fun a b => by
      have h := map_dvd bk.iA (hHsinv g a b)
      rw [map_pow, map_sub] at h
      have e : G (bk.iS (Hs a b)) = bk.iA (Per.σA (g : GQ l) (bk.ev (Hs a b))) := hG.ext _
      show bk.iS bk.E ^ m ∣ G (bk.iS (Hs a b)) - bk.iS (Hs a b)
      rw [e]
      exact h
    have eB : B.map q = ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map q := ((map_mk_eq_iff _ _ _).2 hβD).symm
    have eBG : (B.map G).map q = (((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map G).map q :=
      ((map_mk_eq_iff _ _ _).2 (hGm _ _ hβD)).symm
    have hid : (φε g).map bk.iA * ((l : bk.DA bk.ρ₀) ^ k₃ • (A' * L * Hm)).map G =
        (l : bk.DA bk.ρ₀) ^ k₃ • (A' * (κ g * L.map G) * Hm.map G) := by
      rw [map_smul_mat, map_pow, map_natCast, map_mul_three, Matrix.mul_smul]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hφA]
      simp only [Matrix.mul_assoc]
    have hfin : ((φε g).map bk.iA * B.map G).map q = B.map q := by
      rw [Matrix.map_mul, eBG, ← Matrix.map_mul, hid, eB, map_smul_mat q _ (A' * (κ g * L.map G) * Hm.map G),
        map_smul_mat q _ (A' * L * Hm), map_mul_three q A' (κ g * L.map G) (Hm.map G), eΛ, eH, map_mul_three q A' L Hm]
    have hdiv := (map_mk_eq_iff _ _ _).1 hfin a b
    have hσ : ((β.map bk.ev).map (Per.σA (g : GQ l))).map bk.iA = B.map G := by
      ext a b
      exact (hG.ext _).symm
    have hmat : (φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev).map bk.iA =
        (φε g).map bk.iA * B.map G - B := by
      rw [map_sub_mat, Matrix.map_mul, hσ]
      rfl
    have h2 : bk.iS bk.E ^ m ∣ bk.iA ((φε g * (β.map bk.ev).map (Per.σA (g : GQ l)) - β.map bk.ev) a b) := by
      have h := congrFun (congrFun hmat a) b
      rw [Matrix.map_apply] at h
      rw [h]
      exact hdiv
    have h3 := (GlobalTheory.BSP.ainf_dvd_of_disc_dvd l K bk _).1 m h2
    exact dvd_trans (pow_dvd_pow _ (by omega)) h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspidalCharacterOfRegularCharacterGLn
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial GlobalTheory.CuspGL
open scoped Classical

noncomputable section

namespace GlobalTheory.GreenRegular

theorem pow_modEq_pow_mod {g : ℕ} (d : ℕ) (hg : 0 < g) (m : ℕ) : g ^ m ≡ g ^ (m % d) [MOD g ^ d - 1] := by
  have h1 : g ^ d ≡ 1 [MOD g ^ d - 1] := Nat.modEq_sub (Nat.one_le_pow _ _ hg)
  conv_lhs => rw [← Nat.div_add_mod m d, pow_add, pow_mul]
  calc (g ^ d) ^ (m / d) * g ^ (m % d) ≡ 1 ^ (m / d) * g ^ (m % d) [MOD g ^ d - 1] :=
        (h1.pow _).mul_right _
    _ = g ^ (m % d) := by rw [one_pow, one_mul]

theorem filter_modEq_congr {g d a b l : ℕ} (h : a ≡ b [MOD g ^ d - 1]) :
    ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]) =
      (Finset.range d).filter fun i => b * g ^ i ≡ l [MOD g ^ d - 1] :=
  Finset.filter_congr fun i _ =>
    ⟨fun h' => ((h.symm.mul_right _).trans h'), fun h' => ((h.mul_right _).trans h')⟩

theorem card_filter_le_shift {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a c l : ℕ) :
    ((Finset.range d).filter fun i => a * g ^ c * g ^ i ≡ l [MOD g ^ d - 1]).card ≤
      ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]).card := by
  refine Finset.card_le_card_of_injOn (fun i => (i + c) % d) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
    refine ⟨Nat.mod_lt _ hd, ?_⟩
    refine ((pow_modEq_pow_mod d hg (i + c)).symm.mul_left a).trans ?_
    rw [pow_add, mul_comm (g ^ i), ← mul_assoc]
    exact hi.2
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi hj
    have h1 : i + c ≡ j + c [MOD d] := hij
    have h2 := Nat.ModEq.add_right_cancel' c h1
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hi.1, Nat.mod_eq_of_lt hj.1] at h2

theorem card_filter_shift {g d : ℕ} (hg : 0 < g) (hd : 0 < d) (a c l : ℕ) (hc : c ≤ d) :
    ((Finset.range d).filter fun i => a * g ^ c * g ^ i ≡ l [MOD g ^ d - 1]).card =
      ((Finset.range d).filter fun i => a * g ^ i ≡ l [MOD g ^ d - 1]).card := by
  refine le_antisymm (card_filter_le_shift hg hd a c l) ?_
  have e : a ≡ a * g ^ c * g ^ (d - c) [MOD g ^ d - 1] := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hc]
    calc a = a * 1 := (mul_one a).symm
      _ ≡ a * g ^ d [MOD g ^ d - 1] := (Nat.modEq_sub (Nat.one_le_pow _ _ hg)).symm.mul_left a
  rw [filter_modEq_congr e]
  exact card_filter_le_shift hg hd (a * g ^ c) (d - c) l

end GlobalTheory.GreenRegular

namespace GlobalTheory.GreenRegular

theorem exists_cusp_of_regular : ∀ (g : ℕ) [Fact g.Prime] (d : ℕ), 0 < d → ∀ (K : Type) [Field K] [Algebra (ZMod g) K],
    Module.finrank (ZMod g) K = d → ∃ τ : (Kˣ →* ℂˣ) → Gn g d → ℂ,
      (∀ θ, IsRegularChar g d θ → IsCusp (τ θ) ∧ τ θ 1 = ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1) ∧
        ∀ y : Gn g d, Irreducible (y : Mt g d).charpoly → ∀ z : Kˣ, aeval (z : K) (y : Mt g d).charpoly = 0 →
          τ θ y = (-1) ^ (d - 1) * ∑ i ∈ Finset.range d, ((θ (z ^ g ^ i) : ℂˣ) : ℂ)) ∧
      (∀ θ θ', IsRegularChar g d θ → IsRegularChar g d θ' → (τ θ = τ θ' ↔ ∃ i < d, θ' = θ ^ g ^ i)) := by
  intro g _ d hd K _ _ hK
  have hgp : g.Prime := Fact.out
  have hg : 0 < g := hgp.pos
  have hcF : Nat.card (ZMod g) = g := Nat.card_zmod g
  haveI : FiniteDimensional (ZMod g) K := Module.finite_of_finrank_pos (by rw [hK]; exact hd)
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hcardK : Fintype.card K = g ^ d := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hK]
  have hcardU : Nat.card Kˣ = g ^ d - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcardK]
  have hN0 : 0 < g ^ d - 1 := by
    have := Nat.one_lt_pow hd.ne' hgp.one_lt
    omega
  obtain ⟨θ₀, hθ₀⟩ := _root_.GlobalTheory.CuspGL.TeichEmb.exists_teichmuller (ZMod g)
  let ι : K →ₐ[ZMod g] AlgebraicClosure (ZMod g) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let lam : Kˣ →* ℂˣ := (Units.map θ₀).comp (Units.map (ι : K →* AlgebraicClosure (ZMod g)))
  have hlam : ∀ u : Kˣ, ((lam u : ℂˣ) : ℂ) = θ₀ (ι (u : K)) := fun u => rfl
  have hlam_inj : Function.Injective lam := by
    intro u v h
    have h' := congrArg Units.val h
    rw [hlam, hlam] at h'
    exact Units.ext (ι.injective (hθ₀ _ _ ((map_ne_zero ι).2 u.ne_zero) ((map_ne_zero ι).2 v.ne_zero) h'))
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hprim : IsPrimitiveRoot (lam γ) (g ^ d - 1) := by
    rw [← hcardU, ← orderOf_eq_card_of_forall_mem_zpowers hγ, ← orderOf_injective lam hlam_inj γ]
    exact IsPrimitiveRoot.orderOf _
  have hmod : ∀ u : Kˣ, u ^ (g ^ d - 1) = 1 := fun u => by
    rw [← hcardU]; exact pow_card_eq_one'
  have hpow_eq : ∀ a b : ℕ, lam ^ a = lam ^ b ↔ a ≡ b [MOD g ^ d - 1] := by
    intro a b
    constructor
    · intro h
      have h1 := congrArg (fun f : Kˣ →* ℂˣ => f γ) h
      simp only [MonoidHom.pow_apply] at h1
      rwa [pow_eq_pow_iff_modEq, ← hprim.eq_orderOf] at h1
    · intro h
      refine MonoidHom.ext fun u => ?_
      rw [MonoidHom.pow_apply, MonoidHom.pow_apply, pow_eq_pow_iff_modEq]
      exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hmod, map_one])) h
  have hpow : ∀ θ : Kˣ →* ℂˣ, ∃ k, θ = lam ^ k := by
    intro θ
    have h1 : θ γ ^ (g ^ d - 1) = 1 := by rw [← map_pow, hmod, map_one]
    haveI : NeZero (g ^ d - 1) := ⟨hN0.ne'⟩
    have h1' : ((θ γ : ℂˣ) : ℂ) ^ (g ^ d - 1) = 1 := by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one]
    obtain ⟨k, -, hk0⟩ := (IsPrimitiveRoot.coe_units_iff.2 hprim).eq_pow_of_pow_eq_one h1'
    have hk : lam γ ^ k = θ γ := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk0)
    refine ⟨k, MonoidHom.ext fun u => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hγ u)
    rw [map_zpow, map_zpow, MonoidHom.pow_apply, hk]
  let kOf : (Kˣ →* ℂˣ) → ℕ := fun θ => (hpow θ).choose
  have hkOf : ∀ θ, θ = lam ^ kOf θ := fun θ => (hpow θ).choose_spec
  have hreg : ∀ θ, IsRegularChar g d θ → ∀ i : ℕ, 0 < i → i < d →
      ¬ kOf θ * Nat.card (ZMod g) ^ i ≡ kOf θ [MOD Nat.card (ZMod g) ^ d - 1] := by
    intro θ hθ i hi hid hc
    rw [hcF] at hc
    have e : θ ^ g ^ i = θ ^ g ^ 0 := by
      rw [hkOf θ, ← pow_mul, ← pow_mul, pow_zero, mul_one]
      exact (hpow_eq _ _).2 hc
    exact absurd (hθ i 0 hid hd e) hi.ne'
  have hadd : ∀ k, IsAdditive (rootSum θ₀ k) := fun k => (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one (ZMod g) θ₀ k).1
  have hfr : 0 < Module.finrank (ZMod g) (Fin d → ZMod g) := by rw [Module.finrank_fin_fun]; exact hd
  refine ⟨fun θ x => (-1) ^ (d - 1) *
    psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) (ZMod g))),
    fun θ hθ => ⟨?_, ?_, ?_⟩, fun θ θ' hθ hθ' => ?_⟩
  · exact GlobalTheory.ParamLabel.isCusp_psi θ₀ hθ₀ hd (hreg θ hθ)
  · show (-1) ^ (d - 1) * psi _ _ (Matrix.toLin' ((1 : Gn g d) : Matrix (Fin d) (Fin d) (ZMod g))) = _
    have h1 := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico (ZMod g) (Fin d → ZMod g) (rootSum θ₀ (kOf θ)) (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one (ZMod g) θ₀ (kOf θ)).2 hfr
    rw [Units.val_one, Matrix.toLin'_one, ← Module.End.one_eq_id, h1, Module.finrank_fin_fun, hcF,
      show ((-1 : ℂ)) ^ (d - 1) = ∏ i ∈ Finset.Ico 1 d, (-1 : ℂ) by rw [Finset.prod_const, Nat.card_Ico],
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  · intro y hy z hz
    show (-1) ^ (d - 1) * psi _ _ _ = _
    have h := _root_.GlobalTheory.CuspGL.psi_of_irreducible_charpoly (ZMod g) (Fin d → ZMod g) _ (hadd (kOf θ)) (Matrix.toLin' (y : Mt g d))
      (by rw [Matrix.charpoly_toLin']; exact hy)
    rw [h, Matrix.charpoly_toLin']
    congr 1
    have hz' : aeval (ι (z : K)) (y : Mt g d).charpoly = 0 := by rw [aeval_algHom_apply, hz, map_zero]
    have hnd : (y : Mt g d).charpoly.natDegree = d := by simp
    change ((Formalism.CyclotomicNorms.rootsBar _).map _).sum = _
    rw [GlobalTheory.GreenExists.rootsBar_eq hy hz', hnd, Multiset.map_map, Finset.sum_eq_multiset_sum]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    conv_rhs => rw [hkOf θ]
    show θ₀ (ι ↑z ^ g ^ i) ^ kOf θ = _
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hlam, Units.val_pow_eq_pow_val, map_pow ι]
  · have hsign : ((-1 : ℂ) ^ (d - 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
    have hunit : ∀ G : Module.End (ZMod g) (Fin d → ZMod g), IsUnit G →
        ∃ x : Gn g d, Matrix.toLin' (x : Mt g d) = G := by
      intro G hG
      have hM : IsUnit (LinearMap.toMatrix' G) :=
        hG.map (LinearMap.toMatrixAlgEquiv' : Module.End (ZMod g) (Fin d → ZMod g) ≃ₐ[ZMod g] Mt g d)
      exact ⟨hM.unit, by rw [IsUnit.unit_spec, Matrix.toLin'_toMatrix']⟩
    have hxU : ∀ x : Gn g d, IsUnit (Matrix.toLin' (x : Mt g d)) := fun x =>
      x.isUnit.map (Matrix.toLinAlgEquiv' : Mt g d ≃ₐ[ZMod g] Module.End (ZMod g) (Fin d → ZMod g))
    have heqU : ∀ k k' : ℕ, (∀ x : Gn g d, psi (rootSum θ₀ k) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
        psi (rootSum θ₀ k') (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d))) → ∀ l : ℕ,
        ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) =
          ipGL (psi (rootSum θ₀ k') (Fin d → ZMod g)) (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
      intro k k' h l
      refine finsum_mem_congr rfl fun G hG => ?_
      obtain ⟨x, rfl⟩ := hunit G hG
      rw [h x]
    have hgram : ∀ k l : ℕ, ipGL (psi (rootSum θ₀ k) (Fin d → ZMod g))
        (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = glCard (ZMod g) d *
          (((Finset.range d).filter fun i => k * g ^ i ≡ l [MOD g ^ d - 1]).card : ℂ) := by
      intro k l
      have h := GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ hfr k l
      rwa [Module.finrank_fin_fun, hcF] at h
    have hGL : glCard (ZMod g) d ≠ 0 := by
      unfold glCard
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    constructor
    · intro hτ
      have hx : ∀ x : Gn g d, psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) =
          psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g) (Matrix.toLin' (x : Mt g d)) :=
        fun x => mul_left_cancel₀ hsign (congrFun hτ x)
      have e1 := heqU _ _ hx (kOf θ')
      rw [hgram, hgram] at e1
      have h2 := mul_left_cancel₀ hGL e1
      have hmem : 0 ∈ (Finset.range d).filter fun i => kOf θ' * g ^ i ≡ kOf θ' [MOD g ^ d - 1] := by
        rw [Finset.mem_filter, Finset.mem_range, pow_zero, mul_one]
        exact ⟨hd, Nat.ModEq.refl _⟩
      have hne : ((Finset.range d).filter fun i => kOf θ * g ^ i ≡ kOf θ' [MOD g ^ d - 1]).Nonempty := by
        rw [← Finset.card_pos]
        refine Nat.pos_of_ne_zero fun h0 => ?_
        have h3 := (Finset.card_pos.2 ⟨0, hmem⟩).ne'
        rw [h0, Nat.cast_zero] at h2
        exact h3 (by exact_mod_cast h2.symm)
      obtain ⟨i, hi⟩ := hne
      rw [Finset.mem_filter, Finset.mem_range] at hi
      refine ⟨i, hi.1, ?_⟩
      rw [hkOf θ', hkOf θ, ← pow_mul]
      exact ((hpow_eq _ _).2 hi.2).symm
    · rintro ⟨i, hi, hθi⟩
      have hk : kOf θ' ≡ kOf θ * g ^ i [MOD g ^ d - 1] := by
        rw [← hpow_eq, pow_mul, ← hkOf θ, ← hkOf θ']
        exact hθi
      funext x
      refine congrArg (fun t : ℂ => (-1 : ℂ) ^ (d - 1) * t) ?_
      have hcl : ∀ k : ℕ, IsClassFn (psi (rootSum θ₀ k) (Fin d → ZMod g)) := fun k e G =>
        _root_.GlobalTheory.CuspGL.psi_conj (ZMod g) _ _ _ e G
      have hexp := fun k : ℕ => GlobalTheory.T.primitiveClassFunction_expansion_rootSums (ZMod g) (Fin d → ZMod g) θ₀ hθ₀ _ (hcl k)
        (_root_.GlobalTheory.CuspGL.isPrimitive_psi (ZMod g) (Fin d → ZMod g) _ (hadd k)) hfr _ (hxU x)
      have e1 := hexp (kOf θ)
      have e2 := hexp (kOf θ')
      rw [Module.finrank_fin_fun, hcF] at e1 e2
      have hsum : ∀ l : ℕ, ipGL (psi (rootSum θ₀ (kOf θ)) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) = ipGL (psi (rootSum θ₀ (kOf θ')) (Fin d → ZMod g))
          (fun G => rootSum θ₀ l (LinearMap.charpoly G)) := by
        intro l
        rw [hgram, hgram, filter_modEq_congr hk, card_filter_shift hg hd _ _ _ hi.le]
      rw [Finset.sum_congr rfl fun l _ => by rw [hsum l]] at e1
      exact mul_left_cancel₀ (mul_ne_zero hGL (Nat.cast_ne_zero.2 hd.ne')) (e1.trans e2.symm)

end GlobalTheory.GreenRegular
end
end

