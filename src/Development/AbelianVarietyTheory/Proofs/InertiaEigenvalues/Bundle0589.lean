module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0550
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0577
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStable
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalStab

section Alg
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_mul_eq_smul [IsDomain R] {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • 1) :
    A.det ≠ 0 := by
  have hd : A.det * B.det = c ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ hc hd.symm

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom {R' : Type} [CommRing R'] (f : R →+* R') (c : R) (M : Matrix n n R) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp

end Alg

theorem smul_cancel_of_isUnit {R : Type} [CommRing R] {n : Type} {c : R} (hc : IsUnit c) {M M' : Matrix n n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem gal_E (bk : BK K) (g : GQ l) : ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem frob_zl (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact map_zlW l _ z

theorem frob_Y (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d N : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Pre bk N d ρ) (M : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ M • F.T) :
    bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * F.A.map bk.ev) := by
  apply Matrix.map_injective inclW_injective
  beta_reduce
  have hfτ : frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ := by rw [frobW_inclW, hτ.1, map_mul]
  have h1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
    ext i j; simp only [Matrix.map_apply, frobW_inclW]
  have hA : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by rw [Matrix.map_map]; rfl
  have hφ : inclW l (bk.ev bk.E) ^ N • F.T.map (frobW l) = F.T * F.A.map bk.evW := F.φ
  have h2 : (inclW l τ ^ M • F.T).map (frobW l) = (inclW l (bk.ev bk.E) * inclW l τ) ^ M • F.T.map (frobW l) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hfτ]
  rw [map_smul_hom, map_smul_hom, h1, Matrix.map_mul, hY, h2, hA, Matrix.smul_mul,
    ← hφ, smul_smul, smul_smul, smul_smul, map_pow, map_pow]
  congr 1
  ring

theorem disc_cocycle (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀))
    (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hZ : IsUnit Z) (hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i) (hWZ : s.W * Z.map i = Y.map bk.iA)
    (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G) :
    ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀),
      G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) =
        bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧
      bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) =
        bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) :=
  GlobalTheory.T.exists_semistable_disc_cocycle l K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG

theorem frob_eq (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} (M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A A' : Matrix (Fin d) (Fin d) bk.S) (hA : A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S))
    (hφ : bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev))
    (hdet : (Y.map bk.iA).det ≠ 0) (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G)
    (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ) (w : (Ainf l)ˣ) (hw : Per.σA g (bk.ev bk.E) = bk.ev bk.E * w)
    (P : Matrix (Fin d) (Fin d) (Ainf l)) (hP : P.map WittVector.frobenius = P)
    (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
    (he : bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA)) :
    bk.iS bk.E ^ (2 * N) • e =
      (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA :=
  GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation l K bk τ hτ d M N Y A A' hA hφ hdet g G Φ hG hΦ w hw P hP e he

theorem bounded (bk : BK K) {d : ℕ} (h : ℕ) (C B : Matrix (Fin d) (Fin d) (Ainf l))
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ) (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
    (he : bk.iS bk.E ^ h • e = C.map bk.iA * e.map Φ * B.map bk.iA) :
    ∃ (k : ℕ) (v : Matrix (Fin d) (Fin d) (Ainf l)), v.map bk.iA = (l : bk.DA bk.ρ₀) ^ k • e := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hφX : WittVector.frobenius (bk.ev X) = bk.ev X ^ l := by rw [← bk.ev_frob, frobS_X, map_pow]
  have hj : ∀ j : Fin d × Fin d, HasSum (fun x : Fin d × Fin d => Φ (e x.1 x.2) * bk.iA (C j.1 x.1 * B x.2 j.2))
      (bk.iS bk.E ^ h * e j.1 j.2) := by
    intro j
    convert hasSum_fintype _ using 1
    have := congrFun (congrFun he j.1) j.2
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] at this
    rw [this, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul]; ring
  obtain ⟨k, v, hv, -⟩ := GlobalTheory.BSP.exists_bounded_of_phi_equation l K bk (Ainf l) bk.ev ι tb WittVector.frobenius hφX
    Φ hΦ (Fin d × Fin d) (fun x j => C j.1 x.1 * B x.2 j.2) (fun _ _ => Set.toFinite _) h
    (fun x => e x.1 x.2) (by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot) hj
  refine ⟨k, Matrix.of fun a b => v (a, b), ?_⟩
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (a, b)

theorem descend (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} (M k : ℕ) (Y v : Matrix (Fin d) (Fin d) (Ainf l))
    (T : Matrix (Fin d) (Fin d) (WCb l)) (hT : IsUnit T) (hY : Y.map (inclW l) = inclW l τ ^ M • T) (g : GQ l)
    (P : Matrix (Fin d) (Fin d) ℤ_[l])
    (hv : Per.σA g τ ^ M • (Y * v) =
      (l : Ainf l) ^ k • τ ^ M • (P.map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA g))) :
    ∃ a : Matrix (Fin d) (Fin d) (Ainf l), P.map (algebraMap ℤ_[l] (WCb l)) * T.map (galW l g) = T * a.map (inclW l) ∧
      (l : Ainf l) ^ k • a = v := by
  have hτu := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hTd : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  set P' := P.map (algebraMap ℤ_[l] (WCb l)) with hP'
  have hPA : (P.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = P' := by
    exact Matrix.ext fun i j => (inclWA l).commutes (P i j)
  have hgY : (Y.map (Per.σA g)).map (inclW l) = inclW l (Per.σA g τ) ^ M • T.map (galW l g) := by
    have : (Y.map (Per.σA g)).map (inclW l) = (Y.map (inclW l)).map (galW l g) := by
      ext i j; simp only [Matrix.map_apply, galW_inclW]
    rw [this, hY]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, galW_inclW]
  have hW := congrArg (fun M => M.map (inclW l)) hv
  beta_reduce at hW
  rw [map_smul_hom, map_smul_hom, map_smul_hom, Matrix.map_mul, Matrix.map_mul, hY, hPA, hgY, map_pow, map_pow, map_pow,
    map_natCast] at hW
  have hu : IsUnit (inclW l (Per.σA g τ) ^ M * inclW l τ ^ M) := ((hτu.2.2.2 g).pow M).mul (hτu.1.pow M)
  have hW2 : T * v.map (inclW l) = T * ((l : WCb l) ^ k • (T⁻¹ * (P' * T.map (galW l g)))) := by
    apply smul_cancel_of_isUnit hu
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun hW i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_smul] at this ⊢
    linear_combination this
  have hW3 : v.map (inclW l) = (l : WCb l) ^ k • (T⁻¹ * (P' * T.map (galW l g))) := by
    have := congrArg (fun M => T⁻¹ * M) hW2
    beta_reduce at this
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul, Matrix.one_mul] at this
  have hx : ∀ i j, ∃ a : Ainf l, (T⁻¹ * (P' * T.map (galW l g))) i j = inclW l (1 * a) ∧ (l : Ainf l) ^ k * a = v i j := by
    intro i j
    have hij : (l : WCb l) ^ k * (T⁻¹ * (P' * T.map (galW l g))) i j = inclW l (v i j) := by
      have := congrFun (congrFun hW3 i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.AinfSat.mem_ideal_of_saturated l 1 (by rw [map_one]; exact isUnit_one) k _
      (fun n => ⟨v i j, by rw [hij, one_mul, sub_self]; exact dvd_zero _⟩)
    refine ⟨a, ha, inclW_injective ?_⟩
    rw [map_mul, map_pow, map_natCast, ← hij, ha, one_mul]
  choose a ha1 ha2 using hx
  refine ⟨Matrix.of a, ?_, ?_⟩
  · have : (Matrix.of a).map (inclW l) = T⁻¹ * (P' * T.map (galW l g)) := by
      exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.of_apply, ha1, one_mul]
    rw [this, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
  · exact Matrix.ext fun i j => by simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ha2]

theorem galois_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → ∃ F₀ : Frame bk N d ρ, F₀.toPre = F ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F₀.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
  intro l _ K bk τ hτ d ρ hρ s N F Y Z hY hZ hWZ
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨hmaps, hgal, -, hρ0, hρ1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ hρ0 hρ1).1
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ hρ0 hρ1).1
  obtain ⟨i₀, hi₀⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Φ, hΦ⟩ := hmaps (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0
    (by rw [pow_one, ← bk.ev_frob, frobS_X, map_pow]; exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero) (by rw [pow_one])
  have hτu := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hYφ := frob_Y bk hτ F s.N Y hY
  have hdet : (Y.map bk.iA).det ≠ 0 := by
    rw [← hWZ i₀ hi₀, Matrix.det_mul]
    refine mul_ne_zero (det_ne_zero_of_mul_eq_smul (pow_ne_zero _ hτu.2.1) s.W_mul) ?_
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hZ.map (RingHom.mapMatrix i₀))).ne_zero
  have key : ∀ g : ↥(GK K), ∃ a : Matrix (Fin d) (Fin d) (Ainf l),
      zW (ρ g) * F.T.map (galW l (g : GQ l)) = F.T * a.map (inclW l) ∧
      ∀ (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
        IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * a.map bk.iA) =
          bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
    intro g
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
    obtain ⟨e, heA, heD⟩ := disc_cocycle bk hτ s Y Z i₀ hZ hi₀ (hWZ i₀ hi₀) g G hG
    obtain ⟨w, hw⟩ := gal_E bk (g : GQ l)
    have hP : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map WittVector.frobenius =
        (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
      ext i j; simp only [Matrix.map_apply, frob_zl]
    have hφe := frob_eq bk hτ s.N N Y F.A F.A' F.A_mul hYφ hdet (g : GQ l) G Φ hG hΦ w hw _ hP e heD
    obtain ⟨k, v, hv⟩ := bounded bk (2 * N) _ _ Φ hΦ e hφe
    have hvA : Per.σA (g : GQ l) τ ^ s.N • (Y * v) = (l : Ainf l) ^ k • τ ^ s.N •
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) := by
      apply Matrix.map_injective hinj
      beta_reduce
      simp only [map_smul_hom, Matrix.map_mul, hv, map_pow, map_natCast]
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, heD, smul_comm]
    obtain ⟨a, ha1, ha2⟩ := descend bk hτ s.N k Y v F.T F.unit hY (g : GQ l) (ρ g) hvA
    have hae : a.map bk.iA = e := by
      refine smul_cancel_of_isUnit ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k) ?_
      rw [← hv, ← ha2, map_smul_hom, map_pow, map_natCast]
    refine ⟨a, ha1, fun G' i hG' hi => ?_⟩
    rw [hG'.unique hG, hi.unique hi₀, hae]
    exact heA
  choose ε hε using key
  exact ⟨{ F with ε := ε, gal := fun g => (hε g).1 }, rfl, fun g G i hG hi => (hε g).2 G i hG hi⟩

end GlobalTheory.BKLim.GalStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralFundamentalDomainEqMassMulAverage
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

theorem setIntegral_eq_mass_mul_avg : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] (Γ : AddSubgroup G), IsCoLat Γ → ∀ [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ Φ : G → ℂ, Per Γ Φ → μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ IntegrableOn Φ 𝓕 μ ∧ ∫ x in 𝓕, Φ x ∂μ = ((μ 𝓕).toReal : ℂ) * avg Γ Φ := by
  intro G _ _ _ _ _ _ Γ hΓ mG hB μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hd, K, hK, hcov⟩ := hΓ
  have e := hB.measurable_eq
  subst e
  letI : MeasurableSpace G := borel G
  haveI : Countable Γ := countable_of_discrete_addSubgroup Γ
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.1.continuousOn
  have hb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    have := hC _ hk
    rwa [hΦ.2 γ hγ] at this
  have hint : IntegrableOn Φ 𝓕 μ :=
    Measure.integrableOn_of_bounded hfin hΦ.1.aestronglyMeasurable (M := C) (Filter.Eventually.of_forall hb)
  refine ⟨hne, hfin, hint, ?_⟩
  have hex := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact G Γ K hK hcov).1
  have hex' : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 := by
    obtain ⟨μ₀, F₀, h⟩ := hex
    exact ⟨(μ₀, F₀), h⟩
  have hav : avg Γ Φ = ∫ x in hex'.choose.2, Φ x ∂hex'.choose.1 := by
    simp only [avg]
    rw [dite_eq_left hex']
  rw [hav]
  obtain ⟨hμ₀, hF₀, h1⟩ := hex'.choose_spec
  generalize hex'.choose = p at hμ₀ hF₀ h1 ⊢
  obtain ⟨μ₀, F₀⟩ := p
  simp only at hμ₀ hF₀ h1 ⊢
  obtain ⟨c, hc⟩ : ∃ c : NNReal, μ = c • μ₀ := ⟨_, Measure.isAddLeftInvariant_eq_smul μ μ₀⟩
  have hac : μ ≪ μ₀ := hc ▸ Measure.smul_absolutelyContinuous
  have hF₀' : IsAddFundamentalDomain Γ F₀ μ := hF₀.mono hac
  have e1 : μ 𝓕 = μ F₀ := h𝓕.measure_eq hF₀'
  have e2 : ∫ x in 𝓕, Φ x ∂μ = ∫ x in F₀, Φ x ∂μ :=
    h𝓕.setIntegral_eq hF₀' fun g x => hΦ.2 g g.2 x
  rw [e1, e2, hc, Measure.restrict_smul, integral_smul_nnreal_measure, Measure.smul_apply, h1]
  simp [ENNReal.smul_def, NNReal.smul_def]

end GlobalTheory.CuspGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobenius
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frob_coord_compat {C : Type} [CommRing C] {d d' : ℕ} (φ : C →+* C) (E T : C) (hE : E ∈ nonZeroDivisors C)
    (A : Matrix (Fin d) (Fin d) C) (A' : Matrix (Fin d') (Fin d') C) (Y : Matrix (Fin d') (Fin d) C)
    (a a' r r' k j : ℕ) (hY : E ^ a • (A' * Y.map φ) = E ^ a' • (Y * A)) (u m : Fin d → C) (n : Fin d' → C)
    (h1 : T ^ r • (E ^ a • m - T ^ k • A.mulVec fun i => φ (u i)) = 0)
    (h2 : T ^ r' • (E ^ a' • n - T ^ j • A'.mulVec fun i => φ (Y.mulVec u i)) = 0) :
    T ^ (r + r') • (T ^ k • n) = T ^ (r + r') • (T ^ j • Y.mulVec m) := by
  have e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_mulVec] at h2
  have h3 := congrArg Y.mulVec h1
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY
  simp only [Matrix.smul_mulVec] at h4
  funext i
  have h2i := congrFun h2 i
  have h3i := congrFun h3 i
  have h4i := congrFun h4 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢
  rw [← sub_eq_zero]
  refine (mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_
  linear_combination (T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i +
    T ^ (r + r' + k + j) * h4i

theorem eval_map_Φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  intro l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx
  refine (_root_.GlobalTheory.BSP.exists_cover_receiving_bk l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_
  have hc := hC.2
  have hinj := (_root_.GlobalTheory.BSP.Eval.effective_of_cover l K bk d' S' B C (M'.M B) V' h g hc).1
  have hE := (_root_.GlobalTheory.BSP.hf_E_span_and_regular l K bk C g).2
  have hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j := by
    induction M'.Φ B t (w x) using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨_, j, rfl⟩ := s
      exact ⟨n, j, rfl⟩
  refine hnj.elim fun n hn => hn.elim fun j hn => ?_
  refine (_root_.GlobalTheory.BSP.coord_frobenius l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_
  refine (_root_.GlobalTheory.BSP.coord_frobenius l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_
  rw [hw] at h2
  have hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) =
      BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    have e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g) := by
      ext i j
      exact (g.f_φ (Y i j)).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have h5 := congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply] using h5
  have key := frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2
  unfold IsFrac at hn ⊢
  rw [hn, LocalizedModule.mk_eq]
  refine ⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩
  simp only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]
  exact key

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelope
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem strat_defect_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} (S : Strat bk d)
    (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S) {B C : Obj l ↥(OL K)} (σ : Hom B C)
    (f g : Hom bk.prism B) :
    (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map σ.f =
      S'.ε (σ.comp f) (σ.comp g) * Y.map (BK.hf (σ.comp g)) -
        Y.map (BK.hf (σ.comp f)) * S.ε (σ.comp f) (σ.comp g) := by
  have e1 : (Y.map (BK.hf g)).map σ.f = Y.map (BK.hf (σ.comp g)) := rfl
  have e2 : (Y.map (BK.hf f)).map σ.f = Y.map (BK.hf (σ.comp f)) := rfl
  have m1 := Matrix.map_mul (L := S'.ε f g) (M := Y.map (BK.hf g)) (f := σ.f)
  have m2 := Matrix.map_mul (L := Y.map (BK.hf f)) (M := S.ε f g) (f := σ.f)
  rw [Matrix.map_sub _ (map_sub σ.f), m1, m2, S'.ε_nat, S.ε_nat, e1, e2]

theorem matrix_phi_eq_family_self (C : Type) [CommRing C] (φ : C → C) (e e' : C) (he : Associated e e')
    (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') C) (Q Q' : Matrix (Fin d) (Fin d) C)
    (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) C)) (Δ : Matrix (Fin d') (Fin d) C)
    (h : e' ^ a • (P * Δ.map φ) = e ^ a' • (Δ * Q)) :
    ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → C), ∀ j : Fin d' × Fin d,
      e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * c k j :=
  _root_.GlobalTheory.BSP.matrix_phi_eq_family C C (RingHom.id C) φ e e' he d d' a a' b P Q Q' hQ Δ h

theorem obj_eq_zero_of_pow_dvd {l : ℕ} [Fact l.Prime] {K : FinExt l} (B : Obj l ↥(OL K)) (x : B.A)
    (hk : ∀ k : ℕ, ((l : ℕ) : B.A) ^ k ∣ x) : x = 0 := by
  refine B.complete.toIsHausdorff.haus _ fun n => ?_
  obtain ⟨y, hy⟩ := hk n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

theorem strat_map_A_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d)
    {B : Obj l ↥(OL K)} (g : Hom bk.prism B) :
    S.A.map (BK.hf g) * S.A'.map (BK.hf g) = BK.hf g bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
  rw [← Matrix.map_mul, S.A_mul]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem env_matrix_eq_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K}
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) {d d' : ℕ} (S : Strat bk d) (S' : Strat bk d')
    (Δ : Matrix (Fin d') (Fin d) En.Q.A)
    (h1 : BK.hf En.inr bk.E ^ S.a • (S'.A.map (BK.hf En.inl) * Δ.map En.Q.D.φ) =
      BK.hf En.inl bk.E ^ S'.a • (Δ * S.A.map (BK.hf En.inr)))
    (hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι → Δ.map σ.f = 0) : Δ = 0 := by
  have hass := (_root_.GlobalTheory.BSP.hf_E_pair l K bk En.Q En.inl En.inr).2.1
  obtain ⟨h, c, hc⟩ := matrix_phi_eq_family_self En.Q.A En.Q.D.φ _ _ hass d d' S.a S'.a S.b
    (S'.A.map (BK.hf En.inl)) _ _ (strat_map_A_mul S En.inr) Δ h1
  refine Matrix.ext fun i j => obj_eq_zero_of_pow_dvd En.Q (Δ i j) fun k => ?_
  refine _root_.GlobalTheory.envelope_dvd_lpow_of_sections l K bk En (Fin d' × Fin d) c h k (fun p => Δ p.1 p.2) hc ?_ (i, j)
  intro g σ ha hb p
  have h0 : σ.f (Δ p.1 p.2) = 0 := congrFun (congrFun (hσ g σ ha hb) p.1) p.2
  exact ⟨0, h0.trans (mul_zero _).symm⟩

theorem strat_eps_compat_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S)
    (hφ : bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A))
    (hg : ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) =
      Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) :
    S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  have h1 := GlobalTheory.T.stratifiedHom_defect_frobenius_equation l K bk d d' S S' Y hφ En.Q En.inl En.inr
  have hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι →
      (S'.ε En.inl En.inr * Y.map (BK.hf En.inr) - Y.map (BK.hf En.inl) * S.ε En.inl En.inr).map σ.f = 0 := by
    intro g σ ha hb
    rw [strat_defect_map, ha, hb, hg g, sub_self]
  exact sub_eq_zero.1 (env_matrix_eq_zero En S S' _ h1 hσ)

end GlobalTheory.BSP
end

