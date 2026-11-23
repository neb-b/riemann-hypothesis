module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0355
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaConjBoundedCompatibleBreuilKisinFrames
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.HTBound

section mat
variable {𝕜 : Type*} [NormedField 𝕜] [IsUltrametricDist 𝕜] {m n k : Type*} [Fintype n]

theorem nsub_max (x y : 𝕜) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

theorem bnd_mul {A : Matrix m n 𝕜} {B : Matrix n k 𝕜} {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ s) : ∀ i j, ‖(A * B) i j‖ ≤ r * s := by
  intro i j
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hr hs) fun x _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA _ _) (hB _ _) (norm_nonneg _) hr

theorem bnd_add {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A + B) i j‖ ≤ r := fun i j =>
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_sub {A B : Matrix m k 𝕜} {r : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ r) (hB : ∀ i j, ‖B i j‖ ≤ r) :
    ∀ i j, ‖(A - B) i j‖ ≤ r := fun i j =>
  (nsub_max _ _).trans (max_le (hA i j) (hB i j))

theorem bnd_smul {A : Matrix m k 𝕜} {r : ℝ} (a : 𝕜) (hA : ∀ i j, ‖A i j‖ ≤ r) :
    ∀ i j, ‖(a • A) i j‖ ≤ ‖a‖ * r := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hA i j) (norm_nonneg a)

end mat

variable {l : ℕ} [hl : Fact l.Prime]

theorem th_le (x : Ainf l) : ‖((Per.θD l).comp (aDp l)) x‖ ≤ 1 := by
  rw [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]
  exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l x).2

theorem norm_l : ‖((l : ℕ) : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem th_pow_dvd (n : ℕ) (x : Ainf l) (h : ((l : ℕ) : Ainf l) ^ n ∣ x) :
    ‖((Per.θD l).comp (aDp l)) x‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  obtain ⟨w, rfl⟩ := h
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_l, inv_pow]
  exact mul_le_of_le_one_right (by positivity) (th_le w)

theorem th_gal {K : FinExt l} (bk : BK K) (g : ↥(GK K)) (s : bk.S) :
    ((Per.θD l).comp (aDp l)) (Per.σA (g : GQ l) (bk.ev s)) = ((Per.θD l).comp (aDp l)) (bk.ev s) := by
  simp only [RingHom.comp_apply, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨r, hr⟩ := bk.str.surjective (Ideal.Quotient.mk _ s)
  rw [bk.θ_ev r s hr.symm]
  refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (intToOC K r)).trans ?_
  rw [coe_intToOC, GlobalTheory.RingBasics.σC_coe]
  congr 1
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (r : ↥K.1).2

theorem zl_unique (f g : ℤ_[l] →+* ℂ_[l]) (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1) (x : ℤ_[l]) :
    f x = g x := by
  have key : ∀ n : ℕ, ‖f x - g x‖ ≤ ‖((l : ℕ) : ℂ_[l])‖ ^ n := by
    intro n
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
    have e : x = ((x.appr n : ℕ) : ℤ_[l]) + u * ((l : ℕ) : ℤ_[l]) ^ n := by rw [hu]; ring
    rw [e, map_add (f := _), map_add (f := _), map_natCast, map_natCast, add_sub_add_left_eq_sub, map_mul, map_mul, map_pow,
      map_pow, map_natCast, map_natCast, ← sub_mul, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity)
      ((nsub_max _ _).trans (max_le (hf u) (hg u)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (GlobalTheory.RingBasics.norm_p_lt (p := l))
  have h0 := ge_of_tendsto' ht key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 h0)

theorem th_zl (z : ℤ_[l]) :
    ((Per.θD l).comp (aDp l)) (algebraMap ℤ_[l] (Ainf l) z) = algebraMap (Om l) ℂ_[l] (zOm l z) :=
  zl_unique (((Per.θD l).comp (aDp l)).comp (algebraMap ℤ_[l] (Ainf l)))
    ((algebraMap (Om l) ℂ_[l]).comp (zOm l)) (fun _ => th_le _) (fun x => by
      simp [zOm]
      exact PadicInt.norm_le_one x) z

theorem pow_dvd_of_inclW (k : ℕ) (a : Ainf l) (h : ((l : ℕ) : WCb l) ^ k ∣ inclW l a) :
    ((l : ℕ) : Ainf l) ^ k ∣ a := by
  induction k generalizing a with
  | zero => simp
  | succ k ih =>
    obtain ⟨c, hc⟩ := h
    have h0 : a.coeff 0 = 0 := by
      have h1 : (inclW l a).coeff 0 = 0 := by
        rw [hc, pow_succ', mul_assoc]; exact coeff_zero_l_mul _
      change algebraMap (OCb l) (Cb l) (a.coeff 0) = 0 at h1
      exact (map_eq_zero_iff _ (IsFractionRing.injective (OCb l) (Cb l))).1 h1
    obtain ⟨b, rfl⟩ := ainf_exists_l_mul_of_coeff_zero a h0
    have hl0 : ((l : ℕ) : WCb l) ≠ 0 := fun h => by
      have h1 := congrArg (fun x : WCb l => x.coeff 1) h
      simp [WittVector.coeff_p] at h1
    have hb : ((l : ℕ) : WCb l) ^ k ∣ inclW l b := by
      refine ⟨c, mul_left_cancel₀ hl0 ?_⟩
      rw [← mul_assoc, ← pow_succ', ← hc, map_mul, map_natCast]
    exact pow_succ' ((l : ℕ) : Ainf l) k ▸ mul_dvd_mul_left _ (ih b hb)

theorem bounded_compat : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N : ℕ), ∃ Bd : ℝ, ∀ (N' d d' n : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') (ℤ_[l])) (F : Frame bk N' d ρ) (F' : Frame bk N d' ρ') (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d') (Fin d') (Ainf l)), N' = N → Y.map (inclW l) = inclW l τ ^ N • F.T → Y'.map (inclW l) = inclW l τ ^ N • F'.T → ∀ (g : ↥(GK K)) (U : Matrix (Fin d) (Fin d) (ℂ_[l])) (U' : Matrix (Fin d') (Fin d') (ℂ_[l])), U * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) → U' * Y'.map ((Per.θD l).comp (aDp l)) = Y'.map ((Per.θD l).comp (aDp l)) * (F'.ε g).map ((Per.θD l).comp (aDp l)) → (∀ i j, ‖U i j‖ ≤ Bd) ∧ (∀ i j, ‖U' i j‖ ≤ Bd) ∧ ∀ (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])) (R : Matrix (Fin d) (Fin d') (bk.S)), (∀ g i j, (l : ℤ_[l]) ^ n ∣ (Pi * ρ' g - ρ g * Pi) i j) → (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - F.T * R.map bk.evW) i j) → ∀ i j, ‖(U * Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U') i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹ := by
  intro l _ K bk τ hτ N
  have hs0 := _root_.GlobalTheory.ThetaPer.thetaD_aDp_pow_ne_zero l K bk τ hτ (2 * N)
  set s := ((Per.θD l).comp (aDp l)) (τ ^ (2 * N)) with hs
  have hc0 : 0 < ‖s‖ := norm_pos_iff.2 hs0
  have hc1 : ‖s‖ ≤ 1 := th_le _
  have hci : 1 ≤ ‖s‖⁻¹ := (one_le_inv₀ hc0).2 hc1
  refine ⟨‖s‖⁻¹ * ‖s‖⁻¹, ?_⟩
  intro N' d d' n ρ ρ' F F' Y Y' hN hY hY' g U U' hU hU'
  subst N'
  have hb1 : ∀ {m k : Type} (M : Matrix m k (Ainf l)), ∀ i j, ‖(M.map ((Per.θD l).comp (aDp l))) i j‖ ≤ 1 :=
    fun M i j => th_le _

  have inv : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z : Matrix (Fin e) (Fin e) (Ainf l)), Z.map (inclW l) = inclW l τ ^ N • G.T →
      ∃ Z₁ : Matrix (Fin e) (Fin e) (Ainf l),
        Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 := by
    intro e σ G Z hZ
    obtain ⟨Z₀, Z₁, h0, h1⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N e σ G.toPre
    have e0 : Z₀ = Z := by
      refine Matrix.ext fun i j => ?_
      apply inclW_injective
      have := congrFun (congrFun (h0.trans hZ.symm) i) j
      simpa using this
    subst e0
    refine ⟨Z₁, ?_⟩
    rw [← Matrix.map_mul, h1]
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j <;> simp [Matrix.smul_apply, Matrix.one_apply, hij, s]
  obtain ⟨Y₁, hY₁⟩ := inv F Y hY
  obtain ⟨Y₁', hY₁'⟩ := inv F' Y' hY'

  have solve : ∀ {e : ℕ} (y y₁ x V : Matrix (Fin e) (Fin e) ℂ_[l]), y * y₁ = s • 1 → V * y = y * x →
      V = s⁻¹ • (y * x * y₁) := by
    intro e y y₁ x V h1 h2
    rw [← h2, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have bnd : ∀ {e : ℕ} {σ : ↥(GK K) → Matrix (Fin e) (Fin e) ℤ_[l]} (G : Frame bk N e σ)
      (Z Z₁ : Matrix (Fin e) (Fin e) (Ainf l)) (V : Matrix (Fin e) (Fin e) ℂ_[l]),
      Z.map ((Per.θD l).comp (aDp l)) * Z₁.map ((Per.θD l).comp (aDp l)) = s • 1 →
      V * Z.map ((Per.θD l).comp (aDp l)) = Z.map ((Per.θD l).comp (aDp l)) * (G.ε g).map ((Per.θD l).comp (aDp l)) →
      ∀ i j, ‖V i j‖ ≤ ‖s‖⁻¹ := by
    intro e σ G Z Z₁ V h1 h2
    rw [solve _ _ _ V h1 h2]
    have := bnd_smul s⁻¹ (bnd_mul (mul_nonneg zero_le_one zero_le_one) zero_le_one
      (bnd_mul zero_le_one zero_le_one (hb1 Z) (hb1 (G.ε g))) (hb1 Z₁))
    simpa [norm_inv] using this
  have hUb := bnd F Y Y₁ U hY₁ hU
  have hU'b := bnd F' Y' Y₁' U' hY₁' hU'
  have hle : ‖s‖⁻¹ ≤ ‖s‖⁻¹ * ‖s‖⁻¹ := le_mul_of_one_le_left (by positivity) hci
  refine ⟨fun i j => (hUb i j).trans hle, fun i j => (hU'b i j).trans hle, ?_⟩
  intro Pi R hequi hlink
  set θ' : Ainf l →+* ℂ_[l] := (Per.θD l).comp (aDp l) with hθ'
  have hD1 : ∀ i j, ((l : ℕ) : Ainf l) ^ n ∣ (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev) i j := by
    intro i j
    apply pow_dvd_of_inclW
    have e1 : (Pi.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW Pi := by
      refine Matrix.ext fun a b => ?_
      exact (inclWA l).commutes _
    have e2 : (R.map bk.ev).map (inclW l) = R.map bk.evW := by
      rw [Matrix.map_map]; rfl
    have e : (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map (inclW l) =
        inclW l τ ^ N • (zW Pi * F'.T - F.T * R.map bk.evW) := by
      rw [Matrix.map_sub _ (map_sub (inclW l)), Matrix.map_mul, Matrix.map_mul, hY, hY', e1, e2,
        Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    have := congrFun (congrFun e i) j
    rw [Matrix.map_apply] at this
    rw [this, Matrix.smul_apply, smul_eq_mul]
    exact Dvd.dvd.mul_left (hlink i j) _
  have hD2 := _root_.GlobalTheory.BKLim.LinkCocycle.main l K bk N N d d' n ρ ρ' F F' Pi R hequi hlink g
  have hP : Pi.map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) = (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact (th_zl _).symm
  have hR : ((R.map bk.ev).map (Per.σA (g : GQ l))).map θ' = (R.map bk.ev).map θ' := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact th_gal bk g _
  rw [hP]
  set P := (Pi.map (algebraMap ℤ_[l] (Ainf l))).map θ' with hPdef
  set y := Y.map θ' with hy
  set y' := Y'.map θ' with hy'
  set Ry := (R.map bk.ev).map θ' with hRy
  set e := (F.ε g).map θ' with he
  set e' := (F'.ε g).map θ' with he'
  have eD1 : P * y' - y * Ry = (Pi.map (algebraMap ℤ_[l] (Ainf l)) * Y' - Y * R.map bk.ev).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul]
  have eD2 : e * Ry - Ry * e' = (F.ε g * (R.map bk.ev).map (Per.σA (g : GQ l)) - R.map bk.ev * F'.ε g).map θ' := by
    rw [Matrix.map_sub _ (map_sub θ'), Matrix.map_mul, Matrix.map_mul, hR]
  set q : ℝ := ((l : ℝ) ^ n)⁻¹ with hqdef
  have hq : 0 ≤ q := by positivity
  have bD1 : ∀ i j, ‖(P * y' - y * Ry) i j‖ ≤ q := by
    rw [eD1]; intro i j; exact th_pow_dvd n _ (hD1 i j)
  have bD2 : ∀ i j, ‖(e * Ry - Ry * e') i j‖ ≤ q := by
    rw [eD2]; intro i j; exact th_pow_dvd n _ (hD2 i j)
  have key : (U * P - P * U') * y' = U * (P * y' - y * Ry) + y * (e * Ry - Ry * e') - (P * y' - y * Ry) * e' := by
    rw [Matrix.sub_mul, Matrix.mul_assoc P U' y', hU', Matrix.mul_assoc U P y']
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hU]
    abel
  have hX : U * P - P * U' = s⁻¹ • ((U * P - P * U') * y' * Y₁'.map θ') := by
    rw [Matrix.mul_assoc (U * P - P * U') y', hY₁', Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hs0, one_smul]
  intro i j
  rw [hX, key]
  have hsq : q ≤ ‖s‖⁻¹ * q := le_mul_of_one_le_left hq hci
  have b1 : ∀ i j, ‖(U * (P * y' - y * Ry)) i j‖ ≤ ‖s‖⁻¹ * q := bnd_mul (by positivity) hq hUb bD1
  have b2 : ∀ i j, ‖(y * (e * Ry - Ry * e')) i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul zero_le_one hq (hb1 Y) bD2 i j).trans (by rw [one_mul]; exact hsq)
  have b3 : ∀ i j, ‖((P * y' - y * Ry) * e') i j‖ ≤ ‖s‖⁻¹ * q := fun i j =>
    (bnd_mul hq zero_le_one bD1 (hb1 _) i j).trans (by rw [mul_one]; exact hsq)
  have b4 := bnd_smul s⁻¹ (bnd_mul (by positivity) zero_le_one (bnd_sub (bnd_add b1 b2) b3) (hb1 Y₁'))
  calc _ ≤ _ := b4 i j
    _ = _ := by rw [norm_inv]; ring

end GlobalTheory.HTBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystalline
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

noncomputable section

namespace GlobalTheory.NL.Exact

theorem smul_eq_sum {O : Type} [CommRing O] {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M]
    [Module (LetA O n) M] [Module O M] [IsScalarTower O (LetA O n) M] (c : ℕ)
    (h : ∀ m : M, ((letπ : LetA O n) ^ c) • m = 0) (a : LetA O n) (m : M) :
    a • m = ∑ i : ZMod n, ∑ k ∈ Finset.range c,
      PowerSeries.coeff k (a i) • (((letE i : LetA O n) * (letπ : LetA O n) ^ k) • m) := by
  have ha : a = (∑ i : ZMod n, ∑ k ∈ Finset.range c,
      PowerSeries.coeff k (a i) • ((letE i : LetA O n) * (letπ : LetA O n) ^ k)) +
      (letπ : LetA O n) ^ c * (fun j => PowerSeries.mk fun k => PowerSeries.coeff (k + c) (a j)) := by
    funext j
    ext k
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, letπ, letE]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Pi.single_eq_same, one_mul, map_add (f := _), map_sum, PowerSeries.coeff_smul,
      PowerSeries.coeff_X_pow, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mk, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    by_cases hk : k < c
    · simp [hk, Nat.not_le.2 hk]
    · simp [hk, Nat.le_of_not_lt hk, Nat.sub_add_cancel (Nat.le_of_not_lt hk)]
  conv_lhs => rw [ha]
  rw [add_smul, mul_smul, h, add_zero, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_assoc]

theorem finite_of_pi_pow {O : Type} [CommRing O] {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M]
    [Module (LetA O n) M] [Module O M] [IsScalarTower O (LetA O n) M] [Module.Finite (LetA O n) M]
    (c : ℕ) (h : ∀ m : M, ((letπ : LetA O n) ^ c) • m = 0) : Module.Finite O M := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := LetA O n) (M := M)
  let S : Finset M := (Finset.univ ×ˢ Finset.range c ×ˢ s).image
    fun p => ((letE p.1 : LetA O n) * (letπ : LetA O n) ^ p.2.1) • p.2.2
  refine ⟨⟨S, eq_top_iff.2 fun x _ => ?_⟩⟩
  have hx : x ∈ Submodule.span (LetA O n) (s : Set M) := hs ▸ Submodule.mem_top
  obtain ⟨f, -, rfl⟩ := Submodule.mem_span_finset.1 hx
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [smul_eq_sum c h]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image.2
    ⟨(i, k, m), Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨hk, hm⟩⟩, rfl⟩))

theorem finiteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem length_cokN_lt_top [NeZero n] [IsDomain O] [IsDiscreteValuationRing O]
    (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (π : LatHom T₁.L T₂.L) (p c : ℕ)
    (hp0 : ((p : ℕ) : O) ≠ 0)
    (hl : ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = ((p : ℕ) : LetA O n) ^ c • z)
    (hπ : ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = (letπ : LetA O n) ^ c • z) :
    Module.length O (cokN W π) < ⊤ := by
  haveI : Module.Finite (LetA O n) ↥(W.N T₂) := Module.Finite.iff_fg.mpr (W.N_fg T₂)
  have hπ' : ∀ m : cokN W π, ((letπ : LetA O n) ^ c) • m = 0 := by
    intro m
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, e⟩ := hπ z hz
    exact ⟨y, hy, e⟩
  haveI := finite_of_pi_pow (O := O) c hπ'
  have hl' : ∀ m : cokN W π, ((p : ℕ) : O) ^ c • m = 0 := by
    intro m
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, e⟩ := hl z hz
    refine ⟨y, hy, ?_⟩
    change W.map π y = ((p : ℕ) : O) ^ c • z
    rw [e, ← algebraMap_smul (LetA O n) (((p : ℕ) : O) ^ c) z, map_pow, map_natCast]
  exact lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 (finiteLength_of_killed (pow_ne_zero c hp0) hl'))

end Generic


set_option maxHeartbeats 1600000 in
theorem exactness_of_N : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), P6 D HW F := by
  intro D HW F Cm l _ K s LL h
  obtain ⟨h1, h2⟩ := GlobalTheory.NL.Isog.saturated_and_isogeny_invariant D HW F l K s LL h
  refine ⟨h1, h2, fun T₀ T₁ T₂ ι π c0 c1 c2 hses => ?_⟩
  have hex : Function.Injective (((HW l).W K s LL h).map ι) ∧
      Function.Exact (((HW l).W K s LL h).map ι) (((HW l).W K s LL h).map π) ∧
      Function.Surjective (((HW l).W K s LL h).map π) := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.Decompl.fontaine_and_decompletion D HW F) l K s LL h
    T₀ T₁ T₂ ι π hses
  have h4 := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T₀ T₁ T₂ ι π c0 c1 c2 hses
  obtain ⟨c, hc⟩ := GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T₀ T₁ T₂ ι π c0 c1 c2 hses
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x _ hx => ?_, fun y hy hy0 => ?_, fun z hz => ?_, h4, ?_⟩
  · exact hex.1 (hx.trans (map_zero _).symm)
  · obtain ⟨x, hx⟩ := (hex.2.1 y).1 hy0
    exact ⟨0, x, h4 x (hx ▸ hy), by rw [hx, pow_zero, one_smul]⟩
  · obtain ⟨⟨y, hy, e⟩, -⟩ := hc z hz
    exact ⟨c, y, hy, by rw [e, hp]⟩
  · haveI := ((D.loc l).PD K).finK₀
    haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
    obtain ⟨_, -, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
    have hl0 : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
      intro h0
      have := congrArg (fun x : ↥(OL LL) => (x : ↥LL.1)) h0
      simp [(Fact.out : l.Prime).ne_zero] at this
    exact length_cokN_lt_top _ π l c hl0 (fun z hz => (hc z hz).1) (fun z hz => (hc z hz).2)

end GlobalTheory.NL.Exact
end
end

