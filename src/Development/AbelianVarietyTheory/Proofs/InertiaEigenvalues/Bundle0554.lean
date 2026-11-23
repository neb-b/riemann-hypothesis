module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusSectionAcrisBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfCrystallineBreuilKisinFrame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.CrTop

theorem map_smul_ring {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ} (c : R)
    (M : Matrix (Fin d) (Fin d) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem pow_cancel {R : Type} [CommRing R] {lr : R} (h : ∀ x : R, lr * x = 0 → x = 0) (n : ℕ) :
    ∀ x : R, lr ^ n * x = 0 → x = 0 := by
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; exact ih x (h _ (by rw [← mul_assoc, ← pow_succ']; exact hx))

theorem smul_cancel {R : Type} [CommRing R] {c : R} (h : ∀ x : R, c * x = 0 → x = 0) {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} (hM : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun hM i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact sub_eq_zero.1 (h _ (by rw [mul_sub, this, sub_self]))

theorem crys_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (N : ℕ) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (F : Frame bk N d fun g => (ρ g).val), F.IsCr → IsCrys (P.PD K) (qRep ρ) := by
  intro l _ K bk τ hτ P AI T N d ρ F hcr
  obtain ⟨Y, Y', hY, hYY⟩ := _root_.GlobalTheory.BKLim.pre_bounded_poles l K bk τ hτ N d (fun g => (ρ g).val) F.toPre
  obtain ⟨-, hR1, hE2⟩ := GlobalTheory.T.frame_ainf_matrix_frobenius_galois_eqs l K bk τ hτ N d (fun g => (ρ g).val) F Y Y' hY hYY
  obtain ⟨k, Q, Q', hQQ, hQu, hQ'u, hQφ⟩ := _root_.GlobalTheory.CrisSec.phiSection l K bk N d F.A F.A' F.A_mul
  obtain ⟨htf, -, ⟨v, hv⟩, hφι, hσι⟩ := _root_.GlobalTheory.AcrisFrobE.main l K bk
  set ι := algebraMap (Ainf l) (Per.Acris l) with hι

  have key : ∀ g : ↥(GK K), (F.ε g).map (fun a => ι (WittVector.frobenius a)) * Q.map (sigA (g : GQ l)) = Q := by
    intro g
    set σ := sigA (g : GQ l) with hσdef
    set fA : bk.S →+* Per.Acris l := (ι.comp bk.ev).comp (frobS l bk.a) with hfA
    set f0 : bk.S →+* Per.Acris l := fA.comp ((PowerSeries.C).comp PowerSeries.constantCoeff) with hf0
    set ε' := (F.ε g).map (fun a => ι (WittVector.frobenius a)) with hε'
    have hfr : ∀ s : bk.S, fA s = ι (WittVector.frobenius (bk.ev s)) := fun s => by
      simp only [hfA, RingHom.comp_apply, bk.ev_frob]
    have hfix : ∀ c : Wq l bk.a, σ (fA (PowerSeries.C c)) = fA (PowerSeries.C c) := fun c => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← ActLaws.φA_σA, bk.ev_C, bk.gal_w g c]
    have hcomm : ∀ x, phiA l (σ x) = σ (phiA l x) := fun x => by
      simp only [hσdef]
      exact GlobalTheory.CrisMaps.phiA_sigA (g : GQ l) x
    have he₀ : ∃ w : (Per.Acris l)ˣ, f0 bk.E = (l : Per.Acris l) * w := by
      obtain ⟨w, hw⟩ := bk.coeff_zero
      have hc : PowerSeries.constantCoeff bk.E = (l : Wq l bk.a) * w := by
        rw [← hw]; simp
      refine ⟨((Units.map (PowerSeries.C (R := Wq l bk.a)).toMonoidHom w).map fA.toMonoidHom), ?_⟩
      simp [hf0, hc]

    have hBB : F.A.map fA * F.A'.map fA = fA bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hAA : F.A.map f0 * F.A'.map f0 = f0 bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) := by
      rw [← Matrix.map_mul, F.A_mul, map_smul_ring, map_pow, Matrix.map_one _ (map_zero _) (map_one _)]
    have hσA₀ : (F.A.map f0).map σ = F.A.map f0 := by
      ext i j; simp only [Matrix.map_apply, hf0, RingHom.comp_apply]; exact hfix _
    have hσe₀ : σ (f0 bk.E) = f0 bk.E := by simp only [hf0, RingHom.comp_apply]; exact hfix _
    have hσf : ∀ s : bk.S, ι (WittVector.frobenius (Per.σA (g : GQ l) (bk.ev s))) = σ (fA s) := fun s => by
      rw [hfr, hσdef, hσι, ← GlobalTheory.RingBasics.φA_apply, ← GlobalTheory.RingBasics.φA_apply, ActLaws.φA_σA]
    have h2 : fA bk.E ^ N • (ε' * (F.A.map fA).map σ) = σ (fA bk.E) ^ N • (F.A.map fA * ε'.map (phiA l)) := by
      have e := congrArg (fun M => M.map (ι.comp WittVector.frobenius)) (hE2 g)
      simp only [map_smul_ring, Matrix.map_mul, Matrix.map_map, map_pow, RingHom.comp_apply] at e
      have hfrfun : (fA : bk.S → Per.Acris l) = (fun s => ι (WittVector.frobenius (bk.ev s))) := funext hfr
      simpa only [hε', Matrix.map_map, RingHom.coe_comp, Function.comp_def, RingHom.comp_apply, hfrfun, hσf, hφι] using e
    have hL1 := GlobalTheory.T.frobenius_equation_of_twisted_cocycle_defect (Per.Acris l) (phiA l) σ d N k (l : Per.Acris l) (fA bk.E) (f0 bk.E) Q Q' (F.A.map fA) (F.A'.map fA)
      (F.A.map f0) (F.A'.map f0) ε' htf ⟨v, hv⟩ he₀ hcomm (map_natCast _ _) (map_natCast _ _) hσe₀ hσA₀ hQQ hBB hAA hQφ h2

    obtain ⟨w₀, hw₀⟩ := he₀
    set D := Q' * ε' * Q.map σ - (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) with hD
    have hDeq : (l : Per.Acris l) ^ (2 * N) • D = F.A.map f0 * D.map (phiA l) * (((w₀⁻¹ : (Per.Acris l)ˣ) : Per.Acris l) ^ (2 * N) • F.A'.map f0) := by
      rw [Matrix.mul_smul, ← hL1, smul_smul, hw₀]
      congr 1
      rw [mul_pow, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one]

    set u := ι (bk.ev X) with hu
    set π := Ideal.Quotient.mk (Ideal.span {u}) with hπ
    have hz : ∀ M : Matrix (Fin d) (Fin d) (Per.Acris l), (∀ i j, u ∣ M i j) ↔ M.map π = 0 := fun M => by
      constructor
      · intro h; ext i j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using h i j
      · intro h i j
        have := congrFun (congrFun h i) j
        simpa [hπ, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] using this
    have hQ1 : Q.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQu
    have hQ'1 : Q'.map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 hQ'u
    have hdvdφ : bk.ev X ∣ WittVector.frobenius (bk.ev X) := by
      rw [bk.ev_X, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
      exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero
    have hε1 : ε'.map π = 1 := by
      have : ∀ i j, u ∣ (ε' - 1) i j := fun i j => by
        obtain ⟨c, hc⟩ := hcr g i j
        have e1 : (ε' - 1) i j = ι (WittVector.frobenius ((F.ε g - 1) i j)) := by
          simp only [hε', Matrix.sub_apply, Matrix.map_apply, map_sub]
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        rw [e1, hc, map_mul, map_mul]
        exact dvd_mul_of_dvd_left (map_dvd ι hdvdφ) _
      rw [← sub_eq_zero, ← Matrix.map_one π (map_zero _) (map_one _), ← Matrix.map_sub _ (map_sub π)]
      exact (hz _).1 this
    have hQσ : (Q.map σ).map π = ((l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))).map π := by
      have hdσ : u ∣ σ u := by
        rw [hu, hσdef, hσι]; exact map_dvd ι ((galois_discMap l K bk).1 (g : GQ l))
      have : ∀ i j, u ∣ (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j := fun i j => by
        have e1 : (Q.map σ - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j =
            σ ((Q - (l : Per.Acris l) ^ k • (1 : Matrix (Fin d) (Fin d) (Per.Acris l))) i j) := by
          by_cases hij : i = j
          · subst hij; simp
          · simp [Matrix.one_apply_ne hij]
        obtain ⟨c, hc⟩ := hQu i j
        rw [e1, hc, map_mul]
        exact dvd_mul_of_dvd_left hdσ _
      rw [← sub_eq_zero, ← Matrix.map_sub _ (map_sub π)]; exact (hz _).1 this
    have hdiv : ∀ i j, ι (bk.ev X) ∣ D i j := by
      refine (hz D).2 ?_
      rw [hD, Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul, hQ'1, hε1, hQσ]
      simp only [map_smul_ring, Matrix.map_one _ (map_zero _) (map_one _), mul_one, smul_mul_smul_comm, map_pow]
      rw [← pow_add, ← two_mul, sub_self]
    have hD0 := _root_.GlobalTheory.BKLim.acris_frob_eq_zero l K bk d (2 * N) D (F.A.map f0) _ hdiv hDeq
    have hM : Q' * ε' * Q.map σ = (l : Per.Acris l) ^ (2 * k) • (1 : Matrix (Fin d) (Fin d) (Per.Acris l)) :=
      sub_eq_zero.1 hD0
    refine smul_cancel (pow_cancel htf (2 * k)) ?_
    have := congrArg (fun M => Q * M) hM
    simp only [← Matrix.mul_assoc, hQQ, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one] at this
    exact this
  obtain ⟨U, hU, hinv⟩ := GlobalTheory.T.exists_invariant_unit_matrix_bcris_frame l K bk τ hτ N d k ρ Y Y' F.ε Q Q' hYY hR1 hQQ key
  exact _root_.GlobalTheory.BKLim.isCrys_of_bcris_matrix l K P AI T d ρ U hU hinv

end GlobalTheory.CrTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsExactTripleBreuilKisinOfShortExactLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKExact

theorem det_mul_eq_sum_fun' {R : Type*} [CommRing R] {ι m : Type*} [Fintype ι] [DecidableEq ι] [Fintype m]
    [DecidableEq m] (A : Matrix ι m R) (B : Matrix m ι R) :
    (A * B).det = ∑ f : ι → m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

def selCols {R : Type*} [CommRing R] {m n : Type*} [DecidableEq n] (s : m → n) : Matrix n m R :=
  fun k i => if s i = k then (1 : R) else 0

theorem mul_selCols {R : Type*} [CommRing R] {m n : Type*} [Fintype n] [DecidableEq n] (N : Matrix m n R)
    (s : m → n) : N * (selCols (R := R) s) = N.submatrix id s := by
  ext i j
  rw [Matrix.mul_apply]
  simp [selCols]

theorem exists_right_of_minor {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (N : Matrix m n (A O K)) (s : m → n) :
    ∃ Y : Matrix n m K⟦X⟧, (∀ i j, Y i j ∈ A O K) ∧
      N.map (A O K).val * Y = ((N.submatrix id s).det : K⟦X⟧) • (1 : Matrix m m K⟦X⟧) := by
  refine ⟨(selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val, fun i j => (_ : A O K).2, ?_⟩
  have h1 : N.map (A O K).val * (selCols (R := A O K) s * (N.submatrix id s).adjugate).map (A O K).val =
      (N * (selCols (R := A O K) s * (N.submatrix id s).adjugate)).map (A O K).val := by
    simp only [Matrix.map_mul]
  rw [h1, ← Matrix.mul_assoc, mul_selCols, Matrix.mul_adjugate]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem exists_right {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
    {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n (ZMod a → A O K))
    (Z : Matrix n m (OW l O)) (hZ : M.map (fun x => inclO l O (ϖ.iTot t K x)) * Z = 1) (τ : ZMod a) :
    ∃ (Y : Matrix n m K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ g ∈ A O K ∧ (∃ k, ‖coeff k g‖ = 1) ∧
      (Matrix.of fun i j => (M i j τ : K⟦X⟧)) * Y = g • (1 : Matrix m m K⟦X⟧) := by
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have h1 := congrArg Matrix.det hZ
  rw [Matrix.det_one, det_mul_eq_sum_fun'] at h1
  have h2 : ∀ f : m → n, ((M.map fun x => inclO l O (ϖ.iTot t K x)).submatrix id f).det =
      inclO l O (ϖ.iTot t K (M.submatrix id f).det) := fun f => by
    exact (RingHom.map_det φ (M.submatrix id f)).symm
  simp only [h2] at h1
  obtain ⟨f, k, hk⟩ := _root_.GlobalTheory.ResidueUnitCoeff.exists_norm_coeff_eq_one t ϖ (fun f => (M.submatrix id f).det) _ h1 τ
  let N : Matrix m n (A O K) := fun i j => M i j τ
  have h3 : (M.submatrix id f).det τ = (N.submatrix id f).det :=
    RingHom.map_det (Pi.evalRingHom (fun _ : ZMod a => A O K) τ) (M.submatrix id f)
  obtain ⟨Y, hY, hNY⟩ := exists_right_of_minor N f
  refine ⟨Y, _, hY, (N.submatrix id f).det.2, ⟨k, ?_⟩, hNY⟩
  rw [← h3]
  exact hk

theorem isExactTriple_of_isSESLat_gen {l : ℕ} [Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e] {O K : Type} [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {G : Type} [Group G] [TopologicalSpace G]
    {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
    {P₀ : PhiMod O K l e a ι} {P₁ : PhiMod O K l e a κ} {P₂ : PhiMod O K l e a μ}
    {T₀ T₁ T₂ : LocLat G ℚ_[l] K O} {I₀ : Ident t ϖ P₀ T₀} {I₁ : Ident t ϖ P₁ T₁} {I₂ : Ident t ϖ P₂ T₂}
    {f : LatHom T₀.L T₁.L} {g : LatHom T₁.L T₂.L} {F : BK.Hom P₀ P₁} {H : BK.Hom P₁ P₂}
    (hS : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I₀ I₁ f F) (hH : IsMapOf I₁ I₂ g H) : IsExactTriple F H := by
  obtain ⟨⟨Z, hZ⟩, ⟨Yw, hYw⟩⟩ := GlobalTheory.T.phiModuleHom_shortExact_split_wittTilt_alt t ϖ hS hF hH
  have hex := GlobalTheory.T.tame_setting_group_action_compat t ϖ hS hF hH
  let φ : (ZMod a → A O K) →+* OW l O := (inclO l O).toRingHom.comp (ϖ.iTot t K).toRingHom
  have hφ : Function.Injective φ := inclO_injective.comp (ϖ.iTot_injective t K)
  let ψ : ZMod a → (ZMod a → A O K) →+* K⟦X⟧ := fun τ =>
    (A O K).val.toRingHom.comp (Pi.evalRingHom (fun _ : ZMod a => A O K) τ)
  have extPi : ∀ {m n : Type} (M N : Matrix m n (ZMod a → A O K)),
      (∀ τ, M.map (ψ τ) = N.map (ψ τ)) → M = N := fun M N h => by
    funext i j τ
    exact Subtype.ext (congrFun₂ (h τ) i j)
  let Ht : Matrix μ κ (ZMod a → A O K) := fun i j τ => ⟨H.mat τ i j, H.mem τ i j⟩
  let Ft : Matrix κ ι (ZMod a → A O K) := fun i j τ => ⟨F.mat τ i j, F.mem τ i j⟩
  have hHr : ∀ τ, ∃ (Y : Matrix κ μ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ H.mat τ * Y = c • (1 : Matrix μ μ K⟦X⟧) :=
    fun τ => exists_right t ϖ Ht Z hZ τ
  have hFl : ∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (c : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧
      c ∈ A O K ∧ (∃ k, ‖coeff k c‖ = 1) ∧ Y * F.mat τ = c • (1 : Matrix ι ι K⟦X⟧) := by
    intro τ
    have hT : Ftᵀ.map (fun x => inclO l O (ϖ.iTot t K x)) * Ywᵀ = 1 := by
      rw [Matrix.transpose_map, ← Matrix.transpose_mul]
      exact (congrArg Matrix.transpose hYw).trans Matrix.transpose_one
    obtain ⟨Y, c, hY, hc, hk, h⟩ := exists_right t ϖ Ftᵀ Ywᵀ hT τ
    refine ⟨Yᵀ, c, fun i j => hY j i, hc, hk, ?_⟩
    have h1 := congrArg Matrix.transpose h
    rw [Matrix.transpose_mul, Matrix.transpose_smul, Matrix.transpose_one] at h1
    exact h1
  choose YH cH hYH hcH hkH hHY using hHr
  choose YF cF hYF hcF hkF hFY using hFl
  have hne : ∀ {c : K⟦X⟧}, (∃ k, ‖coeff k c‖ = 1) → c ≠ 0 := by
    rintro c ⟨k, hk⟩ rfl
    simp at hk
  refine ⟨?_, ?_, ?_⟩
  · intro v hv hFv
    funext τ
    have h1 : cF τ • v τ = 0 := by
      have h2 := congrArg (fun x => YF τ *ᵥ x τ) hFv
      simp only [Hom.app_apply, Matrix.mulVec_mulVec, hFY, Matrix.smul_mulVec, Matrix.one_mulVec,
        Pi.zero_apply, Matrix.mulVec_zero] at h2
      exact h2
    exact (smul_eq_zero.1 h1).resolve_left (hne (hkF τ))
  · intro v hv
    constructor
    · intro hHv
      refine (_root_.GlobalTheory.BK.Hom.finiteLength_coker_of_generic O K l e a ι κ P₀ P₁ F).2 (fun τ => ⟨YF τ, cF τ, hYF τ, hkF τ, hFY τ⟩) v hv
        (∏ τ, cF τ) (prod_mem fun τ _ => hcF τ) (Finset.prod_ne_zero_iff.2 fun τ _ => hne (hkF τ)) ?_
      let Yt : Matrix ι κ (ZMod a → A O K) := fun i j τ => ⟨YF τ i j, hYF τ i j⟩
      let gt : ZMod a → A O K := fun τ => ⟨cF τ, hcF τ⟩
      let vt : κ → ZMod a → A O K := fun i τ => ⟨v τ i, mem_tot.1 hv τ i⟩
      have hYFt : Yt * Ft = Matrix.diagonal fun _ => gt := by
        refine extPi _ _ fun τ => ?_
        rw [Matrix.map_mul, Matrix.diagonal_map (map_zero _)]
        exact (hFY τ).trans (Matrix.smul_one_eq_diagonal _)
      have hv' : toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩ = fun i => φ (vt i) :=
        funext fun i => ϖ.iW_of_mem t K (vt i)
      have h0 : homW t ϖ H (toW t ϖ P₁ ⟨v, mem_ME_of_mem_M hv⟩) = 0 := by
        rw [homW_toW]
        have : (⟨H.app v, H.app_mem_Mext (le_away _ _) (mem_ME_of_mem_M hv)⟩ : ME P₂) = 0 :=
          Subtype.ext hHv
        rw [this, map_zero]
      obtain ⟨w, hw⟩ := hex _ h0
      rw [homW_apply, hv'] at hw
      change Ft.map φ *ᵥ w = fun i => φ (vt i) at hw
      have h1 : (Ft * Yt).map φ *ᵥ (fun i => φ (vt i)) = φ gt • (fun i => φ (vt i)) := by
        rw [← hw, Matrix.map_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc,
          show Yt.map φ * Ft.map φ = (Yt * Ft).map φ from (Matrix.map_mul).symm, hYFt,
          Matrix.diagonal_map (map_zero _), ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
          Matrix.smul_mulVec]
      have h2 : (Ft * Yt) *ᵥ vt = gt • vt := by
        funext i
        apply hφ
        rw [RingHom.map_mulVec]
        refine (congrFun h1 i).trans ?_
        show φ gt * φ (vt i) = φ (gt * vt i)
        rw [map_mul]
      have hkey : ∀ τ, F.mat τ *ᵥ (YF τ *ᵥ v τ) = cF τ • v τ := fun τ => by
        funext i
        have := congrArg (ψ τ) (congrFun h2 i)
        rw [RingHom.map_mulVec, Matrix.map_mul] at this
        rw [Matrix.mulVec_mulVec]
        exact this.trans (map_mul (ψ τ) gt (vt i))
      refine ⟨fun τ => (∏ σ ∈ Finset.univ.erase τ, cF σ) • (YF τ *ᵥ v τ), mem_tot.2 fun τ i => ?_, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
        exact mul_mem (prod_mem fun σ _ => hcF σ)
          (sum_mem fun j _ => mul_mem (hYF τ i j) (mem_tot.1 hv τ j))
      · change F.app _ = _
        funext τ
        rw [Hom.app_apply, Matrix.mulVec_smul, hkey, smul_smul,
          Finset.prod_erase_mul _ _ (Finset.mem_univ τ)]
        rfl
    · rintro ⟨w, hw, rfl⟩
      have hlat : ∀ z, latW g (latW f z) = 0 := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => simp only [map_zero]
        | tmul w x =>
          have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) x) = 0 :=
            Subtype.ext ((hS.2.2.2.1 (f.f x)).2 ⟨x, rfl⟩)
          simp only [latW, TensorProduct.map_tmul, LinearMap.id_apply, h0, TensorProduct.tmul_zero]
        | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
      have hW : ∀ x, homW t ϖ H (homW t ϖ F x) = 0 := fun x =>
        I₂.j.injective (by rw [hH, hF, hlat, map_zero])
      have hM : (Ht * Ft).map φ = 0 := by
        ext i j
        have := congrFun (hW (Pi.single j 1)) i
        rw [homW_apply, homW_apply, Matrix.mulVec_mulVec] at this
        simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true, Pi.zero_apply] at this
        rw [Matrix.map_mul]
        exact this
      have hz : Ht * Ft = 0 := Matrix.map_injective hφ (hM.trans (Matrix.map_zero _ (map_zero φ)).symm)
      have hHF : ∀ τ, H.mat τ * F.mat τ = 0 := fun τ => by
        have := congrArg (fun M => M.map (ψ τ)) hz
        simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero (ψ τ))] at this
        exact this
      change H.app (F.app w) = 0
      funext τ
      rw [Hom.app_apply, Hom.app_apply, Matrix.mulVec_mulVec, hHF τ, Matrix.zero_mulVec]
      rfl
  · exact (_root_.GlobalTheory.BK.Hom.finiteLength_coker_of_generic O K l e a κ μ P₁ P₂ H).1 fun τ => ⟨YH τ, cH τ, hYH τ, hkH τ, hHY τ⟩

theorem isExactTriple_of_isSESLat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (μ : Type) [Fintype μ] [DecidableEq μ] (P₀ : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (P₁ : PhiMod ↥(OL LL) ↥LL.1 l e a κ) (P₂ : PhiMod ↥(OL LL) ↥LL.1 l e a μ) (T₀ T₁ T₂ : QLat LL) (I₀ : Ident (thetaW a LL) ϖ P₀ T₀) (I₁ : Ident (thetaW a LL) ϖ P₁ T₁) (I₂ : Ident (thetaW a LL) ϖ P₂ T₂) (f : LatHom T₀.L T₁.L) (g : LatHom T₁.L T₂.L) (F : GlobalTheory.BK.Hom P₀ P₁) (G : GlobalTheory.BK.Hom P₁ P₂), IsSESLat (Qp := ℚ_[l]) f g → IsMapOf I₀ I₁ f F → IsMapOf I₁ I₂ g G → IsExactTriple F G := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ κ _ _ μ _ _ P₀ P₁ P₂ T₀ T₁ T₂ I₀ I₁ I₂ f g F G hS hF hG
  exact isExactTriple_of_isSESLat_gen (thetaW a LL) ϖ hS hF hG

end GlobalTheory.BKExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTopRingLL
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem isTopRingLL : IsTopologicalRing (Br.LL D.nbr i w hw) :=
  (goodO_ringOfIntegers (D.nd.l i) (D.nbr i w hw).LL).2.2.2.1

theorem vecL_sub {a : ℕ} (u v : Fin a → Fin D.R.nV → KK D.nd i) :
    vecL i w hw (u - v) = vecL i w hw u - vecL i w hw v := by
  funext b j
  simp [vecL]

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (Xs : Set (D.nd.X i))

theorem sumG_crys (hr : GoodR D.nd i r) (hAdm : FontaineAtPlacesOverL (D := D)) {a : ℕ} (x : Fin a → ↥Xs)
    (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1)
    (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (hpot : ∀ y : ↥Xs, (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))) :
    IsCrys ((D.loc (D.nd.l i)).PD K')
      ((sumG i w hw r Xs hr x).ρ.comp (Subgroup.inclusion (GK_le h))) := by
  haveI := isTopRingLL i w hw
  have hc' : ∀ (y : ↥Xs) (v : Fin D.R.nV → Br.LL D.nbr i w hw),
      Continuous fun g => ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)) g).mulVec v :=
    fun y v => (contTw i w hw r Xs hr y v).comp (continuous_inclusion (GK_le h))
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hcr : ∀ y : ↥Xs, IsCrys ((D.loc (D.nd.l i)).PD K')
      (matRep ((Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h)))) := fun y =>
    (_root_.GlobalTheory.PcRes.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r y)))).2.1 (hpot y)
  exact (cj_sum (Qp := ℚ_[D.nd.l i]) (O := ↥(OL (D.nbr i w hw).LL))
    (fun y : ↥Xs => (Br.loc D.nbr i w hw (rTwO D.nd i r y)).comp (Subgroup.inclusion (GK_le h))) hc' hF'
    (S := fun _ => Set.univ) (fun y => ⟨hcr y, fun τ b _ => Set.mem_univ _⟩) a x).1

theorem yfun_val {a : ℕ} (hr : GoodR D.nd i r) (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (E : Fin a → Fin D.R.nV → KK D.nd i) (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (g : Br.G D.nbr i w hw) :
    (spanL i w hw Y).subtype (yfun i w hw r Xs x Y E hE g) =
      (sumG i w hw r Xs hr x).ρ g (vecL i w hw E) - (show (sumG i w hw r Xs hr x).V from vecL i w hw E) := by
  rw [sumG_vecL]
  exact vecL_sub i w hw _ _

end GlobalTheory.Pass.LocDual.OneX

end


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.Pass.LocDual.OneX.yfun_Z1fT : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (n : ℕ), PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n → ∀ {a : ℕ} (x : Fin a → ↥Xs) (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) (E : Fin a → Fin D.R.nV → KK D.nd i)
    (hE : ∀ γ : GE D.nd, actK i r Xs x γ E - E ∈ Y)
    (LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ), LY.T = latY i w hw Y →
    (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
    latticeFiniteCocycles (Br.PD D.loc D.nbr i w hw) LY := by
  intro D hAdm i r hr Xs w hw n hpf a x Y hst E hE LY hLY
  obtain ⟨K', h, hN, hF, hS, Sig, Fr, -, -, -, -, hall⟩ := hpf
  haveI := isTopRingLL i w hw
  have hF' := hAdm (D.nd.l i) K' (D.nbr i w hw).LL
  have hz : (yfun i w hw r Xs x Y E hE : Br.G D.nbr i w hw → (XG i w hw r Xs hr x Y hst).V) ∈
      finiteCocycles (Br.PD D.loc D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ :=
    GlobalTheory.Pass.FinDesc.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF
      (fun A₀ A₁ A₂ ι π h1 h2 h3 h4 h5 hA =>
        ⟨((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).1, ((hF'.1 A₀ A₁ A₂ ι π h1 h2 h3 h4 h5).1 hA).2.1⟩)
      (sumG i w hw r Xs hr x) (XG i w hw r Xs hr x Y hst) (spanL i w hw Y).subtype
      (spanL i w hw Y).injective_subtype (fun g v => rfl)
      (sumG_crys i w hw r Xs hr hAdm x K' h hN hF hS (fun y => (hall y).1)) (vecL i w hw E)
      (yfun i w hw r Xs x Y E hE) (yfun_val i w hw r Xs hr x Y E hE)
  refine ⟨⟨hz.1, fun g _ => ?_⟩, hz⟩
  have hm : (yfun i w hw r Xs x Y E hE g : ↥(spanL i w hw Y)) ∈ latY i w hw Y :=
    Submodule.subset_span ⟨_, hE _, rfl⟩
  show yfun i w hw r Xs x Y E hE g ∈ LY.T
  rw [hLY]
  exact hm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftAllSubSumsOfLiftFamilyMatrixFamilyStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftAll_subSums_of_liftFamily_matrixFamily : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)) (e : ℕ)
    (A A' : GRep G Qp LL O), LiftFam (O := O) PD Ms e → IsSubFam Ms A → IsSubFam Ms A' → BlochKatoDuality.LiftAll PD A A' e := by
  first | exact @GlobalTheory.Pass.LocDual.liftAll_of_liftFam | exact GlobalTheory.Pass.LocDual.liftAll_of_liftFam | (intros; apply GlobalTheory.Pass.LocDual.liftAll_of_liftFam <;> assumption)
end

