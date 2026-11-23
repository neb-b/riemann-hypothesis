module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
public import Development.WeilBound.CoreStatements.FlagImmersions.Bundle0004
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.MinorIJConjTranspose
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {N j : ℕ}

theorem exists_selector (R : Type) [CommRing R] (hj : j ≤ N) (i : Fin N) {I' : Finset (Fin N)}
    (hI : IsStepRows N j i I') : ∃ h : Matrix (Fin N) (Fin N) R, IsBlockDiag j h ∧
      ∀ I, minorIJ h I (stepCols N j i) = if I = I' then 1 else 0 := by
  refine ⟨Matrix.of fun a b => if ∃ s, a = I'.orderEmbOfFin hI.1 s ∧ b = (stepCols N j i).orderEmbOfFin rfl s
    then 1 else 0, fun a b hab => ?_, fun I => ?_⟩
  · rw [Matrix.of_apply, if_neg]
    rintro ⟨s, rfl, rfl⟩
    have h1 := hI.2 (I'.orderEmbOfFin_mem hI.1 s)
    have h2 := mem_stepCols_block hj ((stepCols N j i).orderEmbOfFin_mem rfl s)
    apply hab
    split_ifs at h1 h2 with h
    · simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      omega
    · simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and] at h1
      exact ⟨fun _ => h2, fun _ => h1⟩
  · by_cases e : I = I'
    · subst e
      rw [if_pos rfl, minorIJ, dite_eq_left hI.1]
      refine Eq.trans (congrArg Matrix.det ?_) Matrix.det_one
      ext s t
      simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
      refine if_congr ⟨?_, ?_⟩ rfl rfl
      · rintro ⟨u, rfl, rfl⟩; rfl
      · rintro rfl; exact ⟨s, rfl, rfl⟩
    · rw [if_neg e]
      by_cases c : I.card = (stepCols N j i).card
      · have hs : ¬ I ⊆ I' := fun hs => e (Finset.eq_of_subset_of_card_le hs (by rw [c, hI.1]))
        obtain ⟨a, ha, has⟩ := Finset.not_subset.mp hs
        refine minorIJ_eq_zero_of_row _ ha fun b _ => ?_
        rw [Matrix.of_apply, if_neg]
        rintro ⟨s, rfl, -⟩
        exact has (I'.orderEmbOfFin_mem hI.1 s)
      · exact minorIJ_of_card_ne _ c

theorem minorIJ_conjTranspose (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) :
    minorIJ hᴴ J I = star (minorIJ h I J) := by
  by_cases e : I.card = J.card
  · rw [minorIJ_eq_det h I J _ e rfl, minorIJ_eq_det hᴴ J I _ rfl e, ← Matrix.det_conjTranspose]
    rfl
  · rw [minorIJ_of_card_ne h e, minorIJ_of_card_ne hᴴ (Ne.symm e), star_zero]

theorem gram_minor {G h g : Matrix (Fin N) (Fin N) ℂ} {C : Finset (Fin N)} {a l : ℂ}
    (e : ∀ I, a * minorIJ h I C = l * minorIJ g I C) :
    ‖a‖ ^ 2 * (minorIJ (hᴴ * G * h) C C).re = ‖l‖ ^ 2 * (minorIJ (gᴴ * G * g) C C).re := by
  have key : ∀ (b : ℂ) (f : Matrix (Fin N) (Fin N) ℂ), star b * b * minorIJ (fᴴ * G * f) C C =
      ∑ I', ∑ I, star (b * minorIJ f I C) * minorIJ G I I' * (b * minorIJ f I' C) := by
    intro b f
    rw [minorIJ_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I' _ => ?_
    rw [minorIJ_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [minorIJ_conjTranspose, star_mul]
    ring
  have h1 := key a h
  simp only [e] at h1
  rw [← key l g] at h1
  have n : ∀ b : ℂ, star b * b = ((‖b‖ ^ 2 : ℝ) : ℂ) := fun b => by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  rw [n, n] at h1
  simpa only [Complex.re_ofReal_mul] using congrArg Complex.re h1

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (C : Finset (Fin N)) : 0 < minorIJ G C C := by
  rw [minorIJ, dite_eq_left rfl]
  exact (hG.submatrix (C.orderEmbOfFin rfl).injective).det_pos

theorem detFac_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (i : Fin N) : 0 < (detFac j i G).re := by
  have : 0 < detFac j i G := by
    unfold detFac
    refine mul_pos ?_ ?_ <;> split_ifs
    exacts [minor_pos hG _, one_pos, minor_pos hG _, one_pos]
  exact (Complex.pos_iff.1 this).1

theorem gram_pos {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hh : h.det ≠ 0) (C : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * G * h) C C).re := by
  have : (hᴴ * G * h).PosDef := hG.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det h).2 hh.isUnit))
  exact (Complex.pos_iff.1 (minor_pos this C)).1

theorem detFac_conjTranspose (i : Fin N) (h : Matrix (Fin N) (Fin N) ℂ) :
    detFac j i hᴴ = star (detFac j i h) := by
  unfold detFac
  rw [minorIJ_conjTranspose, minorIJ_conjTranspose, star_mul']
  split_ifs <;> simp

theorem log_detFac (hj : j ≤ N) (i : Fin N) {G R : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (bG : IsBlockDiag j G)
    (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    (1 / 2) * Real.log (detFac j i (Rᴴ * G * R)).re =
      (1 / 2) * Real.log (detFac j i G).re + Real.log ‖detFac j i R‖ := by
  have h0 := norm_ne_zero_iff.2 (detFac_ne_zero hj i bR hR)
  have e : detFac j i (Rᴴ * G * R) = ((‖detFac j i R‖ ^ 2 : ℝ) : ℂ) * detFac j i G := by
    rw [detFac_mul i bR, detFac_mul i bG, detFac_conjTranspose, mul_right_comm, Complex.star_def, Complex.conj_mul']
    push_cast; rfl
  rw [e, Complex.re_ofReal_mul, Real.log_mul (pow_ne_zero _ h0) (detFac_pos hG i).ne', Real.log_pow]
  push_cast; ring

theorem pot_step (hj : j ≤ N) (i : Fin N) (hi : IsProperStep N j i) {G R h h' : Matrix (Fin N) (Fin N) ℂ}
    (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) (hh : h.det ≠ 0)
    (hh' : h'.det ≠ 0) {a a' μ : ℂ} (ha : a ≠ 0) (ha' : a' ≠ 0) (hμ : μ ≠ 0)
    (e : ∀ I, a * minorIJ h I (stepCols N j i) = a' * detFac j i R * μ * minorIJ (R * h') I (stepCols N j i)) :
    Real.log ‖a‖ + blockPot j i G h = Real.log ‖a'‖ + Real.log ‖μ‖ + blockPot j i (Rᴴ * G * R) h' := by
  have h0 := detFac_ne_zero hj i bR hR
  have h1 := gram_minor (G := G) e
  have p1 := gram_pos hG hh (stepCols N j i)
  have p2 := gram_pos hG (h := R * h') (by rw [Matrix.det_mul]; exact mul_ne_zero hR hh') (stepCols N j i)
  have h2 := congrArg Real.log h1
  rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ha)) p1.ne',
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (mul_ne_zero (mul_ne_zero ha' h0) hμ))) p2.ne',
    Real.log_pow, Real.log_pow, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)) (norm_ne_zero_iff.2 hμ),
    Real.log_mul (norm_ne_zero_iff.2 ha') (norm_ne_zero_iff.2 h0)] at h2
  have e2 : h'ᴴ * (Rᴴ * G * R) * h' = (R * h')ᴴ * G * (R * h') := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  unfold blockPot
  rw [if_pos hi, if_pos hi, log_detFac hj i hG bG bR hR, e2]
  push_cast at h2
  linarith

theorem pot_base (hj : j ≤ N) (i : Fin N) (hi : ¬ IsProperStep N j i) {G R : Matrix (Fin N) (Fin N) ℂ}
    (h h' : Matrix (Fin N) (Fin N) ℂ) (hG : G.PosDef) (bG : IsBlockDiag j G) (bR : IsBlockDiag j R) (hR : R.det ≠ 0) :
    blockPot j i (Rᴴ * G * R) h' = blockPot j i G h + Real.log ‖detFac j i R‖ := by
  unfold blockPot
  rw [if_neg hi, if_neg hi, log_detFac hj i hG bG bR hR]
  ring

theorem detFac_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (i : Fin N) (A : Matrix (Fin N) (Fin N) R) :
    detFac j i (A.map f) = f (detFac j i A) := by
  unfold detFac
  rw [minorIJ_map, minorIJ_map, map_mul]
  split_ifs <;> simp

theorem pot_conj (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    blockPot j i (G.map (starRingEnd ℂ)) (h.map (starRingEnd ℂ)) = blockPot j i G h := by
  have e : (h.map (starRingEnd ℂ))ᴴ * G.map (starRingEnd ℂ) * h.map (starRingEnd ℂ) =
      (hᴴ * G * h).map (starRingEnd ℂ) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  unfold blockPot
  rw [e, detFac_map, minorIJ_map, Complex.conj_re, Complex.conj_re]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XRePot
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_pot

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem log_line_of_orbit {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (a : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) (x : Re.R.X) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit (Re.R.lift x x) z) :
    Real.log ((Re.line a t).h z) = Real.log ((Re.ref a).h z) + S.phT a t (Re.π x) := by
  obtain ⟨c, hc, e⟩ := ho
  have h := Re.line_eq a t h0 h1 x
  rw [e, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at h
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul hp ((Re.line a t).pos z hz).ne', Real.log_mul hp ((Re.ref a).pos z hz).ne'] at h
  linarith

theorem samePot_line {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (c : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line c t)) ((S.potT c t).pullback Re.π Re.holo.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot c x (Set.mem_univ x)
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
  · intro j
    exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · rintro y ⟨hyV, hyU⟩
    have hm := Re.R.mem x y hyU
    have ho : SameOrbit (Re.R.lift y y) (Re.R.lift x y) := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
    have e1 := log_line_of_orbit Re c t h0 h1 y _ hm.1 ho
    have e2 : Real.log ((Re.ref c).h (Re.R.lift x y)) - (S.th c).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
    show Real.log ((Re.line c t).h (Re.R.lift x y)) -
      ((S.th c).φ (Re.π x) (Re.π y) + S.phT c t (Re.π y)) = (G y).re
    linarith

theorem isNull_compl_univ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) :
    IsNull A (Set.univ : Set X)ᶜ := by
  intro j
  simp

theorem mass_eq {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P)
    (Q : Fin D → LocPot Re.R.X) (Φ : Fin D → LocPot S.X) (hΦ : ∀ j, IsPotential S.A (Φ j))
    (hS : ∀ j, SamePot Re.R.A Set.univ (Q j) ((Φ j).pullback Re.π Re.holo.1)) :
    mInt Re.R.A Q (fun _ => 1) = Re.deg * mInt S.A Φ (fun _ => 1) := by
  rw [← degreeFormula S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree Φ hΦ _ continuous_const]
  exact (mInt_congr_samePot D Re.R.X Re.R.A Set.univ Q _ _ _ (isNull_compl_univ _) hS
    (fun j x _ => isC2At_of_isPotential _ (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hΦ j)) x)
    (fun _ _ => rfl)).1

end PositivityTheory.Xgp.re_pot

theorem PositivityTheory.Xgp.t_re_pot : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly := by
  intro hE K _ ι _ D σ _ S P Re
  have href : ∀ w : Fin D → σ,
      mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := fun w =>
    PositivityTheory.Xgp.re_pot.mass_eq Re _ _ (fun j => (S.sing (w j)).1) fun j => Re.ref_pot (w j)
  refine ⟨fun a t h0 h1 => PositivityTheory.Xgp.re_pot.samePot_line Re a t h0 h1, fun w => ?_, fun w t ht => ?_,
    fun n => ?_⟩
  · rw [ptsIntegral_one_eq_mInt hE resBridge Re.R Re.arith fun j => Re.ref_smooth (w j)]
    exact href w
  · rw [ptsIntegral_one_eq_mInt hE resBridge Re.R Re.arith
        fun j => Re.line_smooth (w j) (t j) (ht j).1 (ht j).2,
      PositivityTheory.Xgp.re_pot.mass_eq Re _ (fun j => S.potT (w j) (t j))
        (fun j => (anSys_open_basics D σ S).2.2.2.1 (w j) (t j) (ht j).1 (ht j).2)
        fun j => PositivityTheory.Xgp.re_pot.samePot_line Re (w j) (t j) (ht j).1 (ht j).2]
    congr 1
    exact massIndep S.A (fun j => S.th (w j)) (fun j => S.phT (w j) (t j)) (fun j => (S.sing (w j)).1)
      fun j => ((S.reg (w j)).2.2 (t j) (ht j).1 (ht j).2).1
  · have hsm : IsSmoothHerm (combLine Re.ref n) := by
      rw [combLine_eq_top]
      exact (RootFieldNumerics.combLine_smooth_conj_invariant K ι σ Re.ref n).1 Re.ref_smooth
    refine ⟨hsm, ?_⟩
    have hQ : ∀ a, IsPotential Re.R.A (potOf Re.R (Re.ref a)) := fun a =>
      isPotential_potOf Re.R (Re.ref_smooth a)
    have h1 : ReciprocityTheory.ChartRestriction.G.Geo.geomDeg P (combLine Re.ref n) D =
        mInt Re.R.A (fun _ : Fin D => potOf Re.R (combLine Re.ref n)) (fun _ => 1) :=
      ptsIntegral_one_eq_mInt hE resBridge Re.R (L := fun _ => combLine Re.ref n) Re.arith fun _ => hsm
    have h2 : mInt Re.R.A (fun _ : Fin D => potOf Re.R (combLine Re.ref n)) (fun _ => 1) =
        mInt Re.R.A (fun _ : Fin D => sumPot (fun a => (n a : ℝ)) fun a => potOf Re.R (Re.ref a))
          (fun _ => 1) := by
      refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr Re.R.A (locDens_congr_of_eqOn Re.R fun _ x y hy => ?_) fun _ => rfl
      have hz := (Re.R.mem x y hy).1
      show Real.log (∏ a, (Re.ref a).h (Re.R.lift x y) ^ n a) =
        ∑ a, (n a : ℝ) * Real.log ((Re.ref a).h (Re.R.lift x y))
      rw [Real.log_prod fun a _ => zpow_ne_zero _ ((Re.ref a).pos _ hz).ne']
      exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
    have h3 := (mInt_sumPot_expand D Re.R.X Re.R.A σ Set.univ (fun a => potOf Re.R (Re.ref a))
      (fun _ a => (n a : ℝ)) (fun _ => 1) (PositivityTheory.Xgp.re_pot.isNull_compl_univ _)
      (fun a x _ => PositivityTheory.Xgp.re_pot.isC2At_of_isPotential _ (hQ a) x)
      fun w => mIntegrableCont Re.R.A _ (fun j => hQ (w j)) _ continuous_const).2
    rw [h1, h2, h3, AnSys.degPoly, (formPoly_isHomogeneous_and_eval σ D S.degNum).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [href w]
    ring
end

