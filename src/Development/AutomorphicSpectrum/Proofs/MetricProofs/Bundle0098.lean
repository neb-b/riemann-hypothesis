module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0088
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0091
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MapMemChartIdealOfAevalEqZero
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.KerChart

open MvPolynomial ReciprocityTheory.AnForm.R

variable {σ : Type}

theorem exists_int_clear (G : MvPolynomial σ ℚ) :
    ∃ (n : ℤ) (G₀ : MvPolynomial σ ℤ), n ≠ 0 ∧
      map (Int.castRingHom ℚ) G₀ = C (n : ℚ) * G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    refine ⟨a.den, C a.num, by exact_mod_cast a.den_nz, ?_⟩
    rw [map_C, ← C_mul]
    congr 1
    simp [Rat.den_mul_eq_num]
  | add f g hf hg =>
    obtain ⟨n₁, F, h₁, e₁⟩ := hf
    obtain ⟨n₂, F', h₂, e₂⟩ := hg
    refine ⟨n₁ * n₂, C n₂ * F + C n₁ * F', mul_ne_zero h₁ h₂, ?_⟩
    simp only [map_add (f := _), map_mul, map_C, e₁, e₂]
    simp only [eq_intCast, Int.cast_mul, C_mul]
    ring
  | mul_X f i hf =>
    obtain ⟨n, F, h, e⟩ := hf
    exact ⟨n, F * X i, h, by rw [map_mul, map_X, e, mul_assoc]⟩

theorem exists_homog (s : σ → σ) (G₀ : MvPolynomial σ ℤ) :
    ∃ H m : MvPolynomial σ ℤ, ∀ (T : Type) [CommRing T] (f : MvPolynomial σ ℤ →+* T) (w : σ → T),
      (∀ q, IsUnit (f (X (s q)))) → (∀ q, f (X q) = f (X (s q)) * w q) →
      IsUnit (f m) ∧ eval₂Hom (Int.castRingHom T) w G₀ * f m = f H := by
  classical
  let M : Submonoid (MvPolynomial σ ℤ) :=
    Submonoid.closure (Set.range fun q => (X (s q) : MvPolynomial σ ℤ))
  let B := Localization M
  have hs : ∀ q, (X (s q) : MvPolynomial σ ℤ) ∈ M := fun q => Submonoid.subset_closure ⟨q, rfl⟩
  let ψ : MvPolynomial σ ℤ →+* B := eval₂Hom (Int.castRingHom B)
    (fun q => IsLocalization.mk' B (X q : MvPolynomial σ ℤ) ⟨X (s q), hs q⟩)
  obtain ⟨⟨H, m⟩, hHm⟩ := IsLocalization.surj M (ψ G₀)
  refine ⟨H, m, fun T _ f w hu hw => ?_⟩
  have hM : ∀ y : M, IsUnit (f y) := by
    rintro ⟨y, hy⟩
    induction hy using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      exact hu q
    | one => simp
    | mul a b _ _ ha hb => simpa using ha.mul hb
  let L : B →+* T := IsLocalization.lift hM
  have hL : ∀ r, L (algebraMap _ B r) = f r := IsLocalization.lift_eq hM
  have hcomp : L.comp ψ = eval₂Hom (Int.castRingHom T) w := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · intro q
      simp only [RingHom.comp_apply, ψ, eval₂Hom_X']
      exact (IsLocalization.lift_mk'_spec _ _ _ _).2 (hw q)
  refine ⟨hM m, ?_⟩
  have h := congrArg L hHm
  rw [map_mul, hL, hL] at h
  rw [← h, ← hcomp]
  rfl

theorem map_mem_chartIdeal_of_aeval_eq_zero :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (p : (k : K) → ι k), (∀ k, y ⟨k, p k⟩ ≠ 0) →
      ∀ G : MvPolynomial (Σ k, ι k) ℚ, aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G = 0 →
        map (algebraMap ℚ ℂ) G ∈
          chartIdeal (ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y)) p := by
  intro K _ ι _ Ω _ _ y p hy G hG
  classical
  obtain ⟨n, G₀, hn, hG₀⟩ := exists_int_clear G
  obtain ⟨H, m, hHm⟩ := exists_homog (fun q : Σ k, ι k => (⟨q.1, p q.1⟩ : Σ k, ι k)) G₀
  have hz : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩) G₀ = (0 : Ω) := by
    have h1 : aeval (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)
        (map (algebraMap ℤ ℚ) G₀) = (0 : Ω) := by
      have : (algebraMap ℤ ℚ) = Int.castRingHom ℚ := rfl
      rw [this, hG₀, map_mul, hG, mul_zero]
    rwa [aeval_map_algebraMap] at h1

  have hH : H ∈ ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y := by
    let F := FractionRing (MvPolynomial K Ω)
    let f : MvPolynomial (Σ k, ι k) ℤ →+* F :=
      (algebraMap (MvPolynomial K Ω) F).comp (ReciprocityTheory.ChartRestriction.G.Geo.mConeMap y).toRingHom
    let w : (Σ k, ι k) → F := fun q => algebraMap (MvPolynomial K Ω) F (C (y q / y ⟨q.1, p q.1⟩))
    have hfX : ∀ q, f (X q) = algebraMap (MvPolynomial K Ω) F (C (y q) * X q.1) := by
      intro q
      simp [f, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap]
    have hinj : Function.Injective (algebraMap (MvPolynomial K Ω) F) :=
      IsFractionRing.injective _ _
    have hu : ∀ q : Σ k, ι k, IsUnit (f (X ⟨q.1, p q.1⟩)) := by
      intro q
      rw [hfX, isUnit_iff_ne_zero]
      intro h0
      have := hinj (h0.trans (map_zero _).symm)
      exact mul_ne_zero (C_ne_zero.mpr (hy q.1)) (X_ne_zero _) this
    have hw : ∀ q, f (X q) = f (X ⟨q.1, p q.1⟩) * w q := by
      intro q
      rw [hfX, hfX, ← map_mul]
      congr 1
      have : y q = y ⟨q.1, p q.1⟩ * (y q / y ⟨q.1, p q.1⟩) := by
        field_simp [hy q.1]
      show C (y q) * X q.1 = C (y ⟨q.1, p q.1⟩) * X q.1 * C (y q / y ⟨q.1, p q.1⟩)
      rw [mul_right_comm, ← C_mul, ← this]
    obtain ⟨-, h⟩ := hHm F f w hu hw
    have hev : eval₂Hom (Int.castRingHom F) w G₀ = 0 := by
      have : eval₂Hom (Int.castRingHom F) w =
          ((algebraMap (MvPolynomial K Ω) F).comp C).comp
            (aeval (R := ℤ) (fun q : Σ k, ι k => y q / y ⟨q.1, p q.1⟩)).toRingHom := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp
        · intro q
          simp [w]
      rw [this]
      simp [hz]
    rw [hev, zero_mul] at h
    exact hinj (h.symm.trans (map_zero _).symm)

  set P := ReciprocityTheory.ChartRestriction.G.Geo.pC (ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal y) with hP
  let A := MvPolynomial (Σ k, ι k) ℂ ⧸ chartIdeal P p
  let f : MvPolynomial (Σ k, ι k) ℤ →+* A :=
    (Ideal.Quotient.mk (chartIdeal P p)).comp (map (Int.castRingHom ℂ))
  let w : (Σ k, ι k) → A := fun q => Ideal.Quotient.mk _ (X q)
  have hone : ∀ k, f (X ⟨k, p k⟩) = 1 := by
    intro k
    have : (X ⟨k, p k⟩ - 1 : MvPolynomial (Σ k, ι k) ℂ) ∈ chartIdeal P p :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)
    simpa [f, sub_eq_zero] using Ideal.Quotient.eq_zero_iff_mem.mpr this
  obtain ⟨hm, h⟩ := hHm A f w (fun q => by rw [hone]; exact isUnit_one)
    (fun q => by rw [hone, one_mul]; simp [f, w])
  have hfH : f H = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.subset_span ⟨H, hH, rfl⟩))
  have hev : eval₂Hom (Int.castRingHom A) w = f := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f]
    · intro q
      simp [f, w]
  rw [hev, hfH] at h
  have hG₀0 : f G₀ = 0 := hm.mul_left_eq_zero.mp h
  have hmem : map (Int.castRingHom ℂ) G₀ ∈ chartIdeal P p :=
    Ideal.Quotient.eq_zero_iff_mem.mp hG₀0
  have hmap : map (Int.castRingHom ℂ) G₀ = C (n : ℂ) * map (algebraMap ℚ ℂ) G := by
    have h1 : map (Int.castRingHom ℂ) G₀ = map (algebraMap ℚ ℂ) (map (Int.castRingHom ℚ) G₀) := by
      rw [map_map]
      congr 1
    rw [h1, hG₀, map_mul, map_C]
    simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [hmap] at hmem
  have := (chartIdeal P p).mul_mem_left (C (n : ℂ)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hn', C_1, one_mul] at this

end GlobalTheory.CompanionTheory.Ar.Cmp.KerChart
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemMcPtsOfOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev PtsOf (P : Ideal (MRing ι)) : Type := ↥(Pts (pC P))

theorem proj_eq_of_orbit {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : proj z = proj w := by
  obtain ⟨c, hc, rfl⟩ := h
  exact Top.proj_smul c hc w

theorem orbit_of_proj {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : proj z = proj w) : SameOrbit z w := by
  refine orbit_of_cross hz hw fun k i i' => ?_
  obtain ⟨j, hj⟩ := hz k
  have hN : ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hz k)).ne'
  have hM : ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hw k)).ne'
  have hj' : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := by simpa using hj
  have h1 := congrFun h ⟨k, (i, j)⟩
  have h2 := congrFun h ⟨k, (i', j)⟩
  simp only [proj] at h1 h2
  rw [div_eq_div_iff hN hM] at h1 h2
  have : (z ⟨k, i⟩ * w ⟨k, i'⟩ - z ⟨k, i'⟩ * w ⟨k, i⟩) *
      (starRingEnd ℂ (z ⟨k, j⟩) * ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    linear_combination (w ⟨k, i'⟩) * h1 - (w ⟨k, i⟩) * h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (mul_ne_zero hj' hM))

variable {P : Ideal (MRing ι)} {e : ℕ}

theorem rep_mem_mcPts (x : PtsOf P) : rep x ∈ mcPts P :=
  (mem_mcPts_iff_conePts_pC P _).2 (rep_mem x)

theorem pts_eq_of_orbit {x y : PtsOf P} (h : SameOrbit (rep x) (rep y)) : x = y := by
  apply Subtype.ext
  rw [← proj_rep x, ← proj_rep y]
  exact proj_eq_of_orbit h

def cls (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : PtsOf P :=
  ⟨proj z, z, (mem_mcPts_iff_conePts_pC P z).1 hz, rfl⟩

theorem rep_cls_orbit (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : SameOrbit (rep (cls z hz)) z :=
  orbit_of_proj (rep_mem_mcPts _).1 hz.1 (proj_rep (cls z hz))

theorem mem_mcPts_of_orbit (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h : SameOrbit z' z) : z' ∈ mcPts P := by
  have hz' := (mem_mcPts_iff_conePts_pC P z).1 hz
  refine (mem_mcPts_iff_conePts_pC P z').2 ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun h0 => hi (by
      obtain ⟨c, hc, rfl⟩ := h
      have : c k * z ⟨k, i⟩ = 0 := h0
      exact (mul_eq_zero.1 this).resolve_left (hc k))⟩
  · obtain ⟨c, hc, rfl⟩ := h
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (isMultiHomogIdeal_pC hP) c z hz'.2

theorem orbit_aff (p : (k : K) → ι k) {x : PtsOf P} (hx : x ∈ src (P := pC P) p) :
    SameOrbit (affCoord p (rep x)) (rep x) := by
  refine ⟨fun k => (rep x ⟨k, p k⟩)⁻¹, fun k => inv_ne_zero (hx k), ?_⟩
  funext q
  simp [affCoord, div_eq_inv_mul]

theorem exists_alt_variant (x : PtsOf P) : ∃ p : (k : K) → ι k, x ∈ src (P := pC P) p := by
  choose p hp using (rep_mem_mcPts x).1
  exact ⟨p, hp⟩

theorem continuousOn_aff (p : (k : K) → ι k) :
    ContinuousOn (fun x : PtsOf P => affCoord p (rep x)) (src (P := pC P) p) := by
  refine continuousOn_pi.2 fun q => ?_
  have hEval (r : Σ k, ι k × ι k) : Continuous (fun x : PtsOf P => x.1 r) :=
    (continuous_apply r).comp continuous_subtype_val
  have hDen (x : PtsOf P) (k : K) : ((∑ i, ‖rep x ⟨k, i⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos ((rep_mem x).1 k)).ne'
  have hDiag (x : PtsOf P) (hx : x ∈ src (P := pC P) p) :
      x.1 ⟨q.1, (p q.1, p q.1)⟩ ≠ 0 := by
    rw [← proj_rep x]
    exact div_ne_zero (mul_ne_zero (hx q.1) (by simpa using hx q.1)) (hDen x q.1)
  refine ((hEval ⟨q.1, (q.2, p q.1)⟩).continuousOn.div₀
    (hEval ⟨q.1, (p q.1, p q.1)⟩).continuousOn hDiag).congr ?_
  intro x hx
  have h : starRingEnd ℂ (rep x ⟨q.1, p q.1⟩) ≠ 0 := by simpa using hx q.1
  dsimp only
  rw [← proj_rep x]
  simp only [proj, affCoord]
  rw [div_div_div_cancel_right₀ (hDen x q.1), mul_div_mul_right _ _ h]

def srcOf (C : OrbitChart P e) : Set (PtsOf P) := {x | rep x ∈ C.O}

theorem mem_O_of_orbit (C : OrbitChart P e) (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ C.O)
    (h : SameOrbit z' z) (hzP : z ∈ mcPts P) : z' ∈ C.O :=
  C.O_orbit z hz z' (mem_mcPts_of_orbit hP hzP h) h

theorem isOpen_srcOf (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) : IsOpen (srcOf C) := by
  obtain ⟨O', hO', hO⟩ := C.O_open
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hOpen : IsOpen (src (P := pC P) p) := by
    have hSrc : src (P := pC P) p = ⋂ k, {y : PtsOf P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      change (∀ k, rep y ⟨k, p k⟩ ≠ 0) ↔ _
      refine forall_congr' fun k => ?_
      have hDen := Complex.ofReal_ne_zero.2 (Top.normSq_pos ((rep_mem y).1 k)).ne'
      rw [← proj_rep y]
      simp only [proj, ne_eq, div_eq_zero_iff, hDen, or_false, mul_eq_zero, map_eq_zero, or_self]
    rw [hSrc]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hS := hOpen.mem_nhds hp
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hax : affCoord p (rep x) ∈ C.O :=
    mem_O_of_orbit C hP hx (orbit_aff p hp) (rep_mem_mcPts x)
  have hax' : affCoord p (rep x) ∈ O' := by rw [hO] at hax; exact hax.1
  filter_upwards [hS, hc (hO'.mem_nhds hax')] with y hy hy'
  have h1 : affCoord p (rep y) ∈ mcPts P := mem_mcPts_of_orbit hP (rep_mem_mcPts y) (orbit_aff p hy)
  have h2 : affCoord p (rep y) ∈ C.O := by rw [hO]; exact ⟨hy', h1⟩
  exact mem_O_of_orbit C hP h2 (Proj.orbit_symm (orbit_aff p hy)) h1

theorem continuousOn_rho (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) :
    ContinuousOn (fun x : PtsOf P => C.ρ (rep x)) (srcOf C) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hOpen : IsOpen (src (P := pC P) p) := by
    have hSrc : src (P := pC P) p = ⋂ k, {y : PtsOf P | y.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
      ext y
      simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      change (∀ k, rep y ⟨k, p k⟩ ≠ 0) ↔ _
      refine forall_congr' fun k => ?_
      have hDen := Complex.ofReal_ne_zero.2 (Top.normSq_pos ((rep_mem y).1 k)).ne'
      rw [← proj_rep y]
      simp only [proj, ne_eq, div_eq_zero_iff, hDen, or_false, mul_eq_zero, map_eq_zero, or_self]
    rw [hSrc]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_ne_fun ((continuous_apply _).comp continuous_subtype_val) continuous_const
  have hS := hOpen.mem_nhds hp
  have hO : srcOf C ∈ 𝓝 x := (isOpen_srcOf hP C).mem_nhds hx
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hmem : ∀ y ∈ src (P := pC P) p, y ∈ srcOf C → affCoord p (rep y) ∈ C.O := fun y hy hy' =>
    mem_O_of_orbit C hP hy' (orbit_aff p hy) (rep_mem_mcPts y)
  have ht : Tendsto (fun y : PtsOf P => affCoord p (rep y)) (𝓝 x) (𝓝[C.O] (affCoord p (rep x))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc, ?_⟩
    filter_upwards [hS, hO] with y hy hy' using hmem y hy hy'
  have h1 := (C.ρ_cont _ (hmem x hp hx)).tendsto.comp ht
  have e1 : C.ρ (affCoord p (rep x)) = C.ρ (rep x) :=
    C.ρ_orbit _ hx _ (hmem x hp hx) (orbit_aff p hp)
  rw [e1] at h1
  refine h1.congr' ?_
  filter_upwards [hS, hO] with y hy hy'
  exact C.ρ_orbit _ hy' _ (hmem y hy hy') (orbit_aff p hy)

def clsT (x₀ : PtsOf P) (z : (Σ k, ι k) → ℂ) : PtsOf P := if h : z ∈ mcPts P then cls z h else x₀

theorem clsT_of_mem (x₀ : PtsOf P) {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : clsT x₀ z = cls z h := dite_eq_left h

theorem continuousOn_cls (C : OrbitChart P e) (x₀ : PtsOf P) :
    ContinuousOn (fun w => clsT x₀ (C.φ w)) C.D := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hφ : ContinuousOn C.φ C.D := continuousOn_pi.2 fun q => (C.holo q).continuousOn
  have h1 : ContinuousOn (fun w => proj (C.φ w)) C.D :=
    Top.continuousOn_proj.comp hφ fun w hw => (C.mem w hw).1
  refine h1.congr fun w hw => ?_
  simp only [Function.comp, clsT_of_mem x₀ (C.mem w hw), cls]

def orbChart (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) (x₀ : PtsOf P) :
    OpenPartialHomeomorph (PtsOf P) (Fin e → ℂ) where
  toFun x := C.ρ (rep x)
  invFun w := clsT x₀ (C.φ w)
  source := srcOf C
  target := C.D
  map_source' _ hx := C.ρ_mem _ hx
  map_target' w hw := by
    rw [clsT_of_mem x₀ (C.mem w hw)]
    exact mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ _) (C.mem w hw)
  left_inv' x hx := by
    have hm := C.mem _ (C.ρ_mem _ hx)
    show clsT x₀ (C.φ (C.ρ (rep x))) = x
    rw [clsT_of_mem x₀ hm]
    exact pts_eq_of_orbit (Proj.orbit_trans (rep_cls_orbit _ hm) (C.φ_ρ _ hx))
  right_inv' w hw := by
    show C.ρ (rep (clsT x₀ (C.φ w))) = w
    rw [clsT_of_mem x₀ (C.mem w hw)]
    have h1 := mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ (C.mem w hw)) (C.mem w hw)
    rw [C.ρ_orbit _ (C.φ_mem_O w hw) _ h1 (rep_cls_orbit _ (C.mem w hw)), C.ρ_φ w hw]
  open_source := isOpen_srcOf hP C
  open_target := C.isOpen_D
  continuousOn_toFun := continuousOn_rho hP C
  continuousOn_invFun := continuousOn_cls C x₀

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PlkFlagPt
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem plk_flagPt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (p : Ψ × Fin N) (k : K), M.IsFrame F → b ∈ mcPts (mCoordIdeal M.x) → M.GoodAt F (mCoordIdeal b) → (∀ τ', IsBlockDiag j (h τ')) → M.blk p = some k → FC.plk M F b (FC.flagPt M F b h) p = minorIJ (h p.1) (stepCols N j p.2) (stepCols N j p.2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M F b h p k hF hb hG hh hp
  have hCB := _root_.GlobalTheory.CompanionTheory.Ar.PB.MinorCalc.minors_main ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (CovMap.LocImg.stepCols_ne_empty M.j_le)
  have hI₀ : IsStepRows N j p.2 (stepCols N j p.2) := CovMap.LocImg.FV.isStepRows_stepCols p.2
  have hdelta : ∀ J, IsStepRows N j p.2 J →
      ∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b =
        if stepCols N j p.2 = J then 1 else 0 := by
    intro J hJ
    have hu' := fun m : ι k => (hG.2.1 ⟨k, m⟩ (stepCols N j p.2)).2
    have hu := fun m : ι k => (hG.2.1 ⟨k, m⟩ J).1
    have e1 := (CovMap.LocImg.reg_sum hb Finset.univ (fun m : ι k => F.u' (stepCols N j p.2) ⟨k, m⟩ * F.u ⟨k, m⟩ J)
      fun m _ => (CovMap.LocImg.reg_mul hb (hu' m) (hu m)).1).2
    rw [hF.2.2.1 p k hp _ J hI₀ hJ] at e1
    rw [Finset.sum_congr rfl fun m _ => ((CovMap.LocImg.reg_mul hb (hu' m) (hu m)).2).symm, ← e1]
    split_ifs
    · exact map_one (CovMap.LocImg.regVal M.x hb)
    · exact map_zero (CovMap.LocImg.regVal M.x hb)
  have e1 : FC.plk M F b (FC.flagPt M F b h) p =
      ∑ J, (∑ m : ι k, valAt M.x (F.u' (stepCols N j p.2) ⟨k, m⟩) b * valAt M.x (F.u ⟨k, m⟩ J) b) *
        minorIJ (h p.1) J (stepCols N j p.2) := by
    simp only [FC.plk, hp, Option.elim_some]
    simp_rw [flagPt_step M F b h hp, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [e1, Finset.sum_eq_single (stepCols N j p.2)]
  · rw [hdelta _ hI₀, if_pos rfl, one_mul]
  · intro J _ hne
    by_cases hJ : IsStepRows N j p.2 J
    · rw [hdelta J hJ, if_neg hne.symm, zero_mul]
    · rw [hoff J hJ, mul_zero]
  · simp

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProdXbPowEqXcOfPowStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_xb_pow_eq_xcOf_pow : ∀ {Ψ : Type} [Fintype Ψ] {p q : ℕ} {Ω : Type} [Field Ω] {n : Ψ ⊕ Ψ → ℕ}
    (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type}
    [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (m : Ψ ⊕ Ψ → ℕ)
    (c : ∀ k : NonPluckerBlocks (blkF (Ψ := Ψ) (p := p) (q := q) K₀),
      baseIdx (idx (p := p) (q := q) J₀ n) (blkF (Ψ := Ψ) (p := p) (q := q) K₀) k)
    (r : Ψ × Fin (p + q)),
    ∏ k', xb A x₀ ⟨k', c k'⟩ ^ bF m r k' =
      xcOf x₀ c ^ (rkW r.2 * m (.inl r.1) + rkO r.2 * m (.inr r.1)) *
        (if p ≤ (r.2 : ℕ) + 1 then (zOf A c (.inl r.1))⁻¹ else 1) *
        (if (r.2 : ℕ) + 1 = p + q then (zOf A c (.inr r.1))⁻¹ else 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.prod_xb_zpow_bF <;> assumption)
end

