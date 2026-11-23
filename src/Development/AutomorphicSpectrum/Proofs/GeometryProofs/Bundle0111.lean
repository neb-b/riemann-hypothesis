module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSmallGenHeightsNonneg
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0106
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeVectorBundleOfSmooth
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPositiveHermitianLine
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FS

open MvPolynomial Filter Topology
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.FubiniStudyLeviForm

theorem log_rho_eq_phi (I : Type) [Fintype I] :
    (fun z : I → ℂ => Real.log ((fsMetric («ι» := I)).ρ z)) = FubiniLevi.phi := by
  funext z
  change Real.log ‖WithLp.toLp 2 z‖ = _
  rw [EuclideanSpace.norm_eq, Real.log_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [FubiniLevi.phi, FubiniLevi.sqSum, PiLp.toLp_apply]
  ring

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem exists_block_ne {z w : (Σ k, J k) → ℂ} (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    ∃ k, ∀ c : ℂ, (fun i => w ⟨k, i⟩) ≠ fun i => c * z ⟨k, i⟩ := by
  by_contra h
  push_neg at h
  choose c hc using h
  exact hw c (funext fun p => by
    obtain ⟨k, i⟩ := p
    exact congrFun (hc k) i)

theorem levi_fsMulti_pos {z w : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hw : ∀ c : K → ℂ, w ≠ torusSmul c z) :
    0 < ReciprocityTheory.ChartRestriction.G.Geo.leviForm (fun y => Real.log ((fsMulti J).h y)) z w := by
  classical
  obtain ⟨k₀, hk₀⟩ := exists_block_ne hw
  set F : K → ((Σ k, J k) → ℂ) → ℝ :=
    fun k y => Real.log ((fsMetric («ι» := J k)).ρ (fun i => y ⟨k, i⟩)) with hF
  have hev : (fun y => Real.log ((fsMulti J).h y)) =ᶠ[𝓝 z] fun y => ∑ k ∈ Finset.univ, F k y := by
    have hopen : ∀ k, ∀ᶠ y in 𝓝 z, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hz k
      exact Filter.mem_of_superset (((continuous_apply _).isOpen_preimage _ isOpen_ne).mem_nhds hi)
        fun y hy => ⟨i, hy⟩
    filter_upwards [Filter.eventually_all.mpr hopen] with y hy
    have hpos : ∀ k, 0 < (fsMetric («ι» := J k)).ρ (fun i => y ⟨k, i⟩) := fun k => by
      obtain ⟨i, hi⟩ := hy k
      exact (fsMetric («ι» := J k)).pos _ fun h0 => hi (congrFun h0 i)
    simp only [fsMulti, HermLine.ofMetrics, zpow_one, hF]
    exact Real.log_prod fun k _ => (hpos k).ne'
  have hk0 : ∀ k, (fun i => z ⟨k, i⟩) ≠ 0 := fun k h0 => by
    obtain ⟨i, hi⟩ := hz k
    exact hi (congrFun h0 i)
  have hφ : ∀ k, ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric («ι» := J k)).ρ u)) (blockProj J k z) := by
    intro k
    have hne : blockProj J k z ≠ 0 := hk0 k
    have hsm := HilbertSamuel.ProjLine.isSmoothMetric_fs (J := J k)
    have hρ : ContDiffAt ℝ 2 (fsMetric («ι» := J k)).ρ (blockProj J k z) :=
      (hsm.contDiffAt (isOpen_ne.mem_nhds hne)).of_le (WithTop.coe_le_coe.2 le_top)
    exact hρ.log ((fsMetric («ι» := J k)).pos _ hne).ne'
  have hFk : ∀ k, F k = (fun u => Real.log ((fsMetric («ι» := J k)).ρ u)) ∘ blockProj J k := fun k => rfl
  have hC : ∀ k, ContDiffAt ℝ 2 (F k) z := fun k =>
    hFk k ▸ (hφ k).comp z ((blockProj J k).restrictScalars ℝ).contDiff.contDiffAt
  have hL : ∀ k v, ReciprocityTheory.AnForm.levi (F k) z v = ReciprocityTheory.ChartRestriction.G.Geo.leviForm (fun u => Real.log ((fsMetric («ι» := J k)).ρ u))
      (fun i => z ⟨k, i⟩) (fun i => v ⟨k, i⟩) := fun k v => by
    rw [hFk, ReciprocityTheory.AnForm.levi_comp v ((blockProj J k).analyticAt z) (hφ k), (blockProj J k).fderiv]
    rfl
  have hnn : ∀ k v, 0 ≤ ReciprocityTheory.AnForm.levi (F k) z v := fun k v => by
    rw [hL]
    exact HilbertSamuel.ProjLine.leviForm_log_fs_nonneg (hk0 k) _
  have hpos : 0 < ReciprocityTheory.AnForm.levi (F k₀) z w := by
    rw [hL, log_rho_eq_phi]
    exact FubiniLevi.levi_phi_pos_of_ne (hz k₀) hk₀
  have hsum := levi_sum_nonneg F (fun k => hC k) hnn w (Finset.univ.erase k₀)
  change 0 < ReciprocityTheory.AnForm.levi _ z w
  rw [ReciprocityTheory.AnForm.levi_congr hev]
  have hsplit : (fun y => ∑ k ∈ Finset.univ, F k y) =
      fun y => F k₀ y + 1 * ∑ k ∈ Finset.univ.erase k₀, F k y := by
    funext y
    rw [_root_.one_mul]
    exact (Finset.add_sum_erase Finset.univ (fun k => F k y) (Finset.mem_univ k₀)).symm
  rw [hsplit, ReciprocityTheory.AnForm.levi_add_smul 1 (hC k₀) hsum.1 w]
  linarith [hsum.2]

theorem isPositiveRel_fsMulti (P : Ideal (MRing J)) : IsPositiveRel P (fsMulti J) :=
  ⟨FsLineSmooth.proof K J, fun _ hz _ _ hw => levi_fsMulti_pos hz.1 hw⟩

theorem isConjInvariantH_fsMulti : IsConjInvariantH (fsMulti J) := by
  intro z
  simp [fsMulti, HermLine.ofMetrics, fsMetric, EuclideanSpace.norm_eq]

def chartForm (c : ∀ k, J k) : MRing J := ∏ k, X ⟨k, c k⟩

theorem isMultiHomog_chartForm (c : ∀ k, J k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (chartForm c) fun k => ((fsMulti J).a k).toNat := by
  classical
  have h := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c (fun _ : K => 1)
  simpa [chartForm, fsMulti, HermLine.ofMetrics, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow] using h

theorem chartForm_le (c : ∀ k, J k) (z : (Σ k, J k) → ℂ) :
    ‖eval z (map (Int.castRingHom ℂ) (chartForm c))‖ ≤ (fsMulti J).h z := by
  have e : eval z (map (Int.castRingHom ℂ) (chartForm c)) = ∏ k, z ⟨k, c k⟩ := by
    simp [chartForm, map_prod]
  rw [e, norm_prod]
  simp only [fsMulti, HermLine.ofMetrics, zpow_one]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun k _ => ?_
  exact PiLp.norm_apply_le (WithLp.toLp 2 (fun i => z ⟨k, i⟩)) (c k)

theorem exists_chartForm_notMem {Q : Ideal (MRing J)} (hQ : IsMultiProjPrime Q) :
    ∃ c, chartForm c ∉ Q := by
  choose c hc using hQ.2.2
  refine ⟨c, fun h => ?_⟩
  obtain ⟨k, -, hk⟩ := (hQ.1.prod_mem_iff).1 h
  exact hc k hk

theorem heights_fsMulti {II : IntersectionSystem} (hII : IsIntersectionSystem II) {W : Ideal (MRing J)}
    (hW : IsArithVar W 1) : 0 ≤ II K J W 1 ![fsMulti J] := by
  classical
  let e := Fintype.equivFin (∀ k, J k)
  refine HilbertSamuel.SmallGenHeightsNonneg.proof K J ⊥ (fsMulti J) II _ (fun j => chartForm (e.symm j)) hII
    (FsLineSmooth.proof K J) (fun k => ?_) (fun j => isMultiHomog_chartForm _) (fun Q hQ _ => ?_)
    (fun j z _ => chartForm_le _ z) W hW bot_le
  · show (0 : ℤ) ≤ 1
    exact zero_le_one
  · obtain ⟨c, hc⟩ := exists_chartForm_notMem hQ
    exact ⟨e c, by simpa using hc⟩

end GlobalTheory.CompanionTheory.Ar.FS

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

theorem exists_fubiniStudy_line :
    ∀ (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P : Ideal (MRing J)),
      IsFullIntersectionSystem II → ∃ A : HermLine J, (∀ k, A.a k = 1) ∧ IsPositiveRel P A ∧ IsConjInvariantH A ∧
        ∀ W : Ideal (MRing J), IsArithVar W 1 → 0 ≤ II K J W 1 ![A] :=
  fun _ _ _ _ _ P hII => ⟨GroundTheory.Heights₂.Heights.fsMulti _, fun _ => rfl, FS.isPositiveRel_fsMulti P,
    FS.isConjInvariantH_fsMulti, fun _ hW => FS.heights_fsMulti hII.1 hW⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatOnLogResolutionCorr
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem isFlatOn_corr : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (P Jd : Ideal (MRing J)) (D : ℕ) (R : AnLogRes P Jd D) (Ψ : Type) (N : ℕ) (T : Ψ × Fin N → HermLine J), (∀ r, IsFlatOn R (T r)) → ∀ a, IsFlatOn R (corr T a) := by
  intro K _ J _ P Jd D R Ψ N T hT a x _
  cases a with
  | none =>
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun _ => 0, fun j => analyticOnNhd_const, fun y _ => ?_⟩
    simp [potOf, corr, Top.trivLine, LocPot.ofFun]
  | some r =>
    choose V hVo hxV G hG hE using fun k : Fin N => hT (r.1, k) x (Set.mem_univ x)
    refine ⟨R.U x ∩ ⋂ k, V k, (R.isOpen_U x).inter (isOpen_iInter_of_finite hVo),
      ⟨R.mem_U x, Set.mem_iInter.2 hxV⟩, fun y => -∑ k ∈ Finset.Iic r.2, G k y, fun j w hw => ?_, fun y hy => ?_⟩
    · have hs : ∀ k ∈ Finset.Iic r.2, AnalyticAt ℂ (G k ∘ (R.A.chart j).symm) w := fun k _ =>
        hG k j w ⟨hw.1, Set.mem_iInter.1 hw.2.2 k⟩
      exact (Finset.analyticAt_fun_sum _ hs).neg
    · have hm := (R.mem x y hy.1).1
      have e : (potOf R (corr T (some r))).φ x y = -∑ k ∈ Finset.Iic r.2, Real.log ((T (r.1, k)).h (R.lift x y)) :=
        log_stepLine (fun k => T (r.1, k)) r.2 hm
      have e' : ∀ k, Real.log ((T (r.1, k)).h (R.lift x y)) = (G k y).re := fun k => by
        simpa [potOf, LocPot.ofFun] using hE k y (Set.mem_iInter.1 hy.2 k)
      simp [e, e', LocPot.ofFun]

end GlobalTheory.CompanionTheory.Ar.Chg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentFourth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgUnit

theorem mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {R : Type}
    [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} {a : Ω} {r : R} (h : ValAt ξ z a r) (p : Cpt ξ)
    (hp : p.1 = centre z) : a ∈ regAt ξ p := by
  obtain ⟨x, hx⟩ := p
  dsimp only at hp
  subst hp
  obtain ⟨_, s, hs, -⟩ := h
  exact ⟨s, hs⟩

theorem inChart_of_coordsAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type}
    [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {w : (Σ k, J k) → R} (hw : CoordsAt ξ y z w) (c : (k : K) → J k)
    (hc : ∀ k, IsUnit (w ⟨k, c k⟩)) (p : Cpt ξ) (hp : p.1 = centre z) :
    InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
  refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => (hw.2 k _ (hc k)).1, fun c' => ?_⟩
  show (∏ k, y ⟨k, c' k⟩) / (∏ k, y ⟨k, c k⟩) ∈ regAt ξ p
  rw [← Finset.prod_div_distrib]
  refine prod_mem fun k _ => ?_
  obtain ⟨r, hr, -⟩ := (hw.2 k _ (hc k)).2 (c' k)
  exact mem_regAt_of_valAt hr p hp

theorem exists_unit_of_span_eq {Ω : Type} [Field Ω] (R : Subring Ω) {a b : Ω} (ha : a ≠ 0)
    (h : Submodule.span R {a} = Submodule.span R {b}) : ∃ u : Ω, u ∈ R ∧ u⁻¹ ∈ R ∧ a = u * b := by
  have h1 : a ∈ Submodule.span R {b} := h ▸ Submodule.mem_span_singleton_self a
  have h2 : b ∈ Submodule.span R {a} := h ▸ Submodule.mem_span_singleton_self b
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h2
  have hr' : (r : Ω) * b = a := hr
  have ht' : (t : Ω) * a = b := ht
  have hrt : (r : Ω) * t = 1 := by
    apply mul_right_cancel₀ ha
    rw [_root_.mul_assoc, ht', hr', _root_.one_mul]
  refine ⟨r, r.2, ?_, hr'.symm⟩
  rw [inv_eq_of_mul_eq_one_right hrt]
  exact t.2

theorem zpow_mem_of_inv_mem {Ω : Type} [Field Ω] (R : Subring Ω) {u : Ω} (h : u ∈ R) (h' : u⁻¹ ∈ R) (n : ℤ) :
    u ^ n ∈ R := by
  cases n with
  | ofNat m => simpa using pow_mem h m
  | negSucc m =>
    rw [zpow_negSucc, ← inv_pow]
    exact pow_mem h' _

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem tens_unit_eq {Λ : Lat ξ Ω} {p : Cpt ξ} {s : Ω} (hs : Λ.IsGenAt p s) (n : ℤ) :
    Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {s ^ n} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro t ⟨s', hs', rfl⟩
    have h' := hs' ()
    obtain ⟨u, hu, hu', e⟩ := exists_unit_of_span_eq (regAt ξ p) h'.1 (h'.2.symm.trans hs.2)
    refine Submodule.mem_span_singleton.2 ⟨⟨u ^ n, zpow_mem_of_inv_mem _ hu hu' n⟩, ?_⟩
    show u ^ n * s ^ n = _
    simp [e, mul_zpow]
  · refine Submodule.span_le.2 ?_
    rintro t rfl
    exact Submodule.subset_span ⟨fun _ => s, fun _ => hs, by simp⟩

theorem exists_gen_of_tens {Λ : Lat ξ Ω} {p : Cpt ξ} {g : Ω} {n : ℤ} (hg : g ≠ 0)
    (h : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = Submodule.span (regAt ξ p) {g}) : ∃ s, Λ.IsGenAt p s := by
  by_contra hn
  have hempty : {t | ∃ s : Unit → Ω, (∀ i, Λ.IsGenAt p (s i)) ∧ t = ∏ i, s i ^ (fun _ => n) i} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨s, hs, -⟩
    exact hn ⟨_, hs ()⟩
  have h0 : Lat.tens (fun _ : Unit => Λ) (fun _ => n) p = ⊥ := by
    show Submodule.span _ _ = ⊥
    rw [hempty, Submodule.span_empty]
  have hm : g ∈ Submodule.span (regAt ξ p) {g} := Submodule.mem_span_singleton_self g
  rw [← h, h0] at hm
  exact hg ((Submodule.mem_bot _).1 hm)

theorem exists_value_of_unit (hξ : IsCptGen ξ) (z : Spec (CommRingCat.of ℂ) ⟶ X) (hz : genPt ξ ⤳ centre z) {f : Ω}
    (hf : f ≠ 0) (h1 : f ∈ regAt ξ ⟨centre z, hz⟩) (h2 : f⁻¹ ∈ regAt ξ ⟨centre z, hz⟩) :
    ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z f u := by
  obtain ⟨s, hs⟩ := h1
  obtain ⟨t, ht⟩ := h2
  have hst : s * t = 1 := hξ.inj ⟨centre z, hz⟩ (by rw [map_mul, hs, ht, map_one, mul_inv_cancel₀ hf])
  refine ⟨(Scheme.stalkClosedPointTo z).hom s, fun h0 => ?_, hz, s, hs, rfl⟩
  exact ((IsUnit.of_mul_eq_one t hst).map (Scheme.stalkClosedPointTo z).hom).ne_zero h0

theorem comparison_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀) (r : CMType H × Fin (D.p + D.q)), Function.Injective β → CharZero Ω → (∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) → GenPull Fl₀ Fl i hd → (Fl₀.rootLat r).IsDegOn Set.univ y₀ a₀ e₀ → (Fl.rootLat r).IsDegOn Set.univ y a e → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → unitAt 𝔐.ξ p (i a) → unitAt 𝔐₀.ξ (pushCpt hd p) a) → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → CoordsAt 𝔐₀.ξ y₀ (z ≫ h) (fun p => w (blkV bk bx p))) → ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) → ∃ u : ℂ, u ≠ 0 ∧ ValAt 𝔐.ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl bk bx a a₀ e e₀ r hβ hΩ
    hy hgen hdeg₀ hdeg hunit hreg hco z w hw cc c₀ hc hc₀
  haveI := hΩ
  have hz : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  let q : Cpt 𝔐.ξ := ⟨centre z, hz⟩
  let q₀ : Cpt 𝔐₀.ξ := pushCpt hd q
  have hw₀ := hco z w hw
  have huc : ∀ k, IsUnit (w ⟨k, cc k⟩) := fun k => IsUnit.mk0 _ (hc k)
  have huc₀ : ∀ k, IsUnit ((fun p => w (blkV bk bx p)) (⟨k, c₀ k⟩ : Σ k, J₀ k)) := fun k => IsUnit.mk0 _ (hc₀ k)
  have hq₀c : q₀.1 = centre (z ≫ h) := rfl
  have hq : (Fl.rootLat r) q = Submodule.span (regAt 𝔐.ξ q) {(∏ k, y ⟨k, cc k⟩ ^ a k) * e} :=
    hdeg.2 q trivial cc (inChart_of_coordsAt hw cc huc q rfl)
  have hq₀ : (Fl₀.rootLat r) q₀ = Submodule.span (regAt 𝔐₀.ξ q₀) {(∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀} :=
    hdeg₀.2 q₀ trivial c₀ (inChart_of_coordsAt hw₀ c₀ huc₀ q₀ hq₀c)
  have hg : (∏ k, y ⟨k, cc k⟩ ^ a k) * e ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k _ (huc k)).1) hdeg.1
  have hg₀ : (∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw₀.2 k _ (huc₀ k)).1) hdeg₀.1
  obtain ⟨s₀, hs₀⟩ := exists_gen_of_tens
    (Λ := (𝔐₀.V (HodgeCpt.rootIdx D r).1).gr (Fl₀.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2)
    (n := HodgeCpt.rootSgn D r) hg₀ hq₀
  have e₁ := tens_unit_eq hs₀ (HodgeCpt.rootSgn D r)
  obtain ⟨u₀, hu₀, hu₀', hgu⟩ := exists_unit_of_span_eq (regAt 𝔐₀.ξ q₀) hg₀ (hq₀.symm.trans e₁)
  have hs : ((𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2).IsGenAt q
      (i s₀) := hgen q (fun p hp => not_inFibre 𝔐.ξ z hz hp) _ _ s₀ hs₀
  have e₂ := tens_unit_eq hs (HodgeCpt.rootSgn D r)
  obtain ⟨v, hv, hv', hgv⟩ := exists_unit_of_span_eq (regAt 𝔐.ξ q) (zpow_ne_zero _ hs.1) (e₂.symm.trans hq)
  have hfe : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) = i u₀ * v := by
    rw [hgu, map_mul, map_zpow₀, hgv, ← _root_.mul_assoc (i u₀) v]
    exact mul_div_cancel_right₀ _ hg
  have hf : i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, cc k⟩ ^ a k) * e) ≠ 0 :=
    div_ne_zero ((map_ne_zero i).2 hg₀) hg
  refine exists_value_of_unit 𝔐.tie.gen z hz hf ?_ ?_
  · rw [hfe]
    exact mul_mem (hreg q _ hu₀) hv
  · rw [hfe, mul_inv, ← map_inv₀]
    exact mul_mem (hreg q _ hu₀') hv'

end GlobalTheory.CompanionTheory.Ar.ChgUnit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompDescentThird
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

theorem normPull_of_stalks : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S₀ S : Finset ℕ) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (j : 𝔐₀.Li →+ 𝔐.Li), CharZero Ω → (∀ (p : Cpt 𝔐.ξ) (a : Ω₀), a ∈ regAt 𝔐₀.ξ (pushCpt hd p) → i a ∈ regAt 𝔐.ξ p) → (∀ (a : Ω₀) e, j (a • e) = i a • j e) → (∀ (n : ℕ) (b : Fin n → 𝔐₀.Li), LinearIndependent Ω₀ b → LinearIndependent Ω fun k => j (b k)) → (∀ s a, j (Fl₀.b s a) = Fl.b s a) → (∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s, 𝔐.V s q = Submodule.span (regAt 𝔐.ξ q) (j '' (𝔐₀.V s (pushCpt hd q) : Set 𝔐₀.Li))) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐₀.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐₀.M.GramAt 𝔐₀.t.PP.L (z ≫ h) b Γ → 𝔐.M.GramAt 𝔐.t.PP.L z (fun k => j (b k)) Γ) → NormPull Fl₀ Fl i h := by
  intro E _ _ _ H D l Xo c O _ β Y S₀ S Ω₀ Ω _ _ K₀ K _ _ J₀ J _ _ y₀ y 𝔐₀ 𝔐 i h hd Fl₀ Fl j hc hreg hsl hli hfl hst hgr
    z s a t₀ ν hN
  obtain ⟨hh, b, Γ, hfs, hfr, hb, hG, hP, rfl⟩ := hN
  have hq : genPt 𝔐.ξ ⤳ centre z := 𝔐.all _
  have hbase : Fl.b s = fun k => j (Fl₀.b s k) := funext fun k => (hfl s k).symm
  have hnf : ∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r ⟨centre z, hq⟩ := fun r hr => not_inFibre 𝔐.ξ z hq hr
  have hV := hst ⟨centre z, hq⟩ hnf s
  have hpush : (⟨centre (z ≫ h), hh⟩ : Cpt 𝔐₀.ξ) = pushCpt hd ⟨centre z, hq⟩ :=
    Subtype.ext (Scheme.Hom.comp_apply z h _)
  have hfr' : (𝔐₀.V s).IsFrameAt b (pushCpt hd ⟨centre z, hq⟩) := hpush ▸ hfr
  refine ⟨hq, fun k => j (b k), Γ, fun s' => ?_, ⟨hli _ b hfr.1, ?_⟩, ?_, hgr z _ b Γ hG, hP, rfl⟩
  · rw [hbase]
    exact FlagPull.flagStep_map_eq hsl hfs s'
  · rw [hV]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨e, he, rfl⟩
      have he' : e ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩) := he
      rw [hfr'.2] at he'
      clear he
      show j e ∈ Submodule.span (regAt 𝔐.ξ ⟨centre z, hq⟩) (Set.range fun k => j (b k))
      induction he' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul u x _ hx =>
        have e1 : j (u • x) = (⟨i u, hreg _ _ u.2⟩ : regAt 𝔐.ξ ⟨centre z, hq⟩) • j x := hsl (u : Ω₀) x
        rw [e1]
        exact Submodule.smul_mem _ _ hx
    · rintro _ ⟨k, rfl⟩
      refine Submodule.subset_span ⟨b k, ?_, rfl⟩
      show b k ∈ 𝔐₀.V s (pushCpt hd ⟨centre z, hq⟩)
      rw [hfr'.2]
      exact Submodule.subset_span ⟨k, rfl⟩
  · have hm := FlagPull.map_mem_flagStep hsl (Fl₀.b s) a hb
    rw [map_sub, hsl, hfl, ← hbase] at hm
    exact hm

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularSectionsOpenNeighbourhoodStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_sections_open_neighbourhood : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li),
    IsCptGen ξ → SmoothOfRelativeDimension g G.hom →
    ∀ (p : Cpt ξ) (n : ℕ) (S : Fin n → Li) (Φ : Fin n → Module.Dual Ω Li),
      (∀ j, S j ∈ M.lat p) → (∀ j, ∀ e ∈ M.lat p, Φ j e ∈ regAt ξ p) →
      ∃ U : X.Opens, p.1 ∈ U ∧ ∀ q : Cpt ξ, q.1 ∈ U →
        (∀ j, S j ∈ M.lat q) ∧ ∀ j, ∀ e ∈ M.lat q, Φ j e ∈ regAt ξ q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.lie_near <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RingOfIntegersHomInjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

theorem ringOfIntegers_hom_injective {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : Function.Injective a := by
  have hI : (RingHom.ker a).comap (algebraMap ℤ (𝓞 F)) = ⊥ := by
    rw [eq_bot_iff]
    intro n hn
    have h0 : ((n : ℤ) : R) = 0 := by
      have h1 : a (algebraMap ℤ (𝓞 F) n) = 0 := hn
      simpa using h1
    have h2 : n = 0 := by exact_mod_cast h0
    simp [h2]
  exact (RingHom.injective_iff_ker_eq_bot a).2 (Ideal.eq_bot_of_comap_eq_bot hI)

theorem exists_ringHom_extend {F : Type} [Field F] [NumberField F] {R : Type} [Field R] [CharZero R]
    (a : 𝓞 F →+* R) : ∃ κ : F →+* R, κ.comp (algebraMap (𝓞 F) F) = a :=
  ⟨IsFractionRing.lift (ringOfIntegers_hom_injective a),
    RingHom.ext fun x => IsFractionRing.lift_algebraMap (ringOfIntegers_hom_injective a) x⟩

theorem exists_isOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Sp ℂ ⟶ 𝔐.X), 𝔐.Interior z → ∃ (κ : c.F →+* ℂ) (p : Sp ℂ ⟶ Xo.X), IsOver 𝔐 z κ p := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 z hz
  have := c.fin
  haveI : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  let a : 𝓞 c.F →+* ℂ := (Spec.preimage (z ≫ 𝔐.f ≫ Y.s)).hom
  have ha : z ≫ 𝔐.f ≫ Y.s = spMap a := by
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨κ, hκ⟩ := exists_ringHom_extend a
  have hc : (z ≫ 𝔐.f) ≫ Y.s = spMap κ ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [Category.assoc, ha, ← hκ, Chg.spMap_comp']
  let w : Sp ℂ ⟶ pullback Y.s (spMap (algebraMap (𝓞 c.F) c.F)) := pullback.lift (z ≫ 𝔐.f) (spMap κ) hc
  have hw₁ : w ≫ pullback.fst _ _ = z ≫ 𝔐.f := pullback.lift_fst _ _ _
  have hw₂ : w ≫ pullback.snd _ _ = spMap κ := pullback.lift_snd _ _ _
  have := Y.jQ_open
  have hr : Set.range w ⊆ Set.range Y.jQ := by
    rintro _ ⟨u, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, hw₁, Scheme.Hom.comp_apply]
    have hu : u = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst hu
    exact (abLocus_pullback abLocusOne Y.t.semi 𝔐.m.cart.1 _).2 hz
  let x : Sp ℂ ⟶ Xo.XF c := IsOpenImmersion.lift Y.jQ w hr
  have hx : x ≫ Y.jQ = w := IsOpenImmersion.lift_fac _ _ _
  refine ⟨κ, x ≫ pullback.fst _ _, x, ?_, rfl, ?_⟩
  · rw [Model.j, ← Category.assoc, hx, hw₁]
  · rw [← Y.jQ_over, ← Category.assoc, hx, hw₂]

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
end
end

