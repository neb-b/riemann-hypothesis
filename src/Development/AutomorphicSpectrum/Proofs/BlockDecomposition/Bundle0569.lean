module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0514
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0544
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SpecializesIffPointIdealLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdFormOf
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LubinTateTeichmullerSequenceCompatibility
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv

variable {l : ℕ} [Fact l.Prime]

theorem continuous_omC : Continuous (omC (l := l)) :=
  (AddMonoidHomClass.isometry_of_norm (omC (l := l)) norm_omC).continuous

theorem tail_le (K : FinExt l) (c : ℕ → ↥(OL K)) (y x : Om l) (hy : ‖omC y‖ ≤ 1)
    (hs : HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * y ^ k) x) (D : ℕ) :
    ‖omC x - ∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i‖ ≤ ‖omC y‖ ^ D := by
  have ht : Filter.Tendsto (fun N => ∑ i ∈ Finset.range N, oc K (c i) * omC y ^ i)
      Filter.atTop (nhds (omC x)) := by
    have h1 := (continuous_omC (l := l)).continuousAt.tendsto.comp hs.tendsto_sum_nat
    refine h1.congr fun N => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Function.comp, map_sum, map_mul, map_pow]
    rfl
  have h2 := (ht.sub_const (∑ i ∈ Finset.range D, oc K (c i) * omC y ^ i)).norm
  refine le_of_tendsto h2 ?_
  filter_upwards [Filter.eventually_ge_atTop D] with N hN
  rw [← Finset.sum_Ico_eq_sub _ hN]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k hk => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (norm_oc_le_one K _)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hy (Finset.mem_Ico.1 hk).1)

theorem norm_read {ρ : ℝ} (hρ : ‖(l : ℂ_[l])‖ ≤ ρ) (a y : Tl l) (b : ℕ → Tl l)
    (A Y : ℂ_[l]) (B : ℕ → ℂ_[l]) (D : ℕ) (hY : ‖Y‖ ≤ 1) (hA : ‖sh a - A‖ ≤ ρ)
    (hy : ‖sh y - Y‖ ≤ ρ) (hb : ∀ i, ‖sh (b i) - B i‖ ≤ ρ) :
    ‖a - ∑ i ∈ Finset.range D, b i * y ^ i‖ ≤
      max ρ ‖A - ∑ i ∈ Finset.range D, B i * Y ^ i‖ := by
  have h1 : ‖sh (∑ i ∈ Finset.range D, b i * y ^ i) - ∑ i ∈ Finset.range D, B i * Y ^ i‖ ≤ ρ :=
    near_sum hρ _ fun i _ => near_mul (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hY)
      (hb i) (near_pow hρ hY hy i)
  have h2 := near_sub hρ hA h1
  rw [norm_eq_norm_sh]
  set x := a - ∑ i ∈ Finset.range D, b i * y ^ i
  set W := A - ∑ i ∈ Finset.range D, B i * Y ^ i
  have e : sh x = (sh x - W) + W := by ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h2 le_rfl)

theorem pow_read (N : ℕ) (a y : Tl l) (b : ℕ → Tl l) (D : ℕ) :
    (a - ∑ i ∈ Finset.range D, b i * y ^ i) ^ l ^ N =
      a ^ l ^ N - ∑ i ∈ Finset.range D, b i ^ l ^ N * (y ^ l ^ N) ^ i := by
  rw [sub_pow_char_pow, sum_pow_char_pow]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm i]

theorem pow_compat {f : ℕ} {u : ℕ → Tl l} (hu : ∀ n, u (n + 1) ^ l ^ f = u n) (n m : ℕ) :
    u (n + m) ^ l ^ (f * m) = u n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hu, ih]

theorem pow_fixed {f : ℕ} {x : Tl l} (hx : x ^ l ^ f = x) (m : ℕ) : x ^ l ^ (f * m) = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [mul_add, mul_one, add_comm (f * m) f, pow_add, pow_mul, hx, ih]

theorem exists_pow_le {f : ℕ} (hf : 0 < f) {ρ ε : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (hε : 0 < ε) :
    ∃ m, 2 ≤ m ∧ ρ ^ l ^ (f * m) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε h1
  refine ⟨N + 2, by omega, (pow_le_pow_of_le_one h0 h1.le ?_).trans hN.le⟩
  have h2 : N + 2 < l ^ (N + 2) := Nat.lt_pow_self (Fact.out : l.Prime).one_lt
  have h3 : l ^ (N + 2) ≤ l ^ (f * (N + 2)) :=
    Nat.pow_le_pow_right (Fact.out : l.Prime).pos (Nat.le_mul_of_pos_left _ hf)
  omega

theorem galdiv : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)) (z : ℕ → Om l) (f : ℕ), 0 < f →
    ‖(l : ℂ_[l])‖ ≤ ‖oc K π‖ → ‖oc K π‖ < 1 →
    (∀ n, ‖omC (z n)‖ < 1) → (∀ n, 2 ≤ n → ‖oc K π‖ < ‖omC (z n)‖) →
    ∀ (u : ℕ → Tl l), (∀ n, u (n + 1) ^ l ^ f = u n) → (∀ n, ‖sh (u n) - omC (z n)‖ ≤ ‖oc K π‖) →
    ∀ (r₀ : ↥(OL K) →+* Tl l), (∀ c, r₀ c ^ l ^ f = r₀ c) → (∀ c, ‖sh (r₀ c) - oc K c‖ ≤ ‖oc K π‖) →
    (∀ n, u n ≠ 0) → ∀ (g : GQ l) (c : ℕ → ↥(OL K)),
    (∀ n, HasSum (fun k : ℕ => ((c k : ↥K.1) : Om l) * z n ^ k) (g (z n))) → ∀ n D : ℕ,
    u n ^ D ∣ actT g (u n) - ∑ i ∈ Finset.range D, r₀ (c i) * u n ^ i := by
  intro l _ K π z f hf hl hπ hz1 hz2 u hu hun r₀ hr hrn hu0 g c hs n D
  rw [GroundTheory.PAdicHodge.preTilt_dvd_iff_norm_le, norm_pow]
  set ρ := ‖oc K π‖ with hρdef
  have hρ0 : 0 ≤ ρ := norm_nonneg _
  have hε : 0 < ‖u n‖ ^ D := pow_pos (norm_pos_iff.2 (hu0 n)) D
  obtain ⟨m, hm, hmρ⟩ := exists_pow_le (l := l) hf hρ0 hπ hε
  set k := n + m with hk
  have hk2 : 2 ≤ k := by omega
  have hzk : ‖omC (z k)‖ ≤ 1 := (hz1 k).le
  have hnorm : ‖omC (z k)‖ ≤ ‖u k‖ := by
    by_contra hlt
    push_neg at hlt
    have e : omC (z k) = sh (u k) - (sh (u k) - omC (z k)) := by ring
    have h3 : ‖omC (z k)‖ ≤ max ‖sh (u k)‖ ρ := by
      conv_lhs => rw [e, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le_max le_rfl (by rw [norm_neg]; exact hun k))
    rcases le_max_iff.1 h3 with h4 | h4
    · rw [← norm_eq_norm_sh] at h4; linarith
    · linarith [hz2 k hk2]
  have hA : ‖sh (actT g (u k)) - omC (g (z k))‖ ≤ ρ := by
    rw [sh_actT, ← galCp_omC, ← map_sub, norm_galCp]
    exact hun k
  have hread := norm_read hl (actT g (u k)) (u k) (fun i => r₀ (c i)) (omC (g (z k))) (omC (z k))
    (fun i => oc K (c i)) D hzk hA (hun k) (fun i => hrn _)
  have htail := tail_le K c (z k) (g (z k)) hzk (hs k) D
  have hx : ‖actT g (u k) - ∑ i ∈ Finset.range D, r₀ (c i) * u k ^ i‖ ≤ max ρ (‖u k‖ ^ D) :=
    hread.trans (max_le_max le_rfl (htail.trans (pow_le_pow_left₀ (norm_nonneg _) hnorm D)))
  have hpow := pow_read (f * m) (actT g (u k)) (u k) (fun i => r₀ (c i)) D
  have hc : u k ^ l ^ (f * m) = u n := pow_compat hu n m
  have ha : actT g (u k) ^ l ^ (f * m) = actT g (u n) := by rw [← map_pow, hc]
  simp only [pow_fixed (hr _) m, hc, ha] at hpow
  rw [← hpow, norm_pow]
  have hun' : ‖u k‖ ^ l ^ (f * m) = ‖u n‖ := by rw [← norm_pow, hc]
  refine (pow_le_pow_left₀ (norm_nonneg _) hx _).trans ?_
  rcases le_total ρ (‖u k‖ ^ D) with h | h
  · rw [max_eq_right h, ← pow_mul, mul_comm, pow_mul, hun']
  · rw [max_eq_left h]; exact hmρ

end GlobalTheory.CompanionTheory.LTPer.Tilt.GalDiv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapEqOne
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.AlgStab

section Gen
variable {R : Type} [CommRing R] {a n : ℕ}

private noncomputable def twoSide [TopologicalSpace R] [IsTopologicalRing R] (h hi : Matrix (Fin a) (Fin a) R)
    (g gi : Matrix (Fin n) (Fin n) R) (h1 : h * hi = 1) (h2 : hi * h = 1) (g1 : g * gi = 1) (g2 : gi * g = 1) :
    Matrix (Fin a) (Fin n) R ≃ₜ Matrix (Fin a) (Fin n) R where
  toFun X := h * X * g
  invFun X := hi * X * gi
  left_inv X := by
    show hi * (h * X * g) * gi = X
    rw [Matrix.mul_assoc h, ← Matrix.mul_assoc hi, h2, Matrix.one_mul, Matrix.mul_assoc, g1, Matrix.mul_one]
  right_inv X := by
    show h * (hi * X * gi) * g = X
    rw [Matrix.mul_assoc hi, ← Matrix.mul_assoc h, h1, Matrix.one_mul, Matrix.mul_assoc, g2, Matrix.mul_one]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private theorem map_inv {S : Type} [CommRing S] (f : R →+* S) {x y : Matrix (Fin a) (Fin a) R} (h : x * y = 1) :
    x.map f * y.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero f) (map_one f)]

private theorem map_eq_one {S : Type} [CommRing S] (f : R →+* S) {e : R} (he : f e = 0) {x : Matrix (Fin a) (Fin a) R}
    (h : e • (x - 1) = x - 1) : x.map f = 1 := by
  have h0 : (x - 1).map f = 0 := by
    rw [← h]
    ext i j
    simp [he]
  rw [Matrix.map_sub _ (map_sub f), Matrix.map_one _ (map_zero f) (map_one f)] at h0
  exact sub_eq_zero.1 h0

private noncomputable def famEquiv {T : Type} [Fintype T] (h hi : T → Matrix (Fin a) (Fin a) ℂ) (g gi : T → Matrix (Fin n) (Fin n) ℂ)
    (h1 : ∀ τ, h τ * hi τ = 1) (h2 : ∀ τ, hi τ * h τ = 1) (g1 : ∀ τ, g τ * gi τ = 1) (g2 : ∀ τ, gi τ * g τ = 1) :
    (T → Fin a → Fin n → ℂ) ≃L[ℝ] (T → Fin a → Fin n → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun X τ => (h τ * Matrix.of (X τ) * g τ : Matrix (Fin a) (Fin n) ℂ)
      invFun := fun X τ => (hi τ * Matrix.of (X τ) * gi τ : Matrix (Fin a) (Fin n) ℂ)
      map_add' := fun X Y => by
        funext τ
        show h τ * (Matrix.of (X τ) + Matrix.of (Y τ)) * g τ = h τ * Matrix.of (X τ) * g τ + h τ * Matrix.of (Y τ) * g τ
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c X => by
        funext τ
        show h τ * (c • Matrix.of (X τ)) * g τ = c • (h τ * Matrix.of (X τ) * g τ)
        rw [Matrix.mul_smul, Matrix.smul_mul]
      left_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).left_inv (Matrix.of (X τ))
      right_inv := fun X => funext fun τ => (twoSide (h τ) (hi τ) (g τ) (gi τ) (h1 τ) (h2 τ) (g1 τ) (g2 τ)).right_inv (Matrix.of (X τ)) }

end Gen

private theorem schw {D : D7} (θ : InfFam D) {a n : ℕ} (h : GL (Fin a) (AE D)) (g : GL (Fin n) (AE D)) {Φ : Mx D a n → ℂ}
    (hΦ : Φ ∈ schwartzA θ a n) : (fun X => Φ (mm (mm h.1 X) g.1)) ∈ schwartzA θ a n := by
  induction hΦ using Submodule.span_induction with
  | zero => exact Submodule.zero_mem _
  | add f₁ f₂ _ _ i₁ i₂ => exact Submodule.add_mem _ i₁ i₂
  | smul c f _ i => exact Submodule.smul_mem _ c i
  | mem Φ hm =>
    obtain ⟨f, k, hk, rfl⟩ := hm
    haveI : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    let ρ : D.what₂.Tau → (AE D →+* ℂ) := fun τ => (θ τ).comp (infPart D)
    let L := famEquiv (fun τ => h.1.map (ρ τ)) (fun τ => h.2.map (ρ τ)) (fun τ => g.1.map (ρ τ)) (fun τ => g.2.map (ρ τ))
      (fun τ => map_inv _ h.3) (fun τ => map_inv _ h.4) (fun τ => map_inv _ g.3) (fun τ => map_inv _ g.4)
    let H := twoSide (h.1.map (finPart D)) (h.2.map (finPart D)) (g.1.map (finPart D)) (g.2.map (finPart D))
      (map_inv _ h.3) (map_inv _ h.4) (map_inv _ g.3) (map_inv _ g.4)
    refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun y => k (H y),
      ⟨hk.1.comp_continuous H.continuous, hk.2.comp_homeomorph H⟩, ?_⟩
    funext X
    have e1 : (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) = L (fun τ i j => compAt θ τ X i j) := by
      funext τ
      show (h.1 * X * g.1).map (ρ τ) = h.1.map (ρ τ) * X.map (ρ τ) * g.1.map (ρ τ)
      rw [Matrix.map_mul, Matrix.map_mul]
    have e2 : (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = H (fun i j => finPart D (X i j)) := by
      show (h.1 * X * g.1).map (finPart D) = h.1.map (finPart D) * X.map (finPart D) * g.1.map (finPart D)
      rw [Matrix.map_mul, Matrix.map_mul]
    show f (fun τ i j => compAt θ τ (mm (mm h.1 X) g.1) i j) * k (fun i j => finPart D (mm (mm h.1 X) g.1 i j)) = _
    rw [e1, e2]
    rfl

end GlobalTheory.CompanionTheory.AlgStab

open GlobalTheory.CompanionTheory.AlgStab in
theorem GlobalTheory.CompanionTheory.AlgStab.algStab : IdemEx → AlgStab := by
  intro _ D θ _ a n S e he h g hh hg Φ hΦ hG hC
  refine ⟨schw θ h g hΦ, fun X => ?_, ?_⟩
  · have hI : IntOff S (mm (mm h.1 X) g.1) ↔ IntOff S X := by
      refine forall_congr' fun v => forall_congr' fun hv => ?_
      have h0 : cv D v e = 0 := by rw [he.2 v, if_neg hv]
      have : (h.1 * X * g.1).map (cv D v) = X.map (cv D v) := by
        rw [Matrix.map_mul, Matrix.map_mul, map_eq_one _ h0 hh, map_eq_one _ h0 hg, Matrix.one_mul, Matrix.mul_one]
      refine forall_congr' fun i => forall_congr' fun j => ?_
      rw [show cv D v (mm (mm h.1 X) g.1 i j) = cv D v (X i j) from congrFun (congrFun this i) j]
    have hs : e • mm (mm h.1 X) g.1 = mm (mm h.1 (e • X)) g.1 := by
      show e • (h.1 * X * g.1) = h.1 * (e • X) * g.1
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have := hG (mm (mm h.1 X) g.1)
    by_cases hX : IntOff S X
    · rw [if_pos (hI.2 hX), hs] at this
      rw [if_pos hX]
      exact this
    · rw [if_neg (fun c => hX (hI.1 c))] at this
      rw [if_neg hX]
      exact this
  · haveI : IsTopologicalRing (AE D) := by first | infer_instance | exact GlobalTheory.AdelicU.isTopologicalRing_tens | exact isTopologicalRing_tens
    exact hC.comp_homeomorph (twoSide h.1 h.2 g.1 g.2 h.3 h.4 g.3 g.4)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableDensityFromBoxVolumeGrowthStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_box_radius_tail_lintegral_le_eps_mul : ∀ (K W : Type) [CommRing K] [Fintype W] (κ : K ≃+* (W → ℂ)) (n M : ℕ) (H : Type) [MeasurableSpace H] [MeasurableSpace (Fin n → Fin M → K)] (μ : Measure (Fin n → Fin M → K)) (ν : Measure H) (q : (Fin n → Fin M → K) → H) (C₀ : ℝ≥0∞), C₀ ≠ ⊤ → (∀ r : Fin n → W → ℝ, (∀ a w, 0 < r a w) → GlobalTheory.CompanionTheory.WhitFree.AvgInf.DenLE μ ν q (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ r) (C₀ * ∏ a, ∏ w, ENNReal.ofReal (r a w) ^ (2 * (M - n)))) → Measurable q → (∀ r : Fin n → W → ℝ, MeasurableSet (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK (M := M) κ r)) → ∀ φ : (Fin n → Fin M → K) → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ X, X ∉ GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R) → ‖φ X‖ ≤ C / R ^ k) → ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ R : ℝ, 1 ≤ R ∧ ∀ Y, MeasurableSet Y → ∫⁻ X in (GlobalTheory.CompanionTheory.WhitFree.AvgInf.boxK κ (fun _ _ => R))ᶜ ∩ q ⁻¹' Y, ‖φ X‖ₑ ∂μ ≤ ε * ν Y := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | exact GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density | (intros; apply GlobalTheory.CompanionTheory.WhitFree.AvgInf.tail_small_of_density <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleCodimensionOne
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.CompanionTheory.MixZ

theorem codimOne_holds : CodimOne := by
  intro X _ p D hD z hz
  let C : Closeds X := ⟨closure {z}, isClosed_closure⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  haveI : IsReduced I.subscheme := GlobalTheory.ReducedSubgroup.isReduced_subscheme_vanishingIdeal C
  have hrange : Set.range I.subschemeι = closure {z} := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  have hemb : Topology.IsEmbedding I.subschemeι := I.subschemeι.isClosedEmbedding.isEmbedding
  haveI : IrreducibleSpace I.subscheme := by
    have hs : IsIrreducible (Set.range I.subschemeι) := by
      rw [hrange]; exact isIrreducible_singleton.closure
    haveI := Subtype.irreducibleSpace hs
    have h2 := (IrreducibleSpace.isIrreducible_univ (Set.range I.subschemeι)).image
      hemb.toHomeomorph.symm hemb.toHomeomorph.symm.continuous.continuousOn
    rw [Set.image_univ_of_surjective hemb.toHomeomorph.symm.surjective] at h2
    exact (irreducibleSpace_def _).2 h2
  haveI : IsIntegral I.subscheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hgen : I.subschemeι (genericPoint I.subscheme) = z := by
    have h1 := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
    rw [Set.image_univ, hrange, closure_closure] at h1
    exact h1.eq isGenericPoint_closure
  have key := GlobalTheory.PrimeDivDim.dim_eq_of_coheight_eq_one ℤ X p D hD I.subscheme I.subschemeι
    (by rw [hgen]; exact hz)
  calc topologicalKrullDim (closure ({z} : Set X))
      = topologicalKrullDim I.subscheme := GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hemb hrange
    _ = D := key

end GlobalTheory.CompanionTheory.MixZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulticonePointDescendsToSubvariety
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

noncomputable section

namespace GlobalTheory.CompanionTheory.MPDict.UnderSub

open GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageInverse (mConeMap_of_isMultiHomog)
open GlobalTheory.CompanionTheory.MPDict.Onto GlobalTheory.CompanionTheory.MPDict.Under

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem point_eq_pt {N : ℕ} (t : Fin (N + 1) → ℂ) (ht : t ≠ 0) (hu : Ideal.span (Set.range t) = ⊤) :
    GlobalTheory.TuplePoint.point ℤ t ht = GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) t hu := by
  unfold GlobalTheory.TuplePoint.point GlobalTheory.ProjSpace.pt
  congr 1

theorem le_mCoordIdeal_of_mem_mcPts {P : Ideal (Geo.MRing (Bk n))} (hP : Geo.IsMultiHomogIdeal P)
    {z : (Σ k, Bk n k) → ℂ} (hz : z ∈ mcPts P) : P ≤ Geo.mCoordIdeal z := by
  obtain ⟨S, hS, hPS⟩ := hP
  have h0 := hz.2
  rw [hPS, Ideal.span_le]
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  have e : aeval z f = 0 := by
    have := h0 f (hPS ▸ Ideal.subset_span hf)
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map]
    simpa using this
  rw [SetLike.mem_coe, Geo.mCoordIdeal, RingHom.mem_ker, mConeMap_of_isMultiHomog _ ha, e, C_0, mul_zero]

theorem ptIdeal_of_isUnder {z : (Σ k, Bk n k) → ℂ} (hz' : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    {w : CxPts (mpStr ℤ m n) σ₀} (H : IsUnder w z) :
    ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) = Geo.mCoordIdeal z := by
  have ht := blockVec_ne_zero hz'
  have hu : ∀ k, Ideal.span (Set.range fun i : Bk n k => z ⟨k, i⟩) = ⊤ := fun k => by
    obtain ⟨i, hi⟩ := hz' k
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨i, rfl⟩) (isUnit_iff_ne_zero.2 hi)
  let a : ∀ k, Sp ℂ ⟶ PSpace ℤ (n k) := fun k =>
    GlobalTheory.ProjSpace.pt (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
  let g : Sp ℂ ⟶ MP ℤ m n := w.1
  have hg : ∀ k, g ≫ prB n k = a k := fun k =>
    (comp_of_isUnder ht hz' H k).trans (point_eq_pt _ _ (hu k))
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  let x : MP ℤ m n := g p
  let θ : ℂ →+* (Sp ℂ).residueField p :=
    ((Sp ℂ).evaluation ⊤ p trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
  let ρ : (MP ℤ m n).residueField x →+* (Sp ℂ).residueField p := (g.residueFieldMap p).hom
  have key : ∀ (k : Fin (m + 1)) (j : Bk n k),
      θ (z ⟨k, ptChart x k⟩) * ρ (ptCoord x ⟨k, j⟩) = θ (z ⟨k, j⟩) := by
    intro k j
    have hx : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
    have hW : g ⁻¹ᵁ blockChart n k (ptChart x k) ≤ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      rw [← hg k]
      exact le_of_eq rfl
    have e1 : ρ (ptCoord x ⟨k, j⟩) = ((Sp ℂ).evaluation _ p hx).hom
        (pullRatio (a k) (g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) hW j) := by
      refine (Scheme.evaluation_naturality_apply g p hx _).trans ?_
      refine congrArg _ ?_
      have := appLE_pullRatio (φ := prB n k) (W := blockChart n k (ptChart x k)) (i := ptChart x k)
        (hi := le_rfl) (j := j) g (T := g ⁻¹ᵁ blockChart n k (ptChart x k)) le_rfl
      exact this.trans (pullRatio_of_eq (hg k) _ _)
    have e2 := pullRatio_pt_mul (Int.castRingHom ℂ) (fun i : Bk n k => z ⟨k, i⟩) (hu k)
      (W := g ⁻¹ᵁ blockChart n k (ptChart x k)) (ptChart x k) j hW
    have e3 : ∀ b : ℂ, ((Sp ℂ).evaluation _ p hx).hom (fnOn (g ⁻¹ᵁ blockChart n k (ptChart x k)) b) = θ b :=
      fun b => evaluation_resG' le_top p hx _
    have := congrArg ((Sp ℂ).evaluation _ p hx).hom e2
    rw [map_mul, e3, e3] at this
    rw [e1, mul_comm]
    exact this
  have hne : ∀ k, θ (z ⟨k, ptChart x k⟩) ≠ 0 := by
    intro k
    refine (map_ne_zero θ).2 fun h0 => ?_
    have hx : p ∈ a k ⁻¹ᵁ chart ℤ (n k) (ptChart x k) := by
      have : g p ∈ blockChart n k (ptChart x k) := mem_ptChart x k
      rw [← hg k]
      exact this
    rw [GlobalTheory.ProjSpace.pt_preimage_chart, GlobalTheory.ProjSpace.mem_spOpen] at hx
    exact hx (h0 ▸ Ideal.zero_mem _)
  change ptIdeal x = _
  rw [ptIdeal, ← mCoordIdeal_comp_ringHom ρ, ← mCoordIdeal_comp_ringHom θ z,
    ← mCoordIdeal_blockScale (fun k => θ (z ⟨k, ptChart x k⟩)) hne]
  congr 1
  funext q
  obtain ⟨k, j⟩ := q
  exact key k j

theorem exists_cxPt_of_mem_mcPts : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (z : (Σ k, Bk n k) → ℂ), z ∈ mcPts (ptIdeal (i (genericPoint X))) →
    ∃ y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀, IsUnder (PtsOver.map i rfl _ y) z := by
  intro m n X _ i _ z hz
  obtain ⟨w, hw, -⟩ := existsUnique_isUnder m n z hz.1
  have hP : ptIdeal (i (genericPoint X)) ≤ ptIdeal (w.1 (IsLocalRing.closedPoint ℂ)) := by
    rw [ptIdeal_of_isUnder hz.1 hw]
    exact le_mCoordIdeal_of_mem_mcPts (isMultiProjPrime_ptIdeal m n _).2.1 hz
  have hs := (_root_.GlobalTheory.CompanionTheory.MPDict.Spec.specializes_iff_ptIdeal_le m n _ _).2 hP
  have hr : w.1 (IsLocalRing.closedPoint ℂ) ∈ Set.range i :=
    hs.mem_closed i.isClosedEmbedding.isClosed_range ⟨_, rfl⟩
  have : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  obtain ⟨f, hf⟩ := GlobalTheory.exists_lift_closedImmersion_of_dense i w.1 Set.univ dense_univ
    fun q _ => by rwa [Subsingleton.elim q (IsLocalRing.closedPoint ℂ)]
  refine ⟨⟨f, by rw [← Category.assoc, hf]; exact w.2⟩, ?_⟩
  have e : PtsOver.map i rfl _ (⟨f, by rw [← Category.assoc, hf]; exact w.2⟩ : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) = w :=
    Subtype.ext hf
  rw [e]
  exact hw

end GlobalTheory.CompanionTheory.MPDict.UnderSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne
section
open Ad3 (Pl Qv pOf)
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)
open GroundTheory.Global.RationalSymbol (prime)

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

theorem pOf_eq_prime (v : Pl) : pOf v = prime v := by
  show Ideal.absNorm v.asIdeal = prime v
  rw [DirichletHecke.asIdeal_eq_span, Ideal.absNorm_span_singleton]
  have h : ((prime v : ℕ) : NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) ((prime v : ℕ) : ℤ) := by
    simp
  rw [h, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Module.finrank_self]
  simp

theorem ord_uniformizer_eq_one (v : Pl) :
    ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v) = 1 := by
  have h1 : Valued.v ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v) = WithZero.exp (-1) :=
    DirichletHecke.valued_uniformizer v
  have h2 := GroundTheory.Global.valued_eq_exp_neg_ord (K := ℚ) (v := v)
    (x := ((DirichletHecke.uniformizer v : (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)ˣ) :
      IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v)) (Units.ne_zero _)
  have h3 : WithZero.exp (-ord ((DirichletHecke.uniformizer v : (Qv v)ˣ) : Qv v)) = WithZero.exp (-1) :=
    h2.symm.trans h1
  have h4 := WithZero.exp_injective h3
  omega

end GlobalTheory.CompanionTheory.HalfIntegral
end
end

