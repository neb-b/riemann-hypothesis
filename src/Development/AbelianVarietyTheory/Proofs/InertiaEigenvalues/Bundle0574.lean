module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0526
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0008
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0007
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizer
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharacterPairingHarishChandraCuspidalMackey
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0567
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0754
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0569
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0562
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdaptedBasisThetaGaloisFixedPolesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBasis_theta_galoisFixed_poles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (C : Core l), C.InvdR → ∀ (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), F.IsDR → Y.map (inclW l) = inclW l τ ^ N • F.T → ∀ H : Hodge C (bk.ev bk.E) (fun g => (ρ g).map (zOm l)) K, (∀ (g : ↥(GK K)) (z : ℂ_[l]), IsZ bk g z → ∃ u : Matrix (Fin d) (Fin d) (ℂ_[l]), u * Y.map ((Per.θD l).comp (aDp l)) = Y.map ((Per.θD l).comp (aDp l)) * (F.ε g).map ((Per.θD l).comp (aDp l)) ∧ u * H.V.map (Per.θD l) = H.V.map (Per.θD l) * Matrix.diagonal fun i => z ^ ((H.p i : ℤ) - H.q)) ∧ ∀ N₀ : ℕ, N₀ ≤ N → (∀ i, |(H.p i : ℤ) - H.q| ≤ N₀) → (∀ i j, bk.E ^ (N - N₀) ∣ F.A i j) ∧ ∀ i j, bk.E ^ (N - N₀) ∣ F.A' i j := by
  first | (exact @GlobalTheory.BKLim.adaptedBasis_theta_and_poles) | (exact GlobalTheory.BKLim.adaptedBasis_theta_and_poles) | (intros; apply GlobalTheory.BKLim.adaptedBasis_theta_and_poles  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfJAdicLimitEqDiscSum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.eq_of_hasSum_toDisc_of_J_adic : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ι : Type),
    TopBasis bk.ev bk.J ι → ∀ (w : ι → Ainf l) (z t : Ainf l), HasSum (fun i => bk.iA (w i)) (bk.iA t) →
    (∀ n : ℕ, ∃ F : Finset ι, ∀ G : Finset ι, F ⊆ G → z - ∑ i ∈ G, w i ∈ (bk.J ^ n).map bk.ev) → z = t := by
  intro l hl K bk ι tb w z t hsum hJ
  classical
  have hρ : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
    have hl1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
    have he : (0 : ℝ) < 1 / (bk.Ep.natDegree : ℝ) := one_div_pos.2 (Nat.cast_pos.2 bk.deg_pos)
    exact ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos he)⟩
  have hinj : Function.Injective (toDisc l (bk.ev X) bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  have hiA : bk.iA = toDisc l (bk.ev X) bk.ρ₀ := rfl
  apply hinj
  rw [← hiA]
  have key : ∀ ε : ℝ, 0 < ε → ‖bk.iA z - bk.iA t‖ ≤ 2 * ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := GlobalTheory.BSP.norm_toDisc_J_pow_small l K bk (Ainf l) bk.ev bk.ρ₀ hρ.1 hρ.2 ε hε
    obtain ⟨F, hF⟩ := hJ n
    have hev : ∀ᶠ G in Filter.atTop, ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ < ε := by
      have := (hsum : Filter.Tendsto _ _ _)
      have h2 := Metric.tendsto_nhds.1 this ε hε
      filter_upwards [h2] with G hG
      simpa [dist_eq_norm] using hG
    obtain ⟨G₀, hG₀⟩ := Filter.eventually_atTop.1 hev
    set G := F ∪ G₀
    have h1 : ‖bk.iA (z - ∑ i ∈ G, w i)‖ ≤ ε := hn _ (hF G Finset.subset_union_left)
    have h2 : ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ < ε := hG₀ G Finset.subset_union_right
    have hsplit : bk.iA z - bk.iA t = bk.iA (z - ∑ i ∈ G, w i) + (∑ i ∈ G, bk.iA (w i) - bk.iA t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]; abel
    rw [hsplit]
    calc _ ≤ ‖bk.iA (z - ∑ i ∈ G, w i)‖ + ‖∑ i ∈ G, bk.iA (w i) - bk.iA t‖ := norm_add_le _ _
      _ ≤ 2 * ε := by linarith
  have h0 : ‖bk.iA z - bk.iA t‖ = 0 := by
    refine le_antisymm ?_ (norm_nonneg _)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (ε / 2) (by positivity)
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 h0)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeFrobeniusSolutionsPowDvd
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem envelope_dvd_lpow_aux₁ {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (L a b : R) (u v : ι → R)
    (hL : L ∈ nonZeroDivisors R) (h : a * (L * b) = ∑ i ∈ s, L * u i * v i) : a * b = ∑ i ∈ s, u i * v i := by
  refine sub_eq_zero.1 ((mem_nonZeroDivisors_iff.mp hL).2 _ ?_)
  have e : ∑ i ∈ s, u i * v i * L = ∑ i ∈ s, L * u i * v i := Finset.sum_congr rfl fun i _ => by ring
  rw [sub_mul, Finset.sum_mul, e, ← h]
  ring

theorem envelope_dvd_lpow_aux₂ {R : Type} [CommRing R] (L w z : R) (k : ℕ)
    (hL : ∀ x : R, L * x = 0 → x = 0) (h : L * w = L ^ (k + 1) * z) : L ^ k ∣ w :=
  ⟨z, sub_eq_zero.1 (hL _ (by rw [mul_sub, h, pow_succ', mul_assoc, sub_self]))⟩

theorem envelope_dvd_lpow_aux₄ {R : Type} [CommRing R] (L x y : R) (k : ℕ) (hxy : x = L * y) (h : L ^ k ∣ y) :
    L ^ (k + 1) ∣ x := by
  rw [hxy, pow_succ']
  exact mul_dvd_mul_left _ h

theorem envelope_dvd_lpow_aux₃ {l : ℕ} [Fact l.Prime] {K : FinExt l} {B : Obj l ↥(OL K)} (σ : Hom B (ainfObj K))
    (x y : B.A) (k : ℕ) (hxy : x = (l : B.A) * y) (h : ((l : ℕ) : (ainfObj K).A) ^ (k + 1) ∣ σ.f x) :
    ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f y := by
  subst hxy
  obtain ⟨z, hz⟩ := h
  rw [map_mul, map_natCast] at hz
  exact envelope_dvd_lpow_aux₂ (R := Ainf l) (l : Ainf l) (σ.f y) z k ainf_torsionFree hz

theorem envelope_dvd_lpow_of_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (c : κ → κ → En.Q.A) (h k : ℕ) (x : κ → En.Q.A), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ^ k ∣ x j := by
  intro l _ K bk En κ _ c h k
  have hreg : ((l : ℕ) : En.Q.A) ∈ nonZeroDivisors En.Q.A :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk En.Q.A (BK.hf En.inl) (Digits l) En.tb).2.2.1
  induction k with
  | zero => intro x _ _ j; rw [pow_zero]; exact one_dvd _
  | succ k ih =>
    intro x hx hσ j
    have h1 := _root_.GlobalTheory.BSP.dvd_l_of_sections_env_bk l K bk En κ x c h hx
      (fun g σ e1 e2 i => dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero k)) (hσ g σ e1 e2 i))
    choose y hy using h1
    have hyeq : ∀ j, BK.hf En.inl bk.E ^ h * y j = ∑ i, En.Q.D.φ (y i) * c i j := by
      intro j
      have hxj := hx j
      simp only [hy, map_mul, map_natCast] at hxj
      exact envelope_dvd_lpow_aux₁ Finset.univ _ _ _ (fun i => En.Q.D.φ (y i)) (fun i => c i j) hreg hxj
    have hσ' : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
        σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ^ k ∣ σ.f (y j) := by
      intro g σ e1 e2 i
      exact envelope_dvd_lpow_aux₃ σ (x i) (y i) k (hy i) (hσ g σ e1 e2 i)
    exact envelope_dvd_lpow_aux₄ _ _ _ k (hy j) (ih y hyeq hσ' j)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFiltrationSpanDeRhamLattice
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (α β : ℕ), (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → (∀ v ∈ P.M, E ↥LL.1 l e ^ β • v ∈ P.L) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), w ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) ((β : ℤ)) ↔ ∃ d : ι → OD l ↥(OL LL), w = ∑ i, act (d i) (∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1)))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Pl AI Td hC X hX act hA α β _ _ hβ w
  obtain ⟨hmul, hone⟩ := _root_.GlobalTheory.BKGal.JumpDR.odAct_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨b⟩ := _root_.GlobalTheory.BKGal.IdentRank.main l a e ϖ LL ι P T I
  have hb0 := (GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b).1
  obtain ⟨m, m', u, r, hu, hm, hr, hrm⟩ := UpperTheory.KN.exists_unit_invertible_matrix_identification_basis l a e ϖ LL ι P T I b
  have hf := UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns l a e ϖ LL ι P T I jB Pl AI Td hC X hX act hA b m u r hu hr hrm β hβ
  exact UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange _ _ act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j))
    hshift ι β
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) m m' hm hf hb0 w
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinGaloisScalesDeRhamPeriodsByUnitPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) (jD : (ι → OD l O) ≃ₗ[OD l O] TW (OD l O) T)
    (ε : OCb l) (hε : IsEps ε) (hCmp : IsCrisCmp I jB) (hHor : IsHoriz t ϖ (sQ l) P jB)
    (hjD : ∀ (c : ι → OA l O) (z : TW (OA l O) T), I.j (inclV l O ι c) = TWincl (inclO l O) T z →
      jD (fun i => toOD l O (c i)) = TWincl (toOD l O) T z)
    (α : ℕ) (hα : ∀ v ∈ P.L, E K l e ^ α • v ∈ P.M) (g : Gl l) (hg : sQ l g ∈ GK (ϖ.field a)) (v : OD l O)
    (hv : GlobalTheory.GalStep.galOD O (sQ l g) (GlobalTheory.GalStep.ED K t ϖ) = GlobalTheory.GalStep.ED K t ϖ * v) (d : P.D) :
    jD.symm (TWact (GlobalTheory.GalStep.galOD O (sQ l g)) T g (jD (GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • P.xi d)))) =
      v ^ α • GlobalTheory.GalStep.YD t ϖ (E K l e ^ α • P.xi d) := by
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  have hd : P.xi d ∈ P.MMl := ((GlobalTheory.BK.xi_trivialises_invL_S O K l e a ι P).2 (cst d)).2
    (GlobalTheory.GalStep.cst_mem_Mext P d)
  have h1 := UpperTheory.KN.phiMod_crystalline_comparison_of_isCrisCmp l a e O K t ϖ ι P T I jB jD C ε hε hCmp hjD α hα ⟨P.xi d, hd⟩
  have h2 := UpperTheory.KN.latticeTensor_deRham_crys_relation_galois_stable l O K T C g _ _ (GlobalTheory.GalStep.ED K t ϖ ^ α) (h1.trans (by rw [map_pow]))
  have h3 : TWact (galOB O (sQ l g)) T g (jB (toBcris t ϖ P ⟨P.xi d, hd⟩)) =
      jB (toBcris t ϖ P ⟨P.xi d, hd⟩) := hHor g hg d hd
  rw [h3, map_pow, hv, mul_pow, mul_comm, map_mul, mul_smul, map_pow (dRO l O) (GlobalTheory.GalStep.ED K t ϖ), ← h1,
    ← BasisCoord.tWincl_smul'] at h2
  have h4 := UpperTheory.KN.latticeTensorIncl_deRham_injective l O K T h2
  rw [← jD.map_smul] at h4
  exact (congrArg jD.symm h4).trans (jD.symm_apply_apply _)

theorem _root_.GlobalTheory.T.breuilKisin_galois_scales_deRhamPeriods_by_unit_pow : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → IsCrisCmp I jB → IsHoriz (thetaW a LL) ϖ (sQ l) P jB → ∀ (jD : (ι → OD l ↥(OL LL)) ≃ₗ[OD l ↥(OL LL)] TW (OD l ↥(OL LL)) T), (∀ (c : ι → OA l ↥(OL LL)) (z : TW (OA l ↥(OL LL)) T), I.j (inclV l ↥(OL LL) ι c) = TWincl (inclO l ↥(OL LL)) T z → jD (fun i => toOD l ↥(OL LL) (c i)) = TWincl (toOD l ↥(OL LL)) T z) → ∀ α : ℕ, (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → ∀ v : OD l ↥(OL LL), GlobalTheory.GalStep.galOD ↥(OL LL) (sQ l g) (GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ) = GlobalTheory.GalStep.ED ↥LL.1 (thetaW a LL) ϖ * v → ∀ d : P.D, GlobalTheory.GalStep.rhoD T jD g (GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xi d)) = v ^ α • GlobalTheory.GalStep.YD (thetaW a LL) ϖ (E ↥LL.1 l e ^ α • P.xi d) := by
  intro _ l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI _ hCmp hHor jD hjD α hα g hg v hv d
  obtain ⟨-, ε, -, hε, -⟩ := _root_.GlobalTheory.KummerMove.main l a e ϖ hl2
  exact gen (thetaW a LL) ϖ P T I jB jD ε hε hCmp hHor hjD α hα g hg v hv d
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCuspidalMultisetsTotalDegreeLe
section
open GlobalTheory.GLq GlobalTheory.Published Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.CuspMultisetCount

theorem degL_toList {g : ℕ} [Fact g.Prime] (M : Multiset (Pc g)) :
    degL M.toList = (M.map fun p => p.1).sum := by
  unfold degL
  conv_rhs => rw [← Multiset.coe_toList M]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem stdAddChar_ne_one (g : ℕ) [Fact g.Prime] : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) ≠ 1 := by
  intro h
  have h1 := congrArg (fun ψ : AddChar (ZMod g) ℂ => ψ 1) h
  simp only [AddChar.one_apply] at h1
  have h0 : (ZMod.stdAddChar : AddChar (ZMod g) ℂ) 0 = 1 := AddChar.map_zero_eq_one _
  have := ZMod.injective_stdAddChar (N := g) (h1.trans h0.symm)
  exact one_ne_zero this

theorem card_le : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), 0 < n → ∀ S : Finset (Multiset (Pc g)),
    (∀ M ∈ S, (M.map fun p => p.1).sum = n ∧ ∀ p ∈ M, IsCusp p.2) → S.card ≤ g ^ n - g ^ (n - 1) := by
  intro g _ n hn S hS
  set ψ : AddChar (ZMod g) ℂ := ZMod.stdAddChar with hψdef
  have hψ : ψ ≠ 1 := stdAddChar_ne_one g
  have hdeg : ∀ M ∈ S, degL M.toList = n := fun M hM => (degL_toList M).trans (hS M hM).1
  have hcusp : ∀ M ∈ S, ∀ p ∈ M.toList, IsCusp p.2 := fun M hM p hp =>
    (hS M hM).2 p (Multiset.mem_toList.1 hp)
  have hchar : ∀ M ∈ S, IsChar (hcL M.toList n) := fun M hM =>
    (GlobalTheory.gl_list_product_perm_char g M.toList M.toList n (hdeg M hM).symm
      (fun p hp => Label.isChar_of_isIrr (hcusp M hM p hp).2.1)).1
  have key : ∀ M ∈ S, ∃ ρ : Gn g n → ℂ, IsIrr ρ ∧ wh ψ ρ ≠ 0 ∧ ip ρ (hcL M.toList n) ≠ 0 :=
    fun M hM => _root_.GlobalTheory.GLq.GenericConstituent.exists_generic_constituent g ψ hψ M.toList n (hdeg M hM) (hcusp M hM)
  choose! f hf using key
  have hfin : {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.Finite :=
    (GlobalTheory.GLq.irr_finite_and_finsum_zOf_eq_one (Gn g n)).1.subset fun ρ h => h.1
  have hinj : Set.InjOn f (S : Set (Multiset (Pc g))) := by
    intro M hM M' hM' heq
    have h1 := (hf M hM).2.2
    have h2 := (hf M' hM').2.2
    rw [heq] at h1
    have hne := Label.ip_ne_zero_of_common (f M') _ _ (hf M' hM').1 (hchar M hM) (hchar M' hM') h1 h2
    have hp : M.toList.Perm M'.toList := by
      by_contra hnp
      exact hne ((GlobalTheory.GLq.IpCuspProd.ip_hcL_cusp g M.toList M'.toList n (hdeg M hM) (hdeg M' hM')
        (hcusp M hM) (hcusp M' hM')).1 hnp)
    rw [← Multiset.coe_toList M, ← Multiset.coe_toList M']
    exact Multiset.coe_eq_coe.2 hp
  calc S.card = (S : Set (Multiset (Pc g))).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ {ρ : Gn g n → ℂ | IsIrr ρ ∧ wh ψ ρ ≠ 0}.ncard :=
        Set.ncard_le_ncard_of_injOn f (fun M hM => ⟨(hf M hM).1, (hf M hM).2.1⟩) hinj hfin
    _ ≤ g ^ n - g ^ (n - 1) := _root_.GlobalTheory.GLq.card_generic_irr_le g ψ hψ n hn

end GlobalTheory.GLq.CuspMultisetCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegree
section
noncomputable section

open MvPolynomial

namespace GlobalTheory.JSW.CauchyGlue

theorem map_jtDet {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (h : ℕ → A)
    (l : Fin m → ℕ) : f (jtDet m h l) = jtDet m (fun k => f (h k)) l := by
  rw [jtDet, jtDet, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem map_alternant {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (m : ℕ) (μ : Fin m → ℕ) :
    MvPolynomial.map f (alternant A m μ) = alternant B m μ := by
  rw [alternant, alternant, RingHom.map_det]
  congr 1
  ext i j
  simp

theorem alternant_eq_det (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = Matrix.det (Matrix.of fun i j : Fin m => (X i : MvPolynomial (Fin m) A) ^ μ j) := by
  rw [alternant, ← Matrix.det_transpose]
  rfl

theorem alternant_staircase_ne_zero (m : ℕ) : alternant ℂ m (staircase m) ≠ 0 := by
  have e : (Matrix.of fun i j : Fin m => (X j : MvPolynomial (Fin m) ℂ) ^ staircase m i) =
      (Matrix.transpose (Matrix.vandermonde (fun j : Fin m => (X j : MvPolynomial (Fin m) ℂ)))).submatrix Fin.revPerm id := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Fin.revPerm_apply, id, staircase, Fin.val_rev]
    congr 1
    omega
  rw [alternant, e, Matrix.det_permute, Matrix.det_transpose]
  refine mul_ne_zero ?_ ?_
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin m))) with h | h <;> simp [h]
  · exact (Matrix.det_vandermonde_ne_zero_iff).2 (MvPolynomial.X_injective)

theorem bialt_int (m : ℕ) (l : Fin m → ℕ) (hl : Antitone l) :
    schur m l * alternant ℤ m (staircase m) = alternant ℤ m (fun i => l i + staircase m i) := by
  simp only [alternant_eq_det, staircase]
  rw [schur_mul_det_eq_det m l hl]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.of_apply]
  congr 1
  have := j.2
  omega

theorem cauchy_formal : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  intro m n hmn α β d
  set hC : ℕ → ℂ := fun k => eval₂ (Int.castRingHom ℂ) α (hsymm (Fin n) ℤ k) with hhC
  have hA := _root_.GlobalTheory.JSW.alternant_staircase_mul_antidiagonal (A := ℂ) m d hC
  have hpad : ∀ l : Fin m → ℕ, schurAt (padTo hmn l) α = jtDet m hC l := by
    intro l
    rw [schurAt, _root_.GlobalTheory.JSW.schur_padTo_eq_jtDet hmn l, ← MvPolynomial.coe_eval₂Hom, map_jtDet]
    rfl
  have hbi : ∀ l ∈ antiParts m d, alternant ℂ m (fun i => l i + staircase m i) =
      MvPolynomial.map (Int.castRingHom ℂ) (schur m l) * alternant ℂ m (staircase m) := by
    intro l hl
    have := congrArg (MvPolynomial.map (Int.castRingHom ℂ)) (bialt_int m l (mem_antiParts.1 hl).2)
    rw [map_mul, map_alternant, map_alternant] at this
    exact this.symm
  have hR : ∑ l ∈ antiParts m d, C (jtDet m hC l) * alternant ℂ m (fun i => l i + staircase m i) =
      alternant ℂ m (staircase m) *
        ∑ l ∈ antiParts m d, C (jtDet m hC l) * MvPolynomial.map (Int.castRingHom ℂ) (schur m l) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [hbi l hl]
    ring
  rw [hR] at hA
  have hP := mul_left_cancel₀ (alternant_staircase_ne_zero m) hA
  have hE := congrArg (MvPolynomial.eval β) hP
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod, map_mul, eval_C, eval_X, map_pow, MvPolynomial.eval_map] at hE
  refine (Finset.sum_congr rfl fun l _ => ?_).trans hE.symm
  rw [hpad]
  rfl

end GlobalTheory.JSW.CauchyGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePotentialFamilyStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_potential_family : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → admBK (D := D) → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ n : ℕ,
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hSub : SubTw i r Xs M),
      IsDR (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1).ρ ∧
      ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PU : (locU i w hw M hSub.1).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) U' ∧
        DualLatLe (Br.PD D.loc D.nbr i w hw) (locU i w hw M hSub.1) U' (Br.locLat D.nbr i w hw M) PU (2 * k) := by
  first | exact @GlobalTheory.Pass.LocDualU.main | exact GlobalTheory.Pass.LocDualU.main | (intros; apply GlobalTheory.Pass.LocDualU.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discPeriod_comparison_relation_map_prismHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B B' : Obj l ↥(OL K)) (f₀ f g : Hom bk.prism B) (f₀' : Hom bk.prism B') (k : Hom B B') (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → (∃ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk) ∧ ∀ Fk : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀' X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) k.f Fk → ht.Rel (BK.hf f₀' X) (k.comp f) (k.comp g) (ε.map Fk) := by
  first | exact @GlobalTheory.BSP.Height.rel_map | exact GlobalTheory.BSP.Height.rel_map | (intros; apply GlobalTheory.BSP.Height.rel_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualLatticeRankBoundStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_over_extension : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → admBK (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), finrank ℚ_[D.nd.l i] (Br.Kw D.nbr i w hw) = 1 → ∀ {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous fun g => M g) (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1), IsCrys ((D.loc (D.nd.l i)).PD K') ((GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).ρ.comp (Subgroup.inclusion (GK_le h))) → ∃ (U' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw)), letI := U'.modO; letI := U'.towO; ∃ (LT' : Lattice (O := Br.OLL D.nbr i w hw) U'.ρ) (PU : (GlobalTheory.Pass.LocDirect.ModuleGaloisRepresentation i w hw M hM).V →ₗ[Br.LL D.nbr i w hw] U'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw), IsDualLat1 (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) LT' PU ∧ finrank (Br.OLL D.nbr i w hw) ↥(latticeFiniteCohomology (Br.PD D.loc D.nbr i w hw) LT') ≤ k := by
  first | exact @GlobalTheory.Pass.LocDirect.dualLat_rank | exact GlobalTheory.Pass.LocDirect.dualLat_rank | (intros; apply GlobalTheory.Pass.LocDirect.dualLat_rank <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdGalSubStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCr_of_wSeed_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → (∀ g, s.κ g = 1) → F.IsCr := by
  first | (exact @GlobalTheory.BKLim.Frame.isCr_of_wSeed) | (exact GlobalTheory.BKLim.Frame.isCr_of_wSeed) | (intros; apply GlobalTheory.BKLim.Frame.isCr_of_wSeed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerInversePowerSeriesEvalOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eulerInverse_powerSeries_eval_one : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  exact @GlobalTheory.JSW.eulerInverse_eval_one
end

