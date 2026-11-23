module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0507
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0508
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEqStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineDiscPeriods_galois_action_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ x, G (j x) = j x) ∧ bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) = G (bk.iA τ) ^ s.N • s.W := by
  first | exact @GlobalTheory.BSP.seed_gal_periods | exact GlobalTheory.BSP.seed_gal_periods | (intros; apply GlobalTheory.BSP.seed_gal_periods <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylLatticeExistsNatPowSmulMem
section
open NumberField

noncomputable section

namespace GlobalTheory.NabScale

open MvPolynomial IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def IntAt (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K) : Prop :=
  ∃ t ∈ w.asIdeal.primeCompl, ∃ A : Matrix (Fin n) (Fin n) (𝓞 K),
    A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • m

theorem IntAt.det {w : HeightOneSpectrum (𝓞 K)} {m : Matrix (Fin n) (Fin n) K} (h : IntAt w m) :
    ∃ t ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m.det := by
  obtain ⟨t, ht, A, hA⟩ := h
  refine ⟨t ^ n, Submonoid.pow_mem _ ht n, A.det, ?_⟩
  rw [RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_smul, map_pow]
  simp

theorem detPow_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) (e : ℤ) :
    ∃ u ∈ w.asIdeal.primeCompl, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K u * (c ^ (n * e.natAbs) * detPow K n g e) := by
  obtain ⟨k, rfl | rfl⟩ := e.eq_nat_or_neg
  · obtain ⟨t, ht, y, hy⟩ := hc.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_natCast, detPow, zpow_natCast, Units.val_pow_eq_pow_val,
      Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring
  · obtain ⟨t, ht, y, hy⟩ := hc'.det
    refine ⟨t ^ k, Submonoid.pow_mem _ ht k, y ^ k, ?_⟩
    rw [map_pow, hy, Matrix.det_smul, map_pow, Int.natAbs_neg, Int.natAbs_natCast, detPow, zpow_neg, zpow_natCast,
      ← inv_pow, Units.val_pow_eq_pow_val, ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
    simp only [Fintype.card_fin]
    ring

theorem sqAct_scaled (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) K) (c : K)
    (hc : IntAt w (c • (g : Matrix (Fin n) (Fin n) K)))
    (hc' : IntAt w (c • ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (lam : DomWeight n) (f : MvPolynomial (Fin n × Fin n) K) (hf : f ∈ (nablaSq (𝓞 K) n lam).map (toK K _)) :
    ∃ s ∈ w.asIdeal.primeCompl,
      algebraMap (𝓞 K) K s • (c ^ (∑ j, lam.natW j + n * lam.detShift.natAbs) • sqAct K n lam g f) ∈
        (nablaSq (𝓞 K) n lam).map (toK K _) := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨t, ht, A, hA⟩ := hc
  obtain ⟨u, hu, y, hy⟩ := detPow_scaled w g c ⟨t, ht, A, hA⟩ hc' lam.detShift
  refine ⟨u * t ^ (∑ j, lam.natW j), Submonoid.mul_mem _ hu (Submonoid.pow_mem _ ht _),
    y • Formalism.GradedWeylDivisibility.rowAct (𝓞 K) Aᵀ f,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable (𝓞 K) n n _ _ f hf), ?_⟩
  have hK : map (algebraMap (𝓞 K) K) f ∈ Formalism.GradedWeylDivisibility.dualWeyl K n n lam.natW :=
    Formalism.GradedWeylDivisibility.dualWeylMap _ _ _ n n _ f hf
  have hT : Aᵀ.map (algebraMap (𝓞 K) K) = (algebraMap (𝓞 K) K t * c) • (g : Matrix (Fin n) (Fin n) K)ᵀ := by
    rw [Matrix.transpose_map, hA, Matrix.transpose_smul, Matrix.transpose_smul, smul_smul]
  rw [map_smul, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.toK_apply, GlobalTheory.NabStab.map_rowAct, hT,
    GlobalTheory.NabStab.rowAct_smul _ _ _ hK.1, sqAct, ← IsScalarTower.algebraMap_smul K y, hy, smul_smul, smul_smul, smul_smul,
    map_mul, map_pow]
  congr 1
  ring

def scaleExp {ι : Type} [Fintype ι] (lam : ι → DomWeight n) : ℕ :=
  ∑ τ, (∑ j, (lam τ).natW j + n * (lam τ).detShift.natAbs)

theorem polyAction_scaled_mem_locP_nabStd {ι : Type} [Fintype ι] (lam : ι → DomWeight n)
    (w : HeightOneSpectrum (𝓞 K)) (g : ι → GL (Fin n) K) (c : K)
    (hc : ∀ τ, IntAt w (c • ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)))
    (hc' : ∀ τ, IntAt w (c • (((g τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) :
    ∀ F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam),
      c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
  have key : ∀ F ∈ nabStd K lam, c ^ scaleExp lam • actP lam g F ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) := by
    intro F hF
    unfold nabStd Formalism.GradedWeylDivisibility.tensorLat at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      choose s hs hs' using fun τ => sqAct_scaled w (g τ) c (hc τ) (hc' τ) (lam τ) (f τ) (hf τ)
      refine ⟨∏ τ, s τ, Submonoid.prod_mem _ fun τ _ => hs τ, Submodule.subset_span ⟨_, hs', ?_⟩⟩
      have h1 := actTen K ι n lam g f
      unfold ten at h1
      rw [h1, ← IsScalarTower.algebraMap_smul K, map_prod, scaleExp, ← Finset.prod_pow_eq_pow_sum, smul_smul,
        ← Finset.prod_mul_distrib]
      simp only [map_smul, smul_smul]
      rw [Finset.prod_smul]
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      rw [LinearMap.map_smul_of_tower, smul_comm]
      exact Submodule.smul_mem _ _ hx
  rintro F ⟨s, hs, hF⟩
  obtain ⟨t, ht, h2⟩ := key _ hF
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [LinearMap.map_smul_of_tower] at h2
  rw [mul_smul, smul_comm s (c ^ scaleExp lam)]
  exact h2

theorem intAt_of_cols (w : HeightOneSpectrum (𝓞 K)) (m : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, ∃ t ∈ w.asIdeal.primeCompl, ∀ a, ∃ y : 𝓞 K,
      algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K t * m a j) :
    IntAt w m := by
  classical
  choose s hs hs' using h
  have h2 : ∀ a j : Fin n, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = algebraMap (𝓞 K) K (∏ i, s i) * m a j := by
    intro a j
    obtain ⟨y, hy⟩ := hs' j a
    refine ⟨(∏ i ∈ Finset.univ.erase j, s i) * y, ?_⟩
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), map_mul, map_mul, hy, mul_assoc]
  choose A hA using h2
  refine ⟨∏ i, s i, Submonoid.prod_mem _ fun i _ => hs i, Matrix.of A, ?_⟩
  ext a j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hA]

theorem intAt_transition (w : HeightOneSpectrum (𝓞 K)) {L L' : Submodule (𝓞 K) (Fin n → K)} {B B' : GL (Fin n) K}
    (hB : IsBasisAt w L B) (hB' : IsBasisAt w L' B') (c : K) (h : ∀ x ∈ L, c • x ∈ L') :
    IntAt w (c • ((B'⁻¹ * B : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  apply intAt_of_cols
  intro j
  have h1 : (fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L := by
    unfold IsBasisAt at hB
    rw [hB]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨j, rfl⟩⟩
  obtain ⟨s, hs, hx⟩ := h1
  have h2 : c • (s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (colLat B') := by
    unfold IsBasisAt at hB'
    rw [← hB']
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact h _ hx⟩
  obtain ⟨s', hs', hx'⟩ := h2
  have h3 : colLat B' = gLat B' (colLat 1) := by rw [← colLat_mul, mul_one]
  rw [h3] at hx'
  obtain ⟨z, hz, hzx⟩ := hx'
  refine ⟨s' * s, Submonoid.mul_mem _ hs' hs, fun a => ?_⟩
  obtain ⟨y, hy⟩ := GlobalTheory.NabStab.int_of_mem_colLat_one hz a
  refine ⟨y, ?_⟩
  have hz' : z = ((B'⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
      (s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j) := by
    have hzx' : (B' : Matrix (Fin n) (Fin n) K) *ᵥ z = s' • c • s • fun a => (B : Matrix (Fin n) (Fin n) K) a j := hzx
    rw [← hzx', Matrix.mulVec_mulVec]
    simp
  rw [hy, hz']
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Units.val_mul, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [Algebra.smul_def, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

section ESide

variable {E : Type} [Field E] [NumberField E] {ι : Type}

theorem tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M, (N : 𝓞 E) • x ∈ M') : ∀ x ∈ tauLat emb τ M, (N : 𝓞 K) • x ∈ tauLat emb τ M' := by
  intro x hx
  unfold tauLat at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, hm, rfl⟩ := hx
    refine Submodule.subset_span ⟨(N : 𝓞 E) • m, h m hm, ?_⟩
    funext a
    simp [Algebra.smul_def]
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem dualFr_tauLat_smul_mem (emb : ι → E →+* K) (τ : ι) {M M' : Submodule (𝓞 E) (Fin n → E)} (N : ℕ)
    (h : ∀ x ∈ M', (N : 𝓞 E) • x ∈ M) :
    ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') := by
  intro φ hφ x hx
  have h1 := hφ _ (tauLat_smul_mem emb τ N h x hx)
  show ((N : K) • φ) ⬝ᵥ x ∈ _
  rw [smul_dotProduct]
  rw [dotProduct_smul] at h1
  convert h1 using 1
  simp [Algebra.smul_def]

end ESide

theorem nabAtr_smul_pow_mem : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (n : ℕ) (emb : ι → E →+* K) (lam : ι → Formalism.BasicNotions.DomWeight n) (M M' : Submodule (𝓞 E) (Fin n → E)) (N : ℕ),
    N ≠ 0 → Submodule.IsFullLattice E M → Submodule.IsFullLattice E M' → (∀ x ∈ M, (N : 𝓞 E) • x ∈ M') →
    (∀ x ∈ M', (N : 𝓞 E) • x ∈ M) →
    ∃ a : ℕ, ∀ F ∈ Formalism.L2.DIV.nabAtr emb lam M, ((N : K) ^ a) • F ∈ Formalism.L2.DIV.nabAtr emb lam M' := by
  intro E K _ _ _ _ ι _ n emb lam M M' N _ hM _ h1 h2
  refine ⟨scaleExp lam, fun F hF => ?_⟩
  have hL : ∀ τ, Submodule.IsFullLattice K (dualFr (tauLat emb τ M)) := fun τ => dualFr_tauLat_isLattice emb τ M hM
  have hLL' : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M), (N : K) • φ ∈ dualFr (tauLat emb τ M') :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h2
  have hL'L : ∀ τ, ∀ φ ∈ dualFr (tauLat emb τ M'), (N : K) • φ ∈ dualFr (tauLat emb τ M) :=
    fun τ => dualFr_tauLat_smul_mem emb τ N h1
  unfold nabAtr nabK at hF ⊢
  rw [Submodule.mem_comap] at hF ⊢
  simp only [nabP, transLat, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.coe_subtype] at hF ⊢
  intro w B' hB'
  choose B hB using fun τ => basisAtEx K n _ (hL τ) w
  have hF' := hF w B hB
  have e : B'⁻¹ = (B'⁻¹ * B) * B⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [SetLike.val_smul, map_smul, e, polyAction_mul]
  refine polyAction_scaled_mem_locP_nabStd lam w (B'⁻¹ * B) (N : K) (fun τ => ?_) (fun τ => ?_) _ hF'
  · exact intAt_transition w (hB τ) (hB' τ) (N : K) (hLL' τ)
  · have h3 : ((B'⁻¹ * B) τ)⁻¹ = (B τ)⁻¹ * B' τ := by simp [mul_inv_rev]
    rw [h3]
    exact intAt_transition w (hB' τ) (hB τ) (N : K) (hL'L τ)

end GlobalTheory.NabScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinApproxRootGaloisSubMemBdRFilStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisensteinApproxRoot_galois_sub_mem_bdRFil : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n M : ℕ) (q : bk.S),
    bk.E ∣ q - (l : bk.S) ^ M * X →
    bk.E ^ n ∣ Polynomial.eval₂ PowerSeries.C q (bk.Ep.scaleRoots ((l : Wq l bk.a) ^ M)) →
    ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev q) - bk.ev q) ∈ Per.FilP l n := by
  first | (exact @GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (exact GlobalTheory.BSP.approxRoot_gal_sub_mem_fil) | (intros; apply GlobalTheory.BSP.approxRoot_gal_sub_mem_fil  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeakStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleComparison_pi_wachLattice_closed_weak : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosed.jD_piN_closed | exact GlobalTheory.WeakClosed.jD_piN_closed | (intros; apply GlobalTheory.WeakClosed.jD_piN_closed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatrices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.EtReal

open Matrix

variable {l : ℕ} [hl : Fact l.Prime]

theorem equivFun_frob {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      fun i => frobW l ((b.baseChange (WCb l)).equivFun y i) := by
  funext i
  simp only [Module.Basis.equivFun_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      map_smul, AlgHom.toLinearMap_apply, LinearMap.id_apply]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _), map_add (f := _), Finsupp.add_apply, Finsupp.add_apply, map_add (f := _), hy, hz]

theorem equivFun_map {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ_[l] T) (s : WCb l ≃ₐ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (b.baseChange (WCb l)).equivFun (TensorProduct.map s.toLinearMap r y) =
      (LinearMap.toMatrix b b r).map (algebraMap ℤ_[l] (WCb l)) *ᵥ
        fun k => s ((b.baseChange (WCb l)).equivFun y k) := by
  funext i
  simp only [Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct, Matrix.map_apply]
  induction y with
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, AlgEquiv.toLinearMap_apply,
      ← LinearMap.toMatrix_mulVec_repr b b r t]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.baseChange_repr_tmul, Matrix.mulVec, dotProduct, map_smul, Algebra.smul_def,
      Finset.sum_mul, map_mul, mul_assoc, map_sum, AlgEquiv.commutes]
  | add y z hy hz =>
    simp only [map_add (f := _), Finsupp.add_apply, hy, hz, mul_add, Finset.sum_add_distrib]

theorem algEquiv_mulVec {R A : Type} [CommSemiring R] [CommRing A] [Algebra R A] {n : Type} [Fintype n]
    (s : A ≃ₐ[R] A) (U : Matrix n n A) (v : n → A) (i : n) :
    s ((U *ᵥ v) i) = (U.map s *ᵥ fun k => s (v k)) i :=
  RingHom.map_mulVec s.toRingEquiv.toRingHom U v i

theorem realises_of_mreal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U → ∃ j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T), Realises K M (ainfObj K) (ainfId K) T ρ j := by
  intro l _ K bk d S M e hF T _ _ ρ b U hU
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) _ e
  let σ : (ainfObj K).A →+* WCb l := (inclW l).comp (ainfId K).toRingHom
  let cv : (Fin d → (ainfObj K).A) →ₛₗ[σ] (Fin d → WCb l) :=
    { toFun := fun v k => σ (v k)
      map_add' := fun v w => funext fun k => map_add σ (v k) (w k)
      map_smul' := fun a v => funext fun k => map_mul σ a (v k) }
  let j : M.M (ainfObj K) →ₛₗ[σ] (WCb l ⊗[ℤ_[l]] T) :=
    ((b.baseChange (WCb l)).equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' U) ∘ₛₗ (cv ∘ₛₗ b₀.equivFun.toLinearMap)
  have hj : ∀ x, (b.baseChange (WCb l)).equivFun (j x) = U *ᵥ fun k => σ (b₀.equivFun x k) := fun x =>
    (b.baseChange (WCb l)).equivFun.apply_symm_apply _
  have hjs : ∀ c : Fin d → (ainfObj K).A, (b.baseChange (WCb l)).equivFun (j (b₀.equivFun.symm c)) = U *ᵥ fun k => σ (c k) := fun c => by
    rw [hj, LinearEquiv.apply_symm_apply]

  have hbc : SemiBC j := by
    letI := hU.unit.invertible
    let c := (Pi.basisFun (WCb l) (Fin d)).map ((Matrix.toLinearEquiv' U this).trans (b.baseChange (WCb l)).equivFun.symm)
    refine _root_.GlobalTheory.BSP.semiBC_of_basis _ _ _ _ _ j (Fin d) b₀ c fun i => ?_
    apply (b.baseChange (WCb l)).equivFun.injective
    rw [hj]
    simp only [c, Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.trans_apply,
      LinearEquiv.apply_symm_apply, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    refine congrArg _ (funext fun k => ?_)
    rw [Module.Basis.equivFun_self]
    by_cases h : i = k
    · subst h; simp
    · simp [h, Pi.single_apply, Ne.symm h]
  have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
  obtain ⟨d₀, hd₀⟩ : ∃ d₀ : ↥(ainfObj K).I, ((d₀ : (ainfObj K).A) : Ainf l) = bk.ev bk.E :=
    ⟨⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩, rfl⟩
  have hne : (d₀ : (ainfObj K).A) ≠ 0 := fun h => hu.ne_zero (by rw [← hd₀, h]; exact map_zero (inclW l))
  refine ⟨j, Realises.of_generator (isAinf_ainfObj K) hbc d₀ (by rw [hd₀]; exact bk.span_ev) ?_ ?_⟩
  · intro x m k hfr
    have hx : x = ∑ i, b₀.equivFun x i • M.tr bk.ι (e i) := by
      simp_rw [← hb₀]; exact (b₀.sum_equivFun x).symm
    rw [hx] at hfr
    obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι d₀ (b₀.equivFun x) m k hfr
    haveI : IsDomain (ainfObj K).A := (ainfId K).toMulEquiv.isDomain
    haveI := Module.Free.of_basis b₀
    have h1 := sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ hne))
    simp_rw [← hb₀] at h1
    rw [← b₀.equivFun_symm_apply] at h1
    have h2 : σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (d₀ : (ainfObj K).A) ^ k •
        j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i))) :=
      calc σ (BK.hf bk.ι bk.E) ^ S.a • j m = σ (BK.hf bk.ι bk.E ^ S.a) • j m := by rw [map_pow]
        _ = j (BK.hf bk.ι bk.E ^ S.a • m) := (j.map_smulₛₗ _ _).symm
        _ = j ((d₀ : (ainfObj K).A) ^ k • b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := congrArg j h1
        _ = σ ((d₀ : (ainfObj K).A) ^ k) • j (b₀.equivFun.symm ((S.A.map (BK.hf bk.ι)) *ᵥ
              fun i => (ainfObj K).D.φ (b₀.equivFun x i))) := j.map_smulₛₗ _ _
        _ = _ := congrArg (· • _) (map_pow σ _ _)
    suffices hs : σ (BK.hf bk.ι bk.E) ^ S.a • (σ (d₀ : (ainfObj K).A) ^ k •
        TensorProduct.map (frobW l).toLinearMap LinearMap.id (j x)) = σ (BK.hf bk.ι bk.E) ^ S.a • j m from
      (hu.pow S.a).smul_left_cancel.1 hs
    rw [h2]
    refine (smul_comm (σ (BK.hf bk.ι bk.E) ^ S.a) (σ (d₀ : (ainfObj K).A) ^ k) _).trans
      (congrArg (σ (d₀ : (ainfObj K).A) ^ k • ·) ?_)
    apply (b.baseChange (WCb l)).equivFun.injective
    have hz : (fun i => frobW l ((b.baseChange (WCb l)).equivFun (j x) i)) =
        U.map (frobW l) *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      rw [hj]
      funext i
      refine (RingHom.map_mulVec (frobW l).toRingHom U _ i).trans ?_
      exact congrArg (fun v => (U.map (frobW l) *ᵥ v) i) (funext fun k => frobW_inclW (b₀.equivFun x k))
    have hc : (fun k => σ (((S.A.map (BK.hf bk.ι)) *ᵥ fun i => (ainfObj K).D.φ (b₀.equivFun x i)) k)) =
        S.A.map bk.evW *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k)) := by
      funext k
      have hA : (S.A.map (BK.hf bk.ι)).map σ = S.A.map bk.evW := Matrix.ext fun _ _ => rfl
      exact (RingHom.map_mulVec σ _ _ k).trans
        (congrArg (fun A => (A *ᵥ fun k => σ ((ainfObj K).D.φ (b₀.equivFun x k))) k) hA)
    have hσE : σ (BK.hf bk.ι bk.E) = bk.evW bk.E := rfl
    refine ((b.baseChange (WCb l)).equivFun.map_smul _ _).trans ?_
    refine Eq.trans ?_ (hjs _).symm
    refine (congrArg (σ (BK.hf bk.ι bk.E) ^ S.a • ·) ((equivFun_frob b (j x)).trans hz)).trans ?_
    refine Eq.trans ?_ (congrArg (U *ᵥ ·) hc).symm
    exact (congrArg (fun t => t ^ S.a • (U.map (frobW l) *ᵥ _)) hσE).trans
      ((Matrix.smul_mulVec _ _ _).symm.trans
        ((congrArg (· *ᵥ _) hU.φ).trans (Matrix.mulVec_mulVec _ _ _).symm))
  · intro g x
    let h := (isAinf_ainfObj K).galHom g
    have hk : ∀ k, M.tr h (b₀ k) = ∑ i, S.ε bk.ι (h.comp bk.ι) i k • b₀ i := fun k =>
      (congrArg (M.tr h) (hb₀ k)).trans ((M.tr_comp h bk.ι (e k)).symm.trans
        ((hF.tr bk.ι (h.comp bk.ι) k).trans (Finset.sum_congr rfl fun i _ => congrArg _ (hb₀ i).symm)))
    have htr : M.tr h x = b₀.equivFun.symm ((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) :=
      calc M.tr h x = M.tr h (∑ k, b₀.equivFun x k • b₀ k) := congrArg (M.tr h) (b₀.sum_equivFun x).symm
        _ = ∑ k, h.f (b₀.equivFun x k) • M.tr h (b₀ k) :=
          (map_sum (M.tr h) _ _).trans (Finset.sum_congr rfl fun k _ => (M.tr h).map_smulₛₗ _ _)
        _ = ∑ k, ∑ i, (h.f (b₀.equivFun x k) * S.ε bk.ι (h.comp bk.ι) i k) • b₀ i :=
          Finset.sum_congr rfl fun k _ => (congrArg _ (hk k)).trans
            (Finset.smul_sum.trans (Finset.sum_congr rfl fun i _ => smul_smul _ _ _))
        _ = ∑ i, (∑ k, S.ε bk.ι (h.comp bk.ι) i k * h.f (b₀.equivFun x k)) • b₀ i :=
          Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ =>
            (Finset.sum_congr rfl fun k _ => congrArg (· • b₀ i) (mul_comm _ _)).trans Finset.sum_smul.symm)
        _ = _ := (b₀.equivFun_symm_apply _).symm
    apply (b.baseChange (WCb l)).equivFun.injective
    have hσ : ∀ a : (ainfObj K).A, σ a = inclW l a := fun a => rfl
    have hh : ∀ a : (ainfObj K).A, h.f a = Per.σA (g : GQ l) a := fun a => rfl
    have hL : (fun k => σ (((S.ε bk.ι (h.comp bk.ι)) *ᵥ fun k => h.f (b₀.equivFun x k)) k)) =
        (S.ε bk.ι (h.comp bk.ι)).map σ *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun k => RingHom.map_mulVec σ _ _ k
    have hR : (fun k => galW l (g : GQ l) ((b.baseChange (WCb l)).equivFun (j x) k)) =
        U.map (galW l (g : GQ l)) *ᵥ fun k => σ (h.f (b₀.equivFun x k)) :=
      funext fun i => by
        have h1 := congrArg (fun v : Fin d → WCb l => galW l (g : GQ l) (v i)) (hj x)
        have h2 := algEquiv_mulVec (galW l (g : GQ l)) U (fun k => σ (b₀.equivFun x k)) i
        have h3 : (fun k => galW l (g : GQ l) (σ (b₀.equivFun x k))) = fun k => σ (h.f (b₀.equivFun x k)) :=
          funext fun k => (congrArg (galW l (g : GQ l)) (hσ _)).trans ((galW_inclW (g : GQ l) (b₀.equivFun x k)).trans
            ((hσ _).symm.trans (congrArg σ (hh _).symm)))
        beta_reduce at h1 ⊢
        exact h1.trans (h2.trans (congrArg (fun v => (U.map (galW l (g : GQ l)) *ᵥ v) i) h3))
    have hg := hU.gal g
    refine ((congrArg (fun z => (b.baseChange (WCb l)).equivFun (j z)) htr).trans (hjs _)).trans ?_
    refine Eq.trans ?_ (equivFun_map b _ _ _).symm
    refine (congrArg (U *ᵥ ·) hL).trans (Eq.trans ?_ (congrArg (_ *ᵥ ·) hR).symm)
    exact (Matrix.mulVec_mulVec _ _ _).trans ((congrArg (· *ᵥ _) hg.symm).trans (Matrix.mulVec_mulVec _ _ _).symm)

end GlobalTheory.BSP.EtReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseEqOfClosedDiscExtendsNormLeOneStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_eq_of_closedDisc_extends_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 → ∀ y : Disc l (s X) ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : Disc l (s X) ρ' →+* Disc l (s X) ρ) (y' : Disc l (s X) ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (s X) ρ a = y := by
  first | exact @GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one | exact GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one | (intros; apply GlobalTheory.BSP.exists_toDisc_eq_of_extends_norm_le_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.exists_bcrisTensorLattice_equiv_periodRing :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL)
      (Pl : LocPrime l) (AI : LocAinf l Pl), GlobalTheory.Per.IsStd Pl AI →
      ∃ β : TW (GlobalTheory.BKReal.OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B,
        (∀ x : ↥T.L.T,
          β ((1 : GlobalTheory.BKReal.OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) =
            (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧
        (∀ g b, β (GlobalTheory.BKGal.actB (GlobalTheory.BKGal.sQ l) T g b) =
          actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧
        (∀ b, β (TWmap (GlobalTheory.BKReal.frobOB l ↥(OL LL)) T b) =
          φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧
        ∀ c ∈ continuousCocycles T.ρ,
          c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔
            ∃ b, GlobalTheory.BKGal.IsCobOf (GlobalTheory.BKGal.sQ l) T b c := by
  exact @GlobalTheory.BKGal.CrisTensor.exists_equiv
end

