module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0420
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLatticeLayerCoverBasisModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section
namespace GlobalTheory.CovLayer

open GlobalTheory.TraceConjugationCover

variable {l : ℕ} [Fact l.Prime]

theorem sumZ {Γ V : Type} [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] (Om l) V]
    (v : Γ → V) (F : Γ →₀ ℤ_[l]) : (F.sum fun g c => zOm l c • v g) = Finsupp.linearCombination ℤ_[l] v F := by
  simp only [Finsupp.linearCombination_apply, zOm_smul]

theorem sumZ_fin {ι V : Type} [Fintype ι] [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] (Om l) V] (v : ι → V) (w : ι → ℤ_[l]) : ∑ i, zOm l (w i) • v i = ∑ i, w i • v i := by
  simp only [zOm_smul]

theorem lpow_smul {V : Type} [AddCommGroup V] [Module (Om l) V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] (Om l) V]
    (N : ℕ) (x : V) : (l : Om l) ^ N • x = ((l : ℤ_[l]) ^ N) • x := by
  rw [← zOm_smul]; simp [zOm, map_pow, map_natCast]

theorem coord_unique {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V]
    [IsScalarTower ℤ_[l] ℚ_[l] V] {b : ι → V} (hb : LinearIndependent ℚ_[l] b) {v w : ι → ℤ_[l]}
    (h : ∑ i, v i • b i = ∑ i, w i • b i) : v = w := by
  have hz : LinearIndependent ℤ_[l] b := (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).2 hb
  funext i
  exact Fintype.linearIndependent_iffₛ.1 hz v w h i

theorem lc_translate {Γ A : Type} [Group Γ] [Ring A] [Module ℤ_[l] A] [SMulCommClass ℤ_[l] A A]
    [IsScalarTower ℤ_[l] A A] (v : Γ → A) (hv : ∀ g h, v (g * h) = v g * v h) (g : Γ) (F : Γ →₀ ℤ_[l]) :
    Finsupp.linearCombination ℤ_[l] v (F.mapDomain (g * ·)) = v g * Finsupp.linearCombination ℤ_[l] v F := by
  rw [Finsupp.linearCombination_mapDomain]
  have : (v ∘ (g * ·)) = (LinearMap.mulLeft ℤ_[l] (v g)) ∘ v := by funext h; simp [hv]
  rw [this, ← Finsupp.apply_linearCombination]
  rfl

theorem tup_mul {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (g h : Γ) :
    tup ρs (g * h) = tup ρs g * tup ρs h := by
  funext k; simp [tup, map_mul, Units.val_mul]

theorem tup_one {Γ : Type} [Group Γ] {a m : ℕ} (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) : tup ρs 1 = 1 := by
  funext k; simp [tup]

theorem coordsB {Γ : Type} [Group Γ] {a d : ℕ} {ρ : Γ →* GL (Fin d) ℤ_[l]} {r : Γ →* GL (Fin a) (Om l)}
    {b : Fin d → Matrix (Fin a) (Fin a) (Om l)} {e : Fin d → ℤ_[l]} (hR : Reads ρ r b e) (f : Γ →₀ ℤ_[l]) :
    Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) f =
      ∑ i, (f.sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j) • b i := by
  have key : ∀ h, ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) =
      ∑ i, (∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j) • b i := by
    intro h
    have h1 := hR.one
    have h2 := hR.equi h
    simp only [zOm_smul] at h1 h2
    calc ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) = (r h).val * ∑ j, e j • b j := by
          rw [h1, Matrix.mul_one]
      _ = ∑ j, e j • ((r h).val * b j) := by rw [Matrix.mul_sum]; simp only [Matrix.mul_smul]
      _ = ∑ j, e j • ∑ i, ((ρ h).val i j) • b i := by simp only [h2]
      _ = _ := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add (f := _), hf, hg, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, Finsupp.sum_add_index' (by simp) (by intros; ring)]
  | single h c =>
    rw [Finsupp.linearCombination_single, key h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_single_index (by simp), smul_smul]

theorem layer : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (Om l)) (d : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (b : Fin d → Matrix (Fin a) (Fin a) (Om l)) (e : Fin d → ℤ_[l]), Reads ρ r b e → LinearIndependent ℚ_[l] b → (∀ i, ∃ f : Γ →₀ ℤ_[l], b i = f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → ∀ c : ℕ, (∀ (n : ℕ) (f : Γ →₀ ℤ_[l]), (∀ g, ‖((f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) * ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + c)) → ∃ f' : Γ →₀ ℤ_[l], (f.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) = (l : Om l) ^ n • (f'.sum fun h c => zOm l c • ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))) → ∀ (n N : ℕ), n ≤ N → (∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ N • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹) → ∀ (m : ℕ) (ρs : Fin m → (Γ →* GL (Fin a) (Om l))) (L : Fin m → FinExt l) (t : Fin m → Finset (Matrix (Fin a) (Fin a) (Om l))), (∀ k, Continuous (ρs k)) → (∀ k g i j, ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ (L k).1) → (∀ k, ∀ x ∈ t k, ∀ i j, x i j ∈ (L k).1) → (∀ k (x : Matrix (Fin a) (Fin a) (Om l)), (∀ i j, x i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (t k : Set (Matrix (Fin a) (Fin a) (Om l)))) → (∀ k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t k, zOm l (c' y) • y = 1) → (∀ k g, ∀ x ∈ t k, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρs k g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t k, zOm l (c' y) • y) → ∀ cs : Fin m → Om l, (∀ g, ‖trc r g - ∑ k, cs k * trc (ρs k) g‖ ≤ ((l : ℝ)⁻¹) ^ (N + c)) → ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin m → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (L k).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin m → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (L k).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ GlobalTheory.TraceConjugationCover.latT ρs t M) ∧ (∀ x ∈ GlobalTheory.TraceConjugationCover.latT ρs t M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ GlobalTheory.TraceConjugationCover.Carries r b ρs t M bb P N ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
  intro l _ Γ _ _ a r d ρ b e hR hind hspan c hlow n N hnN hN m ρs L t hcont hρL htL hLspan hone hstab cs happ
  obtain ⟨u, hu⟩ := GlobalTheory.T.galoisRepTuple_span_saturation_bound l Γ a m ρs t hone hstab
  obtain ⟨M₁, hM₁⟩ := GlobalTheory.T.trace_estimate_scaledProductSpanLattice l Γ a r m ρs t c N n cs hnN happ
  refine ⟨max (N + u) M₁, fun M hM => ?_⟩
  have hMu : N + u ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : M₁ ≤ M := le_trans (le_max_right _ _) hM
  obtain ⟨hstL, hstT⟩ := GlobalTheory.T.scaledProductSpanLattice_stable_galoisRepTuple l Γ a m ρs t M hstab
  obtain ⟨hentT, hspT⟩ := GlobalTheory.T.scaledProductSpanLattice_entries_and_span l Γ a m ρs L t M hρL htL hLspan
  obtain ⟨d', bb, hbbind, hbbmem, hbbco⟩ := GlobalTheory.T.scaledProductSpanLattice_exists_padic_basis l Γ a m ρs t M hone hstab
  obtain ⟨ρ', hρ'c, hact⟩ := GlobalTheory.T.continuous_rep_of_matrixTuple_padic_basis l Γ a m ρs (latT ρs t M) d' bb hcont hbbind hbbmem hbbco hstT
  have hW : ∀ H : Γ →₀ ℤ_[l], Finsupp.linearCombination ℤ_[l] (tup ρs) H ∈ latL t M →
      ∃ w : Fin d → ℤ_[l], Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) H = (l : Om l) ^ N • ∑ i, w i • b i := by
    intro H hH
    rw [← sumZ] at hH
    obtain ⟨H', hH'⟩ := hu N M hMu H hH
    rw [sumZ, sumZ, lpow_smul] at hH'
    obtain ⟨f', hf'⟩ := GlobalTheory.T.galoisRepTuple_relation_mem_pow_span l Γ a r m ρs c N cs hlow happ (H - (l : ℤ_[l]) ^ N • H') (by
      rw [sumZ, map_sub, map_smul, hH', sub_self])
    rw [sumZ, sumZ, map_sub, map_smul, lpow_smul] at hf'
    refine ⟨fun i => (f' + H').sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j, ?_⟩
    rw [← coordsB hR (f' + H'), map_add (f := _), lpow_smul, smul_add, ← hf', sub_add_cancel]
  have hdec : ∀ s, ∃ (F : Γ →₀ ℤ_[l]) (y : Fin m → Matrix (Fin a) (Fin a) (Om l)), y ∈ latL t M ∧ bb s = Finsupp.linearCombination ℤ_[l] (tup ρs) F + y := by
    intro s
    obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hbbmem s)
    obtain ⟨F, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hx
    exact ⟨F, y, hy, by rw [← hxy, Finsupp.linearCombination_apply]⟩
  choose F y hy hFy using hdec
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin d) (Fin d') ℤ_[l], ∀ s, ∑ i, P i s • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) (F s) :=
    ⟨Matrix.of fun i s => (F s).sum fun h c => c * ∑ j, ((ρ h : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) i j * e j,
      fun s => (coordsB hR (F s)).symm⟩
  have hPz : ∀ z : Fin d' → ℤ_[l], ∑ i, (P *ᵥ z) i • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) (∑ s, z s • F s) := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, ← hP, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hCar : ∀ (z : Fin d' → ℤ_[l]) (G : Γ →₀ ℤ_[l]) (y0 : Fin m → Matrix (Fin a) (Fin a) (Om l)), y0 ∈ latL t M →
      ∑ s, z s • bb s = Finsupp.linearCombination ℤ_[l] (tup ρs) G + y0 →
      ∃ w : Fin d → ℤ_[l], ∑ i, (P *ᵥ z) i • b i = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) G + (l : Om l) ^ N • ∑ i, w i • b i := by
    intro z G y0 hy0 heq
    obtain ⟨w, hw⟩ := hW (∑ s, z s • F s - G) (by
      have hLF : ∀ s, Finsupp.linearCombination ℤ_[l] (tup ρs) (F s) = bb s - y s := fun s => by rw [hFy s]; abel
      have : Finsupp.linearCombination ℤ_[l] (tup ρs) (∑ s, z s • F s - G) = y0 - ∑ s, z s • y s := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sub, map_sum]
        simp only [map_smul, hLF, smul_sub, Finset.sum_sub_distrib, heq]
        abel
      rw [this]
      exact Submodule.sub_mem _ hy0 (Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (hy s)))
    refine ⟨w, ?_⟩
    rw [hPz, ← hw, map_sub]
    abel

  have h1T : (1 : Fin m → Matrix (Fin a) (Fin a) (Om l)) ∈ latT ρs t M := by rw [← tup_one ρs]; exact tup_mem_latT ρs t M 1
  obtain ⟨e', he'⟩ := hbbco 1 h1T
  have hrb : ∀ g (v : Fin d → ℤ_[l]), ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * ∑ s, v s • b s =
      ∑ i, (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) *ᵥ v) i • b i := by
    intro g v
    have h2 := hR.equi g
    simp only [zOm_smul] at h2
    rw [Matrix.mul_sum]
    simp only [Matrix.mul_smul, h2, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun i _ => by rw [mul_comm]
  have hrmul : ∀ g h, ((r (g * h) : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) = ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) := fun g h => by simp [map_mul, Units.val_mul]
  refine ⟨d', ρ', bb, e', P, hρ'c, fun s k i j => hentT _ (hbbmem s) k i j, hbbind, ?_, ?_, hbbmem, hbbco, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine Submodule.span_le.2 ?_ (hspT x hx)
    intro v hv
    obtain ⟨z, rfl⟩ := hbbco v hv
    refine Submodule.sum_mem _ fun s _ => ?_
    rw [show zOm l (z s) = algebraMap ℚ_[l] (Om l) (algebraMap ℤ_[l] ℚ_[l] (z s)) from rfl, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · intro k
    constructor
    · intro g j
      have := congrFun (hact g j) k
      simpa only [Pi.mul_apply, Finset.sum_apply, Pi.smul_apply, tup] using this
    · have := congrFun he'.symm k
      simpa only [Finset.sum_apply, Pi.smul_apply, Pi.one_apply] using this
  · intro z G y0 hy0 heq
    rw [sumZ_fin, sumZ] at heq
    obtain ⟨w, hw⟩ := hCar z G y0 hy0 heq
    exact ⟨w, by rw [sumZ_fin, sumZ, sumZ_fin]; exact hw⟩
  · constructor
    · intro g i j
      have hz := hact g j
      rw [sumZ_fin] at hz
      obtain ⟨w, hw⟩ := hCar (fun s => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j)
        ((F j).mapDomain (g * ·)) (tup ρs g * y j) (hstL g _ (hy j)) (by
          rw [← hz, lc_translate _ (tup_mul ρs) g, hFy j, mul_add])
      rw [lc_translate _ hrmul g, ← hP j, hrb, lpow_smul, Finset.smul_sum, ← Finset.sum_add_distrib] at hw
      simp only [smul_smul, ← add_smul] at hw
      have := congrFun (coord_unique hind hw) i
      have e1 : (P * ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) i j =
          (P *ᵥ fun s => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l]) s j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      have e2 : (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) * P) i j =
          (((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l]) *ᵥ fun s => P s j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [Matrix.sub_apply, e1, e2, this, add_sub_cancel_left]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
    · have hb : ∀ j, ∃ f : Γ →₀ ℤ_[l], b j = Finsupp.linearCombination ℤ_[l] (fun h => ((r h : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) f := fun j => by
        obtain ⟨f, hf⟩ := hspan j
        exact ⟨f, by rw [hf, sumZ]⟩
      choose f hf using hb
      have hz : ∀ j, ∃ z : Fin d' → ℤ_[l], Finsupp.linearCombination ℤ_[l] (tup ρs) (f j) = ∑ s, z s • bb s := fun j => by
        obtain ⟨z, hz⟩ := hbbco _ (Submodule.mem_sup_left (Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨f j, by rw [Finsupp.linearCombination_apply]⟩) : Finsupp.linearCombination ℤ_[l] (tup ρs) (f j) ∈ latT ρs t M)
        exact ⟨z, by rw [hz, sumZ_fin]⟩
      choose z hz using hz
      refine ⟨Matrix.of fun s j => z j s, fun i j => ?_⟩
      obtain ⟨w, hw⟩ := hCar (z j) (f j) 0 (Submodule.zero_mem _) (by rw [add_zero, hz j])
      rw [← hf j, lpow_smul, Finset.smul_sum] at hw
      have hbj : b j = ∑ i, (1 : Matrix (Fin d) (Fin d) ℤ_[l]) i j • b i := by
        simp [Matrix.one_apply, ite_smul]
      rw [hbj, ← Finset.sum_add_distrib] at hw
      simp only [smul_smul, ← add_smul] at hw
      have := congrFun (coord_unique hind hw) i
      have e1 : (P * Matrix.of fun s j => z j s) i j = (P *ᵥ z j) i := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [Matrix.sub_apply, e1, this, add_sub_cancel_left]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
  · intro i
    obtain ⟨w, hw⟩ := hCar e' (Finsupp.single 1 1) 0 (Submodule.zero_mem _) (by
      rw [add_zero, Finsupp.linearCombination_single, one_smul, tup_one, he', sumZ_fin])
    rw [Finsupp.linearCombination_single, one_smul, map_one, Units.val_one, ← hR.one, sumZ_fin, lpow_smul,
      Finset.smul_sum, ← Finset.sum_add_distrib] at hw
    simp only [smul_smul, ← add_smul] at hw
    have := congrFun (coord_unique hind hw) i
    rw [Pi.sub_apply, this, add_sub_cancel_left]
    exact Dvd.dvd.mul_right (pow_dvd_pow _ hnN) _
  · intro s
    have := hM₁ M hM1 (F s) (y s) (hy s)
    rw [sumZ_fin, hP s, hFy s, ← sumZ, ← sumZ]
    exact this

end GlobalTheory.CovLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemSubmoduleAllCharpolySeparable
section
open Polynomial

namespace GlobalTheory.SepGeneric

theorem separable_iff_resultant {K : Type} [Field K] {f : K[X]} (hf : f.Monic) {t : ℕ}
    (ht : f.natDegree = t) : f.Separable ↔ resultant f (derivative f) t t ≠ 0 := by
  have hle : (derivative f).natDegree ≤ t :=
    (natDegree_derivative_le f).trans (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
  have h1 : resultant f (derivative f) t t
      = resultant f (derivative f) f.natDegree (derivative f).natDegree := by
    have := resultant_add_right_deg f (derivative f) t (derivative f).natDegree k le_rfl
    rw [← hk] at this
    rw [this, ← ht, hf.coeff_natDegree]
    simp
  rw [h1, ← isUnit_iff_ne_zero, isUnit_resultant_iff_isCoprime hf]
  rfl

theorem finite_bad_base {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K)
    (hB : B.charpoly.Separable) : {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  classical
  let N : Matrix (Fin t) (Fin t) K[X] := B.map C + (X : K[X]) • A.map C
  let D : K[X] := resultant N.charpoly (derivative N.charpoly) t t
  have hN : ∀ l : K, N.map (evalRingHom l) = B + l • A := by
    intro l
    ext i j
    simp [N]
    ring
  have hD : ∀ l : K, (B + l • A).charpoly.Separable ↔ D.eval l ≠ 0 := by
    intro l
    rw [separable_iff_resultant (Matrix.charpoly_monic _)
      (t := t) (by simp), ← hN, Matrix.charpoly_map, derivative_map, resultant_map_map]
    rfl
  have hD0 : D ≠ 0 := by
    intro h
    have := (hD 0).1 (by simpa using hB)
    simp [h] at this
  refine (D.roots.toFinset.finite_toSet).subset ?_
  intro l hl
  simp only [Set.mem_setOf_eq, hD, not_not] at hl
  simp [hD0, hl]

theorem separable_smul {K : Type} [Field K] {t : ℕ} (A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : A.charpoly.Separable) : (c • A).charpoly.Separable := by
  classical
  have h1 : (c • A).charpoly = C c ^ t * A.charpoly.comp (C c⁻¹ * X) := by
    have : (c • A).charmatrix = (C c : K[X]) • (A.charmatrix.map (compRingHom (C c⁻¹ * X))) := by
      ext1 i j
      by_cases h : i = j
      · subst h
        have h3 : (C c : K[X]) * (C c⁻¹ * X) = X := by
          rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]
        simp [mul_sub, h3]
      · simp [Matrix.charmatrix_apply_ne _ _ _ h]
    rw [Matrix.charpoly, this, Matrix.det_smul, Matrix.charpoly, Fintype.card_fin]
    congr 1
    exact ((compRingHom (C c⁻¹ * X)).map_det A.charmatrix).symm
  have h2 : (A.charpoly.comp (C c⁻¹ * X)).Separable := by
    rw [separable_def, derivative_comp]
    have hu : IsUnit (derivative (C c⁻¹ * X : K[X])) := by
      simpa using isUnit_C.2 (IsUnit.mk0 _ (inv_ne_zero hc))
    rw [isCoprime_mul_unit_left_right hu]
    exact ((separable_def _).1 hA).map (compRingHom (C c⁻¹ * X))
  rw [h1, mul_comm]
  exact h2.mul_unit ((isUnit_C.2 (IsUnit.mk0 _ hc)).pow t)

theorem finite_bad_dir {K : Type} [Field K] {t : ℕ} (B A : Matrix (Fin t) (Fin t) K) {c : K}
    (hc : c ≠ 0) (hA : (c • A).charpoly.Separable) :
    {l : K | ¬ (B + l • A).charpoly.Separable}.Finite := by
  have hA' : A.charpoly.Separable := by
    have := separable_smul _ (inv_ne_zero hc) hA
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hf := (finite_bad_base A B hA').preimage (f := fun l : K => l⁻¹) inv_injective.injOn
  refine (hf.insert 0).subset ?_
  intro l hl
  by_cases h0 : l = 0
  · exact Or.inl h0
  · refine Or.inr ?_
    intro h
    apply hl
    have := separable_smul _ h0 h
    rwa [smul_add, smul_smul, mul_inv_cancel₀ h0, one_smul, add_comm] at this

theorem exists_separable {O K X : Type} [CommRing O] [IsDomain O] [Infinite O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite X] (t : ℕ)
    (M : Submodule O (X → Matrix (Fin t) (Fin t) K)) (a : X → Matrix (Fin t) (Fin t) K)
    (h : ∀ x, (a x).charpoly.Separable ∨
      ∃ s ∈ M, ∃ c : K, c ≠ 0 ∧ (c • s x).charpoly.Separable) :
    ∃ s ∈ M, ∀ x, (a x + s x).charpoly.Separable := by
  classical
  have key : ∀ Y : Finset X, ∃ s ∈ M, ∀ x ∈ Y, (a x + s x).charpoly.Separable := by
    intro Y
    induction Y using Finset.induction_on with
    | empty => exact ⟨0, M.zero_mem, by simp⟩
    | insert x Y hx ih =>
      obtain ⟨s, hs, hY⟩ := ih
      have h1 : ∃ s' ∈ M, {l : K | ¬ (a x + s x + l • s' x).charpoly.Separable}.Finite := by
        rcases h x with h | ⟨s', hs', c, hc, h⟩
        · refine ⟨s, hs, ?_⟩
          have hf := (finite_bad_base (a x) (s x) h).preimage (f := fun l : K => 1 + l)
            (add_right_injective 1).injOn
          refine hf.subset ?_
          intro l hl
          simpa [add_smul, add_assoc] using hl
        · exact ⟨s', hs', finite_bad_dir _ _ hc h⟩
      obtain ⟨s', hs', h1⟩ := h1
      have h2 : (⋃ y ∈ insert x Y,
          {l : K | ¬ (a y + s y + l • s' y).charpoly.Separable}).Finite := by
        refine (insert x Y).finite_toSet.biUnion ?_
        intro y hy
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact h1
        · exact finite_bad_base _ _ (hY y hy)
      have h3 := h2.preimage (f := algebraMap O K) (IsFractionRing.injective O K).injOn
      obtain ⟨l, hl⟩ := h3.exists_notMem
      refine ⟨s + l • s', M.add_mem hs (M.smul_mem l hs'), ?_⟩
      intro y hy
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_not] at hl
      have := hl y hy
      rwa [algebraMap_smul, add_assoc] at this
  have := Fintype.ofFinite X
  obtain ⟨s, hs, h⟩ := key Finset.univ
  exact ⟨s, hs, fun x => h x (Finset.mem_univ x)⟩

end GlobalTheory.SepGeneric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMem
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.IntegralPowerScalar

theorem exists_pow_mul_integral {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (c : ↥LL.1) :
    ∃ n : ℕ, (l : ↥LL.1) ^ n * c ∈ OL LL := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have h1 : IsAlgebraic ℚ_[l] c := IsAlgebraic.of_finite ℚ_[l] c
  have h2 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).2 h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hs := PadicInt.unitCoeff_spec hy
  have hm : y • c ∈ OL LL := hint
  have hm2 := (OL LL).smul_mem hm (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  have he : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    exact (Units.inv_mul_eq_iff_eq_mul _).2 hs
  rw [smul_smul, he, Algebra.smul_def, map_pow, map_natCast] at hm2
  exact hm2

theorem smul_mem_of_mem {l : ℕ} [Fact (Nat.Prime l)] {LL : FinExt l} (T : GlobalTheory.BKGal.QLat LL)
    {c : ↥LL.1} (hc : c ∈ OL LL) {x : T.V} (hx : x ∈ T.L.T) : c • x ∈ T.L.T := by
  have h := T.L.T.smul_mem (⟨c, hc⟩ : ↥(OL LL)) hx
  rw [← algebraMap_smul ↥LL.1 (⟨c, hc⟩ : ↥(OL LL)) x] at h
  exact h

theorem exists_pow_smul_mem {l : ℕ} [inst : Fact (Nat.Prime l)] {LL : FinExt l}
    (T : GlobalTheory.BKGal.QLat LL) (v : T.V) : ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  have hl : ∀ k : ℕ, (l : ↥LL.1) ^ k ∈ OL LL := fun k => pow_mem (natCast_mem (OL LL) l) k
  have hv : v ∈ Submodule.span ↥LL.1 (T.L.T : Set T.V) := by
    rw [T.L.span]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rw [pow_zero, one_smul]; exact hx⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    have h1 := smul_mem_of_mem T (hl n) hm
    have h2 := smul_mem_of_mem T (hl m) hn
    rw [smul_smul, ← pow_add, Nat.add_comm] at h1
    rw [smul_smul, ← pow_add] at h2
    rw [smul_add]
    exact T.L.T.add_mem h1 h2
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := exists_pow_mul_integral LL c
    refine ⟨n + m, ?_⟩
    have h := smul_mem_of_mem T hn hm
    have e : (l : ↥LL.1) ^ (n + m) * c = (l : ↥LL.1) ^ n * c * (l : ↥LL.1) ^ m := by ring
    have e2 : (l : ↥LL.1) ^ (n + m) • c • x = ((l : ↥LL.1) ^ n * c) • (l : ↥LL.1) ^ m • x :=
      (smul_smul _ _ x).trans ((congrArg (fun a : ↥LL.1 => a • x) e).trans (smul_smul _ _ x).symm)
    exact Eq.mpr (congrArg (fun w : T.V => w ∈ T.L.T) e2) h

end GlobalTheory.IntegralPowerScalar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemLattice
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.LatticePowerScalar

theorem exists_pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K]
    [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] {c : K} (hc : IsAlgebraic ℚ_[l] c) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℤ_[l] c := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).2 hc
  obtain ⟨y, hy, hyc⟩ := h1.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have h2 : (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * y = (l : ℤ_[l]) ^ y.valuation := by
    rw [Units.inv_mul_eq_iff_eq_mul]
    exact PadicInt.unitCoeff_spec hy
  have h3 : (l : K) ^ y.valuation * c = (((PadicInt.unitCoeff hy)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, h2, Algebra.smul_def, map_pow, map_natCast]
  rw [h3]
  exact hyc.smul _

theorem exists_pow_smul_mem {O K V : Type} [CommRing O] [CommRing K] [Algebra O K] [AddCommGroup V]
    [Module K V] [Module O V] [IsScalarTower O K V] (p : O)
    (hp : ∀ c : K, ∃ (n : ℕ) (o : O), algebraMap O K p ^ n * c = algebraMap O K o)
    (M : Submodule O V) (v : V) (hv : v ∈ Submodule.span K (M : Set V)) :
    ∃ n : ℕ, algebraMap O K p ^ n • v ∈ M := by
  have up : ∀ (n k : ℕ) (x : V), algebraMap O K p ^ n • x ∈ M → algebraMap O K p ^ (k + n) • x ∈ M := by
    intro n k x hx
    rw [pow_add, mul_smul, ← map_pow, algebraMap_smul]
    exact M.smul_mem _ hx
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, hn⟩ := hy
    refine ⟨m + n, ?_⟩
    rw [smul_add]
    exact M.add_mem (add_comm n m ▸ up m n x hm) (up n m y hn)
  | smul c x _ hx =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨n, o, ho⟩ := hp c
    refine ⟨n + m, ?_⟩
    have h : algebraMap O K p ^ (n + m) • c • x = o • (algebraMap O K p ^ m • x) := by
      rw [← algebraMap_smul K o, ← ho, smul_smul, smul_smul, pow_add]
      congr 1
      ring
    rw [h]
    exact M.smul_mem _ hm

theorem exists_pow_smul_mem_lattice {l : ℕ} [Fact (Nat.Prime l)] (LL : FinExt l) (T : GlobalTheory.BKGal.QLat LL) :
    ∀ v ∈ Submodule.span ↥LL.1 ((T.L.T : Submodule ↥(OL LL) T.V) : Set T.V),
      ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T := by
  intro v hv
  have hl : algebraMap ↥(OL LL) ↥LL.1 (l : ↥(OL LL)) = (l : ↥LL.1) := map_natCast _ l
  rw [← hl]
  refine exists_pow_smul_mem (l : ↥(OL LL)) (fun c => ?_) T.L.T v hv
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨n, hn⟩ := exists_pow_mul_isIntegral (l := l) (Algebra.IsAlgebraic.isAlgebraic (R := ℚ_[l]) c)
  exact ⟨n, ⟨(l : ↥LL.1) ^ n * c, hn⟩, by rw [hl]; rfl⟩

end GlobalTheory.LatticePowerScalar
end
end

