module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0198
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0200
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0219
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0227
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import GroundTheory.LocalFields.MainTheorem
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace
public import GroundTheory.LocalFields.LocalFourierHaar

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem locCpt (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : LocallyCompactSpace (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem exists_haar (n : ℕ) : ∃ (_ : MeasurableSpace (G n)) (_ : BorelSpace (G n)) (μ : Measure (G n)), μ.IsHaarMeasure := by
  haveI := locCpt n
  letI : MeasurableSpace (G n) := borel _
  haveI : BorelSpace (G n) := ⟨rfl⟩
  exact ⟨inferInstance, inferInstance, Measure.haar, inferInstance⟩

theorem waveEq {n : ℕ} (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (A : E.V →L[ℂ] E.V)
    (hA : ∀ f ∈ CE E, ∀ g ∈ GLs n, Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g + A (f g)) :
    ∀ s, ∀ y ∈ GLs n, dt (dt u) s y = (1 / 4 : ℝ) • ∑ p : Ix n, Rr (hm p) (Rt (hm p) u s) y + (A.restrictScalars ℝ) (u s y) := by
  intro s y hy
  have h := hu.2.2.1 s y hy
  rw [hA _ (hu.2.1 s) y hy] at h
  have h2 : dt (dt u) s y = iteratedDeriv 2 (fun r => u r y) s := by
    simp only [dt, iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h2, h]
  have : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  rfl

theorem speed_pos (hL : LgFacts) (hR : RCalc) {n : ℕ} (C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hlg : ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C₁)
    (χ : ℝ → ℝ) (h1 : ContDiff ℝ ∞ χ) (h2 : ∀ x, deriv χ x ≤ 0) (h3 : ∀ x, 0 ≤ χ x) (h4 : ∀ x, x ≤ 0 → χ x = 1) (h5 : ∀ x, 1 ≤ x → χ x = 0)
    (E : KMod n) (u : ℝ → Mat n → E.V) (hu : IsWave E u) (t : ℝ) (ht : 0 ≤ t) (x : Mat n) (hx : x ∈ GLs n)
    (C : ℝ) (hC : C₁ * (1 + Fintype.card (Ix n)) ≤ C)
    (h0 : ∀ y ∈ GLs n, lg y ≤ lg (1 : Mat n) + 1 + C * t → u 0 (x * y) = 0) : u t x = 0 := by
  obtain ⟨mG, bG, μ, hμ⟩ := exists_haar n
  letI : InnerProductSpace ℝ E.V := InnerProductSpace.rclikeToReal ℂ E.V
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.CompanionTheory.WaveSpd.om_section E
  obtain ⟨l1, l2, l3⟩ := hlg x hx
  have hxu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have hxx : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul _ hxu
  have hxx' : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
  have hxi : x⁻¹ ∈ GLs n := by
    have : x⁻¹.det * x.det = 1 := by rw [← Matrix.det_mul, hxx, Matrix.det_one]
    exact left_ne_zero_of_mul_eq_one this |> fun h => h
  have hmul : ∀ y ∈ GLs n, x⁻¹ * y ∈ GLs n := fun y hy => by
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul]
    exact mul_ne_zero hxi hy
  have hbp : ∀ Ψ : Mat n → ℝ, ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg (x⁻¹ * y) → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
    intro Ψ hΨ ⟨R, hRΨ⟩ X
    refine _root_.GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero hR μ Ψ hΨ ⟨R + lg x, fun y hy hlt => hRΨ y hy ?_⟩ X
    have := (hL n).1 x hx _ (hmul y hy)
    rw [← mul_assoc, hxx', one_mul] at this
    linarith
  have hv := _root_.GlobalTheory.CompanionTheory.WaveSpd.Vanish.energy_vanish (W := E.V) μ (fun y => lg (x⁻¹ * y)) l1 l2 C₁ hC₁ l3 hbp χ h1 h2 h3 h5 u hu.1
    (A.restrictScalars ℝ) (waveEq E u hu A hA) C hC (lg (1 : Mat n) + C * t) h4 ?_ ?_ t ht x hx ?_
  · exact hv
  · intro y hy hlt
    have := h0 (x⁻¹ * y) (hmul y hy) (by have h' : lg (x⁻¹ * y) < lg (1 : Mat n) + C * t + 1 := hlt; linarith)
    rwa [← mul_assoc, hxx', one_mul] at this
  · intro y hy
    exact hu.2.2.2 y hy
  · simp only [hxx]
    exact le_refl _

theorem asmSpeed : AsmSpeed := by
  intro hL hU hR n
  obtain ⟨C₁, hC₁, hlg⟩ := _root_.GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts hL n
  obtain ⟨χ, h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.CompanionTheory.SmoothCut.exists_smooth_antitone_cut
  set C := C₁ * (1 + Fintype.card (Ix n)) with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hl0 : 0 ≤ lg (1 : Mat n) := by
    unfold lg
    apply Real.log_nonneg
    have : 0 ≤ ∑ a, ∑ b, (‖(1 : Mat n) a b‖ ^ 2 + ‖(1 : Mat n)⁻¹ a b‖ ^ 2) := by positivity
    linarith
  refine ⟨C + lg (1 : Mat n) + 1, ?_⟩
  have key : ∀ (E : KMod n) (u : ℝ → Mat n → E.V), IsWave E u → ∀ t : ℝ, 0 ≤ t → ∀ x ∈ GLs n,
      (∀ y ∈ GLs n, lg y ≤ (C + lg (1 : Mat n) + 1) * (1 + t) → u 0 (x * y) = 0) → u t x = 0 := by
    intro E u hu t ht x hx h0
    refine speed_pos hL hR C₁ hC₁ hlg χ h1 h2 h3 h4 h5 E u hu t ht x hx C le_rfl ?_
    intro y hy hle
    refine h0 y hy (hle.trans ?_)
    nlinarith [mul_nonneg hC0 ht, mul_nonneg hl0 ht]
  intro E u hu t x hx h0
  rcases le_total 0 t with ht | ht
  · exact key E u hu t ht x hx (by rwa [abs_of_nonneg ht] at h0)
  · have := key E _ (_root_.GlobalTheory.CompanionTheory.WaveSpd.isWave_time_refl E u hu) (-t) (by linarith) x hx (by
      intro y hy hle
      simp only [neg_zero]
      exact h0 y hy (by rwa [abs_of_nonpos ht]))
    simpa using this

end GlobalTheory.CompanionTheory.WaveSpd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitDetEmbMat
section
noncomputable section

namespace GlobalTheory.CompanionTheory.DeRhamChar

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cmp.JumpDict GlobalTheory.Cmp.SmallJumps
open scoped Classical

section Coord

variable {Qp Om LL BdR : Type} [Field Qp] [Field Om] [Field LL] [CommRing BdR]
  [Algebra Qp Om] [Algebra Qp LL] [Algebra Qp BdR] [Algebra Om BdR] [IsScalarTower Qp Om BdR]

def ev (σ : LL →ₐ[Qp] Om) : (Fin 1 → LL) ⊗[Qp] BdR →ₗ[Qp] BdR :=
  TensorProduct.lift
    ((LinearMap.mul Qp BdR).comp
      (((IsScalarTower.toAlgHom Qp Om BdR).toLinearMap.comp σ.toLinearMap).comp
        (LinearMap.proj 0 : (Fin 1 → LL) →ₗ[Qp] LL)))

@[simp] theorem ev_tmul (σ : LL →ₐ[Qp] Om) (v : Fin 1 → LL) (b : BdR) :
    ev σ (v ⊗ₜ[Qp] b) = algebraMap Om BdR (σ (v 0)) * b := by
  simp [ev]

theorem ev_smul (σ : LL →ₐ[Qp] Om) (c : LL) (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    ev σ (c • z) = algebraMap Om BdR (σ c) * ev σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [TensorProduct.smul_tmul', mul_assoc]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy, mul_add]

variable [FiniteDimensional Qp LL] [Algebra.IsSeparable Qp LL] [IsAlgClosed Om]


variable (Qp Om LL) in
def embBasis : Basis (LL →ₐ[Qp] Om) Qp LL :=
  (finBasis Qp LL).reindex (Fintype.equivFinOfCardEq (AlgHom.card Qp LL Om)).symm


variable (Qp Om LL) in
def embMat : Matrix (LL →ₐ[Qp] Om) (LL →ₐ[Qp] Om) Om :=
  Algebra.embeddingsMatrixReindex Qp Om (embBasis Qp Om LL) (Equiv.refl _)

theorem embMat_apply (i j : LL →ₐ[Qp] Om) : embMat Qp Om LL i j = j (embBasis Qp Om LL i) := rfl

theorem isUnit_det_embMat : IsUnit (embMat Qp Om LL).det := by
  refine isUnit_iff_ne_zero.2 fun h => ?_
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two Qp Om (embBasis Qp Om LL) (Equiv.refl _)
  have h2 : algebraMap Qp Om (Algebra.discr Qp (embBasis Qp Om LL)) = 0 := by
    rw [h1]; change (embMat Qp Om LL).det ^ 2 = 0; rw [h]; simp
  exact Algebra.discr_not_zero_of_basis Qp (embBasis Qp Om LL)
    ((map_eq_zero_iff _ (algebraMap Qp Om).injective).1 h2)

def coordInv (f : (LL →ₐ[Qp] Om) → BdR) : (Fin 1 → LL) ⊗[Qp] BdR :=
  ∑ i, (fun _ => embBasis Qp Om LL i) ⊗ₜ[Qp]
    ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j

theorem ev_coordInv (f : (LL →ₐ[Qp] Om) → BdR) (k : LL →ₐ[Qp] Om) :
    ev k (coordInv f) = f k := by
  have hN : (embMat Qp Om LL)⁻¹ * embMat Qp Om LL = 1 := Matrix.nonsing_inv_mul _ isUnit_det_embMat
  have h1 : ∀ j, ∑ i, embMat Qp Om LL i k * (embMat Qp Om LL)⁻¹ j i = if j = k then 1 else 0 := fun j => by
    have := congrFun (congrFun hN j) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordInv, map_sum, ev_tmul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h2 : ∀ j, ∑ i, algebraMap Om BdR (k (embBasis Qp Om LL i)) *
      (algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) * f j) =
      algebraMap Om BdR (if j = k then 1 else 0) * f j := fun j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1 j, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, embMat_apply, mul_assoc]
  simp only [h2]
  simp

theorem coordInv_add (f g : (LL →ₐ[Qp] Om) → BdR) : coordInv (f + g) = coordInv f + coordInv g := by
  simp only [coordInv, Pi.add_apply, mul_add, Finset.sum_add_distrib, tmul_add]

theorem coordInv_ev (z : (Fin 1 → LL) ⊗[Qp] BdR) :
    coordInv (fun σ : LL →ₐ[Qp] Om => ev σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp [coordInv]
  | add x y hx hy =>
    nth_rw 2 [← hx]
    nth_rw 2 [← hy]
    rw [← coordInv_add]
    congr 1
    funext σ
    exact map_add (ev σ) x y
  | tmul v b =>
    have hM : embMat Qp Om LL * (embMat Qp Om LL)⁻¹ = 1 := Matrix.mul_nonsing_inv _ isUnit_det_embMat
    set a := (embBasis Qp Om LL).repr (v 0) with ha
    have hv : v 0 = ∑ k, a k • embBasis Qp Om LL k := ((embBasis Qp Om LL).sum_repr (v 0)).symm
    have h1 : ∀ i, ∑ j, (embMat Qp Om LL)⁻¹ j i * j (v 0) = algebraMap Qp Om (a i) := fun i => by
      have h2 : ∀ j : LL →ₐ[Qp] Om, j (v 0) = ∑ k, algebraMap Qp Om (a k) * embMat Qp Om LL k j := fun j => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hv, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, Algebra.smul_def, embMat_apply]
      simp only [h2, Finset.mul_sum]
      rw [Finset.sum_comm]
      have h3 : ∀ k, ∑ j, (embMat Qp Om LL)⁻¹ j i * (algebraMap Qp Om (a k) * embMat Qp Om LL k j) =
          algebraMap Qp Om (a k) * (if k = i then 1 else 0) := fun k => by
        have := congrFun (congrFun hM k) i
        rw [Matrix.mul_apply, Matrix.one_apply] at this
        rw [← this, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring
      simp only [h3]
      simp
    have h4 : ∀ i, ∑ j, algebraMap Om BdR ((embMat Qp Om LL)⁻¹ j i) *
        (algebraMap Om BdR (j (v 0)) * b) = a i • b := fun i => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply Qp Om BdR, ← h1, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, mul_assoc]
    simp only [coordInv, ev_tmul, h4, tmul_smul]
    have h5 : v = ∑ i, a i • (fun _ : Fin 1 => embBasis Qp Om LL i) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp only [Finset.sum_apply, Pi.smul_apply]
      exact hv
    conv_rhs => rw [h5, sum_tmul]
    exact Finset.sum_congr rfl fun i _ => rfl

theorem ev_injective {z w : (Fin 1 → LL) ⊗[Qp] BdR} (h : ∀ σ : LL →ₐ[Qp] Om, ev σ z = ev σ w) : z = w := by
  rw [← coordInv_ev (Om := Om) z, ← coordInv_ev (Om := Om) w]
  exact congrArg _ (funext h)

end Coord

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem mem_DdR_iff (ρ : Representation LL G V) (z : V ⊗[Qp] BdR) :
    z ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g z = z := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem mem_DdRE_iff (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (z : V ⊗[Qp] BdR) :
    z ∈ DdRE PD ρ τ ↔ z ∈ DdR PD ρ ∧
      ∀ c, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c z = τ c • z := by
  simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

theorem exists_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ)
    (h : ∀ a, multV PD ρ τ a = if a = J then 1 else 0) :
    ∃ z ∈ DdRE PD ρ τ, (∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z) ∧
      z ∈ FilV PD (LL := LL) (V := V) J ∧ z ∉ FilV PD (LL := LL) (V := V) (J + 1) := by
  haveI : FiniteDimensional LL (DdRE PD ρ τ) :=
    finite_ddRE_of_multV PD ρ τ {J} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have hanti : ∀ a, FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := fun a =>
    inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1))
  have h1 : finrank LL (DdRE PD ρ τ) = 1 :=
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left) hanti
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) J h
  have hJ := h J
  rw [if_pos rfl] at hJ
  unfold multV at hJ
  have hle : finrank LL (FildR PD ρ τ J) ≤ 1 := by
    rw [← h1]; exact Submodule.finrank_mono inf_le_left
  have h2 : finrank LL (FildR PD ρ τ J) = 1 := by omega
  have h3 : finrank LL (FildR PD ρ τ (J + 1)) = 0 := by omega
  have h4 : FildR PD ρ τ J = DdRE PD ρ τ :=
    Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [h1, h2])
  haveI : FiniteDimensional LL (FildR PD ρ τ (J + 1)) := Submodule.finiteDimensional_of_le inf_le_left
  have h5 : FildR PD ρ τ (J + 1) = ⊥ := Submodule.finrank_eq_zero.1 h3
  obtain ⟨z, hz0, hz⟩ := finrank_eq_one_iff'.1 h1
  have hz1 : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ J := by rw [h4]; exact z.2
  refine ⟨z, z.2, fun w hw => ?_, hz1.2, fun hz2 => ?_⟩
  · obtain ⟨c, hc⟩ := hz ⟨w, hw⟩
    exact ⟨c, (congrArg Subtype.val hc).symm⟩
  · have : (z : V ⊗[Qp] BdR) ∈ FildR PD ρ τ (J + 1) := ⟨z.2, hz2⟩
    rw [h5, Submodule.mem_bot] at this
    exact hz0 (Subtype.ext this)

theorem multV_of_gen (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : ℤ) (z : V ⊗[Qp] BdR)
    (hz : z ∈ DdRE PD ρ τ) (hgen : ∀ w ∈ DdRE PD ρ τ, ∃ c : LL, w = c • z)
    (h1 : z ∈ FilV PD (LL := LL) (V := V) J) (h2 : z ∉ FilV PD (LL := LL) (V := V) (J + 1)) (a : ℤ) :
    multV PD ρ τ a = if a = J then 1 else 0 := by
  have hz0 : z ≠ 0 := fun h => h2 (h ▸ Submodule.zero_mem _)
  have hlo : ∀ a ≤ J, FildR PD ρ τ a = LL ∙ z := fun a ha => by
    refine le_antisymm (fun w hw => ?_) ?_
    · obtain ⟨c, rfl⟩ := hgen w hw.1
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact ⟨hz, filV_anti PD ha h1⟩
  have hhi : ∀ a, J < a → FildR PD ρ τ a = ⊥ := fun a ha => by
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨c, rfl⟩ := hgen w hw.1
    by_cases hc : c = 0
    · simp [hc]
    · refine absurd ?_ h2
      have := filV_anti PD (by omega : J + 1 ≤ a) hw.2
      simpa [hc] using (Submodule.smul_mem_iff _ hc).1 this
  have hone : finrank LL (LL ∙ z) = 1 := finrank_span_singleton hz0
  unfold multV
  rcases lt_trichotomy a J with ha | ha | ha
  · rw [hlo a ha.le, hlo (a + 1) (by omega), if_neg ha.ne]; simp
  · subst ha
    rw [hlo a le_rfl, hhi (a + 1) (by omega), if_pos rfl, hone]; simp
  · rw [hhi a ha, hhi (a + 1) (by omega), if_neg ha.ne']; simp

end Period

end GlobalTheory.CompanionTheory.DeRhamChar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFromKummerUnramifiedUnit
section
open ValuativeRel IntermediateField

namespace GlobalTheory.CompanionTheory.LocalField

open GroundTheory.LocalField

theorem exists_norm_fixedField_ker_eq_unit :
    ∀ {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
      [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), N ≠ 0 → ∀ ξ : Ω,
      IsPrimitiveRoot ξ (Nat.card 𝓀[K] ^ N - 1) →
      ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) →
      (∀ g : Ω ≃ₐ[K] Ω, g ξ = ξ → ψ g = 1) → ∀ U : Kˣ, GroundTheory.LocalField.ord (U : K) = 0 →
      ∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K) := by
  intro K Ω _ _ _ _ _ _ _ N hN ξ hξ ψ hopen hψ U hU
  have hgal : IsGalois K Ω := inferInstance
  obtain ⟨hL, -⟩ := isUnramifiedSubextension_adjoin hN hξ
  have := hL.1
  have := hL.isGalois
  have hclosed : IsClosed (ψ.ker : Set (Ω ≃ₐ[K] Ω)) := Subgroup.isClosed_of_isOpen _ hopen
  let C : ClosedSubgroup (Ω ≃ₐ[K] Ω) := ⟨ψ.ker, hclosed⟩
  set M : IntermediateField K Ω := fixedField ψ.ker with hM
  have hMU : M.fixingSubgroup = ψ.ker := InfiniteGalois.fixingSubgroup_fixedField C
  have hML : M ≤ K⟮ξ⟯ := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K⟮ξ⟯]
    intro x hx
    rw [mem_fixedField_iff]
    intro g hg
    have hgξ : g ξ = ξ := (mem_fixingSubgroup_iff _ _).1 hg ξ (mem_adjoin_simple_self K ξ)
    exact (mem_fixedField_iff _ _).1 hx g (hψ g hgξ)
  have : FiniteDimensional K M := FiniteDimensional.of_injective (IntermediateField.inclusion hML).toLinearMap
    (IntermediateField.inclusion hML).toRingHom.injective
  have : IsGalois K M := IsGalois.of_fixedField_normal_subgroup ψ.ker
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun τ₁ τ₂ => by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, hMU, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, mul_inv_rev]
    rw [mul_comm (ψ g₁) (ψ g₂)]
    group⟩⟩
  have : IsAbelianGalois K M := ⟨⟩
  have hle := hL.le_maximalUnramifiedExtension
  have h1 := restrictAb_localArtinMap_of_le_maximalUnramifiedExtension K⟮ξ⟯ hle U
  rw [hU, zpow_zero] at h1
  have h2 : restrictAb M (le_maximalAbelianExtension M) (localArtinMap K Ω U) = 1 := by
    ext x
    have e1 := restrictAb_apply M (le_maximalAbelianExtension M) (localArtinMap K Ω U) x
    have e2 := restrictAb_apply K⟮ξ⟯
      (hle.trans maximalUnramifiedExtension_le_maximalAbelianExtension) (localArtinMap K Ω U)
      ⟨x, hML x.2⟩
    rw [h1] at e2
    exact e1.trans e2.symm
  have h3 : U ∈ (normUnits K M).range := by
    rw [← ker_restrictAb_localArtinMap M, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact h2
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, by simpa using congrArg Units.val hy⟩

end GlobalTheory.CompanionTheory.LocalField
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueFieldCardEqNorm
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.LocRes

theorem natCard_residueField_eq_normV : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)), Nat.card 𝓀[v.adicCompletion F] = normV v := by
  intro F _ _ v
  rw [GroundTheory.Global.natCard_residueField_adicCompletion v, Ideal.absNorm_apply,
    Submodule.cardQuot_apply]
  rfl

end GlobalTheory.CompanionTheory.LocRes
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerRatioValuationZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.Uniformiser

theorem valued_eq_exp_neg_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (h1 : a ∈ v.asIdeal) (h2 : a ∉ v.asIdeal ^ 2) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-1 : ℤ) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  rw [show algebraMap F (v.adicCompletion F) (a : F) = ((a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : v.intValuation a ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem v a 1).2 (by simpa using h1)
  have hnle2 : ¬ v.intValuation a ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem v a 2).1 h)
  have hne : v.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v a ha0
  rw [← WithZero.exp_log hne] at hle1 hnle2 ⊢
  rw [WithZero.exp_le_exp] at hle1 hnle2
  congr 1
  omega

theorem ord_eq_zero_of_valued_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    GroundTheory.LocalField.ord x = 0 := by
  have heq : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsEquiv
      (ValuativeRel.valuation (v.adicCompletion F)) := ValuativeRel.isEquiv _ _
  have h1 : ValuativeRel.valuation (v.adicCompletion F) x = 1 := heq.eq_one_iff_eq_one.1 hx
  unfold GroundTheory.LocalField.ord
  rw [GroundTheory.LocalField.normalizedValuation_apply, h1, map_one, WithZero.log_one, neg_zero]

theorem ord_ratio_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 →
    ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) →
    GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  intro F _ _ v ϖ ϖ' h1 h2 h1' h2' U hU
  apply ord_eq_zero_of_valued_eq_one v
  have e1 := valued_eq_exp_neg_one v ϖ h1 h2
  have e2 := valued_eq_exp_neg_one v ϖ' h1' h2'
  have h := congrArg Valued.v hU
  rw [map_mul, e1, e2] at h
  exact mul_right_cancel₀ WithZero.exp_ne_zero (h.trans (one_mul _).symm)

end GlobalTheory.CompanionTheory.Uniformiser
end

