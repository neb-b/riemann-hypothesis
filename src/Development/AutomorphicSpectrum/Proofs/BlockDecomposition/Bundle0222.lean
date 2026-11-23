module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0198
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0215
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0216
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0212

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorPairingAdjoint
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.WordAdj

open GlobalTheory.CompanionTheory.WaveK.Sym (integrable_inner cpt_inner_left)
open GlobalTheory.CompanionTheory.WaveSpd (val_mem_GLs)

section Ops

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (X : Mat n) : ∀ y ∈ GLs n, R < lg y → Rd X u y = 0 := by
  intro y hy hR
  unfold LgFacts at hL
  have hc : ContinuousOn lg (GLs n) := (hL n).2.2.2.1.continuousOn
  have ho : IsOpen (GLs n) := by
    unfold GLs
    exact isOpen_ne_fun (by fun_prop) continuous_const
  have hU : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) := hc.isOpen_inter_preimage ho isOpen_Ioi
  have hev : u =ᶠ[nhds y] fun _ => 0 :=
    Filter.eventually_of_mem (hU.mem_nhds ⟨hy, hR⟩) fun z hz => hu z hz.1 hz.2
  unfold Rd
  rw [hev.fderiv_eq]
  simp

theorem Eu_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (a b : Fin n) : ∀ y ∈ GLs n, R < lg y → Eu s a b u y = 0 := by
  intro y hy hR
  have h1 := Rd_van hL hu (single a b 1) y hy hR
  have h2 := Rd_van hL hu (single a b Complex.I) y hy hR
  unfold Eu
  cases s <;> simp [h1, h2]

theorem Epow_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (m : ℕ) (a b : Fin n) : ∀ y ∈ GLs n, R < lg y → Epow s m a b u y = 0 := by
  induction m generalizing a b with
  | zero =>
    intro y hy hR
    by_cases hab : a = b
    · simp [Epow, hab, hu y hy hR]
    · simp [Epow, hab]
  | succ m ih =>
    intro y hy hR
    simp only [Epow, Finset.sum_apply]
    exact Finset.sum_eq_zero fun c _ => Eu_van hL (ih c b) s a c y hy hR

theorem gel_van (hL : LgFacts) {u : Mat n → V} {R : ℝ} (hu : ∀ y ∈ GLs n, R < lg y → u y = 0)
    (s : Bool) (m : ℕ) : ∀ y ∈ GLs n, R < lg y → gel s m u y = 0 := by
  intro y hy hR
  unfold gel
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun a _ => Epow_van hL hu s m a a y hy hR

theorem cpt_zOp (hL : LgFacts) (w : List (Bool × ℕ)) {u : Mat n → V} (hu : Cpt u) :
    Cpt (zOp w u) := by
  unfold Cpt at hu ⊢
  obtain ⟨R, hR⟩ := hu
  refine ⟨R, ?_⟩
  induction w with
  | nil => exact hR
  | cons p w ih => exact gel_van hL ih p.1 p.2

theorem zOp_contDiffOn (w : List (Bool × ℕ)) {u : Mat n → V} (hu : ContDiffOn ℝ ∞ u (GLs n)) :
    ContDiffOn ℝ ∞ (zOp w u) (GLs n) := by
  induction w with
  | nil => exact hu
  | cons p w ih => exact GlobalTheory.CompanionTheory.RCalc.gel_contDiffOn p.1 p.2 ih

theorem zOp_append (w w' : List (Bool × ℕ)) (u : Mat n → V) :
    zOp (w ++ w') u = zOp w (zOp w' u) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    show gel p.1 p.2 (zOp (w ++ w') u) = gel p.1 p.2 (zOp w (zOp w' u))
    rw [ih]

end Ops

private theorem isHecke_div_and_resEtaPow_div (n : ℕ) (s : Bool) (m : ℕ) : ∃ (M : ℕ) (e : Fin M → ℂ) (v : Fin M → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal [(s, m)] χ) = ∑ j, e j * zVal (v j) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪gel s m f y.val, h y.val⟫_ℂ ∂μ = ∑ j, e j * ∫ y : G n, ⟪f y.val, zOp (v j) h y.val⟫_ℂ ∂μ) := by
  obtain ⟨M, d, w, hv, ho⟩ := _root_.GlobalTheory.CompanionTheory.WaveMult.GenTr.transposed_invariants n m
  refine ⟨M, fun j => (-1) ^ m * d j, fun j => (w j).map (fun k => (!s, k)), ?_, ?_⟩
  · intro χ hχ
    have h1 : zVal [(s, m)] χ = GlobalTheory.Dec.gelfVal (χ s) m := by simp [zVal]
    rw [h1, conj_gelfVal_of_isHerm n χ hχ s m]
    have h3 : ∀ j, zVal ((w j).map (fun k => (!s, k))) χ = ((w j).map (GlobalTheory.Dec.gelfVal (χ (!s)))).prod := by
      intro j
      simp [zVal, List.map_map, Function.comp_def]
    rw [Finset.sum_congr rfl (fun j _ => by rw [h3 j, mul_assoc]), ← Finset.mul_sum, ← hv (χ (!s)), ← mul_assoc, ← mul_pow]
    simp
  · intro hL hR _ _ μ _ V _ _ _ f h hf hh cf ch
    rw [_root_.GlobalTheory.CompanionTheory.WaveMult.Ibp.ibp_gel hL hR n μ V s m f h hf hh cf ch]
    have hpt : ∀ y : G n, ⟪f y.val, GlobalTheory.CompanionTheory.WaveMult.gelT (!s) m h y.val⟫_ℂ = ∑ j, d j * ⟪f y.val, zOp ((w j).map (fun k => (!s, k))) h y.val⟫_ℂ := by
      intro y
      rw [ho hR (!s) h hh y.val (val_mem_GLs y), inner_sum]
      simp only [inner_smul_right]
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun j _ => (integrable_inner μ hL hf (zOp_contDiffOn _ hh) (cpt_inner_left cf)).const_mul (d j)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    ring

private theorem isPair_and_isPair_of_isTriple {M N : ℕ} (F : Fin M → Fin N → ℂ) : ∑ k : Fin (M * N), F (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 = ∑ j, ∑ i, F j i :=
  (Equiv.sum_comp finProdFinEquiv.symm (fun q => F q.1 q.2)).trans (Fintype.sum_prod_type _)

theorem word_adjoint : ∀ (n : ℕ) (w : List (Bool × ℕ)), ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)), (∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ) ∧ (LgFacts → RCalc → ∀ [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (f h : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → ContDiffOn ℝ ∞ h (GLs n) → Cpt f → Cpt h → ∫ y : G n, ⟪zOp w f y.val, h y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i) h y.val⟫_ℂ ∂μ) := by
  intro n w
  induction w with
  | nil =>
    refine ⟨1, fun _ => 1, fun _ => [], ?_, ?_⟩
    · intro χ _
      simp [zVal]
    · intro _ _ _ _ μ _ V _ _ _ f h _ _ _ _
      simp [zOp]
  | cons p w ih =>
    obtain ⟨s, m⟩ := p
    obtain ⟨N, c, w₁, hz, hi⟩ := ih
    obtain ⟨M, e, v, hz1, hi1⟩ := isHecke_div_and_resEtaPow_div n s m
    refine ⟨M * N, fun k => e (finProdFinEquiv.symm k).1 * c (finProdFinEquiv.symm k).2,
      fun k => w₁ (finProdFinEquiv.symm k).2 ++ v (finProdFinEquiv.symm k).1, ?_, ?_⟩
    · intro χ hχ
      have hs := isPair_and_isPair_of_isTriple (fun j i => e j * c i * zVal (w₁ i ++ v j) χ)
      beta_reduce at hs
      rw [hs]
      have h1 : zVal ((s, m) :: w) χ = zVal [(s, m)] χ * zVal w χ := zVal_append [(s, m)] w χ
      rw [h1, map_mul, hz1 χ hχ, hz χ hχ, Finset.sum_mul_sum]
      simp only [zVal_append]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    · intro hL hR _ _ μ _ V _ _ _ f h hf hh cf ch
      have hs := isPair_and_isPair_of_isTriple (fun j i => e j * c i * ∫ y : G n, ⟪f y.val, zOp (w₁ i ++ v j) h y.val⟫_ℂ ∂μ)
      beta_reduce at hs
      rw [hs]
      have hwf := zOp_contDiffOn w hf
      have cwf := cpt_zOp hL w cf
      have step1 : ∫ y : G n, ⟪zOp ((s, m) :: w) f y.val, h y.val⟫_ℂ ∂μ =
          ∑ j, e j * ∫ y : G n, ⟪zOp w f y.val, zOp (v j) h y.val⟫_ℂ ∂μ :=
        hi1 hL hR μ V (zOp w f) h hwf hh cwf ch
      rw [step1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hi hL hR μ V f (zOp (v j) h) hf (zOp_contDiffOn _ hh) cf (cpt_zOp hL _ ch), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zOp_append]
      ring

end GlobalTheory.CompanionTheory.WaveMult.WordAdj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckePowerCosetFormula
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct GlobalTheory.CompanionTheory.SatPow

noncomputable section

namespace GlobalTheory.CompanionTheory.SatPow.HeckeTrace

variable {G : Type} [Group G]

theorem aOp_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) : ∀ g, ∀ i ∈ I, aOp R t φ (g * i) = aOp R t φ g :=
  _root_.UpperTheory.Reformulated.B.Qf37.aOp_rightInvariant hR hu hφ

theorem aOp_iterate_rightInvariant {I : Subgroup G} {t : G} {R : Finset G} (hR : ∀ r ∈ R, r ∈ I)
    (hu : ∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) {φ : G → ℂ}
    (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g) (j : ℕ) :
    ∀ g, ∀ i ∈ I, (aOp R t)^[j] φ (g * i) = (aOp R t)^[j] φ g := by
  induction j with
  | zero => simpa using hφ
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact aOp_rightInvariant hR hu ih

theorem exists_words (K : Subgroup G) (t : G) (R : Finset G) (h1 : (1 : G) ∈ R)
    (hc : ∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) (j : ℕ) :
    ∃ W : Multiset G, W ≠ 0 ∧ (∀ w ∈ W, ∃ k ∈ K, w = k * t ^ j) ∧
      ∀ (ψ : G → ℂ) (g : G), (aOp R t)^[j] ψ g = (W.map fun w => ψ (g * w)).sum := by
  induction j with
  | zero =>
    refine ⟨{1}, by simp, ?_, fun ψ g => by simp⟩
    intro w hw
    exact ⟨1, one_mem K, by simpa using hw⟩
  | succ j ih =>
    obtain ⟨W, hW0, hWK, hWf⟩ := ih
    refine ⟨W.bind fun w => R.val.map fun r => w * r * t, ?_, ?_, ?_⟩
    · obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
      intro h0
      have hm : w * 1 * t ∈ W.bind fun w => R.val.map fun r => w * r * t :=
        Multiset.mem_bind.2 ⟨w, hw, Multiset.mem_map.2 ⟨1, h1, rfl⟩⟩
      rw [h0] at hm
      exact Multiset.notMem_zero _ hm
    · intro x hx
      obtain ⟨w, hw, hx⟩ := Multiset.mem_bind.1 hx
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hx
      obtain ⟨k, hk, rfl⟩ := hWK w hw
      refine ⟨k * (t ^ j * r * (t ^ j)⁻¹), mul_mem hk (hc r hr j), ?_⟩
      rw [pow_succ]
      group
    · intro ψ g
      rw [Function.iterate_succ_apply, hWf, Multiset.map_bind, Multiset.sum_bind]
      congr 1
      refine Multiset.map_congr rfl fun w _ => ?_
      rw [Multiset.map_map]
      show ∑ r ∈ R, ψ (g * w * r * t) = _
      simp only [Function.comp, mul_assoc]
      rfl

theorem finsum_left_mul {K I : Subgroup G} (hIK : I ≤ K) {φ : G → ℂ} (hφ : ∀ g, ∀ i ∈ I, φ (g * i) = φ g)
    {k : G} (hk : k ∈ K) :
    ∑ᶠ c : K ⧸ I.subgroupOf K, φ (k * ((c.out : K) : G)) = ∑ᶠ c : K ⧸ I.subgroupOf K, φ ((c.out : K) : G) := by
  let kk : K := ⟨k, hk⟩
  rw [← finsum_comp_equiv (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K))
    (f := fun c : K ⧸ I.subgroupOf K => φ ((c.out : K) : G))]
  refine finsum_congr fun c => ?_
  have e : (MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c = ((kk * c.out : K) : K ⧸ I.subgroupOf K) := by
    show kk • c = _
    conv_lhs => rw [← QuotientGroup.out_eq' c]
    rfl
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (I.subgroupOf K) (kk * c.out)
  have hi : ((h : K) : G) ∈ I := Subgroup.mem_subgroupOf.1 h.2
  show _ = φ ((((MulAction.toPerm kk : Equiv.Perm (K ⧸ I.subgroupOf K)) c).out : K) : G)
  rw [e, hh]
  show _ = φ (k * ((c.out : K) : G) * ((h : K) : G))
  rw [hφ _ _ hi]

theorem multiset_sum_eq_hAct (K : Subgroup G) (s : G) (M : Multiset G) (hM0 : M ≠ 0)
    (hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G))
    (hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum) :
    ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = (m : ℂ) * hAct K (dosetInd ℂ K s) ψ 1 := by
  classical
  set M' : Multiset (G ⧸ K) := M.map (QuotientGroup.mk : G → G ⧸ K) with hM'
  have hout : ∀ (ψ : G → ℂ), (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ x : G,
      ψ ((x : G ⧸ K).out) = ψ x := by
    intro ψ hψ x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
    rw [hh, hψ _ _ h.2]
  have key1 : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) →
      (M.map ψ).sum = ∑ y ∈ M'.toFinset, (M'.count y : ℂ) * ψ y.out := by
    intro ψ hψ
    have e : M.map ψ = M'.map fun y : G ⧸ K => ψ y.out := by
      rw [hM', Multiset.map_map]
      exact Multiset.map_congr rfl fun x _ => (hout ψ hψ x).symm
    rw [e, Finset.sum_multiset_map_count]
    simp only [nsmul_eq_mul]
  let e : G ⧸ K → G → ℂ := fun y x => if (x : G ⧸ K) = y then 1 else 0
  have he : ∀ y g, ∀ k ∈ K, e y (g * k) = e y g := by
    intro y g k hk
    have : ((g * k : G) : G ⧸ K) = g := by
      rw [QuotientGroup.eq]
      simpa using inv_mem hk
    simp only [e, this]
  have key2 : ∀ y, (M.map (e y)).sum = (M'.count y : ℂ) := by
    intro y
    rw [key1 _ (he y)]
    have : ∀ z : G ⧸ K, (M'.count z : ℂ) * e y z.out = if z = y then (M'.count z : ℂ) else 0 := by
      intro z
      simp only [e, QuotientGroup.out_eq']
      split_ifs <;> simp
    simp only [this]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · have : M'.count y = 0 := Multiset.count_eq_zero.2 (by simpa using h)
      simp [this]
  have key3 : ∀ k ∈ K, ∀ g : G, M'.count ((k * g : G) : G ⧸ K) = M'.count (g : G ⧸ K) := by
    intro k hk g
    have h1 := hinv (e ((k * g : G) : G ⧸ K)) (he _) k hk
    have h2 : (fun x => e ((k * g : G) : G ⧸ K) (k * x)) = e (g : G ⧸ K) := by
      funext x
      have : ((k * x : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) ↔ (x : G ⧸ K) = (g : G ⧸ K) := by
        rw [QuotientGroup.eq, QuotientGroup.eq]
        have : (k * x)⁻¹ * (k * g) = x⁻¹ * g := by group
        rw [this]
      simp only [e, this]
    rw [h2, key2, key2] at h1
    exact_mod_cast h1.symm
  obtain ⟨x0, hx0⟩ := Multiset.exists_mem_of_ne_zero hM0
  have hconst : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
      M'.count (g : G ⧸ K) = M'.count (x0 : G ⧸ K) := by
    have hred : ∀ g ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G),
        M'.count (g : G ⧸ K) = M'.count (s : G ⧸ K) := by
      intro g hg
      obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      have : ((a * s * b : G) : G ⧸ K) = ((a * s : G) : G ⧸ K) := by
        rw [QuotientGroup.eq]
        simpa [mul_assoc] using inv_mem hb
      rw [this, key3 a ha]
    intro g hg
    rw [hred g hg, hred x0 (hMs x0 hx0)]
  have hpos : 0 < M'.count (x0 : G ⧸ K) :=
    Multiset.count_pos.2 (Multiset.mem_map_of_mem _ hx0)
  refine ⟨M'.count (x0 : G ⧸ K), hpos, fun ψ hψ => ?_⟩
  have hmem : ∀ y : G ⧸ K, y ∈ M'.toFinset ↔ y.out ∈ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 hy)
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul K x
      obtain ⟨a, ha, b, hb, e1⟩ := DoubleCoset.mem_doubleCoset.1 (hMs x hx)
      refine DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b * h, mul_mem hb h.2, ?_⟩
      rw [hh, e1]
      group
    · intro hy
      have h := hconst _ hy
      rw [QuotientGroup.out_eq'] at h
      refine Multiset.mem_toFinset.2 (Multiset.count_pos.1 ?_)
      rw [h]
      exact hpos
  have hact : hAct K (dosetInd ℂ K s) ψ 1 = ∑ y ∈ M'.toFinset, ψ y.out := by
    unfold hAct
    rw [finsum_eq_sum_of_support_subset (s := M'.toFinset)]
    · refine Finset.sum_congr rfl fun y hy => ?_
      have h := (hmem y).1 hy
      simp [dosetInd, Set.indicator_of_mem h]
    · intro y hy
      by_contra hn
      have h : y.out ∉ DoubleCoset.doubleCoset s (K : Set G) (K : Set G) := fun h => hn ((hmem y).2 h)
      apply hy
      simp [dosetInd, Set.indicator_of_notMem h]
  rw [hact, key1 ψ hψ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hconst _ ((hmem y).1 hy)
  rw [QuotientGroup.out_eq'] at h
  rw [h]

theorem heckeTrace : ∀ (G : Type) [Group G] (K I : Subgroup G), I ≤ K → Finite (K ⧸ I.subgroupOf K) → ∀ (t : G) (R : Finset G), (1 : G) ∈ R → (∀ r ∈ R, r ∈ I) → (∀ r ∈ R, ∀ k : ℕ, t ^ k * r * (t ^ k)⁻¹ ∈ K) → (∀ i ∈ I, ∃! r, r ∈ R ∧ t⁻¹ * (r⁻¹ * i) * t ∈ I) → ∀ j : ℕ, ∃ m : ℕ, 0 < m ∧ ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (m : ℂ) * hAct K (dosetInd ℂ K (t ^ j)) ψ 1 := by
  intro G _ K I hIK hfin t R h1 hR hc hu j
  classical
  haveI := Fintype.ofFinite (K ⧸ I.subgroupOf K)
  obtain ⟨W, hW0, hWK, hWf⟩ := exists_words K t R h1 hc j
  set M : Multiset G := (Finset.univ : Finset (K ⧸ I.subgroupOf K)).val.bind
    fun c => W.map fun w => ((c.out : K) : G) * w with hMdef
  have hM : ∀ φ : G → ℂ, (M.map φ).sum =
      ∑ c : K ⧸ I.subgroupOf K, (W.map fun w => φ (((c.out : K) : G) * w)).sum := by
    intro φ
    rw [hMdef, Multiset.map_bind, Multiset.sum_bind]
    simp only [Multiset.map_map, Function.comp_def]
    rfl
  have hL : ∀ ψ : G → ℂ, ∑ᶠ c : K ⧸ I.subgroupOf K, ((aOp R t)^[j] ψ) ((c.out : K) : G) = (M.map ψ).sum := by
    intro ψ
    rw [finsum_eq_sum_of_fintype, hM]
    exact Finset.sum_congr rfl fun c _ => hWf ψ _
  have hIinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ g, ∀ i ∈ I, ψ (g * i) = ψ g :=
    fun ψ hψ g i hi => hψ g i (hIK hi)
  have hinv : ∀ ψ : G → ℂ, (∀ g, ∀ k ∈ K, ψ (g * k) = ψ g) → ∀ k ∈ K,
      (M.map fun x => ψ (k * x)).sum = (M.map ψ).sum := by
    intro ψ hψ k hk
    rw [← hL ψ, ← finsum_left_mul hIK (aOp_iterate_rightInvariant hR hu (hIinv ψ hψ) j) hk,
      finsum_eq_sum_of_fintype, hM]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hWf ψ]
    simp only [mul_assoc]
  have hMs : ∀ x ∈ M, x ∈ DoubleCoset.doubleCoset (t ^ j) (K : Set G) (K : Set G) := by
    intro x hx
    obtain ⟨c, -, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨k, hk, rfl⟩ := hWK w hw
    exact DoubleCoset.mem_doubleCoset.2
      ⟨((c.out : K) : G) * k, mul_mem (c.out : K).2 hk, 1, one_mem K, by simp [mul_assoc]⟩
  have hM0 : M ≠ 0 := by
    obtain ⟨w, hw⟩ := Multiset.exists_mem_of_ne_zero hW0
    let c0 : K ⧸ I.subgroupOf K := ((1 : K) : K ⧸ I.subgroupOf K)
    intro h0
    have hm : ((c0.out : K) : G) * w ∈ M :=
      Multiset.mem_bind.2 ⟨c0, Finset.mem_univ c0, Multiset.mem_map.2 ⟨w, hw, rfl⟩⟩
    rw [h0] at hm
    exact Multiset.notMem_zero _ hm
  obtain ⟨m, hm, hmf⟩ := multiset_sum_eq_hAct K (t ^ j) M hM0 hMs hinv
  exact ⟨m, hm, fun ψ hψ => by rw [hL, hmf ψ hψ]⟩

end GlobalTheory.CompanionTheory.SatPow.HeckeTrace

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftConvolutionApproximation
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem norm_lConv_sub_le : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ φ : Mat n → ℝ, IsTest φ → (∀ y, 0 ≤ φ y) → (∫ y : G n, φ y.val ∂μ = 1) → ∀ (x : Lp V 2 μ) (ε : ℝ), (∀ y : G n, φ y.val ≠ 0 → ‖lT μ V y x - x‖ ≤ ε) → ‖lConv μ V φ x - x‖ ≤ ε := by
  intro n _ _ μ _ V _ _ _ hU φ hφ hpos h1 x ε hε
  have hemb := GlobalTheory.CompanionTheory.SobGL.HaarDom.isOpenEmbedding_valG n
  have hφc : Continuous fun y : G n => φ y.val := hφ.1.continuous.comp hemb.continuous
  have hK : IsCompact ((Units.val : G n → Mat n) ⁻¹' tsupport φ) := by
    refine (hemb.isInducing.isCompact_preimage_iff ?_).2 hφ.2.1
    intro z hz
    have hdet : z.det ≠ 0 := hφ.2.2 hz
    obtain ⟨u, rfl⟩ := (Matrix.isUnit_iff_isUnit_det z).2 (isUnit_iff_ne_zero.2 hdet)
    exact ⟨u, rfl⟩
  have hcs : HasCompactSupport (fun y : G n => φ y.val) :=
    HasCompactSupport.of_support_subset_isCompact hK (fun y hy => subset_tsupport φ hy)
  have hL := (translations_strongly_continuous n μ V hU x).2
  have hint1 : Integrable (fun y : G n => φ y.val) μ := hφc.integrable_of_hasCompactSupport hcs
  have hf : Integrable (fun y : G n => φ y.val • lT μ V y x) μ :=
    (hφc.smul hL).integrable_of_hasCompactSupport hcs.smul_right
  have hg : Integrable (fun y : G n => φ y.val • x) μ := hint1.smul_const x
  have e : lConv μ V φ x - x = ∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ := by
    simp_rw [smul_sub]
    rw [integral_sub hf hg, integral_smul_const, h1, one_smul]
    rfl
  rw [e]
  calc ‖∫ y : G n, φ y.val • (lT μ V y x - x) ∂μ‖ ≤ ∫ y : G n, φ y.val * ε ∂μ := by
        refine norm_integral_le_of_norm_le (hint1.mul_const ε) (ae_of_all _ fun y => ?_)
        by_cases h0 : φ y.val = 0
        · simp [h0]
        · rw [norm_smul, Real.norm_of_nonneg (hpos _)]
          exact mul_le_mul_of_nonneg_left (hε y h0) (hpos _)
    _ = ε := by rw [integral_mul_const, h1, one_mul]

end GlobalTheory.CompanionTheory.PresSobA
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGaloisEmbeddingExtensionStatement
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_galois_embedding_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 →
    ∀ (j : {j : w.adicCompletion E →+* Qbar l // Continuous j}),
    ∃ (φ : w.adicCompletion E →+* Om l) (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), Continuous φ ∧
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) ∧
      (∀ x, ∃ hx : φ x ∈ Bw.Kw.1, ((τ ⟨φ x, hx⟩ : ↥LL'.1) : Om l) = j.1 x) ∧
      ∀ τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1,
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' ↔ τ' = τ := by
  first | exact @GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | exact GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous | (intros; apply GlobalTheory.CompanionTheory.EmbBridge.embeddings_of_continuous <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollificationRightTranslateStatement
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mollification_right_translate : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V], Unimod → ∀ (φ : Mat n → ℝ) (h : G n) (x : Lp V 2 μ) (z : Mat n), Mol μ φ (⇑(rR μ V h x)) z = Mol μ φ (⇑x) (z * h.val) := by
  first | exact @GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | exact GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq | (intros; apply GlobalTheory.CompanionTheory.PresSobA.Mol_rR_eq <;> assumption)
end
end

