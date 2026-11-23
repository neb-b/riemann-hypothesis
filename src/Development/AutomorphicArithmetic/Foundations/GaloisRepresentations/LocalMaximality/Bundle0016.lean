module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0452

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RatioMemRB
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma omB_smul_mem {K : Type} [Field K] [Algebra ℂ K] (B : Subalgebra ℂ K) (q : ℕ) {b : K} (hb : b ∈ B)
    {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) : b • y ∈ omB ℂ K B q := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b', hb', v, hv, rfl⟩ := hz
    apply Submodule.subset_span
    exact ⟨b * b', B.mul_mem hb hb', v, hv, by rw [smul_smul]⟩
  | zero => simp
  | add u w _ _ hu hw =>
    rw [smul_add]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [smul_comm]
    exact Submodule.smul_mem _ c hu

private lemma ratio_mem_rB {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K]
    [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (i j : Fin (d + 1)) :
    algebraMap F K (x j / x i) ∈ rB ℂ K x {i} := by
  rw [rB, Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  have h : x j / x i ∈ rA ℂ x {i} := Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
  exact isIntegral_algebraMap (x := (⟨x j / x i, h⟩ : rA ℂ x {i}))

private lemma omG_ratio {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) (N : ℕ) :
    ((x j : F) / x i) ^ (N + d + 1) * ((x i : F) / x j) ^ N * omG x j = omG x i := by
  have hi : (x i : F) ≠ 0 := (x i).ne_zero
  have hj : (x j : F) ≠ 0 := (x j).ne_zero
  have h : omG x j = omG x i * ((x i : F) / x j) ^ (d + 1) := by
    simp only [omG]
    rw [show ((x i : F) / x j) ^ (d + 1) = ∏ _l : Fin (d + 1), ((x i : F) / x j) by simp [div_pow],
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun l _ => ?_
    field_simp
  rw [h, ← inv_div (x j : F) (x i : F)]
  have ha : (x j : F) / x i ≠ 0 := div_ne_zero hj hi
  generalize (x j : F) / x i = a at ha ⊢
  rw [inv_pow, inv_pow]
  field_simp
  ring

private lemma pair_prod {F : Type} [Field F] {d : ℕ} (x : Fin (d + 1) → Fˣ) (i j : Fin (d + 1)) :
    (∏ l ∈ ({i, j} : Finset (Fin (d + 1))), (x l : F) / x i) = (x j : F) / x i := by
  by_cases h : i = j
  · subst h
    simp
  · rw [Finset.prod_pair h, div_self (x i).ne_zero, one_mul]

private theorem key_lemma' {K : Type} [Field K] [Algebra ℂ K] (s t : K) (y z : DR ℂ K) :
    actZ K (s ⊗ₜ[ℂ] t) (y ⊗ₜ[ℂ] z) = (s • y) ⊗ₜ[ℂ] (t • z) := by
  simp [actZ, Module.endTensorEndAlgHom, Module.endTensorEndAlgHom_apply]

private lemma key {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]
    {d : ℕ} (x : Fin (d + 1) → Fˣ) (hc : IsFinCover ℂ K (xv x))
    (hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q) (a : ℕ) (i j : Fin (d + 1))
    (m : DR ℂ K ⊗[ℂ] DR ℂ K) (hm : m ∈ MZ F K (xv x) a {j} {j}) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
      (algebraMap F K ((x i : F) / x j) ^ N)) m ∈ MZ F K (xv x) a {i} {j} := by
  have hu : algebraMap F K ((x j : F) / x i) ∈ rB ℂ K (xv x) {i} := ratio_mem_rB K (xv x) i j
  have hv : algebraMap F K ((x i : F) / x j) ∈ rB ℂ K (xv x) {j} := ratio_mem_rB K (xv x) j i
  have gen : ∀ y ∈ omB ℂ K (rB ℂ K (xv x) {j}) (d - a), ∀ z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a,
      ∃ N0 : ℕ, ∀ N, N0 ≤ N → actZ K ((algebraMap F K ((x j : F) / x i) ^ (N + d + 1)) ⊗ₜ[ℂ]
        (algebraMap F K ((x i : F) / x j) ^ N)) (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y z) ∈
          MZ F K (xv x) a {i} {j} := by
    intro y hy z hz
    have hy' : y ∈ omB ℂ K (rB ℂ K (xv x) {i, j}) (d - a) :=
      hmono (d - a) {j} {i, j} (Finset.singleton_nonempty j)
        (Finset.singleton_subset_iff.mpr (by simp)) hy
    obtain ⟨N1, hN1⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc {i, j} i (by simp) (d - a) y).mp hy'
    have hN1' : algebraMap F K ((x j : F) / x i) ^ N1 • y ∈ omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      rw [← pair_prod x i j]
      exact hN1
    refine ⟨N1, fun N hN => ?_⟩
    rw [TensorProduct.mk_apply, key_lemma']
    have h1 : algebraMap F K ((x j : F) / x i) ^ (N + d + 1) • y ∈
        omB ℂ K (rB ℂ K (xv x) {i}) (d - a) := by
      have e : N + d + 1 = (N + d + 1 - N1) + N1 := by omega
      rw [e, pow_add, ← smul_smul]
      exact omB_smul_mem _ _ (pow_mem hu _) hN1'
    have h2 : algebraMap F K ((x i : F) / x j) ^ N • z ∈ omB ℂ K (rB ℂ K (xv x) {j}) a :=
      omB_smul_mem _ _ (pow_mem hv _) hz
    exact Submodule.apply_mem_map₂ _ h1 h2
  unfold MZ at hm
  rw [Submodule.map₂_eq_span_image2] at hm
  induction hm using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, z, hz, rfl⟩ := hw
    exact gen y hy z hz
  | zero => exact ⟨0, fun N _ => by simp⟩
  | add w w' _ _ h1 h2 =>
    obtain ⟨N1, h1⟩ := h1
    obtain ⟨N2, h2⟩ := h2
    exact ⟨max N1 N2, fun N hN => by
      rw [map_add (f := _)]
      exact Submodule.add_mem _ (h1 N (le_of_max_le_left hN)) (h2 N (le_of_max_le_right hN))⟩
  | smul c w _ h =>
    obtain ⟨N1, h⟩ := h
    exact ⟨N1, fun N hN => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (h N hN)⟩

theorem UpperTheory.Gal.productCup_of_system.idIJ_of :
    IdJ → ActsLin → GoodZ → IdIJ := by
  intro hJ hL hG F K _ _ _ _ _ _ d x hc τ hτ a ha i j
  obtain ⟨m, hm, hact⟩ := hJ F K d x hc τ hτ a ha j
  have hmono : ∀ (q : ℕ) (s t : Finset (Fin (d + 1))), s.Nonempty → s ⊆ t →
      omB ℂ K (rB ℂ K (xv x) s) q ≤ omB ℂ K (rB ℂ K (xv x) t) q :=
    fun q => (hG F K d x hc q).2.2
  obtain ⟨N0, hN0⟩ := key x hc hmono a i j m hm
  refine ⟨_, hN0 N0 le_rfl, ?_⟩
  have h2 := (hL F K d x hc τ hτ a).2.1 m _
    ((algebraMap F K ((x j : F) / x i) ^ (N0 + d + 1)) ⊗ₜ[ℂ] (algebraMap F K ((x i : F) / x j) ^ N0)) hact
  rw [Algebra.TensorProduct.lmul'_apply_tmul, ← map_pow, ← map_pow, ← map_mul, ← map_mul,
    omG_ratio] at h2
  simpa only [map_pow] using h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.SmRangeCongr
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private theorem sm_image_congr {S S' E ι : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (act' : S' →ₐ[ℂ] Module.End ℂ E)
    (M : Submodule ℂ E) (f : ι → S) (g : ι → S') (h : ∀ k, act (f k) = act' (g k)) (A : Set ι) :
    sm act M (f '' A) = sm act' M (g '' A) := by
  simp only [sm, iSup_image, h]

private theorem sm_range_congr {S S' E ι : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (act' : S' →ₐ[ℂ] Module.End ℂ E)
    (M : Submodule ℂ E) (f : ι → S) (g : ι → S') (h : ∀ k, act (f k) = act' (g k)) :
    sm act M (Set.range f) = sm act' M (Set.range g) := by
  rw [← Set.image_univ, ← Set.image_univ]
  exact sm_image_congr act act' M f g h _

private theorem reg_congr {S S' E : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [AddCommGroup E] [Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E) (act' : S' →ₐ[ℂ] Module.End ℂ E)
    (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) (g : Fin d → S') (h : ∀ k, act (f k) = act' (g k))
    (hr : Reg act M f) : Reg act' M g := by
  intro k m hm hk
  rw [← sm_image_congr act act' M f g h, ← h k] at hk
  rw [← sm_image_congr act act' M f g h]
  exact hr k m hm hk

section SysLem
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)

private theorem r_eq (i j : Fin (d + 1)) (l : Fin d) :
    T.r n11 T.mu i j (dj j l) = ((T.X (j.succAbove l) * (T.X i)⁻¹ : Sˣ) : S)
      - ((T.X j * (T.X i)⁻¹ : Sˣ) : S) * ((T.Y (j.succAbove l) * (T.Y j)⁻¹ : Sˣ) : S) := by
  have hY : (T.Y j : S) * ((T.Y j)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  have hd : T.mu (dj j l) = (T.X (j.succAbove l) : S) * T.Y j - T.X j * T.Y (j.succAbove l) := rfl
  simp only [Sys.r, Sys.u, n11, hd, pow_one, mul_inv, Units.val_mul]
  linear_combination ((T.X (j.succAbove l) : S) * ((T.X i)⁻¹ : Sˣ)) * hY

private theorem r_mul (i j : Fin (d + 1)) (l : Fin d) :
    T.r n11 T.mu i j (dj j l) * ((T.X i * (T.X j)⁻¹ : Sˣ) : S) = T.r n11 T.mu j j (dj j l) := by
  have hX : (T.X i : S) * ((T.X i)⁻¹ : Sˣ) = 1 := Units.mul_inv _
  simp only [Sys.r, Sys.u, n11, pow_one, mul_inv, Units.val_mul]
  linear_combination (T.mu (dj j l) * ((T.Y j)⁻¹ : Sˣ) * ((T.X j)⁻¹ : Sˣ)) * hX

private theorem r_mem (hG : T.Good) {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
    (l : Fin d) : T.r n11 T.mu i j (dj j l) ∈ T.R I J := by
  rw [r_eq]
  exact sub_mem (hG.memX I J ⟨j, hj⟩ i hi _)
    (mul_mem (hG.memX I J ⟨j, hj⟩ i hi _) (hG.memY I J ⟨i, hi⟩ j hj _))

end SysLem

section Forms
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private theorem omB_le_fixed (B : Subalgebra ℂ K) (q : ℕ) {y : DR ℂ K} (hy : y ∈ omB ℂ K B q) :
    y ∈ ⋀[K]^q Ω[K⁄ℂ] := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, -, v, -, rfl⟩ := hz
    exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range K q ⟨_, rfl⟩)
  | zero => exact Submodule.zero_mem _
  | add a c _ _ ha hc => exact Submodule.add_mem _ ha hc
  | smul r a _ ha =>
    rw [← algebraMap_smul K r a]
    exact Submodule.smul_mem _ _ ha

private theorem actZ_tmul (u v : K) (y y' : DR ℂ K) :
    actZ K (u ⊗ₜ v) (y ⊗ₜ y') = (u • y) ⊗ₜ[ℂ] (v • y') := by
  simp only [actZ, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
  rfl

private theorem actF_tmul (u v : F) (y y' : DR ℂ K) :
    actF F (DR ℂ K) (DR ℂ K) (u ⊗ₜ v) (y ⊗ₜ y') = (u • y) ⊗ₜ[ℂ] (v • y') := by
  simp only [actF, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
  rfl

private theorem ctrF_eq (τ : DR ℂ K →ₗ[K] K) (ψ : DR ℂ K →ₗ[F] F) (A B : Submodule ℂ (DR ℂ K)) (w : DR ℂ K)
    (h : ∀ y ∈ A, ψ y = Algebra.trace F K (τ (y * w))) {m : DR ℂ K ⊗[ℂ] DR ℂ K}
    (hm : m ∈ Submodule.map₂ (TensorProduct.mk ℂ _ _) A B) :
    ctrF (DR ℂ K) ψ m = mulP F K (muP F K τ m w) := by
  have key : Submodule.map₂ (TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K)) A B ≤
      LinearMap.eqLocus (ctrF (DR ℂ K) ψ) (mulP F K ∘ₗ (muP F K τ).flip w) := by
    refine Submodule.map₂_le.2 fun y hy y' _ => ?_
    simp [ctrF, muP, mulP, h y hy, algebraMap_smul]
  exact key hm

section Sz
variable {d : ℕ} (x : Fin (d + 1) → Fˣ)

private theorem xe (K : Type) [Field K] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (a : ℕ) (p j : Fin (d + 1)) :
    (((sysZ K x a).X p * ((sysZ K x a).X j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      algebraMap F K ((x p : F) / x j) ⊗ₜ[ℂ] 1 := by
  have h : (sysZ K x a).X p * ((sysZ K x a).X j)⁻¹ =
      Units.map ((Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) : F →* K ⊗[ℂ] K)
        (x p * (x j)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [h, div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul]
  rfl

private theorem ye (K : Type) [Field K] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (a : ℕ) (p j : Fin (d + 1)) :
    (((sysZ K x a).Y p * ((sysZ K x a).Y j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x p : F) / x j) := by
  have h : (sysZ K x a).Y p * ((sysZ K x a).Y j)⁻¹ =
      Units.map (((Algebra.TensorProduct.includeRight : K →ₐ[ℂ] K ⊗[ℂ] K).toRingHom.comp (algebraMap F K) : F →+* K ⊗[ℂ] K) :
        F →* K ⊗[ℂ] K) (x p * (x j)⁻¹) := by
    simp only [map_mul, map_inv]
    rfl
  rw [h, div_eq_mul_inv, ← Units.val_inv_eq_inv_val, ← Units.val_mul]
  rfl

private theorem act_r_diag (a : ℕ) (j : Fin (d + 1)) (l : Fin d) :
    (sysZ K x a).act ((sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) = actF F (DR ℂ K) (DR ℂ K) (f0 x j l) := by
  rw [r_eq, mul_inv_cancel, Units.val_one, one_mul, xe, ye]
  refine TensorProduct.ext' fun y y' => ?_
  change actZ K _ _ = _
  simp only [f0, map_sub, LinearMap.sub_apply, actZ_tmul, actF_tmul, one_smul, algebraMap_smul]

private theorem diag_case (hReg : RegLat) (hLat : LatOm) (hDual : DualForm) (hK1 : K1) (hGood : GoodZ)
    (hc : IsFinCover ℂ K (xv x)) (τ : DR ℂ K →ₗ[K] K) (hτ : IsTop ℂ K (xv x) τ) (a : ℕ) (ha : a ≤ d)
    (I J : Finset (Fin (d + 1))) (j : Fin (d + 1)) (hI : j ∈ I) (hJ : j ∈ J) :
    KE (kos (sysZ K x a).act ((sysZ K x a).M I J) fun l => (sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) d ∧
    ∀ m ∈ (sysZ K x a).M I J, Acts (F := F) K τ a m 0 →
      m ∈ sm (sysZ K x a).act ((sysZ K x a).M I J)
        (Set.range fun l => (sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) := by
  have hG := (hGood F K d x hc a).1
  obtain ⟨hR, hS⟩ := hReg F d x hc.pd (DR ℂ K) (DR ℂ K) I J _ _ (hLat F K d x hc (d - a) I ⟨j, hI⟩).1
    (hLat F K d x hc a J ⟨j, hJ⟩).1 j hI hJ
  have hact : ∀ l, actF F (DR ℂ K) (DR ℂ K) (f0 x j l) =
      (sysZ K x a).act ((sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l)) := fun l => (act_r_diag x a j l).symm
  have hrm := fun l => r_mem (sysZ K x a) hG hI hJ l
  refine ⟨hK1 _ _ (sysZ K x a).act (Fin d) ((sysZ K x a).R I J) _ _ d _ (hG.stab I J ⟨j, hI⟩ ⟨j, hJ⟩) hrm
    (reg_congr _ _ _ _ _ hact hR) fun k => ⟨Pi.single k 1, fun l => ?_, ?_⟩, fun m hm h0 => ?_⟩
  · rw [Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · simp [Pi.single_apply]
  · rw [← sm_range_congr _ _ _ _ _ hact]
    refine hS m hm fun ψ => ?_
    obtain ⟨⟨w, hw, hψ⟩, -⟩ := hDual F K d x hc τ hτ a ha ψ
    rw [ctrF_eq τ ψ _ _ w (fun y hy => hψ y (omB_le_fixed _ _ hy)) hm, h0 w hw, zero_smul]

private theorem loc_om (hc : IsFinCover ℂ K (xv x)) {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I)
    (j : Fin (d + 1)) (q : ℕ) {y : DR ℂ K} (hy : y ∈ omB ℂ K (rB ℂ K (xv x) (insert j I)) q) :
    ∃ N : ℕ, (algebraMap F K ((x j : F) / x i)) ^ N • y ∈ omB ℂ K (rB ℂ K (xv x) I) q := by
  by_cases hj : j ∈ I
  · rw [Finset.insert_eq_of_mem hj] at hy
    exact ⟨0, by simpa using hy⟩
  · obtain ⟨N, hN⟩ := (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc (insert j I) i (Finset.mem_insert_of_mem hi) q y).1 hy
    refine ⟨N, (GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul ℂ F K d (xv x) hc I i hi q _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj, map_mul, mul_pow] at hN
    rwa [smul_smul, mul_comm]

private theorem loc_M (a : ℕ) (hc : IsFinCover ℂ K (xv x)) (hG : (sysZ K x a).Good) {I J : Finset (Fin (d + 1))}
    {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J) :
    ∀ m ∈ (sysZ K x a).M (insert j I) J, ∃ N : ℕ,
      (sysZ K x a).act ((((sysZ K x a).X j * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) ^ N) m ∈ (sysZ K x a).M I J := by
  have hst : ∀ N : ℕ, ∀ m ∈ (sysZ K x a).M I J,
      (sysZ K x a).act ((((sysZ K x a).X j * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) ^ N) m ∈ (sysZ K x a).M I J :=
    fun N m hm => hG.stab I J ⟨i, hi⟩ ⟨j, hj⟩ _ (pow_mem (hG.memX I J ⟨j, hj⟩ i hi j) N) m hm
  intro m hm
  have hm' : m ∈ Submodule.span ℂ (Set.image2 (fun y y' => TensorProduct.mk ℂ (DR ℂ K) (DR ℂ K) y y')
      (omB ℂ K (rB ℂ K (xv x) (insert j I)) (d - a) : Set (DR ℂ K)) (omB ℂ K (rB ℂ K (xv x) J) a : Set (DR ℂ K))) := by
    rw [← Submodule.map₂_eq_span_image2]
    exact hm
  clear hm
  induction hm' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, hy, y', hy', rfl⟩ := hz
    obtain ⟨N, hN⟩ := loc_om x hc hi j (d - a) hy
    refine ⟨N, ?_⟩
    rw [xe, Algebra.TensorProduct.tmul_pow, one_pow]
    change actZ K _ (y ⊗ₜ y') ∈ _
    rw [actZ_tmul, one_smul]
    exact Submodule.apply_mem_map₂ _ hN hy'
  | zero => exact ⟨0, by simp⟩
  | add m₁ m₂ _ _ h₁ h₂ =>
    obtain ⟨N₁, h₁⟩ := h₁
    obtain ⟨N₂, h₂⟩ := h₂
    refine ⟨N₁ + N₂, ?_⟩
    rw [map_add (f := _)]
    refine Submodule.add_mem _ ?_ ?_
    · rw [add_comm, pow_add, map_mul]
      exact hst N₂ _ h₁
    · rw [pow_add, map_mul]
      exact hst N₁ _ h₂
  | smul c m _ h =>
    obtain ⟨N, h⟩ := h
    refine ⟨N, ?_⟩
    rw [map_smul]
    exact Submodule.smul_mem _ c h

end Sz

end Forms

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.colZ_of :
    RegLat → LatOm → DualForm → K1 → LocD → GoodZ → ColZ := by
  intro hReg hLat hDual hK1 hLoc hGood F K _ _ _ _ _ _ d x hc τ hτ a ha I J i hi j hj
  by_cases hij : i = j
  · subst hij
    exact diag_case x hReg hLat hDual hK1 hGood hc τ hτ a ha I J i hi hj
  obtain ⟨l0, hl0⟩ := Fin.exists_succAbove_eq hij
  have hG := (hGood F K d x hc a).1
  have hD := diag_case x hReg hLat hDual hK1 hGood hc τ hτ a ha (insert j I) J j (Finset.mem_insert_self j I) hj
  have hIi : i ∈ insert j I := Finset.mem_insert_of_mem hi
  have hJn : J.Nonempty := ⟨j, hj⟩
  have hIn : I.Nonempty := ⟨i, hi⟩
  have hL := hLoc _ _ (sysZ K x a).act (Fin d) ((sysZ K x a).R I J) ((sysZ K x a).M I J)
    ((sysZ K x a).M (insert j I) J) (fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l))
    ((sysZ K x a).X i * ((sysZ K x a).X j)⁻¹)
    (((sysZ K x a).X j * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)
    (((sysZ K x a).Y i * ((sysZ K x a).Y j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) l0 d
    (hG.stab I J hIn hJn) (fun l => r_mem _ hG hi hj l) (hG.memX I J hJn i hi j) (hG.memY I J hIn j hj i)
    (by
      have := r_eq (sysZ K x a) i j l0
      rw [hl0, mul_inv_cancel, Units.val_one] at this
      exact this)
    (hG.monoM I _ J J hIn hJn (Finset.subset_insert j I) subset_rfl) (loc_M x a hc hG hi hj)
    (fun m hm => ⟨hG.stab _ J ⟨i, hIi⟩ hJn _ (hG.memX _ J hJn j (Finset.mem_insert_self j I) i) m hm, by
      rw [mul_inv, inv_inv, mul_comm]
      exact hG.stab _ J ⟨i, hIi⟩ hJn _ (hG.memX _ J hJn i hIi j) m hm⟩)
  have hfun : (fun l => (sysZ K x a).r n11 (sysZ K x a).mu i j (dj j l) *
      (((sysZ K x a).X i * ((sysZ K x a).X j)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K)) =
      fun l => (sysZ K x a).r n11 (sysZ K x a).mu j j (dj j l) := funext fun l => r_mul _ i j l
  rw [hfun] at hL
  refine ⟨hL.1 hD.1, fun m hm h0 => hL.2 m hm (hD.2 m ?_ h0)⟩
  exact hG.monoM I _ J J hIn hJn (Finset.subset_insert j I) subset_rfl hm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ZActionCriterion
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem resP_one {F V : Type} [Field F] [Algebra ℂ F] [AddCommGroup V] [Module ℂ V] (ρ : F →ₗ[ℂ] ℂ)
    (h : ρ 1 = 1) (w : V) : resP V ρ ((1 : F) ⊗ₜ[ℂ] w) = w := by
  simp [resP, h]

private theorem lft_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    lft (uni I J) = I := by
  ext i
  simp [lft, uni, Finset.mem_toLeft]

private theorem rgt_uni' {ι κ : Type} [LinearOrder ι] [LinearOrder κ] (I : Finset ι) (J : Finset κ) :
    rgt (uni I J) = J := by
  ext i
  simp [rgt, uni, Finset.mem_toRight]

private theorem card_filter_le {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (· ≤ i)).card = (i : ℕ) + 1 := by
  have h : Finset.univ.filter (· ≤ i) = Finset.Iic i := by
    ext j
    simp
  rw [h, Fin.card_Iic]

private theorem card_filter_ge {d : ℕ} (i : Fin (d + 1)) :
    (Finset.univ.filter (i ≤ ·)).card = d + 1 - (i : ℕ) := by
  have h : Finset.univ.filter (i ≤ ·) = Finset.Ici i := by
    ext j
    simp
  rw [h, Fin.card_Ici]

theorem UpperTheory.Gal.productCup_of_system.zAct_of :
    PCup → PTheta → PCmp → PInt → EdgeRel → SysBasic → GoodZ → ZAct := by
  intro hCup hTh hCmp hInt hEdge hBas hGood F K _ _ _ _ _ _ d x hx τ hτ ρ hρ a p ha c hc hD α hα
  obtain ⟨hc1, hv1, hk1⟩ := hCup F K d x hx τ hτ a p ha c hc hD α hα
  obtain ⟨cθ, hcθ, hvθ, hkθ, htθ⟩ := hTh F K d x hx a p α hα
  have hmono := (hGood F K d x hx a).2.2
  have hE := hEdge (Fin (d + 1)) (DR ℂ K) (fun s => omB ℂ K (rB ℂ K (xv x) s) a) p hmono α hα
  let c1 := rcup (muP F K τ) p c α - cθ
  have hZ : c1 ∈ ((sysP K x a).cx n11 (sysP K x a).mu).Z (d + p + 2) := sub_mem hc1 hcθ
  have hv : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), d < L.card → c1 (uni b L) = 0 := by
    intro b L h
    simp [c1, hv1 b L h, hvθ b L h]
  let γ : Finset (Two d) → DR ℂ K :=
    ((-1 : ℤ) ^ (p * (d + 1) + d)) • edge1 α - ((-1 : ℤ) ^ ((p + 1) * d)) • edge2 α
  have hγe : γ = (-((-1 : ℤ) ^ ((p + 1) * d))) • (edge2 α - ((-1 : ℤ) ^ p) • edge1 α) := by
    have h : p * (d + 1) + d = (p + 1) * d + p := by ring
    simp only [γ, h, pow_add]
    generalize ((-1 : ℤ) ^ ((p + 1) * d)) = s
    generalize ((-1 : ℤ) ^ p) = t
    module
  have hγ : γ ∈ (acx (mixF fun I J : Finset (Fin (d + 1)) => omB ℂ K (rB ℂ K (xv x) (I ∪ J)) a) fun _ => 1).B (p + 2) := by
    rw [hγe]
    exact zsmul_mem hE _
  have hk : ∀ (b : Finset (Two d)) (L : Finset (Mi d)), L.card = d → mulP F K (c1 (uni b L)) = kap K x L • γ b := by
    intro b L h
    simp only [c1, γ, Pi.sub_apply, map_sub, hk1 b L h, hkθ b L h, smul_sub, Pi.smul_apply]
  have hB := hCmp F K d x hx a p c1 hZ hv γ hγ hk
  have hTop := (hBas d _ _ (sysP K x a) (Mi d) n11 (sysP K x a).mu (d + p + 2)).2.2.2.1 c1 hB
  have hI := hInt F K d x hx τ hτ ρ hρ a p (top c1) hTop
  have hCc := (hBas d _ _ (sysZ K x a) (Mi d) n11 (sysZ K x a).mu (d + 2)).1 c hc.1
  have hαs : ∀ s : Finset (Fin (d + 1)), s.card ≠ p + 1 → α s = 0 := by
    intro s hs
    have h1 : α s ∈ (if s.Nonempty ∧ (s.card : ℤ) = (p : ℤ) + 1 then omB ℂ K (rB ℂ K (xv x) s) a else ⊥ :
        Submodule ℂ (DR ℂ K)) := hα.1 s (Set.mem_univ s)
    rw [if_neg (by
      rintro ⟨-, h⟩
      exact hs (by exact_mod_cast h))] at h1
    simpa using h1
  have key : (α - fun J => resP (DR ℂ K) ρ (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))))) =
      -(fun J => resP (DR ℂ K) ρ (top c1 (uni Finset.univ J))) := by
    funext J
    have hsum : ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) =
        ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) := by
      by_cases hJ : J.card = p + 1
      · have : Even (p * J.card) := by
          rw [hJ]
          exact Nat.even_mul_succ_self p
        rw [this.neg_one_pow, one_smul]
      · have : ∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : (Finset.univ.filter (i ≤ ·)).card = p + 1
          · have h0 : top c (uni (Finset.univ.filter (· ≤ i)) J) = 0 := by
              refine hCc _ _ ∅ (Or.inr (Or.inr ?_))
              rw [card_filter_ge] at hi
              have hid := i.is_lt
              simp only [card_filter_le, Finset.card_empty, add_zero]
              omega
            rw [h0]
            simp
          · rw [hαs _ hi]
            simp
        rw [this, smul_zero]
    have htop : top c1 (uni Finset.univ J) = ((-1 : ℤ) ^ (p * J.card)) • (∑ i, muP F K τ (top c (uni (Finset.univ.filter (· ≤ i)) J)) (α (Finset.univ.filter (i ≤ ·)))) - (1 : F) ⊗ₜ[ℂ] α J := by
      simp only [top, c1, Pi.sub_apply, htθ, rcup, lft_uni', rgt_uni', Finset.card_empty, add_zero]
    simp only [Pi.sub_apply, Pi.neg_apply]
    rw [htop, hsum, map_sub, resP_one ρ hρ.1]
    abel
  rw [key]
  exact neg_mem hI
end

