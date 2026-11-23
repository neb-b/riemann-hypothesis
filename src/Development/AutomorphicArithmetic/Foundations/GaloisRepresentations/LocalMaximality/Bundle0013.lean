module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PActsLin
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma actZ_tmul (a b : K) (w' w'' : DR ℂ K) :
    actZ K (a ⊗ₜ b) (w' ⊗ₜ w'') = (a • w') ⊗ₜ[ℂ] (b • w'') := by
  simp [actZ]
  rfl

private lemma key1 (τ : DR ℂ K →ₗ[K] K) (a b : K) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (a ⊗ₜ b) m) w) = b • mulP F K (muP F K τ m (a • w)) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [actZ_tmul, muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, smul_mul_assoc, mul_smul_comm]
    exact smul_comm _ _ _
  | add x y hx hy => simp only [map_add (f := _), LinearMap.add_apply, hx, hy, smul_add]

private lemma key2 (τ : DR ℂ K →ₗ[K] K) (f : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ m (algebraMap F K f • w)) = algebraMap F K f • mulP F K (muP F K τ m w) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul w' w'' =>
    rw [muP_tmul, muP_tmul, mulP_tmul, mulP_tmul, mul_smul_comm, map_smul, smul_eq_mul, ← Algebra.smul_def,
      map_smul, smul_eq_mul, map_mul, mul_smul]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, smul_add, hp, hq]

private lemma key3 (τ : DR ℂ K →ₗ[K] K) (f g : F) (m : DR ℂ K ⊗[ℂ] DR ℂ K) (w : DR ℂ K) :
    mulP F K (muP F K τ (actZ K (algebraMap F K f ⊗ₜ algebraMap F K g) m) w) =
      algebraMap F K (f * g) • mulP F K (muP F K τ m w) := by
  rw [key1, key2, ← mul_smul, ← map_mul, mul_comm g f]

private lemma sysP_act_tmul {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (f f' : F) (k : K) (w : DR ℂ K) :
    (sysP K x a).act (f ⊗ₜ k) (f' ⊗ₜ w) = (f * f') ⊗ₜ[ℂ] (k • w) := by
  simp [sysP]
  rfl

private lemma r_eq {d : ℕ} (x : Fin (d + 1) → Fˣ) (a : ℕ) (i j : Fin (d + 1)) (l : Mi d) :
    (sysZ K x a).r n11 (sysZ K x a).mu i j l =
      algebraMap F K (x (ofLex l).1 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).2 / x j : Fˣ) -
      algebraMap F K (x (ofLex l).2 / x i : Fˣ) ⊗ₜ algebraMap F K (x (ofLex l).1 / x j : Fˣ) := by
  simp [Sys.r, Sys.mu, Sys.u, n11, sysZ, sub_mul, div_eq_mul_inv]

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.actsLin_of :
    ActsLin := by
  intro F K _ _ _ _ _ _ d x _ τ _ a
  have hadd : ∀ (m m' : DR ℂ K ⊗[ℂ] DR ℂ K) (c c' : K),
      Acts (F := F) K τ a m c → Acts (F := F) K τ a m' c' →
        Acts (F := F) K τ a (m + m') (c + c') ∧ Acts (F := F) K τ a (m - m') (c - c') := by
    intro m m' c c' hm hm'
    unfold Acts at hm hm' ⊢
    refine ⟨fun w hw => ?_, fun w hw => ?_⟩
    · rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), hm w hw, hm' w hw, add_smul]
    · rw [map_sub, LinearMap.sub_apply, map_sub, hm w hw, hm' w hw, sub_smul]
  have hr : ∀ (i j : Fin (d + 1)) (l : Mi d) (m : DR ℂ K ⊗[ℂ] DR ℂ K),
      Acts (F := F) K τ a (actZ K ((sysZ K x a).r n11 (sysZ K x a).mu i j l) m) 0 := by
    intro i j l m
    unfold Acts
    intro w _
    rw [r_eq, map_sub, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub, key3, key3,
      ← Units.val_mul, ← Units.val_mul, div_mul_div_comm, div_mul_div_comm,
      mul_comm (x (ofLex l).1) (x (ofLex l).2), sub_self, zero_smul]
  have hsm : ∀ (i j : Fin (d + 1)) (M : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K)),
      ∀ m ∈ sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)),
        Acts (F := F) K τ a m 0 := by
    intro i j M m hm
    let N : Submodule ℂ (DR ℂ K ⊗[ℂ] DR ℂ K) :=
      { carrier := {m | Acts (F := F) K τ a m 0}
        add_mem' := fun {m m'} hm hm' => by simpa using (hadd m m' 0 0 hm hm').1
        zero_mem' := by
          simp only [Set.mem_setOf_eq, Acts]
          intro w _
          simp
        smul_mem' := fun c m hm => by
          simp only [Set.mem_setOf_eq, Acts] at hm ⊢
          intro w hw
          rw [map_smul, LinearMap.smul_apply, map_smul, hm w hw]
          simp }
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤ N := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨u, _, rfl⟩
      obtain ⟨l, rfl⟩ := hs
      exact hr i j l u
    exact hle hm
  refine ⟨hadd, ?_, hsm, ?_, ?_, ?_⟩
  · intro m c s hm
    induction s using TensorProduct.induction_on with
    | zero =>
      unfold Acts
      intro w _
      simp
    | tmul p q =>
      unfold Acts at hm ⊢
      intro w hw
      rw [key1, hm _ (Submodule.smul_mem _ p hw)]
      simp only [Algebra.TensorProduct.lmul'_apply_tmul, smul_smul]
      congr 1
      ring
    | add s s' hs hs' =>
      simpa only [map_add (f := _), LinearMap.add_apply, add_mul] using (hadd _ _ _ _ hs hs').1
  · intro u M m i j hm
    apply hsm i j (M.map (actZ K u))
    have hle : sm (actZ K) M (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j)) ≤
        (sm (actZ K) (M.map (actZ K u))
          (Set.range ((sysZ K x a).r n11 (sysZ K x a).mu i j))).comap (actZ K u) := by
      unfold sm
      refine iSup₂_le fun s hs => ?_
      rintro _ ⟨v, hv, rfl⟩
      rw [Submodule.mem_comap]
      refine Submodule.mem_iSup_of_mem s (Submodule.mem_iSup_of_mem hs ⟨actZ K u v, ⟨v, hv, rfl⟩, ?_⟩)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    exact hle hm
  · intro s m
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul f' w =>
        rw [sysP_act_tmul, mulP_tmul, mulP_tmul]
        simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]
        rw [← algebraMap_smul K f' w, smul_smul]
        congr 1
        ring
      | add y z hy hz => simp only [map_add (f := _), smul_add, hy, hz]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, add_smul, hy, hz]
  · intro s m w
    induction s using TensorProduct.induction_on with
    | zero => simp
    | tmul f k =>
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul w' w'' =>
        rw [Algebra.TensorProduct.map_tmul, actZ_tmul, muP_tmul, muP_tmul, sysP_act_tmul]
        simp only [IsScalarTower.coe_toAlgHom', AlgHom.coe_id, id_eq, smul_mul_assoc, map_smul,
          smul_eq_mul]
        rw [← Algebra.smul_def, map_smul, smul_eq_mul]
      | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, hy, hz]
    | add y z hy hz => simp only [map_add (f := _), LinearMap.add_apply, hy, hz]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PGoodZ
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section Tensor
variable {S S' E E' : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
  [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']

private theorem range_mono {A A' : Subalgebra ℂ S} {B B' : Subalgebra ℂ S'} (hA : A ≤ A') (hB : B ≤ B') :
    (Algebra.TensorProduct.map A.val B.val).range ≤ (Algebra.TensorProduct.map A'.val B'.val).range := by
  rintro _ ⟨z, rfl⟩
  refine ⟨Algebra.TensorProduct.map (Subalgebra.inclusion hA) (Subalgebra.inclusion hB) z, ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add p q hp hq => simp only [map_add (f := _)] at *; rw [hp, hq]

private theorem tmul_mem_range {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {a : S} {b : S'} (ha : a ∈ A) (hb : b ∈ B) :
    a ⊗ₜ[ℂ] b ∈ (Algebra.TensorProduct.map A.val B.val).range :=
  ⟨(⟨a, ha⟩ : A) ⊗ₜ[ℂ] (⟨b, hb⟩ : B), by simp⟩

private theorem stab_tensor (f : S →ₐ[ℂ] Module.End ℂ E) (g : S' →ₐ[ℂ] Module.End ℂ E')
    {A : Subalgebra ℂ S} {B : Subalgebra ℂ S'} {P : Submodule ℂ E} {Q : Submodule ℂ E'}
    (hP : ∀ a ∈ A, ∀ m ∈ P, f a m ∈ P) (hQ : ∀ b ∈ B, ∀ m ∈ Q, g b m ∈ Q) :
    Stab ((Module.endTensorEndAlgHom).comp (Algebra.TensorProduct.map f g))
      (Algebra.TensorProduct.map A.val B.val).range (Submodule.map₂ (TensorProduct.mk ℂ _ _) P Q) := by
  rintro _ ⟨z, rfl⟩ m hm
  induction z using TensorProduct.induction_on generalizing m with
  | zero => simp
  | tmul a b =>
    have hle : Submodule.map₂ (TensorProduct.mk ℂ E E') P Q ≤
        (Submodule.map₂ (TensorProduct.mk ℂ E E') P Q).comap (TensorProduct.map (f a) (g b)) := by
      rw [Submodule.map₂_le]
      intro p hp q hq
      simp only [Submodule.mem_comap, TensorProduct.mk_apply, TensorProduct.map_tmul]
      exact Submodule.apply_mem_map₂ _ (hP _ a.2 _ hp) (hQ _ b.2 _ hq)
    have h2 := hle hm
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Subalgebra.coe_val]
    exact h2
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), LinearMap.add_apply]
    exact add_mem (hp m hm) (hq m hm)

private theorem units_ratio {F : Type} [Field F] (f : F →+* S) (u v : Fˣ) :
    ((Units.map (f : F →* S) u * (Units.map (f : F →* S) v)⁻¹ : Sˣ) : S) = f ((u : F) / v) := by
  simp [div_eq_mul_inv]

end Tensor

section Forms
variable {K : Type} [Field K] [Algebra ℂ K]

private theorem omB_mono' {B B' : Subalgebra ℂ K} (h : B ≤ B') (q : ℕ) : omB ℂ K B q ≤ omB ℂ K B' q := by
  unfold omB
  exact Submodule.span_mono (fun y ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩)

private theorem omB_smul (B : Subalgebra ℂ K) (q : ℕ) {c : K} (hc : c ∈ B) {m : DR ℂ K} (hm : m ∈ omB ℂ K B q) :
    Algebra.lsmul ℂ ℂ (DR ℂ K) c m ∈ omB ℂ K B q := by
  show c • m ∈ omB ℂ K B q
  unfold omB at hm ⊢
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hy
    exact Submodule.subset_span ⟨c * b, B.mul_mem hc hb, v, hv, by rw [mul_smul]⟩
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul r y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ r hy

end Forms

section Chart
variable {F : Type} (K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] {d : ℕ}
  (x : Fin (d + 1) → Fˣ)

private theorem ratio_mem_rA {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    (x a : F) / x i ∈ rA ℂ (xv x) I := by
  unfold rA
  exact Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private theorem ratio_mem_rB {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    algebraMap F K ((x a : F) / x i) ∈ rB ℂ K (xv x) I := by
  unfold rB
  exact (integralClosure (rA ℂ (xv x) I) K).algebraMap_mem (⟨_, ratio_mem_rA x hi a⟩ : rA ℂ (xv x) I)

private theorem sysZ_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).X b * ((sysZ K x a).X i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      algebraMap F K ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysZ_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysZ K x a).Y b * ((sysZ K x a).Y i)⁻¹ : (K ⊗[ℂ] K)ˣ) : K ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysZ
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysP_X (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).X b * ((sysP K x a).X i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      ((x b : F) / x i) ⊗ₜ[ℂ] 1 := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

private theorem sysP_Y (a : ℕ) (b i : Fin (d + 1)) :
    (((sysP K x a).Y b * ((sysP K x a).Y i)⁻¹ : (F ⊗[ℂ] K)ˣ) : F ⊗[ℂ] K) =
      1 ⊗ₜ[ℂ] algebraMap F K ((x b : F) / x i) := by
  unfold sysP
  exact (units_ratio _ (x b) (x i)).trans rfl

end Chart

theorem UpperTheory.Gal.productCup_of_system.goodZ_of :
    GoodZ := by
  intro F K _ _ _ _ _ _ d x hx a
  have hrB : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → I ⊆ J → rB ℂ K (xv x) I ≤ rB ℂ K (xv x) J := by
    intro I J hI hIJ
    obtain ⟨i, hi⟩ := hI
    exact (GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d (xv x) hx I i hi).1 J hIJ
  have hx0 : ∀ i, xv x i ≠ 0 := fun i => (x i).ne_zero
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (hrB I I' hI hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    show MZ F K (xv x) a I J ≤ MZ F K (xv x) a I' J'
    unfold MZ
    exact Submodule.map₂_le_map₂ (omB_mono' (hrB I I' hI hII) _) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ (DR ℂ K)) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => omB_smul _ _ hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysZ_X]
    exact tmul_mem_range (ratio_mem_rB K x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysZ_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro I I' J J' hI hJ hII hJJ
    exact range_mono (rA_le_of_subset hII) (hrB J J' hJ hJJ)
  · intro I I' J J' hI hJ hII hJJ
    exact Submodule.map₂_le_map₂ (omA_le_of_subset hx0 hI hII) (omB_mono' (hrB J J' hJ hJJ) _)
  · intro I J hI hJ
    exact stab_tensor (Algebra.lsmul ℂ ℂ F) (Algebra.lsmul ℂ ℂ (DR ℂ K))
      (fun c hc m hm => mul_mem_omA_of_mem_rA hc hm) (fun c hc m hm => omB_smul _ _ hc hm)
  · intro I J hJ i hi b
    rw [sysP_X]
    exact tmul_mem_range (ratio_mem_rA x hi b) (Subalgebra.one_mem _)
  · intro I J hI j hj b
    rw [sysP_Y]
    exact tmul_mem_range (Subalgebra.one_mem _) (ratio_mem_rB K x hj b)
  · intro s t hs hst
    exact omB_mono' (hrB s t hs hst) a
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PKapInd
section
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

namespace UpperTheory.Gal.productCup_of_system

private theorem wd_apply' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (c : Finset ι → E) (t : Finset ι) :
    wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem map_detC' {S S' κ : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']
    [LinearOrder κ] {p : ℕ} (φ : S →ₐ[ℂ] S') (ρ : κ → Fin p → S) (s : Finset κ) :
    φ (detC ρ s) = detC (fun t b => φ (ρ t b)) s := by
  unfold detC
  split_ifs with h
  · rw [AlgHom.map_det]
    congr 1
  · simp

private def rho0 {d : ℕ} {K : Type} [Field K] (y : Fin (d + 1) → K) :
    Fin (d + 1) ⊕ₗ Mi d → Fin (d + 1) → K := fun t => Sum.elim (fun i => Pi.single i 1)
  (fun l m => (if m = (ofLex l).1 then y m * y (ofLex l).2 else 0) -
    if m = (ofLex l).2 then y m * y (ofLex l).1 else 0) (ofLex t)

private theorem map_rowMu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (s : Finset (Fin (d + 1) ⊕ₗ Mi d)) :
    π (detC T.rowMu s) = detC (rho0 y) s := by
  rw [map_detC']
  congr 1
  funext t b
  rcases ht : ofLex t with i | l
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inl, Pi.single_apply]
    split_ifs <;> simp
  · simp only [Sys.rowMu, rho0, ht, Sum.elim_inr, map_sub, apply_ite π, map_mul, hX, hY, map_zero]

private theorem map_mu {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) (π : S →ₐ[ℂ] K) (y : Fin (d + 1) → K)
    (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i) (l : Mi d) : π (T.mu l) = 0 := by
  simp only [Sys.mu, map_sub, map_mul, hX, hY]
  ring

private theorem ind_of {d : ℕ} {K S E : Type} [Field K] [Algebra ℂ K] [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (hM : ThMu) (hU : WdUni) (T : Sys d S E) (π : S →ₐ[ℂ] K)
    (y : Fin (d + 1) → K) (hX : ∀ i, π (T.X i) = y i) (hY : ∀ i, π (T.Y i) = y i)
    (i : Fin (d + 1)) (L : Finset (Mi d)) :
    π (detC T.rowMu (uni {i} L)) = π (detC T.rowMu (uni {0} L)) := by
  by_cases h : i = 0
  · rw [h]
  have h0 : (0 : Fin (d + 1)) ≠ i := fun e => h e.symm
  have h1 := congrFun (hM d S E T).1 (uni {0, i} L)
  rw [(hU _ _ _ _ _ {0, i} L).1] at h1
  have hl : wd (fun j : Fin (d + 1) => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inlE j : Fin (d + 1) ⊕ₗ Mi d)))
      (fun b' => detC T.rowMu (uni b' L)) {0, i} =
      detC T.rowMu (uni {i} L) - detC T.rowMu (uni {0} L) := by
    have e0 : ({0, i} : Finset (Fin (d + 1))).erase 0 = {i} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact absurd hb ha
        · exact hb
      · rintro rfl; exact ⟨h, Or.inr rfl⟩
    have ei : ({0, i} : Finset (Fin (d + 1))).erase i = {0} := by
      ext a; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨ha, hb | hb⟩
        · exact hb
        · exact absurd hb ha
      · rintro rfl; exact ⟨h0, Or.inl rfl⟩
    have s0 : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) 0 = 1 := by
      simp [GlobalTheory.cubeSign, Finset.filter_eq_empty_iff]
    have si : GlobalTheory.cubeSign ({0, i} : Finset (Fin (d + 1))) i = -1 := by
      have hp : (0 : Fin (d + 1)) < i := Fin.pos_iff_ne_zero.2 h
      have : ({0, i} : Finset (Fin (d + 1))).filter (· < i) = {0} := by
        ext a; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl | rfl, hb⟩
          · rfl
          · exact absurd hb (lt_irrefl _)
        · rintro rfl; exact ⟨Or.inl rfl, hp⟩
      simp [GlobalTheory.cubeSign, this]
    rw [wd_apply', Finset.sum_pair h0, e0, ei, s0, si]
    simp [app, inlE, sub_eq_add_neg, add_comm]
  have hr : π (wd (fun l : Mi d => (Algebra.lmul ℂ S) (app (fun _ => 1) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d)))
      (fun L' => detC T.rowMu (uni {0, i} L')) L) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [wd_apply', map_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : app (fun _ : Fin (d + 1) => (1 : S)) T.mu (inrE l : Fin (d + 1) ⊕ₗ Mi d) = T.mu l := by simp [app, inrE]
    rw [map_zsmul]
    simp [this, map_mu T π y hX hY l]
  rw [hl] at h1
  have h2 := congrArg π h1
  rw [map_add (f := _), map_zsmul, hr, smul_zero, add_zero, map_sub] at h2
  simpa [sub_eq_zero] using h2

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.kapInd_of :
    ThMu → WdUni → KapInd := by
  intro hM hU F K _ _ _ _ _ _ d x _ S E _ _ _ _ T π hX hY i L _
  have hZ : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).X j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  have hZ' : ∀ j, Algebra.TensorProduct.lmul' ℂ ((sysZ K x 0).Y j : K ⊗[ℂ] K) = algebraMap F K (x j) := by
    intro j; simp [sysZ]
  rw [ind_of hM hU T π _ hX hY i L, kap,
    map_rowMu T π (fun j => algebraMap F K (x j)) hX hY,
    map_rowMu (sysZ K x 0) (Algebra.TensorProduct.lmul' ℂ) (fun j => algebraMap F K (x j)) hZ hZ']
end

