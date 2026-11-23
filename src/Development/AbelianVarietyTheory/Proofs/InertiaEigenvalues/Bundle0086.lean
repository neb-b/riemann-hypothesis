module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisHankelDetNeZeroOfLift
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DeltaLift

variable {k : Type} [Field k] {r : ℕ}

theorem full_cc (Z : Gl r k) (i j : Fin r) : full Z (Fin.castSucc i) (Fin.castSucc j) = Z.1 i j := by
  simp [full]

theorem full_cl (Z : Gl r k) (i : Fin r) : full Z (Fin.castSucc i) (Fin.last r) = Z.2.1 i := by
  simp [full]

theorem full_lc (Z : Gl r k) (j : Fin r) : full Z (Fin.last r) (Fin.castSucc j) = Z.2.2.1 j := by
  simp [full]

theorem full_mulVec_cs (Z : Gl r k) (V : Fin (r + 1) → k) (i : Fin r) :
    (full Z *ᵥ V) (Fin.castSucc i) = (Z.1 *ᵥ (fun j => V (Fin.castSucc j))) i + V (Fin.last r) * Z.2.1 i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_castSucc, full_cc, full_cl]
  ring

theorem vecMul_full_cs (Z : Gl r k) (V : Fin (r + 1) → k) (j : Fin r) :
    (V ᵥ* full Z) (Fin.castSucc j) = ((fun i => V (Fin.castSucc i)) ᵥ* Z.1) j + V (Fin.last r) * Z.2.2.1 j := by
  simp only [vecMul, dotProduct, Fin.sum_univ_castSucc, full_cc, full_lc]

theorem dot_split (W V : Fin (r + 1) → k) :
    W ⬝ᵥ V = (fun i => W (Fin.castSucc i)) ⬝ᵥ (fun i => V (Fin.castSucc i)) + W (Fin.last r) * V (Fin.last r) := by
  simp only [dotProduct, Fin.sum_univ_castSucc]

theorem dot_pow_all (A : Matrix (Fin r) (Fin r) k) (w b : Fin r → k)
    (h : ∀ i < r, w ⬝ᵥ (A ^ i *ᵥ b) = 0) (m : ℕ) : w ⬝ᵥ (A ^ m *ᵥ b) = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp [dotProduct]
  have hP : A.charpoly.Monic := Matrix.charpoly_monic A
  have hdeg : A.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim A
  have hne : A.charpoly ≠ 1 := by
    intro h1; rw [h1, Polynomial.natDegree_one] at hdeg; omega
  have hlt : (Polynomial.X ^ m %ₘ A.charpoly).natDegree < r := by
    simpa [hdeg] using Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ m) hP hne
  rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hlt]
  have key : ∀ (s : Finset ℕ), (∀ i ∈ s, i < r) → ∀ c : ℕ → k,
      w ⬝ᵥ ((∑ i ∈ s, c i • A ^ i) *ᵥ b) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _ c; simp
    | insert a s ha ih =>
      intro hs c
      rw [Finset.sum_insert ha, add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul,
        h a (hs a (Finset.mem_insert_self a s)), ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) c]
      simp
  exact key _ (fun i hi => Finset.mem_range.mp hi) _

theorem det_Bm_lift (Z : Gl r k) (μ l : k) (h : (Bm Z).det = 0) :
    (Bm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨w, hw0, hw⟩ := (Matrix.exists_vecMul_eq_zero_iff (M := Bm Z)).mpr h
  have hw' : ∀ m, w ⬝ᵥ (Z.1 ^ m *ᵥ Z.2.1) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hw ⟨i, hi⟩
    simpa [vecMul, Bm, dotProduct] using this
  set A' := full Z
  let x : ℕ → Fin r → k := fun j i => (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.castSucc i)
  have hx : ∀ j m, w ⬝ᵥ (Z.1 ^ m *ᵥ x j) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : x 0 = 0 := by
        funext i; simp [x, GlobalTheory.JR.Step.eL, Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, mulVec_zero, dotProduct_zero]
    | succ j ih =>
      intro m
      have hxs : x (j + 1) = Z.1 *ᵥ x j + (A' ^ j *ᵥ GlobalTheory.JR.Step.eL r k) (Fin.last r) • Z.2.1 := by
        funext i
        simp only [x, pow_succ', ← mulVec_mulVec]
        rw [full_mulVec_cs]
        simp [mul_comm]
      rw [hxs, mulVec_add, dotProduct_add, mulVec_mulVec, ← pow_succ, ih, mulVec_smul, dotProduct_smul, hw']
      simp
  refine (Matrix.exists_vecMul_eq_zero_iff (M := Bm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 w i, ?_, ?_⟩
  · intro h0
    apply hw0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · have e : (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ᵥ* Bm (GlobalTheory.JR.Step.lift Z μ l)
        = fun j : Fin (r + 1) => μ * (w ⬝ᵥ x (j : ℕ)) := by
      funext j
      show (fun i => Fin.lastCases 0 w i : Fin (r + 1) → k) ⬝ᵥ (A' ^ (j : ℕ) *ᵥ (μ • GlobalTheory.JR.Step.eL r k)) = _
      rw [mulVec_smul, dotProduct_smul, dot_split]
      simp [x, smul_eq_mul]
    rw [e]
    funext j
    simpa using congrArg (μ * ·) (hx j 0)

theorem det_Cm_lift (Z : Gl r k) (μ l : k) (h : (Cm Z).det = 0) :
    (Cm (GlobalTheory.JR.Step.lift Z μ l)).det = 0 := by
  obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := Cm Z)).mpr h
  have hv' : ∀ m, Z.2.2.1 ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    apply dot_pow_all
    intro i hi
    have := congrFun hv ⟨i, hi⟩
    rw [dotProduct_mulVec]
    simpa [mulVec, Cm, dotProduct] using this
  set A' := full Z
  let u : ℕ → Fin r → k := fun j i => (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.castSucc i)
  have hu : ∀ j m, u j ⬝ᵥ (Z.1 ^ m *ᵥ v) = 0 := by
    intro j
    induction j with
    | zero =>
      intro m
      have h0 : u 0 = 0 := by
        funext i
        simp only [u, pow_zero, vecMul_one, GlobalTheory.JR.Step.eL]
        simp [Pi.single_apply, Fin.castSucc_ne_last]
      rw [h0, zero_dotProduct]
    | succ j ih =>
      intro m
      have hus : u (j + 1) = u j ᵥ* Z.1 + (GlobalTheory.JR.Step.eL r k ᵥ* A' ^ j) (Fin.last r) • Z.2.2.1 := by
        funext i
        simp only [u, pow_succ, ← vecMul_vecMul]
        rw [vecMul_full_cs]
        simp [mul_comm]
      rw [hus, add_dotProduct, ← dotProduct_mulVec, mulVec_mulVec, ← pow_succ', ih, smul_dotProduct, hv']
      simp
  refine (Matrix.exists_mulVec_eq_zero_iff (M := Cm (GlobalTheory.JR.Step.lift Z μ l))).mp ?_
  refine ⟨fun i => Fin.lastCases 0 v i, ?_, ?_⟩
  · intro h0
    apply hv0
    funext i
    simpa using congrFun h0 (Fin.castSucc i)
  · funext j
    simp only [mulVec, Cm, GlobalTheory.JR.Step.lift, Matrix.of_apply]
    rw [dot_split]
    simpa [u, A'] using hu j 0

end GlobalTheory.JR.DeltaLift


open GlobalTheory.JR.DeltaLift in
theorem GlobalTheory.JR.Step.delta_lift_ne : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k),
    Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  intro k _ r Z μ l h
  have e1 := (_root_.GlobalTheory.JR.normalForm_invariants k (r + 1)).2.2.1 (GlobalTheory.JR.Step.lift Z μ l)
  have e0 := (_root_.GlobalTheory.JR.normalForm_invariants k r).2.2.1 Z
  unfold Delta at h ⊢
  rw [← e1, det_mul] at h
  rw [← e0, det_mul]
  have hC : (Cm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := left_ne_zero_of_mul h
  have hB : (Bm (GlobalTheory.JR.Step.lift Z μ l)).det ≠ 0 := right_ne_zero_of_mul h
  exact mul_ne_zero (fun hc => hC (det_Cm_lift Z μ l hc)) (fun hb => hB (det_Bm_lift Z μ l hb))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHomSubmoduleFgAndSpanEqTop
section
open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

noncomputable section

namespace GlobalTheory.StableLatCount

theorem exists_smul_mem_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E] [Algebra O E]
    [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A] [IsScalarTower O E A]
    (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (a : A) :
    ∃ d ∈ nonZeroDivisors O, d • a ∈ M := by
  have ha : a ∈ Submodule.span E (M : Set A) := hM ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by simpa using hx⟩
  | zero => exact ⟨1, one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₂ * d₁, mul_mem hd₂ hd₁, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm d₂ d₁ y]
    exact M.add_mem (M.smul_mem _ h₁) (M.smul_mem _ h₂)
  | smul e x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨⟨o, s⟩, hs⟩ := IsLocalization.surj (nonZeroDivisors O) e
    have h1 : (s : O) • (e • x) = o • x := by
      rw [← algebraMap_smul E (s : O) (e • x), smul_smul, mul_comm, hs, algebraMap_smul]
    refine ⟨(s : O) * d, mul_mem s.2 hd, ?_⟩
    rw [mul_comm, mul_smul, h1, smul_comm d o x]
    exact M.smul_mem o h

theorem exists_smul_mem_finset_of_span_eq_top (O : Type) [CommRing O] [IsDomain O] (E : Type) [Field E]
    [Algebra O E] [IsFractionRing O E] {A : Type} [AddCommGroup A] [Module E A] [Module O A]
    [IsScalarTower O E A] (M : Submodule O A) (hM : Submodule.span E (M : Set A) = ⊤) (t : Finset A) :
    ∃ d ∈ nonZeroDivisors O, ∀ a ∈ t, d • a ∈ M := by
  classical
  refine Finset.induction_on t ⟨1, one_mem _, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨d₁, hd₁, h₁⟩ := ih
  obtain ⟨d₂, hd₂, h₂⟩ := exists_smul_mem_of_span_eq_top O E M hM a
  refine ⟨d₁ * d₂, mul_mem hd₁ hd₂, ?_⟩
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · rw [mul_smul]; exact M.smul_mem _ h₂
  · rw [mul_comm, mul_smul]; exact M.smul_mem _ (h₁ b hb)

theorem homLat_fg_and_span_eq_top (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (E : Type)
    [Field E] [Algebra O E] [IsFractionRing O E] (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra E A₁]
    [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁] [IsScalarTower O E A₂]
    [Module.Finite E A₁] [Module.Finite E A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) :
    IsLat O E M₁ → IsLat O E M₂ →
      (homLat E M₁ M₂).FG ∧ Submodule.span E (homLat E M₁ M₂ : Set (A₂ →ₗ[E] A₁)) = ⊤ := by
  classical
  intro h₁ h₂
  obtain ⟨h₁fg, h₁sp⟩ := h₁
  obtain ⟨h₂fg, h₂sp⟩ := h₂
  obtain ⟨s, hs⟩ := h₂fg
  have hsE : Submodule.span E (s : Set A₂) = ⊤ := by
    rw [eq_top_iff, ← h₂sp, Submodule.span_le, ← hs]
    exact fun x hx => Submodule.span_le_restrictScalars O E _ hx
  have memH : ∀ ψ ∈ homLat E M₁ M₂, ∀ x ∈ M₂, ψ x ∈ M₁ := fun ψ hψ => hψ
  refine ⟨?_, ?_⟩
  · haveI : Module.Finite O M₁ := Module.Finite.iff_fg.mpr h₁fg
    let f : homLat E M₁ M₂ →ₗ[O] (s → M₁) :=
      { toFun := fun ψ x => ⟨ψ.1 x, memH ψ.1 ψ.2 x (hs ▸ Submodule.subset_span x.2)⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro ψ φ h
      apply Subtype.ext
      apply LinearMap.ext_on hsE
      intro x hx
      exact congrArg Subtype.val (congrFun h ⟨x, hx⟩)
    haveI := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.mp this
  · rw [eq_top_iff]
    intro ψ _
    obtain ⟨d, hd, hdψ⟩ := exists_smul_mem_finset_of_span_eq_top O E M₁ h₁sp (s.image ψ)
    have hmem : d • ψ ∈ homLat E M₁ M₂ := by
      show ∀ x ∈ M₂, (d • ψ) x ∈ M₁
      intro x hx
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem y hy => rw [LinearMap.smul_apply]; exact hdψ _ (Finset.mem_image_of_mem _ hy)
      | zero => simp
      | add y z _ _ hy hz => rw [map_add (f := _)]; exact M₁.add_mem hy hz
      | smul o y _ hy => rw [LinearMap.map_smul_of_tower]; exact M₁.smul_mem o hy
    have hd' : algebraMap O E d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    have hψ : ψ = (algebraMap O E d)⁻¹ • (d • ψ) := by
      rw [← algebraMap_smul E d ψ, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hψ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftMulTau
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

def bas (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [hG.2.1]; simp)

def pt (hG : A.IsGen τ p) (lam : F) (b c : A.K) : Gl r F :=
  (companion p, (bas A hG).equivFun b, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * c), lam)

def tm (hG : A.IsGen τ p) : A.Kˣ →* GL (Fin r) F :=
  Units.map (Algebra.leftMulMatrix (bas A hG)).toRingHom.toMonoidHom

def unitsMeas (μK : Measure A.K) : Measure A.Kˣ :=
  (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹).comap Units.val

def desc (M : Meas r F E)
    (hG : A.IsGen τ p) (lam : F) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (x : A.K × A.K) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem bas_apply (hG : A.IsGen τ p) (i : Fin r) : LinDesc.bas A hG i = τ ^ (i : ℕ) := by
  simp [LinDesc.bas]

theorem repr_sum (hG : A.IsGen τ p) (c : Fin r → F) :
    (LinDesc.bas A hG).repr (∑ i, c i • τ ^ (i : ℕ)) = Finsupp.equivFunOnFinite.symm c := by
  have : (∑ i, c i • τ ^ (i : ℕ)) = (LinDesc.bas A hG).equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]; simp [bas_apply]
  rw [this]
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]; simp

theorem leftMul_tau (hG : A.IsGen τ p) : Algebra.leftMulMatrix (LinDesc.bas A hG) τ = companion p := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, bas_apply, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj]
    have h3 : τ ^ r = ∑ k, (-p k) • τ ^ (k : ℕ) := by
      have := hG.2.2
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left this
    rw [h3, repr_sum]; simp
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    have h3 : τ ^ ((j : ℕ) + 1) = LinDesc.bas A hG ⟨(j : ℕ) + 1, hlt⟩ := by rw [bas_apply]
    rw [h3, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg]
      intro h; exact hi (by rw [← h])

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

theorem tm_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Algebra.leftMulMatrix (bas A hG) (t : A.K) := rfl

theorem tm_inv_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    (((tm A hG t)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Algebra.leftMulMatrix (bas A hG) ((t⁻¹ : A.Kˣ) : A.K) := by
  rw [← map_inv]; rfl

theorem row_mul (hG : A.IsGen τ p) (s c : A.K) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* Algebra.leftMulMatrix (bas A hG) s =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]
  have hx := (bas A hG).sum_repr (s * bas A hG j)
  calc ∑ i : Fin r, Algebra.trace F A.K (τ ^ (i : ℕ) * c) * (bas A hG).repr (s * bas A hG j) i
      = Algebra.trace F A.K (∑ i : Fin r, ((bas A hG).repr (s * bas A hG j) i • bas A hG i) * c) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]
    _ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
        rw [← Finset.sum_mul, hx, bas_apply]; ring_nf

theorem act_tm (hG : A.IsGen τ p) (lam : F) (t : A.Kˣ) (b c : A.K) :
    act (tm A hG t) (pt A hG lam b c) = pt A hG lam ((t : A.K) * b) (((t⁻¹ : A.Kˣ) : A.K) * c) := by
  unfold act pt
  rw [tm_inv_coe, tm_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← leftMul_tau A hG, ← map_mul, ← map_mul]; congr 1
    rw [mul_comm (t : A.K) τ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · simp only
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr _ _ _
  · exact row_mul A hG _ c

theorem det_tm (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = Algebra.norm F (t : A.K) := by
  rw [tm_coe, Algebra.norm_eq_matrix_det (bas A hG)]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  unfold act
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

theorem act_one {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) : act 1 Y = Y := by
  unfold act; simp

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
theorem pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ a : A.K, LinDesc.pt A hG lam 1 a = sec (A.invK τ p lam a) := by
  intro F E _ _ _ _ _ A r τ p hG lam a
  unfold LinDesc.pt sec Et.invK
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  have h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩ := by
    simp [LinDesc.bas]
  simp only
  rw [h1, Module.Basis.equivFun_self]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
  · rw [if_neg hi, if_neg]
    intro h; exact hi (by rw [← h])
end GlobalTheory.JR.LinDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma

theorem mem_range_of_val_nonneg (K : UQ) (z : K.E) (h : 0 ≤ val K.O z) :
    ∃ a : K.O, algebraMap K.O K.E a = z := by
  by_cases hz : z = 0
  · exact ⟨0, by simp [hz]⟩
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≠ 0 := by simpa using hz
  have hle : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E z ≤ 1 := by
    unfold val at h
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hle
  exact ⟨a, ha⟩

theorem val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  unfold val
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (IsDiscreteValuationRing.maximalIdeal K.O) (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using ha
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem exists_int_image {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (a : K.O) :
    ∃ b : K'.O, algebraMap K'.O K'.E b = φ (algebraMap K.O K.E a) := by
  apply mem_range_of_val_nonneg
  rw [hU.2.2.1]
  exact val_algebraMap_nonneg K a

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NLineOne
section
noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial IsLocalRing

theorem c_mem (K : UQ) {z : K.E} (hz : z ∈ (algebraMap K.O K.E).range) : K.c z ∈ (algebraMap K.O K.E).range := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, hy⟩ := K.c_int x
  exact ⟨y, hy.symm⟩

end GlobalTheory.UnitLemma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotIsIntegralResidueInvSmallInteger
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.NotIntegral

theorem inv_small_not_integral : ∀ (K : UQ) (B : InvAlg K) (a : K.O), K.Small a → ∀ m : MaximalSpectrum B.A, ¬ IsIntegral K.O (algebraMap K.E (B.A ⧸ m.asIdeal) (algebraMap K.O K.E a)⁻¹) := by
  intro K B a ha m hint
  obtain ⟨ha0, hmax, -⟩ := ha
  haveI : m.asIdeal.IsMaximal := m.isMaximal
  letI : Field (B.A ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  let f : K.E →ₐ[K.O] (B.A ⧸ m.asIdeal) := IsScalarTower.toAlgHom K.O K.E (B.A ⧸ m.asIdeal)
  have hf : Function.Injective f := (algebraMap K.E (B.A ⧸ m.asIdeal)).injective
  have hE : IsIntegral K.O (algebraMap K.O K.E a)⁻¹ := (isIntegral_algHom_iff f hf).1 hint
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 hE
  have hne : algebraMap K.O K.E a ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective K.O K.E)]; exact ha0
  have hab : a * b = 1 := by
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, hb, map_one, mul_inv_cancel₀ hne]
  exact (IsLocalRing.mem_maximalIdeal a).1 hmax ⟨⟨a, b, hab, by rw [mul_comm]; exact hab⟩, rfl⟩

end GlobalTheory.NotIntegral
end

