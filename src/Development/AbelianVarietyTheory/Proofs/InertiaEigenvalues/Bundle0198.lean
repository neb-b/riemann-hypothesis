module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem linApprox_of_polyApprox_trc : ∀ (k Γ : Type) [NormedField k] [IsUltrametricDist k] [Group Γ] (a : ℕ)
    (r : Γ →* GL (Fin a) k) (C : Set (Γ →* GL (Fin a) k)), PolyApprox (trc r) (trc '' C) → LinApprox r C := by
  intro k Γ _ _ _ a r C h ε hε
  classical
  obtain ⟨s, c, hs, hP⟩ := h ε hε
  let f : (Γ → k) → (Γ →* GL (Fin a) k) := Function.invFunOn trc C
  have hf : ∀ η ∈ s, f η ∈ C ∧ trc (f η) = η := fun η hη =>
    ⟨Function.invFunOn_mem (hs hη), Function.invFunOn_eq (hs hη)⟩
  have hinj : Set.InjOn f (s : Set (Γ → k)) := fun x hx y hy hxy => by
    rw [← (hf x hx).2, ← (hf y hy).2, hxy]
  refine ⟨s.image f, fun ρ => c (trc ρ), ?_, fun g => ?_⟩
  · intro ρ hρ
    obtain ⟨η, hη, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hρ)
    exact (hf η hη).1
  · have := hP (MvPolynomial.X g)
    simp only [MvPolynomial.aeval_X] at this
    rw [Finset.sum_image hinj]
    have e : ∑ x ∈ s, c (trc (f x)) * trc (f x) g = ∑ η ∈ s, c η * η g :=
      Finset.sum_congr rfl fun η hη => by rw [(hf η hη).2]
    rw [e]
    exact this

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapAevalNab
section
noncomputable section
namespace GlobalTheory.Models.EPolyModel
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

variable {k : Type} [Field k]

theorem map_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a) (g' : Vc k b →ₗ[k] Vc k b)
    (h : ∀ x, φ (g x) = g' (φ x)) (x : Vc k a) : φ (nab g x) = nab g' (φ x) := by
  rw [nab_apply_eq, nab_apply_eq, map_smul, map_sub, h]

theorem map_aeval_nab {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (f : Polynomial k) (x : Vc k a) :
    φ (Polynomial.aeval (nab g) f x) = Polynomial.aeval (nab g') f (φ x) := by
  induction f using Polynomial.induction_on generalizing x with
  | C c =>
    simp only [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact φ.map_smul_of_tower c x
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial m c ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (Polynomial.aeval (nab g')), Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, map_nab φ g g' h]

theorem comap {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k b)) (s : ℤ)
    (hN : EPoly g' N s) : EPoly g (N.comap (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, fun x hx => ?_⟩
  have h1 := hN (φ x) hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  change φ _ ∈ N
  rwa [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem map {a b : ℕ} (φ : Vc k a →ₗ[k⸨X⸩] Vc k b) (g : Vc k a →ₗ[k] Vc k a)
    (g' : Vc k b →ₗ[k] Vc k b) (h : ∀ x, φ (g x) = g' (φ x)) (N : Submodule k⟦X⟧ (Vc k a)) (s : ℤ)
    (hN : EPoly g N s) : EPoly g' (N.map (φ.restrictScalars k⟦X⟧)) s := by
  obtain ⟨f, hf, hN⟩ := hN
  refine ⟨f, hf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := hN x hx
  rw [mem_sh_iff_smul_mem] at h1 ⊢
  refine ⟨_, h1, ?_⟩
  change φ _ = _ • nab g' (Polynomial.aeval (nab g') f (φ x))
  rw [map_smul, map_nab φ g g' h, map_aeval_nab φ g g' h]

theorem model_ePoly : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T3 l →
    ∀ (A : Ob k G) (N : Lats k n A.m), M.Model A N → ∀ i, Dt.ty i = LType.Bd →
      EPoly ((F.D A).γ i) (N i) (Dt.wst i + 1) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h3 A N hN i hi
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := hN
  have oB := M.base_obj B Nb hB
  have o1 := F.obj_sub A₁ B j hj hji oB
  have oA := F.obj_quot A₁ A p hp hps o1
  exact map _ _ _ (F.map_γ A₁ A p o1 oA hp i) _ _
    (comap _ _ _ (F.map_γ A₁ B j o1 oB hj i) _ _ (M.base_e h1 h3 B Nb hB i hi))

end GlobalTheory.Models.EPolyModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddle
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem exact_of_finrank_add {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (h0 : p ∘ₗ f = 0)
    (hd : Module.finrank K V = Module.finrank K U + Module.finrank K W) : Function.Exact f p := by
  rw [LinearMap.exact_iff]
  have hle : LinearMap.range f ≤ LinearMap.ker p := by
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, h0, LinearMap.zero_apply]
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top] at hrn
  have hrf := LinearMap.finrank_range_of_inj hf
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem finrank_add_of_exact {K U V W : Type*} [Field K] [AddCommGroup U] [Module K U] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K V] (f : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hf : Function.Injective f) (hp : Function.Surjective p) (he : Function.Exact f p) :
    Module.finrank K V = Module.finrank K U + Module.finrank K W := by
  rw [LinearMap.exact_iff] at he
  have hrn := LinearMap.finrank_range_add_finrank_ker p
  rw [he, LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.finrank_range_of_inj hf] at hrn
  omega

theorem DFun.map_exact_middle {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k))
    (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (hB : F.Obj B) (hf : IsHom A B f) (hp : IsHom B C p)
    (hi : Function.Injective f) (hs : Function.Surjective p) (he : Function.Exact f p) (i : ZMod n) :
    Function.Exact (F.map A B f i) (F.map B C p i) := by
  have hA : F.Obj A := F.obj_sub A B f hf hi hB
  have hC : F.Obj C := F.obj_quot B C p hp hs hB
  have hd := finrank_add_of_exact f p hi hs he
  simp only [Module.finrank_fin_fun] at hd
  have hpf : p ∘ₗ f = 0 := LinearMap.ext fun x => he.apply_apply_eq_zero x
  have h0hom : IsHom A C (0 : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) := fun g x => by simp
  have hcomp : F.map B C p i ∘ₗ F.map A B f i = 0 := by
    rw [← F.map_comp A B C f p hA hB hC hf hp i, hpf]
    refine LinearMap.ext fun x => ?_
    have h := F.map_smul A C 0 0 hA hC h0hom i x
    simpa using h
  refine exact_of_finrank_add (F.map A B f i) (F.map B C p i) (F.map_inj A B f hA hB hf hi i)
    (F.map_surj B C p hB hC hp hs i) hcomp ?_
  simp only [Vc, Module.finrank_fin_fun]
  exact hd

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCommutantValuationDecomposition
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory.ValDecomp

section Abstract
variable {R : Type*} [CommRing R]

end Abstract
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp
section Abstract2
variable {R : Type*} [CommRing R]

end Abstract2
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp
section Mat
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

end Mat
end GlobalTheory.ValDecomp

namespace GlobalTheory.ValDecomp

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem exists_pow_smul_entries_norm_le_one {ϖ : E} (h1 : ‖ϖ‖ < 1)
    (c : Matrix (Fin n) (Fin n) E) : ∃ k : ℕ, ∀ i j, ‖(ϖ ^ k • c) i j‖ ≤ 1 := by
  set B : ℝ := 1 + ∑ i, ∑ j, ‖c i j‖
  have hB : 0 < B := by positivity
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hB) h1
  refine ⟨k, fun i j => ?_⟩
  have hij : ‖c i j‖ ≤ B := by
    have h := (Finset.single_le_sum (f := fun j => ‖c i j‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖c i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))
    linarith
  rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_pow]
  calc ‖ϖ‖ ^ k * ‖c i j‖ ≤ B⁻¹ * B := mul_le_mul hk.le hij (norm_nonneg _) (inv_pos.2 hB).le
    _ = 1 := inv_mul_cancel₀ hB.ne'

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem inv_mul_comm_of_mul_comm' {x N : Matrix (Fin n) (Fin n) E} (hx : IsUnit x.det)
    (h : x * N = N * x) : x⁻¹ * N = N * x⁻¹ := by
  calc x⁻¹ * N = x⁻¹ * (N * x) * x⁻¹ := by
        rw [mul_assoc, mul_assoc, Matrix.mul_nonsing_inv x hx, mul_one]
    _ = x⁻¹ * (x * N) * x⁻¹ := by rw [h]
    _ = N * x⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul x hx, one_mul]

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem norm_det_le_one_of_entries_norm_le_one' {x : Matrix (Fin n) (Fin n) E}
    (hx : ∀ i j, ‖x i j‖ ≤ 1) : ‖x.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp only [h, one_smul, Units.neg_smul, norm_neg, norm_prod] <;>
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hx _ _

variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ} in
private theorem inv_entries_norm_le_one_of_norm_det_one {x : Matrix (Fin n) (Fin n) E}
    (hx : ∀ i j, ‖x i j‖ ≤ 1) (hd : ‖x.det‖ = 1) : ∀ i j, ‖x⁻¹ i j‖ ≤ 1 := by
  intro i j
  rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, norm_mul, Ring.inverse_eq_inv', norm_inv,
    hd, inv_one, one_mul, Matrix.adjugate_apply]
  apply norm_det_le_one_of_entries_norm_le_one'
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs <;> simp
  · exact hx _ _

theorem _root_.GlobalTheory.ValDecomp.valuation_decomp : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (N : Matrix (Fin n) (Fin n) E) (ϖ : E), 0 < ‖ϖ‖ → ‖ϖ‖ < 1 → (∀ x y : Matrix (Fin n) (Fin n) E, x * N = N * x → y * N = N * y → x * y = y * x) → (∀ y : Matrix (Fin n) (Fin n) E, y * N = N * y → (∀ i j, ‖y i j‖ ≤ 1) → ∃ e a : Matrix (Fin n) (Fin n) E, e * N = N * e ∧ a * N = N * a ∧ (∀ i j, ‖e i j‖ ≤ 1 ∧ ‖a i j‖ ≤ 1) ∧ e * e = e ∧ ‖(y * e + (1 - e)).det‖ = 1 ∧ y * (1 - e) = ϖ • a) → ∀ c : Matrix (Fin n) (Fin n) E, IsUnit c → c * N = N * c → ∃ e₁ e₂ e₃ u a₂ a₃ : Matrix (Fin n) (Fin n) E, (e₁ * N = N * e₁ ∧ e₂ * N = N * e₂ ∧ e₃ * N = N * e₃ ∧ u * N = N * u ∧ a₂ * N = N * a₂ ∧ a₃ * N = N * a₃) ∧ (∀ i j, ‖e₁ i j‖ ≤ 1 ∧ ‖e₂ i j‖ ≤ 1 ∧ ‖e₃ i j‖ ≤ 1 ∧ ‖u i j‖ ≤ 1 ∧ ‖a₂ i j‖ ≤ 1 ∧ ‖a₃ i j‖ ≤ 1) ∧ ‖u.det‖ = 1 ∧ e₁ * e₁ = e₁ ∧ e₂ * e₂ = e₂ ∧ e₃ * e₃ = e₃ ∧ e₁ * e₂ = 0 ∧ e₁ * e₃ = 0 ∧ e₂ * e₃ = 0 ∧ e₁ + e₂ + e₃ = 1 ∧ c * e₁ = u * e₁ ∧ c * e₂ = ϖ • (a₂ * e₂) ∧ c⁻¹ * e₃ = ϖ • (a₃ * e₃) := by
  intro E _ _ n N ϖ h0 h1 hcomm hdec c hc hcN
  have hϖ : ϖ ≠ 0 := norm_pos_iff.1 h0
  have hpow : ∀ k : ℕ, ‖ϖ ^ k‖ ≤ 1 := fun k => by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) h1.le
  have hone : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 :=
    fun i j => _root_.GlobalTheory.UnitDiscAlg.integ_one i j
  let S := Subalgebra.centralizer E ({N} : Set (Matrix (Fin n) (Fin n) E))
  have memS : ∀ {x : Matrix (Fin n) (Fin n) E}, x * N = N * x → x ∈ S := fun hx => by
    rw [Subalgebra.mem_centralizer_iff]; rintro g rfl; exact hx.symm
  have ofS : ∀ {x : Matrix (Fin n) (Fin n) E}, x ∈ S → x * N = N * x := fun hx =>
    ((Subalgebra.mem_centralizer_iff E).1 hx N rfl).symm
  letI : CommRing S := { (inferInstance : Ring S) with
    mul_comm := fun x y => Subtype.ext (hcomm x y (ofS x.2) (ofS y.2)) }
  have toM : ∀ {X Y : S}, X = Y → (X : Matrix (Fin n) (Fin n) E) = Y := fun h => congrArg _ h
  have hscal : ∀ r : E, (r • (1 : Matrix (Fin n) (Fin n) E)) * N = N * (r • 1) := fun r => by
    rw [smul_one_mul, Matrix.mul_smul, mul_one]
  let Pp : S := ⟨ϖ • 1, memS (hscal ϖ)⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_entries_norm_le_one h1 c
  induction k generalizing c with
  | zero =>
    have hc0 : ∀ i j, ‖c i j‖ ≤ 1 := by simpa using hk
    obtain ⟨e, a, heN, haN, hea, hee, hdet, hca⟩ := hdec c hcN hc0
    have he : ∀ i j, ‖e i j‖ ≤ 1 := fun i j => (hea i j).1
    let C : S := ⟨c, memS hcN⟩
    let Ee : S := ⟨e, memS heN⟩
    let A : S := ⟨a, memS haN⟩
    have re : Ee * Ee = Ee := Subtype.ext hee
    have rca : C * (1 - Ee) = Pp * A :=
      Subtype.ext (show c * (1 - e) = (ϖ • 1) * a by rw [smul_one_mul]; exact hca)
    refine ⟨e, 1 - e, 0, c * e + (1 - e), a, 0, ⟨heN, ofS (1 - Ee).2, by simp,
      ofS (C * Ee + (1 - Ee)).2, haN, by simp⟩, fun i j => ⟨he i j,
      _root_.GlobalTheory.UnitDiscAlg.integ_sub hone he i j, by simp,
      _root_.GlobalTheory.UnitDiscAlg.integ_add (_root_.GlobalTheory.UnitDiscAlg.integ_mul hc0 he)
        (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j, (hea i j).2, by simp⟩, hdet, hee,
      toM (by linear_combination re : (1 - Ee) * (1 - Ee) = 1 - Ee), by simp,
      toM (by linear_combination (-1 : S) * re : Ee * (1 - Ee) = 0), by simp, by simp,
      by abel, toM (by linear_combination (1 - C) * re : C * Ee = (C * Ee + (1 - Ee)) * Ee),
      ?_, by simp⟩
    have h := toM (by linear_combination (1 - Ee) * rca - C * re :
      C * (1 - Ee) = Pp * (A * (1 - Ee)))
    rw [← smul_one_mul]; exact h
  | succ k ih =>
    have hyN : (ϖ ^ (k + 1) • c) * N = N * (ϖ ^ (k + 1) • c) :=
      (show Commute c N from hcN).smul_left _
    obtain ⟨e, a, heN, haN, hea, hee, hdet, hya⟩ := hdec _ hyN hk
    have he : ∀ i j, ‖e i j‖ ≤ 1 := fun i j => (hea i j).1
    have ha : ∀ i j, ‖a i j‖ ≤ 1 := fun i j => (hea i j).2
    have hcd : IsUnit c.det := (Matrix.isUnit_iff_isUnit_det c).1 hc
    have hciN : c⁻¹ * N = N * c⁻¹ := inv_mul_comm_of_mul_comm' hcd hcN
    let C : S := ⟨c, memS hcN⟩
    let Ci : S := ⟨c⁻¹, memS hciN⟩
    let Ee : S := ⟨e, memS heN⟩
    let Pk : S := ⟨ϖ ^ k • 1, memS (hscal _)⟩
    have re : Ee * Ee = Ee := Subtype.ext hee
    have r1 : C * Ci = 1 := Subtype.ext (Matrix.mul_nonsing_inv c hcd)
    have hsplit : ϖ ^ (k + 1) • c = (ϖ • 1) * (ϖ ^ k • 1) * c := by
      rw [smul_one_mul, smul_mul_assoc, smul_one_mul, smul_smul, ← pow_succ']
    have hzN : (ϖ ^ (k + 1) • c * e + (1 - e)) * N = N * (ϖ ^ (k + 1) • c * e + (1 - e)) := by
      rw [hsplit]; exact ofS (Pp * Pk * C * Ee + (1 - Ee)).2
    have hzint : ∀ i j, ‖(ϖ ^ (k + 1) • c * e + (1 - e)) i j‖ ≤ 1 :=
      _root_.GlobalTheory.UnitDiscAlg.integ_add (_root_.GlobalTheory.UnitDiscAlg.integ_mul hk he)
        (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he)
    have hzd : IsUnit (ϖ ^ (k + 1) • c * e + (1 - e)).det :=
      isUnit_iff_ne_zero.2 fun h => by rw [h, norm_zero] at hdet; exact zero_ne_one hdet
    have hw := inv_entries_norm_le_one_of_norm_det_one hzint hdet
    have hwN := inv_mul_comm_of_mul_comm' hzd hzN
    let W : S := ⟨_, memS hwN⟩
    have rwz : (Pp * Pk * C * Ee + (1 - Ee)) * W = 1 := Subtype.ext (show
      ((ϖ • 1) * (ϖ ^ k • 1) * c * e + (1 - e)) * (ϖ ^ (k + 1) • c * e + (1 - e))⁻¹ = 1 by
        rw [← hsplit]; exact Matrix.mul_nonsing_inv _ hzd)
    have hA : Ci * Ee = Pp * Pk * (Ee * W) := by
      linear_combination (-(Ci * Ee)) * rwz + (Pp * Pk * W - Ci * W) * re
        + (Pp * Pk * Ee ^ 2 * W) * r1
    have ha' : ϖ ^ k • (c * (1 - e)) = a := smul_right_injective _ hϖ
      (show ϖ • (ϖ ^ k • (c * (1 - e))) = ϖ • a by
        rw [← hya, smul_smul, ← pow_succ', smul_mul_assoc])
    have hc'int : ∀ i j, ‖(ϖ ^ k • (c * (1 - e) + e)) i j‖ ≤ 1 := by
      rw [smul_add, ha']
      exact _root_.GlobalTheory.UnitDiscAlg.integ_add ha (_root_.GlobalTheory.UnitDiscAlg.integ_smul (hpow k) he)
    have rcd : (C * (1 - Ee) + Ee) * (Ci * (1 - Ee) + Ee) = 1 := by
      linear_combination (1 - Ee) * r1 + (C * Ci - C - Ci + 1) * re
    have hmat : (c * (1 - e) + e) * (c⁻¹ * (1 - e) + e) = 1 := toM rcd
    have hunit : IsUnit (c * (1 - e) + e) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hmat)
    have hinv : (c * (1 - e) + e)⁻¹ = c⁻¹ * (1 - e) + e := Matrix.inv_eq_right_inv hmat
    obtain ⟨f₁, f₂, f₃, u, b₂, b₃, ⟨h1N, h2N, h3N, huN, hb2N, hb3N⟩, hint, hu, h11, h22, h33,
      h12, h13, h23, hsum, hc1, hc2, hc3⟩ := ih _ hunit (ofS (C * (1 - Ee) + Ee).2) hc'int
    rw [hinv] at hc3
    have hF1 : ∀ i j, ‖f₁ i j‖ ≤ 1 := fun i j => (hint i j).1
    have hF2 : ∀ i j, ‖f₂ i j‖ ≤ 1 := fun i j => (hint i j).2.1
    have hF3 : ∀ i j, ‖f₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.1
    have hB3 : ∀ i j, ‖b₃ i j‖ ≤ 1 := fun i j => (hint i j).2.2.2.2.2
    let F1 : S := ⟨f₁, memS h1N⟩
    let F2 : S := ⟨f₂, memS h2N⟩
    let F3 : S := ⟨f₃, memS h3N⟩
    let U : S := ⟨u, memS huN⟩
    let B2 : S := ⟨b₂, memS hb2N⟩
    let B3 : S := ⟨b₃, memS hb3N⟩
    have s11 : F1 * F1 = F1 := Subtype.ext h11
    have s22 : F2 * F2 = F2 := Subtype.ext h22
    have s33 : F3 * F3 = F3 := Subtype.ext h33
    have s12 : F1 * F2 = 0 := Subtype.ext h12
    have s13 : F1 * F3 = 0 := Subtype.ext h13
    have s23 : F2 * F3 = 0 := Subtype.ext h23
    have ssum : F1 + F2 + F3 = 1 := Subtype.ext hsum
    have sc1 : (C * (1 - Ee) + Ee) * F1 = U * F1 := Subtype.ext hc1
    have sc2 : (C * (1 - Ee) + Ee) * F2 = Pp * (B2 * F2) := Subtype.ext
      (show (c * (1 - e) + e) * f₂ = (ϖ • 1) * (b₂ * f₂) by rw [smul_one_mul]; exact hc2)
    have sc3 : (Ci * (1 - Ee) + Ee) * F3 = Pp * (B3 * F3) := Subtype.ext
      (show (c⁻¹ * (1 - e) + e) * f₃ = (ϖ • 1) * (b₃ * f₃) by rw [smul_one_mul]; exact hc3)
    refine ⟨f₁ * (1 - e), f₂ * (1 - e), f₃ * (1 - e) + e, u, b₂,
      b₃ * (1 - e) + (ϖ ^ k • 1) * (e * (ϖ ^ (k + 1) • c * e + (1 - e))⁻¹),
      ⟨ofS (F1 * (1 - Ee)).2, ofS (F2 * (1 - Ee)).2, ofS (F3 * (1 - Ee) + Ee).2, huN, hb2N,
        ofS (B3 * (1 - Ee) + Pk * (Ee * W)).2⟩,
      fun i j => ⟨_root_.GlobalTheory.UnitDiscAlg.integ_mul hF1 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j,
        _root_.GlobalTheory.UnitDiscAlg.integ_mul hF2 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he) i j,
        _root_.GlobalTheory.UnitDiscAlg.integ_add
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul hF3 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he)) he i j,
        (hint i j).2.2.2.1, (hint i j).2.2.2.2.1,
        _root_.GlobalTheory.UnitDiscAlg.integ_add
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul hB3 (_root_.GlobalTheory.UnitDiscAlg.integ_sub hone he))
          (_root_.GlobalTheory.UnitDiscAlg.integ_mul (_root_.GlobalTheory.UnitDiscAlg.integ_smul (hpow k) hone)
            (_root_.GlobalTheory.UnitDiscAlg.integ_mul he hw)) i j⟩, hu,
      toM (by linear_combination (1 - Ee) ^ 2 * s11 + F1 * re :
        F1 * (1 - Ee) * (F1 * (1 - Ee)) = F1 * (1 - Ee)),
      toM (by linear_combination (1 - Ee) ^ 2 * s22 + F2 * re :
        F2 * (1 - Ee) * (F2 * (1 - Ee)) = F2 * (1 - Ee)),
      toM (by linear_combination (1 - Ee) ^ 2 * s33 + (1 - F3) * re :
        (F3 * (1 - Ee) + Ee) * (F3 * (1 - Ee) + Ee) = F3 * (1 - Ee) + Ee),
      toM (by linear_combination (1 - Ee) ^ 2 * s12 : F1 * (1 - Ee) * (F2 * (1 - Ee)) = 0),
      toM (by linear_combination (1 - Ee) ^ 2 * s13 - F1 * re :
        F1 * (1 - Ee) * (F3 * (1 - Ee) + Ee) = 0),
      toM (by linear_combination (1 - Ee) ^ 2 * s23 - F2 * re :
        F2 * (1 - Ee) * (F3 * (1 - Ee) + Ee) = 0),
      toM (by linear_combination (1 - Ee) * ssum :
        F1 * (1 - Ee) + F2 * (1 - Ee) + (F3 * (1 - Ee) + Ee) = 1),
      toM (by linear_combination (1 - Ee) * sc1 - (C * F1 - F1) * re :
        C * (F1 * (1 - Ee)) = U * (F1 * (1 - Ee))), ?_, ?_⟩
    · have h := toM (by linear_combination (1 - Ee) * sc2 - (C * F2 - F2) * re :
        C * (F2 * (1 - Ee)) = Pp * (B2 * (F2 * (1 - Ee))))
      rw [← smul_one_mul]; exact h
    · have h := toM (by
        linear_combination (1 - Ee) * sc3 + hA
          + (F3 - Ci * F3 - Pp * B3 * F3 + Pp * B3 + Pp * Pk * W * F3 - Pp * Pk * W) * re :
        Ci * (F3 * (1 - Ee) + Ee) = Pp * ((B3 * (1 - Ee) + Pk * (Ee * W)) * (F3 * (1 - Ee) + Ee)))
      rw [← smul_one_mul]; exact h

end GlobalTheory.ValDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbc
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_obj_and_abc : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  intro k G _ _ l n _ _ _ R F r Dt M A N h
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := h
  have oB : F.Obj B := M.base_obj B Nb hB
  have o1 : F.Obj A₁ := F.obj_sub A₁ B j hj hji oB
  have oA : F.Obj A := F.obj_quot A₁ A p hp hps o1
  obtain ⟨h1, h2, h3⟩ := M.base_abc B Nb hB
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.phiGammaModule_saturation_theorem R (F.D B) (F.D A₁) (F.map A₁ B j)
    (F.map_inj A₁ B j o1 oB hj hji) (F.map_φ A₁ B j o1 oB hj) (F.map_γ A₁ B j o1 oB hj)
    Dt.w Dt.wst Nb h1 h2 h3
  exact ⟨oA, GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective R (F.D A₁) (F.D A) (F.map A₁ A p)
    (F.map_surj A₁ A p o1 oA hp hps) (F.map_φ A₁ A p o1 oA hp) (F.map_γ A₁ A p o1 oA hp)
    Dt.w Dt.wst (F.pre A₁ B j Nb) s1 s2 s3⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem ModTh.model_push_of_surjective {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n A.m) (hp : IsHom A B p)
    (hs : Function.Surjective p) (hN : M.Model A N) : M.Model B (F.push A B p N) := by
  obtain ⟨C, Nb, A₁, j, q, hb, hj, hji, hq, hqs, rfl⟩ := hN
  have hC : F.Obj C := M.base_obj C Nb hb
  have h1 : F.Obj A₁ := F.obj_sub A₁ C j hj hji hC
  have hA : F.Obj A := F.obj_quot A₁ A q hq hqs h1
  have hB : F.Obj B := F.obj_quot A B p hp hs hA
  refine ⟨C, Nb, A₁, j, p ∘ₗ q, hb, hj, hji, fun g x => ?_, hs.comp hqs, ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hq g x, hp g]
  · funext i
    simp only [DFun.push]
    rw [F.map_comp A₁ A B q p h1 hA hB hq hp i, ← Submodule.map_comp]
    rfl

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
section
open GlobalTheory.UnitDiscAlg

namespace GlobalTheory

theorem norm_det_le_one_of_entries_le_one :
    ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ)
      (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  intro E _ _ n x hx
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have hp : ‖∏ i, x (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hx _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul, norm_neg]; exact hp

end GlobalTheory
end

