module

public import Development.EtaleCohomology.DivisorCycles.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0048

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.AlgStruct2
section
open Matrix
namespace LateralTheory.DivDb
namespace AlgStruct₂

variable {C : Type} [Field C] {N n : ℕ} {p : Fin n → Mat C N}

theorem pp (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq
theorem pp' (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, pp hp]
theorem pq (hp : Sys p) {i j : Fin n} (h : i ≠ j) : p i * p j = 0 := hp.1.ortho h
theorem pq' (hp : Sys p) {i j : Fin n} (h : i ≠ j) (X : Mat C N) : p i * (p j * X) = 0 := by
  rw [← mul_assoc, pq hp h, zero_mul]

theorem corner_comm (hp : Sys p) (X : Mat C N) (i m : Fin n) :
    p i * X * p i * p m = p m * (p i * X * p i) := by
  by_cases h : m = i
  · rw [h]; simp only [mul_assoc, pp hp, pp' hp]
  · simp only [mul_assoc, pq hp (Ne.symm h), pq' hp h, mul_zero]

theorem decomp (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, p i * a * p j * (p j * b * p k) := by
  have h1 : a * b = a * (∑ j, p j) * b := by rw [hp.1.complete, mul_one]
  rw [h1]; simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, pp' hp]

theorem expand (hp : Sys p) (Y : Mat C N) : Y = ∑ i, ∑ j, p i * Y * p j := by
  have h : Y = (∑ i, p i) * Y * (∑ j, p j) := by rw [hp.1.complete, one_mul, mul_one]
  conv_lhs => rw [h]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]

def S (p : Fin n → Mat C N) (g : Submodule C (Mat C N)) : Set (Mat C N) :=
  {a | (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i}

variable {g : Submodule C (Mat C N)}

theorem S_add {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a + b ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_add, add_mul]; exact g.add_mem (ha.1 i j h) (hb.1 i j h)
  · obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
    exact ⟨c + c', by rw [mul_add, add_mul, hc, hc', add_smul]⟩

theorem S_alg (hp : Sys p) (r : C) : algebraMap C (Mat C N) r ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ⟨r, ?_⟩⟩
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pq hp h, smul_zero]
    exact g.zero_mem
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pp hp]

theorem S_mul (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a * b ∈ S p g := by
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [decomp hp]
    refine g.sum_mem fun j _ => ?_
    by_cases hji : j = i
    · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i
      have e : p i * (p i * b * p k) = p i * b * p k := by simp only [mul_assoc, pp' hp]
      rw [hc, smul_mul_assoc, e]; exact g.smul_mem _ (hb.1 _ _ hik)
    by_cases hjk : j = k
    · rw [hjk]; obtain ⟨c, hc⟩ := hb.2 k
      have e : p i * a * p k * p k = p i * a * p k := by simp only [mul_assoc, pp hp]
      rw [hc, mul_smul_comm, e]; exact g.smul_mem _ (ha.1 _ _ hik)
    have h := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j k hjk)
    have z : p j * b * p k * (p i * a * p j) = 0 := by
      simp only [mul_assoc, pq' hp (Ne.symm hik), mul_zero]
    rwa [z, sub_zero] at h
  · have key : ∀ j, ∃ c : C, p i * a * p j * (p j * b * p i) = c • p i := by
      intro j
      by_cases hji : j = i
      · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
        exact ⟨c * c', by rw [hc, hc', smul_mul_assoc, mul_smul_comm, pp hp, smul_smul]⟩
      have hZ := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j i hji)
      have e1 : p i * a * p j * (p j * b * p i) = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc]
      have e2 : p j * b * p i * (p i * a * p j) = p j * (b * p i * (p i * a)) * p j := by
        simp only [mul_assoc]
      rw [e1, e2] at hZ
      have hc : ∀ m, (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) * p m =
          p m * (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) := by
        intro m; rw [sub_mul, mul_sub, corner_comm hp, corner_comm hp]
      obtain ⟨c, hcZ⟩ := hdiag _ hZ hc i
      refine ⟨c, ?_⟩
      rw [e1, ← hcZ, sub_mul]
      have f1 : p i * (a * p j * (p j * b)) * p i * p i = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc, pp hp]
      have f2 : p j * (b * p i * (p i * a)) * p j * p i = 0 := by
        simp only [mul_assoc, pq hp hji, mul_zero]
      rw [f1, f2, sub_zero]
    choose f hf using key
    exact ⟨∑ j, f j, by rw [decomp hp, Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => hf j⟩

theorem S_of_mem (hp : Sys p) (hoff : ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {Y : Mat C N} (hY : Y ∈ g) : Y ∈ S p g := by
  refine ⟨hoff Y hY, fun i => ?_⟩
  set D := ∑ k, p k * Y * p k with hDdef
  have hsplit : Y = D + ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
    conv_lhs => rw [expand hp Y]
    rw [hDdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have hD : D ∈ g := by
    have : D = Y - ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
      rw [eq_sub_iff_add_eq, ← hsplit]
    rw [this]
    refine g.sub_mem hY (g.sum_mem fun k _ => g.sum_mem fun j hj => hoff Y hY k j ?_)
    exact Ne.symm (Finset.ne_of_mem_erase hj)
  have hcomm : ∀ m, D * p m = p m * D := by
    intro m; rw [hDdef, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => corner_comm hp Y k m
  obtain ⟨c, hc⟩ := hdiag D hD hcomm i
  refine ⟨c, ?_⟩
  rw [← hc, hDdef, Finset.sum_mul, Finset.sum_eq_single i]
  · simp only [mul_assoc, pp hp]
  · intro k _ hki; simp only [mul_assoc, pq hp hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

def Sa (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) :
    Subalgebra C (Mat C N) where
  carrier := S p g
  mul_mem' := S_mul hp hbr hdiag
  add_mem' := S_add
  algebraMap_mem' := S_alg hp

theorem AlgStruct_of : AlgStruct := by
  intro C _ N n p g hp hbr hoff hdiag a ha
  have hle : Algebra.adjoin C (g : Set (Mat C N)) ≤ Sa hp hbr hdiag :=
    Algebra.adjoin_le fun Y hY => S_of_mem hp hoff hdiag hY
  exact hle ha

end AlgStruct₂
end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.BigCorner2
section
open Matrix

namespace LateralTheory.DivDb.BigCorner₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N n : ℕ}

def gens (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) : Set (Mat C N) :=
  {x | ∃ a ∈ A, ∃ g, x = a * (ρ g : Mat C N)}

lemma rmul (ρ : Γ →* GL (Fin N) C) (g h : Γ) : (ρ (g * h) : Mat C N) = ρ g * ρ h := by simp

lemma rone (ρ : Γ →* GL (Fin N) C) : (ρ 1 : Mat C N) = 1 := by simp

lemma rinv (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g : Mat C N) * ρ g⁻¹ = 1 := by
  rw [← rmul, mul_inv_cancel, rone]

lemma rinv' (ρ : Γ →* GL (Fin N) C) (g : Γ) : (ρ g⁻¹ : Mat C N) * ρ g = 1 := by
  rw [← rmul, inv_mul_cancel, rone]

lemma span_mul (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A)
    (x y : Mat C N) (hx : x ∈ Submodule.span C (gens ρ A)) (hy : y ∈ Submodule.span C (gens ρ A)) :
    x * y ∈ Submodule.span C (gens ρ A) :=
  _root_.UpperTheory.Reformulated.B.NormalizedMatrixSpan.span_mul ρ A hN x y hx hy

lemma one_mem_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) :
    (1 : Mat C N) ∈ Submodule.span C (gens ρ A) :=
  Submodule.subset_span ⟨1, A.one_mem, 1, by rw [rone, one_mul]⟩

noncomputable def RR (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) :
    Subalgebra C (Mat C N) :=
  (Submodule.span C (gens ρ A)).toSubalgebra (one_mem_span ρ A) (span_mul ρ A hN)

lemma mem_RR {ρ : Γ →* GL (Fin N) C} {A : Subalgebra C (Mat C N)} {hN : Normd ρ A} {x : Mat C N} :
    x ∈ RR ρ A hN ↔ x ∈ Submodule.span C (gens ρ A) := Iff.rfl

lemma corner_gen (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ gens ρ A) : ∃ c : C, p i * x * p i = c • p i := by
  obtain ⟨a, ha, g, rfl⟩ := hx
  by_cases h : p i * a * (ρ g : Mat C N) * p i = 0
  · exact ⟨0, by rw [zero_smul, ← mul_assoc, h]⟩
  · obtain ⟨w, hw, hpw⟩ := hyp g i ⟨a, ha, h⟩
    have ha' : (ρ g⁻¹ : Mat C N) * a * ρ g ∈ A := by simpa using hN g⁻¹ a ha
    have e1 : a * (ρ g : Mat C N) = ρ g * ((ρ g⁻¹ : Mat C N) * a * ρ g) := by
      simp only [← mul_assoc, rinv, one_mul]
    obtain ⟨c, hc⟩ := hC.2 _ (A.mul_mem hw ha') i
    refine ⟨c, ?_⟩
    rw [e1, ← mul_assoc, ← mul_assoc, hpw, ← hc]; simp only [mul_assoc]

lemma corner_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N)
    (hC : Corner A p) (hN : Normd ρ A)
    (hyp : ∀ g i, (∃ a ∈ A, p i * a * (ρ g : Mat C N) * p i ≠ 0) → ∃ w ∈ A, p i * (ρ g : Mat C N) = p i * w)
    (i : Fin n) {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∃ c : C, p i * x * p i = c • p i := by
  induction hx using Submodule.span_induction with
  | mem x hx' => exact corner_gen ρ A p hC hN hyp i hx'
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨c, hc⟩ := hu; obtain ⟨d, hd⟩ := hv
    exact ⟨c + d, by rw [mul_add, add_mul, hc, hd, add_smul]⟩
  | smul c u _ hu =>
    obtain ⟨d, hd⟩ := hu
    exact ⟨c * d, by rw [mul_smul_comm, smul_mul_assoc, hd, smul_smul]⟩

lemma normd_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hN : Normd ρ A) (g : Γ)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) :
    (ρ g : Mat C N) * x * (ρ g⁻¹ : Mat C N) ∈ Submodule.span C (gens ρ A) := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, h, rfl⟩ := hx'
    refine Submodule.subset_span ⟨(ρ g : Mat C N) * a * ρ g⁻¹, hN g a ha, g * h * g⁻¹, ?_⟩
    have key : (ρ g⁻¹ : Mat C N) * (ρ g * (ρ h * ρ g⁻¹)) = ρ h * ρ g⁻¹ := by
      rw [← mul_assoc, rinv', one_mul]
    rw [rmul, rmul]; simp only [mul_assoc, key]
  | zero => simp
  | add u v _ _ hu hv => rw [mul_add, add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hu

lemma keeps_span (ρ : Γ →* GL (Fin N) C) (A : Subalgebra C (Mat C N)) (hK : Keeps ρ A)
    (W : Submodule C (Fin N → C)) (hW : ∀ g, ∀ v ∈ W, (ρ g : Mat C N) *ᵥ v ∈ W)
    {x : Mat C N} (hx : x ∈ Submodule.span C (gens ρ A)) : ∀ v ∈ W, x *ᵥ v ∈ W := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨a, ha, g, rfl⟩ := hx'
    intro v hv
    rw [← Matrix.mulVec_mulVec]
    exact hK W hW a ha _ (hW g v hv)
  | zero => intro v _; simp
  | add u v _ _ hu hv => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hu w hw) (hv w hw)
  | smul c u _ hu => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hu w hw)

end LateralTheory.DivDb.BigCorner₂

open LateralTheory.DivDb.BigCorner₂ in
theorem LateralTheory.DivDb.BigCorner₂.BigCorner_of : LateralTheory.DivDb.BigCorner := by
  intro Γ C _ _ N n ρ A p hC hN hK hyp
  refine ⟨RR ρ A hN, fun g => ?_, ⟨fun i => ?_, fun a ha i => ?_⟩, fun g a ha => ?_, fun W hW a ha => ?_⟩
  · exact mem_RR.2 (Submodule.subset_span ⟨1, A.one_mem, g, (one_mul _).symm⟩)
  · exact mem_RR.2 (Submodule.subset_span ⟨p i, hC.1 i, 1, by rw [rone, mul_one]⟩)
  · exact corner_span ρ A p hC hN hyp i (mem_RR.1 ha)
  · exact mem_RR.2 (normd_span ρ A hN g (mem_RR.1 ha))
  · exact keeps_span ρ A hK W hW (mem_RR.1 ha)
end

-- bundled from Development.EtaleCohomology.DivisorCycles.ChainPf
section
open Matrix MvPolynomial
namespace LateralTheory.DivDb.ChainPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N M : ℕ}

noncomputable def lin (φ : Mat C N →ₗ[C] Mat C M) (q : Fin M × Fin M) : MP C N :=
  ∑ r : Fin N × Fin N, MvPolynomial.C (φ (Matrix.single r.1 r.2 1) q.1 q.2) * X r

theorem sum_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ∑ r : Fin N × Fin N, φ (Matrix.single r.1 r.2 1) q.1 q.2 * x r.1 r.2 = φ x q.1 q.2 := by
  have hx : x = ∑ r : Fin N × Fin N, x r.1 r.2 • Matrix.single r.1 r.2 (1 : C) := by
    rw [Fintype.sum_prod_type]
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp [Matrix.smul_single]
  conv_rhs => rw [hx]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun r _ => mul_comm _ _

theorem ev_lin (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (q : Fin M × Fin M) :
    ev x (lin φ q) = φ x q.1 q.2 := by
  rw [← sum_lin φ x q]; simp [ev, lin]

theorem dAt_lin (φ : Mat C N →ₗ[C] Mat C M) (x Y : Mat C N) (q : Fin M × Fin M) :
    dAt (lin φ q) x Y = φ Y q.1 q.2 := by
  rw [← sum_lin φ Y q]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dAt, lin, map_sum, Derivation.leibniz, pderiv_X, pderiv_C, smul_zero, add_zero, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [ev, Pi.single_apply, Finset.sum_ite_eq']

theorem ev_bind (φ : Mat C N →ₗ[C] Mat C M) (x : Mat C N) (f : MP C M) :
    ev x (bind₁ (lin φ) f) = ev (φ x) f := by
  show eval₂Hom (RingHom.id C) _ (bind₁ (lin φ) f) = eval₂Hom (RingHom.id C) _ f
  rw [eval₂Hom_bind₁]
  congr 2; funext q; exact ev_lin φ x q

theorem dAt_add (f g : MP C N) (x Y : Mat C N) : dAt (f + g) x Y = dAt f x Y + dAt g x Y := by
  simp [dAt, ev, add_mul, Finset.sum_add_distrib]

theorem dAt_mul (f g : MP C N) (x Y : Mat C N) :
    dAt (f * g) x Y = ev x f * dAt g x Y + ev x g * dAt f x Y := by
  simp only [dAt, Derivation.leibniz, smul_eq_mul, ev, map_add (f := _), map_mul, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

theorem dAt_C (a : C) (x Y : Mat C N) : dAt (MvPolynomial.C a : MP C N) x Y = 0 := by
  simp [dAt, ev]

theorem chain_of : Chain := by
  intro C _ N M φ f
  refine ⟨bind₁ (lin φ) f, fun x => ?_, ?_⟩
  · exact ev_bind φ x f
  · induction f using MvPolynomial.induction_on with
    | C a => intro x Y; simp [dAt_C]
    | add f g hf hg => intro x Y; rw [map_add (f := _), dAt_add, dAt_add, hf, hg]
    | mul_X f q hf =>
      intro x Y
      rw [map_mul, bind₁_X_right, dAt_mul, dAt_mul, hf, dAt_lin, ev_lin]
      rw [ev_bind]
      simp [dAt, ev, pderiv_X, Pi.single_apply]

end LateralTheory.DivDb.ChainPf

theorem LateralTheory.DivDb.Chain_of : LateralTheory.DivDb.Chain := LateralTheory.DivDb.ChainPf.chain_of
end

-- bundled from Development.EtaleCohomology.DivisorCycles.CoeMulInv
section
open Matrix

namespace LateralTheory.DivDb.EnvStab₂
open LateralTheory.DivDb

variable {Γ C : Type} [Group Γ] [Field C] {N : ℕ}

theorem ev_X (x : Mat C N) (q : Fin N × Fin N) : ev x (MvPolynomial.X q) = x q.1 q.2 := by
  simp [ev]

theorem mem_img (ρ : Γ →* GL (Fin N) C) (h : Γ) : ((ρ h : GL (Fin N) C) : Mat C N) ∈ (img ρ ⊤ : Set (Mat C N)) := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map]
  exact ⟨h, by simp, rfl⟩

theorem img_cases (ρ : Γ →* GL (Fin N) C) {x : Mat C N} (hx : x ∈ (img ρ ⊤ : Set (Mat C N))) :
    ∃ h : Γ, ((ρ h : GL (Fin N) C) : Mat C N) = x := by
  simp only [img, SetLike.mem_coe, Submonoid.mem_map] at hx
  obtain ⟨h, _, rfl⟩ := hx
  exact ⟨h, rfl⟩

theorem coe_mul_inv (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

theorem coe_inv_mul (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) * ((ρ g : GL (Fin N) C) : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

def conjL (G G' : Mat C N) : Mat C N →ₗ[C] Mat C N where
  toFun x := G * x * G'
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by simp

theorem lie_conj (hC : Chain) (ρ : Γ →* GL (Fin N) C) (g : Γ) (Y : Mat C N) (hY : Y ∈ lie ρ) :
    ((ρ g : GL (Fin N) C) : Mat C N) * Y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N) ∈ lie ρ := by
  intro f hf
  obtain ⟨f', hev, hd⟩ := hC C N N (conjL (ρ g : Mat C N) (ρ g⁻¹ : Mat C N)) f
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev]
    apply hf
    have : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) (ρ h : Mat C N)
        = ((ρ (g * h * g⁻¹) : GL (Fin N) C) : Mat C N) := by
      simp [conjL, map_mul, Units.val_mul]
    rw [this]; exact mem_img ρ _
  have h1 : conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) 1 = 1 := by
    simp only [conjL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_one]; exact coe_mul_inv ρ g
  have := hd 1 Y
  rw [h1] at this
  show dAt f 1 (conjL (C := C) (N := N) (ρ g : Mat C N) (ρ g⁻¹ : Mat C N) Y) = 0
  rw [← this]
  exact hY f' hf'

theorem normd (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Normd ρ (env ρ) := by
  intro g a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin (lie_conj hC ρ g x hx)
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, coe_mul_inv]
    exact Subalgebra.smul_mem _ (Subalgebra.one_mem _) r
  | add x y _ _ hx hy =>
    rw [Matrix.mul_add, Matrix.add_mul]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have : ((ρ g : GL (Fin N) C) : Mat C N) * (x * y) * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)
        = (((ρ g : GL (Fin N) C) : Mat C N) * x * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) *
          (((ρ g : GL (Fin N) C) : Mat C N) * y * ((ρ g⁻¹ : GL (Fin N) C) : Mat C N)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc ((ρ g⁻¹ : GL (Fin N) C) : Mat C N), coe_inv_mul, Matrix.one_mul]
    rw [this]; exact Subalgebra.mul_mem _ hx hy

def lamL (ℓ : Module.Dual C (Fin N → C)) (v : Fin N → C) : Mat C N →ₗ[C] Mat C 1 where
  toFun x := Matrix.of fun _ _ => ℓ (x *ᵥ v)
  map_add' x y := by ext; simp [Matrix.add_mulVec]
  map_smul' c x := by ext; simp [Matrix.smul_mulVec]

theorem lie_keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) (W : Submodule C (Fin N → C))
    (hW : ∀ g, ∀ v ∈ W, ((ρ g : GL (Fin N) C) : Mat C N) *ᵥ v ∈ W) (Y : Mat C N) (hY : Y ∈ lie ρ)
    (v : Fin N → C) (hv : v ∈ W) : Y *ᵥ v ∈ W := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro ℓ hℓ
  rw [Submodule.mem_dualAnnihilator] at hℓ
  obtain ⟨f', hev, hd⟩ := hC C N 1 (lamL ℓ v) (MvPolynomial.X (0, 0))
  have hf' : f' ∈ Van (img ρ ⊤ : Set (Mat C N)) := by
    intro x hx
    obtain ⟨h, rfl⟩ := img_cases ρ hx
    rw [hev, ev_X]
    simp only [lamL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
    exact hℓ _ (hW h v hv)
  have h0 := hY f' hf'
  rw [hd] at h0
  simpa [dAt, lamL, ev, MvPolynomial.pderiv_X, Fintype.sum_unique, Pi.single_apply, Prod.ext_iff, Fin.fin_one_eq_zero] using h0

theorem keeps (hC : Chain) (ρ : Γ →* GL (Fin N) C) : Keeps ρ (env ρ) := by
  intro W hW a ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact fun v hv => lie_keeps hC ρ W hW x hx v hv
  | algebraMap r =>
    intro v hv
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
    exact W.smul_mem r hv
  | add x y _ _ hx hy =>
    intro v hv; rw [Matrix.add_mulVec]; exact W.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy =>
    intro v hv; rw [← Matrix.mulVec_mulVec]; exact hx _ (hy v hv)

end LateralTheory.DivDb.EnvStab₂

namespace LateralTheory.DivDb

theorem EnvStab_of (hC : Chain) : EnvStab := fun _ _ _ _ _ ρ =>
  ⟨EnvStab₂.normd hC ρ, EnvStab₂.keeps hC ρ⟩

end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.CycleCountPf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.CycleCountPf
open LateralTheory.DivDb

def CycSpec : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)), Sys p → IsUnit y → (∀ j, y * p j = p (π j) * y) → Disj y π p →
  ∃ l : Fin n → C, Function.Injective l ∧ ∀ j, y.charpoly.IsRoot (l j) ∧
    ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0

def FixScal : Prop := ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N n : ℕ) (p : Fin n → Mat C N)
  (y : Mat C N) (π : Equiv.Perm (Fin n)) (l : Fin n → C), Sys p → (∀ j, y * p j = p (π j) * y) → Deg n y →
  Disj y π p → Function.Injective l →
  (∀ j, ∃ v : Fin N → C, v ≠ 0 ∧ y *ᵥ v = l j • v ∧ ∀ k, ¬ π.SameCycle j k → p k *ᵥ v = 0) →
  ∀ i, π i = i → ∃ c : C, y * p i = c • p i

theorem CycleCount_of (h1 : CycSpec) (h2 : FixScal) : CycleCount := by
  intro C _ _ _ N n p y π hp hy hyp hdeg hd
  obtain ⟨l, hl, hr⟩ := h1 C N n p y π hp hy hyp hd
  exact ⟨⟨l, hl, fun j => (hr j).1⟩, h2 C N n p y π l hp hyp hdeg hd hl (fun j => (hr j).2)⟩

end LateralTheory.DivDb.CycleCountPf
end

-- bundled from Development.EtaleCohomology.DivisorCycles.FinSpecLie
section
namespace LateralTheory.Fin.SpecLie
theorem etale_special_point_exists_of_key : LateralTheory.DivDb.SpecPt := by
  apply LateralTheory.DivDb.SpecPtPf.SpecPt_of
theorem etale_spectrum_lie_algebra_instance : LateralTheory.DivDb.SpecLie := by
  apply LateralTheory.DivDb.SpecLiePf.SpecLie_of <;> first | exact etale_special_point_exists_of_key
theorem intersectionNumber_baseChange : LateralTheory.DivDb.SpecLie := etale_spectrum_lie_algebra_instance
end LateralTheory.Fin.SpecLie
end

