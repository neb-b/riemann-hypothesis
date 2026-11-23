module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsLeftInvariantPolySeparatingCoset
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.CosetSep

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def vanC (S : Set (Matrix ι ι ℂ)) : Ideal (MvPolynomial (ι × ι) ℂ) where
  carrier := {f | ∀ g ∈ S, evC f g = 0}
  add_mem' := by
    intro a b ha hb g hg
    have h1 := ha g hg
    have h2 := hb g hg
    simp only [evC] at h1 h2 ⊢
    rw [map_add (f := _), h1, h2, add_zero]
  zero_mem' := by
    intro g _
    simp [evC]
  smul_mem' := by
    intro c a ha g hg
    have h1 := ha g hg
    simp only [evC] at h1 ⊢
    rw [smul_eq_mul, map_mul, h1, mul_zero]


omit [DecidableEq ι] in
lemma evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) : evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC] at hp hq ⊢
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p ij hp =>
    simp only [evC] at hp ⊢
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in
lemma exists_rtr (h : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    ∃ f' : MvPolynomial (ι × ι) ℂ, ∀ z, evC f' z = evC f (z * h) := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a, fun z => by simp [evC]⟩
  | add p q hp hq =>
    obtain ⟨p', hp⟩ := hp
    obtain ⟨q', hq⟩ := hq
    refine ⟨p' + q', fun z => ?_⟩
    have h1 := hp z
    have h2 := hq z
    simp only [evC] at h1 h2 ⊢
    rw [map_add (f := _), map_add (f := _), h1, h2]
  | mul_X p ij hp =>
    obtain ⟨p', hp⟩ := hp
    refine ⟨p' * ∑ k, MvPolynomial.X (ij.1, k) * MvPolynomial.C (h k ij.2), fun z => ?_⟩
    have h1 := hp z
    simp only [evC] at h1 ⊢
    rw [map_mul, map_mul, h1]
    congr 1
    simp [Matrix.mul_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma evC_map (f : MvPolynomial (ι × ι) ℚ) (g : Matrix ι ι ℂ) :
    evC (MvPolynomial.map (algebraMap ℚ ℂ) f) g = ev f g := by
  simp only [evC, ev]
  rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]

lemma mem_of_forall_vanC {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {z : Matrix ι ι ℂ}
    (hz : ∀ f ∈ vanC Γ, evC f z = 0) : z ∈ Γ := by
  apply hΓ.closed
  intro f hf
  rw [← evC_map]
  apply hz
  intro g hg
  rw [evC_map]
  exact hf g hg

lemma vanC_sup_eq_top {Γ : Set (Matrix ι ι ℂ)} (hΓ : IsQGroup Γ) {y : Matrix ι ι ℂ} (hy : y.det = 1)
    (hyΓ : y ∉ Γ) : vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  set z : Matrix ι ι ℂ := Matrix.of fun i j => x (i, j) with hz
  have key : ∀ f ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ), evC f z = 0 := by
    intro f hf
    have h1 := (MvPolynomial.mem_vanishingIdeal_singleton_iff x f).1 (hle hf)
    simpa [evC, hz] using h1
  have hzΓ : z ∈ Γ := mem_of_forall_vanC hΓ fun f hf => key f (Ideal.mem_sup_left hf)
  have hyy : y * y.adjugate = 1 := by rw [Matrix.mul_adjugate, hy, one_smul]
  have hyy' : y.adjugate * y = 1 := by rw [Matrix.adjugate_mul, hy, one_smul]
  have hwΓ : z * y.adjugate ∈ Γ := by
    refine mem_of_forall_vanC hΓ fun f hf => ?_
    obtain ⟨f', hf'⟩ := exists_rtr y.adjugate f
    rw [← hf']
    refine key f' (Ideal.mem_sup_right ?_)
    rintro _ ⟨g, hg, rfl⟩
    rw [hf', mul_assoc, hyy, mul_one]
    exact hf g hg
  apply hyΓ
  have h1 : (z * y.adjugate).adjugate * (z * y.adjugate) = 1 := by
    rw [Matrix.adjugate_mul, hΓ.det_eq _ hwΓ, one_smul]
  have h2 : y = (z * y.adjugate).adjugate * z := by
    calc y = (z * y.adjugate).adjugate * (z * y.adjugate) * y := by rw [h1, one_mul]
      _ = (z * y.adjugate).adjugate * (z * (y.adjugate * y)) := by simp only [mul_assoc]
      _ = _ := by rw [hyy', mul_one]
  rw [h2]
  exact hΓ.mul_mem _ (hΓ.adj_mem _ hwΓ) _ hzΓ

end GlobalTheory.ClassFin.CosetSep

namespace GlobalTheory.ClassFin


open CosetSep in
theorem exists_isInv_evC_one_ne : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsQGroup Γ → IsReynolds Γ Rey → ∀ y : Matrix ι ι ℂ, y.det = 1 → y ∉ Γ → ∃ f, IsInv Γ f ∧ evC f 1 ≠ evC f y := by
  intro ι _ _ Γ Rey hΓ hR y hy hyΓ
  have htop := vanC_sup_eq_top hΓ hy hyΓ
  have h1 : (1 : MvPolynomial (ι × ι) ℂ) ∈ vanC Γ ⊔ vanC ((fun g => g * y) '' Γ) := by
    rw [htop]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
  have hRa : Rey a ∈ vanC Γ := by
    refine hR.stable ((vanC Γ).restrictScalars ℂ) ?_ a ha
    intro g hg f hf h hh
    rw [evC_ltr]
    exact hf _ (hΓ.mul_mem _ hg _ hh)
  have hRb : Rey b ∈ vanC ((fun g => g * y) '' Γ) := by
    refine hR.stable ((vanC ((fun g => g * y) '' Γ)).restrictScalars ℂ) ?_ b hb
    rintro g hg f hf _ ⟨h, hh, rfl⟩
    rw [evC_ltr, ← mul_assoc]
    exact hf _ ⟨g * h, hΓ.mul_mem _ hg _ hh, rfl⟩
  have hR1 : Rey 1 = 1 := hR.fix 1 (fun g _ z => by simp [evC])
  have hsum : Rey a + Rey b = 1 := by rw [← map_add (f := _), hab, hR1]
  refine ⟨Rey a, hR.inv a, ?_⟩
  have e1 : evC (Rey a) 1 = 0 := hRa 1 hΓ.one_mem
  have e2 : evC (Rey b) y = 0 := hRb y ⟨1, hΓ.one_mem, one_mul y⟩
  have e3 : evC (Rey a) y = 1 := by
    have h := congrArg (fun f => evC f y) hsum
    simp only [evC] at h e2 ⊢
    rw [map_add (f := _), e2, add_zero, map_one] at h
    exact h
  rw [e1, e3]
  exact zero_ne_one

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRationalCoordPolynomialBaseChange
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_eq {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (a : F) (k : β) :
    b.repr (algebraMap F A a) k = algebraMap ℚ R (ω.repr a k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) :=
    fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F))
      ((algebraMap R A).comp (algebraMap ℚ R))) q
  have hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i := by
    conv_lhs => rw [← ω.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb,
      Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]
  rw [hsum, b.repr_sum_self]

private theorem basis_repr_mul_of_basis_eq_algebraMap {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (u v : A)
    (k : β) : b.repr (u * v) k =
      ∑ i, ∑ j, b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
  have e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k
      = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
    intro i j
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul,
      repr_algebraMap_of_basis_eq ω b hb]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]
  exact Finset.sum_comm

theorem exists_coord_polynomial : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  intro F β _ _ _ _ ω τ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨fun k => Q1 k + Q2 k, ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_add (f := _), map_add (f := _), Finsupp.add_apply, map_add (f := _), h1 R A b hb x k, h2 R A b hb x k]
  | mul_X p n hp =>
    obtain ⟨Q1, h1⟩ := hp
    refine ⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) *
      MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducible
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma projection_comm_of_mapsTo {p q : Submodule ℂ V} (h : IsCompl p q)
    (T : V →ₗ[ℂ] V) (hp : ∀ v ∈ p, T v ∈ p) (hq : ∀ v ∈ q, T v ∈ q) (v : V) :
    p.projection q h (T v) = T (p.projection q h v) := by
  have hv : v ∈ p ⊔ q := by
    rw [h.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have e1 := (Submodule.IsCompl.projection_eq_self_iff h a).mpr ha
  have e2 := (Submodule.IsCompl.projection_eq_self_iff h (T a)).mpr (hp a ha)
  have e3 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr hb
  have e4 := (Submodule.IsCompl.projection_apply_eq_zero_iff h).mpr (hq b hb)
  simp only [map_add (f := _), e1, e2, e3, e4, add_zero]

variable {V : Type} [AddCommGroup V] [Module ℂ V] in
private lemma sub_projection_mem' {p q : Submodule ℂ V} (h : IsCompl p q) (v : V) :
    v - p.projection q h v ∈ q := by
  rw [← Submodule.IsCompl.projection_apply_eq_zero_iff h, map_sub,
    (Submodule.IsCompl.projection_eq_self_iff h _).mpr
      (Submodule.IsCompl.projection_apply_mem h v), sub_self]


variable {V : Type} [AddCommGroup V] [Module ℂ V] in
theorem _root_.GlobalTheory.ClassFin.exists_reynolds_of_completelyReducible (V : Type) [AddCommGroup V] [Module ℂ V]
    (S : Set (V →ₗ[ℂ] V)) :
    (∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
      ∃ U' : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U', (s : V → V) v ∈ U') ∧ IsCompl U U') →
    ∃ Rey : V →ₗ[ℂ] V,
      (∀ v : V, ∀ s ∈ S, (s : V → V) ((Rey : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, (∀ s ∈ S, (s : V → V) v = v) → (Rey : V → V) v = v) ∧
      (∀ v : V, ∀ s ∈ S, (Rey : V → V) ((s : V → V) v) = (Rey : V → V) v) ∧
      (∀ v : V, v - (Rey : V → V) v ∈
        Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}) ∧
      (∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v : V, (T : V → V) ((s : V → V) v) = (s : V → V) ((T : V → V) v)) →
        ∀ v : V, (Rey : V → V) ((T : V → V) v) = (T : V → V) ((Rey : V → V) v)) ∧
      ∀ U : Submodule ℂ V, (∀ s ∈ S, ∀ v ∈ U, (s : V → V) v ∈ U) →
        ∀ v ∈ U, (Rey : V → V) v ∈ U := by
  intro hS
  let W : Submodule ℂ V := Submodule.span ℂ {x : V | ∃ s ∈ S, ∃ w : V, x = (s : V → V) w - w}
  have hWgen : ∀ s ∈ S, ∀ w, (s : V → V) w - w ∈ W := fun s hs w =>
    Submodule.subset_span ⟨s, hs, w, rfl⟩
  have hWT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v ∈ W, T v ∈ W := by
    intro T hT v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, hs, w, rfl⟩ := hx
      rw [map_sub, hT s hs]
      exact hWgen s hs (T w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  have hWS : ∀ s ∈ S, ∀ v ∈ W, (s : V → V) v ∈ W := by
    intro s hs v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s', hs', w, rfl⟩ := hx
      have e : s (s' w - w) = (s (s' w) - s' w) + (s' w - w) - (s w - w) := by
        rw [map_sub]
        abel
      rw [e]
      exact W.sub_mem (W.add_mem (hWgen s hs _) (hWgen s' hs' w)) (hWgen s hs w)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact W.add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul]
      exact W.smul_mem a hx
  let Fix : Submodule ℂ V :=
    { carrier := {x | ∀ s ∈ S, (s : V → V) x = x}
      add_mem' := fun ha hb s hs => by simp [map_add (f := _), ha s hs, hb s hs]
      zero_mem' := fun s _ => map_zero s
      smul_mem' := fun c x hx s hs => by simp [map_smul, hx s hs] }
  have hFixW : ∀ v ∈ Fix, v ∈ W → v = 0 := by
    intro v hvF hvW
    have hZS : ∀ s ∈ S, ∀ x ∈ Fix ⊓ W, (s : V → V) x ∈ Fix ⊓ W := by
      intro s hs x hx
      rw [hx.1 s hs]
      exact hx
    obtain ⟨Z', hZ'S, hZZ'⟩ := hS (Fix ⊓ W) hZS
    let Q := (Fix ⊓ W).projection Z' hZZ'
    have hQS : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hZZ' s (hZS s hs) (hZ'S s hs) x
    have hQW : W ≤ LinearMap.ker Q := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, w, rfl⟩
      have hmem := Submodule.IsCompl.projection_apply_mem hZZ' w
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, hQS s hs, Q]
      rw [hmem.1 s hs, sub_self]
    have h1 : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hZZ' v).mpr ⟨hvF, hvW⟩
    have h2 : Q v = 0 := hQW hvW
    rw [← h1, h2]
  obtain ⟨W', hW'S, hWW'⟩ := hS W hWS
  have hW'Fix : ∀ v ∈ W', v ∈ Fix := by
    intro v hv s hs
    have h1 : (s : V → V) v - v ∈ W := hWgen s hs v
    have h2 : (s : V → V) v - v ∈ W' := W'.sub_mem (hW'S s hs v hv) hv
    exact sub_eq_zero.mp (Submodule.disjoint_def.mp hWW'.disjoint _ h1 h2)
  let P := W'.projection W hWW'.symm
  have hPfix : ∀ v ∈ Fix, P v = v := by
    intro v hv
    have hd : v - P v ∈ Fix := Fix.sub_mem hv (hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v))
    exact (sub_eq_zero.mp (hFixW _ hd (sub_projection_mem' hWW'.symm v))).symm
  have hPT : ∀ T : V →ₗ[ℂ] V, (∀ s ∈ S, ∀ v, T (s v) = s (T v)) → ∀ v, P (T v) = T (P v) := by
    intro T hT v
    refine projection_comm_of_mapsTo hWW'.symm T (fun x hx => ?_) (hWT T hT) v
    have hTx : T x ∈ Fix := fun s hs => by rw [← hT s hs, hW'Fix x hx s hs]
    rw [← hPfix _ hTx]
    exact Submodule.IsCompl.projection_apply_mem _ _
  refine ⟨P, fun v s hs => hW'Fix _ (Submodule.IsCompl.projection_apply_mem _ v) s hs,
    fun v hv => hPfix v hv, fun v s hs => ?_, fun v => sub_projection_mem' hWW'.symm v,
    hPT, fun U hU v hv => ?_⟩
  · have h0 : P ((s : V → V) v - v) = 0 :=
      (Submodule.IsCompl.projection_apply_eq_zero_iff _).mpr (hWgen s hs v)
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  · obtain ⟨U', hU'S, hUU'⟩ := hS U hU
    let Q := U.projection U' hUU'
    have hQ : ∀ s ∈ S, ∀ x, Q (s x) = s (Q x) := fun s hs x =>
      projection_comm_of_mapsTo hUU' s (hU s hs) (hU'S s hs) x
    have hQv : Q v = v := (Submodule.IsCompl.projection_eq_self_iff hUU' v).mpr hv
    have e := hPT Q hQ v
    rw [hQv] at e
    rw [e]
    exact Submodule.IsCompl.projection_apply_mem hUU' _

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingEquivNeOfTranscendental
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_ringEquiv_ne_of_transcendental :
    ∀ z : ℂ, Transcendental ℚ z → ∃ σ : ℂ ≃+* ℂ, σ z ≠ z := by
  intro z hz
  have hind : AlgebraicIndepOn ℚ id ({z} : Set ℂ) := by
    show AlgebraicIndependent ℚ _
    exact algebraicIndependent_unique_type_iff.2 hz
  obtain ⟨t, hzt, ht⟩ := exists_isTranscendenceBasis_superset hind
  let v : t → ℂ := (↑)
  let i0 : t := ⟨z, hzt rfl⟩
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis v ht
  let f : t → MvPolynomial t ℚ := fun i => if i = i0 then -MvPolynomial.X i else MvPolynomial.X i
  have hcomp : (MvPolynomial.aeval f).comp (MvPolynomial.aeval f) =
      AlgHom.id ℚ (MvPolynomial t ℚ) := by
    apply MvPolynomial.algHom_ext
    intro i
    by_cases h : i = i0 <;> simp [f, h]
  let neg := AlgEquiv.ofAlgHom (MvPolynomial.aeval f) (MvPolynomial.aeval f) hcomp hcomp
  let e : Algebra.adjoin ℚ (Set.range v) ≃+* Algebra.adjoin ℚ (Set.range v) :=
    ht.1.aevalEquiv.symm.toRingEquiv.trans (neg.toRingEquiv.trans ht.1.aevalEquiv.toRingEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ e, ?_⟩
  have h1 : algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ (ht.1.aevalEquiv (MvPolynomial.X i0)) = z := by
    rw [AlgebraicIndependent.algebraMap_aevalEquiv, MvPolynomial.aeval_X]
  have key : IsAlgClosure.equivOfEquiv ℂ ℂ e z = -z := by
    conv_lhs => rw [← h1]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.symm_apply_apply]
    rw [AlgebraicIndependent.algebraMap_aevalEquiv]
    simp [neg, f, v, i0]
  rw [key]
  intro h
  have h0 : z = 0 := by linear_combination (-1 / 2 : ℂ) * h
  rw [h0] at hz
  exact hz isAlgebraic_zero

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRingHomAdicCompletionUnder
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem GlobalTheory.QNorm.exists_ringHom_adicCompletion_under :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (w : HeightOneSpectrum (𝓞 E)),
      ∃ φ : (w.under (𝓞 F)).adicCompletion F →+* w.adicCompletion E,
        ∀ x : F, φ (algebraMap F ((w.under (𝓞 F)).adicCompletion F) x) =
          algebraMap E (w.adicCompletion E) (algebraMap F E x) := by
  intro K L _ _ _ _ _ w
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have hc := (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver K L (w.under (𝓞 K))
    w).continuous
  refine ⟨((HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal ((w.under (𝓞 K)).valuation K)) (WithVal (w.valuation L))) hc)).comp
      (HeightOneSpectrum.adicCompletion.equiv K (w.under (𝓞 K))).toRingHom, fun x => ?_⟩
  apply HeightOneSpectrum.adicCompletion.ext
  exact UniformSpace.Completion.mapRingHom_coe hc (WithVal.toVal _ x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem finite_valuation_ne_one (F : Type) [Field F] [NumberField F] (x : Fˣ) :
    {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}.Finite := by
  refine ((HeightOneSpectrum.Support.finite (𝓞 F) (x : F)).union
    (HeightOneSpectrum.Support.finite (𝓞 F) ((x : F)⁻¹))).subset ?_
  intro v hv
  have hv' : v.valuation F (x : F) ≠ 1 := hv
  have h0 : v.valuation F (x : F) ≠ 0 := by
    rw [Ne, map_eq_zero]
    exact x.ne_zero
  rcases lt_or_gt_of_ne hv' with h | h
  · right
    show 1 < v.valuation F ((x : F)⁻¹)
    rw [map_inv₀]
    exact one_lt_inv₀ (zero_lt_iff.mpr h0) |>.mpr h
  · left
    exact h

theorem exists_superset_mem_sUnits :
    ∀ (F : Type) [Field F] [NumberField F] (X : Finset Fˣ)
      (S₀ : Finset (HeightOneSpectrum (𝓞 F))),
      ∃ S, S₀ ⊆ S ∧ ∀ S', S ⊆ S' → ∀ x ∈ X, x ∈ sUnits F S' := by
  intro F _ _ X S₀
  classical
  have hT : (⋃ x ∈ X, {v : HeightOneSpectrum (𝓞 F) | v.valuation F (x : F) ≠ 1}).Finite :=
    X.finite_toSet.biUnion fun x _ => finite_valuation_ne_one F x
  refine ⟨S₀ ∪ hT.toFinset, Finset.subset_union_left, ?_⟩
  intro S' hS' x hx
  rw [mem_sUnits]
  intro v hv
  by_contra h
  apply hv
  apply hS'
  apply Finset.mem_union_right
  rw [Set.Finite.mem_toFinset]
  exact Set.mem_biUnion hx h

end GlobalTheory.QNorm
end

