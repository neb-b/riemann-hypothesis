module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FormalPointSubstitutionSeriesValueAtTwoPoints
section
noncomputable section

open MvPowerSeries

namespace GlobalTheory.FrameBiextId

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}


variable (k d) in
def Q (n : ℕ) : AddSubgroup (Pt k n d) where
  carrier := {p | ∀ i, constantCoeff (p i) = 0}
  add_mem' := fun ha hb i => by rw [Pi.add_apply, map_add (f := _), ha i, hb i, add_zero]
  zero_mem' := fun _ => map_zero _
  neg_mem' := fun ha i => by rw [Pi.neg_apply, map_neg, ha i, neg_zero]

variable {n l : ℕ}

def gen (j : Fin n) : Q (k := k) (d := d) n := ⟨pt k d j, CZ.pt j⟩

theorem czQ (b : Fin n → Q (k := k) (d := d) l) : CZ (fun j => (b j).1) := by
  intro j i
  exact (b j).2 i

def sb (b : Fin n → Q (k := k) (d := d) l) : PS k n d →+* PS k l d := evHom (czQ b)

theorem sb_apply (b : Fin n → Q (k := k) (d := d) l) (f : PS k n d) : sb b f = ev (fun j => (b j).1) f := by
  unfold sb
  exact evHom_apply (czQ b) f

def sq (b : Fin n → Q (k := k) (d := d) l) : Q (k := k) (d := d) n →+ Q (k := k) (d := d) l where
  toFun p := ⟨fun i => sb b (p.1 i), fun i =>
    (congrArg constantCoeff (sb_apply b _)).trans (constantCoeff_ev (czQ b) (p.2 i))⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)

@[simp] theorem sq_gen (b : Fin n → Q (k := k) (d := d) l) (j : Fin n) : sq b (gen j) = b j := by
  apply Subtype.ext
  funext i
  show sb b (X (j, i)) = (b j).1 i
  rw [sb_apply]
  exact ev_X (czQ b) j i

theorem sb_sb {m : ℕ} (b : Fin n → Q (k := k) (d := d) l) (a : Fin m → Q (k := k) (d := d) n) (f : PS k m d) :
    sb b (sb a f) = sb (fun j => sq b (a j)) f := by
  simp only [sb_apply]
  rw [ev_ev (czQ b) (czQ a)]
  congr 1
  funext j i
  show ev (fun j => (b j).1) ((a j).1 i) = sb b ((a j).1 i)
  rw [sb_apply]

theorem sb_gen (f : PS k n d) : sb gen f = f := by
  rw [sb_apply]
  exact ev_pt f

def E2 (f : PS k 2 d) (u v : Q (k := k) (d := d) n) : PS k n d := sb ![u, v] f

def E3 (f : PS k 3 d) (u v w : Q (k := k) (d := d) n) : PS k n d := sb ![u, v, w] f

@[simp] theorem formalPointSubstitutionSeries_valueAtTwoPoints (b : Fin n → Q (k := k) (d := d) l) (f : PS k 2 d) (u v : Q (k := k) (d := d) n) : sb b (E2 f u v) = E2 f (sq b u) (sq b v) := by
  show sb b (sb ![u, v] f) = sb ![sq b u, sq b v] f
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

@[simp] theorem formalPointSubstitutionSeries_valueAtThreePoints (b : Fin n → Q (k := k) (d := d) l) (f : PS k 3 d) (u v w : Q (k := k) (d := d) n) :
    sb b (E3 f u v w) = E3 f (sq b u) (sq b v) (sq b w) := by
  show sb b (sb ![u, v, w] f) = sb ![sq b u, sq b v, sq b w] f
  have h : (fun j => sq b (![u, v, w] j)) = ![sq b u, sq b v, sq b w] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

theorem formalSeriesValueAtTwoPoints_genericPoints (f : PS k 2 d) : E2 f (gen 0) (gen 1) = f := by
  show sb ![gen 0, gen 1] f = f
  have h : (![gen 0, gen 1] : Fin 2 → Q (k := k) (d := d) 2) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]

theorem formalSeriesValueAtThreePoints_genericPoints (f : PS k 3 d) : E3 f (gen 0) (gen 1) (gen 2) = f := by
  show sb ![gen 0, gen 1, gen 2] f = f
  have h : (![gen 0, gen 1, gen 2] : Fin 3 → Q (k := k) (d := d) 3) = gen := by
    funext j
    fin_cases j <;> rfl
  rw [h, sb_gen]

def ac (A : Q (k := k) (d := d) 1) (u : Q (k := k) (d := d) n) : Q (k := k) (d := d) n := sq ![u] A

@[simp] theorem sq_ac (b : Fin n → Q (k := k) (d := d) l) (A : Q (k := k) (d := d) 1) (u : Q (k := k) (d := d) n) : sq b (ac A u) = ac A (sq b u) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u] (A.1 i)) = sb ![sq b u] (A.1 i)
  have h : (fun j => sq b (![u] j)) = ![sq b u] := by
    funext j
    fin_cases j
    rfl
  rw [sb_sb, h]

theorem formalSeriesValueAtTwoPoints_eq_ev (f : PS k 2 d) (u v : Q (k := k) (d := d) n) : E2 f u v = ev ![u.1, v.1] f := by
  show sb ![u, v] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem formalSeriesValueAtThreePoints_eq_ev (f : PS k 3 d) (u v w : Q (k := k) (d := d) n) : E3 f u v w = ev ![u.1, v.1, w.1] f := by
  show sb ![u, v, w] f = _
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem ac_val (A : Q (k := k) (d := d) 1) (u : Q (k := k) (d := d) n) : (ac A u).1 = comp1 A.1 u.1 := by
  funext i
  show sb ![u] (A.1 i) = ev ![u.1] (A.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j
  rfl

def op (F : Q (k := k) (d := d) 2) (u v : Q (k := k) (d := d) n) : Q (k := k) (d := d) n := sq ![u, v] F

theorem op_val (F : Q (k := k) (d := d) 2) (u v : Q (k := k) (d := d) n) : (op F u v).1 = addOf F.1 u.1 v.1 := by
  funext i
  show sb ![u, v] (F.1 i) = ev ![u.1, v.1] (F.1 i)
  rw [sb_apply]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem sq_op (b : Fin n → Q (k := k) (d := d) l) (F : Q (k := k) (d := d) 2) (u v : Q (k := k) (d := d) n) : sq b (op F u v) = op F (sq b u) (sq b v) := by
  apply Subtype.ext
  funext i
  show sb b (sb ![u, v] (F.1 i)) = sb ![sq b u, sq b v] (F.1 i)
  have h : (fun j => sq b (![u, v] j)) = ![sq b u, sq b v] := by
    funext j
    fin_cases j <;> rfl
  rw [sb_sb, h]

theorem gen_val (j : Fin n) : (gen j : Q (k := k) (d := d) n).1 = pt k d j := rfl

theorem ext_of_trunc {R σ : Type} [CommRing R] [Finite σ] {f g : MvPowerSeries σ R}
    (h : ∀ m : ℕ, Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ (m + 1)) (truncTotal (m + 1) f) =
      Ideal.Quotient.mk _ (truncTotal (m + 1) g)) : f = g := by
  ext e
  have h1 := h (Finsupp.degree e)
  rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff'] at h1
  have h2 := h1 e (Nat.lt_succ_self _)
  rw [MvPolynomial.coeff_sub, coeff_truncTotal _ (Nat.lt_succ_self _),
    coeff_truncTotal _ (Nat.lt_succ_self _), sub_eq_zero] at h2
  exact h2

end GlobalTheory.FrameBiextId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocalizedModuleSubtype
section
namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DualFamily

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.herm_one_eq {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = ∑ a, x a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.herm
  simp [Matrix.one_apply]

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.herm_one_symm {n : ℕ} (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 y x) := by
  rw [_root_.GlobalTheory.DualFamily.herm_one_eq, _root_.GlobalTheory.DualFamily.herm_one_eq]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, IsCMField.complexConj_apply_apply, mul_comm]

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.isIntegral_cc {a : E} (ha : IsIntegral ℤ a) :
    IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.cc a) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  exact ha.map (RingHom.toIntAlgHom (IsCMField.complexConj E).toRingEquiv.toRingHom)


open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.exists_herm_eq {n : ℕ} (f : (Fin n → E) →ₗ[E] E) :
    ∃ w : Fin n → E, ∀ u, f u = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u w := by
  refine ⟨fun a => _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (f fun b => if a = b then 1 else 0), fun u => ?_⟩
  rw [f.pi_apply_eq_sum_univ u, _root_.GlobalTheory.DualFamily.herm_one_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
  rw [IsCMField.complexConj_apply_apply, smul_eq_mul]


open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.eq_zero_of_line {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG) (w : Fin n → E) (hw : ∀ c : E, c • w ∈ Λ) : w = 0 := by
  by_contra h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h
  have htop : Λ.map (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin n => E) j) = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ⟨(x / w j) • w, hw _, ?_⟩
    simp [div_mul_cancel₀ _ hj]
  have : Module.Finite (𝓞 E) E := ⟨by rw [← htop]; exact hfg.map _⟩
  have := Algebra.IsIntegral.of_finite (𝓞 E) E
  exact RingOfIntegers.not_isField E
    (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.DualFamily.span_eq_top {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ := by
  by_contra h
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr h)
  obtain ⟨w, hw⟩ := _root_.GlobalTheory.DualFamily.exists_herm_eq f
  have hline : ∀ c : E, c • w ∈ Λ := fun c => hdual _ fun y hy => by
    have hfy : f y = 0 := LinearMap.mem_ker.mp (hle (Submodule.subset_span hy))
    have hsmul : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (c • w) y = c * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 w y := by
      simp only [_root_.GlobalTheory.DualFamily.herm_one_eq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        mul_assoc]
    rw [hsmul, _root_.GlobalTheory.DualFamily.herm_one_symm w y, ← hw, hfy]
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.cc
    rw [map_zero, mul_zero]
    exact isIntegral_zero
  have hw0 := _root_.GlobalTheory.DualFamily.eq_zero_of_line Λ hfg w hline
  exact hf0 (LinearMap.ext fun u => by simp [hw u, hw0, _root_.GlobalTheory.DualFamily.herm_one_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc])

end DualFamily

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
omit [IsCMField E] in
private lemma exists_linearForm_extend_of_span_eq_univ {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hspan : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (g : Λ →ₗ[𝓞 E] 𝓞 E) :
    ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y : Λ, φ y = g y := by
  obtain ⟨t, htΛ, hts, hli⟩ := exists_linearIndependent E (Λ : Set (Fin n → E))
  let b : Module.Basis t E (Fin n → E) :=
    Module.Basis.mk hli (le_of_eq (by rw [Subtype.range_coe, hts, hspan]))
  have hb : ∀ i, b i ∈ Λ := fun i => by rw [Module.Basis.mk_apply]; exact htΛ i.2
  have := Module.Finite.finite_basis b
  have := Fintype.ofFinite t
  refine ⟨b.constr E fun i => ((g ⟨b i, hb i⟩ : 𝓞 E) : E), fun y => ?_⟩
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ (b.repr y)
  have hd' : ∀ i, ∃ x : 𝓞 E, algebraMap (𝓞 E) E x = (d : 𝓞 E) • b.repr y i :=
    fun i => hd i (Finset.mem_univ _)
  choose a ha using hd'
  have hdy : (d : 𝓞 E) • y = ∑ i, a i • (⟨b i, hb i⟩ : Λ) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, Submodule.coe_sum]
    conv_lhs => rw [← b.sum_repr y]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, ← algebraMap_smul E (a i), ha i, smul_assoc]
  have hg := congrArg (fun z => ((g z : 𝓞 E) : E)) hdy
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul] at hg
  simp only [RingOfIntegers.coe_eq_algebraMap]
  have hd0 : algebraMap (𝓞 E) E d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  apply mul_left_cancel₀ hd0
  rw [hg]
  conv_lhs => rw [← b.sum_repr (y : Fin n → E)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, ha i, smul_eq_mul, Algebra.smul_def]
  ring

open NumberField in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.exists_dual_family {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ.FG)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ, IsIntegral ℤ (_root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)) → x ∈ Λ) :
    Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ ∃ (m : ℕ) (v w : Fin m → Fin n → E),
      (∀ i, v i ∈ Λ) ∧ (∀ i, w i ∈ Λ) ∧ ∀ u : Fin n → E, u = ∑ i, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 u (w i) • v i := by
  have hspan := _root_.GlobalTheory.DualFamily.span_eq_top Λ hfg hdual
  refine ⟨hspan, ?_⟩
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have := Module.finitePresentation_of_finite (𝓞 E) Λ
  have : Module.Projective (𝓞 E) Λ := Module.Flat.projective_of_finitePresentation
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) Λ
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hext : ∀ j : Fin m, ∃ φ : (Fin n → E) →ₗ[E] E, ∀ y (hy : y ∈ Λ), φ y = σ ⟨y, hy⟩ j :=
    fun j => (exists_linearForm_extend_of_span_eq_univ Λ hspan ((LinearMap.proj j).comp σ)).imp
      fun φ h y hy => h ⟨y, hy⟩
  choose φ hφ using hext
  choose w hw using fun j => _root_.GlobalTheory.DualFamily.exists_herm_eq (φ j)
  let v : Fin m → Fin n → E := fun j => (π fun k => if j = k then 1 else 0 : Λ)
  refine ⟨m, v, w, fun j => (π _).2, fun j => hdual _ fun y hy => ?_, fun u => ?_⟩
  · rw [_root_.GlobalTheory.DualFamily.herm_one_symm, ← hw, hφ j y hy]
    exact _root_.GlobalTheory.DualFamily.isIntegral_cc (RingOfIntegers.isIntegral_coe _)
  · have hL : (∑ j, (φ j).smulRight (v j)) = LinearMap.id := by
      refine LinearMap.ext_on hspan fun y hy => ?_
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      have hy' : y = ((π (σ ⟨y, hy⟩) : Λ) : Fin n → E) := by
        rw [← LinearMap.comp_apply, hσ]
        rfl
      conv_rhs => rw [hy', π.pi_apply_eq_sum_univ]
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hφ j y hy, RingOfIntegers.coe_eq_algebraMap, algebraMap_smul]
    have hu := congrArg (fun L : (Fin n → E) →ₗ[E] (Fin n → E) => L u) hL
    simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, hw] at hu
    exact hu.symm

end GlobalTheory
end

