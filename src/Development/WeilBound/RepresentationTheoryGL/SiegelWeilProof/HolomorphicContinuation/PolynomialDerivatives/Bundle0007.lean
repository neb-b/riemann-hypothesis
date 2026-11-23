module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.PartialDerivZeroSecondFamily
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.BoxLeFirstFamily
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC

namespace CoreD

variable {m n : ℕ} {ε : Fin m → Bool}

theorem opMono_add (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (f g : PX m n) :
    opMono t (f + g) = opMono t f + opMono t g := by
  simp [opMono, map_add (f := _), mul_add]

theorem opMono_smul (t : (Fin m × Fin n × Bool) ⊕ (Fin m × Fin n × Bool) →₀ ℕ) (r : ℂ) (f : PX m n) :
    opMono t (r • f) = r • opMono t f := by
  simp [opMono, map_smul, mul_smul_comm]

def opL (s : Sym m n) : Module.End ℂ (PX m n) where
  toFun := op s
  map_add' f g := by simp [op, opMono_add, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by simp [op, opMono_smul, Finset.smul_sum, smul_comm r]

theorem op_eq (s : Sym m n) (T : Finset _) (h : s.support ⊆ T) (f : PX m n) :
    op s f = ∑ t ∈ T, s.coeff t • opMono t f := by
  unfold op
  refine Finset.sum_subset h fun t _ ht => ?_
  rw [mem_support_iff, not_not] at ht
  rw [ht, zero_smul]

theorem op_add_sym (s₁ s₂ : Sym m n) (f : PX m n) : op (s₁ + s₂) f = op s₁ f + op s₂ f := by
  classical
  rw [op_eq (s₁ + s₂) (s₁.support ∪ s₂.support) support_add, op_eq s₁ (s₁.support ∪ s₂.support)
    Finset.subset_union_left, op_eq s₂ (s₁.support ∪ s₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by rw [MvPolynomial.coeff_add, add_smul]

theorem op_smul_sym (s : Sym m n) (r : ℂ) (f : PX m n) : op (r • s) f = r • op s f := by
  classical
  rw [op_eq (r • s) s.support support_smul, op, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ => by rw [coeff_smul, smul_eq_mul, mul_smul]

theorem op_sum_sym {ι : Type*} (F : Finset ι) (g : ι → Sym m n) (f : PX m n) :
    op (∑ i ∈ F, g i) f = ∑ i ∈ F, op (g i) f := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [op]
  | insert a F ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_sym, ih]

theorem box_le_first_family (R : Set (Fin m → ℕ)) : box (n := n) ε R ≤ F1 ε := by
  refine Submodule.span_le.2 fun p ⟨s, hs, _, hp⟩ => ?_
  subst hp
  change monomial s 1 ∈ MvPolynomial.supported ℂ {k | inF1 ε k}
  rw [MvPolynomial.mem_supported, vars_monomial one_ne_zero]
  exact fun k hk => hs k hk

def Ad {V : Submodule ℂ (PX m n)} (K : Module.End ℂ (PX m n)) (KV : Module.End ℂ V) :
    Module.End ℂ (V →ₗ[ℂ] PX m n) where
  toFun h := K ∘ₗ h - h ∘ₗ KV
  map_add' h₁ h₂ := LinearMap.ext fun f => by simp; abel
  map_smul' r h := LinearMap.ext fun f => by simp [smul_sub]

section main

variable (R : Set (Fin m → ℕ)) (hV : ∀ (i j : Fin n), ∀ f ∈ box ε R, KopL ε i j f ∈ box ε R)

def KV (i j : Fin n) : Module.End ℂ (box (n := n) ε R) := (KopL ε i j).restrict (hV i j)

def OmH : Module.End ℂ (box (n := n) ε R →ₗ[ℂ] PX m n) :=
  ∑ ij : Fin n × Fin n, Ad (KopL ε ij.1 ij.2) (KV R hV ij.1 ij.2) * Ad (KopL ε ij.2 ij.1) (KV R hV ij.2 ij.1)

def rr (N : ℕ) : S (n := n) ε N →ₗ[ℂ] (box (n := n) ε R →ₗ[ℂ] PX m n) where
  toFun x := opL x.1 ∘ₗ (box ε R).subtype
  map_add' x y := LinearMap.ext fun f => op_add_sym x.1 y.1 f.1
  map_smul' r x := LinearMap.ext fun f => op_smul_sym x.1 r f.1

variable (hS : SymKComm)
include hS

theorem rr_Om (N : ℕ) (x : S (n := n) ε N) : rr R N (OmS ε N x) = OmH R hV (rr R N x) := by
  refine LinearMap.ext fun f => ?_
  have hf : f.1 ∈ F1 ε := box_le_first_family R f.2
  have hF1 : ∀ (i j : Fin n) (g : box (n := n) ε R), (KopL ε i j g.1) ∈ F1 ε := fun i j g => box_le_first_family R (hV i j g.1 g.2)
  simp only [rr, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, Submodule.coe_subtype, OmH,
    LinearMap.sum_apply, Module.End.mul_apply, opL]
  change op (Om ε x.1) f.1 = _
  rw [Om_apply, op_sum_sym]
  refine Finset.sum_congr rfl fun ij _ => ?_
  have hx : SymbolInFirstFamily ε x.1 := symbol_first_family_of_mem x.2
  have hx' : SymbolInFirstFamily ε (symK ε ij.2 ij.1 x.1) := symbol_first_family_of_mem (symK_mem _ _ x.2)
  rw [hS m n ε ij.1 ij.2 _ hx' f.1 hf, hS m n ε ij.2 ij.1 _ hx f.1 hf,
    hS m n ε ij.2 ij.1 _ hx _ (hF1 ij.1 ij.2 f)]
  rfl

theorem rr_aeval (N : ℕ) (q : Polynomial ℂ) (x : S (n := n) ε N) :
    rr R N (Polynomial.aeval (OmS ε N) q x) = Polynomial.aeval (OmH R hV) q (rr R N x) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial k a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, LinearMap.map_smul_of_tower,
      Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, map_smul]
    congr 1
    induction k generalizing x with
    | zero => simp
    | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, rr_Om R hV hS, pow_succ, Module.End.mul_apply]

end main

theorem aeval_ker {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (v : V) (h : T v = 0)
    (q : Polynomial ℂ) : Polynomial.aeval T q v = q.eval 0 • v := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add q]
  rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply, Module.End.mul_apply, h,
    map_zero, zero_add, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply,
    Polynomial.coeff_zero_eq_eval_zero]

end CoreD


open CoreD in
theorem equivLift_of (hFFT : PositivityTheory.Rg.Sw.FFT) (_hSF : SemiFam) (hD : Dens) (hS : SymKComm) (hI : InvOp)
    (hF : FormFacts) : EquivLift := by
  intro m n ε c hc R t ht htk
  obtain ⟨-, -, -, hF4, hF5⟩ := hF m n ε c hc
  have hadj : ∀ (i j : Fin n) (s u : Sym m n), psi (symK ε i j s) u = psi s (symK ε j i u) := fun i j s u => by
    have := (hF5 i j s u).2
    simpa [psi] using this
  have hV : ∀ (i j : Fin n), ∀ f ∈ box ε (R : Set (Fin m → ℕ)), KopL ε i j f ∈ box ε (R : Set (Fin m → ℕ)) :=
    fun i j f hf => hF4 i j _ f hf
  obtain ⟨s, hs1, hs2⟩ := hD m n ε R t (fun f hf => box_le_first_family _ (ht f hf))
  set N := s.totalDegree
  let x : S (n := n) ε N := ⟨s, mem_S_of hs1⟩
  obtain ⟨q, hq0, hq⟩ := exists_q hadj N
  set y := Polynomial.aeval (OmS ε N) q x with hy
  have ht' : OmH (R : Set (Fin m → ℕ)) hV (t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype) = 0 := by
    rw [OmH, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun ij _ => ?_
    have h0 : Ad (KopL ε ij.2 ij.1) (KV (R : Set (Fin m → ℕ)) hV ij.2 ij.1) (t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype) = 0 := by
      refine LinearMap.ext fun f => ?_
      simp [Ad, KV, LinearMap.restrict_apply, htk ij.2 ij.1 f.1 f.2]
    rw [Module.End.mul_apply, h0, map_zero]
  have hrx : rr (R : Set (Fin m → ℕ)) N x = t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype := by
    refine LinearMap.ext fun f => ?_
    exact hs2 f.1 f.2
  have hry : rr (R : Set (Fin m → ℕ)) N y = t ∘ₗ (box ε (R : Set (Fin m → ℕ))).subtype := by
    rw [hy, rr_aeval _ hV hS, hrx, aeval_ker _ _ ht', hq0, one_smul]
  have hy0 : Om ε y.1 = 0 := congrArg Subtype.val (hq x)
  have hsym : ∀ i j, symK ε i j y.1 = 0 := symK_eq_zero_of_Om hadj _ hy0
  obtain ⟨w, hw, hwf⟩ := hI hFFT m n ε c hc y.1 (symbol_first_family_of_mem y.2) hsym
  refine ⟨w, hw, fun f hf => ?_⟩
  have h1 : op y.1 f = t f := LinearMap.congr_fun hry ⟨f, hf⟩
  rw [← h1, hwf f (box_le_first_family _ hf)]

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.ContractionFirstOperatorAdjoint
section
noncomputable section

open MvPolynomial Finsupp

namespace PositivityTheory.Rg.Sw.LC

namespace CoreC

open PositivityTheory.Rg.Sw G

variable {m n : ℕ}

theorem tA (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * pderiv (b, i, false) h * g) = contr c (h * (X (b, i, true) * pderiv (a, i, true) g)) := by
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (partial_deriv_mem_first_family ε (b, i, false) hh) hg
  have h2 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false] at h1 h2
  rw [h1, h2]

theorem tB (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (b, i, true) * pderiv (a, i, true) h * g) = contr c (h * (X (a, i, false) * pderiv (b, i, false) g)) := by
  have h1 := T1 ε (c := c) (k := (b, i, true)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (partial_deriv_mem_second_family ε (b, i, false) hg)
  simp only [pE_apply, Bool.not_true] at h1 h2
  rw [h1, h2]

theorem tC (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = true) (hb : ε b = false) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    contr c (X (a, i, false) * X (b, i, true) * h * g) =
      ((2 * c : ℝ) : ℂ) ^ 2 * contr c (h * pderiv (b, i, false) (pderiv (a, i, true) g)) := by
  have hbT : inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T1 ε (c := c) (k := (a, i, false)) (by simp [inF1, ha]) (variable_mul_mem_first_family ε hbT hh) hg
  have h2 := T1 ε (c := c) (k := (b, i, true)) hbT hh (partial_deriv_mem_second_family ε (a, i, true) hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [mul_assoc (X (a, i, false)), h1, h2]; ring

theorem tD (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) {a b : Fin m} (ha : ε a = false) (hb : ε b = true) (i : Fin n)
    {h g : PX m n} (hh : h ∈ F1 ε) (hg : g ∈ F2 ε) :
    ((2 * c : ℝ) : ℂ) ^ 2 * contr c (pderiv (b, i, false) (pderiv (a, i, true) h) * g) =
      contr c (h * (X (a, i, false) * X (b, i, true) * g)) := by
  have hbT : ¬ inF1 ε (b, i, true) := by simp [inF1, hb]
  have h1 := T2 ε (c := c) (k := (b, i, false)) (by simp [inF1, hb]) (partial_deriv_mem_first_family ε (a, i, true) hh) hg
  have h2 := T2 ε (c := c) (k := (a, i, true)) (by simp [inF1, ha]) hh (variable_mul_mem_second_family ε hbT hg)
  simp only [pE_apply, Bool.not_false, Bool.not_true] at h1 h2
  rw [pow_two, mul_assoc, h1, h2, mul_assoc]

theorem contraction_first_operator_adjoint (ε : Fin m → Bool) {c : ℝ} (hc : 0 < c) (a b : Fin m) {h g : PX m n} (hh : h ∈ F1 ε)
    (hg : g ∈ F2 ε) : contr c (D1 ε c a b h * g) = -contr c (h * D2 ε c a b g) := by
  have hc2 : ((2 * c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * c) ≠ 0)
  unfold D1 D2
  by_cases hab : ε a = ε b
  · rw [if_pos hab, if_pos hab]
    cases ha : ε a
    · have hb : ε b = false := by rw [← hab, ha]
      simp only [Bool.false_eq_true, if_false]
      rw [Finset.sum_mul, contr_sum, mul_neg, contr_neg, Finset.mul_sum, contr_sum, neg_neg]
      exact Finset.sum_congr rfl fun i _ => tB ε hc ha hb i hh hg
    · have hb : ε b = true := by rw [← hab, ha]
      simp only [if_true]
      rw [neg_mul, contr_neg, Finset.sum_mul, contr_sum, Finset.mul_sum, contr_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => tA ε hc ha hb i hh hg
  · rw [if_neg hab, if_neg hab]
    cases ha : ε a
    · have hb : ε b = true := by cases h' : ε b <;> simp_all
      simp only [Bool.false_eq_true, if_false]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [← tD ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp
    · have hb : ε b = false := by cases h' : ε b <;> simp_all
      simp only [if_true]
      rw [smul_mul_assoc, contr_smul, Finset.sum_mul, contr_sum, mul_smul_comm, contr_smul, Finset.mul_sum _ _ h,
        contr_sum]
      simp_rw [tC ε hc ha hb _ hh hg]
      rw [← Finset.mul_sum]
      push_cast at hc2 ⊢
      field_simp

end CoreC

end PositivityTheory.Rg.Sw.LC
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.MapDomainInlInr
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ} {ε : Fin m → Bool}

theorem op_sum_f (u : Sym m n) {ι : Type*} (S : Finset ι) (c : ι → ℂ) (h : ι → PX m n) :
    op u (∑ i ∈ S, c i • h i) = ∑ i ∈ S, c i • op u (h i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [op_zero_f]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, op_add_f, op_smul_f, ih]

theorem kpow {a : Ix m n} (ha : inF1 ε a) (b : ℕ) : ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (X a ^ b * g) = op (u * X (Sum.inl a) ^ b) g + op r g := by
  induction b with
  | zero => intro d u _ _; exact ⟨0, good_zero d, fun g => by simp [op_zero]⟩
  | succ b ih =>
    intro d u hu hue
    obtain ⟨r₁, hr₁, e₁⟩ := ih d u hu hue
    have hdu := good_pderiv hu hue a
    obtain ⟨r₂, hr₂, e₂⟩ := ih d (pderiv (Sum.inr a) u) hdu.1 (good_le hdu)
    have hX : ∀ k, ((Finsupp.single (Sum.inl a) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (Finsupp.single (Sum.inl a) 1 : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
      split_ifs at hk with h
      · subst h; exact ha
      · exact absurd rfl hk
    have hXb : ∀ k, ((Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (Finsupp.single (Sum.inl a) b : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      simp only [Finsupp.single_apply, Sum.inl.injEq, reduceCtorEq, if_false, ne_eq, not_true, or_false] at hk
      split_ifs at hk with h
      · subst h; exact ha
      · exact absurd rfl hk
    have g1 : Good ε d (r₁ * X (Sum.inl a)) := by
      have := good_mul_monomial (e := 0) hr₁ _ hX (by simp [Finsupp.single_apply])
      simpa [X] using this
    have g2 : Good ε d (pderiv (Sum.inr a) u * X (Sum.inl a) ^ b) := by
      have := good_mul_monomial (e := 0) hdu _ hXb (by simp [Finsupp.single_apply])
      simpa [X_pow_eq_monomial] using this
    refine ⟨r₁ * X (Sum.inl a) + pderiv (Sum.inr a) u * X (Sum.inl a) ^ b + r₂, good_add (good_add g1 g2) hr₂, fun g => ?_⟩
    rw [pow_succ', mul_assoc, op_X_mul, e₁, e₂, op_add, op_add, op_mul_inl, pow_succ, ← mul_assoc, op_mul_inl]
    ring

theorem mapDomain_inl_inl (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) = γ k :=
  Finsupp.mapDomain_apply_of_injective Sum.inl_injective γ k

theorem mapDomain_inl_inr (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) = 0 :=
  Finsupp.mapDomain_notin_range γ _ (by simp)

theorem mapDomain_inr_inr (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) = γ k :=
  Finsupp.mapDomain_apply_of_injective Sum.inr_injective γ k

theorem mapDomain_inr_inl (γ : Ix m n →₀ ℕ) (k : Ix m n) :
    (γ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) = 0 :=
  Finsupp.mapDomain_notin_range γ _ (by simp)

theorem k2 (γ : Ix m n →₀ ℕ) : (∀ k ∈ γ.support, inF1 ε k) → ∀ (d : ℕ) (u : Sym m n), SymbolInFirstFamily ε u → EtaLe u d →
    ∃ r, Good ε d r ∧ ∀ g, op u (monomial γ 1 * g) = op (u * monomial (γ.mapDomain Sum.inl) 1) g + op r g := by
  induction γ using Finsupp.induction with
  | zero => intro _ d u _ _; exact ⟨0, good_zero d, fun g => by simp [monomial_zero', op_zero]⟩
  | single_add a b f haf hb ih =>
    intro hsup d u hu hue
    have hsf : ∀ k ∈ f.support, inF1 ε k := by
      intro k hk
      apply hsup k
      have hka : k ≠ a := fun h => haf (h ▸ hk)
      rw [Finsupp.mem_support_iff] at hk ⊢
      simpa [Finsupp.single_apply, Ne.symm hka] using hk
    have hai : inF1 ε a := by
      apply hsup a
      rw [Finsupp.mem_support_iff]
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.notMem_support_iff.1 haf, add_zero]
      exact hb
    obtain ⟨r₁, hr₁, e₁⟩ := kpow hai b d u hu hue
    have hu' := first_family_symbol_mul_variable_pow hu hai b
    obtain ⟨r₂, hr₂, e₂⟩ := ih hsf d (u * X (Sum.inl a) ^ b) hu'.1 (hu'.2 d hue)
    obtain ⟨r₃, hr₃, e₃⟩ := ih hsf d r₁ hr₁.1 (good_le hr₁)
    have hM : ∀ k, ((f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inl k) ≠ 0 ∨
        (f.mapDomain Sum.inl : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inl_inl, mapDomain_inl_inr] at hk
      exact hsf k (Finsupp.mem_support_iff.2 (by tauto))
    have g3 : Good ε d (r₁ * monomial (f.mapDomain Sum.inl) 1) := by
      have := good_mul_monomial (e := 0) hr₁ _ hM (by simp [mapDomain_inl_inr])
      simpa using this
    refine ⟨r₂ + r₁ * monomial (f.mapDomain Sum.inl) 1 + r₃, good_add (good_add hr₂ g3) hr₃, fun g => ?_⟩
    rw [monomial_single_add, mul_assoc, e₁, e₂, e₃, Finsupp.mapDomain_add, Finsupp.mapDomain_single,
      monomial_single_add, op_add, op_add]
    have : u * (X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1) =
        u * X (Sum.inl a) ^ b * monomial (Finsupp.mapDomain Sum.inl f) 1 := by ring
    rw [this]
    ring

theorem op_dvE (w : Sym m n) (δ : Ix m n →₀ ℕ) (f : PX m n) :
    op w (dvE (fun k => δ k) f) = op (w * monomial (δ.mapDomain Sum.inr) 1) f := by
  classical
  conv_rhs => rw [w.as_sum, Finset.sum_mul, op_sum]
  conv_lhs => rw [op]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [monomial_mul, mul_one, op_monomial, opMono_eq, opMono_eq, comapDomain_inl_add]
  have h1 : (δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ).comapDomain Sum.inl Sum.inl_injective.injOn = 0 := by
    ext j; simp [Finsupp.comapDomain_apply, mapDomain_inr_inl]
  have h2 : (fun k : Ix m n => (t + δ.mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) =
      (fun k => t (Sum.inr k)) + fun k => δ k := by
    ext j; simp [mapDomain_inr_inr]
  rw [h1, add_zero, h2, ← dvE_mul]
  rfl

theorem decomp (t : Ix m n ⊕ Ix m n →₀ ℕ) :
    (t.comapDomain Sum.inl Sum.inl_injective.injOn).mapDomain Sum.inl +
      (t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr = t := by
  ext j
  rcases j with j | j
  · simp [mapDomain_inl_inl, mapDomain_inr_inl, Finsupp.comapDomain_apply]
  · simp [mapDomain_inl_inr, mapDomain_inr_inr, Finsupp.comapDomain_apply]

theorem compSt : CompSt := by
  intro m n ε u v d₁ d₂ hu hv hue hve
  classical
  have key : ∀ t ∈ v.support, ∃ r, Good ε (d₁ + d₂) r ∧
      ∀ f, op u (opMono t f) = op (u * monomial t 1) f + op r f := by
    intro t ht
    have hγ : ∀ k ∈ (t.comapDomain Sum.inl Sum.inl_injective.injOn).support, inF1 ε k := by
      intro k hk
      apply hv t ht k
      left
      simpa [Finsupp.comapDomain_apply] using hk
    obtain ⟨r, hr, e⟩ := k2 _ hγ d₁ u hu hue
    have hs : ∀ k, (((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr : Ix m n ⊕ Ix m n →₀ ℕ)
        (Sum.inl k) ≠ 0 ∨ ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
          Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k) ≠ 0) → inF1 ε k := by
      intro k hk
      rw [mapDomain_inr_inl, mapDomain_inr_inr] at hk
      apply hv t ht k
      right
      simpa [Finsupp.comapDomain_apply] using hk
    have he : (∑ k, ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr :
        Ix m n ⊕ Ix m n →₀ ℕ) (Sum.inr k)) ≤ d₂ := by
      simp only [mapDomain_inr_inr, Finsupp.comapDomain_apply]
      exact hve t ht
    refine ⟨r * monomial ((t.comapDomain Sum.inr Sum.inr_injective.injOn).mapDomain Sum.inr) 1,
      good_mul_monomial hr _ hs he, fun f => ?_⟩
    rw [opMono_eq, e]
    have hδ : (fun k : Ix m n => t (Sum.inr k)) =
        fun k => (t.comapDomain Sum.inr Sum.inr_injective.injOn) k := by
      ext k; simp [Finsupp.comapDomain_apply]
    rw [hδ, op_dvE, op_dvE, mul_assoc, monomial_mul, mul_one, decomp]
  choose! R hR using key
  refine ⟨∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • R t, ?_, ?_, fun f => ?_⟩
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).1
  · exact (good_sum _ _ fun t ht => good_smul _ (hR t ht).1).2
  · rw [show op v f = ∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • opMono t f from rfl, op_sum_f]
    have huv : u * v = ∑ t ∈ v.support, AddMonoidAlgebra.coeff v t • (u * monomial t 1) := by
      conv_lhs => rw [v.as_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    rw [huv, op_sum, op_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(hR t ht).2, op_smul, op_smul, smul_add]

end PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators

theorem PositivityTheory.Rg.Sw.LC.compSt : PositivityTheory.Rg.Sw.LC.CompSt := PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.compSt
end
end

