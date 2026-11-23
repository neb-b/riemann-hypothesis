module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.Bundle0008

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.EmbComb
section
namespace ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
noncomputable section
variable {E : Type} [Field E] [NumberField E]

namespace ChA

open NumberField.InfinitePlace Classical in
lemma emb_comb [IsCMField E] (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ τ : E →+* ℂ,
      ∑ i, (r i : ℂ) * τ (RingOfIntegers.basis E i : E) =
        if τ = σ then c else if τ = ComplexEmbedding.conjugate σ then (starRingEnd ℂ) c else 0 := by
  classical
  have hne := ne_conj σ
  have hcx : ∀ τ : E →+* ℂ, (mk τ).IsComplex := fun τ => IsTotallyComplex.isComplex _
  let wc : {w : InfinitePlace E // w.IsComplex} := ⟨mk σ, hcx σ⟩
  let c' : ℂ := if (mk σ).embedding = σ then c else (starRingEnd ℂ) c
  let y : mixedEmbedding.mixedSpace E := (0, Pi.single wc c')
  let B := mixedEmbedding.latticeBasis E
  refine ⟨fun i => B.repr y i, fun τ => ?_⟩
  have hsum := B.sum_repr y

  have hcoord : ∑ i, (B.repr y i : ℂ) * (mk τ).embedding (RingOfIntegers.basis E i : E) =
      y.2 ⟨mk τ, hcx τ⟩ := by
    conv_rhs => rw [← hsum]
    rw [Prod.snd_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [B, Prod.smul_snd, Pi.smul_apply, mixedEmbedding.latticeBasis_apply,
      mixedEmbedding.mixedEmbedding_apply_isComplex, integralBasis_apply, Complex.real_smul]
  have hy : y.2 ⟨mk τ, hcx τ⟩ = if mk τ = mk σ then c' else 0 := by
    simp only [y]
    by_cases h : mk τ = mk σ
    · rw [if_pos h]
      have : (⟨mk τ, hcx τ⟩ : {w : InfinitePlace E // w.IsComplex}) = wc := Subtype.ext h
      rw [this, Pi.single_eq_same]
    · rw [if_neg h, Pi.single_eq_of_ne]
      intro h'; exact h (congrArg Subtype.val h')
  have hemb := embedding_mk_eq τ

  have hval : ∑ i, (B.repr y i : ℂ) * τ (RingOfIntegers.basis E i : E) =
      if (mk τ).embedding = τ then (if mk τ = mk σ then c' else 0)
      else (starRingEnd ℂ) (if mk τ = mk σ then c' else 0) := by
    rcases hemb with h | h
    · rw [if_pos h, ← hy, ← hcoord, h]
    · by_cases h' : (mk τ).embedding = τ
      · rw [if_pos h', ← hy, ← hcoord, h']
      · rw [if_neg h', ← hy, ← hcoord, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [h, map_mul, Complex.conj_ofReal, ComplexEmbedding.conjugate_coe_eq]
        simp
  rw [hval]
  by_cases hτ : τ = σ
  · subst hτ
    simp only [if_true, c']
    split_ifs with h1 <;> simp
  · by_cases hτ' : τ = ComplexEmbedding.conjugate σ
    · subst hτ'
      have hm : mk (ComplexEmbedding.conjugate σ) = mk σ := mk_conjugate_eq σ
      simp only [if_neg hτ, if_true, hm, c']
      rcases embedding_mk_eq σ with h | h
      · have : (mk σ).embedding ≠ ComplexEmbedding.conjugate σ := by rw [h]; exact hne.symm
        simp [h, hm, this, hne, hne.symm]
      · simp [h, hm, hne, hne.symm]
    · have hm : mk τ ≠ mk σ := by
        intro h; rcases mk_eq_iff.mp h with h | h
        · exact hτ h
        · exact hτ' (by rw [← h]; exact (ComplexEmbedding.involutive_conjugate (K := E) τ).symm)
      simp [hτ, hτ', hm]


open Classical in
lemma Mc_comb [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (c : ℂ) :
    ∃ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ, ∀ v : Vsp dim,
      Mc σ c v = ∑ i, r i • act (RingOfIntegers.basis E i) v := by
  classical
  obtain ⟨r, hr⟩ := emb_comb σ c
  refine ⟨r, fun v => ?_⟩
  ext j
  rw [Mc_apply, WithLp.ofLp_sum, Finset.sum_apply]
  have := hr j.1
  simp only [PiLp.smul_apply, act_apply, Complex.real_smul]
  rw [show (∑ i, (r i : ℂ) * (j.1 (RingOfIntegers.basis E i : E) * v j)) =
    (∑ i, (r i : ℂ) * j.1 (RingOfIntegers.basis E i : E)) * v j by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun _ _ => by ring, this]
  split_ifs <;> simp

lemma Mc_mem [IsCMField E] {dim : (E →+* ℂ) → ℕ} (σ : E →+* ℂ) (S : Submodule ℝ (Vsp dim))
    (hS : ∀ (α : 𝓞 E) v, v ∈ S → act α v ∈ S) (c : ℂ) {v : Vsp dim} (hv : v ∈ S) :
    Mc σ c v ∈ S := by
  obtain ⟨r, hr⟩ := Mc_comb (dim := dim) σ c
  rw [hr]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hS _ _ hv)

end ChA
end
end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PolyDerivDeterminantPolyTensor
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MvPolynomial

noncomputable section

variable {E : Type} [Field E] [NumberField E] {n nb : ℕ} {dim : (E →+* ℂ) → ℕ}

section Expand
variable (bs : Fin nb → Block E n dim)

abbrev Choice := ∀ j : Fin nb, Fin (bs j).c → Equiv.Perm (Fin (bs j).i)

abbrev Slot := Σ j : Fin nb, Fin (bs j).c × Fin (bs j).i

def sgnT (T : Choice bs) : ℂ := ∏ j, ∏ r, ((Equiv.Perm.sign (T j r) : ℤ) : ℂ)

def letter (T : Choice bs) (t : Slot bs) : Letter n dim :=
  ((bs t.1).col t.2.2, ⟨(bs t.1).τ, Fin.castLE (bs t.1).hi (T t.1 t.2.1 t.2.2)⟩)

theorem block_poly_expand (B : Block E n dim) :
    B.poly = ∑ p : Fin B.c → Equiv.Perm (Fin B.i),
      (∏ r, ((Equiv.Perm.sign (p r) : ℤ) : MvPolynomial (Letter n dim) ℂ)) *
        ∏ r, ∏ b, X (B.col b, ⟨B.τ, Fin.castLE B.hi (p r b)⟩) := by
  rw [Block.poly, Matrix.det_apply', ← Fin.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem determinantPoly_expand :
    P1 bs = ∑ T : Choice bs, sgnT bs T • ∏ t : Slot bs, X (letter bs T t) := by
  rw [P1]
  simp only [block_poly_expand]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_mul_distrib, MvPolynomial.smul_eq_C_mul]
  congr 1
  · simp only [sgnT, map_prod, map_intCast]
  · rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Fintype.prod_prod_type]
    rfl

end Expand

section PD
variable (X : PT E) (bs : Fin nb → Block E n X.dim)


open Classical in
def lst (T : Choice bs) : List (Fin n × Vsp X.dim) :=
  by
    classical
    exact (Multiset.map (letter bs T) Finset.univ.val).toList.map
      (fun l => (l.1, EuclideanSpace.single l.2 (1 : ℂ)))

theorem prod_X_letter (T : Choice bs) :
    (∏ t : Slot bs, MvPolynomial.X (letter bs T t) : MvPolynomial (Letter n X.dim) ℂ) =
      monomial (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) 1 := by
  rw [MvPolynomial.monomial_sum_one]
  rfl

theorem toMultiset_letters (T : Choice bs) :
    Finsupp.toMultiset (∑ t : Slot bs, Finsupp.single (letter bs T t) 1) =
      Multiset.map (letter bs T) Finset.univ.val := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  rw [Finset.sum_eq_multiset_sum]
  have h : ∀ (s : Multiset (Slot bs)),
      (s.map fun t => ({letter bs T t} : Multiset (Letter n X.dim))).sum = s.map (letter bs T) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih]
  exact h _

theorem polyDeriv_determinantPoly_tensor (s : Fin n → (Fin 1 → Vsp X.dim) → ℂ)
    (hs : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (s k)) :
    polyDeriv (P1 bs) dir (tens X s) 0 =
      ∑ T : Choice bs, sgnT bs T * ∏ k, d1 (s k) (colL (lst X bs T) k).length
        (fun j => (colL (lst X bs T) k).get j) := by
  rw [determinantPoly_expand, jof_polyDeriv_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [polyDeriv_smul, prod_X_letter, polyDeriv_monomial_one, pdTerm_eq_itD, toMultiset_letters]
  congr 1
  have hl : (Multiset.map (letter bs T) Finset.univ.val).toList.map dir =
      (lst X bs T).map (fun p => Pi.single p.1 p.2) := by
    rw [lst, List.map_map]
    rfl
  rw [hl]
  have hg : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (fun z : Vsp X.dim => s k (fun _ => z)) := fun k =>
    (hs k).comp (contDiff_pi.2 fun _ => contDiff_id)
  have h1 := itD_prod hg (lst X bs T) 0
  rw [show tens X s = fun v : Fin n → Vsp X.dim => ∏ k, s k (fun _ => v k) from rfl, h1]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Pi.zero_apply, itD_col (hs k)]
  rfl


end PD

end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropABSt
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

section

variable {ι : Type} [Fintype ι]

open Classical

def paTh (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun v => ∑' γ : lat Y.b, Y.ka γ * paU q γ F v

end




end

end ReciprocityTheory.ChartRestriction.G.I2
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitB
section
namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

structure Good (X : PT E) (c : ℝ) (I : Submodule ℤ (Vsp X.dim)) : Prop where
  le : I ≤ X.L
  sat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I
  stable : ∀ (α : 𝓞 E) x, x ∈ I → act α x ∈ I
  iso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0
  sep : ∀ x ∈ X.L, ∀ u, IsU I x u → u ≠ 0 → c < ‖u‖

private lemma act_zero_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) : act α (0 : Vsp dim) = 0 := by
  first
  | (ext i; simp [act])
  | simp [act]
  | (unfold act; ext i; simp)

theorem Good.bot (X : PT E) (c : ℝ) : Good X c ⊥ := by
  refine { le := bot_le, sat := ?_, stable := ?_, iso := ?_, sep := ?_ }
  ·
    intro x _ hx
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    rw [this] at hx
    simpa using hx
  ·
    intro α x hx
    rw [Submodule.mem_bot] at hx ⊢
    subst hx
    rw [act_eq_actE, actE_zero_right]
  ·
    intro x hx y _
    rw [Submodule.mem_bot] at hx
    subst hx
    exact Hf_im_zero_left y
  ·
    intro x _ u hu hne
    exfalso
    have : IR (⊥ : Submodule ℤ (Vsp X.dim)) = ⊥ := by simp [IR]
    have h1 := hu.1
    rw [this, Submodule.mem_bot] at h1
    exact hne h1

private lemma act_add_square_integrability {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (v w : Vsp dim) :
    act α (v + w) = act α v + act α w := by
  first
  | (ext i; simp [act, mul_add])
  | (unfold act; ext i; simp [mul_add])

private lemma act_real_smul {dim : (E →+* ℂ) → ℕ} (α : 𝓞 E) (r : ℝ) (v : Vsp dim) :
    act α (r • v) = r • act α v := by
  first
  | (ext i; simp [act, Complex.real_smul]; ring)
  | (ext i; simp [act, mul_smul_comm])
  | (unfold act; ext i; simp [Complex.real_smul]; ring)

theorem Good.IR_stable {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I)
    (α : 𝓞 E) : ∀ v ∈ IR I, act α v ∈ IR I := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (hI.stable α x hx)
  | zero => rw [act_zero_square_integrability]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [act_add_square_integrability]; exact add_mem hx hy
  | smul r x _ hx => rw [act_real_smul]; exact Submodule.smul_mem _ r hx

private lemma Hf_add_left' {ι : Type} [Fintype ι] (v v' w : EuclideanSpace ℂ ι) :
    Hf (v + v') w = Hf v w + Hf v' w := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private lemma Hf_add_right' {ι : Type} [Fintype ι] (v w w' : EuclideanSpace ℂ ι) :
    Hf v (w + w') = Hf v w + Hf v w' := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

private lemma im_Hf_real_smul_left {ι : Type} [Fintype ι] (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf (r • v) w).im = r * (Hf v w).im := by
  first
  | (simp only [Hf, PiLp.smul_apply, Complex.real_smul, mul_assoc, ← Finset.mul_sum]; simp [Complex.mul_im])
  | (simp [Hf, Complex.real_smul, mul_assoc, ← Finset.mul_sum, Complex.mul_im])
  | (simp [Hf, Finset.mul_sum, Complex.mul_im, Complex.real_smul])

private lemma Hf_real_smul_right_im {ι : Type} [Fintype ι] (r : ℝ) (v w : EuclideanSpace ℂ ι) :
    (Hf v (r • w)).im = r * (Hf v w).im := by
  first
  | (simp only [Hf, PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal, mul_left_comm _ (r : ℂ), ← Finset.mul_sum]; simp [Complex.mul_im])
  | (simp [Hf, Complex.real_smul, mul_left_comm _ (r : ℂ), ← Finset.mul_sum, Complex.mul_im])
  | (simp [Hf, Finset.mul_sum, Complex.mul_im, Complex.real_smul])

theorem Good.IR_iso {X : PT E} {c : ℝ} {I : Submodule ℤ (Vsp X.dim)} (hI : Good X c I) :
    ∀ v ∈ IR I, ∀ w ∈ IR I, (Hf v w).im = 0 := by
  intro v hv w hw
  induction hv using Submodule.span_induction with
  | mem x hx =>
    induction hw using Submodule.span_induction with
    | mem y hy => exact hI.iso x hx y hy
    | zero => simp [Hf]
    | add y y' _ _ h1 h2 => rw [Hf_add_right', Complex.add_im, h1, h2, add_zero]
    | smul r y _ h => rw [Hf_real_smul_right_im, h, mul_zero]
  | zero => simp [Hf]
  | add x x' _ _ h1 h2 => rw [Hf_add_left', Complex.add_im, h1, h2, add_zero]
  | smul r x _ h => rw [im_Hf_real_smul_left, h, mul_zero]

theorem im_eq_zero_of_lt (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : |(Hf x y).im| < 1) : (Hf x y).im = 0 := by
  obtain ⟨k, hk⟩ := X.integral x y hx hy
  rw [hk] at h ⊢
  have hk1 : |k| < 1 := by exact_mod_cast h
  have hk0 : k = 0 := by
    rw [abs_lt] at hk1
    omega
  simp [hk0]

theorem one_le_abs_im (X : PT E) {x y : Vsp X.dim} (hx : x ∈ X.L) (hy : y ∈ X.L)
    (h : (Hf x y).im ≠ 0) : 1 ≤ |(Hf x y).im| := by
  obtain ⟨k, hk⟩ := X.integral x y hx hy
  rw [hk] at h ⊢
  have hk0 : k ≠ 0 := by exact_mod_cast h
  exact_mod_cast Int.one_le_abs hk0

end

end ReciprocityTheory.ChartRestriction.G.I2
end

