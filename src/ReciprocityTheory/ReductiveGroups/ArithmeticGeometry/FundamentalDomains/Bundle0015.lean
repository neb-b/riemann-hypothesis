module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0012

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegralBasisReduction
section
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace IntegralBasisReduction

open Matrix NumberField Complex Module QuadraticLatticeForms
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

private lemma sum4_lemma {n : ℕ} (f : Fin n → Fin n → Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := by
  calc ∑ a, ∑ b, ∑ i, ∑ j, f a b i j = ∑ a, ∑ i, ∑ b, ∑ j, f a b i j :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ b, ∑ j, f a b i j := Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ b, f a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ a, ∑ b, f a b i j := Finset.sum_congr rfl fun i _ => Finset.sum_comm

private lemma hermC_mulVec_lemma_2 {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (Y : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℂ) :
    hermC τ G (Y *ᵥ u) (Y *ᵥ v) = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
  calc hermC τ G (Y *ᵥ u) (Y *ᵥ v)
      = ∑ a, ∑ b, ∑ i, ∑ j, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := by
        simp only [hermC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul]
    _ = ∑ i, ∑ j, ∑ a, ∑ b, Y a i * u i * τ (G a b) * (conj (Y b j) * conj (v j)) := sum4_lemma _
    _ = ∑ i, ∑ j, u i * gram τ G Y i j * conj (v j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [gram, hermC, col, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

theorem hermC_normal {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0) (s : Fin r → ℂ)
    (hg : gram τ X.Gm Y = diagonal s) (p q : Fin r → ℂ) :
    hermC τ X.Gm p q = ∑ a, s a * (Y⁻¹ *ᵥ p) a * conj ((Y⁻¹ *ᵥ q) a) := by
  have hu : IsUnit Y.det := isUnit_iff_ne_zero.mpr hY
  have key := hermC_mulVec_lemma_2 τ X.Gm Y (Y⁻¹ *ᵥ p) (Y⁻¹ *ᵥ q)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mulVec, Matrix.one_mulVec, hg] at key
  rw [key]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]; ring
  · intro j _ hj
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

def IsNormal (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, (y τ).det ≠ 0 ∧ gram τ.1 X.Gm (y τ) = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

theorem ip_Sg {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (p q : Fin r → E) :
    ip X (Ly X y (X.embV p)) (Sg X (Ly X y (X.embV q))) = ∑ τ, X.c τ * (τ.1 (herm X.Gm p q)).re := by
  simp only [ip, Sg, Ly, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨hdet, hg⟩ := hy τ
  have hτ : τ.1 (herm X.Gm p q) = hermC τ.1 X.Gm (X.embV p τ) (X.embV q τ) := by
    first
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          IsCMField.complexEmbedding_complexConj]
      | simp [herm, hermC, Data.embV, Data.emb, cc, map_sum, map_mul,
          NumberField.IsCMField.complexEmbedding_complexConj]
  rw [hτ, hermC_normal X hdet _ hg]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def zbas {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Basis ι ℝ (X.Ψ → Fin r → ℂ) :=
  (Basis.mk (RealPlaceEmbeddings.linIndR X g) (RealPlaceEmbeddings.span_embV X g).ge).map
    (LinearEquiv.ofBijective (Ly X y) ⟨Ly_injective X y fun τ => (hy τ).1,
      Ly_surjective X y fun τ => (hy τ).1⟩)

theorem zbas_apply {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ)
    (i : ι) : zbas X hy g i = Ly X y (X.embV (g i : Fin r → E)) := by
  simp only [zbas, Basis.map_apply, Basis.mk_apply]
  exact LinearEquiv.ofBijective_apply _ _

private lemma ip_sum_lemma_3 (u : X.Ψ → Fin r → ℂ) (a : ι → ℝ) (w : ι → X.Ψ → Fin r → ℂ) :
    ip X u (∑ k, a k • w k) = ∑ k, a k * ip X u (w k) := by
  have h1 : ∀ τ b, u τ b * conj ((∑ k, a k • w k) τ b) =
      ∑ k, ((a k : ℂ) * (u τ b * conj (w k τ b))) := by
    intro τ b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_apply, Finset.sum_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
    ring
  simp only [ip, h1, Complex.re_sum, Complex.re_ofReal_mul, Finset.mul_sum]
  calc ∑ τ, ∑ b, ∑ k, X.c τ * (a k * (u τ b * conj (w k τ b)).re)
      = ∑ τ, ∑ k, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) :=
        Finset.sum_congr rfl fun τ _ => Finset.sum_comm
    _ = ∑ k, ∑ τ, ∑ b, X.c τ * (a k * (u τ b * conj (w k τ b)).re) := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun τ _ =>
          Finset.sum_congr rfl fun b _ => ?_
        ring

theorem Bm_eq {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    Bm X g = Am X y g * LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) := by
  ext i j
  rw [Matrix.mul_apply]
  have hS := (zbas X hy g).sum_repr (Sg X (zbas X hy g j))
  simp only [LinearMap.toMatrix_apply]
  rw [show Bm X g i j = ip X (zbas X hy g i) (Sg X (zbas X hy g j)) by
    simp only [Bm, Matrix.of_apply, zbas_apply]
    exact (ip_Sg X hy _ _).symm]
  conv_lhs => rw [← hS]
  rw [ip_sum_lemma_3]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Am, Matrix.of_apply, zbas_apply]
  ring

theorem det_Am_le {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) (g : Basis ι ℤ X.Λ) :
    (Am X y g).det ≤ |(Bm X g).det| := by
  have hSS : Sg X * Sg X = 1 := by
    refine LinearMap.ext fun u => funext fun τ => funext fun a => ?_
    show ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * (((sgn X.p0 (a : ℕ) : ℝ) : ℂ) * u τ a) = u τ a
    rw [← mul_assoc, ← Complex.ofReal_mul]
    unfold sgn
    split_ifs <;> simp
  have hM : LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) *
      LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X) = 1 := by
    rw [← LinearMap.toMatrix_mul, hSS, LinearMap.toMatrix_one]
  have h2 : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| *
      |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rw [← abs_mul, ← Matrix.det_mul, hM, Matrix.det_one, abs_one]
  have hd : |(LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det| = 1 := by
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · linarith [abs_nonneg (LinearMap.toMatrix (zbas X hy g) (zbas X hy g) (Sg X)).det]
  rw [Bm_eq X hy g, Matrix.det_mul, abs_mul, hd, mul_one]
  exact le_abs_self _

theorem reduce {y : X.Ψ → Matrix (Fin r) (Fin r) ℂ} (hy : IsNormal X y) {m : ℝ} (hm : 0 < m)
    (hmin : ∀ v ∈ X.Λ, v ≠ 0 → m ≤ Qy X y v) :
    ∃ f : Basis (Fin (finrank ℤ X.Λ)) ℤ X.Λ,
      (∀ i, Qy X y (f i) ≤ 2 ^ (finrank ℤ X.Λ * (finrank ℤ X.Λ - 1)) *
        |(Bm X (RealPlaceEmbeddings.zb X)).det| / m ^ (finrank ℤ X.Λ - 1)) ∧
      ∀ (v : X.Λ) (i : Fin (finrank ℤ X.Λ)),
        ((f.repr v i : ℤ) : ℝ) ^ 2 ≤ 9 ^ (finrank ℤ X.Λ) * Qy X y v / m := by
  set g := RealPlaceEmbeddings.zb X with hgdef
  have hcoe : ∀ x : Fin (finrank ℤ X.Λ) → ℤ,
      ((∑ i, x i • g i : X.Λ) : Fin r → E) = ∑ i, x i • (g i : Fin r → E) := by
    intro x; simp
  have hint : ∀ x : Fin (finrank ℤ X.Λ) → ℤ, x ≠ 0 →
      m ≤ (fun i => (x i : ℝ)) ⬝ᵥ (Am X y g *ᵥ fun i => (x i : ℝ)) := by
    intro x hx
    rw [quad_int]
    refine hmin _ ?_ ?_
    · rw [← hcoe]; exact (∑ i, x i • g i : X.Λ).2
    · intro h0
      rw [← hcoe] at h0
      have h1 : (∑ i, x i • g i : X.Λ) = 0 := Subtype.ext h0
      exact hx (funext (Fintype.linearIndependent_iff.mp g.linearIndependent x h1))
  obtain ⟨eb, h1, h2⟩ := ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases.redGram_holds (finrank ℤ X.Λ) (Am X y g) m
    |(Bm X g).det| (Am_posDef X y (fun τ => (hy τ).1) g) hm hint (det_Am_le X hy g)
  refine ⟨eb.map g.equivFun.symm, fun i => ?_, fun v i => ?_⟩
  · have h3 := h1 i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.equivFun_symm_apply] using h3
  · have h3 := h2 (g.equivFun v) i
    rw [quad_int, ← hcoe] at h3
    simpa [Basis.map_repr, Basis.equivFun_symm_apply, g.sum_repr] using h3

end IntegralBasisReduction

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r)

theorem maj_transfer {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) (τ : X.Ψ)
    (g g' : Matrix (Fin r) (Fin r) ℂ) (hgg' : ∀ w, Matrix.mulVec g (Matrix.mulVec g' w) = w)
    (hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v)
    (H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP y τ a)
    (H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP y τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c))
    (w : Fin r → ℂ) : X.maj y τ w = X.maj x τ (Matrix.mulVec g' w) := by
  have pp : ∀ (x' : Frame X.Ψ r) (v : Fin r → ℂ),
      X.posPart x' τ v = (hermC τ.1 X.Gm (X.ppos x' τ v) v).re := by
    intro x' v
    rw [X.hermC_ppos_self]
    rfl
  set u := Matrix.mulVec g' w with hu
  set p := Matrix.mulVec g (X.ppos x τ u) with hp
  set z := Matrix.mulVec g u with hz
  have hA : ∀ d : Fin r → ℂ, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) →
      ∀ c, hermC τ.1 X.Gm d (Matrix.mulVec g (X.colP x τ c)) = 0 := by
    intro d hd c
    obtain ⟨K, hK⟩ := H1 c
    rw [hK, hermC_sum_right]
    exact Finset.sum_eq_zero fun a _ => by rw [hermC_smul_right, hd, mul_zero]
  have hB : ∀ b, hermC τ.1 X.Gm z (X.colP y τ b) = hermC τ.1 X.Gm p (X.colP y τ b) := by
    intro b
    rw [← sub_eq_zero, ← hermC_sub_left]
    obtain ⟨L, hL⟩ := H2 b
    rw [hL, hermC_sum_right]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hermC_smul_right, hz, hp, ← Matrix.mulVec_sub, hiso, hermC_sub_left,
      X.hermC_ppos_colP hx, sub_self, mul_zero]
  have h1 : X.ppos y τ z = X.ppos y τ p := by
    rw [X.ppos_eq, X.ppos_eq]
    simp only [hB]
  have h2 : ∀ c', hermC τ.1 X.Gm (X.ppos y τ p - p) (X.colP y τ c') = 0 := by
    intro c'
    rw [hermC_sub_left, X.hermC_ppos_colP hy, sub_self]
  have h3 : ∀ d, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) → hermC τ.1 X.Gm d p = 0 := by
    intro d hd
    rw [hp, X.ppos_eq x τ u, Matrix.mulVec_sum, hermC_sum_right]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.mulVec_smul, hermC_smul_right, hA d hd a, mul_zero]
  have key : hermC τ.1 X.Gm (X.ppos y τ z) z = hermC τ.1 X.Gm (X.ppos x τ u) u := by
    have e := h3 _ h2
    rw [hermC_sub_left, sub_eq_zero] at e
    rw [X.hermC_ppos_left hy τ z z, h1, ← X.hermC_ppos_left hy τ p p, e, hp, hiso,
      ← X.hermC_ppos_left hx τ u u]
  have hwz : w = z := (hgg' w).symm
  rw [hwz]
  simp only [Data.maj]
  rw [pp, pp, key, hz, hiso]

theorem maj_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC_zero_left]

theorem maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X x τ]
  · exact (X.maj_pos hx τ hv).le

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u - u') w = X.Hf x τ u w - X.Hf x τ u' w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_sub, hermC_sub_left,
    hermC_sub_left]
  ring

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_smul_eq, hermC_smul_left, hermC_smul_left]
  ring

theorem Hf_sub_right (x : Frame X.Ψ r) (τ : X.Ψ) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w - w') = X.Hf x τ u w - X.Hf x τ u w' := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_sub_right, hermC_sub_right]
  ring

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_smul_right, hermC_smul_right]
  ring

theorem Hf_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, map_sub, map_mul, map_ofNat, hermC_conj _ X.Gm_herm,
    hermC_conj _ X.Gm_herm, X.ppos_selfadj hx τ w u]

theorem cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    ‖X.Hf x τ u v‖ ^ 2 ≤ X.maj x τ u * X.maj x τ v := by
  by_cases hv : v = 0
  · have h0 : X.Hf x τ u 0 = 0 := by
      have := Hf_sub_right X x τ u 0 0
      simpa using this
    rw [hv, h0, maj_zero X x τ]
    simp
  have hm : 0 < X.maj x τ v := X.maj_pos hx τ hv
  have hmu := maj_nonneg X hx τ u

  set H := X.Hf x τ u v with hH
  have hw := X.Hf_self hx τ ((X.maj x τ v : ℂ) • u - H • v)
  have hn := maj_nonneg X hx τ ((X.maj x τ v : ℂ) • u - H • v)
  simp only [Hf_sub_left, Hf_sub_right, Hf_smul_left, Hf_smul_right] at hw
  rw [X.Hf_self hx τ u, X.Hf_self hx τ v, ← Hf_conj X hx τ u v, ← hH, Complex.conj_ofReal] at hw
  have hHH : H * conj H = (Complex.normSq H : ℂ) := Complex.mul_conj H
  have e : ((X.maj x τ ((X.maj x τ v : ℂ) • u - H • v) : ℝ) : ℂ) =
      ((X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) : ℝ) : ℂ) := by
    rw [← hw]
    push_cast
    linear_combination (-(X.maj x τ v : ℂ)) * hHH
  have e' := Complex.ofReal_injective e
  rw [e'] at hn
  have hle : Complex.normSq H ≤ X.maj x τ v * X.maj x τ u := by
    by_contra hc
    push_neg at hc
    have : X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) < 0 :=
      mul_neg_of_pos_of_neg hm (by linarith)
    linarith
  rw [Complex.sq_norm]
  linarith [mul_comm (X.maj x τ u) (X.maj x τ v)]

end MajorantConjugateTransfer

end ReciprocityTheory.ChartRestriction.G.FD
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
section
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

lemma uGu_lower (G : Matrix (Fin n) (Fin n) ℂ) (hdet : ∀ c : Fin n, (blk G c).det ≠ 0) {a c : Fin n}
    (hac : a < c) : ((uMat G)ᵀ * G * (uMat G).map (starRingEnd ℂ)) c a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge a k with h | h
  · rw [Matrix.map_apply, upper_lt (uMat_upper G) h, map_zero, mul_zero]
  · rw [uT_G_zero G c (hdet c) k (lt_of_le_of_lt h hac), zero_mul]

lemma prod_castLE_succ {k : ℕ} (h : k + 1 ≤ n) (f : Fin n → ℂ) :
    ∏ j : Fin (k + 1), f (Fin.castLE h j) = (∏ j : Fin k, f (Fin.castLE (Nat.le_of_succ_le h) j)) * f ⟨k, h⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl

lemma lminor_diagonal (D : Fin n → ℂ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal D) i = ∏ j : Fin i, D (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [lminor, det_sub_upper _ (Matrix.blockTriangular_diagonal D)]
  simp

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def uOf (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := uMat (gram τ.1 X.Gm (mat x τ))

def dOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := gram τ.1 X.Gm (mat x τ * uOf X x τ) k k

lemma blk_det {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    (blk (gram τ.1 X.Gm (mat x τ)) c).det ≠ 0 := by
  intro h0
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 c.castSucc
  have h2 : dmin X.Gm x τ c.castSucc = 0 := h0
  rw [h2, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

lemma gram_u_eq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat x τ * uOf X x τ) = Matrix.diagonal (dOf X x τ) := by
  ext c a
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rcases lt_or_gt_of_ne h with h' | h'
    · have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
      rw [← hH.apply c a, uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h', star_zero]
    · rw [uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h']

lemma dOf_real {x : Frame X.Ψ r} (_hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : (dOf X x τ k).im = 0 := by
  have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
  exact Complex.conj_eq_iff_im.mp (hH.apply k k)

lemma dmin_prod {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ∏ j : Fin i, dOf X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  have h1 := lminor_conj (N := uOf X x τ) (A := gram τ.1 X.Gm (mat x τ)) (uMat_upper _) i
  rw [← gram_mul, gram_u_eq X hx τ, lminor_diagonal] at h1
  simp only [uOf, uMat_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

lemma dmin_succ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm x τ k.succ = dmin X.Gm x τ k.castSucc * dOf X x τ k := by
  rw [dmin_prod X hx τ, dmin_prod X hx τ]
  exact prod_castLE_succ k.isLt (dOf X x τ)

lemma psgn_succ (p0 k : ℕ) : psgn p0 (k + 1) = psgn p0 k * sgn p0 k := by
  rw [psgn, psgn, Finset.prod_range_succ]

lemma sgn_dOf_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    0 < sgn X.p0 k * (dOf X x τ k).re := by
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 k.castSucc
  have h2 := ((X.mem_dom_iff x).1 hx τ).2 k.succ
  rw [dmin_succ X hx τ k, Complex.mul_re, dOf_real X hx τ k, mul_zero, sub_zero] at h2
  rw [Fin.val_succ, psgn_succ] at h2
  rw [Fin.coe_castSucc] at h1
  by_contra hneg
  push_neg at hneg
  nlinarith

def sOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := ((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ)

def bOf (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix _ _ ℂ)

lemma sgn_sq (p0 k : ℕ) : sgn p0 k = 1 ∨ sgn p0 k = -1 := by
  unfold sgn
  split_ifs <;> simp

lemma abs_re_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : 0 < |(dOf X x τ k).re| := by
  have h := sgn_dOf_pos X hx τ k
  refine abs_pos.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

lemma sOf_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : sOf X x τ k ≠ 0 := by
  unfold sOf
  rw [Ne, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero']
  exact not_le.mpr (abs_re_pos X hx τ k)

lemma bOf_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) : bOf X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)).det ≠ 0
    unfold uOf
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_of_upperTriangular (uMat_upper _)]
    simp only [uMat_diag, Finset.prod_const_one, one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => sOf_ne X hx τ k
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)) a c = 0
    unfold uOf
    rw [Matrix.mul_diagonal, upper_lt (uMat_upper _) hca, zero_mul]

lemma ortho_bOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.IsOrtho (rmul x (bOf X x)) := by
  intro τ
  change gram τ.1 X.Gm (mat x τ * (uOf X x τ * Matrix.diagonal (sOf X x τ))) = _
  rw [← Matrix.mul_assoc, gram_mul, gram_u_eq X hx τ, Matrix.diagonal_transpose,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  have hd : dOf X x τ a = ((dOf X x τ a).re : ℂ) :=
    Complex.ext (by simp) (by simp [dOf_real X hx τ a])
  have hpos := sgn_dOf_pos X hx τ a
  have habs := abs_re_pos X hx τ a
  rw [hd]
  simp only [sOf, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  set d := (dOf X x τ a).re
  have hs : (Real.sqrt |d|)⁻¹ * d * (Real.sqrt |d|)⁻¹ = d / |d| := by
    rw [mul_comm _ d, mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_mul_inv]
  rw [hs]
  rcases sgn_sq X.p0 a with h1 | h1 <;> rw [h1] at hpos ⊢
  · rw [abs_of_pos (by linarith), div_self (by linarith)]
  · have hn : d < 0 := by linarith
    rw [abs_of_neg hn, div_neg, div_self hn.ne]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end

