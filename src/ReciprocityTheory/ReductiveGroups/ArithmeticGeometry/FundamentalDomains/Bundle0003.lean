module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BabaiCovering
section
namespace ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering

open Submodule Module

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem babai : ∀ (m : ℕ) (y : Fin m → V) (v : V), v ∈ span ℝ (Set.range y) →
    ∃ x ∈ span ℤ (Set.range y), ‖v - x‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
  have key : ∀ (m : ℕ) (y : Fin m → V) (c : Fin m → ℝ), ∃ n : Fin m → ℤ,
      ‖∑ i, (c i - (n i : ℝ)) • y i‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
    intro m
    induction m with
    | zero => intro y c; exact ⟨fun i => i.elim0, by simp⟩
    | succ m ih =>
      intro y c
      obtain ⟨n, hn⟩ := ih (fun i => y i.castSucc) (fun i => c i.castSucc)
      set u := ∑ i : Fin m, (c i.castSucc - (n i : ℝ)) • y i.castSucc with hu
      set w := y (Fin.last m) with hw
      set f := Int.fract (c (Fin.last m)) with hfd
      have hf0 : 0 ≤ f := Int.fract_nonneg _
      have hf1 : f < 1 := Int.fract_lt_one _
      have havg : (1 - f) * ‖u + f • w‖ ^ 2 + f * ‖u + (f - 1) • w‖ ^ 2 =
          ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_right,
          real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
        ring
      have hq : f * (1 - f) ≤ 1 / 4 := by nlinarith [sq_nonneg (f - 1 / 2)]
      have hbound : ‖u‖ ^ 2 + f * (1 - f) * ‖w‖ ^ 2 ≤ (1 / 4) * ∑ i, ‖y i‖ ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        have h1 := mul_le_mul_of_nonneg_right hq (sq_nonneg ‖w‖)
        nlinarith [hn]
      have hsplit : ∀ N : ℤ, ∑ i, (c i - ((Fin.snoc (α := fun _ => ℤ) n N i : ℤ) : ℝ)) • y i =
          u + (c (Fin.last m) - (N : ℝ)) • w := by
        intro N
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last, hu, hw]
      by_cases hc : ‖u + f • w‖ ^ 2 ≤ ‖u + (f - 1) • w‖ ^ 2
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n ⌊c (Fin.last m)⌋, ?_⟩
        rw [hsplit, ← Int.fract]
        nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hc)]
      · refine ⟨Fin.snoc (α := fun _ => ℤ) n (⌊c (Fin.last m)⌋ + 1), ?_⟩
        have e : c (Fin.last m) - (((⌊c (Fin.last m)⌋ + 1 : ℤ)) : ℝ) = f - 1 := by
          rw [hfd, Int.fract]
          push_cast
          ring
        rw [hsplit, e]
        push_neg at hc
        nlinarith [mul_nonneg (sub_nonneg.mpr hf1.le) (sub_nonneg.mpr hc.le)]
  intro m y v hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  obtain ⟨n, hn⟩ := key m y c
  refine ⟨∑ i, (n i) • y i, Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), ?_⟩
  have e : v - ∑ i, (n i) • y i = ∑ i, (c i - (n i : ℝ)) • y i := by
    rw [← hc, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sub_smul, Int.cast_smul_eq_zsmul]
  rw [e]
  exact hn

theorem cover {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ V) (bd : ι → V)
    (hd : ∀ i j, inner ℝ (b i) (bd j) = if i = j then 1 else 0) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ x ∈ span ℤ (Set.range bd), x ≠ 0 → lam ≤ ‖x‖) (v : V) :
    ∃ x ∈ span ℤ (Set.range b),
      ‖v - x‖ ^ 2 ≤ (finrank ℝ V : ℝ) / 4 * ((finrank ℝ V : ℝ) ^ 2 / lam) ^ 2 := by
  classical
  set n := finrank ℝ V with hn
  have hcard : Fintype.card ι = n := (finrank_eq_card_basis b).symm
  have hli : LinearIndependent ℝ bd := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrArg (inner ℝ (b i)) hg
    simpa [inner_sum, real_inner_smul_right, hd] using this
  let Bd : Basis ι ℝ V := Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' hcard).ge
  have hBd : ∀ i, Bd i = bd i := fun i => Basis.mk_apply _ _ _
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let φ : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) := (stdOrthonormalBasis ℝ V).repr
  let B' : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Bd.reindex e).map φ.toLinearEquiv
  have hB' : ∀ j, B' j = φ (bd (e.symm j)) := fun j => by simp [B', hBd]
  have hmin' : ∀ x ∈ span ℤ (Set.range B'), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    obtain ⟨c, rfl⟩ := (mem_span_range_iff_exists_fun ℤ).1 hx
    have hw : (∑ i, c i • B' i) = φ (∑ i, c i • bd (e.symm i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [hB', map_sum, map_zsmul]
    have hwmem : (∑ i, c i • bd (e.symm i)) ∈ span ℤ (Set.range bd) :=
      sum_mem fun i _ => zsmul_mem (subset_span (Set.mem_range_self _)) _
    rw [hw, LinearIsometryEquiv.norm_map]
    refine hmin _ hwmem ?_
    intro h0
    apply hx0
    rw [hw, h0, map_zero]
  obtain ⟨y, hyli, hyint, hynorm⟩ := ReciprocityTheory.ChartRestriction.G.T0.transference_dual B' lam hlam hmin'
  let yV : Fin n → V := fun i => φ.symm (y i)
  have hyVint : ∀ i k, ∃ m : ℤ, inner ℝ (yV i) (bd k) = m := by
    intro i k
    obtain ⟨m, hm⟩ := hyint i (e k)
    refine ⟨m, ?_⟩
    rw [← hm, hB', Equiv.symm_apply_apply, ← LinearIsometryEquiv.inner_map_map φ]
    simp [yV]
  have hyVmem : ∀ i, yV i ∈ span ℤ (Set.range b) := by
    intro i
    have hrep : ∀ k, b.repr (yV i) k = inner ℝ (yV i) (bd k) := by
      intro k
      have h : inner ℝ (yV i) (bd k) = ∑ l, b.repr (yV i) l * inner ℝ (b l) (bd k) := by
        conv_lhs => rw [← b.sum_repr (yV i)]
        rw [sum_inner]
        simp_rw [real_inner_smul_left]
      rw [h]
      simp [hd]
    rw [← b.sum_repr (yV i)]
    refine sum_mem fun k _ => ?_
    obtain ⟨m, hm⟩ := hyVint i k
    rw [hrep, hm, Int.cast_smul_eq_zsmul]
    exact zsmul_mem (subset_span (Set.mem_range_self k)) m
  have hyVli : LinearIndependent ℝ yV :=
    hyli.map' φ.symm.toLinearEquiv.toLinearMap φ.symm.toLinearEquiv.ker
  have hspan : span ℝ (Set.range yV) = ⊤ :=
    hyVli.span_eq_top_of_card_eq_finrank' (by simp [n])
  obtain ⟨x, hx, hxb⟩ := babai n yV v (hspan ▸ mem_top)
  refine ⟨x, span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyVmem i) hx, hxb.trans ?_⟩
  calc (1 / 4) * ∑ i, ‖yV i‖ ^ 2 ≤ (1 / 4) * ∑ _i : Fin n, ((n : ℝ) ^ 2 / lam) ^ 2 := by
        gcongr with i
        have : ‖yV i‖ = ‖y i‖ := by simp [yV]
        rw [this]
        exact hynorm i
    _ = (n : ℝ) / 4 * ((n : ℝ) ^ 2 / lam) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.BabaiCovering
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.EmbeddingHermitianPairs
section
namespace ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma emb_cc' (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) := NumberField.IsCMField.complexEmbedding_complexConj E τ x

section herm

variable (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)

lemma hermC_emb (x y : Fin r → E) :
    hermC τ G (fun a => τ (x a)) (fun a => τ (y a)) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, map_sum, map_mul, emb_cc']

end herm

section flowAlg

variable (X : Data E r)

def wv (ξ : Fin r → E) (τ : X.Ψ) : Fin r → ℂ := fun b => ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k))

lemma wv_dot (ξ : Fin r → E) (τ : X.Ψ) (v : Fin r → ℂ) :
    wv X ξ τ ⬝ᵥ v = hermC τ.1 X.Gm v (Data.emb τ.1 ξ) := by
  simp only [dotProduct, wv, hermC, Data.emb, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma wv_dot_self {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    wv X ξ τ ⬝ᵥ Data.emb τ.1 ξ = 0 := by
  rw [wv_dot]
  exact (hermC_emb τ.1 X.Gm ξ ξ).trans (by rw [hξ, map_zero])

lemma flowMat_eq (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) :
    X.flowMat ξ τ s = 1 + (-(I * X.c τ * s)) • vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
    vecMulVec_apply, wv, Data.emb, smul_eq_mul]
  ring

lemma nil_sq {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) :
    vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) * vecMulVec (Data.emb τ.1 ξ) (wv X ξ τ) = 0 := by
  ext a b
  have h0 := wv_dot_self X hξ τ
  simp only [dotProduct] at h0
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply]
  calc ∑ k, Data.emb τ.1 ξ a * wv X ξ τ k * (Data.emb τ.1 ξ k * wv X ξ τ b)
      = Data.emb τ.1 ξ a * wv X ξ τ b * ∑ k, wv X ξ τ k * Data.emb τ.1 ξ k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = 0 := by rw [h0, mul_zero]

lemma flowMat_mul {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s s' : ℂ) :
    X.flowMat ξ τ s * X.flowMat ξ τ s' = X.flowMat ξ τ (s + s') := by
  rw [flowMat_eq, flowMat_eq, flowMat_eq]
  rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, nil_sq X hξ,
    smul_zero, smul_zero, add_zero, add_assoc, ← add_smul]
  congr 2
  ring

lemma flowMat_zero (ξ : Fin r → E) (τ : X.Ψ) : X.flowMat ξ τ 0 = 1 := by
  ext a b
  simp [Data.flowMat, Matrix.one_apply]

lemma det_flowMat {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (τ : X.Ψ) (s : ℂ) :
    (X.flowMat ξ τ s).det = 1 := by
  rw [flowMat_eq, Matrix.vecMulVec_eq Unit, ← Matrix.smul_mul, ← Matrix.replicateCol_smul,
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, wv_dot_self X hξ,
    smul_zero, add_zero]

lemma flow_flow {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (s s' : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s (X.flow ξ s' x) = X.flow ξ (s + s') x := by
  funext τ
  show (X.flowMat ξ τ (s τ) * (X.flowMat ξ τ (s' τ) * mat x τ) : Matrix (Fin r) (Fin r) ℂ) =
    X.flowMat ξ τ ((s + s') τ) * mat x τ
  rw [← Matrix.mul_assoc, flowMat_mul X hξ, Pi.add_apply]

lemma flow_zero (ξ : Fin r → E) (x : Frame X.Ψ r) : X.flow ξ 0 x = x := by
  funext τ
  show (X.flowMat ξ τ ((0 : X.Ψ → ℂ) τ) * mat x τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [Pi.zero_apply, flowMat_zero, Matrix.one_mul]
  rfl

lemma flowMat_mulVec (ξ : Fin r → E) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    X.flowMat ξ τ s *ᵥ v = v + ((-(I * X.c τ * s)) * hermC τ.1 X.Gm v (Data.emb τ.1 ξ)) •
      Data.emb τ.1 ξ := by
  rw [flowMat_eq, Matrix.add_mulVec, Matrix.one_mulVec]
  congr 1
  ext a
  rw [← wv_dot X ξ τ v]
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end flowAlg

end ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
section
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def EFf {r : ℕ} (ξ0 : E) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : ℚ :=
  Algebra.trace ℚ E (-ξ0 * herm G x y)

structure DataX (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) extends Data E r where
  k0 : ℝ
  minWeight_pos : 0 < k0
  k0_le : k0 ≤ 2
  ξ0_abs : ∀ τ : Ψ, ‖τ.1 ξ0‖ = k0 / 2
  EF_int : ∀ x ∈ Λ, ∀ y ∈ Λ, ∃ k : ℤ, EFf ξ0 Gm x y = k
  EF_perf : ∀ φ : Λ →+ ℤ, ∃ x ∈ Λ, ∀ y : Λ, (φ y : ℚ) = EFf ξ0 Gm x y
  L' : Submodule (𝓞 E) (Fin r → E)
  L'_fg : L'.FG
  L'_int : ∀ x ∈ L', ∀ y ∈ L', IsIntegral ℤ (herm Gm x y)
  L'_dual : ∀ x, (∀ y ∈ L', IsIntegral ℤ (herm Gm x y)) → x ∈ L'
  NA : ℕ
  NC : ℕ
  NA_pos : 0 < NA
  NC_pos : 0 < NC
  NA_sub : ∀ x ∈ Λ, (NA : E) • x ∈ L'
  NC_sub : ∀ x ∈ L', (NC : E) • x ∈ Λ
  g : ℕ
  g_pos : 0 < g
  cong : ∀ γ : GL (Fin r) E, IsUStab Gm Λ γ →
    (∀ x ∈ Λ, ∃ y ∈ Λ, Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) x - x = (g : E) • y) → γ ∈ Γ

def fdeg (E : Type) [Field E] [NumberField E] : ℕ := Module.finrank ℚ E / 2

def dE (E : Type) [Field E] [NumberField E] : ℝ := |(NumberField.discr E : ℝ)|

def rdE (E : Type) [Field E] [NumberField E] : ℝ := dE E ^ (1 / (Module.finrank ℚ E : ℝ))

namespace Data

variable {r : ℕ} (X : Data E r)

def embV (v : Fin r → E) : X.Ψ → Fin r → ℂ := fun τ => emb τ.1 v

def lineV (ξ : Fin r → E) (s : X.Ψ → ℂ) : X.Ψ → Fin r → ℂ := fun τ => s τ • emb τ.1 ξ

def ppos (x : Frame X.Ψ r) (τ : X.Ψ) (u : Fin r → ℂ) : Fin r → ℂ :=
  ∑ a : Fin X.p0, (∑ b : Fin X.p0, hermC τ.1 X.Gm u (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a) • col (mat x τ) (Fin.castLE X.p0_le a)

def Jz (x : Frame X.Ψ r) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => I • ((2 : ℂ) • X.ppos x τ (u τ) - u τ)

def Hf (x : Frame X.Ψ r) (τ : X.Ψ) (u w : Fin r → ℂ) : ℂ :=
  hermC τ.1 X.Gm ((2 : ℂ) • X.ppos x τ u - u) w

def Iperp (ξ : Fin r → E) : Set (X.Ψ → Fin r → ℂ) :=
  {u | ∀ τ : X.Ψ, hermC τ.1 X.Gm (u τ) (emb τ.1 ξ) = 0}

def Uz (x : Frame X.Ψ r) (ξ : Fin r → E) : Set (X.Ψ → Fin r → ℂ) :=
  {u | u ∈ X.Iperp ξ ∧ X.Jz x u ∈ X.Iperp ξ}

def aproj (x : Frame X.Ψ r) (ξ : Fin r → E) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  X.lineV ξ fun τ => X.Hf x τ (u τ) (emb τ.1 ξ) / X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)

def ucomp (x : Frame X.Ψ r) (ξ : Fin r → E) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  u - X.aproj x ξ u

def hermL (ξ : Fin r → E) : (Fin r → E) →+ E where
  toFun x := herm X.Gm x ξ
  map_zero' := by simp [herm]
  map_add' x y := by simp [herm, add_mul, Finset.sum_add_distrib]

def Λp (ξ : Fin r → E) : AddSubgroup (Fin r → E) := X.Λ.toAddSubgroup ⊓ (X.hermL ξ).ker

def lmulC (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (n τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def applyV (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (u : X.Ψ → Fin r → ℂ) : X.Ψ → Fin r → ℂ :=
  fun τ => Matrix.mulVec (n τ) (u τ)

def IsUnitaryC (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ : X.Ψ, ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec (n τ) u) (Matrix.mulVec (n τ) w) = hermC τ.1 X.Gm u w

def IsDominant (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i ≤ j → (j : ℕ) < X.p0 → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i ≤ j → la τ j ≤ la τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ i ≤ la τ j)

def SameFlag (x x' : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x τ) (Fin.castLE X.p0_le a)) =
    Submodule.span ℂ (Set.range fun a : Fin X.p0 => col (mat x' τ) (Fin.castLE X.p0_le a))

def hatN (la : Wt X.Ψ r) (Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ :=
  sSup {t | ∃ x' ∈ X.dom, X.SameFlag x x' ∧ t = X.pnorm la Q x'}

def FramesOverBasis (ξ : Fin r → E) : Set (Frame X.Ψ r) :=
  {x | x ∈ X.dom ∧ ∀ τ : X.Ψ, X.c τ * X.maj x τ (emb τ.1 ξ) = 1}

end Data

def flowEpsilonBound (g d f NA NC c1 w : ℝ) : ℝ :=
  let rd := d ^ (1 / (2 * f))
  let N0 := g * d ^ 2
  let H := NC ^ 2 * (2 + 4 * f ^ 4 * rd ^ 2 * NA ^ 2)
  let K2 := 1 + N0 * H * (2 * c1 + 1)
  let N2 := 4 * f
  let R2 := w + N2 * Real.log (2 * K2 * N2) + N2 + 2
  min 1 (f ^ 2 / (N0 ^ 2 * NC ^ 2 * c1 * R2))

def ProjectionAlongComplement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom, ∀ u ∈ X.Iperp ξ,
    X.ucomp x ξ u ∈ X.Uz x ξ

def PerfectPairingQuotient : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ →
    (∀ φ : X.Λp ξ →+ ℤ, (∀ μ : X.Λp ξ, (∃ e : E, (μ : Fin r → E) = e • ξ) → φ μ = 0) →
      ∃ μ : X.Λp ξ, ∀ ν : X.Λp ξ, (φ ν : ℚ) = EFf X.ξ0 X.Gm μ ν) ∧
    ∀ μ : X.Λp ξ, (∀ ν : X.Λp ξ, EFf X.ξ0 X.Gm μ ν = 0) → ∃ e : E, (μ : Fin r → E) = e • ξ

def PerpQuotientSelfDual : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x : Fin r → E, herm X.Gm x ξ = 0 →
    (∀ y ∈ X.L', herm X.Gm y ξ = 0 → IsIntegral ℤ (herm X.Gm x y)) → ∃ e : E, x + e • ξ ∈ X.L'

def UnitaryComplementMove : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom,
    ∀ h1 : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC h1 →
    (∀ s t : X.Ψ → ℂ, X.applyV h1 (X.lineV ξ s + X.Jz x (X.lineV ξ t)) =
      X.lineV ξ s + X.Jz x (X.lineV ξ t)) →
    (∀ u ∈ X.Uz x ξ, X.applyV h1 u ∈ X.Uz x ξ) →
    X.lmulC h1 x ∈ X.dom ∧ (∀ u ∈ X.Iperp ξ, X.aproj (X.lmulC h1 x) ξ u = X.aproj x ξ u) ∧
      (∀ τ, X.maj (X.lmulC h1 x) τ (Data.emb τ.1 ξ) = X.maj x τ (Data.emb τ.1 ξ)) ∧
      ∀ u ∈ X.Uz x ξ, X.Jz (X.lmulC h1 x) (X.applyV h1 u) = X.applyV h1 (X.Jz x u)

def ReducedFrameDomainCovering : Prop :=
  ∀ (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ → ∀ x ∈ X.dom,
    ∀ (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) (κ : ℝ), 0 ≤ κ → κ ≤ 1 →
    (∀ u ∈ X.Uz x ξ, ∀ τ, X.maj x τ (δ τ (u τ) • Data.emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ (u τ)) →
    ∃ n : X.Ψ → Matrix (Fin r) (Fin r) ℂ, X.IsUnitaryC n ∧
      (∀ τ, Matrix.mulVec (n τ) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ) ∧
      (∀ u ∈ X.Uz x ξ, X.applyV n u = u + X.lineV ξ (fun τ => δ τ (u τ))) ∧
      X.lmulC n x ∈ X.dom ∧
      (∀ u ∈ X.Iperp ξ, X.aproj (X.lmulC n x) ξ u =
        X.aproj x ξ u - X.lineV ξ (fun τ => δ τ (X.ucomp x ξ u τ))) ∧
      (∀ τ, X.maj (X.lmulC n x) τ (Data.emb τ.1 ξ) = X.maj x τ (Data.emb τ.1 ξ)) ∧
      (∀ u ∈ X.Uz x ξ, X.ucomp (X.lmulC n x) ξ (X.Jz x u) =
        X.Jz (X.lmulC n x) (X.ucomp (X.lmulC n x) ξ u)) ∧
      ∀ τ (v : Fin r → ℂ), X.maj x τ (Matrix.mulVec (n τ - 1) v) ≤ (3 * κ) ^ 2 * X.maj x τ v

def IntegerApproximationCount : Prop :=
  ∀ (r : ℕ) (X : Data E r),
    (∀ w : X.Ψ → ℂ, ∃ α : 𝓞 E, ∀ τ : X.Ψ, ‖τ.1 (α : E) - w τ‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E) ∧
    ∀ R : ℝ, 0 ≤ R → {α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.Finite ∧
      ({α : 𝓞 E | ∀ τ : E →+* ℂ, ‖τ (α : E)‖ ≤ R}.ncard : ℝ) ≤ (1 + 2 * R) ^ (2 * fdeg E)

def ShortVectorHypotheses {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r) : Prop :=
  X.IsDominant la ∧ P ∈ X.SS la ∧ X.IsIso ξ ∧ 0 < c1 ∧ ∑ τ, ν τ ≤ c1 ∧
    (∃ x ∈ X.dom, X.fj la ξ ν P x ≠ 0) ∧ 1 ≤ w ∧ (∑ τ, X.spread la τ) ≤ w ∧
    (∀ γ ∈ X.Γ, (∀ v ∈ X.Λ, ∃ y ∈ X.Λ,
      Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) v - v = (X.g : E) • y) → X.χ la γ = 1) ∧
    z0 ∈ X.FramesOverBasis ξ ∧
    sSup {t | ∃ x ∈ X.FramesOverBasis ξ, t = X.hatN la (X.fj la ξ ν P) x} < 2 * X.hatN la (X.fj la ξ ν P) z0

def ShortVectorBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 →
    ∀ x ∈ X.L', herm X.Gm x ξ = 0 → (∀ e : E, x ≠ e • ξ) →
      ∃ τ : X.Ψ, flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w ≤
        X.maj z0 τ (X.ucomp z0 ξ (X.embV x) τ)

def d6rh (c1 w : ℝ) : ℝ := 1 / (12 * Real.pi * (c1 + w))

def d6La (r p0 : ℕ) (f : ℕ) (d ep0 rh : ℝ) : ℝ :=
  (2 * ReciprocityTheory.MultiplicativeHeights.approxR (r - 2) (d5mu f (r - 2) d (Real.sqrt ep0)) (rh / 40)) ^ (2 * p0 - 1)

def frameIndexBound (r f : ℕ) (d rd NA NC ep0 : ℝ) : ℝ :=
  (f : ℝ) * ((2 * f * (r - 2) : ℕ) : ℝ) ^ 3 * d * NA * Real.sqrt (NC ^ 2 * rd / ep0)

def FundamentalDomainPointBound : Prop :=
  ∀ (r : ℕ) (X : DataX E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (ξ : Fin r → E)
    (ν : X.Ψ → ℝ) (c1 w : ℝ) (z0 : Frame X.Ψ r), ShortVectorHypotheses X la P ξ ν c1 w z0 → (r : ℝ) ≤ w →
    let ep0 := flowEpsilonBound X.g (dE E) (fdeg E) X.NA X.NC c1 w
    let rh := d6rh c1 w
    let La := d6La r X.p0 (fdeg E) (dE E) ep0 rh
    let ms := frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep0
    ∀ n' : ℕ, 1000 * ms / rh ≤ n' →
    ∃ x ∈ X.dom, ∃ lam : Fin (r - 2) → Fin r → E,
      (∀ j, lam j ∈ X.L' ∧ herm X.Gm (lam j) ξ = 0) ∧
      LinearIndependent E (Fin.cons ξ lam : Fin (r - 2 + 1) → Fin r → E) ∧
      (∀ j k : Fin (r - 2), (j : ℕ) < X.p0 - 1 → X.p0 - 1 ≤ (k : ℕ) → herm X.Gm (lam j) (lam k) = 0) ∧
      (∀ j : Fin (r - 2), (j : ℕ) < X.p0 - 1 → (∀ τ : X.Ψ, 0 < (τ.1 (herm X.Gm (lam j) (lam j))).re) ∧
        X.Jz x (X.ucomp x ξ (X.embV (lam j))) = I • X.ucomp x ξ (X.embV (lam j))) ∧
      (∀ j : Fin (r - 2), X.p0 - 1 ≤ (j : ℕ) →
        (∀ τ : X.Ψ, (τ.1 (herm X.Gm (lam j) (lam j))).re < 0) ∧
        X.Jz x (X.ucomp x ξ (X.embV (lam j))) = -(I • X.ucomp x ξ (X.embV (lam j)))) ∧
      (∀ j (τ : X.Ψ), ‖τ.1 (herm X.Gm (lam j) (lam j))‖ ≤ La ^ 2) ∧
      (∀ μ ∈ X.Λp ξ, ∃ e : E, e • ξ ∈ X.Λ ∧ (n' : ℂ) • X.aproj x ξ (X.embV μ) = X.embV (e • ξ)) ∧
      X.fj la ξ ν P x ≠ 0

end

end ReciprocityTheory.ChartRestriction.G.FD
end

