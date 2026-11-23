module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecZero
section
noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.AbsSt.SZ

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

lemma cell_decomp (y : GR n) (hy : ((mR y).toBlocks₂₁).det ≠ 0) :
    ∃ (p g : GR n) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian ∧ mR g = JJ n * nU b ∧
      (mR p).toBlocks₂₁ = 0 ∧ y = p * g := by
  set C := (mR y).toBlocks₂₁ with hC
  set D := (mR y).toBlocks₂₂ with hD
  have hyG : InG (mR y) := y.2
  have hrel : C * Dᴴ = D * Cᴴ := lowerDiagonalBlockAsGL hyG
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hy
  have hCHu : IsUnit (Cᴴ).det := by
    rw [det_conjTranspose]
    exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hy)
  set b := C⁻¹ * D with hb
  have hbH : b.IsHermitian := by
    show bᴴ = b
    calc bᴴ = Dᴴ * (Cᴴ)⁻¹ := by
            rw [hb, conjTranspose_mul, conjTranspose_nonsing_inv]
      _ = C⁻¹ * (C * Dᴴ) * (Cᴴ)⁻¹ := by
            rw [← Matrix.mul_assoc C⁻¹, nonsing_inv_mul _ hCu, Matrix.one_mul]
      _ = C⁻¹ * (D * Cᴴ) * (Cᴴ)⁻¹ := by rw [hrel]
      _ = b := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hCHu, Matrix.mul_one, hb]
  obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hbH)
  set N : M2 n := fromBlocks (-b) (-1) 1 0 with hN
  have h1 : mR g⁻¹ * mR g = 1 := by
    rw [← SZ.mR_mul, inv_mul_cancel]
    rfl
  have h2 : mR g * N = 1 := by
    rw [hg, hN]
    simp only [JJ, nU, fromBlocks_multiply]
    rw [← fromBlocks_one]
    congr 1 <;> simp
  have hM : mR g⁻¹ = N := by
    calc mR g⁻¹ = mR g⁻¹ * (mR g * N) := by rw [h2, Matrix.mul_one]
      _ = N := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  refine ⟨y * g⁻¹, g, b, hbH, hg, ?_, (inv_mul_cancel_right y g).symm⟩
  rw [SZ.mR_mul, hM, ← fromBlocks_toBlocks (mR y), hN, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  rw [← hC, ← hD, Matrix.mul_neg, Matrix.mul_one, ← Matrix.mul_assoc, mul_nonsing_inv _ hCu,
    Matrix.one_mul, neg_add_cancel]

end PositivityTheory.Rg.Sw.AbsSt.SZ

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt.SZ

theorem secZero : NullIff → SecZero := by
  intro hN m n ε c t p q e sL ρ hL P
  have ht : t ≠ 0 := by
    rcases hL.sign with ⟨h, -, -⟩ | ⟨h, -, -⟩
    · rw [h]; exact hL.cpos.ne'
    · rw [h]; exact neg_ne_zero.2 hL.cpos.ne'
  obtain ⟨C, hC, hcell⟩ := hL.cell
  rw [hN m n ε c t hL.cpos ht P]
  constructor
  · intro h y
    have hS : {z : GR n | ((mR z).toBlocks₂₁).det ≠ 0} ⊆ {z | sL P z = 0} := by
      intro z hz
      obtain ⟨p', g, b, hb, hg, hp, rfl⟩ := cell_decomp z hz
      show sL P (p' * g) = 0
      rw [hL.law P p' g hp, hcell P g b hb hg, h b hb, mul_zero, mul_zero]
    have hcl : IsClosed {z : GR n | sL P z = 0} := isClosed_eq (hL.cont P) continuous_const
    exact hcl.closure_subset_iff.2 hS (dense_cell y)
  · intro h b hb
    obtain ⟨g, hg⟩ := exists_of_InG (InG_JJ_nU hb)
    have hh := hcell P g b hb hg
    rw [h g] at hh
    exact (mul_eq_zero.1 hh.symm).resolve_left hC

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecondUnitaryBlockOfPair
section
noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.AbsSt.Proj

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

theorem shape_mul (A B A' B' : Matrix (Fin n) (Fin n) ℂ) :
    fromBlocks A B (-B) A * fromBlocks A' B' (-B') A' =
      fromBlocks (A * A' - B * B') (A * B' + B * A') (-(A * B' + B * A')) (A * A' - B * B') := by
  rw [fromBlocks_multiply]
  congr 1 <;> noncomm_ring

theorem kM_mul (a b a' b' : Matrix (Fin n) (Fin n) ℂ) : kM a b * kM a' b' = kM (a * a') (b * b') := by
  simp only [kM]
  rw [shape_mul]
  congr 1 <;>
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_sub, Matrix.sub_mul, smul_add, smul_sub, smul_neg, neg_add, neg_sub] <;>
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring

theorem kM_one : kM (1 : Matrix (Fin n) (Fin n) ℂ) 1 = 1 := by
  simp only [kM, sub_self, smul_zero, neg_zero]
  rw [← fromBlocks_one]
  congr 1 <;> rw [← two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ), smul_smul] <;> norm_num

theorem kM_conjTranspose (a b : Matrix (Fin n) (Fin n) ℂ) : (kM a b)ᴴ = kM aᴴ bᴴ := by
  simp only [kM, fromBlocks_conjTranspose, conjTranspose_smul, conjTranspose_add, conjTranspose_sub,
    conjTranspose_neg]
  congr 1 <;> simp [Complex.conj_ofReal, map_div₀] <;> module

theorem JJ_comm_shape (A B : Matrix (Fin n) (Fin n) ℂ) :
    JJ n * fromBlocks A B (-B) A = fromBlocks A B (-B) A * JJ n := by
  simp only [JJ, fromBlocks_multiply]
  congr 1 <;> simp

theorem JJ_comm_kM (a b : Matrix (Fin n) (Fin n) ℂ) : JJ n * kM a b = kM a b * JJ n := by
  unfold kM
  exact JJ_comm_shape _ _

theorem first_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u1 (kM a b) = a := by
  simp only [u1, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem second_unitary_block_of_pair (a b : Matrix (Fin n) (Fin n) ℂ) : u2 (kM a b) = b := by
  simp only [u2, kM, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, smul_neg, smul_smul, neg_neg]
  rw [show Complex.I * (Complex.I / 2) = -(1/2 : ℂ) by
    rw [mul_div_assoc', Complex.I_mul_I]; ring]
  module

theorem kM_low (a : Matrix (Fin n) (Fin n) ℂ) : (kM a a).toBlocks₂₁ = 0 := by
  unfold kM
  rw [toBlocks_fromBlocks₂₁]
  simp

theorem kM_of_unitary (a b : Matrix (Fin n) (Fin n) ℂ) (ha : a ∈ unitaryGroup (Fin n) ℂ)
    (hb : b ∈ unitaryGroup (Fin n) ℂ) : ∃ k : GR n, k ∈ KR n ∧ mR k = kM a b := by
  have ha1 : aᴴ * a = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp ha
  have ha2 : a * aᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp ha
  have hb1 : bᴴ * b = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hb
  have hb2 : b * bᴴ = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hb
  let u : GL (Fin n ⊕ Fin n) ℂ :=
    ⟨kM a b, kM aᴴ bᴴ, by rw [kM_mul, ha2, hb2, kM_one], by rw [kM_mul, ha1, hb1, kM_one]⟩
  have hG : u ∈ GR n := by
    show InG (kM a b)
    unfold InG
    rw [kM_conjTranspose, Matrix.mul_assoc, JJ_comm_kM, ← Matrix.mul_assoc, kM_mul, ha1, hb1,
      kM_one, Matrix.one_mul]
  refine ⟨⟨u, hG⟩, ?_, rfl⟩
  show InK (kM a b)
  exact ⟨hG, by rw [kM_conjTranspose, kM_mul, ha1, hb1, kM_one]⟩

theorem KR_shape (k : GR n) (hk : k ∈ KR n) :
    u1 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧ u2 (mR k) ∈ unitaryGroup (Fin n) ℂ ∧
      mR k = kM (u1 (mR k)) (u2 (mR k)) := by
  have hk' : InK (mR k) := hk
  obtain ⟨hG, hU⟩ := hk'
  unfold InG at hG
  set g := mR k with hg
  have hU' : g * gᴴ = 1 := mul_eq_one_comm.mp hU
  have hc : JJ n * g = g * JJ n := by
    calc JJ n * g = (g * gᴴ) * JJ n * g := by rw [hU', Matrix.one_mul]
      _ = g * (gᴴ * JJ n * g) := by simp only [Matrix.mul_assoc]
      _ = g * JJ n := by rw [hG]
  have hc' := hc
  rw [← fromBlocks_toBlocks g] at hc'
  simp only [JJ, fromBlocks_multiply, Matrix.zero_mul, Matrix.one_mul, zero_add, add_zero,
    Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_one, Matrix.mul_zero, neg_zero] at hc'
  rw [fromBlocks_inj] at hc'
  obtain ⟨h1, h2, -, -⟩ := hc'
  have hshape : g = kM (u1 g) (u2 g) := by
    conv_lhs => rw [← fromBlocks_toBlocks g]
    simp only [kM, u1, u2, h1, h2]
    congr 1 <;> match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring
  have hx : kM ((u1 g)ᴴ * u1 g) ((u2 g)ᴴ * u2 g) = kM 1 1 := by
    rw [← kM_mul, ← kM_conjTranspose, ← hshape, hU, kM_one]
  have e1 : (u1 g)ᴴ * u1 g = 1 := by
    have := congrArg u1 hx
    rwa [first_unitary_block_of_pair, first_unitary_block_of_pair] at this
  have e2 : (u2 g)ᴴ * u2 g = 1 := by
    have := congrArg u2 hx
    rwa [second_unitary_block_of_pair, second_unitary_block_of_pair] at this
  exact ⟨Matrix.mem_unitaryGroup_iff'.mpr e1, Matrix.mem_unitaryGroup_iff'.mpr e2, hshape⟩

theorem kIso : KIso := by
  intro n
  exact ⟨fun a b ha hb => kM_of_unitary a b ha hb, kM_mul, kM_one, fun a b => ⟨first_unitary_block_of_pair a b, second_unitary_block_of_pair a b⟩,
    kM_low, KR_shape⟩

end PositivityTheory.Rg.Sw.AbsSt.Proj
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SphericalCharacterInvCompact
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ComplexOrder

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw LocOpA

variable {n : ℕ}

def jLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (w : ℂ) (g : GR n) : ℂ :=
  ∫ x, ((hLoc (g * A * nbEl x * B) : ℂ) ^ w * F0 p q e (g * A * nbEl x * B)) * ψ x

def czLoc (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) [MeasurableSpace (KR n)] (μ : Measure (KR n))
    (w : ℂ) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ

theorem eigen (hI : Iwa) (hM : Mult) (p q : ℕ) (e : ℤ) (A B : GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] (μ : Measure (KR n)) [μ.IsHaarMeasure] (w : ℂ) (y : GR n) :
    ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * A * nbEl x * B) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * A * nbEl x * B)) * ψ x) ∂μ =
      czLoc p q e A B ψ μ w * ((hLoc y : ℂ) ^ w * F0 p q e y) := by
  obtain ⟨p0, k0, hp, hk0, rfl⟩ := hI n y
  have hM1 := (hM n p q e).1
  have hM2 := (hM n p q e).2
  have hJ : ∀ g : GR n, jLoc p q e A B ψ w (p0 * g) =
      ((hLoc p0 : ℂ) ^ w * F0 p q e p0) * jLoc p q e A B ψ w g := by
    intro g
    unfold jLoc
    rw [← integral_const_mul]
    congr 1
    funext x
    have h1 : p0 * g * A * nbEl x * B = p0 * (g * A * nbEl x * B) := by simp only [mul_assoc]
    rw [h1, (hM2 p0 _ hp).1, (hM2 p0 _ hp).2]
    push_cast
    rw [Complex.mul_cpow_ofReal_nonneg (by unfold hLoc; positivity) (by unfold hLoc; positivity)]
    ring
  have hne : F0 p q e k0 ≠ 0 := by
    intro h0
    have h2 := (hM1 k0 k0⁻¹ (inv_mem hk0)).1
    rw [mul_inv_cancel, weight_factor_one, h0, zero_mul] at h2
    exact one_ne_zero h2
  let K0 : KR n := ⟨k0, hk0⟩
  have hK0 : (K0 : GR n) = k0 := rfl
  have hshift : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ =
      F0 p q e k0 * (F0 p q e ((K0 * k : KR n) : GR n))⁻¹ := by
    intro k
    rw [Subgroup.coe_mul, hK0, (hM1 k0 k k.2).1, mul_inv, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  calc _ = ∫ k : KR n, ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ((F0 p q e ((K0 * k : KR n) : GR n))⁻¹ * jLoc p q e A B ψ w ((K0 * k : KR n) : GR n)) ∂μ := by
        congr 1
        funext k
        show (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (p0 * k0 * (k : GR n)) = _
        rw [show p0 * k0 * (k : GR n) = p0 * ((K0 * k : KR n) : GR n) by
          rw [Subgroup.coe_mul, hK0, mul_assoc], hJ, hshift k]
        ring
    _ = ((hLoc p0 : ℂ) ^ w * F0 p q e p0 * F0 p q e k0) *
        ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n) ∂μ := by
        rw [integral_const_mul]
        congr 1
        exact integral_mul_left_eq_self
          (fun k : KR n => (F0 p q e (k : GR n))⁻¹ * jLoc p q e A B ψ w (k : GR n)) K0
    _ = _ := by
        rw [(hM1 p0 k0 hk0).1, (hM1 p0 k0 hk0).2]
        unfold czLoc
        ring

theorem cz_zero (p q : ℕ) (e : ℤ) (a b : M2 n) (ha : InG a) (hb : InG b) (ψ : (Fin n → Fin n → ℝ) → ℂ)
    [MeasurableSpace (KR n)] (μ : Measure (KR n)) :
    czLoc p q e (mkG a ha) (mkG b hb) ψ μ 0 = (a.det * b.det) ^ e *
      ∫ k : KR n, (∫ x, f0 p q (mR (k : GR n) * a * nU (herm x) * b) * ψ x) * (f0 p q (mR (k : GR n)))⁻¹ ∂μ := by
  have hmul : ∀ g h : GR n, mR (g * h) = mR g * mR h := fun _ _ => rfl
  have hdetN : ∀ x, (nU (herm x) : M2 n).det = 1 := by
    intro x
    simp [nU, det_fromBlocks_zero₂₁]
  unfold czLoc
  rw [← integral_const_mul]
  congr 1
  funext k
  have hk : (mR (k : GR n)).det ^ e ≠ 0 := by
    apply zpow_ne_zero
    have h1 : (mR (k : GR n)).det * (mR ((k : GR n)⁻¹)).det = 1 := by
      rw [← det_mul, ← hmul, mul_inv_cancel]
      exact det_one
    exact left_ne_zero_of_mul_eq_one h1
  unfold jLoc
  simp only [Complex.cpow_zero, one_mul, F0, hmul, mR_mkG, nbEl, det_mul, hdetN, mul_one, mul_zpow,
    mul_assoc, integral_const_mul]
  generalize (mR (k : GR n)).det ^ e = D at hk ⊢
  have hD := inv_mul_cancel₀ hk
  rw [mul_inv]
  linear_combination (det a ^ e * (det b ^ e *
    ((∫ (x : Fin n → Fin n → ℝ), f0 (↑p) (↑q) (mR (k : GR n) * (a * (nU (herm x) * b))) * ψ x) *
      (f0 (↑p) (↑q) (mR (k : GR n)))⁻¹))) * hD

end PositivityTheory.Rg.Sw.AbsSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.TopSing
section
noncomputable section

open MeasureTheory Set Filter Topology Matrix
open scoped NNReal

namespace PositivityTheory.Rg.Sw.AbsSt.Vac

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt

variable {m n : ℕ} {G : Type} [Group G]

def hz (Ht : G → ℝ≥0) (sec : PX m n →ₗ[ℂ] (G → ℂ)) (s₀ z : ℂ) (x : G) : ℂ := ((Ht x : ℝ) : ℂ) ^ (z - s₀) * sec 1 x

def Top [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ι : GR n →* G) (p q : ℕ) (e : ℤ) (a b : GR n)
    (nb : (Fin n → Fin n → ℝ) → GR n) (ψ : (Fin n → Fin n → ℝ) → ℂ) (F : G → ℂ) (g : G) : ℂ :=
  ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) ∂μ

variable [TopologicalSpace G] {ε : Fin m → Bool} {c t : ℝ} {p q : ℕ} {e : ℤ} {sL : PX m n →ₗ[ℂ] (GR n → ℂ)}
  {ρ : GR n → PX m n →ₗ[ℂ] PX m n} {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0}
  {sec I : PX m n →ₗ[ℂ] (G → ℂ)} {Λ : Set ((G → ℂ) → ℂ)}

theorem top_sing [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ)
    {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n} {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψ : IsSingTest ψ)
    (hnb : ∀ x, mR (nb x) = nU (herm x)) (F : G → ℂ) (hF : Continuous F) (hinv : ∀ γ ∈ Γ, ∀ g, F (γ * g) = F g)
    (hl : ∀ l ∈ Λ, l F = 0) (g : G) : Top μ ι p q e a b nb ψ F g = 0 := by
  unfold Top
  have : ∀ k : KR n, (∫ x, F (g * ι ((k : GR n) * a * nb x * b)) * ψ x) = 0 := fun k =>
    hG.Λsing F hF hinv hl ψ hψ nb hnb g ((k : GR n) * a) b
  simp only [this, mul_zero, integral_zero]

theorem hz_split (hL : LocData ε c t p q e sL ρ) (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) (g : G) :
    ∃ (y : GR n) (K : ℂ) (r : ℝ), 0 < r ∧ ∀ (z : ℂ) (w : GR n), hz Ht sec s₀ z (g * ι w) =
      K * ((r : ℂ) ^ (z - s₀)) * (((hLoc (y * w) : ℝ) : ℂ) ^ (z - s₀) * F0 p q e (y * w)) := by
  obtain ⟨x0, y, S, r, hr, hg, hsp⟩ := hG.split g
  refine ⟨y, S, r, hr, fun z w => ?_⟩
  have h1 := hsp (y * w)
  have e1 : g * ι w = x0 * ι (y * w) := by rw [hg, map_mul, mul_assoc]
  rw [e1]
  simp only [hz]
  rw [h1.1, h1.2 1, hL.vac, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hr.le (hLoc_nonneg _)]
  ring

theorem top_hz [MeasurableSpace (KR n)] (μ : Measure (KR n)) (hL : LocData ε c t p q e sL ρ)
    (hG : GlobData ε c sL ρ G Pp Γ ι s₀ Ht sec I Λ) {a b : GR n} {nb : (Fin n → Fin n → ℝ) → GR n}
    {ψ : (Fin n → Fin n → ℝ) → ℂ} {cz : ℂ → ℂ}
    (hceig : ∀ (w : ℂ) (y : GR n), ∫ k : KR n, (F0 p q e (k : GR n))⁻¹ * (∫ x, ((hLoc (y * (k : GR n) * a * nb x * b) : ℂ) ^ w *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) ∂μ = cz w * ((hLoc y : ℂ) ^ w * F0 p q e y))
    (z : ℂ) (g : G) : Top μ ι p q e a b nb ψ (hz Ht sec s₀ z) g = cz (z - s₀) * hz Ht sec s₀ z g := by
  obtain ⟨y, K, r, hr, hsp⟩ := hz_split hL hG g
  have e1 : ∀ (k : KR n) x, hz Ht sec s₀ z (g * ι ((k : GR n) * a * nb x * b)) * ψ x =
      (K * (r : ℂ) ^ (z - s₀)) * ((((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := by
    intro k x
    rw [hsp]
    simp only [mul_assoc]
  have e2 : hz Ht sec s₀ z g = K * (r : ℂ) ^ (z - s₀) * (((hLoc y : ℝ) : ℂ) ^ (z - s₀) * F0 p q e y) := by
    have := hsp z 1
    rwa [map_one, mul_one, mul_one] at this
  unfold Top
  simp_rw [e1, MeasureTheory.integral_const_mul]
  have e3 : ∀ k : KR n, (F0 p q e (k : GR n))⁻¹ * (K * (r : ℂ) ^ (z - s₀) * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) = (K * (r : ℂ) ^ (z - s₀)) * ((F0 p q e (k : GR n))⁻¹ * ∫ x, (((hLoc (y * (k : GR n) * a * nb x * b) : ℝ) : ℂ) ^ (z - s₀) *
        F0 p q e (y * (k : GR n) * a * nb x * b)) * ψ x) := fun k => by ring
  simp_rw [e3, MeasureTheory.integral_const_mul, hceig, e2]
  ring

end PositivityTheory.Rg.Sw.AbsSt.Vac
end
end

