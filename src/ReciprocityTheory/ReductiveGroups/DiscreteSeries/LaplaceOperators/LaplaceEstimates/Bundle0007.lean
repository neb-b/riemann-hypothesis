module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ImageLeClosGen
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.LFSingleNe
section
noncomputable section

open Matrix Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence

open Formalism.QuantumDeterminants ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

variable {k r : ℕ}

def psiC (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Z : Mat k r) : ℂ :=
  Complex.I / 2 * (LF z c Z - starRingEnd ℂ (LF z c (Hpk k r * Zᴴ * Hpk k r)))

theorem LF_comb (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (s t : ℂ) (X Y : Mat k r) :
    LF z c (s • (X + t • Y)) = s * (LF z c X + t * LF z c Y) := by
  simp only [LF, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun p _ => by ring

theorem parts (Z : Mat k r) :
    let S := Hpk k r * Zᴴ * Hpk k r
    let Y1 := (1 / 2 : ℂ) • (Z + (-1 : ℂ) • S)
    let Y2 := (-Complex.I / 2) • (Z + (1 : ℂ) • S)
    Hpk k r * Y1ᴴ * Hpk k r = -Y1 ∧ Hpk k r * Y2ᴴ * Hpk k r = -Y2 ∧ Z = Y1 + Complex.I • Y2 := by
  intro S Y1 Y2
  have hS : Hpk k r * Sᴴ * Hpk k r = Z := by
    simp only [S, conjTranspose_mul, conjTranspose_conjTranspose, Hpk_herm, ← Matrix.mul_assoc, Hpk_sq,
      Matrix.one_mul]
    rw [Matrix.mul_assoc, Hpk_sq, Matrix.mul_one]
  have hZ : Hpk k r * Zᴴ * Hpk k r = S := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Y1, conjTranspose_smul, conjTranspose_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hS, hZ]
    ext i j; simp; ring
  · simp only [Y2, conjTranspose_smul, conjTranspose_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_add, Matrix.add_mul, hS, hZ]
    ext i j; simp; ring
  · ext i j
    simp only [Y1, Y2, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (Z i j + S i j) / 2 * Complex.I_mul_I

theorem psiC_parts (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (Z S : Mat k r) :
    Complex.I * ((LF z c ((1 / 2 : ℂ) • (Z + (-1 : ℂ) • S))).re : ℂ) +
      Complex.I * (Complex.I * ((LF z c ((-Complex.I / 2) • (Z + (1 : ℂ) • S))).re : ℂ)) =
      Complex.I / 2 * (LF z c Z - starRingEnd ℂ (LF z c S)) := by
  rw [LF_comb, LF_comb]
  apply Complex.ext <;> simp <;> ring

open scoped Matrix.Norms.Operator in
theorem st_mem {Z : Mat k r} (h : Z ∈ levF (levB k r) 0) : Hpk k r * Zᴴ * Hpk k r ∈ levF (levB k r) 0 :=
  isAdjB.mem Z h

theorem nxt_val (p : Fin r) : (nxt k r p).val = if p.val + 1 < r then p.val + 1 else r + k := by
  unfold nxt; split_ifs <;> rfl

theorem LF_single (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (a b : Fin (2 * r + k + 1)) (s : ℂ) :
    LF z c (Matrix.single a b s) =
      ∑ p, if a = eI k r p ∧ b = nxt k r p then c p * (kap k r z p * s) else 0 := by
  refine sum_congr rfl fun p _ => ?_
  rw [Matrix.single_apply]; split_ifs <;> simp

theorem st_single (a b : Fin (2 * r + k + 1)) :
    Hpk k r * (Matrix.single a b (1 : ℂ))ᴴ * Hpk k r =
      Matrix.single (flipB k r b) (flipB k r a) (sgnB k r b * sgnB k r a) := by
  ext i j
  rw [mul_Hpk_apply, Hpk_mul_apply, conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = flipB k r j ∧ b = flipB k r i
  · obtain ⟨rfl, rfl⟩ := h
    simp [flipB_flipB, sgnB_flip]
  · rw [if_neg h, if_neg, star_zero, mul_zero, zero_mul]
    rintro ⟨rfl, rfl⟩
    exact h ⟨(flipB_flipB a).symm, (flipB_flipB b).symm⟩

def Simple (k r : ℕ) (a b : Fin (2 * r + k + 1)) : Prop :=
  levB k r b = levB k r a + 1 ∧ ¬ (r ≤ a.val ∧ a.val < r + k) ∧ ¬ (r ≤ b.val ∧ b.val < r + k)

theorem simple_of {a b : Fin (2 * r + k + 1)} {p : Fin r} :
    (a = eI k r p ∧ b = nxt k r p → Simple k r a b) ∧
      (flipB k r b = eI k r p ∧ flipB k r a = nxt k r p → Simple k r a b) := by
  have := p.isLt
  have := a.isLt
  have := b.isLt
  simp only [Fin.ext_iff, flipB_val, nxt_val, eI, Simple, levB]
  constructor <;> rintro ⟨h1, h2⟩ <;> split_ifs at h1 h2 ⊢ <;> omega

theorem psiC_zero (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) {a b : Fin (2 * r + k + 1)}
    (h : ¬ Simple k r a b) : psiC z c (Matrix.single a b 1) = 0 := by
  rw [psiC, st_single, LF_single, LF_single, sum_eq_zero fun p _ => if_neg fun hp => h (simple_of.1 hp),
    sum_eq_zero fun p _ => if_neg fun hp => h (simple_of.2 hp)]
  simp

theorem LF_single_ne {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} (hc : ∀ p, c p ≠ 0)
    (hT : 0 < Tz k r z) (p : Fin r) {s : ℂ} (hs : s ≠ 0) :
    LF z c (Matrix.single (eI k r p) (nxt k r p) s) ≠ 0 := by
  rw [LF_single, sum_eq_single p (fun q _ hq => if_neg fun h => hq
    (Fin.ext (by have := congrArg Fin.val h.1; exact this.symm))) (by simp), if_pos ⟨rfl, rfl⟩]
  refine mul_ne_zero (hc p) (mul_ne_zero ?_ hs)
  unfold kap
  split_ifs
  · simp
  · exact_mod_cast (Real.sqrt_pos.mpr hT).ne'

theorem psiC_ne {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} (hc : ∀ p, c p ≠ 0) (hT : 0 < Tz k r z)
    {a b : Fin (2 * r + k + 1)} (h : Simple k r a b) : psiC z c (Matrix.single a b 1) ≠ 0 := by
  have ha := a.isLt
  have hb := b.isLt
  have hI : Complex.I / 2 ≠ 0 := div_ne_zero Complex.I_ne_zero two_ne_zero
  rw [psiC, st_single]
  refine mul_ne_zero hI ?_
  unfold Simple levB at h
  by_cases h1 : a.val < r
  · have e1 : a = eI k r ⟨a.val, h1⟩ := rfl
    have e2 : b = nxt k r ⟨a.val, h1⟩ := Fin.ext (by rw [nxt_val]; split_ifs at h ⊢ <;> simp only at * <;> omega)
    rw [LF_single z c (flipB k r b), sum_eq_zero fun p _ => if_neg fun hp => ?_, map_zero, sub_zero]
    · have := LF_single_ne hc hT ⟨a.val, h1⟩ one_ne_zero
      rwa [← e1, ← e2] at this
    · have h2 := congrArg Fin.val hp.2
      have := p.isLt
      rw [flipB_val, nxt_val] at h2
      split_ifs at h2 <;> omega
  · have h3 : r + k ≤ a.val ∧ b.val = a.val + 1 := by split_ifs at h <;> omega
    have hp : 2 * r + k - b.val < r := by omega
    have e1 : flipB k r b = eI k r ⟨_, hp⟩ := Fin.ext (by rw [flipB_val, if_pos (by omega)]; rfl)
    have e2 : flipB k r a = nxt k r ⟨_, hp⟩ := Fin.ext (by
      rw [flipB_val, nxt_val]; split_ifs <;> simp only at * <;> omega)
    rw [LF_single z c a, sum_eq_zero fun p _ => if_neg fun hq => ?_, zero_sub, neg_ne_zero, e1, e2]
    · refine (map_ne_zero _).mpr (LF_single_ne hc hT _ ?_)
      unfold sgnB; split_ifs <;> simp
    · have h2 := congrArg Fin.val hq.1
      have := p.isLt
      simp only [eI] at h2; omega

end ReciprocityTheory.ChartRestriction.DS.Lap.EvaluationEquivalence
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.ToL2CongrOnUnitaryBis
section
noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.QuotA

open ReciprocityTheory.ChartRestriction.DS

section Group

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}

theorem uh_mul {H A B : Mat k r} (hA : A ∈ Formalism.QuantumDeterminants.UH H) (hB : B ∈ Formalism.QuantumDeterminants.UH H) :
    A * B ∈ Formalism.QuantumDeterminants.UH H := by
  show (A * B)ᴴ * H * (A * B) = H
  have hA' : Aᴴ * H * A = H := hA
  have hB' : Bᴴ * H * B = H := hB
  calc (A * B)ᴴ * H * (A * B) = Bᴴ * (Aᴴ * H * A) * B := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = H := by rw [hA', hB']

theorem cay_inv {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) : P * P⁻¹ = 1 ∧ P⁻¹ * P = 1 ∧ (P⁻¹)ᴴ * Pᴴ = 1 := by
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP.1
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  refine ⟨h1, Matrix.nonsing_inv_mul P hPu, ?_⟩
  rw [← conjTranspose_mul, h1, conjTranspose_one]

theorem ujset_conj {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {M : Mat k r}
    (hM : M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : P * M * P⁻¹ ∈ UJset ε := by
  obtain ⟨h1, -, h2⟩ := cay_inv hP
  have hC : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hM' : Mᴴ * Formalism.QuantumDeterminants.Hpk k r * M = Formalism.QuantumDeterminants.Hpk k r := hM
  show (P * M * P⁻¹)ᴴ * Jm ε * (P * M * P⁻¹) = Jm ε
  calc (P * M * P⁻¹)ᴴ * Jm ε * (P * M * P⁻¹) = (P⁻¹)ᴴ * (Mᴴ * (Pᴴ * Jm ε * P) * M) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = ((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) := by rw [hC, hM', ← hC]; simp only [Matrix.mul_assoc]
    _ = Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem uh_conj {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {u : Mat k r} (hu : u ∈ UJset ε) :
    P⁻¹ * u * P ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  obtain ⟨h1, -, h2⟩ := cay_inv hP
  have hC : Pᴴ * Jm ε * P = Formalism.QuantumDeterminants.Hpk k r := hP.2
  have hu' : uᴴ * Jm ε * u = Jm ε := hu
  show (P⁻¹ * u * P)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P⁻¹ * u * P) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hC]
  calc (P⁻¹ * u * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * u * P)
      = Pᴴ * (uᴴ * (((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹)) * u) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * Jm ε * P := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one, hu']

end Group

section Per

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {Vp : Type*} [NormedAddCommGroup Vp]
  [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

theorem ae_bdata {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} (hB : IsBData z c u π μW μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hW := hB.2.2.2.2.1
  have hN := hB.2.2.2.2.2
  have := hW.1
  have := hN.1
  have h1 : (μW.prod μN) ({x | Matrix.of x ∉ Formalism.QuantumDeterminants.UWset k r z} ×ˢ Set.univ) = 0 := by
    rw [Measure.prod_prod, hW.2.2.1, zero_mul]
  have h2 : (μW.prod μN) (Set.univ ×ˢ {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r}) = 0 := by
    rw [Measure.prod_prod, hN.2.2.1, mul_zero]
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) (measure_union_null h1 h2)
  simp only [Set.mem_ofPred_eq, not_and_or] at hp
  rcases hp with hp | hp
  · exact Or.inl ⟨hp, trivial⟩
  · exact Or.inr ⟨trivial, hp⟩

theorem per_congr {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) (ψ : Mat k r → ℂ) {F G : Mat k r → ℂ} (hFG : ∀ g ∈ UJset ε, F g = G g)
    (ξ : Vp) {x : Mat k r} (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN ψ π F ξ x = per P μW μN ψ π G ξ x := by
  unfold per sInt
  apply integral_congr_ae
  filter_upwards [ae_bdata hB] with p hp
  have hm : Matrix.of p.1 * Matrix.of p.2 * x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
    uh_mul (uh_mul hp.1.1 hp.2.1) hx
  rw [hFG _ (ujset_conj hP hm)]

theorem eabB_zero {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P) {f : Mat k r → Vp}
    (hf : ∀ y ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), f y = 0) (a b : Fin (2 * r + k + 1)) {x : Mat k r}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : eabB ε P a b f x = 0 := by
  obtain ⟨-, h2, -⟩ := cay_inv hP
  have key : ∀ X, inG ε X → (fun t : ℝ => f (P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P)) =
      fun _ => 0 := by
    intro X hX
    funext t
    apply hf
    have : P⁻¹ * (P * x * P⁻¹ * NormedSpace.exp ((t : ℂ) • X)) * P =
        x * (P⁻¹ * NormedSpace.exp ((t : ℂ) • X) * P) := by
      simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [this]
    exact uh_mul hx (uh_conj hP (exp_smul_mem_UJset hX t))
  unfold eabB S7.EabV S7.EcV S7.RdV
  simp only
  rw [key _ (SmDerA.inG_cpart1 ε _), key _ (SmDerA.inG_cpart2 ε _)]
  simp

theorem per_add {u : Fin k → ℝ} {h : ℝ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ}
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {P : Mat k r} (hP : Formalism.MainNotions.S.IsCayley k r ε P)
    (hB : IsBData z c u π μW μN) (hp : pOf ε = k + r) (hq : qOf ε = r + 1) (hgap : StepGap ε r h)
    {F G : Mat k r → ℂ} (hFc : ContinuousOn F (UJset ε))
    (hFb : ∃ C : ℝ, ∀ g ∈ UJset ε, ‖F g‖ ≤ C * frob g ^ (1 - aExp ε h)) (hGc : ContinuousOn G (UJset ε))
    (hGb : ∃ C : ℝ, ∀ g ∈ UJset ε, ‖G g‖ ≤ C * frob g ^ (1 - aExp ε h)) (ξ : Vp) {x : Mat k r}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π (F + G) ξ x =
      per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π F ξ x + per P μW μN (Formalism.MainNotions.S.psiGen k r z c) π G ξ x := by
  have hi := (per_spec k r ε u h z c Vp π μW μN P hP hB hp hq hgap).1
  obtain ⟨CF, hCF⟩ := hFb
  obtain ⟨CG, hCG⟩ := hGb
  have iF := hi F CF hFc hCF x hx ξ
  have iG := hi G CG hGc hCG x hx ξ
  unfold per sInt
  rw [← integral_add iF iG]
  congr 1
  funext p
  simp [add_smul]

theorem per_smul (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (a : ℂ) (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π (a • F) ξ x = a • per P μW μN ψ π F ξ x := by
  unfold per sInt
  rw [← integral_smul]
  congr 1
  funext p
  exact (smul_smul a _ _).symm

end Per

section Fun

variable {n : ℕ} {ε : Fin n → Bool}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem contOn_of_smooth {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Formalism.REAL.SmoothOnG ε F) :
    ContinuousOn F (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F', hU, hg, hF', hEq⟩ := hF g₀ hg₀
  have hc : ContinuousAt F' g₀ := hF'.continuousOn.continuousAt (hU.mem_nhds hg)
  refine hc.continuousWithinAt.congr_of_eventuallyEq ?_ (hEq g₀ hg hg₀)
  filter_upwards [inter_mem_nhdsWithin (UJset ε) (hU.mem_nhds hg)] with g hg'
  exact hEq g hg'.2 hg'.1

theorem eqOn_unitary_of_toL2_eq {F G : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : IsSmoothL2 ε F) (hG : IsSmoothL2 ε G)
    (h : toL2 ε F = toL2 ε G) : ∀ g ∈ UJset ε, F g = G g := by
  have hF2 : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hF.2 []
  have hG2 : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := hG.2 []
  unfold toL2 at h
  rw [dite_eq_left hF2, dite_eq_left hG2] at h
  have hae := (MemLp.toLp_eq_toLp_iff hF2 hG2).1 h
  have hcF : Continuous (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) := Formalism.REAL.continuous_smooth_on_group_eval hF.1
  have hcG : Continuous (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) := Formalism.REAL.continuous_smooth_on_group_eval hG.1
  have heq := (hcF.ae_eq_iff_eq (Formalism.REAL.muG ε) hcG).1 hae
  intro g hg
  obtain ⟨y, rfl⟩ := exists_unitary_preimage ε hg
  exact congrFun heq y

end Fun

end ReciprocityTheory.ChartRestriction.DS.Lap.QuotA
end
end

