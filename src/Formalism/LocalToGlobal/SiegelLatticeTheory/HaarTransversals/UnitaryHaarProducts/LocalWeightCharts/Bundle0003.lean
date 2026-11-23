module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.Closed

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SchurOrthogonalityRelations
section
noncomputable section

namespace WlocSk.Port

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ENNReal
open PI.UpqRep

section Transport

variable {n : ℕ} (ε : Fin n → Bool) (P : Matrix (Fin n) (Fin n) ℂ)

def conjPrime₂ (g : UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (P⁻¹ * toM g * P)

lemma conjP_isClosedEmbedding (hP : IsUnit P) : IsClosedEmbedding (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  let e : Matrix (Fin n) (Fin n) ℂ ≃ₜ (Fin n → Fin n → ℂ) :=
    { toFun := fun m => Matrix.of.symm (P⁻¹ * m * P)
      invFun := fun x => P * Matrix.of x * P⁻¹
      left_inv := fun m => by
        show P * (P⁻¹ * m * P) * P⁻¹ = m
        calc P * (P⁻¹ * m * P) * P⁻¹ = (P * P⁻¹) * m * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = m := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      right_inv := fun x => by
        show P⁻¹ * (P * Matrix.of x * P⁻¹) * P = Matrix.of x
        calc P⁻¹ * (P * Matrix.of x * P⁻¹) * P = (P⁻¹ * P) * Matrix.of x * (P⁻¹ * P) := by
              simp only [Matrix.mul_assoc]
          _ = Matrix.of x := by rw [h1, Matrix.one_mul, Matrix.mul_one]
      continuous_toFun := by
        show Continuous fun m : Matrix (Fin n) (Fin n) ℂ => P⁻¹ * m * P
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := by
        show Continuous fun x : Fin n → Fin n → ℂ => P * Matrix.of x * P⁻¹
        exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  exact e.isClosedEmbedding.comp (isClosedEmbeddingMatrix n ε).1

lemma conjP_measurableEmbedding (hP : IsUnit P) : MeasurableEmbedding (conjPrime₂ ε P) :=
  (conjP_isClosedEmbedding ε P hP).measurableEmbedding

theorem haar_transport (hP : IsUnit P) (μ : Measure (Fin n → Fin n → ℂ)) [SigmaFinite μ] (h0 : μ ≠ 0)
    (hconc : μ {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * Jm ε * P)} = 0)
    (hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P), μ.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ μ = (c • muG ε).map (conjPrime₂ ε P) := by
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hdet
  have hE := conjP_measurableEmbedding ε P hP
  set ψ := conjPrime₂ ε P with hψdef

  have hrange : {x : Fin n → Fin n → ℂ | Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P)} ⊆ Set.range ψ := by
    intro x hx
    have hx' : (Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x = Pᴴ * Jm ε * P := hx
    have hin : inUJ ε (P * Matrix.of x * P⁻¹) := by
      show (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹) = Jm ε
      calc (P * Matrix.of x * P⁻¹)ᴴ * Jm ε * (P * Matrix.of x * P⁻¹)
          = (P⁻¹)ᴴ * ((Matrix.of x)ᴴ * (Pᴴ * Jm ε * P) * Matrix.of x) * P⁻¹ := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (P⁻¹)ᴴ * (Pᴴ * Jm ε * P) * P⁻¹ := by rw [hx']
        _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Jm ε := by rw [h2]; simp
    have hr := (isClosedEmbeddingMatrix n ε).2
    have hmem : P * Matrix.of x * P⁻¹ ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [hr]; exact hin
    obtain ⟨g, hg⟩ := hmem
    refine ⟨g, ?_⟩
    show Matrix.of.symm (P⁻¹ * toM g * P) = x
    have hg' : toM g = P * Matrix.of x * P⁻¹ := hg
    rw [hg']
    calc Matrix.of.symm (P⁻¹ * (P * Matrix.of x * P⁻¹) * P)
        = Matrix.of.symm ((P⁻¹ * P) * Matrix.of x * (P⁻¹ * P)) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [h1, Matrix.one_mul, Matrix.mul_one]; rfl

  have hinto : ∀ g : UJ ε, P⁻¹ * toM g * P ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P) := by
    intro g
    have hg : (toM g)ᴴ * Jm ε * toM g = Jm ε := g.2
    show (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P) = Pᴴ * Jm ε * P
    have hPP : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
    calc (P⁻¹ * toM g * P)ᴴ * (Pᴴ * Jm ε * P) * (P⁻¹ * toM g * P)
        = Pᴴ * (toM g)ᴴ * ((P⁻¹)ᴴ * Pᴴ) * Jm ε * (P * P⁻¹) * toM g * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * ((toM g)ᴴ * Jm ε * toM g) * P := by
          rw [hPP, h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Pᴴ * Jm ε * P := by rw [hg]

  set ν := μ.comap ψ with hνdef
  have hmapν : ν.map ψ = μ := by
    rw [hνdef, hE.map_comap]
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    refine measure_mono_null ?_ hconc
    intro x hx
    by_contra hc
    have hc' : Matrix.of x ∈ PI.UpqRep.UH (Pᴴ * Jm ε * P) := by
      by_contra h'
      exact hc h'
    exact hx (hrange hc')
  have hσν : SigmaFinite ν := SigmaFinite.of_map ν hE.measurable.aemeasurable (by rw [hmapν]; infer_instance)
  have hinj : ∀ a b : Measure (UJ ε), a.map ψ = b.map ψ → a = b := by
    intro a b hab
    rw [← hE.comap_map a, ← hE.comap_map b, hab]
  have hleft : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    apply hinj
    have hcomp : ψ ∘ (fun h : UJ ε => g * h) =
        (fun x => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) ∘ ψ := by
      funext h
      show Matrix.of.symm (P⁻¹ * toM (g * h) * P) =
        Matrix.of.symm ((P⁻¹ * toM g * P) * (P⁻¹ * toM h * P))
      congr 1
      show P⁻¹ * (toM g * toM h) * P = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P)
      calc P⁻¹ * (toM g * toM h) * P = P⁻¹ * toM g * (P * P⁻¹) * toM h * P := by
            rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = (P⁻¹ * toM g * P) * (P⁻¹ * toM h * P) := by simp only [Matrix.mul_assoc]
    have hmul : Measurable (fun h : UJ ε => g * h) := measurable_const_mul g
    have hlm : Measurable (fun x : Fin n → Fin n → ℂ => Matrix.of.symm ((P⁻¹ * toM g * P) * Matrix.of x)) := by
      apply Continuous.measurable
      show Continuous fun x : Fin n → Fin n → ℂ => (P⁻¹ * toM g * P) * Matrix.of x
      exact continuous_const.matrix_mul continuous_id
    rw [Measure.map_map hE.measurable hmul, hcomp, ← Measure.map_map hlm hE.measurable, hmapν]
    exact hinv _ (hinto g)

  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds (1 : UJ ε)
  have hK0 : muG ε K ≠ 0 := (Measure.measure_pos_of_mem_nhds (muG ε) hKn).ne'
  have hKt : muG ε K ≠ ∞ := hK.measure_lt_top.ne
  have heq := measure_eq_div_smul ν (muG ε) hK0 hKt
  set c := ν K / muG ε K with hc
  have hcne0 : c ≠ 0 := by
    intro h
    apply h0
    rw [← hmapν, heq, h, zero_smul, Measure.map_zero]
  have hcnetop : c ≠ ∞ := by
    intro h
    have hnull : ∀ i, muG ε (spanningSets ν i) = 0 := by
      intro i
      have hlt := measure_spanningSets_lt_top ν i
      have hS : ν (spanningSets ν i) = (c • muG ε) (spanningSets ν i) :=
        congrArg (fun m : Measure (UJ ε) => m (spanningSets ν i)) heq
      rw [hS, Measure.smul_apply, smul_eq_mul, h] at hlt
      by_contra hne
      rw [ENNReal.top_mul hne] at hlt
      exact lt_irrefl _ hlt
    have : muG ε Set.univ = 0 := by
      rw [← iUnion_spanningSets ν]
      exact measure_iUnion_null hnull
    have hne : muG ε ≠ 0 := NeZero.ne _
    exact hne (Measure.measure_univ_eq_zero.mp this)
  exact ⟨c, hcne0, hcnetop, by rw [← hmapν, ← heq]⟩

end Transport

theorem schur_orthogonality_relations : WlocSk.SchurG := by
  intro k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨_, hσ, _, _, hG, _⟩ := hyp
  obtain ⟨P, ⟨⟨hPu, hPJ⟩, _⟩, hDS⟩ := hσ
  have : Nontrivial H := hDS.2.1
  obtain ⟨d₀, hd₀, hF⟩ := PIW.HCFdeg.formal_degree_abstract_form _ (Formalism.MainNotions.CayleySignature.eps48 k r) H (fun g => σ (P⁻¹ * g * P))
    hDS.2.2.1 hDS.2.2.2.1 hDS.2.2.2.2.1
  have : SigmaFinite μG := hG.1
  have hPJ' : Pᴴ * PI.UpqRep.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) * P = PI.UpqRep.Hpk k r := hPJ
  have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (Pᴴ * PI.UpqRep.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) * P)} = 0 := by
    rw [hPJ']; exact hG.2.2.1
  have hinv : ∀ s ∈ PI.UpqRep.UH (Pᴴ * PI.UpqRep.Jm (Formalism.MainNotions.CayleySignature.eps48 k r) * P),
      μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
    rw [hPJ']; intro s hs; exact hG.2.2.2 s hs
  obtain ⟨cc, hc0, hctop, hμ⟩ := haar_transport (Formalism.MainNotions.CayleySignature.eps48 k r) P hPu μG hG.2.1 hconc hinv
  have hE := conjP_measurableEmbedding (Formalism.MainNotions.CayleySignature.eps48 k r) P hPu
  have hct : 0 < cc.toReal := ENNReal.toReal_pos hc0 hctop
  refine ⟨d₀ / cc.toReal, div_pos hd₀ hct, fun v₁ w₁ v₂ w₂ => ?_⟩
  obtain ⟨hI, hV⟩ := hF v₁ w₁ v₂ w₂
  have hfun : (fun g : UJ (Formalism.MainNotions.CayleySignature.eps48 k r) =>
      (fun x : Formalism.QuantumDeterminants.Mt k r => ⟪w₁, σ (Matrix.of x) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of x) v₂⟫_ℂ)
        (conjPrime₂ (Formalism.MainNotions.CayleySignature.eps48 k r) P g)) =
      fun g => coefOn (ε := Formalism.MainNotions.CayleySignature.eps48 k r) (fun g => σ (P⁻¹ * g * P)) v₁ w₁ g *
        star (coefOn (ε := Formalism.MainNotions.CayleySignature.eps48 k r) (fun g => σ (P⁻¹ * g * P)) v₂ w₂ g) := rfl
  rw [hμ]
  refine ⟨?_, ?_⟩
  · rw [hE.integrable_map_iff]
    show Integrable ((fun x : Formalism.QuantumDeterminants.Mt k r =>
      ⟪w₁, σ (Matrix.of x) v₁⟫_ℂ * star ⟪w₂, σ (Matrix.of x) v₂⟫_ℂ) ∘ conjPrime₂ (Formalism.MainNotions.CayleySignature.eps48 k r) P) _
    rw [Function.comp_def, hfun]
    exact hI.smul_measure hctop
  · rw [hE.integral_map, hfun, integral_smul_measure, hV]
    rw [Complex.real_smul]
    have hd₀' : (d₀ : ℂ) ≠ 0 := by exact_mod_cast hd₀.ne'
    have hc' : (cc.toReal : ℂ) ≠ 0 := by exact_mod_cast hct.ne'
    push_cast
    field_simp

end WlocSk.Port
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Unfold
section
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal

namespace WlocSk

namespace Grp

def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

lemma sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sig k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold sig; split_ifs <;> rfl

lemma sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  have h1 := sig_val k r i
  have h2 := sig_val k r (sig k r i)
  split_ifs at h1 h2 <;> omega

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  have h1 := sig_val k r i
  unfold sgn
  split_ifs at h1 ⊢ <;> first | rfl | (exfalso; omega)

lemma Hpk_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  have e1 : (j = sig k r i) ↔ j.val = (sig k r i).val := Fin.ext_iff
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  unfold Formalism.QuantumDeterminants.Hpk sgn
  simp only [e1, e2]
  split_ifs at * <;> first | rfl | (exfalso; omega)

lemma Hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hpk_eq k r i, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq, sig_sig, sgn_sig, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm]; unfold sgn; split_ifs <;> norm_num
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

variable {k r : ℕ}

lemma one_mem : (1 : Mat k r) ∈ Gr k r := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

lemma mul_mem {a b : Mat k r} (ha : a ∈ Gr k r) (hb : b ∈ Gr k r) : a * b ∈ Gr k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

lemma of_mul_mem {s x : Mat k r} (hs : s ∈ Gr k r) (hsx : s * x ∈ Gr k r) : x ∈ Gr k r := by
  have hs' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hs
  have hsx' : (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = Formalism.QuantumDeterminants.Hpk k r := hsx
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (sᴴ * Formalism.QuantumDeterminants.Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hsx'

lemma inv_left {g : Mat k r} (hg : g ∈ Gr k r) :
    (Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r) * g = 1 := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  calc Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r * g
      = Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

lemma inv_eq {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r :=
  Matrix.inv_eq_left_inv (inv_left hg)

lemma inv_mul {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ * g = 1 := by
  rw [inv_eq hg]; exact inv_left hg

lemma mul_inv {g : Mat k r} (hg : g ∈ Gr k r) : g * g⁻¹ = 1 := by
  rw [inv_eq hg]; exact mul_eq_one_comm.mp (inv_left hg)

lemma inv_mem {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ ∈ Gr k r := by
  apply of_mul_mem hg
  rw [mul_inv hg]; exact one_mem

lemma isClosed_Gr : IsClosed (Gr k r) := by
  have hc : Continuous (fun x : Mat k r => xᴴ * Formalism.QuantumDeterminants.Hpk k r * x) := by fun_prop
  exact isClosed_eq hc continuous_const

lemma continuous_of : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mat k r)) := continuous_id

lemma measurableSet_Gr : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Gr k r} :=
  (isClosed_Gr.preimage continuous_of).measurableSet

end Grp

section Unfold

variable {k r : ℕ}

lemma continuous_mulP : Continuous (mulP (k := k) (r := r)) := by
  have h1 : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mat k r) :=
    continuous_fst
  have h2 : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mat k r) :=
    continuous_snd
  exact h1.matrix_mul h2

lemma measurable_mulP : Measurable (mulP (k := k) (r := r)) := continuous_mulP.measurable

lemma continuous_rmul (x : Formalism.QuantumDeterminants.Mt k r) :
    Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  have h1 : Continuous fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mat k r) := continuous_id
  exact h1.matrix_mul continuous_const

theorem unfold_weil {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {cS : ℝ≥0∞} (hcS : cS ≠ ⊤)
    (hP : (μW.prod μN).map mulP = cS • μS) (hQ : IsQuotMeas μG μS ν)
    (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) ∂ν =
      cS * ∫⁻ y, f y ∂μG := by
  have hin : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) =
        cS * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    have hm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
      hf.comp (continuous_rmul x).measurable
    have h := lintegral_map (μ := μW.prod μN) hm measurable_mulP
    rw [hP, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  rw [lintegral_congr hin, lintegral_const_mul' _ _ hcS, hQ f hf]

theorem nu_conc {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} {T : Set (Mat k r)} (hQ : IsQuotMeas μG μS ν)
    (hG : μG {x | Matrix.of x ∉ Gr k r} = 0) (hS0 : μS ≠ 0) (hSc : μS {x | Matrix.of x ∉ T} = 0)
    (hTG : T ⊆ Gr k r) : ν {x | Matrix.of x ∉ Gr k r} = 0 := by
  set E : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Gr k r} with hEdef
  have hE : MeasurableSet E := Grp.measurableSet_Gr.compl
  have hw := hQ (E.indicator 1) (measurable_one.indicator hE)
  rw [lintegral_indicator_one hE, hG] at hw
  have hlow : ∀ x, E.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, E.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ T := ae_iff.mpr hSc
      have h1 : ∀ᵐ s ∂μS, E.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) = (1 : ℝ≥0∞) := by
        filter_upwards [hae] with s hs
        apply Set.indicator_of_mem
        intro hsx
        exact hx (Grp.of_mul_mem (hTG hs) hsx)
      rw [lintegral_congr_ae h1, lintegral_one]
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have h2 := lintegral_mono (μ := ν) hlow
  rw [lintegral_indicator_const hE, ← hw] at h2
  have hpos : μS Set.univ ≠ 0 := by
    intro h0; exact hS0 (Measure.measure_univ_eq_zero.mp h0)
  exact (mul_eq_zero.mp (le_zero_iff.mp h2)).resolve_left hpos

end Unfold

section FromSteps

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ}
  {b : Fin (2 * r + 2) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat k r → (H →L[ℂ] H)} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)} {w : H}
  {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}

lemma S_sub_G (hSG : SGrp) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    Formalism.QuantumDeterminants.Sset k r z ⊆ Gr k r := by
  obtain ⟨hset, -⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hW, hN, -⟩ := hSG k r z c hz hT
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact Grp.mul_mem (hW hh) (hN hm)

theorem unfold_of (hSP : SProd) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    ∃ cS : ℝ≥0∞, cS ≠ 0 ∧ cS ≠ ⊤ ∧ ∀ f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) ∂ν =
        cS * ∫⁻ y, f y ∂μG := by
  obtain ⟨cS, h0, htop, hP⟩ := hSP k r z c u v b H σ Vp π w μG μS ν μW μN hyp
  exact ⟨cS, h0, htop, fun f hf => unfold_weil htop hP hyp.2.2.2.2.2.2.1 f hf⟩

theorem nu_conc_of (hSG : SGrp) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    ν {x | Matrix.of x ∉ Gr k r} = 0 := by
  have hS := S_sub_G hSG hyp
  obtain ⟨-, -, -, -, hG, hSm, hQ, -⟩ := hyp
  exact nu_conc hQ hG.2.2.1 hSm.2.1 hSm.2.2.1 hS

end FromSteps

end WlocSk
end
end

