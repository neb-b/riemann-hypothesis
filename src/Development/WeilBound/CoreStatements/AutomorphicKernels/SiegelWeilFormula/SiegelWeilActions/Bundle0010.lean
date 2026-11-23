module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0009
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.Bundle0001
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureSplitExactSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EllA
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

structure Hyp (nb : nA σ d.Y d.b → d.G) (uM : (Fin L.n → AE F E) → d.G) (nb' : nA σ L.Y L.b → G2 σ L.Y) (w₁ : d.G)
    (cM : (Fin L.n → AE F E) × AF F → d.G) (δ : E) : Prop where
  nb : IsNMap d.b nb
  uM : ∀ u, ∃ a', inFrame d.b (uM u) = Matrix.fromBlocks (uA L u) 0 0 a'
  nb' : IsNMap L.b nb'
  wr : w₁ ∈ rat2 σ d.Y
  wf : ∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)
  cf : ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (uA L c.1) (aB L δ c.2) 0 A'
  δ0 : δ ≠ 0

def sM (b : Fin L.n → AE F E) : d.G := elt (bMat (sB R L b))

def pb (β : nA σ d.Y d.b) : Fin L.n → AE F E := fun j => β.1 L.i₀ (L.em j)

def ellA (δ : E) : AE F E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    LinearMap.baseChange (AF F) (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1)

def pa (δ : E) (β : nA σ d.Y d.b) : AF F := ellA δ (β.1 L.i₀ L.i₀)

def E2 (Φ : d.G → ℂ) (g : d.G) : ℂ := ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, Φ (rep q.1 * g)

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ExistsNeZeroInFrameW1ColumnI0
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

namespace N

theorem fix_of_col {w x : d.G}
    (hc : ∀ r, inFrame d.b x r (Sum.inl L.i₀) = inFrame d.b w r (Sum.inl L.i₀)) : Fix L (w⁻¹ * x) := by
  intro k
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply]
  simp_rw [hc]
  rw [← Matrix.mul_apply, ← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, inv_mul_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]

theorem exists_ne_zero_inFrame_w1_column_i0 (h : Hyp L nb uM nb' w₁ cM δ) : ∃ b₀ : E, b₀ ≠ 0 ∧ ∀ r, inFrame d.b w₁ r (Sum.inl L.i₀) =
    inclR (F := F) (AF F) ((Pi.single (Sum.inr L.i₀) b₀ : Fin d.n ⊕ Fin d.n → E) r) := by
  obtain ⟨a, b, -, hb, hw⟩ := h.wf
  refine ⟨b, hb, fun r => ?_⟩
  rw [hw]
  rcases r with i | i <;> by_cases hi : i = L.i₀
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]
  · subst hi; simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply]
  · simp [Matrix.single_apply, Matrix.one_apply, Pi.single_apply, hi, Ne.symm hi]

theorem nCond_of_E {n : ℕ} (ε : ℤˣ) {β0 : Matrix (Fin n) (Fin n) E}
    (hβ : β0ᵀ = -((((ε : ℤ) : E)) • β0.map σ)) : incM F β0 ∈ kfour.nCond σ n ε := by
  show (incM F β0)ᵀ = -((((ε : ℤ) : AE F E)) • (incM F β0).map (cA σ))
  ext r c
  have := congrFun (congrFun hβ r) c
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] at this ⊢
  simp only [incM, Matrix.map_apply]
  rw [kfour.cA_inclR', this, map_neg, map_mul, kfour.inclR_int]

theorem exists_E {n : ℕ} (i₀ : Fin n) (hσ : ∀ a, σ (σ a) = a) (ε : ℤˣ)
    {G0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E} (hform : G0ᵀ * Bq.QE n ε * G0.map σ = Bq.QE n ε)
    {b₀ : E} (hb : b₀ ≠ 0) (hy : (fun k => G0 (Sum.inr k) (Sum.inl i₀)) ≠ 0) :
    ∃ (A : GL (Fin n) E) (β0 : Matrix (Fin n) (Fin n) E), β0ᵀ = -((((ε : ℤ) : E)) • β0.map σ) ∧
      ∀ r, ((Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) r (Sum.inl i₀)) = (Pi.single (Sum.inr i₀) b₀ : Fin n ⊕ Fin n → E) r := by
  set vx : Fin n → E := fun k => G0 (Sum.inl k) (Sum.inl i₀) with hvx
  set vy : Fin n → E := fun k => G0 (Sum.inr k) (Sum.inl i₀) with hvy
  set εE : E := ((ε : ℤ) : E) with hεE
  have hσε : σ εE = εE := map_intCast _ _
  have hεε : εE * εE = 1 := by
    rw [hεE, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hσb : σ b₀ ≠ 0 := fun h0 => hb (by rw [← hσ b₀, h0, map_zero])
  set w : Fin n → E := fun k => σ (vy k) / σ b₀ with hw_def
  have hw0 : w ≠ 0 := by
    intro h0
    apply hy
    funext k
    have h1 := congrFun h0 k
    simp only [hw_def, Pi.zero_apply, div_eq_zero_iff, hσb, or_false] at h1
    rw [Pi.zero_apply, ← hσ (vy k), h1, map_zero]
  obtain ⟨a0, ha0⟩ := Bq.exists_gl_col i₀ w hw0
  have hdet : (a0.1ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnits_det_units a0).ne_zero
  set A : GL (Fin n) E := Matrix.GeneralLinearGroup.mkOfDetNeZero a0.1ᵀ hdet with hA_def
  have hArow : ∀ k, A.1 i₀ k = w k := fun k => ha0 k
  have hw : ∀ k, σ (vy k) = σ b₀ * A.1 i₀ k := fun k => by
    rw [hArow, hw_def]
    field_simp
  have hvyA : ∀ k, vy k = b₀ * σ (A.1 i₀ k) := fun k => by
    have h1 := congrArg σ (hw k)
    rw [hσ, map_mul, hσ] at h1
    exact h1
  set X : Fin n → E := A.1 *ᵥ vx with hX
  have hXi : X i₀ = ∑ j, A.1 i₀ j * vx j := rfl
  have hiso0 : ∑ j, vx j * σ (vy j) + εE * ∑ j, vy j * σ (vx j) = 0 := by
    have h1 := congrFun (congrFun hform (Sum.inl i₀)) (Sum.inl i₀)
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Bq.QE, Matrix.one_apply, Finset.mul_sum] at h1
    have e1 : ∑ j, vx j * σ (vy j) = ∑ x, G0 (Sum.inl x) (Sum.inl i₀) * σ (G0 (Sum.inr x) (Sum.inl i₀)) := rfl
    have e2 : εE * ∑ j, vy j * σ (vx j) =
        ∑ x, G0 (Sum.inr x) (Sum.inl i₀) * ((ε : ℤ) : E) * σ (G0 (Sum.inl x) (Sum.inl i₀)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hvx, hvy, hεE]
      ring
    rw [e1, e2, add_comm]
    exact h1
  have hiso : σ b₀ * X i₀ + εE * (b₀ * σ (X i₀)) = 0 := by
    have e1 : ∑ j, vx j * σ (vy j) = σ b₀ * X i₀ := by
      rw [hXi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hw]
      ring
    have e2 : ∑ j, vy j * σ (vx j) = b₀ * σ (X i₀) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hXi, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hvyA, map_mul]
      ring
    rw [← e1, ← e2]
    exact hiso0
  set col : Fin n → E := fun k => -(X k) / b₀ with hcol
  have hcol0 : col i₀ = -(εE * σ (col i₀)) := by
    simp only [hcol, map_div₀, map_neg]
    field_simp
    linear_combination (-1 : E) * hiso
  set β0 : Matrix (Fin n) (Fin n) E :=
    Matrix.of fun r c => if c = i₀ then col r else if r = i₀ then -(εE * σ (col c)) else 0 with hβ0
  refine ⟨A, β0, ?_, ?_⟩
  · ext r c
    simp only [hβ0, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply,
      smul_eq_mul]
    by_cases hr : r = i₀ <;> by_cases hc : c = i₀
    · subst hr; subst hc; simp only [if_true]; exact hcol0
    · subst hr; simp only [if_true, hc, if_false, map_neg, map_mul, hσε, hσ]
      rw [mul_neg, neg_neg, ← mul_assoc, hεε, one_mul]
    · subst hc; simp [hr]
    · simp [hr, hc]
  · have hD : (((A⁻¹).1)ᵀ.map σ) *ᵥ vy = (Pi.single i₀ b₀ : Fin n → E) := by
      funext k
      calc ((((A⁻¹).1)ᵀ.map σ) *ᵥ vy) k = ∑ l, σ ((A⁻¹).1 l k) * vy l := rfl
        _ = b₀ * σ (∑ l, A.1 i₀ l * (A⁻¹).1 l k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hvyA, map_mul]
          ring
        _ = b₀ * σ ((A.1 * (A⁻¹).1) i₀ k) := rfl
        _ = (Pi.single i₀ b₀ : Fin n → E) k := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
          by_cases hk : k = i₀
          · subst hk; simp
          · rw [Matrix.one_apply_ne (Ne.symm hk), Pi.single_eq_of_ne hk, map_zero, mul_zero]
    have hv : (fun m => G0 m (Sum.inl i₀)) = Sum.elim vx vy := by
      funext m
      rcases m with m | m <;> rfl
    intro r
    have hcolM : ∀ (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) r,
        (M * G0) r (Sum.inl i₀) = (M *ᵥ fun m => G0 m (Sum.inl i₀)) r := fun M r => rfl
    rw [hcolM, ← Matrix.mulVec_mulVec, hv]
    simp only [Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.zero_mulVec, Matrix.one_mulVec,
      add_zero, zero_add, hD, ← hX, Matrix.mulVec_single]
    have hcb : ∀ k, col k * b₀ = -X k := fun k => div_mul_cancel₀ _ hb
    rcases r with i | i
    · simp only [Sum.elim_inl, Pi.add_apply, Pi.smul_apply, Matrix.col_apply, hβ0, Matrix.of_apply, if_true,
        op_smul_eq_mul, smul_eq_mul]
      rw [hcb, add_neg_cancel, Pi.single_eq_of_ne (by simp)]
    · simp only [Sum.elim_inr, Pi.smul_apply, Matrix.col_apply, op_smul_eq_mul]
      by_cases hi : i = i₀
      · subst hi; simp
      · rw [Matrix.one_apply_ne hi, zero_mul, Pi.single_eq_of_ne (by simp [hi])]

theorem normalize (h : Hyp L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ LagrangianCondition L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ Fix L (w₁⁻¹ * (p * γ)) := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) γ hγ
  have hform := Bq.form_E hε γ hG0
  obtain ⟨b₀, hb₀, hw1⟩ := exists_ne_zero_inFrame_w1_column_i0 h
  have hy : (fun k => G0 (Sum.inr k) (Sum.inl L.i₀)) ≠ 0 := by
    intro h0
    apply hn
    intro i
    rw [hG0]
    show inclR (F := F) (AF F) (G0 (Sum.inr i) (Sum.inl L.i₀)) = 0
    rw [congrFun h0 i, Pi.zero_apply, map_zero]
  obtain ⟨A, β0, hβ, hcol⟩ := exists_E L.i₀ hσ ε hform hb₀ hy
  obtain ⟨pm, hpmr, hpm⟩ := Afc.levi_ex hσ d.ok.frame A
  have hpmP : pm ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pm).2 (by rw [hpm, Matrix.toBlocks_fromBlocks₂₁])
  have hβA : incM F β0 ∈ nA σ d.Y d.b := (kfour.mem_nA_iff hσ hε _).2 (nCond_of_E ε hβ)
  set pn := nb ⟨incM F β0, hβA⟩ with hpn_def
  have hpn : inFrame d.b pn = Matrix.fromBlocks 1 (incM F β0) 0 1 := h.nb _
  have hpnP : pn ∈ par2 σ d.Y :=
    (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame pn).2 (by rw [hpn, Matrix.toBlocks_fromBlocks₂₁])
  have hpnr : pn ∈ rat2 σ d.Y :=
    kunf.rat_of_inFrame (M := Matrix.fromBlocks 1 β0 0 1) (by rw [hpn, kfour.incM_nM]; rfl)
  refine ⟨pn * pm, mul_mem hpnP hpmP, mul_mem hpnr hpmr, fix_of_col fun r => ?_⟩
  have hF : inFrame d.b (pn * pm * γ) =
      incM F (Matrix.fromBlocks 1 β0 0 1 * Matrix.fromBlocks A.1 0 0 (((A⁻¹).1)ᵀ.map σ) * G0) := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hpn, hpm, hG0, kfour.incM_mul', kfour.incM_mul',
      kfour.incM_nM, Afc.incM_fromBlocks, kfour.incM_zero]
    rfl
  rw [hF, hw1 r]
  show inclR (F := F) (AF F) _ = _
  rw [hcol r]

end N

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.PadZeroMemNilradical
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def pad0 (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then β h.1.choose h.2.choose else 0

theorem pad_zero_embedding_alt (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (a c : Fin L.n) : pad0 L β (L.em a) (L.em c) = β a c := by
  have h : (∃ a', L.em a' = L.em a) ∧ ∃ c', L.em c' = L.em c := ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩
  simp only [pad0, dif_pos h]
  rw [L.inj h.1.choose_spec, L.inj h.2.choose_spec]

theorem pad_zero_outside_range (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (i k : Fin d.n)
    (h : ¬ ((∃ a, L.em a = i) ∧ ∃ c, L.em c = k)) : pad0 L β i k = 0 := by
  simp only [pad0, dif_neg h]

theorem pad_zero_symm_cases (β : Matrix (Fin L.n) (Fin L.n) (AE F E)) (P : AE F E → AE F E → Prop) (h0 : P 0 0)
    (h1 : ∀ a c, P (β a c) (β c a)) (i k : Fin d.n) : P (pad0 L β i k) (pad0 L β k i) := by
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    rw [pad_zero_embedding_alt, pad_zero_embedding_alt]
    exact h1 a c
  · rw [pad_zero_outside_range L β i k h, pad_zero_outside_range L β k i (fun h' => h ⟨h'.2, h'.1⟩)]
    exact h0

theorem eps_common : ∃ ε : ℤˣ, d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 ∧
    L.b.1ᵀ * dbl L.Y.J * L.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  exact ⟨ε, hε, hε'⟩

theorem pad_zero_mem_nilradical (β : nA σ L.Y L.b) : pad0 L β.1 ∈ nA σ d.Y d.b := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  rw [kunf.mem_nA_iff hε]
  have hβ := (kunf.mem_nA_iff hε' β.1).1 β.2
  ext i k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply]
  refine pad_zero_symm_cases L β.1 (fun u v => v = -((((ε : ℤ) : AE F E)) • cA σ u)) (by simp) (fun a c => ?_) i k
  have := congrFun (congrFun hβ a) c
  simpa only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply] using this

def padN : nA σ L.Y L.b →+ nA σ d.Y d.b where
  toFun β := ⟨pad0 L β.1, pad_zero_mem_nilradical L β⟩
  map_zero' := by
    apply Subtype.ext
    ext i k
    refine pad_zero_symm_cases L (0 : nA σ L.Y L.b).1 (fun u _ => u = (0 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i k) rfl
      (fun a c => rfl) i k
  map_add' β β' := by
    apply Subtype.ext
    ext i k
    by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
    · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
      simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_embedding_alt]
    · simp only [AddSubgroup.coe_add, Matrix.add_apply, pad_zero_outside_range L _ i k h, add_zero]

theorem prj_padN (β : nA σ L.Y L.b) : prj L (padN L β) = β := by
  apply Subtype.ext
  ext a c
  simp only [prj_val, Matrix.submatrix_apply]
  exact pad_zero_embedding_alt L β.1 a c

theorem continuous_padN : Continuous (padN L) := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => continuous_pi fun k => ?_
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · obtain ⟨⟨a, rfl⟩, ⟨c, rfl⟩⟩ := h
    simp only [pad_zero_embedding_alt]
    exact (continuous_apply c).comp ((continuous_apply a).comp continuous_subtype_val)
  · simp only [pad_zero_outside_range L _ i k h]
    exact continuous_const

theorem countable_nF (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) : Countable (nF σ Y b) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  refine Function.Injective.countable (f := fun ν : nF σ Y b => Classical.choose (kunf.mem_nF_iff.1 ν.2)) ?_
  intro ν ν' h
  have h1 := Classical.choose_spec (kunf.mem_nF_iff.1 ν.2)
  have h2 := Classical.choose_spec (kunf.mem_nF_iff.1 ν'.2)
  apply Subtype.ext; apply Subtype.ext
  rw [h1, h2]
  exact congrArg _ h

theorem prj_nF {β : nA σ d.Y d.b} (h : β ∈ nF σ d.Y d.b) : prj L β ∈ nF σ L.Y L.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨T.submatrix L.em L.em, ?_⟩
  rw [prj_val, hT]
  rfl

theorem padN_nF {β : nA σ L.Y L.b} (h : β ∈ nF σ L.Y L.b) : padN L β ∈ nF σ d.Y d.b := by
  obtain ⟨T, hT⟩ := kunf.mem_nF_iff.1 h
  refine kunf.mem_nF_iff.2 ⟨Matrix.of fun i k => if h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k then
    T h.1.choose h.2.choose else 0, ?_⟩
  ext i k
  show pad0 L β.1 i k = _
  by_cases h : (∃ a, L.em a = i) ∧ ∃ c, L.em c = k
  · rw [pad0, dif_pos h, hT]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_pos h]
  · rw [pad0, dif_neg h]
    simp only [incM, Matrix.map_apply, Matrix.of_apply, dif_neg h, map_zero]

theorem nA_inst (n : ℕ) (Y : Spc F E n) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ)
    (hε : b.1ᵀ * dbl Y.J * b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) :
    LocallyCompactSpace (nA σ Y b) ∧ T2Space (nA σ Y b) := by
  have h := GlobalTheory.T.adelic_skew_matrices_locally_compact_group F E σ n Y b ε (fun β => by
    rw [kunf.mem_nA_iff hε, ← sub_eq_zero, sub_neg_eq_add])
  exact ⟨h.2.2.1, h.2.2.2.2.1⟩

theorem fiber {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' : nA σ L.Y L.b → G2 σ L.Y} {lam' : Measure (nA σ L.Y L.b)}
    {𝓖' : Set (nA σ L.Y L.b)} (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖')
    (G : nA σ L.Y L.b → ℂ) (hG : Continuous G) (hper : ∀ β₀ ∈ nF σ L.Y L.b, ∀ β', G (β₀ + β') = G β') :
    ∫ β in 𝓖, G (prj L β) ∂lam = ∫ β' in 𝓖', G β' ∂lam' := by
  obtain ⟨ε, hε, hε'⟩ := eps_common L
  obtain ⟨h1, h2⟩ := nA_inst d.n d.Y d.b ε hε
  obtain ⟨h3, h4⟩ := nA_inst L.n L.Y L.b ε hε'
  exact _root_.GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq (prj L) (padN L) (continuous_prj L) (continuous_padN L) (prj_padN L)
    (nF σ d.Y d.b) (nF σ L.Y L.b) (countable_nF _ _ _) (countable_nF _ _ _) (fun γ hγ => prj_nF L hγ)
    (fun γ hγ => padN_nF L hγ) lam lam' hc.2.1 hc'.2.1 𝓖 𝓖' hc.2.2.1 hc.2.2.2 hc'.2.2.1 hc'.2.2.2 G hG
    (fun γ hγ x => hper γ hγ x)

end PositivityTheory.SiegelWeilFormula.Act.C4

end
end

