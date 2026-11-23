module

public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.Bundle0007
public import Formalism.LocalToGlobal.GlobalTheory.BlockActions.NfAllSmulReB

@[expose] public section

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.DualLStable
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Formalism.BasicNotions Formalism.L2.Forms NumberField Formalism.UG Matrix

theorem mulLat_one {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) :
    mulLat (1 : Matrix (Fin n) (Fin n) E) L = L := by
  unfold mulLat
  convert Submodule.map_id L
  ext x i
  simp

theorem dualL_stable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) (γ γi : Matrix (Fin n) (Fin n) E) (hγi : γi * γ = 1) (hγ' : γ * γi = 1)
    (hU : cT σ γ * J * γ = J) (hL : mulLat γ L = L) :
    ∀ y ∈ dualL σ J L, γ *ᵥ y ∈ dualL σ J L := by
  have hLi : mulLat γi L = L := by
    conv_lhs => rw [← hL]
    rw [mulLat_mulLat, hγi, mulLat_one]
  have hset : ∀ y ∈ dualSet σ J L, γ *ᵥ y ∈ dualSet σ J L := by
    intro y hy x hx
    have hxi : γi *ᵥ x ∈ L := by
      rw [← hLi]; exact Submodule.mem_map_of_mem hx
    have e : x = γ *ᵥ (γi *ᵥ x) := by rw [mulVec_mulVec, hγ', one_mulVec]
    rw [e, hform_UJ σ J γ hU]
    exact hy _ hxi
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span (hset z hz)
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mulVec_add]; exact add_mem ha hb
  | smul r a _ ha =>
    have e : γ *ᵥ (r • a) = r • (γ *ᵥ a) := by
      rw [← algebraMap_smul E r a, mulVec_smul, algebraMap_smul]
    rw [e]; exact Submodule.smul_mem _ r ha

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i}

theorem stabLF_of (Tf : FormsTiedSym D u Ch chOf)
    (h : ∀ (c : (D.fm u).clsP) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)),
      γ ∈ ((Tf.cls D.R.m le_rfl (Or.inr rfl)).stabI ((D.fm u).til c)).range →
      mulLat γ.1.1 (clsCrd D u D.R.m le_rfl ((D.fm u).til c)) = clsCrd D u D.R.m le_rfl ((D.fm u).til c) ∧
      ∀ (v : (D.mem u).A.vT) (x : ↥(Ld D u D.R.m le_rfl ((D.fm u).til c)))
        (hx : γ.1.1 *ᵥ x.1 ∈ Ld D u D.R.m le_rfl ((D.fm u).til c)),
        (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ ⟨γ.1.1 *ᵥ x.1, hx⟩) =
          (D.fm u).fv D.R.m v ((D.fm u).til c) ((Tf.lv D.R.m le_rfl).pr v _ x)) :
    StabLF Tf := by
  intro c γ hγ
  obtain ⟨hL, hf⟩ := h c γ hγ
  refine ⟨hL, ?_, hf⟩
  have h1 : (γ.1⁻¹ : GL _ _).1 * γ.1.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : γ.1.1 * (γ.1⁻¹ : GL _ _).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  exact dualL_stable _ _ _ γ.1.1 _ h1 h2 γ.2 hL

end Formalism.L2.GlobalTheoryTheory.Br
end
end

-- bundled from Formalism.LocalToGlobal.GlobalTheory.BlockActions.NormOneOfPow
section
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms

section Gen

variable {ι : Type} [Fintype ι] {n : ℕ}

def rowSubK {R : Type} [CommRing R] (o : ι → Matrix (Fin n) (Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R →ₐ[R] MvPolynomial (ι × Fin n × Fin n) R :=
  aeval fun x => ∑ a', C (o x.1 x.2.1 a') * X (x.1, a', x.2.2)

theorem rowSubK_eq_subP (o : ι → Matrix (Fin n) (Fin n) ℂ) : rowSubK o = subP o := rfl

theorem subP_eq_blkRow (o : ι → Matrix (Fin n) (Fin n) ℂ) : subP o = blkRow o := rfl

theorem map_rowSubK {R S : Type} [CommRing R] [CommRing S] (j : R →+* S) (o : ι → Matrix (Fin n) (Fin n) R)
    (P : MvPolynomial (ι × Fin n × Fin n) R) :
    map j (rowSubK o P) = rowSubK (fun τ => (o τ).map j) (map j P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowSubK, MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp [rowSubK, map_sum, Matrix.map_apply]

theorem blkRow_comp (K L : ι → Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    blkRow K (blkRow L P) = blkRow (fun τ => L τ * K τ) P := by
  have e : (blkRow K).comp (blkRow L) = blkRow (fun τ => L τ * K τ) := by
    apply MvPolynomial.algHom_ext
    intro v
    rw [AlgHom.comp_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [blkRow, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, ← mul_assoc,
      MvPolynomial.algebraMap_eq]
    rw [Finset.sum_comm]
  rw [← e, AlgHom.comp_apply]

theorem norm_one_of_pow {K : Type} [Field K] (j s : K →+* ℂ) (a : K) (k : ℕ) (hk : 0 < k) (h : (j a) ^ k = 1) :
    ‖s a‖ = 1 := by
  have h1 : a ^ k = 1 := j.injective (by rw [map_pow, h, map_one])
  have h2 : (s a) ^ k = 1 := by rw [← map_pow, h1, map_one]
  have h3 := congrArg norm h2
  rw [norm_pow, norm_one] at h3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h3

end Gen

end Formalism.L2.GlobalTheoryTheory.Br
end
end

