module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0051
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ParabolicBlockForms.NilpotentFramePartApplyZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SecondOrbitSectionIntegral
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C5
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}
def th_k (T : nF σ d.Y d.b) (β : nA σ d.Y d.b) : ℂ := d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
def th'_k (T' : nF σ L.Y L.b) (β : nA σ L.Y L.b) : ℂ :=
  d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1))))
theorem second_orbit_section_integral {f : d.G → ℂ} {s₁ z : ℂ} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)} {T : nF σ d.Y d.b}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d, Integrable (_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d => ∫ p, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection L f s₁ z nb lam 𝓖 T uM ν 𝓤 x =
        ∫ p, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) (nb p.2 * (uM p.1 * x)) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) ∧
      ∫⁻ p, ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ
        ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) < ⊤ := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  let g : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)} → (Fin L.n → AE F E) × nA σ d.Y d.b → ℂ :=
    fun q => _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k L f s₁ z nb T uM (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x
  have hgi : ∀ q, Integrable (g q) μ := fun q => hi q.1
  have hgs : Summable fun q => ∫ p, ‖g q p‖ ∂μ := hs.subtype _
  have htm : ∀ q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, _root_.PositivityTheory.SiegelWeilFormula.Act.tm_k L f s₁ z nb lam 𝓖 T uM ν 𝓤 (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1) x = ∫ p, g q p ∂μ := by
    intro q
    rw [hμ, integral_prod _ (hgi q)]
    rfl
  constructor
  · unfold _root_.PositivityTheory.SiegelWeilFormula.Act.secondOrbitSection
    simp_rw [htm]
    rw [(hasSum_integral_of_summable_integral_norm hgi hgs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [g, _root_.PositivityTheory.SiegelWeilFormula.Act.kq_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k]
    rw [tsum_mul_right]
  · have hm : ∀ q, AEMeasurable (fun p => ‖g q p‖ₑ) μ := fun q => (hgi q).aemeasurable.enorm
    have e1 : ∫⁻ p, ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ ∂μ =
        ∑' q, ENNReal.ofReal (∫ p, ‖g q p‖ ∂μ) := by
      rw [show (fun p => ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)},
          ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * (nb p.2 * (uM p.1 * x))) * _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th_k T p.2‖ₑ) = fun p => ∑' q, ‖g q p‖ₑ from rfl,
        lintegral_tsum hm]
      exact tsum_congr fun q => (ofReal_integral_norm_eq_lintegral_enorm (hgi q)).symm
    rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg fun p => norm_nonneg _) hgs]
    exact ENNReal.ofReal_lt_top
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSiegel
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem siegelSmall_of_k (hF : SliceFacts) (hAC : AdaptedChar) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k := by
  intro F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1 hsr1 φ₀ hφ₀ h0 om' hbox
  intro l hl hinv p t hpt φ hφ
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hchar : ∀ (y : Fin d.m × Fin n × Fin 2 → AF F), ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2),
      l (fun x => d.B.ψ (x ⬝ᵥ y) * φ x) = l φ := by
    intro y φ hφ
    obtain ⟨z, hz⟩ := (hAC F E σ d.m n d.bs d.A Y b dd' had' hb).2 y
    have := hinv z φ hφ
    rw [Darboux.rho, hz, schr_zero_fst] at this
    exact this
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CharInvForm.main F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) l hl hchar
  have hbm : boxFun φ φ₀ ∈ schA F (K1 d.m n) := GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀
  have hb1 := hbox p φ hφ
  have hm1 : boxFun (om' p φ) φ₀ ∈ schA F (K1 d.m n) := hb1 ▸ hsp1.pres (j p) _ hbm
  have hmem : om' p φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    have := (hF F _ _).1 _ hm1
    rwa [slice0_box_one _ h0] at this
  rw [hc _ hmem, hc _ hφ]
  have hv : om' p φ 0 = ev0 (K1 d.m n) (om1 (j p) (boxFun φ φ₀)) := by
    rw [hb1]
    simp [ev0, boxFun, h0]
  obtain ⟨t', ht', hdet⟩ := _root_.PositivityTheory.SiegelWeilFormula.Ald.jPar_k d h hb hj p t hpt
  have hkill : ∀ (z : Matrix (Fin d.m) (Fin d.n) (AE F E)), ∀ Ψ ∈ schA F (K1 d.m n),
      ev0 (K1 d.m n) ((GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm).rho d.B.ψ
        (z * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ) Ψ) = ev0 (K1 d.m n) Ψ := by
    intro z Ψ _
    have h1 := (hAC F E σ d.m d.n d.bs d.A d.Y d.b dd0 had0 d.ok.frame).1 z
    rw [Darboux.rho, GlobalTheory.TowU.reindexD_e, h1]
    simp [ev0, schr]
  have key := hsr1 (ev0 (K1 d.m n)) (evalZero_mem_adelicSchwartzAdmittedForms _) hkill (j p) t' ht' (boxFun φ φ₀) hbm
  rw [hv, key, hdet]
  simp [ev0, boxFun, h0]
  ring
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCosA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
open Matrix
theorem padE_emS_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (a a' : Fin L.n ⊕ Fin L.n) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = N a a' := by
  have h : (∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a) ∧ ∃ x, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L x = _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_left h, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.1.choose_spec, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L h.2.choose_spec]
theorem padE_out_row_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = r) (c : Fin d.n ⊕ Fin d.n) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_right (fun h => hr h.1)]
theorem padE_out_col_k (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = c) : _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L N r c = (1 : Matrix _ _ E) r c := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k]
  rw [dite_eq_right (fun h => hc h.2)]
theorem nq_E_k {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0)
    {H' : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E} (hH : M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) * H' = 1) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') := by
  have hxo : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inl L.i₀ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L L.i₀ rfl
  have hyo : ¬ ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = Sum.inr L.i₀ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L L.i₀ rfl
  refine ⟨fun k => ?_, fun k l hlx hly hkx => ?_⟩
  · have : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') k (Sum.inl L.i₀) = (M * (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E)) k (Sum.inl L.i₀) := by
      simp only [Matrix.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_out_col_k L H' _ hxo]
    rw [Matrix.sub_apply, this, Matrix.mul_one, hx k, sub_self]
  · have hl : ∃ c', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c' = l := by
      by_contra hc
      rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hc with h | h
      · exact hlx h
      · exact hly h
    obtain ⟨c', rfl⟩ := hl
    have hsum : (M * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padE_k L H') k (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = ∑ a', M k (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') * H' a' c' := by
      rw [Matrix.mul_apply, sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
      · simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_emS_k]
      · intro m hm
        rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padE_out_row_k L H' (fun h => hm (by obtain ⟨a, ha⟩ := h; exact ⟨a, ha⟩)), Matrix.one_apply_ne, mul_zero]
        rintro rfl
        exact hm ⟨c', rfl⟩
    rw [Matrix.sub_apply, hsum]
    by_cases hk : ∃ a, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a = k
    · obtain ⟨a, rfl⟩ := hk
      have := congrFun (congrFun hH a) c'
      rw [Matrix.mul_apply] at this
      simp only [Matrix.submatrix_apply] at this
      rw [this, Matrix.one_apply, Matrix.one_apply]
      simp [(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L).eq_iff]
    · rcases _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hk with h | h
      · exact (hkx h).elim
      · have h' : k = Sum.inr L.i₀ := h
        subst h'
        rw [Finset.sum_eq_zero fun a' _ => by rw [hy _ (fun he => hyo ⟨a', he⟩), zero_mul], Matrix.one_apply_ne, sub_self]
        intro he
        exact hyo ⟨c', he.symm⟩
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCosB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem blockH_form_k {ε : ℤˣ} {M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E}
    (hM : Mᵀ * QE d.n ε * M.map σ = QE d.n ε)
    (hx : ∀ r, M r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀))
    (hy : ∀ c, c ≠ Sum.inr L.i₀ → M (Sum.inr L.i₀) c = 0) :
    (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L))ᵀ * QE L.n ε * (M.submatrix (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L)).map σ = QE L.n ε := by
  have hQx : ∀ r, r ≠ Sum.inr L.i₀ → QE (E := E) d.n ε r (Sum.inl L.i₀) = 0 := by
    intro r hr
    rcases r with i | i
    · simp [QE]
    · have hi : i ≠ L.i₀ := fun h => hr (by rw [h])
      simp [QE, Matrix.one_apply, hi]
  have hQx' : ∀ a', QE (E := E) d.n ε (Sum.inl L.i₀) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') = 0 := by
    intro a'
    rcases a' with k | k
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, Ne.symm (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k)]
  have hne : ∀ a', _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a' ≠ Sum.inr L.i₀ := by
    intro a'
    rcases a' with k | k
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L k]
  have hQQ : ∀ a' c', QE (E := E) d.n ε (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a') (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c') = QE L.n ε a' c' := by
    intro a' c'
    rcases a' with k | k <;> rcases c' with k' | k' <;> simp [QE, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Matrix.one_apply, L.inj.eq_iff]
  refine Matrix.ext fun a c => ?_
  have h := congrFun (congrFun hM (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L a)) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L c)
  rw [← hQQ, ← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply, Finset.sum_mul]
  symm
  rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
  · refine Finset.sum_congr rfl fun c' _ => ?_
    rw [Bq.sum_emb (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k L) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_inj_k L)]
    · exact Finset.sum_congr rfl fun a' _ => by rw [hQQ]
    · intro r hr
      have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
      rcases hm with rfl | rfl
      · rw [hQx', mul_zero, zero_mul]
      · rw [hy _ (hne a), zero_mul, zero_mul]
  · intro s hs
    have hm := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.mem_out_k L hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : r = Sum.inr L.i₀
      · subst hr
        rw [hy _ (hne a), zero_mul, zero_mul]
      · rw [hQx r hr, mul_zero, zero_mul]
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [hy _ (hne c), map_zero, mul_zero]
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbCosM
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem inStabilizer_parabolic_mul {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {p γ : d.G} (hp : p ∈ par2 σ d.Y) (hγ : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L γ) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (p * γ) := by
  intro i
  have hP := (ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame p).1 hp
  have e1 : ∀ j, inFrame d.b p (Sum.inr i) (Sum.inl j) = 0 := fun j => by
    have := congrFun (congrFun hP i) j
    simpa [Matrix.toBlocks₂₁] using this
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [e1, hγ _]
theorem inStabilizer_smallerGroupEmbed {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (g : G2 σ L.Y) : _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (L.j g) := by
  intro i
  exact (L.j_out g (Sum.inl L.i₀) (by simp) (Sum.inr i)).2.trans (by simp [Matrix.one_apply])
theorem par_of_j_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) {g : G2 σ L.Y} (h : L.j g ∈ par2 σ d.Y) : g ∈ par2 σ L.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k] at h
  refine Matrix.ext fun a c => ?_
  have h1 := congrFun (congrFun h (L.em a)) (L.em c)
  have h2 := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L (inFrame L.b g) (Sum.inr a) (Sum.inl c)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.emS_k, Sum.map_inr, Sum.map_inl] at h2
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at h1 ⊢
  rw [← h2]
  exact h1
end Bq
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAscfourbKey
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
set_option linter.unusedSimpArgs false
namespace PositivityTheory.SiegelWeilFormula.Act.C4
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
namespace Bq
theorem pad_j_k (g : G2 σ L.Y) : Pad (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b (L.j g)) := by
  intro r c h
  rcases h with h | h | h | h
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g r (by simp [h]) c).1
  · exact (L.j_out g c (by simp [h]) r).2
  · exact (L.j_out g c (by simp [h]) r).2
def bp_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  Matrix.of fun i k => if i = L.i₀ ∨ k = L.i₀ then 0 else β i k
theorem padM_n_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_k L (Matrix.fromBlocks 1 (-(β.submatrix L.em L.em)) 0 1) = Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1 := by
  refine Matrix.ext fun r c => ?_
  rcases r with i | i <;> rcases c with k | k
  all_goals
    by_cases hi : i = L.i₀
    · first
        | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L i hi)]
        | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_row_k L _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L i hi)]
      subst hi
      simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply]
    · by_cases hk : k = L.i₀
      · first
          | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inl_k L k hk)]
          | rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_out_col_k L _ _ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.not_inr_k L k hk)]
        subst hk
        simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, hi]
      · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
        obtain ⟨a', rfl⟩ := (L.rng k).1 hk
        first
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inl a) (Sum.inl a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inl a) (Sum.inr a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inr a) (Sum.inl a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
          | exact (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.padM_emS_k L _ (Sum.inr a) (Sum.inr a')).trans (by simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, Matrix.one_apply, L.inj.eq_iff, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k])
theorem unipotentEntry_eq_zero (u : Fin L.n → AE F E) (a k : Fin d.n) (h : a ≠ L.i₀ ∨ k = L.i₀) : _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u a k = 0 := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.single_apply_of_ne]
  rintro ⟨h1, h2⟩
  rcases h with h | h
  · exact h h1.symm
  · exact _root_.PositivityTheory.SiegelWeilFormula.Act.C4.em_ne_k L j (h2.trans h)
theorem nq_q_k (β : Matrix (Fin d.n) (Fin d.n) (AE F E)) (u : Fin L.n → AE F E) :
    NQ (Sum.inl L.i₀) (Sum.inr L.i₀)
      (Matrix.fromBlocks 1 β 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1) := by
  set A := 1 + _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u with hA
  set D := ((1 - _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.unipotentNilpotentPart L u)ᵀ).map (cA σ) with hD
  have e : Matrix.fromBlocks 1 β 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β)) 0 1 =
      Matrix.fromBlocks A (-(A * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β) + β * D) 0 D := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, Matrix.mul_neg, hA, hD]
    congr 1
    abel
  have hA1 : ∀ a k, a ≠ L.i₀ ∨ k = L.i₀ → (A - 1) a k = 0 := fun a k h => by
    rw [hA, add_sub_cancel_left, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.unipotentEntry_eq_zero L u a k h]
  have hD1 : ∀ a k, k ≠ L.i₀ → D a k = (1 : Matrix _ _ (AE F E)) a k := fun a k hk => by
    simp only [hD, Matrix.map_apply, Matrix.transpose_apply, Matrix.sub_apply, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.unipotentEntry_eq_zero L u k a (Or.inl hk), sub_zero]
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : k = a
    · subst h; simp [map_one]
    · rw [if_neg h, if_neg (Ne.symm h), map_zero]
  rw [e]
  refine Bq.NQ.of_blocks (fun a => hA1 a L.i₀ (Or.inr rfl)) (fun a k ha => hA1 a k (Or.inl ha)) (fun a k ha hk => ?_)
    (fun a k hk => by rw [Matrix.sub_apply, hD1 a k hk, sub_self])
  have h1 : (A * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β) a k = β a k := by
    rw [Matrix.mul_apply]
    have : ∀ m, A a m * _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β m k = if m = a then β a k else 0 := fun m => by
      have hAm : A a m = (1 : Matrix _ _ (AE F E)) a m := by
        have := hA1 a m (Or.inl ha); rwa [Matrix.sub_apply, sub_eq_zero] at this
      rw [hAm, Matrix.one_apply]
      by_cases hm : a = m
      · subst hm; simp [_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k, ha, hk]
      · simp [hm, Ne.symm hm]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have h2 : (β * D) a k = β a k := by
    rw [Matrix.mul_apply]
    simp only [hD1 _ k hk, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Matrix.add_apply, Matrix.neg_apply, h1, h2, neg_add_cancel]
theorem isPar_of_nq_k {p : d.G} (h : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p)) :
    ∃ t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 := by
  obtain ⟨-, t₀, ht₀⟩ := d.ok.frame
  set M := inFrame d.b p
  set T0 := incM F t₀.1
  set T0i := incM F (t₀⁻¹).1
  have e1 : T0 * T0i = 1 := by
    simp only [T0, T0i, incM, ← Matrix.map_mul]
    rw [show t₀.1 * (t₀⁻¹).1 = 1 from t₀.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdet : (T0 * M.toBlocks₁₁ * T0i).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, h.upper_block_det_one, mul_one, ← Matrix.det_mul, e1, Matrix.det_one]
  have hu : IsUnit (T0 * M.toBlocks₁₁ * T0i) := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hdet]; exact isUnit_one)
  refine ⟨hu.unit, (kunf.isPar_frame ht₀ p hu.unit).2 ⟨h.projected_block_lower_sum, rfl⟩, ?_⟩
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, hdet]
end Bq
theorem key_id_pf_k {nb : nA σ d.Y d.b → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} (hnb : IsNMap d.b nb)
    (hnb' : IsNMap L.b nb') {uM : (Fin L.n → AE F E) → d.G} {ν : Measure (Fin L.n → AE F E)}
    {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤) (h : G2 σ L.Y) (β : nA σ d.Y d.b) (u : Fin L.n → AE F E)
    (x : d.G) : ∃ p t, IsPar p t ∧ Matrix.GeneralLinearGroup.det t = 1 ∧
      L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
  set q : d.G := nb β * uM u * L.j (nb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) with hq
  set p : d.G := L.j h * q * L.j h⁻¹ with hp
  have hinv : L.j (nb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) = (L.j (nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)))⁻¹ := by
    rw [kunf.nb_neg hnb', map_inv]
  have hid : L.j h * (nb β * (uM u * x)) = p * (L.j (h * nb' (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β)) * x) := by
    simp only [hp, hq, hinv, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hQ : inFrame d.b q = Matrix.fromBlocks 1 β.1 0 1 * _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.muF_k L u * Matrix.fromBlocks 1 (-(_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.bp_k L β.1)) 0 1 := by
    rw [hq, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hnb β, _root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.inFrame_uM_k L hU u, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.inFrame_j_k,
      hnb' (-_root_.PositivityTheory.SiegelWeilFormula.Act.C4.prj_k L β), ← _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.padM_n_k L β.1]
    rfl
  have hJJ : inFrame d.b (L.j h) * inFrame d.b (L.j h⁻¹) = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hnq : Bq.NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (inFrame d.b p) := by
    rw [hp, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hQ]
    exact Bq.NQ.conj (by simp) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L h) (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.pad_j_k L h⁻¹) hJJ (_root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.nq_q_k L β.1 u)
  obtain ⟨t, ht, hdt⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C4.Bq.isPar_of_nq_k L hnq
  exact ⟨p, t, ht, hdt, hid⟩
end PositivityTheory.SiegelWeilFormula.Act.C4
end
end
end

