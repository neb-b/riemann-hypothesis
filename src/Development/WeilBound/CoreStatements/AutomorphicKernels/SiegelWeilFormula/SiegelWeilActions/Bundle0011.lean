module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0009
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0010
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.UnipotentBlockCornerEmbedded
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LocCompactNA
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.DifferentialOperatorClasses
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem normalize (h : Hyp L nb uM nb' w₁ cM δ) {γ : d.G} (hγ : γ ∈ rat2 σ d.Y) (hn : ¬ LagrangianCondition L γ) :
    ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ Fix L (w₁⁻¹ * (p * γ)) :=
  N.normalize h hγ hn

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.GeometricRayBounds
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
open PositivityTheory.SiegelWeilFormula.Act.C4 PositivityTheory.SiegelWeilFormula.Act.C4.Bq PositivityTheory.SiegelWeilFormula.Act.C5

namespace PositivityTheory.SiegelWeilFormula.Act.C6

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} {L : LD d}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

theorem stab_dec (h : Hyp L nb uM nb' w₁ cM δ) {x : d.G} (hx : x ∈ rat2 σ d.Y) (hf : Fix L x) :
    ∃ (s : d.G) (c : Cr L) (γ' : G2 σ L.Y), s ∈ rat2 σ d.Y ∧ w₁ * s * w₁⁻¹ ∈ par2 σ d.Y ∧ γ' ∈ rat2 σ L.Y ∧
      inFrame L.b γ' = (inFrame d.b x).submatrix (emS L) (emS L) ∧ x = s * (cM c.1 * L.j γ') := by
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  obtain ⟨G0, hG0⟩ := Afc.rat_frame (b := d.b) x hx
  have hx0 : ∀ r, G0 r (Sum.inl L.i₀) = (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r (Sum.inl L.i₀) := by
    intro r
    apply kfour.inclR_injective (F := F)
    have h1 := hf r
    rw [hG0] at h1
    simp only [incM, Matrix.map_apply] at h1
    rw [h1]
    by_cases hr : r = Sum.inl L.i₀ <;> simp [Matrix.one_apply, hr]
  have hform := form_E hε x hG0
  have hy := yrow_zero hform hx0
  set H := G0.submatrix (emS L) (emS L) with hH_def
  have hH := blockH_form L hform hx0 hy
  have hε1 : (((ε : ℤ) : E)) * (((ε : ℤ) : E)) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hεσ : (σ : E →+* E) (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast _ _
  obtain ⟨hHH', hH'H⟩ := kunf.frame_inv_pf (σ : E →+* E) hσ (((ε : ℤ) : E)) hε1 hεσ H hH
  set H' := Matrix.fromBlocks ((H.toBlocks₂₂.map (σ : E →+* E))ᵀ) ((((ε : ℤ) : E)) • (H.toBlocks₁₂.map (σ : E →+* E))ᵀ)
      ((((ε : ℤ) : E)) • (H.toBlocks₂₁.map (σ : E →+* E))ᵀ) ((H.toBlocks₁₁.map (σ : E →+* E))ᵀ) with hH'_def
  have hIA : incM F H * incM F H' = 1 := by rw [← kfour.incM_mul', hHH', Afc.incM_one']
  have hformA : (incM F H)ᵀ * kunf.jw L.n (((ε : ℤ) : AE F E)) * (incM F H).map (cA σ) =
      kunf.jw L.n (((ε : ℤ) : AE F E)) := by
    have h1 := congrArg (incM F) hH
    rw [kfour.incM_mul', kfour.incM_mul', ← Afc.incM_transpose, ← Afc.incM_map_cA, ← QA_eq] at h1
    exact h1
  obtain ⟨g', hg'⟩ := kunf.exists_of_frame (Y := L.Y) hε' (incM F H) (incM F H') hIA hformA
  have hg'r : g' ∈ rat2 σ L.Y := kunf.rat_of_inFrame hg'
  have hg'i : inFrame L.b g'⁻¹ = incM F H' := by
    rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_inv, hg']
    exact Matrix.inv_eq_right_inv hIA
  set n := x * L.j g'⁻¹ with hn_def
  have hnF : inFrame d.b n = incM F (G0 * padE L H') := by
    rw [hn_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hG0, inFrame_j, hg'i, padM_incM, kfour.incM_mul']
  have hnq0 : NQ (Sum.inl L.i₀) (Sum.inr L.i₀) (G0 * padE L H') := nq_E L hx0 hy hHH'
  have hnr : n ∈ rat2 σ d.Y := mul_mem hx (j_rat L (inv_mem hg'r))
  set N0 := G0 * padE L H' with hN0
  set u₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inl (L.em j)) with hu₀
  set b₀ : Fin L.n → E := fun j => N0 (Sum.inl L.i₀) (Sum.inr (L.em j)) with hb₀
  set z₀ : E := N0 (Sum.inl L.i₀) (Sum.inr L.i₀) + ∑ j, b₀ j * σ (u₀ j) with hz₀
  have hUN0 : M.U (σ : E →+* E) (((ε : ℤ) : E)) N0 := form_E hε n hnF
  have hpz : σ z₀ = -(((ε : ℤ) : E) * z₀) := M.even_im_hermitian_sub hσ hε1 hεσ L.em L.inj L.rng hUN0 hnq0
  have hpd := delta_par h hε
  have hε0 : (((ε : ℤ) : E)) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hε1; exact zero_ne_one hε1
  have hfix : σ (z₀ / δ) = z₀ / δ := by
    rw [map_div₀, hpz, hpd, neg_div_neg_eq, mul_div_mul_left _ _ hε0]
  obtain ⟨a₀, ha₀⟩ := fixed_in_F d.ok.good.cm (z₀ / δ) hfix
  let c : Cr L := ⟨(GlobalTheory.ThK.incV F u₀, algebraMap F (AF F) a₀), AddSubgroup.subset_closure ⟨u₀, rfl⟩, ⟨a₀, rfl⟩⟩
  set s := n * (cM c.1)⁻¹ with hs_def
  have hsr : s ∈ rat2 σ d.Y := mul_mem hnr (inv_mem (cM_rat' h c.2.1 c.2.2))
  set e : AE F E := ((ε : ℤ) : AE F E) with he_def
  have he : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hse : (cA σ).toRingHom e = e := map_intCast _ _
  have hN : inFrame d.b n = sExp L e (GlobalTheory.ThK.incV F b₀) * inFrame d.b (cM c.1) := by
    apply M.nq_unique (s := (cA σ).toRingHom) (e := e) (i₀ := L.i₀) (cA_inv' hσ) he hse
    · exact kunf.frame_eq hε n
    · have hUS := U_sExp (ε := ε) (L := L) hσ (GlobalTheory.ThK.incV F b₀)
      have hUC : M.U (cA σ).toRingHom e (inFrame d.b (cM c.1)) := kunf.frame_eq hε (cM c.1)
      unfold M.U at hUS hUC ⊢
      rw [Matrix.transpose_mul, Matrix.map_mul]
      calc (inFrame d.b (cM c.1))ᵀ * (sExp L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            ((sExp L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom * (inFrame d.b (cM c.1)).map (cA σ).toRingHom)
          = (inFrame d.b (cM c.1))ᵀ * ((sExp L e (GlobalTheory.ThK.incV F b₀))ᵀ * kunf.jw d.n e *
            (sExp L e (GlobalTheory.ThK.incV F b₀)).map (cA σ).toRingHom) * (inFrame d.b (cM c.1)).map (cA σ).toRingHom := by
            simp only [Matrix.mul_assoc]
        _ = kunf.jw d.n e := by rw [hUS, hUC]
    · rw [hnF]; exact NQ.map _ hnq0
    · exact NQ.mul (nq_sExp _ _) (nq_cM h _)
    · obtain ⟨r1, r2, r3, r4⟩ := row_sC h e (GlobalTheory.ThK.incV F b₀) (GlobalTheory.ThK.incV F u₀) (algebraMap F (AF F) a₀)
      intro c'
      rw [hnF]
      rcases c' with k | k
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r4]
          have := hnq0.1 (Sum.inl L.i₀)
          simp only [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at this
          simp [incM, this]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r1]; rfl
      · by_cases hk : k = L.i₀
        · subst hk
          rw [r3]
          have e1 : algebraMap F (AF F) a₀ • inclR (F := F) (AF F) δ = inclR (F := F) (AF F) z₀ := by
            have : z₀ = algebraMap F E a₀ * δ := by rw [ha₀, div_mul_cancel₀ _ h.δ0]
            rw [this, map_mul]
            show algebraMap F (AF F) a₀ • ((1 : AF F) ⊗ₜ[F] δ) = (1 : AF F) ⊗ₜ[F] (algebraMap F E a₀) * (1 : AF F) ⊗ₜ[F] δ
            rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← Algebra.smul_def, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.algebraMap_eq_smul_one]
          rw [e1, hz₀]
          have hc : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun _ => rfl
          set_option synthInstance.maxHeartbeats 100000 in
            simp [incM, GlobalTheory.ThK.incV, hc, map_add (f := _), map_sum, map_mul]
        · obtain ⟨j, rfl⟩ := (L.rng k).1 hk
          rw [r2]; rfl
  have hS : inFrame d.b s = sExp L e (GlobalTheory.ThK.incV F b₀) := by
    have h1 : inFrame d.b (cM c.1) * inFrame d.b (cM c.1)⁻¹ = 1 := by
      rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, mul_inv_cancel, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
    rw [hs_def, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, hN, Matrix.mul_assoc, h1, Matrix.mul_one]
  refine ⟨s, c, g', hsr, w1_conj_sExp_mem_par2 h hS, hg'r, ?_, ?_⟩
  · rw [hg', hG0]; rfl
  · rw [hs_def, hn_def, map_inv]; group

end PositivityTheory.SiegelWeilFormula.Act.C6

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IndepDom
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

theorem indepDom : IndepDom := by
  intro F E _ _ _ _ _ σ d L s₁ f hf z
  have hE := C1.eis_leftInv d hf z
  refine ⟨fun nb lam 𝓖 𝓖₀ h h₀ uM ν 𝓤 𝓤₀ hU hU₀ T T' hT x => ?_, fun nb' lam' 𝓖' 𝓖'₀ h' h'₀ T' x => ?_⟩
  · have step1 : ∀ g, fc d.B.ψ d.b nb lam 𝓖 (d.eis f s₁ z) T g = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T g :=
      fun g => C1.fc_dom d h h₀ _ hE T g
    simp_rw [step1]
    have := hU.2.1
    have : VAddInvariantMeasure L.ratV (Fin L.n → AE F E) ν := ⟨fun c s _ => measure_preimage_add ν c.1 s⟩
    have : Countable L.ratV := by
      have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
      refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
        (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
      obtain ⟨v, hv⟩ := C1.ratV_inc u.2
      exact ⟨v, Subtype.ext hv.symm⟩
    refine hU.2.2.1.setIntegral_eq hU₀.2.2.1 fun u₀ u => ?_
    show fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM (u₀.1 + u) * x) = fc d.B.ψ d.b nb lam 𝓖₀ (d.eis f s₁ z) T (uM u * x)
    rw [C1.uM_add hU, mul_assoc, C1.fc_conj h₀ hU _ hE hT u₀.2]
  · exact C1.fc_dom L.sd h' h'₀ _ (GlobalTheory.Eis.leftInv_cosetSum (C1.phz_j_leftInv L hf z x)) T' 1

end PositivityTheory.SiegelWeilFormula.Act

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SectionSumIntegralExpand
section
noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : SD σ} (R : RD d) (L : LD d)

variable {R L}
variable {nb : nA σ d.Y d.b → d.G} {uM : (Fin L.n → AE F E) → d.G} {nb' : nA σ L.Y L.b → G2 σ L.Y} {w₁ : d.G}
  {cM : (Fin L.n → AE F E) × AF F → d.G} {δ : E}

def th (T : nF σ d.Y d.b) (β : nA σ d.Y d.b) : ℂ := d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))

def th' (T' : nF σ L.Y L.b) (β : nA σ L.Y L.b) : ℂ :=
  d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T'.1.1 * β.1))))

theorem section_sum_integral_expand {f : d.G → ℂ} {s₁ z : ℂ} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)} {T : nF σ d.Y d.b}
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hν : ν 𝓤 = 1) (hlam : lam 𝓖 = 1) (x : d.G)
    (hi : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) ((ν.restrict 𝓤).prod (lam.restrict 𝓖)))
    (hs : Summable fun q : Cs d => ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖))) :
    sec2 L f s₁ z nb lam 𝓖 T uM ν 𝓤 x =
        ∫ p, E2 L (phz d f s₁ z) (nb p.2 * (uM p.1 * x)) * th T p.2 ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) ∧
      ∫⁻ p, ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x))) * th T p.2‖ₑ
        ∂((ν.restrict 𝓤).prod (lam.restrict 𝓖)) < ⊤ := by
  have : Countable (rat2 σ d.Y) := GlobalTheory.EisBL.DoubledGroupTopology.countable_rational_points_doubled σ d.Y
  have : Countable (Cs d) := Quotient.countable
  have : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by simp [hν])
  have : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by simp [hlam])
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  let g : {q : Cs d // ¬ LagrangianCondition L (rep q)} → (Fin L.n → AE F E) × nA σ d.Y d.b → ℂ :=
    fun q => kq L f s₁ z nb T uM (rep q.1) x
  have hgi : ∀ q, Integrable (g q) μ := fun q => hi q.1
  have hgs : Summable fun q => ∫ p, ‖g q p‖ ∂μ := hs.subtype _
  have htm : ∀ q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, tm L f s₁ z nb lam 𝓖 T uM ν 𝓤 (rep q.1) x = ∫ p, g q p ∂μ := by
    intro q
    rw [hμ, integral_prod _ (hgi q)]
    rfl
  constructor
  · unfold sec2
    simp_rw [htm]
    rw [(hasSum_integral_of_summable_integral_norm hgi hgs).tsum_eq]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [g, kq, E2, th]
    rw [tsum_mul_right]
  · have hm : ∀ q, AEMeasurable (fun p => ‖g q p‖ₑ) μ := fun q => (hgi q).aemeasurable.enorm
    have e1 : ∫⁻ p, ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)}, ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x))) * th T p.2‖ₑ ∂μ =
        ∑' q, ENNReal.ofReal (∫ p, ‖g q p‖ ∂μ) := by
      rw [show (fun p => ∑' q : {q : Cs d // ¬ LagrangianCondition L (rep q)},
          ‖phz d f s₁ z (rep q.1 * (nb p.2 * (uM p.1 * x))) * th T p.2‖ₑ) = fun p => ∑' q, ‖g q p‖ₑ from rfl,
        lintegral_tsum hm]
      exact tsum_congr fun q => (ofReal_integral_norm_eq_lintegral_enorm (hgi q)).symm
    rw [e1, ← ENNReal.ofReal_tsum_of_nonneg (fun q => integral_nonneg fun p => norm_nonneg _) hgs]
    exact ENNReal.ofReal_lt_top

end PositivityTheory.SiegelWeilFormula.Act.C5

end
end

