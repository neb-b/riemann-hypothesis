module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.IncMScalarMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0047
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.CountableMat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHtA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit.Ht
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem par_topleft_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (t : GL (Fin d.n) (AE F E)) (hp : IsPar p t) :
    ∃ tb : GL (Fin d.n) E, (inFrame d.b p).toBlocks₁₁ = incM F (tb⁻¹).1 * t.1 * incM F tb.1 := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  refine ⟨tb, ?_⟩
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hp' : mat2 p * DC = DC * t.1 := hp
  have hcol : ∀ M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), M * E1 = M.toCols₁ := by
    intro M
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hBB : incM F (d.b⁻¹).1 * incM F d.b.1 = 1 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have key : inFrame d.b p * E1 = E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
    have e0 : inFrame d.b p = incM F (d.b⁻¹).1 * mat2 p * incM F d.b.1 := rfl
    calc inFrame d.b p * E1 = incM F (d.b⁻¹).1 * (mat2 p * (incM F d.b.1 * E1)) := by
          rw [e0]; simp only [Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((mat2 p * DC) * incM F tb.1) := by
          rw [hb, Matrix.mul_assoc]
      _ = incM F (d.b⁻¹).1 * ((DC * t.1) * incM F tb.1) := by rw [hp']
      _ = (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * (incM F (tb⁻¹).1 * t.1 * incM F tb.1) := by
          rw [hdc]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hBB, Matrix.one_mul]
  ext i j
  have := congrFun (congrFun key (Sum.inl i)) j
  rw [hcol] at this
  simpa [E1, Matrix.toBlocks₁₁, Matrix.toCols₁, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq] using this
theorem inFrame_form_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (y : d.G) : ∃ C' : Matrix (Fin d.n) (Fin d.n) (AE F E),
    (∃ ε : ℤˣ, C' = ((ε : ℤ) : AE F E) • 1) ∧
    (inFrame d.b y)ᵀ * Matrix.fromBlocks 0 1 C' 0 * (inFrame d.b y).map (cA σ) = Matrix.fromBlocks 0 1 C' 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  have hF : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
      Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 := by
    rw [e1, e2, ← key, hε]
    simp only [incM, Matrix.fromBlocks_map, Matrix.map_zero _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine ⟨((ε : ℤ) : AE F E) • 1, ⟨ε, rfl⟩, ?_⟩
  have hM : (mat2 y)ᵀ * dbl (incM F d.Y.J) * (mat2 y).map (cA σ) = dbl (incM F d.Y.J) := y.2
  have := form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hM
  rw [← hF]
  exact this
theorem levi_tu_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1) :
    t.1ᵀ * u.1.map (cA σ) = 1 := by
  obtain ⟨C', -, h⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d x
  rw [hx] at h
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at h
  exact h.2.1
theorem frame_iwa_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : d.G) : ∃ (D : GL (Fin d.n) (AE F E)) (k : d.G), k ∈ d.K ∧
    d.a g = ((GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det D) : ℝ≥0) : ℝ)⁻¹ ∧
    (inFrame d.b g).toBlocks₂₁ = D.1 * (inFrame d.b k).toBlocks₂₁ ∧
    (inFrame d.b g).toBlocks₂₂ = D.1 * (inFrame d.b k).toBlocks₂₂ := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa g
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p t' hp
  obtain ⟨tb, htl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.par_topleft_k d p t' hp
  set A := (inFrame d.b p).toBlocks₁₁ with hA
  set B := (inFrame d.b p).toBlocks₁₂ with hB
  set D₀ := (inFrame d.b p).toBlocks₂₂ with hD₀
  have hPb : inFrame d.b p = Matrix.fromBlocks A B 0 D₀ := by rw [← h21, Matrix.fromBlocks_toBlocks]
  obtain ⟨C', ⟨ε, hC'⟩, hform⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.inFrame_form_k d p
  rw [hPb, hC'] at hform
  simp only [Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.transpose_zero,
    Matrix.map_zero _ (map_zero (cA σ)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one,
    Matrix.fromBlocks_inj] at hform
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have hDA : D₀ᵀ * A.map (cA σ) = 1 := by
    have h3 := hform.2.2.1
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul] at h3
    have := congrArg (fun M => ((ε : ℤ) : AE F E) • M) h3
    simpa [smul_smul, hεε] using this
  have hdet : D₀.det * cA σ A.det = 1 := by
    have := congrArg Matrix.det hDA
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one,
      show (A.map (cA σ)).det = cA σ A.det from (AlgHom.map_det (cA σ) A).symm] at this
    exact this
  have hDu : IsUnit D₀ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_exists_inv.2 ⟨_, hdet⟩)
  refine ⟨hDu.unit, k, hk, ?_, ?_, ?_⟩
  · rw [d.ok.hgt.val p t' hp k hk]
    have hAt : A.det = (Matrix.GeneralLinearGroup.det t').1 := by
      rw [htl, Matrix.det_mul, Matrix.det_mul]
      have hinv : (incM F (tb⁻¹).1).det * (incM F tb.1).det = 1 := by
        rw [← Matrix.det_mul]
        have e : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
          simp only [incM, ← Matrix.map_mul, Units.inv_mul]
          exact Matrix.map_one _ (map_zero _) (map_one _)
        rw [e, Matrix.det_one]
      simp only [Matrix.GeneralLinearGroup.val_det_apply]
      linear_combination (t'.1.det) * hinv
    have hU : Matrix.GeneralLinearGroup.det hDu.unit *
        GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det t') = 1 := by
      ext
      simp only [Units.val_mul, Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec,
        GlobalTheory.Doubling.conjUnit, Units.coe_map]
      change D₀.det * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ t'.1.det = 1
      rw [sigR_eq_cA, ← Matrix.GeneralLinearGroup.val_det_apply, ← hAt]
      exact hdet
    have := congrArg (GlobalTheory.Doubling.absE F E) hU
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at this
    have hpos : (0 : ℝ≥0) < GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit) := by
      rcases eq_or_ne (GlobalTheory.Doubling.absE F E (Matrix.GeneralLinearGroup.det hDu.unit)) 0 with h | h
      · rw [h, zero_mul] at this; exact absurd this zero_ne_one
      · exact pos_iff_ne_zero.2 h
    rw [eq_inv_of_mul_eq_one_right this, NNReal.coe_inv]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
  · rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hPb]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (inFrame d.b k)]
    simp [Matrix.fromBlocks_multiply]
theorem bottom_rows_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (t u : GL (Fin d.n) (AE F E)) (hx : inFrame d.b x = Matrix.fromBlocks t.1 0 0 u.1)
    (nb : nA σ d.Y d.b → d.G) (hnb : IsNMap d.b nb) (ε : ℤˣ) (w : d.G) (hw : d.IsW ε w) (β : nA σ d.Y d.b) :
    (inFrame d.b (w * nb β * x)).toBlocks₂₁ = (((ε : ℤ) : AE F E) • t.1) ∧
    (inFrame d.b (w * nb β * x)).toBlocks₂₂ = (((ε : ℤ) : AE F E) • (β.1 * u.1)) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, hw, hnb β, hx]
  simp only [Matrix.fromBlocks_multiply, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.zero_mul, Matrix.mul_zero,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add, Matrix.of_apply, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂]
  constructor <;> ext i j <;> simp [Matrix.smul_apply, Matrix.mul_apply, Matrix.one_apply, ite_mul, Finset.sum_ite_eq,
    Finset.mul_sum, mul_assoc]
end PositivityTheory.SiegelWeilFormula.KWhit.Ht
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwaX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem kFinK_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.KFinK_k := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => _root_.PositivityTheory.SiegelWeilFormula.KWhit.kfin_om_k d hΦ hk
theorem iwaRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.IwaRedC_k := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.par_decomp_k d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KWhit.int_n_k d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    unfold flat
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc], _root_.PositivityTheory.SiegelWeilFormula.KWhit.a_mul_K_k d _ k hk,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.constantTerm_mul_right]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.orb_n_k hT d T (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d _ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLinX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem linRedC_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.LinRedC_k := by
  intro hT hTC hLB hU hS c F E _ _ _ _ _ σ d hE k cs Φs hK x hW nb lam 𝓖 hcd ε w hw T hND
  have hTT : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := hT.2.2.2.1
  have hTA : _root_.PositivityTheory.SiegelWeilFormula.ThetaAuto_k := hT.2.2.2.2
  have hsch : ∀ i ∈ (Finset.univ : Finset (Fin k)), Φs i ∈ d.sch := fun i _ => (hK i).1
  have hsum := _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_sum_mem_k d Finset.univ cs Φs hsch
  have hIfun : d.I (∑ i, cs i • Φs i) = ∑ i, cs i • d.I (Φs i) := by
    funext y; rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_I_sum_k d hTT hTA Finset.univ cs Φs hsch y]; simp [Finset.sum_apply]
  have horb : d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * d.orb T (d.om x (Φs i)) := by
    rw [← hTC F E σ d _ hsum nb lam 𝓖 hcd T x, hIfun,
      _root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_fc_sum_k hLB d hcd T hND x Finset.univ cs (fun i => d.I (Φs i)) (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.1)
        (fun i => ((hTA F E σ d).2.2 _ (hK i).1).2.2)]
    exact Finset.sum_congr rfl fun i _ => by rw [hTC F E σ d _ (hK i).1 nb lam 𝓖 hcd T x]
  have horbc : c * d.orb T (d.om x (∑ i, cs i • Φs i)) = ∑ i, cs i * (c * d.orb T (d.om x (Φs i))) := by
    rw [horb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  choose t ht using fun i => hU F E σ d (s0 d.m d.n) (d.sec0 (Φs i)) (hS F E σ d (Φs i) (hK i)) (hE (Φs i) (hK i))
  have hval := lin_holValueAt_sum Finset.univ cs
    (fun i z => ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam)
    (fun i => c * d.orb T (d.om x (Φs i))) (s0 d.m d.n) (fun i _ => hW i nb lam 𝓖 hcd ε w hw T hND)
  rw [horbc]
  refine hval.congr ⟨∑ i, |t i|, fun z hz => ?_⟩
  have hzi : ∀ i, t i < z.re := fun i => lt_of_le_of_lt
    ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i))) hz
  have hint : ∀ i, Integrable (fun β => flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) *
      d.B.ψ (-d.tt (T.1.1 * β.1))) lam := fun i =>
    ((ht i z (hzi i) nb lam 𝓖 hcd ε w hw x).1).mul_bdd (_root_.PositivityTheory.SiegelWeilFormula.KWhit.lin_psi_meas_k d T.1.1).aestronglyMeasurable
      (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
  show ∑ i, cs i * ∫ β, flat d.a (d.sec0 (Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam =
    ∫ β, flat d.a (d.sec0 (∑ i, cs i • Φs i)) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam
  refine (Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm).trans ?_
  rw [← integral_finsetSum _ fun i _ => (hint i).const_mul (cs i)]
  congr 1
  funext β
  simp only [flat, constantTerm_finsetSum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitVac
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def vac_gen_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ φ, Dense.Good φ ∧ f = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R (fun _ => 1) (Dense.pf φ)}
theorem vac_gen_sub_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R ⊆ R.vac := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩
theorem vac_le_span_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vac ≤ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : _root_.PositivityTheory.SiegelWeilFormula.KWhit.genL_k R (fun _ => 1) g ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key
theorem vac_isPureBy_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = _root_.PositivityTheory.SiegelWeilFormula.KWhit.genF_k R (fun _ => 1) (Dense.pf φ)) : ∃ gf, _root_.PositivityTheory.SiegelWeilFormula.KWhit.IsPureBy_k R Φ (fun _ => 1) gf := by
  refine ⟨φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl
theorem vacSpan_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.VacSpan_k := by
  intro hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  have h1 : d.T Φ ∈ Submodule.span ℂ (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_k R) := _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_le_span_k R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (hvf (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2)))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ hvf (_root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2)),
    hTs i ▸ _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_gen_sub_k R (gs i).2, ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (gs i).2
    exact _root_.PositivityTheory.SiegelWeilFormula.KWhit.vac_isPureBy_k R φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sub_k, _root_.PositivityTheory.SiegelWeilFormula.KWhit.T_sum_k, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilMeasdictHOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw SiegelEisensteinSeries.Grp
namespace PositivityTheory.SiegelWeilFormula.MeasD
open PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KWhit PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
section HOf
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {η : E} (hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n)
theorem hOf_val_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ)) (β : nA σ d.Y d.b) :
    ((hOf β).1 : Mx F E d.n d.n) = -(inclR (F := F) (AF F) η⁻¹ • (β.1)ᵀ) := by
  ext a b
  have h := congrFun (congrFun (hof β) b) a
  rw [incM_scalar_mul] at h
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul] at h ⊢
  linear_combination inclR (F := F) (AF F) η⁻¹ * h - ((hOf β).1 a b) * inclR_inv_mul (F := F) hne
theorem inv_mem_k (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) (S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) :
    (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)) ∈ nA σ d.Y d.b := by
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  obtain ⟨⟨ε, hb⟩, -⟩ := d.ok.frame
  have hrel := _root_.PositivityTheory.SiegelWeilFormula.MeasD.eta_sign_k d herm hb
  rw [mem_nA_iff hσ hb]
  have hS : ∀ a b, HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ (S.1 b a) = S.1 a b := S.2
  have h1 : ∀ a b, cA σ (S.1 b a) = S.1 a b := fun a b => by rw [← sigR_eq]; exact hS a b
  have h2 : cA σ (inclR (F := F) (AF F) η) = -(((ε : ℤ) : AE F E)) * inclR (F := F) (AF F) η := by
    rw [cA_inclR', hrel, map_mul, map_neg, inclR_int]
  show (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ))ᵀ =
    -((((ε : ℤ) : AE F E)) • (-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)).map (cA σ))
  ext a b
  simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_neg, map_mul,
    h1, h2]
  linear_combination (inclR (F := F) (AF F) η * S.1 a b) * eps_sq (F := F) (E := E) ε
def hEq_k (hne : η ≠ 0)
    (hof : ∀ β, β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * ((hOf β).1 : Mx F E d.n d.n)ᵀ))
    (herm : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    nA σ d.Y d.b ≃ₜ+ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n where
  toFun := hOf
  invFun S := ⟨-(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ), _root_.PositivityTheory.SiegelWeilFormula.MeasD.inv_mem_k herm S⟩
  left_inv β := by
    apply Subtype.ext
    show -(inclR (F := F) (AF F) η • ((hOf β).1 : Mx F E d.n d.n)ᵀ) = β.1
    rw [hof β, incM_scalar_mul]
  right_inv S := by
    apply Subtype.ext
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination (S.1 a b) * inclR_inv_mul (F := F) hne
  map_add' β γ := by
    apply Subtype.ext
    show ((hOf (β + γ)).1 : Mx F E d.n d.n) = (hOf β).1 + (hOf γ).1
    rw [_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof, _root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof]
    ext a b
    simp only [AddSubgroup.coe_add, Matrix.transpose_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.add_apply,
      smul_eq_mul]
    ring
  continuous_toFun := by
    apply continuous_induced_rng.2
    have hc : Continuous fun β : nA σ d.Y d.b => -(inclR (F := F) (AF F) η⁻¹ • (β.1 : Mx F E d.n d.n)ᵀ) :=
      (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
    exact hc.congr fun β => (_root_.PositivityTheory.SiegelWeilFormula.MeasD.hOf_val_k hOf hne hof β).symm
  continuous_invFun := by
    apply continuous_induced_rng.2
    show Continuous fun S : HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n => -(inclR (F := F) (AF F) η • (S.1 : Mx F E d.n d.n)ᵀ)
    exact (Continuous.fun_const_smul (continuous_subtype_val.matrix_transpose) _).fun_neg
end HOf
end PositivityTheory.SiegelWeilFormula.MeasD
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoCoefA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Tauto
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (g : UA σ d.A.J) (X : Matrix (Fin d.m) (Fin d.n) E) : Mx F E d.m d.n := mat g⁻¹ * incM F X
theorem cont_tr_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ d.schM) (X : Matrix (Fin d.m) (Fin d.n) E) :
    Continuous fun g : UA σ d.A.J => f (_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k d g X) := by
  have h1 : Continuous (f ∘ d.cmb) := PositivityTheory.ThKEst.continuous_schA (Φ := f ∘ d.cmb) hf
  have e : ∀ Y, f Y = (f ∘ d.cmb) (d.crd Y) := fun Y => by simp [_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.cmb_crd_k]
  have h2 : Continuous fun h : UA σ d.A.J =>
      (((h : GL (Fin d.m) (AE F E))⁻¹ : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) :=
    Units.continuous_coe_inv.comp continuous_subtype_val
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Tauto.tr_k, e, _root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.crd_mul_k]
  exact h1.comp (((_root_.PositivityTheory.SiegelWeilFormula.Kdil.Tb.continuous_mh_k d).comp h2).matrix_mulVec continuous_const)
theorem chr_comb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (β G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    d.B.ψ (-(⅟(2 : AF F) * d.tt (β * G))) * d.B.ψ (-(d.tt (T * β))) =
      d.B.ψ (-(d.tt ((⅟(2 : AF F) • G + T) * β))) := by
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, add_mul, Matrix.trace_add, smul_mul_assoc, Matrix.trace_smul, map_add (f := _), map_smul, smul_eq_mul,
    Matrix.trace_mul_comm G β]
  ring
theorem half_eq_iff_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (G T : Matrix (Fin d.n) (Fin d.n) (AE F E)) :
    ⅟(2 : AF F) • G + T = 0 ↔ G = (-2 : ℤ) • T := by
  have h2 : algebraMap (AF F) (AE F E) ⅟(2 : AF F) * 2 = 1 := by
    rw [← map_ofNat (algebraMap (AF F) (AE F E)) 2, ← map_mul, invOf_mul_self, map_one]
  constructor
  · intro h
    ext i j
    have := congrFun (congrFun h i) j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def] at this
    rw [Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination 2 * this - G i j * h2
  · rintro rfl
    ext i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Matrix.smul_apply, zsmul_eq_mul]
    push_cast
    linear_combination (-T i j) * h2
end PositivityTheory.SiegelWeilFormula.Tauto
end
end
end

