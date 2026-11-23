module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0432
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.HeisSch
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.EcHeisSch
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureKernelMemJacquetKernel
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem tmul_mem_twKer_topRep (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (τ : Representation ℂ (Mir k i) V) {w : V} (hw : w ∈ twKer τ (MirUin k i) 1) (b : W) :
    w ⊗ₜ[ℂ] b ∈ twKer (topRep τ W) ⊤ 1 := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨n, a, rfl⟩ := hw
    obtain ⟨x, hx⟩ := exists_uM_of_mem k i n.2
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd x, Subgroup.mem_top _⟩, a ⊗ₜ[ℂ] b, ?_⟩
    have h1 : topRep τ W (Multiplicative.ofAdd x) (a ⊗ₜ[ℂ] b) = (τ (uM k i x) a) ⊗ₜ[ℂ] b := rfl
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [h1, hx, TensorProduct.sub_tmul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [TensorProduct.add_tmul]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [← TensorProduct.smul_tmul']
    exact Submodule.smul_mem _ c hx

theorem mem_twKer_topRep_of_clT_eq_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (z : V ⊗[ℂ] W), clT τ W z = 0 → z ∈ twKer (topRep τ W) ⊤ 1 := by
  intro k _ _ _ _ i V W _ _ _ _ τ z hz
  have hex : Function.Exact (twKer τ (MirUin k i) 1).subtype (twKer τ (MirUin k i) 1).mkQ :=
    LinearMap.exact_subtype_mkQ _
  obtain ⟨y, rfl⟩ := (rTensor_exact W hex (Submodule.mkQ_surjective _) z).1 hz
  clear hz
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul w b => exact tmul_mem_twKer_topRep k i τ w.2 b
  | add a b ha hb =>
    rw [map_add (f := _)]
    exact add_mem ha hb

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientUnipotentLeviInvariance
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WzHeis

section Blocks
variable {R : Type} [CommRing R] {n ρ p : ℕ} (hn : ρ + p = n)

theorem block_mul₂ (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d * bl hn a' b' c' d' =
      bl hn (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one : bl hn (1 : Matrix (Fin ρ) (Fin ρ) R) 0 0 1 = 1 := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem bl_add (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d + bl hn a' b' c' d' = bl hn (a + a') (b + b') (c + c') (d + d') := by
  unfold bl
  rw [← Matrix.fromBlocks_add]
  rfl

theorem block_sub (a a' : Matrix (Fin ρ) (Fin ρ) R) (b b' : Matrix (Fin ρ) (Fin p) R)
    (c c' : Matrix (Fin p) (Fin ρ) R) (d d' : Matrix (Fin p) (Fin p) R) :
    bl hn a b c d - bl hn a' b' c' d' = bl hn (a - a') (b - b') (c - c') (d - d') := by
  ext i j
  simp only [bl, Matrix.sub_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem blockMatrix_zero : bl hn (0 : Matrix (Fin ρ) (Fin ρ) R) 0 0 0 = 0 := by
  ext i j
  simp only [bl, Matrix.zero_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem det_bl_lower (c : Matrix (Fin p) (Fin ρ) R) : (bl hn 1 0 c 1).det = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₁₂]
  simp

end Blocks

variable {D : D7} {n ρ p : ℕ}

theorem adj_bl (hn : ρ + p = n) (a : Mx D ρ ρ) (b : Mx D ρ p) (c : Mx D p ρ) (d : Mx D p p) :
    adj (bl hn a b c d) = bl hn (adj a) (adj c) (adj b) (adj d) := by
  ext i j
  simp only [adj, bl, Matrix.transpose_apply, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  have e : chz ψ b₀ (a + b) = ψ (GlobalTheory.CompanionTheory.FourierN.pr b₀.1 (a.1 + b.1)) := rfl
  rw [e, GlobalTheory.CompanionTheory.FourierN.pr_add_right, AddChar.map_add_eq_mul]
  rfl

theorem conj_chz (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    conj (chz ψ b₀ a) = conj (chz ψ b₀ (a + b)) * chz ψ b₀ b := by
  have hb : ‖chz ψ b₀ b‖ = 1 := hψ.2.1 _
  rw [chz_add, map_mul, mul_assoc, Complex.conj_mul', hb]
  simp

variable {hn : ρ + p = n} (M : Maps D hn)

theorem mat_u (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    mat (M.nzx 0 x₀ * M.emb g₁) = blk4 1 (bl hn 0 x₀ (adj x₀) b) 0 1 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  rw [LeftInvSect.mat_mul, M.nzx_mat, h1, submatrix_fromBlocks_mul]
  simp [bl_add]

theorem nzx_comm (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (ζ z₀ : hermA D ρ) :
    M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁) = (M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0 := by
  have h1 := M.emb_mat g₁ 1 b 0 1 hg
  rw [blockRowSubstitution_one, blockMatrix_zero] at h1
  apply GlobalTheory.CompanionTheory.FourierN.mat_injective
  rw [LeftInvSect.mat_mul, LeftInvSect.mat_mul, LeftInvSect.mat_mul, mat_u M g₁ b hg, M.nzx_mat, M.nzx_mat, M.nzx_mat, h1]
  simp only [submatrix_fromBlocks_mul, bl_add, adj_zero, mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add]
  rw [show (ζ + z₀).1 = z₀.1 + ζ.1 from add_comm _ _]

theorem q_mat (g₁ : G D p) (b : Mx D p p) (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) :
    ∃ (β δ : Mx D n n), mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹) = blk4 (bl hn 1 0 (adj x₀) 1) β 0 δ := by
  have h := GlobalTheory.CompanionTheory.SwUnf.SmallCell.conj_block M.w (M.nzx 0 x₀ * M.emb g₁) M.w_mat (mat_u M g₁ b hg x₀)
  have hC : adj (bl hn (-1 : Mx D ρ ρ) 0 0 0) = bl hn (-1) 0 0 0 := by
    simp [adj_bl, adj_zero, adj_neg, adj_one]
  rw [hC] at h
  have e1 : (1 : Mx D n n) - bl hn 0 0 0 1 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0 = bl hn 1 0 (adj x₀) 1 := by
    rw [← blockRowSubstitution_one hn]
    simp [block_mul₂, block_sub]
  have e2 : -(bl hn (-1 : Mx D ρ ρ) 0 0 0 * bl hn 0 x₀ (adj x₀) b * bl hn (-1) 0 0 0) = (0 : Mx D n n) := by
    simp [block_mul₂, blockMatrix_zero]
  rw [e1, e2] at h
  exact ⟨_, _, h⟩

theorem law_q (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ) (hf : IsLaw χ z f) (g₁ : G D p) (b : Mx D p p)
    (hg : mat g₁ = blk4 1 b 0 1) (x₀ : Mx D ρ p) (v : G D n) :
    f (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * v) = f v := by
  obtain ⟨β, δ, hq⟩ := q_mat M g₁ b hg x₀
  let a : GL (Fin n) (AE D) := ⟨bl hn 1 0 (adj x₀) 1, bl hn 1 0 (-adj x₀) 1,
    by simp [block_mul₂, blockRowSubstitution_one], by simp [block_mul₂, blockRowSubstitution_one]⟩
  have hdet : Matrix.GeneralLinearGroup.det a = 1 := Units.ext (det_bl_lower hn _)
  have hA : blkA (mat (M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹)) = a.1 := by
    rw [hq]
    simp [blkA, blk4, a]
  rw [hf _ (GlobalTheory.CompanionTheory.SwUnf.SmallCell.mem_siegelParabolic_of_lowerLeft_entries_eq_zero hq) a hA v, hdet, map_one, map_one]
  simp [npow]

theorem wz_heis : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ →
  ∀ (b₀ : HermE D ρ) (χ : (AE D)ˣ →* Circle) (z : ℂ) (f : G D n → ℂ), IsLaw χ z f → ∀ (g₁ : G D p) (b : Mx D p p),
  mat g₁ = blk4 1 b 0 1 → ∀ (z₀ : hermA D ρ) (x₀ : Mx D ρ p) (x : G D n),
    Wz M m ψ b₀ f (M.nzx z₀ x₀ * M.emb g₁ * x) = chz ψ b₀ z₀ * Wz M m ψ b₀ f x := by
  intro D n ρ p hn M m ψ hψ b₀ χ z f hf g₁ b hg z₀ x₀ x
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨hlam, -, -⟩ := m.hz
  have step : ∀ ζ : hermA D ρ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) =
      f (M.w * M.nzx (ζ + z₀) 0 * x) := by
    intro ζ
    have e : M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x) =
        M.w * (M.nzx 0 x₀ * M.emb g₁) * M.w⁻¹ * (M.w * M.nzx (ζ + z₀) 0 * x) := by
      have h := nzx_comm M g₁ b hg x₀ ζ z₀
      calc M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)
          = M.w * (M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁)) * x := by group
        _ = M.w * ((M.nzx 0 x₀ * M.emb g₁) * M.nzx (ζ + z₀) 0) * x := by rw [h]
        _ = _ := by group
    rw [e, law_q M χ z f hf g₁ b hg x₀]
  unfold Wz
  calc ∫ ζ, f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) ∂m.lz
      = ∫ ζ, (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) (ζ + z₀) ∂m.lz := by
        refine integral_congr_ae (.of_forall fun ζ => ?_)
        show f (M.w * M.nzx ζ 0 * (M.nzx z₀ x₀ * M.emb g₁ * x)) * conj (chz ψ b₀ ζ) =
          chz ψ b₀ z₀ * (f (M.w * M.nzx (ζ + z₀) 0 * x) * conj (chz ψ b₀ (ζ + z₀)))
        rw [step, conj_chz ψ hψ b₀ ζ z₀]
        ring
    _ = ∫ y, chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y)) ∂m.lz :=
        integral_add_right_eq_self (μ := m.lz) (fun y => chz ψ b₀ z₀ * (f (M.w * M.nzx y 0 * x) * conj (chz ψ b₀ y))) z₀
    _ = _ := integral_const_mul _ _

end GlobalTheory.CompanionTheory.WzHeis
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousFlipGL
section
open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ConjSat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem locU_eq_of_under {w u : HeightOneSpectrum (𝓞 E)}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : locU n u = locU n w := by
  simp only [locU, h]

abbrev flipGL (w : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E) ≃* GL (Fin n) (w.adicCompletion E) :=
  GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n

theorem flipGL_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)) :
    flipGL w g = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem continuous_flipGL (w : HeightOneSpectrum (𝓞 E)) : Continuous (flipGL (n := n) w) := by
  have : (flipGL (n := n) w : _ → _) = fun g => GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
    funext (flipGL_eq w)
  rw [this]
  exact (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1))

theorem cLoc_eq_flipGL (x : UA E n) (w : HeightOneSpectrum (𝓞 E)) :
    cLoc w x = flipGL w (cLoc (GlobalTheory.ThetaSatake.cw w) x) :=
  (GlobalTheory.BCT.LocCpt.cLoc_eq_invT x w).trans (flipGL_eq w _).symm

def flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) : SmIrr (GLw n (GlobalTheory.ThetaSatake.cw w)) where
  V := σ.V
  ρ := σ.ρ.comp (flipGL w).toMonoidHom
  smooth v := (σ.smooth v).preimage (continuous_flipGL w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (flipGL w).surjective σ.irred

theorem hasSatGL_flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) {B : Multiset ℂˣ}
    (h : HasSatGL w σ.ρ B) : HasSatGL (GlobalTheory.ThetaSatake.cw w) (flipIrr σ).ρ (B.map (·⁻¹)) := by
  refine GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w).symm (fun a => ?_)
    (GlobalTheory.ThetaSatake.absNorm_cw w) (LinearEquiv.refl ℂ σ.V) (fun g x => ?_) h
  · have := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w).2.2 ((GlobalTheory.ThetaSatake.cloc w).symm a)
    exact (this.symm.trans (congrArg _ ((GlobalTheory.ThetaSatake.cloc w).apply_symm_apply a)))
  · change σ.ρ (flipGL w ((flipGL w).symm g)) x = σ.ρ g x
    rw [MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.ConjSat


open GlobalTheory.CompanionTheory.ConjSat in
theorem GlobalTheory.CompanionTheory.ConjSat.satConj : PositivityTheory.Rg.BcB.F.RS.SatConj := by
  intro E _ _ _ n π w u B _ _ hc ⟨σ, ⟨hirr, f, f0, hf, hfx⟩, hB⟩
  obtain rfl : u = GlobalTheory.ThetaSatake.cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
  refine ⟨flipIrr σ, ⟨(flipIrr σ).irred, f, f0, hf, fun x v => ?_⟩, hasSatGL_flipIrr σ hB⟩
  have hx : (x : UA E n) ∈ locU n w := locU_eq_of_under hc.1 ▸ x.2
  have := hfx ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply] at this
  change f (σ.ρ (flipGL w (cLoc _ x.1)) v) = _
  rw [← cLoc_eq_flipGL]
  exact this

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionJacquetKernelStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coset_function_jacquet_kernel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (z : Z), z ∈ twKer ρ₀ ⊤ 1 → cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.CosetKer.cosetFn_mem_twKer <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetFunctionTranslateJacquetKernel
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem topPart_append_zero (i t : ℕ) (a : Fin t → k) : topP i t (Fin.append (0 : Fin i → k) a) = 0 := by
  funext j
  exact Fin.append_left _ _ j

theorem middlePart_append_zero (i t : ℕ) (a : Fin t → k) : middlePart i t (Fin.append (0 : Fin i → k) a) = a := by
  funext j
  exact Fin.append_right _ _ j

theorem fibAct_cosetFn_translate (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) {c : k} (hc : c ≠ 0) (a : Fin t → k) (z : Z) :
    fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z) = cosetFn t hc 0 z := by
  apply Subtype.ext
  funext v
  have h1 : Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)) = 1 :=
    congrArg Multiplicative.ofAdd (topPart_append_zero i t a)
  have h2 : (fibAct t ρ₀ (Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a)) (cosetFn t hc a z)).1 v
      = ρ₀ (Multiplicative.ofAdd (topP i t (Fin.append (0 : Fin i → k) a)))
        ((cosetFn t hc a z).1 (v + middlePart i t (Fin.append (0 : Fin i → k) a))) := rfl
  rw [h2, h1, map_one, middlePart_append_zero]
  show (cosetSet t c a).indicator (fun _ => z) (v + a) = (cosetSet t c 0).indicator (fun _ => z) v
  have hs : (v + a ∈ cosetSet t c a) ↔ v ∈ cosetSet t c 0 := by
    have : v + a - a = v - 0 := by simp
    show Multiplicative.ofAdd (v + a - a) ∈ Lc t c ↔ Multiplicative.ofAdd (v - 0) ∈ Lc t c
    rw [this]
  classical
  by_cases hv : v ∈ cosetSet t c 0
  · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (hs.2 hv)]
  · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem (fun h => hv (hs.1 h))]

theorem cosetFn_sub_cosetFn_zero_mem_twKer : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z) (c : k) (hc : c ≠ 0) (a : Fin t → k) (z : Z), cosetFn t hc a z - cosetFn t hc 0 z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
  intro k _ _ _ _ i t Z _ _ ρ₀ c hc a z
  have hgen : cosetFn t hc 0 z - cosetFn t hc a z ∈ twKer (fibAct t ρ₀) ⊤ 1 := by
    refine Submodule.subset_span ⟨⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩, cosetFn t hc a z, ?_⟩
    have h1 : (((1 : (⊤ : Subgroup (Multiplicative (Fin (i + t) → k))) →* ℂˣ)
        ⟨Multiplicative.ofAdd (Fin.append (0 : Fin i → k) a), trivial⟩ : ℂˣ) : ℂ) = 1 := rfl
    rw [h1, one_smul]
    exact congrArg (· - cosetFn t hc a z) (fibAct_cosetFn_translate i t ρ₀ hc a z).symm
  have := Submodule.neg_mem _ hgen
  rwa [neg_sub] at this

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHeisenbergSchwartz
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HeisSchwartz

theorem heisSch_holds : PositivityTheory.GramSchwartzFunctions.EC.HeisSch := PositivityTheory.RdEc.heisSch

end GlobalTheory.CompanionTheory.HeisSchwartz
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtensionStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_extension : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ} (U : Submodule ℂ (Sm E N)) (z : ℂ), (∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W)) → ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (tw U z) K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.typed_tw_finite | exact GlobalTheory.CompanionTheory.LimV.typed_tw_finite | (intros; apply GlobalTheory.CompanionTheory.LimV.typed_tw_finite <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarMeasureCosetNeZero
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibKer

theorem volume_cosetSet_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] (c : k), c ≠ 0 → (((μ (cosetSet t c 0)).toReal : ℝ) : ℂ) ≠ 0 := by
  intro k _ _ _ _ t _ _ μ _ c hc
  have h0 : (0 : Fin t → k) ∈ cosetSet t c 0 := by
    show Multiplicative.ofAdd ((0 : Fin t → k) - 0) ∈ Lc t c
    rw [sub_zero, ofAdd_zero]
    exact one_mem _
  have hpos : 0 < μ (cosetSet t c 0) := (isClopen_cosetSet t c 0).isOpen.measure_pos μ ⟨0, h0⟩
  have hfin : μ (cosetSet t c 0) < ⊤ := (isCompact_cosetSet t hc 0).measure_lt_top
  rw [Complex.ofReal_ne_zero]
  exact (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'

end GlobalTheory.CompanionTheory.BZPsiPG.FibKer
end

