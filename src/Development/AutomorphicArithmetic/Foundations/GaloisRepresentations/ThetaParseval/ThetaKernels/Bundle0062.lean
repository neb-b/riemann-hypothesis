module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalWeilElements.TtSmul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0034
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0048
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapid
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.TendstoIndMul
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0018
public import Development.WeilBound.ThetaLifts.CartanFactorisation.ArchimedeanEvaluationVector
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0011
public import Development.WeilBound.ThetaLifts.CartanFactorisation.TensOfEval
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0036
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0049
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0037
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.FormEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0024
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GRPFockOf
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0038

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTwvUpTo
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.TW.UpToPf
open PositivityTheory.SiegelWeilFormula.Tpar
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem w_cols_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {ε : ℤˣ} {w : d.G} (hw : d.IsW ε w) :
    mat2 w * incM F d.b.1.toCols₂ = incM F d.b.1.toCols₁ ∧
    mat2 w⁻¹ * incM F d.b.1.toCols₂ = ((ε : ℤ) : AE F E) • incM F d.b.1.toCols₁ := by
  obtain ⟨t0, hB, -, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  have h1 := inFrame_mul hw
  have he : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hN : (Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • 1) 0 :
        Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) *
      Matrix.fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp [smul_smul, he]
  have h2 := inv_mul_frame h1 hN
  rw [hB, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks] at h1 h2
  obtain ⟨-, h1b⟩ := Matrix.fromCols_inj h1
  obtain ⟨-, h2b⟩ := Matrix.fromCols_inj h2
  refine ⟨?_, ?_⟩
  · rw [h1b]; simp
  · rw [h2b]; simp
theorem tt_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (ε : ℤˣ) (X Z : Mx F E d.m d.n) :
    d.tt (d.gram (((ε : ℤ) : AE F E) • X) Z) = ((ε : ℤ) : AF F) * d.tt (d.gram X Z) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, _root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul]
  rw [Int.cast_smul_eq_zsmul, map_zsmul, zsmul_eq_mul]
theorem upTo_of_k (hU : _root_.PositivityTheory.SiegelWeilFormula.TW.Uniq_k) : _root_.PositivityTheory.SiegelWeilFormula.TW.UpTo_k := by
  intro F E _ _ _ _ _ σ d ν hν ε w hw
  have h := d.ok.dbl
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨t0, -, hBx, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Tpar.frameData_k d
  obtain ⟨hw1, hw2⟩ := _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.w_cols_k d hw
  have hsp := h.weil.2.1.toIsSplitting
  obtain ⟨C, hC⟩ := hU F E σ d ν hν (d.l ∘ₗ d.om w) (hsp.adm w d.l h.adm) (by
    intro Z Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hsp.impl w _ Φ hΦ]
    have e : actB (cA σ) w (Z * (incM F d.b.1.toCols₂)ᵀ) =
        (Z * (incM F t0.1)ᵀ) * (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E))ᵀ := by
      change Z * (incM F d.b.1.toCols₂)ᵀ * (mat2 w)ᵀ = _
      rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw1, hBx, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e]
    convert h.kill (Z * (incM F t0.1)ᵀ) _ (hsp.pres w Φ hΦ) using 4
    all_goals rfl)
  refine ⟨C, fun Φ hΦ X => ?_⟩
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) = _
  have key : X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ =
      (((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ := by
    rw [Matrix.mul_assoc, ← Matrix.transpose_mul, hw2, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  have hr := l_rho_om h w (X * (incM F d.b.1.toCols₂)ᵀ) (Φ := Φ) hΦ
  change d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (d.om w Φ)) =
    d.l (d.om w (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ * (mat2 w⁻¹)ᵀ) Φ)) at hr
  rw [hr, key]
  have hm : d.dd.rho d.B.ψ ((((ε : ℤ) : AE F E) • X) * (incM F d.b.1.toCols₁)ᵀ) Φ ∈ d.sch :=
    GlobalTheory.HeisSchA.schr_mem_schA _ hψ _ Φ hΦ
  have e1 := hC _ hm
  simp only [LinearMap.comp_apply] at e1
  rw [e1]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
  simp only
  rw [(_root_.PositivityTheory.SiegelWeilFormula.Tunit.tHeis_k F E σ d Φ hΦ (((ε : ℤ) : AE F E) • X) Z).2, _root_.PositivityTheory.SiegelWeilFormula.TW.UpToPf.tt_smul_k]
end PositivityTheory.SiegelWeilFormula.TW.UpToPf
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGLiftAut
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
open PositivityTheory.ThKEnd.Grp in
private theorem stab_of_pk {m : ℕ} {Y : Spc F E m} {V : Type} [AddCommGroup V] [Module ℂ V] (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : UA σ Y.J →* Module.End ℂ V) (P : Submodule ℂ V)
    (hlev : ∀ Φ ∈ P, ∀ᶠ u in 𝓝 (1 : UA σ Y.J), (∀ w, (mat u).map (piInf (τ w)) = 1) → A u Φ = Φ)
    (hr : ∀ g ∈ UAt σ Y (evI F), ∀ Φ ∈ P, A g Φ ∈ P)
    (hl : ∀ v : Pl F, ∀ g ∈ UAt σ Y (evFin F v), ∀ Φ ∈ P, A g Φ ∈ P) (g : UA σ Y.J) : ∀ Φ ∈ P, A g Φ ∈ P := by
  intro Φ hΦ
  have h1 : Tendsto (fun S : Finset (Pl F) => (piece (eps S) (eps_sq S) g)⁻¹ * g) atTop (𝓝 1) := by
    rw [← inv_mul_cancel g]
    exact (tendsto_piece g).inv.mul_const g
  obtain ⟨S, h2⟩ := (h1.eventually (hlev Φ hΦ)).exists
  have h4 : ∀ w, (mat ((piece (eps S) (eps_sq S) g)⁻¹ * g)).map (piInf (τ w)) = 1 := fun w => by
    rw [mat_mul, Matrix.map_mul, ← piInf_piece S g, ← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨l, l1, l2⟩ := piece_prod g S
  have e : g = piece (eps ∅) (eps_sq ∅) g * l.prod * ((piece (eps S) (eps_sq S) g)⁻¹ * g) := by
    rw [← l2, mul_inv_cancel_left]
  rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h2 h4]
  refine hr _ (piece_inf g) _ ?_
  clear e h2 h4 l2
  induction l with
  | nil => simpa using hΦ
  | cons x l ih =>
    obtain ⟨v, hv⟩ := l1 x List.mem_cons_self
    rw [List.prod_cons, map_mul, Module.End.mul_apply]
    exact hl v x hv _ (ih fun h hh => l1 h (List.mem_cons_of_mem _ hh))
variable {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
theorem levelX_sch_k {r s r' s' : ℕ} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∀ᶠ u in 𝓝 (1 : UA σ X.J), (∀ w, (mat u).map (piInf (B.emb w)) = 1) → om (u, 1) Φ = Φ := by
  induction hΦ using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨U, hU, h⟩ := _root_.UpperTheory.exists_nhds_one_weil_fixes_pure_tensor F E σ B n d X W M χX χW om r s r' s' hp g hg
    exact mem_of_superset hU fun u hu k => h u hu k f
  | zero => exact Eventually.of_forall fun _ _ => map_zero _
  | add x y _ _ hx hy => filter_upwards [hx, hy] with u h1 h2 k using by rw [map_add (f := _), h1 k, h2 k]
  | smul a x _ hx => filter_upwards [hx] with u h1 k using by rw [map_smul, h1 k]
theorem polStab_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) (x : UA σ X.J) (y : UA σ W.J) :
    ∀ Φ ∈ PolData B M, om (x, y) Φ ∈ PolData B M := by
  have hsch : ∀ Φ ∈ PolData B M, Φ ∈ schA F (Fin n × Fin d) := fun Φ h => PositivityTheory.ThKG.polData_le hp.good h
  have o1 : ∀ {m : ℕ} {v : Pl F} (Y : Spc F E m), (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun Y => PositivityTheory.ThKH.Locrep.one_mem_UAt (σ := σ) Y _
  have o2 : ∀ {m : ℕ} (Y : Spc F E m), (1 : UA σ Y.J) ∈ UAt σ Y (evI F) := fun Y u _ => by
    rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]
  have e : ((x, y) : UA σ X.J × UA σ W.J) = (x, 1) * (1, y) := by simp
  intro Φ hΦ
  rw [e, map_mul, Module.End.mul_apply]
  refine stab_of_pk B.emb (om.comp (MonoidHom.inl _ _)) _ (fun Φ h => _root_.UpperTheory.TP.levelX_sch_k hp (hsch Φ h))
    (fun g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_archimedean F E σ B n d X W M χX χW om hp g hg 1 (o2 W) Φ h)
    (fun v g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_finite_place T F E σ B n d X W M χX χW om _ _ _ _ hp v g hg 1 (o1 W) Φ h) x _ ?_
  exact stab_of_pk B.emb (om.comp (MonoidHom.inr _ _)) _
    (fun Φ h => _root_.PositivityTheory.ThKEnd.Grp.level_sch_k _root_.PositivityTheory.ThKEst.level_k hp (hsch Φ h))
    (fun g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_archimedean F E σ B n d X W M χX χW om hp 1 (o2 X) g hg Φ h)
    (fun v g hg Φ h => _root_.UpperTheory.weilRep_mem_polynomialFock_of_finite_place T F E σ B n d X W M χX χW om _ _ _ _ hp v 1 (o1 X) g hg Φ h) y _ hΦ
theorem lift_left_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (φ : UA σ X.J → ℂ) {γ : UA σ W.J} (hγ : γ ∈ ratU σ W.J) (h : UA σ W.J) : lift M om Φ φ (γ * h) = lift M om Φ φ h := by
  refine integral_congr_ae (.of_forall fun g => ?_)
  have := (T.basic F E σ B n d X W M χX χW om n 0 d 0 hp).1 Φ hΦ
  have h2 := this.2.1 1 (one_mem _) γ hγ g h
  rw [one_mul] at h2
  show theta om Φ g (γ * h) * star (φ g) = theta om Φ g h * star (φ g)
  rw [h2]
private theorem real_of_off_pk {τ : ∀ w : InfinitePlace F, EmbOver E w} {g : UA σ W.J} (hg : g ∈ gOff σ W ∅) (w : InfinitePlace F) :
    (mat g).map (piInf (τ w)) = 1 := by
  have h : ∀ w, (mat g).map (compInf F E w) = 1 := by
    refine Subgroup.closure_induction (k := {g : UA σ W.J | (∀ w : InfinitePlace F, (mat g).map (compInf F E w) = 1) ∧ ∀ v ∈ (∅ : Finset (Pl F)), OffAt v g}) (p := fun g _ => ∀ w, (mat g).map (compInf F E w) = 1) (fun x hx => hx.1) ?_ ?_ ?_ hg
    · intro w; exact Matrix.map_one _ (map_zero _) (map_one _)
    · intro x y _ _ hx hy w
      rw [show mat (x * y) = mat x * mat y from rfl, Matrix.map_mul, hx, hy, one_mul]
    · intro x _ hx w
      have e : mat x⁻¹ * mat x = 1 := PositivityTheory.ThKEnd.Grp.mat_inv_mul x
      have := congrArg (fun A => A.map (compInf F E w)) e
      simp only [Matrix.map_mul, hx w, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at this
      exact this
  have e : (mat g).map (piInf (τ w)) = ((mat g).map (compInf F E w)).map (infEmb (τ w)) := by ext i j; rfl
  rw [e, h, Matrix.map_one _ (map_zero _) (map_one _)]
end Gen
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n}
  {W : Spc (maximalRealSubfield E) E d} {B : Base (maximalRealSubfield E) E} {M : Model (cj E) X W}
  {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
theorem RU_lift_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
    {Φ : Fn (maximalRealSubfield E) n d} (hΦ : Φ ∈ schA (maximalRealSubfield E) (Fin n × Fin d)) {ψ : UA (cj E) X.J → ℂ} (hψ : IsFn ψ)
    (k : GlobalTheory.UnitaryBC.UA E d) :
    GlobalTheory.UnitaryBC.RU E d k (lift M om Φ ψ ∘ e') = lift M om (om (1, e' k) Φ) ψ ∘ e' := by
  funext h
  have := _root_.UpperTheory.thetaLift_weil_translate_equivariant T _ E (cj E) B n d X W M χX χW om hp Φ hΦ ψ hψ 1 (e' k) (e' h)
  simp only [mul_one] at this
  exact (congrArg (lift M om Φ ψ) (map_mul e' h k)).trans this.symm
theorem aut_lift_k (T : _root_.UpperTheory.TP.Tools_k) (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J} (he' : IsBr W e')
    {Φ : Fn (maximalRealSubfield E) n d} (hΦ : Φ ∈ PolData B M) {ψ : UA (cj E) X.J → ℂ} (hψ : IsFn ψ) :
    GlobalTheory.UnitaryBC.IsAutFormU (lift M om Φ ψ ∘ e') := by
  have hs : Φ ∈ schA (maximalRealSubfield E) (Fin n × Fin d) := PositivityTheory.ThKG.polData_le hp.good hΦ
  refine ⟨(_root_.UpperTheory.continuous_thetaLift_of_definite T _ E (cj E) B n d X W M χX χW om hp Φ hs ψ hψ).comp e'.continuous, fun γ hγ g => ?_, ?_, ?_⟩
  · show lift M om Φ ψ (e' (γ * g)) = lift M om Φ ψ (e' g)
    rw [map_mul]
    exact _root_.UpperTheory.TP.lift_left_k T hp hs ψ ((he'.rat γ).2 hγ) _
  · let f := lift M om Φ ψ ∘ e'
    let H : Subgroup (GlobalTheory.UnitaryBC.finU (E := E) (n := d)) :=
      { carrier := {k | GlobalTheory.UnitaryBC.RU E d k f = f}
        one_mem' := by show GlobalTheory.UnitaryBC.RU E d 1 f = f; rw [map_one]; rfl
        mul_mem' := fun {a b} ha hb => by
          show GlobalTheory.UnitaryBC.RU E d (a.1 * b.1) f = f
          rw [map_mul, Module.End.mul_apply, show GlobalTheory.UnitaryBC.RU E d b.1 f = f from hb]; exact ha
        inv_mem' := fun {a} ha => by
          show GlobalTheory.UnitaryBC.RU E d (a.1⁻¹) f = f
          have : GlobalTheory.UnitaryBC.RU E d a.1 f = f := ha
          conv_lhs => rw [← this]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl }
    refine Subgroup.isOpen_of_mem_nhds H (g := 1) ?_
    have h1 := _root_.PositivityTheory.ThKEnd.Grp.level_sch_k _root_.PositivityTheory.ThKEst.level_k hp hs
    have c : Tendsto (fun k : GlobalTheory.UnitaryBC.finU (E := E) (n := d) => e' k.1) (𝓝 1) (𝓝 1) :=
      (e'.continuous.comp continuous_subtype_val).tendsto' _ _ (map_one e')
    filter_upwards [c.eventually h1] with k hk
    show GlobalTheory.UnitaryBC.RU E d k.1 f = f
    rw [_root_.UpperTheory.TP.RU_lift_k T hp hs hψ, hk fun w => real_of_off_pk ((he'.fin k.1).2 k.2) w]
  · obtain ⟨V, hV, hVs, hk⟩ := _root_.UpperTheory.exists_finiteDimensional_weil_archimedean_orbit _ E (cj E) B n d X W M χX χW om hp Φ hΦ
    obtain ⟨l1, l2, -, -⟩ := _root_.UpperTheory.thetaLift_linear_in_schwartz T _ E (cj E) B n d X W M χX χW om hp
    let L : V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
      { toFun := fun x => lift M om x.1 ψ ∘ e'
        map_add' := fun x y => by
          funext h
          exact congrFun (l1 x.1 (hVs x.2) y.1 (hVs y.2) ψ hψ) (e' h)
        map_smul' := fun c x => by
          funext h
          exact congrFun (l2 c x.1 (hVs x.2) ψ hψ) (e' h) }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨⟨_, hk _ ((he'.inf k.1).2 k.2)⟩, (_root_.UpperTheory.TP.RU_lift_k T hp hs hψ k.1).symm⟩
end CM
theorem _root_.UpperTheory.TP.liftAut_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.LiftAut_k := by
  intro T E _ _ _ B n d X W M χX χW om hP hn e e' he he'
  classical
  let C : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ GlobalTheory.UnitaryBC.ratU E n, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp only [Pi.add_apply, ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp only [Pi.smul_apply, ha.2 γ hγ g]⟩ }
  obtain ⟨C', hC'⟩ := Submodule.exists_isCompl C
  let Pj : (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) := C.subtype ∘ₗ C.linearProjOfIsCompl C' hC'
  have p1 : ∀ φ, Pj φ ∈ C := fun φ => (C.linearProjOfIsCompl C' hC' φ).2
  have p2 : ∀ φ ∈ C, Pj φ = φ := fun φ h => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC' ⟨φ, h⟩)
  have fn : ∀ φ ∈ C, IsFn (φ ∘ e.symm) := fun φ h => ⟨h.1.comp e.symm.continuous, fun γ hγ g => by
    show φ (e.symm (γ * g)) = φ (e.symm g)
    rw [map_mul]
    exact h.2 _ ((he.rat _).1 (by simpa using hγ)) _⟩
  have sch : ∀ Φ : PolData B M, Φ.1 ∈ schA (maximalRealSubfield E) (Fin n × Fin d) := fun Φ => PositivityTheory.ThKG.polData_le hP.good Φ.2
  obtain ⟨l1, l2, l3, l4⟩ := _root_.UpperTheory.thetaLift_linear_in_schwartz T _ E (cj E) B n d X W M χX χW om hP
  let Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun Φ ψ => lift M om Φ.1 (Pj ψ ∘ e.symm) ∘ e')
      (fun Φ Φ' ψ => funext fun h => congrFun (l1 Φ.1 (sch Φ) Φ'.1 (sch Φ') _ (fn _ (p1 ψ))) (e' h))
      (fun c Φ ψ => funext fun h => congrFun (l2 c Φ.1 (sch Φ) _ (fn _ (p1 ψ))) (e' h))
      (fun Φ ψ ψ' => funext fun h => by
        have := congrFun (l3 Φ.1 (sch Φ) _ _ (fn _ (p1 ψ)) (fn _ (p1 ψ'))) (e' h)
        refine Eq.trans ?_ this
        show lift M om Φ.1 (Pj (ψ + ψ') ∘ e.symm) (e' h) = _
        rw [map_add (f := _)]
        rfl)
      (fun c Φ ψ => funext fun h => by
        have := congrFun (l4 c Φ.1 (sch Φ) _ (fn _ (p1 ψ))) (e' h)
        refine Eq.trans ?_ this
        show lift M om Φ.1 (Pj (c • ψ) ∘ e.symm) (e' h) = _
        rw [map_smul]
        rfl)
  have q : ∀ (Φ₀ : PolData B M) (φ₀ : GlobalTheory.UnitaryBC.UA E n → ℂ), φ₀ ∈ C → Θ Φ₀ φ₀ = lift M om Φ₀.1 (φ₀ ∘ e.symm) ∘ e' :=
    fun Φ₀ φ₀ h => by
      show lift M om Φ₀.1 (Pj φ₀ ∘ e.symm) ∘ e' = _
      rw [p2 _ h]
  refine ⟨Θ, fun Φ φ hφ => ?_⟩
  have hφC : φ ∈ C := ⟨hφ.cont, hφ.left⟩
  refine ⟨q Φ φ hφC, by rw [q _ _ hφC]; exact _root_.UpperTheory.TP.aut_lift_k T hP he' Φ.2 (fn φ hφC), fun g h => ?_⟩
  have hm := _root_.UpperTheory.TP.polStab_k T hP (e g) (e' h) Φ.1 Φ.2
  refine ⟨⟨_, hm⟩, rfl, ?_⟩
  have hRC : GlobalTheory.UnitaryBC.RU E n g φ ∈ C :=
    ⟨hφ.cont.comp (continuous_mul_const g), fun γ hγ x => by
      show φ (γ * x * g) = φ (x * g)
      rw [mul_assoc]
      exact hφ.left γ hγ _⟩
  rw [q _ _ hRC, q _ _ hφC]
  funext h₀
  have := _root_.UpperTheory.thetaLift_weil_translate_equivariant T _ E (cj E) B n d X W M χX χW om hP Φ.1 (sch Φ) (φ ∘ e.symm) (fn φ hφC) (e g) (e' h) (e' h₀)
  have e1 : GlobalTheory.UnitaryBC.RU E n g φ ∘ e.symm = fun y => (φ ∘ e.symm) (y * e g) := by
    funext y
    show φ (e.symm y * g) = φ (e.symm (y * e g))
    rw [map_mul, e.symm_apply_apply]
  rw [e1]
  refine this.trans ?_
  show lift M om Φ.1 (φ ∘ e.symm) (e' h₀ * e' h) = lift M om Φ.1 (φ ∘ e.symm) (e' (h₀ * h))
  rw [map_mul]
end UpperTheory.TP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRealPair
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP
private theorem rightSub_one_pk {n d : ℕ} : (rightSub 1 : PP n d →ₐ[ℂ] PP n d) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun l => ?_
  rcases l with ⟨b | b, c | c⟩
  · simp [rightSub, xv, Matrix.one_apply]
  · exact c.elim0
  · exact b.elim0
  · exact b.elim0
private theorem polyAction_one {n d : ℕ} (c : ℤ) : (act2 c (1 : GL (Fin d) ℂ) : Module.End ℂ (PP n d)) = 1 := by
  refine LinearMap.ext fun f => ?_
  simp [act2, detPow, rightSub_one_pk]
theorem UpperTheory.TP.realPair_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.RealPair_k := by
  intro T E _ _ _ B n d X W M χX χW om hP hn e e' he he' hnd δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨Φ, a, b, hinj, hran, ha, hb, h1, h2⟩ :=
    _root_.UpperTheory.TP.RP.fockOf_k T E B n d X W M χX χW om hP hn hnd e e' he he' δ mX mW hXJ hWJ eX eW
  have hμ : ∀ w, ∃ μ : Fin n → ℕ, ∀ k, (μ k : ℤ) + a w = (lam w).w k := fun w =>
    ⟨fun k => ((lam w).w k - a w).toNat, fun k => by
      have h3 := hdom w k
      have h4 := ha w
      rw [Int.toNat_of_nonneg (by omega)]
      omega⟩
  choose μ hμ using hμ
  have hanti : ∀ w, Antitone (μ w) := fun w i j hij => by
    have h3 := (lam w).anti hij
    have h4 := hμ w i
    have h5 := hμ w j
    omega
  choose i₁ hi₁ x₁ hx₁ using fun w => exists_act1_equivariant_nablaSq_map_hitting_joint hnd (lam w) (a w) (μ w) (hμ w)
  obtain ⟨ρ, j, hfd, hirr, hρ, hjinj, hjU, hj⟩ :=
    formEx E n hn _ (fun w => (B.emb w).1) (embBij E B) lam U hU hwt
  let J : ∀ _ : InfinitePlace (maximalRealSubfield E), PP n d := fun w => joint hnd (μ w)
  have hJ : ∀ w, J w ≠ 0 := fun w => jointNe hnd (μ w) (hanti w)
  have hx0 : ∀ w, x₁ w ≠ 0 := fun w h => hJ w (by show joint hnd (μ w) = 0; rw [← hx₁ w, h, map_zero])
  let T₀ : Tens (maximalRealSubfield E) n 0 d 0 := PiTensorProduct.tprod ℂ J
  have hT₀ : T₀ ≠ 0 := tprodNe J hJ
  let iV : (⨂[ℂ] w, nablaSq ℂ n (lam w)) →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0 := PiTensorProduct.map i₁
  have hiV : iV (PiTensorProduct.tprod ℂ x₁) = T₀ := by
    simp only [iV, T₀, PiTensorProduct.map_tprod, hx₁, J]
  have hmem : ∀ T, Φ T ∈ M.Pol B.ψ B.emb := fun T => hran ▸ LinearMap.mem_range_self Φ T
  have hS : UpperTheory.TP.SameType om e U (Φ T₀) (j (PiTensorProduct.tprod ℂ x₁)) := by
    refine ⟨_, _, _, hfd, ρ, Φ ∘ₗ iV, j, PiTensorProduct.tprod ℂ x₁, hirr, ?_, rfl, hjU, fun k x => ?_, hj⟩
    · simp only [LinearMap.comp_apply, hiV]
    · have e1 : PiTensorProduct.map (fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) (iV x) =
          iV (ρ k x) := by
        rw [hρ k]
        have e2 : (PiTensorProduct.map fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) ∘ₗ iV =
            iV ∘ₗ PiTensorProduct.map fun w => GlobalTheory.Branching.sqRep ℂ n (lam w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) := by
          simp only [iV, ← PiTensorProduct.map_comp]
          congr 1
          funext w
          exact LinearMap.ext fun y => (hi₁ w _ y).symm
        exact LinearMap.congr_fun e2 x
      have := h1 k.1 k.2 (iV x)
      rw [e1] at this
      exact this
  refine ⟨Φ T₀, hmem _, fun h => hT₀ (hinj (h.trans (map_zero Φ).symm)), j (PiTensorProduct.tprod ℂ x₁), hjU _,
    fun h => tprodNe x₁ hx0 (hjinj (h.trans (map_zero j).symm)), hS, fun w => ?_⟩
  let lam' : DomWeight d := ⟨fun k => (if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w, fun p q hpq => by
    have hle : (p : ℕ) ≤ q := hpq
    dsimp only
    by_cases h3 : (q : ℕ) < n
    · have h4 : (p : ℕ) < n := by omega
      rw [dite_eq_left h3, dite_eq_left h4]
      have := hanti w (show (⟨p, h4⟩ : Fin n) ≤ ⟨q, h3⟩ from hle)
      omega
    · rw [dite_eq_right h3]
      split_ifs <;> omega⟩
  refine ⟨lam', fun k => ?_, GlobalTheory.DefU.isIrreducible_sqRep d lam', ?_⟩
  · have h3 := ha w
    have h4 := hb w
    show 2 * ((if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w) = _
    split_ifs with hk
    · have h5 := hμ w ⟨k, hk⟩
      omega
    · omega
  obtain ⟨i₂, hi₂, x₂, hx₂⟩ := exists_act2_equivariant_nablaSq_map_hitting_joint hnd lam' (b w) (μ w) (fun k => rfl)
  let up : PP n d →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0 := (PiTensorProduct.tprod ℂ).toLinearMap J w
  have hup : ∀ y, up y = PiTensorProduct.tprod ℂ (Function.update J w y) := fun y => rfl
  refine ⟨Φ ∘ₗ up ∘ₗ i₂, fun x => hmem _, ⟨x₂, ?_⟩, fun k hk x => ?_⟩
  · simp only [LinearMap.comp_apply, hx₂, hup]
    congr 2
    exact Function.update_eq_self_iff.2 rfl
  · have e1 : PiTensorProduct.map (fun w' => (act2 (b w') (GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k) : Module.End ℂ (PP n d))) (up (i₂ x)) =
        up (i₂ (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) x)) := by
      rw [hi₂, hup, hup, PiTensorProduct.map_tprod]
      congr 1
      funext w'
      by_cases hw' : w' = w
      · subst hw'
        simp
      · rw [Function.update_of_ne hw', Function.update_of_ne hw']
        have h3 := (Subgroup.mem_inf.1 hk).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 (B.emb w').1
        rw [Subgroup.mem_iInf] at h4
        have h5 : GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k = 1 := h4 fun h6 => hw' ((embBij E B).1 h6)
        rw [h5, polyAction_one]
        rfl
    have := h2 k (Subgroup.mem_inf.1 hk).1 (up (i₂ x))
    rw [e1] at this
    exact this
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WeilRepresentationHermitianPair
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_hermitian_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∃ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om := by
  first | exact @_root_.GlobalTheory.TransportF.exists_isTransportF_k | exact _root_.GlobalTheory.TransportF.exists_isTransportF_k | (intros; apply _root_.GlobalTheory.TransportF.exists_isTransportF_k <;> assumption)
end
end

