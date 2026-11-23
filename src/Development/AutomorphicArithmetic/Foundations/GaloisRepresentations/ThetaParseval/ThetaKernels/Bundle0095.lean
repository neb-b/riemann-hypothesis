module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContSingle
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0053
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0089
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0066
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0094
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0072
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0050
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0086
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0073
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0078
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfo
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0016
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0074
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0052

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CLawExK
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Act
def CLawEx_k : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d),
  ∃ (w₁ : d.G) (cM : (Fin L.n → AE F E) × AF F → d.G) (κ : Measure ((Fin L.n → AE F E) × AF F)),
    _root_.PositivityTheory.SiegelWeilFormula.Act.CLaw_k R L w₁ cM κ ∧ w₁ ∈ rat2 σ d.Y ∧
    (∃ a b : E, a ≠ 0 ∧ b ≠ 0 ∧ inFrame d.b w₁ = 1 - Matrix.single (Sum.inl L.i₀) (Sum.inl L.i₀) 1 -
      Matrix.single (Sum.inr L.i₀) (Sum.inr L.i₀) 1 + Matrix.single (Sum.inl L.i₀) (Sum.inr L.i₀) (inclR (F := F) (AF F) a) +
      Matrix.single (Sum.inr L.i₀) (Sum.inl L.i₀) (inclR (F := F) (AF F) b)) ∧
    Continuous cM ∧ κ.IsAddHaarMeasure ∧
    ∃ δ : E, δ ≠ 0 ∧ ∀ c, ∃ A', inFrame d.b (cM c) = Matrix.fromBlocks (1 + ∑ j, Matrix.single L.i₀ (L.em j) (c.1 j))
      (Matrix.single L.i₀ L.i₀ (c.2 • inclR (F := F) (AF F) δ)) 0 A'
theorem cLawEx_k : _root_.PositivityTheory.SiegelWeilFormula.Act.CLawEx_k := by
  intro F E _ _ _ _ _ σ d R L
  have hε := R.hε
  have hem : ∀ j, L.em j ≠ L.i₀ := fun j => (L.rng (L.em j)).2 ⟨j, rfl⟩
  set e : AE F E := ((R.ε : ℤ) : AE F E) with he_def
  have hee : e * e = 1 := by
    rw [he_def, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  obtain ⟨δ, hδ0, hδ⟩ := CL.deltaEx' d.cm R.ε
  obtain ⟨κ, hκ, hsc⟩ := CL.measEx' (F := F) (E := E) L.n d.bs
  let M₀ : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ (1 : E) ((R.ε : ℤ) : E)
  let M₀' : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := CL.wM L.i₀ ((R.ε : ℤ) : E) (1 : E)
  have hW : incM F M₀ = CL.wM L.i₀ (1 : AE F E) e := by
    show M₀.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hW' : incM F M₀' = CL.wM L.i₀ e (1 : AE F E) := by
    show M₀'.map _ = _
    rw [CL.wM_map, map_one, map_intCast]
  have hWW : incM F M₀ * incM F M₀' = 1 := by
    rw [hW, hW']; exact CL.wM_mul L.i₀ _ _ _ _ (one_mul 1) hee
  have hWu : (incM F M₀)ᵀ * kunf.jw d.n e * (incM F M₀).map (cA σ) = kunf.jw d.n e := by
    rw [hW]
    refine CL.wM_unitary L.i₀ (cA σ).toRingHom 1 e e ?_ ?_
    · simp only [AlgHom.toRingHom_eq_coe, map_one, mul_one, hee]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, he_def, map_intCast, one_mul]
  obtain ⟨w₁, hw₁⟩ := kunf.exists_of_frame hε (incM F M₀) (incM F M₀') hWW hWu
  have hw₁' : inFrame d.b w₁ = CL.wM L.i₀ (1 : AE F E) e := hw₁.trans hW
  set δ' : AE F E := inclR (F := F) (AF F) δ with hδ'
  let Mc : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em c.1 (fun j => cA σ (c.1 j)) (c.2 • δ')
  let Mc' : (Fin L.n → AE F E) × AF F → Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := fun c =>
    CL.cB L.i₀ L.em (-c.1) (-fun j => cA σ (c.1 j)) (-(c.2 • δ'))
  have hcont : ∀ s : AF F → AF F, Continuous s → ∀ t : (Fin L.n → AE F E) → (Fin L.n → AE F E), Continuous t →
      Continuous fun c : (Fin L.n → AE F E) × AF F =>
        CL.cB L.i₀ L.em (t c.1) (fun j => cA σ (t c.1 j)) (s c.2 • δ') := by
    intro s hs t ht
    refine Continuous.matrix_fromBlocks ?_ ?_ continuous_const ?_
    · exact continuous_const.add (continuous_finsetSum _ fun j _ =>
        cont_single _ _ ((continuous_apply j).comp (ht.comp continuous_fst)))
    · exact cont_single _ _ (Continuous.smul (f := fun c : (Fin L.n → AE F E) × AF F => s c.2) (g := fun _ => δ')
        (hs.comp continuous_snd) continuous_const)
    · exact continuous_const.sub (continuous_finsetSum _ fun j _ => cont_single _ _
        ((GlobalTheory.EisBL.DoubledGroupTopology.continuous_cA σ).comp ((continuous_apply j).comp (ht.comp continuous_fst))))
  have hMc : Continuous Mc := hcont id continuous_id id continuous_id
  have hMc' : Continuous Mc' := by
    have := hcont (fun a => -a) continuous_neg (fun u => -u) continuous_neg
    convert this using 2 with c
    simp only [Mc', neg_smul, Pi.neg_apply, map_neg]
    rfl
  have cA_inclR (x : E) : cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ ((1 : AF F) ⊗ₜ[F] x) = (1 : AF F) ⊗ₜ[F] σ x
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have cA_invol (z : AE F E) : cA σ (cA σ z) = z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ
        (Algebra.TensorProduct.map (AlgHom.id (AF F) (AF F)) σ (a ⊗ₜ[F] x)) = a ⊗ₜ[F] x
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, CL.sigma_sigma_cm d.cm]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hcA_z : ∀ a : AF F, cA σ (a • δ') = -(e * (a • δ')) := by
    intro a
    rw [map_smul, hδ', cA_inclR δ, hδ, map_neg, map_mul, map_intCast, smul_neg, mul_smul_comm]
  obtain ⟨cM, hcMc, hcM⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.ptEx'_k d hε Mc Mc' hMc hMc'
    (fun c => CL.cB_mul hem c.1 _ _) (fun c => CL.cB_unitary hem (cA σ).toRingHom
      cA_invol e hee c.1 (c.2 • δ') (hcA_z c.2))
  have hfr := fun x y => GlobalTheory.EisBL.DoubledParabolic.inFrame_mul (σ := σ) (Y := d.Y) d.b x y
  refine ⟨w₁, cM, κ, ⟨?_, ?_, ?_⟩, kunf.rat_of_inFrame hw₁, ⟨1, (R.ε : ℤ), one_ne_zero, ?_, ?_⟩, hcMc, hκ,
    ⟨δ, hδ0, fun c => ⟨_, hcM c⟩⟩⟩
  ·
    intro w τ y g hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
    exact CL.comm_dM L.i₀ _ (L.j_out g) _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, -, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    have hy' := CL.isDil_inv hy
    obtain ⟨t, ht, ha, hχ⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.par_dil_k d R w L.i₀ hy'
    refine ⟨R.ι w y⁻¹, t, ht, by rw [ha]; ring_nf, hχ, ?_⟩
    apply kunf.inFrame_injective d.b
    rw [hfr, hfr, hw₁', _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy', neg_neg]
    exact CL.wM_dM L.i₀ _ _ _ _
  ·
    intro w τ y hy
    obtain ⟨r, hr0, hr1, hrm, hrw, hro, hrf⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.CL.rEx_k d w
    obtain ⟨sc, hsc1, hsc2⟩ := hsc (r (-τ))
    refine ⟨sc, fun c => ?_, ?_⟩
    · apply kunf.inFrame_injective d.b
      rw [hfr, hfr, hcM, hcM, _root_.PositivityTheory.SiegelWeilFormula.Act.CL.frame_dil_k d R w r hrw hro hrf L.i₀ hy]
      have hxy : ((r τ : AF F) • (1 : AE F E)) * ((r (-τ) : AF F) • (1 : AE F E)) = 1 := by
        rw [smul_mul_smul_comm, one_mul, ← Units.val_mul, ← hr0, add_neg_cancel, hr1]; simp
      rw [CL.cB_dM hem _ _ _ _ _ hxy, hsc1]
      congr 1
      simp only [Mc]
      congr 1
      · funext j; exact smul_one_mul _ _
      · funext j; rw [map_smul, smul_one_mul]
      · rw [mul_assoc, smul_one_mul, smul_one_mul, smul_assoc, mul_smul]
    · rw [hsc2, hrm, ← Real.exp_neg, neg_neg, ← Real.exp_nat_mul, ← _root_.PositivityTheory.SiegelWeilFormula.Atop.LD.n_succ_k L]
      congr 2
      push_cast; ring
  · simp [map_intCast]
  · rw [hw₁']; simp [CL.wM, map_intCast, map_one, he_def]
end PositivityTheory.SiegelWeilFormula.Act
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ContinuousThK
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
theorem continuous_th'_k (T' : nF σ L.Y L.b) : Continuous fun β : nA σ L.Y L.b => _root_.PositivityTheory.SiegelWeilFormula.Act.C5.th'_k (d := d) T' β :=
  kfour.continuous_chr (σ := σ) (Y := L.Y) (b := L.b) d.ok.good.std.1 T'.1.1
theorem countable_crat_k : Countable (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) := by
  have : Countable L.ratV := by
    have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
    refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
      (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
    obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
    exact ⟨v, Subtype.ext hv.symm⟩
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (Set.range (algebraMap F (AF F))) := (Set.countable_range _).to_subtype
  refine Function.Injective.countable (f := fun c : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L =>
    ((⟨c.1.1, c.2.1⟩ : L.ratV), (⟨c.1.2, c.2.2⟩ : Set.range (algebraMap F (AF F)))))
    fun c c' hcc => ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq] at hcc
  exact Subtype.ext (Prod.ext hcc.1 (congrArg Subtype.val hcc.2))
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.CountableRationalVectors
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
set_option linter.style.haveILetI false
def rationalCosetEquiv (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L ≃ L.ratV × fA F where
  toFun c := (⟨c.1.1, c.2.1⟩, ⟨c.1.2, c.2.2⟩)
  invFun c := ⟨((c.1 : Fin L.n → AE F E), (c.2 : AF F)), c.1.2, c.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem countable_rational_vectors (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : Countable L.ratV := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  refine Function.Surjective.countable (f := fun v : Fin L.n → E =>
    (⟨GlobalTheory.ThK.incV F v, AddSubgroup.subset_closure ⟨v, rfl⟩⟩ : L.ratV)) fun u => ?_
  obtain ⟨v, hv⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C1.ratV_inc_k u.2
  exact ⟨v, Subtype.ext hv.symm⟩
theorem coset_point_decomposition (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) {γ' : G2 σ L.Y}
    {Λ : ((Fin L.n → AE F E) × (Fin L.n → AE F E)) ≃ₜ+ ((Fin L.n → AE F E) × (Fin L.n → AE F E))}
    {Q : (Fin L.n → AE F E) × (Fin L.n → AE F E) → AF F}
    (hΛ : ∀ b u a, L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM ((Λ (b, u)).2, a + Q (b, u)) * L.j γ')
    {Z : (Fin L.n → AE F E) → (Fin L.n → AE F E) → AF F}
    (hZ : ∀ u₀ a₀ b u a, cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a)) = _root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u₀ + u, a₀ + a + Z u₀ b))
    (Y : d.G) (c₀ : (Fin L.n → AE F E) × AF F) (p : (Fin L.n → AE F E) × ((Fin L.n → AE F E) × AF F)) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀ * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y))))) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM (UnfoldingIntegralSum.sh Λ Q Z c₀ p) * (L.j γ' * Y))) := by
  obtain ⟨u₀, a₀⟩ := c₀
  obtain ⟨u, b, a⟩ := p
  have e1 : L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * (cM (u, a) * Y)) = (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L b * cM (u, a))) * Y := by simp only [mul_assoc]
  have e2 : ∀ c', cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM c' * L.j γ' * Y) =
      (cM (u₀, a₀) * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L (Λ (b, u)).1 * cM c')) * (L.j γ' * Y) := by intro c'; simp only [mul_assoc]
  rw [e1, hΛ, e2, hZ, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.section_unipotent_invariant h hf z]
  simp only [UnfoldingIntegralSum.sh, add_assoc]
theorem unfqE_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G) :
    ∫⁻ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y)))))‖ₑ
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫⁻ c, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  haveI := hν
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis_k (R := R) h
  have hg : Continuous fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_cM_k h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_lint hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable.enorm]
  refine lintegral_congr fun p => ?_
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coset_point_decomposition h hf z hΛeq hheis]; rfl
theorem unfqC_k (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {ν : Measure (Fin L.n → AE F E)} {𝓤 : Set (Fin L.n → AE F E)} (hU : L.UData uM ν 𝓤)
    {𝓐 : Set (AF F)} (h𝓐 : IsAddFundamentalDomain (fA F) 𝓐 (lamA F)) {γ' : G2 σ L.Y} (hγ : γ' ∈ rat2 σ L.Y) (Y : d.G)
    (hfin : ∫⁻ c, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y)))‖ₑ ∂(ν.prod (lamA F)) < ⊤) :
    ∫ p, ∑' c₀ : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c₀.1 * (L.j γ' * (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.sM_k R L p.2.1 * (cM (p.1, p.2.2) * Y)))))
        ∂((ν.restrict 𝓤).prod ((ν.restrict 𝓤).prod ((lamA F).restrict 𝓐))) =
      ∫ c, _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) ∂(ν.prod (lamA F)) := by
  obtain ⟨-, hν, hU0, hU1⟩ := hU
  haveI := hν
  haveI := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.countable_rational_vectors L
  obtain ⟨Λ, Q, hQ, hΛeq, hΛrat⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.j_conj_k (R := R) h γ'
  obtain ⟨Z, hZ, -, hheis⟩ := _root_.PositivityTheory.SiegelWeilFormula.Act.C5.heis_k (R := R) h
  have hg : Continuous fun c => _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM c * (L.j γ' * Y))) :=
    (_root_.PositivityTheory.SiegelWeilFormula.Act.ComplexParameterFamilyContinuity.continuous_phz_k d hf.cont s₁ z).comp (continuous_const.mul ((_root_.PositivityTheory.SiegelWeilFormula.Act.C5.continuous_cM_k h).mul continuous_const))
  rw [← UnfoldingIntegralSum.unf_int hU0 hU1 (fd_prod hU0 hU0) h𝓐 Λ (hΛrat hγ) hQ.measurable hZ.measurable hg.measurable hfin]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  beta_reduce
  rw [← (_root_.PositivityTheory.SiegelWeilFormula.Act.C5.rationalCosetEquiv L).symm.tsum_eq]
  exact tsum_congr fun c => by rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.coset_point_decomposition h hf z hΛeq hheis]; rfl
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSecondTermExpand
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
theorem eisenstein_second_term_expand (h : _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Hyp_k L nb uM nb' w₁ cM δ) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ)
    {e : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L) ≃ {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}}
    (he : ∀ x, ∃ p ∈ par2 σ d.Y, p ∈ rat2 σ d.Y ∧ _root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 = p * (w₁ * (cM x.2.1 * L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1)))) (g : d.G) :
    _root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm L (_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z) g = ∑' x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1) * g))) ∧
      ∑' q : {q : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k d // ¬ _root_.PositivityTheory.SiegelWeilFormula.Act.FirstOrbit L (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q)}, ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k q.1 * g)‖ₑ =
        ∑' x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L), ‖_root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1) * g)))‖ₑ := by
  have key : ∀ x : (Σ _ : _root_.PositivityTheory.SiegelWeilFormula.Act.Cs_k L.sd, _root_.PositivityTheory.SiegelWeilFormula.Act.C5.Crat_k L), _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k (e x).1 * g) =
      _root_.PositivityTheory.SiegelWeilFormula.Act.phz_k d f s₁ z (w₁ * (cM x.2.1 * (L.j (_root_.PositivityTheory.SiegelWeilFormula.Act.rep_k x.1) * g))) := fun x => by
    obtain ⟨p, hp, hr, hx⟩ := he x
    rw [hx, mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.Act.C4.phz_rat_k hf z hp hr, mul_assoc, mul_assoc]
  constructor
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Act.C5.eisensteinSecondTerm, ← e.tsum_eq]
    exact tsum_congr key
  · rw [← e.tsum_eq]
    exact tsum_congr fun x => by rw [key]
end PositivityTheory.SiegelWeilFormula.Act.C5
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.FundamentalDomainPlancherelGlobal
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.LagrangianIntegralFactorisation
open PositivityTheory.ThKW.ModulusFactorDefinition
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end PositivityTheory.ThKW.LagrangianIntegralFactorisation
end
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.LagrangianIntegralFactorisation in
theorem PositivityTheory.ThKW.fundamental_domain_plancherel_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∃ α : GL (Fin nT) (AF F ⊗[F] E) →* Circle, Continuous α ∧
        (∀ a : GL (Fin nT) E, α (Matrix.GeneralLinearGroup.map (incAF F E) a) = 1) ∧
        ∀ (h : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
          mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) = ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) * t.1 →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) (ωd (1, h) f) = (α t : ℂ) * ((((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AF F ⊗[F] E →* AF F) (Matrix.GeneralLinearGroup.det t)) : ℝ) ^ ((Fintype.card (Fin nS) : ℝ) / 2) : ℝ) : ℂ) * GlobalTheory.LagrTheta.lagrInt ν 𝓕 ((diagCols (Fin nT) : Matrix (Fin nT ⊕ Fin nT) (Fin nT) (AF F ⊗[F] E)).submatrix finSumFinEquiv.symm id) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd
  obtain ⟨m, hmc, hmC, hmr⟩ := _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.levi_k F E σ B hB nT JT hT
  obtain ⟨α, hαc, hαq, hlaw⟩ := core (V := WOF F E nS (nT + nT) → ℂ)
    (IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ)
    (fun a b f g hf hg => GlobalTheory.WeilPartsF.theta_add (GlobalTheory.WeilPartsF.theta_smul a hf) (GlobalTheory.WeilPartsF.theta_smul b hg))
    (ωd.comp (MonoidHom.inr _ _)) (fun h f hf => hωd.om_pres _ f hf)
    (GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT))
    (fun a b f g hf hg => lagrInt_lin ν 𝓕 f g a b
      (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 f hf) (PositivityTheory.ThKW.PhaseFourierInjectivity.integrable F E σ nS nT JS JT ξ₀ B.ψ ν 𝓕 hν h𝓕 g hg))
    (fun h t => mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) h * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1)
    (fun a b s u ha hb => by
      show mtF σ _ (a * b) * _ = _ * (s * u).1
      rw [mtF_mul, Matrix.mul_assoc, hb, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Units.val_mul])
    (fun a s ha => by
      show mtF σ _ a⁻¹ * _ = _ * (s⁻¹).1
      have e : dC (AF F ⊗[F] E) nT = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) := by
        rw [← ha, ← Matrix.mul_assoc, mtF_inv_mul, Matrix.one_mul]
      calc mtF σ _ a⁻¹ * dC (AF F ⊗[F] E) nT
          = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * (s.1 * (s⁻¹).1)) := by
            rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
        _ = mtF σ _ a⁻¹ * (dC (AF F ⊗[F] E) nT * s.1) * (s⁻¹).1 := by
            simp only [Matrix.mul_assoc]
        _ = dC (AF F ⊗[F] E) nT * (s⁻¹).1 := by rw [← e])
    (mfac F E nS) (mfac_one nS) (mfac_pos nS) (mfac_mul nS)
    (fun h t hr f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.norm_law_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd h t hr f hf)
    m hmc hmC
    (fun f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.cont_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd f hf)
    (GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) : Set _)
    (fun γ hγ t hr f hf => _root_.PositivityTheory.ThKW.PhaseFourierInjectivity.rat_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ₀ hσ ν 𝓕 hν h𝓕 χS ωd hωd γ hγ t hr f hf)
    (fun k hk => by
      obtain ⟨M, t, h1, h2⟩ := PositivityTheory.ThKW.PhaseFourierInjectivity.conj_pow F E σ nT JT hT k hk
      exact ⟨M, t, h1, fun n hn => h2 n (by rw [Units.val_one, Matrix.mul_one] at hn; exact hn)⟩)
  exact ⟨α, hαc, fun a => hαq _ (hmr a), fun h t hr f hf => hlaw h t hr f hf⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ModelExistsOfSmallness
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
theorem modelExists_of_smallness (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k :=
  _root_.PositivityTheory.SiegelWeilFormula.Ald.modelEx_wired_k _root_.PositivityTheory.SiegelWeilFormula.Ldexa.sDarb_k partCharInv _root_.PositivityTheory.SiegelWeilFormula.Ald.chartFacts_k hG hS
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

