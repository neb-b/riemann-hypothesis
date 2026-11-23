module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0029
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.SectionEqThetaZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldModelPf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem modelEx_of_k (hS : _root_.PositivityTheory.SiegelWeilFormula.Ald.SDarb_k) (hE : _root_.PositivityTheory.SiegelWeilFormula.Ald.SEv_k) (hB : _root_.PositivityTheory.SiegelWeilFormula.Ald.BigT_k) (hF : SliceFacts) (hO : OpBox) (hU : SubSplit)
    (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.Ald.SiegelSmall_k) (hA' : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k) : _root_.PositivityTheory.SiegelWeilFormula.Ald.ModelEx_k := by
  intro hT hA F E _ _ _ _ _ σ d n h Y b j hn hs hb hε hj
  obtain ⟨ε, e1, e2⟩ := hε
  have hψ : IsStd d.B.ψ := d.ok.good.std
  obtain ⟨dd0, had0, hr0⟩ := hS F E σ d.B d.bs d.m d.n d.A d.Y d.b ε d.r d.s d.ok.good d.ok.hm d.ok.hn d.ok.sign
    d.ok.frame e1
  obtain ⟨dd', had', hr'⟩ := hS F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2
  obtain ⟨hev, hkill, htheta⟩ := hE F E σ d.B d.bs d.m n d.A Y b ε d.r d.s d.ok.good d.ok.hm hn hs hb e2 dd' had'
  obtain ⟨S0, S0', C, hC0, hop, hTf⟩ := hB hT hA F E σ d dd0 had0 hr0
  obtain ⟨c1, c2, c3, c4, -⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  let dd1 := GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm
  let S1 := GlobalTheory.TowU.RealComp.reix (eK d.m h) ∘ₗ S0
  let S1' := S0' ∘ₗ GlobalTheory.TowU.RealComp.reix (eK d.m h).symm
  have hop1 : GlobalTheory.TowU.IsOp d.B.ψ (fun w => dd1.e (d.dd.e.symm w)) S1 S1' :=
    GlobalTheory.TowU.RealComp.isOp_comp hop.1 (GlobalTheory.TowU.RealComp.isOp_reix d.B.ψ (eK d.m h))
  have hT1 : ∀ Φ ∈ d.sch, ∀ X, d.T Φ X = C * S1 Φ (crdB d.bs X ∘ eK d.m h) := fun Φ hΦ X => by
    rw [hTf Φ hΦ X]
    simp only [S1, LinearMap.comp_apply, GlobalTheory.TowU.RealComp.reix_apply]
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  have hw := d.ok.dbl.weil
  obtain ⟨om1, hom1⟩ := projHom (G := d.G) (fun x => S1 ∘ₗ d.om x ∘ₗ S1')
    (fun x φ hφ => hop1.pres _ (hw.2.1.pres x _ (hop1.pres' φ hφ)))
    (fun φ hφ => by simp [hop1.right φ hφ])
    (fun x y φ hφ => by
      simp only [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
      rw [hop1.left _ (hw.2.1.pres y _ (hop1.pres' φ hφ))])
  have hsp1 : IsUSplitting (adeleClass F) d.B.ψ dd1 (actB (cA σ)) om1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop1 hom1 hw.2.1
  have hsr1 : SiegelRule (cA σ) (adeleClass F) d.B.ψ (-1) (incM F d.A.J) (dbl (incM F d.Y.J)) dd1 d.χ
      (diagCols (Fin d.n)) om1 :=
    GlobalTheory.TowU.siegelRule_of_isOp (fun w => by simp) hop1 hom1 hw.2.2
  obtain ⟨hsl1, hsl2, ⟨φ₀, hφ₀, hφ₀0, hφ₀n⟩, -⟩ := hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)
  have hbox := fun g => hO F d.B.ψ hψ _ _ _ _ dd1 d.G (actB (cA σ)) om1 hsp1.toIsSplitting c2 (j g) (c3 g) φ₀ hφ₀ hφ₀0
  let cg : G2 σ Y → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun g => slice0 _ _ ∘ₗ om1 (j g) ∘ₗ PositivityTheory.ThKF0.Chr.boxL _ φ₀
  have hbx : ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), boxFun φ' φ₀ ∈ schA F (K1 d.m n) := fun φ' hφ' =>
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' hφ' φ₀ hφ₀
  have hsl0 : ∀ φ' : (Fin d.m × Fin n × Fin 2 → AF F) → ℂ, slice0 _ _ (boxFun φ' φ₀) = φ' := fun φ' => by
    funext x
    simp [slice0, boxFun, hφ₀0]
  have hcg : ∀ g φ', cg g φ' = slice0 _ _ (om1 (j g) (boxFun φ' φ₀)) := fun g φ' => rfl
  have hboxc : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2),
      om1 (j g) (boxFun φ' φ₀) = boxFun (cg g φ') φ₀ := fun g φ' hφ' =>
    (hbox g).2 φ' hφ' φ₀ hφ₀
  obtain ⟨om', hom'⟩ := projHom cg
    (fun g φ' hφ' => hsl1 _ (hsp1.pres _ _ (hbx φ' hφ')))
    (fun φ' hφ' => by rw [hcg, map_one, map_one, Module.End.one_apply, hsl0])
    (fun g g' φ' hφ' => by
      rw [hcg, map_mul, map_mul, Module.End.mul_apply, hboxc g' φ' hφ', hcg g])
  have hboxom : ∀ g, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), om1 (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₀ :=
    fun g φ' hφ' => by rw [hom' g φ' hφ', hboxc g φ' hφ']
  have hsp' : IsUSplitting (adeleClass F) d.B.ψ dd' (actB (cA σ)) om' :=
    hU F d.B.ψ hψ _ _ _ _ _ _ dd1 dd' (emb h b d.b) c1 d.G (G2 σ Y) (actB (cA σ)) (actB (cA σ)) j hj.1 c4 om1 om' hsp1
      φ₀ hφ₀ hφ₀0 hφ₀n (fun g => ⟨φ₀, hφ₀, hφ₀0, fun _ _ => rfl, hboxom g⟩)
  have hsg' := hG F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' om1 hsp1.toIsSplitting hsr1 φ₀ hφ₀ hφ₀0 om'
    hboxom
  obtain ⟨S', hS'1, hS'2⟩ := hA' hT F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop1 hT1
  refine ⟨Fin d.m × Fin n × Fin 2, inferInstance, dd', om', S', ev0 _,
    ⟨hr', ⟨isLagr_diagCols _ _, hsp', hsg'⟩, hS'1, hev, hkill, hS'2, htheta⟩, ?_⟩
  intro Φ hΦ Φ' hΦ' hres g X hX
  have hS1Φ : S1 Φ ∈ schA F (K1 d.m n) := hop1.pres Φ hΦ
  have hsl : Φ' = C • slice0 _ _ (S1 Φ) := by
    funext x
    obtain ⟨X', rfl⟩ := crdB_surj d.bs x
    have e := hres (ext0 h X') (extend_zero_column h X')
    rw [extension_zero_sub, tof_adapted d.bs d.B.ψ had', hT1 Φ hΦ, crdB_eK h d.bs _ (extend_zero_column h X'), extension_zero_sub] at e
    rw [e]
    rfl
  rw [tof_adapted d.bs d.B.ψ had', hom' g Φ' hΦ', hT1 _ (hw.2.1.pres (j g) Φ hΦ), crdB_eK h d.bs X hX]
  have e1' : S1 (d.om (j g) Φ) = om1 (j g) (S1 Φ) := by
    rw [hom1 (j g) _ hS1Φ]
    simp only [LinearMap.comp_apply]
    rw [hop1.left Φ hΦ]
  rw [e1', show (Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 : K1 d.m n → AF F) =
    Sum.elim (crdB d.bs (X.submatrix id (em0 h))) 0 from rfl]
  have e2' := congrFun ((hbox g).1 (S1 Φ) hS1Φ) (crdB d.bs (X.submatrix id (em0 h)))
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk] at e2'
  rw [e2', hcg, hsl]
  simp only [slice0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]
  rfl
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCLawD
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem j_comm_dil_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (w : InfinitePlace F) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single L.i₀ 1) τ y) (g : L.sd.G) : L.j g * R.ι w y = R.ι w y * L.j g := by
  apply PositivityTheory.SiegelWeilFormula.kfour.inFrame_injective d.b
  rw [GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, _root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil_k R w L.i₀ τ y hy]
  ext u v
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hv : v ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
  · rw [((L.j_out g) v hv u).2, Matrix.one_apply]
    split_ifs with huv
    · subst huv; ring
    · simp
  · by_cases hu : u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n))
    · rw [((L.j_out g) u hu v).1, Matrix.one_apply]
      split_ifs with huv
      · subst huv; ring
      · simp
    · rw [dilV_off d.cm w L.i₀ τ u hu, dilV_off d.cm w L.i₀ τ v hv, one_mul, mul_one]
theorem l_eq_T_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Ψ : d.Fn) (hΨ : Ψ ∈ d.sch) : d.l Ψ = d.T Ψ 0 := by
  have h1 := d.ok.dbl.kill 0 Ψ hΨ
  have h2 : ∀ M : Matrix (Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * M = 0 :=
    fun M => Matrix.zero_mul M
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T
  rw [← h1]
  congr 2
  ext i j
  exact (congrFun (congrFun (Matrix.zero_mul (diagCols (Fin d.n))ᵀ) i) j).trans
    (congrFun (congrFun (Matrix.zero_mul (incM F d.b.1.toCols₂)ᵀ) i) j).symm
theorem inFrame_dil'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) :
    inFrame d.b (R.ι w y) = Matrix.fromBlocks (dilT d.cm w i₀ τ).1 0 0 (dilT d.cm w i₀ (-τ)).1 := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil_k R w i₀ τ y hy]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal_apply, dilT, dilV]
theorem constantTerm_dilation (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (i₀ : Fin d.n) (τ : ℝ) (y : GR d.n)
    (hy : IsDil (Pi.single i₀ 1) τ y) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (h : d.G) :
    d.sec0 Φ (R.ι w y * h) = Complex.exp (τ * d.m) * d.sec0 Φ h := by
  haveI := d.cm.1
  have hpres : ∀ x, ∀ Ψ ∈ d.sch, d.om x Ψ ∈ d.sch := d.ok.dbl.weil.2.1.pres
  have hΨ := hpres h Φ hΦ
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.sec0
  rw [map_mul, Module.End.mul_apply, _root_.PositivityTheory.SiegelWeilFormula.AStep.l_eq_T_k d _ (hpres _ _ hΨ), _root_.PositivityTheory.SiegelWeilFormula.AStep.l_eq_T_k d _ hΨ,
    ((H.tAll.2.1 F E σ d _ hΨ).2.1 (R.ι w y) (dilT d.cm w i₀ τ) (dilT d.cm w i₀ (-τ)) (_root_.PositivityTheory.SiegelWeilFormula.AStep.inFrame_dil'_k R w i₀ τ y hy) 0),
    det_dilT, _root_.PositivityTheory.SiegelWeilFormula.AStep.chi_adrU_k d w τ, absE_adrU d.cm w τ]
  have hz : ∀ M : Matrix (Fin d.n) (Fin d.n) (AE F E), d.T (d.om h Φ) ((0 : Mx F E d.m d.n) * M) = d.T (d.om h Φ) 0 :=
    fun M => congrArg _ (Matrix.zero_mul M)
  rw [hz, ← Real.exp_mul, Complex.ofReal_exp, one_mul]
  congr 2
  push_cast; ring
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCOne
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace COne
theorem om_sch_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.om x Φ ∈ d.sch :=
  d.ok.dbl.weil.2.1.pres x Φ h
theorem T_zero_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (h : Φ ∈ d.sch) : d.T Φ 0 = d.l Φ := by
  have := d.ok.dbl.kill 0 Φ h
  have e2 : (0 : Matrix (Fin d.m) (Fin d.n) (AE F E)) * (diagCols (Fin d.n) : Matrix _ _ (AE F E))ᵀ = 0 := Matrix.zero_mul _
  have e3 : (0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ = 0 := Matrix.zero_mul _
  erw [e2] at this
  show d.l (d.dd.rho d.B.ψ ((0 : Mx F E d.m d.n) * (incM F d.b.1.toCols₂)ᵀ) Φ) = _
  rw [e3]
  exact this
theorem constantTerm_eq_fourierAtZero (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ : d.Fn} (h : Φ ∈ d.sch) (x : d.G) : d.sec0 Φ x = d.T (d.om x Φ) 0 :=
  (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_zero_k d (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d x h)).symm
theorem T_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : ℂ) (Φ : d.Fn) (X : Mx F E d.m d.n) : d.T (c • Φ) X = c * d.T Φ X := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.T Darboux.rho
  have : schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) (c • Φ) = c • schr d.B.ψ (d.dd.e (X * (incM F d.b.1.toCols₂)ᵀ)) Φ := by
    funext y; simp only [schr, Pi.smul_apply, smul_eq_mul]; ring
  rw [this, map_smul, smul_eq_mul]
theorem orb_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) (c : ℂ) (Φ : d.Fn) : d.orb T (c • Φ) = c * d.orb T Φ := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.orb
  simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k, tsum_mul_left]
  simp only [MeasureTheory.average]
  exact integral_const_mul _ _
theorem Ln_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : L.n + 1 = d.n := by
  have e : Fin L.n ≃ {i : Fin d.n // ¬ i = L.i₀} :=
    (Equiv.ofInjective L.em L.inj).trans (Equiv.subtypeEquivRight fun i => (L.rng i).symm)
  have h1 := Fintype.card_congr e
  rw [Fintype.card_fin, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq] at h1
  have := L.i₀.isLt
  omega
theorem fcVal_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d' : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R'' : _root_.PositivityTheory.SiegelWeilFormula.RD_k d') (hMV : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R'') {Ψ : d'.Fn} (hΨ : Ψ ∈ d'.sch)
    (hv : d'.T Ψ ∈ R''.vac) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d'.Y) d'.b nb lam 𝓖) (T : nF σ d'.Y d'.b)
    (g : d'.G) :
    HolValueAt (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z) T g) (s0 d'.m d'.n)
      (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
  have hK := H.polyKFin F E σ d' R'' Ψ hΨ ((H.vacK F E σ d' R'').2.1 hv)
  have hsec := H.secK F E σ d' Ψ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d' _ _ hsec (s0 d'.m d'.n)
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hadd, hbd⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d' hc T g
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d'.Y) (fun f => fc d'.B.ψ d'.b nb lam 𝓖 f T g) hadd hbd U Ê hUo hd hcont hinv
  have hpt : ∀ g', ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n), iteratedDeriv i (Ê · g') (s0 d'.m d'.n) =
      iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * d'.I Ψ g') := fun g' =>
    ordVal U p (Ê · g') (fun z => d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g') t _ (2 * d'.I Ψ g') hUo hR hs hp (hd g')
      (fun z hz => (hfar z hz).2 g') (hMV Ψ hΨ hv g')
  have hsm : ∀ (c : ℂ) (φ : d'.G → ℂ), fc d'.B.ψ d'.b nb lam 𝓖 (fun g' => c * φ g') T g =
      c * fc d'.B.ψ d'.b nb lam 𝓖 φ T g := by
    intro c φ; simp only [fc, mul_assoc]; exact integral_const_mul _ _
  have hder : ∀ i ≤ p.rootMultiplicity (s0 d'.m d'.n),
      iteratedDeriv i (fun z => fc d'.B.ψ d'.b nb lam 𝓖 (Ê z) T g) (s0 d'.m d'.n) =
        iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * (2 * fc d'.B.ψ d'.b nb lam 𝓖 (d'.I Ψ) T g) := by
    intro i hi
    rw [hComm _ hs i]
    have : (fun g' => iteratedDeriv i (Ê · g') (s0 d'.m d'.n)) =
        fun g' => (iteratedDeriv i (fun z => p.eval z) (s0 d'.m d'.n) * 2) * d'.I Ψ g' :=
      funext fun g' => by rw [hpt g' i hi]; ring
    rw [this, hsm]; ring
  refine wrap U p _ _ t _ _ hUo hR hs hp hDiff (fun z hz => ?_) (fun i hi => ?_) (hder _ le_rfl)
  · have e1 : Ê z = fun g' => p.eval z * d'.eis (d'.sec0 Ψ) (s0 d'.m d'.n) z g' := funext (hfar z hz).2
    rw [e1, hsm]
  · rw [hder i hi.le, pderiv_lt p _ i hi, zero_mul]
end COne
section Deg
variable (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)
include H hIH hΦ hv in
theorem cOneVal_pf_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {nb' lam' 𝓖'}
    (hc' : CoefData (σ := σ) (Y := L.Y) L.b nb' lam' 𝓖') {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T') (x : d.G) :
    HolValueAt (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) (s0 d.m d.n)
      (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x) := by
  obtain ⟨q, g₀, k, r, c, hk, hx, hr, ha, hTq⟩ := H.iwaQ F E σ d L x
  have hΦk : d.om k Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d k hΦ
  have hvk : d.T (d.om k Φ) ∈ R.vac := (H.vacK F E σ d R).1 Φ hΦ hv k hk
  obtain ⟨Φ', hres, hv'⟩ := (H.vacK F E σ d R).2.2 L R' _ hΦk hvk
  have hΦ' : Φ' ∈ L.sd.sch := hres.1
  have hres0 : ∀ g : L.sd.G, L.sd.T (L.sd.om g Φ') 0 = d.T (d.om (L.j g) (d.om k Φ)) 0 := by
    intro g
    have := L.res _ hΦk Φ' hΦ' hres.2 g 0 (fun a => rfl)
    rwa [Matrix.submatrix_zero] at this
  have hf : ∀ g' : L.sd.G, d.sec0 Φ (L.j g' * x) = c * L.sd.sec0 Φ' (g' * g₀) := by
    intro g'
    have hΨ : d.om (L.j g₀) (d.om k Φ) ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d _ hΦk
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero d hΦ, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.constantTerm_eq_fourierAtZero L.sd hΦ', hx]
    have e : d.om (L.j g' * (q * L.j g₀ * k)) Φ = d.om (L.j g' * q) (d.om (L.j g₀) (d.om k Φ)) := by
      simp only [map_mul, mul_assoc]; rfl
    rw [e, hTq _ hΨ g' 0 (fun a => rfl), hres0 (g' * g₀)]
    congr 2
    simp only [map_mul]; rfl
  have hs' : s0 d.m L.n = s0 d.m d.n + 1 / 2 := by
    unfold s0; rw [← _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.Ln_k L]; push_cast; ring
  have hid : ∀ z, _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x = (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2)) T' g₀ := by
    intro z
    have ex : z + 1 / 2 - s0 d.m L.n = z - s0 d.m d.n := by rw [hs']; ring
    have hF : ∀ g' : L.sd.G, ((d.Ht (L.j g' * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 Φ (L.j g' * x) =
        (c * (r : ℂ) ^ (z - s0 d.m d.n)) * (((L.sd.Ht (g' * g₀) : ℝ) : ℂ) ^ (z + 1 / 2 - s0 d.m L.n) *
          L.sd.sec0 Φ' (g' * g₀)) := by
      intro g'
      rw [hf g', ex]
      have e1 : ((d.Ht (L.j g' * x) : ℝ) : ℂ) = ((((r * L.a (g' * g₀)).toNNReal : ℝ)) : ℂ) := by
        simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, ha g']
      rw [e1, COne.ht_cpow r _ hr]
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht]
      ring
    have hcs : GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) (fun g => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s0 d.m d.n) *
        d.sec0 Φ (L.j g * x)) = fun g => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
          L.sd.eis (L.sd.sec0 Φ') (s0 d.m L.n) (z + 1 / 2) (g * g₀) :=
      funext fun g => COne.cosetSum_factor _ _ _ _ _ g₀ hF g
    unfold _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k
    rw [hcs]
    simp only [fc, mul_one, mul_assoc, integral_const_mul]
  have hW := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.fcVal_k H R' hIH hΦ' hv' hc' T' g₀
  rw [hs'] at hW
  have hsh := COne.hv_shift _ (s0 d.m d.n) (1 / 2) _ c r hr hW
  have hv1 : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = c * fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.I Φ') T' g₀ := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x, H.thetaCoef F E σ L.sd Φ' hΦ' nb' lam' 𝓖' hc' T' g₀]
    rw [(H.orbRes F E σ d).2 L T T' hT (d.om x Φ) (c • L.sd.om g₀ Φ') ⟨?_, ?_⟩, _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.orb_smul_k]
    · exact Submodule.smul_mem _ _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k L.sd g₀ hΦ')
    · intro X hX
      rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COne.T_smul_k]
      have h1 := L.res _ hΦk Φ' hΦ' hres.2 g₀ X hX
      have hΨ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COne.om_sch_k d (L.j g₀) hΦk
      have h2 := hTq _ hΨ 1 X hX
      simp only [map_one, one_mul, Module.End.one_apply] at h2
      have h1' : L.sd.T (L.sd.om g₀ Φ') (X.submatrix id L.em) = d.T (d.om (L.j g₀) (d.om k Φ)) X := h1
      rw [h1', hx]
      have e : d.om (q * L.j g₀ * k) Φ = d.om q (d.om (L.j g₀) (d.om k Φ)) := by simp only [map_mul]; rfl
      rw [e, h2]
  have hfun : (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) (s0 d.m d.n) z nb' lam' 𝓖' T' x) = fun z => (c * (r : ℂ) ^ (z - s0 d.m d.n)) *
      (fun z => fc d.B.ψ L.b nb' lam' 𝓖' (L.sd.eis (L.sd.sec0 Φ') (s0 d.m d.n + 1 / 2) z) T' g₀) (z + 1 / 2) := by
    funext z; rw [hid z, hs']
  rw [hfun, hv1]
  convert hsh using 1
  ring
end Deg
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepCOneC
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace COneB
theorem fcBd'_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) :
    ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      ∀ y : d.G, (∀ β ∈ K, ‖f (nb β * y)‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T y‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  refine ⟨K, hK, fun f M hf y hM => ?_⟩
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hbd : ∀ β, ‖f (nb β * y) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))‖ ≤ M := by
    intro β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hψ.2.1 _, mul_one]
    have e : f (nb β * y) = f (nb (γ + β) * y) := by
      rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
    rw [e]
    exact hM _ hk
  have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd β)
  have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
  rw [hr, mul_one] at h1
  exact h1
end COneB
section Deg
variable (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
  (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U : Set ℂ} {p : Polynomial ℂ} {Ê : ℂ → d.G → ℂ} {t : ℝ}
  (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t)
include H hE in
theorem avgHol_pf_k {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) {T' : nF σ L.Y L.b}
    (hT : L.IsSub T T') {uM ν 𝓤} (hu : L.UData uM ν 𝓤) (x : d.G) :
    DifferentiableOn ℂ (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) U ∧ ∀ i : ℕ,
      iteratedDeriv i (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x) (s0 d.m d.n) =
        _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => iteratedDeriv i (Ê · g) (s0 d.m d.n)) T x := by
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  have hσ := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
  have hb := d.ok.frame
  have hnbc := kfour.nb_continuous hσ hb hc.1
  obtain ⟨iTG, -, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  obtain ⟨KN, hKN, hKNb⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.fcBd'_k d hc T
  obtain ⟨KU, hKU, hKUc⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.ratV_cocompact_k L
  have huc := _root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_cont_k L hu
  let C : Set d.G := (fun q : nA σ d.Y d.b × (Fin L.n → AE F E) => nb q.1 * uM q.2 * x) '' (KN ×ˢ KU)
  have hCc : IsCompact C :=
    (hKN.prod hKU).image (((hnbc.comp continuous_fst).mul (huc.comp continuous_snd)).mul continuous_const)
  have hper : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) → ∀ u, ∃ k ∈ KU,
      fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) = fc d.B.ψ d.b nb lam 𝓖 φ T (uM k * x) := by
    intro φ hφ hi u
    obtain ⟨r, hr, hk⟩ := hKUc u
    refine ⟨r + u, hk, ?_⟩
    rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.COneB.uM_add_k L hu, mul_assoc, (H.fcConj F E σ d L nb lam 𝓖 hc).2 uM ν 𝓤 hu T T' hT φ hφ hi r hr]
  have hbound : ∀ (φ : d.G → ℂ) (M : ℝ), Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      (∀ y ∈ C, ‖φ y‖ ≤ M) → ∀ u, ‖fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)‖ ≤ M := by
    intro φ M hφ hi hM u
    obtain ⟨k, hk, e⟩ := hper φ hφ hi u
    rw [e]
    refine hKNb φ M hi _ fun β hβ => hM _ ⟨(β, k), ⟨hβ, hk⟩, ?_⟩
    simp only [mul_assoc]
  have hmeas : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      AEStronglyMeasurable (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) ν := by
    intro φ hφ hi
    exact ((_root_.PositivityTheory.SiegelWeilFormula.AStep.fcCont_k d hc T φ hφ hi).comp (huc.mul continuous_const)).aestronglyMeasurable
  have hfin : ν 𝓤 < ⊤ := by rw [hu.2.2.2]; exact ENNReal.one_lt_top
  have hint : ∀ φ : d.G → ℂ, Continuous φ → (∀ γ ∈ rat2 σ d.Y, ∀ g, φ (γ * g) = φ g) →
      IntegrableOn (fun u => fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x)) 𝓤 ν := by
    intro φ hφ hi
    obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hφ.continuousOn
    exact Measure.integrableOn_of_bounded (M := M) hfin.ne (hmeas φ hφ hi)
      (Filter.Eventually.of_forall fun u => hbound φ M hφ hi hM u)
  have hadd : ∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) → _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (a • f + f') T x =
        a * _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 f T x + _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 f' T x := by
    intro a f f' hf hf' hi hi'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k]
    have e : (fun u => fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T (uM u * x)) =
        fun u => a * fc d.B.ψ d.b nb lam 𝓖 f T (uM u * x) + fc d.B.ψ d.b nb lam 𝓖 f' T (uM u * x) :=
      funext fun u => (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d hc T (uM u * x)).1 a f f' hf hf' hi hi'
    rw [e, integral_add ((hint f hf hi).const_mul a) (hint f' hf' hi'), integral_const_mul]
  have hbd : ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → (∀ y ∈ C, ‖f y‖ ≤ M) → ‖_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 f T x‖ ≤ M := by
    refine ⟨C, hCc, fun f M hf hi hM => ?_⟩
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun u _ => hbound f M hf hi hM u)
    have hr : ν.real 𝓤 = 1 := by simp [Measure.real, hu.2.2.2]
    rw [hr, mul_one] at h1
    exact h1
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) (fun φ => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x) hadd hbd U Ê hUo hd hcont hinv
  exact ⟨hDiff, fun i => hComm _ hs i⟩
end Deg
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCoreX
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem coreX_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.CoreX_k := by
  intro ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
    μH, 𝓕, hH, hF, horb⟩ := hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
    (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb, mul_left_comm]
  exact ((holValueAt_const_mul_cpow c' hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
end

