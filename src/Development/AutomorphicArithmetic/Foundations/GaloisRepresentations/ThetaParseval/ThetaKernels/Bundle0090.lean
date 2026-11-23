module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0013
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0039
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.NdZero
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0087
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaLine
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0055
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0056
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.ExpAlg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0075
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0083
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalOperatorBlocks.GoodSigPq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0068
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0081
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0088
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0084

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAldSmallS
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal ENNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Ald
variable {F : Type} [Field F] [NumberField F]
theorem smallS_of_k (hC : _root_.PositivityTheory.SiegelWeilFormula.Ald.ChartFacts_k) (hF : SliceFacts) (hU : SubSplit) (hH : HaarLc) : _root_.PositivityTheory.SiegelWeilFormula.Ald.SmallS_k := by
  intro hT F E _ _ _ _ _ σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had' S1 S1' C hC0 hop hTf
  have hψ : IsStd d.B.ψ := d.ok.good.std
  have hcm : IsCMExt F E σ := d.ok.good.cm
  have hJ : d.A.J.det ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact (_root_.GlobalTheory.isUnit_det_of_isHerm F E σ d.B d.m d.A d.r d.s hA).ne_zero
    · exact (_root_.GlobalTheory.SkewUnit.isUnit_det_of_isSkew F E σ d.B d.m d.A d.r d.s hA).ne_zero
  obtain ⟨hc1, -, -, -, hc5⟩ := hC F E σ d n h Y b j ε hn hs hb e1 e2 hj dd0 dd' had0 had'
  have hlin := d.ok.dbl.lin
  have pres1 : ∀ u : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S u ∘ₗ S1') φ ∈ schA F (K1 d.m n) :=
    fun u φ hφ => hop.pres _ (hlin.pres u _ (hop.pres' φ hφ))
  have one1 : ∀ φ ∈ schA F (K1 d.m n), (S1 ∘ₗ d.S 1 ∘ₗ S1') φ = φ := fun φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_one, Module.End.one_apply]
    exact hop.right φ hφ
  have mul1 : ∀ u v : UA σ d.A.J, ∀ φ ∈ schA F (K1 d.m n),
      (S1 ∘ₗ d.S (u * v) ∘ₗ S1') φ = (S1 ∘ₗ d.S u ∘ₗ S1') ((S1 ∘ₗ d.S v ∘ₗ S1') φ) := fun u v φ hφ => by
    simp only [LinearMap.coe_comp, Function.comp_apply, map_mul, Module.End.mul_apply]
    rw [hop.left _ (hlin.pres v _ (hop.pres' φ hφ))]
  obtain ⟨SA1, hSA1⟩ := projHom (fun u => S1 ∘ₗ d.S u ∘ₗ S1') pres1 one1 mul1
  have hsplit : IsUSplitting (adeleClass F) d.B.ψ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm)
      (fun (g : UA σ d.A.J) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) => mat g * x) SA1 :=
    GlobalTheory.TowU.isUSplitting_of_isOp hψ (fun w => by simp) hop hSA1 hlin
  have hexp : ∀ u : UA σ d.A.J, ∀ Ψ ∈ schA F (K1 d.m n), ∀ x : K1 d.m n → AF F,
      SA1 u Ψ x = Ψ (Sum.elim (Lk d.bs (mat u⁻¹) (x ∘ Sum.inl)) (Lc d.bs (mat u⁻¹) (x ∘ Sum.inr))) := by
    intro u Ψ hΨ x
    set X : Mx F E d.m d.n := cmbB d.bs (x ∘ (eK d.m h).symm) with hX
    have hx : crdB d.bs X ∘ eK d.m h = x := by
      rw [hX, crdB_cmbB]; funext k; simp
    have hΦ : S1' Ψ ∈ d.sch := hop.pres' Ψ hΨ
    have hTP := (hT.2.1 F E σ d (S1' Ψ) hΦ).2.2 u X
    rw [hTf _ (hlin.pres u _ hΦ), hTf _ hΦ, hop.right Ψ hΨ] at hTP
    have key := mul_left_cancel₀ hC0 hTP
    calc SA1 u Ψ x = S1 (d.S u (S1' Ψ)) x := by rw [hSA1 u Ψ hΨ]; rfl
      _ = S1 (d.S u (S1' Ψ)) (crdB d.bs X ∘ eK d.m h) := by rw [hx]
      _ = Ψ (crdB d.bs (mat u⁻¹ * X) ∘ eK d.m h) := key
      _ = _ := by rw [← Lk_crdB, hX, crdB_cmbB, Lk_eK]
  have hbox : ∀ u : UA σ d.A.J, ∀ φ' ∈ schA F (Fin d.m × Fin n × Fin 2), ∀ φ'' ∈ schA F (Fin d.m × Fin 2),
      SA1 u (boxFun φ' φ'') = boxFun (φ' ∘ Lk d.bs (mat u⁻¹)) (φ'' ∘ Lc d.bs (mat u⁻¹)) := by
    intro u φ' h' φ'' h''
    funext x
    rw [hexp u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ' h' φ'' h'')]
    rfl
  obtain ⟨φ₀, hφ₀, hφ₀1, hφ₀n⟩ := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).2.2.1
  obtain ⟨φa, hφa, hφa1, -⟩ := (hF F (Fin d.m × Fin 2) (Fin d.m × Fin n × Fin 2)).2.2.1
  let c : UA σ d.A.J → ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) →ₗ[ℂ] ((Fin d.m × Fin n × Fin 2 → AF F) → ℂ) :=
    fun u => LinearMap.funLeft ℂ ℂ (Lk d.bs (mat u⁻¹))
  have hc : ∀ u φ, c u φ = φ ∘ Lk d.bs (mat u⁻¹) := fun _ _ => rfl
  have presS : ∀ u, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c u φ ∈ schA F (Fin d.m × Fin n × Fin 2) := by
    intro u φ hφ
    have := (hF F (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2)).1 _
      (hsplit.pres u _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φ hφ φ₀ hφ₀))
    rw [hbox u φ hφ φ₀ hφ₀, slice0_box, Function.comp_apply, Lc_zero, hφ₀1, one_smul] at this
    exact this
  have oneS : ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c 1 φ = φ := by
    intro φ _
    have hm : mat (1 : UA σ d.A.J)⁻¹ = 1 := by rw [inv_one]; rfl
    rw [hc, hm]
    funext x
    simp only [Function.comp_apply, Lk_one]
  have mulS : ∀ u v, ∀ φ ∈ schA F (Fin d.m × Fin n × Fin 2), c (u * v) φ = c u (c v φ) := by
    intro u v φ _
    rw [hc, hc, hc, mul_inv_rev, show mat (v⁻¹ * u⁻¹) = mat v⁻¹ * mat u⁻¹ from rfl]
    funext x
    simp only [Function.comp_apply, Lk_mul]
  obtain ⟨S', hS'⟩ := projHom c presS oneS mulS
  have hφ₁ : ∀ g : UA σ d.A.J, φ₀ ∘ Lc d.bs (mat g⁻¹) ∈ schA F (Fin d.m × Fin 2) := by
    intro g
    have := sliceL_mem hF (hsplit.pres g _ (GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ φa hφa φ₀ hφ₀))
    rw [hbox g φa hφa φ₀ hφ₀] at this
    convert this using 1
    funext x''
    simp only [boxFun, Function.comp_apply, Sum.elim_comp_inl, Sum.elim_comp_inr, Lk_zero, hφa1, one_mul]
  have hsplitS : IsUSplitting (adeleClass F) d.B.ψ dd' (fun (g : UA σ d.A.J) x => mat g * x) S' :=
    hU F d.B.ψ hψ (Fin d.m × Fin n × Fin 2) (Fin d.m × Fin 2) (Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
      (Matrix (Fin d.m) (Fin n ⊕ Fin n) (AE F E)) _ _ (GlobalTheory.TowU.reindexD dd0 (eK d.m h).symm) dd' (emb h b d.b) hc1
      (UA σ d.A.J) (UA σ d.A.J) (fun g x => mat g * x) (fun g x => mat g * x) (MonoidHom.id _) continuous_id
      (fun g w' => hc5 g w') SA1 S' hsplit φ₀ hφ₀ hφ₀1 hφ₀n (fun g => ⟨φ₀ ∘ Lc d.bs (mat g⁻¹), hφ₁ g,
        by rw [Function.comp_apply, Lc_zero, hφ₀1],
        fun μ'' hμ'' => hH F E σ hcm d.m d.A.J hJ d.bs g⁻¹ μ'' hμ'' (fun x => ‖φ₀ x‖ₑ ^ 2),
        fun φ' hφ' => by
          show SA1 g (boxFun φ' φ₀) = _
          rw [hbox g φ' hφ' φ₀ hφ₀, hS' g φ' hφ', hc]⟩)
  refine ⟨S', hsplitS, fun g Φ hΦ => ?_⟩
  show S' g Φ 0 = Φ 0
  rw [hS' g Φ hΦ, hc, Function.comp_apply, Lk_zero]
end PositivityTheory.SiegelWeilFormula.Ald
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepTop
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem ndZero_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (hmn : d.m < d.n) {Φ : d.Fn} (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac)
    {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ) (hj : j ≤ p.rootMultiplicity (s0 d.m d.n))
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} (hT : IsND T) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hL : (fun f => fc d.B.ψ d.b nb lam 𝓖 f T x) ∈ d.lamSet := ⟨nb, lam, 𝓖, T, x, hc, hT, rfl⟩
  obtain ⟨hadd, hbd⟩ := H.lamBd F E σ d _ hL
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  obtain ⟨hDiff, hComm⟩ := lamDeriv (rat2 σ d.Y) _ hadd hbd U Ê hUo hd hcont hinv
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hAc := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, iteratedDeriv j (Ê · (γ * g)) (s0 d.m d.n) = iteratedDeriv j (Ê · g) (s0 d.m d.n) :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hLI : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x = 0 := by
    rw [H.thetaCoef F E σ d Φ hΦ nb lam 𝓖 hc T x]; exact (H.orbRes F E σ d).1 hmn T hT _
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) • d.I Φ +
      (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n)) := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have h1 := hadd (-(iteratedDeriv j (fun z => p.eval z) (s0 d.m d.n) * 2)) (d.I Φ) (fun g => iteratedDeriv j (Ê · g) (s0 d.m d.n))
    hIc hAc hIi hAi
  rw [hB, h1, hLI, mul_zero, zero_add, ← hComm _ hs j]
  obtain ⟨t', ht'⟩ := H.unfold F E σ d _ _ hsec hEis
  obtain ⟨ε, w, hw, -⟩ := (H.auxEx F E σ d).2.1
  have hWL := H.whitLow F E σ d R hmn Φ hΦ hv nb lam 𝓖 hc ε w hw T hT x
  rw [zero_mul] at hWL
  have := ordVal U p (fun z => fc d.B.ψ d.b nb lam 𝓖 (Ê z) T x)
    (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) (max t t')
    (s0 d.m d.n) 0 hUo hR hs hp hDiff ?_ hWL j hj
  · rw [this, mul_zero]
  · intro z hz
    have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
    have h2 := (ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hc ε w hw x).2 T hT
    rw [← h2]
    simp only [fc, h1, mul_assoc]
    exact integral_const_mul _ _
theorem stepJ_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0) :
    ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
  obtain ⟨nb, lam, 𝓖, hc⟩ := H.coefEx F E σ d
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  have hBc : Continuous (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) :=
    (famCont U Ê hUo hd hcont _ hs j).sub (continuous_const.mul (continuous_const.mul hIc))
  have hBr : ∀ γ ∈ rat2 σ d.Y, ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j (γ * g) = _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g := fun γ hγ g => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j, hIi γ hγ g]
  have hz := H.fourierZero F E σ d nb lam 𝓖 hc (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) hBc (fun β hβ g => hBr _ (_root_.PositivityTheory.SiegelWeilFormula.AStep.nbRat_k d hc β hβ) g) ?_
  · intro g; exact congrFun hz g
  · intro T g
    by_cases hT : IsND T
    · exact _root_.PositivityTheory.SiegelWeilFormula.AStep.ndZero_k H R hmn hΦ hv hE j hj hc hT g
    · obtain ⟨γ, hγ, T₀, T', hsub, hfc⟩ := (H.fcConj F E σ d L nb lam 𝓖 hc).1 T hT
      rw [hfc _ hBc hBr g]
      exact _root_.PositivityTheory.SiegelWeilFormula.AStep.deg_k H R L R' hmn hIH hΦ hv hE j hj hlow hc hsub _
theorem step_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) : _root_.PositivityTheory.SiegelWeilFormula.Step_k := by
  intro F E _ _ _ _ _ σ d R L R' hmn hIH Φ hΦ hv x
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  obtain ⟨U, p, Ê, t, hE⟩ := H.eisWk F E σ d _ _ hsec (s0 d.m d.n)
  have hall : ∀ j ≤ p.rootMultiplicity (s0 d.m d.n), ∀ g, _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j g = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      refine _root_.PositivityTheory.SiegelWeilFormula.AStep.stepJ_k H R L R' hmn hIH hΦ hv hE j hj fun i hi g => ?_
      have := ih i hi (hi.le.trans hj) g
      simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ i (lt_of_lt_of_le hi hj), zero_mul, sub_zero] using this
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE
  refine wrap U p (Ê · x) (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) t _ _ hUo hR hs hp (hd x)
    (fun z hz => (hfar z hz).2 x) (fun j hj => ?_) ?_
  · have := hall j hj.le x
    simpa only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, pderiv_lt p _ j hj, zero_mul, sub_zero] using this
  · exact sub_eq_zero.1 (hall _ le_rfl x)
theorem stepOf_k : _root_.PositivityTheory.SiegelWeilFormula.StepOf_k := fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 =>
  _root_.PositivityTheory.SiegelWeilFormula.AStep.step_k ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaLine
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace LineFix
theorem good_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : (PositivityTheory.RgEis.adCM σ d.χ).Good :=
  PositivityTheory.RgEis.Hd.cmGood_of PositivityTheory.RgEis.Hd.stdGood PositivityTheory.RgEis.Hd.dict PositivityTheory.RgEis.Hd.dictInf F E σ d.χ d.m
    d.ok.good.cm d.ok.good.unram d.ok.hecke d.ok.res
theorem cc_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : AE F E) : cA σ (cA σ x) = x := (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).σσ x
theorem frame_eps_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ ε : ℤˣ, (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ) =
    Matrix.fromBlocks 0 1 (((ε : ℤ) : AE F E) • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E))) 0 := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  refine ⟨ε, ?_⟩
  have e1 : (incM F d.b.1).map (cA σ) = incM F (d.b.1.map σ) := by
    ext i j
    simp [incM, cA, inclR, Algebra.TensorProduct.map_tmul]
  have e2 : dbl (incM F d.Y.J) = incM F (dbl d.Y.J) := by
    simp [dbl, incM, Matrix.fromBlocks_map, Matrix.map_neg]
  have key : incM F (d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ) =
      (incM F d.b.1)ᵀ * incM F (dbl d.Y.J) * incM F (d.b.1.map σ) := by
    simp only [incM, Matrix.map_mul, Matrix.transpose_map]
  rw [e1, e2, ← key, hε]
  ext (i|i) (j|j) <;> simp [incM, Matrix.fromBlocks_map, Matrix.one_apply] <;> split_ifs <;> simp
variable {n : ℕ}
section Unit
variable {ι : Type} [Fintype ι] [DecidableEq ι]
end Unit
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
theorem mL_mem_k (κ : GL (Fin d.n) (AE F E)) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J) := by
  obtain ⟨ε, hε⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.frame_eps_k d
  have hN := Nk_form (σ := σ) (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.cc_k d) ((ε : ℤ) : AE F E) κ
  rw [← hε] at hN
  exact KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hN
theorem mL_mul_k (κ : GL (Fin d.n) (AE F E)) :
    (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * (incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1) = 1 := by
  calc _ = incM F d.b.1 * Nk (σ := σ) κ * (incM F (d.b⁻¹).1 * incM F d.b.1) * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one, Matrix.mul_assoc (incM F d.b.1), Nk_mul_inv, Matrix.mul_one,
          _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d]
def mL_k (κ : GL (Fin d.n) (AE F E)) : d.G :=
  ⟨⟨incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1, incM F d.b.1 * Nk (σ := σ) κ⁻¹ * incM F (d.b⁻¹).1, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mul_k d κ,
    by simpa using _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mul_k d κ⁻¹⟩, by
    show (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1)ᵀ * dbl (incM F d.Y.J) *
      (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1).map (cA σ) = dbl (incM F d.Y.J)
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mem_k d κ⟩
theorem inFrame_mL_k (κ : GL (Fin d.n) (AE F E)) : inFrame d.b (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ) = Nk (σ := σ) κ := by
  show incM F (d.b⁻¹).1 * (incM F d.b.1 * Nk (σ := σ) κ * incM F (d.b⁻¹).1) * incM F d.b.1 = Nk (σ := σ) κ
  simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
  rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
theorem mL_inv_k (κ : GL (Fin d.n) (AE F E)) : _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ⁻¹ = (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  apply _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_injective_k d
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k, Nk_mul_inv, _root_.PositivityTheory.SiegelWeilFormula.Avac.inFrame_one_k]
theorem O_int_k {z : AE F E} (hz : z ∈ (PositivityTheory.RgEis.adCM σ d.χ).O) : finOne F • z ∈ intHat F E :=
  ((PositivityTheory.RgEis.Hd.dict F E).2.2.2.1 z).1 hz
theorem Nk_int_k {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) (i j : Fin d.n ⊕ Fin d.n) :
    finOne F • Nk (σ := σ) κ i j ∈ intHat F E := by
  have hκ' := hκ.1
  rcases i with i | i <;> rcases j with j | j
  · exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.O_int_k d (hκ' i j).1
  · simp [Nk, (intHat F E).zero_mem]
  · simp [Nk, (intHat F E).zero_mem]
  · exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.O_int_k d ((_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).σO _ (hκ' j i).2)
theorem Nk_unit_k {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) (w : InfinitePlace F) :
    (Nk (σ := σ) κ).map (piInf (d.B.emb w)) * ((Nk (σ := σ) κ).map (piInf (d.B.emb w)))ᴴ = 1 := by
  obtain ⟨w', hw'⟩ := ((PositivityTheory.RgEis.Hd.dictInf F E σ d.ok.good.cm).2 d.B.emb).1 w
  set g := (PositivityTheory.RgEis.adCM σ d.χ).φ w' with hg
  have hU : (κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g ∈ Matrix.unitaryGroup (Fin d.n) ℂ := hκ.2 w'
  have hV : ((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g ∈
      Matrix.unitaryGroup (Fin d.n) ℂ := (inv_mem hκ).2 w'
  have hσφ : ∀ z, g (cA σ z) = (starRingEnd ℂ) (g z) := fun z => (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).σφ w' z
  rcases hw' with hf | hf
  · have hf' : ∀ z, piInf (d.B.emb w) z = g z := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = Matrix.fromBlocks ((κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g) 0 0
        (star (((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g)) := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit hU (Unitary.star_mem hV)
  · have hf' : ∀ z, piInf (d.B.emb w) z = (starRingEnd ℂ) (g z) := hf
    have e : (Nk (σ := σ) κ).map (piInf (d.B.emb w)) = Matrix.fromBlocks (star ((κ : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g))ᵀ 0 0
        ((((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)).map g))ᵀ := by
      ext (i | i) (j | j) <;> simp [Nk, Dk, hf', hσφ, Matrix.star_apply]
    rw [e]
    exact blk_unit (transpose_mem_unitaryGroup_vacuum_iwasawa (Unitary.star_mem hU)) (transpose_mem_unitaryGroup_vacuum_iwasawa hV)
theorem mL_mem_K_k {κ : GL (Fin d.n) (AE F E)} (hκ : κ ∈ (PositivityTheory.RgEis.adCM σ d.χ).kGL (Fin d.n)) : _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ ∈ d.K := by
  refine (d.ok.stdK _).2 ⟨fun w => ?_, fun k' hk' i j => ?_⟩
  · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k]; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.Nk_unit_k d hκ w
  · rcases hk' with rfl | hk'
    · rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k]; exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.Nk_int_k d hκ i j
    · rw [Set.mem_singleton_iff] at hk'
      subst hk'
      rw [← _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_inv_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k]
      exact _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.Nk_int_k d (inv_mem hκ) i j
end LineFix
theorem line_fix'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (i₀ : Fin d.n) (x : d.G) : ∃ (p k : d.G) (lam : (AE F E)ˣ), k ∈ d.K ∧ x = p * k ∧
    ∀ a, inFrame d.b p a (Sum.inl i₀) = if a = Sum.inl i₀ then (lam : AE F E) else 0 := by
  obtain ⟨p0, t, hp, k1, hk1, rfl⟩ := d.ok.hgt.iwa x
  have h21 := _root_.PositivityTheory.SiegelWeilFormula.KWhit.parabolic_lowerLeft_block_zero d p0 t hp
  obtain ⟨-, -, A, -, -, -, hA, -, -⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d p0 h21
  obtain ⟨a1, ha1, κ, hκ, hAe⟩ := (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.good_k d).iwa (Fin d.n) {i₀} A
  have hs : ∀ r, r ≠ i₀ → (a1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) r i₀ = 0 ∧
      ((a1⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) r i₀ = 0 :=
    fun r hr => ha1 r (by simpa using hr) i₀ rfl
  have hunit : (a1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) i₀ i₀ *
      ((a1⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) i₀ i₀ = 1 := by
    have := congrFun (congrFun (LineFix.val_mul_inv a1) i₀) i₀
    rw [Matrix.mul_apply, Finset.sum_eq_single i₀ (fun r _ hr => by rw [(hs r hr).2, mul_zero]) (by simp),
      Matrix.one_apply_eq] at this
    exact this
  refine ⟨p0 * (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ)⁻¹, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_k d κ * k1, Units.mkOfMulEqOne _ _ hunit,
    d.K.mul_mem (_root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_mem_K_k d hκ) hk1, by group, fun a => ?_⟩
  have hMb : inFrame d.b p0 = Matrix.fromBlocks (A : Matrix (Fin d.n) (Fin d.n) (AE F E)) (inFrame d.b p0).toBlocks₁₂ 0
      (inFrame d.b p0).toBlocks₂₂ := by
    rw [hA, ← h21, Matrix.fromBlocks_toBlocks]
  have hAk : (A : Matrix (Fin d.n) (Fin d.n) (AE F E)) * ((κ⁻¹ : GL (Fin d.n) (AE F E)) : Matrix (Fin d.n) (Fin d.n) (AE F E)) =
      a1 := by
    rw [hAe, Units.val_mul, Matrix.mul_assoc, LineFix.val_mul_inv, Matrix.mul_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k, ← _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.mL_inv_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.LineFix.inFrame_mL_k, hMb]
  rcases a with r | r
  · simp only [LineFix.Nk, Matrix.fromBlocks_multiply, Matrix.mul_zero, add_zero, Matrix.fromBlocks_apply₁₁, hAk]
    by_cases hr : r = i₀
    · subst hr; simp
    · rw [(hs r hr).1]; simp [hr]
  · simp [LineFix.Nk, Matrix.fromBlocks_multiply]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem B_vline_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.TUnit_k) (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∃ (C : ℂ) (c s : ℝ) (ν : Measure (Mx F E d.m d.n)) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)), C ≠ 0 ∧ s ≠ 0 ∧
      ν.IsAddHaarMeasure ∧ νf.IsAddHaarMeasure ∧
      ∀ g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), ∀ Ω ∈ d.sch, d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g → ∀ Φ ∈ d.sch, ∀ W : Mx F E d.m d.n, finOne F • W = 0 → ∀ z : ℂ,
        _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k ν Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) = C * Real.exp (-(c * ‖z‖ ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2)) *
          (Complex.exp (-(z ^ 2 * ‖s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W‖ ^ 2 / (16 * Real.pi))) *
            ∫ u, _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
              Complex.exp (z * ⟪s • _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W, u⟫_ℝ)) := by
  obtain ⟨νf, hνf, hν⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFP.exists_nuf_k R
  refine ⟨1, 1 / (16 * Real.pi), -(4 * Real.pi), Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf), νf,
    one_ne_zero, neg_ne_zero.2 (by positivity), hν, hνf, ?_⟩
  intro g hg' Ω hΩ hTΩ Φ hΦ W hW z
  set w := _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W with hw
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z
  let b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ := _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z
  have hTv : ∀ X, d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) :=
    _root_.PositivityTheory.SiegelWeilFormula.KFP.T_vline_k hH R hΩ hTΩ hW z
  have hb : Continuous b := _root_.PositivityTheory.SiegelWeilFormula.KFP.continuous_bv_k w z
  have hb1 : ∀ u, ‖b u‖ ≤ 1 := _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_bv_le_k w z
  have hTΦ : d.T Φ ∈ d.schM := (hT.1 F E σ d).1 Φ hΦ
  have e1 : _root_.PositivityTheory.SiegelWeilFormula.KFP.B_k (Measure.map (_root_.PositivityTheory.SiegelWeilFormula.KFP.jnp_k R) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) Φ (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.B_k, hTv]
    exact _root_.PositivityTheory.SiegelWeilFormula.KFP.integral_jnp_k R hνf hTΦ hg' hb hb1
  rw [e1]
  have key : ∀ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u =
      ((Real.exp (-(1 / (16 * Real.pi) * ‖z‖ ^ 2 * ‖(-(4 * Real.pi)) • w‖ ^ 2)) : ℝ) : ℂ) *
        Complex.exp (-(z ^ 2 * (‖(-(4 * Real.pi)) • w‖ ^ 2 : ℝ) / (16 * Real.pi))) *
          (_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf (d.T Φ) g u * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2)) *
            Complex.exp (z * ⟪(-(4 * Real.pi)) • w, u⟫_ℝ)) := by
    intro u
    have hz : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
    have h1 := exp_alg z.re z.im (‖w‖ ^ 2) ⟪w, u⟫_ℝ (‖u‖ ^ 2)
    rw [← hz] at h1
    have hn : ‖(-(4 * Real.pi)) • w‖ ^ 2 = 16 * Real.pi ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have hi : ⟪(-(4 * Real.pi)) • w, u⟫_ℝ = -(4 * Real.pi) * ⟪w, u⟫_ℝ := real_inner_smul_left _ _ _
    have hzn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by rw [Complex.sq_norm, Complex.normSq_apply]; ring
    simp only [b, _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, star_star, hn, hi, hzn]
    have h2 : _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u = 2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
        4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
        ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
      rfl
    rw [h2, h1]
    ring
  simp_rw [key]
  rw [integral_const_mul]
  simp only [one_mul, Complex.ofReal_exp]
  push_cast
  ring
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocinstInst
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.KLI
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem locHyp_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ} (hL : R.IsLocOp w L) :
    LocHyp (R.sg w) L := by
  have hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.goodAwayEx_k
  refine
    { sw := fun y f hf => (hL y f hf).1
      one := R.locOp_one hT hG hL
      mul := R.locOp_mul hT hG hL
      lin := R.locOp_lin hT hG hL
      nU := R.locOp_nU hT hG hL
      mM := ?_
      nbar := ?_
      longWeylFunctional := R.localOperator_longWeyl_integral hT hA hG hL
      cont := _root_.PositivityTheory.SiegelWeilFormula.KLI.locOp_cont_k hT R hL }
  · obtain ⟨k, hk⟩ := R.locOp_mM_law w hT hG hL
    exact ⟨k, fun y a ha hy f hf => hk y a ha hy f hf⟩
  · obtain ⟨C, s, κ, ε, hs, hκ, h4, hf, -, hs2, hη⟩ := R.locOp_nbar hT hA hG hL
    exact ⟨C, s, κ, ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹, hs, hκ, hs2, hη, h4, fun y c hc hy f hf' => hf y c hc hy f hf'⟩
theorem locInst_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (_hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (_hLi : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k) : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k := by
  intro F E _ _ _ _ _ σ d R w L hL
  obtain ⟨sL, ρ, e, hD, h1, h2⟩ := locData_of (_root_.PositivityTheory.SiegelWeilFormula.KLI.locHyp_of_k hT hA R hL)
  exact ⟨sL, ρ, pOf (R.sg w) d.m, qOf (R.sg w) d.m, e, fun hnm => goodSig_pq _ hnm, hD, h1, h2⟩
end PositivityTheory.SiegelWeilFormula.KLI
end
end
end

