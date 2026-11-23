module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0016
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0015
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0083
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.ExpNeOfLt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0040
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0030
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.NormAddSmulSq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0043
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0035
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0075
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0032
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0055
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0065
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0081
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0084
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0058
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0076
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0068

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RestrictBoxFunK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.DblTargetRestrict
theorem restrict_boxFun_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
      ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ),
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
      ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
      ∀ ωd : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
          Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
          (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ omp : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ) × UG (cA σ) (incM F JB) →*
          Module.End ℂ ((κ ⊕ κ → AF F) → ℂ),
        GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) ωd omp →
      ∀ (g : UG (cA σ) (incM F JA)) (gd : UG (cA σ) (incM F (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)ᵀ)),
        gd.1.1 = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks g.1.1 0 0 1) →
        ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, omp (gd, 1) (boxFun φ₁ φ₂) = boxFun (om (g, 1) φ₁) φ₂ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT _ _ _ _ ω hω JA JB ξ hA hB' κ _ co hrat om hom
    ωd hωd omp homp g gd hgd φ₁ hφ₁ φ₂ hφ₂
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hω.std.1
  let h : Formalism.IndefR.DatumF.GAF σ JT := ⟨g.1, GlobalTheory.TransportF.mem_HR_target hA g⟩
  let hd : Formalism.IndefR.DatumF.GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) := ⟨gd.1, GlobalTheory.TransportF.mem_HR_target rfl gd⟩
  have hh : Formalism.IndefR.DatumF.mtF σ JT h = g.1.1 := rfl
  have hhd : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd = gd.1.1 := rfl
  have h1 : Formalism.IndefR.DatumF.mtF σ JS 1 = ((1 : UG (cA σ) (incM F JB))⁻¹).1.1ᵀ := by
    show (Formalism.IndefR.DatumF.matHomF σ JS 1).1 = _
    rw [map_one, inv_one]
    first | rfl | simp | exact Matrix.transpose_one.symm
  have hdm : Formalism.IndefR.DatumF.mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) hd =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Formalism.IndefR.DatumF.mtF σ JT h) 0 0 1) := by
    rw [hhd, hgd, hh]
  have t1 := hom g 1 1 h hh h1 φ₁ hφ₁
  have hΦ := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ φ₁ hφ₁ φ₂ hφ₂
  have hΦ' := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ _ t1.1 φ₂ hφ₂
  have t2 := homp gd 1 1 hd hhd h1 _ hΦ
  have hφ₂' := _root_.GlobalTheory.Adopt.adelicSchwartzSpace_closed_under_conj_reflection F κ φ₂ hφ₂
  let τ := Fintype.equivFin κ
  have he : ∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' =
      GlobalTheory.ThetaTransform.symV (GlobalTheory.TransportF.numCoordF co τ w) (GlobalTheory.TransportF.numCoordF co τ w') := fun w w' => by
    rw [GlobalTheory.TransportF.symplOF_eq_symp hA hB', co.form]
    simp only [GlobalTheory.ThetaTransform.symV, GlobalTheory.TransportF.numCoordF_apply, comp_equiv_dotProduct_comp_equiv]
  have hr : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin (Fintype.card κ) → F,
      GlobalTheory.TransportF.numCoordF co τ (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun x => by
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨y ∘ τ.symm, z ∘ τ.symm, by rw [GlobalTheory.TransportF.numCoordF_apply]; erw [h]; rfl⟩
  have thf : ∀ Φ ∈ schA F κ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ
      (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) := fun Φ hΦ => by
    rw [GlobalTheory.TransportF.thetaTr_eqF co τ]
    exact _root_.GlobalTheory.T.schrodinger_model_isomorphism F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ hω.std _ (GlobalTheory.TransportF.numCoordF co τ) he hr _
      (GlobalTheory.TransportF.comp_mem_schA τ hΦ)
  have key := t2.2.trans ((congrArg (ωd (1, hd)) (_root_.GlobalTheory.T.lagrangian_darboux_theta_model F E σ B hB hω.std nS nT JT JA JB ξ hA κ co φ₁ hφ₁ φ₂ hφ₂)).trans
    ((_root_.GlobalTheory.T.weil_pair_global_intertwiner F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hσξ χS χT ω hω ωd hωd h hd hdm _ _ (thf φ₁ hφ₁) (thf _ hφ₂')).trans
      ((congrArg (fun f => GlobalTheory.DblTargetDelta.deltaT f
        (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x))))) t1.2.symm).trans
        (_root_.GlobalTheory.T.lagrangian_darboux_theta_model F E σ B hB hω.std nS nT JT JA JB ξ hA κ co _ t1.1 φ₂ hφ₂).symm)))
  let τ' := Fintype.equivFin (κ ⊕ κ)
  erw [GlobalTheory.TransportF.thetaTr_eqF (ψ := B.ψ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' ((omp (gd, 1)) (boxFun φ₁ φ₂))] at key
  erw [GlobalTheory.TransportF.thetaTr_eqF (ψ := B.ψ) (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ' (boxFun (om (g, 1) φ₁) φ₂)] at key
  have h2 := GlobalTheory.TransportF.thV_injOn hR hψ (GlobalTheory.TransportF.comp_mem_schA τ' t2.1) (GlobalTheory.TransportF.comp_mem_schA τ' hΦ')
    ((GlobalTheory.TransportF.numCoordF (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) τ').surjective.injective_comp_right key)
  funext x
  have hx : (x ∘ τ'.symm) ∘ τ' = x := by
    funext i
    simp
  erw [← hx]
  exact congrFun h2 (x ∘ τ'.symm)
end GlobalTheory.DblTargetRestrict
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepDeg
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem deg_k (H : _root_.PositivityTheory.SiegelWeilFormula.AStep.Hyps_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (hmn : d.m < d.n) (hIH : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R') {Φ : d.Fn}
    (hΦ : Φ ∈ d.sch) (hv : d.T Φ ∈ R.vac) {U p Ê t} (hE : _root_.PositivityTheory.SiegelWeilFormula.AStep.EData_k d (d.sec0 Φ) (s0 d.m d.n) (s0 d.m d.n) U p Ê t) (j : ℕ)
    (hj : j ≤ p.rootMultiplicity (s0 d.m d.n)) (hlow : ∀ i < j, ∀ g, iteratedDeriv i (Ê · g) (s0 d.m d.n) = 0)
    {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {T : nF σ d.Y d.b} {T' : nF σ L.Y L.b} (hT : L.IsSub T T')
    (x : d.G) : fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x = 0 := by
  have hK := H.polyKFin F E σ d R Φ hΦ ((H.vacK F E σ d R).2.1 hv)
  have hsec := H.secK F E σ d Φ hK
  have hEis := H.eisWk F E σ d _ _ hsec
  have hE' := hE
  obtain ⟨hUo, hR, hs, hp, hd, hcont, hinv, hfar⟩ := hE'
  obtain ⟨-, -, hI⟩ := H.tAll.2.2.2.2 F E σ d
  obtain ⟨-, hIc, hIi⟩ := hI Φ hΦ
  set s := s0 d.m d.n with hsdef
  set A : d.G → ℂ := fun g => iteratedDeriv j (Ê · g) s with hAdef
  have hAc : Continuous A := famCont U Ê hUo hd hcont _ hs j
  have hAi : ∀ γ ∈ rat2 σ d.Y, ∀ g, A (γ * g) = A g :=
    fun γ hγ g => derivInv U Ê hUo _ hs γ g (fun z hz => hinv z hz γ hγ g) j
  have hB : _root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j = (-(iteratedDeriv j (fun z => p.eval z) s * 2)) • d.I Φ + A := by
    funext g; simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k, hAdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have hfcB : ∀ x', fc d.B.ψ d.b nb lam 𝓖 (_root_.PositivityTheory.SiegelWeilFormula.AStep.Bj_k d Φ p Ê j) T x' =
      fc d.B.ψ d.b nb lam 𝓖 A T x' - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x') := by
    intro x'
    rw [hB, (_root_.PositivityTheory.SiegelWeilFormula.AStep.fcAll_k d hc T x').1 _ _ _ hIc hAc hIi hAi]; ring
  let w : InfinitePlace F := Classical.arbitrary _
  obtain ⟨y, hy⟩ := dilEx d.n (Pi.single L.i₀ 1) 1
  obtain ⟨pp, qq, e, hpq, hhol⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holA_k H R hmn hΦ hv hE w j hj hlow
  obtain ⟨hlawA, huA⟩ := _root_.PositivityTheory.SiegelWeilFormula.AStep.holCoef_k H R L w hc hT A hAc hAi pp qq e hpq hhol
  obtain ⟨uM, ν, 𝓤, hu⟩ := (H.uEx F E σ d R L).1
  obtain ⟨nb', lam', 𝓖', hc'⟩ := H.coefEx F E σ L.sd
  obtain ⟨t', hct⟩ := H.cTSplit F E σ d R L _ _ hsec hEis
  have hspl : ∀ z : ℂ, t' < z.re → ∃ c₂ : d.G → ℂ,
      (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x = _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c₂ x) ∧
      ∀ x, c₂ (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c₂ x := by
    intro z hz
    obtain ⟨c₂, h1, h2⟩ := hct z hz nb lam 𝓖 hc nb' lam' 𝓖' hc' uM ν 𝓤 hu T T' hT
    exact ⟨c₂, h1, fun x => h2 w 1 y x hy⟩
  let c2 : ℂ → d.G → ℂ := fun z => if h : t' < z.re then Classical.choose (hspl z h) else 0
  have hc2 : ∀ z : ℂ, t' < z.re → (∀ x, _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (d.eis (d.sec0 Φ) s z) T x =
      _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x + c2 z x) ∧
      ∀ x, c2 z (R.ι w y * x) = Complex.exp (((1 : ℝ) : ℂ) * (d.n - 2 * z)) * c2 z x := by
    intro z hz
    simp only [c2, dif_pos hz]
    exact Classical.choose_spec (hspl z hz)
  have havg_smul : ∀ (c : ℂ) (φ : d.G → ℂ) x', _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (fun g => c * φ g) T x' =
      c * _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 φ T x' := by
    intro c φ x'
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc, mul_assoc]
    simp only [integral_const_mul]
  have hhol1 := _root_.PositivityTheory.SiegelWeilFormula.AStep.avgHol_k H L hE hc T hT hu
  have hsep := lawSep U p (max t t') s j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x)
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T (R.ι w y * x))
    (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x) (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x))
    (fun z => c2 z x) (fun z => c2 z (R.ι w y * x)) (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)
    (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x)) (d.n : ℂ) (-2) hUo hR hs hp hj (hhol1 x).1 (hhol1 _).1
    (fun i hi => by
      rw [(hhol1 x).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun i hi => by
      rw [(hhol1 _).2 i]
      have : (fun g => iteratedDeriv i (Ê · g) s) = fun _ => 0 := funext fun g => hlow i hi g
      rw [this]; simp [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, fc])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 x])
    (fun z hz => by
      have h1 := (hfar z (lt_of_le_of_lt (le_max_left _ _) hz)).2
      have e1 : Ê z = fun g => p.eval z * d.eis (d.sec0 Φ) s z g := funext h1
      rw [e1, havg_smul, (hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).1 _])
    (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    (fun z hz => by
      rw [(hc2 z (lt_of_le_of_lt (le_max_right _ _) hz)).2 x]
      congr 1; push_cast; ring_nf)
  have havgA : ∀ x', iteratedDeriv j (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 (Ê z) T x') s = fc d.B.ψ d.b nb lam 𝓖 A T x' := by
    intro x'
    rw [(hhol1 x').2 j]
    show _root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k d L uM ν 𝓤 nb lam 𝓖 A T x' = _
    simp only [_root_.PositivityTheory.SiegelWeilFormula.AStep.avg_k, huA uM ν 𝓤 hu, setIntegral_const]
    simp [Measure.real, hu.2.2.2]
  rw [havgA, havgA] at hsep
  have hth : fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T (R.ι w y * x) = Complex.exp (d.m : ℂ) * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x := by
    have := valLaw (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' x)
      (fun z => _root_.PositivityTheory.SiegelWeilFormula.AStep.cOne_k d L (d.sec0 Φ) s z nb' lam' 𝓖' T' (R.ι w y * x)) 0 (d.n : ℂ) 2 s _ _
      (fun z _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneLaw_k H R L hΦ w hc' T' 1 y hy z x]; congr 1; push_cast; ring_nf)
      (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT x) (_root_.PositivityTheory.SiegelWeilFormula.AStep.cOneVal_k H R L R' hIH hΦ hv hc hc' hT _)
    have e2 : (d.n : ℂ) + 2 * s = d.m := by rw [hsdef, s0]; ring
    rw [e2] at this
    linear_combination this / 2
  have hA1 := hlawA 1 y hy x
  rw [Complex.ofReal_one, one_mul] at hA1
  rw [hfcB x]
  rw [hA1, hth] at hsep
  have e3 : (d.n : ℂ) + -2 * s = ((2 * d.n - d.m : ℕ) : ℂ) := by
    have h2 : ((2 * d.n - d.m : ℕ) : ℂ) = 2 * (d.n : ℂ) - d.m := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [h2, hsdef, s0]; ring
  rw [e3] at hsep
  have hne := exp_ne_of_lt hmn
  have key : (Complex.exp ((2 * d.n - d.m : ℕ) : ℂ) - Complex.exp (d.m : ℂ)) *
      (fc d.B.ψ d.b nb lam 𝓖 A T x - iteratedDeriv j (fun z => p.eval z) s * (2 * fc d.B.ψ d.b nb lam 𝓖 (d.I Φ) T x)) = 0 := by
    linear_combination -hsep
  rcases mul_eq_zero.1 key with h | h
  · exact absurd (sub_eq_zero.1 h) hne
  · exact h
end PositivityTheory.SiegelWeilFormula.AStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpLineD
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
def ev_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ :=
  2 * Real.pi * Complex.I * z.re * z.im * ((‖w‖ ^ 2 : ℝ) : ℂ) -
    4 * Real.pi * Complex.I * z.im * (⟪w, u⟫_ℝ + z.re * ((‖w‖ ^ 2 : ℝ) : ℂ)) +
    ((-(2 * Real.pi * (‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2)) : ℝ) : ℂ)
def bv_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ℂ := star (Complex.exp (_root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k w z u))
theorem norm_add_smul_sq_k (w u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (x : ℝ) :
    ‖u + x • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * x * ⟪w, u⟫_ℝ + x ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_comm]
  ring
theorem T_vline_k (hH : _root_.PositivityTheory.SiegelWeilFormula.THeis_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} {Ω : d.Fn} (hΩ : Ω ∈ d.sch) (hTΩ : d.T Ω = _root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k R g)
    {W : Mx F E d.m d.n} (hW : finOne F • W = 0) (z : ℂ) (X : Mx F E d.m d.n) :
    d.T (d.dd.rho d.B.ψ (_root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k R W z) Ω) X = _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R W) z (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.vline_k
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.T_rho_sum'_k hH hΩ, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_sp_k R hW, _root_.PositivityTheory.SiegelWeilFormula.KFP.psi_tw_k R hW, hTΩ]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.vac_k]
  rw [_root_.PositivityTheory.SiegelWeilFormula.KFP.gau_eq_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_add_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_realAd_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_add_of_k R (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_realAd_smul_k hW z.re)]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k]
  rw [show star (Complex.exp _) = Complex.exp (conj _) from (Complex.exp_conj _).symm, Complex.ofReal_exp,
    ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_add_smul_sq_k]
  simp only [map_add (f := _), map_sub, map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring
theorem continuous_bv_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) : Continuous (_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z) := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k _root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k
  refine continuous_star.comp (Complex.continuous_exp.comp ?_)
  fun_prop
theorem norm_bv_le_k (w : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) (z : ℂ) (u : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d) : ‖_root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k w z u‖ ≤ 1 := by
  unfold _root_.PositivityTheory.SiegelWeilFormula.KFP.bv_k
  rw [norm_star, Complex.norm_exp]
  apply Real.exp_le_one_iff.2
  have h : ‖u‖ ^ 2 + 2 * z.re * ⟪w, u⟫_ℝ + z.re ^ 2 * ‖w‖ ^ 2 ≥ 0 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KFP.norm_add_smul_sq_k]
    positivity
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.ev_k, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, Complex.add_im, Complex.mul_im]
  nlinarith [Real.pi_pos]
end PositivityTheory.SiegelWeilFormula.KFP
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopLocJJ
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace RD
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.locOp_nbar_of (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) {ε : ℤˣ} {w₀ : d.G} (hw₀ : d.IsW ε w₀)
    {C s : ℂ} {B : d.MF → d.MF} (hW' : R.StepOK w w₀ (locFT C s) B) :
    ∃ κ : ℂ, κ ≠ 0 ∧
      (∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f) ∧
      (∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f))))) ∧
      ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        locFT C s (L y f) = chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f) := by
  have hsch := d.om_sch
  have h4 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hW'
  rw [_root_.PositivityTheory.SiegelWeilFormula.RD_k.w_four hw₀] at h4
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hΨ.2.1 (funext hc)
  have hB4 : d.IsAwayW w (B (B (B (B Ψ)))) := (h4.2 Ψ hΨ.1).1
  have key : ∀ f : d.LF, IsSw f → ∀ X, f (R.loc w X) * Ψ X =
      locFT C s (locFT C s (locFT C s (locFT C s f))) (R.loc w X) * B (B (B (B Ψ))) X := by
    intro f hf X
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e := (h4.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    rw [map_one, Module.End.one_apply, hT'] at e
    exact congrFun e X
  have key0 : ∀ f : d.LF, IsSw f → ∀ u, f u * Ψ X₀ =
      locFT C s (locFT C s (locFT C s (locFT C s f))) u * B (B (B (B Ψ))) X₀ := by
    intro f hf u
    obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
    have := key f hf (X₀ + Z)
    rwa [hZ3, hΨ.1 X₀ Z hZ1 hZ2, hB4 X₀ Z hZ1 hZ2] at this
  by_cases hb : B (B (B (B Ψ))) X₀ = 0
  · have hz : ∀ f : d.LF, IsSw f → f = 0 := by
      intro f hf
      funext u
      have := key0 f hf u
      rw [hb, mul_zero] at this
      exact (mul_eq_zero.mp this).resolve_right hX₀
    refine ⟨1, one_ne_zero, fun f hf => ?_, fun y c hc hy f hf => ?_, fun y c hc hy f hf => ?_⟩
    · rw [hz f hf]
      simp [locFT_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
    · rw [hz f hf, R.locOp_zero hT hG hL y]
      simp [locFT_zero, chirp_zero]
  · set κ := Ψ X₀ / B (B (B (B Ψ))) X₀ with hκ
    have hκ0 : κ ≠ 0 := div_ne_zero hX₀ hb
    have h4f : ∀ f : d.LF, IsSw f → locFT C s (locFT C s (locFT C s (locFT C s f))) = κ • f := by
      intro f hf
      funext u
      have := key0 f hf u
      simp only [Pi.smul_apply, smul_eq_mul, hκ]
      field_simp
      linear_combination -this
    have hmain : ∀ (y : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ), cᴴ = c → mR y = nbLoc c → ∀ f, IsSw f →
        IsSw (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)) ∧
        L y f = κ⁻¹ • locFT C s (locFT C s (locFT C s
          (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) (locFT C s f)))) := by
      intro y c hc hy f hf
      obtain ⟨y', hy', hrel⟩ := R.oppositeUnipotent_weylConj w hw₀ y c hc hy
      have hx : ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)ᴴ = (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c := by
        have hs : star (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) = ((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹ := by
          rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩
          · rw [hz]; simp
          · rw [hz]; simp [Complex.inv_I]
        rw [Matrix.conjTranspose_smul, hc, hs]
      have hN : R.StepOK w (R.ι w y') (chirp ((R.sg w : ℤ) : ℂ) ((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c)) id :=
        R.stepN w hT y' _ hx hy'
      refine ⟨hN.1 _ (hW'.1 f hf), ?_⟩
      by_cases hf0 : ∀ u, f u = 0
      · have : f = 0 := funext hf0
        rw [this, R.locOp_zero hT hG hL y]
        simp [locFT_zero, chirp_zero]
      push Not at hf0
      obtain ⟨u₀, hu₀⟩ := hf0
      have hBΨ : ∀ X, B (B (B (B Ψ))) X = κ⁻¹ * Ψ X := by
        intro X
        obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X u₀
        have := key f hf (X + Z)
        rw [hZ3, hΨ.1 X Z hZ1 hZ2, hB4 X Z hZ1 hZ2, h4f f hf] at this
        simp only [Pi.smul_apply, smul_eq_mul] at this
        rw [eq_inv_mul_iff_mul_eq₀ hκ0]
        apply mul_left_cancel₀ hu₀
        linear_combination -this
      have hc3 := R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch (R.step_comp w hsch hW' hW') hW') hN) hW'
      obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
      have e := (hc3.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
      have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
      rw [hrel] at e1
      apply R.tens_cancel hΨ.1 hΨ.2.1
      rw [← e1, e]
      funext X
      simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, Function.comp_apply, id, Pi.smul_apply, smul_eq_mul, hBΨ]
      ring
    refine ⟨κ, hκ0, h4f, fun y c hc hy f hf => (hmain y c hc hy f hf).2,
      fun y c hc hy f hf => ?_⟩
    obtain ⟨hsw, heq⟩ := hmain y c hc hy f hf
    rw [heq, locFT_smul, h4f _ hsw, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
theorem _root_.PositivityTheory.SiegelWeilFormula.RD_k.localOperator_longWeyl_integral (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hG : _root_.PositivityTheory.SiegelWeilFormula.GoodAwayEx_k) (hL : R.IsLocOp w L) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ y : GR d.n, mR y = JJ d.n → ∀ f, IsSw f → L y f 0 = C * ∫ v, f v := by
  obtain ⟨-, ⟨ε, w₀, hw₀, -⟩, -⟩ := hA F E σ d
  have hεR : ε = R.ε := R.isW_eps w hw₀
  obtain ⟨C₀, B, hC₀, hW⟩ := R.stepW_exp w hT hA ε w₀ hw₀
  set s : ℂ := -2 * ((ε : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ) / R.ζ with hs_def
  have hW' : R.StepOK w w₀ (locFT C₀ s) B := hW
  obtain ⟨κ, hκ, -, hnb, -⟩ := R.locOp_nbar_of hT hG hL hw₀ hW'
  have hk : ((R.sg w : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (Units.ne_zero _)
  have hζn : ‖R.ζ‖ = 1 := by
    rcases R.hζ with ⟨-, hz⟩ | ⟨-, hz⟩ <;> rw [hz] <;> simp
  have hunit : ∀ u : ℤˣ, ‖((u : ℤ) : ℂ)‖ = 1 := fun u => by
    rcases Int.units_eq_one_or u with h | h <;> rw [h] <;> simp
  have hsn : ‖s‖ = 2 * |((R.sg w : ℤ) : ℝ)| := by
    have h1 : |((R.sg w : ℤ) : ℝ)| = 1 := by
      rcases Int.units_eq_one_or (R.sg w) with h | h <;> rw [h] <;> simp
    rw [h1, hs_def, norm_div, norm_mul, norm_mul, hunit, hunit, hζn]
    norm_num
  obtain ⟨c, hc, hfres⟩ := _root_.GlobalTheory.CompanionTheory.Kloc.Fresnel.value_at_zero d.m d.n C₀ s ((R.sg w : ℤ) : ℝ) hC₀ hk hsn
  refine ⟨κ⁻¹ * c, mul_ne_zero (inv_ne_zero hκ) hc, fun y hy f hf => ?_⟩
  obtain ⟨y₁, y₂, h1, h2, rfl⟩ := jj_split y hy
  have hb1 : (1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = 1 := Matrix.conjTranspose_one
  have hbm : (-1 : Matrix (Fin d.n) (Fin d.n) ℂ)ᴴ = -1 := by rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_one]
  have hf1 : IsSw (L y₁ f) := (hL y₁ f hf).1
  have hf2 : IsSw (L y₂ (L y₁ f)) := (hL y₂ _ hf1).1
  rw [R.locOp_mul hT hG hL (y₁ * y₂) y₁ f hf, R.locOp_mul hT hG hL y₁ y₂ _ hf1,
    R.locOp_nU hT hG hL y₁ 1 hb1 h1 _ hf2, hnb y₂ (-1) hbm h2 _ hf1, R.locOp_nU hT hG hL y₁ 1 hb1 h1 f hf]
  have hx : (((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • (-1 : Matrix (Fin d.n) (Fin d.n) ℂ) = 1 := by
    rw [hεR]
    rcases R.hζ with ⟨he, hz⟩ | ⟨he, hz⟩ <;> rw [he, hz] <;> simp [Complex.inv_I]
  rw [hx]
  obtain ⟨φ, hφ⟩ := hf
  have hch : ∀ g : d.LF, chirp ((R.sg w : ℤ) : ℂ) (1 : Matrix (Fin d.n) (Fin d.n) ℂ) g =
      fun u => Complex.exp (2 * Real.pi * Complex.I * (((R.sg w : ℤ) : ℝ) : ℂ) *
        Matrix.trace ((Matrix.of u)ᴴ * Matrix.of u)) * g u := fun g => by
    funext u
    simp [chirp]
  have hin : (fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) * ((Matrix.of u)ᴴ * Matrix.of u))) * f u) =
      chirp ((R.sg w : ℤ) : ℂ) 1 f := rfl
  have h0 : Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace ((1 : Matrix (Fin d.n) (Fin d.n) ℂ) *
        ((Matrix.of (0 : Fin d.m → Fin d.n → ℂ))ᴴ * Matrix.of (0 : Fin d.m → Fin d.n → ℂ)))) = 1 := by
    simp
  simp only [hin]
  rw [h0, one_mul, Pi.smul_apply, smul_eq_mul, hch, hch, ← hφ]
  have := hfres φ
  simp only [locFT] at this ⊢
  rw [this, hφ]
  ring
end RD
end PositivityTheory.SiegelWeilFormula
end
end
end

