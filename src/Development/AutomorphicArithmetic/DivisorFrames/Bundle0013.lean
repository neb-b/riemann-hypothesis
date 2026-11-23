module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AutomorphicArithmetic.DivisorFrames.ThetaTransformFockModelEqOfStandardChar
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianDatumFlippedFiniteTensorBigRoute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ThetaLiftPureTensorOfIsFinF
section
section SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (At evI realAd SInf ActsD piInf Spc Model)
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealDict GlobalTheory.RealDict.FockMap

private theorem finPart_ne {F : Type} [Field F] [NumberField F] {n d : ℕ}
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n × Fin d → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hs : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) :
    ∃ y, GlobalTheory.BigNZ.finPartFn φ y ≠ 0 := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (h0 v)
  have hS := Filter.eventually_cofinite.1 hs
  let y : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  refine ⟨y, ?_⟩
  refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
  by_cases hv : v ∈ hS.toFinset
  · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
    rw [this]
    exact hξ v
  · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
    rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
    exact one_ne_zero


set_option maxHeartbeats 1000000 in
private theorem fock_of {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {ε : Bool} {M X : HSp D} {Xs : Spc D.host.F D.host.E M.rank}
    {Ws : Spc D.host.F D.host.E X.rank} (Mo : Model D.sp.cm.sig Xs Ws)
    (hψ : IsStdChar D ψ (-1)) {θ : InfFam D} (hθ : IsInfFam θ) (A : Fr M) (B : Fr X)
    {τ : ∀ w : InfinitePlace D.host.F, EmbOver D.host.E w} (hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hStd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) (hX : Xs.J = sgE (D := D) ε • M.gram)
    (hW : Ws.J = D.host.xi0 • (X.gramᵀ).submatrix (Equiv.refl (Fin X.rank)) (Equiv.refl (Fin X.rank)))
    (hM : Mo.IsGood ψ) (h2X : ∀ w, Xs.θ w * Xs.θ w = 1) (h2W : ∀ w, Ws.θ w * Ws.θ w = 1)
    (hc : ∀ w, ∃ t, (∀ x, (τ w).1 x = conj (tauE D t x)) ∧ Xs.θ w = (if ε then 1 else -1 : ℂ) • A.cart t ∧
      Ws.θ w = (B.cart t).map conj)
    (g₀ : SInf D.host.F (Fin M.rank × Fin X.rank)) (g0 : g₀ ≠ 0)
    {g : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ} (hg : g ∈ SB _) (hy : ∃ y, g y ≠ 0)
    (hv : IsVacF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g))) :
    ∃ Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank),
      LinearMap.range Φ = Mo.Pol ψ τ ∧
      ∀ g' : (Fin M.rank × Fin X.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) → ℂ, g' ∈ SB _ →
        ∀ P, th ψ ε Mo (pureA D.host.F (Φ P) g') = ptF ψ θ (frSgn ε A) B (th ψ ε Mo (pureA D.host.F g₀ g')) P := by
  obtain ⟨-, -, tinj, tth, -⟩ := th_laws Mo hψ hθ hX hW hM
  obtain ⟨Dr, hD1, hD2, hD3⟩ := exists_der Mo hStd
  obtain ⟨y, hy⟩ := hy
  obtain ⟨Θ, hΘ⟩ : ∃ Θ, Θ = thL Mo hψ hθ hX hW hM hg := ⟨_, rfl⟩
  have hΘ' : ∀ f : SInf D.host.F (Fin M.rank × Fin X.rank), th ψ ε Mo (pureA D.host.F f g) = Θ f := fun f => by rw [hΘ]; rfl
  rw [hΘ'] at hv
  have hd : ∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f) :=
    hΘ ▸ dRho_thL Mo hψ hθ hX hW hM hD1 hg
  have hi : Function.Injective Θ := fun f f' h => by
    have e := tinj _ (pureA_mem f hg) _ (pureA_mem f' hg) (by rw [hΘ] at h; exact h)
    refine DFunLike.ext _ _ fun a => ?_
    have e2 := congrFun e (GlobalTheory.RealLift.ptAt a y)
    rw [GlobalTheory.RealLift.pureA_ptAt, GlobalTheory.RealLift.pureA_ptAt] at e2
    exact mul_right_cancel₀ hy e2
  have hg₀ : ∀ t z, Dr (dir ε M X θ t z) g₀ +
      Complex.I • Dr (dir ε M X θ t (cplxO ((frSgn ε A).cart t) (B.cart t) z)) g₀ = 0 := fun t z => hi (by
    have h : annih (heisO ψ (sgn ε M) X) θ t (cplxO ((frSgn ε A).cart t) (B.cart t)) z (Θ g₀) = 0 := hv.2 t z
    rw [annih, hd, hd, ← map_smul, ← map_add (f := _)] at h
    rw [h, map_zero])
  let um : FVar D X.rank M.rank → Matrix (Fin X.rank) (Fin M.rank) ℂ := fun k =>
    Formalism.IndefR.Datum.unitMap ((frSgn ε A).onb k.1) (B.onb k.1) k.2.1 k.2.2
  let Cr : FVar D X.rank M.rank → SInf D.host.F (Fin M.rank × Fin X.rank) → SInf D.host.F (Fin M.rank × Fin X.rank) :=
    fun k f => ((fockScale D k.1 : ℂ)⁻¹) • (Dr (dir ε M X θ k.1 (um k)) f -
      Complex.I • Dr (dir ε M X θ k.1 (cplxO ((frSgn ε A).cart k.1) (B.cart k.1) (um k))) f)
  let Φ : PolF D X.rank M.rank →ₗ[ℂ] SInf D.host.F (Fin M.rank × Fin X.rank) :=
    (MvPolynomial.basisMonomials _ ℂ).constr ℂ fun k => (Multiset.toList (Finsupp.toMultiset k)).foldr Cr g₀
  have hΦ : ∀ Θ : SInf D.host.F (Fin M.rank × Fin X.rank) →ₗ[ℂ] (WO (sgn ε M) X → ℂ),
      (∀ t z f, Formalism.IndefR.Datum.dRho (heisO ψ (sgn ε M) X) θ t z (Θ f) = Θ (Dr (dir ε M X θ t z) f)) →
      Θ ∘ₗ Φ = pureTensorO ψ θ (sgn ε M) X (frSgn ε A).cart B.cart (frSgn ε A).onb B.onb (Θ g₀) := by
    intro Θ hd
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorO, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih, aPlusAll, Formalism.IndefR.Datum.aPlus, crea, hd, hd, ← map_smul, ← map_sub,
        ← map_smul]
  have hΦ' : ∀ P, Θ (Φ P) = ptF ψ θ (frSgn ε A) B (Θ g₀) P := fun P => LinearMap.congr_fun (hΦ Θ hd) P
  have hsum : ∀ u, At (evI D.host.F) u → ∀ f, Dr u f =
      ∑ t, Dr (dir ε M X θ t (compAt θ t (toO (sgn ε M).gram u))) f := fun u hu f => by
    rw [← hD3 _ _ _ fun t => dir_at hθ t _, ← eq_sum_dir hθ hu]
  have hG : Mo.IsGauss ψ τ g₀ := ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => by
    rw [hD2 u hu _ _ hf, hD2 u' hu' _ _ hf', hsum u hu, hsum u' hu', Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [compAt_cplx hθ A B hc (fun w => by simpa using hrel w) t,
      eq_neg_of_add_eq_zero_left (hg₀ t (compAt θ t (toO (sgn ε M).gram u))), smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]⟩
  have hP : ∀ u, At (evI D.host.F) u → ∀ f ∈ Mo.Pol ψ τ, Dr u f ∈ Mo.Pol ψ τ := fun u hu f hf =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ (hD1 u hu f)
  refine ⟨Φ, le_antisymm ?_ (sInf_le ⟨fun f hf => ?_, ?_⟩), fun g' hg' P =>
    LinearMap.congr_fun (hΦ (thL Mo hψ hθ hX hW hM hg') (dRho_thL Mo hψ hθ hX hW hM hD1 hg')) P⟩
  · rw [Module.Basis.constr_range, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    induction (Finsupp.toMultiset k).toList with
    | nil => exact Submodule.mem_sInf.2 fun N hN => hN.1 g₀ hG
    | cons i l ih =>
      exact Submodule.smul_mem _ _ (sub_mem (hP _ (dir_at hθ _ _) _ ih) (Submodule.smul_mem _ _ (hP _ (dir_at hθ _ _) _ ih)))
  · obtain ⟨z, rfl⟩ := gauss_line Mo ψ τ hCM hStd h2X h2W f g₀ hG g0 hf
    exact Submodule.smul_mem _ z ⟨1, hi ((hΦ' 1).trans (GlobalTheory.LieScalar.ptF_one _ _ _))⟩
  · rintro u hu _ ⟨P, rfl⟩ f₁ h1
    rw [hD2 u hu _ _ h1, hsum u hu]
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨Q, hQ⟩ := dRho_ptF (frSgn ε A) B hψ hθ hv t (compAt θ t (toO (sgn ε M).gram u)) P
    exact ⟨Q, hi (by rw [← hd, hΦ', hΦ', hQ])⟩

end SlopeTestRemainingChoices

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Geo piW chrW unifAt latAtV At SInf)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime IsSplitBasis)
open GlobalTheory.BotMatch (evW)
open GlobalTheory.StageGeo
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.thetaLift_pure_tensor_of_isFinF :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (hd : d = X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X (finCongr hd) Bs Vs Ws M → ∀ (θ : InfFam D), IsInfFam θ →
        ∀ (A : Fr S) (B : Fr X), IsCart ε A B (finCongr hd) Bs Vs Ws →
        ∀ (g : SInf D.host.F (Fin S.rank × Fin d)), g ≠ 0 →
        ∀ (φ₀ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ₀ v ∈ GlobalTheory.WeilM.SB _) →
        (∀ᶠ v in Filter.cofinite, φ₀ v = M.vac v) → (∀ v, φ₀ v ≠ 0) →
        IsFinF ψ θ ε A B (thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ₀)) →
        ∃ Φ : PolF D X.rank S.rank →ₗ[ℂ] SInf D.host.F (Fin S.rank × Fin d), LinearMap.range Φ = M.Pol Bs.ψ Bs.emb ∧
          ∀ (φ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (Fin S.rank × Fin d → Fv D.host.F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
            (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → ∀ P,
            thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Φ P) φ) =
              fockF ψ θ ε A B (thO M ψ (sgn ε S).gram (finCongr hd) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ)) P := by
  intro D ψ ε S X d hd Bs Vs Ws M hP θ hθ A B hc g g0 φ₀ hφ hφ' hφ0 hv
  subst hd
  obtain ⟨hBs, hψe, hX, hW, ⟨r, s, hV⟩, ⟨r', s', hWs⟩, hM⟩ := hP
  subst hψe
  have hψ : IsStdChar D Bs.ψ (-1) := GlobalTheory.StdCharFromIsStd.isStdChar_of_isStd D Bs.ψ hBs.std
  have hF : GlobalTheory.BigNZ.Fam M φ₀ := ⟨hφ, hφ'⟩
  obtain ⟨Φ, h1, h2⟩ := fock_of M hψ hθ A B hBs.cm hBs.std hX hW hM (fun w => (hV.cartan w).1)
    (fun w => (hWs.cartan w).1) hc g g0 (hF.sb hM) (finPart_ne φ₀ hφ0 (hF.std hM)) hv
  refine ⟨Φ, h1, fun φ hs hs' P => ?_⟩
  have hF' : GlobalTheory.BigNZ.Fam M φ := ⟨hs, hs'⟩
  exact h2 _ (hF'.sb hM) P
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.VectorValuedAutFormEquivariantInfiniteComponent
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem UpperTheory.infinite_matrix_rational {D : D7} {V : HSp D}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ)
    (h : GA D V) (γ₀ : GL (Fin V.rank) D.host.E)
    (e : matHom V h = Matrix.GeneralLinearGroup.map (incA D) γ₀) (τ : D.what₂.Tau) :
    Formalism.MainNotions.StandardLattice.infMat D.sp.cm.sig V.gram (θ τ) h =
      (Matrix.GeneralLinearGroup.map (tauE D τ) γ₀ : GL (Fin V.rank) ℂ).val := by
  have e' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat _ D.sp.cm.sig V.gram h = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e
  unfold Formalism.MainNotions.StandardLattice.infMat
  rw [e']
  ext a b
  change θ τ (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ⊗ₜ[D.host.F] γ₀.val a b)) = tauE D τ (γ₀.val a b)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  exact (hθ τ).1 _

private theorem UpperTheory.exists_conjugate_embedding {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (σ ε : E →+* ℂ)
    (hε : ε = σ ∨ ε = ComplexEmbedding.conjugate σ) (A : Matrix (Fin n) (Fin n) ℂ) (hA : IsUnit A) :
    ∃ B : GL (Fin n) ℂ, ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val = A * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * A⁻¹ →
      Matrix.GeneralLinearGroup.map ε γ₀ = B * cEmb ε x * B⁻¹ := by
  obtain ⟨B, rfl⟩ := hA
  have key : ∀ (x : UA E n) (γ₀ : GL (Fin n) E),
      (Matrix.GeneralLinearGroup.map σ γ₀ : GL (Fin n) ℂ).val =
        B.val * (cEmb σ x : Matrix (Fin n) (Fin n) ℂ) * (B.val)⁻¹ →
      Matrix.GeneralLinearGroup.map σ γ₀ = B * cEmb σ x * B⁻¹ := fun x γ₀ h => by
    apply Units.ext
    rw [h, Units.val_mul, Units.val_mul, Matrix.coe_units_inv]
  rcases hε with rfl | rfl
  · exact ⟨B, key⟩
  · refine ⟨Matrix.GeneralLinearGroup.map (starRingEnd ℂ) B, fun x γ₀ h => ?_⟩
    have h1 := congrArg (Matrix.GeneralLinearGroup.map (starRingEnd ℂ)) (key x γ₀ h)
    rw [map_mul, map_mul, map_inv] at h1
    have h2 : Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (cEmb σ x) = cEmb (ComplexEmbedding.conjugate σ) x := by
      ext a b
      exact (GlobalTheory.DefiniteBC.coord_conjugate σ _).symm
    rw [h2] at h1
    rw [← h1]
    ext a b
    rfl

private theorem UpperTheory.weight_operator_conjugate {n : ℕ} {ι : Type} [Fintype ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)
    (B C G : ι → GL (Fin n) ℂ) (h : G = B * C * B⁻¹) (u : NablaT ℂ n mu) :
    wtOp ℂ n mu sh B⁻¹ (wtOp ℂ n mu sh G u) = wtOp ℂ n mu sh C (wtOp ℂ n mu sh B⁻¹ u) := by
  classical
  rw [h, ← Module.End.mul_apply, ← wtOp_mul, ← mul_assoc, inv_mul_cancel_left, wtOp_mul]
  rfl

private theorem UpperTheory.monoidHom_kernel_invariance {G H K : Type} [Monoid G] [Monoid H] [Monoid K] (j : G →* H) (φ : H →* K)
    (g x : G) (h : H) (hx : φ (j x) = 1) : φ (j (g * x) * h) = φ (j g * h) := by
  simp only [map_mul, hx, mul_one]

theorem UpperTheory.vectorValued_autForm_equivariant_infinite_component :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
        (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V), IsInfFam θ → GlobalTheory.DefTransfer.IsTransfer V θ j h₀ →
        ∀ (emb : D.what₂.Tau → (D.host.E →+* ℂ)), (∀ τ, emb τ = tauE D τ ∨ emb τ = ComplexEmbedding.conjugate (tauE D τ)) →
        ∀ (mu : D.what₂.Tau → ℕ → ℕ) (sh : D.what₂.Tau → ℤ) (Fm : Bridge.Gf V → NablaT ℂ V.rank mu), Fm ≠ 0 →
        (∀ (γ : GQ V) (γ₀ : GL (Fin V.rank) D.host.E), matHom V γ = Matrix.GeneralLinearGroup.map (incA D) γ₀ → ∀ g,
          Fm (Bridge.ratF V γ * g) = wtOp ℂ V.rank mu sh (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) (Fm g)) →
        (∀ᶠ κ in nhds (1 : GA D V), ∀ g, Fm (g * (finHom V).rangeRestrict κ) = Fm g) →
        ∃ F1 : UA D.host.E V.rank → NablaT ℂ V.rank mu, F1 ≠ 0 ∧
          (∀ γ ∈ ratU D.host.E V.rank, ∀ g, F1 (γ * g) = wtOp ℂ V.rank mu sh (fun τ => cEmb (emb τ) γ) (F1 g)) ∧
          (∀ x ∈ infU D.host.E V.rank, ∀ g, F1 (g * x) = F1 g) ∧ (∀ᶠ y in nhds (1 : UA D.host.E V.rank), ∀ g, F1 (g * y) = F1 g) ∧
          ∃ A : Module.End ℂ (NablaT ℂ V.rank mu), ∀ x, F1 x = A (Fm ((finHom V).rangeRestrict (j x * h₀))) := by
  intro D _ V θ j h₀ hθ hT emb hemb mu sh Fm hF hrat hlev
  classical
  obtain ⟨-, hQ, -, hI, ⟨A, hA, hAe⟩, -⟩ := hT
  choose B hB using fun τ => UpperTheory.exists_conjugate_embedding (tauE D τ) (emb τ) (hemb τ) (A τ) (hA τ)
  refine ⟨fun x => wtOp ℂ V.rank mu sh B⁻¹ (Fm ((finHom V).rangeRestrict (j x * h₀))), ?_, ?_, ?_, ?_, _, fun _ => rfl⟩
  · intro h0
    apply hF
    funext g
    obtain ⟨k, rfl⟩ := (finHom V).rangeRestrict_surjective g
    have h1 := congrArg (wtOp ℂ V.rank mu sh B) (congrFun h0 (j.symm (k * h₀⁻¹)))
    simp only [ContinuousMulEquiv.apply_symm_apply, inv_mul_cancel_right, Pi.zero_apply, map_zero] at h1
    rw [← Module.End.mul_apply, ← wtOp_mul, mul_inv_cancel, wtOp_one] at h1
    exact h1
  · intro γ hγ g
    have hj : j γ ∈ GQ V := (hQ γ).1 hγ
    obtain ⟨γ₀, -, e⟩ := id hj
    have e' : matHom V (j γ) = Matrix.GeneralLinearGroup.map (incA D) γ₀ := e.symm
    have h1 := hrat ⟨j γ, hj⟩ γ₀ e' ((finHom V).rangeRestrict (j g * h₀))
    have h2 : (finHom V).rangeRestrict (j (γ * g) * h₀) =
        Bridge.ratF V ⟨j γ, hj⟩ * (finHom V).rangeRestrict (j g * h₀) := by
      have h4 : j (γ * g) * h₀ = j γ * (j g * h₀) := by rw [map_mul, mul_assoc]
      exact (congrArg (finHom V).rangeRestrict h4).trans (map_mul (finHom V).rangeRestrict _ _)
    have h3 : (fun τ => Matrix.GeneralLinearGroup.map (emb τ) γ₀) = B * (fun τ => cEmb (emb τ) γ) * B⁻¹ := by
      funext τ
      exact hB τ γ γ₀ ((UpperTheory.infinite_matrix_rational θ hθ _ γ₀ e' τ).symm.trans (hAe τ γ))
    exact (congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm h2).trans h1)).trans
      (UpperTheory.weight_operator_conjugate mu sh B _ _ h3 _)
  · intro x hx g
    have hj : finHom V (j x) = 1 := (hI x).1 hx
    have h1 : (finHom V).rangeRestrict (j x) = 1 := Subtype.ext hj
    exact congrArg (fun z => wtOp ℂ V.rank mu sh B⁻¹ (Fm z))
      (UpperTheory.monoidHom_kernel_invariance j.toMulEquiv.toMonoidHom (finHom V).rangeRestrict g x h₀ h1)
  · have hc : Continuous fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀ :=
      (continuous_const.mul j.continuous).mul continuous_const
    have ht : Filter.Tendsto (fun y : UA D.host.E V.rank => h₀⁻¹ * j y * h₀) (nhds 1) (nhds 1) := by
      exact hc.tendsto' 1 1 (by simp only [map_one, mul_one, inv_mul_cancel])
    filter_upwards [ht.eventually hlev] with y hy g
    have h1 : j (g * y) * h₀ = j g * h₀ * (h₀⁻¹ * j y * h₀) := by
      rw [map_mul]
      group
    exact congrArg (wtOp ℂ V.rank mu sh B⁻¹) ((congrArg Fm ((congrArg (finHom V).rangeRestrict h1).trans
      (map_mul (finHom V).rangeRestrict _ _))).trans (hy _))
end

