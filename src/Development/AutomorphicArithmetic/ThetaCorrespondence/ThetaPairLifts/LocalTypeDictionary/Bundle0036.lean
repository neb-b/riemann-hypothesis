module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0033
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsGaussianOfFockVacuumStabilizerActs
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
namespace GlobalTheory.FockVacStab
theorem isGaussian_of_fock_vacuum_stabilizer_acts : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f₀ hG f₁ hact
  have hPA := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff _ using hD
  obtain ⟨Dk, _, hDk⟩ := hPA.2.1 k hk
  have hGP : ∀ g, M.IsGauss B.ψ B.emb g → g ∈ M.Pol B.ψ B.emb := fun g h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 g h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hAt : ∀ (a : Matrix (Fin n) (Fin n) (AE F E)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
      At (evI F) (a * u) := fun a u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨hkk, hkk'⟩ := mat_mul_mat_inv k
  have hcomm : ∀ w, (mat k⁻¹).map (piInf (B.emb w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
    intro w
    set A := (mat k).map (piInf (B.emb w))
    set A' := (mat k⁻¹).map (piInf (B.emb w))
    have h1 : A * A' = 1 := by
      rw [← Matrix.map_mul, hkk]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : A' * A = 1 := by
      rw [← Matrix.map_mul, hkk']; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hc : A * X.θ w = X.θ w * A := hk.2 w
    calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [h1, Matrix.mul_one]
      _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A' * (A * X.θ w) * A' := by rw [hc]
      _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
      _ = X.θ w * A' := by rw [h2, Matrix.one_mul]
  obtain ⟨ε, hε⟩ := hG
  refine ⟨ε, fun u u' hu hu' huu' f f' hf hf' => ?_⟩
  set v := mat k⁻¹ * u
  set v' := mat k⁻¹ * u'
  have hv : At (evI F) v := hAt _ u hu
  have hv' : At (evI F) v' := hAt _ u' hu'
  have hvv' : ∀ w, v'.map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * v.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    simp only [v, v', Matrix.map_mul, huu' w, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm w]
  have hkv : mat k * v = u := by simp only [v, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hkv' : mat k * v' = u' := by simp only [v', ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hgg : Dfun v' f₀ = Complex.I • Dfun v f₀ :=
    hε v v' hv hv' hvv' _ _ ((hDiff v hv f₀ _).2 rfl) ((hDiff v' hv' f₀ _).2 rfl)
  have hf0 : f₀ ∈ M.Pol B.ψ B.emb := hGP f₀ ⟨ε, hε⟩
  have hmove : ∀ x, At (evI F) x → ActsD (evI F) (M.heisLine B.ψ (mat k * x)) f₁ (Dk (Dfun x f₀)) := by
    intro x hx
    exact GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k hk x hx f₀ (Dfun x f₀) f₁ (Dk (Dfun x f₀))
      ((hDiff x hx f₀ _).2 rfl) hact ((hDk _ (hclos x hx f₀ hf0) _).2 rfl)
  have e1 : f = Dk (Dfun v f₀) := by
    have a := (hDiff u hu f₁ f).1 hf
    have b := (hDiff u hu f₁ _).1 (hkv ▸ hmove v hv)
    rw [a, b]
  have e2 : f' = Dk (Dfun v' f₀) := by
    have a := (hDiff u' hu' f₁ f').1 hf'
    have b := (hDiff u' hu' f₁ _).1 (hkv' ▸ hmove v' hv')
    rw [a, b]
  rw [e2, e1, hgg, map_smul]
end GlobalTheory.FockVacStab
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  first | exact @_root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | exact _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | (intros; apply _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteAlgebraClosedUnderDerivation
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KFinAlg
theorem polynomial_vector_kFinite (fockFirst : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∃ (A : InfinitePlace F → Matrix (Fin a) (Formalism.BasicNotions.TH.Ix (a - Γ.p) Γ.p) ℂ)
      (Φ : GlobalTheory.RealLift.Tens F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a')))
      (c : InfinitePlace F → ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame ((1 : ℂ) • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w))) (A w)) ∧
      (∀ w, Γ.V.θ w * A w = A w * Formalism.BasicNotions.TH.Jm (a - Γ.p) Γ.p) ∧
      LinearMap.range Φ = Γ.M.Pol Bs.ψ Bs.emb ∧
      GlobalTheory.RealLift.ActsBy Bs.emb A (om.comp (MonoidHom.inl _ _)) Φ
        (Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) c) : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ f ∈ Γ.M.Pol Bs.ψ Bs.emb,
    ∃ P : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))), FiniteDimensional ℂ P ∧ P ≤ Γ.M.Pol Bs.ψ Bs.emb ∧
      f ∈ P ∧ ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ g ∈ P, ∃ g₁ ∈ P,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) (⇑g) (⇑g₁) := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT f hf
  classical
  obtain ⟨A, Φ, c, hA, hAθ, hr, hact⟩ := fockFirst hPr F E σ Bs a a' Γ Xc om om' hT
  have hb := hT.base
  have hwp : GlobalTheory.WeilM.IsUWeilPair (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.WeilM.adeleClass F) Bs.ψ (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.W.J) Γ.M.co Xc.β (Xc.β / Xc.α) om := hT.weil
  have hadm := fun g => (hwp.isUSplitting).adm g
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain ⟨D, hD⟩ := exists_tensDeg T
  haveI : FiniteDimensional ℂ (tensDeg F (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) D) :=
    LinearMap.finiteDimensional_range _
  refine ⟨(tensDeg F _ _ _ _ D).map Φ, inferInstance, hr ▸ LinearMap.map_le_range, ⟨T, hD, rfl⟩, ?_⟩
  rintro k hk _ ⟨T', hT', rfl⟩
  obtain ⟨γ, hγ, Yg, hgen, hKC, hγ1⟩ := GlobalTheory.RealLift.kLine_of_lineEx _root_.GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin a) _ _ Bs.emb
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Γ.V.J) 1 A Γ.V.θ hb.cm hA hAθ k hk.1 hk.2
  let L := GlobalTheory.RealLift.sumPl (fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
    (c w * (Yg w).trace) • (1 : Module.End ℂ _))
  have hloc : GlobalTheory.RealLift.LocFin L := GlobalTheory.RealLift.locFin_sumPl _ _ _ fun w v => by
    obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights _ _ _ _).1 v
    exact ⟨W, hW, hv, fun y hy => W.add_mem (hs (Yg w) (hKC w) y hy) (W.smul_mem _ hy)⟩
  obtain ⟨U, hexp, hSA⟩ := _root_.GlobalTheory.ExpAct.expAct_fock F (Fin a × Fin (a + a')) _ Φ L ((om.comp (MonoidHom.inl _ _)).comp γ) hloc
    (fun t l hl => hadm _ l hl) (fun T => hact γ hγ Yg hgen T)
  let Lw : ∀ w : InfinitePlace F, Module.End ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun w => Formalism.BasicNotions.TH.fockAct1 (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q) (Yg w) +
      (c w * (Yg w).trace) • (1 : Module.End ℂ _)
  let Nw : ∀ w : InfinitePlace F, Submodule ℂ (Formalism.BasicNotions.TH.Pol (a - Γ.p) Γ.p (a + a' - (Γ.p + Γ.q)) (Γ.p + Γ.q)) :=
    fun _ => MvPolynomial.restrictTotalDegree _ ℂ D
  have hN : ∀ i, ∀ z ∈ Nw i, Lw i z ∈ Nw i := by
    intro i z hz
    simp only [Lw, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.add_mem _ (GlobalTheory.FockPolGK.kStable1 _ _ _ _ D (Yg i) (hKC i) z hz) (Submodule.smul_mem _ _ hz)
  have hLst : ∀ y ∈ tensDeg F _ _ _ _ D, L y ∈ tensDeg F _ _ _ _ D := by
    intro y hy
    change GlobalTheory.RealLift.sumPl Lw y ∈ _
    rw [GlobalTheory.RealLift.sumPl, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun w _ => GlobalTheory.RealLift.atPl_mem_range_map Lw Nw hN w y hy
  refine ⟨Φ (U T'), ⟨U T', exp_stable hexp _ hLst T' hT', rfl⟩, ?_⟩
  have h1 := hSA T'
  change GlobalTheory.RealLift.SA (om (γ (Multiplicative.ofAdd 1), 1)) (Φ T') (Φ (U T')) at h1
  rw [hγ1] at h1
  exact (GlobalTheory.RealLift.actsLaws F _ (Φ T') (Φ (U T')) (Φ (U T'))).2.1 _ (map_zero _) h1
theorem derivation_algebra_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  intro hPr F E _ _ _ _ _ σ Bs a a' Γ Xc om om' hT ΦD hΦ
  have hPair := GlobalTheory.ThK.RealUniq.isPair_V hT
  have hstdM := hPair.good.std
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hSB, hcof, rfl⟩ := hx
    obtain ⟨P, hPfin, hPle, hfP, hPst⟩ := _root_.GlobalTheory.SquareAgree.KFinAlg.polynomial_vector_kFinite _root_.GlobalTheory.T.real_lift_exists_fock_map hPr F E σ Bs a a' Γ Xc om om' hT f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x : Fin a × Fin (a + a') → Fv F v |
          ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hcof, hstdM] with v h1 h2
      rw [h1, h2]
    refine ⟨P.map (pureL φ), inferInstance, ?_, ⟨f, hfP, rfl⟩, ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      exact Submodule.subset_span ⟨g, φ, hPle hg, hSB, hcof, rfl⟩
    · rintro k hk _ ⟨g, hg, rfl⟩
      obtain ⟨g₁, hg₁, hA⟩ := hPst k hk g hg
      have key : om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g₁ φ :=
        hA _ (GlobalTheory.ThK.EvUniqInf.rest_pure _ _ hSB hstd)
      exact ⟨g₁, hg₁, key.symm⟩
  | zero =>
    exact ⟨⊥, inferInstance, bot_le, Submodule.zero_mem _, fun k _ x hx => by
      rw [Submodule.mem_bot] at hx; subst hx; rw [map_zero]; exact Submodule.zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨U₁, h1, l1, m1, s1⟩ := hx
    obtain ⟨U₂, h2, l2, m2, s2⟩ := hy
    refine ⟨U₁ ⊔ U₂, inferInstance, sup_le l1 l2, Submodule.add_mem_sup m1 m2, fun k hk z hz => ?_⟩
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hz
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (s1 k hk y₁ hy₁) (s2 k hk y₂ hy₂)
  | smul c x _ hx =>
    obtain ⟨U, h, l, m, s⟩ := hx
    exact ⟨U, h, l, U.smul_mem c m, s⟩
end GlobalTheory.SquareAgree.KFinAlg
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_algebra_closed_under_derivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' → ∀ ΦD ∈ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb,
    ∃ U : Submodule ℂ ((Fin a × Fin (a + a') → AF F) → ℂ), FiniteDimensional ℂ U ∧
      U ≤ GlobalTheory.SquareAgree.algD Γ.M Bs.ψ Bs.emb ∧ ΦD ∈ U ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ Γ.V Bs.emb, ∀ x ∈ U, om (k, 1) x ∈ U := by
  first | exact @_root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | exact _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite | (intros; apply _root_.GlobalTheory.SquareAgree.KFinAlg.derivation_algebra_kFinite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernel
section
section
open NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.PolKerLie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PolKer
theorem polynomialKernel_constTerm_lieDeriv : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ Φ₁ hΦ hd
  obtain ⟨T, hT, m, f, φ, hf, rfl, hz⟩ := hΦ
  have act := _root_.GlobalTheory.T.dualPair_preserves_polarization hP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)
  obtain ⟨D, hDm, hDi⟩ := act.2.2.1 γ hγ
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1 := by
    intro i
    filter_upwards [T.finite_toSet.compl_mem_cofinite, hM.triple.geo.hM.std] with v hv hs
    rw [(hf i).2.2 v hv, hs]
  have hder : ∀ i x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x)
      (pure (D (f i)) (φ i) x) 0 := fun i x =>
    (hDi (f i) (hf i).1 (D (f i))).2 rfl _
      (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x)
      (∑ i, pure (D (f i)) (φ i) x) 0 := by
    intro x
    have eq : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, pure (f i) (φ i)) x) =
        fun t : ℝ => ∑ i ∈ Finset.univ, om (1, γ (Multiplicative.ofAdd t)) (pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finset.sum_apply]
    rw [eq]
    exact HasDerivAt.fun_sum (fun i _ => hder i x)
  have e1 : Φ₁ = ∑ i, pure (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  refine ⟨T, hT, m, fun i => D (f i), φ, fun i => ⟨hDm _ (hf i).1, (hf i).2⟩, e1, ?_⟩
  let π : G.M.Pol Bs.ψ Bs.emb →ₗ[ℂ] R.Pi := R.p ∘ₗ (G.M.Pol Bs.ψ Bs.emb).subtype
  have hπ : Function.Surjective π := fun y => by
    have : y ∈ (G.M.Pol Bs.ψ Bs.emb).map R.p := hM.real.quot.onto ▸ Submodule.mem_top
    obtain ⟨g, hg, e⟩ := Submodule.mem_map.1 this
    exact ⟨⟨g, hg⟩, e⟩
  have ker0 : ∀ g ∈ G.M.Pol Bs.ψ Bs.emb, R.p g = 0 → R.p (D g) = 0 := fun g hg h0 => by
    have := hM.real.lie γ hγ g hg 0 (zero_mem _) (D g) 0 ((hDi g hg _).2 rfl)
      (GlobalTheory.ThK.RealUniq.actsD_zero _) (by rw [h0, map_zero])
    rwa [map_zero] at this
  let A := GlobalTheory.ThK.RealUniq.induced π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu)
  have hA : ∀ i, R.p (D (f i)) = A (R.p (f i)) := fun i =>
    (GlobalTheory.ThK.RealUniq.induced_apply π hπ (D.restrict hDm) (fun u hu => ker0 u.1 u.2 hu) ⟨f i, (hf i).1⟩).symm
  have := congrArg (A.rTensor _) hz
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, hA] using this
end GlobalTheory.PolKerLie
end
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.W, ∀ Φ Φ₁, GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) →
    (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | exact _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv | (intros; apply _root_.GlobalTheory.PolKerLie.polynomialKernel_constTerm_lieDeriv <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieAlgebraPreservesPolynomialKernelDualSpace
section
section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.PolKerLieV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem polynomialKernel_constTerm_lieDeriv_dualSpace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  intro hP F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM γ hγ Φ hΦ Φ₁ hd
  classical
  have exists_decomp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {Wd : Spc F E d} (M : Model σ Y Wd)
      (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : (w : InfinitePlace F) → GlobalTheory.AdelicU.EmbOver E w)
      {Φ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ} (hΦ : Φ ∈ GlobalTheory.SquareAgree.algD M ψ emb) :
      ∃ (T : Finset (Pl F)) (m : ℕ) (f : Fin m → SInf F (Fin n × Fin d))
        (φ : Fin m → (v : Pl F) → (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ i, f i ∈ M.Pol ψ emb ∧ (∀ v, φ i v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧
          ∀ v ∉ T, φ i v = M.vac v) ∧ Φ = ∑ i, pure (f i) (φ i) := by
    classical
    unfold GlobalTheory.SquareAgree.algD at hΦ
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, φ, hf, hφ, hv, rfl⟩ := hx
      have hfin := Filter.eventually_cofinite.1 hv
      refine ⟨hfin.toFinset, 1, fun _ => f, fun _ => φ, fun _ => ⟨hf, hφ, fun v hvT => ?_⟩, by simp⟩
      by_contra h
      exact hvT (hfin.mem_toFinset.2 h)
    | zero =>
      exact ⟨∅, 0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨T₁, m₁, f₁, φ₁, h₁, rfl⟩ := hx
      obtain ⟨T₂, m₂, f₂, φ₂, h₂, rfl⟩ := hy
      refine ⟨T₁ ∪ T₂, m₁ + m₂, Fin.append f₁ f₂, Fin.append φ₁ φ₂, fun i => ?_, ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
        · simp only [Fin.append_left]
          exact ⟨(h₁ i).1, (h₁ i).2.1, fun v hv => (h₁ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩
        · simp only [Fin.append_right]
          exact ⟨(h₂ i).1, (h₂ i).2.1, fun v hv => (h₂ i).2.2 v (fun h => hv (Finset.mem_union_right _ h))⟩
      · rw [Fin.sum_univ_add]
        simp [Fin.append_left, Fin.append_right]
    | smul c x _ hx =>
      obtain ⟨T, m, f, φ, h, rfl⟩ := hx
      refine ⟨T, m, fun i => c • f i, φ, fun i => ⟨(M.Pol ψ emb).smul_mem c (h i).1, (h i).2⟩, ?_⟩
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext x
      simp only [Pi.smul_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.smul_apply, smul_eq_mul, mul_assoc]
  obtain ⟨T, m, f, φ, hfφ, rfl⟩ := exists_decomp G.M Bs.ψ Bs.emb hΦ
  obtain ⟨D, hDmem, hD⟩ := (_root_.GlobalTheory.T.dualPair_preserves_polarization hP F E σ Bs _ _ G.V G.W G.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hM.triple)).1 γ hγ
  have hstd := hM.triple.geo.hM.std
  have hacts : ∀ i, ActsD (evI F) (fun t => ⇑(om (γ (Multiplicative.ofAdd t), 1))) ⇑(f i) ⇑(D (f i)) :=
    fun i => (hD (f i) (hfφ i).1 (D (f i))).2 rfl
  have hrest : ∀ i, Rest (evI F) ⇑(f i) (GlobalTheory.EvZeroInf.finPart (φ i)) := by
    intro i
    refine GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hfφ i).2.1 ?_
    filter_upwards [hstd, (Filter.eventually_cofinite.2 (by simpa using T.finite_toSet) : ∀ᶠ v in Filter.cofinite, v ∉ T)] with v hv hvT
    rw [(hfφ i).2.2 v hvT, hv]
  have hpure : ∀ i x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (pure (f i) (φ i)) x)
      (pure (D (f i)) (φ i) x) 0 := by
    intro i x
    rw [GlobalTheory.EvZeroInf.pure_eq_tens, GlobalTheory.EvZeroInf.pure_eq_tens]
    exact hacts i _ (hrest i) x
  have hsum : ∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (∑ i, pure (f i) (φ i)) x)
      (∑ i, pure (D (f i)) (φ i) x) 0 := by
    intro x
    refine (HasDerivAt.sum (u := Finset.univ) (fun i _ => hpure i x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.sum_apply]
  have hΦ₁ : Φ₁ = ∑ i, pure (D (f i)) (φ i) := by
    funext x
    rw [Finset.sum_apply]
    exact (hd x).unique (hsum x)
  have hp0 : ∀ i, R.p (D (f i)) = 0 := fun i =>
    hM.real.quot.lie γ hγ (f i) (hfφ i).1 (D (f i)) (hacts i)
  refine ⟨T ∪ Xc.T, Finset.subset_union_right, m, fun i => D (f i), φ, fun i =>
    ⟨hDmem _ (hfφ i).1, (hfφ i).2.1, fun v hv => (hfφ i).2.2 v (fun h => hv (Finset.mem_union_left _ h))⟩,
    hΦ₁, ?_⟩
  simp [hp0]
end GlobalTheory.PolKerLieV
end

section
open NumberField IsDedekindDomain
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieAlgebra_preserves_polynomialKernel_dualSpace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ G.V, ∀ Φ ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb, ∀ Φ₁,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Φ x) (Φ₁ x) 0) → GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ₁) := by
  first | exact @_root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace | exact _root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace | (intros; apply _root_.GlobalTheory.PolKerLieV.polynomialKernel_constTerm_lieDeriv_dualSpace <;> assumption)
end
end

