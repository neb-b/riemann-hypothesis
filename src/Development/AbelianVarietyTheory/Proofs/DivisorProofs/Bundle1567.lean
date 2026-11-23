module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeAtFinitePlaceEqSumSplitPlaceParts
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LatSplit

open GlobalTheory.AdelicU.Supp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem singleTens_tmul (v : Pl (F := F)) (a : Fv F v) (x : E) :
    singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.LatVac.liftV v a ⊗ₜ[F] x := rfl

theorem tmul_smul_gen_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {a : Fv F v}
    (ha : a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) {c : AF F} (hc : At (evFin F v) c)
    (hcv : evFin F v c ∈ v.adicCompletionIntegers F) {x : Fin n → E} (hx : x ∈ X.L) {y : Fin d → E} (hy : y ∈ W.L) :
    singleTens E v (a ⊗ₜ[F] (o : E)) • (c • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v := by
  refine AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a * c, ?_, ?_, o • x, X.L.smul_mem o hx, y, hy, ?_⟩
  · intro u hu
    rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u c, hc u hu, mul_zero]
  · rw [map_mul, GlobalTheory.LatVac.evFin_liftV]
    exact mul_mem ha hcv
  · ext i j
    simp only [singleTens_tmul, Matrix.smul_apply, incM, Matrix.map_apply, Matrix.vecMulVec_apply, smul_eq_mul,
      Pi.smul_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, inclR]
    change _ * ((c ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] (x i * y j))) =
      ((GlobalTheory.LatVac.liftV v a * c) ⊗ₜ[F] (1:E)) * ((1:AF F) ⊗ₜ[F] ((o:E) * x i * y j))
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, mul_assoc]

theorem singleTens_smul_mem {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fv F v ⊗[F] E}
    (hy : y ∈ intLoc F E v) {γ : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hγ : γ ∈ latAtV X W v) :
    singleTens E v y • γ ∈ latAtV X W v := by
  refine intLoc_induction (p := fun y => singleTens E v y • γ ∈ latAtV X W v) ?_ ?_ ?_ ?_ hy
  · intro a ha o
    induction hγ using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨c, hc, hcv, x, hx, y', hy', rfl⟩ := hz
      exact tmul_smul_gen_mem X W v ha o hc hcv hx hy'
    | zero => rw [smul_zero]; exact zero_mem _
    | add z z' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | neg z _ h => rw [smul_neg]; exact neg_mem h
  · show singleTens E v 0 • γ ∈ latAtV X W v
    rw [map_zero, zero_smul]; exact zero_mem _
  · intro y z h h'
    show singleTens E v (y + z) • γ ∈ latAtV X W v
    rw [map_add (f := _), add_smul]; exact add_mem h h'
  · intro y h
    show singleTens E v (-y) • γ ∈ latAtV X W v
    rw [map_neg, neg_smul]; exact neg_mem h

theorem piW_splitIdemAd {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) :
    piW t (splitIdemAd hcm t) = 1 ∧ piW (t.comp σ) (splitIdemAd hcm t) = 0 := by
  constructor
  · change splitProj t (compFin F E v (singleTens E v (splitIdem hcm t))) = 1
    rw [compFin_singleTens_self, splitProj_splitIdem]
  · change splitProj (t.comp σ) (compFin F E v (singleTens E v (splitIdem hcm t))) = 0
    rw [compFin_singleTens_self, splitProj_comp_splitIdem]

theorem latAtV_decomp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ},
    IsCMExt F E σ → ∀ (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∀ γ ∈ latAtV X W v,
      ∃ γ₁ ∈ latAtV X W v, ∃ γ₂ ∈ latAtV X W v, γ = γ₁ + γ₂ ∧ γ₁.map (piW (t.comp σ)) = 0 ∧ γ₂.map (piW t) = 0 := by
  intro F E _ _ _ _ _ σ n d hcm X W v t γ hγ
  have h1 : splitIdemAd hcm t • γ ∈ latAtV X W v := singleTens_smul_mem X W v (splitIdem_mem hcm t) hγ
  obtain ⟨e1, e0⟩ := piW_splitIdemAd hcm t
  refine ⟨splitIdemAd hcm t • γ, h1, γ - splitIdemAd hcm t • γ, sub_mem hγ h1, (add_sub_cancel _ _).symm, ?_, ?_⟩
  · ext i j
    simp [smul_eq_mul, e0]
  · ext i j
    simp [smul_eq_mul, e1]

end GlobalTheory.LatSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplecticStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_darboux_adelic_symplectic : GlobalTheory.FunPr.Hypotheses₂ → DerEx → VacLine →
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGen τ C γ Y → ∀ (T : Tens F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 P Q R S (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRep.archRep | exact GlobalTheory.ArchRep.archRep | (intros; apply GlobalTheory.ArchRep.archRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreWeilComm

variable {D : D7} {θ : InfFam D} {V : HSp D} {n : ℕ} {τ : D.what₂.Tau}

theorem continuous_of_mem (hθ : IsInfFam θ) {m : ℕ} (Φ : schwartzA θ m n) : Continuous Φ.1 :=
  (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)).1

theorem integrable_of_mem (hθ : IsInfFam θ) {m : ℕ} (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (Φ : schwartzA θ m n) :
    Integrable Φ.1 μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun t _ => map_add_right_eq_self μ t)
  obtain ⟨C, hC⟩ := hC N
  exact ((hN K hK).const_mul C).mono' hc.aestronglyMeasurable (.of_forall hC)


variable {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
  {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}


section

variable (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
  (hω : StdUnn.IsWeilSch ψ χ θ V μ ω)
include hψ hθ hμ hω

end

end GlobalTheory.RegSch.CentreWeilComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticAddSelfExpansionHalfIdempotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.VacExpand

theorem symp_add_self_expand : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : E, θ + σ θ = 1 →
    ∀ γ γ' : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                   (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ') =
        GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
                     (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ' +
          2 * GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) θ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
          GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY θ hθ γ γ'
  have hinv : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hcc : ∀ z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hinv]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have hcI : ∀ x : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
    intro x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, inclR]
  let e : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) ≃ₐ[AF F] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) :=
    AlgEquiv.ofAlgHom (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
  have htr : ∀ z, Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) z := fun z => Algebra.trace_eq_of_algEquiv e z
  set A := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J with hA
  set Bm := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J with hBm
  set c := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ with hc
  have key : ∀ f : Fin n → Fin d → Fin n → Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := by
    intro f
    calc _ = ∑ i, ∑ k, ∑ j, ∑ l, f i j k l := Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, ∑ l, f i j k l := Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ l, ∑ j, f i j k l :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
  have hconj : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      c (GlobalTheory.WeilM.hTens c A Bm x y) = -GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.WeilM.hTens, map_sum, map_mul, hcc, hA, hBm, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hcI,
      hX.herm, hY.skew, map_neg]
    rw [key, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hexp : ∀ x y : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
      GlobalTheory.WeilM.hTens c A Bm (x + y) (x + y) = GlobalTheory.WeilM.hTens c A Bm x x + GlobalTheory.WeilM.hTens c A Bm y y +
        GlobalTheory.WeilM.hTens c A Bm x y + GlobalTheory.WeilM.hTens c A Bm y x := by
    intro x y
    simp only [GlobalTheory.WeilM.hTens, Matrix.add_apply, map_add (f := _), add_mul, mul_add, Finset.sum_add_distrib]
    ring
  have hθ' : σ θ = 1 - θ := eq_sub_of_add_eq' hθ
  have hcΘ : c (inclR (F := F) (AF F) θ) = 1 - inclR (F := F) (AF F) θ := by
    rw [hc, hcI, hθ', map_sub, map_one]
  have hswap : Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ) =
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ γ') +
      Algebra.trace (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ((-1) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
    have h1 : GlobalTheory.WeilM.hTens c A Bm γ' γ = -c (GlobalTheory.WeilM.hTens c A Bm γ γ') := by rw [hconj]; ring
    have h2 : inclR (F := F) (AF F) θ * GlobalTheory.WeilM.hTens c A Bm γ' γ =
        -c ((1 - inclR (F := F) (AF F) θ) * GlobalTheory.WeilM.hTens c A Bm γ γ') := by
      rw [h1, map_mul, ← hcΘ, hcc]; ring
    rw [h2, map_neg, htr]
    simp only [sub_mul, one_mul, neg_mul, map_sub, map_neg]
    ring
  simp only [GlobalTheory.WeilM.symp]
  rw [hexp, mul_add, mul_add, mul_add, map_add (f := _), map_add (f := _), map_add (f := _), hswap]
  ring

end GlobalTheory.VacExpand
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtComplet
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDegInt

open GlobalTheory.LamT

private theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (GlobalTheory.sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

private theorem integral_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : CDVR) (io : c.F →+* T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (_ : y.x = x) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro y hx
  subst hx
  exact integral_of T io y

theorem intPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∃ (ρV : 𝓞 K →+* T.V) (_ : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))) (_ : m1'.φ = n'.φ ≫ m1.φ) (_ : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), (∀ σ i j, i < j → C σ i j = 0) ∧ (∀ σ i, C σ i i = (td (some ⟨σ, i⟩) : T.Fr)) ∧ FrChg C (td none : T.Fr) yT y' ∧ GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u ∧ Integral T (iK.comp (algebraMap c.F K)) y' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 𝔓 T iK hiK yT hyT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ρV, hρV⟩ := exists_restrict_ringHom (algebraMap (𝓞 K) K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hiK _).2 (HeightOneSpectrum.valuation_le_one 𝔓 r))
  obtain ⟨G, n, -⟩ := (GlobalTheory.LamT.pat_pullback E H _ _ ρV B).1
  obtain ⟨_, _, _, _, _, n', -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap iK) t₀
  have hx : yT.x = spMap iK ≫ y.x := hyT.1
  obtain ⟨m1', h1⟩ := sab_comp' n' m1 yT.x hx
  obtain ⟨k2, hk2⟩ := sab_comp' n' m2 _ rfl
  obtain ⟨m2', h2⟩ := sab_cancel' n k2 (spMap (algebraMap T.V T.Fr))
    (by rw [← spMap_comp', ← spMap_comp', hρV])
  obtain ⟨⟨g0, hg0u, hg0⟩, -⟩ := GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' yT rfl
  obtain ⟨a0, ha0⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G _ yT.x m1' m2' yT rfl
  choose k hk using fun σ => _root_.GlobalTheory.iwasawa_lowerTriangular_of_det T.V T.Fr (Dw.mult σ) (g0 σ) (hg0u σ).ne_zero
  have hkdet : ∀ σ, IsUnit (((k σ).map (algebraMap T.V T.Fr))).det := fun σ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hk σ).1.map _
  let C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr :=
    fun σ => (k σ).map (algebraMap T.V T.Fr) * g0 σ
  have hCdet : ∀ σ, IsUnit (C σ).det := fun σ => by
    simp only [C, Matrix.det_mul]
    exact (hkdet σ).mul (hg0u σ)
  have hlow : ∀ σ i j, i < j → C σ i j = 0 := fun σ i j hij => (hk σ).2 i j hij
  have hdiag : ∀ σ i, C σ i i ≠ 0 := fun σ i => by
    have hd : (C σ).det = ∏ j, C σ j j :=
      Matrix.det_of_lowerTriangular _ (fun a b hab => hlow σ a b hab)
    have hne : (C σ).det ≠ 0 := (hCdet σ).ne_zero
    rw [hd] at hne
    exact Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ _)
  let td : Ix Dw → T.Frˣ := fun o => o.elim a0 (fun p => Units.mk0 (C p.1 p.2 p.2) (hdiag p.1 p.2))
  obtain ⟨y', hy', hyu⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT C a0 hCdet
  obtain ⟨y0, hy0, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT g0 a0 hg0u
  obtain ⟨y1, hy1, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr y0 (fun σ => (k σ).map (algebraMap T.V T.Fr)) 1 hkdet
  have hc := (frChg_refl_and_comp E H Dw l Xo c T.Fr yT y0 y1).2 g0 _ (a0 : T.Fr) _ hy0 hy1
  have h1y : y1 = y' := hyu y1 (by simpa [C] using hc)
  have hL0 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y0.u := hg0 a0 y0 hy0
  have hL1 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y1.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' y0 hy0.1).2 hL0 k _ y1
      (fun σ => (hk σ).1) hy1
  rw [h1y] at hL1
  refine ⟨ρV, hρV, G, _, n, n', m1', m2', h1, h2.trans hk2, C, td, y', hlow, fun σ i => rfl, hy', hL1, ?_⟩
  exact integral_of_eq T (iK.comp (algebraMap c.F K)) y' hy'.1 m1' m2' hL1 (ha0 C y' hy')

end GlobalTheory.PtDegInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotDvdDifferentIdeal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistPlDiff

theorem natAbs_discr_dvd_pow (D : D7) : ∃ M : ℕ,
    (discr D.host.E).natAbs ∣ (D.host.QS * D.host.q * D.host.d) ^ M := by
  have hD : (discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  have hN : D.host.QS * D.host.q * D.host.d ≠ 0 := D.host.condN_ne_zero
  refine ⟨(discr D.host.E).natAbs, (Nat.dvd_pow_self_iff hD hN).2 fun p hp => ?_⟩
  have h := Nat.mem_primeFactors.1 hp
  exact Nat.mem_primeFactors.2
    ⟨h.1, D.host.der.discr_primes.1 p h.1 (Int.natCast_dvd.2 h.2.1), hN⟩

theorem under_not_dvd_differentIdeal : ∀ {D : D7} {T : Type} (Lc : LevCh D T) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T), ∀ PP ∈ Lc.Q t, ¬ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal ∣ differentIdeal ℤ (𝓞 D.host.F) := by
  intro D T Lc μ₀ hL t PP hPP hdvd
  obtain ⟨h2qdT, -⟩ := hL.Q_off t PP hPP
  set P := (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) with hPdef

  have h1 : Ideal.absNorm P.asIdeal ∣ (discr D.host.E).natAbs := by
    have ha : Ideal.absNorm P.asIdeal ∣ (discr D.host.F).natAbs := by
      rw [← NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
    exact ha.trans (Int.natAbs_dvd_natAbs.2 (NumberField.discr_dvd_discr _ _))
  obtain ⟨M, hM⟩ := natAbs_discr_dvd_pow D

  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    have := Ideal.absNorm_mem P.asIdeal
    have h' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (Ideal.absNorm P.asIdeal : 𝓞 D.host.F) ∈ PP.asIdeal := this
    simpa using h'
  have hpow : (((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E)) ^ M ∈ PP.asIdeal := by
    obtain ⟨c, hc⟩ := h1.trans hM
    rw [← Nat.cast_pow, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem
  have hx := PP.isPrime.mem_of_pow_mem M hpow
  apply h2qdT
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hx

end GlobalTheory.TwistPlDiff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTwistPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ hμ t v e he PP hPP hv hns
  obtain ⟨f, hf⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt ((hμ.Q_pl t PP hPP).2 PP hPP)
  exact GlobalTheory.AdTh.RecPair.under_ne hf hns hv

end GlobalTheory.SplitTwistPlaces
end

