module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0256
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1327
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLe
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0565
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSectionStatement
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_lift_gives_holomorphic_section : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (O : Set (Fin D → ℂ)) (γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ) (s : (Fin D → ℂ) → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀),
    IsOpen O → DifferentiableOn ℂ γ O → (∀ v ∈ O, IsUnder (PtsOver.map i rfl _ (s v)) (γ v)) →
    ContinuousOn s O ∧ ∀ (W : X.Opens) (f : Γ(X, W)),
      DifferentiableOn ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ s) (O ∩ s ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.Holo.holo | exact GlobalTheory.CompanionTheory.MixZ.Holo.holo | (intros; apply GlobalTheory.CompanionTheory.MixZ.Holo.holo <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealLatticeToAddSubgroupEqIdealSub
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticDict

theorem idealLattice_toAddSubgroup_eq_idealSub :
    ∀ {K : Type} [Field K] [NumberField K] [Algebra K ℂ] (I : FractionalIdeal (𝓞 K)⁰ K),
      (GroundTheory.Global.Elliptic.idealLattice (algebraMap K ℂ) I).toAddSubgroup =
        GlobalTheory.EllipticCM.idealSub I := by
  intro K _ _ _ I
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

end GlobalTheory.CompanionTheory.EllipticDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzAHaar
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.CompanionTheory.WSum
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WSum

theorem integrable_schwartzA_haar : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (μ : Measure (Mx D m n))
    [μ.IsAddHaarMeasure] (φ : Mx D m n → ℂ), φ ∈ schwartzA θ m n → Integrable φ μ := by
  intro D θ hθ m n μ _ φ hφ
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    haveI : IsModuleTopology (Af D.host.F) (GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
    haveI : IsTopologicalRing (GlobalTheory.RegSch.IkSchwartz.AEf D) := IsModuleTopology.isTopologicalRing (Af D.host.F) _
    haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele D.host.F
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
    obtain ⟨e0⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
    haveI : LocallyCompactSpace (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isClosedEmbedding.locallyCompactSpace
    haveI : SecondCountableTopology (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.secondCountableTopology
    haveI : T2Space (GlobalTheory.RegSch.IkSchwartz.AEf D) := e0.isEmbedding.t2Space
    letI : MeasurableSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := borel _
    haveI : BorelSpace (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := ⟨rfl⟩
    haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
    haveI := (GlobalTheory.TowerRestrict.lattice_Mx D m n).1
    obtain ⟨e, he⟩ := GlobalTheory.RegSch.IkSchwartz.exists_split hθ m n
    let μr : Measure (D.what₂.Tau → Fin m → Fin n → ℂ) := Measure.addHaar
    let ν : Measure (Fin m → Fin n → GlobalTheory.RegSch.IkSchwartz.AEf D) := Measure.addHaar
    obtain ⟨c, hc⟩ := GlobalTheory.PartialIntegral.exists_integral_split e μ μr ν
    have h := (hc f g (f.integrable) (hg.1.continuous.integrable_of_hasCompactSupport hg.2)).1
    simpa only [he] using h
  | zero => exact integrable_zero _ _ _
  | add φ ψ _ _ h1 h2 => exact h1.add h2
  | smul c φ _ h => exact h.smul c

end GlobalTheory.CompanionTheory.WSum

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvSmulEqFinitePartInvSmul
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.EllipticCM

theorem ord_eq_ord_vw_finitePart {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    GroundTheory.Global.IdeleGroup.ord v s =
      GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v :=
  rfl

theorem coe_smul_eq_finitePart_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s) • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
  refine GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _)
    (GlobalTheory.Idele.smul_ne_zero _ (Units.ne_zero _)) fun v => ?_
  rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ (Units.ne_zero _),
    ord_eq_ord_vw_finitePart]

theorem inv_smul_eq_finitePart_inv_smul {K : Type} [Field K] [NumberField K]
    (s : GroundTheory.Global.IdeleGroup K) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s⁻¹ • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  coe_smul_eq_finitePart_smul s⁻¹ 𝔞

end GlobalTheory.CompanionTheory.EllipticCM
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InversePointTorusScaling
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCoord

variable {K : Type} [CommRing K] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) K} {Rx Ry : Matrix (Fin r) (Fin n) K}

theorem left_proj (h1 : Rx * X = 0) (h3 : Rx * Y = 1) : Rx * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, h3, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem left_proj' (h2 : Ry * Y = 0) (h4 : Ry * X = 1) : Ry * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h2, h4, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem lin (h1 : Rx * X = 0) (h2 : Ry * Y = 0) (h3 : Rx * Y = 1) (h4 : Ry * X = 1)
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A * B = 1) {T S : Matrix (Fin r) (Fin r) K} (hTS : T * S = 1)
    (hST : S * T = 1) (hX : B * X = X * T) (hY : B * Y = Y * S) (ξ : Matrix (Fin n) (Fin 1) K)
    (hq : B * ((1 - X * Ry - Y * Rx) * ξ) = (1 - X * Ry - Y * Rx) * ξ) :
    Ry * (A * ξ) = S * (Ry * ξ) ∧ Rx * (A * ξ) = T * (Rx * ξ) ∧
      (1 - X * Ry - Y * Rx) * (A * ξ) = (1 - X * Ry - Y * Rx) * ξ := by
  have hRxQ := left_proj (Ry := Ry) h1 h3
  have hRyQ := left_proj' (Rx := Rx) h2 h4
  have e : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K),
      (1 - X * Ry - Y * Rx) * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  generalize hQ : 1 - X * Ry - Y * Rx = Q at hq hRxQ hRyQ ⊢
  have eQ : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K), Q * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    rw [← hQ]; exact e M
  have hAX : A * X = X * S := by
    have h : A * (B * X) = X := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hX, ← Matrix.mul_assoc] at h
    calc A * X = A * X * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = (A * X * T) * S := by simp only [Matrix.mul_assoc]
      _ = X * S := by rw [h]
  have hAY : A * Y = Y * T := by
    have h : A * (B * Y) = Y := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hY, ← Matrix.mul_assoc] at h
    calc A * Y = A * Y * (S * T) := by rw [hST, Matrix.mul_one]
      _ = (A * Y * S) * T := by simp only [Matrix.mul_assoc]
      _ = Y * T := by rw [h]
  have hAQ : A * (Q * ξ) = Q * ξ := by
    conv_lhs => rw [← hq]
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hQX : Q * X = 0 := by rw [eQ, h1, h4]; simp
  have hQY : Q * Y = 0 := by rw [eQ, h2, h3]; simp
  have hQQ : Q * Q = Q := by rw [eQ, hRxQ, hRyQ]; simp
  have hdec : ξ = X * (Ry * ξ) + Y * (Rx * ξ) + Q * ξ := by rw [eQ]; abel
  have hu : A * ξ = X * (S * (Ry * ξ)) + Y * (T * (Rx * ξ)) + Q * ξ := by
    conv_lhs => rw [hdec]
    rw [Matrix.mul_add, Matrix.mul_add, hAQ, ← Matrix.mul_assoc A X, ← Matrix.mul_assoc A Y, hAX, hAY,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Ry X, ← Matrix.mul_assoc Ry Y, ← Matrix.mul_assoc Ry Q, h4, h2,
      hRyQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Rx X, ← Matrix.mul_assoc Rx Y, ← Matrix.mul_assoc Rx Q, h3, h1,
      hRxQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Q X, ← Matrix.mul_assoc Q Y, ← Matrix.mul_assoc Q Q, hQX, hQY,
      hQQ]
    simp

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  have h := congrArg Units.val (map_mul (Formalism.L2.Theta.matHom V) a⁻¹ a)
  rw [inv_mul_cancel, map_one] at h
  exact h.symm

theorem map_mt_eq_archMat {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (ρ : D.what₂.Tau) (a : GA D V) :
    (Formalism.L2.Theta.mt V a).map (fun x => θ ρ (infPart D x)) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) a) := by
  have e := eq_infProj hθ (embOverOf D ρ) rfl
  have h := infMat_infProj (J := V.gram) (isCMExt_host D) (embOverOf D ρ) a
  rw [← e] at h
  refine Eq.trans ?_ (h.trans (GlobalTheory.Orb.archMat_eq_archEquiv V.gram (isCMExt_host D) _ _).symm)
  ext i j
  rfl

theorem torus_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  intro D θ hθ V r Xf Yf hW t ht a ha ξ
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  refine ⟨?_, fun ρ => ?_⟩
  · have h1 : (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 :=
      GlobalTheory.CompanionTheory.SiegelArch.map_matHom_fin V.gram (inv_mem ha.1)
    change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map (finPart D) = _
    rw [Matrix.map_mul, h1, Matrix.one_mul, Matrix.map_map]
    ext i j
    exact GlobalTheory.LatVac.finPart_incA _
  · have hhτ : ∀ x, θ ρ (infPart D (incA D x)) = tauE D ρ x := fun x => (hθ ρ).1 x
    let φ : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hAB : (Formalism.L2.Theta.mt V a⁻¹).map φ * (Formalism.L2.Theta.mt V a).map φ = 1 := by
      rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hB : (Formalism.L2.Theta.mt V a).map φ = _ := map_mt_eq_archMat hθ V ρ a
    have hcomp : compAt θ ρ (invPt V a ξ) = (Formalism.L2.Theta.mt V a⁻¹).map φ * ξ.map (tauE D ρ) := by
      change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map φ = _
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hhτ _
    obtain ⟨hX, hY, hZ⟩ := ha.2 (placeOf D ρ) (embOverOf D ρ)
    rw [← hB] at hX hY hZ
    simp only [embOverOf_val] at hX hY hZ
    obtain ⟨-, -, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)
    have hxx := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).1
    have hyy := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).2.1
    have hJc : (V.gram.map (tauE D ρ))ᴴ = V.gram.map (tauE D ρ) := by
      ext i j
      rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]
    have hyx := GlobalTheory.CentreFin.dual_swap hJc hxy
    have hR : ∀ C : Matrix (Fin V.rank) (Fin r) D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (tauE D ρ) =
          (C.map (tauE D ρ))ᴴ * V.gram.map (tauE D ρ) := fun C => by
      rw [Matrix.map_mul, GlobalTheory.CentreFin.map_cT_emb hcm]
    have h1 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hxx
    have h2 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hyy
    have h3 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hxy
    have h4 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hyx
    have h4E : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * Xf = 1 := by
      refine Matrix.map_injective (tauE D ρ).injective ?_
      beta_reduce
      rw [Matrix.map_mul, h4, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQm : (1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ) =
        1 - Xf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ) -
          Yf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ) := by
      change (tauE D ρ).mapMatrix _ = _
      rw [map_sub, map_sub, map_one]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
    have hxq := left_proj (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.xx hW.xy
    have hyq := left_proj' (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.yy h4E
    have hq := hZ (fun i => ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ :
            Matrix (Fin V.rank) (Fin 1) D.host.E) i 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hxq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hyq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
    have hq' := by
      refine lin h1 h2 h3 h4 hAB (T := diagonal fun i => (t i : ℂ)) (S := diagonal fun i => (t i : ℂ)⁻¹) ?_ ?_ hX hY
        (ξ.map (tauE D ρ)) ?_
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact mul_inv_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact inv_mul_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [← hQm, ← Matrix.map_mul]
        ext i j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact congrFun hq i
    obtain ⟨c1, c2, c3⟩ := hq'
    have m : ∀ {a : ℕ} (M : Matrix (Fin a) (Fin V.rank) D.host.E),
        (M * ξ).map (tauE D ρ) = M.map (tauE D ρ) * ξ.map (tauE D ρ) := fun M => Matrix.map_mul
    rw [hcomp, m, m, m, hQm]
    exact ⟨c1, c2, c3⟩

end GlobalTheory.CompanionTheory.TorusCoord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdmissibleDegenerate
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.DegenSeries

theorem isAdmissible_degenerate : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ →
    IsAdmissible (parInd (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)) := by
  intro k _ _ _ _ a b χ₁ χ₂ _ _
  exact GlobalTheory.SmGL.ParIndAdm.isAdmissible_parInd _ _

end GlobalTheory.CompanionTheory.DegenSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsClosedUnipotentRadicalStabilizer
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem isClosed_radN : ∀ (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t),
    IsClosed (radN d : Set (GlobalTheory.RegSW.stab d)) := by
  intro D B W t d
  have e : (radN d : Set (GlobalTheory.RegSW.stab d)) =
      (Subtype.val : GlobalTheory.RegSW.stab d → GA D B) ⁻¹' (GlobalTheory.MixPer.radX d : Set (GA D B)) := by
    ext q
    constructor
    · rintro ⟨c, b, h⟩
      exact (GlobalTheory.MixPer.Decomp.mem_radX_iff d).2 ⟨b, c, h.trans (d.nC_mul_nB b c)⟩
    · intro h
      obtain ⟨b, c, h⟩ := (GlobalTheory.MixPer.Decomp.mem_radX_iff d).1 h
      exact ⟨c, b, h.trans (d.nC_mul_nB b c).symm⟩
  rw [e]
  exact (GlobalTheory.JacMeas.isClosed_radX d).preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.QKAvg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityOfEquiv
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.JacquetCongr

theorem jm_congr_of_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (σ : Representation ℂ (GL (Fin N) k) W), Nonempty (π.Equiv σ) → jm x hd π = jm x hd σ := by
  intro k _ _ _ _ h N x hd V W _ _ _ _ π σ ⟨φ⟩
  exact jhMult_congr_right _ (GlobalTheory.SmGL.Exponents.jacEquiv _ φ)

end GlobalTheory.CompanionTheory.JacquetCongr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityTransitiveLeStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_transitive_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ {g N : ℕ} (y : Fin g → IrrGL (k := k)) (hy : ∑ b, (y b).1 = N) (Wb : Fin g → List (IrrGL (k := k))) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π → (∀ b, ∑ a, ((Wb b).get a).1 = (y b).1) → jm y hy π * ∏ b, jmL (Wb b) (y b).rep ≤ jmL (List.ofFn Wb).flatten π := by
  first | exact @GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | exact GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le | (intros; apply GlobalTheory.CompanionTheory.CsStages.jm_mul_prod_jmL_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetQuotientEigenvectorStatement
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_quotient_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ (μ : ℂ) (w : V), (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 → (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) w) : Jacquet π (unipRad k (stdBlocks d hd))) = μ • (Submodule.Quotient.mk w : Jacquet π (unipRad k (stdBlocks d hd))) → ∃ (x : Fin 2 → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N), (∀ a, (x a).1 = d a) ∧ Zc.jm x hx π ≠ 0 ∧ Zl.ScalarBy (x 0) (Zls.unifU k) (μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2)) ∧ ∃ c1 : ℂ, Zl.ScalarBy (x 1) (Zls.unifU k) c1 := by
  first | exact @GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | exact GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen | (intros; apply GlobalTheory.CompanionTheory.JacExp.exists_constituent_of_eigen <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsFactorsDualReverseOrdered
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.DualForms

theorem exists_revOrdered_dual : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegDual k →
    ∀ (𝔪 : Multiset (Segment k)) {h : ℕ} (x : Fin h → IrrGL (k := k)), LFactors 𝔪 x →
      ∃ Γ : Fin h → Segment k, IsRevOrdered Γ ∧ ∀ i, IsLSeg (Γ i) (dualCl (x i)).rep := by
  intro k _ _ _ _ hA hD 𝔪 h x hx
  obtain ⟨Δ, ⟨-, hord⟩, hL⟩ := hx
  refine ⟨fun i => segDual (Δ i), fun i j hij hp => hord i j hij ((_root_.GlobalTheory.CompanionTheory.SegDualPrec.segDual_precedes hA _ _).1 hp), fun i => ?_⟩
  rw [GlobalTheory.CompanionTheory.Zcore.dualCl_eq_of hA (x i)]
  exact (hD (Δ i) (x i).rep (hL i)).of_equiv (IrrGL.equivOf _ _ _)

end GlobalTheory.CompanionTheory.DualForms
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMinimalIdeleHermitianBoundStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_minimal_idele_hermitian_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ m ∈ leviMin σ J X Y, m ∈ minParOne σ J X → ∀ j, ∃ s : GroundTheory.Global.IdeleGroup F, 1 ≤ (GroundTheory.Global.IdeleGroup.ideleModule F s : ℝ) ∧ ∀ ξ : Fin n → E, hR (AF F) σ (hermFam σ J X Y j) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) ((matHom _ σ J m⁻¹).1 *ᵥ ratV F ξ) = algebraMap (AF F) (AF F ⊗[F] E) (s : AF F) * inclR (F := F) (AF F) (hE σ (hermFam σ J X Y j) ξ ξ) := by
  first | exact @GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale | exact GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale | (intros; apply GlobalTheory.CompanionTheory.ParCocompact.hermFam_levi_scale <;> assumption)
end

