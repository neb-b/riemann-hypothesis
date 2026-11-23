module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0797
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientRealPlaceTwoVacua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adelic_point_lattice_isLattice : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (h : GA D (Vc D j)), Submodule.IsLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  first | exact @GlobalTheory.LatFull.latAt_isLattice | exact GlobalTheory.LatFull.latAt_isLattice | (intros; apply GlobalTheory.LatFull.latAt_isLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarPrimePowIntegralAtLevelPlaces
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_pow_mul_mem_of_mem_fieldRange (z : ℂ) (l : ℕ) (hl : l.Prime) : ∃ c : ℕ, ∀ (k : Type) [Field k] [NumberField k]
    (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O →
    z ∈ σ.fieldRange → (l : ℂ) ^ c * z ∈ O := by
  classical
  by_cases h : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : ℂ) * z)
  · obtain ⟨m, hm0, hint⟩ := h
    obtain ⟨c, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
    refine ⟨c, fun k _ _ σ la O hla hO hz => ?_⟩
    obtain ⟨y, rfl⟩ := hz
    have hti : IsIntegral ℤ ((m : k) * y) := by
      rw [← isIntegral_algHom_iff σ.toIntAlgHom σ.injective]
      simpa using hint
    have hm'0 : (m' : k) ≠ 0 := by
      rintro h0
      rw [Nat.cast_eq_zero] at h0
      subst h0
      simp at hmeq
      exact hm0 hmeq
    have hcop : IsCoprime (m' : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hm'))
    have hnot : ((m' : ℕ) : 𝓞 k) ∉ la.asIdeal := by
      intro hmem
      obtain ⟨s, t, hst⟩ := hcop
      apply la.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have : ((s : 𝓞 k) * ((m' : ℕ) : 𝓞 k) + (t : 𝓞 k) * ((l : ℕ) : 𝓞 k)) = 1 := by
        have := congrArg (Int.cast : ℤ → 𝓞 k) hst
        push_cast at this
        exact this
      rw [← this]
      exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hmem) (la.asIdeal.mul_mem_left _ hla)
    have hv1 : la.valuation k (m' : k) = 1 := by
      have e : ((m' : ℕ) : k) = algebraMap (𝓞 k) k ((m' : ℕ) : 𝓞 k) := (map_natCast _ _).symm
      rw [e, HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
    have hvt : la.valuation k ((m : k) * y) ≤ 1 := by
      have := HeightOneSpectrum.valuation_le_one (K := k) la (⟨(m : k) * y, hti⟩ : 𝓞 k)
      exact this
    have heq : ((l : k) ^ c * y) = ((m : k) * y) / (m' : k) := by
      rw [hmeq]; push_cast; field_simp
    have hmem := hO ((l : k) ^ c * y) (by rw [heq, map_div₀, hv1, div_one]; exact hvt)
    simpa using hmem
  · refine ⟨0, fun k _ _ σ la O hla hO hz => ?_⟩
    exfalso
    obtain ⟨y, rfl⟩ := hz
    have hy : IsAlgebraic ℤ y := (IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, hm0, hmi⟩ := hy.exists_integral_multiple
    apply h
    refine ⟨m.natAbs, by simpa using hm0, ?_⟩
    have h2 : IsIntegral ℤ (σ (m • y)) := hmi.map σ.toIntAlgHom
    rcases Int.natAbs_eq m with hm | hm
    · rw [hm] at h2; simpa [zsmul_eq_mul] using h2
    · rw [hm] at h2
      have h3 := h2.neg
      simpa [zsmul_eq_mul, neg_mul] using h3

theorem flipScal_pow_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP hW χ M₀ l hχ hl hM T
  have hM' : ((M₀ : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hM
  set u : D.host.Eˣ := Units.mk0 _ hM' with hu
  set z : ℂ := (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank) *
    ((Real.sqrt (flipIdx V W T M₀ : ℝ) : ℝ) : ℂ)⁻¹ with hz
  obtain ⟨c, hc⟩ := exists_pow_mul_mem_of_mem_fieldRange z l hl
  refine ⟨c, fun eT x hT hTM hx k _ _ σ la O hla hO hconj hval _ _ => ?_⟩
  have hfl : flipScal χW V W T M₀ x = z := by
    unfold flipScal
    rw [GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components D V χW χ M₀ u T eT x hχ.1 rfl hT hx]
  rw [hfl]
  refine hc k σ la O hla hO ?_
  obtain ⟨a, hai, hA1, hA2⟩ := _root_.GlobalTheory.LevelFieldApprox.exists_approx D.host.E χ M₀ u rfl T
  have hinf := _root_.GlobalTheory.LevelSeries.inf_eq_mul_normPow D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP χ hχ.1 k σ hconj a
  have := _root_.GlobalTheory.FlipScalField.mem_fieldRange D.host.E χ M₀ V.rank W.rank u a T k σ hW rfl hai hTM (fun v hv => hχ.2.1 v hv) hval hinf hA1 hA2
  simpa [hz, flipIdx] using this

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockVacuumPairingPolynomialTranslatesScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.VacPairSchur

set_option synthInstance.maxHeartbeats 400000 in
theorem actO_fin : ∀ (D : D7) (S T : HSp D) (u : GA D T), u ∈ GinfC T → ∀ w : WO S T, w.map (infPart D) = 0 → actO S T 1 u w = w := by
  intro D S T u hu w hw
  have hf : (Formalism.L2.Theta.mt T u).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hu)
    exact h
  have hm : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  unfold actO
  rw [inv_one, hm, Matrix.mul_one]
  ext i j
  refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
  · have h0 : ∀ k, infPart D (w k j) = 0 := fun k => by
      have := congrFun (congrFun hw k) j
      simpa using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp [h0]
  · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T u i k) = if i = k then 1 else 0 := fun k => by
      have := congrFun (congrFun hf i) k
      simpa [Matrix.one_apply] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum]
    simp [h1]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem pT_heisO (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ) {w : WO S T}
    (hw : w.map (infPart D) = 0) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T w f) P = heisO ψ S T w (pureTensorO ψ θ S T sS sT BS BT f P) := by
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (fun _ => True) trivial (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) (GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T w)
    (fun k g _ => ⟨trivial, ?_⟩) f trivial P).2
  · exact h.symm
  · obtain ⟨τ, i, j⟩ := k
    simp only [aPlusAll, aPlus, crea]
    rw [map_smul, map_sub, map_smul]
    show _ • (heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T w (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
    rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hw]
    rfl

theorem thetaIP_eq_ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    thetaIP μ 𝓕 f g = GlobalTheory.Ker.ipO μ 𝓕 g f := by
  unfold thetaIP GlobalTheory.Ker.ipO
  congr 1
  funext w
  rw [mul_comm]
  rfl

theorem thetaInner_heisenberg (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b)
    (w : WO S T) : thetaIP μ 𝓕 (heisO ψ S T w a) (heisO ψ S T w b) = thetaIP μ 𝓕 a b := by
  rw [thetaIP_eq_ipO, thetaIP_eq_ipO, GlobalTheory.Size.ipO_heisO hψ hcv.1 hcv.2.1 hb ha]

theorem om_heisO_fin {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {u : GA D T} (hu : u ∈ GinfC T) {w : WO S T} (hw : w.map (infPart D) = 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (1, u) (heisO ψ S T w f) = heisO ψ S T w (om (1, u) f) := by
  rw [hom.om_heis 1 u w f hf, actO_fin D S T u hu w hw]

theorem pT_lin (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (a : ℂ) {f f' : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hf' : IsThetaFunO ψ S T f') (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (a • f + f') P =
      a • pureTensorO ψ θ S T sS sT BS BT f P + pureTensorO ψ θ S T sS sT BS BT f' P :=
  GlobalTheory.VacCoefAtPlace.pure_lin (P := IsThetaFunO ψ S T) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h)
    (fun _ b _ _ h h' => by
      simp only [aPlusAll]
      rw [GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (GlobalTheory.OrientedHeis.theta_smul b h) h',
        GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ b h]) a hf hf' P

theorem onb_min {k : ℕ} {G s B : Matrix (Fin k) (Fin k) ℂ} {p : ℕ} (h : IsONBasis G s B p) :
    IsONBasis G s B (min p k) := by
  obtain ⟨ε, h1, h2, h3⟩ := h
  refine ⟨ε, fun a => ?_, h2, h3⟩
  rcases h1 a with ⟨e, ha⟩ | ⟨e, ha⟩
  · exact Or.inl ⟨e, lt_min ha a.2⟩
  · exact Or.inr ⟨e, (min_le_left _ _).trans ha⟩

theorem cs (hψ : IsStdChar D ψ (-1)) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hcv : IsCovolOne (ratL T S) μ 𝓕) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    ‖thetaIP μ 𝓕 a b‖ ^ 2 ≤ (thetaIP μ 𝓕 a a).re * (thetaIP μ 𝓕 b b).re := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have ii : ∀ {c : WO S T → ℂ}, IsThetaFunO ψ S T c → Integrable (fun x => star (c x) * c x) (μ.restrict 𝓕) :=
    fun {c} hc => (GlobalTheory.Size.integrableOn_mul_conj hψ hcv.1 hcv.2.1 hc hc).congr
      (ae_of_all _ fun x => mul_comm _ _)
  exact GlobalTheory.norm_integral_star_mul_sq_le (μ.restrict 𝓕) a b ha.cont.aestronglyMeasurable
    hb.cont.aestronglyMeasurable (ii ha) (ii hb)

theorem pair_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ u ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv u hu P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (1, u) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (a : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (a • f + f') g = star a * Φ f g + Φ f' g := by
    intro a f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT a hf hf' P, map_add (f := _), map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul a (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (a : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (a • g + g') = a * Φ f g + Φ f g' := by
    intro a f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT a hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul a (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hb : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_fin hom hu hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact _root_.GlobalTheory.VacSchurFin.vacSchur D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hb hi

end GlobalTheory.VacPairSchur
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameKeepsMatricesMatchesRationalPoints
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MtRead
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
namespace GlobalTheory.MtReadRat

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem cT_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (σA : A →+* A) (σB : B →+* B)
    (hc : ∀ x, φ (σA x) = σB (φ x)) {m : Type} [Fintype m] [DecidableEq m] (J g : Matrix m m A) :
    Formalism.UG.cT σB (g.map φ) * J.map φ * g.map φ = (Formalism.UG.cT σA g * J * g).map φ := by
  have : Formalism.UG.cT σB (g.map φ) = (Formalism.UG.cT σA g).map φ := by
    ext i j; simp [Formalism.UG.cT, hc]
  rw [this, Matrix.map_mul, Matrix.map_mul]

variable {D : D7}

theorem finHom_entry (V : HSp D) (h : GA D V) (X : GL (Fin V.rank) D.host.E) (hX : matHom V h = Formalism.UG.bc (incA D) X)
    (a b : Fin V.rank) : (finHom V h).1 a b = inclR (F := D.host.F) (Af D.host.F) (X.1 a b) := by
  have : (finHom V h).1 a b = Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) ((matHom V h).1 a b) := rfl
  rw [this, hX]
  simp [Formalism.UG.bc, inclR, incA]

theorem entry_of_ratF {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b))
    (κ : GAf D.host.E V.rank) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E)
    (e : Bridge.ratF V γ' = frameEquiv P κ) (hR : Bridge.IsRatMat V γ' γE) (a c : Fin V.rank) :
    ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a c =
      Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  have e' : finHom V γ'.1 = finHom V (P.ψ κ) := congrArg Subtype.val e
  have h1 := hId κ a c
  have h2 : finMat D.sp.cm.sig V.gram (P.ψ κ) a c = inclR (F := D.host.F) (Af D.host.F) (γE.val a c) := by
    show (finHom V (P.ψ κ)).1 a c = _
    rw [← e']
    exact finHom_entry V γ'.1 γE hR a c
  rw [h2] at h1
  rw [← (RingEquiv.eq_symm_apply _).1 h1]
  exact GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _

theorem ratMatch_fwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ : ReciprocityTheory.Aut.GQ D.host.E V.rank) :
    ∃ γ' : Formalism.L2.Theta.GQ V, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γ0, hγ0, e0⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
  have hγent : ∀ a b, (γ.1.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) a b =
      Algebra.TensorProduct.includeLeftRingHom ((γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun a b => by
    rw [← e0]; exact Matrix.GeneralLinearGroup.map_apply _ _ _ _
  have hfin : ∀ a b, (finHom V (P.ψ γ.1)).1 a b = inclR (F := D.host.F) (Af D.host.F) ((γ0 : Matrix _ _ D.host.E) a b) :=
    fun a b => by
      show finMat D.sp.cm.sig V.gram (P.ψ γ.1) a b = _
      rw [hId]
      simp only [Fin.cast_eq_self]
      rw [hγent, RingEquiv.symm_apply_eq]
      exact (GlobalTheory.Mem.R3.DatApi.swapCast_one_tmul hF _).symm

  have hsnd : ∀ x : AF D.host.F ⊗[D.host.F] D.host.E,
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom (sigR (AF D.host.F) D.sp.cm.sig x) =
      sigR (Af D.host.F) D.sp.cm.sig ((Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom x) :=
    fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [sigR, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  have hUA := (P.ψ γ.1).2
  change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((P.ψ γ.1).1.1) * JR (AF D.host.F) V.gram * (P.ψ γ.1).1.1 =
    JR (AF D.host.F) V.gram at hUA
  have hUf := congrArg (fun M => M.map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom) hUA
  rw [← cT_map _ _ _ hsnd] at hUf
  have hM : ((P.ψ γ.1).1.1 : Matrix (Fin V.rank) (Fin V.rank) _).map
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      (γ0 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; exact hfin a b
  have hJ : (JR (AF D.host.F) V.gram).map (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom =
      V.gram.map (inclR (F := D.host.F) (Af D.host.F)) := by
    ext a b; simp [JR, inclR]
  have hci : ∀ (R : Type) [CommRing R] [Algebra D.host.F R] (x : D.host.E),
      inclR (F := D.host.F) R (D.sp.cm.sig x) = sigR R D.sp.cm.sig (inclR (F := D.host.F) R x) := fun R _ _ x => by
    simp [sigR, inclR, Algebra.TensorProduct.map_tmul]
  rw [hM, hJ, cT_map _ _ _ (hci (Af D.host.F))] at hUf
  have hγ0' : γ0 ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := Matrix.map_injective hinjR hUf
  have hHR : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) γ0 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    show Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * (γ0 : Matrix _ _ D.host.E).map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [JR, cT_map _ _ _ (hci (AF D.host.F))]
    exact congrArg (fun M => Matrix.map M (inclR (F := D.host.F) (AF D.host.F))) hγ0'
  refine ⟨⟨⟨_, hHR⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γ0, hγ0', rfl⟩)⟩, Subtype.ext (Units.ext ?_)⟩
  ext a b
  refine (finHom_entry V ⟨_, hHR⟩ γ0 rfl a b).trans ?_
  exact (hfin a b).symm

theorem ratMatch_bwd {V : HSp D} (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V V.rank)
    (hId : ∀ κ a b, finMat D.sp.cm.sig V.gram (P.ψ κ) a b =
      (GlobalTheory.Mem.R3.swapCast hF).symm ((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast rfl a) (Fin.cast rfl b))) (γ' : Formalism.L2.Theta.GQ V) :
    ∃ γ : ReciprocityTheory.Aut.GQ D.host.E V.rank, Bridge.ratF V γ' = frameEquiv P γ := by

  have key := entry_of_ratF hF P hId
  haveI : Nontrivial (Af D.host.F) := Formalism.L2.DIV.af_nontrivial D.host.F
  haveI : Nontrivial (ReciprocityTheory.Aut.AFplus D.host.E) := Formalism.L2.DIV.af_nontrivial (maximalRealSubfield D.host.E)
  have hinjR : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    Algebra.TensorProduct.includeRight_injective (RingHom.injective _)
  have hinjL : Function.Injective (Algebra.TensorProduct.includeLeftRingHom :
      D.host.E →+* ReciprocityTheory.Aut.AL D.host.E) :=
    Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield D.host.E) (RingHom.injective _)

  obtain ⟨γE, hγE, eE⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ'.2)
  have hR : Bridge.IsRatMat V γ' γE := eE.symm
  set κ := (frameEquiv P).symm (Bridge.ratF V γ') with hκ
  have he : Bridge.ratF V γ' = frameEquiv P κ := ((frameEquiv P).apply_symm_apply _).symm
  have hent := key κ γ' γE he hR
  have hmat : ((κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) =
      (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom := by
    ext a c; exact hent a c
  have hU := κ.2
  simp only [ReciprocityTheory.Aut.GA, ReciprocityTheory.Aut.UGroup, Subgroup.mem_mk, Set.mem_ofPred_eq] at hU
  have hc : ∀ x : D.host.E, (Algebra.TensorProduct.includeLeftRingHom : D.host.E →+* ReciprocityTheory.Aut.AL D.host.E)
      ((IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) x) =
      ReciprocityTheory.Aut.conjAL D.host.E (Algebra.TensorProduct.includeLeftRingHom x) := fun x => by
    simp [ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.map_tmul]
  have hcT : ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E)
      ((γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map Algebra.TensorProduct.includeLeftRingHom) =
      (ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) (γE : Matrix _ _ _)).map
        Algebra.TensorProduct.includeLeftRingHom := by
    ext i j; simp only [ReciprocityTheory.Aut.conjT, Matrix.transpose_apply, Matrix.map_apply, hc]
  have h0 : γE ∈ ReciprocityTheory.Aut.GQ0 D.host.E V.rank := by
    show (γE : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *
      ReciprocityTheory.Aut.conjT (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E) γE = 1
    apply Matrix.map_injective hinjL
    simp only
    rw [Matrix.map_mul, ← hcT, ← hmat, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hU
  refine ⟨⟨κ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨γE, h0, Units.ext ?_⟩)⟩, he⟩
  rw [hmat]
  ext a c
  exact Matrix.GeneralLinearGroup.map_apply _ _ _ _

end GlobalTheory.MtReadRat

namespace GlobalTheory.MtRead
open GlobalTheory.MtReadRat Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ratMatch_of_idFrame : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n), IdFrame hF P → RatMatch (frameEquiv P) ∧ ∀ (hn : V.rank = n) (γ : ReciprocityTheory.Aut.GQ D.host.E n) (γ' : Formalism.L2.Theta.GQ V) (γE : GL (Fin V.rank) D.host.E), Bridge.ratF V γ' = frameEquiv P γ → Bridge.IsRatMat V γ' γE → ∀ a c, (((γ : GAf D.host.E n) : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn c) = Algebra.TensorProduct.includeLeftRingHom (γE.val a c) := by
  intro D V n hF P ⟨hn, hId⟩
  subst hn
  refine ⟨⟨ratMatch_fwd hF P hId, ratMatch_bwd hF P hId⟩, fun hn γ γ' γE e hR a c => ?_⟩
  simpa only [Fin.cast_eq_self] using entry_of_ratF hF P hId γ.1 γ' γE e hR a c

end GlobalTheory.MtRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjCoverFunctionEqConstMulConjTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ k0 : ℂ, IsRoot1 k0 ∧ ∀ (a b : Tp) (cx : Rul (M.dδ a).Xo₂ (M.dδ a).c₂), M.dδ b = { M.dδ a with cδ := cx } → HEq (M.U₂ b) (M.U₂ a) → HEq (M.dict₂ b) (M.dict₂ a) → ConjTup R τ (tup a) (tup b) → ∃ (h₂ : Fixes (M.dδ a).c₂ (covAut (M.dδ a) ta)) (ka : M.c'.F) (s : (AE D)ˣ), (ka : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ a).c₂.F k] (y₂ : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ k), evR (M.dδ a).Xo₂ (M.dδ a).c₂ (galRul h₂ (M.dδ a).cδ) y₂ = algebraMap (M.dδ a).c₂.F k ((M.dδ a).eF ka) * evR (M.dδ a).Xo₂ (M.dδ a).c₂ cx y₂ := by
  first | exact @GlobalTheory.CoverConj.conj_cover_const | exact GlobalTheory.CoverConj.conj_cover_const | (intros; apply GlobalTheory.CoverConj.conj_cover_const <;> assumption)
end

