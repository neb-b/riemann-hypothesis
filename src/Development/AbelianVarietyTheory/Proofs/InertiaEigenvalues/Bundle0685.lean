module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.MemIntegralClosureIffMemBall
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.ExistsDen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.IsEquivAdicAbvNormAbv
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Formalism.GaloisCohomology.LocalTateDualityK
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0674
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysLitAll
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Module

namespace GlobalTheory.CrysFormalism

theorem crysLit_all : ∀ D : D7, Formalism.MainNotions.tableLineDegreeTwo.adm22 D := by
  intro D l _ K LL _
  have T := D.locT l
  refine ⟨?_, ?_, ?_⟩
  · intro μ a _ hμ hm
    refine ⟨GlobalTheory.Adopt.isCrys_inv_and_hodgeTate_jumps_neg l (D.loc l) (D.locA l) T K LL μ a hμ hm, ?_⟩
    intro V _ _ _ _ _ _ _ ρ ρ' _ hρ hρ'
    have htw : IsTwistRep μ ρ ρ' := ⟨LinearEquiv.refl _ _, fun g x => by simp [hρ']⟩
    obtain ⟨hc, hmult⟩ := GlobalTheory.TwistRepCrys.isCrys_and_multV_twist l (D.loc l) (D.locA l) T K LL
      V ρ V ρ' μ htw hμ hρ
    refine ⟨hc, fun τ b => ?_⟩
    have hj : IsJumpV ((D.loc l).PD K) (charRep μ) τ (a τ) := by
      rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (D.loc l) (D.locA l) T K LL _ (charRep μ) τ (a τ)).2.2, hm]
      simp
    have := hmult τ (b - a τ) (a τ) hj
    rwa [sub_add_cancel] at this
  · intro V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ hι hπ hinj hsurj hex h1
    have h0 := (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ ι hι).1 hinj h1
    have h2 := ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l (D.loc l) (D.locA l) T K LL V₁ ρ₁ V₂ ρ₂ π hπ).2 hsurj h1).1
    have hdr := GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) T K LL V₁ ρ₁ h1
    refine ⟨h0, h2, fun τ a => ?_⟩
    exact ((GlobalTheory.Per.ExactMult.exact_hodge_add l (D.loc l) (D.locA l) T K LL V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π
      hι hπ hinj hsurj hex hdr.1).2.2 τ a).2.1
  · intro V _ _ _ _ _ _ _ ρ _ τ
    obtain ⟨h1, _⟩ := GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) T K LL V ρ
    exact ⟨(h1 τ).1, (h1 τ).2.1⟩

end GlobalTheory.CrysFormalism
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
section
noncomputable section

namespace GlobalTheory.DecLocal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem exists_place_below : ∀ {p : ℕ} [Fact p.Prime] {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∃ w : HeightOneSpectrum (𝓞 F), w ∈ Formalism.BasicNotions.placesOver F p ∧ IsPlaceOver A w := by
  intro p _ F Ω _ _ _ _ A hp
  have hint : ∀ x : 𝓞 F, algebraMap F Ω (x : F) ∈ A := fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A ((NumberField.RingOfIntegers.isIntegral_coe x).algebraMap)
  let f : 𝓞 F →+* A := RingHom.codRestrict ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)) A hint
  let I : Ideal (𝓞 F) := Ideal.comap f (IsLocalRing.maximalIdeal A)
  have hI : ∀ x : 𝓞 F, x ∈ I ↔ A.valuation (algebraMap F Ω (x : F)) < 1 := fun x => by
    change f x ∈ IsLocalRing.maximalIdeal A ↔ _
    exact ValuationSubring.valuation_lt_one_iff A (f x)
  have hpI : ((p : 𝓞 F)) ∈ I := by
    rw [hI]; simpa using hp
  have hp0 : ((p : 𝓞 F)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  let w : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := I, isPrime := Ideal.comap_isPrime f _,
      ne_bot := fun h => hp0 (by rw [← Ideal.mem_bot, ← h]; exact hpI) }
  exact ⟨w, hpI, fun x => (hI x).symm⟩

theorem exists_root_of_unity : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl p)
    (n : ℕ) (z : PadicAlgCl p), z ^ (p ^ n) = 1 → ∃ y : Ω, y ^ (p ^ n) = 1 ∧ j y = z := by
  intro p _ Ω _ _ j n z hz
  have hf : ((X ^ (p ^ n) - 1 : Polynomial Ω).map j) = X ^ (p ^ n) - 1 := by simp
  have hne : (X ^ (p ^ n) - 1 : Polynomial (PadicAlgCl p)) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (pow_pos (Fact.out : p.Prime).pos n) (1 : PadicAlgCl p)
  have hz' : z ∈ ((X ^ (p ^ n) - 1 : Polynomial Ω).map j).roots := by
    rw [hf, mem_roots hne]; simp [hz]
  rw [Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hz'
  obtain ⟨y, hy, rfl⟩ := hz'
  refine ⟨y, ?_, rfl⟩
  have := isRoot_of_mem_roots hy
  simpa [sub_eq_zero] using this

theorem norm_lt_one_iff {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p)
    (hA : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (y : Ω) : ‖j y‖ < 1 ↔ A.valuation y < 1 := by
  rw [valuation_lt_one_iff', hA, hA]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have h0 : 0 < ‖j y‖ := norm_pos_iff.2 ((map_ne_zero j).2 hy)
    rw [map_inv₀, norm_inv]
    simp only [hy, false_or]
    constructor
    · intro h
      exact ⟨h.le, not_le.2 ((one_lt_inv₀ h0).2 h)⟩
    · rintro ⟨h1, h2⟩
      refine lt_of_le_of_ne h1 fun h => h2 ?_
      rw [h, inv_one]

theorem finrank_closure_eq_locDeg : ∀ (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p), (∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) →
    ∀ v : HeightOneSpectrum (𝓞 F), IsPlaceOver A v →
      Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] (Set.range fun x : F => j (algebraMap F Ω x))) =
        locDeg v := by
  intro p _ F Ω _ _ _ _ A j hA v hv
  let φ : F →+* PadicAlgCl p := j.comp (algebraMap F Ω)
  obtain ⟨v', -, hφ⟩ := PI.CompDegEF.placeProp p F φ
  have hvp : v ∈ Formalism.BasicNotions.placesOver F p := by
    show ((p : 𝓞 F)) ∈ v.asIdeal
    rw [← hv, ← norm_lt_one_iff A j hA]
    simpa using GlobalTheory.PlaceBridge.norm_l_lt_one (l := p)
  exact PI.CompDegEF.locDegOf_of PI.CompDegEF.ballCard PI.CompDegEF.denseSurj PI.CompDegEF.kerProp
    PI.CompDegEF.normCard p F φ ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range φ⟩
    (fun x => IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
    (GlobalTheory.PlaceBridge.adjoin_range_subset_closure φ) v hvp
    (fun x => ⟨(hφ x).1, (norm_lt_one_iff A j hA _).trans (hv x)⟩)

theorem decEquiv : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  intro p _ F Ω _ _ _ _ _ A hp
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  obtain ⟨w, hw, hAw⟩ := exists_place_below (F := F) A hp
  obtain ⟨j, hj⟩ := GlobalTheory.PlaceBridge.exists_embedding F Ω w A hw hAw
  obtain ⟨i, hi⟩ := _root_.GlobalTheory.DecGalois.exists_continuousMulEquiv p F Ω A j hj
  refine ⟨_, GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range (j.comp (algebraMap F Ω)), i, ?_,
    fun g => GlobalTheory.T.localInertia_iff_mem_placeInertia p F Ω A j hj _ i.toMulEquiv hi g,
    fun v hv => finrank_closure_eq_locDeg p F Ω A j hj v hv⟩
  intro O _ ε hε g n ζ hζ
  obtain ⟨y, hy, rfl⟩ := exists_root_of_unity p Ω j n ζ hζ
  obtain ⟨a, ha, ha'⟩ := hε (i.symm g) n y hy
  refine ⟨a, ?_, ha'⟩
  have e := hi (i.symm g) y
  rw [ContinuousMulEquiv.apply_symm_apply] at e
  rw [e, ha, map_pow]

end GlobalTheory.DecLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionLocalAway
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

noncomputable section
namespace GlobalTheory.CrysChiOne

variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locC_cont' (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : Continuous fun g => M g) : Continuous fun g => TruncatedSeriesCountingIdentities.locC C M g := by
  refine continuous_matrix fun a b => ?_
  have h1 : Continuous fun g : Br.G D.nbr i w hw => M ((Br.iota D.nbr i w hw g : Gw D.nd w) : GE D.nd) a b :=
    (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  have h2 : Continuous fun y : D.nd.O i => (((D.nbr i w hw).eO y : ↥(OL (D.nbr i w hw).LL)) :
      ↥(D.nbr i w hw).LL.1) := continuous_subtype_val.comp (D.nbr i w hw).eO_cont
  have h3 : Continuous fun y : ↥(D.nbr i w hw).LL.1 => C.inc y :=
    Continuous.subtype_mk continuous_subtype_val _
  exact h3.comp (h2.comp h1)

theorem sub_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))))
    (hcont : Continuous fun g => rO D.nd i r π g)
    {k : ℕ} (N : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hN : Continuous fun g => N g)
    (B : Matrix (Fin D.R.nV) (Fin k) (KK D.nd i)) (A : Matrix (Fin k) (Fin D.R.nV) (KK D.nd i))
    (hAB : A * B = 1)
    (hint : ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) N g) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C N)) := by
  let φ := GlobalTheory.HTW.RecS.Model.phiK i w hw C
  let Bt : Matrix (Fin D.R.nV) (Fin k) ↥C.LL.1 := B.map φ
  have hinj : Function.Injective Bt.mulVec := by
    have h1 : A.map φ * Bt = 1 := by
      rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (A.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  have hcN : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C N g).mulVec v :=
    fun _ v => (locC_cont' C N hN).matrix_mulVec continuous_const
  have hcR : ∀ (_ : Unit) (v : Fin D.R.nV → ↥C.LL.1), Continuous fun g => (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π) g).mulVec v :=
    fun _ v => (locC_cont' C _ hcont).matrix_mulVec continuous_const
  have hsub : IsSubOfSums (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => TruncatedSeriesCountingIdentities.locC C N) hcN ()).ρ
      (fun _ : Unit => ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))) := by
    refine ⟨1, fun _ => (), LinearMap.pi fun _ => Matrix.mulVecLin Bt, ?_, fun g v => ?_⟩
    · intro u v huv
      exact hinj (congrFun huv 0)
    · have key : ∀ (u : Fin k → ↥C.LL.1), Bt.mulVec ((TruncatedSeriesCountingIdentities.locC C N g).mulVec u) =
          (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π) g).mulVec (Bt.mulVec u) := by
        intro u
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        congr 1
        rw [GlobalTheory.HTW.RecS.Model.locC_eq_map, GlobalTheory.HTW.RecS.Model.locC_eq_map]
        simp only [Bt]
        rw [← Matrix.map_mul, ← Matrix.map_mul, hint]
      funext a
      exact key v
  exact (subsum_crys (fun _ : Unit => TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π)) hcR hF (S := fun _ => Set.univ)
    (fun _ => hcr) (fun _ _ _ _ => Set.mem_univ _) _ hsub).1

def chiM (c : ℕ) : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i) :=
  twistM (1 : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i)) (chiU D.nd i c)

theorem decomp_rho (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) :
    ∃ (B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i)) (A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i)),
      A * B = 1 ∧ ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) (rhoO D.nd i ρ π) g := by
  obtain ⟨e, he⟩ := hd
  refine ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inl (KK D.nd i) _ _),
    LinearMap.toMatrix' (LinearMap.fst (KK D.nd i) _ _ ∘ₗ e.toLinearMap), ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    apply e.injective
    rw [he]
    simp
    rfl

theorem decomp_chi (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π) :
    ∃ (B : Matrix (Fin D.R.nV) (Fin 1) (KK D.nd i)) (A : Matrix (Fin 1) (Fin D.R.nV) (KK D.nd i)),
      A * B = 1 ∧ ∀ g, mapM (toK D.nd i) (rO D.nd i r π) g * B = B * mapM (toK D.nd i) (chiM (D := D) (i := i) 1) g := by
  obtain ⟨e, he⟩ := hd
  have ht : 0 < D.R.t := by
    have := D.R.rank_add_five_le
    omega
  let c0 : Fin D.R.t := ⟨0, ht⟩
  let L : (Fin 1 → KK D.nd i) →ₗ[KK D.nd i] (Fin D.R.t → KK D.nd i) :=
    LinearMap.single (KK D.nd i) (fun _ => KK D.nd i) c0 ∘ₗ LinearMap.proj 0
  let L' : (Fin D.R.t → KK D.nd i) →ₗ[KK D.nd i] (Fin 1 → KK D.nd i) :=
    LinearMap.pi fun _ => LinearMap.proj c0
  refine ⟨LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr (KK D.nd i) _ _ ∘ₗ L),
    LinearMap.toMatrix' (L' ∘ₗ LinearMap.snd (KK D.nd i) _ _ ∘ₗ e.toLinearMap), ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [L, L']
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, Matrix.toLin'_apply,
      LinearEquiv.coe_coe]
    apply e.injective
    rw [he]
    simp only [LinearEquiv.apply_symm_apply, LinearMap.inr_apply]
    ext c
    · simp
    · simp only [L, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.single_apply]
      by_cases hc : c = c0
      · subst hc
        simp [chiM, twistM, mapM, Matrix.mulVec, dotProduct, c0]
      · simp [Pi.single_apply, hc]

theorem chiM_cont (c : ℕ) : Continuous fun g => chiM (D := D) (i := i) c g := by
  have : (fun g => chiM (D := D) (i := i) c g) = fun g => ((D.nd.chi i c g : (D.nd.O i)ˣ) : D.nd.O i) • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    funext g
    simp [chiM, twistM]
  rw [this]
  exact (D.nd.chi_cont i c).smul continuous_const

theorem locC_chiM_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1) g 0 0 = ((TruncatedSeriesCountingIdentities.chi1C C g : (↥C.LL.1)ˣ) : ↥C.LL.1) := by
  simp [TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, chiM, twistM, Br.loc, Br.locChi, Br.locM, Br.locO, Br.chiG, mapM, LocBridge.toLL]

theorem chi1inv_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition (D := D) i r ρ π)
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rO D.nd i r π))))
    (hcont : Continuous fun g => rO D.nd i r π g) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (WeaklyAdmissibleFiltrations.charRep (TruncatedSeriesCountingIdentities.chi1C C)⁻¹) := by
  obtain ⟨B, A, hAB, hint⟩ := decomp_chi r ρ π hd
  have h1 : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1))) :=
    sub_crys C hF r π hcr hcont _ (chiM_cont 1) B A hAB hint
  have h2 := (GlobalTheory.HTW.Rec.tateDual_matRep_crys (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1)) hF.2.2.1 (locC_cont' C _ (chiM_cont 1)) h1).2
  have h3 : IsCrys (Br.PD D.loc D.nbr i w hw)
      (WeaklyAdmissibleFiltrations.charRep ((TruncatedSeriesCountingIdentities.chi1C C)⁻¹ * cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) := by
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv _ (LinearEquiv.funUnique (Fin 1) ↥C.LL.1 ↥C.LL.1) ?_ h2
    intro g v
    simp only [LinearEquiv.funUnique_apply, Function.eval]
    change ((twistM (dualM (TruncatedSeriesCountingIdentities.locC C (chiM (D := D) (i := i) 1))) _ g).mulVec v) 0 = _
    simp [twistM, dualM, Matrix.mulVec, dotProduct, WeaklyAdmissibleFiltrations.charRep, locC_chiM_apply]
    left
    rw [mul_comm]
    rfl
  exact (GlobalTheory.BlockCrys.isCrys_mul_cyc _ _).1 h3

theorem twist_crys (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 ↥(OL C.LL))
    {k : ℕ} (M : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥C.LL.1) (χ : Br.G D.nbr i w hw →* (↥C.LL.1)ˣ)
    (hM : Continuous fun g => M g) (hM' : Continuous fun g => twistM M χ g)
    (hχ : IsCrys (Br.PD D.loc D.nbr i w hw) (WeaklyAdmissibleFiltrations.charRep χ))
    (hcr : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep M)) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (twistM M χ)) := by
  have hc : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (M g).mulVec v :=
    fun _ v => hM.matrix_mulVec continuous_const
  have hc' : ∀ (_ : Unit) (v : Fin k → ↥C.LL.1), Continuous fun g => (twistM M χ g).mulVec v :=
    fun _ v => hM'.matrix_mulVec continuous_const
  refine (hF.2.1 (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => M) hc ())
    (GRep.mat (Qp := ℚ_[D.nd.l i]) (O := ↥(OL C.LL)) (fun _ : Unit => twistM M χ) hc' ()) χ
    ⟨LinearEquiv.refl _ _, fun g x => ?_⟩ hχ hcr).1
  have key : ∀ u : Fin k → ↥C.LL.1, (twistM M χ g).mulVec u = ((χ g : (↥C.LL.1)ˣ) : ↥C.LL.1) • (M g).mulVec u := by
    intro u
    ext j
    simp [twistM, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  exact key x

theorem locC_WpO (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π) = twistM (TruncatedSeriesCountingIdentities.locC C (rhoO D.nd i ρ π)) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹ := by
  apply MonoidHom.ext
  intro g
  apply Matrix.ext
  intro a b
  have key : ∀ u v : D.nd.O i, C.inc ((D.nbr i w hw).toLL (u * v)) =
      C.inc ((D.nbr i w hw).toLL u) * C.inc ((D.nbr i w hw).toLL v) := by
    intro u v
    rw [map_mul, map_mul]
  exact key _ _

theorem cyc_locC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (g : Br.G D.nbr i w hw) :
    ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) := by
  have h := congrArg (fun u : (Br.LL D.nbr i w hw)ˣ => C.inc (u : Br.LL D.nbr i w hw))
    (GlobalTheory.CycBridge.locChi_epsU D i w hw g)
  refine Eq.trans ?_ h.symm
  exact ((IntermediateField.inclusion C.le).commutes _).symm

theorem locC_rDuO (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (x : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (rDuO D.nd i r x) =
      twistM (dualM (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  ext g a b
  simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cyc_locC]
  congr 1
  show C.inc ((D.nbr i w hw).toLL (rDuO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) *
      C.inc ((D.nbr i w hw).toLL (rTwO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) b a))
  rw [← map_mul, ← map_mul, map_inv, map_inv]
  congr 2
  all_goals (simp [rDuO, rTwO, T2O, WpO, twistM, dualM] <;> ring)

theorem locC_T2O (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) :
    TruncatedSeriesCountingIdentities.locC C (T2O D.nd i ρ π) =
      twistM (dualM (TruncatedSeriesCountingIdentities.locC C (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  ext g a b
  simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply,
    smul_eq_mul, cyc_locC]
  congr 1
  show C.inc ((D.nbr i w hw).toLL (T2O D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) =
    C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) *
      C.inc ((D.nbr i w hw).toLL (WpO D.nd i ρ π (decS D.nd w (Br.iota D.nbr i w hw g⁻¹)) b a))
  rw [← map_mul, ← map_mul, map_inv, map_inv]
  congr 2
  all_goals (simp [rDuO, rTwO, T2O, WpO, twistM, dualM] <;> ring)

end GlobalTheory.CrysChiOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeterminantRecCompatibleStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_rec_compatible : StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (t : ℕ) χ hχ, rc (cls (IrrRep.det (Fin t) χ hχ)) = sumList ((List.range t).map fun j : ℕ => (rc (.ofChar χ hχ)).lpTw (((t : ℝ) - 1) / 2 - j)) := by
  first | exact @GlobalTheory.lawsLit_det | exact GlobalTheory.lawsLit_det | (intros; apply GlobalTheory.lawsLit_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensionsStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantIso_transport_cocycles_extensions : ∀ {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M'), (∀ g x, e (W g x) = W' g (e x)) →
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  first | exact @GlobalTheory.TransportCoef.transport | exact GlobalTheory.TransportCoef.transport | (intros; apply GlobalTheory.TransportCoef.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivStableLatticeIntegralCharacterStatement
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_stableLattice_integralCharacter : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  first | exact @GlobalTheory.CharLat.exists_equiv_charLattice | exact GlobalTheory.CharLat.exists_equiv_charLattice | (intros; apply GlobalTheory.CharLat.exists_equiv_charLattice <;> assumption)
end

