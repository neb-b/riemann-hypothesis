module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNeZeroMemJumpTypeTwo
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0029
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousTwistedDualRhoO
section
noncomputable section

namespace GlobalTheory.HTW.RecS.Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.HTW.Rec GlobalTheory.HTW.RecS

theorem coefExt_dvr {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    ∃ _ : IsDomain ↥(OL Cx.LL), IsDiscreteValuationRing ↥(OL Cx.LL) ∧ IsFractionRing ↥(OL Cx.LL) ↥Cx.LL.1 :=
  (goodO_finExt_integers _ Cx.LL).1

section Std

variable {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {k : ℕ}

theorem mem_stdG_OL (x : Fin k → ↥LL.1) : x ∈ stdG ↥(OL LL) ↥LL.1 k ↔ ∀ j, x j ∈ OL LL := by
  constructor
  · rintro ⟨u, rfl⟩ j
    exact (u j).2
  · intro h
    exact ⟨fun j => ⟨x j, h j⟩, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
def stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Lat K LL where
  V := Fin k → ↥LL.1
  ρ := matRep M
  cont := hc
  L :=
    { T := stdG ↥(OL LL) ↥LL.1 k
      stable := fun g x hx => by
        rw [mem_stdG_OL] at hx ⊢
        intro j
        change ∑ b, M g j b * x b ∈ OL LL
        exact Subalgebra.sum_mem _ fun b _ => Subalgebra.mul_mem _ (hO g j b) (hx b)
      fg := by
        rw [stdG, LinearMap.range_eq_map]
        exact (Module.Finite.fg_top).map _
      free := Module.Free.of_equiv (LinearEquiv.ofInjective _ (stdG_inj Subtype.val_injective k))
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL.1 (Fin k)).span_eq]
        apply Submodule.span_mono
        rintro _ ⟨j, rfl⟩
        refine ⟨Pi.single j 1, ?_⟩
        funext j'
        simp [Pi.single_apply] }

theorem stdLat_isMatRep (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : IsMatRep (stdLat M hO hc) M :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem finrank_stdLat (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1) (hO : ∀ g a b, M g a b ∈ OL LL)
    (hc : ∀ v, Continuous fun g => (M g).mulVec v) : Module.finrank ↥LL.1 (stdLat M hO hc).V = k :=
  Module.finrank_fin_fun _

def latId (T : Lat K LL) : LatHom T.L T.L where
  f := LinearMap.id
  equiv _ _ := rfl
  cont := continuous_id
  T_le _ h := h

theorem latId_onto (T : Lat K LL) : (latId T).Onto := fun y hy => ⟨y, hy, rfl⟩

end Std

section LocRep

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
  (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

theorem locC_mem_OL {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw)
    (a b : Fin k) : TruncatedSeriesCountingIdentities.locC Cx M g a b ∈ OL Cx.LL := by
  have h1 : Br.loc D.nbr i w hw M g a b ∈ OL (D.nbr i w hw).LL :=
    ((D.nbr i w hw).eO (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)).2
  change Cx.inc (Br.loc D.nbr i w hw M g a b) ∈ OL Cx.LL
  exact IsIntegral.map ((IntermediateField.inclusion Cx.le).restrictScalars ℤ_[D.nd.l i]) h1

end LocRep

section Glob

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem continuous_twistedDual_rhoO (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous fun g => T2O D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have hW : Continuous fun g => WpO D.nd i ρ π g := h1.smul hρ
  have hε : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  exact hε.smul (hW.comp continuous_inv).matrix_transpose

end Glob

section Sub

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

def phiK : KK D.nd i →+* ↥Cx.LL.1 := Cx.inc.comp (Br.toLLK (D.nbr i w hw))

theorem locC_eq_map {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC Cx M g = (mapM (toK D.nd i) M (decS D.nd w (Br.iota D.nbr i w hw g))).map (phiK i w hw Cx) := by
  refine Matrix.ext fun a b => ?_
  change Cx.inc ((D.nbr i w hw).toLL (M _ a b)) = Cx.inc (Br.toLLK (D.nbr i w hw) (toK D.nd i (M _ a b)))
  rw [Br.toLLK_alg]
  rfl

theorem mapM_rDuO (h : GE D.nd) :
    mapM (toK D.nd i) (rDuO D.nd i r π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rO D.nd i r π) h⁻¹).transpose := by
  ext a b
  simp [mapM, rDuO, twistM, dualM]

theorem mapM_T2O (h : GE D.nd) :
    mapM (toK D.nd i) (T2O D.nd i ρ π) h = toK D.nd i (((chiU D.nd i 1 * epsU D.nd i) h : (D.nd.O i)ˣ) : D.nd.O i) •
      (mapM (toK D.nd i) (rhoO D.nd i ρ π) h⁻¹).transpose := by
  ext a b
  simp [mapM, T2O, WpO, twistM, dualM]
  ring

end Sub

section Sub2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)

theorem isSubOfSums_T2O (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    IsSubOfSums (matRep (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π))) fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r x)) := by
  obtain ⟨e, he⟩ := hd
  let A : Matrix (Fin D.R.r) (Fin D.R.nV) (KK D.nd i) :=
    LinearMap.toMatrix' ((LinearMap.fst (KK D.nd i) _ _).comp e.toLinearMap)
  let B : Matrix (Fin D.R.nV) (Fin D.R.r) (KK D.nd i) :=
    LinearMap.toMatrix' (e.symm.toLinearMap.comp (LinearMap.inl (KK D.nd i) _ _))
  have hA : ∀ u, A.mulVec u = (e u).1 := fun u => by simp [A, LinearMap.toMatrix'_mulVec]
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun v => ?_
    simp
  have hint : ∀ h : GE D.nd, A * mapM (toK D.nd i) (rO D.nd i r π) h = mapM (toK D.nd i) (rhoO D.nd i ρ π) h * A := by
    intro h
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hA, hA, he]
  let φ := phiK i w hw Cx
  let At : Matrix (Fin D.R.nV) (Fin D.R.r) ↥Cx.LL.1 := A.transpose.map φ
  have hinj : Function.Injective At.mulVec := by
    have h1 : B.transpose.map φ * At = 1 := by
      rw [← Matrix.map_mul, ← Matrix.transpose_mul, hAB, Matrix.transpose_one, Matrix.map_one _ (map_zero φ) (map_one φ)]
    intro u v huv
    have := congrArg (B.transpose.map φ).mulVec huv
    simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
  refine ⟨1, fun _ => π, LinearMap.pi fun _ => Matrix.mulVecLin At, ?_, fun g v => ?_⟩
  · intro u v huv
    exact hinj (congrFun huv 0)
  · funext a
    change At.mulVec ((TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π) g).mulVec v) =
      (TruncatedSeriesCountingIdentities.locC Cx (rDuO D.nd i r π) g).mulVec (At.mulVec v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    rw [locC_eq_map, locC_eq_map, mapM_rDuO, mapM_T2O]
    have hK : ∀ (s : KK D.nd i) (h : GE D.nd),
        A.transpose * (s • (mapM (toK D.nd i) (rhoO D.nd i ρ π) h).transpose) =
          (s • (mapM (toK D.nd i) (rO D.nd i r π) h).transpose) * A.transpose := by
      intro s h
      rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hint]
    simp only [At]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hK]

end Sub2

theorem exists_lattices {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw)
    (h : PtIn i r ρ π) :
    ∃ (T₁ T₂ : Lat (D.nbr i w hw).Kw Cx.LL) (F : LatHom T₁.L T₂.L),
      IsSubOfTwistedDualSums i r w hw Cx T₁ ∧ IsTwistedDualOfGaloisRep i ρ π w hw Cx T₂ ∧ F.Onto ∧ Module.finrank ↥Cx.LL.1 T₂.V = D.R.r := by
  let T := stdLat (TruncatedSeriesCountingIdentities.locC Cx (T2O D.nd i ρ π)) (locC_mem_OL i w hw Cx _)
    (fun v => locC_cont D i _ (continuous_twistedDual_rhoO i ρ π h.contρ) w hw Cx v)
  exact ⟨T, T, latId T, isSubOfSums_T2O i r ρ π w hw Cx h.dec, stdLat_isMatRep _ _ _, latId_onto T,
    finrank_stdLat _ _ _⟩

end GlobalTheory.HTW.RecS.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCoprimeMulIsIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

noncomputable section

namespace GlobalTheory.KerTie.MuqUnit

theorem dvd_absNorm_of_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {p : ℕ} (hp : p.Prime)
    (h : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal) : p ∣ Ideal.absNorm P.asIdeal := by
  by_contra hn
  have hc : IsCoprime ((p : ℤ)) ((Ideal.absNorm P.asIdeal : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1 : (1 : 𝓞 E) ∈ P.asIdeal := by
    rw [← hab]
    refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
    · simpa using h
    · simpa using Ideal.absNorm_mem P.asIdeal
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem exists_coprime_mul_isIntegral {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime) (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    ∃ M : ℕ, M.Coprime p ∧ IsIntegral ℤ ((M : K) * x) := by
  have halg : IsAlgebraic ℤ x :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  have hd0 : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  have hdint : IsIntegral ℤ ((y.natAbs : K) * x) := by
    rcases Int.natAbs_eq y with e | e
    · have e2 : ((y.natAbs : ℤ) : K) = (y : K) := congrArg (fun z : ℤ => (z : K)) e.symm
      have : (y.natAbs : K) * x = y • x := by
        rw [zsmul_eq_mul, ← e2, Int.cast_natCast]
      rw [this]; exact hyint
    · have : (y.natAbs : K) * x = -(y • x) := by
        rw [zsmul_eq_mul, ← neg_mul]; congr 1
        have e' : (y : K) = -((y.natAbs : ℤ) : K) := by
          have := congrArg (fun z : ℤ => (z : K)) e
          simpa using this
        rw [e', neg_neg, Int.cast_natCast]
      rw [this]; exact hyint.neg
  obtain ⟨e, M, hpM, hd⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.ne_one
  refine ⟨M, (Nat.Prime.coprime_iff_not_dvd hp).2 hpM |>.symm, ?_⟩
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((M : K) * x) fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 K) ∈ w.asIdeal
    · rw [map_mul]
      refine mul_le_one' ?_ (h w hw)
      have := w.valuation_le_one (K := K) (M : 𝓞 K)
      simpa using this
    · obtain ⟨s, hs⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 K) K ((y.natAbs : K) * x) fun v => by
        obtain ⟨t, ht⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).1 hdint
        rw [← ht]; exact v.valuation_le_one t
      have hp1 : w.valuation K (p : K) = 1 := by
        have := (w.intValuation_eq_one_iff (x := ((p : ℕ) : 𝓞 K))).2 hw
        rw [← map_natCast (algebraMap (𝓞 K) K), HeightOneSpectrum.valuation_of_algebraMap]
        exact this
      have hle : w.valuation K ((y.natAbs : K) * x) ≤ 1 := by rw [← hs]; exact w.valuation_le_one s
      rw [hd, Nat.cast_mul, Nat.cast_pow, mul_assoc, map_mul, map_pow, hp1, one_pow, one_mul] at hle
      exact hle
  rw [← hr]
  exact RingOfIntegers.isIntegral_coe r

theorem intOff_of_val {K : Type} [Field K] [NumberField K] (σ : K →+* ℂ) (S : Finset ℕ) (x : K)
    (h : ∀ p : ℕ, p.Prime → p ∉ S → ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∈ w.asIdeal → w.valuation K x ≤ 1) :
    IntOff S (σ x) := by
  have hQ : σ x ∈ TaylorLogMetric.Qbar := by
    rw [TaylorLogMetric.Qbar, mem_algebraicClosure_iff']
    exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map σ.toRatAlgHom
  refine ⟨hQ, fun p hp lam hpS => ?_⟩
  rw [lamC_of_mem lam hQ]
  obtain ⟨M, hM, hint⟩ := exists_coprime_mul_isIntegral hp.out x (h p hp.out hpS)
  have h1 : IsIntegral ℤ ((M : ℂ) * σ x) := by
    have := map_isIntegral_int σ hint
    simpa using this
  have h2 : IsIntegral ℤ ((M : TaylorLogMetric.Qbar) * (⟨σ x, hQ⟩ : TaylorLogMetric.Qbar)) :=
    (isIntegral_algHom_iff ((algebraMap TaylorLogMetric.Qbar ℂ).toIntAlgHom) Subtype.val_injective).1 (by simpa using h1)
  exact GlobalTheory.HeckeVal.norm_le_one_of_denom lam hM h2

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

open GlobalTheory.CharVal

variable {X : Fields} {Pr : Primes X} {m : ℕ} {Ch : Chars X Pr m} {σ₀ : X.K →+* ℂ} {e : X.Tau → ℚ} {j : Fin m}
  {μ : Formalism.L2.Host.HChar X.E}

theorem mu_core_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) (P : HeightOneSpectrum (𝓞 X.E)) (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) :
    ∃ (M : ℕ) (z : X.E) (n : X.Tau → ℤ), 0 < M ∧ (∀ τ, (n τ : ℚ) = 2 * e τ) ∧ P.valuation X.E z = P.valuation X.E (k : X.E) ^ M ∧
      (∀ Q : HeightOneSpectrum (𝓞 X.E), Q ≠ P → Q.valuation X.E z = 1) ∧ c ^ (2 * M) = ∏ τ, X.emb τ (z / star z) ^ n τ := by
  classical
  have hg : ∀ i, ((Pr.g i : ℕ) : 𝓞 X.E) ≠ 0 := fun i => by exact_mod_cast (hPr.g_prime i).ne_zero
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf X.E μ (divs ((Pr.g 0 : ℕ) : 𝓞 X.E) ∪ divs ((Pr.g 1 : ℕ) : 𝓞 X.E))
    (productRule μ) (fun v hv => hμ.unr v fun i hi => hv (by
      rw [Finset.mem_union, mem_divs (hg 0), mem_divs (hg 1)]
      fin_cases i
      exacts [Or.inl hi, Or.inr hi])) hμ.tame P k
  obtain ⟨n, hn, hinf⟩ := hμ.inf
  refine ⟨M, z, fun τ => -n τ, hM, fun τ => by push_cast; rw [hn]; ring, h1, h2, σ₀.injective ?_⟩
  have h4 : ((μ.locK P k : ℂˣ) : ℂ) ^ M = (((μ.inf z : ℂˣ) : ℂ))⁻¹ := by
    rw [← Units.val_pow_eq_pow_val, eq_inv_of_mul_eq_one_left h3, Units.val_inv_eq_inv_val]
  rw [map_pow, hc, mul_comm 2 M, pow_mul, h4, hinf z, ← Finset.prod_inv_distrib, ← Finset.prod_pow, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, ← zpow_neg, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  congr 1
  change _ = X.embC σ₀ τ (z / star (z : X.E))
  have h0 : X.embC σ₀ τ (z : X.E) ≠ 0 := by simp
  rw [map_div₀, hconj, div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rfl

theorem mu_unit_of_conj (hconj : ∀ τ (x : X.E), X.embC σ₀ τ (star x) = starRingEnd ℂ (X.embC σ₀ τ x)) (hPr : Pr.Ok)
    (hμ : IsMu0 Ch σ₀ e j μ) {P : HeightOneSpectrum (𝓞 X.E)} (k : X.Eˣ) {c : X.K}
    (hc : σ₀ c = ((μ.locK P k : ℂˣ) : ℂ)) {p : ℕ} (hP : ((p : ℕ) : 𝓞 X.E) ∉ P.asIdeal) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((p : ℕ) : 𝓞 X.K) ∈ w.asIdeal) : w.valuation X.K c = 1 := by
  obtain ⟨M, z, n, hM, -, -, h2, h3⟩ := mu_core_of_conj hconj hPr hμ P k hc
  refine unit_of_pow (M := 2 * M) (by omega) ?_
  rw [h3]
  refine val_prod_unit w (fun τ => ?_) n
  have h4 := (natCast_mem_pullW τ w p).2 hw
  rw [map_div₀, ← valuation_conjP, h2 _ (fun e' => hP (e' ▸ h4)), h2 _ (fun e' => hP (e' ▸ (natCast_mem_conjP _ p).2 h4)), div_one]

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie.MuqUnit

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem embC_star (t : KerEntTied ex) (τ : t.X.Tau) (x : t.X.E) :
    t.X.embC t.seam.σ₀ τ (star x) = starRingEnd ℂ (t.X.embC t.seam.σ₀ τ x) := by
  change t.seam.σ₀ (t.X.emb τ (star x)) = starRingEnd ℂ (t.seam.σ₀ (t.X.emb τ x))
  rw [t.seam_ok.1, t.seam_ok.1, t.seam_ok.2]
  exact D.host.conjE_apply (TaylorLogMetric.embT D (t.seam.iT τ)) (t.seam.iE x)

end GlobalTheory.KerTie.MuqUnit

namespace GlobalTheory.KerTie

open MuqUnit

theorem muq_intOff : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < D.R.m → ∀ P : rowSG t.Pr t.sel (t.tup μ), P.1 ∉ t.Pr.vGs → IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)) ∧ IntOff (t.O u μ).S (t.seam.σ₀ ((t.cst μ).muq (i + 1) P)⁻¹) := by
  intro D L hT Gi Gl K Y cX ex t hmu hval u μ hQg i hi P hP
  have hPQ : P.1 ∈ QE t.sel (t.tup μ : Chr t.X.F t.X.E t.X.K) := (Finset.mem_union.1 P.2).resolve_left hP
  have hg : ∀ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun k hk =>
    hQg k (t.g_rec k ▸ (t.Q_rec μ (t.Pr.g k)).2 ⟨t.pr_ok.g_prime k, P.1, hPQ, hk⟩)
  have hq := (t.idx_ok μ).muqQ i hi P hP
  have key : ∀ p : ℕ, p.Prime → p ∉ (t.O u μ).S → ∀ w : HeightOneSpectrum (𝓞 t.X.K), ((p : ℕ) : 𝓞 t.X.K) ∈ w.asIdeal →
      w.valuation t.X.K ((t.cst μ).muq (i + 1) P) = 1 := by
    intro p hp hpS w hw
    have hpP : ((p : ℕ) : 𝓞 t.X.E) ∉ P.1.asIdeal := fun h =>
      hpS ((sNum_qOf_rowSG D L hT Gi Gl K Y cX ex t u μ P).2 p hp (dvd_absNorm_of_mem P.1 hp h))
    obtain ⟨e, he⟩ := hmu ⟨i, hi⟩
    have hm := mu_unit_of_conj (embC_star t) t.pr_ok he (Formalism.L2.Host.unif P.1) (hval ⟨i, hi⟩ P.1 hg) hpP hw
    have htw := (GlobalTheory.ColPeriod.twistUnit t.X.F t.X.E t.X.K t.S (t.tup μ) P.1 w).2
    rw [hq, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_mul, map_inv₀, map_inv₀, hm, htw]
    simp
  refine ⟨intOff_of_val _ _ _ fun p hp hpS w hw => (key p hp hpS w hw).le, ?_⟩
  have h2 := intOff_of_val t.seam.σ₀ (t.O u μ).S ((t.cst μ).muq (i + 1) P)⁻¹ fun p hp hpS w hw => by
    rw [map_inv₀, key p hp hpS w hw, inv_one]
  exact h2

end GlobalTheory.KerTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.InertHeckeLift

theorem dualC_single {d : List ℤ} (hd : dualLab d = d) :
    dualC (Finsupp.mapRange star (star_zero ℂ) (Finsupp.single d (1 : ℂ))) = Finsupp.single d 1 := by
  rw [Finsupp.mapRange_single, star_one, dualC, Finsupp.mapDomain_single, hd]

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, one_apply_eq_self, hk, Units.val_one, one_smul] at h2

theorem csum_adj {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (M : HMod (Gr → W)) (hM : M.Is (Bridge.AdForms ι ρ J χ) (Bridge.adInner ι J P.y))
    (jm : S.Forms → M.H) (hj : ∀ f, M.e (jm f) = P.ext f.1) (U : Module.End K S.Forms) (u : Module.End ℂ M.H)
    (hu : LinearMap.adjoint u = u) (hU : ∀ f, jm (U f) = u (jm f)) (f g : S.Forms) :
    S.csum (U f).1 g.1 = S.csum f.1 (U g).1 := by
  have hin : ∀ f g : S.Forms, inner ℂ (jm f) (jm g) = σ (S.csum f.1 g.1) := by
    intro f g
    rw [hM.2.2, hj, hj]
    exact (GlobalTheory.classPres_basic ι S σ ρ J χ P).2.1 f g
  apply σ.injective
  rw [← hin, ← hin, hU, hU, ← LinearMap.adjoint_inner_right, hu]

theorem tie_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {I : Type} {pl : I → Pl D.host.E}
    {ty : I → List ℤ} {op : I → Module.End K S.Forms} {inR : I → Prop}
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op inR (fun i => IsLabElt V (pl i) (ty i)) (fun i => IsLocElt V (pl i)))
    (i : I) (hi : inR i) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl i ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl i))
    (hpw : (ty i).Pairwise (fun a b => b ≤ a)) :
    IsLab V (pl i) (ty i) ∧ ∀ f : S.Forms, Pr.ext (op i f).1 = hkF V (pl i) (Finsupp.single (ty i) 1) (Pr.ext f.1) := by
  obtain ⟨c, hc⟩ := hβ
  rw [one_pow] at hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl i).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl i).isPrime.ne_top
  have hd := _root_.GlobalTheory.HkDict.dcOp_eq_label V β Λ 1 L hc (pl i) h1 hoff (ty i) (Comparison₂.hx i) (Comparison₂.hA i) hpw
    (Comparison₂.hx_ok i hi) (Comparison₂.hA_loc i hi) (Comparison₂.hDC i hi)
  exact ⟨hd.1, fun f => (Comparison₂.op_eq i hi f).trans (hd.2 W _ fun g k hk => ext_mul Pr f g k (Comparison₂.chi_loc i hi k hk))⟩

theorem inert_lifts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → ∀ j t, ∀ (I : Type) (pl : I → Pl D.host.E) (ty : I → List ℤ) (op : I → Module.End D.what₂.LL (A.MtCSD j t).Forms) (inR : I → Prop), (∀ i, inR i → Good R t (pl i) ∧ conjPl (pl i) = pl i ∧ (ty i).Pairwise (fun a b => b ≤ a)) → Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j t).pres op inR (fun i => IsLabElt (Vc D j) (pl i) (ty i)) (fun i => IsLocElt (Vc D j) (pl i)) → ∀ i, inR i → (∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL) ∧ (∀ f g : (A.MtCSD j t).Forms, (A.MtCSD j t).csum ((op i f : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V) (g : (A.MtCSD j t).Cl → (A.MtCSD j t).V) = (A.MtCSD j t).csum (f : (A.MtCSD j t).Cl → (A.MtCSD j t).V) ((op i g : (A.MtCSD j t).Forms) : (A.MtCSD j t).Cl → (A.MtCSD j t).V)) ∧ IsLab (Vc D j) (pl i) (ty i) ∧ ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM j t I pl ty op inR hin Comparison₂ i hi
  have hgood := (hin i hi).1
  have hd := tie_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres Comparison₂ i hi hgood (hin i hi).2.2
  have hj : ∀ f : (A.MtCSD j t).Forms, (R.HV j t).e (R.jV j t f) = (R.B.L j t).pres.ext f.1 := fun f => hM.jV j t f
  have hint : ∀ h, IsOpsV R j t h → ∀ f, R.jV j t (op i f) = h (pl i) (Finsupp.single (ty i) 1) (R.jV j t f) :=
    fun h hh f => (hM.HV j t).1 (((hj _).trans (hd.2 f)).trans
      ((congrArg (hkF (Vc D j) (pl i) (Finsupp.single (ty i) 1)) (hj f).symm).trans (hh (pl i) hgood _ _).symm))
  have hrat : ∀ a b, LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis (op i) a b ∈ cmMax D.what₂.LL := by
    obtain ⟨_, _, _, hT⟩ := hF.tie
    open GlobalTheory.HeckeRational in
    exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres
      (hT.coefL j t) (hT.mapL j) (fun g a b => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g a b).2)
      (Comparison₂.hA i) (op i) (Comparison₂.op_eq i hi)).2
  refine ⟨hrat, ?_, hd.1, hint⟩
  have hnormal : ∃ h, IsOpsV R j t h ∧ NormalFam (Good R t) h :=
    GlobalTheory.DefiniteOps.side (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (Good R t)
      (fun _ h => h) (R.cV j).coef.ρ (fun γ => (hM.cV j).2.1 γ) (R.B.L j t).pres.y (R.B.L j t).pres.reps
      (fun c => Finite.of_equiv _ ((R.B.L j t).pres.stabI c).toEquiv) (R.HV j t) (hM.HV j t)
  obtain ⟨h, hh⟩ := hnormal
  have hdual : dualLab (ty i) = ty i := ((_root_.GlobalTheory.LabChar.labels_char (Vc D j) (pl i) (ty i)).1 hd.1).2.2 (hin i hi).2.1
  have hadj := (hh.2.2 (pl i) hgood (Finsupp.single (ty i) 1)).trans (congrArg (h (pl i)) (dualC_single hdual))
  exact csum_adj (R.B.L j t).pres (R.HV j t) (hM.HV j t) (fun f => R.jV j t f) hj (op i) _ hadj (hint h hh.1)

end GlobalTheory.InertHeckeLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatakeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | exact GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | (intros; apply GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake <;> assumption)
end

