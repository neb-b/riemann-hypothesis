module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelSubgroupRestrictedProductOfLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0638
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0898
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwoReadings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0384
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Formalism.SatakeDualWeyl.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFinIdem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PartsSpanProof

theorem exists_isFinIdem {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    ∃ v, IsFinIdem D v f := by
  rcases h with ⟨⟨⟨-, -, v, ε, hv, he⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, hv, rfl⟩, -⟩
  · exact ⟨v, ε, hv, he⟩
  · exact ⟨v, ε, hv, rfl⟩

theorem exists_lift {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X)
    (he : Function.Injective e) (L : X →ₗ[ℂ] X) (hL : ∀ x, L (e x) ∈ LinearMap.range e) :
    ∃ h : Module.End ℂ H, ∀ x, e (h x) = L (e x) := by
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (L ∘ₗ e).codRestrict _ hL, fun x => ?_⟩
  exact congrArg Subtype.val ((LinearEquiv.ofInjective e he).apply_symm_apply ⟨L (e x), hL x⟩)

theorem dualLab_dualLab (d : List ℤ) : dualLab (dualLab d) = d := by
  simp [dualLab, List.map_reverse, List.map_map]


set_option maxHeartbeats 2000000 in
theorem partsSpan : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type)
    (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i S, PartsSpan R i S := by
  intro hC D G _ _ Pl0 T A Ks _ _ _ R F hL hF i S
  have hLP := GlobalTheory.LevelProduct.levProd_of_laws D G Pl0 T A Ks R F hL hF i
  have hS := (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hC R).2.2 i
  obtain ⟨inj, hr, hip⟩ := hL.models.HW i (sg0 D A)
  have hmem : ∀ x, (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := fun x => hr ▸ LinearMap.mem_range_self _ x
  have hlv := fun x v => ((GlobalTheory.MultMem.mem_mult_iff ..).1 (hmem x)).lev v
  let ι := {x : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D (Wc D i)) //
    Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S
      x.1 x.2.1 x.2.2}
  have keep : ∀ x : ι, ∀ U ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) x.1.2.2 U ∈ R.Wall i (sg0 D A) := by
    rintro ⟨⟨P, d, B⟩, e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, hB, hc⟩ U hU
    obtain ⟨v, hv⟩ := exists_isFinIdem hP
    exact GlobalTheory.LocalHeckeLevel.heckeOn_mem_wall hLP v f hv α hα B hB hc U hU
  have hex : ∀ x : ι, ∃ h : Module.End ℂ (R.HW i (sg0 D A)).H, ∀ y,
      (R.HW i (sg0 D A)).e (h y) = heckeOn (R.MW i (sg0 D A)) x.1.2.2 ((R.HW i (sg0 D A)).e y) :=
    fun x => exists_lift _ inj _ fun y => hr ▸ keep x _ (hmem y)
  choose op hop using hex
  have hcomm : Formalism.L2.Col.PairComm op := fun x x' => by
    refine LinearMap.ext fun y => inj ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hop, hop, hop, hop]
    exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.comm_heckeLin (J := levW R i)
      (GlobalTheory.HeckeAdjoint.realUnif D _) x.2 x'.2 (hlv y v)
  have hadj : ∀ x : ι, ∃ x', op x' = LinearMap.adjoint (op x) := by
    intro x
    obtain ⟨B', hB', -⟩ := GlobalTheory.SphericalOps.exists_dual (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D x.1.1) x.2
    let x' : ι := ⟨(x.1.1, dualLab x.1.2.1, B'), hB'⟩
    refine ⟨x', ?_⟩
    rw [LinearMap.eq_adjoint_iff]
    intro a b
    rw [hip, hip, hop, hop]
    unfold ipAt
    congr 1
    exact GlobalTheory.HeckeAdjoint.ipM_heckeOn_dualLab D (Wc D i) _ R.θ (R.MW i (sg0 D A)) (levW R i) _ S (R.νW i) (R.fdW i)
      hL.models.inf (hL.models.νW i).1.1 (hL.models.νW i).2 hS x.1.1 (dualLab x.1.2.1) B' x.1.2.2 hB'
      (by rw [dualLab_dualLab]; exact x.2) _ (hmem a) _ (hmem b) (keep x' _ (hmem a)) (keep x _ (hmem b))
  obtain ⟨h1, h2, -⟩ := GlobalTheory.normalFamily_orthogonal_decomposition op hcomm hadj
  classical
  unfold PartsSpan
  refine eq_top_iff.2 (h2 ▸ iSup_le fun y => ?_)
  refine le_iSup_of_le (fun P d => if h : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B then y ⟨(P, d, h.choose), h.choose_spec⟩ else 0) ?_
  intro x hx
  rw [h1, Submodule.mem_iInf] at hx
  show (R.HW i (sg0 D A)).e x ∈ partFull _ _ _ _ _ _
  unfold partFull
  refine Submodule.mem_inf.2 ⟨hmem x, ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  intro P d B hB
  have hE : ∃ B, Hecke₂ (Wc D i) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) S P d B := ⟨B, hB⟩
  rw [dite_eq_left hE]
  have e1 := Module.End.mem_eigenspace_iff.1 (hx ⟨(P, d, hE.choose), hE.choose_spec⟩)
  have e2 := congrArg (R.HW i (sg0 D A)).e e1
  rw [hop, map_smul] at e2
  rw [← e2]
  exact MultilinearMap.ext fun v => GlobalTheory.SphericalOps.labelUnique (J := levW R i) (GlobalTheory.HeckeAdjoint.realUnif D)
    P d B _ hB hE.choose_spec _ (hlv x v)

end GlobalTheory.PartsSpanProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
section
noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting GlobalTheory.ToricDistribution

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : ∀ a w, OverP D.host D.host.pde w ∨ OverP D.host D.host.pde' w → ∃ w', below w' = below w ∧ TeichTriv (Z.chi a) w') :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z := by
  let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
    ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
  have hcu : ∀ i a P, P ∉ T.S0 i → (Z.chi a).UnrAt P := fun i a P hP => chi_unr hZ a fun h => hP (hS i P h)
  have hpD : ∀ i v, v ∈ T.pD i ↔ OverP D.host (if T.l i = D.host.pde then D.host.pde' else D.host.pde) v := fun i v => by
    rw [← Finset.mem_coe, T.pD_eq]; rfl
  have hlu : ∀ i j a P, P ∉ T.S0 i → (Z.lam0 (T.l i) j a).UnrAt P := fun i j a P hP =>
    (((Z.C.isMu0 j).unr P fun k hk => hP (T.placesOver_subset_exceptional i k hk)).mul
      ((inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l i)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional i ((hpD i P).2 hk)))).mul (hcu i a P hP).inv
  choose K f f' hf hf' hK using fun i => exists_two_readings ((ι i).toRingHom.comp (κ i))
  have key := fun (i : T.Tw) (j a : Fin D.R.m) (b : Bool) =>
    hostHeckeFrame_toric_quotient_character C T.cc_cm ha (fun j τ => (D.hc _).e_int j) (T.l i) (T.O0 i) (T.twistBaseCoefficientRing_isAdic i) (κ i) (hκ i) (ι i) (K i)
      (K i).subtype (f i) (f' i) (hf i) (hf' i) (T.pD i) (T.pD_eq i) (T.delta i) (hδ i) (T.O i) (T.O_adic i) (T.O_l i) j b (Z.chi a) (Z.c a) (hZ.aux a).triv
      (by
        obtain ⟨n, hn, h⟩ := (hZ.aux a).inf
        have : n = fun τ => 2 * Z.c a τ := funext fun τ => by have := hn τ; beta_reduce at this; exact_mod_cast this
        exact this ▸ h)
      (fun v hv => by
        have h4 : OverP D.host D.host.pde v ∨ OverP D.host D.host.pde' v := by
          have := (hpD i v).1 hv
          split_ifs at this
          exacts [Or.inr this, Or.inl this]
        obtain ⟨w', e, h⟩ := hT a v h4
        exact chi_teich hZ a h4 e h)
      (valuesIn_of_unitary (hK i) (Z.C.isMu0 j).unitary (hμ i j))
      (valuesIn_of_unitary (hK i) (delAt_unitary_triv Z.C _).1 (valuesIn_of_isGal ha (hδ i)))
      (valuesIn_of_unitary (hK i) (hZ.aux a).unitary (hχ i a)) (T.S0 i) (T.twistExcludedPlaces_contains_residueChar i) (T.placesOver_subset_exceptional i) (T.primes_subset_exceptional i) (hcu i a)
  choose r g Xv h1 h2 h3 h4 h5 h6 h7 using key
  let L : (∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i)) → TwL T := fun th =>
    { abelian₂ := fun _ => Idx D.R
      jL := fun _ x => x.1.1 + 1
      sideL := fun _ x => x.2.2.2
      s2 := fun _ x => 2 * (x.2.2.1.1 : ℤ)
      jL_range := fun _ x => ⟨by omega, x.1.2⟩
      lamG := fun i x => g i x.1 x.2.1 x.2.2.2
      lamG_cont := fun i x => h3 i _ _ _
      lamG_unr := fun i x => h4 i _ _ _
      lamG_pD := fun i x => h5 i _ _ _
      lamG_anti := fun i x => h6 i _ _ _
      Xv := fun i x => Xv i x.1 x.2.1 x.2.2.2
      Xv_def := fun i x P hP => h7 i _ _ _ P hP _ (N.plOm.2 P)
      qs := fun i x P => ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ))
      qs_sq := fun i x P _ => by rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
      qs_conj := fun i x P P' h => by
        rw [show Ideal.absNorm P'.asIdeal = Ideal.absNorm P.asIdeal from by
          simpa [Ideal.absNorm_eq_natCard, Formalism.ConjugateSelfDual.normV] using
            GlobalTheory.TwistDet.normV_conj h]
      th := th }
  have hcl : ∀ th i (x : Idx D.R), (L th).jL i x = x.1.1 + 1 ∧ (L th).sideL i x = x.2.2.2 ∧
      (L th).s2 i x = 2 * (x.2.2.1.1 : ℤ) ∧
      (∃ n r, IsGal art (κ i) (sideIso (ι i) x.2.2.2) (Z.lam0 (T.l i) x.1 x.2.1) n r ∧
        (L th).lamG i x = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
      ∀ P, (L th).qs i x P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-(x.2.2.1.1 : ℤ)) := fun th i x => by
    refine ⟨rfl, rfl, rfl, ?_, fun _ => rfl⟩
    obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
    exact ⟨n, _, hn, h2 i _ _ _⟩
  rcases isEmpty_or_nonempty (TwF T) with hF | ⟨⟨F₀⟩⟩
  · exact ⟨L fun _ _ _ _ => 0, fun _ => Equiv.refl _, hcl _, fun F => hF.elim F⟩
  let X₀ := T.ntw hE F₀ (L fun _ _ _ _ => 0)
  choose ι₀ hι₀ using fun i => exists_reading X₀ i (κ i) (ι i) (hκ i)
  have m0 : ∀ i, (∀ x : D.LL0, ι₀ i (D.what₂.embLL (x : D.what₂.LL)) = toBar X₀ i (T.emb0 i x)) ∧
      ∀ x : Idx D.R, IsLam X₀ Z i (atSide X₀ x.2.2.2 (ι₀ i)) x x.1 x.2.1 x.2.2.1.1 := fun i => by
    refine ⟨fun x => by rw [← hι i x]; exact hι₀ i true _, fun x => ⟨rfl, ⟨rfl, ?_, ?_⟩, fun P hP => ?_⟩⟩
    · exact_mod_cast x.2.2.1.2.1
    · exact_mod_cast x.2.2.1.2.2
    · obtain ⟨n, hn⟩ := h1 i x.1 x.2.1 x.2.2.2
      exact xv_mul_val X₀ i (hι₀ i x.2.2.2) ha hn (h2 i _ _ _) hP (hlu i _ _ P hP)
  have hL : ToricSumFormula := _root_.GlobalTheory.ToricSumValue.toricSum_eq exists_isHeckeL_of_hasInf
  have tkey : ∀ i (x : Idx D.R), ∃ t : ∀ Q, T.RCG i Q → FractionRing (T.O i),
      ∀ th : ∀ i Q, X₀.abelian₂ i → X₀.RCG i Q → FractionRing (X₀.O i), (∀ Q, th i Q x = t Q) →
        IsThOf (setTh X₀ th) i (atSide X₀ x.2.2.2 (ι₀ i)) x (phi D.host) x.2.2.1.1 (Z.kap x.1 x.2.1 x.2.2.1.1)
          (cond0 D.host Z.w0) (Z.lam0 (T.l i) x.1 x.2.1) := fun i x => by
    have hl := (m0 i).2 x
    have hD := _root_.GlobalTheory.LamTie.toricCharacter_isCMHostValueDatum D Z hZ (T.l i) x.1 x.2.1 x.2.2.1.1 (by exact_mod_cast hl.2.1.2.1) hl.2.1.2.2
    exact exists_th_of hA hR hL (atSide_emb_mem (m0 i).1 _) hD (hS i) hl.2.2
  choose t ht using tkey
  let th : ∀ i Q, Idx D.R → T.RCG i Q → FractionRing (T.O i) := fun i Q x => t i x Q
  refine ⟨L th, fun _ => Equiv.refl _, hcl th, fun F => ?_⟩
  refine isLamTieFull_of_labels (fun _ x => x.1) (fun _ x => x.2.1) (fun _ x => x.2.2.1.1) (fun i _ => hS i)
    (fun i _ => ⟨ι₀ i, (m0 i).1, fun x => ⟨(m0 i).2 x, ht i x th fun _ => rfl⟩⟩)
    (fun i _ j a s b hs hs' => ⟨(j, a, ⟨s, hs, hs'⟩, b), rfl, rfl, rfl, rfl⟩)

end GlobalTheory.LamTie.TrueList
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlaceSplitIdempotentOrInert
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.PlaceDichotomy

theorem split_or_inert_idem : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : Formalism.L2.Theta.AE D),
    IsFinIdem D v f → (∃ e, Formalism.L2.Theta.IsSplitIdem D e ∧ e + Formalism.L2.Theta.cA D e = f) ∨
      (∃ w : HeightOneSpectrum (𝓞 D.host.E), Formalism.UG.IsInertAt D.host.F D.host.E v w) := by
  intro D v f hf
  obtain ⟨ε, ⟨α, hεα, hα1, hα0⟩, rfl⟩ := hf
  haveI := v.isMaximal
  obtain ⟨⟨P, hPp, hPo⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 D.host.E)
  let w : HeightOneSpectrum (𝓞 D.host.E) := ⟨P, hPp, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩
  have hw : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hPo.over.symm
  rcases GlobalTheory.LPositivity.split_or_inert D w with hs | hi
  · left
    rw [hw] at hs
    obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hs hw
    refine ⟨GlobalTheory.EmbChart.idem τ, GlobalTheory.EmbChart.isSplitIdem_idem τ, ?_⟩
    have hα : α = GlobalTheory.AdelicU.singleFin v 1 := by
      refine FiniteAdeleRing.ext _ fun u => ?_
      change evalV D.host.F u α = evalV D.host.F u (GlobalTheory.AdelicU.singleFin v 1)
      by_cases e : u = v
      · subst e; rw [hα1, GlobalTheory.AdelicU.evalV_singleFin_self]
      · rw [hα0 u e, GlobalTheory.AdelicU.evalV_singleFin_ne e]
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel, hεα, hα]
    rfl
  · right
    exact ⟨w, hw ▸ hi⟩

end GlobalTheory.PlaceDichotomy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameBaseEqCoverFrameMovedByArithmetic
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CoverFrameArith

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem arch_rat {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (ρ : GA D V) (hρ : ρ ∈ GQ V) :
    ∃ R : GL (Fin r) D.host.E, ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ),
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ → ∀ u : GA D V,
        Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (ρ * u)) =
          (R : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  obtain ⟨R, -, -, hRa⟩ := GlobalTheory.MarkCoset.rational_matrix V ρ hρ
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  refine ⟨R, fun τ θ hθ u => ?_⟩
  rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hRa τ θ hθ]

theorem mulVec_add_nsmul {A : Type} [CommRing A] {n : ℕ} (m : Matrix (Fin n) (Fin n) A) (N : ℕ) (y y' : Fin n → A) :
    m *ᵥ (y + N • y') = m *ᵥ y + N • (m *ᵥ y') := by
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]


set_option maxHeartbeats 1000000 in
theorem conj_move {D : D7} (V : HSp D) {r : ℕ} (hr : V.rank = r) (δa g₀ κ : GA D V) (hδ : δa ∈ GQ V) (N : ℕ)
    (hN : N ≠ 0) (hκ : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ).1.mulVec z - z = N • y)
    (hκ' : ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V κ⁻¹).1.mulVec z - z = N • y)
    (he : finHom V (g₀⁻¹ * δa * g₀) = finHom V κ) (L : Submodule (𝓞 D.host.E) (Fin r → D.host.E))
    (hL : (L : Set (Fin r → D.host.E)) =
      (fun v : Fin V.rank → D.host.E => v ∘ Fin.cast hr.symm) '' (latG V g₀ : Set _))
    (G : Matrix (Fin r) (Fin r) D.host.E) (hG : G = -(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) :
    ∃ Δ : GL (Fin r) D.host.E,
      (∀ v w, herm G ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v) ((Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ w) =
        herm G v w) ∧
      (∀ v, v ∈ L ↔ (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v ∈ L) ∧
      (∀ v ∈ L, ∃ u ∈ L, (Δ : Matrix (Fin r) (Fin r) D.host.E) *ᵥ v = v + N • u) ∧
      ∀ (τ : D.host.E →+* ℂ) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ), Formalism.MainNotions.StandardLattice.IsInfEmb τ θ →
        ∀ u : GA D V, Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ (δa * u)) =
          (Δ : Matrix (Fin r) (Fin r) D.host.E).map τ * Matrix.reindex (finCongr hr) (finCongr hr) (archM V θ u) := by
  subst hr
  have hgr : Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) V.gram = V.gram := by
    ext i j
    rfl
  have hre : ∀ m : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      Matrix.reindex (finCongr (rfl : V.rank = V.rank)) (finCongr rfl) m = m := fun m => by
    ext i j
    rfl
  rw [hgr] at hG
  obtain ⟨Δ, hΔu, hΔf, hΔa⟩ := GlobalTheory.MarkCoset.rational_matrix V δa hδ
  have hmem : ∀ v, v ∈ L ↔ finVec V v ∈ latGHat V g₀ := fun v => by
    rw [← (GlobalTheory.MarkCoset.latG_spec D V _).1, ← SetLike.mem_coe, hL]
    exact Set.ext_iff.1 (Set.image_id _) v
  have hfh : finHom V (δa * g₀ * κ⁻¹) = finHom V g₀ := by
    have e : δa * g₀ * κ⁻¹ = g₀ * (g₀⁻¹ * δa * g₀) * κ⁻¹ := by group
    rw [e, map_mul, map_mul, he, map_inv, mul_inv_cancel_right]
  have hLh : latGHat V (δa * g₀ * κ⁻¹) = latGHat V g₀ := by
    unfold latGHat gLat
    rw [hfh]
  obtain ⟨ht1, -⟩ := GlobalTheory.MarkCoset.transport (finHom V) (latGHat V) (fun g => (GlobalTheory.MarkCoset.latG_spec D V g).2) N
    δa g₀ κ⁻¹ (GlobalTheory.MarkCoset.level_latGHat V N κ⁻¹ hκ')
    (by rw [inv_inv]; exact GlobalTheory.MarkCoset.level_latGHat V N κ hκ)
  rw [hLh] at ht1
  refine ⟨Δ, fun v w => by rw [hG]; exact hΔu v w, fun v => by rw [hmem, hmem, ← hΔf]; exact ht1 _,
    fun v hv => ?_, fun τ θ hθ u => ?_⟩
  · obtain ⟨y, hy, hyz⟩ := ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).1 ((hmem v).1 hv)
    obtain ⟨y', hy', ey⟩ := GlobalTheory.MarkCoset.level_latGHat V N κ hκ y hy
    have hc : (finHom V δa).1 *ᵥ ((finHom V g₀).1 *ᵥ y) = (finHom V g₀).1 *ᵥ ((finHom V κ).1 *ᵥ y) := by
      rw [← he, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
        show g₀ * (g₀⁻¹ * δa * g₀) = δa * g₀ by group]
    have hs : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) - finVec V v := by
      funext i
      simp only [finVec, Pi.sub_apply, TensorProduct.tmul_sub]
    have key : finVec V ((Δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v - v) =
        N • ((finHom V g₀).1 *ᵥ y') := by
      rw [hs, ← hΔf, ← hyz, hc, ey, mulVec_add_nsmul, add_sub_cancel_left]
    obtain ⟨w, hw, e⟩ := GlobalTheory.MarkCoset.finVec_div V N hN _ _ key
    refine ⟨w, (hmem w).2 ?_, sub_eq_iff_eq_add'.1 e⟩
    rw [hw]
    exact ((GlobalTheory.MarkCoset.latG_spec D V g₀).2 _).2 ⟨y', hy', rfl⟩
  · rw [hre, hre, archM, archM, map_mul, Units.val_mul, Matrix.map_mul, ← archM, hΔa τ θ hθ]


set_option maxHeartbeats 4000000 in
theorem frame_move_arith : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ (h h₀ : GA D (T.V j σ)), (C.dict₂ h).1 = (C.dict₂ h₀).1 → ∀ γ₀ : GL (Fin D.R.r) D.host.E, (((T.U j σ).X (T.dict j σ h₀).1).Λ : Set (Fin D.R.r → D.host.E)) = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec '' ((C.U₂.X (C.dict₂ h₀).1).Λ : Set _) → (∀ v w, herm ((T.U j σ).X (T.dict j σ h₀).1).Gm ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec v) ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).mulVec w) = herm (C.U₂.X (C.dict₂ h₀).1).Gm v w) → (∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h₀).1).Ψ), mat (T.dict j σ h₀).2 ⟨τ, h₁⟩ = (γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h₀).2 ⟨τ, h₂⟩) → ∃ δ ∈ ((T.U j σ).X (T.dict j σ h).1).Γ, ∀ (τ : D.host.E →+* ℂ) (h₂ : τ ∈ (C.U₂.X (C.dict₂ h).1).Ψ) (h₁ : τ ∈ ((T.U j σ).X (T.dict j σ h).1).Ψ), mat (T.dict j σ h).2 ⟨τ, h₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * ((γ₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ h).2 ⟨τ, h₂⟩) := by
  intro D T hT j hj σ hσ C hC h h₀ hh γ₀ _ _ hfr0
  have hk : (T.dict j σ h).1 = (T.dict j σ h₀).1 :=
    GlobalTheory.CoverRead.CompIndep.comp_eq_of_cover D T hT j hj σ hσ C hC h h₀ hh
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, hι, -, hth₁, -, hd₁⟩ := hT.adPin j hj σ hσ
  obtain ⟨⟨-, hMl, -, hIl, -⟩, -, -, hU₂, hdom, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, -, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hT.modelW j hj σ hσ
  have hU₁ := hT.unf j hj σ hσ
  have hK := hT.levelK j hj σ hσ
  rw [← hT.pins.2.1.1] at hK
  obtain ⟨γ₁, hγ₁, hL₁, hm₁, hf₁⟩ := hd₁ h
  obtain ⟨γ₁', hγ₁', hL₁', hm₁', hf₁'⟩ := hd₁ h₀
  obtain ⟨γ₂, hγ₂, hL₂, hm₂, hf₂⟩ := hd₂ h
  obtain ⟨γ₂', hγ₂', hL₂', hm₂', hf₂'⟩ := hd₂ h₀

  obtain ⟨M₀, hM₀⟩ := arch_rat (T.V j σ) hr₁ (γ₁' * γ₂'⁻¹) (mul_mem hγ₁' (inv_mem hγ₂'))
  have hΨ : ∀ (g : GA D (T.V j σ)) τ, τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ ↔ τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ :=
    fun g τ => ((hU₁.2.1 _).2 τ).trans ((hU₂.2.1 _).2 τ).symm
  have hM0eq : (M₀ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) = γ₀ := by
    obtain ⟨τ, t₂⟩ : ∃ τ, τ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ := by
      by_cases h0 : D.host.φ₀ ∈ (C.U₂.X (C.dict₂ h₀).1).Ψ
      · exact ⟨_, h0⟩
      · exact ⟨_, not_not.1 (mt ((C.U₂.X (C.dict₂ h₀).1).cmType _).2 h0)⟩
    have t₁ := (hΨ h₀ τ).2 t₂
    have a₁ := hf₁' ⟨τ, t₁⟩
    have a₂ := hf₂' ⟨τ, t₂⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
    have e : γ₁' * h₀ = γ₁' * γ₂'⁻¹ * (γ₂' * h₀) := by group
    rw [e, hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, ← a₂] at a₁
    have a₃ := (hfr0 τ t₂ t₁).symm.trans a₁
    have hu : IsUnit (mat (C.dict₂ h₀).2 ⟨τ, t₂⟩) :=
      (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit (hdom h₀ ⟨τ, t₂⟩).1)
    exact (Matrix.map_injective τ.injective (hu.mul_right_cancel a₃)).symm

  rw [← hk] at hL₁' hm₁'
  rw [← hh] at hL₂' hm₂'
  have hinj : ∀ hr : (T.V j σ).rank = D.R.r,
      Function.Injective (fun v : Fin (T.V j σ).rank → D.host.E => v ∘ Fin.cast hr.symm) := fun hr u v huv =>
    funext fun i => congrFun huv (Fin.cast hr i)
  have hLb : latG (T.V j σ) (γ₁' * h₀) = latG (T.V j σ) (γ₁ * h) :=
    SetLike.coe_injective ((hinj hr₁).image_injective (hL₁'.symm.trans hL₁))
  have hLc : latG (T.V j σ) (γ₂ * h) = latG (T.V j σ) (γ₂' * h₀) :=
    SetLike.coe_injective ((hinj hr₂).image_injective (hL₂.symm.trans hL₂'))

  obtain ⟨a₁, ha₁, k₁, hk₁, eak₁⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₁' * h₀)⁻¹ * (γ₁ * h))
  obtain ⟨a₂, ha₂, k₂, hk₂, eak₂⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (T.V j σ)).1 ((γ₂ * h)⁻¹ * (γ₂' * h₀))
  have hk₁K : k₁ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₁).2 ⟨hk₁, ?_⟩
    have hmA := hm₁'
    have hmB := hm₁
    rw [show (T.Q.l.M : ℕ) = T.Q.l.M * 1 from (mul_one _).symm] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ one_ne_zero _ _
      (fun b hb => by rwa [Nat.cast_one, one_mul]) (γ₁' * h₀) (γ₁ * h) k₁
      (by rw [eak₁, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁, one_mul]) hLb _ hmA hmB
  have hp : C.d.pd ≠ 0 := fun h0 => by
    have := C.d.l₂.three_le
    rw [hMl, h0] at this
    omega
  have hk₂K : k₂ ∈ T.Kf j σ := by
    refine (hT.kfHalf j hj σ hσ k₂).2 ⟨hk₂, ?_⟩
    have hmA := hm₂
    have hmB := hm₂'
    rw [hMl] at hmA hmB
    exact GlobalTheory.CoverRead.CompIndep.congr_of_marked (T.V j σ) _ hι _ _ hp _ _
      (GlobalTheory.CoverRead.CompIndep.ratio_mul_mem T.Q.l C.d.l₂ _ _ hMl hIl) (γ₂ * h) (γ₂' * h₀) k₂
      (by rw [eak₂, map_mul, show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul]) hLc _ hmA hmB
  have hκK : k₁ * k₂ ∈ T.Kf j σ := mul_mem hk₁K hk₂K
  have he : finHom (T.V j σ) ((γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀)) =
      finHom (T.V j σ) (k₁ * k₂) := by
    have e : (γ₁' * h₀)⁻¹ * (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * (γ₁' * h₀) =
        ((γ₁' * h₀)⁻¹ * (γ₁ * h)) * ((γ₂ * h)⁻¹ * (γ₂' * h₀)) := by group
    rw [e, map_mul, eak₁, eak₂, map_mul, map_mul, show finHom (T.V j σ) a₁ = 1 from ha₁,
      show finHom (T.V j σ) a₂ = 1 from ha₂, one_mul, one_mul, map_mul]
  have hM0' : T.Q.l.M ≠ 0 := by
    have := T.Q.l.three_le
    omega
  have hδa : γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹ ∈ GQ (T.V j σ) :=
    mul_mem (mul_mem (mul_mem hγ₁ (inv_mem hγ₂)) hγ₂') (inv_mem hγ₁')
  obtain ⟨Δ, hΔi, hΔl, hΔc, hΔa⟩ := conj_move (T.V j σ) hr₁ _ (γ₁' * h₀) (k₁ * k₂) hδa T.Q.l.M hM0'
    ((hK _).1 hκK).2 ((hK _).1 (inv_mem hκK)).2 he _ hL₁' _ (hW₁ (T.dict j σ h).1).1
  refine ⟨Δ, GlobalTheory.PrincCore.mem_group_of_congruent D T.toCore hT.toLawsM j hj σ hσ _ Δ ⟨hΔi, hΔl⟩ hΔc,
    fun τ t₂ t₁ => ?_⟩
  have a₁ := hf₁ ⟨τ, t₁⟩
  have a₂ := hf₂ ⟨τ, t₂⟩
  rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at a₂
  have e : γ₁ * h = (γ₁ * γ₂⁻¹ * γ₂' * γ₁'⁻¹) * ((γ₁' * γ₂'⁻¹) * (γ₂ * h)) := by group
  rw [a₁, e, hΔa τ _ (hth₁ _ ⟨τ, t₁⟩), hM₀ τ _ (hth₁ _ ⟨τ, t₁⟩), Matrix.mul_assoc, Matrix.mul_assoc, ← a₂, hM0eq]

end GlobalTheory.CoverFrameArith
end
end

