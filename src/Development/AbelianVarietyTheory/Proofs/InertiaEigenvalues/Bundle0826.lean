module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0353
public import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PetEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelCharactersTypePlacesEqLocalComponents
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK)
open Formalism.AUTREP (GAf)
open GlobalTheory.FormInner (frameEquiv)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem GlobalTheory.TwInputs.tau_eq_locK : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf → ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ, (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) = sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) → ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (x : (ZMod (D.host.g kv.1))ˣ) (u : 𝓞 D.host.E) (hu : (u : D.host.E) ≠ 0), (((x : ZMod (D.host.g kv.1)).val : 𝓞 D.host.E) - u) ∈ (NX.pG D kv).asIdeal → embLL0 D ((τ (j.1 + 1) kv x : (↥D.LL0)ˣ) : ↥D.LL0) = (((cf.mu0 j).locK (NX.pG D kv) (Units.mk0 (u : D.host.E) hu) : ℂˣ) : ℂ) := by
  intro hGAR D cf Rw low Pq S hL eig θ Bs hV τ hτ j kv x u hu0 hxu0
  obtain ⟨k, v⟩ := kv
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  haveI : Fact (D.host.g k).Prime := ⟨hgp⟩
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨p, hpg, hp⟩ := Nat.exists_infinite_primes (D.host.g k + 1)
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨w, hw⟩⟩ := Formalism.BasicNotions.Examples₂.PlOver.plNe D p
  obtain ⟨i, hi, -⟩ := Bs.cover w
  have hk : D.ntw.l i ≠ D.host.g k := by rw [hi, hw]; omega
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ρ⟩ := GlobalTheory.Triple.Reading.nonempty (X := D.ntw) i true
  obtain ⟨n, hn⟩ := GlobalTheory.TwChiGal.firstTwistCharacter_eq_ladic_heckeCharacter D cf Bs.chiD Bs.chi Bs.eta_eq Bs.ringSpec_normalisedCharacter_eq Bs.del_eq hV art ha i true ρ j
  have hl := GlobalTheory.Triple.Model.notMem_l (X := D.ntw) hk v
  have hgw : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgw
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg2 := hgp.two_le
  have hAw : IsPlaceOver (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) := D.nd.plOm.2 _
  have hu : u ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 : (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := by
      have := (D.naut.plGw k v).asIdeal.add_mem hxu0 h
      rwa [sub_add_cancel] at this
    obtain ⟨a, c, hac⟩ : IsCoprime (((x : ZMod (D.host.g k)).val : ℕ) : 𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.E) :=
      (ZMod.val_coe_unit_coprime x).cast
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hac]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ hgw)
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap D.host.E D.nd.Om (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E))
    (show 0 < normV (D.naut.plGw k v) - 1 by omega)
  have hxu : IsUnitAt (D.naut.plGw k v) (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) := by
    show Valued.v (((u : D.host.E) : (D.naut.plGw k v).adicCompletion D.host.E)) = 1
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hu
  obtain ⟨σ, hσI, hσart, hσval⟩ := GlobalTheory.TameRecip.exists_ine_of_unit hGAR D.host.E D.nd.Om art ha
    (D.naut.plGw k v) _ hAw _ hgw hspl.2.1 π hπ (atFin (D.naut.plGw k v) (Units.mk0 (u : D.host.E) hu0)) u hxu
    (by simp [atFin])
  have hTR : NX.TameRep (D.naut.plGw k v) 1 σ u :=
    ⟨_, hAw, hσI, _, π, hgw, hspl.2.1, hπ, by simpa using hσval⟩
  have e1 := hn.loc (Or.inl hl) hσart.symm
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.GalChar.inertialOrderFifteenChar_auxiliaryPrime_spec (GlobalTheory.Triple.hframe cf) (l := D.ntw.l i)
  have hdel : (cf.delAt (D.ntw.l i)).UnrAt (D.naut.plGw k v) :=
    h5.unr _ (GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) h1 (h3 k).symm (D.naut.plGw_over k v))
  have hloc (a b : HChar D.host.E) (v : HeightOneSpectrum (𝓞 D.host.E))
      (x : (v.adicCompletion D.host.E)ˣ) : (a * b).loc v x = a.loc v x * b.loc v x := rfl
  rw [GlobalTheory.Triple.blockChar, GlobalTheory.GalChar.block_loc (cf.isEta.unr _) hxu, GlobalTheory.Triple.muBase, hloc,
    hdel _ hxu, mul_one] at e1
  have hm : ((normV (D.naut.plGw k v) - 1 : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    rw [hN]
    intro h
    apply (D.naut.plGw k v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have := (D.naut.plGw k v).asIdeal.sub_mem hgw h
    rwa [Nat.cast_sub (by omega), Nat.cast_one, sub_sub_cancel] at this
  have hex : ∃ s : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, NX.TameRep (D.naut.plGw k v) 1 s u := ⟨σ, hTR⟩
  have e2 : NX.tameVal (D.ntw.chi1 i (j.1 + 1) true) (D.naut.plGw k v) 1 u = D.ntw.chi1 i (j.1 + 1) true σ := by
    unfold NX.tameVal
    rw [dite_eq_left hex]
    refine GlobalTheory.T.tameChar_eq_of_tameRep_congr (D.naut.plGw k v) (D.ntw.twistBaseCoefficientRing_isAdic i) _ (D.ntw.twistCharacterFamily_continuous i (j.1 + 1) true) (by omega) hm
      (fun A hA s hs => ?_) _ _ u u hex.choose_spec hTR (by rw [sub_self]; exact zero_mem _)
    rw [hN]
    exact D.ntw.twistCharacterFamily_tame i (j.1 + 1) true k _ hgw hl A hA s hs
  have e3 := Bs.exp.tau_galois_first_character i (j.1 + 1) true ⟨k, v⟩ x u (by omega) (by omega) hl hxu0
  rw [hτ i (j.1 + 1) true ⟨k, v⟩ x (by omega) (by omega), Bs.exp.sgnG_one, Bs.exp.sgnT_one, one_mul] at e3
  have e4 : GlobalTheory.Triple.embSide D.ntw i true ((τ (j.1 + 1) ⟨k, v⟩ x : (↥D.LL0)ˣ) : ↥D.LL0) =
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.chi1 i (j.1 + 1) true σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
    apply (IsFractionRing.map (A := D.ntw.O0 i) (B := D.ntw.O i) (K := FractionRing (D.ntw.O0 i))
      (L := FractionRing (D.ntw.O i)) (D.ntw.O_inj i)).injective
    rw [← e2]
    refine e3.trans ?_
    simp only [IsFractionRing.map, IsLocalization.map_eq]
    rfl
  rw [← ρ.read, e4]
  exact e1

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixCoeffFinitePlaceOffLevelConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift.GoodFactor

theorem mt_mul' {D : D7} (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one' {D : D7} (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_inj {D : D7} (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem comm_of_supp_triv {D : D7} {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_inj
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul', mt_mul', e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem actO_one_of_trivAt {D : D7} {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun w => w = v) : actO S T 1 γ u = u := by
  obtain ⟨ε, hε, rfl⟩ := hf
  have hu' := GlobalTheory.VecInvInert.idem_smul_eq hε hu
  have hz : algebraMap (AF D.host.F) (AE D) ε • (mt T γ - 1) = 0 := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    exact hγ a b
  have h0 : HMul.hMul (mt T γ - 1) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, hz, Matrix.zero_mul]
  unfold actO
  rw [inv_one, mt_one', Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h0
  exact h0

theorem vacFin_om_trivAt {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {f : AE D} (hf : IsFinIdem D v f) {γ : GA D T} (hγ : TrivAt T f γ)
    {x : WO S T → ℂ} (hx : GlobalTheory.FinZeta.VacFin ψ S T v x) : GlobalTheory.FinZeta.VacFin ψ S T v (om (1, γ) x) := by
  obtain ⟨hth, hl1, hl2⟩ := hx
  refine ⟨hW.om_pres _ _ hth, fun u hu => ?_, fun e he u hu hh => ?_⟩
  · rw [← actO_one_of_trivAt hf hγ (nsmul_mem hu 2), ← hW.om_heis 1 γ _ x hth, hl1 u hu]
  · rw [← actO_one_of_trivAt hf hγ hu, ← hW.om_heis 1 γ _ x hth, hl2 e he u hu hh]

theorem thetaInner_eq_star_l2 {D : D7} {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (x y : WO S T' → ℂ) :
    thetaIP μ 𝓕 x y = star (GlobalTheory.AdelicScalar.l2 μ 𝓕 x y) := by
  unfold thetaIP GlobalTheory.AdelicScalar.l2 Formalism.IndefR.Lift.pet
  show _ = (starRingEnd ℂ) _
  rw [← integral_conj]
  congr 1; funext w
  simp [mul_comm]

theorem finmult_good : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ v f, IsFinIdem D v f → (∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f', IsPrimeIdem P e f' → f' ≠ f) → ∀ k, SuppF (Wc D i) f k → ∃ c : ℂ, ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = c * thetaIP μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)) (R.vP i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL _ i t μ 𝓕 hμ v f hf hoff k hk
  obtain ⟨a, rfl⟩ := _root_.GlobalTheory.RawLift.suppF_finIdem_mem_range D (Wc D i) v f hf k hk
  have hW := hL.thP.ωP i t
  have hvac := _root_.GlobalTheory.RawLift.vacFin_off D G Pl0 T A Ks R F hL i t v f hf hoff
  have hunr := _root_.GlobalTheory.GoodModUnr.chrTh_unrAt D G Pl0 T A Ks R F hL i t v f hf hoff
  obtain ⟨φ, -, hc⟩ := GlobalTheory.VacCoef.vac_coef D R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW μ 𝓕 hμ v hunr
  refine ⟨star (φ a), fun γ _ hγ => ?_⟩
  have hcomm := comm_of_supp_triv hk hγ
  have hv' := vacFin_om_trivAt hW hf hγ hvac
  have e : R.ωP i t (1, γ * GlobalTheory.FinZeta.embV (Wc D i) v a) (R.vP i t) =
      R.ωP i t (1, GlobalTheory.FinZeta.embV (Wc D i) v a) (R.ωP i t (1, γ) (R.vP i t)) := by
    rw [← hcomm]
    show _ = (R.ωP i t (1, _) * R.ωP i t (1, γ)) (R.vP i t)
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  rw [e, thetaInner_eq_star_l2, thetaInner_eq_star_l2 μ 𝓕 (R.ωP i t (1, γ) (R.vP i t)), hc a _ _ hv' hvac, star_mul']

end GlobalTheory.RawLift.GoodFactor

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurableCompInfGLProd
section
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host GlobalTheory.Published GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.Petersson
open scoped nonZeroDivisors ComplexConjugate

noncomputable section

namespace GlobalTheory.MspanROrth

open GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} {ω : HChar E}

theorem measurable_chart_prod {F : GA E a → ℂ} (hF : Continuous F) :
    Measurable fun p : GA E a × Lie E a => chart F p.1 p.2 := by
  classical
  have h1 := GlobalTheory.ConstTermSmooth.continuousOn_chart (E := E) (a := a) hF
  have e : (fun p : GA E a × Lie E a => chart F p.1 p.2) =
      (Set.univ ×ˢ invSet E a).piecewise (fun p : GA E a × Lie E a => chart F p.1 p.2) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ (Set.univ ×ˢ invSet E a : Set (GA E a × Lie E a))
    · rw [Set.piecewise_eq_of_mem _ _ _ hp]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hp]
      exact dif_neg fun h => hp ⟨Set.mem_univ _, h⟩
  rw [e]
  exact h1.measurable_piecewise continuousOn_const (isOpen_univ.prod isOpen_invSet).measurableSet

theorem measurable_comp_infGL_prod {F : GA E a → ℂ} (hF : Continuous F) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun p : GA E a × X => F (p.1 * infGL E a (γ p.2)) := by
  have h : Measurable fun x => toL (γ x).val := hγ
  have e : (fun p : GA E a × X => F (p.1 * infGL E a (γ p.2))) =
      (fun q : GA E a × Lie E a => chart F q.1 q.2) ∘ fun p : GA E a × X => (p.1, toL (γ p.2).val) :=
    funext fun p => (chart_val F p.1 (γ p.2)).symm
  rw [e]
  exact (measurable_chart_prod hF).comp (measurable_fst.prodMk (h.comp measurable_snd))

theorem measurable_comp_infGL' {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) {X : Type} [MeasurableSpace X]
    {γ : X → GL (Fin a) (Cinf E)} (hγ : Measurable fun x => (γ x : Matrix (Fin a) (Fin a) (Cinf E))) :
    Measurable fun x => F (g * infGL E a (γ x)) :=
  by
  have h := (measurable_comp_infGL_prod hF hγ).comp (measurable_prodMk_left (x := g) (β := X))
  exact h

theorem integrable_of_isRapidInf {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) : Integrable k ν := by
  have h := hk.2.2 0
  simp only [pow_zero, mul_one] at h
  exact (integrable_norm_iff hk.1.aestronglyMeasurable).1 h

theorem kerInf_mem_bddForms {X : Type} [MeasurableSpace X] {ν : Measure X} {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F : GA E a → ℂ} (h : F ∈ bddForms E a ω) :
    (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ∈ bddForms E a ω := by
  set_option synthInstance.maxHeartbeats 200000 in
  obtain ⟨C, hC⟩ := h.2.2.2
  have hki := integrable_of_isRapidInf hk
  refine ⟨?_, fun γ' g => ?_, fun z g => ?_, ∫ x, ‖k x‖ * C ∂ν, fun g => ?_⟩
  · refine continuous_of_dominated (bound := fun x => ‖k x‖ * C)
      (fun g => (hk.1.mul (measurable_comp_infGL' h.1 g hk.2.1)).aestronglyMeasurable)
      (fun g => .of_forall fun x => ?_) (hki.norm.mul_const C)
      (.of_forall fun x => continuous_const.mul (h.1.comp (continuous_id.mul continuous_const)))
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
  · simp only [mul_assoc, h.2.1]
  · rw [← integral_const_mul]
    beta_reduce
    congr 1; funext x; rw [mul_assoc, h.2.2.1]; ring
  · exact norm_integral_le_of_norm_le (hki.norm.mul_const C)
      (.of_forall fun x => (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)))

section Lemmas

variable (μ : Measure (GA E a)) [μ.IsHaarMeasure]

theorem pet_kerInf_left (hω : ω.IsUnitary) {X : Type} [MeasurableSpace X] {ν : Measure X} [SFinite ν] {k : X → ℂ}
    {γ : X → GL (Fin a) (Cinf E)} (hk : IsRapidInf ν k γ) {F ψ : GA E a → ℂ}
    (h : F ∈ bddForms E a ω) (h' : ψ ∈ bddForms E a ω) :
    pet (latticeGL E a) μ (fun g => ∫ x, k x * F (g * infGL E a (γ x)) ∂ν) ψ =
      ∫ x, k x * pet (latticeGL E a) μ (fun g => F (g * infGL E a (γ x))) ψ ∂ν := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hD := isFundamentalDomain_stdDom (latticeGL E a) μ
  haveI : IsFiniteMeasure (μ.restrict (stdDom (latticeGL E a))) :=
    ⟨by rw [Measure.restrict_apply_univ, ← quotMeasure_univ hD]; exact measure_lt_top _ _⟩
  obtain ⟨C, hC⟩ := h.2.2.2
  obtain ⟨D, hD'⟩ := h'.2.2.2
  have hki := integrable_of_isRapidInf hk
  have hm : Measurable fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1) :=
    ((hk.1.comp measurable_snd).mul (measurable_comp_infGL_prod h.1 hk.2.1)).mul
      ((Complex.continuous_conj.comp h'.1).measurable.comp measurable_fst)
  have hi : Integrable (fun p : GA E a × X => k p.2 * F (p.1 * infGL E a (γ p.2)) * conj (ψ p.1))
      ((μ.restrict (stdDom (latticeGL E a))).prod ν) := by
    refine ((integrable_const (C * D)).mul_prod hki.norm).mono' hm.aestronglyMeasurable
      (.of_forall fun p => ?_)
    rw [norm_mul, norm_mul, mul_assoc, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hD' _) (norm_nonneg _)
      ((norm_nonneg _).trans (hC 1))) (norm_nonneg _)
  rw [(pet_eq_setIntegral hω (kerInf_mem_bddForms hk h) h' hD).2]
  simp only [← integral_mul_const]
  rw [integral_integral_swap hi]
  refine integral_congr_ae (.of_forall fun x => ?_)
  simp only [(pet_eq_setIntegral hω (mul_right_mem_bddForms h _) h' hD).2, ← integral_const_mul, mul_assoc]

theorem mul_right_mem_mspanR {π : CuspSub E a} {F : GA E a → ℂ} (hF : F ∈ mspanR π) (h : GA E a) :
    (fun g => F (g * h)) ∈ mspanR π :=
  Submodule.mem_sInf.2 fun S hS => hS.2.1 F (Submodule.mem_sInf.1 hF S hS) h

theorem mspanR_pet_eq_zero (hω : ω.IsUnitary) {π : CuspSub E a} (hπ : π.HasCentChar ω) (T : Set (GA E a → ℂ))
    (hT : ∀ G ∈ T, G ∈ bddForms E a ω) (hTr : ∀ G ∈ T, ∀ h : GA E a, (fun g => G (g * h)) ∈ T)
    (h0 : ∀ φ ∈ π.V, ∀ G ∈ T, pet (latticeGL E a) μ φ.1 G = 0) {F : GA E a → ℂ} (hF : F ∈ mspanR π) :
    F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0 := by
  let S : Submodule ℂ (GA E a → ℂ) :=
    { carrier := {F | F ∈ bddForms E a ω ∧ ∀ G ∈ T, pet (latticeGL E a) μ F G = 0}
      add_mem' := fun {F F'} hF hF' => ⟨add_mem hF.1 hF'.1, fun G hG => by
        rw [pet_add_left μ hω hF.1 hF'.1 (hT G hG), hF.2 G hG, hF'.2 G hG, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun G _ => by simp [pet, descend]⟩
      smul_mem' := fun c F hF => ⟨Submodule.smul_mem _ c hF.1, fun G hG => by
        rw [pet_smul_left, hF.2 G hG, mul_zero]⟩ }
  have htr : ∀ F ∈ S, ∀ h : GA E a, (fun g => F (g * h)) ∈ S := fun F hF h =>
    ⟨mul_right_mem_bddForms hF.1 h, fun G hG => by
      rw [pet_mul_right_left μ hω hF.1 (hT G hG) h]; exact hF.2 _ (hTr G hG h⁻¹)⟩
  refine Submodule.mem_sInf.1 hF S ⟨fun φ hφ => ⟨mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω hπ hφ,
    fun G hG => h0 φ hφ G hG⟩, htr, fun F hF X _ ν _ k γ hk => ⟨kerInf_mem_bddForms hk hF.1, fun G hG => ?_⟩⟩
  rw [pet_kerInf_left μ hω hk hF.1 (hT G hG)]
  exact integral_eq_zero_of_ae (.of_forall fun x => mul_eq_zero_of_right _ ((htr F hF _).2 G hG))

end Lemmas

theorem setIntegral_mspanR_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (π π'' : CuspSub E a) (ω : HChar E), ω.IsUnitary → π.HasCentChar ω → π''.HasCentChar ω →
    ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    (∀ φ ∈ π.V, ∀ φ'' ∈ π''.V, GlobalTheory.AutomorphicL2Unitary.pet (latticeGL E a) μ φ.1 φ''.1 = 0) →
    ∀ 𝓕' : Set (GA E a), IsFundamentalDomain (latticeGL E a) 𝓕' μ →
    ∀ F ∈ GlobalTheory.JSW.mspanR π, ∀ F'' ∈ GlobalTheory.JSW.mspanR π'', ∫ g in 𝓕', F g * starRingEnd ℂ (F'' g) ∂μ = 0 := by
  intro E _ _ _ a _ π π'' ω hω hπ hπ'' μ _ h0 𝓕' h𝓕 F hF F'' hF''
  have hB := GlobalTheory.CuspOrth.cuspFormsBounded
  have base : ∀ φ ∈ π.V, ∀ ψ ∈ π''.V, ∀ h : GA E a, pet (latticeGL E a) μ φ.1 (fun g => ψ.1 (g * h)) = 0 := by
    intro φ hφ ψ hψ h
    have e := pet_mul_right_left μ hω (mem_bddForms_of_cuspSub hB hω hπ hφ) (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h⁻¹
    rw [inv_inv] at e
    rw [← e]
    obtain ⟨y, k, e'⟩ : ∃ y k, h⁻¹ = infGL E a y * finGL E a k := ⟨_, _, (infGL_mul_finGL h⁻¹).symm⟩
    rw [e']
    have H := (GlobalTheory.KeepOrth.pet_eq_zero_of_orthogonal hB E a π π'' ω hω hπ hπ'' μ h0).1 (act (.fin k) φ)
      (π.stable (.fin k) φ hφ) ψ hψ y
    refine Eq.trans (congrArg (fun F => pet (latticeGL E a) μ F ψ.1) (funext fun g => ?_)) H
    show φ.1 (g * (infGL E a y * finGL E a k)) = (act (.fin k) φ).1 (g * infGL E a y)
    rw [← mul_assoc]; rfl
  have A1 := fun {F} (hF : F ∈ mspanR π) => mspanR_pet_eq_zero μ hω hπ
    {G | ∃ ψ ∈ π''.V, ∃ h : GA E a, G = fun g => ψ.1 (g * h)}
    (by rintro _ ⟨ψ, hψ, h, rfl⟩; exact mul_right_mem_bddForms (mem_bddForms_of_cuspSub hB hω hπ'' hψ) h)
    (by rintro _ ⟨ψ, hψ, h, rfl⟩ k; exact ⟨ψ, hψ, k * h, funext fun g => by simp only [mul_assoc]⟩)
    (by rintro φ hφ _ ⟨ψ, hψ, h, rfl⟩; exact base φ hφ ψ hψ h) hF
  have A2 := fun {G} (hG : G ∈ mspanR π'') => mspanR_pet_eq_zero μ hω hπ'' (mspanR π : Set (GA E a → ℂ))
    (fun F hF => (A1 hF).1) (fun F hF h => mul_right_mem_mspanR hF h)
    (fun ψ hψ F hF => by
      rw [← conj_pet, (A1 hF).2 _ ⟨ψ, hψ, 1, funext fun g => by rw [mul_one]⟩, map_zero]) hG
  obtain ⟨bF'', h2⟩ := A2 hF''
  rw [← (pet_eq_setIntegral hω (A1 hF).1 bF'' h𝓕).2, ← conj_pet, h2 F hF, map_zero]

end GlobalTheory.MspanROrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MellinIntegralRapidDecayEntireOfLeOne
section
open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory

theorem integral_mul_cpow_of_rapid_decay_entire :
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) (δ : X → ℝ) (F : X → ℂ), Measurable δ →
      (∀ᵐ x ∂ν, 0 < δ x ∧ δ x ≤ 1) → Integrable δ ν → AEStronglyMeasurable F ν →
      (∀ K : ℕ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ ≤ C * δ x ^ K) →
      (∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν) ∧
        Differentiable ℂ fun s : ℂ => ∫ x, F x * (δ x : ℂ) ^ s ∂ν := by
  intro X _ ν δ F hδm hδ hδi hF hdec
  have key : ∀ t : ℝ, ∃ C : ℝ, ∀ᵐ x ∂ν, ‖F x‖ * δ x ^ t ≤ C * δ x := by
    intro t
    obtain ⟨K, hK⟩ : ∃ K : ℕ, 1 - t ≤ K := exists_nat_ge (1 - t)
    obtain ⟨C, hC⟩ := hdec K
    refine ⟨C, ?_⟩
    filter_upwards [hC, hδ] with x hx hx'
    obtain ⟨h0, h1⟩ := hx'
    have hpK : 0 < δ x ^ K := pow_pos h0 K
    have hC0 : 0 ≤ C := by
      by_contra hc
      push_neg at hc
      have := mul_neg_of_neg_of_pos hc hpK
      linarith [norm_nonneg (F x)]
    have hpt : 0 ≤ δ x ^ t := Real.rpow_nonneg h0.le t
    calc ‖F x‖ * δ x ^ t ≤ C * δ x ^ K * δ x ^ t := mul_le_mul_of_nonneg_right hx hpt
      _ = C * δ x ^ ((K : ℝ) + t) := by rw [Real.rpow_add h0, Real.rpow_natCast]; ring
      _ ≤ C * δ x ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)) hC0
      _ = C * δ x := by rw [Real.rpow_one]
  have hcm : ∀ s : ℂ, Measurable fun x => (δ x : ℂ) ^ s :=
    fun s => (Complex.measurable_ofReal.comp hδm).pow_const s
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (δ x : ℂ) ^ s) ν :=
    fun s => hF.mul (hcm s).aestronglyMeasurable
  have hint : ∀ s : ℂ, Integrable (fun x => F x * (δ x : ℂ) ^ s) ν := by
    intro s
    obtain ⟨C, hC⟩ := key s.re
    refine Integrable.mono' (hδi.const_mul C) (hmeas s) ?_
    filter_upwards [hC, hδ] with x hx hx'
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx'.1]
    exact hx
  refine ⟨hint, fun s₀ => ?_⟩
  obtain ⟨C, hC⟩ := key (s₀.re - 2)
  have hF'm : AEStronglyMeasurable
      (fun x => F x * ((δ x : ℂ) ^ s₀ * Complex.log (δ x))) ν :=
    hF.mul ((hcm s₀).mul (Complex.measurable_log.comp
      (Complex.measurable_ofReal.comp hδm))).aestronglyMeasurable
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := s₀)
    (F := fun s x => F x * (δ x : ℂ) ^ s)
    (F' := fun s x => F x * ((δ x : ℂ) ^ s * Complex.log (δ x)))
    (bound := fun x => C * δ x) (Metric.ball_mem_nhds s₀ zero_lt_one)
    (Filter.Eventually.of_forall hmeas) (hint s₀) hF'm ?_ (hδi.const_mul C) ?_
  · exact hd.2.differentiableAt
  · filter_upwards [hC, hδ] with x hx hx'
    obtain ⟨h0, h1⟩ := hx'
    intro s hs
    rw [Metric.mem_ball, Complex.dist_eq] at hs
    have hre : s₀.re - 1 ≤ s.re := by
      have h := Complex.abs_re_le_norm (s - s₀)
      rw [Complex.sub_re] at h
      linarith [neg_abs_le (s.re - s₀.re)]
    have hlog : ‖Complex.log (δ x)‖ = |Real.log (δ x)| := by
      rw [← Complex.ofReal_log h0.le, Complex.norm_real, Real.norm_eq_abs]
    have hl := Real.abs_log_mul_self_lt (δ x) h0 h1
    rw [abs_mul, abs_of_pos h0] at hl
    have e1 : δ x ^ s.re ≤ δ x ^ (s₀.re - 1) := Real.rpow_le_rpow_of_exponent_ge h0 h1 hre
    have e2 : δ x ^ (s₀.re - 1) = δ x ^ (s₀.re - 2) * δ x := by
      rw [← Real.rpow_add_one h0.ne']; ring_nf
    have hp2 : 0 ≤ δ x ^ (s₀.re - 2) := Real.rpow_nonneg h0.le _
    have e3 : δ x ^ s.re * |Real.log (δ x)| ≤ δ x ^ (s₀.re - 2) := by
      calc δ x ^ s.re * |Real.log (δ x)| ≤ δ x ^ (s₀.re - 1) * |Real.log (δ x)| :=
            mul_le_mul_of_nonneg_right e1 (abs_nonneg _)
        _ = δ x ^ (s₀.re - 2) * (|Real.log (δ x)| * δ x) := by rw [e2]; ring
        _ ≤ δ x ^ (s₀.re - 2) * 1 := mul_le_mul_of_nonneg_left hl.le hp2
        _ = δ x ^ (s₀.re - 2) := mul_one _
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos h0, hlog]
    calc ‖F x‖ * (δ x ^ s.re * |Real.log (δ x)|) ≤ ‖F x‖ * δ x ^ (s₀.re - 2) :=
          mul_le_mul_of_nonneg_left e3 (norm_nonneg _)
      _ ≤ C * δ x := hx
  · filter_upwards [hδ] with x hx' s _
    exact ((Complex.hasStrictDerivAt_const_cpow (x := (δ x : ℂ)) (y := s)
      (Or.inl (Complex.ofReal_ne_zero.mpr hx'.1.ne'))).hasDerivAt).const_mul (F x)

end GlobalTheory
end

