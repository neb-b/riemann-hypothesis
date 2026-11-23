module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Formalism.SharpRestriction.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0540
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0241
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableRowsCDAdmissible
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section

namespace GlobalTheory.NLink.RowCDSize

open Classical

theorem ratIn_le {x y c : ℝ} (hy : y ≤ c) (hc : 0 ≤ c) : ((Formalism.MainNotions.N.ratIn x y : ℚ) : ℝ) ≤ c := by
  by_cases h : x < y
  · exact (RowBSize.ratIn_lt h).le.trans hy
  · rw [RowBSize.ratIn_of_not_lt h]; simpa using hc

theorem one_le_hB {D : D7} (L : SizeData₂ D) : 1 ≤ TwistedPlaces.hB L := by
  unfold TwistedPlaces.hB
  have := RowBSize.one_le_b' L
  have := L.Sc_pos
  have := L.etaSz_pos
  have : (0 : ℝ) ≤ D.R.t := by positivity
  linarith

theorem etaP_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.eta₃ L := by
  unfold TwistedPlaces.eta₃
  have := L.etaSz_pos
  positivity

theorem placeWeight_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ TwistedPlaces.wP L := by
  have hb : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    have := RowBSize.x_pos' L
    have := RowBSize.one_le_b' L
    positivity
  have h1 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w''
    have := RowBSize.x_pos' L
    positivity
  unfold TwistedPlaces.wP TwistedPlaces.wB
  have h2 := L.etaSz_pos
  have h4 : L.sc.w'' D.R.n + L.etaSz ≤ max (L.sc.w'' D.R.n + L.etaSz)
      ((⨆ t : D.host.TT, (L.bT t : ℝ)) + L.sc.b' / L.sc.x + L.etaSz) := le_max_left _ _
  have h5 : (0:ℝ) ≤ D.R.t := by positivity
  linarith

theorem coreE_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) : 0 ≤ coreE L l := by
  unfold coreE
  have h1 : 0 ≤ TwistedPlaces.hB L / l := div_nonneg (by linarith [one_le_hB L]) (by positivity)
  have h2 : 0 ≤ Real.logb l (TwistedPlaces.hB L) := by
    unfold Real.logb
    exact div_nonneg (Real.log_nonneg (one_le_hB L)) (Real.log_natCast_nonneg l)
  linarith

theorem flat_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) : 0 ≤ flat L bd l := by
  unfold flat
  have := placeWeight_nonneg L
  have := etaP_nonneg L
  have := L.Sc_pos
  have := RowBSize.one_le_Lg L
  have h1 : 0 ≤ (TwistedPlaces.wP L + TwistedPlaces.eta₃ L) / l := by positivity
  have h2 : 0 ≤ TwistedPlaces.eta₃ L * (if bd then (1:ℝ) else 0) := by split_ifs <;> simp [*]
  linarith

theorem coreH_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreH L l lam := by
  unfold coreH
  have := RowBSize.hB_nonneg L
  positivity

theorem coreF_nonneg {D : D7} (L : SizeData₂ D) (bd : Prop) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreF L bd l lam := by
  unfold coreF
  have := flat_nonneg L bd l
  positivity

theorem coreM_nonneg {D : D7} (L : SizeData₂ D) (l : ℕ) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    0 ≤ coreM L l lam := by
  unfold coreM
  have := coreE_nonneg L l
  positivity

theorem len_le {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ)
    (hD : KillingConditions.DataAD L HW X R) (hR : R.Le C) (i : D.nd.Loc) (hI : TwistedPlaces.InertK D (D.nd.l i))
    (hB : ¬ KillingConditions.IsRowB L (D.nd.l i)) (lam : HeightOneSpectrum (𝓞 D.host.E)) :
    (tabX L X).len i lam ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by
  obtain ⟨-, -, -, -, hC1, -, h1, h2, h3, -⟩ := hR
  have hH := coreH_nonneg L (D.nd.l i) lam
  have hF := coreF_nonneg L (X.band i lam) (D.nd.l i) lam
  have hM := coreM_nonneg L (D.nd.l i) lam
  have hC0 : (0:ℝ) ≤ C := by linarith
  have h0 : 0 ≤ C * coreH L (D.nd.l i) lam + C * coreF L (X.band i lam) (D.nd.l i) lam +
      C * C * coreM L (D.nd.l i) lam := by positivity
  have key : (tabX L X).len i lam = KillingConditions.supZ i
      (fun _ => ((lenRowCD L (X.band i) R.K₁ R.K₂ R.K₃ (D.nd.l i) lam : ℚ) : ℝ)) := by
    show KillingConditions.lenR X.len0 i lam = _
    unfold KillingConditions.lenR
    congr 1
    funext π
    rw [hD.len0I i hI π lam, hD.rowCD i hI hB]
  rw [key]
  unfold KillingConditions.supZ
  split_ifs with hne
  · rw [Finset.sup'_const]
    unfold lenRowCD
    refine ratIn_le ?_ h0
    unfold bdCD
    have h4 : R.K₃ ≤ C * C := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 hH
    have := mul_le_mul_of_nonneg_right h2 hF
    have := mul_le_mul_of_nonneg_right h4 hM
    linarith
  · exact h0

end GlobalTheory.NLink.RowCDSize

theorem GlobalTheory.NLink.localBoundTable_rowsCD_admissible : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK) (C : ℝ), KillingConditions.DataAD L HW X R → R.Le C → TwistedPlaces.MediumInertPrimeLengthBound L (tabX L X) C ∧ TwistedPlaces.SmallInertPrimeSmallOrderLengthBound L (tabX L X) C := by
  intro D L P HW X R C hD hR
  have hfl : ∀ i lam l, TwistedPlaces.flatCD L (tabX L X) i lam l = flat L (X.band i lam) l := fun _ _ _ => rfl
  have he : ∀ l, TwistedPlaces.eP L C l = C * coreE L l := fun _ => rfl
  constructor
  · rintro i - ⟨hI, hA, -, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.1 (not_lt.2 hA)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring
  · rintro i - ⟨hI, -, hO, -⟩ lam -
    have h := GlobalTheory.NLink.RowCDSize.len_le L HW X R C hD hR i hI (fun h => absurd h.2 (not_lt.2 hO)) lam
    rw [hfl, he]
    refine h.trans (le_of_eq ?_)
    unfold coreH coreF coreM
    ring

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalIntegerSpanOfImageIsStableLattice
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Pass.LocDual.OneX

variable {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

def vecLS (a : ℕ) :
    (Fin a → Fin D.R.nV → KK D.nd i) →ₛₗ[(D.nbr i w hw).eO.toRingHom]
      (Fin a → Fin D.R.nV → Br.LL D.nbr i w hw) where
  toFun := vecL i w hw
  map_add' u v := by
    funext b j
    simp [vecL]
  map_smul' c v := by
    funext b j
    simp only [vecL, Pi.smul_apply, Algebra.smul_def, map_mul, Br.toLLK_alg]
    rfl

theorem eO_surj : RingHomSurjective (D.nbr i w hw).eO.toRingHom :=
  ⟨(D.nbr i w hw).eO.surjective⟩

theorem latY_map {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    (latY i w hw Y).map ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) =
      Submodule.span (Br.OLL D.nbr i w hw) (vecL i w hw '' (Y : Set _)) := by
  rw [latY, Submodule.map_span]
  congr 1
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact hu
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩, ⟨y, hy, rfl⟩, rfl⟩

theorem latY_fg {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    (latY i w hw Y).FG := by
  have hinj : Function.Injective ((spanL i w hw Y).subtype.restrictScalars (Br.OLL D.nbr i w hw)) :=
    Subtype.val_injective
  apply Submodule.fg_of_fg_map_injective _ hinj
  rw [latY_map]
  haveI := eO_surj i w hw
  obtain ⟨S, rfl⟩ := hY
  have h : ∀ T : Set (Fin a → Fin D.R.nV → KK D.nd i), vecL i w hw '' T = (vecLS i w hw a) '' T :=
    fun _ => rfl
  rw [h, ← Submodule.map_coe, Submodule.span_eq, Submodule.map_span]
  classical
  exact ⟨(S.image (vecLS i w hw a)), by rw [Finset.coe_image]⟩

theorem span_stable_of_gen {R K M : Type} [CommRing R] [Field K] [Algebra R K] [AddCommGroup M] [Module K M]
    [Module R M] (hT : IsScalarTower R K M) (f : M →ₗ[K] M) (s : Set M) (h : ∀ v ∈ s, f v ∈ s) :
    ∀ v ∈ Submodule.span R s, f v ∈ Submodule.span R s := by
  intro v hv
  haveI := hT
  have key : Submodule.span R s ≤ (Submodule.span R s).comap (f.restrictScalars R) :=
    Submodule.span_le.2 fun u hu => Submodule.subset_span (h u hu)
  exact key hv

theorem latY_stable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y) :
    ∀ g, ∀ u ∈ latY i w hw Y,
      subRho (sumG i w hw r Xs hr x) (spanL i w hw Y) (spanL_stable i w hw r Xs hr x Y hst) g u ∈ latY i w hw Y := by
  intro g
  apply span_stable_of_gen (K := Br.LL D.nbr i w hw)
  · exact ⟨fun c k u => Subtype.ext (smul_assoc c k (u.1 : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw))⟩
  rintro v ⟨y, hy, hv⟩
  refine ⟨actK i r Xs x (gl i w hw g) y, hst _ y hy, ?_⟩
  show _ = (sumG i w hw r Xs hr x).ρ g (v : Fin a → Fin D.R.nV → Br.LL D.nbr i w hw)
  rw [← hv, sumG_vecL]

theorem latY_span {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) :
    Submodule.span (Br.LL D.nbr i w hw) ((latY i w hw Y : Set ↥(spanL i w hw Y))) = ⊤ := by
  apply Submodule.map_injective_of_injective (spanL i w hw Y).injective_subtype
  rw [Submodule.map_span, Submodule.map_subtype_top]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    apply Submodule.subset_span
    exact ⟨⟨vecL i w hw y, Submodule.subset_span ⟨y, hy, rfl⟩⟩,
      Submodule.subset_span ⟨y, hy, rfl⟩, rfl⟩

theorem latY_free {a : ℕ} (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i)) (hY : Y.FG) :
    Module.Free (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
  letI : CommRing (Br.OLL D.nbr i w hw) := inferInstance
  letI : AddCommGroup ↥(latY i w hw Y) := inferInstance
  letI : Module (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := inferInstance
  haveI : Module.Finite (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) :=
    Module.Finite.iff_fg.2 (latY_fg i w hw Y hY)
  haveI : NoZeroSMulDivisors (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := by
    constructor
    intro c u h
    by_cases hc : c = 0
    · exact Or.inl hc
    right
    have h1 : ((c • u : ↥(latY i w hw Y)) : ↥(spanL i w hw Y)) = 0 := by rw [h]; rfl
    have h2 : ((algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c) • (u : ↥(spanL i w hw Y))) = 0 := by
      rw [algebraMap_smul]; exact h1
    have hc' : algebraMap (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) c ≠ 0 := by
      intro h0; apply hc; exact Subtype.val_injective h0
    have := (smul_eq_zero.1 h2).resolve_left hc'
    exact Subtype.ext this
  haveI : IsPrincipalIdealRing (Br.OLL D.nbr i w hw) := inferInstance
  haveI : IsDomain (Br.OLL D.nbr i w hw) := inferInstance
  haveI : IsTorsionFree (Br.OLL D.nbr i w hw) ↥(latY i w hw Y) := inferInstance
  exact @Module.free_of_finite_type_torsion_free' (Br.OLL D.nbr i w hw) inferInstance
    ↥(latY i w hw Y) inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

theorem latY_lattice : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)) (hr : GoodR D.nd i r) {a : ℕ} (x : Fin a → ↥Xs)
    (Y : Submodule (D.nd.O i) (Fin a → Fin D.R.nV → KK D.nd i))
    (hst : ∀ γ : GE D.nd, ∀ y ∈ Y, actK i r Xs x γ y ∈ Y), Y.FG →
    ∃ LY : Lattice (O := Br.OLL D.nbr i w hw) (XG i w hw r Xs hr x Y hst).ρ, LY.T = latY i w hw Y := by
  intro D i w hw r Xs hr a x Y hst hY
  exact ⟨{ T := latY i w hw Y
           stable := latY_stable i w hw r Xs hr x Y hst
           fg := latY_fg i w hw Y hY
           free := latY_free i w hw Y hY
           span := latY_span i w hw Y }, rfl⟩

end GlobalTheory.Pass.LocDual.OneX

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDetectedSubgroupTowerRatProof
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem noTowerQ_holds : NoTowerQ := by
  intro l _ N hanti hopen h1 h2 h3
  by_contra hcon
  push Not at hcon
  obtain ⟨k₀, hk₀⟩ := h3 8
  have hex : ∃ k ≥ k₀, ∃ σ ∈ N k, (∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1) ∧ σ ∉ N (k + 1) := by
    by_contra hno
    push Not at hno
    obtain ⟨j, σ, hσ, hi, hj⟩ := hcon k₀
    have : ∀ i, σ ∈ N (k₀ + i) := by
      intro i
      induction i with
      | zero => exact hσ
      | succ i ih => exact hno (k₀ + i) (by omega) σ ih hi
    exact hj (hanti (by omega : j ≤ k₀ + j) (this j))
  obtain ⟨k, hk, σ₀, hσ₀, hi₀, hn₀⟩ := hex
  have hT : (N k).index ≠ 0 := by
    have : Finite (GQ l ⧸ N k) := Subgroup.quotient_finite_of_isOpen _ (hopen k)
    exact Subgroup.index_ne_zero_of_finite
  set T := (N k).index with hTdef
  choose ι hι x a hxa hdet using fun i : ℕ => hk₀ (k + i) (by omega)
  have hS : (⋃ i ∈ Set.Iic (2 * T), Set.range (x i)).Finite :=
    (Set.finite_Iic _).biUnion fun i _ => by have := hι i; exact Set.finite_range _
  obtain ⟨L, _, _, _, _, _, _, _, _, _, _, hker, hSL⟩ :=
    exists_galois_ker_le_range l (N (k + (2 * T + 8))) _ (hopen _) hS
  set res : GQ l →* (L ≃ₐ[ℚ_[l]] L) := AlgEquiv.restrictNormalHom L with hres
  set I := lowerRamificationGroup ℚ_[l] L 0 with hI
  have hlift : ∀ j ≤ 2 * T + 8, ∀ σ : GQ l, res σ ∈ (N (k + j)).map res → σ ∈ N (k + j) := by
    intro j hj σ ⟨τ, hτ, e⟩
    have h : τ⁻¹ * σ ∈ res.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
    have h' : τ⁻¹ * σ ∈ N (k + j) := hanti (by omega) (hker h)
    simpa using (N (k + j)).mul_mem hτ h'
  have hE : 0 < Nat.card I := Nat.card_pos
  have hfin := _root_.GlobalTheory.PMon.Ram.finiteTowerBound ℚ_[l] L l (Nat.card I) T (fun j => (N (k + j)).map res ⊓ I) Fact.out hE
    (ordIs_eq_card_inertia l L) (_root_.GlobalTheory.PMon.Ram.axIn_padic l L)
    (fun i j hij => inf_le_inf_right _ (Subgroup.map_mono (hanti (by omega)))) inf_le_right
    (fun h => hn₀ (hlift 1 (by omega) σ₀
      (h ⟨⟨σ₀, hσ₀, rfl⟩, restrictNormalHom_mem_lowerRamificationGroup_zero l L σ₀ hi₀⟩).1))
    (by
      rintro _ ⟨⟨σ, hσ, rfl⟩, hσI⟩
      exact ⟨⟨σ ^ l, h1 k σ hσ, map_pow _ _ _⟩, I.pow_mem hσI l⟩)
    (by
      rintro j hj _ ⟨⟨σ, hσ, rfl⟩, hσI⟩ hp
      refine ⟨⟨σ, h2 (k + j) σ (hanti (Nat.zero_le _) hσ) (hlift (j + 1) hj _ ?_), rfl⟩, hσI⟩
      rw [map_pow]; exact hp.1)
    (by
      intro i hi
      have := _root_.GlobalTheory.PMon.Ram.detects_restrictNormal_inf l L 8 (N (k + i)) (N (k + i + 8)) I (ι i) (x i) (a i)
        (fun b => hSL (Set.mem_biUnion (show i ∈ Set.Iic (2 * T) from hi) ⟨b, rfl⟩)) (hxa i) (hdet i)
      simpa [add_assoc] using this)
  have hidx := card_le_index_mul_card_map_inf (GQ l) (L ≃ₐ[ℚ_[l]] L) res (N k) I
    (AlgEquiv.restrictNormalHom_surjective _) hT
  have hlt : T < 2 ^ T := Nat.lt_two_pow_self
  have hpos : 0 < Nat.card ↥((N k).map res ⊓ I) := Nat.card_pos
  simp only [add_zero] at hfin
  nlinarith

end GlobalTheory.PMon.Ram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PotentialFamilySummandRestrictionStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_family_summand_restriction : ∀ (D : D7), FontaineAtPlacesOverL (D := D) → PotDRL D.loc → ∀ (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r →
    ∀ (Xs : Set (D.nd.X i)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (n : ℕ),
      PotFam i w hw (fun x : ↥Xs => rTwO D.nd i r x) n →
    ∀ X : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw), IsSummandTw i w hw r Xs X →
      IsDR (Br.PD D.loc D.nbr i w hw) X.ρ ∧
      ∃ (X' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) (Br.OLL D.nbr i w hw))
        (PX : X.V →ₗ[Br.LL D.nbr i w hw] X'.V →ₗ[Br.LL D.nbr i w hw] Br.LL D.nbr i w hw),
        IsDual1 (Br.PD D.loc D.nbr i w hw) X.ρ X'.ρ PX ∧
        IsSubFam (fun x : ↥Xs => Br.loc D.nbr i w hw (rDuO D.nd i r x)) X' := by
  first | exact @GlobalTheory.SummandDual.xdual | exact GlobalTheory.SummandDual.xdual | (intros; apply GlobalTheory.SummandDual.xdual <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCrystalChangeOfBasisConstantCoeffEqOneStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismCrystal_changeOfBasis_constantCoeff_eq_one : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (PP S₀ : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (δ : GlobalTheory.Prism.Hom PP S₀) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (κ₀ : ZMod a → S₀.A →+* K⟦X⟧), δ.comp p₀ = δ.comp p₁ → (∀ τ y, κ₀ τ (δ.f y) = PowerSeries.constantCoeff (κ τ y)) → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)).map PowerSeries.constantCoeff = 1 := by
  first | exact @GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | exact GlobalTheory.CrysDiag.eps_constantCoeff_eq_one | (intros; apply GlobalTheory.CrysDiag.eps_constantCoeff_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PsiAtPsiAt
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.JointSix

theorem psiAt_psiW {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) :
    BlochKatoReduction.Gen.psiAt (C.sd w) (KillingConditions.psiW C w) = GlobalTheory.PtCore.psiG D C w := by
  unfold KillingConditions.psiW GlobalTheory.PtCore.psiG
  cases h : C.sd w
  · ext g
    simp [BlochKatoReduction.Gen.psiAt]
  · simp [BlochKatoReduction.Gen.psiAt]

theorem main : GlobalTheory.TwSys.Cheb → ∀ (D : D7) (C : NChoice D)
    (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))),
    GlobalTheory.PtCore.PtFam D r ρ → NChTie D C → GlobalTheory.PtCore.TriplesGood D → GlobalTheory.PtCore.SameTwist D C →
    GlobalTheory.PtCore.GoodPtRow D → GlobalTheory.PtCore.ResAbsIrr D → KillingConditions.SignatureChoiceCondition ρ C := by
  intro hC D C r ρ hF hT hTr hS hG hR i _
  have hsel := GlobalTheory.PtSel.selCore hC D C hT hTr hG hR hS ρ
    (fun i π hπ => hF.pt i π (Formalism.L2.zgoodSub D i hπ))
  refine ⟨fun π hπ => ?_, ?_⟩
  · obtain ⟨s, h1, h2, h3, h4, -⟩ := hsel i π hπ
    refine ⟨s, h1, ?_⟩
    rw [h2, psiAt_psiW]
    exact ⟨h3, h4⟩
  · rw [Rat.cast_sum, ← hT.Q_eq i]
    exact Finset.sum_le_sum fun v hv => GlobalTheory.T.conductorRoot_sub_one_length_le_tameValue D C hT i v hv

end GlobalTheory.JointSix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
section
noncomputable section

namespace GlobalTheory.JSW

def padTo {m n : ℕ} (_h : m ≤ n) (l : Fin m → ℕ) : Fin n → ℕ :=
  fun i => if hi : (i : ℕ) < m then l ⟨i, hi⟩ else 0


open Classical in
def antiParts (m d : ℕ) : Finset (Fin m → ℕ) :=
  (Finset.Nat.antidiagonalTuple m d).filter Antitone

def jtDet {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) : A :=
  Matrix.det (Matrix.of fun i j : Fin m =>
    if ((l i : ℤ) - i + j) < 0 then 0 else h (((l i : ℤ) - i + j).toNat))

def staircase (m : ℕ) : Fin m → ℕ := fun i => m - 1 - i

def alternant (A : Type*) [CommRing A] (m : ℕ) (μ : Fin m → ℕ) : MvPolynomial (Fin m) A :=
  Matrix.det (Matrix.of fun i j : Fin m => (MvPolynomial.X j : MvPolynomial (Fin m) A) ^ μ i)

theorem schur_eq_jtDet (n : ℕ) (l : Fin n → ℕ) :
    schur n l = jtDet n (fun k => MvPolynomial.hsymm (Fin n) ℤ k) l := rfl

theorem mem_antiParts {m d : ℕ} {l : Fin m → ℕ} : l ∈ antiParts m d ↔ ∑ i, l i = d ∧ Antitone l := by
  classical
  simp [antiParts, Finset.Nat.mem_antidiagonalTuple]

theorem padTo_self {m : ℕ} (l : Fin m → ℕ) : padTo le_rfl l = l := by
  funext i; simp [padTo, i.2]

end GlobalTheory.JSW
end
end

