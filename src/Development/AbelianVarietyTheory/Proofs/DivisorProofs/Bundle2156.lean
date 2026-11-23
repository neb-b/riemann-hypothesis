module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeIffOfSpecializesGeometricPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1846
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTateIsoOfLevel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPointPolarisedFibreUniformised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolPoint

theorem isProper_of_image {S T : Scheme.{0}} (A : Over S) (B : Over T) (g : T ⟶ S) (φ : B.left ⟶ A.left)
    (h : IsPullback φ B.hom A.hom g) (W : S.Opens) (hg : ∀ t, g t ∈ W) (hpr : IsProper (A.hom ∣_ W)) :
    IsProper B.hom := by
  have hr : Set.range g ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg y
  have hr' : Set.range φ ⊆ Set.range (A.hom ⁻¹ᵁ W).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show A.hom (φ y) ∈ W
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact hg _
  let l := IsOpenImmersion.lift W.ι _ hr
  let ψ := IsOpenImmersion.lift (A.hom ⁻¹ᵁ W).ι φ hr'
  have hl : l ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ hr
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ W).ι = φ := IsOpenImmersion.lift_fac _ _ hr'
  have big : IsPullback (ψ ≫ (A.hom ⁻¹ᵁ W).ι) B.hom A.hom (l ≫ W.ι) := by rw [hψ, hl]; exact h
  have sq : IsPullback ψ B.hom (A.hom ∣_ W) l := by
    refine IsPullback.of_right big ?_ (isPullback_morphismRestrict A.hom W).flip
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, h.w, Category.assoc, hl]
  exact MorphismProperty.of_isPullback (P := @IsProper) sq hpr

theorem exists_field_point_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW y hyW hy
  obtain ⟨⟨hN, -, -, -⟩, -⟩ := hR
  let O := Localization.AtPrime y.asIdeal
  have hiO : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDomain O := IsLocalization.isDomain_localization y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing y.asIdeal.primeCompl O hN
  have hf : ¬ IsField O := by
    intro hfO
    apply hy
    have h1 : maximalIdeal O = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfO
    have h2 := Localization.AtPrime.under_maximalIdeal (I := y.asIdeal)
    rw [← h2, Ideal.under, h1]
    exact Ideal.comap_bot_of_injective _ hiO
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  let a : R →+* V := ρ.comp (algebraMap R O)
  have ha : Function.Injective a := hρ.comp hiO
  have hgen : ∀ q : PrimeSpectrum V, spMap a q ∈ W := by
    intro q
    have hle : PrimeSpectrum.comap a q ≤ y := by
      show Ideal.comap a q.asIdeal ≤ y.asIdeal
      intro s hs
      rw [← Localization.AtPrime.under_maximalIdeal (I := y.asIdeal)]
      exact IsLocalRing.le_maximalIdeal (q.isPrime.comap ρ).ne_top hs
    exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open W.isOpen hyW
  let B := (Over.pullback (spMap a)).obj G
  have hcart : IsPullback (pullback.fst G.hom (spMap a)) B.hom G.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hpB : IsProper B.hom := isProper_of_image G B (spMap a) _ hcart W hgen hW
  have hsB := IsSemiAbelian.pullback (spMap a) G hG
  have hAb : IsAbelianScheme B := ⟨hsB.comm, hsB.smooth, hpB, hsB.geomConnected⟩
  obtain ⟨hL, hL2, -⟩ := GlobalTheory.allSixLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  let φ := U.gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hφ : IsGrpPullback A.A G (spMap (algebraMap R (FractionRing R))) φ :=
    GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hLφ : LBIso A.L (M.L.L.pull φ) := LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
    (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
  obtain ⟨P', M', φ', hφ', hL', hM'⟩ :=
    GlobalTheory.PolExtendDVR.exists_baseChange (K' := FractionRing V) hL.polBaseChange a ha A G M φ hφ hLφ
  obtain ⟨hAB, hKB⟩ := GlobalTheory.polarisation_extends_dvr hL hL2 V (FractionRing V) P' B M' φ' hAb hφ' hL'
  let r := IsLocalRing.residue V
  obtain ⟨z, hz0⟩ : ∃ z : Sp (IsLocalRing.ResidueField V) ⟶ Sp R, z = spMap (r.comp a) := ⟨_, rfl⟩
  have hz : z = spMap r ≫ spMap a := by
    rw [hz0]
    unfold spMap
    rw [← Spec.map_comp]
    rfl
  let ψ : pullback G.hom z ⟶ B.left := pullback.lift (pullback.fst G.hom z) (pullback.snd G.hom z ≫ spMap r)
    (by rw [pullback.condition, hz, Category.assoc])
  have hψ : ψ ≫ pullback.fst G.hom (spMap a) = pullback.fst G.hom z := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ B.hom = ((Over.pullback z).obj G).hom ≫ spMap r := pullback.lift_snd _ _ _
  have hgz : IsGrpPullback ((Over.pullback z).obj G) B (spMap r) ψ :=
    (isGrpPullback_pullback G (spMap a)).cancel ((isGrpPullback_pullback G z).congr hz hψ.symm) hψ2
  have hiso : LBIso (U.LG.L.pull (pullback.fst G.hom z)) (M'.L.L.pull ψ) := by
    have e := GlobalTheory.PolExtendDVR.lbIso_pull_comp hM' ψ
    rw [hψ] at e
    exact e.symm
  obtain ⟨w, hw⟩ := hiso
  have hw' := (isGen_iff w).1 hw
  refine ⟨IsLocalRing.ResidueField V, inferInstance, z, ?_, ?_, ?_, ?_⟩
  · have e1 : PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint r
    have e2 : PrimeSpectrum.comap ρ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint O :=
      IsLocalRing.comap_closedPoint ρ
    have e3 : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = y :=
      PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
    rw [hz0]
    show PrimeSpectrum.comap (algebraMap R O) (PrimeSpectrum.comap ρ
      (PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)))) = y
    rw [e1, e2, e3]
  · exact MorphismProperty.of_isPullback (P := @IsProper) hgz.1 hpB
  · exact relAmple_pull hgz.1 M'.L.isLB (pull_isLB U.LG.isLB _) hw' ⊤ (isAffineOpen_top _) (fun _ => trivial) hAB
  · exact kTriv_pull hgz M'.L.isLB (pull_isLB U.LG.isLB _) hw' hKB

end GlobalTheory.PolPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLevelLiftScheme
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.LevCover

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

def TateAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k] (x : Sp k ⟶ S)
    (l : D.La → (Over.mk x ⟶ o.A)) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, l y = I.ev N' y

theorem tateAt_congr {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) {k : Type} [Field k]
    {x x' : Sp k ⟶ S} (e : x = x') (l : D.La → (Over.mk x ⟶ o.A)) (l' : D.La → (Over.mk x' ⟶ o.A))
    (h : ∀ a, (Over.homMk (𝟙 _) (by simp [e]) : Over.mk x' ⟶ Over.mk x) ≫ l a = l' a) :
    TateAt o N' x l → TateAt o N' x' l' := by
  subst e
  have h' : ∀ a, l a = l' a := fun a => by
    rw [← h a]
    have : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := by ext; simp
    rw [this, Category.id_comp]
  rintro ⟨I, hI⟩
  exact ⟨I, fun a => (h' a).symm.trans (hI a)⟩

theorem comp_actN_nsmul {A : Over S} [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) {T : Over S}
    (x : T ⟶ A) (n : ℕ) (c : D.O) : x ≫ act.act (n • c) = (x ^ n) ≫ act.act c := by
  have := act.hom c
  rw [add_map_nsmul act.add, MonObj.comp_pow, MonObj.pow_comp]

theorem exists_liftHom {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (N' : ℕ) (hc : N'.Coprime p)
    (hd : N ∣ N') :
    ∃ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom ∧ Etale Z.hom ∧ (∀ a c, et (a + c) = et a * et c) ∧
      (∀ a, et (N' • a) = 1) ∧ (∀ (c : D.O) a, et (c • a) = et a ≫ o.act.act c) ∧
      (∀ a, et ((N' / N) • a) = toUnit Z ≫ o.eta a) ∧
      ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (∀ a c, lv (a + c) = lv a * lv c) → (∀ a, lv (N' • a) = 1) →
        (∀ (c : D.O) a, lv (c • a) = lv a ≫ o.act.act c) → (∀ a, lv ((N' / N) • a) = toUnit T ≫ o.eta a) →
          ∃! h : T ⟶ Z, ∀ a, h ≫ et a = lv a := by
  have hN' := levelPos_of_coprime hc
  have hNS : IsUnit (N' : Γ(S, ⊤)) := by
    have := (b.unit N' hc).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  haveI := D.freeLa
  haveI := D.finLa
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨Z, y, hfin, het, yadd, ypow, huniv⟩ := GlobalTheory.exists_finiteEtale_latticeTorsionHom S o.A N' D.La o.ab hNS
  have R : RepTors o.A N' D.La Z y := ⟨hfin, het, yadd, ypow, huniv⟩
  haveI := hfin
  haveI := het
  have ymod : ∀ a c, y (a + N' • c) = y a := fun a c => by
    rw [yadd, add_map_nsmul yadd, ypow, _root_.mul_one]
  have etaN : ∀ a, o.eta (N' • a) = 1 := fun a => by
    rw [← Nat.mul_div_cancel' hd, mul_smul, o.eta_ker]
  obtain ⟨κ', _, q', hq'⟩ := exists_finite_mod D.O hN'
  have c1 : ClopenCond Z fun _ h => ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := by
    refine ClopenCond.forall_of_finite q' (fun c => ?_) fun c c' e T' h Hc a => ?_
    · have := o.act.hom c
      refine R.clopenCond (fun a => y (c • a)) (fun a => y a ≫ o.act.act c) (fun a a' => by rw [smul_add, yadd])
        (fun a => ypow _) (fun a a' => by rw [yadd, MonObj.mul_comp]) fun a => by
          rw [← MonObj.pow_comp, ypow, MonObj.one_comp]
    · obtain ⟨d, rfl⟩ := hq' c c' e
      have := o.act.hom d
      rw [add_smul, smul_assoc, ymod, Hc, o.act.add, MonObj.comp_mul, comp_actN_nsmul, ypow, MonObj.one_comp,
        _root_.mul_one]
  have c2 : ClopenCond Z fun _ h => ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) :=
    R.clopenCond (fun a => y ((N' / N) • a)) (fun a => toUnit Z ≫ o.eta a) (fun a a' => by rw [smul_add, yadd])
      (fun a => ypow _) (fun a a' => by rw [o.eta_add, MonObj.comp_mul]) fun a => by
        rw [← MonObj.comp_pow, ← add_map_nsmul o.eta_add, etaN, MonObj.comp_one]
  obtain ⟨U, hU, HU⟩ := c1.and c2
  obtain ⟨W, i, hW1, hW2, hmono, Hi⟩ := exists_sub U hU
  have hi := (HU W i).2 ((Hi W i).2 ⟨𝟙 W, Category.id_comp i⟩)
  refine ⟨W, fun a => i ≫ y a, hW1, hW2, fun a c => by beta_reduce; rw [yadd, MonObj.comp_mul],
    fun a => by beta_reduce; rw [add_map_nsmul yadd, ypow, MonObj.comp_one],
    fun c a => by beta_reduce; rw [hi.1, Category.assoc], fun a => ?_, fun T lv hadd hker hlin hlev => ?_⟩
  · beta_reduce
    rw [hi.2, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  have hpow : ∀ a, lv a ^ N' = 1 := fun a => by rw [← add_map_nsmul hadd, hker]
  obtain ⟨h, hh, -⟩ := huniv T lv hadd hpow
  have hP1 : ∀ (c : D.O) a, h ≫ y (c • a) = h ≫ y a ≫ o.act.act c := fun c a => by
    rw [hh, hlin, ← hh a, Category.assoc]
  have hP2 : ∀ a, h ≫ y ((N' / N) • a) = h ≫ (toUnit Z ≫ o.eta a) := fun a => by
    rw [hh, hlev, ← Category.assoc]
    congr 1
    exact toUnit_unique _ _
  obtain ⟨h', hh'⟩ := (Hi T h).1 ((HU T h).1 ⟨hP1, hP2⟩)
  refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
  have : g ≫ i = h' ≫ i := R.ext fun a => by
    rw [Category.assoc, Category.assoc, hg, ← Category.assoc, hh', hh]
  exact (cancel_mono i).1 this

theorem exists_liftScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N N' : ℕ), N'.Coprime p → N ∣ N' → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (ηu : D.La → (Y ⟶ o.A)), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (T : Over S) (lv : D.La → (T ⟶ o.A)), (IsLift o N' T lv → ∃! f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) ∧ ((∃ f : T ⟶ Y, ∀ a, f ≫ ηu a = lv a) → IsLift o N' T lv) := by
  intro p _ D R _ b N N' hc hd S _ s o
  obtain ⟨Z, et, hZf, hZe, eadd, eker, elin, elev, huniv⟩ := exists_liftHom o N' hc hd
  haveI := hZf
  haveI := hZe
  haveI : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hsp : ∀ {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] (x : Sp k ⟶ Z.left)
      (x' : Sp k' ⟶ Z.left) (u : Sp k) (u' : Sp k'), x'.base u' ⤳ x.base u →
      (TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        TateAt o N' (x' ≫ Z.hom) (fun a => (Over.homMk x' rfl : Over.mk (x' ≫ Z.hom) ⟶ Z) ≫ et a)) :=
    fun x x' u u' h => _root_.GlobalTheory.HTSpecTate.tateIsoO_iff_of_specializes p D R b N N' hc S s o Z et eadd eker elin x x' u u' h
  let U : Set Z.left := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ Z.left),
    z ∈ Set.range x.base ∧
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a)}
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Z.left),
      TateAt o N' (x ≫ Z.hom) (fun a => (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ et a) ↔
        Set.range x.base ⊆ U := by
    intro k _ _ x
    refine ⟨fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩, fun hx => ?_⟩
    let pt : Sp k := (⊥ : PrimeSpectrum k)
    obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
    exact (hsp x x' pt u' (hu' ▸ specializes_rfl)).2 hG'
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff Z.left U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := FinEt.exists_algClosed_point Z.left z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩, (hsp x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  let U' : Z.left.Opens := ⟨U, hclo.isOpen⟩
  obtain ⟨V, i, hV1, hV2, hmono, Hi⟩ := exists_sub U' hclo.isClosed
  refine ⟨V, fun a => i ≫ et a, hV1, hV2, fun T lv => ⟨fun hL => ?_, fun hex => ?_⟩⟩
  · obtain ⟨hadd, hker, hlin, hlev, hgeo⟩ := hL
    obtain ⟨h, hh, hu⟩ := huniv T lv hadd hker hlin hlev
    have hr : Set.range h.left ⊆ U' := by
      rintro _ ⟨t, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := FinEt.exists_algClosed_point T.left t
      obtain ⟨u, hu⟩ : t ∈ Set.range x.base := by rw [show Set.range x.base = {t} from hx]; rfl
      have hG := tateAt_congr o N' (x' := (x ≫ h.left) ≫ Z.hom)
        (by rw [Category.assoc, Over.w h]) _
        (fun a => (Over.homMk (x ≫ h.left) rfl : Over.mk ((x ≫ h.left) ≫ Z.hom) ⟶ Z) ≫ et a)
        (fun a => by rw [← hh a, ← Category.assoc, ← Category.assoc]; congr 1; try (ext; simp)) (hgeo k x)
      refine (key k (x ≫ h.left)).1 hG ⟨u, ?_⟩
      rw [Scheme.Hom.comp_apply, hu]
    obtain ⟨h', hh'⟩ := (Hi T h).1 hr
    refine ⟨h', fun a => by beta_reduce; rw [← Category.assoc, hh', hh], fun g hg => ?_⟩
    have : g ≫ i = h := hu _ fun a => by rw [Category.assoc]; exact hg a
    exact (cancel_mono i).1 (this.trans hh'.symm)
  · obtain ⟨f, hf⟩ := hex
    have hf' : ∀ a, lv a = (f ≫ i) ≫ et a := fun a => by rw [Category.assoc]; exact (hf a).symm
    refine ⟨fun a c => by rw [hf', hf', hf', eadd, MonObj.comp_mul], fun a => by rw [hf', eker, MonObj.comp_one],
      fun c a => by rw [hf', hf', elin]; simp only [Category.assoc], fun a => ?_, fun k _ _ x => ?_⟩
    · rw [hf', elev, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    have hr : Set.range (f ≫ i).left ⊆ U' := (Hi T (f ≫ i)).2 ⟨f, rfl⟩
    have hG := (key k (x ≫ (f ≫ i).left)).2 fun z ⟨u, hu⟩ => hr ⟨x.base u, by rw [← hu, Scheme.Hom.comp_apply]⟩
    refine tateAt_congr o N' (by rw [Category.assoc, Over.w (f ≫ i)]) _ _ ?_ hG
    intro a
    rw [hf' a]
    simp only [← Category.assoc]
    congr 1
    try (ext; simp)

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleLocalExtResidueFieldSeparable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_etale_of_isSeparable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
    AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k']
    [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'],
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R')
      (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧
      σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  intro R _ _ _ hR k' _ _ _ _
  obtain ⟨hN, -, hIC, hC⟩ := hR
  haveI := hN; haveI := hIC; haveI := hC
  obtain ⟨A, _, _, hfin, het, hloc, ⟨ε⟩⟩ := GlobalTheory.exists_etale_lift_of_isSeparable R k'
  haveI : IsLocalHom (algebraMap R A) :=
    ((local_hom_tfae (algebraMap R A)).out 1 5).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale R (maximalIdeal A)
    (Localization.AtPrime (maximalIdeal A))
  let e := IsLocalization.atUnits A (maximalIdeal A).primeCompl
    (S := Localization.AtPrime (maximalIdeal A)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  haveI : IsDomain A := e.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherian R A := inferInstance
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  let g2 : ResidueField R ⊗[R] A →ₐ[R] ResidueField A :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField A))
      (IsScalarTower.toAlgHom R A (ResidueField A)) (fun _ _ => Commute.all _ _)
  let σ : k' →+* ResidueField A := g2.toRingHom.comp ε.symm.toRingHom
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap R A, σ,
    ⟨⟨inferInstance, inferInstance, inferInstance, ?_⟩, ?_, RingHom.finite_algebraMap.mpr hfin⟩,
    RingHom.etale_algebraMap.mpr het, ?_⟩
  · have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) A
    rwa [hm] at this
  · haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
    intro x y hxy
    rw [← sub_eq_zero]
    have h0 : (x - y) • (1 : A) = 0 := by
      rw [Algebra.smul_def, _root_.mul_one, map_sub, hxy, sub_self]
    exact (smul_eq_zero.mp h0).resolve_right one_ne_zero
  · ext r
    simp only [RingHom.comp_apply, σ, AlgEquiv.coe_toRingEquiv, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, AlgHom.toRingHom_eq_coe]
    change g2 (algebraMap (ResidueField R) (ResidueField R ⊗[R] A) (residue R r)) = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [g2]

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtAbelianVarietyHomDescent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.HomFinExt

open GlobalTheory.Spread GlobalTheory.HomExtNormal

theorem exists_finite_hom : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] (ga : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ f : (Over.pullback (spMap ga)).obj A ⟶ (Over.pullback (spMap ga)).obj A', IsMonHom f → ∃ (K' : Type) (_ : Field K') (io : K →+* K') (Ω' : Type) (_ : Field Ω') (j : Ω →+* Ω') (l : K' →+* Ω') (f' : (Over.pullback (spMap io)).obj A ⟶ (Over.pullback (spMap io)).obj A'), io.Finite ∧ l.comp io = j.comp ga ∧ IsMonHom f' ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ pullback A.hom (spMap ga)) (p' : Z ⟶ pullback A.hom (spMap io)) (t : Z ⟶ Sp Ω'), p ≫ pullback.fst _ _ = p' ≫ pullback.fst _ _ → p ≫ pullback.snd _ _ = t ≫ spMap j → p' ≫ pullback.snd _ _ = t ≫ spMap l → p ≫ f.left ≫ pullback.fst _ _ = p' ≫ f'.left ≫ pullback.fst _ _ := by
  intro K Ω _ _ _ ga A A' _ _ hA hA' f hf
  haveI := hf
  have := hA.proper
  have := hA'.proper
  have := hA.smooth
  have := hA'.smooth
  let Ωb := AlgebraicClosure Ω
  let j : Ω →+* Ωb := algebraMap Ω Ωb
  letI : Algebra K Ωb := (j.comp ga).toAlgebra
  let Kb := algebraicClosure K Ωb
  have hcomp : spMap j ≫ spMap ga = spMap (algebraMap K Ωb) := by
    rw [← Spec.map_comp]; rfl
  obtain ⟨f₁, hf₁, e₁⟩ := exists_pull_hom (spMap j) (spMap ga) (spMap (algebraMap K Ωb)) hcomp f
  obtain ⟨g, hg, eg⟩ := _root_.GlobalTheory.ChowRigid.chow_rigidity K Ωb A A' hA hA' f₁ hf₁
  obtain ⟨s, hs⟩ := GlobalTheory.HomPairDescent.exists_descend (K := K) (Ω := Kb) A A' g
  let L : IntermediateField K Kb := IntermediateField.adjoin K (s : Set Kb)
  obtain ⟨g', hg'⟩ := hs L (IntermediateField.subset_adjoin _ _)
  have hfin : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have gA := GlobalTheory.HomPairDescent.isGrpPullback_bcMap A L.val
  have gB := GlobalTheory.HomPairDescent.isGrpPullback_bcMap A' L.val
  obtain ⟨-, hmon⟩ := GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff L Kb L.val.toRingHom
  have hg'm : IsMonHom g' := (hmon _ _ _ _ _ _ g' g gA gB hg').1 hg
  let l : L →+* Ωb := Kb.val.toRingHom.comp L.val.toRingHom
  refine ⟨L, inferInstance, algebraMap K L, Ωb, inferInstance, j, l, g', RingHom.finite_algebraMap.mpr hfin,
    ?_, hg'm, ?_⟩
  · ext x
    change Kb.val (L.val (algebraMap K L x)) = algebraMap K Ωb x
    rw [AlgHom.commutes, AlgHom.commutes]
  · intro Z p p' t h1 h2 h3
    have hP : (p ≫ pullback.fst _ _) ≫ A.hom = t ≫ spMap (algebraMap K Ωb) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, h2, Category.assoc, hcomp]
    let P : Z ⟶ pullback A.hom (spMap (algebraMap K Ωb)) := pullback.lift (p ≫ pullback.fst _ _) t hP
    have hPp : P ≫ pullMap (spMap j) (spMap ga) (spMap (algebraMap K Ωb)) hcomp A = p := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, pullback.lift_fst]
      · rw [Category.assoc, pullMap_snd, pullback.lift_snd_assoc, h2]
    have hQ : (P ≫ bcMap A.hom Kb.val) ≫ bcMap A.hom L.val = p' := by
      apply pullback.hom_ext
      · rw [Category.assoc, bcMap_fst, Category.assoc, bcMap_fst, pullback.lift_fst, h1]
      · rw [Category.assoc, bcMap_snd, Category.assoc, bcMap_snd_assoc, pullback.lift_snd_assoc, h3]
        rw [← Spec.map_comp]; rfl
    calc p ≫ f.left ≫ pullback.fst _ _
        = P ≫ f₁.left ≫ pullback.fst _ _ := by rw [e₁, ← hPp, Category.assoc]
      _ = P ≫ bcMap A.hom Kb.val ≫ g.left ≫ pullback.fst _ _ := by rw [eg]
      _ = p' ≫ g'.left ≫ pullback.fst _ _ := by
        rw [← hQ, Category.assoc, Category.assoc, ← Category.assoc (bcMap A.hom L.val), hg', Category.assoc,
          bcMap_fst]

end GlobalTheory.HomFinExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarmonicPolynomialLocalDepthBetweenStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harmonicPolynomial_localDepth_between : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (a : (D.host.E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → ∀ n : ℕ, ∑ f : Lt1 Dw, 2 * rk f ≤ n → ∀ A B : ℝ, NuBetween Xo la (gap Dw a) A B → ∃ P₁ ∈ harmA (Dw := Dw) c a n, PolyBetween Xo la P₁ A B := by
  first | exact @GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | exact GlobalTheory.RefSum.GlobalPoly.exists_polyBetween | (intros; apply GlobalTheory.RefSum.GlobalPoly.exists_polyBetween <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitEqPositiveSquaresTimesSelfAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_eq_positive_squares_times_selfAdjoint : ∀ (n : ℕ) (Tm : Matrix (Fin n) (Fin n) ℚ) (B : Matrix (Fin n) (Fin n) ℝ), B.PosDef → (B * Tm.map (Rat.cast : ℚ → ℝ)).PosDef → ∃ (c₀ : ℚ) (r : ℕ) (c : Fin r → ℚ) (p : Fin r → Polynomial ℚ), 0 < c₀ ∧ (∀ i, 0 < c i) ∧ (1 : Matrix (Fin n) (Fin n) ℚ) = c₀ • Tm + ∑ i, c i • ((Polynomial.aeval Tm (p i)) ^ 2 * Tm) := by
  first | exact @GlobalTheory.Desc.SqLin.main | exact GlobalTheory.Desc.SqLin.main | (intros; apply GlobalTheory.Desc.SqLin.main <;> assumption)
end

