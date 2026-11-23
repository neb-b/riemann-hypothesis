module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelDetAdelicOfPinned
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPelUnifPull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdaptedThKerEntC
section
noncomputable section

namespace GlobalTheory.KerJ

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_hecke {D : D7} {C : CharFrame D} (Dt : Formalism.L2.Host.DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n) (hord : ξ.OrderDvd n)
    (mt : ℕ → D.Dt →* ℂˣ) (h : ∀ (j : Fin D.R.m) a, Formalism.L2.Host.IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _), GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : Formalism.L2.Host.eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [Formalism.L2.Host.eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.KerJ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.KerEntTrue

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem powRatAll_true (l : I.Laws) (Z : TC.Later B (I.cols l)) : GL3Theta.PowRatAll (I.rec7 l Z) := by
  obtain ⟨idl, h⟩ := GlobalTheory.Mem.NormOneIdeal.pinned_of_finer (I.rec7 l Z) I.SQ (MulEquiv.refl _)
    (by
      show UOQ B.host I.SQ = _
      ext x
      constructor
      · intro h
        exact ⟨x, h, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact hy)
    (fun z => rfl)
    (fun N L L' t ht => by
      exact (trueDtPackQ_relDet I.SQ I.C N L L').trans ht)
  exact GL3Theta.powRatAll_of _ idl h (GlobalTheory.KernelScalarUnit.normOne_pow _)

theorem mtType_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : I.StdO l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_hecke T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

theorem rhoAlg_std (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ}
    {O : ∀ u a, GL3Theta.LiftObj (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).chTw u a)} (hO : I.StdO l Z Qp O) (u : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Word) (a : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).what₂.Tup) :
    GL3Columns.RhoAlg (O u a) := by
  have h3 := GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType _ u ((I.rec7 l Z).chTw u a) (O u a).mt (mtType_std I hok hp l Z hO u a)
  have hq := powRatAll_true I l Z
  intro i hi
  refine ⟨fun c => ?_, fun c' => ?_⟩
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt i c)
    exact ((h3 i hi).1 _ h z hz).1.1
  · obtain ⟨h, z, hz⟩ := hq ((O u a).dt (i + 1) c')
    exact ((h3 i hi).1 _ h z hz).2.1


open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.G in
theorem adaptedTh_kerEntC {D : D7} {P : Examples₂.EntPl D} {O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)} {Bs : PlaceMatrixFamily D} {Dx : DivX D} {Tw : TwForms D}
    (hB : BasOk P O Bs) (hA : AdaptedEnt P O Bs Dx) (h : KerEntHyp P O Bs Dx Tw) : AdaptedTh (kerEntC P O Bs h) O := by
  intro w hw u μ hl
  obtain ⟨Pm, h1, h2, h3, h4⟩ := hA w hw u μ hl
  refine ⟨Pm, h1, h2, h3, fun i hi c c' => ?_⟩
  show thAtW P O Bs u μ w i c c' = _
  unfold thAtW
  congr 1
  funext k j
  unfold adCoef
  split_ifs with hk
  · set s := Formalism.MainNotions.TaylorLogMetric.lamC (P.lam w) ((O u μ).dgen k.1) with hs
    have hs0 : s ≠ 0 := by
      intro h0
      have hd := (hB u μ w (i + 1) hi c' k.1).1
      haveI hne : Nonempty (Fin (D.R.N (i + 1))) := ⟨j.2.2⟩
      rw [h4 (i + 1) hi c' k.1, ← hs, h0, _root_.inv_zero, zero_pow (by omega), zero_smul] at hd
      exact hd Matrix.det_zero
    have hdet : ((Pm i c k.1).map (tauEmb D (P.lam w) k.1)).det ≠ 0 := (h1 i hi.le c k.1).1
    have ht : s⁻¹ ^ i ≠ 0 := pow_ne_zero _ (inv_ne_zero hs0)
    have hinv : (s⁻¹ ^ i • (Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ =
        (s⁻¹ ^ i)⁻¹ • ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ ht, one_smul]
      exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet)
    rw [h4 (i + 1) hi c' k.1, h4 i hi.le c k.1, ← hs, hinv]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have e : (1 : ℂ_[D.what₂.places.resChar w]) * s * s⁻¹ ^ (i + 1) * (s⁻¹ ^ i)⁻¹ = 1 := by
      rw [inv_pow, inv_pow, inv_inv, pow_succ]
      field_simp
    simp only [show (kerEntC P O Bs h).lam w = P.lam w from rfl]
    generalize ((Pm (i + 1) c' k.1).map (tauEmb D (P.lam w) k.1)) k.2.1 j.2.2 = x
    generalize ((Pm i c k.1).map (tauEmb D (P.lam w) k.1))⁻¹ j.2.1 k.2.2 = y
    linear_combination (x * y) * e
  · rfl

end GlobalTheory.Mem.Col2.KerEntTrue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem admissibleBase_of_completeNormalLocalCharZero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (h : IsCN R) :
    AdmBase R (maximalIdeal R) :=
  ⟨h.1, inferInstance, h.2.1, h.2.2.1⟩

theorem pullSt : PullSt := by
  intro E _ _ _ H R R' _ _ _ _ _ _ φ t P hR hR' hφ hloc _
  obtain ⟨h1, -, h3, h4, h5, -⟩ := GlobalTheory.allSixLaws
  have aR := admissibleBase_of_completeNormalLocalCharZero hR
  have aR' := admissibleBase_of_completeNormalLocalCharZero hR'
  have : CharZero R' := hR'.2.2.2
  have hI : (maximalIdeal R).map φ ≤ maximalIdeal R' :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (map_mem_nonunits_iff φ a).2 ha
  obtain ⟨t', m₀, P', hD, -, -, -, -, xl, -⟩ :=
    GlobalTheory.ArcDataDescent.exists_pelUnif_pull h3.cubePull h1.polBaseChange h4.unifBaseChange h5 aR aR' t P φ hφ hI
  let e : P'.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X := { hD.xe with map_smul' := xl }
  exact ⟨t', m₀, P', e, GlobalTheory.FlatTors.torsionIso_holds E H R' _ aR' t' P',
    fun y r hr => GlobalTheory.PelCoordPull.psiCoord_pull hD y r hr⟩

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.TorRef.DomFine

theorem generalizing_of_stalk {Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) : GeneralizingMap ξ := by
  have h₁ : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := by
    rw [Flat.SpecMap_iff]; exact hf
  have h₂ : GeneralizingMap (Y.fromSpecStalk (ξ (closedPoint _))) := by
    refine (Y.fromSpecStalk (ξ (closedPoint _))).isEmbedding.isInducing.generalizingMap ?_
    rw [Scheme.range_fromSpecStalk]
    exact fun a b hab hb => hab.trans hb
  have e : (ξ : Sp A → Y) = Y.fromSpecStalk (ξ (closedPoint _)) ∘ Spec.map (Scheme.stalkClosedPointTo ξ) := by
    funext p
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    exact Scheme.Hom.comp_apply _ _ _
  rw [e]
  exact (Flat.generalizingMap _).comp h₂

theorem eq_of_specializes {Y : Scheme.{0}} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) (w : Sp (FractionRing A)) (q : Y) (h : q ⤳ (jK A ≫ ξ) w) :
    q = (jK A ≫ ξ) w := by
  rw [Scheme.Hom.comp_apply] at h ⊢
  obtain ⟨r, hr, rfl⟩ := generalizing_of_stalk ξ hf h
  have hw : (jK A w).asIdeal = ⊥ := by
    haveI : (PrimeSpectrum.asIdeal w).IsPrime := PrimeSpectrum.isPrime w
    have hw₀ : PrimeSpectrum.asIdeal w = ⊥ := Ideal.eq_bot_of_prime _
    ext x
    change algebraMap A (FractionRing A) x ∈ PrimeSpectrum.asIdeal w ↔ _
    rw [hw₀, Ideal.mem_bot, Ideal.mem_bot]
    exact map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))
  have hle := (PrimeSpectrum.le_iff_specializes (R := A) r (jK A w)).mpr hr
  have : r = jK A w := by
    apply le_antisymm hle
    change (jK A w).asIdeal ≤ PrimeSpectrum.asIdeal r
    rw [hw]; exact bot_le
  rw [this]

theorem mem_range_of_generic {U V : Scheme.{0}} (j : U ⟶ V) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [TopologicalSpace.NoetherianSpace V] (g : V) (hg : ∀ q : V, q ⤳ g → q = g) : g ∈ Set.range j := by
  have hc : closure {g} ∈ irreducibleComponents V := by
    refine ⟨isIrreducible_singleton.closure, fun S hS hle => ?_⟩
    have hq := hS.isGenericPoint_genericPoint_closure
    have hgS : g ∈ S := hle (subset_closure rfl)
    have e := hg _ (hq.specializes (subset_closure hgS))
    rw [e] at hq
    exact subset_closure.trans hq.def.symm.subset
  obtain ⟨o, ho, hne, hle⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨u, hu, hu'⟩ := hd.inter_open_nonempty o ho hne
  have hs : g ⤳ u := specializes_iff_mem_closure.2 (hle hu)
  exact j.isOpenEmbedding.isOpen_range.stableUnderGeneralization hs hu'

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem injective_of_flat {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat)
    (κ : O →+* A) (hκ : spMap κ = ξ₀ ≫ s) : Function.Injective ((algebraMap A (FractionRing A)).comp κ) := by
  have hsρ : spMap ((algebraMap A (FractionRing A)).comp κ) = (jK A ≫ ξ₀) ≫ s := by
    rw [← spMap_comp', hκ, Category.assoc]
  refine GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ (⊥ : PrimeSpectrum (FractionRing A)) ?_
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s
    (genericPoint_specializes (s ((jK A ≫ ξ₀) (⊥ : PrimeSpectrum (FractionRing A)))))
  have h := eq_of_specializes ξ₀ hfl (⊥ : PrimeSpectrum (FractionRing A)) y hy
  rw [hsρ]
  refine (Scheme.Hom.comp_apply (jK A ≫ ξ₀) s _).trans ?_
  rw [← h, e]

theorem exists_lift_frac {O F B : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F] [CommRing B]
    (g : O →+* B) (hu : ∀ y : O, y ≠ 0 → IsUnit (g y)) : ∃ ρ : F →+* B, ρ.comp (algebraMap O F) = g := by
  have hu' : ∀ y : nonZeroDivisors O, IsUnit (g y) := fun y => hu _ (nonZeroDivisors.ne_zero y.2)
  exact ⟨IsLocalization.lift hu', IsLocalization.lift_comp hu'⟩

theorem exists_generic_fibre {O F A : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X)
    (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ v : Sp (FractionRing A) ⟶ pullback s (spMap (algebraMap O F)), v ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ s)
  obtain ⟨κ, rfl⟩ : ∃ κ : O →+* A, CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ s := hκ'
  have hρ := injective_of_flat s hs ξ₀ hfl κ hκ
  obtain ⟨ρ', hρ'⟩ := exists_lift_frac (F := F) ((algebraMap A (FractionRing A)).comp κ) (fun y hy => by
    have h0 : κ y ≠ 0 := fun h => hy (hρ (by simp [h]))
    exact IsLocalization.map_units (FractionRing A) (⟨κ y, mem_nonZeroDivisors_of_ne_zero h0⟩ : nonZeroDivisors A))
  have hv : (jK A ≫ ξ₀) ≫ s = spMap ρ' ≫ spMap (algebraMap O F) := by
    rw [spMap_comp', hρ', ← spMap_comp', hκ, Category.assoc]
  exact ⟨pullback.lift (jK A ≫ ξ₀) _ hv, pullback.lift_fst _ _ _⟩

theorem exists_generic_point (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    (X U : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap (algebraMap O F))) (hs : Flat s) (hp : IsProjOver s)
    (hj : IsOpenImmersion jQ) (hd : Dense (Set.range jQ)) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ y : Sp (FractionRing A) ⟶ U, y ≫ jQ ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨v, v1⟩ := exists_generic_fibre (F := F) s hs ξ₀ hfl
  obtain ⟨hN, hC, -⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ hs hp hj hd
  haveI : IsNoetherian X := {}
  have hb0 : IsPreimmersion (spMap (algebraMap O F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  haveI h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb0
  haveI hNs : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap (algebraMap O F))) :=
    (pullback.fst s (spMap (algebraMap O F))).isEmbedding.isInducing.noetherianSpace
  have hr : Set.range v ⊆ Set.range jQ := by
    rintro _ ⟨w, rfl⟩
    refine mem_range_of_generic jQ hd _ fun q hq => ?_
    have h' := hq.map (pullback.fst s (spMap (algebraMap O F))).continuous
    have e : (pullback.fst s (spMap (algebraMap O F))) (v w) = (jK A ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, v1]
    rw [e] at h'
    exact (pullback.fst s (spMap (algebraMap O F))).isEmbedding.injective ((eq_of_specializes ξ₀ hfl w _ h').trans e.symm)
  refine ⟨IsOpenImmersion.lift jQ v hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, v1]

end GlobalTheory.TorRef.DomFine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOriginStatement
section
open Formalism.DegreeFormula

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTop_density_model_metric_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  first | exact @GlobalTheory.DomainDens.chernTop_model_origin | exact GlobalTheory.DomainDens.chernTop_model_origin | (intros; apply GlobalTheory.DomainDens.chernTop_model_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffZeroEqZeroIff
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Geo GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.PinPlace

theorem mem_mul_iff {R K : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) (y : K) :
    (∃ a : R, y = algebraMap R K (ϖ * a)) ↔ y = 0 ∨ y⁻¹ ∉ (algebraMap R K).range := by
  have hinj := IsFractionRing.injective R K
  constructor
  · rintro ⟨a, rfl⟩
    by_contra hc
    push Not at hc
    obtain ⟨h0, b, hb⟩ := hc
    have h1 : ϖ * a * b = 1 := hinj (by rw [map_mul, hb, mul_inv_cancel₀ h0, map_one])
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one (a * b) (by rw [← mul_assoc, h1]))
  · rintro (rfl | h)
    · exact ⟨0, by simp⟩
    · rcases ValuationRing.isInteger_or_isInteger R y with ⟨b, rfl⟩ | hb
      · have hb : ¬ IsUnit b := by
          rintro ⟨u, rfl⟩
          refine h ⟨(u⁻¹ : Rˣ), ?_⟩
          exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
        have hm : b ∈ IsLocalRing.maximalIdeal R := hb
        rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
        obtain ⟨a, rfl⟩ := hm
        exact ⟨a, rfl⟩
      · exact absurd hb h

variable {D : D7} {p : ℕ} [Fact p.Prime] {la : PlL D p} {jc : DV.KW p →+* ℂ}

theorem mem_range_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    y ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ↔
      la.1.valuation D.what₂.LL z ≤ 1 := by
  obtain ⟨W, h1, h2⟩ := h
  rw [← h2, hyz, h1]

theorem mem_pW_iff (h : JcPin D p la jc) {y : DV.KW p} {z : D.what₂.LL} (hyz : jc y = D.what₂.embLL z) :
    (∃ a : WittVector p (AlgebraicClosure (ZMod p)),
        y = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
      la.1.valuation D.what₂.LL z < 1 := by
  rw [mem_mul_iff (WittVector.irreducible p) y,
    mem_range_iff h (y := y⁻¹) (z := z⁻¹) (by rw [map_inv₀, map_inv₀, hyz])]
  have h0 : y = 0 ↔ z = 0 := by
    rw [← map_eq_zero_iff jc jc.injective, hyz, map_eq_zero_iff _ D.what₂.embLL.injective]
  rw [h0, map_inv₀, not_le]
  by_cases hz : z = 0
  · simp [hz]
  · have hv : 0 < la.1.valuation D.what₂.LL z := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hz)
    rw [one_lt_inv₀ hv]
    simp [hz]

theorem pinned_reads_place : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) →
    ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p) (τ : DV.Emb D p) (e : D.host.E →+* D.what₂.LL),
      (jC p la).comp τ = D.what₂.embLL.comp e → ∀ x : 𝓞 D.host.E,
        τ x ∈ (algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p)).range ∧
        ((∃ a : WittVector p (AlgebraicClosure (ZMod p)),
            τ x = algebraMap (WittVector p (AlgebraicClosure (ZMod p))) (DV.KW p) (p * a)) ↔
          la.1.valuation D.what₂.LL (e x) < 1) ∧
        (la.1.valuation D.what₂.LL (e x) < 1 ↔ RingOfIntegers.mapRingHom e x ∈ la.1.asIdeal) := by
  intro D jC h p _ la τ e hτ x
  have hx : jC p la (τ x) = D.what₂.embLL (e x) := RingHom.congr_fun hτ (x : D.host.E)
  have he : e x = algebraMap (𝓞 D.what₂.LL) D.what₂.LL (RingOfIntegers.mapRingHom e x) := rfl
  refine ⟨(mem_range_iff (h p la) hx).2 ?_, mem_pW_iff (h p la) hx, ?_⟩
  · rw [he]; exact la.1.valuation_le_one _
  · rw [he]; exact la.1.valuation_lt_one_iff_mem _

theorem coeff_zero_eq_zero_iff {k : Type} [Field k] [CharP k p] [PerfectRing k p] (b : WittVector p k) :
    b.coeff 0 = 0 ↔ ∃ a : WittVector p k, b = p * a := by
  constructor
  · intro h0
    have hb : ¬ IsUnit b := by
      rintro ⟨u, rfl⟩
      have h1 := congrArg (fun w : WittVector p k => w.coeff 0) u.mul_inv
      simp only [WittVector.mul_coeff_zero, WittVector.one_coeff_zero] at h1
      rw [h0, zero_mul] at h1
      exact zero_ne_one h1
    have hm : b ∈ IsLocalRing.maximalIdeal (WittVector p k) := hb
    rw [(WittVector.irreducible p).maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨a, rfl⟩ := hm
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    rw [WittVector.mul_coeff_zero]
    have : ((p : WittVector p k)).coeff 0 = 0 := by simp
    rw [this, zero_mul]

theorem pinned_tiedFor : ∀ (D : D7) (jC : ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)),
    (∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)) → Formalism.L2.Geo.ComplexEmbeddingsCompatible jC := by
  intro D jC h p _ la τ e hτ x
  obtain ⟨-, h2, -⟩ := pinned_reads_place D jC h p la τ e hτ x
  rw [← h2]
  constructor
  · rintro ⟨b, hb, h0⟩
    obtain ⟨a, rfl⟩ := (coeff_zero_eq_zero_iff b).1 h0
    exact ⟨a, hb.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨p * a, ha.symm, (coeff_zero_eq_zero_iff _).2 ⟨a, rfl⟩⟩

end GlobalTheory.ShFam.PinPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem latDR_subset_latHT :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X), latDR t x ⊆ latHT t p x := by
  intro E _ _ _ H X t C _ _ p x v hv
  obtain ⟨xO, hx, vO, htan, hvO⟩ := hv
  have h1 : epsMul (1 : C) = RingHom.id (DualNumber C) := by
    ext a <;> simp [epsMul]
  have h2 : spMap (RingHom.id (DualNumber C)) = 𝟙 _ := by
    simp [spMap]
  refine ⟨xO, hx, 0, vO, htan, ?_, ?_⟩
  · rw [pow_zero, h1, h2, Category.id_comp, hvO]
  · intro n c g _
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top

end GlobalTheory.ShFam.Pad
end

