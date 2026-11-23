module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.AwayLiftCompFromZeroRingHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniversalFullLevelOfPelThetaFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.TripleTheta

open CharZeroPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ} {J : Type}

theorem map_bas {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) (v : Fin (2 * g) → ℤ) :
    u (bas v) = ∏ i, u (bas (Pi.single i 1)) ^ v i := by
  rw [LatticeTorsion.eq_prod_zpow ((Pi.basisFun ℤ (Fin (2 * g))).map bas) u hu]
  simp

theorem map_nsmul' {A : Type} [Group A] (u : D.La → A) (hu : ∀ x y, u (x + y) = u x * u y) (n : ℕ) (x : D.La) :
    u (n • x) = u x ^ n :=
  (MonoidHom.mk' (fun x : Multiplicative D.La => u x.toAdd) fun _ _ => hu _ _).map_pow (Multiplicative.ofAdd x) n

theorem existsUnique_coeff {A : Type} [CommGroup A] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (u : D.La → A)
    (hu : ∀ x y, u (x + y) = u x * u y) {N : ℕ} (hN : 0 < N) (hk : ∀ x, u x = 1 ↔ ∃ y, x = N • y) (x : D.La) :
    ∃! c : Fin (2 * g) → ZMod N, ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u x := by
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨v, rfl⟩ := bas.surjective x
  have key : ∀ c : Fin (2 * g) → ZMod N,
      ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas v) ↔ c = fun i => (v i : ZMod N) := fun c => by
    have e₁ : ∏ i, u (bas (Pi.single i 1)) ^ (c i).val = u (bas fun i => ((c i).val : ℤ)) := by
      rw [map_bas bas u hu]; simp only [zpow_natCast]
    have e₂ := hu (bas (v - fun i => ((c i).val : ℤ))) (bas fun i => ((c i).val : ℤ))
    rw [← map_add (f := _), sub_add_cancel] at e₂
    rw [e₁, e₂, right_eq_mul, hk]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨w, rfl⟩ := bas.surjective y
      rw [← map_nsmul] at hy
      funext i
      have := congrArg (fun z : ℤ => (z : ZMod N)) (congrFun (bas.injective hy) i)
      simp at this
      exact (sub_eq_zero.1 this).symm
    · intro hc
      have : ∀ i, ∃ w : ℤ, v i - ((c i).val : ℤ) = N * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (by simp [hc])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  simp only [key]
  exact existsUnique_eq

theorem coe_rt (n N : ℕ) : ((RZ.rt H n N : RZ H n N) : ℂ) = H.rt0 := by
  show ((2 : RZ H n N) : ℂ) * ((1 + H.rt0) / 2) - 1 = H.rt0
  have : ((2 : RZ H n N) : ℂ) = 2 := map_ofNat (RZ H n N).subtype 2
  rw [this]; ring

theorem rt_sq (n N : ℕ) : RZ.rt H n N ^ 2 = -(H.d : RZ H n N) := by
  apply Subtype.ext
  push_cast
  rw [coe_rt, H.sqrt_neg_disc_sq]

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) (v : Kˣ) (hv : (v : K) = β u) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn v := by
  apply Units.ext
  show x.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) =
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom v
  have e := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  have e' := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  rw [hv]
  exact e'.trans e.symm


set_option maxHeartbeats 800000 in
theorem exists_under (hL : Out.Laws) {n N : ℕ} (hN : 0 < N) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La)
    (hbas : IsSympBasis D bas) (b : TBase (RZ H n N) N) (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} [Flat s] {t : SAB H S} {lv : D.La → (𝟙_ (Over S) ⟶ t.G)} (h : FullObj D s t lv) :
    ∃ T : TObj g N J b s, Under t lv a bas T ∧ IsPEL D a bas (RZ.rt H n N) T t := by
  have hab : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, h.proper, t.semi.geomConnected⟩
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have := bas.finrank_eq
    rw [datum_finrank_int, Module.finrank_fin_fun] at this
    omega
  have hdim : SmoothOfRelativeDimension g t.G.hom := by
    have := t.semi.smooth
    have := t.semi.geomConnected
    refine smoothOfRelativeDimension_of_generization _ g fun y => ?_
    obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization (t.G.hom ≫ s) y
    refine ⟨K, inferInstance, z, hz, fun m hm => ?_⟩
    refine (ObjDim.dim_eq_of_detCond D t.act (z ≫ t.G.hom) ?_
      (h.geom K _ β ((Category.assoc _ _ _).trans hβ)).1 hm).trans hg
    rw [← map_pow, rt_sq, map_neg, map_natCast]
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ t.G) := fun i => toUnit _ ≫ lv (bas (Pi.single i 1))
  have hpt : ∀ i, pt i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← map_nsmul' lv h.add, h.ker, MonObj.comp_one]
  have hptx : ∀ {X : Scheme.{0}} (x : X ⟶ S) (i), toB x ≫ pt i = toUnit _ ≫ lv (bas (Pi.single i 1)) := fun x i => by
    rw [← Category.assoc, toUnit_unique (toB x ≫ toUnit _) (toUnit _)]
  have hu : IsUnit (N : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of (RZ H n N))).inv.hom)
    rwa [map_natCast] at this
  have hζ : b.ζ ^ N = 1 := by
    apply Units.ext
    apply Subtype.val_injective
    exact (b.prim ℂ (RZ H n N).subtype).pow_eq_one
  let P : Out.PolAV S :=
    { A := t.G, isAb := hab, g := g, smoothDim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
      sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv }
  have : IsMonHom (Iso.refl t.G).hom := inferInstanceAs (IsMonHom (𝟙 t.G))
  have hid : LBIso t.PP.L (t.PP.L.pull (Iso.refl t.G).hom.left) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ (𝟙 _) (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl t.PP.isLB)
  have hpl : ∀ i, (lv (bas (Pi.single i 1))).left ≫ (Iso.refl t.G).hom.left = (pt i).left := fun i => by
    have e : (toUnit (Out.baseOver S)).left = 𝟙 S := ObjPull.toUnit_left' _
    rw [Iso.refl_hom, Over.id_left, Category.comp_id, Over.comp_left, e]
    exact (Category.id_comp (X := S) _).symm
  refine ⟨{ A := t.G, ab := hab, dim := hdim, L := t.PP.L, isLB := t.PP.isLB, rigid := ObjDim.rigidified,
            sym := ObjDim.sym, ample := h.ample, ktriv := h.ktriv, pt := pt, torsion := hpt,
            bij := torsion_basis_of_generization t.G N _ pt hab hN hu hpt fun p => ?_,
            pairing := fun i j => weilIs_of_generization hL P N _ _ _ hN hu (hpt i) (hpt j) ?_ fun p => ?_,
            act := fun j => t.act.act (a j), hom := fun j => t.act.hom _ },
    ⟨Iso.refl _, this, hid, fun j => by simp, hpl⟩,
    ⟨Iso.refl _, this, hid, fun j => by simp, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, -, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, inferInstance, z, hz, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := (I.onto N hN y).1 hy
    simp only [hptx, hI, Out.linComb, List.prod_ofFn]
    exact existsUnique_coeff bas (I.ev N) (I.add N) hN (I.ker N hN) x
  · rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, unitS, unitOn, ← map_pow, ← map_pow, hζ, map_one,
      map_one, one_zpow]
  · obtain ⟨K, _, _, _, z, β, hβ, hz⟩ := exists_generization s p
    obtain ⟨-, I, hIζ, hI⟩ := h.geom K z β hβ
    refine ⟨K, inferInstance, z, hz, ?_⟩
    have hc : Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j) =
        unitOn (I.ζ N ^ Out.stdSymp g i j) := by
      rw [map_zpow, map_unitS s z β hβ b.ζ (I.ζ N) (by rw [hIζ, hb]), unitOn, unitOn, map_zpow]
    have e : Out.WeilIs t.G t.PP.L N (toB z ≫ pt i) (toB z ≫ pt j)
        (Units.map z.appTop.hom.toMonoidHom (unitS s b.ζ ^ Out.stdSymp g i j)) := by
      rw [hc, hptx z i, hptx z j, hI, hI, ← hbas i j]
      exact I.isom N hN _ _
    exact e
  · obtain ⟨hd, I, hIζ, hI⟩ := h.geom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], fun i => ?_⟩
    have e : I.ev N (bas (Pi.single i 1)) ≫ 𝟙 t.G = toB x ≫ pt i := by rw [hptx, hI, Category.comp_id]
    exact e

theorem exists_level {n N : ℕ} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La}
    {b : TBase (RZ H n N) N} (hb : (b.ζ : RZ H n N) = RZ.ze H n N) {S : Scheme.{0}}
    {s : S ⟶ Sp (RZ H n N)} {t : SAB H S} {T : TObj g N J b s} (h : IsPEL D a bas (RZ.rt H n N) T t) :
    ∃ lv : D.La → (𝟙_ (Over S) ⟶ t.G), Under t lv a bas T ∧ FullObj D s t lv := by
  obtain ⟨φ, hφ, hφL, hφa, hgeom⟩ := h
  let j : 𝟙_ (Over S) ⟶ Out.baseOver S := Over.homMk (𝟙 S) (Category.id_comp _)
  let q : Fin (2 * g) → (𝟙_ (Over S) ⟶ t.G) := fun i => j ≫ T.pt i ≫ φ.inv
  have hq : ∀ i, q i ^ N = 1 := fun i => by
    rw [← MonObj.comp_pow, ← MonObj.pow_comp, T.torsion, MonObj.one_comp, MonObj.comp_one]
  let lv : D.La → (𝟙_ (Over S) ⟶ t.G) := fun x => ∏ i, q i ^ bas.symm x i
  have hadd : ∀ x y, lv (x + y) = lv x * lv y := fun x y => by
    simp only [lv, map_add (f := _), Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  have hlv : ∀ i, lv (bas (Pi.single i 1)) = q i := fun i => by
    simp only [lv, LinearEquiv.symm_apply_apply]
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp
  obtain ⟨hab, hA, hK⟩ := PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally S S T.A t.G _ _ T.L t.PP.L
    T.isLB t.PP.isLB T.ab (isGrpPullback_of_iso φ) hφL
  refine ⟨lv, ⟨φ, hφ, hφL, hφa, fun i => ?_⟩, hab.proper, hA T.ample, hK T.ktriv, hadd, fun x => ?_,
    fun K _ _ _ x β hx => ?_⟩
  · rw [hlv]
    show (𝟙 S ≫ (T.pt i).left ≫ φ.inv.left) ≫ _ = _
    rw [Category.assoc, Category.assoc, inv_hom_left]
    exact (Category.id_comp _).trans (Category.comp_id _)
  · rw [map_nsmul' lv hadd, ← Finset.prod_pow]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hq, one_zpow]
  · obtain ⟨hd, I, hIζ, hI⟩ := hgeom K x β hx
    refine ⟨hd, I, by rw [hIζ, hb], eq_of_basis bas (fun y => toUnit _ ≫ lv y) (I.ev N)
      (fun y y' => by rw [hadd, MonObj.comp_mul]) (I.add N) fun i => ?_⟩
    have e : toUnit (Over.mk x) ≫ j = toB x := Over.OverMorphism.ext
      ((Category.comp_id _).trans (ObjPull.toUnit_left' _))
    rw [hlv, ← Category.assoc, e, ← Category.assoc, Iso.comp_inv_eq]
    exact (hI i).symm

theorem arBase_RZ (H : Host E) {n N e : ℕ} (hn : 0 < n) (hN : 0 < N) (h : N ∣ n ^ e) : ArBase (RZ H n N).subtype := by
  obtain ⟨l⟩ : Nonempty (Level H) := HostModel.instNonemptyLevel H
  exact ⟨BaseRing.isDedekindDomain_RZ { l with A := N, A_pos := hN } hn h, BaseRing.finiteType_RZ H n N,
    Subtype.val_injective⟩

end GlobalTheory.TripleTheta

namespace GlobalTheory


open TripleTheta CharZeroPts in
theorem exists_famCore_of_thetaFam : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (n N' : ℕ) (g : ℕ) (J : Type) [Finite J] (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (b : TBase (RZ H n (N' ^ 2)) (N' ^ 2)) (F : ThetaFam n (RZ H n (N' ^ 2)).subtype (PELClass (b := b) D a bas (RZ.rt H n (N' ^ 2)) (RZ H n (N' ^ 2)).subtype)) (τ : SAB H F.MM), IsSympBasis D bas → Subring.closure (Set.range a) = ⊤ → (∃ w w', a w = H.w0 ∧ a w' = H.bar H.w0) → (b.ζ : RZ H n (N' ^ 2)) = RZ.ze H n (N' ^ 2) → IsPEL D a bas (RZ.rt H n (N' ^ 2)) F.univ τ → SmoothOfRelativeDimension D.dim (pullback.snd F.s (spMap (algebraMap (RZ H n (N' ^ 2)) (FractionRing (RZ H n (N' ^ 2)))))) → 1 ≤ D.p + D.q → n.Prime → Odd n → (∃ j, 1 ≤ j ∧ N' = n ^ j) → ∃ lev : D.La → (𝟙_ (Over F.MM) ⟶ τ.G), FamCore D F.s τ lev := by
  intro hL hL2 E _ _ _ H D n N' g J _ a bas b F τ hbas ha ⟨w, w', hw, hw'⟩ hb hP hsm hpq hn _ ⟨j, _, hj⟩
  have hN : 0 < N' ^ 2 := by rw [hj]; exact pow_pos (pow_pos hn.pos _) _
  have hbase : ArBase (RZ H n (N' ^ 2)).subtype := arBase_RZ H (e := j * 2) hn.pos hN (by rw [hj, pow_mul])
  obtain ⟨lev, hU, hF⟩ := exists_level hb hP
  refine ⟨lev, F.reduced, F.flat, F.qproj, SmoothOfRelativeDimension.smooth D.dim _, hF,
    fun S s t lv hS _ hs ho => ?_, fun k _ x t lv ν ν' hx hν hν' => ?_⟩
  · obtain ⟨T, hT, hTP⟩ := exists_under hL hN a bas hbas b hb ho
    obtain ⟨f, ⟨hf, hm⟩, huniq⟩ := F.rep S s T hS fun p => by
      obtain ⟨K, _, _, _, z, β, -, hz⟩ := exists_generization s p
      exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure (subset_closure ⟨K, inferInstance, z, ⟨_, rfl⟩,
        PELFrom.fromC_of_isPEL hL hL2 E H D g J a w w' bas hpq hbas hw hw' ha N' _ b _ _ (coe_rt n _) hbase S s T t hTP K z⟩)
    exact ⟨f, ⟨hf, sabMap_of_tmap hU hT hF.add ho.add ha hS ho.proper hm⟩,
      fun f' ⟨hf', ν, hν⟩ => huniq f' ⟨hf', tmap_of_sabMap hU hT ν hν⟩⟩
  · obtain ⟨T, hT⟩ := tObj_pull _ g _ J b _ _ F.s (x ≫ F.s) x F.univ rfl
    exact F.unram k x T hx hT (tmap_of_sabMap hU (under_of_tmap hU hT ν hν) ν' hν')

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGenSecIffFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.GenSecFibre

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.VVRank GlobalTheory.EmbPull TopologicalSpace

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem mem_nonzeroLocus_pullS (a : ℤ) (h : T' ⟶ T) (th : LB.Sec (LPow P.A P.L a T)) (z : (T' ⊗ P.A).left) :
    z ∈ nonzeroLocus (pullS P.A a h th) ↔ (h ▷ P.A).left z ∈ nonzeroLocus th := by
  have e : ∀ j, z ∈ (LPow P.A P.L a T').U j → (IsUnit (gs (𝟙 _) z _ ((pullS P.A a h th).f j)) ↔
      IsUnit (gs (𝟙 _) ((h ▷ P.A).left z) _ (th.f j))) := fun j hj => by
    have q := gs_pullTo (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => a) th (h ▷ P.A).left
      (fun _ => whisker_snd_left P.A h) (𝟙 _) z j hj
    rw [Category.id_comp] at q
    have q' := q.trans (gs_stalkMap (h ▷ P.A).left z _ (wchart_le_of_eq _ (fun _ => whisker_snd_left P.A h) j hj) _)
    exact (iff_of_eq (congrArg IsUnit q')).trans (isUnit_map_iff _ _)
  rw [mem_nonzeroLocus, mem_nonzeroLocus]
  refine exists_congr fun j => ⟨fun ⟨hj, u⟩ => ⟨?_, (e j hj).1 u⟩, fun ⟨hj, u⟩ => ?_⟩
  · exact wchart_le_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) j hj
  · have hj' := mem_wchart_of_eq (φ := fun _ : Fin 1 => (snd T P.A).left) _ (fun _ => whisker_snd_left P.A h) z j hj
    exact ⟨hj', (e j hj').2 u⟩

theorem exists_mem_nonzeroLocus (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : IsGenSec P.A P.L 1 th) (p : T.left) :
    ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th := by
  let w : Spec (CommRingCat.of (T.left.residueField p)) ⟶ T.left := T.left.fromSpecResidueField p
  let h : Over.mk (w ≫ T.hom) ⟶ T := Over.homMk w rfl
  have : IsAffine (Over.mk (w ≫ T.hom)).left := inferInstanceAs (IsAffine (Spec _))
  have h₀ := ThetaCoset.ne_zero_of_isGenSec hS P (w ≫ T.hom) (isGenSec_pullS P hS h H)
  have := P.isAb.smooth
  have : Smooth (fst (Over.mk (w ≫ T.hom)) P.A).left :=
    inferInstanceAs (Smooth (pullback.fst (w ≫ T.hom) P.A.hom))
  have : IsReduced (Over.mk (w ≫ T.hom) ⊗ P.A).left :=
    isReduced_scheme_of_smooth_of_isIntegrallyClosed (T.left.residueField p) (fst (Over.mk (w ≫ T.hom)) P.A).left
  obtain ⟨z, hz⟩ : ∃ z, z ∈ nonzeroLocus (pullS P.A 1 h th) := by
    by_contra hn
    refine h₀ (Subtype.ext (funext fun j => ?_))
    exact eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z hz => hn ⟨z, Opens.mem_iSup.2 ⟨j, hz⟩⟩)
  refine ⟨(h ▷ P.A).left z, ?_, (mem_nonzeroLocus_pullS P 1 h th z).1 hz⟩
  rw [← Scheme.Hom.comp_apply, (isPullback_whisker P.A h).w, Scheme.Hom.comp_apply]
  exact (T.left.range_fromSpecResidueField p).le ⟨_, rfl⟩

theorem map_sub_eq_zero' {R R' M M' : Type} [CommRing R] [CommRing R'] [AddCommGroup M] [AddCommGroup M'] [Module R M]
    [Module R' M'] (σ : R →+* R') (φ : M →ₛₗ[σ] M') (s t : M) (b : M') (a c d₀ e₀ : R) (d e : R')
    (ht : φ t = d • b) (hs : φ s = e • b) (hd : σ d₀ = σ a * d) (he : σ e₀ = σ c * e) :
    φ ((d₀ * c) • s - (e₀ * a) • t) = 0 := by
  rw [map_sub, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, map_mul, map_mul, ht, hs, hd, he, smul_smul, smul_smul,
    sub_eq_zero]
  congr 1
  ring

theorem isGenSec_of_fibres (hS : SecBaseChangeAnySt) [IsAffine T.left] {th : LB.Sec (LPow P.A P.L 1 T)}
    (H : ∀ p : T.left, ∃ q : (T ⊗ P.A).left, (fst T P.A).left q = p ∧ q ∈ nonzeroLocus th) :
    IsGenSec P.A P.L 1 th := by
  intro s
  let I : Ideal Γ(T.left, ⊤) := (Submodule.span Γ(T.left, ⊤)
    {SecM.ofSec P.A th}).comap (LinearMap.toSpanSingleton _ _ (SecM.ofSec P.A s))
  have key : ∀ p : T.left, ∃ f ∈ I, p ∈ T.left.basicOpen f := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨f, hf, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen f
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hf y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
    have : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    have rep : ∀ x : SecM P.A P.L 1 (overRes W), ∃ d : Γ((overRes W).left, ⊤), x = d • (c hq.default :) := fun x => by
      have := c.sum_repr x
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    obtain ⟨d, hd⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A th))
    obtain ⟨e, he⟩ := rep (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A s))
    obtain ⟨m, d₀, hd₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * d := exists_pow_mul_extend f d
    obtain ⟨n, e₀, he₀⟩ : ∃ (m : ℕ) (d₀ : Γ(T.left, ⊤)), (overResι W).left.appTop.hom d₀ =
        (overResι W).left.appTop.hom (f ^ m) * e := exists_pow_mul_extend f e
    obtain ⟨N, hN⟩ := exists_pow_kill_secM P 1 f ((d₀ * f ^ n) • SecM.ofSec P.A s - (e₀ * f ^ m) • SecM.ofSec P.A th)
      (map_sub_eq_zero' _ _ _ _ _ _ _ _ _ d e hd he hd₀ he₀)
    have hu : p ∈ T.left.basicOpen d₀ := by
      obtain ⟨q, hqp, hq0⟩ := H p
      obtain ⟨z, hz, hz'⟩ := Scheme.exists_preimage_of_isPullback (isPullback_whisker P.A (overResι W)) q
        ⟨p, hp⟩ hqp
      subst hz
      obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 ((mem_nonzeroLocus_pullS P 1 (overResι W) th z).2 hq0)
      have k := (congrArg (fun x => gs (𝟙 _) z _ (x.1 j)) hd).trans (PushInv.gs_smul P.A P.L _ 1 d _ j z hj)
      have u₁ : IsUnit (gs (fst (overRes W) P.A).left z ⊤ d) := isUnit_of_mul_isUnit_left (k ▸ u)
      rw [gs_stalkMap _ z ⊤ trivial, isUnit_map_iff, gs_eq _ _ ⊤ trivial] at u₁
      have u₂ : (fst (overRes W) P.A).left z ∈ (overRes W).left.basicOpen d := (Scheme.mem_basicOpen_top _ _ _).2 u₁
      have u₃ : (⟨p, hp⟩ : (overRes W).left) ∈ (overResι W).left ⁻¹ᵁ T.left.basicOpen d₀ := by
        rw [Scheme.preimage_basicOpen_top, hd₀, Scheme.basicOpen_mul, ← Scheme.preimage_basicOpen_top]
        refine ⟨?_, hz' ▸ u₂⟩
        change p ∈ T.left.basicOpen (f ^ m)
        rw [Scheme.mem_basicOpen_top] at hp ⊢
        rw [map_pow]
        exact hp.pow _
      exact u₃
    refine ⟨f ^ N * (d₀ * f ^ n), Submodule.mem_span_singleton.2 ⟨f ^ N * (e₀ * f ^ m), ?_⟩, ?_⟩
    · rw [smul_sub, sub_eq_zero, ← mul_smul, ← mul_smul] at hN
      exact hN.symm
    · rw [Scheme.mem_basicOpen_top] at hp hu ⊢
      simp only [map_mul, map_pow]
      exact (hp.pow _).mul (hu.mul (hp.pow _))
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨f, hf, hp⟩ := key p
      exact Opens.mem_iSup.2 ⟨⟨f, hf⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hI
  rw [LinearMap.toSpanSingleton_apply, one_smul] at hr
  exact ⟨r, fun j => (congrArg (fun q => q.1 j) hr).symm⟩

theorem isGenSec_iff_fibres : Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (R : Type) [CommRing R] (y : Sp R ⟶ S) (th : LB.Sec (Out.LPow P.A P.L 1 (Over.mk y))), Out.IsGenSec P.A P.L 1 th ↔ ∀ p : Sp R, ∃ q : (Over.mk y ⊗ P.A).left, (fst (Over.mk y) P.A).left q = p ∧ q ∈ Out.nonzeroLocus th := by
  intro h S P R _ y th
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Spec _))
  exact ⟨exists_mem_nonzeroLocus P h.secBaseChangeAny,
    isGenSec_of_fibres P (T := Over.mk y) h.secBaseChangeAny⟩

end GlobalTheory.GenSecFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivNearGoodPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild

private theorem isGrpPullback_pullback_fst {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) :
    IsGrpPullback ((Over.pullback f).obj G) G f (pullback.fst G.hom f) := by
  refine ⟨IsPullback.of_hasPullback G.hom f, ?_⟩
  intro T x y x₀ y₀ hx hy
  have h := GlobalTheory.UU.toBase_mul_pullback G f T x y
  have ex : x₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition x := by
    ext
    simp [hx, Out.toBase]
  have ey : y₀ = Out.toBase (A := G) (A' := (Over.pullback f).obj G) (g := pullback.fst G.hom f) pullback.condition y := by
    ext
    simp [hy, Out.toBase]
  rw [ex, ey, ← h]
  simp [Out.toBase]

theorem kTriv_near_good_prime : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), q₀ ∈ objPrimes b Mat κ β v → PolFam b Mat κ β v A L act Q → ∃ f : R, f ∉ q₀ ∧ Out.KTriv ((Over.pullback (spMap (loc f))).obj A) (L.pull (pullback.fst A.hom (spMap (loc f)))) := by
  intro o _ g N' J b Mat κ R _ _ β v A _ L act Q q₀ hq hP
  obtain ⟨K, _, _, x, s, t, hker, hgood⟩ := mem_objPrimes.1 hq
  obtain ⟨hab, -, hLB, -, -, hamp, -, hfib⟩ := hP
  obtain ⟨ψ, hψ, hiso⟩ := hfib K x s t hgood
  obtain ⟨e, he, hcomp⟩ := grpPullback_iso (isGrpPullback_pullback_fst A (spMap x)) hψ.1
  haveI := he
  have hLB' : (L.pull (pullback.fst A.hom (spMap x))).IsLB := pull_isLB hLB _
  have hLt : (t.L.pull e.hom.left).IsLB := pull_isLB t.isLB _
  have hψL : (L.pull ψ).IsLB := pull_isLB hLB ψ
  have hcls : LBIso (L.pull (pullback.fst A.hom (spMap x))) (t.L.pull e.hom.left) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff hLB' hLt, GlobalTheory.CechPic.cls_pull hLB _ hLB', GlobalTheory.CechPic.cls_pull t.isLB _ hLt,
      ← hcomp, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hLB ψ hψL,
      ← (GlobalTheory.CechPic.cls_eq_iff t.isLB hψL).2 hiso]
  have hfibK := (amplePt (Sp K) K (𝟙 _) t.A _ e.hom.left (isGrpPullback_of_iso e) t.L _ t.isLB hLB' hcls
    t.ample t.ktriv).2
  obtain ⟨f, hf, hk⟩ := kTriv_away_of_kTriv_fibre globalFns_holds R A L K x hab hLB hamp hfibK
  refine ⟨f, fun h => hf ?_, hk⟩
  rw [← hker, RingHom.mem_ker] at h
  exact h

end GlobalTheory.ZM.NearBuild
end

