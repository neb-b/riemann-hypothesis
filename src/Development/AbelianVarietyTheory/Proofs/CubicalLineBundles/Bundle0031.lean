module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSymplecticCoordinatesOfIsPeriod
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsProdPolAV
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.PolProd

open GlobalTheory.CechPic GlobalTheory.TripleProd

variable {S : Scheme.{0}}

theorem locZero_add {Y B : Scheme.{0}} {π : Y ⟶ B} {c d : Pic Y} (H : LocZero π c) (H' : LocZero π d) :
    LocZero π (c + d) := by
  have h := H.sub ((locZero_base π 0).sub H')
  rwa [map_zero, zero_sub, sub_neg_eq_add] at h

theorem rigidified_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Rigidified A L ↔ pull (eSec A) (cls L hL) = 0 := by
  exact (cls_eq_zero_iff (pull_isLB hL _)).symm

theorem sym_iff (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) :
    Out.Sym A L ↔ LocZero A.hom (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
  refine forall_congr' fun _ => exists_congr fun U => and_congr_right fun _ => ?_
  refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).symm.trans ?_
  have e : cls (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]) (LB.isLB_linComb hL _ _) =
      pull (A.hom ⁻¹ᵁ U).ι (pull (GrpObj.inv : A ⟶ A).left (cls L hL) - cls L hL) := by
    refine (cls_linComb hL _ _ _).trans ?_
    rw [Fin.sum_univ_two]
    show (1 : ℤ) • pull ((A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left) (cls L hL) +
      (-1 : ℤ) • pull (A.hom ⁻¹ᵁ U).ι (cls L hL) = _
    rw [one_zsmul, neg_one_zsmul, map_sub, sub_eq_add_neg, pull_comp]
  rw [e]

theorem eSec_comp {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    eSec A ≫ f.left = eSec G := by
  have h : η[A] ≫ f = η[G] := IsMonHom.one_hom f
  exact congrArg (fun z => z.left) h

theorem inv_comp_left {A G : Over S} [GrpObj A] [GrpObj G] (f : A ⟶ G) [IsMonHom f] :
    (GrpObj.inv : A ⟶ A).left ≫ f.left = f.left ≫ (GrpObj.inv : G ⟶ G).left := by
  have h : (GrpObj.inv : A ⟶ A) ≫ f = f ≫ GrpObj.inv := GrpObj.inv_hom f
  exact congrArg (fun z => z.left) h

theorem exists_prod_polAV : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P P' : Out.PolAV (Sp R)), ∃ (Q : Out.PolAV (Sp R)) (p : Q.A ⟶ P.A) (q : Q.A ⟶ P'.A), IsMonHom p ∧ IsMonHom q ∧ IsIso (lift p q) ∧ Q.g = P.g + P'.g := by
  intro _ R _ _ P P'
  have hB : IsAbelianScheme (P.A ⊗ P'.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ P.isAb P'.isAb
  let p := fst P.A P'.A
  let q := snd P.A P'.A
  obtain ⟨M, hM, eM⟩ := cls_surj (pull p.left (cls P.L P.isLB) + pull q.left (cls P'.L P'.isLB))
  have hd := LB.isLB_div hM (pull_isLB P.isLB p.left)
  have last : LBIso (M.div (P.L.pull p.left)) (P'.L.pull q.left) := by
    refine (cls_eq_iff hd (pull_isLB P'.isLB _)).1 ?_
    rw [cls_div hM (pull_isLB P.isLB p.left), eM, cls_pull P.isLB, cls_pull P'.isLB, add_sub_cancel_left]
  haveI := P.isAb.proper
  haveI := P'.isAb.proper
  haveI := hB.proper
  have hdim : SmoothOfRelativeDimension (P.g + P'.g) (P.A ⊗ P'.A).hom := by
    haveI := P.smoothDim
    haveI : SmoothOfRelativeDimension P'.g (pullback.fst P.A.hom P'.A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip P'.smoothDim
    rw [add_comm]
    exact inferInstanceAs (SmoothOfRelativeDimension (P'.g + P.g) (pullback.fst P.A.hom P'.A.hom ≫ P.A.hom))
  have hrig : Out.Rigidified (P.A ⊗ P'.A) M := by
    rw [rigidified_iff _ hM, eM, map_add (f := _), ← pull_comp, ← pull_comp, eSec_comp p, eSec_comp q,
      (rigidified_iff _ P.isLB).1 P.rigid, (rigidified_iff _ P'.isLB).1 P'.rigid, add_zero]
  have hsym : Out.Sym (P.A ⊗ P'.A) M := by
    have h₁ := ((sym_iff _ P.isLB).1 P.sym).pull_over (π' := (P.A ⊗ P'.A).hom) p.left (Over.w p)
    have h₂ := ((sym_iff _ P'.isLB).1 P'.sym).pull_over (π' := (P.A ⊗ P'.A).hom) q.left (Over.w q)
    rw [sym_iff _ hM, eM]
    convert locZero_add h₁ h₂ using 1
    rw [map_add (f := _), map_sub, map_sub, ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp, inv_comp_left p,
      inv_comp_left q]
    abel
  have hamp : Out.RelAmple (P.A ⊗ P'.A) M :=
    (relAmple_iff_isAmpleLB_of_isAffine _ hM).2 (IsAmpleLB.box
      ((relAmple_iff_isAmpleLB_of_isAffine _ P.isLB).1 P.ample) ((relAmple_iff_isAmpleLB_of_isAffine _ P'.isLB).1 P'.ample)
      hM (p := p.left) (q := q.left) (f := P.A.hom) (g := P'.A.hom) (IsPullback.of_hasPullback _ _) last.symm)
  refine ⟨⟨P.A ⊗ P'.A, hB, P.g + P'.g, hdim, M, hM, hrig, hsym, hamp,
    kTriv_prod hM P.isLB P'.isLB eM P.ktriv P'.ktriv⟩, p, q, inferInstance, inferInstance, ?_, rfl⟩
  show IsIso (lift (fst P.A P'.A) (snd P.A P'.A))
  rw [lift_fst_snd]
  infer_instance

end GlobalTheory.PolProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPureVectorsPeriodsSpan
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem span_pure_periods_eq_top {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe) {p q : ℕ} (Z : CMLat hP p q) :
    Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v} = ⊤ := by
  set W := Submodule.span ℂ {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  obtain ⟨n, hn, h⟩ := Z.span
  have key : ∀ a, Pe a ∈ W := by
    intro a
    obtain ⟨x, hx⟩ := h a
    have h1 : (n : ℂ) • Pe a ∈ W := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hx, map_sum]
      refine W.sum_mem fun j _ => Submodule.subset_span ?_
      have h2 := Z.pure j (x j)
      rcases j with j | j
      · exact ⟨1, ⟨_, by simpa using h2⟩, rfl⟩
      · exact ⟨-1, ⟨_, by simpa using h2⟩, rfl⟩
    exact (W.smul_mem_iff (Nat.cast_ne_zero.2 hn.ne')).1 h1
  have h3 : Submodule.span ℝ (Set.range Pe) ≤ W.restrictScalars ℝ :=
    Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact key a)
  rw [hP.2.2.2.1] at h3
  exact eq_top_iff.2 fun v _ => h3 Submodule.mem_top

theorem exists_pure_vectors_periods_span :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pe : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty Pe) (p q : ℕ) (Z : CMLat hP p q), ∃ (ε : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℤˣ) (a : ∀ i, PureType.lat hP (((ε i : ℤ) : ℂ) * H.rt0)), ∀ z : Fin g → ℂ, ∃ c : Fin (Module.finrank ℚ E / 2 * (D.p + D.q)) → ℂ, z = ∑ i, c i • Pe (a i) := by
  intro E _ _ _ H D g ty Pe hP p q Z
  have h1 := (FibreExp.free_finite_finrank_of_isPeriod hP).2.2
  rw [datum_finrank_int D] at h1
  have hs := span_pure_periods_eq_top hP Z
  have h2 := Submodule.exists_fun_fin_finrank_span_eq ℂ
    {v : Fin g → ℂ | ∃ (ε : ℤˣ) (a : PureType.lat hP (((ε : ℤ) : ℂ) * H.rt0)), Pe a = v}
  rw [hs, finrank_top, Module.finrank_fin_fun] at h2
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by omega
  rw [hg]
  obtain ⟨f, hf, hsp, -⟩ := h2
  choose ε a ha using hf
  refine ⟨ε, a, fun z => ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hsp ▸ Submodule.mem_top (x := z))
  exact ⟨c, by simp [ha, hc]⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSecGeneric
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.ThetaDegree

def IsPullOf {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (t : LB.Gen (P.L.pull (eSec P.A))) (θ : P.L.Sec) (y : KeyIn R) : Prop :=
  ∃ (ψ : y.P.A.left ⟶ P.A.left) (w : LB.Iso y.P.L (P.L.pull ψ)), y.P.g = P.g ∧ IsGrpPullback y.P.A P.A (spMap f) ψ ∧
    PGen w ∧ PMaps w (K := PUnit) (fun _ => eSec y.P.A) (fun _ => eSec P.A) (fun _ => 1) y.rig t (spMap f) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ y.P.A.left) (z : Z) j k, ψ (r z) ∈ P.L.U j → r z ∈ y.P.L.U k →
      gs (r ≫ ψ) z _ (θ.f j) = (gw w r z j k).val * gs r z _ (y.th.f k)

theorem exists_isPullOf {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (f : O →+* R) (P : Out.PolAV (Sp O))
    (hg : 1 ≤ P.g) {t : LB.Gen (P.L.pull (eSec P.A))} (ht : t.IsGen) (θ : P.L.Sec)
    (hθ : ∀ s : Sp R, ∃ z, P.A.hom z = spMap f s ∧ z ∈ Out.nonzeroLocus θ) : ∃ y : KeyIn R, IsPullOf f P t θ y := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := pull_isLB P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R) :=
    { A := (Over.pullback (spMap f)).obj P.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
      g := P.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
      L := P.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h P.rigid
      sym := PolBaseChange.sym_pull h P.sym
      ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
      ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }
  have he : eSec P'.A ≫ φ = spMap f ≫ eSec P.A := PolBaseChange.eSec_comm h
  have hr : (rigPullOf φ (spMap f) he P.L t).IsGen :=
    Out.LBxP.isGen_pullAlong P.L φ (spMap f) (fun _ : PUnit => eSec P.A) (fun _ => 1) (fun _ => eSec P'.A)
      (fun _ => he) t ht
  obtain ⟨th', hth'⟩ := sec_pull_down hw P.isLB hL' θ
  obtain ⟨v, hv⟩ := KeyPow.exists_isLieBasis P'.A P'.smoothDim
  refine ⟨⟨P', hg, _, hr, th', fun s => ?_, v, hv⟩, φ, idIso _, rfl, h, hw,
    (maps_iff (idIso _) (fun _ => eSec P'.A) (fun _ => eSec P.A) _ _ t (spMap f) _ (rigPull_le φ (spMap f) he P.L)
      (fun _ => rfl)).1 (fun p => hr p.1 p.2), hth'⟩
  obtain ⟨z, hz, hz'⟩ := hθ s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (θ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem IsPullOf.exists_keyPB {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [CommRing R'] {f : O →+* R}
    {g : R →+* R'} {P : Out.PolAV (Sp O)} {t : LB.Gen (P.L.pull (eSec P.A))} {θ : P.L.Sec} {y : KeyIn R} {x : KeyIn R'}
    (hy : IsPullOf f P t θ y) (hx : IsPullOf (g.comp f) P t θ x) :
    ∃ v' hv', KeyPB ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v', hv'⟩ y g := by
  obtain ⟨ψ, w, hg, hc, hw, hr, hs⟩ := hy
  obtain ⟨φ'', w'', hg'', hc'', hw'', hr'', hs''⟩ := hx
  have hsp : spMap (g.comp f) = spMap g ≫ spMap f := (spMap_comp_spMap f g).symm
  obtain ⟨φ, rfl, hw0⟩ : ∃ φ : x.P.A.left ⟶ y.P.A.left, φ ≫ ψ = φ'' ∧ φ ≫ y.P.A.hom = x.P.A.hom ≫ spMap g :=
    ⟨hc.1.lift φ'' (x.P.A.hom ≫ spMap g) (by rw [hc''.1.w, Category.assoc, hsp]), hc.1.lift_fst _ _ _,
      hc.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap g) φ := hc.cancel (hc''.congr hsp rfl) hw0
  have he : eSec x.P.A ≫ φ = spMap g ≫ eSec y.P.A := PolBaseChange.eSec_comm h
  obtain ⟨w', T⟩ := exists_cancel P.isLB w w'' hw hw'' y.P.isLB x.P.isLB
  rw [hsp] at hr''
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq : ∀ i, (spMap (Chart.dualMapR g) ≫ (y.v i).left) ≫ y.P.A.hom = (epsR R').hom ≫ spMap g := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR R' ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR g) ≫ (y.v i).left := fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange g h y.basis hv'
  have hg' : x.P.g = y.P.g := hg''.trans hg.symm
  refine ⟨_, hb hg', φ, he, w', hg', Chart.dualMapR g, h, (isGen_iff _).2 (T.pgen_cancel P.isLB hw hw''),
    (maps_iff w' _ (fun _ => eSec y.P.A) _ x.rig y.rig _ _ (rigPull_le φ _ he y.P.L) (fun _ => rfl)).2
      (T.pmaps_cancel P.isLB (fun _ => he) hr hr''),
    KeyPow.appLE_eq_of_stalk _ y.th x.th fun z i k hi hk => ?_, fun a => ?_, ?_, fun i => hv' _⟩
  · obtain ⟨j, hj⟩ := exists_chart P.isLB (ψ (φ z))
    have a := hs _ (𝟙 _ ≫ φ) z j i hj hi
    have b := hs'' _ (𝟙 _) z j k hj hk
    rw [T _ (𝟙 _) z j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

theorem exists_sec_generic (hT : Out.SecTwistSt) {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] (P : Out.PolAV (Sp O)) {X : Scheme.{0}} {φ : X ⟶ P.A.left} {q : X ⟶ Sp K}
    (hp : IsPullback φ q P.A.hom (spMap (algebraMap O K))) : ∃ (θ : P.L.Sec) (z : X), φ z ∈ Out.nonzeroLocus θ := by
  have := P.isAb.smooth
  have := P.isAb.proper
  obtain ⟨s, hs⟩ := KeyPow.exists_sec_fibre_ne_zero hT P hp
  obtain ⟨d, hd, θ, hθ⟩ := SecSpread.exists_spread hp P.isLB s
  obtain ⟨z, -, hz⟩ := hs (default : PrimeSpectrum K)
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz
  have hk' : φ z ∈ P.L.U (k PUnit.unit) := mem_pull.1 hk
  have hu : IsUnit (gs φ z _ (θ.f (k PUnit.unit))) := by
    rw [hθ _ z hk']
    exact (SecSpread.isUnit_cst hp.w z hd).mul u
  rw [gs_stalkMap φ z _ hk', isUnit_map_iff] at hu
  exact ⟨θ, z, (mem_nonzeroLocus _ _).2 ⟨_, hk', hu⟩⟩

variable {K : Type} [Field K] [NumberField K]

theorem exists_scalar (hT : Out.SecTwistSt) (P : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ P.A.left)
    (w : LB.Iso x.P.L (P.L.pull φ)) (hg : x.P.g = P.g)
    (hφ : IsGrpPullback x.P.A P.A (spMap (algebraMap (𝓞 K) K)) φ) (hw : w.IsGen) :
    ∃ a : K, a ≠ 0 ∧ {𝔭 | ¬ ∃ M, KeyPow.IsLocalModel x 𝔭 a M}.Finite := by
  have := P.isAb.smooth
  obtain ⟨θ, z₀, hz₀⟩ := exists_sec_generic hT P hφ.1
  obtain ⟨t, ht⟩ := P.rigid
  obtain ⟨w', g', m'⟩ := KeyPow.exists_rescale P.isLB x.P.isLB ((isGen_iff _).1 hw) (p := x.P.A.hom) (Over.w η[x.P.A])
    (PolBaseChange.eSec_comm hφ) x.rig_gen ht
  obtain ⟨th', hth'⟩ := sec_pull_down g' P.isLB x.P.isLB θ
  have hne : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ Out.nonzeroLocus th' := fun s => by
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz₀
    obtain ⟨k, hk⟩ := exists_chart x.P.isLB z₀
    refine ⟨z₀, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ z₀ _ (θ.f j)) := by rw [gs_stalkMap φ z₀ _ hj]; exact u.map _
    have e := hth' _ (𝟙 _) z₀ j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  let x' : KeyIn K := ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', hne, x.v, x.basis⟩
  have hx' : IsPullOf (algebraMap (𝓞 K) K) P t θ x' := ⟨φ, w', hg, hφ, g', m', hth'⟩
  obtain ⟨a, -, ha, -⟩ := KeyPow.exists_scalar_matrix hT x.P x.th th' x.th_ne x.basis x.basis
  obtain ⟨_, ⟨d, rfl⟩, hd, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (Set.mem_image_of_mem P.A.hom hz₀) (P.A.hom.isOpenMap _ (Out.nonzeroLocus θ).isOpen)
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hd (Ideal.zero_mem _)
  refine ⟨a, ?_, (Ideal.finite_factors (I := Ideal.span {d}) (by simpa using hd0)).subset fun 𝔭 h𝔭 => ?_⟩
  · rintro rfl
    obtain ⟨z, -, hz⟩ := hne (default : PrimeSpectrum K)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    rw [ha i, constFn, map_zero, map_zero, zero_mul, Scheme.basicOpen_zero] at hi
    exact hi
  by_contra hn
  refine h𝔭 ?_
  have hv : 𝔭.valuation K (algebraMap (𝓞 K) K d) = 1 := by
    refine (𝔭.valuation_le_one d).antisymm (not_lt.1 fun h => hn ?_)
    exact (𝔭.valuation_lt_one_iff_dvd d).1 h
  let R := (𝔭.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => 𝔭.valuation_le_one r
  have hu : IsUnit (f d) := (Valuation.integer.integers (𝔭.valuation K)).isUnit_iff_valuation_eq_one.2 hv
  obtain ⟨y, hy⟩ := exists_isPullOf f P (hg ▸ x.g_pos) ht θ fun s => by
    have hs : spMap f s ∈ (PrimeSpectrum.basicOpen d : Set (PrimeSpectrum (𝓞 K))) := fun h =>
      s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ (show f d ∈ s.asIdeal from h) hu)
    obtain ⟨z, h₁, h₂⟩ := hsub hs
    exact ⟨z, h₂, h₁⟩
  obtain ⟨v', hv', hPB⟩ := hy.exists_keyPB (g := algebraMap R K) (x := x') hx'
  choose M hM using fun i => (x.basis.2 _ (hv'.1 i)).exists
  exact ⟨M, R, _, inferInstance, inferInstance, _,
    inferInstanceAs (IsFractionRing (𝔭.valuation K).valuationSubring K), y, th', hne, v', hv', fun r => r.2, ha, hM, hPB⟩

theorem exists_isThetaDeg : Out.SecTwistSt → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K]
    (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth), ∃ δ : ℝ, IsThetaDeg (F.key hg rig hr th hth) δ := by
  intro hT hU K _ _ P F hg rig hr th hth
  classical
  obtain ⟨e, hφ, hL⟩ := F.fib
  obtain ⟨w, hw⟩ := LBIso.symm hL
  let x := F.key hg rig hr th hth
  obtain ⟨oa, od, hloc⟩ := KeyPow.exists_isLocalModel_of_integral hT K P x F.φ w e hφ hw
  obtain ⟨a, ha, hfin⟩ := exists_scalar hT P x F.φ w e hφ hw
  obtain ⟨nth, nη, hn⟩ := KeyPow.exists_archNorms hU x
  have hv : ∀ 𝔭 : HeightOneSpectrum (𝓞 K), 𝔭.valuation K a = WithZero.exp (- -WithZero.log (𝔭.valuation K a)) :=
    fun 𝔭 => by rw [neg_neg, WithZero.exp_log (by simpa using ha)]
  refine ⟨_, fun 𝔭 => if ∃ M, KeyPow.IsLocalModel x 𝔭 a M then -WithZero.log (𝔭.valuation K a) else oa 𝔭, nth,
    fun 𝔭 => ?_, fun σ => ?_, (hfin.union (KeyPow.sum_log_norm_eq_finsum ha _ hv).1).subset fun 𝔭 h => ?_, rfl⟩
  · by_cases h : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · obtain ⟨M, hM⟩ := id h
      exact ⟨a, M, hM, by beta_reduce; rw [if_pos h]; exact hv 𝔭⟩
    · obtain ⟨a', M, hM, h₁, -⟩ := hloc 𝔭
      exact ⟨a', M, hM, by beta_reduce; rw [if_neg h]; exact h₁⟩
  · obtain ⟨x', h₁, h₂⟩ := hn σ
    exact ⟨x', _, h₁, h₂⟩
  · by_cases h' : ∃ M, KeyPow.IsLocalModel x 𝔭 a M
    · exact Or.inr (by simpa only [Function.mem_support, if_pos h'] using h)
    · exact Or.inl h'

end GlobalTheory.ThetaDegree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTateIsoZetaEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.TateRoot

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
private lemma isCoprime_add_sub_mul_pow_factorial {j N : ℤ} (hj : IsCoprime j N) {n : ℕ} (hn : 0 < n) :
    IsCoprime (j + (1 - j) * N ^ n.factorial) n := by
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
  apply Nat.coprime_of_dvd
  intro p hp hpν hpn
  haveI := Fact.mk hp
  have hν : ((j + (1 - j) * N ^ n.factorial : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact Int.natCast_dvd.mpr hpν
  have hpn' : p ≤ n := Nat.le_of_dvd hn hpn
  by_cases hN : (N : ZMod p) = 0
  · have hfac : n.factorial ≠ 0 := Nat.factorial_ne_zero n
    push_cast at hν
    rw [hN, zero_pow hfac, mul_zero, add_zero, ZMod.intCast_zmod_eq_zero_iff_dvd] at hν
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
    have hu := hj.isUnit_of_dvd' hν hN
    rw [Int.isUnit_iff] at hu
    have := hp.two_le
    omega
  · have hdvd : p - 1 ∣ n.factorial :=
      Nat.dvd_factorial (by have := hp.two_le; omega) (by omega)
    obtain ⟨s, hs⟩ := hdvd
    push_cast at hν
    rw [hs, pow_mul, ZMod.pow_card_sub_one_eq_one hN, one_pow] at hν
    simp at hν

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
private lemma zmod_pow_eq_pow_factorial_of_dvd {n : ℕ} (hn : 0 < n) (x : ZMod n) {c : ℕ}
    (hc : n.factorial ∣ c) (hc0 : 0 < c) : x ^ c = x ^ n.factorial := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have key : ∀ a t : ℕ, a ≤ n → 0 < t → t ≤ n → x ^ (a + t) = x ^ a → x ^ c = x ^ n.factorial := by
    intro a t ha ht htn h
    have hstep : ∀ k, a ≤ k → x ^ (k + t) = x ^ k := by
      intro k hk
      have e1 : k + t = (k - a) + (a + t) := by omega
      have e2 : k = (k - a) + a := by omega
      rw [e1, pow_add, h, ← pow_add, ← e2]
    have hper : ∀ k s, a ≤ k → x ^ (k + t * s) = x ^ k := by
      intro k s hk
      induction s with
      | zero => simp
      | succ s ih =>
        rw [show k + t * (s + 1) = (k + t * s) + t by ring, hstep _ (by omega), ih]
    have hfac : n.factorial ≤ c := Nat.le_of_dvd hc0 hc
    have htd : t ∣ c - n.factorial :=
      Nat.dvd_sub ((Nat.dvd_factorial ht htn).trans hc) (Nat.dvd_factorial ht htn)
    obtain ⟨s, hs⟩ := htd
    have : c = n.factorial + t * s := by omega
    rw [this, hper _ _ (le_trans ha (Nat.self_le_factorial n))]
  obtain ⟨a, b, hab, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => x ^ (i : ℕ))
    (by simp [ZMod.card])
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact key a (b - a) (by omega) (by omega) (by omega)
      (by rw [show (a : ℕ) + (b - a) = b by omega]; exact heq.symm)
  · exact key b (a - b) (by omega) (by omega) (by omega)
      (by rw [show (b : ℕ) + (a - b) = a by omega]; exact heq)


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.TateRoot.exists_tateIso_zeta_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (_ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e) (N : ℕ) (z : k),
    0 < N → IsPrimitiveRoot z N → ∃ I' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.TateIso D k Q act e, (I'.ζ N : k) = z := by
  intro E _ _ _ H D l k _ Q _ act e I N z hN hz
  have hζ : IsPrimitiveRoot ((I.ζ N : kˣ) : k) N := IsPrimitiveRoot.coe_units_iff.mpr (I.ζ_prim N hN)
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hz.pow_eq_one
  have hcop : IsCoprime (i : ℤ) N := by
    rw [Nat.isCoprime_iff_coprime]
    rw [← hζ.pow_iff_coprime hN, hi]
    exact hz
  suffices h : ∃ g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D, ∃ hν : (∀ (n m : ℕ), 0 < n → 0 < m → (n : ℤ) ∣ g.ν (n * m) - g.ν n ∧
      IsCoprime (g.ν n) n), (N : ℤ) ∣ g.ν N - i by
    obtain ⟨g, hν, hg⟩ := h
    refine ⟨_root_.GlobalTheory.LevelTwist.twist I g hν, ?_⟩
    rw [_root_.GlobalTheory.LevelTwist.twist_ζ, _root_.GlobalTheory.LevelTwist.zeta_zpow_congr I hN hg, zpow_natCast, Units.val_pow_eq_pow_val, hi]
  rcases Nat.eq_zero_or_pos (D.p + D.q) with hpq | hpq
  · haveI := D.proj
    haveI := D.fin
    have hsub : Subsingleton D.La := Module.finrank_zero_iff.mp (by rw [D.rank]; exact hpq)
    let g : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sim D :=
      { f := fun _ => LinearMap.id
        ν := fun n => i + (1 - i) * (N : ℤ) ^ n.factorial
        tower := fun n m _ _ a => ⟨0, by simp⟩
        inv := fun n _ => ⟨LinearMap.id, fun a => ⟨⟨0, Subsingleton.elim _ _⟩, ⟨0, Subsingleton.elim _ _⟩⟩⟩
        mult := fun n _ a b => by rw [Subsingleton.elim a 0]; simp }
    refine ⟨g, fun n m hn hm => ⟨?_, isCoprime_add_sub_mul_pow_factorial hcop hn⟩, ?_⟩
    · have h := zmod_pow_eq_pow_factorial_of_dvd hn (N : ZMod n)
        (Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right n hm)) (Nat.factorial_pos _)
      have h' : (((N : ℤ) ^ n.factorial : ℤ) : ZMod n) =
          (((N : ℤ) ^ (n * m).factorial : ℤ) : ZMod n) := by
        push_cast
        exact h.symm
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h'
      show (n : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial)
      rw [show (i + (1 - i) * (N : ℤ) ^ (n * m).factorial) - (i + (1 - i) * (N : ℤ) ^ n.factorial) =
        (1 - i) * ((N : ℤ) ^ (n * m).factorial - (N : ℤ) ^ n.factorial) by ring]
      exact Dvd.dvd.mul_left h' _
    · show (N : ℤ) ∣ (i + (1 - i) * (N : ℤ) ^ N.factorial) - i
      rw [add_sub_cancel_left]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (Nat.factorial_ne_zero N)) _
  · have hgrp := _root_.GlobalTheory.SimAlg.sim_group
    obtain ⟨g, hg, -⟩ := _root_.GlobalTheory.SimMult.exists_sim_trivial_of_mult hgrp _root_.GlobalTheory.exists_sim_lift
      E H D { l with A := 1, A_pos := Nat.one_pos } N i hN hcop (by simp)
    exact ⟨g, (hgrp E H D hpq).1 g, hg⟩

end GlobalTheory.TateRoot
end

