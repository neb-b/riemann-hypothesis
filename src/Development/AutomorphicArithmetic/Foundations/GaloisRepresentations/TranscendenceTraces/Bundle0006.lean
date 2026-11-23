module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PMultOpen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_self_eq_of_ringEquiv {R R' : Type*} [CommRing R] [CommRing R'] (f : R ≃+* R') :
    Module.length R R = Module.length R' R' := by
  haveI : RingHomInvPair (f : R →+* R') (f.symm : R' →+* R) := RingHomInvPair.of_ringEquiv f
  haveI : RingHomInvPair (f.symm : R' →+* R) (f : R →+* R') := RingHomInvPair.symm _ _
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f.toSemilinearEquiv)

private theorem length_stalk_eq {X Y : Scheme.{0}} (e : X ⟶ Y) [IsOpenImmersion e] (x : X) :
    Module.length (X.presheaf.stalk x) (X.presheaf.stalk x) =
      Module.length (Y.presheaf.stalk (e x)) (Y.presheaf.stalk (e x)) := by
  exact (length_self_eq_of_ringEquiv (asIso (e.stalkMap x)).commRingCatIsoToRingEquiv).symm

theorem UpperTheory.Gal.TranscendenceTraces.multOpen_of :
    MultOpen := by
  intro W Z S j _ p
  funext Ω _ _ z
  have e1 : (j ≫ p) ≫ 𝟙 S = j ≫ p := by simp
  have e2 : (z ≫ j ≫ p) ≫ 𝟙 S = 𝟙 (gp Ω) ≫ (z ≫ j) ≫ p := by simp
  let m := pullback.map (j ≫ p) (z ≫ j ≫ p) p ((z ≫ j) ≫ p) j (𝟙 _) (𝟙 S) e1 e2
  have hm : IsOpenImmersion m := by infer_instance
  have hx : pullback.lift z (𝟙 (gp Ω)) (by simp) ≫ m =
      pullback.lift (z ≫ j) (𝟙 (gp Ω)) (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc (pullback.lift z (𝟙 (gp Ω)) _)]
      simp only [m, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
    · rw [Category.assoc (pullback.lift z (𝟙 (gp Ω)) _)]
      simp only [m, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc, Category.comp_id]
  have hl := length_stalk_eq m (pt (pullback.lift z (𝟙 (gp Ω)) (by simp)))
  rw [← pt_comp, hx] at hl
  simp only [mult, Wt.comap]
  rw [hl]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNormSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.normSpec_of :
    SplitCover → CountEx → CountWt → MultPt → PtEx → PtLift → GenBasic → NormSpec := by
  intro hS hCE hCW hMP hPE hPL _
  unfold NormSpec
  intro A B _ _ _ _ _ _
  set p := Spec.map (CommRingCat.ofHom (algebraMap A B)) with hp
  haveI : IsFinite p := by
    rw [hp, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  obtain ⟨T, π, ι, σ, c, hπi, hπs, hι, hσ, hsym, hgen⟩ := hS A B
  haveI := hπi
  haveI := hπs
  haveI := hι
  have hk : ∀ s : ↥(Spec (CommRingCat.of B)), ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (y : gp Ω ⟶ Spec (CommRingCat.of B)), pt y = s := fun s => hPE _ s
  choose Ωk fk ak yk hyk using hk
  let key : ↥(Spec (CommRingCat.of B)) → ℤ := fun s => letI := fk s; letI := ak s; mult p (Ωk s) (yk s)
  let m : ι → ℤ := fun j => key (c j)
  have hm : ∀ j (Ω : Type) [Field Ω] [IsAlgClosed Ω] (z : gp Ω ⟶ Spec (CommRingCat.of B)),
      c j = pt z → m j = mult p Ω z := by
    intro j Ω _ _ z hz
    letI := fk (c j)
    letI := ak (c j)
    exact hMP p (Ωk (c j)) Ω (yk (c j)) z ((hyk (c j)).trans hz)
  have hSy : UpperTheory.Gal.TranscendenceTraces.Sym π σ m := by
    unfold UpperTheory.Gal.TranscendenceTraces.Sym
    intro Ω _ _ x x' hxx'
    obtain ⟨e, he⟩ := hsym Ω x x' hxx'
    exact ⟨e, fun j => ⟨(he j).1, congrArg key (he j).2⟩⟩
  obtain ⟨w, hw⟩ := hCE p π σ m hSy
  refine ⟨w, hCW p π σ m w hσ hw, ?_⟩
  intro Ω _ _ z hz
  obtain ⟨v, hv⟩ := π.surjective (pt (z ≫ p))
  obtain ⟨x, hx, -⟩ := hPL π Ω (z ≫ p) v hv
  have hcount := hw Ω x z hx.symm
  have hbot : (pt (x ≫ π)).asIdeal = ⊥ := by
    rw [hx]
    unfold GenPt at hz
    have h0 := hz (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le)
    rw [← h0]
  obtain ⟨⟨j0, hj0, huniq⟩, hcj⟩ := hgen Ω x z hx.symm hbot
  have hset : {j | x ≫ σ j = z} = {j0} := by
    ext j
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact huniq j
    · rintro rfl
      exact hj0
  rw [hcount, hset, finsum_mem_singleton]
  exact hm j0 Ω z (hcj j0 hj0)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtAgree
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtAgree_of :
    NwtOpen → WtUnique → GenBasic → MultBC → NwtAgree := by
  intro hOpen hUniq hGen _ Z S p _ A B _ _ w w' hw hw' Ω _ _ z z' hz
  have hc : pullback.fst A.u B.u ≫ A.u = pullback.snd A.u B.u ≫ B.u := pullback.condition
  have hP : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.fst A.u B.u ≫ A.u) :=
    IsPullback.of_hasPullback _ _
  have hP' : IsPullback (pullback.fst p (pullback.fst A.u B.u ≫ A.u))
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) p (pullback.snd A.u B.u ≫ B.u) := by
    rw [← hc]
    exact hP
  have eA : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.fst A.u B.u) ≫ A.u := by
    rw [Category.assoc]
    exact hP.w
  have eB : pullback.fst p (pullback.fst A.u B.u ≫ A.u) ≫ p =
      (pullback.snd p (pullback.fst A.u B.u ≫ A.u) ≫ pullback.snd A.u B.u) ≫ B.u := by
    rw [Category.assoc]
    exact hP'.w
  let C : Sq A.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.fst A.u B.u,
    A.pb.lift _ _ eA, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [A.pb.lift_fst]; exact hP) (A.pb.lift_snd _ _ _) A.pb⟩
  let C' : Sq B.r := ⟨pullback A.u B.u, pullback p (pullback.fst A.u B.u ≫ A.u), pullback.snd A.u B.u,
    B.pb.lift _ _ eB, pullback.snd p (pullback.fst A.u B.u ≫ A.u),
    IsPullback.of_right (by rw [B.pb.lift_fst]; exact hP') (B.pb.lift_snd _ _ _) B.pb⟩
  haveI : IsOpenImmersion C.u := inferInstanceAs (IsOpenImmersion (pullback.fst A.u B.u))
  haveI : IsOpenImmersion C'.u := inferInstanceAs (IsOpenImmersion (pullback.snd A.u B.u))
  have h1 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w.comap C.v) := hOpen A.r w C hw
  have h2 : IsNwt (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) (w'.comap C'.v) := hOpen B.r w' C' hw'
  haveI : IsFinite (pullback.snd p (pullback.fst A.u B.u ≫ A.u)) := MorphismProperty.of_isPullback hP ‹_›
  have hE : w.comap C.v = w'.comap C'.v :=
    hUniq _ _ _ h1.1 h2.1 {s | GenPt s} (hGen.1 _) fun Ω _ _ y hy => by
      rw [h1.2 Ω y hy, h2.2 Ω y hy]
  have e1 : (z ≫ A.r) ≫ A.u = (z' ≫ B.r) ≫ B.u := by
    rw [Category.assoc, Category.assoc, ← A.pb.w, ← B.pb.w, ← Category.assoc, ← Category.assoc, hz]
  have e2 : (z ≫ A.v) ≫ p = pullback.lift (z ≫ A.r) (z' ≫ B.r) e1 ≫ pullback.fst A.u B.u ≫ A.u := by
    rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, A.pb.w]
  let z0 : gp Ω ⟶ pullback p (pullback.fst A.u B.u ≫ A.u) :=
    pullback.lift (z ≫ A.v) (pullback.lift (z ≫ A.r) (z' ≫ B.r) e1) e2
  have hz0 : z0 ≫ C.v = z := by
    apply A.pb.hom_ext
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.v = _
      rw [Category.assoc, A.pb.lift_fst]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ A.pb.lift _ _ eA) ≫ A.r = _
      rw [Category.assoc, A.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_fst]
  have hz0' : z0 ≫ C'.v = z' := by
    apply B.pb.hom_ext
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.v = _
      rw [Category.assoc, B.pb.lift_fst, ← hz]
      exact pullback.lift_fst _ _ _
    · change (z0 ≫ B.pb.lift _ _ eB) ≫ B.r = _
      rw [Category.assoc, B.pb.lift_snd, pullback.lift_snd_assoc, pullback.lift_snd]
  have := congrFun (congrFun (congrFun (congrFun hE Ω) ‹_›) ‹_›) z0
  simpa only [Wt.comap, hz0, hz0'] using this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtDeg
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtDeg_of :
    WtNormal → WtDegConst → MultSum → MultBC → GenBasic → NwtDeg := by
  intro hN hD hMS hBC hG Z' Z S K _ v p' p g _ _ hpb hLoc hg
  obtain ⟨hW, hgen⟩ := hN p hLoc
  obtain ⟨d, hd⟩ := hD p (nwt p) hW
  rw [hd]
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  let Ω := AlgebraicClosure K
  let y : gp Ω ⟶ gp K := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have hval := congrArg (fun w : Wt S => w Ω (y ≫ g)) hd
  simp only [Wt.const] at hval
  have h1 : Wt.push p (nwt p) Ω (y ≫ g) = Wt.push p (mult p) Ω (y ≫ g) := by
    simp only [Wt.push]
    apply finsum_congr
    intro z
    apply finsum_congr
    intro hz
    apply hgen
    have hz' : z ≫ p = y ≫ g := hz
    rw [hz', pt_comp, Subsingleton.elim (pt y) (IsLocalRing.closedPoint K)]
    exact (hG.2.2 S _).mpr hg
  have h2 : Wt.push p (mult p) Ω (y ≫ g) = Wt.push p' (mult p') Ω y := by
    simp only [Wt.push]
    symm
    rw [finsum_mem_eq_of_bijOn (fun z => z ≫ v) (fib_bijOn hpb y)
      (g := fun z => mult p Ω z)]
    intro z _
    rw [hBC v p' p g hpb]
    rfl
  have h3 := hMS p' Ω y
  have h4 : pt y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  rw [h1, h2, h3, h4] at hval
  rw [hval]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtFlat_of :
    WtBC → WtFlat → WtUnique → MultBC → NwtFlat := by
  intro hBC hFlat hUniq hMBC Z' S' Z S v p' p g _ _ _ pb hN hD
  haveI : IsFinite p' := MorphismProperty.of_isPullback pb ‹_›
  refine hUniq p' _ _ (hBC v p' p g _ pb hN.1) (hFlat p') _ hD ?_
  intro Ω _ _ z hz
  rw [hMBC v p' p g pb]
  refine hN.2 Ω (z ≫ v) ?_
  have e : (z ≫ v) ≫ p = (z ≫ p') ≫ g := by
    rw [Category.assoc, pb.w, Category.assoc]
  rw [e, pt_comp]
  exact hz
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtGlue
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem lift_ex {Z S : Scheme.{0}} {p : Z ⟶ S} (A : Sq p) [IsOpenImmersion A.u] {Ω : Type} [Field Ω]
    (z : gp Ω ⟶ Z) (hz : pt (z ≫ p) ∈ Set.range A.u) : ∃ l : gp Ω ⟶ A.V, l ≫ A.v = z := by
  have hr : Set.range (z ≫ p) ⊆ Set.range A.u := by
    rintro _ ⟨t, rfl⟩
    rw [pt_eq]
    exact hz
  exact ⟨A.pb.lift z (IsOpenImmersion.lift A.u (z ≫ p) hr) (IsOpenImmersion.lift_fac _ _ _).symm,
    A.pb.lift_fst _ _ _⟩

theorem UpperTheory.Gal.TranscendenceTraces.nwtGlue_of :
    NwtAgree → WtLocal → MultBC → GenBasic → NwtGlue := by
  intro hAg hLoc hBC hGen Z S p _ h
  choose A w hopen hmem hw using h
  have hl : ∀ (Ω : Type) [Field Ω] (z : gp Ω ⟶ Z), ∃ l : gp Ω ⟶ (A (pt (z ≫ p))).V, l ≫ (A (pt (z ≫ p))).v = z := by
    intro Ω _ z
    haveI := hopen (pt (z ≫ p))
    exact lift_ex _ z (hmem _)
  choose l hlv using hl
  let W : Wt Z := fun Ω _ _ z => w (pt (z ≫ p)) Ω (l Ω z)
  have hcomap : ∀ t, W.comap (A t).v = w t := by
    intro t
    funext Ω _ _ z
    haveI := hopen t
    haveI := hopen (pt ((z ≫ (A t).v) ≫ p))
    exact hAg p (A _) (A t) (w _) (w t) (hw _) (hw t) Ω (l Ω (z ≫ (A t).v)) z (hlv Ω _)
  refine ⟨W, hLoc p W fun s => ⟨A s, hopen s, hmem s, ?_⟩, ?_⟩
  · rw [hcomap s]
    exact (hw s).1
  · intro Ω _ _ z hz
    set s := pt (z ≫ p) with hs
    haveI := hopen s
    have hz' : GenPt (pt (l Ω z ≫ (A s).r)) := by
      rw [← hGen.2.1 (A s).u, ← pt_comp, Category.assoc, ← (A s).pb.w, ← Category.assoc, hlv Ω z]
      exact hz
    have h1 := (hw s).2 Ω (l Ω z) hz'
    have h2 := hBC (A s).v (A s).r p (A s).u (A s).pb
    change w s Ω (l Ω z) = _
    rw [h1, h2]
    change mult p Ω (l Ω z ≫ (A s).v) = _
    rw [hlv Ω z]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOfFlat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOfFlat_of :
    WtFlat → WtUnique → GenBasic → NwtOfFlat := by
  intro hW hU hG Z S p _ _ _
  have hm : IsNwt p (mult p) := ⟨hW p, fun _ _ _ _ _ => rfl⟩
  have hex : ∃ w, IsNwt p w := ⟨mult p, hm⟩
  have hspec : IsNwt p hex.choose := hex.choose_spec
  have hval : nwt p = hex.choose := by
    unfold nwt
    rw [dite_eq_left hex]
  rw [hval]
  refine hU p _ _ hspec.1 hm.1 {s | GenPt s} (hG.1 S) ?_
  intro Ω _ _ z hz
  exact hspec.2 Ω z hz
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PNwtOpen
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.nwtOpen_of :
    WtBC → MultBC → GenBasic → NwtOpen := by
  intro hw hm hg Z S p w A _ hp
  obtain ⟨hwt, hgen⟩ := hp
  refine ⟨hw A.v A.r p A.u w A.pb hwt, ?_⟩
  intro Ω _ _ z hz
  have hsq : (z ≫ A.v) ≫ p = (z ≫ A.r) ≫ A.u := by
    rw [Category.assoc, Category.assoc, A.pb.w]
  have hz' : GenPt (pt ((z ≫ A.v) ≫ p)) := by
    rw [hsq, pt_comp]
    exact (hg.2.1 A.u (pt (z ≫ A.r))).mpr hz
  rw [hm A.v A.r p A.u A.pb]
  exact hgen Ω (z ≫ A.v) hz'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtCommon
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.ptCommon_of :
    PtCommon := by
  intro X Ω Ω' _ _ z z' h
  have key : ∀ (K : Type) [Field K] (w : gp K ⟶ X) (y : X), pt w = y →
      ∃ ψ : X.residueField y ⟶ CommRingCat.of K, w = Spec.map ψ ≫ X.fromSpecResidueField y := by
    intro K _ w y hy
    subst hy
    exact ⟨_, (Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X w).symm⟩
  obtain ⟨x, hx⟩ : ∃ x, pt z = x := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ := key Ω z x hx
  obtain ⟨φ', hφ'⟩ := key Ω' z' x (h.symm.trans hx)
  have i1 : Function.Injective φ.hom := φ.hom.injective
  have i2 : Function.Injective φ'.hom := φ'.hom.injective
  letI := φ.hom.toAlgebra
  letI := φ'.hom.toAlgebra
  haveI : Nontrivial (TensorProduct (X.residueField x) Ω Ω') :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ i1 i2
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (TensorProduct (X.residueField x) Ω Ω')
  letI := Ideal.Quotient.field M
  let ψ : TensorProduct (X.residueField x) Ω Ω' →+* AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M) :=
    (algebraMap _ _).comp (Ideal.Quotient.mk M)
  have e1 : ∀ c, (φ.hom c ⊗ₜ[X.residueField x] (1 : Ω') : TensorProduct (X.residueField x) Ω Ω') =
      (1 : Ω) ⊗ₜ (φ'.hom c) := by
    intro c
    change algebraMap _ Ω c ⊗ₜ _ = _ ⊗ₜ algebraMap _ Ω' c
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  refine ⟨AlgebraicClosure (TensorProduct (X.residueField x) Ω Ω' ⧸ M), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (ψ.comp Algebra.TensorProduct.includeLeftRingHom)),
    Spec.map (CommRingCat.ofHom (ψ.comp (Algebra.TensorProduct.includeRight :
      Ω' →ₐ[X.residueField x] TensorProduct (X.residueField x) Ω Ω').toRingHom)), ?_⟩
  rw [hφ, hφ', ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext c
  simp [e1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtLift
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pt_map_ideal {Ω : Type} [Field Ω] {B : CommRingCat.{0}} (s : B ⟶ CommRingCat.of Ω) :
    (show PrimeSpectrum B from pt (Spec.map s)).asIdeal = RingHom.ker s.hom := by
  have h : (pt (Spec.map s) : Spec B) = PrimeSpectrum.comap s.hom (IsLocalRing.closedPoint Ω) := rfl
  change (pt (Spec.map s) : Spec B).asIdeal = _
  rw [h, RingHom.ker_eq_comap_bot]
  change Ideal.comap s.hom (IsLocalRing.maximalIdeal Ω) = _
  rw [IsLocalRing.maximalIdeal_eq_bot]

private theorem exists_retract {Ω : Type} [Field Ω] [IsAlgClosed Ω] {B : CommRingCat.{0}} (φ : CommRingCat.of Ω ⟶ B)
    (hφ : φ.hom.IsIntegral) (q : Ideal B) [q.IsPrime] :
    ∃ s : B ⟶ CommRingCat.of Ω, φ ≫ s = 𝟙 _ ∧ RingHom.ker s.hom = q := by
  letI : Algebra Ω B := φ.hom.toAlgebra
  haveI : Algebra.IsIntegral Ω B := ⟨hφ⟩
  have hb : Function.Bijective (algebraMap Ω (B ⧸ q)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : Ω ≃+* B ⧸ q := RingEquiv.ofBijective (algebraMap Ω (B ⧸ q)) hb
  refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp (Ideal.Quotient.mk q)), ?_, ?_⟩
  · ext a
    change e.symm (Ideal.Quotient.mk q (φ.hom a)) = a
    exact e.symm_apply_apply a
  · ext b
    change e.symm (Ideal.Quotient.mk q b) = 0 ↔ b ∈ q
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp

theorem UpperTheory.Gal.TranscendenceTraces.ptLift_of :
    PtLift := by
  intro V U r _ Ω _ _ x v hv
  obtain ⟨t, ht1, ht2⟩ := Scheme.Pullback.exists_preimage_pullback (f := r) (g := x) v
    (IsLocalRing.closedPoint Ω) hv
  let P := pullback r x
  haveI : IsIntegralHom (pullback.snd r x) := inferInstance
  haveI : IsAffine P := isAffine_of_isAffineHom (pullback.snd r x)
  let φ : CommRingCat.of Ω ⟶ Γ(P, ⊤) := Spec.preimage (P.isoSpec.inv ≫ pullback.snd r x)
  have hφ' : Spec.map φ = P.isoSpec.inv ≫ pullback.snd r x := Spec.map_preimage _
  have hφ : φ.hom.IsIntegral := by
    rw [← IsIntegralHom.SpecMap_iff, hφ']
    infer_instance
  let y : Spec Γ(P, ⊤) := P.isoSpec.hom t
  haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime y
  obtain ⟨s, hs, hk⟩ := exists_retract φ hφ y.asIdeal
  refine ⟨Spec.map s ≫ P.isoSpec.inv ≫ pullback.fst r x, ?_, ?_⟩
  · have h1 : Spec.map s ≫ Spec.map φ = 𝟙 _ := by
      rw [← Spec.map_comp, hs, Spec.map_id]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc P.isoSpec.inv,
      ← hφ', ← Category.assoc, h1, Category.id_comp]
  · have hy : (pt (Spec.map s) : Spec Γ(P, ⊤)) = y :=
      PrimeSpectrum.ext ((pt_map_ideal s).trans hk)
    rw [← Category.assoc, pt_comp, pt_comp, hy]
    change (pullback.fst r x) (P.isoSpec.inv (P.isoSpec.hom t)) = v
    have h2 : P.isoSpec.inv (P.isoSpec.hom t) = t := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [h2, ht1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPtOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma ring_eq {Ω B L : Type} [Field Ω] [IsAlgClosed Ω] [CommRing B] [Algebra Ω B] [Module.Finite Ω B] [Field L]
    (f f' : B →+* L) (h : f.comp (algebraMap Ω B) = f'.comp (algebraMap Ω B))
    (hk : RingHom.ker f = RingHom.ker f') : f = f' := by
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  haveI : IsDomain (B ⧸ RingHom.ker f) := Ideal.Quotient.isDomain _
  have hb := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := B ⧸ RingHom.ker f)
  ext b
  obtain ⟨c, hc⟩ := hb.2 (Ideal.Quotient.mk _ b)
  have hm : b - algebraMap Ω B c ∈ RingHom.ker f := by
    rw [← Ideal.Quotient.eq]
    rw [← hc]
    rfl
  have h1 : f b = f (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp hm
    rw [map_sub, sub_eq_zero] at this
    exact this
  have h2 : f' b = f' (algebraMap Ω B c) := by
    have := RingHom.mem_ker.mp (hk ▸ hm)
    rw [map_sub, sub_eq_zero] at this
    exact this
  rw [h1, h2]
  exact congrArg (fun g : Ω →+* L => g c) h

private lemma pt_spec {B L : Type} [CommRing B] [Field L] (f : CommRingCat.of B ⟶ CommRingCat.of L) :
    (pt (Spec.map f) : Spec (CommRingCat.of B)).asIdeal = RingHom.ker f.hom := by
  ext b
  change f.hom b ∈ (IsLocalRing.closedPoint L).asIdeal ↔ _
  simp [RingHom.mem_ker, IsLocalRing.closedPoint]

theorem UpperTheory.Gal.TranscendenceTraces.ptOne_of :
    Chart → PtOne := by
  intro hC V Ω _ _ r _ L _ a z z' hz hz' hp
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 _)
  haveI : IsIso v := hpb.isIso_fst_of_isIso
  have hs : inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = r := by
    have := hpb.w
    rw [Category.comp_id] at this
    rw [← this, IsIso.inv_hom_id_assoc]
  obtain ⟨f, hf⟩ := Spec.map_surjective (z ≫ inv v)
  obtain ⟨f', hf'⟩ := Spec.map_surjective (z' ≫ inv v)
  have e1 : Spec.map f ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf, Category.assoc, hs, hz]
  have e2 : Spec.map f' ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) = a := by
    rw [hf', Category.assoc, hs, hz']
  have e3 : CommRingCat.ofHom (algebraMap Ω B) ≫ f = CommRingCat.ofHom (algebraMap Ω B) ≫ f' := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, e1, e2]
  have e4 : pt (Spec.map f) = pt (Spec.map f') := by
    rw [hf, hf', pt_comp, pt_comp, hp]
  have e5 : RingHom.ker f.hom = RingHom.ker f'.hom := by
    rw [← pt_spec f, ← pt_spec f', e4]
  have e6 : f.hom = f'.hom := ring_eq f.hom f'.hom (congrArg CommRingCat.Hom.hom e3) e5
  have e7 : f = f' := CommRingCat.hom_ext e6
  have e8 : z ≫ inv v = z' ≫ inv v := by rw [← hf, ← hf', e7]
  exact (cancel_mono (inv v)).mp e8
end

