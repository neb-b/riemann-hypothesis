module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0058
public import Development.EtaleCohomology.EtaleSheaves.StrictHenselColimits.ColimOf
public import Development.EtaleCohomology.EtaleSheaves.Bundle0054
public import Development.EtaleCohomology.EtaleSheaves.ChartsGeomVpaPf

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.A9OfA0A1EigenbasisA6
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafClosedSH0Pf
open LateralTheory.E.E4 LateralTheory.E.LeafVanBPf

def LeafSHSieve : Prop := ∀ (X : Scheme.{0}) [IsAffine X], SH Γ(X, ⊤) →
  ∀ S ∈ Scheme.etaleTopology X, S (𝟙 X)

def LeafSHQuot : Prop := ∀ (A : Type) [CommRing A], SH A → ∀ {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'],
  IsEmpty W' ∨ SH Γ(W', ⊤)

def LeafEmptySec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (X : Scheme.{0}), IsEmpty X → Subsingleton (Sec F X)

def LeafPrimLift : Prop := ∀ (q : ℕ) (B C : Type) [CommRing B] [CommRing C] [HenselianLocalRing B] [Nontrivial C]
  (f : B →+* C), Function.Surjective f → Function.Surjective (Prim.map (q := q) f)

theorem a9_of_a0_a1_eigenbasis_a6 (hy : Hyps) : A9 := hy.2.2.2.2.2.2.2.1

theorem twF_surj (hP : LeafPrimLift) (q : ℕ) (i : ℤ) {B C : CommRingCat.{0}} [HenselianLocalRing B] [Nontrivial C]
    (f : B ⟶ C) (hf : Function.Surjective f) : Function.Surjective ((twF q i).map f) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨x', rfl⟩ := Finsupp.mapDomain_surjective (hP q B C f.hom hf) x
  exact ⟨Submodule.Quotient.mk x', rfl⟩

theorem secSurj (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) (q : ℕ) (i : ℤ)
    (A : Type) [CommRing A] (hA : SH A) {W' : Scheme.{0}} (ι' : W' ⟶ Sp A) [IsClosedImmersion ι'] :
    Function.Surjective (Sec.res ι' : Sec (tw q i) (Sp A) → Sec (tw q i) W') := by
  rcases hQ A hA ι' with hW | hW
  · have := hE (ZMod q) (tw q i) W' hW
    exact fun y => ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  have hW0 := hW
  obtain ⟨_, _⟩ := hW
  obtain ⟨_, _⟩ := hA
  intro s
  let P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) := Scheme.Γ ⋙ twF q i
  have hmem := Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) s
  obtain ⟨t, ht⟩ := hS W' hW0 _ hmem
  let g : CommRingCat.of A ⟶ Γ(W', ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ι'.appTop
  have hg : Function.Surjective g := hsurj.comp (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.surjective
  obtain ⟨t', rfl⟩ := twF_surj hP q i g hg t
  refine ⟨(toSheafify Scheme.etaleTopology P).app (op (Sp A)) ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t'), ?_⟩
  have e1 := NatTrans.naturality_apply (toSheafify Scheme.etaleTopology P) ι'.op
    ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t')
  have e2 : P.map ι'.op ((twF q i).map (Scheme.ΓSpecIso (CommRingCat.of A)).inv t') = (twF q i).map g t' := by
    simp only [P, g, Functor.comp_map, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  rw [e2, ht] at e1
  simp only [op_id] at e1
  refine Eq.trans ?_ (e1.symm.trans ?_)
  · rfl
  · simp
    rfl

theorem LeafClosedSH0_of (hS : LeafSHSieve) (hQ : LeafSHQuot) (hE : LeafEmptySec) (hP : LeafPrimLift) :
    LeafClosedSH0 := by
  intro hy q _ i A _ _ hA hq W' ι' _
  obtain ⟨-, e, he, -⟩ := a9_of_a0_a1_eigenbasis_a6 hy (ZMod q) (tw q i)
  intro y
  obtain ⟨s, rfl⟩ := (e W').surjective y
  obtain ⟨t, rfl⟩ := secSurj hS hQ hE hP q i A hA ι' s
  exact ⟨e _ t, he _ t⟩

end LateralTheory.E.LeafClosedSH0Pf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.AbsorbPf
section
noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.AbsorbPf

def Sys : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (φ : ∀ j, D.obj j →+* Ω),
    (∀ j, Et (t.app j)) ∧ (∀ j, (φ j).comp (t.app j).hom = ι) ∧
    (∀ (j k : J) (a : j ⟶ k), (φ k).comp (D.map a).hom = φ j) ∧
    (∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (j : J) (h : B ⟶ D.obj j), g ≫ h = t.app j ∧ (φ j).comp h.hom = φB) ∧
    (∀ (j : J) (x : D.obj j), φ j x ≠ 0 → ∃ (k : J) (a : j ⟶ k), IsUnit ((D.map a).hom x))

theorem t_nat {J : Type} [SmallCategory J] {A : CommRingCat.{0}} {D : J ⥤ CommRingCat.{0}}
    (t : (Functor.const J).obj A ⟶ D) {j k : J} (a : j ⟶ k) : t.app j ≫ D.map a = t.app k := by
  have := t.naturality a
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at this
  exact this.symm

theorem Absorb_of (hS : Sys) : LateralTheory.E.ColimPf.Absorb := by
  intro A Ω _ ι
  obtain ⟨J, _, _, D, t, φ, hEt, hpt, hcomp, habs, hloc⟩ := hS A Ω ι
  let O : CommRingCat.{0} := colimit D
  let s : D ⟶ (Functor.const J).obj O := (colimit.cocone D).ι
  let j0 : J := IsFiltered.nonempty.some
  let f : A ⟶ O := t.app j0 ≫ colimit.ι D j0
  have hf : ∀ j, t.app j ≫ colimit.ι D j = f := by
    intro j
    let k := IsFiltered.max j j0
    show t.app j ≫ colimit.ι D j = t.app j0 ≫ colimit.ι D j0
    rw [← colimit.w D (IsFiltered.leftToMax j j0), ← colimit.w D (IsFiltered.rightToMax j j0),
      ← Category.assoc, ← Category.assoc, t_nat, t_nat]
  let cΩ : Cocone D :=
    { pt := CommRingCat.of Ω
      ι := { app := fun j => CommRingCat.ofHom (φ j)
             naturality := by
               intro j k a
               ext x
               have := DFunLike.congr_fun (hcomp j k a) x
               simpa using this } }
  let ψ : O →+* Ω := (colimit.desc D cΩ).hom
  have hψ : ∀ j (y : D.obj j), ψ (colimit.ι D j y) = φ j y := by
    intro j y
    have := colimit.ι_desc cΩ j
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom this) y
  refine ⟨O, f, ψ, ?_, ?_, ?_, ?_⟩
  · refine ⟨J, inferInstance, inferInstance, D, t, s, colimit.isColimit D, fun j => ⟨hEt j, hf j⟩⟩
  · ext a
    have := DFunLike.congr_fun (hpt j0) a
    simp only [RingHom.comp_apply] at this ⊢
    rw [← this, ← hψ]; rfl
  · intro x hx
    obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep D x
    rw [hψ] at hx
    obtain ⟨k, a, hu⟩ := hloc j y hx
    have : colimit.ι D j y = colimit.ι D k ((D.map a).hom y) := by
      rw [← colimit.w D a]; rfl
    rw [this]
    exact hu.map (colimit.ι D k).hom
  · intro B g hg φB hφB
    obtain ⟨j, h, hh1, hh2⟩ := habs B g hg φB hφB
    refine ⟨h ≫ colimit.ι D j, ?_, ?_⟩
    · rw [← Category.assoc, hh1, hf]
    · ext b
      simp only [RingHom.comp_apply, CommRingCat.hom_comp]
      rw [hψ]
      exact DFunLike.congr_fun hh2 b

def Sys2 : Prop := ∀ (A : CommRingCat.{0}) (Ω : Type) [Field Ω] (ι : A →+* Ω),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (t : (Functor.const J).obj A ⟶ D) (φ : ∀ j, D.obj j →+* Ω),
    (∀ j, Et (t.app j)) ∧ (∀ j, (φ j).comp (t.app j).hom = ι) ∧
    (∀ (j k : J) (a : j ⟶ k), (φ k).comp (D.map a).hom = φ j) ∧
    (∀ (B : CommRingCat.{0}) (g : A ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = ι →
      ∃ (j : J) (h : B ⟶ D.obj j), g ≫ h = t.app j ∧ (φ j).comp h.hom = φB) ∧
    (∀ (j : J) (B : CommRingCat.{0}) (g : D.obj j ⟶ B), Et g → ∀ φB : B →+* Ω, φB.comp g.hom = φ j →
      ∃ (k : J) (a : j ⟶ k) (h : B ⟶ D.obj k), g ≫ h = D.map a)

theorem Sys_of (h2 : Sys2) : Sys := by
  intro A Ω _ ι
  obtain ⟨J, i1, i2, D, t, φ, hEt, hpt, hcomp, habs, hst⟩ := h2 A Ω ι
  refine ⟨J, i1, i2, D, t, φ, hEt, hpt, hcomp, habs, ?_⟩
  intro j x hx
  let B : CommRingCat.{0} := CommRingCat.of (Localization.Away x)
  let g : D.obj j ⟶ B := CommRingCat.ofHom (algebraMap (D.obj j) (Localization.Away x))
  have hg : Et g := by
    change (algebraMap (D.obj j) (Localization.Away x)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  have hu : IsUnit (φ j x) := isUnit_iff_ne_zero.mpr hx
  let φB : B →+* Ω := IsLocalization.Away.lift x hu
  obtain ⟨k, a, h, hh⟩ := hst j B g hg φB (IsLocalization.Away.lift_comp x hu)
  refine ⟨k, a, ?_⟩
  have e : (D.map a).hom x = h.hom (algebraMap (D.obj j) (Localization.Away x) x) := by
    rw [← hh]; rfl
  rw [e]
  exact (IsLocalization.Away.algebraMap_isUnit x).map h.hom

theorem etaleAbsorbing_of_strongFilteredEtaleSystemExists (h2 : Sys2) : LateralTheory.E.ColimPf.Absorb := Absorb_of (Sys_of h2)

end LateralTheory.E.AbsorbPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.BaseLocLocPf
section
set_option linter.style.haveILetI false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace LateralTheory.E.BaseLocLocPf

theorem pb_cancel {C : Type*} [Category C] {P X Y Z T : C} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i : Z ⟶ T} [Mono i] (h : IsPullback a b (f ≫ i) (g ≫ i)) : IsPullback a b f g := by
  refine ⟨⟨by simpa [← cancel_mono i] using h.w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift s.fst s.snd (by simp [s.condition_assoc])) (fun s => by simp) (fun s => by simp) ?_⟩⟩
  intro s m h1 h2
  apply h.hom_ext <;> simp [h1, h2]

theorem loc_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (M : Submonoid A)
    (hf : @IsLocalization _ _ M _ _ f.toAlgebra) [Algebra B C] (N : Submonoid B) [IsLocalization N C] :
    ∃ M' : Submonoid A, @IsLocalization _ _ M' _ _ ((algebraMap B C).comp f).toAlgebra := by
  letI := f.toAlgebra
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact ⟨_, IsLocalization.localization_localization_isLocalization M N C⟩

theorem loc_equiv' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (e : B ≃+* C) :
    @IsLocalization _ _ M _ _ ((e : B →+* C).comp (algebraMap A B)).toAlgebra := by
  letI : Algebra A C := ((e : B →+* C).comp (algebraMap A B)).toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv M (AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl))

theorem chart {Z S : Scheme.{0}} (c : Z ⟶ S) (x : S) (W : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens)
    (y : (pullback c (S.fromSpecStalk x) : Scheme.{0})) (hy : y ∈ W) :
    ∃ U : (pullback c (S.fromSpecStalk x) : Scheme.{0}).Opens, y ∈ U ∧ U ≤ W ∧
    ∃ V : Z.Opens, IsAffineOpen V ∧ (V : Set Z).Nonempty ∧
    ∃ f : Γ(Z, V) →+* Γ((pullback c (S.fromSpecStalk x) : Scheme.{0}), U), ∃ M : Submonoid Γ(Z, V),
      @IsLocalization _ _ M _ _ f.toAlgebra := by
  obtain ⟨U0, hU0a, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : S.Opens) from trivial)
  have hg : S.fromSpecStalk x = Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec :=
    (hU0a.fromSpecStalk_eq_fromSpecStalk hxU0).symm
  have hgU : ∀ z, S.fromSpecStalk x z ∈ U0 := by
    intro z; rw [hg, Scheme.Hom.comp_apply]; exact hU0a.range_fromSpec.le (Set.mem_range_self _)
  have hcy : c (pullback.fst c (S.fromSpecStalk x) y) ∈ U0 := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]; exact hgU _
  obtain ⟨V, hVa, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
    (show pullback.fst c (S.fromSpecStalk x) y ∈ c ⁻¹ᵁ U0 from hcy)
  have hVU' : V ≤ c ⁻¹ᵁ U0 := hVU
  set p := pullback.fst c (S.fromSpecStalk x)
  set O := p ⁻¹ᵁ V with hOdef
  have H1 : IsPullback (p ∣_ V) O.ι V.ι p := isPullback_morphismRestrict p V
  have H2 : IsPullback (p ∣_ V) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (V.ι ≫ c) (S.fromSpecStalk x) :=
    H1.paste_vert (IsPullback.of_hasPullback c (S.fromSpecStalk x))
  let ψ := c.appLE U0 V hVU'
  have e1 : V.ι ≫ c = hVa.isoSpec.hom ≫ Spec.map ψ ≫ hU0a.fromSpec := by
    rw [IsAffineOpen.SpecMap_appLE_fromSpec c hU0a hVa hVU', ← IsAffineOpen.isoSpec_inv_ι]; simp
  have H3 : IsPullback ((p ∣_ V) ≫ hVa.isoSpec.hom) (O.ι ≫ pullback.snd c (S.fromSpecStalk x)) (Spec.map ψ ≫ hU0a.fromSpec)
      (Spec.map (S.presheaf.germ U0 x hxU0) ≫ hU0a.fromSpec) := by
    rw [← hg]
    exact IsPullback.of_iso H2 (Iso.refl _) hVa.isoSpec (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [e1]) (by simp)
  have H4 := pb_cancel H3
  letI : Algebra Γ(S, U0) Γ(Z, V) := ψ.hom.toAlgebra
  letI := S.presheaf.algebra_section_stalk ⟨x, hxU0⟩
  haveI hSt : IsLocalization.AtPrime (S.presheaf.stalk x) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal :=
    hU0a.isLocalization_stalk ⟨x, hxU0⟩
  have H5 := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(S, U0) Γ(Z, V) (S.presheaf.stalk x))
  let e := H4.isoIsPullback _ _ H5
  haveI : IsAffine O.toScheme := IsAffine.of_isIso e.hom
  have hOa : IsAffineOpen O := this
  let eR : CommRingCat.of (Γ(Z, V) ⊗[Γ(S, U0)] S.presheaf.stalk x) ≅ Γ(pullback c (S.fromSpecStalk x), O) :=
    (Scheme.ΓSpecIso _).symm ≪≫ Scheme.Γ.mapIso e.op ≪≫ O.topIso
  have hL := loc_equiv' (Algebra.algebraMapSubmonoid Γ(Z, V) (hU0a.primeIdealOf ⟨x, hxU0⟩).asIdeal.primeCompl)
    eR.commRingCatIsoToRingEquiv
  have hyO : y ∈ O := hyV
  obtain ⟨h, hhW, hyh⟩ := hOa.exists_basicOpen_le (V := W) ⟨y, hy⟩ hyO
  haveI := hOa.isLocalization_basicOpen h
  obtain ⟨M, hM⟩ := loc_comp (C := Γ(pullback c (S.fromSpecStalk x), (pullback c (S.fromSpecStalk x)).basicOpen h)) _ _ hL (Submonoid.powers h)
  exact ⟨_, hyh, hhW, V, hVa, ⟨_, hyV⟩, _, M, hM⟩

theorem BaseLocLoc_of : LateralTheory.E.BaseAICPf.BaseLocLoc := by
  intro Z S c _ _ _ _ _ x W y hy
  exact chart c x W y hy

end LateralTheory.E.BaseLocLocPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ChartMapBase
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.ChartOverlap₂

set_option linter.unusedSectionVars false

variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]

theorem restr_iff (B : Subalgebra A K) (t : K) (S : Subalgebra A K) {R W : Type} [CommRing R] [CommRing W]
    (eR : R ≃+* S) (eW : W ≃+* AdjoinInv B t) (res : R →+* W) (hc : ∀ r, ((eW (res r) : AdjoinInv B t) : K) = (eR r : K))
    (P : PrimeSpectrum W) (x : PrimeSpectrum S) :
    Restr B t (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P) S x ↔
      PrimeSpectrum.comap (eR : R →+* S) x = PrimeSpectrum.comap res P := by
  have key : ∀ s : S, (∃ d ∈ (PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* W) P).asIdeal, (d : K) = (s : K)) ↔
      res (eR.symm s) ∈ P.asIdeal := by
    intro s
    have hd : eW (res (eR.symm s)) = ⟨(s : K), by simpa [hc] using (eW (res (eR.symm s))).2⟩ := by
      apply Subtype.ext; simp [hc]
    constructor
    · rintro ⟨d, hd1, hd2⟩
      have : d = eW (res (eR.symm s)) := by rw [hd]; exact Subtype.ext hd2
      subst this
      simpa using hd1
    · intro h
      refine ⟨eW (res (eR.symm s)), ?_, by simp [hc]⟩
      simpa using h
  unfold Restr
  simp_rw [key]
  constructor
  · intro h
    ext r
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe]
    have := h (eR r)
    simpa using this
  · intro h s
    have := congrArg (fun q : PrimeSpectrum R => eR.symm s ∈ q.asIdeal) h
    simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply] at this
    exact Iff.of_eq this

theorem chartMap_base {Z : Scheme.{0}} {U : Z.Opens} (hU : IsAffineOpen U) (φ : Γ(Z, U) →+* K)
    (hi : Function.Injective φ) (B : Subalgebra A K) (hr : φ.range = B.toSubring) (x : PrimeSpectrum B) :
    (chartMap hU φ hi B hr).base x =
      hU.fromSpec.base (PrimeSpectrum.comap (chartEquiv φ hi B hr : Γ(Z, U) →+* B) x) := rfl

theorem fromSpec_res {Z : Scheme.{0}} {U W : Z.Opens} (hU : IsAffineOpen U) (hW : IsAffineOpen W) (h : W ≤ U)
    (P : PrimeSpectrum Γ(Z, W)) :
    hU.fromSpec.base (PrimeSpectrum.comap (Z.presheaf.map (homOfLE h).op).hom P) = hW.fromSpec.base P := by
  rw [← hU.map_fromSpec hW (homOfLE h).op]; rfl

theorem Overlap_of : LateralTheory.E.ChartsGeom_vpaPf.Overlap := by
  intro A _ _ K _ _ Z p B C t _ U V φU φV φW hU hV hW hUV iU iV iW rU rV rW cU cV x y
  set eU := chartEquiv φU iU B rU
  set eV := chartEquiv φV iV C rV
  set eW := chartEquiv φW iW (AdjoinInv B t) rW
  have hcU : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom r) : AdjoinInv B t) : K) =
      (eU r : K) := fun r => cU r
  have hcV : ∀ r, ((eW ((Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom r) : AdjoinInv B t) : K) =
      (eV r : K) := fun r => cV r
  rw [chartMap_base, chartMap_base]
  constructor
  · intro h
    have hzU : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (U : Set Z) := by
      rw [← hU.range_fromSpec]; exact ⟨_, rfl⟩
    have hzV : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ (V : Set Z) := by
      rw [h, ← hV.range_fromSpec]; exact ⟨_, rfl⟩
    have hz : hU.fromSpec.base (PrimeSpectrum.comap (eU : Γ(Z, U) →+* B) x) ∈ Set.range hW.fromSpec.base := by
      rw [hW.range_fromSpec]; exact ⟨hzU, hzV⟩
    obtain ⟨P, hP⟩ := hz
    refine ⟨PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V)) P,
      (restr_iff B t B eU eW _ hcU P x).2 ?_, (restr_iff B t C eV eW _ hcV P y).2 ?_⟩
    · apply hU.fromSpec.isOpenEmbedding.injective
      exact ((fromSpec_res hU hW inf_le_left P).trans hP).symm
    · apply hV.fromSpec.isOpenEmbedding.injective
      exact (h.symm.trans hP.symm).trans (fromSpec_res hV hW inf_le_right P).symm
  · rintro ⟨Q, hx, hy⟩
    have hQ : Q = PrimeSpectrum.comap (eW.symm : AdjoinInv B t →+* Γ(Z, U ⊓ V))
        (PrimeSpectrum.comap (eW : Γ(Z, U ⊓ V) →+* AdjoinInv B t) Q) := by
      ext a; simp only [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, RingEquiv.apply_symm_apply]
    rw [hQ] at hx hy
    have hx1 := (restr_iff B t B eU eW _ hcU _ x).1 hx
    have hy1 := (restr_iff B t C eV eW _ hcV _ y).1 hy
    exact (congrArg hU.fromSpec.base hx1).trans ((fromSpec_res hU hW inf_le_left _).trans
      ((fromSpec_res hV hW inf_le_right _).symm.trans (congrArg hV.fromSpec.base hy1).symm))

end LateralTheory.E.ChartOverlap₂
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.DescendPf
section
noncomputable section
open CategoryTheory Limits LateralTheory.E.t_E3Cut

namespace LateralTheory.E.DescendPf

def Spread : Prop := ∀ (A O : CommRingCat.{0}) (f : A ⟶ O), IE f →
  ∀ (C : Type) [CommRing C] [Algebra O C] [Algebra.Etale O C],
  ∃ (B : CommRingCat.{0}) (g : A ⟶ B) (d : B ⟶ O) (C' : CommRingCat.{0}) (e : B ⟶ C') (c : C' →+* C),
    Et g ∧ Et e ∧ g ≫ d = f ∧
    IsPushout e d (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap O C))

theorem Descend_of (hS : Spread) : LateralTheory.E.ColimPf.Descend := by
  intro A O f hf C _ _ _
  obtain ⟨B, g, d, C', e, c, hg, he, hgd, hP⟩ := hS A O f hf C
  refine ⟨B, g, d, C', e, c, hg, he, hgd, ?_, ?_, ?_⟩
  · ext y
    have := congrArg (fun φ => φ.hom y) hP.w
    simpa using this
  · intro k hk
    have hw : e ≫ k = d ≫ 𝟙 O := by rw [hk, Category.comp_id]
    let s := hP.desc k (𝟙 O) hw
    have h1 : CommRingCat.ofHom c ≫ s = k := hP.inl_desc k (𝟙 O) hw
    have h2 : CommRingCat.ofHom (algebraMap O C) ≫ s = 𝟙 O := hP.inr_desc k (𝟙 O) hw
    refine ⟨{ s.hom with commutes' := fun r => ?_ }, ?_⟩
    · have := congrArg (fun φ => φ.hom r) h2
      change s.hom (algebraMap O C r) = (𝟙 O : O ⟶ O).hom r
      exact this
    · ext y
      have := congrArg (fun φ => φ.hom y) h1
      simpa using this
  · intro R _ α β h1 h2
    have := hP.hom_ext (W := CommRingCat.of R) (k := CommRingCat.ofHom α) (l := CommRingCat.ofHom β) ?_ ?_
    · exact congrArg CommRingCat.Hom.hom this
    · ext y
      exact DFunLike.congr_fun h2 y
    · ext y
      exact DFunLike.congr_fun h1 y

end LateralTheory.E.DescendPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.StdChartsProof
  LateralTheory.E.ChartsGeom_vpaPf

namespace LateralTheory.E.GeometricData

def rA {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (W : Z.Opens) : A →+* Γ(Z, W) :=
  (p.appLE ⊤ W le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

def NonDeg {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (U V : Z.Opens) (s : Γ(Z, U)) (s' : Γ(Z, V)), IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ ∧
    Z.basicOpen s = U ⊓ V ∧ Z.basicOpen s' = U ⊓ V ∧ ((U ⊓ V : Z.Opens) : Set Z).Nonempty ∧
    Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op s *
      Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s' = 1 ∧
    (Polynomial.eval₂RingHom (rA p U) s).IsIntegral ∧ (Polynomial.eval₂RingHom (rA p V) s').IsIntegral

def Concl {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Algebra A K) (B C : Subalgebra A K) (t : K), Charts B C t ∧
    (∀ x ∈ B, x ∈ C → IsIntegral A x) ∧ ChartData p B C t

def TopInt : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → (rA p ⊤).IsIntegral

def LineOpens : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z → IsAffineOpen (⊤ : Z.Opens) ∨ NonDeg p

def EmbedNonDeg : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → NonDeg p → Concl p

def EmbedAffine : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IsIntegral Z → (rA p ⊤).IsIntegral → IsAffineOpen (⊤ : Z.Opens) → Concl p

theorem GeoData_of (hT : TopInt) (hL : LineOpens) (hN : EmbedNonDeg) (hE : EmbedAffine) : GeoData := by
  intro A _ _ Z p hIL hZ
  have hI : IsIntegral Z := hZ.1
  have hTop := hT A p hIL
  rcases hL A p hIL hZ with h | h
  · exact hE A p hI hTop h
  · exact hN A p hI hTop h

end LateralTheory.E.GeometricData
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LZARStepOf
section
namespace LateralTheory.E.LZARFacts

theorem LZARStep_of : LateralTheory.E.LZIdemSumNoetherian.LZARStep := by
  intro A _ _ _ M _ _ N P hN
  have : Module.Finite A N := Module.Finite.iff_fg.mpr hN
  set I := IsLocalRing.maximalIdeal A
  set Q : Submodule A N := P.comap N.subtype
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I Q
  refine ⟨c + 1, by omega, ?_⟩
  have hQ : I ^ (c + 1) • (⊤ : Submodule A N) ⊓ Q ≤ I • Q := by
    rw [hc (c + 1) (by omega), show c + 1 - c = 1 by omega, pow_one]
    exact Submodule.smul_mono (le_refl _) inf_le_right
  intro x ⟨hx, hxP⟩
  have hmap : I ^ (c + 1) • N = (I ^ (c + 1) • (⊤ : Submodule A N)).map N.subtype := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top]
  rw [hmap] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyQ : y ∈ Q := hxP
  have := hQ ⟨hy, hyQ⟩
  have h2 : (I • Q).map N.subtype ≤ I • P := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono (le_refl _) (Submodule.map_comap_le _ _)
  exact h2 ⟨y, this, rfl⟩

end LateralTheory.E.LZARFacts
end

