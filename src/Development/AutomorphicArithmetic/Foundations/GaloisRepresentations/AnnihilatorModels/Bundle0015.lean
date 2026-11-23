module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsQuotientByFiniteGroupOfPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1423
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MConstSub
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory GlobalTheory.PointQuot

private theorem constObj_hom_ext {S : Scheme} {I : Type} {Z : Over S} (f₁ f₂ : constObj S I ⟶ Z)
    (h : ∀ c, PointQuot.constPt S c ≫ f₁ = PointQuot.constPt S c ≫ f₂) : f₁ = f₂ := by
  ext : 1
  apply Sigma.hom_ext
  intro c
  have := congrArg Over.Hom.left (h c)
  exact this

theorem UpperTheory.Gal.crystallineComparison.Mod.constSub_of : ConstSub := by
  intro K _ A _ hsep Γ hfin
  have hinj : Function.Injective (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) := Subtype.val_injective
  haveI hmono : Mono (constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A))) := mono_constDesc _ hinj
  obtain ⟨hG, hmon⟩ := exists_grpObj_constObj (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) Γ
    Subtype.range_coe
  have hsplit : FinEt.IsSplitOfRank (constObj (Sp K) Γ).hom (Nat.card Γ) := by
    rw [FinEt.isSplitOfRank_iff_exists_iso]
    refine ⟨Sigma.reindex (Finite.equivFin Γ).symm (fun _ => Sp K), ?_⟩
    apply Sigma.hom_ext
    intro j
    have h := Sigma.ι_reindex_hom (Finite.equivFin Γ).symm (fun _ : Γ => Sp K) j
    simp only [constObj, Over.mk_hom]
    rw [← Category.assoc]
    erw [h]
    simp
  haveI := hsplit.isFinite
  haveI := hsplit.etale
  refine ⟨constObj (Sp K) Γ, hG, constDesc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)), hmon, hmono,
    hsplit.isFinite, hsplit.etale, ?_, ?_, ?_, ?_⟩
  · refine ⟨hsplit.isFinite, (inferInstance : Flat (constObj (Sp K) Γ).hom), ?_, hsplit.finrank_eq⟩
    let c0 : Γ := ⟨1, Γ.one_mem⟩
    have hw : (PointQuot.constPt (Sp K) c0).left ≫ (toUnit (constObj (Sp K) Γ)).left = 𝟙 _ := by
      rw [← Over.comp_left]
      simp
    refine ⟨fun y => ⟨(PointQuot.constPt (Sp K) c0).left y, ?_⟩⟩
    rw [← Scheme.Hom.comp_apply, hw]
    rfl
  · intro g
    constructor
    · rintro ⟨y, hy⟩
      let z : (𝟙_ (Over (Sp K))).left := (⊥ : PrimeSpectrum K)
      obtain ⟨V, hzV, c, hc⟩ := locally_const_desc (Subtype.val : Γ → (𝟙_ (Over (Sp K)) ⟶ A)) y z
      haveI : Nonempty (openObj (𝟙_ (Over (Sp K))) V).left := ⟨⟨z, hzV⟩⟩
      haveI := epi_toUnit (openObj (𝟙_ (Over (Sp K))) V)
      have e : openι (𝟙_ (Over (Sp K))) V = toUnit _ := toUnit_unique _ _
      rw [hy, e] at hc
      have := (cancel_epi _).1 hc
      rw [this]
      exact c.2
    · intro hg
      exact ⟨PointQuot.constPt (Sp K) (⟨g, hg⟩ : Γ), constPt_desc _ _⟩
  · intro α hα
    apply constObj_hom_ext
    intro c
    rw [← Category.assoc, constPt_desc]
    exact (hα _ c.2).trans (comp_one _).symm
  · intro α hα
    refine ⟨constDesc (fun c : Γ => PointQuot.constPt (Sp K) (⟨c.1 ≫ α, hα _ c.2⟩ : Γ)), ?_⟩
    apply constObj_hom_ext
    intro c
    simp only [← Category.assoc, constPt_desc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCotanOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem tangent_of_form {κ B : Type} [Field κ] [CommRing B] [Algebra κ B] (ε : B →ₐ[κ] κ)
    (d : B →ₗ[κ] κ) (h1 : d 1 = 0) (h2 : ∀ x ∈ RingHom.ker ε.toRingHom ^ 2, d x = 0) :
    ∃ v : B →ₐ[κ] DualNumber κ, (TrivSqZeroExt.fstHom κ κ κ).comp v = ε ∧ ∀ x, (v x).snd = d x := by
  have hmem : ∀ x, x - algebraMap κ B (ε x) ∈ RingHom.ker ε.toRingHom := by
    intro x
    rw [RingHom.mem_ker]
    change ε (x - algebraMap κ B (ε x)) = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have key : ∀ x y, d (x * y) = ε x * d y + ε y * d x := by
    intro x y
    have hm : (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) ∈
        RingHom.ker ε.toRingHom ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hmem x) (hmem y)
    have hz := h2 _ hm
    have e : x * y = (x - algebraMap κ B (ε x)) * (y - algebraMap κ B (ε y)) + ε y • x
        + ε x • y - (ε x * ε y) • (1 : B) := by
      simp only [Algebra.smul_def, map_mul, mul_one]
      ring
    rw [e, map_sub, map_add (f := _), map_add (f := _), hz, map_smul, map_smul, map_smul, h1]
    simp only [smul_eq_mul]
    ring
  let f : B →ₗ[κ] DualNumber κ :=
    { toFun := fun x => TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x)
      map_add' := by
        intro x y
        ext <;> simp <;> ring
      map_smul' := by
        intro a x
        ext <;> simp }
  have hf : ∀ x, f x = TrivSqZeroExt.inl (ε x) + TrivSqZeroExt.inr (d x) := fun _ => rfl
  refine ⟨AlgHom.ofLinearMap f ?_ ?_, ?_, ?_⟩
  · rw [hf]
    ext <;> simp [h1]
  · intro x y
    rw [hf, hf, hf]
    ext <;> simp [key] <;> ring
  · ext x
    simp [hf]
  · intro x
    simp [hf]

theorem UpperTheory.Gal.crystallineComparison.Mod.cotanOne_of :
    CotanOne := by
  intro κ B _ _ _ ε v₀ hall
  classical
  let m := RingHom.ker ε.toRingHom
  let s : B → κ := fun x => (v₀ x).snd
  have hs_sub : ∀ x y, s (x - y) = s x - s y := by
    intro x y
    simp [s]
  have hs_smul : ∀ (a : κ) x, s (a • x) = a * s x := by
    intro a x
    simp [s]
  have hkill : ∀ y ∈ m, s y = 0 → y ∈ m ^ 2 := by
    intro y hy hsy
    by_contra hy2
    let P : Submodule κ B := (m ^ 2).restrictScalars κ ⊔ Submodule.span κ {(1 : B)}
    have hyP : y ∉ P := by
      intro hyP
      obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.1 hyP
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hw
      have hz' : z ∈ m ^ 2 := hz
      have hzm : z ∈ m := Ideal.pow_le_self two_ne_zero hz'
      have e1 : ε y = ε z + a * ε 1 := by
        rw [← hzw, map_add (f := _), map_smul, smul_eq_mul]
      have hεy : ε y = 0 := hy
      have hεz : ε z = 0 := hzm
      simp only [hεy, hεz, _root_.map_one, zero_add] at e1
      have ha : a = 0 := by simpa using e1.symm
      apply hy2
      rw [← hzw, ha, zero_smul, add_zero]
      exact hz'
    obtain ⟨d, hdy, hdP⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyP inferInstance
    have hdP' : ∀ p ∈ P, d p = 0 := by
      intro p hp
      have h3 : d p ∈ Submodule.map d P := ⟨p, hp, rfl⟩
      rw [hdP, Submodule.mem_bot] at h3
      exact h3
    have hd1 : d 1 = 0 := hdP' 1 (Submodule.mem_sup_right (Submodule.mem_span_singleton_self 1))
    have hd2 : ∀ x ∈ m ^ 2, d x = 0 := fun x hx => hdP' x (Submodule.mem_sup_left hx)
    obtain ⟨v, hv, hvd⟩ := tangent_of_form ε d hd1 hd2
    obtain ⟨c, hc⟩ := hall v hv
    apply hdy
    rw [← hvd, hc]
    change c * s y = 0
    rw [hsy, mul_zero]
  by_cases hex : ∃ t ∈ m, s t ≠ 0
  · obtain ⟨t, ht, hst⟩ := hex
    refine ⟨t, ht, ?_⟩
    intro x hx
    have hy : x - (s x / s t) • t ∈ m := by
      refine m.sub_mem hx ?_
      rw [Algebra.smul_def]
      exact m.mul_mem_left _ ht
    have hsy : s (x - (s x / s t) • t) = 0 := by
      rw [hs_sub, hs_smul, div_mul_cancel₀ _ hst, sub_self]
    have h2 := hkill _ hy hsy
    have e : x = (s x / s t) • t + (x - (s x / s t) • t) := by abel
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left ?_) (Ideal.mem_sup_right h2)
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self t)
  · push_neg at hex
    refine ⟨0, m.zero_mem, ?_⟩
    intro x hx
    exact Ideal.mem_sup_right (hkill x hx (hex x hx))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFFRead
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem count_eq (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (hab : IsAbelianScheme A)
    (K : Over S) (i : K ⟶ A) (hm : Mono i) (hfin : IsFinite K.hom) (hfl : Flat K.hom) (c : ℕ) (hi : i ^ c = 1)
    (P : ∀ T : Over S, (T ⟶ A) → Prop) (hP : ∀ (T : Over S) (g : T ⟶ A), InSub i g ↔ P T g)
    (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] [IsAlgClosed (FractionRing V)] (hc : (c : V) ≠ 0)
    (z : Sp V ⟶ S) (B : Type) [CommRing B] [Algebra V B] [Module.Finite V B] [Module.Free V B] (k : Sp B ⟶ K.left)
    (hk : IsPullback k (spMap (algebraMap V B)) K.hom z) :
    Module.finrank V B = Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} := by
  haveI := hfin
  haveI := hfl
  have hcF : ((c : FractionRing V)) ≠ 0 := by
    intro h
    apply hc
    apply IsFractionRing.injective V (FractionRing V)
    simpa using h
  let pt : Sp (FractionRing V) := (⊥ : PrimeSpectrum (FractionRing V))
  have h1 := GlobalTheory.T.finrank_finiteFlat_torsion_subscheme_eq_card_points S A hab K i c hm hfin hfl hi (FractionRing V) hcF
    (spMap (algebraMap V (FractionRing V)) ≫ z) pt
  have h2 := Scheme.Hom.finrank_of_isPullback k (spMap (algebraMap V B)) K.hom z hk
    (spMap (algebraMap V (FractionRing V)) pt)
  have h3 := Scheme.Hom.finrank_SpecMap_algebraMap V B (spMap (algebraMap V (FractionRing V)) pt)
  rw [Scheme.Hom.comp_apply] at h1
  have h4 : Nat.card {g : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ A // P _ g} =
      Nat.card (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ z) ⟶ K) := by
    refine Nat.card_congr (Equiv.ofBijective (fun g => ⟨g ≫ i, (hP _ _).1 ⟨g, rfl⟩⟩) ⟨?_, ?_⟩).symm
    · intro a b hab'
      exact (cancel_mono i).1 (congrArg Subtype.val hab')
    · rintro ⟨g, hg⟩
      obtain ⟨y, hy⟩ := (hP _ _).2 hg
      exact ⟨y, Subtype.ext hy⟩
  rw [h4, ← h1, ← h2]
  unfold spMap at h3 ⊢
  rw [h3, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem fFRead_of : AlgOf → FFRead := by
  intro hAlg S A _ _ hab P hRep c hc V _ _ _ _ hcV z A' φ hpb P' hP'
  obtain ⟨K, i, hm, hfin, hfl, hiP⟩ := hRep
  haveI := hfin
  haveI := hfl
  have hi : i ^ c = 1 := hc K i ((hiP K i).1 ⟨𝟙 _, by simp⟩)
  obtain ⟨BV, _, _, kV, _, _, hkV⟩ := hAlg S K.left K.hom hfin hfl V z
  have hcount := count_eq S A hab K i hm hfin hfl c hi P hiP V hcV z BV kV hkV
  obtain ⟨Bk, _, _, kk, _, _, hkk⟩ :=
    hAlg S K.left K.hom hfin hfl (IsLocalRing.ResidueField V) (resPt V ≫ z)
  have hr : Module.finrank (IsLocalRing.ResidueField V) Bk = Module.finrank V BV := by
    let q : Sp (IsLocalRing.ResidueField V) := (⊥ : PrimeSpectrum (IsLocalRing.ResidueField V))
    have e1 := Scheme.Hom.finrank_of_isPullback kk _ K.hom (resPt V ≫ z) hkk q
    have e2 := Scheme.Hom.finrank_of_isPullback kV _ K.hom z hkV (resPt V q)
    have e3 := Scheme.Hom.finrank_SpecMap_algebraMap (IsLocalRing.ResidueField V) Bk q
    have e4 := Scheme.Hom.finrank_SpecMap_algebraMap V BV (resPt V q)
    rw [Scheme.Hom.comp_apply] at e1
    unfold spMap at e1 e2
    rw [e3, Module.rankAtStalk_eq_finrank_of_free] at e1
    rw [e4, Module.rankAtStalk_eq_finrank_of_free] at e2
    exact e1.trans e2.symm
  have wsq : (kk ≫ i.left) ≫ A.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) ≫ (resPt V ≫ z) := by
    rw [Category.assoc, Over.w i]
    exact hkk.w
  have hlf : hpb.lift _ _ wsq ≫ φ = kk ≫ i.left := hpb.lift_fst _ _ wsq
  have hls : hpb.lift _ _ wsq ≫ A'.hom = spMap (algebraMap (IsLocalRing.ResidueField V) Bk) :=
    hpb.lift_snd _ _ wsq
  have hlm : Mono (hpb.lift _ _ wsq) := by
    constructor
    intro X a b hab'
    apply hkk.hom_ext
    · haveI := Over.mono_left_of_mono i
      have h1 := congrArg (· ≫ φ) hab'
      simp only [Category.assoc, hlf] at h1
      simpa only [Category.assoc] using (cancel_mono i.left).1 (by simpa only [Category.assoc] using h1)
    · have h1 := congrArg (· ≫ A'.hom) hab'
      simpa only [Category.assoc, hls] using h1
  refine ⟨Bk, inferInstance, inferInstance, inferInstance, inferInstance, hr.trans hcount,
    Over.homMk (U := Over.mk (spMap (algebraMap (IsLocalRing.ResidueField V) Bk))) (hpb.lift _ _ wsq) hls,
    ?_, ?_⟩
  · constructor
    intro X a b hab'
    ext
    exact (cancel_mono (hpb.lift _ _ wsq)).1 (by simpa using congrArg Over.Hom.left hab')
  · intro T g
    have hw : (g.left ≫ φ) ≫ A.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
      rw [Category.assoc, hpb.w, ← Category.assoc, Over.w g]
      rfl
    rw [hP' T g (Over.homMk (g.left ≫ φ) hw) rfl, ← hiP]
    constructor
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw2 : (y.left ≫ kk) ≫ K.hom = (Over.mk (T.hom ≫ resPt V ≫ z)).hom := by
        rw [Category.assoc, hkk.w]
        simpa using congrArg (· ≫ resPt V ≫ z) (Over.w y)
      refine ⟨Over.homMk (y.left ≫ kk) hw2, ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left, Category.assoc]
      rw [← hyl, Category.assoc, hlf]
    · rintro ⟨y, hy⟩
      have hyl := congrArg Over.Hom.left hy
      simp only [Over.comp_left, Over.homMk_left] at hyl
      have hw3 : y.left ≫ K.hom = T.hom ≫ resPt V ≫ z := by
        simpa using Over.w y
      refine ⟨Over.homMk (hkk.lift y.left T.hom hw3) (by simpa using hkk.lift_snd _ _ hw3), ?_⟩
      ext
      simp only [Over.comp_left, Over.homMk_left]
      apply hpb.hom_ext
      · rw [Category.assoc, hlf, ← Category.assoc, hkk.lift_fst, hyl]
      · rw [Category.assoc, hls, hkk.lift_snd]
        simpa using (Over.w g).symm

end UpperTheory.Gal.crystallineComparison.Mod
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobFin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isIntegral_of_pow {R : Type} [CommRing R] (φ : R →+* R) {n : ℕ} (hn : 0 < n)
    (hφ : ∀ y, φ y = y ^ n) : φ.IsIntegral := by
  intro y
  refine ⟨Polynomial.X ^ n - Polynomial.C y, Polynomial.monic_X_pow_sub_C y hn.ne', ?_⟩
  simp [hφ]

private theorem isIntegralHom_absFrob_affine (p f : ℕ) (hp : Nat.Prime p) (Y : Scheme) [IsAffine Y] (h : ((p : ℕ) : Γ(Y, ⊤)) = 0) :
    IsIntegralHom (GlobalTheory.SS.FrobField.absFrob Y p f hp h) := by
  have hk : ((p : ℕ) : Γ(Sp Γ(Y, ⊤), ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Γ(Y, ⊤) h
  have hsp : GlobalTheory.SS.FrobField.absFrob (Sp Γ(Y, ⊤)) p f hp hk =
      spMap (GlobalTheory.SS.FrobField.powHom Γ(Y, ⊤) p f hp h) :=
    GlobalTheory.SS.FrobField.absFrob_spec Γ(Y, ⊤) p f hp hk _ (fun _ => rfl)
  have hnat := GlobalTheory.SS.FrobField.absFrob_nat Y.isoSpec.hom p f hp h hk
  have he : GlobalTheory.SS.FrobField.absFrob Y p f hp h =
      Y.isoSpec.hom ≫ GlobalTheory.SS.FrobField.absFrob (Sp Γ(Y, ⊤)) p f hp hk ≫ Y.isoSpec.inv := by
    rw [← Category.comp_id (GlobalTheory.SS.FrobField.absFrob Y p f hp h), ← Y.isoSpec.hom_inv_id,
      ← Category.assoc, hnat, Category.assoc]
    rfl
  rw [he, hsp]
  have hi : IsIntegralHom (spMap (GlobalTheory.SS.FrobField.powHom Γ(Y, ⊤) p f hp h)) :=
    (IsIntegralHom.SpecMap_iff).mpr (isIntegral_of_pow _ (pow_pos hp.pos f) (fun _ => rfl))
  infer_instance

theorem UpperTheory.Gal.crystallineComparison.Mod.frobFin_of :
    FrobFin := by
  intro p f hp κ _ _ _ X s hs h
  haveI : Fact p.Prime := ⟨hp⟩
  have hk0 : ((p : ℕ) : κ) = 0 := CharP.cast_eq_zero κ p
  have hκ : ((p : ℕ) : Γ(Sp κ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp κ hk0
  have hsp : GlobalTheory.SS.FrobField.absFrob (Sp κ) p f hp hκ = spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) :=
    GlobalTheory.SS.FrobField.absFrob_spec κ p f hp hκ _ (fun _ => rfl)
  have hb : Function.Bijective (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) := by
    constructor
    · intro x y hxy
      change x ^ p ^ f = y ^ p ^ f at hxy
      have hz : (x - y) ^ p ^ f = 0 := by rw [sub_pow_char_pow, hxy, sub_self]
      exact sub_eq_zero.mp (pow_eq_zero_iff (pow_pos hp.pos f).ne' |>.mp hz)
    · intro y
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos hp.pos f)
      exact ⟨x, hx⟩
  let e : κ ≃+* κ := RingEquiv.ofBijective _ hb
  haveI : IsIso (spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0)) := by
    change IsIso (Spec.map (RingEquiv.toCommRingCatIso e).hom)
    infer_instance
  refine ⟨?_, ⟨fun x => ⟨x, rfl⟩⟩⟩
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  constructor
  · rw [@HasAffineProperty.eq_targetAffineLocally @IsIntegralHom _ IsIntegralHom.hasAffineProperty]
    intro U
    haveI : IsAffine U.1.toScheme := U.2
    apply (@HasAffineProperty.iff_of_isAffine @IsIntegralHom _ IsIntegralHom.hasAffineProperty _ _ _ _).mp
    have hU : ((p : ℕ) : Γ(U.1.toScheme, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_of_hom U.1.ι h
    have heq : GlobalTheory.SS.FrobField.absFrob X p f hp h ⁻¹ᵁ U.1 = U.1 := rfl
    have hres : GlobalTheory.SS.FrobField.absFrob X p f hp h ∣_ U.1 =
        (X.isoOfEq heq).hom ≫ GlobalTheory.SS.FrobField.absFrob U.1.toScheme p f hp hU := by
      rw [← cancel_mono U.1.ι, morphismRestrict_ι, Category.assoc,
        GlobalTheory.SS.FrobField.absFrob_nat U.1.ι p f hp hU h, ← Category.assoc, Scheme.isoOfEq_hom_ι]
    rw [hres]
    haveI := isIntegralHom_absFrob_affine p f hp U.1.toScheme hU
    infer_instance
  · have hc : GlobalTheory.SS.FrobField.absFrob X p f hp h ≫ s = s ≫ spMap (GlobalTheory.SS.FrobField.powHom κ p f hp hk0) := by
      rw [GlobalTheory.SS.FrobField.absFrob_nat s p f hp h hκ, hsp]
    haveI : LocallyOfFiniteType (GlobalTheory.SS.FrobField.absFrob X p f hp h ≫ s) := by
      rw [hc]
      infer_instance
    exact locallyOfFiniteType_of_comp _ s
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobRing_of :
    FrobRing := by
  intro p f hp κ _ _ A _ B Λ _ _ _ _ i hi ε₀ hε ν g hg
  have hpΛ : (p : Λ) = 0 := by
    have h := map_natCast (algebraMap κ Λ) p
    rw [CharP.cast_eq_zero κ p, map_zero] at h
    exact h.symm
  let σ : Λ →+* Λ := GlobalTheory.SS.FrobField.powHom Λ p f hp hpΛ
  have hσ : ∀ c, σ c = c ^ p ^ f := fun _ => rfl
  have h0 : (p : Γ(Sp Λ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Λ hpΛ
  have hfr : GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 = spMap σ :=
    GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h0 σ hσ
  have hmono : Mono i.left := (Over.forget _).map_mono i
  have h1 : (1 : algPt κ Λ ⟶ A).left = spMap (algebraMap κ Λ) ≫ spMap ε₀.toRingHom ≫ i.left := by
    have e : (1 : algPt κ Λ ⟶ A) = toUnit (algPt κ Λ) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ A) := by
      simp
    have e2 : (toUnit (algPt κ Λ)).left = spMap (algebraMap κ Λ) := by
      have := Over.w (toUnit (algPt κ Λ))
      simpa using this
    rw [e, Over.comp_left, e2]
    exact congrArg (spMap (algebraMap κ Λ) ≫ ·) hε.symm
  have sc : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (u : R →+* S) (v : S →+* T),
      spMap v ≫ spMap u = spMap (v.comp u) := by
    intro R S T _ _ _ u v
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have key : FrobKill p f hp g ↔ σ.comp ν.toRingHom = (σ.comp (algebraMap κ Λ)).comp ε₀.toRingHom := by
    constructor
    · intro h
      have h2 := h h0
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ (1 : algPt κ Λ ⟶ A).left at h2
      rw [hfr, hg, h1] at h2
      simp only [← Category.assoc] at h2
      have h3 := (cancel_mono i.left).1 h2
      rw [sc, sc, sc] at h3
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    · intro h hh
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ (1 : algPt κ Λ ⟶ A).left
      rw [show GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh = spMap σ from hfr, hg, h1]
      simp only [← Category.assoc]
      rw [sc, sc, sc, h]
  rw [key]
  constructor
  · intro h x hx
    have := RingHom.congr_fun h x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, map_zero] at this
    rw [hσ] at this
    exact this
  · intro h
    ext x
    have hy : ε₀ (x - algebraMap κ B (ε₀ x)) = 0 := by
      simp
    have h2 := h _ hy
    have h3 : σ (ν (x - algebraMap κ B (ε₀ x))) = 0 := by rw [hσ]; exact h2
    rw [map_sub, map_sub, AlgHom.commutes, sub_eq_zero] at h3
    simpa using h3
end

