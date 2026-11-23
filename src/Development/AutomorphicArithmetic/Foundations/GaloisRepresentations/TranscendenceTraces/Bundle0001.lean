module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.ImgcSpec
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

namespace UpperTheory.Gal.TranscendenceTraces.RepresentationImage

variable {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}

private theorem img_zero (τ : Fam p I J) (n : ℤ) :
    τ.IsImage (0 : Cochain ((chains R').obj (sch.obj Z)) I n) (0 : Cochain ((chains R).obj (sch.obj S)) J n) := by
  intro k s h A
  have h1 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj S) (I := J) (n := n)).1 0 0 k s h A.U A.u).2.2.1
  have h2 := ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R' (E := sch.obj Z) (I := I) (n := n)).1 0 0 k s h A.V A.v).2.2.1
  exact h1.trans ((map_zero ((τ.deg s).app A)).symm.trans (congrArg ((τ.deg s).app A) h2.symm))

private theorem img_add (τ : Fam p I J) {n : ℤ} {a a' : Cochain ((chains R').obj (sch.obj Z)) I n}
    {b b' : Cochain ((chains R).obj (sch.obj S)) J n} (h : τ.IsImage a b) (h' : τ.IsImage a' b') :
    τ.IsImage (a + a') (b + b') := by
  intro k s hs A
  rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).1 b b' k s hs A.U A.u).1, ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R').1 a a' k s hs A.V A.v).1, map_add (f := _),
    h k s hs A, h' k s hs A]

private noncomputable def imgc (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : Cocycle ((chains R).obj (sch.obj S)) J n :=
  Cocycle.mk ((hI R' R τ n).1 α.1).exists.choose (n + 1) rfl (by
    have h := (hI R' R τ n).2 (n + 1) rfl _ _ ((hI R' R τ n).1 α.1).exists.choose_spec
    rw [Cocycle.δ_eq_zero] at h
    exact ((hI R' R τ (n + 1)).1 0).unique h (img_zero τ (n + 1)))

private theorem imgc_spec (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) : τ.IsImage α.1 (imgc hI τ α).1 :=
  ((hI R' R τ n).1 α.1).exists.choose_spec

private theorem imgc_eq (hI : ImgBasic) (τ : Fam p I J) {n : ℤ}
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : imgc hI τ α = β :=
  Cocycle.ext (((hI R' R τ n).1 α.1).unique (imgc_spec hI τ α) h)

private noncomputable def opMap (hI : ImgBasic) (τ : Fam p I J) (n : ℤ) :
    CohomologyClass ((chains R').obj (sch.obj Z)) I n →+ CohomologyClass ((chains R).obj (sch.obj S)) J n :=
  CohomologyClass.descAddMonoidHom
    (AddMonoidHom.mk' (fun α => CohomologyClass.mk (imgc hI τ α)) (fun α α' => by
      rw [← CohomologyClass.mk_add]; congr 1
      exact imgc_eq hI τ _ _ (img_add τ (imgc_spec hI τ α) (imgc_spec hI τ α'))))
    (by
      rintro ⟨a, ha⟩ ⟨n', hn', a', rfl⟩
      change CohomologyClass.mk _ = 0
      rw [CohomologyClass.mk_eq_zero_iff]
      obtain ⟨b, hb, -⟩ := (hI R' R τ n').1 a'
      exact ⟨n', hn', b, ((hI R' R τ n).1 _).unique ((hI R' R τ n').2 n hn' _ _ hb) (imgc_spec hI τ ⟨_, ha⟩)⟩)

private theorem op_spec (hI : ImgBasic) (τ : Fam p I J) (n : ℤ)
    (α : Cocycle ((chains R').obj (sch.obj Z)) I n) (β : Cocycle ((chains R).obj (sch.obj S)) J n)
    (h : τ.IsImage α.1 β.1) : τ.op n (CohomologyClass.mk α) = CohomologyClass.mk β :=
  pick_spec (P := fun c : CohomologyClass ((chains R').obj (sch.obj Z)) I n →+
      CohomologyClass ((chains R).obj (sch.obj S)) J n =>
    ∀ (α : Cocycle _ I n) (β : Cocycle _ J n), τ.IsImage α.1 β.1 →
      c (CohomologyClass.mk α) = CohomologyClass.mk β)
    ⟨opMap hI τ n, fun α β h => congrArg CohomologyClass.mk (imgc_eq hI τ α β h)⟩ α β h

end UpperTheory.Gal.TranscendenceTraces.RepresentationImage

open UpperTheory.Gal.TranscendenceTraces.RepresentationImage in
theorem UpperTheory.Gal.TranscendenceTraces.rpOp_of :
    ImgBasic → RpOp := by
  intro hI Z S p R' R _ _ I J τ n x a hx
  obtain ⟨α, rfl, rfl⟩ := hx
  exact ⟨imgc hI τ α, (op_spec hI τ n α _ (imgc_spec hI τ α)).symm, imgc_spec hI τ α 0 n (by simp) (Sq.self p)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.OpEqOf
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.opEq_of :
    FL → RpBasic → RpOp → OpEq := by
  intro hFL hB hOp Q Z S p _ F G t τ τ' hτ hτ' n
  ext x
  obtain ⟨a, ha⟩ := (hB (ZMod Q) (res (ZMod Q) F) Z n).1 x
  have hd := (hB (ZMod Q) (res (ZMod Q) F) Z n).2.1 x a ha
  have h1 := hOp _ _ τ n x a ha
  have h2 := hOp _ _ τ' n x a ha
  obtain ⟨y, hy⟩ := (hFL Q p F G t).2 τ τ' hτ hτ' (Sq.self p) (n - 1) n (n + 1)
    (sub_add_cancel n 1) rfl a hd
  exact ((hB (ZMod Q) (res (ZMod Q) G) S n).2.2.1 _ _ _ _ h1 h2).1.mpr ⟨y, hy⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PArtSum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_local (Ω R : Type) [Field Ω] [IsAlgClosed Ω] [CommRing R] [Algebra Ω R]
    [Module.Finite Ω R] [IsLocalRing R] : Module.length R R = Module.finrank Ω R := by
  have h1 := IsLocalRing.length_restrictScalars Ω R R
  have h2 : Module.length (IsLocalRing.ResidueField Ω) (IsLocalRing.ResidueField R) = 1 := by
    rw [← Module.length_eq_of_surjective (S := Ω) (M := IsLocalRing.ResidueField R)
      IsLocalRing.residue_surjective]
    haveI : Module.Finite Ω (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (IsScalarTower.toAlgHom Ω R (IsLocalRing.ResidueField R)).toLinearMap
        IsLocalRing.residue_surjective
    rw [Module.length_eq_finrank,
      Module.finrank_of_bijective_algebraMap IsAlgClosed.algebraMap_bijective_of_isIntegral]
    rfl
  rw [h2, mul_one, Module.length_eq_finrank] at h1
  exact h1.symm

theorem UpperTheory.Gal.TranscendenceTraces.artSum_of : ArtSum := by
  intro Ω B _ _ _ _ _
  classical
  haveI : IsArtinianRing B := IsArtinianRing.of_finite Ω B
  haveI : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have hbij := PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp
    (inferInstance : DiscreteTopology (PrimeSpectrum B))
  let e : B ≃ₗ[Ω] PrimeSpectrum.PiLocalization B :=
    LinearEquiv.ofBijective
      ((PrimeSpectrum.toPiLocalization B).restrictScalars Ω).toLinearMap hbij
  haveI : Module.Finite Ω (PrimeSpectrum.PiLocalization B) := Module.Finite.equiv e
  haveI : ∀ P : PrimeSpectrum B, Module.Finite Ω (Localization.AtPrime P.asIdeal) := fun P =>
    Module.Finite.of_surjective
      (LinearMap.proj (R := Ω) (φ := fun P : PrimeSpectrum B => Localization.AtPrime P.asIdeal) P)
      (fun x => ⟨Pi.single P x, by simp⟩)
  rw [finsum_eq_sum_of_fintype, e.finrank_eq, Module.finrank_pi_fintype]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [length_local Ω (Localization.AtPrime P.asIdeal)]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.chart_of :
    Chart := by
  intro Z S p _ A _ u
  haveI : IsAffine (pullback p u) := isAffine_of_isAffineHom (pullback.snd p u)
  let V := pullback p u
  let e : Spec Γ(V, ⊤) ≅ V := V.isoSpec.symm
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := Spec.preimage (e.hom ≫ pullback.snd p u)
  have hφ : Spec.map φ = e.hom ≫ pullback.snd p u := Spec.map_preimage _
  letI alg : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = e.hom ≫ pullback.snd p u := hφ
  refine ⟨Γ(V, ⊤), inferInstance, alg, e.hom ≫ pullback.fst p u, ?_, ?_⟩
  · have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤)))) := by
      rw [hφ']; infer_instance
    have h2 := (IsFinite.SpecMap_iff _).1 hfin
    exact RingHom.finite_algebraMap.1 h2
  · rw [hφ']
    exact IsPullback.of_iso (IsPullback.of_hasPullback p u) e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrBCQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem pullHQ_comp' (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n i : ℤ) :
    pullHQ l (sch.map (f ≫ g)) n i = pullHQ l (sch.map f) n i ∘ₗ pullHQ l (sch.map g) n i := by
  simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem UpperTheory.Gal.TranscendenceTraces.corrBCQ_of :
    TrBCQ → CorrBCQ := by
  intro hT l _ n i S' Y' S Y c' c g g' v hpb hf hw hl
  haveI := c.fin
  haveI := c'.fin
  simp only [Corr.opQ]
  rw [← LinearMap.comp_assoc, hT l n i v c'.p c.p g c.w hpb c.wt hl, ← hw,
    LinearMap.comp_assoc, LinearMap.comp_assoc, ← pullHQ_comp', ← pullHQ_comp', hf]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrCompQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrCompQ_of :
    CycComp → WtBC → WtComp → TrBCQ → TrCompQ → CorrCompQ := by
  intro hC hBC hWC hTB hTC S Y X c d
  haveI := c.fin
  haveI := d.fin
  have pb := IsPullback.of_hasPullback d.p c.f
  have hbw := hBC _ _ d.p c.f d.w pb d.wt
  have hw := hWC (pullback.snd d.p c.f) c.p (Wt.comap (pullback.fst d.p c.f) d.w) c.w hbw c.wt
  let e : Corr S X := ⟨pullback d.p c.f, pullback.snd d.p c.f ≫ c.p, pullback.fst d.p c.f ≫ d.f,
    Wt.mul (pullback.snd d.p c.f) (Wt.comap (pullback.fst d.p c.f) d.w) c.w, inferInstance, hw⟩
  refine ⟨e, pullback.fst d.p c.f, pullback.snd d.p c.f, pb, rfl, rfl, rfl, ?_, ?_⟩
  · exact hC c d e _ _ pb rfl rfl rfl
  · intro l _ n i hl hl2
    have hpull : pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
        pullHQ l (sch.map (pullback.fst d.p c.f)) n i ∘ₗ pullHQ l (sch.map d.f) n i := by
      simp only [pullHQ, Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]
    have key := hTB l n i _ _ d.p c.f d.w pb d.wt hl2
    show trHQ l (pullback.snd d.p c.f ≫ c.p) _ n i ∘ₗ pullHQ l (sch.map (pullback.fst d.p c.f ≫ d.f)) n i =
      (trHQ l c.p c.w n i ∘ₗ pullHQ l (sch.map c.f) n i) ∘ₗ (trHQ l d.p d.w n i ∘ₗ pullHQ l (sch.map d.f) n i)
    rw [hTC l n i _ _ _ _ hbw c.wt hl, hpull]
    refine LinearMap.ext fun v => ?_
    simp only [LinearMap.comp_apply]
    exact congrArg (trHQ l c.p c.w n i) (LinearMap.congr_fun key _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrEq_of :
    ImageFin → TrRel → TrPush → WtPush → CorrEq := by
  intro hIF hTR hTP hWP q _ n i S Y B bS bY _ _ ι _ c m hc hq D hD hcyc y
  obtain ⟨G, pG, fG, h, hpG, hh, hp, hf, hmono⟩ :=
    hIF bS bY ι (fun a => (c a).Z) (fun a => (c a).p) (fun a => (c a).f) (fun a => (c a).fin) hc
  haveI := hpG
  have hwt : ∀ a, IsWt (h a ≫ pG) (c a).w := by
    intro a
    rw [hp a]
    exact (c a).wt
  have key : ∀ a, (c a).op q n i y =
      tr pG (Wt.push (h a) (c a).w) q n i (pull (ZMod q) (sch.map fG) (tw q i) n y) := by
    intro a
    haveI := hh a
    rw [← hTP q n i (h a) pG (c a).w (hwt a) hq, ← pull_comp, ← Functor.map_comp, hf a]
    simp only [Corr.op, AddMonoidHom.comp_apply]
    rw [hp a]
  simp only [key]
  refine hTR q n i pG ι (fun a => Wt.push (h a) (c a).w) m
    (fun a => by haveI := hh a; exact hWP (h a) pG (c a).w (hwt a)) hq D hD ?_ _
  intro Ω _ _ z hz
  rw [← hcyc Ω (z ≫ pG) (z ≫ fG) hz]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have hs : fib (h a) z = {z' | z' ≫ (c a).p = z ≫ pG ∧ z' ≫ (c a).f = z ≫ fG} := by
    ext z'
    simp only [fib, Set.mem_setOf_eq]
    constructor
    · rintro rfl
      exact ⟨by rw [Category.assoc, hp a], by rw [Category.assoc, hf a]⟩
    · rintro ⟨h1, h2⟩
      apply hmono
      · rw [Category.assoc, hp a, h1]
      · rw [Category.assoc, hf a, h2]
  simp only [Wt.push, Corr.cyc]
  rw [hs]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrEqQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem hl_rel (hTr : TrHl) (hC : CorrEq) (l : ℕ) [Fact l.Prime] (n i : ℤ) {S Y B : Scheme.{0}} (bS : S ⟶ B) (bY : Y ⟶ B)
    [IsSeparated bY] [LocallyOfFiniteType bY] (ι : Type) [Fintype ι] (c : ι → Corr S Y) (m : ι → ℤ)
    (hb : ∀ a, (c a).f ≫ bY = (c a).p ≫ bS) (hl : IsUnit (l : Γ(S, ⊤))) (D : Set S) (hD : Dense D)
    (hz : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y), pt x ∈ D →
      ∑ a, m a * (c a).cyc Ω x y = 0) :
    ∑ a, m a • (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) = 0 := by
  refine LinearMap.ext fun x => Subtype.ext (funext fun k => ?_)
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  have h := hC (l ^ k) n i bS bY ι c m hb hq D hD hz (x.1 k)
  have e : ∀ a, ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k =
      (c a).op (l ^ k) n i (x.1 k) := fun a => by
    haveI := (c a).fin
    exact hTr l n i (c a).p (c a).w (c a).wt hl _ k
  rw [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h
  change m a • ((trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) x).1 k = _
  rw [e a]
  rfl

theorem UpperTheory.Gal.TranscendenceTraces.corrEqQ_of :
    TrHl → CorrEq → CorrEqQ := by
  intro hTr hC l _ n i S Y B bS bY _ _ ι _ c m hb hl D hD hz
  have h := hl_rel hTr hC l n i bS bY ι c m hb hl D hD hz
  have e : ∀ a, Corr.opQ l (c a) n i = LinearMap.baseChangeHom ℤ_[l] ℚ_[l] _ _
      (trHl l (c a).p (c a).w n i ∘ₗ pullHl l (sch.map (c a).f) n i) := by
    intro a
    rw [LinearMap.baseChangeHom_apply, LinearMap.baseChange_comp]
    rfl
  simp only [e, Int.cast_smul_eq_zsmul]
  simp_rw [← map_zsmul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, h, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCorrGraphQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.corrGraphQ_of :
    TrIdQ → WtLin → CorrGraphQ := by
  intro hT hW S Y f d
  refine ⟨⟨S, 𝟙 S, f, Wt.const S d, inferInstance, hW.2.2 (𝟙 S) d⟩, ?_, ?_, ?_⟩
  · intro B bY
    simp
  · intro Ω _ _ x y
    constructor
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = {x} := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Category.comp_id]
        constructor
        · exact fun hz => hz.1
        · rintro rfl
          exact ⟨rfl, h⟩
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = d
      rw [hs, finsum_mem_singleton]
      rfl
    · intro h
      have hs : {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y} = ∅ := by
        ext z
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Category.comp_id]
        rintro ⟨rfl, h'⟩
        exact h h'
      change ∑ᶠ z ∈ {z : gp Ω ⟶ S | z ≫ 𝟙 S = x ∧ z ≫ f = y}, Wt.const S d Ω z = 0
      rw [hs, finsum_mem_empty]
  · intro l _ n i hl
    change (trHQ l (𝟙 S) (Wt.const S d) n i).comp (pullHQ l (sch.map f) n i) = _
    rw [hT l n i S d hl, LinearMap.smul_comp, LinearMap.id_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCountEx
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.countEx_of :
    CountEx := by
  classical
  intro T Z S p π ι σ m hsym
  refine ⟨fun Ω _ _ z => if h : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π then
      ∑ᶠ (j : ι) (_ : j ∈ {j | h.choose ≫ σ j = z}), m j else 0, ?_⟩
  intro Ω _ _ x z hz
  have hex : ∃ x : gp Ω ⟶ T, z ≫ p = x ≫ π := ⟨x, hz⟩
  simp only [dif_pos hex]
  set x₀ := hex.choose with hx₀
  have h₀ : z ≫ p = x₀ ≫ π := hex.choose_spec
  obtain ⟨e, he⟩ := hsym Ω x x₀ (hz.symm.trans h₀)
  symm
  apply finsum_mem_eq_of_bijOn e
  · refine ⟨?_, ?_, ?_⟩
    · intro j hj
      simp only [Set.mem_setOf_eq] at hj ⊢
      rw [← (he j).1, hj]
    · intro a _ b _ hab
      exact e.injective hab
    · intro k hk
      simp only [Set.mem_setOf_eq] at hk
      refine ⟨e.symm k, ?_, by simp⟩
      simp only [Set.mem_setOf_eq]
      rw [(he (e.symm k)).1, Equiv.apply_symm_apply, hk]
  · intro j _
    exact ((he j).2).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PCoverOne
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.coverOne_of :
    CoverOne := by
  intro R _ F G f V b h
  have hd : ∀ (V' W : Scheme.{0}) (g : V' ⟶ V) (k : W ⟶ V'),
      (∃ a : Sec F V', Sec.map f a = Sec.res g b) → ∃ a : Sec F W, Sec.map f a = Sec.res (k ≫ g) b := by
    rintro V' W g k ⟨a, ha⟩
    exact ⟨Sec.res k a, by rw [map_res, ha, res_res]⟩
  have h2 := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover V (fun W k => ∃ a : Sec F W, Sec.map f a = Sec.res k b) hd).1 h
  choose Wf k _ het hx a ha using h2
  obtain ⟨a', ha'⟩ := (GlobalTheory.T.sec_sigma_res_bijective R F Wf).2 a
  refine ⟨∐ Wf, Sigma.desc k, a', ?_, ?_, ?_⟩
  · have : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale) fun i => het i
  · refine ⟨fun x => ?_⟩
    obtain ⟨y, hy⟩ := hx x
    refine ⟨Sigma.ι Wf x y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, hy]
  · refine (GlobalTheory.T.sec_sigma_res_bijective R G Wf).1 (funext fun i => ?_)
    show Sec.res (Sigma.ι Wf i) (Sec.map f a') = Sec.res (Sigma.ι Wf i) (Sec.res (Sigma.desc k) b)
    have e : Sec.res (Sigma.ι Wf i) a' = a i := congrFun ha' i
    rw [← map_res, e, ha, res_res, Sigma.ι_desc]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamBC
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.famBC_of :
    FamBC := by
  intro q i Z' S' Z S v p' p g w h τ hτ
  let push : Sq p' → Sq p := fun A =>
    { U := A.U, V := A.V, u := A.u ≫ g, v := A.v ≫ v, r := A.r,
      pb := A.pb.paste_horiz h }
  let pushTo : ∀ {A B : Sq p'}, A.To B → (push A).To (push B) := fun {A B} t =>
    { g := t.g, k := t.k,
      hu := by simp only [push, ← Category.assoc, t.hu],
      hv := by simp only [push, ← Category.assoc, t.hv],
      hr := t.hr }
  let τ' : Fam p' (res (ZMod q) (tw q i)) (res (ZMod q) (tw q i)) :=
    { deg := fun s =>
        { app := fun A => (τ.deg s).app (push A),
          nat := fun {A B} t a => (τ.deg s).nat (pushTo t) a },
      comm := fun A s t a => τ.comm (push A) s t a }
  refine ⟨τ', ?_, ?_⟩
  · intro A a
    obtain ⟨b, hb1, hb2⟩ := hτ (push A) a
    refine ⟨b, hb1, ?_⟩
    intro Ω _ _ x
    have := hb2 Ω x
    simpa only [IsSum, Wt.comap, push, Category.assoc] using this
  · intro n a
    let t : (push (Sq.self p')).To (Sq.self p) :=
      { g := g, k := v,
        hu := by simp [push, Sq.self],
        hv := by simp [push, Sq.self],
        hr := by simpa [push, Sq.self] using h.w }
    exact ((τ.deg n).nat t a).symm
end

