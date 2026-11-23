module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0363
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0058

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PRpBasic
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem cohomologyClass_mk_zsmul {R : Type} [CommRing R] {K L : Cx R} {n : ℤ} (d : ℤ) (a : Cocycle K L n) :
    CohomologyClass.mk (d • a) = d • CohomologyClass.mk a :=
  map_zsmul (CohomologyClass.mkAddMonoidHom K L n) d a

private theorem ev_cocycle_add {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (α β : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((α + β : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) +
        ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_add]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ _ 0 n h0 X (𝟙 X)).1

private theorem ev_cocycle_zsmul {R : Type} [CommRing R] (I : Cx R) (X : Scheme) (n : ℤ) (h0 : -((0 : ℕ) : ℤ) + n = n)
    (d : ℤ) (α : Cocycle ((chains R).obj (sch.obj X)) I n) :
    ev ((d • α : Cocycle ((chains R).obj (sch.obj X)) I n) : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) =
      d • ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
  rw [Cocycle.coe_smul]
  exact ((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)).1 _ 0 0 n h0 X (𝟙 X)).2.2.2 d

theorem UpperTheory.Gal.TranscendenceTraces.rpBasic_of :
    RpBasic := by
  intro R _ I X n
  have ev_lin := GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := sch.obj X) (I := I) (n := n)
  have key := fun (α : Cocycle ((chains R).obj (sch.obj X)) I n) =>
    (GlobalTheory.T.cocycle_ev_d_eq_zero_and_mk_eq_zero_iff R X I (n - 1) n (n + 1) (by ring) rfl).2 α
  have h0 : -((0 : ℕ) : ℤ) + n = n := by simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    exact ⟨_, α, rfl, rfl⟩
  · rintro x a ⟨α, -, rfl⟩
    exact (key α).1
  · rintro x x' a a' ⟨α, rfl, ha⟩ ⟨β, rfl, hb⟩
    subst ha hb
    have hiff : CohomologyClass.mk α = CohomologyClass.mk β ↔
        ∃ y, Sec.map (I.d (n - 1) n) y =
          ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) -
            ev (β : Cochain ((chains R).obj (sch.obj X)) I n) 0 n h0 X (𝟙 X) := by
      rw [← sub_eq_zero, ← CohomologyClass.mk_sub, (key (α - β)).2, Cocycle.coe_sub,
        (ev_lin.1 (α : Cochain _ I n) β 0 n h0 X (𝟙 X)).2.1]
    refine ⟨hiff, fun h => hiff.2 ⟨0, ?_⟩, ⟨α + β, CohomologyClass.mk_add α β, ev_cocycle_add I X n h0 α β⟩,
      fun d => ⟨d • α, cohomologyClass_mk_zsmul d α, ev_cocycle_zsmul I X n h0 d α⟩⟩
    rw [h, sub_self]
    exact map_zero _
  · rintro Y f x a ⟨α, rfl, rfl⟩
    refine ⟨zcomp (Cocycle.ofHom ((chains R).map (sch.map f))) α (zero_add n), rfl, ?_⟩
    have h1 := ev_lin.2.2.2.1 (sch.map f) (α : Cochain _ I n) 0 n h0 Y (𝟙 Y)
    have h2 := ev_lin.2.1 (α : Cochain _ I n) 0 n h0 Y X f (𝟙 X)
    exact h1.trans h2.symm
  · rintro R' _ J ρ x a ⟨α, rfl, rfl⟩
    obtain ⟨β, hβ⟩ := SemiMap.image_exists ρ (sch.obj X) n α
    exact ⟨β, (SemiMap.op_spec ρ (sch.obj X) n α β hβ).symm, hβ 0 n h0 X (𝟙 X)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private lemma exists_hom {R Ω : Type} [CommRing R] [Field Ω] (x : gp Ω ⟶ Spec (CommRingCat.of R)) :
    ∃ φ : R →+* Ω, x = Spec.map (CommRingCat.ofHom φ) := by
  refine ⟨(Spec.preimage x).hom, ?_⟩
  simp [Spec.map_preimage]

private lemma map_comp' {R S Ω : Type} [CommRing R] [CommRing S] [CommRing Ω] (a : R →+* S) (φ : S →+* Ω) :
    Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom a) =
      Spec.map (CommRingCat.ofHom (φ.comp a)) := by
  rw [← Spec.map_comp]
  rfl

private lemma map_inj' {R S : Type} [CommRing R] [CommRing S] {f g : R →+* S}
    (h : Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom g)) : f = g := by
  have := Spec.map_injective h
  simpa using congrArg CommRingCat.Hom.hom this

private lemma pt_map {R Ω : Type} [CommRing R] [Field Ω] (f : R →+* Ω) :
    (pt (Spec.map (CommRingCat.ofHom f))).asIdeal = RingHom.ker f := by
  ext a
  simp only [pt]
  show a ∈ (Ideal.comap f (IsLocalRing.closedPoint Ω).asIdeal) ↔ _
  simp [IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

theorem UpperTheory.Gal.TranscendenceTraces.splitCover_of :
    SplitField → GalTrans → SplitCover := by
  intro hsf hgt A B _ _ _ _ _ _
  obtain ⟨L, _, _, _, _, _, _, hfin, hsp⟩ := hsf A B
  set C := integralClosure A L
  have hinj : Function.Injective (algebraMap A C) := by
    intro a b hab
    have h1 : algebraMap A L a = algebraMap A L b := by
      have := congrArg (fun c : C => (c : L)) hab
      simpa using this
    rw [IsScalarTower.algebraMap_apply A (FractionRing A) L a,
      IsScalarTower.algebraMap_apply A (FractionRing A) L b] at h1
    exact IsFractionRing.injective A (FractionRing A) ((algebraMap (FractionRing A) L).injective h1)
  have key : ∀ {Ω : Type} [Field Ω] (φ : C →+* Ω),
      RingHom.ker (φ.comp (algebraMap A C)) = ⊥ → RingHom.ker φ = ⊥ := by
    intro Ω _ φ h
    apply Ideal.eq_bot_of_comap_eq_bot (R := A)
    change Ideal.comap (algebraMap A C) (RingHom.ker φ) = ⊥
    rw [RingHom.comap_ker]
    exact h
  refine ⟨Spec (CommRingCat.of C), Spec.map (CommRingCat.ofHom (algebraMap A C)), (B →ₐ[A] C),
    fun j => Spec.map (CommRingCat.ofHom (j : B →+* C)),
    fun j => (⟨RingHom.ker (j : B →+* C), RingHom.ker_isPrime _⟩ : PrimeSpectrum B),
    ?_, ?_, hfin, ?_, ?_, ?_⟩
  · exact IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)
  · refine ⟨fun p => ?_⟩
    have hp : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := C) p.asIdeal ⊥ (by
      rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
      exact bot_le)
    exact ⟨⟨Q, hQ⟩, PrimeSpectrum.ext hQc⟩
  · intro j
    rw [map_comp']
    congr 2
    exact j.comp_algebraMap
  · intro Ω _ x x' hxx
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨φ', rfl⟩ := exists_hom x'
    simp only [map_comp'] at hxx
    obtain ⟨g, hg⟩ := hgt A L Ω φ φ' (map_inj' hxx)
    let e : (B →ₐ[A] C) ≃ (B →ₐ[A] C) :=
      { toFun := fun j => (g.symm : C →ₐ[A] C).comp j
        invFun := fun j => (g : C →ₐ[A] C).comp j
        left_inv := fun j => by
          ext b
          simp
        right_inv := fun j => by
          ext b
          simp }
    refine ⟨e, fun j => ⟨?_, ?_⟩⟩
    · simp only [map_comp']
      congr 2
      ext b
      simp [e, hg]
    · apply PrimeSpectrum.ext
      ext b
      simp [e]
  · intro Ω _ x z hz hbot
    obtain ⟨φ, rfl⟩ := exists_hom x
    obtain ⟨ζ, rfl⟩ := exists_hom z
    simp only [map_comp'] at hz
    rw [map_comp', pt_map] at hbot
    have hφ : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr (key φ hbot)
    have hiff : ∀ j : B →ₐ[A] C, Spec.map (CommRingCat.ofHom φ) ≫
        Spec.map (CommRingCat.ofHom (j : B →+* C)) = Spec.map (CommRingCat.ofHom ζ) ↔
        φ.comp (j : B →+* C) = ζ := by
      intro j
      rw [map_comp']
      exact ⟨map_inj', fun h => by rw [h]⟩
    obtain ⟨j0, hj0, hu⟩ := hsp Ω φ ζ ((RingHom.injective_iff_ker_eq_bot _).mpr hbot) (map_inj' hz)
    refine ⟨⟨j0, (hiff j0).2 hj0, fun j hj => hu j ((hiff j).1 hj)⟩, fun j hj => ?_⟩
    rw [hiff] at hj
    apply PrimeSpectrum.ext
    rw [pt_map, ← hj]
    ext b
    simp [map_eq_zero_iff _ hφ]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSplitField
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.splitField_of :
    SplitField :=
  _root_.UpperTheory.Reformulated.B.SplittingFieldConstruction.splitField_of
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PStalkSum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem length_congr {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  have : RingHomSurjective (e : R →+* S) := ⟨e.surjective⟩
  let f : R →ₛₗ[(e : R →+* S)] S :=
    { toFun := e
      map_add' := e.map_add
      map_smul' := fun a b => by simp [smul_eq_mul] }
  rw [Module.length, Module.length, WithBot.unbot_inj]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

theorem UpperTheory.Gal.TranscendenceTraces.stalkSum_of :
    Chart → ArtSum → StalkSum := by
  intro hC hA V Ω _ _ r _
  obtain ⟨B, _, _, v, hfin, hpb⟩ := hC r Ω (𝟙 (gp Ω))
  have hv : IsIso v := hpb.isIso_fst_of_isIso
  have hr : r = inv v ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω B)) := by
    rw [IsIso.eq_inv_comp, hpb.w, Category.comp_id]
  have hfl : Flat (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [Flat.SpecMap_iff]
    simpa [RingHom.flat_algebraMap_iff] using (inferInstance : Module.Flat Ω B)
  have hfi : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap Ω B))) := by
    rw [IsFinite.SpecMap_iff]
    simpa [RingHom.finite_algebraMap] using hfin
  have hR : Scheme.Hom.finrank r (IsLocalRing.closedPoint Ω) = Module.finrank Ω B := by
    rw [hr, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_SpecMap_algebraMap,
      Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hs : ∀ P : PrimeSpectrum B, IsIso (v.stalkMap P) :=
    (IsOpenImmersion.iff_isIso_stalkMap (f := v)).mp inferInstance |>.2
  have e2 : ∀ P : PrimeSpectrum B,
      V.presheaf.stalk (v P) ≃+* Localization.AtPrime P.asIdeal := fun P =>
    ((asIso (v.stalkMap P)) ≪≫ Spec.stalkIso (CommRingCat.of B) P).commRingCatIsoToRingEquiv
  rw [hR, ← hA Ω B, ← finsum_comp_equiv v.homeomorph.toEquiv]
  refine finsum_congr fun P => ?_
  change (Module.length (V.presheaf.stalk (v P)) (V.presheaf.stalk (v P))).toNat = _
  rw [length_congr (e2 P)]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumComp_of :
    FibFin → SumComp := by
  intro hF W V U r p _ _ Ω _ x M _ c
  have hset : fib (r ≫ p) x = ⋃ y ∈ fib p x, fib r y := by
    ext z
    simp only [fib, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hz
      exact ⟨z ≫ r, by rw [Category.assoc]; exact hz, rfl⟩
    · rintro ⟨y, hy, hz⟩
      rw [← Category.assoc, hz, hy]
  have hdisj : (fib p x).PairwiseDisjoint (fun y => fib r y) := by
    intro y₁ _ y₂ _ hne
    refine Set.disjoint_left.mpr ?_
    intro z h₁ h₂
    apply hne
    simp only [fib, Set.mem_setOf_eq] at h₁ h₂
    rw [← h₁, ← h₂]
  change ∑ᶠ z ∈ fib (r ≫ p) x, c z = ∑ᶠ y ∈ fib p x, ∑ᶠ z ∈ fib r y, c z
  rw [hset]
  exact finsum_mem_biUnion hdisj (hF p Ω x) (fun y _ => hF r Ω y)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PSumNat
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.sumNat_of :
    SumNat := by
  intro R _ F Z S p w A B t a b hB Ω _ _ x
  rw [res_res, hB Ω (x ≫ t.g)]
  symm
  refine finsum_mem_eq_of_bijOn (fun z => z ≫ t.k) (fib_bijOn t.isPullback x) ?_
  intro z _
  simp only [res_res, Category.assoc, t.hv]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrBCQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trBCQ_of :
    TrHl → TrBC → WtBC → TrBCQ := by
  intro hHl hBC hWt l _ n i Z' S' Z S v p' p g _ w hpb hw hl
  haveI : IsFinite p' := MorphismProperty.of_isPullback (P := @IsFinite) hpb inferInstance
  have hw' : IsWt p' (Wt.comap v w) := hWt v p' p g w hpb hw
  have hl' : IsUnit ((l : ℕ) : Γ(S', ⊤)) := by
    have := hl.map g.appTop.hom
    rwa [map_natCast] at this
  have key : pullHl l (sch.map g) n i ∘ₗ trHl l p w n i =
      trHl l p' (Wt.comap v w) n i ∘ₗ pullHl l (sch.map v) n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    show (pull (ZMod (l ^ k)) (sch.map g) (tw (l ^ k) i) n) ((trHl l p w n i x).1 k) =
      (trHl l p' (Wt.comap v w) n i (pullHl l (sch.map v) n i x)).1 k
    rw [hHl l n i p w hw hl x k, hHl l n i p' (Wt.comap v w) hw' hl' _ k]
    exact hBC (l ^ k) n i v p' p g w hpb hw hk (x.1 k)
  unfold trHQ pullHQ
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, key]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrChar
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trChar_of :
    FL → OpEq → TrSum → PtInj → TrChar := by
  intro hFL hOp hTS hPI q _ i Z S p _ w hw hq
  have hOver : (trFam p w q i).Over (tr0 p w q i) := by
    unfold trFam
    exact GlobalTheory.EtC.pick_spec (hFL q p (tw q i) (tw q i) (tr0 p w q i)).1
  refine ⟨hOver, ?_, ?_⟩
  · intro A a
    exact ⟨(tr0 p w q i).app A a, hOver A a, hTS q i p w hw hq A a⟩
  · intro τ hτ n
    have hτo : τ.Over (tr0 p w q i) := by
      intro A a
      obtain ⟨b, hb, hs⟩ := hτ A a
      have hbe : b = (tr0 p w q i).app A a := by
        apply hPI q i A.U
        intro Ω _ _ x
        rw [hs Ω x, hTS q i p w hw hq A a Ω x]
      rw [hb, hbe]
    exact hOp q p (tw q i) (tw q i) (tr0 p w q i) (trFam p w q i) τ hOver hτo n
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrComp
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trComp_of :
    TrChar → FamComp → WtComp → RpBasic → RpOp → TrComp := by
  intro hChar hFam hWc hRp hOp q _ n i W Z S r p _ _ w' w hr hp hq x
  have hrp : IsWt (r ≫ p) (Wt.mul r w' w) := hWc r p w' w hr hp
  have hqZ : IsUnit ((q : ℕ) : Γ(Z, ⊤)) := by
    have := hq.map p.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨_, hsr, _⟩ := hChar q i r w' hr hqZ
  obtain ⟨_, hsp, _⟩ := hChar q i p w hp hq
  obtain ⟨σ, hσ, hσeq⟩ := hFam q i r p w' w (trFam r w' q i) (trFam p w q i) hsr hsp
  rw [(hChar q i (r ≫ p) _ hrp hq).2.2 σ hσ n, (hChar q i p w hp hq).2.2 _ hsp n,
    (hChar q i r w' hr hqZ).2.2 _ hsr n]
  obtain ⟨a, ha⟩ := (hRp (ZMod q) (res (ZMod q) (tw q i)) W n).1 x
  have h1 := hOp _ _ (trFam r w' q i) n x a ha
  have h2 := hOp _ _ (trFam p w q i) n _ _ h1
  have h3 := hOp _ _ σ n x a ha
  rw [hσeq n a] at h3
  exact ((hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.1 _ _ _ _ h3 h2).2.1 rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrCompQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trCompQ_of :
    TrHl → TrComp → WtComp → TrCompQ := by
  intro hHl hC hWC l _ n i W Z S r p _ _ w' w hr hp hl
  have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
    simpa using hl.map p.appTop.hom
  have hcomp : trHl l (r ≫ p) (Wt.mul r w' w) n i = trHl l p w n i ∘ₗ trHl l r w' n i := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext k
    haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hlk : IsUnit ((l ^ k : ℕ) : Γ(S, ⊤)) := by
      rw [Nat.cast_pow]
      exact hl.pow k
    rw [LinearMap.comp_apply, hHl l n i p w hp hl, hHl l n i r w' hr hlZ,
      hHl l n i (r ≫ p) _ (hWC r p w' w hr hp) hl]
    exact hC (l ^ k) n i r p w' w hr hp hlk _
  unfold trHQ
  rw [hcomp, LinearMap.baseChange_comp]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDeg
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trDeg_of :
    TrPush → TrLin → TrDeg := by
  intro hP hL q _ n i Z S p _ w d hw hq hpush x
  have h1 := hP q n i p (𝟙 S) w (by simpa using hw) hq x
  simp only [Category.comp_id] at h1
  rw [h1, hpush]
  exact (hL q n i).2.2 S d hq x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PTrDegQ
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem trHl_pullHl (hHl : TrHl) (hDeg : TrDeg) (l : ℕ) [Fact l.Prime] (n i : ℤ) {Z S : Scheme.{0}} (p : Z ⟶ S)
    [IsFinite p] (w : Wt Z) (d : ℤ) (hw : IsWt p w) (hl : IsUnit (l : Γ(S, ⊤))) (hd : w.push p = Wt.const S d)
    (x : Hl l (sch.obj S) n i) :
    trHl l p w n i (pullHl l (sch.map p) n i x) = d • x := by
  apply Subtype.ext
  funext k
  have hk : IsUnit ((↑(l ^ k) : ℕ) : Γ(S, ⊤)) := by
    rw [Nat.cast_pow]
    exact hl.pow k
  show (trHl l p w n i (pullHl l (sch.map p) n i x)).1 k = (d • x).1 k
  rw [hHl l n i p w hw hl _ k]
  exact hDeg (l ^ k) n i p w d hw hk hd (x.1 k)

theorem UpperTheory.Gal.TranscendenceTraces.trDegQ_of :
    TrHl → TrDeg → TrDegQ := by
  intro hHl hDeg l _ n i Z S p _ w d hw hl hd
  apply LinearMap.ext
  intro z
  unfold trHQ pullHQ
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
      trHl_pullHl hHl hDeg l n i p w d hw hl hd y]
    simp only [TensorProduct.tmul_smul, LinearMap.smul_apply, LinearMap.id_apply]
    exact (Int.cast_smul_eq_zsmul ℚ_[l] d _).symm
  | add u v hu hv =>
    simp only [map_add (f := _)] at hu hv ⊢
    rw [hu, hv]
end

