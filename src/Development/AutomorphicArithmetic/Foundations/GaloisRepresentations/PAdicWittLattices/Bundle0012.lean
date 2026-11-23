module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.CoverLowOfCov
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIndepBridge
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JBCTower
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3.BaseChangeTowers

private noncomputable def cmp {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    pullback p ab ⟶ pullback p a :=
  pullback.lift (pullback.fst p ab) (pullback.snd p ab ≫ b)
    (by rw [pullback.condition, Category.assoc, h])

private theorem cmp_fst {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.fst p a = pullback.fst p ab := pullback.lift_fst _ _ _

private theorem cmp_snd {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp p a ab b h ≫ pullback.snd p a = pullback.snd p ab ≫ b := pullback.lift_snd _ _ _

private theorem cmp_isPullback {X A B C : Scheme.{0}} (p : X ⟶ A) (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp p a ab b h) (pullback.snd p ab) (pullback.snd p a) b := by
  refine IsPullback.of_right (h₁₂ := pullback.fst p a) (h₂₂ := a) (v₁₃ := p) ?_ (cmp_snd p a ab b h)
    (IsPullback.of_hasPullback p a)
  rw [cmp_fst, h]
  exact IsPullback.of_hasPullback p ab

private theorem cmp_bcMap {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    cmp q a ab b h ≫ bcMap a f hf = bcMap ab f hf ≫ cmp p a ab b h := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, bcMap_fst, cmp_fst, bcMap_fst, ← Category.assoc, cmp_fst]
  · rw [Category.assoc, Category.assoc, bcMap_snd, cmp_snd, cmp_snd, ← Category.assoc, bcMap_snd]

private theorem cmp_bcMap_isPullback {X Y A B C : Scheme.{0}} (p : X ⟶ A) (q : Y ⟶ A) (f : Y ⟶ X) (hf : f ≫ p = q)
    (a : B ⟶ A) (ab : C ⟶ A) (b : C ⟶ B) (h : b ≫ a = ab) :
    IsPullback (cmp q a ab b h) (bcMap ab f hf) (bcMap a f hf) (cmp p a ab b h) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p ab) (v₂₂ := pullback.snd p a) (h₃₁ := b) ?_
    (cmp_bcMap p q f hf a ab b h) (cmp_isPullback p a ab b h)
  rw [bcMap_snd, bcMap_snd]
  exact cmp_isPullback q a ab b h

end UpperTheory.Gal.G3.BaseChangeTowers

open UpperTheory.Gal.G3.BaseChangeTowers in
theorem UpperTheory.Gal.G3.jBCTower :
    UpperTheory.Gal.Seam.NiceBc → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BCTower := by
  intro hN k K F _ _ _ τ φ H hH
  refine ⟨hN k K τ H hH, ⟨?_⟩⟩
  have hab : Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom τ) =
      Spec.map (CommRingCat.ofHom (φ.comp τ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let a := Spec.map (CommRingCat.ofHom τ)
  let ab := Spec.map (CommRingCat.ofHom (φ.comp τ))
  let b := Spec.map (CommRingCat.ofHom φ)
  have hz : IsPullback (cmp H.q a ab b hab) (UpperTheory.Gal.Int.Geo.bcAlong H (φ.comp τ)).q
      (UpperTheory.Gal.Int.Geo.bcAlong H τ).q b := cmp_isPullback H.q a ab b hab
  refine
    { z := cmp H.q a ab b hab
      hz := hz
      y := fun j => cmp (H.s j ≫ H.q) a ab b hab
      hs := fun j => ?_
      ht := fun j => ?_ }
  · exact cmp_bcMap_isPullback H.q (H.s j ≫ H.q) (H.s j) rfl a ab b hab
  · exact cmp_bcMap H.q (H.s j ≫ H.q) (H.t j) (H.comm j) a ab b hab
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JBridgeInt
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jBridgeInt :
    UpperTheory.Gal.Seam.IntMap → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BridgeInt := by
  intro hInt E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hB γ x
  obtain ⟨φ, hφ, -⟩ := hInt E Ω l w A hA O Bw hB
  have h1 : Bw.j (algebraMap E Ω x) =
      ((algebraMap (CrystallineSemistableComparison.OK l Bw.Kw.1) Bw.Kw.1 (φ x) : Bw.Kw.1) : PadicAlgCl l) := by
    rw [hφ x]
    rfl
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ ≤ 1 := by
    rw [h1]
    have hm : ‖(((φ x : Bw.Kw.1)) : PadicAlgCl l)‖₊ ≤ 1 := (φ x).2
    exact_mod_cast hm
  have h3 : ‖γ (Bw.j (algebraMap E Ω x))‖ = ‖Bw.j (algebraMap E Ω x)‖ :=
    (GlobalTheory.Cyc.Model.isom_gal γ).norm_map_of_map_zero (map_zero _) _
  rw [h3]
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JConjBridge
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual
universe u v

theorem UpperTheory.Gal.G3.jConjBridge :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.ConjBridge := by
  intro E Ω _ _ _ _ _ l _ Gw O iR iA iT Bw τ LL' τ' hτ
  haveI := Bw.Kw.2
  haveI := LL'.2
  let τo : ↥Bw.Kw.1 →ₐ[ℚ_[l]] Om l := LL'.1.val.comp τ'
  let g : GQ l := AlgEquiv.ofBijective (τo.liftNormal (Om l)) (Algebra.IsAlgebraic.algHom_bijective _)
  have hg : ∀ x : ↥Bw.Kw.1, g (x : Om l) = ((τ' x : ↥LL'.1) : Om l) :=
    fun x => τo.liftNormal_commutes (Om l) x
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : FinExt l, K₁.1 = Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l) :=
    ⟨⟨Bw.Kw.1.map (g : Om l →ₐ[ℚ_[l]] Om l),
      LinearEquiv.finiteDimensional (IntermediateField.equivMap Bw.Kw.1 (g : Om l →ₐ[ℚ_[l]] Om l)).toLinearEquiv⟩, rfl⟩
  have hK : ∀ x, x ∈ Bw.Kw.1 ↔ g x ∈ K₁.1 := GlobalTheory.Pst.BridgeInd.mem_iff_of_map_eq hK₁
  have hcont : Continuous (fun x : Om l => g x) := (GlobalTheory.Cyc.Model.isom_gal g).continuous
  let c : ↥(GK Bw.Kw) ≃* ↥(GK K₁) :=
    { toFun := fun h => ⟨g * (h : GQ l) * g⁻¹, GlobalTheory.Pst.BridgeInd.mem_GK_conj hK h.2⟩
      invFun := fun h => ⟨g⁻¹ * (h : GQ l) * g, GlobalTheory.Pst.BridgeInd.mem_GK_conj_inv hK h.2⟩
      left_inv := fun h => Subtype.ext (by simp [mul_assoc])
      right_inv := fun h => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun h₁ h₂ => Subtype.ext (by simp [mul_assoc]) }
  have c_cont : Continuous c :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have c_symm_cont : Continuous c.symm :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  let Bw' : LocBridge l E Ω Gw O :=
    { Kw := K₁
      j := (g : Om l →+* Om l).comp Bw.j
      j_E := fun x => (hK _).1 (Bw.j_E x)
      j_dense := by
        intro y hy
        have h1 : g⁻¹ y ∈ Bw.Kw.1 := (hK _).2 (by simpa using hy)
        have h2 := image_closure_subset_closure_image hcont (Set.mem_image_of_mem _ (Bw.j_dense h1))
        have h3 : g (g⁻¹ y) = y := g.apply_symm_apply y
        simp only [h3] at h2
        refine closure_mono ?_ h2
        rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, rfl⟩
      e := Bw.e.trans c
      e_cont := c_cont.comp Bw.e_cont
      e_symm_cont := Bw.e_symm_cont.comp c_symm_cont
      e_comm := fun h x => by
        have h1 : g⁻¹ (g (Bw.j x)) = Bw.j x := g.symm_apply_apply _
        have h2 := Bw.e_comm h x
        change g (((Bw.e h : ↥(GK Bw.Kw)) : GQ l) (g⁻¹ (g (Bw.j x)))) = g (Bw.j ((h : Ω ≃ₐ[E] Ω) x))
        rw [h1, h2]
      LL := Bw.LL
      LL_split := fun σ x => by
        have hx : g⁻¹ (x : Om l) ∈ Bw.Kw.1 := (hK _).2 (by simp)
        let e₁ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥K₁.1 :=
          ((g : Om l →ₐ[ℚ_[l]] Om l).comp Bw.Kw.1.val).codRestrict K₁.1.toSubalgebra fun c => (hK _).1 c.2
        have he : e₁ ⟨g⁻¹ (x : Om l), hx⟩ = x := Subtype.ext (g.apply_symm_apply _)
        rw [← he]
        exact Bw.LL_split (σ.comp e₁) ⟨g⁻¹ (x : Om l), hx⟩
      eO := Bw.eO
      eO_alg := Bw.eO_alg
      eO_cont := Bw.eO_cont
      eO_symm_cont := Bw.eO_symm_cont }
  refine ⟨g, O, iR, iA, iT, Bw', ⟨fun x => rfl, fun h => rfl⟩, ?_⟩
  refine RingHom.ext fun x => ?_
  exact (hg ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩).trans (hτ x).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JCoverOp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

namespace UpperTheory.Gal.G3

private theorem isUnit_natCast_sp (l : ℕ) (hl : l ≠ 0) (Ω : Type) [Field Ω] [CharZero Ω] :
    IsUnit ((l : Γ(sp Ω, ⊤))) := by
  have h : IsUnit ((l : Ω)) := isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hl)
  have h2 := h.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem th_pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}} {p : X ⟶ B}
    {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) : T.pull f h = T.pull f' h' := by
  subst e; rfl

private theorem bcMap_comp' {B B' X Y Z : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : Z ⟶ B'} (u : Z ⟶ Y)
    (f : Y ⟶ X) (hu : u ≫ q = r) (hf : f ≫ p = q) (h : (u ≫ f) ≫ p = r) :
    bcMap g u hu ≫ bcMap g f hf = bcMap g (u ≫ f) h := by
  apply pullback.hom_ext
  · rw [Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, bcMap_fst, Category.assoc]
  · rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]

private theorem lmap_of_key {R : Type*} [Semiring R] {M N P : ℤ → Type*} [∀ m, AddCommMonoid (M m)]
    [∀ m, AddCommMonoid (N m)] [∀ m, AddCommMonoid (P m)] [∀ m, Module R (M m)] [∀ m, Module R (N m)]
    [∀ m, Module R (P m)] (T : ∀ m, M m →ₗ[R] N m) (C : ∀ m, N m →ₗ[R] P m) {I : Type*} [Fintype I]
    (S : I → ∀ m, M m →ₗ[R] P m) (h : ∀ m x, C m (T m x) = ∑ i, S i m x) (x : DirectSum ℤ M) :
    DirectSum.lmap C (DirectSum.lmap T x) = ∑ i, DirectSum.lmap (S i) x := by
  apply DFinsupp.ext
  intro m
  have hs : ∀ s : Finset I, (∑ i ∈ s, DirectSum.lmap (S i) x) m = ∑ i ∈ s, S i m (x m) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, DirectSum.add_apply, ih, DirectSum.lmap_apply]
  rw [hs, DirectSum.lmap_apply, DirectSum.lmap_apply]
  exact h m (x m)

private theorem coverCore (hE : EtnGood) (hS : BcSplits) (hG : BcGal) (hU : CorrUniq) (l : ℕ) [Fact l.Prime]
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [CharZero Ω] (H : HTower k) (g : H.Γ) [IsFinite (H.s g)] [Etale (H.s g)]
    (W : Scheme.{0}) (c : W ⟶ H.Z) (G : Type) [Group G] [Finite G] (a : G → (W ⟶ W)) (I : Type) [Fintype I]
    (σ : I → (W ⟶ H.Y g)) (hσ : ∀ i, (σ i ≫ H.t g) ≫ H.q = c ≫ H.q) (hGal : IsGalois c G a) (hSp : Splits (H.s g) c σ)
    (hEx : ∃ T, IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) T) :
    ∃ Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0,
      hop l H Ω g = DirectSum.lmap Tm ∧
      (∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0), pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x) ∧
      ∀ m : ℤ, Function.Injective (pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0) := by
  classical
  have hu := isUnit_natCast_sp l (Fact.out : l.Prime).ne_zero Ω
  have hGood := fun m : ℤ => hE l (sp Ω) hu m 0
  let g₀ : sp Ω ⟶ sp k := Spec.map (CommRingCat.ofHom (algebraMap k Ω))
  have hσs : ∀ j, σ j ≫ H.s g ≫ H.q = c ≫ H.q := fun j => by
    rw [← Category.assoc, hSp.choose j]
  have hac : ∀ x, a x ≫ c ≫ H.q = c ≫ H.q := fun x => by
    rw [← Category.assoc, hGal.2.2.2.2.2.choose x]
  obtain ⟨hfin, het, hspl⟩ := hS g₀ H.q (H.s g ≫ H.q) (c ≫ H.q) (H.s g) rfl c rfl I σ hσs
  have hsp' := hspl hSp
  have hgal' := hG g₀ H.q (c ≫ H.q) c rfl G a hac hGal
  choose tr htr using fun m : ℤ => (hGood m).tr (pullback.snd H.q g₀) (pullback.snd (H.s g ≫ H.q) g₀)
    (bcMap g₀ (H.s g) rfl) (bcMap_snd _ _ _)
  let Tm : ∀ m : ℤ, HQ l (sch.obj (H.geomZ Ω)) m 0 →ₗ[ℚ_[l]] HQ l (sch.obj (H.geomZ Ω)) m 0 := fun m =>
    tr m ∘ₗ (etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
  have key : ∀ (m : ℤ) (x : HQ l (sch.obj (H.geomZ Ω)) m 0),
      pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0 (Tm m x) =
        ∑ i, pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0 x := by
    intro m x
    have h1 := htr m _ (pullback.snd (c ≫ H.q) g₀) (bcMap g₀ c rfl) (bcMap_snd _ _ _) I
      (fun j => bcMap g₀ (σ j) (hσs j)) (fun j => bcMap_snd _ _ _) hsp'
      ((etn l (sp Ω) m 0).pull (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _) x)
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    have e := bcMap_comp' g₀ (σ i) (H.t g) (hσs i) (H.comm g) (hσ i)
    have h2 := (etn l (sp Ω) m 0).pull_comp (bcMap g₀ (σ i) (hσs i)) (bcMap g₀ (H.t g) (H.comm g)) (bcMap_snd _ _ _)
      (bcMap_snd _ _ _) (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x
    rw [← h2, th_pull_congr _ e _ (bcMap_snd _ _ _)]
    rfl
  have hA : IsCorrOp l (H.sΩ Ω g) (H.tΩ Ω g) (DirectSum.lmap Tm) := by
    refine ⟨_, bcMap g₀ c rfl, G, inferInstance, inferInstance, fun x => bcMap g₀ (a x) (hac x), I, inferInstance,
      fun j => bcMap g₀ (σ j) (hσs j), hgal', hsp', fun x => ?_⟩
    have e : ∀ j, bcMap g₀ (σ j) (hσs j) ≫ H.tΩ Ω g = geomMap Ω (c ≫ H.q) (σ j ≫ H.t g) (hσ j) := fun j =>
      bcMap_comp' g₀ (σ j) (H.t g) (hσs j) (H.comm g) (hσ j)
    simp only [e]
    exact lmap_of_key Tm (fun m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) c rfl)) m 0)
      (fun i m => pullHQ l (sch.map (geomMap Ω (c ≫ H.q) (σ i ≫ H.t g) (hσ i))) m 0) key x
  refine ⟨Tm, ?_, key, fun m => ?_⟩
  · have hh : hop l H Ω g = hEx.choose := by
      unfold hop
      exact dif_pos hEx
    rw [hh]
    exact hU l Ω (pullback.snd H.q g₀) _ _ _ _ hEx.choose_spec hA
  · exact (hGood m).inj _ _ (bcMap g₀ c rfl) (bcMap_snd _ _ _) G _ hgal'

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.jCoverOp :
    EtnGood → BcSplits → BcGal → CorrUniq → PositivityTheory.AutomorphicGaloisHodgeTate.G8.CoverOp := by
  intro hE hS hG hU l _ K H _ g _ _ W c G _ _ a I _ σ hσ hGal hSp hEx n
  obtain ⟨Tm, h1, h2, h3⟩ := coverCore hE hS hG hU l H g W c G a I σ hσ hGal hSp hEx
  refine ⟨h3 n, Tm n, fun x => ?_, ?_⟩
  · rw [h1, DirectSum.lmap_lof]
  · refine LinearMap.ext fun x => ?_
    rw [LinearMap.comp_apply, LinearMap.sum_apply]
    exact h2 n x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JGenIso
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.G3

theorem jGenIso : GenIso := by
  intro O O' k K _ _ _ _ _ _ φ τ h X p
  have hg : gen O' K ≫ Spec.map (CommRingCat.ofHom φ) =
      Spec.map (CommRingCat.ofHom τ) ≫ gen O k := by
    simp only [gen, ← Spec.map_comp]
    congr 1
    ext x
    simpa using h x
  refine ⟨pullbackLeftPullbackSndIso p (Spec.map (CommRingCat.ofHom φ)) (gen O' K) ≪≫
    pullback.congrHom rfl hg ≪≫
    (pullbackLeftPullbackSndIso p (gen O k) (Spec.map (CommRingCat.ofHom τ))).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd]
    rw [pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  · simp only [Iso.trans_hom, Iso.symm_hom, pullback.congrHom_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    rw [pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHodgeOpBc
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV GlobalTheory.HodgeCoh UpperTheory.Gal.G3 UpperTheory.Gal.Int.Geo
universe u v

private theorem hodgeTrace_pull_congr {F : Type} [Field F] {Y Z : Scheme.{0}} (s t : Y ⟶ Z) [IsFinite s] [Etale s]
    (p : Z ⟶ sp F) {q q' : Y ⟶ sp F} (e : q = q') (h₁ : s ≫ p = q) (h₂ : t ≫ p = q) (h₁' : s ≫ p = q') (h₂' : t ≫ p = q')
    (a b : ℕ) (x : hodgeH p a b) :
    hodgeTrace h₁ a b (hodgePull h₂ a b x) = hodgeTrace h₁' a b (hodgePull h₂' a b x) := by
  subst e; rfl

theorem UpperTheory.Gal.G3.jHodgeOpBc :
    BcSplits → HodgeTr → TrBc.{0} → HodgeOpBc := by
  intro hBc hTr hTrBc k F _ _ φ H g _ _ a b
  letI : Algebra k F := φ.toAlgebra
  obtain ⟨hF, hE, -⟩ := hBc (Spec.map (CommRingCat.ofHom φ)) H.q (H.s g ≫ H.q) (H.s g ≫ H.q) (H.s g) rfl
    (H.s g) rfl PEmpty (fun e => e.elim) (fun e => e.elim)
  refine ⟨hF, hE, hodgeTrace (bcMap_snd _ (H.s g) rfl) a b, ?_, ?_⟩
  · exact hTrBc (hodge F a b) _ H.q (H.s g ≫ H.q) (H.s g) rfl _ (hTr F a b _ _ _ (bcMap_snd _ _ _))
  · intro hF' hE' x
    exact @hodgeTrace_pull_congr _ _ _ _ _ _ hF' hE' _ _ _
      (bcMap_snd (Spec.map (CommRingCat.ofHom φ)) (H.s g) rfl) _ _ _ _ a b x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JHopLies
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo PositivityTheory.AutomorphicGaloisHodgeTate.G8
universe u v

namespace UpperTheory.Gal.G3.HopfLiesOver

private theorem isTr_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {Z Y : Scheme.{0}} (p : Z ⟶ B)
    {q q' : Y ⟶ B} (e : q = q') (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p) (h : T.IsTr p q s tr) :
    ∃ tr' : T.H q' →ₗ[R] T.H p, T.IsTr p q' s tr' ∧
      ∀ {X : Scheme.{0}} (r : X ⟶ B) (t : Y ⟶ X) (a : t ≫ r = q) (a' : t ≫ r = q') (y : T.H r),
        tr' (T.pull t a' y) = tr (T.pull t a y) := by
  subst e
  exact ⟨tr, h, fun _ _ _ _ _ => rfl⟩

private theorem unit_l (l : ℕ) {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (hl : (l : k) ≠ 0) :
    IsUnit (l : Γ(sp Ω, ⊤)) := by
  have h1 : (l : Ω) ≠ 0 := by
    intro h0
    apply hl
    apply (algebraMap k Ω).injective
    simpa using h0
  have h2 := (h1.isUnit).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using h2

private theorem low_fet (hF : FEtBasic) {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C : Cover H θ O} (D : LowData C) (g : H.Γ) : FEt ((low D).s g) (D.d g) := by
  have hp : IsPullback (pullback.fst (D.s g ≫ C.p) (gen O k)) ((low D).s g) (D.s g)
      (pullback.fst C.p (gen O k)) := by
    refine (IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback C.p (gen O k)).flip).flip
    · change IsPullback (bcMap (gen O k) (D.s g) rfl ≫ pullback.snd C.p (gen O k)) _ _ _
      rw [bcMap_snd]
      exact (IsPullback.of_hasPullback _ _).flip
    · exact bcMap_fst (gen O k) (D.s g) rfl
  exact hF.1 _ _ _ _ _ hp (D.fet g)

end UpperTheory.Gal.G3.HopfLiesOver

open UpperTheory.Gal.G3.HopfLiesOver in
theorem UpperTheory.Gal.G3.jHopLies :
    EtGood → BcGood.{1} → FEtBasic → HopSpec → LiesOp.{1} → HopLies := by
  intro hEt hBc hF hHop hLies l _ k L O _ _ _ _ hl H θ C D hN Ω _ _ g
  have hT : (etG l k Ω).Good := hBc _ _ (hEt l (sp Ω) (unit_l l hl))
  obtain ⟨d, hd⟩ := hN.2.2 g
  haveI : IsFinite (H.s g) := hd.1
  haveI : Etale (H.s g) := hd.2.1
  obtain ⟨trg, htrg⟩ := hT.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  have hfet := low_fet hF D g
  obtain ⟨tr, htr⟩ := @Th.Good.tr _ _ _ _ hT _ _ (pullback.snd C.p (gen O k))
    (pullback.snd (D.s g ≫ C.p) (gen O k)) ((low D).s g) hfet.1 hfet.2.1
    (bcMap_snd (gen O k) (D.s g) rfl)
  have hq : pullback.snd (D.s g ≫ C.p) (gen O k) = (low D).s g ≫ (low D).q :=
    (bcMap_snd (gen O k) (D.s g) rfl).symm
  obtain ⟨tr', htr', hrel⟩ := isTr_congr (etG l k Ω) _ hq _ tr htr
  rw [(hHop l hl H Ω g d hd).2 trg htrg, (hHop l hl (low D) Ω g (D.d g) hfet).2 tr' htr']
  apply LinearMap.ext
  intro x
  have e := hLies C g (D.s g) (D.t g) (D.comm g) (D.m g) (D.d g) (D.lies g) hfet (etG l k Ω) hT tr trg
    htr htrg x
  have e2 := hrel _ _ (bcMap_snd (gen O k) (D.t g) (D.comm g))
    ((bcMap_snd (gen O k) (D.t g) (D.comm g)).trans hq) x
  exact e.trans (congrArg (fun y => (D.m g : ℚ_[l]) • (etG l k Ω).pull (piK C) (piK_snd C) y) e2.symm)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLocalMat
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem isMatF_of_isMat {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (H : HTower k) (Ω : Type) [Field Ω] [Algebra k Ω]
    (θ : H.Γ → Formalism.ConjugateSelfDual.Qbar l) {d : ℕ} (ρ₁ : (Ω ≃ₐ[k] Ω) →* Matrix.GeneralLinearGroup (Fin d) (Formalism.ConjugateSelfDual.Qbar l))
    (h : UpperTheory.Gal.Int.Geo.IsMat l H Ω (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁)
    (f : (Ω ≃ₐ[k] Ω) → Matrix (Fin d) (Fin d) (Formalism.ConjugateSelfDual.Qbar l)) (hf : ∀ σ, (ρ₁ σ).val = f σ) :
    PositivityTheory.AutomorphicGaloisHodgeTate.G8.IsMatF H Ω θ f := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b, fun σ j => ?_⟩
  rw [hb σ j, hf σ]

theorem UpperTheory.Gal.G3.jLocalMat :
    UpperTheory.Gal.Seam.NiceBc → UpperTheory.Gal.Seam.HopEx → UpperTheory.Gal.Seam.LocTower → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LocalMat := by
  intro hNice hHop hLoc E Ω _ _ _ _ _ l _ H θ hN Gw O _ _ _ Bw τK hτ
  refine ⟨fun g => ⟨_, hHop l _ _ (UpperTheory.Gal.Int.Geo.bcAlong H τK) (hNice _ _ τK H hN) g⟩, ?_⟩
  intro d ρ hρ
  obtain ⟨ρ₁, hρ₁, hc⟩ := hLoc l E _ Ω (Formalism.ConjugateSelfDual.Qbar l) τK Bw.j (fun x => (hτ x).symm) H hN
    (Formalism.ConjugateSelfDual.Qbar l) θ d ρ hρ
  refine isMatF_of_isMat (UpperTheory.Gal.Int.Geo.bcAlong H τK) (Formalism.ConjugateSelfDual.Qbar l) θ ρ₁ hρ₁ _
    (fun σ => congrArg Units.val (hc _ σ (fun x => ?_)))
  rw [← Bw.e_comm]
  erw [MulEquiv.apply_symm_apply]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JLowNice
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

private theorem sq_bc {T Y S B : Scheme.{0}} (s : T ⟶ Y) (p : Y ⟶ S) (c : B ⟶ S) :
    IsPullback (pullback.fst (s ≫ p) c)
      (pullback.lift (pullback.fst (s ≫ p) c ≫ s) (pullback.snd (s ≫ p) c)
        (by rw [Category.assoc, pullback.condition]) : pullback (s ≫ p) c ⟶ pullback p c)
      s (pullback.fst p c) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := p) (h₃₁ := c) ?_ ?_
    (IsPullback.of_hasPullback p c)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (s ≫ p) c
  · rw [pullback.lift_fst]

theorem UpperTheory.Gal.G3.jLowNice :
    FEtBasic → PositivityTheory.AutomorphicGaloisHodgeTate.G8.LowNice := by
  intro hb k L _ _ H θ O _ _ C D
  haveI : Smooth C.p := C.smooth
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (pullback.snd C.p (UpperTheory.Gal.Int.Geo.gen O k))
    infer_instance
  · exact GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap O k) C.proj
  · intro g
    exact ⟨D.d g, hb.1 _ _ _ _ _ (sq_bc (D.s g) C.p (UpperTheory.Gal.Int.Geo.gen O k)) (D.fet g)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.JTrBc
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jTrBc :
    BcSplits → TrBc.{u} := by
  intro hbc B B' R _ T g Z Y p q s _ _ hs tr htr W r c hc J _ σ hσ hspl x
  have key := (hbc g p q r s hs c hc J σ hσ).2.2 hspl
  exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
    (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j)) key x
end

