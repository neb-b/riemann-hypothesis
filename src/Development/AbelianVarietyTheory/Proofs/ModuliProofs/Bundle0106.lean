module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0097
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FixTorsionOfForallGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem eq_id_of_forall_geometric_fibre (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (A : Over S)
    [GrpObj A] (hA : IsAbelianScheme A) (σ : A ⟶ A) (h0 : η[A] ≫ σ = η[A])
    (hσ : ∀ t : S, ∃ (S' X : Scheme.{0}) (f : S' ⟶ S) (g : X ⟶ A.left) (q : X ⟶ S') (y : S'),
      f y = t ∧ IsPullback g q A.hom f ∧ g ≫ σ.left = g) : σ = 𝟙 A := by
  have := hA.proper
  let u : A ⟶ A := σ * (𝟙 A)⁻¹
  have hu : ∀ {T : Over S} (x : T ⟶ A), x ≫ σ = x → x ≫ u = 1 := fun x hx => by
    simp only [u, MonObj.comp_mul, GrpObj.comp_inv, hx, Category.comp_id, mul_inv_cancel]
  have hη : (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ A.hom = 𝟙 S := Over.w η[A]
  have hfib : ∀ (t : S) (x : A.left), A.hom x = t →
      u.left x = (η[A] : 𝟙_ (Over S) ⟶ A).left t := by
    intro t x hx
    obtain ⟨S', X, f, g, q, y, hy, hg, e⟩ := hσ t
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hg x y (hx.trans hy.symm)
    let x₀ : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk g rfl
    have h₀ : g ≫ u.left = (g ≫ A.hom) ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left :=
      congrArg (fun q => q.left) (hu x₀ (Over.OverMorphism.ext e))
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx]
  have key : u.left = A.hom ≫ (η[A] : 𝟙_ (Over S) ⟶ A).left ≫ u.left := by
    refine Scheme.hom_ext_of_forall _ _ fun x => ?_
    obtain ⟨V, hV, e⟩ := local_rigidity _ _ _ A.hom _ u.left hη inferInstance
      (surjective_app_of_isAbelianScheme hG A hA) (A.hom x) _ (hfib _)
    exact ⟨A.hom ⁻¹ᵁ V, hV, e⟩
  have h₁ : u = toUnit A ≫ η[A] ≫ u := Over.OverMorphism.ext key
  rw [hu η[A] h0, MonObj.comp_one] at h₁
  exact mul_inv_eq_one.1 h₁

theorem serre_any_base (hL : Out.Laws) {S : Scheme.{0}} (P : Out.PolAV S) (M : ℕ) (hM : 3 ≤ M)
    (σ : P.A ≅ P.A) (hσ : IsMonHom σ.hom)
    (hloc : ∀ p : S, ∃ V : S.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]).pull
        (P.A.hom ⁻¹ᵁ V).ι), c.IsGen)
    (hfix : ∀ (T : Over S) (x : T ⟶ P.A), x ^ M = 1 → x ≫ σ.hom = x) : σ.hom = 𝟙 P.A := by
  refine eq_id_of_forall_geometric_fibre hL.globalFns P.A P.isAb σ.hom (IsMonHom.one_hom σ.hom)
    fun t => ?_
  obtain ⟨V, hV, c, hc⟩ := hloc t
  have hf : ∀ y, S.fromSpecResidueField t y = t := Scheme.fromSpecResidueField_apply t
  obtain ⟨X, g, q, hg, e⟩ := comp_aut_eq_of_serre_baseChange hL.polBaseChange
    (S.fromSpecResidueField t) P M
    (fun P' σ' h' ⟨c', hc'⟩ hx => hL.serre _ P' M hM σ' h' (fun _ => ⟨⊤, trivial,
      gen_chartPull (chartPullPull _ _ _ rfl) c' hc'⟩) hx)
    σ hσ V (fun y => by rw [hf]; exact hV) c hc hfix
  exact ⟨_, X, _, g, q, (default : PrimeSpectrum (S.residueField t)), hf _, hg, e⟩

theorem fix_torsion_of_forall_geometric {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ)
    [Etale (Out.mulA A n).left] (σ : A ⟶ A) [IsMonHom σ]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (x : Over.mk t ⟶ A),
      x ^ n = 1 → x ≫ σ = x) (T : Over S) (x : T ⟶ A) (hx : x ^ n = 1) : x ≫ σ = x := by
  have e : ∀ y : T ⟶ A, y ≫ Out.mulA A n = y ^ n := fun y => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
  have hx' : (x ≫ σ) ^ n = 1 := by
    rw [← MonObj.pow_comp, hx, MonObj.one_comp]
  apply Over.OverMorphism.ext
  refine eq_of_range_equalizer_ι_eq_univ (Out.mulA A n).left
    (by rw [← Over.comp_left, ← Over.comp_left, e, e, hx, hx']) (Set.eq_univ_of_forall fun z => ?_)
  let K : Type := AlgebraicClosure (T.left.residueField z)
  let j : Sp K ⟶ T.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField z) K)) ≫
      T.left.fromSpecResidueField z
  have hj : ∀ p, j p = z := fun p =>
    (Scheme.Hom.comp_apply _ _ p).trans (Scheme.fromSpecResidueField_apply z _)
  let j' : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j rfl
  have h₁ := h K (j ≫ T.hom) (j' ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  replace h₁ := (Category.assoc _ _ _).symm.trans h₁
  exact range_subset_range_equalizer_ι j (congrArg (fun q => q.left) h₁)
    ⟨(default : PrimeSpectrum K), hj _⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem obj_aut_fix_geometric_torsion {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o : Obj D l b s) (θ : o.t.G ≅ o.t.G) [IsMonHom θ.hom]
    (hact : ∀ a, o.t.act.act a ≫ θ.hom = θ.hom ≫ o.t.act.act a)
    (hL : LBIso o.t.PP.L (o.t.PP.L.pull θ.hom.left)) (heta : ∀ a, o.eta a ≫ θ.hom = o.eta a)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (y : Over.mk x ⟶ o.t.G)
    (hy : y ^ l.M = 1) : y ≫ θ.hom = y := by
  obtain ⟨w, hw⟩ := hL
  obtain ⟨-, I, -, -, hI⟩ := o.geom k x (Spec.preimage (x ≫ s)).hom (Spec.map_preimage _).symm
  refine ObjRigid.fix_torsion l I (IsMonHom.monoidHom θ.hom (Over.mk x)) (fun a z => ?_)
    (fun z z' c c' h h' => ?_) (fun a ha => ?_) y hy
  · show (z ≫ _) ≫ θ.hom = (z ≫ θ.hom) ≫ _
    rw [Category.assoc, hact, Category.assoc]
  · have : Subsingleton (Over.mk x).left := inferInstanceAs (Subsingleton (Sp k))
    exact H1.unitOn_injective
      (ObjRigid.weil_eq_of_iso (T := Over.mk x) o.t.PP.isLB θ w hw _ z z' _ _ h h')
  · show _ ≫ θ.hom = _
    rw [← hI a ha, Category.assoc, heta]

theorem obj_rigid_of_pol : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), IsAbelianScheme o.t.G ∧ SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (D.p + D.q)) o.t.G.hom ∧ Out.Rigidified o.t.G o.t.PP.L ∧ Out.Sym o.t.G o.t.PP.L) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (o : Obj D l b s) (o' : Obj D l b' s') (f : S' ⟶ S), ∀ m m' : SABMap o'.t o.t f, (∀ a, ∃ σ, (o'.eta a).left ≫ m.φ = σ ∧ (o'.eta a).left ≫ m'.φ = σ) → m.φ = m'.φ := by
  intro hL hpol E _ _ _ H D l B B' _ _ b b' S S' s s' o o' f m m' heta
  obtain ⟨hA, hd, hr, hs⟩ := hpol E H D l B' b' S' s' o'
  obtain ⟨θ, hθ, hφ, hact, -, w, hw, -⟩ := sabMap_iso m m' rfl rfl
  have hη : ∀ a, o'.eta a ≫ θ.hom = o'.eta a := fun a => by
    obtain ⟨σ, h₁, h₂⟩ := heta a
    apply Over.OverMorphism.ext
    apply m'.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc]
      exact (congrArg _ hφ).trans (h₁.trans h₂.symm)
    · rw [Over.w, Over.w]
  let P : Out.PolAV S' :=
    { A := o'.t.G, g := _, smoothDim := hd, L := o'.t.PP.L, isLB := o'.t.PP.isLB,
      ample := o'.ample, ktriv := o'.ktriv, isAb := hA, rigid := hr, sym := hs }
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hMu : IsUnit (l.M : Γ(S', ⊤)) := by
    simpa using (b'.unit _ hM).map ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ s'.appTop).hom
  have := hA.smooth
  have : Etale (Out.mulA o'.t.G l.M).left := GrpTangent.etale_id_pow o'.t.G hMu
  have h : θ.hom = 𝟙 _ := by
    refine serre_any_base hL P l.M l.three_le θ hθ (fun _ => ⟨⊤, trivial, ?_⟩)
      (fix_torsion_of_forall_geometric o'.t.G l.M θ.hom
        (obj_aut_fix_geometric_torsion o' θ hact ⟨w, hw⟩ hη))
    obtain ⟨t, ht⟩ := gen_of_iso ((isGen_iff w).1 hw) (o'.t.G.hom ⁻¹ᵁ ⊤).ι
    refine gen_chartPull (chartPullOut o'.t.PP.L _ _ _ _ fun n => ?_) t ht
    fin_cases n
    exacts [rfl, (Category.comp_id _).symm]
  rw [← hφ, h, Over.id_left, Category.id_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FamRep

theorem hom_ext_loc {X Y : Scheme.{0}} {f g : X ⟶ Y}
    (h : ∀ p : X, ∃ (W : Scheme.{0}) (a : W ⟶ X), IsOpenImmersion a ∧ p ∈ Set.range a ∧ a ≫ f = a ≫ g) : f = g := by
  choose W a ha hp e using h
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers X W a
    (fun p => by obtain ⟨y, hy⟩ := hp p; exact ⟨p, y, hy⟩) ha
  exact 𝒰.hom_ext _ _ e

theorem exists_glue {X Y : Scheme.{0}} {I : Type} (U : I → Scheme.{0}) (j : ∀ i, U i ⟶ X) (g : ∀ i, U i ⟶ Y)
    (hj : ∀ i, IsOpenImmersion (j i)) (hc : ∀ p : X, ∃ i, p ∈ Set.range (j i))
    (h : ∀ i i' (y : U i), j i y ∈ Set.range (j i') → ∃ (W : Scheme.{0}) (a : W ⟶ U i) (a' : W ⟶ U i'),
      IsOpenImmersion a ∧ y ∈ Set.range a ∧ a ≫ j i = a' ≫ j i' ∧ a ≫ g i = a' ≫ g i') :
    ∃ G : X ⟶ Y, ∀ i, j i ≫ G = g i := by
  let 𝒰 : X.OpenCover := Scheme.Cover.mkOfCovers I U j
    (fun p => by obtain ⟨i, y, hy⟩ := hc p; exact ⟨i, y, hy⟩) hj
  have hg : ∀ i i', pullback.fst (j i) (j i') ≫ g i = pullback.snd (j i) (j i') ≫ g i' := by
    intro i i'
    refine hom_ext_loc fun p => ?_
    obtain ⟨W, a, a', ha, ⟨w, hw⟩, e, e'⟩ := h i i' (pullback.fst (j i) (j i') p)
      ⟨pullback.snd (j i) (j i') p, by rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
    have := hj i'
    have h1 : pullback.lift a a' e ≫ pullback.fst (j i) (j i') = a := pullback.lift_fst _ _ _
    have : IsOpenImmersion (pullback.lift a a' e ≫ pullback.fst (j i) (j i')) := by rw [h1]; exact ha
    refine ⟨W, pullback.lift a a' e, IsOpenImmersion.of_comp _ (pullback.fst (j i) (j i')), ⟨w, ?_⟩, ?_⟩
    · apply (pullback.fst (j i) (j i')).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, h1, hw]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, e']
  exact ⟨𝒰.glueMorphisms g hg, fun i => 𝒰.ι_glueMorphisms g hg i⟩

theorem range_of_isPullback {P X Y Z : Scheme.{0}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (x : X) : x ∈ Set.range a ↔ f x ∈ Set.range g := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨b p, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩
  · rintro ⟨y, hy⟩
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback h x y hy.symm
    exact ⟨p, hp⟩

theorem mul_left_pre {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (k : T'.left ⟶ T.left)
    (hk : k ≫ T.hom = T'.hom) (x y : T ⟶ G) (x' y' : T' ⟶ G) (hx : x'.left = k ≫ x.left)
    (hy : y'.left = k ≫ y.left) : (x' * y').left = k ≫ (x * y).left := by
  have e1 : x' = (Over.homMk k hk : T' ⟶ T) ≫ x := Over.OverMorphism.ext hx
  have e2 : y' = (Over.homMk k hk : T' ⟶ T) ≫ y := Over.OverMorphism.ext hy
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem isGrpPullback_of_loc {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A.left ⟶ A'.left) [IsIso φ]
    (w : φ ≫ A'.hom = A.hom)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (B : Over W) (_ : GrpObj B) (a : B.left ⟶ A.left),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsGrpPullback B A x a ∧ IsGrpPullback B A' x (a ≫ φ)) :
    IsGrpPullback A A' (𝟙 S) φ := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by rw [w, Category.comp_id]⟩, fun T y z y₀ z₀ hy hz => ?_⟩
  refine hom_ext_loc fun q => ?_
  obtain ⟨W, x, B, _, a, hx, hp, ha, hb⟩ := h (T.hom q)
  let k := pullback.fst T.hom x
  let T' : Over W := Over.mk (pullback.snd T.hom x)
  have hk : k ≫ T.hom = T'.hom ≫ x := pullback.condition
  let y' : T' ⟶ B := Over.homMk (ha.1.lift (k ≫ y.left) T'.hom (by rw [Category.assoc, Over.w y, hk]))
    (ha.1.lift_snd _ _ _)
  let z' : T' ⟶ B := Over.homMk (ha.1.lift (k ≫ z.left) T'.hom (by rw [Category.assoc, Over.w z, hk]))
    (ha.1.lift_snd _ _ _)
  have ey : y'.left ≫ a = k ≫ y.left := ha.1.lift_fst _ _ _
  have ez : z'.left ≫ a = k ≫ z.left := ha.1.lift_fst _ _ _
  have e1 := ha.2 T' y' z' (pushPt ha.1.w y') (pushPt ha.1.w z') rfl rfl
  have e2 := hb.2 T' y' z' (pushPt hb.1.w y') (pushPt hb.1.w z') rfl rfl
  have e3 := mul_left_pre (T' := Over.mk (T'.hom ≫ x)) k hk y z (pushPt ha.1.w y') (pushPt ha.1.w z') ey ez
  have e4 := mul_left_pre (T := Over.mk (T.hom ≫ 𝟙 S)) (T' := Over.mk (T'.hom ≫ x)) k
    (by show k ≫ T.hom ≫ 𝟙 S = T'.hom ≫ x; rw [Category.comp_id, hk]) y₀ z₀ (pushPt hb.1.w y') (pushPt hb.1.w z')
    (by show y'.left ≫ a ≫ φ = _; rw [← Category.assoc, ey, hy, Category.assoc])
    (by show z'.left ≫ a ≫ φ = _; rw [← Category.assoc, ez, hz, Category.assoc])
  refine ⟨_, k, inferInstance, (range_of_isPullback (IsPullback.of_hasPullback T.hom x) q).2 hp, ?_⟩
  refine e4.symm.trans (e2.trans ?_)
  rw [← Category.assoc, ← e1, e3, Category.assoc]

theorem lbIso_of_loc (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {L M : LB A.left} (hL : L.IsLB) (hM : M.IsLB) (rL : Out.Rigidified A L) (rM : Out.Rigidified A M)
    (h : ∀ p : S, ∃ (W B : Scheme.{0}) (x : W ⟶ S) (a : B ⟶ A.left) (c : B ⟶ W),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ IsPullback a c A.hom x ∧ LBIso (L.pull a) (M.pull a)) : LBIso L M := by
  refine exists_gen_of_local_of_section A.left S A.hom (eSec A) (LB.div M L) (LB.isLB_div hM hL) (Over.w η[A])
    (BaseChangeFns.app_surjective hG S A hA S A.left (𝟙 _) (𝟙 _) A.hom (IsPullback.of_horiz_isIso ⟨by simp⟩))
    (fun p => ?_) ?_
  · obtain ⟨W, B, x, a, c, hx, hp, ha, H⟩ := h p
    have : IsOpenImmersion a := MorphismProperty.of_isPullback ha.flip hx
    refine ⟨x.opensRange, hp, ?_⟩
    have hr : Set.range (A.hom ⁻¹ᵁ x.opensRange).ι ⊆ Set.range a := by
      rintro _ ⟨y, rfl⟩
      exact (range_of_isPullback ha _).2 y.2
    have e := IsOpenImmersion.lift_fac a _ hr
    obtain ⟨w, hw⟩ := H.chartPull (chartPullSame L (fun _ : PUnit => (A.hom ⁻¹ᵁ x.opensRange).ι) _ _ _ fun _ => e.symm)
      (chartPullSame M (fun _ : PUnit => (A.hom ⁻¹ᵁ x.opensRange).ι) _ _ _ fun _ => e.symm)
    exact gen_chartPull (IsoDescent.chartPullDiv M L _) w hw
  · obtain ⟨u, hu⟩ := rL
    obtain ⟨u', hu'⟩ := rM
    obtain ⟨w, hw⟩ := IsoDescent.lbIso_of_gens hL hM _ _ _ _ u hu u' hu'
    exact gen_chartPull (IsoDescent.chartPullDiv M L _) w hw

variable {o : Type} [CommRing o] {S S' S'' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o}

def IsTM (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) (φ : t'.A.left ⟶ t.A.left) : Prop :=
  IsGrpPullback t'.A t.A f φ ∧ LBIso t'.L (t.L.pull φ) ∧
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ∧ ∀ j, (t'.act j).left ≫ φ = φ ≫ (t.act j).left

theorem tMap_iff {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} : TMap t' t f ↔ ∃ φ, IsTM t' t f φ := Iff.rfl

theorem lbIso_pull_pull {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LBIso ((L.pull f).pull h) (L.pull (h ≫ f)) :=
  (PolBaseChange.lbIso_refl (LB.isLB_pull hL (h ≫ f))).chartPull
    (chartPullOut L (fun _ : PUnit => f) (fun _ => 1) h _ fun _ => rfl) (chartPullId _)

theorem lbIso_pull {Y Z : Scheme.{0}} {L M : LB Y} (H : LBIso L M) (h : Z ⟶ Y) : LBIso (L.pull h) (M.pull h) :=
  H.chartPull (chartPullPull L h h rfl) (chartPullPull M h h rfl)

theorem IsTM.congr {t' : TObj g k J b s'} {t : TObj g k J b s} {f f' : S' ⟶ S} {φ φ' : t'.A.left ⟶ t.A.left}
    (h : IsTM t' t f φ) (e : f = f') (e' : φ = φ') : IsTM t' t f' φ' := e ▸ e' ▸ h

theorem IsTM.comp {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    {φ : t'.A.left ⟶ t.A.left} {φ' : t''.A.left ⟶ t'.A.left} (h' : IsTM t'' t' f' φ') (h : IsTM t' t f φ) :
    IsTM t'' t (f' ≫ f) (φ' ≫ φ) := by
  refine ⟨h'.1.comp h.1, ?_, fun i => ?_, fun j => ?_⟩
  · exact LBIso.trans t''.isLB (LB.isLB_pull t'.isLB _) (LB.isLB_pull t.isLB _) h'.2.1
      (LBIso.trans (LB.isLB_pull t'.isLB _) (LB.isLB_pull (LB.isLB_pull t.isLB _) _) (LB.isLB_pull t.isLB _)
        (lbIso_pull h.2.1 φ') (lbIso_pull_pull t.isLB φ φ'))
  · rw [← Category.assoc, h'.2.2.1, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, h'.2.2.2, Category.assoc, h.2.2.2, Category.assoc]

theorem IsTM.cancel {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    {φ : t'.A.left ⟶ t.A.left} {ψ : t''.A.left ⟶ t.A.left} (h : IsTM t' t f φ) (n : IsTM t'' t (f' ≫ f) ψ) :
    ∃ φ', φ' ≫ φ = ψ ∧ IsTM t'' t' f' φ' := by
  have hp := h.1.1
  let F : t''.A.left ⟶ t'.A.left := hp.lift ψ (t''.A.hom ≫ f') (by rw [n.1.1.w, Category.assoc])
  have hF : F ≫ φ = ψ := hp.lift_fst _ _ _
  have hw : F ≫ t'.A.hom = t''.A.hom ≫ f' := hp.lift_snd _ _ _
  refine ⟨F, hF, h.1.cancel (by rw [hF]; exact n.1) hw, ?_, fun i => ?_, fun j => ?_⟩
  · have H := n.2.1
    rw [← hF] at H
    exact LBIso.trans t''.isLB (LB.isLB_pull t.isLB _) (LB.isLB_pull t'.isLB _) H
      (LBIso.trans (LB.isLB_pull t'.isLB _) (LB.isLB_pull (LB.isLB_pull t.isLB _) _) (LB.isLB_pull t.isLB _)
        (lbIso_pull h.2.1 F) (lbIso_pull_pull t.isLB φ F)).symm
  · apply hp.hom_ext
    · rw [Category.assoc, hF, n.2.2.1, Category.assoc, Category.assoc, h.2.2.1]
    · have a1 : (t''.pt i).left ≫ t''.A.hom = 𝟙 _ := Over.w _
      have a2 : (t'.pt i).left ≫ t'.A.hom = 𝟙 _ := Over.w _
      rw [Category.assoc, hw, ← Category.assoc, a1, Category.assoc, a2]; simp
  · apply hp.hom_ext
    · rw [Category.assoc, hF, n.2.2.2, Category.assoc, h.2.2.2, ← Category.assoc, hF]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

theorem tMap_comp {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h' : TMap t'' t' f') (h : TMap t' t f) : TMap t'' t (f' ≫ f) := by
  obtain ⟨φ', h'⟩ := tMap_iff.1 h'
  obtain ⟨φ, h⟩ := tMap_iff.1 h
  exact tMap_iff.2 ⟨_, h'.comp h⟩

theorem tMap_cancel {t'' : TObj g k J b s''} {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {f' : S'' ⟶ S'}
    (h : TMap t' t f) (n : TMap t'' t (f' ≫ f)) : TMap t'' t' f' := by
  obtain ⟨φ, h⟩ := tMap_iff.1 h
  obtain ⟨ψ, n⟩ := tMap_iff.1 n
  obtain ⟨φ', -, H⟩ := h.cancel n
  exact tMap_iff.2 ⟨_, H⟩

theorem exists_glue_tm (t t' : TObj g k J b s) {I : Type} (W : I → Scheme.{0}) (x : ∀ i, W i ⟶ S)
    (u : ∀ i, TObj g k J b (x i ≫ s)) (a : ∀ i, (u i).A.left ⟶ t.A.left) (a' : ∀ i, (u i).A.left ⟶ t'.A.left)
    (hx : ∀ i, IsOpenImmersion (x i)) (hc : ∀ p : S, ∃ i, p ∈ Set.range (x i))
    (ha : ∀ i, IsTM (u i) t (x i) (a i)) (ha' : ∀ i, IsTM (u i) t' (x i) (a' i))
    (hp : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ S), ∃ w : TObj g k J b (z ≫ s), TMap w t z)
    (hu : ∀ (R : Type) [CommRing R] (z : Sp R ⟶ S) (w : TObj g k J b (z ≫ s)) φ φ', IsOpenImmersion z →
      IsTM w t' z φ → IsTM w t' z φ' → φ = φ') :
    ∃ φ : t.A.left ⟶ t'.A.left, ∀ i, a i ≫ φ = a' i := by
  have hao : ∀ i, IsOpenImmersion (a i) := fun i => MorphismProperty.of_isPullback (ha i).1.1.flip (hx i)
  refine exists_glue _ a a' hao (fun q => ?_) fun i i' y hy => ?_
  · obtain ⟨i, hi⟩ := hc (t.A.hom q)
    exact ⟨i, (range_of_isPullback (ha i).1.1 q).2 hi⟩
  · have := hx i
    have := hx i'
    have := hao i
    have h1 := (range_of_isPullback (ha i).1.1 (a i y)).1 ⟨y, rfl⟩
    have h2 := (range_of_isPullback (ha i').1.1 (a i y)).1 hy
    obtain ⟨R, z, hz, hq, hr⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (U := (x i).opensRange ⊓ (x i').opensRange) (x := t.A.hom (a i y)) ⟨h1, h2⟩
    have e1 := IsOpenImmersion.lift_fac (x i) z (fun p hp => (hr hp).1)
    have e2 := IsOpenImmersion.lift_fac (x i') z (fun p hp => (hr hp).2)
    obtain ⟨w, hw⟩ := hp R z
    obtain ⟨c, hw⟩ := tMap_iff.1 hw
    obtain ⟨d, hd, Hd⟩ := (ha i).cancel (hw.congr e1.symm rfl)
    obtain ⟨d', hd', Hd'⟩ := (ha i').cancel (hw.congr e2.symm rfl)
    have hco : IsOpenImmersion c := MorphismProperty.of_isPullback hw.1.1.flip hz
    have : IsOpenImmersion (d ≫ a i) := by rw [hd]; exact hco
    refine ⟨_, d, d', IsOpenImmersion.of_comp d (a i), ?_, hd.trans hd'.symm,
      hu R z w _ _ hz ((Hd.comp (ha' i)).congr e1 rfl) ((Hd'.comp (ha' i')).congr e2 rfl)⟩
    obtain ⟨q, hq⟩ := (range_of_isPullback hw.1.1 (a i y)).2 hq
    refine ⟨q, (a i).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hd, hq]

theorem tMap_of_loc (hG : Out.GlobalFnsSt) (t t' : TObj g k J b s)
    (h : ∀ p : S, ∃ (W : Scheme.{0}) (x : W ⟶ S) (u : TObj g k J b (x ≫ s)),
      IsOpenImmersion x ∧ p ∈ Set.range x ∧ TMap u t x ∧ TMap u t' x)
    (hp : ∀ (t : TObj g k J b s) (R : Type) [CommRing R] (z : Sp R ⟶ S), ∃ w : TObj g k J b (z ≫ s), TMap w t z)
    (hu : ∀ (t : TObj g k J b s) (R : Type) [CommRing R] (z : Sp R ⟶ S) (w : TObj g k J b (z ≫ s)) φ φ',
      IsOpenImmersion z → IsTM w t z φ → IsTM w t z φ' → φ = φ') : TMap t t' (𝟙 S) := by
  choose W x u hx hc ha ha' using h
  choose a ha using fun p => tMap_iff.1 (ha p)
  choose a' ha' using fun p => tMap_iff.1 (ha' p)
  obtain ⟨φ, hφ⟩ := exists_glue_tm t t' W x u a a' hx (fun p => ⟨p, hc p⟩) ha ha' (hp t) (hu t')
  obtain ⟨φ', hφ'⟩ := exists_glue_tm t' t W x u a' a hx (fun p => ⟨p, hc p⟩) ha' ha (hp t') (hu t)
  have ext : ∀ {Y : Scheme.{0}} {f f' : t.A.left ⟶ Y}, (∀ p, a p ≫ f = a p ≫ f') → f = f' := fun H =>
    hom_ext_loc fun q => ⟨_, a (t.A.hom q), MorphismProperty.of_isPullback (ha _).1.1.flip (hx _),
      (range_of_isPullback (ha _).1.1 q).2 (hc _), H _⟩
  have ext' : ∀ {Y : Scheme.{0}} {f f' : t'.A.left ⟶ Y}, (∀ p, a' p ≫ f = a' p ≫ f') → f = f' := fun H =>
    hom_ext_loc fun q => ⟨_, a' (t'.A.hom q), MorphismProperty.of_isPullback (ha' _).1.1.flip (hx _),
      (range_of_isPullback (ha' _).1.1 q).2 (hc _), H _⟩
  have : IsIso φ := ⟨φ', ext fun p => by rw [← Category.assoc, hφ, hφ', Category.comp_id],
    ext' fun p => by rw [← Category.assoc, hφ', hφ, Category.comp_id]⟩
  have gp : IsGrpPullback t.A t'.A (𝟙 S) φ :=
    isGrpPullback_of_loc φ (ext fun p => by rw [← Category.assoc, hφ, (ha p).1.1.w, (ha' p).1.1.w])
      fun p => ⟨W p, x p, (u p).A, inferInstance, a p, hx p, hc p, (ha p).1, by rw [hφ]; exact (ha' p).1⟩
  refine ⟨φ, gp, ?_, fun i => hom_ext_loc fun p => ⟨W p, x p, hx p, hc p, ?_⟩, fun j => ext fun p => ?_⟩
  · refine lbIso_of_loc hG t.ab t.isLB (LB.isLB_pull t'.isLB _) t.rigid (PolBaseChange.rigidified_pull gp t'.rigid)
      fun p => ⟨W p, _, x p, a p, _, hx p, hc p, (ha p).1.1, ?_⟩
    have H := (ha' p).2.1
    rw [← hφ] at H
    exact LBIso.trans (LB.isLB_pull t.isLB _) (u p).isLB (LB.isLB_pull (LB.isLB_pull t'.isLB _) _) (ha p).2.1.symm
      (LBIso.trans (u p).isLB (LB.isLB_pull t'.isLB _) (LB.isLB_pull (LB.isLB_pull t'.isLB _) _) H
        (lbIso_pull_pull t'.isLB φ (a p)).symm)
  · rw [← Category.assoc, ← (ha p).2.2.1, Category.assoc, hφ, (ha' p).2.2.1, Category.id_comp]
  · rw [← Category.assoc, ← (ha p).2.2.2, Category.assoc, hφ, (ha' p).2.2.2, ← Category.assoc, hφ]

end GlobalTheory.FamRep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

noncomputable section

namespace GlobalTheory.SquarePol

variable {S : Scheme.{0}}

def sqIsPowGrp (G : Over S) [GrpObj G] : Out.IsPowGrp (G ⊗ G) G 2 where
  pr := ![fst G G, snd G G]
  hom := fun i => by
    fin_cases i
    · exact inferInstanceAs (IsMonHom (fst G G))
    · exact inferInstanceAs (IsMonHom (snd G G))
  lim := Fan.IsLimit.mk _ (fun s => lift (s.proj 0) (s.proj 1))
    (fun s i => by
      fin_cases i
      · exact lift_fst _ _
      · exact lift_snd _ _)
    (fun s m hm => by
      apply CartesianMonoidalCategory.hom_ext
      · exact (hm 0).trans (lift_fst _ _).symm
      · exact (hm 1).trans (lift_snd _ _).symm)

def sqPol (P : Out.PolAV S) : Out.PolAV S :=
  haveI : IsCommMonObj P.A := P.isAb.comm
  haveI : ∀ i, IsMonHom ((sqIsPowGrp P.A).pr i) := (sqIsPowGrp P.A).hom
  { A := P.A ⊗ P.A
    isAb := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.2.1 P.isAb
    g := 2 * P.g
    smoothDim := (PowGrp.powers S _ P.A 2 (sqIsPowGrp P.A)).2.2.1 P.g P.smoothDim
    L := Out.boxLB P.L (sqIsPowGrp P.A).pr
    isLB := DVR.linComb_isLB _ P.isLB _ _
    rigid := by
      obtain ⟨r, hr⟩ := P.rigid
      exact ⟨_, BoxPower.boxRig_isGen (sqIsPowGrp P.A) P.L r hr⟩
    sym := BoxPower.sym_box _ _ P.sym
    ample := relAmple_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ample
    ktriv := kTriv_boxLB S _ P.A 2 (sqIsPowGrp P.A) P.L P.isLB P.ktriv }

theorem sqPol_L (P : Out.PolAV S) :
    (sqPol P).L = LB.LinComb P.L (K := Fin 2) ![(fst P.A P.A).left, (snd P.A P.A).left] ![1, 1] := by
  simp only [sqPol, Out.boxLB]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem exists_square : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), ∃ (P₂ : Out.PolAV (Sp K)) (e : P₂.A ≅ P.A ⊗ P.A), IsMonHom (e.hom ≫ fst P.A P.A) ∧ IsMonHom (e.hom ≫ snd P.A P.A) ∧ P₂.g = 2 * P.g ∧ LBIso P₂.L (LB.LinComb P.L (K := Fin 2) ![(e.hom ≫ fst P.A P.A).left, (e.hom ≫ snd P.A P.A).left] ![1, 1]) := by
  intro K _ _ P
  refine ⟨sqPol P, Iso.refl _, ?_, ?_, rfl, ?_⟩
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 0
  · show IsMonHom (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A)
    rw [Category.id_comp]
    exact (sqIsPowGrp P.A).hom 1
  · show LBIso (sqPol P).L (LB.LinComb P.L (K := Fin 2)
      ![(𝟙 (P.A ⊗ P.A) ≫ fst P.A P.A).left, (𝟙 (P.A ⊗ P.A) ≫ snd P.A P.A).left] ![1, 1])
    simp only [Category.id_comp]
    have h : LBIso (sqPol P).L (sqPol P).L := ⟨idIso _, idIso_isGen (sqPol P).isLB⟩
    rw [sqPol_L] at h ⊢
    exact h

end GlobalTheory.SquarePol
end
end

