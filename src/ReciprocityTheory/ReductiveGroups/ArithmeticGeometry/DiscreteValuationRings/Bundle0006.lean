module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Lemmata.MiscLemmasN.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBCorr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenDiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsAtScale
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

section Scale

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma const_pull' {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (pY : Y ⟶ Spec (CommRingCat.of R)) (pZ : Z ⟶ Spec (CommRingCat.of R))
    (hφ : φ ≫ pZ = pY) (r : R) {U : Z.Opens} {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U (scal pZ r))) = resTop W (scal pY r) := by
  subst hφ
  simp only [rs, resTop, scal, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) ((pZ.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem expandsAt_scale (U : UnifPre I D A G) (e k : ℕ)
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (r : R) (h : U.ExpandsAt e k σ f) :
    U.ExpandsAt e k (SecOps.secScale (scal G.hom r) σ)
      (fun α => SecOps.secScale (scal D.toPre.P.A.hom r) (f α)) := by
  obtain ⟨S, hvan, hid⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt h1 hcoh => ?_⟩
  · show ((U.gt e).pG.left.app _).hom (resTop _ (scal D.toPre.P.A.hom r) * (f α).f j) = 0
    rw [map_mul, hvan α hα j, mul_zero]
  · have e0 := hid p j₁ jf jt h1 hcoh
    set W := U.expW e p j₁ S jf jt
    have hG : (fstG I e G).left ≫ G.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom := Over.w _
    have hB : (U.gt e).pG.left ≫ D.toPre.P.A.hom = ((Over.map (thick R I e)).obj (thickObj R I e G)).hom :=
      Over.w _
    have e1 := congrArg (fun x => resTop W (scal ((Over.map (thick R I e)).obj (thickObj R I e G)).hom r) * x) e0
    simp only [Finset.mul_sum] at e1
    convert e1 using 1
    · simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (fstG I e G).left _ G.hom (Over.w _) r (U := U.LG.L.wchart (fun _ => 𝟙 G.left) j₁)]
      exact mul_left_comm _ _ _
    · refine Finset.sum_congr rfl (fun α _ => ?_)
      simp only [SecOps.secScale]
      erw [map_mul, map_mul, const_pull' (U.gt e).pG.left _ D.toPre.P.A.hom (Over.w _) r (U := D.toPre.P.L.wchart (D.toPre.famφB α.1) (jf α.1))]
      exact mul_assoc _ _ _

end Scale


lemma scal_mul {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of V)) (r r' : V) : scal p (r * r') = scal p r * scal p r' := by
  simp only [scal, map_mul]

lemma resTop_mul {Y : Scheme.{0}} (W : Y.Opens) (c c' : Γ(Y, ⊤)) : resTop W (c * c') = resTop W c * resTop W c' :=
  map_mul _ _ _

lemma app_resTop {Y Z : Scheme.{0}} (φ : Y ⟶ Z) (U : Z.Opens) {W : Y.Opens} (h : W ≤ φ ⁻¹ᵁ U) (c : Γ(Z, ⊤)) :
    (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom (resTop U c)) = resTop W (φ.appTop.hom c) := by
  simp only [resTop]
  have key := congrArg (fun f => (CommRingCat.Hom.hom f) c) (φ.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.comp_apply] at key
  rw [key, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma secScal_scale {X Y Y' : Scheme.{0}} {L : LB X} {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    {φ₁ : K₁ → (Y' ⟶ X)} {ε₁ : K₁ → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ} {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)}
    (hs : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c) (c' : Γ(Y, ⊤)) :
    GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ (SecOps.secScale c' s₂) h (h.appTop.hom c' * c) := by
  intro j₁ j₂ hj
  have e := hs j₁ j₂ hj
  show _ = _ * _
  erw [map_mul, map_mul, e, app_resTop, resTop_mul]
  exact (_root_.mul_assoc _ _ _).symm

section BackK

variable {G : Over (Spec (CommRingCat.of V))}

lemma rs_resTop {Y : Scheme.{0}} {W W' : Y.Opens} (h : W' ≤ W) (c : Γ(Y, ⊤)) : rs h (resTop W c) = resTop W' c :=
  SecOps.resTop_res h c

end BackK

section Integral

variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenInj
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem away_fractionRing {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.SecondBlockLemmaO.goal1 .. | (apply Bl.SecondBlockLemmaO.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaO.goal1 <;> assumption)

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem eq_zero_of_app_fst_open {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X T : AlgebraicGeometry.Scheme.{0}} (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.Flat p]
    (t : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.IsOpenImmersion t] [Nonempty T]
    (W : X.Opens) (d : Γ(X, W)) (h : ((CategoryTheory.Limits.pullback.fst p t).app W).hom d = 0) : d = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ' : Γ(Sp V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ
  have hrange : ∀ t' : Sp V, t' ∈ (Sp V).basicOpen ϖ' → t' ∈ Set.range t.base := by
    intro t' ht
    have ht' : t' ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V)) := by
      have := basicOpen_eq_of_affine (R := CommRingCat.of V) ϖ
      rw [← this]; exact ht
    have hbot : PrimeSpectrum.asIdeal (R := V) t' = ⊥ := by
      by_contra hne
      have hmax := Ideal.IsPrime.isMaximal (PrimeSpectrum.isPrime (R := V) t') hne
      have hm := IsLocalRing.eq_maximalIdeal hmax
      apply (PrimeSpectrum.mem_basicOpen _ _).1 ht'
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    obtain ⟨y⟩ := ‹Nonempty T›
    have hle : PrimeSpectrum.asIdeal (R := V) t' ≤ PrimeSpectrum.asIdeal (R := V) (t.base y) := by
      rw [hbot]; exact bot_le
    have hsp : t' ⤳ t.base y := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 hle)
    exact hsp.mem_open t.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  let O : X.Opens := p ⁻¹ᵁ (Sp V).basicOpen ϖ'
  let q := IsOpenImmersion.lift t (O.ι ≫ p) (by
    rintro _ ⟨a, rfl⟩
    exact hrange _ a.2)
  let s : O.toScheme ⟶ pullback p t :=
    pullback.lift O.ι q (IsOpenImmersion.lift_fac _ _ _).symm
  have hs : s ≫ pullback.fst p t = O.ι := pullback.lift_fst _ _ _
  have hO : ∀ x ∈ W, x ∈ O → gs (𝟙 X) x W d = 0 := by
    intro x hxW hxO
    have hm : (s ≫ pullback.fst p t) ⟨x, hxO⟩ ∈ W := by rw [hs]; exact hxW
    have e1 : gs O.ι ⟨x, hxO⟩ W d = 0 := by
      rw [← hs, ← gs_pull s (pullback.fst p t) ⟨x, hxO⟩ W hm, h]
      exact gs_zero' _ _ _
    rw [gs_stalkMap O.ι ⟨x, hxO⟩ W hxW] at e1
    have : IsIso (O.ι.stalkMap ⟨x, hxO⟩) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    exact (ConcreteCategory.bijective_of_isIso (O.ι.stalkMap ⟨x, hxO⟩)).1 (e1.trans (map_zero _).symm)
  refine fn_ext fun x hx => ?_
  rw [gs_zero']
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hU' : IsAffineOpen (U : X.Opens) := hU
  let g : Γ(X, U) := constFn p U ϖ
  let dU : Γ(X, U) := (X.presheaf.map (homOfLE hUW).op).hom d
  have hgs : ∀ x' ∈ U, gs (𝟙 X) x' U g = cst p x' ϖ := fun x' hx' =>
    (gs_constFn p U (𝟙 X) x' hx' ϖ).trans (by rw [Category.id_comp])
  refine (exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU'.isCompact dU g ?_).elim
    fun n hn => ?_
  · refine fn_ext fun x' hx' => ?_
    have hx'U : x' ∈ U := X.basicOpen_le g hx'
    have hunit : IsUnit (X.presheaf.germ U x' hx'U g) := (X.mem_basicOpen g x' hx'U).1 hx'
    have h2 : IsUnit (cst p x' ϖ) := by
      rw [← hgs x' hx'U, gs_eq (𝟙 X) x' U hx'U]; exact hunit
    have h3 : IsUnit (gs (𝟙 (Sp V)) (p x') ⊤ ϖ') := by
      rw [cst, gs_stalkMap p x' ⊤ trivial] at h2
      exact (isUnit_map_iff (p.stalkMap x').hom _).1 h2
    have hxO : x' ∈ O := by
      show p x' ∈ (Sp V).basicOpen ϖ'
      rw [gs_eq (𝟙 (Sp V)) (p x') ⊤ trivial] at h3
      exact ((Sp V).mem_basicOpen ϖ' (p x') trivial).2 h3
    change gs (𝟙 X) x' _ ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom dU) = gs (𝟙 X) x' _ 0
    rw [gs_zero', gs_res (𝟙 X) x' (X.basicOpen_le g) hx']
    exact (gs_res (𝟙 X) x' hUW hx'U d).trans (hO x' (hUW hx'U) hxO)
  · have e := congrArg (gs (𝟙 X) x U) hn
    have hdU : gs (𝟙 X) x U dU = gs (𝟙 X) x W d := gs_res (𝟙 X) x hUW hxU d
    rw [gs_zero', gs_mul (𝟙 X) x U hxU, hdU] at e
    have hpow : gs (𝟙 X) x U (g ^ n) = cst p x ϖ ^ n := by
      rw [gs_eq (𝟙 X) x U hxU, map_pow, map_pow, ← gs_eq (𝟙 X) x U hxU, hgs x hxU]
    rw [hpow] at e
    exact ((cst_regular p x hϖ.ne_zero).pow n) (e.trans (mul_zero _).symm)

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

def subSec {Y : Scheme.{0}} {M : LB Y} (s s' : LB.Sec M) : LB.Sec M where
  f j := s.f j - s'.f j
  compat i j := by rw [map_sub, map_sub, s.compat, s'.compat, mul_sub]

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

lemma fstG_act {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    (f : G ⟶ G) :
    ((Over.pullback (thick R I e)).map f).left ≫ (fstG I e G).left = (fstG I e G).left ≫ f.left := by
  simp only [fstG]
  simp
  all_goals first
    | exact pullback.lift_fst _ _ _
    | erw [pullback.lift_fst]

lemma pG_act {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))}
    [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] {ιD : D.OAct O} {ιA : A.OAct O} {ιG : RingAct G O} (hlin : U.OLinear O ιD ιA ιG)
    (e : ℕ) (a : O) :
    ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ (U.gt e).pG.left =
      (U.gt e).pG.left ≫ (ιD.onB.act a).left := by
  have hq := congrArg (fun φ => φ.left) (hlin.q_lin e a)
  simp only [Over.comp_left] at hq
  unfold GtCoord.pG
  simp only [Over.comp_left, Over.map_map_left, Category.assoc]
  rw [← Category.assoc, hq, Category.assoc]
  congr 1
  first
    | exact fstG_act I e (ιD.onB.act a)
    | (unfold DegPre.prBe; simp; done)
    | (unfold DegPre.prBe; simp; exact pullback.lift_fst _ _ _)


end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenGeneric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

def pullSec' {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) :
    LB.Sec (LB.LinComb L φ' ε) := by
  have e : φ' = fun k => h ≫ φ k := funext hφ
  subst e
  exact pullSec L φ ε s h

lemma pullSec'_f {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k)
    (j : K → L.ι) :
    (pullSec' L φ ε s h φ' hφ).f j =
      (Z.presheaf.map (homOfLE (wchart_le_preimage L h φ φ' hφ j)).op).hom ((h.app _).hom (s.f j)) := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  rfl

lemma map_inj_of_le_ge {X : Scheme.{0}} {V W : X.Opens} (h1 : W ≤ V) (h2 : V ≤ W) {a b : Γ(X, V)}
    (h : (X.presheaf.map (homOfLE h1).op).hom a = (X.presheaf.map (homOfLE h1).op).hom b) : a = b := by
  obtain rfl : W = V := le_antisymm h1 h2
  have e : homOfLE h1 = 𝟙 W := Subsingleton.elim _ _
  rw [e] at h
  simpa using h

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def secK (U : UnifPre I D A G) (s : H0 U.LG.L 1) : U.SecK 1 :=
  pullSec' U.LG.L _ _ s (pullback.fst G.hom (jK R)) _ (fun _ => (Category.comp_id _).symm)

lemma secK_rel (U : UnifPre I D A G) (s : H0 U.LG.L 1) :
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) (secK U s)
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1 := by
  intro j₁ j₂ hc
  have hj : j₁ = j₂ := funext fun k => by
    rw [Subsingleton.elim k 0]
    exact hc (Sum.inl 0) (Sum.inr 0) (Category.comp_id _).symm
  subst hj
  rw [secK, pullSec'_f]
  have h1 : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j₁ ⊓
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) j₁)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1, _root_.one_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem sec_eq_of_secScal (U : UnifPre I D A G) [Flat G.hom] (s σ : H0 U.LG.L 1) (sK : U.SecK 1) (r : R)
    (h1 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) s (pullback.fst G.hom (jK R)) 1)
    (h2 : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((1 : ℕ) : ℤ)) sK
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R))
      (scal (pullback.snd G.hom (jK R) ≫ jK R) r)) :
    ∀ j, σ.f j = toW G.hom _ r * s.f j := by
  intro (j : Fin 1 → U.LG.L.ι)
  have hc : LB.Coh U.LG.L (Sum.elim (fun _ : Fin 1 => pullback.fst G.hom (jK R))
      (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k)) (Sum.elim j j) := by
    intro a b _
    rcases a with a | a <;> rcases b with b | b <;> exact congrArg j (Subsingleton.elim _ _)
  have e1 := h1 j j hc
  have e2 := h2 j j hc
  have h1' : resTop (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
      LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j)
      (1 : Γ(pullback G.hom (jK R), ⊤)) = 1 := map_one _
  rw [h1', _root_.one_mul] at e1
  rw [← e1] at e2
  have hle : pullback.fst G.hom (jK R) ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j ≤
      LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j ⊓
        LB.wchart U.LG.L (fun k : Fin 1 => pullback.fst G.hom (jK R) ≫ (fun _ : Fin 1 => 𝟙 G.left) k) j :=
    fun x hx => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k, Set.mem_iInter.2 fun k => Set.mem_iInter.1 hx k⟩
  apply app_fst_jF_injective G.hom
  apply map_inj_of_le_ge (inf_le_right.trans (wchart_comp_le _ _ j)) hle
  refine e2.trans ?_
  have e3 : (((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
      (toW G.hom (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) r *
        (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j))) =
      toW (pullback.fst G.hom (jK R) ≫ G.hom) _ r *
        ((pullback.fst G.hom (jK R)).app (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)).hom
          (show Γ(G.left, LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j) from s.f j) := by
    rw [map_mul, app_toW]
  erw [e3, map_mul, toW_res, resTop_scal, toW_congr pullback.condition.symm]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end

