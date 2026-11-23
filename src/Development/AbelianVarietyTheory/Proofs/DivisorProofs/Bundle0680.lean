module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FamUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodCompTranslationGroupHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.Reindex

open GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ)

abbrev fam : Fam I g Λ' := ⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩

variable {F A} (K' : Charts (fam F A))

@[reducible] def charts : Charts F where
  K := K'.K
  W := K'.W
  base := K'.base
  le m k' k := ∃ l, A l = m ∧ K'.le l k' k
  le_refl k := ⟨0, map_zero A, K'.le_refl k⟩
  le_trans := by
    rintro _ _ k k' k'' ⟨l, rfl, h⟩ ⟨m, rfl, h'⟩
    exact ⟨l + m, map_add A l m, K'.le_trans h h'⟩
  maps := by
    rintro _ k k' ⟨l, rfl, h⟩
    exact K'.maps h

@[reducible] def obj (T : K'.Obj) : (charts K').Obj where
  k := T.k
  C := T.C
  alg := T.alg
  J := T.J
  nil := T.nil
  ρ := T.ρ
  ρ_cst := T.ρ_cst

def hom {T T' : K'.Obj} (f : T ⟶ T') : obj K' T ⟶ obj K' T' where
  φ := f.φ
  deg := A f.deg
  le := ⟨f.deg, rfl, Charts.Hom.le f⟩
  mem := f.mem
  close := f.close

theorem isPeriod_comp : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ) {Λ' : Type} [AddCommGroup Λ'] (A : Λ' →+ Λ) (u' : Unif (⟨F.V, F.τ.comp A, fun l ↦ F.hol (A l)⟩ : Fam I g Λ') s σ), u'.E = u.E → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod u c per → IsPeriod u' c (per.comp A) := by
  intro I _ g Λ _ F B _ X s σ u Λ' _ A u' hE c per h K' r' hr
  let r : Real (charts K') s σ :=
    { x := r'.x
      w := r'.w
      compat := by
        rintro _ k k' ⟨l, rfl, e⟩
        exact r'.compat e }
  have h1 := h (charts K') r (fun k p hp ↦ (hr k p hp).trans (congrFun hE p))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := H1.mk_eq_mk.1 h1
  refine H1.mk_eq_mk.2 ⟨fun T ↦ G (obj K' T), ?_⟩
  funext T T' φ
  exact congrFun (congrFun (congrFun hG (obj K' T)) (obj K' T')) (hom K' φ)

end GlobalTheory.AnPer.Reindex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodOverRingRestrictFamilyClass
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ}
  (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R)
  (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k))
  (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C)
  (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
  (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
    ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S)))

def famObj (S : K₀.DObj et M) : K.Obj where
  k := ka S.T.k
  C := S.T.C
  alg := ((algebraMap R S.T.C).comp θ).toAlgebra
  J := S.T.J
  nil := S.T.nil
  ρ := ρ' S
  ρ_cst := h1 S

def famCoef : CoefMap θ K.Oc (K₀.OD et M) where
  G :=
    { obj := famObj K K₀ et M θ ka ρ' h1
      map {S S'} f :=
        { φ := { (f.1.φ : S.T.C →+* S'.T.C) with commutes' := fun x ↦ f.2 (θ x) }
          deg := f.1.deg
          le := hka (Charts.Hom.le f.1)
          mem := f.1.mem
          close := h3 S S' f }
      map_id _ := Charts.hom_ext (fun _ ↦ rfl) rfl
      map_comp _ _ := Charts.hom_ext (fun _ ↦ rfl) rfl }
  α S := RingHom.id S.T.C
  naturality _ _ := rfl
  smul S d c := (Algebra.smul_def (A := S.T.C) (θ d) c).symm

theorem famCoef_perCl (per : Λ →+ Hol F.V) :
    (famCoef K K₀ et M θ ka hka ρ' h1 h3).pull1 (K.perCl per) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  congrArg (H1.mk _) (Subtype.ext (funext fun _ ↦ funext fun _ ↦ funext fun _ ↦ rfl))

theorem coefD_pull1_of_family (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k))
    (h2 : ∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J)
    {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀}
    {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : Real K s σ) (r₀ : Real K₀ s₀ σ₀) {J : Ideal D}
    (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io)
    (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀) (h4 : ∀ b, θ (σ b) = io (j b))
    (h5 : ∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) (c : FirstDeRham s) (per : Λ →+ Hol F.V)
    (hc : r.coef.pull1 c = K.perCl per) (h1 : ∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f))
    (h3 : ∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1))))
      ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) :
    (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) := by
  let t : (r.coef.comp (famCoef K K₀ et M θ ka hka ρ' h1 h3)).G ⟶ (n.coef.comp (r₀.coefD dl H)).G :=
    { app S :=
        { φ := { RingHom.id S.T.C with commutes' := fun b ↦ congrArg (algebraMap R S.T.C) (h4 b) }
          φ₀ := RingHom.id (S.T.C ⧸ S.T.J)
          comm := fun _ ↦ rfl
          dp := letI := S.T.ratAlg; isDPMorphism_of_rat (C := S.T.C) (C' := S.T.C) _ _ (RingHom.id S.T.C) fun _ h ↦ h
          pt := by
            have e : (Ideal.Quotient.mk S.T.J).comp (ρ' S) = ((Ideal.Quotient.mk S.T.J).comp S.T.ρ).comp (res _) :=
              RingHom.ext fun h ↦ Ideal.Quotient.eq.2 (h2 S h)
            change spMap (RingHom.id (S.T.C ⧸ S.T.J)) ≫ spMap ((Ideal.Quotient.mk S.T.J).comp (ρ' S)) ≫ r.x (ka S.T.k) =
              (spMap ((Ideal.Quotient.mk S.T.J).comp S.T.ρ) ≫ r₀.x S.T.k) ≫ φ₀
            rw [Cris.spMap_id, Category.id_comp, Category.assoc, ← h5, e, Cris.spMap_comp (res _), Category.assoc] }
      naturality _ _ _ := by
        apply Thick.Hom.ext'
        ext b
        rfl }
  refine (n.coef.pullCohomologyOne_comp (r₀.coefD dl H) c).symm.trans ?_
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans _ _ t (fun _ _ ↦ rfl) c).symm.trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hc, famCoef_perCl]

end GlobalTheory.AnPer


open GlobalTheory.AnPer in
theorem GlobalTheory.AnPer.period_restrict_family : ∀ {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam I₀ g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] (et : Hol F₀.V →+* R) (M : Ideal R) (θ : Hol F.V →+* R) (ka : K₀.K → K.K) (hka : ∀ {l k' k}, K₀.le l k' k → K.le l (ka k') (ka k)) (res : ∀ k, Hol (K.W (ka k)) →+* Hol (K₀.W k)) (ρ' : ∀ S : K₀.DObj et M, Hol (K.W (ka S.T.k)) →+* S.T.C), (∀ S f, ρ' S (K.cst _ f) = algebraMap R S.T.C (θ f)) → (∀ S h, ρ' S h - S.T.ρ (res _ h) ∈ S.T.J) → (∀ (S S' : K₀.DObj et M) (f : S ⟶ S'), Close S'.T.J ((ρ' S').comp (Charts.sh (hka (Charts.Hom.le f.1)))) ((f.1.φ : S.T.C →+* S'.T.C).comp (ρ' S))) → ∀ {B B₀ D : Type} [CommRing B] [CommRing B₀] [CommRing D] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp B₀} {σ : B →+* Hol F.V} {σ₀ : B₀ →+* Hol F₀.V} (r : GlobalTheory.AnPer.Real K s σ) (r₀ : GlobalTheory.AnPer.Real K₀ s₀ σ₀) {J : Ideal D} (dl : DividedPowers J) {s' : X₀ ⟶ Sp D} {π : D →+* B₀} {io : D →+* R} (H : IsOver et M s₀ σ₀ J s' π io) (j : B →+* D) (φ₀ : X₀ ⟶ X) (n : IsMor (dp0 B) s dl s' j φ₀), (∀ b, θ (σ b) = io (j b)) → (∀ k, spMap (res k) ≫ r.x (ka k) = r₀.x k ≫ φ₀) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V), r.coef.pull1 c = K.perCl per → (r₀.coefD dl H).pull1 (n.pull1 c) = K₀.perClD et M (θ.toAddMonoidHom.comp per) :=
  fun K K₀ _ _ et M θ ka hka res ρ' h1 h2 h3 _ _ _ _ _ _ _ _ _ _ _ _ r r₀ _ dl _ _ _ H j φ₀ n h4 h5 c per hc ↦
    coefD_pull1_of_family K K₀ et M θ ka hka ρ' res h2 r r₀ dl H j φ₀ n h4 h5 c per hc h1 h3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsExistAffineZeroSection
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace CategoryTheory AlgebraicGeometry GlobalTheory.CatCoh GlobalTheory.Cris
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.PerExist

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

theorem ev_cst (K : Charts F) (k : K.K) (p : Tot I g) (hp : p ∈ K.W k) :
    (Hol.ev p hp).toRingHom.comp (K.cst k) = (Hol.ev p.1 (K.base k p hp)).toRingHom :=
  RingHom.ext fun f ↦ by
    change Hol.ev p hp (K.cst k f) = Hol.ev p.1 (K.base k p hp) f
    rw [Hol.ev_apply, Hol.ev_apply]
    exact K.fn_cst k f hp

theorem ev_sh {K : Charts F} {l : Λ} {k k' : K.K} (h : K.le l k' k) (p : Tot I g) (hp : p ∈ K.W k') :
    (Hol.ev p hp).toRingHom.comp (Charts.sh h) = (Hol.ev (F.shift l p) (K.maps h p hp)).toRingHom :=
  RingHom.ext fun f ↦ by
    change Hol.ev p hp (Charts.sh h f) = Hol.ev (F.shift l p) (K.maps h p hp) f
    rw [Hol.ev_apply, Hol.ev_apply]
    exact Charts.fn_sh h f hp

def Pt (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem Pt.mono {u : Unif F s σ} {W W' : Opens (Tot I g)} (hW : W' ≤ W) (h : Pt u W) : Pt u W' := by
  obtain ⟨x, hx⟩ := h
  refine ⟨spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp)).toRingHom ≫ x, fun p hp ↦ ?_⟩
  rw [← Category.assoc, ← Cris.spMap_comp]
  have e : (Hol.ev p hp).toRingHom.comp (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp) : Hol W →ₐ[ℂ] Hol W').toRingHom =
      (Hol.ev p (hW hp)).toRingHom :=
    RingHom.ext fun f ↦ by
      change Hol.ev p hp (Hol.comap id analyticOnNhd_id (fun p hp ↦ hW hp) f) = Hol.ev p (hW hp) f
      rw [Hol.ev_apply, Hol.ev_apply]
      exact Hol.fn_comap _ _ _ f hp
  rw [e]
  exact hx p (hW hp)

theorem isHolTo (u : Unif F s σ) (W : Opens (Tot I g)) (hW : ∀ p ∈ W, p.1 ∈ F.V) : IsHolTo (W : Set (Tot I g)) u.E := by
  intro U f
  obtain ⟨ho, hd⟩ := u.hol U f
  have e : {b ∈ (W : Set (Tot I g)) | ⊤ ≤ u.E b ⁻¹ᵁ U} =
      (W : Set (Tot I g)) ∩ {p : Tot I g | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U} :=
    Set.ext fun b ↦ ⟨fun h ↦ ⟨h.1, hW b h.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  rw [e]
  exact ⟨W.isOpen.inter ho, hd.mono Set.inter_subset_right⟩

theorem pt_of_affine (u : Unif F s σ) (U : X.Opens) (hU : IsAffineOpen U) (W : Opens (Tot I g))
    (hW : ∀ p ∈ W, p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U) : Pt u W := by
  obtain ⟨x, -, hx⟩ := exists_point_hol (Tot I g) W X u.E U hU (isHolTo u W fun p hp ↦ (hW p hp).1)
    fun p hp ↦ (hW p hp).2
  exact ⟨x, hx⟩

def inU (u : Unif F s σ) (U : X.Opens) : Opens (Tot I g) :=
  ⟨{p | p.1 ∈ F.V ∧ ⊤ ≤ u.E p ⁻¹ᵁ U}, (u.hol U 0).1⟩

variable (u : Unif F s σ)

abbrev Kmax : Charts F := Charts.std F (Pt u)

theorem rich : (Kmax u).Rich := by
  refine ⟨fun p hp ↦ ?_, fun l k₁ k₂ p h₁ h₂ ↦ ?_⟩
  · obtain ⟨_, ⟨U, hU, rfl⟩, hq, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (u.E p (default : PrimeSpectrum ℂ))) isOpen_univ
    have hpU : p ∈ inU u U := ⟨hp, fun y _ ↦ by
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) y default]
      exact hq⟩
    exact ⟨⟨inU u U, fun q hq ↦ hq.1, pt_of_affine u U hU _ fun q hq ↦ hq⟩, hpU⟩
  · let W : Opens (Tot I g) := ⟨(k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g)),
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen⟩
    have hW : W ≤ k₁.1 := fun q hq ↦ hq.1
    refine ⟨⟨W, fun q hq ↦ k₁.2.1 q hq.1, k₁.2.2.mono hW⟩, ⟨h₁, h₂⟩, fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    change F.shift 0 q ∈ k₁.1
    rw [F.shift_zero]
    exact hq.1

theorem based (hu : u.Based) : (Kmax u).Based := by
  obtain ⟨U, hU, hz⟩ := hu
  exact ⟨⟨inU u U, fun q hq ↦ hq.1, pt_of_affine u U hU _ fun q hq ↦ hq⟩, fun z hz' ↦ ⟨hz', hz z hz'⟩⟩

theorem over_base (K : Charts F) (k : K.K) (x : Sp (Hol (K.W k)) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) :
    x ≫ s = spMap ((K.cst k).comp σ) :=
  point_hol_ext (Tot I g) (K.W k) (Sp B) _ (Limits.terminal.from _) _ _ (Limits.terminal.hom_ext _ _) fun p hp ↦ by
    change spMap (Hol.ev p hp).toRingHom ≫ x ≫ s = spMap (Hol.ev p hp).toRingHom ≫ _
    rw [← Category.assoc, hx p hp, u.w p (K.base k p hp), ← Cris.spMap_comp, ← RingHom.comp_assoc, ev_cst]

variable [IsSeparated s]

theorem pt_unique (K : Charts F) (k : K.K) (x x' : Sp (Hol (K.W k)) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p)
    (hx' : ∀ (p : Tot I g) (hp : p ∈ K.W k), spMap (Hol.ev p hp).toRingHom ≫ x' = u.E p) : x = x' :=
  point_hol_ext (Tot I g) (K.W k) X (Sp B) s _ _ ((over_base u K k x hx).trans (over_base u K k x' hx').symm)
    fun p hp ↦ (hx p hp).trans (hx' p hp).symm

def rmax : Real (Kmax u) s σ where
  x k := k.2.2.choose
  w k := over_base u (Kmax u) k _ k.2.2.choose_spec
  compat {l k k'} h := pt_unique u (Kmax u) k' _ _ (fun p hp ↦ by
    rw [← Category.assoc, ← Cris.spMap_comp, ev_sh h p hp]
    exact (k.2.2.choose_spec _ _).trans (u.per l p (k'.2.1 p hp))) k'.2.2.choose_spec

variable {u} {K : Charts F} {r : Real K s σ}


omit [IsSeparated s] in
def toMax (hr : r.IsFor u) : K.Obj ⥤ (Kmax u).Obj where
  obj T :=
    { k := ⟨K.W T.k, K.base T.k, r.x T.k, hr T.k⟩
      C := T.C
      J := T.J
      nil := T.nil
      ρ := T.ρ
      ρ_cst := T.ρ_cst }
  map {T T'} f :=
    { φ := (Charts.Hom.φ f : T.C →ₐ[Hol F.V] T'.C)
      deg := Charts.Hom.deg f
      le := K.maps (Charts.Hom.le f)
      mem := Charts.Hom.mem f
      close := Charts.Hom.close f }


omit [IsSeparated s] in
def toMaxCoef (hr : r.IsFor u) : CoefMap (RingHom.id (Hol F.V)) (Kmax u).Oc K.Oc where
  G := toMax hr
  α T := RingHom.id T.C
  naturality _ _ := rfl
  smul _ _ _ := rfl

def toMaxTrans (hr : r.IsFor u) : r.coef.G ⟶ ((rmax u).coef.comp (toMaxCoef hr)).G where
  app T :=
    { φ := { RingHom.id T.C with commutes' := fun _ ↦ rfl }
      φ₀ := RingHom.id (T.C ⧸ T.J)
      comm := fun _ ↦ rfl
      dp := letI := T.ratAlg; isDPMorphism_of_rat T.δ T.δ (RingHom.id T.C) fun _ h ↦ h
      pt := ((congrArg (· ≫ _) (Cris.spMap_id (T.C ⧸ T.J))).trans (Category.id_comp _)).trans
        (congrArg (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ ·)
          (pt_unique u K T.k _ _ (hr T.k) ((toMax hr).obj T).k.2.2.choose_spec)) }
  naturality _ _ _ := Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)

end GlobalTheory.AnPer.PerExist

namespace GlobalTheory.AnPer


open PerExist in
theorem periods_exist : PExist := by
  intro I _ g Λ _ F B _ X s _ σ u hu c
  obtain ⟨per, hper⟩ := GlobalTheory.T.exists_period_cohomologyClass_of_rich_based (Kmax u) (rich u) (based u hu) ((rmax u).coef.pull1 c)
  refine ⟨per, fun K r hr ↦ ?_⟩
  refine (CoefMap.pullCohomologyOne_eq_of_natTrans r.coef _ (toMaxTrans hr) (fun _ _ ↦ rfl) c).trans ?_
  rw [CoefMap.pullCohomologyOne_comp, hper]
  rfl

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsOfDeRhamClassesUnique
section
set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.AnPer.MaxCharts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
  {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V}

def Alg (u : Unif F s σ) (W : Opens (Tot I g)) : Prop :=
  ∃ x : Sp (Hol W) ⟶ X, (∀ h : ∀ p ∈ W, p.1 ∈ F.V,
      x ≫ s = spMap ((Hol.comap Prod.fst (fun _ _ ↦ analyticAt_fst) h).toRingHom.comp σ)) ∧
    ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p

theorem alg_of_ev (u : Unif F s σ) (W : Opens (Tot I g)) (x : Sp (Hol W) ⟶ X)
    (hx : ∀ (p : Tot I g) (hp : p ∈ W), spMap (Hol.ev p hp).toRingHom ≫ x = u.E p) : Alg u W := by
  refine ⟨x, fun h ↦ ?_, hx⟩
  refine point_hol_ext _ W (Sp B) (⊤_ Scheme.{0}) (terminal.from _) _ _ (terminal.hom_ext _ _) fun p hp ↦ ?_
  have e := hx p hp
  change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
  rw [← Category.assoc, e, u.w p (h p hp), ← Cris.spMap_comp]
  rfl

theorem alg_mono (u : Unif F s σ) {W W' : Opens (Tot I g)} (h : W' ≤ W) (a : Alg u W) : Alg u W' := by
  obtain ⟨x, -, hx⟩ := a
  refine alg_of_ev u W' (spMap (Hol.comap id analyticOnNhd_id (fun p hp ↦ h hp)).toRingHom ≫ x) fun p hp ↦ ?_
  rw [← Category.assoc, ← Cris.spMap_comp, ← hx p (h hp)]
  rfl

@[reducible] def charts (u : Unif F s σ) : Charts F := Charts.std F (Alg u)

def real [IsSeparated s] (u : Unif F s σ) : Real (charts u) s σ where
  x k := k.2.2.choose
  w k := k.2.2.choose_spec.1 k.2.1
  compat {l k k'} h := by
    refine point_hol_ext _ k'.1 X _ s _ _ ?_ fun p hp ↦ ?_
    · rw [Category.assoc, k.2.2.choose_spec.1 k.2.1, k'.2.2.choose_spec.1 k'.2.1, ← Cris.spMap_comp]
      exact congrArg spMap (RingHom.ext fun b ↦ Charts.sh_cst (K := charts u) h (σ b))
    · change spMap (Hol.ev p hp).toRingHom ≫ _ = spMap (Hol.ev p hp).toRingHom ≫ _
      rw [k'.2.2.choose_spec.2 p hp, ← Category.assoc, ← Cris.spMap_comp, ← u.per l p (k'.2.1 p hp),
        ← k.2.2.choose_spec.2 _ (h p hp)]
      rfl

theorem isFor [IsSeparated s] (u : Unif F s σ) : (real u).IsFor u := fun k ↦ k.2.2.choose_spec.2

theorem rich (u : Unif F s σ) : (charts u).Rich := by
  constructor
  · intro p hp
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := u.E p (default : PrimeSpectrum ℂ))
      (U := ⊤) trivial
    let W : Opens (Tot I g) := ⟨{q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U}, (u.hol U 0).1⟩
    have hol : IsHolTo (W : Set (Tot I g)) u.E := fun U' f ↦ ⟨by
      have e : {q | q ∈ (W : Set (Tot I g)) ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} =
          (W : Set (Tot I g)) ∩ {q | q.1 ∈ F.V ∧ ⊤ ≤ u.E q ⁻¹ᵁ U'} :=
        Set.ext fun q ↦ ⟨fun h ↦ ⟨h.1, h.1.1, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
      exact e ▸ W.isOpen.inter (u.hol U' f).1,
      (u.hol U' f).2.mono fun q h ↦ ⟨h.1.1, h.2⟩⟩
    obtain ⟨x, -, hx⟩ := exists_point_hol _ W X u.E U hU hol fun q hq ↦ hq.2
    refine ⟨⟨W, fun q hq ↦ hq.1, alg_of_ev u W x hx⟩, hp, fun y _ ↦ ?_⟩
    obtain rfl : y = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    exact hpU
  · intro l k₁ k₂ p h₁ h₂
    have ho : IsOpen ((k₁.1 : Set (Tot I g)) ∩ F.shift l ⁻¹' (k₂.1 : Set (Tot I g))) :=
      (F.shift_analytic l k₁.2.1).continuousOn.isOpen_inter_preimage k₁.1.isOpen k₂.1.isOpen
    refine ⟨⟨⟨_, ho⟩, fun q hq ↦ k₁.2.1 q hq.1, alg_mono u (fun q hq ↦ hq.1) k₁.2.2⟩, ⟨h₁, h₂⟩,
      fun q hq ↦ ?_, fun q hq ↦ hq.2⟩
    rw [F.shift_zero]
    exact hq.1

end GlobalTheory.AnPer.MaxCharts

namespace GlobalTheory.AnPer

theorem period_unique : PUniq := by
  intro I _ g Λ _ F B _ X s _ σ u c per per' h h'
  exact GlobalTheory.T.periodClass_injective_of_rich_charts (MaxCharts.charts u) (MaxCharts.rich u) per per'
    ((h _ _ (MaxCharts.isFor u)).symm.trans (h' _ _ (MaxCharts.isFor u)))

end GlobalTheory.AnPer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiposAddSmul
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.SemiPosLarge

theorem semipos_add_smul : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  intro n Y _ _ _ _ _ _ ι La _ A H G hH
  obtain ⟨C⟩ := _root_.GlobalTheory.OTY.nonempty_cover n Y ι La A
  obtain ⟨k0, hk0⟩ := _root_.GlobalTheory.OTY.CoverCurv.curv_cover n Y ι La A C H G hH 0
  refine ⟨k0, fun k hk i y hy ξ => ?_⟩
  have hcurv := hk0 k hk

  have hex : ∃ a, C.chi a y ≠ 0 := by
    by_contra hno
    push_neg at hno
    have := C.sum_one y
    simp [hno] at this
  obtain ⟨a, ha⟩ := hex
  have hts : y ∈ tsupport (C.chi a) := subset_tsupport _ (Function.mem_support.2 ha)
  obtain ⟨hsrc, hball⟩ := C.supp a hts
  have hsm : A.SmoothFn (fun _ : Y => (0 : ℝ)) := fun _ => contDiffOn_const
  have ht := A.levi_transfer (G + k • H) (fun _ => (0 : ℝ)) hsm i (C.idx a) hy hsrc ξ
  simp only [add_zero] at ht ⊢
  rw [ht]
  have h1 := hcurv a (A.chart (C.idx a) y) hball
    (fderiv ℂ ((A.chart (C.idx a)) ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp
  rw [(A.chart (C.idx a)).left_inv hsrc, zero_mul] at h1
  exact h1

end GlobalTheory.SemiPosLarge
end

