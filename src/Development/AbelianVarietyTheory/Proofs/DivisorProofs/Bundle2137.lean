module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightLeOneOfFlat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

section Top

theorem coheight_le_one_of_flat {H S : Scheme.{0}} (p : H ⟶ S) [Flat p] (x : H)
    (hx : Order.coheight x ≤ 1) : Order.coheight (p x) ≤ 1 := by
  have hp := Flat.generalizingMap p
  have hx' := (Order.coheight_le_coe_iff (n := 1)).1 hx
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_
  obtain ⟨x', h₁, rfl⟩ := hp (show y ⤳ p x from hy.le)
  have hlt : x < x' := ⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩
  have hm : IsMax x' := by simpa using hx' x' hlt
  have : IsMax (p x') := fun w hw ↦ by
    obtain ⟨x'', h₂, rfl⟩ := hp (show w ⤳ p x' from hw)
    exact Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous
  simpa using this

theorem coheight_le_one_iff {X : Scheme.{0}} (x : X) :
    Order.coheight x ≤ 1 ↔ ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Iff.rfl

theorem height_le_one {R : Type} [CommRing R] (q : Sp R) (h : Order.coheight q ≤ 1) :
    q.asIdeal.height ≤ 1 := by
  rw [coheight_le_one_iff] at h
  have : q.asIdeal.IsPrime := q.2
  letI : Algebra R ((Sp R).presheaf.stalk q) := StructureSheaf.stalkAlgebra R q
  have : IsLocalization.AtPrime ((Sp R).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R q
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal] at h
  exact_mod_cast h

variable {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} [IsIntegral X]

theorem asIdeal_genericPoint (p : X ⟶ Sp R) [Flat p] : (p (genericPoint X)).asIdeal = ⊥ := by
  let o : Sp R := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  have h : o ⤳ p (genericPoint X) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨x, h₁, h₂⟩ := Flat.generalizingMap p h
  have : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
  rw [← this, h₂]

theorem cst_injective (p : X ⟶ Sp R) [Flat p] : Function.Injective (GlobalTheory.Desc.cst p) := by
  refine (injective_iff_map_eq_zero _).2 fun r hr => ?_
  by_contra h
  refine ((unitAt_cst_iff p (genericPoint X) r).2 ?_).ne_zero hr
  rwa [asIdeal_genericPoint]

theorem ringKrullDim_eq_one (p : X ⟶ Sp R) [Flat p] {x : X} (h : (p x).asIdeal ≠ ⊥)
    (hx : Order.coheight x ≤ 1) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  have h0 : Order.coheight x ≠ 0 := fun h0 => by
    rw [Order.coheight_eq_zero] at h0
    have h₁ : x ⤳ genericPoint X := h0 (show x ≤ genericPoint X from genericPoint_specializes x)
    obtain rfl : x = genericPoint X := (h₁.antisymm (genericPoint_specializes x)).eq
    exact h (asIdeal_genericPoint p)
  have : Order.coheight x = 1 := le_antisymm hx (Order.one_le_iff_ne_zero.2 h0)
  rw [this]; rfl

theorem eq_of_coheight_le_one (p : X ⟶ Sp R) [Smooth p] [GeometricallyConnected p] {x x' : X}
    (e : p x = p x') (h : (p x).asIdeal ≠ ⊥) (hx : Order.coheight x ≤ 1) (hx' : Order.coheight x' ≤ 1) :
    x = x' := by
  have := isIntegral_fiber_of_smooth p (p x)
  let ξ := p.fiberι (p x) (genericPoint _)
  have hξ : p ξ = p x := (p.range_fiberι (p x)).le ⟨_, rfl⟩
  have key : ∀ w : X, p w = p x → Order.coheight w ≤ 1 → w = ξ := by
    intro w hw hc
    obtain ⟨w', rfl⟩ := (p.range_fiberι (p x)).ge hw
    have hs : ξ ⤳ p.fiberι (p x) w' := (genericPoint_specializes w').map (p.fiberι (p x)).continuous
    by_contra hne
    have hlt : p.fiberι (p x) w' < ξ := ⟨hs, fun h' => hne (Specializes.antisymm h' hs).eq⟩
    have hm : IsMax ξ := by simpa using (Order.coheight_le_coe_iff (n := 1)).1 hc ξ hlt
    have h₁ : ξ ⤳ genericPoint X := hm (show ξ ≤ genericPoint X from genericPoint_specializes ξ)
    have h₂ : ξ = genericPoint X := (h₁.antisymm (genericPoint_specializes ξ)).eq
    apply h
    rw [← hξ, h₂]
    exact asIdeal_genericPoint p
  rw [key x rfl hx, key x' e.symm hx']

end Top

section Ring

theorem exists_common_field {R A B : Type} [CommRing R] [CommRing A] [CommRing B] (ρ : R →+* A)
    (ρ' : R →+* B) (q : Sp A) (q' : Sp B) (h : spMap ρ q = spMap ρ' q') :
    ∃ (Ω : Type) (_ : Field Ω) (u : A →+* Ω) (u' : B →+* Ω), RingHom.ker u = q.asIdeal ∧
      RingHom.ker u' = q'.asIdeal ∧ u.comp ρ = u'.comp ρ' := by
  obtain ⟨w, h₁, h₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := spMap ρ) (g := spMap ρ') q q' h
  let k := (pullback (spMap ρ) (spMap ρ')).fromSpecResidueField w
  have hk : ∀ {C : Type} [CommRing C] (g : pullback (spMap ρ) (spMap ρ') ⟶ Sp C),
      RingHom.ker (Spec.preimage (k ≫ g)).hom = (g w).asIdeal := by
    intro C _ g
    let o : Spec ((pullback (spMap ρ) (spMap ρ')).residueField w) := (⊥ : PrimeSpectrum _)
    have e := congrArg (fun m => m o) (Spec.map_preimage (k ≫ g))
    have e' : (k ≫ g) o = g w := by
      rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    rw [← e', ← e]
    rfl
  refine ⟨_, inferInstance, (Spec.preimage (k ≫ pullback.fst _ _)).hom,
    (Spec.preimage (k ≫ pullback.snd _ _)).hom, (hk _).trans (by rw [h₁]), (hk _).trans (by rw [h₂]), ?_⟩
  have : CommRingCat.ofHom ρ ≫ Spec.preimage (k ≫ pullback.fst _ _) =
      CommRingCat.ofHom ρ' ≫ Spec.preimage (k ≫ pullback.snd _ _) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage, Category.assoc,
      Category.assoc, pullback.condition]
  exact congrArg CommRingCat.Hom.hom this

theorem dvr_of_height {E : Type} [CommRing E] [IsRegularLocalRing E] [IsDomain E]
    (h : (maximalIdeal E).height ≤ 1) (h0 : maximalIdeal E ≠ ⊥) : IsDiscreteValuationRing E := by
  have : IsPrincipalIdealRing E :=
    GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one (by
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]; exact_mod_cast h)
  exact ⟨h0⟩

theorem height_le_of_map {A E : Type} [CommRing A] [IsNoetherianRing A] [CommRing E] [IsLocalRing E]
    [IsNoetherianRing E] (a : A →+* E) (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1)
    (h₁ : (maximalIdeal E).comap a = q) (h₂ : q.map a = maximalIdeal E) : (maximalIdeal E).height ≤ 1 := by
  letI := a.toAlgebra
  have : (maximalIdeal E).LiesOver q := ⟨h₁.symm⟩
  refine (Ideal.height_le_height_add_of_liesOver q (maximalIdeal E)).trans ?_
  have h₃ : q.map (algebraMap A E) = maximalIdeal E := h₂
  have h₄ : (maximalIdeal E).map (Ideal.Quotient.mk (q.map (algebraMap A E))) = ⊥ := by
    rw [← h₃, Ideal.map_quotient_self]
  have : Nontrivial (E ⧸ q.map (algebraMap A E)) :=
    Ideal.Quotient.nontrivial_iff.2 (h₃ ▸ (maximalIdeal.isMaximal E).ne_top)
  rw [h₄, Ideal.height_bot, add_zero]
  exact hq

theorem injective_of_flat {A E : Type} [CommRing A] [IsDomain A] [CommRing E] [Nontrivial E]
    {a : A →+* E} (h : a.Flat) : Function.Injective a := by
  letI := a.toAlgebra
  have : Module.Flat A E := h
  exact FaithfulSMul.algebraMap_injective A E

theorem dvd_pow_of_dim {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (h : ringKrullDim O ≤ 1)
    {g t : O} (hg : g ≠ 0) (ht : ¬ IsUnit t) : ∃ n : ℕ, g ∣ t ^ n := by
  have : Ring.KrullDimLE 1 O := Ring.krullDimLE_iff.2 h
  have : t ∈ (Ideal.span {g}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hJ, hp⟩
    have hne : J ≠ ⊥ := fun e => hg (by simpa [e] using hJ)
    rw [eq_maximalIdeal (hp.isMaximal_of_ne_bot hne)]
    exact ht
  obtain ⟨n, hn⟩ := this
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

end Ring

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

theorem mem_spanBy_iff (T : Set F₁) (v : F₁) :
    v ∈ spanBy c T ↔ letI := c.toAlgebra; v ∈ Submodule.span R₁ T := by
  letI := c.toAlgebra
  rw [Submodule.mem_span_set']
  constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    exact ⟨n, r, fun i => ⟨t i, ht i⟩, rfl⟩
  · rintro ⟨n, r, t, rfl⟩
    exact ⟨n, r, fun i => t i, fun i => (t i).2, rfl⟩

variable {c}

theorem spanBy_zero (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (zero_mem _)

theorem spanBy_add {T : Set F₁} {u v : F₁} (hu : u ∈ spanBy c T) (hv : v ∈ spanBy c T) :
    u + v ∈ spanBy c T :=
  (mem_spanBy_iff c T _).2 (add_mem ((mem_spanBy_iff c T _).1 hu) ((mem_spanBy_iff c T _).1 hv))

theorem spanBy_smul {T : Set F₁} (r : R₁) {u : F₁} (hu : u ∈ spanBy c T) : c r * u ∈ spanBy c T :=
  letI := c.toAlgebra
  (mem_spanBy_iff c T _).2 (Submodule.smul_mem _ r ((mem_spanBy_iff c T _).1 hu))

theorem spanBy_induction {T : Set F₁} {P : F₁ → Prop} (h₀ : P 0) (h₁ : ∀ t ∈ T, P t)
    (h₂ : ∀ u v, P u → P v → P (u + v)) (h₃ : ∀ r u, P u → P (c r * u)) {v : F₁}
    (hv : v ∈ spanBy c T) : P v := by
  letI := c.toAlgebra
  rw [mem_spanBy_iff] at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact h₁ x hx
  | zero => exact h₀
  | add x y _ _ hx hy => exact h₂ x y hx hy
  | smul r x _ hx => exact h₃ r x hx

end Span

end GlobalTheory.Desc.GaussPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCup
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem sgn_mem_rel_of_mem {x : DR R B} (hx : x ∈ rel R δ) : sgn x ∈ rel R δ := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, a, ha, rfl⟩ := hx
    rw [sgn_ι]; exact neg_mem (Ideal.subset_span ⟨n, a, ha, rfl⟩)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul r x _ ih => rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ ih

theorem mul_ι_mem_rel {x : DR R B} (hx : x ∈ rel R δ) (ω : Ω[B⁄R]) : x * ι1 ω ∈ rel R δ := by
  have h := ι_mul ω (sgn x)
  rw [sgn_sgn] at h
  rw [← h]; exact Ideal.mul_mem_left _ _ (sgn_mem_rel_of_mem δ hx)

theorem mem_divPowerCompatFormRelSubmodule_two_iff {x : Om R B 2} : x ∈ N R δ 2 ↔ (x : DR R B) ∈ rel R δ := Iff.rfl

theorem wedge_mem_N {x y : Ω[B⁄R]} (h : x ∈ N1 R δ ∨ y ∈ N1 R δ) : wedge R B x y ∈ N R δ 2 := by
  rw [mem_divPowerCompatFormRelSubmodule_two_iff, coe_wedge]
  rcases h with h | h
  · exact mul_ι_mem_rel δ h y
  · exact Ideal.mul_mem_left _ _ h


variable (R) in
def kwedge : K1 R δ →ₗ[B] K1 R δ →ₗ[B] K R δ 2 :=
  LinearMap.liftQ₂ _ _ ((wedge R B).compr₂ (N R δ 2).mkQ)
    (fun x hx ↦ LinearMap.ext fun y ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inl hx)))
    (fun y hy ↦ LinearMap.ext fun x ↦ (Submodule.Quotient.mk_eq_zero _).2 (wedge_mem_N δ (Or.inr hy)))

theorem kwedge_mk (x y : Ω[B⁄R]) :
    kwedge R δ (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (wedge R B x y) := rfl

end Ring

section Ring2

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} (δ : DividedPowers J)

theorem kwedge_swap (x y : K1 R δ) : kwedge R δ x y = -kwedge R δ y x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, kwedge_mk, wedge_swap, Submodule.Quotient.mk_neg]

theorem divPowerCompatFunctionDifferential_mul (a b : B) : kd0 R δ (a * b) = a • kd0 R δ b + b • kd0 R δ a := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.leibniz, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul_eq_wedge_add (b : B) (x : K1 R δ) : kd1 R δ (b • x) = kwedge R δ (kd0 R δ b) x + b • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, divPowerCompatFunctionDifferential_apply, kwedge_mk, dOne_smul, Submodule.Quotient.mk_add,
    Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_wedge_of_closed {x y : K1 R δ} (hx : kd1 R δ x = 0) (hy : kd1 R δ y = 0) : kd2 R δ (kwedge R δ x y) = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [divPowerCompatOneFormDerivative_mk, Submodule.Quotient.mk_eq_zero, mem_divPowerCompatFormRelSubmodule_two_iff, coe_dOne] at hx hy
  rw [kwedge_mk, divPowerCompatTwoFormDerivative_mk, Submodule.Quotient.mk_eq_zero]
  change dDR R B (ι1 x * ι1 y) ∈ rel R δ
  rw [dDR_mul, sgn_ι, neg_mul]
  exact add_mem (neg_mem (Ideal.mul_mem_left _ _ hy)) (mul_ι_mem_rel δ hx y)

variable {δ} {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul_function (b : B) (x : K1 R δ) : km1 h hd (b • x) = α b • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, h.oneFormMap_smul_semilinear, Submodule.Quotient.mk_smul]

theorem km_kwedge (x y : K1 R δ) : km h hd 2 (kwedge R δ x y) = kwedge R' δ' (km1 h hd x) (km1 h hd y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [kwedge_mk, km_mk, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, kwedge_mk, h.mOm_wedge]

end Ring2

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

def cupK (a b : (KK κ t).T1) : (KK κ t).T2 :=
  (fun _ T' T'' φ ψ ↦ (show T''.B from (KK κ t).M0.map ψ (a.1 _ T' φ)) * (show T''.B from b.1 T' T'' ψ),
    fun T T' φ ↦ (show T'.B from a.1 T T' φ) • b.2 T' - (show T'.B from b.1 T T' φ) • (KK κ t).M1.map φ (a.2 T),
    fun T ↦ kwedge R T.δ (a.2 T) (b.2 T))

theorem crystallineCompatibleFormsComplex_cocycleOne_components (k : (KK κ t).Z1) :
    (∀ {T T' T'' : Thick κ t} (φ : T ⟶ T') (ψ : T' ⟶ T''),
      (k.1.1 T T'' (φ ≫ ψ) : T''.B) = ψ.φ (k.1.1 T T' φ) + k.1.1 T' T'' ψ) ∧
    (∀ {T T' : Thick κ t} (φ : T ⟶ T'), k.1.2 T' = (KK κ t).M1.map φ (k.1.2 T) + kd0 R T'.δ (k.1.1 T T' φ)) ∧
    ∀ T : Thick κ t, kd1 R T.δ (k.1.2 T) = 0 := by
  have h : (KK κ t).D1 k.1 = 0 := k.2
  refine ⟨fun {T T' T''} φ ψ ↦ ?_, fun {T T'} φ ↦ ?_, fun T ↦ ?_⟩
  · have := congrFun (congrFun (congrFun (congrFun (congrFun (congrArg Prod.fst h) T) T') T'') φ) ψ
    change ψ.φ (k.1.1 T T' φ) - k.1.1 T T'' (φ ≫ ψ) + k.1.1 T' T'' ψ = 0 at this
    linear_combination -this
  · have := congrFun (congrFun (congrFun (congrArg (fun c ↦ c.2.1) h) T) T') φ
    change k.1.2 T' - (KK κ t).M1.map φ (k.1.2 T) - kd0 R T'.δ (k.1.1 T T' φ) = 0 at this
    rw [sub_sub, sub_eq_zero] at this
    exact this
  · exact congrFun (congrArg (fun c ↦ c.2.2) h) T

end Site

section Site2

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem cupK_mem (a b : (KK κ t).Z1) : cupK a.1 b.1 ∈ (KK κ t).Z2 := by
  obtain ⟨ha1, ha2, ha3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components a
  obtain ⟨hb1, hb2, hb3⟩ := crystallineCompatibleFormsComplex_cocycleOne_components b
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · change χ.φ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ) + χ.φ (a.1.1 T T'' (φ ≫ ψ)) * b.1.1 T'' T''' χ =
      (ψ ≫ χ).φ (a.1.1 T T' φ) * b.1.1 T' T''' (ψ ≫ χ) + χ.φ (a.1.1 T' T'' ψ) * b.1.1 T'' T''' χ
    rw [ha1 φ ψ, hb1 ψ χ, Thick.comp_φ, map_mul, map_add (f := _)]
    ring
  · have hs : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B) (x : K1 R T.δ),
        (KK κ t).M1.map φ (r • x) = φ.φ r • (KK κ t).M1.map φ x := fun φ r x ↦ divPowerCompatOneFormMap_smul_function (SemiHom.of_algHom φ.φ) φ.dp r x
    have hd : ∀ {T T' : Thick κ t} (φ : T ⟶ T') (r : T.B),
        (KK κ t).M1.map φ (kd0 R T.δ r) = kd0 R T'.δ (φ.φ r) := fun φ r ↦ divPowerCompatOneFormMap_functionDifferential (SemiHom.of_algHom φ.φ) φ.dp r
    change (a.1.1 T T'' (φ ≫ ψ) : T''.B) • b.1.2 T'' - (b.1.1 T T'' (φ ≫ ψ) : T''.B) • (KK κ t).M1.map (φ ≫ ψ) (a.1.2 T) =
      (KK κ t).M1.map ψ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T)) +
      ((a.1.1 T' T'' ψ : T''.B) • b.1.2 T'' - (b.1.1 T' T'' ψ : T''.B) • (KK κ t).M1.map ψ (a.1.2 T')) +
      kd0 R T''.δ (ψ.φ (a.1.1 T T' φ) * b.1.1 T' T'' ψ)
    rw [ha1 φ ψ, hb1 φ ψ, (KK κ t).M1.map_comp, hb2 ψ, ha2 φ]
    simp only [map_add (f := _), map_sub, hs, hd, divPowerCompatFunctionDifferential_mul, smul_add, smul_sub, add_smul]
    module
  · have hd1 : kd1 R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) = 0 :=
      ((KK κ t).diffOne_natural φ _).trans (by rw [show (KK κ t).d1 T (a.1.2 T) = 0 from ha3 T, map_zero])
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = (KK κ t).M2.map φ (kwedge R T.δ (a.1.2 T) (b.1.2 T)) +
      kd1 R T'.δ ((a.1.1 T T' φ : T'.B) • b.1.2 T' - (b.1.1 T T' φ : T'.B) • (KK κ t).M1.map φ (a.1.2 T))
    rw [map_sub, divPowerCompatOneFormDerivative_smul_eq_wedge_add, divPowerCompatOneFormDerivative_smul_eq_wedge_add, hb3 T', hd1, smul_zero, smul_zero, add_zero, add_zero]
    change _ = km (SemiHom.of_algHom φ.φ) φ.dp 2 _ + _
    rw [km_kwedge]
    change kwedge R T'.δ (a.1.2 T') (b.1.2 T') = kwedge R T'.δ ((KK κ t).M1.map φ (a.1.2 T)) ((KK κ t).M1.map φ (b.1.2 T)) + _
    rw [ha2 φ, hb2 φ]
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [kwedge_swap T'.δ (kd0 R T'.δ (b.1.1 T T' φ))]
    abel
  · exact divPowerCompatTwoFormDerivative_wedge_of_closed T.δ (ha3 T) (hb3 T)

end Site2

section Main

variable {D : Data} (Λ : Lift D)

theorem Lift.lift_res2_cup {k k' : (KK D.κ D.t).T1} {w w' : Tot1 (OAff D.s)}
    (hk : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k) w) (hk' : Λ.Res1 (((KK D.κ D.t).resMap Λ.L).p1 k') w') :
    Λ.Res2 (((KK D.κ D.t).resMap Λ.L).p2 (cupK k k')) (cupTot (OAff D.s) w w') := by
  have e1 : ∀ U V a, (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w.1 U V a) := hk.1
  have e1' : ∀ U V a, (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) = Λ.e V (w'.1 U V a) := hk'.1
  have e2 : ∀ U, k.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w.2 U)) := hk.2
  have e2' : ∀ U, k'.2 (Λ.L.obj U) = Submodule.Quotient.mk ((Λ.semi U).m1 (w'.2 U)) := hk'.2
  refine ⟨fun U V W a b ↦ ?_, fun U V a ↦ ?_, fun U ↦ ?_⟩
  · change (Λ.L.map b).φ (k.1 _ _ (Λ.L.map a)) * (k'.1 _ _ (Λ.L.map b) : (Λ.L.obj W).B) =
      Λ.e W (mp (OAff D.s) b (w.1 U V a) * w'.1 V W b)
    rw [e1, e1', map_mul, Λ.nat]
  · have key : ∀ x, (SemiHom.of_algHom (Λ.L.map a).φ).m1 ((Λ.semi U).m1 x) = (Λ.semi V).m1 (p1 (OAff D.s) a x) :=
      fun x ↦ (SemiHom.oneFormMap_comp_oneFormMap (Λ.semi U) (SemiHom.of_algHom _) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
        (fun b ↦ (Λ.nat a b).symm) x).trans
        (SemiHom.oneFormMap_comp_oneFormMap (semiHom_mp (OAff D.s) a) (Λ.semi V) ((semiHom_mp (OAff D.s) a).comp (Λ.semi V))
          (fun _ ↦ rfl) x).symm
    change (k.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • k'.2 (Λ.L.obj V) -
        (k'.1 _ _ (Λ.L.map a) : (Λ.L.obj V).B) • km1 (SemiHom.of_algHom (Λ.L.map a).φ) (Λ.L.map a).dp (k.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi V).m1 (w.1 U V a • w'.2 V - w'.1 U V a • p1 (OAff D.s) a (w.2 U)))
    rw [e1, e1', e2' V, e2 U, divPowerCompatOneFormMap_mk, key, map_sub, SemiHom.oneFormMap_smul_semilinear, SemiHom.oneFormMap_smul_semilinear, Submodule.Quotient.mk_sub,
      Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    rfl
  · change kwedge D.R (Λ.L.obj U).δ (k.2 (Λ.L.obj U)) (k'.2 (Λ.L.obj U)) =
      Submodule.Quotient.mk ((Λ.semi U).mOm 2 (wedge D.R _ (w.2 U) (w'.2 U)))
    rw [e2, e2', kwedge_mk, SemiHom.mOm_wedge]

theorem Lift.lift_rel2_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' →
    Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  intro D Λ a b h h' ha hb
  obtain ⟨k, f, w, hf, hw, hkf, hr⟩ := ha
  obtain ⟨k', g, w', hg, hw', hkg, hr'⟩ := hb
  refine ⟨⟨cupK k.1 k'.1, cupK_mem k k'⟩, cupZ _ f g, cupZZ _ w w', ?_, ?_, ?_, Λ.lift_res2_cup hr hr'⟩
  · rw [← hf, ← hg]; rfl
  · rw [← hw, ← hw']; rfl
  · funext T T' T'' φ ψ
    change ψ.φ (k.1.1 T T' φ) * (k'.1.1 T' T'' ψ : T''.B) = ψ.φ (f.1 T T' φ) * g.1 T' T'' ψ
    rw [hkf, hkg]

end Main

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleCotangentValueSubOfCoboundaryA
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

attribute [local instance] cotOp cotCentral cotTower

theorem cotSnd_cotPt_eq_dUnit (R : Type) [CommRing R] (D : Type) [CommRing D] [Bialgebra R D] (z : D) :
    cotSnd R D (cotPt R D z) = dUnit (R := R) z := by
  change TrivSqZeroExt.snd (algebraMap R (TrivSqZeroExt R (Cot R D)) (Coalgebra.counit z) +
    TrivSqZeroExt.inr (AugCot.d (Bialgebra.counitAlgHom R D) z)) = _
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

theorem crystallineCocycleCotangentValue_sub_of_coboundary (R : Type) [CommRing R]
    (X : Over (Sp R)) (D : Type) [CommRing D] [Bialgebra R D] (y : Pt X D)
    (f f' : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (k : C0 (O (dp0 R) (X.hom ≫ 𝟙 _)))
    (h : d0 _ k = f.1 - f'.1) :
    cotVal f y - cotVal f' y = dUnit (R := R) (A := D) (k (trivAt y)) := by
  have hf : f - f' = ⟨d0 _ k, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ k⟩ := Subtype.ext h.symm
  let E := cotExt R D
  let p : D →ₐ[R] E.C := cotPt R D
  let y' : Pt X E.C := spOver p ≫ y
  let k₀ : E.B := k (Thick.triv E.B _ (E.red_w y'.w))
  let i : E.C := E.i k₀
  have h1 : E.val y'.left y'.w f - E.val y'.left y'.w f' = k (trivAt y') - i := by
    rw [← map_sub, hf]
    exact E.tangentValue_coboundary y'.left y'.w k
  have h2 : fv f D E.C p y - fv f' D E.C p y = k (trivAt y') - p (k (trivAt y)) := by
    let τ : trivAt y ⟶ trivAt y' := trivMap p y
    have e := congrArg (fun g : C1 (O (dp0 R) (X.hom ≫ 𝟙 _)) ↦ g _ _ τ) h
    change d0 _ k _ _ τ = _ at e
    rw [amitsur_d0_apply, mp_O] at e
    exact e.symm
  have hi : cotSnd R D i = 0 := by
    exact TrivSqZeroExt.snd_inl (M := Cot R D) k₀
  change cotSnd R D (E.val y'.left y'.w f - fv f D E.C p y) -
    cotSnd R D (E.val y'.left y'.w f' - fv f' D E.C p y) = _
  rw [← map_sub, sub_sub_sub_comm, h1, h2, sub_sub_sub_cancel_left, map_sub]
  rw [show p (k (trivAt y)) = cotPt R D (k (trivAt y)) from rfl,
    cotSnd_cotPt_eq_dUnit, hi, sub_zero]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentDatumFrameCocycleUnitStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descentDatum_frame_cocycle_unit : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (L : LB X), L.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f L i j)ˣ), DescCompat f L φ → DescCocycle f L φ →
    ∀ (V : Y.Opens) (t : ∀ i, Γ(X, f ⁻¹ᵁ V ⊓ L.U i)ˣ), (∀ (i j : L.ι) (x : X), f x ∈ V → x ∈ L.U i → x ∈ L.U j →
      gm (𝟙 X) x _ (t i) = gm (𝟙 X) x _ (L.g i j) * gm (𝟙 X) x _ (t j)) →
    ∃ c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ,
      (∀ (z : ↥(pullback f f)) (i j : L.ι), f (pullback.fst f f z) ∈ V → pullback.fst f f z ∈ L.U i →
        pullback.snd f f z ∈ L.U j →
        gm (𝟙 _) z _ c = gm (pullback.fst f f) z _ (t i) * gm (𝟙 _) z _ (φ i j) * (gm (pullback.snd f f) z _ (t j))⁻¹) ∧
      ∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c := by
  first | exact @GlobalTheory.LBDescent.frame_cocycle | exact GlobalTheory.LBDescent.frame_cocycle | (intros; apply GlobalTheory.LBDescent.frame_cocycle <;> assumption)
end

