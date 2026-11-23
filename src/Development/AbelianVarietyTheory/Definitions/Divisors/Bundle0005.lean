module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import GroundTheory.AutomorphicForms.GKModules.RightRegular
public import GroundTheory.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0256

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BicechC
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

section Bi

variable {k : Type} [Field k] {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
  {E E' E'' : Type} [AddCommGroup E] [Module k E] [AddCommGroup E'] [Module k E'] [AddCommGroup E''] [Module k E'']


variable (k ι κ E'') in
def biD : (Finset ι × Finset κ → E'') →ₗ[k] (Finset ι × Finset κ → E'') :=
  LinearMap.pi fun x =>
    (∑ i ∈ x.1, GlobalTheory.cubeSign x.1 i • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1.erase i, x.2)) +
      ((-1 : ℤ) ^ (x.1.card + 1)) •
        ∑ j ∈ x.2, GlobalTheory.cubeSign x.2 j • LinearMap.proj (R := k) (φ := fun _ : Finset ι × Finset κ => E'') (x.1, x.2.erase j)

def bicechC (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') (n : ℤ) :
    Submodule k (Finset ι × Finset κ → E'') :=
  Submodule.pi Set.univ fun x =>
    if x.1.Nonempty ∧ x.2.Nonempty ∧ ((x.1.card + x.2.card : ℕ) : ℤ) = n + 2 then Submodule.map₂ μ (A x.1) (B x.2) else ⊥

def bicech (μ : E →ₗ[k] E' →ₗ[k] E'') (A : Finset ι → Submodule k E) (B : Finset κ → Submodule k E') :
    Cx k (Finset ι × Finset κ → E'') :=
  ⟨bicechC μ A B, biD k ι κ E''⟩

def boxC (μ : E →ₗ[k] E' →ₗ[k] E'') (a : Finset ι → E) (b : Finset κ → E') : Finset ι × Finset κ → E'' :=
  fun x => μ (a x.1) (b x.2)


end Bi

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.Cris

open CatCoh

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}

def derSec {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] (D : Derivation R B M) : B →ₐ[R] TrivSqZeroExt B M where
  toFun b := TrivSqZeroExt.inl b + TrivSqZeroExt.inr (D b)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

section
variable {B M : Type} [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module B M] [Module Bᵐᵒᵖ M] [IsCentralScalar B M] [Module R M] [IsScalarTower R B M]
    [IsScalarTower R Bᵐᵒᵖ M] (D : Derivation R B M) (b : B)

@[simp] theorem fst_derSec : (derSec D b).fst = b := by
  exact add_zero b

@[simp] theorem snd_derSec : (derSec D b).snd = D b := by
  exact zero_add (D b)

end

section Conn

open KaehlerDifferential

variable (R) (B B' : Type) [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']

@[reducible] def opModule : Module Bᵐᵒᵖ Ω[B⁄R] :=
  Module.compHom _ ((RingHom.id B).fromOpposite mul_comm)

attribute [local instance] opModule

theorem isCentralScalar_kaehler : IsCentralScalar B Ω[B⁄R] := ⟨fun _ _ ↦ rfl⟩

theorem isScalarTower_kaehler : IsScalarTower R Bᵐᵒᵖ Ω[B⁄R] := ⟨fun r b m ↦ smul_assoc r b.unop m⟩

attribute [local instance] isCentralScalar_kaehler isScalarTower_kaehler

abbrev diagExt : SqExt R := SqExt.ofModule R B Ω[B⁄R]

abbrev diagSec : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R] := derSec (D R B)

def diagMap [Algebra B B'] [IsScalarTower R B B'] :
    TrivSqZeroExt B Ω[B⁄R] →ₐ[R] TrivSqZeroExt B' Ω[B'⁄R] where
  toFun c := TrivSqZeroExt.inl (algebraMap B B' c.fst) +
    TrivSqZeroExt.inr (KaehlerDifferential.map R R B B' c.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp
  commutes' r := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl', ← IsScalarTower.algebraMap_apply]


variable {B B'} in
theorem fst_diagMap [Algebra B B'] [IsScalarTower R B B'] (c : TrivSqZeroExt B Ω[B⁄R]) :
    (diagMap R B B' c).fst = algebraMap B B' c.fst := by
  exact add_zero _


variable {B B'} in
theorem snd_diagMap [Algebra B B'] [IsScalarTower R B B'] (c : TrivSqZeroExt B Ω[B⁄R]) :
    (diagMap R B B' c).snd = KaehlerDifferential.map R R B B' c.snd := by
  exact zero_add _

variable {R B B'} {s : X ⟶ Sp R}

def connForm (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) : Ω[B⁄R] :=
  TrivSqZeroExt.snd (R := B) (ev f ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) -
    ev f ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)))

theorem crystallineConnectionForm_coboundaryZero (g : C0 (O (dp0 R) s)) (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    connForm ⟨d0 _ g, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ g⟩ x hx = D R B (g (Thick.triv B x hx)) := by
  change TrivSqZeroExt.snd (R := B) ((_ - TrivSqZeroExt.inl _) - (_ - diagSec R B _)) = _
  simp

theorem connForm_map [Algebra B B'] [IsScalarTower R B B'] (f : Z1 (O (dp0 R) s)) (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (x' : Sp B' ⟶ X) (hx' : x' ≫ s = spMap (algebraMap R B'))
    (e : spMap (algebraMap B B') ≫ x = x') :
    connForm f x' hx' - KaehlerDifferential.map R R B B' (connForm f x hx) =
      D R B' (ev f (Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx')
        (IsScalarTower.toAlgHom R B B') e)) := by
  let a := Thick.trivHom (hx := hx) (T := Thick.triv B' x' hx') (IsScalarTower.toAlgHom R B B') e
  let Φ := (diagExt R B).thickHom (diagExt R B') (diagMap R B B') (IsScalarTower.toAlgHom R B B')
    (fun c ↦ (fst_diagMap R c).symm) hx hx' e
  have k1 := ev_sq f a ((diagExt R B').secHom hx' (diagExt R B').i fun _ ↦ rfl)
    ((diagExt R B).secHom hx (diagExt R B).i fun _ ↦ rfl) Φ fun c ↦
      TrivSqZeroExt.ext (fst_diagMap R (TrivSqZeroExt.inl c)).symm
        ((snd_diagMap R (TrivSqZeroExt.inl c)).trans (map_zero _)).symm
  have k2 := ev_sq f a ((diagExt R B').secHom hx' (diagSec R B') (fst_derSec _))
    ((diagExt R B).secHom hx (diagSec R B) (fst_derSec _)) Φ fun c ↦
      by
      change diagSec R B' (algebraMap B B' c) = diagMap R B B' (diagSec R B c)
      ext
      · rw [fst_diagMap, fst_derSec, fst_derSec]
      · rw [snd_diagMap, snd_derSec, snd_derSec, KaehlerDifferential.map_D]
  have l1 := congrArg (TrivSqZeroExt.snd (R := B')) k1
  have l2 := congrArg (TrivSqZeroExt.snd (R := B')) k2
  change 0 + _ = (diagMap R B B' _).snd + _ at l1
  change (diagSec R B' (ev f a)).snd + _ = (diagMap R B B' _).snd + _ at l2
  rw [snd_diagMap] at l1 l2
  rw [snd_derSec] at l2
  simp only [connForm, TrivSqZeroExt.snd_sub, map_sub]
  have key : ∀ a b c d e f : Ω[B'⁄R], 0 + a = c + e → f + b = d + e → a - b - (c - d) = f :=
    fun a b c d e f h1 h2 ↦ by linear_combination (norm := abel1) h1 - h2
  exact key _ _ _ _ _ _ l1 l2

end Conn

section Chern

def evalAt {B : Type} [CommRing B] (x : Sp B ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

variable (γ : DividedPowers I) (s : X ⟶ Sp R)

def IsSmall {ι : Type} (U : ι → X.Opens) : ObjectProperty (Thick γ s) :=
  fun T ↦ ∃ i, ⊤ ≤ T.x ⁻¹ᵁ U i


variable {γ s} in
theorem Thick.Hom.le_preimage {T T' : Thick γ s} (φ : T ⟶ T') {U : X.Opens} (h : ⊤ ≤ T.x ⁻¹ᵁ U) :
    ⊤ ≤ T'.x ⁻¹ᵁ U := by
  rw [← φ.pt]
  exact fun p _ ↦ h (Set.mem_univ ((spMap φ.φ₀) p))

def IsChern (L : LB X) (z : H2 γ s) : Prop :=
  ∃ (i : (IsSmall γ s L.U).FullSubcategory → L.ι) (hi : ∀ T, ⊤ ≤ T.obj.x ⁻¹ᵁ L.U (i T))
    (u : ∀ T T' : (IsSmall γ s L.U).FullSubcategory, (T ⟶ T') → T'.obj.B)
    (ℓ : Z2 ((IsSmall γ s L.U).ι ⋙ O γ s)),
    (∀ T T' φ, T'.obj.π (u T T' φ) = evalAt T'.obj.x (L.U (i T') ⊓ L.U (i T))
      (le_inf (hi T') (φ.hom.le_preimage (hi T))) (L.g (i T') (i T)).val) ∧
    (∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J ∧
      dpExp T''.obj.δ (ℓ.1 T T' T'' φ ψ) * u T T'' (φ ≫ ψ) = ψ.hom.φ (u T T' φ) * u T' T'' ψ) ∧
    (CoefMap.restrict (O γ s) (IsSmall γ s L.U).ι).pull2 z = H2.mk _ ℓ

theorem isChern_zero (L : LB X) (h : ∀ i j, L.g i j = 1) : IsChern γ s L 0 := by
  refine ⟨fun T ↦ T.property.choose, fun T ↦ T.property.choose_spec, fun _ _ _ ↦ 1, 0,
    fun T T' φ ↦ by rw [h, Units.val_one, map_one, map_one], fun T T' T'' φ ψ ↦ ⟨T''.obj.J.zero_mem, ?_⟩,
    by rw [map_zero, map_zero]⟩
  change dpExp T''.obj.δ 0 * 1 = _
  rw [dpExp_zero, map_one]

end Chern

section Examples

theorem firstDeRham_base_eq_zero (s : X ⟶ Sp R) [IsIso s] (c : FirstDeRham s) : c = 0 := by
  have hx : inv s ≫ s = spMap (algebraMap R R) := by rw [IsIso.inv_hom_id]; exact (spMap_id R).symm
  refine H1.eq_zero_of_isInitial _ (T₀ := Thick.triv R (inv s) hx)
    (Limits.IsInitial.ofUniqueHom (fun T ↦ Thick.trivHom (Algebra.ofId R T.B) ?_) fun T m ↦ ?_) c
  · rw [IsIso.comp_inv_eq]; exact T.w.symm
  · have hφ : ∀ b : R, m.φ b = (Algebra.ofId R T.B) b :=
      fun b ↦ (m.φ.commutes b).trans ((Algebra.ofId R T.B).commutes b).symm
    exact Thick.Hom.ext' (AlgHom.ext hφ)

open Polynomial

abbrev lineStr (R : Type) [CommRing R] : Sp R[X] ⟶ Sp R := spMap (algebraMap R R[X])

def coordLift (T : Thick (dp0 R) (lineStr R)) : T.B := (T.surj ((Spec.preimage T.x).hom Polynomial.X)).choose

theorem π_coordLift (T : Thick (dp0 R) (lineStr R)) :
    T.π (coordLift T) = (Spec.preimage T.x).hom Polynomial.X := (T.surj _).choose_spec

theorem coordLift_sub_mem {T T' : Thick (dp0 R) (lineStr R)} (φ : T ⟶ T') :
    coordLift T' - φ.φ (coordLift T) ∈ T'.J := by
  rw [← T'.ker, map_sub, ← φ.comm, π_coordLift, π_coordLift, ← φ.pt, sub_eq_zero]
  have : Spec.preimage (spMap φ.φ₀ ≫ T.x) = Spec.preimage T.x ≫ CommRingCat.ofHom φ.φ₀ := by
    apply Spec.map_injective
    simp
  rw [this]; rfl

theorem dpow_two_add {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {a b : B} (ha : a ∈ J)
    (hb : b ∈ J) : δ.dpow 2 (a + b) = δ.dpow 2 a + a * b + δ.dpow 2 b := by
  rw [δ.dpow_add ha hb]
  simp [Finset.Nat.antidiagonal_succ, δ.dpow_zero ha, δ.dpow_zero hb, δ.dpow_one ha, δ.dpow_one hb]
  ring

def tdt (R : Type) [CommRing R] : Form (lineStr R) :=
  ⟨⟨fun T T' φ ↦ φ.φ (coordLift T) * (coordLift T' - φ.φ (coordLift T)) +
      T'.δ.dpow 2 (coordLift T' - φ.φ (coordLift T)), fun T T' T'' φ ψ ↦ by
    have e : coordLift T'' - (φ ≫ ψ).φ (coordLift T) =
        ψ.φ (coordLift T' - φ.φ (coordLift T)) + (coordLift T'' - ψ.φ (coordLift T')) := by simp
    have h1 := ψ.mem (coordLift_sub_mem φ)
    have h2 := coordLift_sub_mem ψ
    have h3 : ψ.φ (T'.δ.dpow 2 (coordLift T' - φ.φ (coordLift T))) =
      T''.δ.dpow 2 (ψ.φ (coordLift T' - φ.φ (coordLift T))) := ψ.dp.map_dpow (coordLift_sub_mem φ)
    change (_ * _ + T''.δ.dpow 2 (_ - _) : T''.B) = ψ.φ (_ + _) + (_ * _ + _)
    rw [e, dpow_two_add _ h1 h2, map_add (f := _), h3]
    simp only [map_mul, map_sub, Thick.comp_φ]
    ring⟩, fun T T' φ _ h ↦ by
    have := coordLift_sub_mem φ
    rw [h, Ideal.mem_bot] at this
    change (_ * _ + _ : T'.B) = 0
    rw [this, mul_zero, zero_add, dpow_eval_zero _ two_ne_zero]⟩

end Examples

end GlobalTheory.Cris
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsCorrOpOfAvg
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.GalV

variable (l : ℕ) [Fact l.Prime]

abbrev Htot (E : Spc) : Type 1 := DirectSum ℤ fun n : ℤ => HQ l E n 0

def pullTot {E E' : Spc} (f : E ⟶ E') : Htot l E' →ₗ[ℚ_[l]] Htot l E :=
  DirectSum.lmap fun n => pullHQ l f n 0

theorem pullTot_id (E : Spc) : pullTot l (𝟙 E) = LinearMap.id := by
  simp only [pullTot, pullHQ, pullHl_id, LinearMap.baseChange_id]
  exact DirectSum.lmap_id

theorem pullTot_comp {E E' E'' : Spc} (f : E ⟶ E') (g : E' ⟶ E'') :
    pullTot l (f ≫ g) = pullTot l f ∘ₗ pullTot l g := by
  simp only [pullTot, pullHQ, pullHl_comp, LinearMap.baseChange_comp]
  exact DirectSum.lmap_comp _ _

def galTot {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    (Ω ≃ₐ[k] Ω) → Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) →ₗ[ℚ_[l]] Htot l (sch.obj (GlobalTheory.Et.geom Ω p)) :=
  fun σ => pullTot l (sch.map (GlobalTheory.Et.galMap Ω p σ))

private theorem galMap_one' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : GlobalTheory.Et.galMap Ω p (1 : Ω ≃ₐ[k] Ω) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.id_comp]
  · rw [GlobalTheory.Et.galMap_snd, Category.id_comp]
    have h1 : CommRingCat.ofHom ((1 : Ω ≃ₐ[k] Ω) : Ω →+* Ω) = 𝟙 _ := by
      ext x; rfl
    rw [h1, Spec.map_id, Category.comp_id]

theorem galTot_one {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    galTot l Ω p 1 = LinearMap.id := by
  simp only [galTot]
  rw [galMap_one', CategoryTheory.Functor.map_id, pullTot_id]

private theorem galMap_mul' {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (σ τ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p (σ * τ) = GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.galMap Ω p τ := by
  apply pullback.hom_ext
  · rw [GlobalTheory.Et.galMap_fst, Category.assoc, GlobalTheory.Et.galMap_fst, GlobalTheory.Et.galMap_fst]
  · have h2 : CommRingCat.ofHom ((σ * τ : Ω ≃ₐ[k] Ω) : Ω →+* Ω) =
        CommRingCat.ofHom (τ : Ω →+* Ω) ≫ CommRingCat.ofHom (σ : Ω →+* Ω) := by
      ext x; rfl
    rw [GlobalTheory.Et.galMap_snd, Category.assoc, GlobalTheory.Et.galMap_snd, GlobalTheory.Et.galMap_snd_assoc, h2, Spec.map_comp]

theorem galTot_mul {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))
    (σ τ : Ω ≃ₐ[k] Ω) : galTot l Ω p (σ * τ) = galTot l Ω p σ ∘ₗ galTot l Ω p τ := by
  simp only [galTot]
  rw [galMap_mul', CategoryTheory.Functor.map_comp, pullTot_comp]

def galTotRep {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) :
    Representation ℚ_[l] (Ω ≃ₐ[k] Ω) (Htot l (sch.obj (GlobalTheory.Et.geom Ω p))) where
  toFun := galTot l Ω p
  map_one' := galTot_one l Ω p
  map_mul' := galTot_mul l Ω p

def Splits {Z Y W : Scheme.{0}} (s : Y ⟶ Z) (c : W ⟶ Z) {J : Type} (σ : J → (W ⟶ Y)) : Prop :=
  ∃ h : ∀ j, σ j ≫ s = c,
    IsIso (Limits.Sigma.desc (fun j => pullback.lift (σ j) (𝟙 W) (by rw [h j, Category.id_comp])) :
      ∐ (fun _ : J => W) ⟶ pullback s c)

def IsGalois {W X : Scheme.{0}} (c : W ⟶ X) (G : Type) [Group G] (a : G → (W ⟶ W)) : Prop :=
  IsFinite c ∧ Etale c ∧ Surjective c ∧ a 1 = 𝟙 W ∧ (∀ g h, a (g * h) = a g ≫ a h) ∧ Splits c c a

def IsCorrOp {Z Y Z' : Scheme.{0}} (s : Y ⟶ Z) (t : Y ⟶ Z') (T : Htot l (sch.obj Z') →ₗ[ℚ_[l]] Htot l (sch.obj Z)) : Prop :=
  ∃ (W : Scheme.{0}) (c : W ⟶ Z) (G : Type) (_ : Group G) (_ : Finite G) (a : G → (W ⟶ W)) (J : Type) (_ : Fintype J)
    (σ : J → (W ⟶ Y)), IsGalois c G a ∧ Splits s c σ ∧
    ∀ x, pullTot l (sch.map c) (T x) = ∑ j, pullTot l (sch.map (σ j ≫ t)) x

variable {l}

def genEig {H : Type*} [AddCommGroup H] [Module ℚ_[l] H] (L : Type*) [Field L] [Algebra ℚ_[l] L] {J : Type*}
    (T : J → H →ₗ[ℚ_[l]] H) (θ : J → L) : Submodule L (TensorProduct ℚ_[l] L (H)) :=
  ⨅ j, Module.End.maxGenEigenspace ((T j).baseChange L) (θ j)

variable (l)

theorem isGalois_id (X : Scheme.{0}) : IsGalois (𝟙 X) Unit (fun _ => 𝟙 X) := by
  refine ⟨inferInstance, inferInstance, inferInstance, rfl, fun _ _ => (Category.comp_id _).symm,
    fun _ => Category.comp_id _, ?_⟩
  have hd : IsIso (Sigma.desc (fun _ : Unit => 𝟙 X)) :=
    ⟨⟨Sigma.ι (fun _ : Unit => X) (), by ext j; cases j; simp, by simp⟩⟩
  refine (isIso_comp_right_iff _ (pullback.fst (𝟙 X) (𝟙 X))).mp ?_
  convert hd using 1
  ext j
  simp

theorem splits_fold (X : Scheme.{0}) (J : Type) :
    Splits (Sigma.desc fun _ : J => 𝟙 X) (𝟙 X) (Sigma.ι (fun _ : J => X)) := by
  refine ⟨fun _ => by simp, ?_⟩
  refine (isIso_comp_right_iff _ (pullback.fst (Sigma.desc fun _ : J => 𝟙 X) (𝟙 X))).mp ?_
  convert (inferInstance : IsIso (𝟙 (∐ fun _ : J => X))) using 1
  ext j
  simp

theorem isCorrOp_fold {X Z' : Scheme.{0}} {J : Type} [Fintype J] (f : J → (X ⟶ Z')) :
    IsCorrOp l (Sigma.desc fun _ : J => 𝟙 X) (Sigma.desc f) (∑ j, pullTot l (sch.map (f j))) := by
  refine ⟨X, 𝟙 X, Unit, inferInstance, inferInstance, fun _ => 𝟙 X, J, inferInstance, Sigma.ι (fun _ : J => X),
    isGalois_id X, splits_fold X J, fun x => ?_⟩
  rw [CategoryTheory.Functor.map_id, pullTot_id, LinearMap.id_apply, LinearMap.sum_apply]
  simp only [Sigma.ι_comp_desc]

end GlobalTheory.GalV

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsExpLieAlgebraComplexUnits
section
noncomputable section

open MeasureTheory GroundTheory.Automorphic

namespace GlobalTheory.HCA

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤) {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤)

structure SmFn [MeasurableSpace G] (μ : Measure G) (S : Submodule ℂ (G → ℂ)) (K : Set G)
    (Λ : List (Fin d) → (G → ℂ) → ℂ) : Prop where
  lin : ∀ l, ∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ l (c • f + f') = c * Λ l f + Λ l f'
  bdd : ∀ l, ∃ C : ℝ, ∀ f ∈ S, ‖Λ l f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ
  der : ∀ l i, ∀ f ∈ S, HasDerivAt (fun t : ℝ => Λ l fun y => f (h.expG (t • b i) * y)) (Λ (i :: l) f) 0

def solG (P : Polynomial ℂ) : Submodule ℂ (G → ℂ) :=
  (LinearMap.ker (Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P)).map
    (h.smoothFuns (F := ℂ)).subtype

theorem mem_solG {P : Polynomial ℂ} {f : G → ℂ} : f ∈ solG h b P ↔ ∃ hf : h.IsSmoothFun f,
    Polynomial.aeval (∑ i, h.rightDerivEnd (F := ℂ) (b i) * h.rightDerivEnd (F := ℂ) (b i)) P
      (⟨f, hf⟩ : h.smoothFuns (F := ℂ)) = 0 := by
  simp only [solG, Submodule.mem_map, LinearMap.mem_ker, Submodule.subtype_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hf, h0⟩
    exact ⟨⟨f, hf⟩, h0, rfl⟩

namespace SmFnEx

end SmFnEx

end GlobalTheory.HCA

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
section
noncomputable section

open MeasureTheory Matrix ValuativeRel Filter
open scoped NNReal Topology Kronecker

namespace GlobalTheory.WeilM

theorem eventually_comp_eq {P V : Type} [TopologicalSpace P] [TopologicalSpace V] {p₀ : P} (f g : P → V → V)
    (hf : Continuous fun q : P × V => f q.1 q.2) (hg : Continuous fun q : P × V => g q.1 q.2)
    (f0 : ∀ v, f p₀ v = v) (g0 : ∀ v, g p₀ v = v) (hgf : ∀ p v, g p (f p v) = v) {φ : V → ℂ} (hφ : φ ∈ SB V) :
    ∀ᶠ p in 𝓝 p₀, ∀ v, φ (f p v) = φ v := by
  have key : ∀ f : P → V → V, (Continuous fun q : P × V => f q.1 q.2) → (∀ v, f p₀ v = v) →
      ∀ᶠ p in 𝓝 p₀, ∀ v ∈ tsupport φ, φ (f p v) = φ v := fun f hf f0 => by
    refine IsCompact.eventually_forall_of_forall_eventually hφ.2 fun v _ => ?_
    filter_upwards [(hφ.1.comp_continuous hf).eventually_eq (p₀, v),
      (hφ.1.comp_continuous continuous_snd).eventually_eq (p₀, v)] with q h1 h2
    simp only [Function.comp, f0] at h1 h2
    rw [h1, h2]
  filter_upwards [key f hf f0, key g hg g0] with p h1 h2 v
  by_cases hv : v ∈ tsupport φ
  · exact h1 v hv
  · by_cases hw : f p v ∈ tsupport φ
    · rw [← h2 _ hw, hgf]
    · rw [image_eq_zero_of_notMem_tsupport hv, image_eq_zero_of_notMem_tsupport hw]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem eventually_char_eq_one (μ : Fˣ →* Circle) (hμ : Continuous μ) :
    ∀ᶠ t in 𝓝 (1 : Fˣ), μ t = 1 ∧ distribHaarChar F t = 1 := by
  have h0 : {t : Fˣ | ‖(μ t : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (1 : Fˣ) :=
    (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨U, hU, hUV⟩ := h0
  have h1 : (fun x : F => 1 + x) ⁻¹' U ∈ 𝓝 (0 : F) :=
    (Continuous.tendsto' (by fun_prop) _ _ (by simp) : Tendsto (fun x : F => 1 + x) (𝓝 0) (𝓝 ((1 : Fˣ) : F))) hU
  have h2 : {x : F | valuation F x < 1} ∈ 𝓝 (0 : F) := (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨1, fun _ h => h⟩
  obtain ⟨s, hs⟩ := SplitWeil.exists_cball_subset (inter_mem h1 h2)
  have h3 : Tendsto (fun t : Fˣ => (t : F) - 1) (𝓝 1) (𝓝 0) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  filter_upwards [h3.eventually (SplitWeil.cball_mem_nhds s)] with t ht
  have hv : valuation F (t : F) = 1 := by simpa using (valuation F).map_one_add_of_lt (hs ht).2
  have hn : ∀ n : ℕ, (t : F) ^ n - 1 ∈ SplitWeil.cball s := fun n => by
    induction n with
    | zero => simp [SplitWeil.cball]
    | succ n ih =>
      rw [show (t : F) ^ (n + 1) - 1 = t * (t ^ n - 1) + (t - 1) by ring]
      refine SplitWeil.add_mem_cball ?_ ht
      show valuation F ((t : F) * ((t : F) ^ n - 1)) ≤ valuation F (s : F)
      rw [map_mul, hv, one_mul]
      exact ih
  refine ⟨Circle.coe_eq_one.mp (eq_one_of_forall_pow_near fun n => ?_),
    NNReal.coe_injective (SplitWeil.nabs_eq_one_of_valuation_eq_one hv)⟩
  have : t ^ n ∈ Units.val ⁻¹' U := by simpa using (hs (hn n)).1
  simpa using hUV this

variable {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]


variable [Invertible (2 : F)] {JA : Matrix α α (F × F)} {JB : Matrix β β (F × F)}

end GlobalTheory.WeilM

end
end

