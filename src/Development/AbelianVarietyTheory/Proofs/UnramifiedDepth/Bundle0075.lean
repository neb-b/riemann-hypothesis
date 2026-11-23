module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0074
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPHomomorphismCubicalWeilTrivialRationalTors
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

def unitsOfΓ {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A] [Algebra Ω A] :
    Γ((overAt s A).left, ⊤)ˣ →* Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom

theorem unitsOfΓ_injective {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A]
    [Algebra Ω A] : Function.Injective (unitsOfΓ s A) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem unitsOfΓ_natural {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (ζ : Γ((overAt s A).left, ⊤)ˣ) :
    unitsOfΓ s B (Units.map (homAt s f).left.appTop.hom.toMonoidHom ζ) = Units.map (f : A →* B) (unitsOfΓ s A ζ) := by
  have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
  exact Units.ext (congrArg (fun φ => φ.hom ζ.val) h₁)

theorem cubWeil_alpha_rational : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (g : Fam s G), IsAlpha p s G g → ∀ x : overAt s Ω ⟶ G, x ^ p = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) 1 := by
  intro Ω _ p _ _ S s G _ _ L c g hg x hx
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hex : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ ζ : Γ((overAt s A).left, ⊤)ˣ,
      a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) ζ := by
    intro A _ _ a
    by_cases ha : a ^ p = 0
    · obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c (hg.pow_eq_one hp ha)
        (y := homAt s (Algebra.ofId Ω A) ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      exact ⟨ζ, fun _ => hζ⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose ζ hζ using hex
  intro A _ _ a ha
  have key := _root_.GlobalTheory.AlphaChar.char_eq_one Ω p (fun A _ _ a => unitsOfΓ s A (ζ A a)) ?_ ?_ A a ha
  · have : ζ A a = 1 := unitsOfΓ_injective s A (key.trans (map_one _).symm)
    exact this ▸ hζ A a ha
  · intro A B _ _ _ _ f a ha
    beta_reduce
    have hb : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
    have h₁ := (hζ A a ha).comp (homAt s f)
    rw [← hg.1 A B f a ha, ← Category.assoc, hom_comp, Subsingleton.elim (f.comp (Algebra.ofId Ω A)) (Algebra.ofId Ω B)] at h₁
    rw [(hζ B (f a) hb).unique h₁, unitsOfΓ_natural]
  · intro A _ _ a a' ha ha'
    beta_reduce
    have hs : (a + a') ^ p = 0 := by
      rcases subsingleton_or_nontrivial A with _ | _
      · exact Subsingleton.elim _ _
      · haveI : CharP A p := charP_of_injective_algebraMap (algebraMap Ω A).injective p
        rw [add_pow_char, ha, ha', add_zero]
    have h₁ := (hζ A a ha).mul_left (hζ A a' ha')
    rw [← hg.2 A a a' ha ha'] at h₁
    rw [(hζ A (a + a') hs).unique h₁, map_mul]

end GlobalTheory.AlphaPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EqOneOfTangentVectorEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_tangent_vector_eq_one : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] (g : Fam s G), IsAlpha p s G g → g (DualNumber Ω) DualNumber.eps = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → g A a = 1 := by
  first | exact @GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | exact GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent | (intros; apply GlobalTheory.AlphaPair.IsAlpha.eq_one_of_tangent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EvalPowerSeriesEqOneOfTwoAxesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evalPowerSeries_eq_one_of_two_axes : ∀ (R : Type) [CommRing R] (d : ℕ) (ph : PS R 3 d), ev (n := 2) ![0, pt R d 0, pt R d 1] ph = 1 → ev (n := 2) ![pt R d 0, 0, pt R d 1] ph = 1 → ∀ (A : Type) [CommRing A] [Algebra R A] (e : A), e ^ 2 = 0 → ∀ a a' b : Fin d → A, (∀ j, a j ∈ Ideal.span {e}) → (∀ j, a' j ∈ Ideal.span {e}) → (∀ j, IsNilpotent (b j)) → evP ![a, a', b] ph = 1 := by
  first | exact @GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | exact GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes | (intros; apply GlobalTheory.AlphaPair.evalPoints_eq_one_of_two_axes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalChartPointNilpotentCoordinates
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair.JetPt

section Rho

variable {V Ω : Type} [CommRing V] [CommRing Ω] (β : V →+* Ω)

def Compat {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) : Prop :=
  ∀ v : V, ψ (algebraMap V B v) = algebraMap Ω A (β v)

variable {β}

theorem Compat.left {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) : Compat β (ψ.comp (f : B' →+* B)) := fun v => by
  rw [RingHom.comp_apply, RingHom.coe_coe, f.commutes, h v]

theorem Compat.right {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') : Compat β ((g : A →+* A').comp ψ) := fun v => by
  rw [RingHom.comp_apply, h v, RingHom.coe_coe, g.commutes]

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

def rho {B A : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] (ψ : B →+* A) (h : Compat β ψ) :
    overAt (spMap β) A ⟶ overAt (𝟙 (Sp V)) B :=
  Over.homMk (spMap ψ) (by
    change spMap ψ ≫ spMap (algebraMap V B) ≫ 𝟙 _ = spMap (algebraMap Ω A) ≫ spMap β
    rw [Category.comp_id, sp_comp, sp_comp]
    congr 1
    exact RingHom.ext h)

theorem rho_homAt {B B' A : Type} [CommRing B] [Algebra V B] [CommRing B'] [Algebra V B'] [CommRing A] [Algebra Ω A]
    {ψ : B →+* A} (h : Compat β ψ) (f : B' →ₐ[V] B) :
    rho ψ h ≫ homAt (𝟙 (Sp V)) f = rho (ψ.comp (f : B' →+* B)) (h.left f) :=
  Over.OverMorphism.ext (sp_comp _ _)

theorem homAt_rho {B A A' : Type} [CommRing B] [Algebra V B] [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A']
    {ψ : B →+* A} (h : Compat β ψ) (g : A →ₐ[Ω] A') :
    homAt (spMap β) g ≫ rho ψ h = rho ((g : A →+* A').comp ψ) (h.right g) :=
  Over.OverMorphism.ext (sp_comp _ _)

def co {d m : ℕ} {A : Type} [CommRing A] (ψ : Jet V (Fin 1 × Fin d) m →+* A) : Fin d → A :=
  fun j => ψ (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j)))

theorem eq_of_co {d m : ℕ} {A : Type} [CommRing A] [Algebra Ω A] {ψ ψ' : Jet V (Fin 1 × Fin d) m →+* A}
    (h : Compat β ψ) (h' : Compat β ψ') (e : co ψ = co ψ') : ψ = ψ' := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun v => (h v).trans (h' v).symm) ?_)
  rintro ⟨i, j⟩
  obtain rfl : i = 0 := Subsingleton.elim _ _
  exact congrFun e j

theorem jetMap_X {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ') (i : κ) :
    (jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      Ideal.Quotient.mk _ (φ i) := by
  change Ideal.Quotient.mk _ (MvPolynomial.aeval φ (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  change MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i) = _
  rw [MvPolynomial.aeval_X]

theorem exists_jet {κ : Type} [Fintype κ] [DecidableEq κ] {A : Type} [CommRing A] [Algebra Ω A] (a : κ → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V κ m →+* A), Compat β ψ ∧ ∀ i, ψ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = a i := by
  have hn : IsNilpotent (Ideal.span (Set.range a)) := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range a))).2 (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact ha i
  obtain ⟨m, hm⟩ := hn
  obtain ⟨ψ, hψ, -⟩ := (GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β κ m).1 a (by rw [pow_succ, hm, zero_mul]; rfl)
  exact ⟨m, ψ, hψ⟩

theorem exists_jet_one {d : ℕ} {A : Type} [CommRing A] [Algebra Ω A] (a : Fin d → A)
    (ha : ∀ i, IsNilpotent (a i)) :
    ∃ (m : ℕ) (ψ : Jet V (Fin 1 × Fin d) m →+* A), Compat β ψ ∧ co ψ = a := by
  obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 1 × Fin d => a q.2) fun q => ha q.2
  exact ⟨m, ψ, h, funext fun j => e (0, j)⟩

variable {G : Over (Sp V)} {d : ℕ} {x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G}

theorem lift_add (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} (ψ : Jet V (Fin 1 × Fin d) m →+* A) (h : Compat β ψ)
    {n : ℕ} (hn : m ≤ n) :
    ∃ (χ : Jet V (Fin 1 × Fin d) n →+* A) (hχ : Compat β χ), co χ = co ψ ∧ rho χ hχ ≫ x n = rho ψ h ≫ x m := by
  induction n, hn using Nat.le_induction with
  | base => exact ⟨ψ, h, rfl, rfl⟩
  | succ n _ ih =>
    obtain ⟨χ, hχ, e, e'⟩ := ih
    refine ⟨_, hχ.left jetTrunc, e, ?_⟩
    rw [← rho_homAt hχ, Category.assoc, hx, e']

theorem indep (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m n : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {ψ' : Jet V (Fin 1 × Fin d) n →+* A} (h' : Compat β ψ') (e : co ψ = co ψ') :
    rho ψ h ≫ x m = rho ψ' h' ≫ x n := by
  obtain ⟨χ, hχ, e₁, e₂⟩ := lift_add hx ψ h (le_max_left m n)
  obtain ⟨χ', hχ', e₁', e₂'⟩ := lift_add hx ψ' h' (le_max_right m n)
  obtain rfl : χ = χ' := eq_of_co hχ hχ' (by rw [e₁, e₁', e])
  rw [← e₂, ← e₂']

end Rho

section Main

variable {V Ω : Type} [CommRing V] [Field Ω] (β : V →+* Ω) {G : Over (Sp V)} [GrpObj G] {d : ℕ}
  (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G)


open Classical in
def ptOf : PtFam (spMap β) G d := fun A _ _ a =>
  if h : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a then
    rho h.choose.2 h.choose_spec.1 ≫ x h.choose.1
  else 1

variable {β x}

theorem ptOf_co (hx : ∀ m, homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ x (m + 1) = x m)
    {A : Type} [CommRing A] [Algebra Ω A] {m : ℕ} {ψ : Jet V (Fin 1 × Fin d) m →+* A} (h : Compat β ψ)
    {a : Fin d → A} (e : co ψ = a) : ptOf β x A a = rho ψ h ≫ x m := by
  have hh : ∃ p : (m : ℕ) × (Jet V (Fin 1 × Fin d) m →+* A), Compat β p.2 ∧ co p.2 = a := ⟨⟨m, ψ⟩, h, e⟩
  rw [ptOf, dite_eq_left hh]
  exact indep hx _ h (hh.choose_spec.2.trans e.symm)

end Main

end GlobalTheory.AlphaPair.JetPt


open GlobalTheory.AlphaPair.JetPt in
theorem GlobalTheory.AlphaPair.exists_jetPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t : SAB H (Sp V)) (d : ℕ) (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (uv : Fin d → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G), IsChartG t (𝟙 (Sp V)) d F act tg uv x → (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ∀ (Ω : Type) [Field Ω] (β : V →+* Ω), ∃ P : PtFam (spMap β) t.G d, IsJetPt β x P ∧ IsPtLaw (spMap β) t.G (fun j => MvPowerSeries.map β (F j)) P := by
  intro E _ _ _ H V _ t d F act tg uv x hc hF Ω _ β
  refine ⟨ptOf β x, fun A _ _ m ψ h => ?_, fun A B _ _ _ _ f a ha => ?_, fun A _ _ => ?_, fun A _ _ a b ha hb => ?_⟩
  · exact congrArg CommaMorphism.left (ptOf_co hc.trunc (ψ := ψ) h rfl)
  · obtain ⟨m, ψ, h, rfl⟩ := exists_jet_one (β := β) a ha
    rw [ptOf_co hc.trunc h rfl, ptOf_co hc.trunc (h.right f) (a := fun j => f (co ψ j)) rfl, ← Category.assoc, homAt_rho]
  · have h : Compat β ((algebraMap Ω A).comp β) := fun v => rfl
    rw [ptOf_co hc.trunc (h.left (jetAug : Jet V (Fin 1 × Fin d) 0 →ₐ[V] V))
      (funext fun j => by simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetAug_X, map_zero, Pi.zero_apply]),
      ← rho_homAt h, Category.assoc, hc.zero, MonObj.comp_one]
  · obtain ⟨m, ψ, h, e⟩ := exists_jet (β := β) (fun q : Fin 2 × Fin d => ![a, b] q.1 q.2) (by
      rintro ⟨i, j⟩
      fin_cases i
      exacts [ha j, hb j])
    have hi : ∀ i : Fin 2, ptOf β x A (![a, b] i) = rho ψ h ≫ jptG t (𝟙 (Sp V)) d x m i := fun i => by
      rw [jptG, ← Category.assoc, rho_homAt]
      refine ptOf_co hc.trunc _ (funext fun j => ?_)
      simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetCopy, jetMap_X, e]
    have h0 : ptOf β x A a = _ := hi 0
    have h1 : ptOf β x A b = _ := hi 1
    rw [h0, h1, ← MonObj.comp_mul, ← hc.law m, ← Category.assoc, rho_homAt]
    refine ptOf_co hc.trunc _ (funext fun j => ?_)
    have h3 := ((GlobalTheory.AlphaPair.JetEv.jet_hom_spec V Ω A β (Fin 2 × Fin d) m).2 ψ h).2.2 (F j)
    simp only [e] at h3
    simp only [co, RingHom.comp_apply, RingHom.coe_coe, jetSubstP, jetMap_X]
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.cc_psTrunc, hF, map_zero, sub_zero]
    exact h3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsGeneratorOfRosatiAdjointLambdaBundle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RosGen

private theorem lbIso_of_local {O : Type} [CommRing O] [IsLocalRing O] {A : Over (Geo.Tor.Sp O)} [GrpObj A]
    [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB) (f g : A ⟶ A) (h : Out.RosatiAdj A L f g) :
    Geo.Tor.LBIso (cubeLB A ![fst A A ≫ f, snd A A] L) (cubeLB A ![fst A A, snd A A ≫ g] L) := by
  obtain ⟨U, hs, t, ht⟩ := h (IsLocalRing.closedPoint O)
  have hU : U = ⊤ := (IsLocalRing.closedPoint_mem_iff U).1 hs
  obtain ⟨n, hn⟩ : ∃ n : (A ⊗ A).left ⟶ ((A ⊗ A).hom ⁻¹ᵁ U).toScheme,
      n ≫ ((A ⊗ A).hom ⁻¹ᵁ U).ι = 𝟙 _ :=
    ⟨IsOpenImmersion.lift ((A ⊗ A).hom ⁻¹ᵁ U).ι (𝟙 _) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι, hU]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨u, hu, -⟩ := Geo.Tor.exists_gen hL (φ' := Out.rosatiφ A f g) (ε' := Out.rosatiε)
    (fun V _ k => Finset.prod_congr rfl fun i _ => by
      show k (n ≫ _ ≫ _) ^ _ = k _ ^ _
      rw [← Category.assoc, hn, Category.id_comp])
    (LB.pullGen L _ _ t n) (DVR.pullGen_isGen _ _ _ _ ht n)
  exact GlobalTheory.RosLam.lbIso_of_gen hL f g u hu

private theorem prod_two {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G)
    {U : Type 1} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum G ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left := by
  have key := GlobalTheory.NormRos.prod_square x y (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
    (fun ψ => Multiplicative.ofAdd (FreeAbelianGroup.of ψ))
  have k := congrArg (AddMonoidHom.toMultiplicativeLeft
    (FreeAbelianGroup.lift fun ψ : T.left ⟶ G.left => Additive.ofMul (h ψ))) key
  simpa only [map_mul, map_inv, map_prod, map_zpow, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply,
    toAdd_ofAdd, FreeAbelianGroup.lift_apply_of, toMul_ofMul] using k

theorem exists_gen_of_rosatiAdj : ∀ (O : Type) [CommRing O] [IsLocalRing O] (P : Out.PolAV (Geo.Tor.Sp O)) (Z : Scheme.{0}) (Q : LB Z) (ψ₂ : (P.A ⊗ P.A).left ⟶ Z), Q.IsLB → Geo.Tor.LBIso (abelian₂ P.A P.L) (Q.pull ψ₂) → ∀ f f' : P.A ⟶ P.A, IsMonHom f → IsMonHom f' → Out.RosatiAdj P.A P.L f f' → ∃ t : LB.Gen (LB.LinComb Q (K := Fin 2) ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]), t.IsGen := by
  intro O _ _ P Z Q ψ₂ hQ hI f f' _ _ h
  have := P.isAb.comm
  have H := lbIso_of_local P.isLB f f' h
  obtain ⟨Pic, _, cl, pl, h₁, h₂, -, h₄, h₅, -⟩ := GlobalTheory.CechPicMul.exists_picardGroup
  obtain ⟨a, a'⟩ : (abelian₂ P.A P.L).IsLB ∧ cl (abelian₂ P.A P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
  obtain ⟨q, q'⟩ : (Q.pull ψ₂).IsLB ∧ cl (Q.pull ψ₂) = _ := h₅ _ _ Q hQ _ _ _
  have e₀ : pl ψ₂ (cl Q) = cl (abelian₂ P.A P.L) := by
    rw [(h₁ _ _ _ a q).2 hI, q']; simp
  have key : ∀ x y : P.A ⊗ P.A ⟶ P.A, (cubeLB P.A ![x, y] P.L).IsLB ∧
      pl ((lift x y).left ≫ ψ₂) (cl Q) = cl (cubeLB P.A ![x, y] P.L) := fun x y => by
    obtain ⟨b, b'⟩ : (cubeLB P.A ![x, y] P.L).IsLB ∧ cl (cubeLB P.A ![x, y] P.L) = _ := h₅ _ _ P.L P.isLB _ _ _
    refine ⟨b, ?_⟩
    rw [h₄, e₀, a', b']
    have p₁ := prod_two x y (fun φ => pl φ (cl P.L))
    have p₂ := prod_two (fst P.A P.A) (snd P.A P.A) (fun φ => pl φ (cl P.L))
    refine Eq.trans (congrArg (pl (lift x y).left) p₂) (Eq.trans ?_ p₁.symm)
    simp only [map_mul, map_inv, ← h₄, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd]
  obtain ⟨c, c'⟩ := h₅ _ _ Q hQ (Fin 2)
    ![(lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂, (lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂] ![1, -1]
  refine (h₂ _ _ c).1 ?_
  rw [c', Fin.prod_univ_two]
  show pl ((lift (fst P.A P.A ≫ f) (snd P.A P.A)).left ≫ ψ₂) (cl Q) ^ (1 : ℤ) *
    pl ((lift (fst P.A P.A) (snd P.A P.A ≫ f')).left ≫ ψ₂) (cl Q) ^ (-1 : ℤ) = 1
  rw [(key _ _).2, (key _ _).2, (h₁ _ _ _ (key _ _).1 (key _ _).1).2 H]
  simp

end GlobalTheory.RosGen
end

