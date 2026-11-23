module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PBaseCase
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def selfPl {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : PlacesOver K v :=
  ⟨v, ⟨Ideal.ext fun _ => Iff.rfl⟩⟩

private theorem cm_id {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (x : v.adicCompletion K) : completionMap v (selfPl v).1 x = x := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap K v).equalizer
    (continuous_completionMap v (selfPl v).1) continuous_id (funext fun y => ?_)) x
  simp only [Function.comp_apply, id]
  rw [completionMap_algebraMap]
  rfl

private theorem map_refl {R : Type} [CommRing R] {n : ℕ} (g : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map (RingEquiv.refl R).toRingHom g = g := by
  ext i j
  simp

theorem UpperTheory.Gal.InertialTypesAlt.baseCase :
    ResEmbCompat → LblIso → BaseCase := by
  intro hC hI K Ω _ _ _ _ _ n π A Θ v e e' he he' τ τ' hτ hτ' a ha
  have H : ∃ (r : 𝓀[v.adicCompletion K] →+* 𝓀[v.adicCompletion K])
      (j : AlgebraicClosure 𝓀[v.adicCompletion K] ≃+* AlgebraicClosure 𝓀[v.adicCompletion K]),
      (∀ (x y : 𝒪[v.adicCompletion K]), (y : v.adicCompletion K) = x →
        IsLocalRing.residue _ y = r (IsLocalRing.residue _ x)) ∧
      (∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) ∧ ∀ x, e' (j x) = e x := by
    obtain ⟨r, j, h1, h2, h3⟩ := hC K K Ω A v (selfPl v) e e' he he'
    exact ⟨r, j, fun x y h => h1 x y (h.trans (cm_id v _).symm), h2, h3⟩
  obtain ⟨r, j, h1, h2, h3⟩ := H
  obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v τ τ' hτ hτ'
  have hθ : (Θ.comp e'.toMonoidHom).comp j.toMonoidHom = Θ.comp e.toMonoidHom := by
    ext x
    simp [h3]
  refine hI (v.adicCompletion K) (v.adicCompletion K) (RingEquiv.refl _) (fun _ => Iff.rfl) j ?_
    (Θ.comp e'.toMonoidHom) n τ.V τ'.V τ.ρ τ'.ρ E.toLinearEquiv ?_ a (by rw [hθ]; exact ha)
  · intro x y hxy
    rw [h2, h1 x y hxy]
  · intro g x
    rw [map_refl]
    exact LinearMap.congr_fun (E.isIntertwining' g) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblOn
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Pointwise in
private theorem ine_restrict {K M Ω : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] (A : ValuationSubring Ω) (t : G M Ω) (ht : t ∈ Ine (F := M) A) :
    (AlgEquiv.restrictScalars K t : G K Ω) ∈ Ine (F := K) A := by
  obtain ⟨h1, h2⟩ := ht
  refine ⟨?_, fun x hx => h2 x hx⟩
  have h1' : t • A = A := h1
  show (AlgEquiv.restrictScalars K t : G K Ω) • A = A
  have : (AlgEquiv.restrictScalars K t : G K Ω) • A = t • A := by
    ext x
    simp only [ValuationSubring.mem_smul_pointwise_iff_exists]
    rfl
  rw [this, h1']

private theorem place_unique {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (A : ValuationSubring Ω)
    (v w : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v) (h' : IsPlaceOver A w) : v = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, ← h' x]

private theorem le_closed (P₀ : Lbl → Prop) (hl : ∀ a l, P₀ a → P₀ (a.lift l)) {a b : Lbl} (h : a.Le b) (ha : P₀ a) : P₀ b := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih =>
    obtain ⟨l, _, rfl⟩ := hbc
    exact hl _ _ ih

theorem UpperTheory.Gal.InertialTypesAlt.lblOn :
    BaseCase → LiftsFix → PlaceEx → ResEmbEx → UnrOfIne → ∀ P₀ : Lbl → Prop, (∀ a l, P₀ a → P₀ (a.lift l)) → StepAt P₀ id → StepAt P₀ Not → LblOn P₀ := by
  intro hB hF hP hR hU P₀ hl hS hN E Ω _ _ _ n hn X Y hXY A Θ hΘ
  induction hXY using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro _ v w hv hw e e' he he' τ τ' hτ hτ' a _ hL
    obtain rfl := place_unique A v w hv hw
    exact ⟨a, Relation.ReflTransGen.refl, hB Y.K Ω n Y.π A Θ v e e' he he' τ τ' hτ hτ' a hL⟩
  | @head X Z hXZ hZY ih =>
    intro hI v w hv hw e e' he he' τ τ' hτ hτ' a ha hL
    obtain ⟨i1, i2, hGal, hpr, hW⟩ := hXZ
    obtain ⟨u, hu, τ₁, hτ₁⟩ := hP X.K Z.K Ω A v hv n Z.π
    obtain ⟨⟨e₁, he₁⟩, _⟩ := hR Z.K Ω A u hu
    have hIZ : ∀ t ∈ Ine (F := X.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Z.K t := by
      intro t ht x
      obtain ⟨y, hy⟩ := hF E Ω n Z Y hZY x
      rw [← hy]
      exact hI t ht y
    obtain ⟨hund, hUnr, _⟩ := hU X.K Z.K Ω A v u hv hu hIZ
    let u' : PlacesOver Z.K v := ⟨u, ⟨by rw [← hund]; rfl⟩⟩
    have hb : ∃ b₁, a.Le b₁ ∧ HasLbl (Θ.comp e₁.toMonoidHom) τ₁.ρ b₁ := by
      by_cases hs : UpperTheory.ConvolutionTheory.GM.Split Z.K v
      · exact hS X.K Z.K Ω hpr n hn X.π Z.π hW A Θ hΘ v u' hs hUnr e e₁ he he₁ τ τ₁ hτ hτ₁ a ha hL
      · exact hN X.K Z.K Ω hpr n hn X.π Z.π hW A Θ hΘ v u' hs hUnr e e₁ he he₁ τ τ₁ hτ hτ₁ a ha hL
    obtain ⟨b₁, hab, hb₁⟩ := hb
    have hIZ' : ∀ t ∈ Ine (F := Z.K) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t := by
      intro t ht y
      exact hI _ (ine_restrict (K := X.K) A t ht) y
    obtain ⟨b, hbb, hbL⟩ := ih hIZ' u w hu hw e₁ e' he₁ he' τ₁ τ' hτ₁ hτ' b₁ (le_closed P₀ hl hab ha) hb₁
    exact ⟨b, hab.trans hbb, hbL⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt

def expand (D : List (ℕ × ℕ)) : List (ℕ × ℕ) := D.flatMap fun p => List.replicate p.1 (1, p.2)

def Pairs {G : Type} (Y T : G → ℂ) : Prop := ∑ᶠ g, star (Y g) * T g ≠ 0

def Lbl.Apart (a : Lbl) : Prop :=
  (∀ p ∈ a.D, p.2 < a.q - 1) ∧ (a.D.map Prod.snd).Nodup ∧ (∀ p ∈ a.L, 2 ≤ p.1) ∧
    a.L.Pairwise fun p r => p.1 = r.1 → ∀ i : ℕ, ¬ r.2 ≡ p.2 * a.q ^ i [MOD a.q ^ p.1 - 1]

def MixType : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v →
      IsPlaceOver A w → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
      ∃ (c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = n) (θ : Fin c → 𝓀[w.adicCompletion Y.K]ˣ →* ℂˣ), (∀ b, 0 < d b) ∧
        Function.Injective θ ∧ UpperTheory.Gal.TypesAndIwahori.HasTypeVec τ'.ρ (stdBlocks d hd) θ

def MixUnlinked : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (n : ℕ), 0 < n →
    ∀ (π : CuspSub E n) (Y : Pt E Ω n), Lifts (Pt.base Ω π) Y →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 Y.K)), IsPlaceOver A v →
      IsPlaceOver A w → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    (∀ t ∈ Ine (F := E) A, UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes Y.K t) →
    ∀ τ τ', π.IsLocComp v τ → Y.π.IsLocComp w τ' → Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
    ∀ f : ℕ, normV w = g ^ f → (∀ s, HasSupport τ.ρ s → ∀ y ∈ s, y.1 ∣ f) →
      ∀ s, HasSupport τ'.ρ s → GlobalTheory.RoadU.Unlinked s

theorem suppBC_of_mix (h₁ : SuppAny) (h₂ : MixUnlinked) : SuppBC := by
  intro E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hD f hf hs
  obtain ⟨ξ, hξ, H⟩ := h₁ E Ω n hn π Y hY A v w h h' g i hi hI τ τ' hτ hτ' hD f hf hs
  exact ⟨ξ, hξ, H, fun hM => h₂ E Ω n hn π Y hY A v w h h' g i hi hI τ τ' hτ hτ' hM f hf hs _ H.2.1⟩

def JAppend : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (L L' : List (ℕ × ℕ)) (n : ℕ), n = deg L + deg L' →
    J θ (L ++ L') n = hc (deg L) (deg L') (J θ L (deg L)) (J θ L' (deg L')) n

def SepOf : Prop := ∀ (a : Lbl) (Q : ℕ), a.Ok → a.Apart → a.Splits Q → a.Sep Q

def Group1 : Prop :=
  ∀ L₀ : List (ℕ × ℕ), (∀ p ∈ L₀, 0 < p.1) → ∃ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1 ∧ (1, p.2) ∈ L₀) ∧ (D.map Prod.snd).Nodup ∧
    (expand D ++ L₀.filter fun p => 2 ≤ p.1).Perm L₀

def HcPair : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∀ (α A : GL (Fin a) F → ℂ) (β B : GL (Fin b) F → ℂ),
    GlobalTheory.BI.IsChar ℂ ℂ α → GlobalTheory.BI.IsChar ℂ ℂ A → GlobalTheory.BI.IsChar ℂ ℂ β → GlobalTheory.BI.IsChar ℂ ℂ B → Pairs A α → Pairs B β →
    Pairs (hc a b A B n) (hc a b α β n)

def HcOne : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (a b n : ℕ), n = a + b → ∀ (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ),
    α 1 ≠ 0 → β 1 ≠ 0 → hc a b α β n 1 ≠ 0

def DetPair : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (t c : ℕ),
    Pairs (J θ (List.replicate t (1, c)) t) (detc θ t c)

def JDPair : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), Inj θ → ∀ a : Lbl, a.Ok → a.q = Nat.card F →
    deg (expand a.D ++ a.L) = a.rk ∧ Pairs (J θ (expand a.D ++ a.L) a.rk) (JD θ a.D a.L a.rk)

def CuspFrob : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), Inj θ → ∀ m c c' i : ℕ, 0 < m →
    c' ≡ c * Nat.card F ^ i [MOD Nat.card F ^ m - 1] → cusp θ m c' = cusp θ m c

def AvgMap : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H : Subgroup G) (U Z W X : Type) [AddCommGroup U] [Module ℂ U] [AddCommGroup Z] [Module ℂ Z]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G U) (κ : Representation ℂ H Z)
    (η : Representation ℂ G X) (Φ : Z →ₗ[ℂ] U) (ev : U →ₗ[ℂ] W) (ψ : X →ₗ[ℂ] Z),
    (∀ (h : H) z, Φ (κ h z) = ρ h (Φ z)) → (∀ g ∉ H, ∀ z, ev (ρ g (Φ z)) = 0) → (∀ z, ev (Φ z) = 0 → z = 0) →
    (∀ (h : H) x, ψ (η h x) = κ h (ψ x)) → ψ ≠ 0 → ∃ Ψ : X →ₗ[ℂ] U, Ψ ≠ 0 ∧ ∀ g x, Ψ (η g x) = ρ g (Ψ x)

def IndMap : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = N) (W Z : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (κ : Representation ℂ (Levi 𝓀[k] fun a => Fin (d a)) Z) (j : Z →ₗ[ℂ] W),
    Function.Injective j →
    (∀ (x : leviK k fun a => Fin (d a)) (z : Z), j (κ (redLevi k _ x) z) = ρ (x : Levi k fun a => Fin (d a)) (j z)) →
    ∃ (Φ : Z →ₗ[ℂ] fixed (parInd (stdBlocks d hd) ρ) (KOne k (Fin N)))
      (ev : fixed (parInd (stdBlocks d hd) ρ) (KOne k (Fin N)) →ₗ[ℂ] W),
      (∀ (p : parab 𝓀[k] (stdBlocks d hd)) z,
        Φ (κ (leviProj 𝓀[k] (stdBlocks d hd) p) z) = levelZero (parInd (stdBlocks d hd) ρ) p (Φ z)) ∧
      (∀ γ ∉ parab 𝓀[k] (stdBlocks d hd), ∀ z, ev (levelZero (parInd (stdBlocks d hd) ρ) γ (Φ z)) = 0) ∧
      ∀ z, ev (Φ z) = 0 → z = 0

def TensInc : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s : ℕ) (d : Fin s → ℕ) (V : Fin s → Type) [∀ a, AddCommGroup (V a)] [∀ a, Module ℂ (V a)]
    (σ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (V a)),
    ∃ j : (PiTensorProduct ℂ fun a => fixed (σ a) (KOne k (Fin (d a)))) →ₗ[ℂ] PiTensorProduct ℂ V, Function.Injective j ∧
      ∀ (x : leviK k fun a => Fin (d a)) z, j (piTensor (fun a => levelZero (σ a)) (redLevi k _ x) z) =
        piTensor σ (x : Levi k fun a => Fin (d a)) (j z)

def UnlFull : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (s : ℕ) (x : Fin s → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N), HasSupport π (Finset.univ.val.map x) →
    GlobalTheory.RoadU.Unlinked (Finset.univ.val.map x) → Nonempty (π.Equiv (prodIrr x hd))

def LblFull : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (θ : AlgebraicClosure 𝓀[k] →* ℂ) (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible →
    ∀ (s : ℕ) (x : Fin s → IrrGL (k := k)) (c : Fin s → ℕ) (hd : ∑ a, (x a).1 = N), Nonempty (π.Equiv (prodIrr x hd)) →
    (∀ a γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).1 (c a) γ) →
    ∀ T : GL (Fin N) 𝓀[k] → ℂ, GlobalTheory.BI.IsChar ℂ ℂ T → Pairs (J θ (List.ofFn fun a => ((x a).1, c a)) N) T → Meets (levelZero π) T

def InertOf : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver A v → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    ∀ (m : ℕ) (x y : IrrCl (GL (Fin m) (v.adicCompletion E))), IrrGL.IsCusp ⟨m, x⟩ → IrrGL.IsCusp ⟨m, y⟩ →
      UpperTheory.Zero.LLC.DZ ⟨m, x⟩ → UpperTheory.Zero.LLC.DZ ⟨m, y⟩ →
      (∀ γ, LinearMap.trace ℂ _ (levelZero x.rep.ρ γ) = LinearMap.trace ℂ _ (levelZero y.rep.ρ γ)) →
      IrrGL.Inert ⟨m, x⟩ ⟨m, y⟩

def LblMixed : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver A v → ∀ (g : ℕ) [Fact g.Prime] (i : ℚ_[g] ≃+* v.adicCompletion E), Continuous i →
    ∀ (θ : AlgebraicClosure 𝓀[v.adicCompletion E] →* ℂ), Inj θ → ∀ (n : ℕ) (τ : SmIrr (GL (Fin n) (v.adicCompletion E))),
      Mixed (IrrGL.of τ.ρ τ.smooth τ.irred) →
      ∃ (a : Lbl) (s : Multiset (IrrGL (k := v.adicCompletion E))), HasLbl θ τ.ρ a ∧ a.Apart ∧ HasSupport τ.ρ s ∧
        ∀ p ∈ a.L, ∃ y ∈ s, y.1 = p.1

end UpperTheory.Gal.InertialTypesAlt
end
end

