module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchCut
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.GeoTransport

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobFactsAlt
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DZA UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

structure IsRes {k K : Type} [Field k] [ValuativeRel k] [Field K] [ValuativeRel K] [Algebra k K] {F₀ F₁ : Type} [Field F₀]
    [Fintype F₀] [Field F₁] [Algebra F₀ F₁] (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁) : Prop where
  deg : Module.finrank F₀ F₁ = Module.finrank k K
  onto₀ : Function.Surjective rk
  onto₁ : Function.Surjective rK
  inc : ∀ (x : 𝒪[k]) (y : 𝒪[K]), (y : K) = algebraMap k K x → rK y = algebraMap F₀ F₁ (rk x)
  gal : ∀ x y : 𝒪[K], (y : K) = s x → rK y = sb (rK x)
  frob : ∀ z : F₁, sb z = z ^ Fintype.card F₀

def ResEx : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k K →
    ∃ (F₀ F₁ : Type) (_ : Field F₀) (_ : Fintype F₀) (_ : Field F₁) (_ : Fintype F₁) (_ : Algebra F₀ F₁)
      (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb

def InflFacts : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (F₀ : Type) [Field F₀] [Fintype F₀]
    (rd : 𝒪[k] →+* F₀), Function.Surjective rd → ∀ n : ℕ,
    KO k n = PositivityTheory.Rg.Tf.Loc.unitGL k ∧ IsOpen (K1 rd n : Set (GL (Fin n) k)) ∧ IsCompact (K1 rd n : Set (GL (Fin n) k)) ∧
      K1 rd n ≤ KO k n ∧
      (∀ (fb : GL (Fin n) F₀ → ℂ) (y : GL (Fin n) 𝒪[k]),
        infl rd fb (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) = fb (GeneralLinearGroup.map rd y)) ∧
      ∀ fb : GL (Fin n) F₀ → ℂ, GlobalTheory.BCT.IsHecke (K1 rd n) (infl rd fb) ∧ Test (infl rd fb) ∧ ∀ x, infl rd fb x ≠ 0 → x ∈ KO k n

def FrobFacts : Prop :=
  ∀ (k K : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Algebra k K] [ValuativeExtension k K] [FiniteDimensional k K] [IsGalois k K],
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (rk : 𝒪[k] →+* F₀) (rK : 𝒪[K] →+* F₁) (s : K ≃ₐ[k] K) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    (∀ τ : K ≃ₐ[k] K, τ ∈ Subgroup.zpowers s) ∧ ∀ n : ℕ, GlobalTheory.LBC.IsStable s (K1 rK n) ∧ GlobalTheory.LBC.IsStable s (KO K n) ∧
      ∀ y : GL (Fin n) 𝒪[K], ∃ y' : GL (Fin n) 𝒪[K],
        GeneralLinearGroup.map (algebraMap 𝒪[K] K) y' = GlobalTheory.LBC.galAct s n (GeneralLinearGroup.map (algebraMap 𝒪[K] K) y) ∧
        GeneralLinearGroup.map rK y' = GlobalTheory.LBC.galAct sb n (GeneralLinearGroup.map rK y)

def GlobOf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E], (Module.finrank F E).Prime →
    ∀ (v : Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)], (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ¬ GM.Split E v ∧ Module.finrank (v.adicCompletion F) (w.1.adicCompletion E) = Module.finrank F E ∧
      ∀ s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E, (∀ τ, τ ∈ Subgroup.zpowers s) →
        ∃ σ : E ≃ₐ[F] E, (∀ τ, τ ∈ Subgroup.zpowers σ) ∧ ∀ y, galFin σ v y w = s (y w)

def InflTrace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E], (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (v : Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) → GM.Unr E v →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ∀ (F₀ F₁ : Type) [Field F₀] [Fintype F₀] [Field F₁] [Fintype F₁] [Algebra F₀ F₁] (rk : 𝒪[v.adicCompletion F] →+* F₀) (rK : 𝒪[w.1.adicCompletion E] →+* F₁)
      (s : w.1.adicCompletion E ≃ₐ[v.adicCompletion F] w.1.adicCompletion E) (sb : F₁ ≃ₐ[F₀] F₁), IsRes rk rK s sb →
    ∀ (τ : SmIrr (Gw n v)) (τ' : SmIrr (Gw n w.1)), (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' →
      ∃ (I : τ'.V →ₗ[ℂ] τ'.V) (c : ℂ), GlobalTheory.LBC.IsTwInt (v.adicCompletion F) s τ'.ρ I ∧ c ≠ 0 ∧
        ∀ fb : GL (Fin n) F₀ → ℂ, (∀ a b, fb (b⁻¹ * a * b) = fb a) →
          GlobalTheory.BCT.twTr τ'.ρ (KO _ n) (K1 rK n) (infl rK (normLift sb fb)) I =
            c * GlobalTheory.BCT.twTr τ.ρ (KO _ n) (K1 rk n) (infl rk fb) LinearMap.id

def bor {F₀ : Type} [Field F₀] {n : ℕ} (θ : Fin n → (F₀ˣ →* ℂˣ)) (g : GL (Fin n) F₀) : ℂ :=
  if h : ∃ d : Fin n → F₀ˣ, (g : Matrix (Fin n) (Fin n) F₀).BlockTriangular id ∧ ∀ i, (g : Matrix (Fin n) (Fin n) F₀) i i = d i then
    ((∏ i, θ i (h.choose i) : ℂˣ) : ℂ) else 0

def borCard (F₀ : Type) [Field F₀] (n : ℕ) : ℕ :=
  Nat.card {g : GL (Fin n) F₀ // (g : Matrix (Fin n) (Fin n) F₀).BlockTriangular id}

def indBor {F₀ : Type} [Field F₀] {n : ℕ} (t : GL (Fin n) F₀ →* GL (Fin n) F₀) (θ : Fin n → (F₀ˣ →* ℂˣ)) (g : GL (Fin n) F₀) : ℂ :=
  (borCard F₀ n : ℂ)⁻¹ * ∑ᶠ x : GL (Fin n) F₀, bor θ (x⁻¹ * g * t x)

def TorFin : Prop :=
  ∀ (F₀ : Type) [Field F₀] [Fintype F₀] (n : ℕ) (θ : Fin n → (F₀ˣ →* ℂˣ)) (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (r : Representation ℂ (GL (Fin n) F₀) W),
    (∀ a b, indBor (MonoidHom.id _) θ (b⁻¹ * a * b) = indBor (MonoidHom.id _) θ a) ∧
    ((∃ x : W, x ≠ 0 ∧ ∀ g, bor θ g ≠ 0 → r g x = bor θ g • x) →
      LinearMap.trace ℂ W (∑ᶠ g, indBor (MonoidHom.id _) (fun i => (θ i)⁻¹) g • r g) ≠ 0) ∧
    ∀ (t : GL (Fin n) F₀ →* GL (Fin n) F₀) (A : W →ₗ[ℂ] W), (∀ g, r (t g) ∘ₗ A = A ∘ₗ r g) →
      LinearMap.trace ℂ W (∑ᶠ g, indBor t (fun i => (θ i)⁻¹) g • (r g ∘ₗ A)) ≠ 0 →
      ∃ x : W, x ≠ 0 ∧ ∀ g, bor θ g ≠ 0 → r g x = bor θ g • x

def FinAct : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (F₀ : Type) [Field F₀] [Fintype F₀]
    (rd : 𝒪[k] →+* F₀), Function.Surjective rd → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) k) V),
    (∀ g : GL (Fin n) F₀, ∃ y : GL (Fin n) 𝒪[k], GeneralLinearGroup.map rd y = g) ∧
    ∃ r : Representation ℂ (GL (Fin n) F₀) (fixed ρ (K1 rd n)),
      (∀ (y : GL (Fin n) 𝒪[k]) (x : fixed ρ (K1 rd n)),
        (r (GeneralLinearGroup.map rd y) x : V) = ρ (GeneralLinearGroup.map (algebraMap 𝒪[k] k) y) x) ∧
      ∀ (fb : GL (Fin n) F₀ → ℂ) (A : V →ₗ[ℂ] V) (hA : ∀ x ∈ fixed ρ (K1 rd n), A x ∈ fixed ρ (K1 rd n)),
        GlobalTheory.BCT.twTr ρ (KO k n) (K1 rd n) (infl rd fb) A =
          (Nat.card (GL (Fin n) F₀) : ℂ)⁻¹ * LinearMap.trace ℂ _ (∑ᶠ g, fb g • (r g ∘ₗ A.restrict hA))

end UpperTheory.Gal.InertialTypesAlt.L
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.MatchSmulAlt
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain ValuativeRel Matrix GroundTheory.Global GroundTheory.Global.SemiLocal
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets PositivityTheory.Rg.Tf.Loc UpperTheory.ConvolutionTheory.Loc
open GlobalTheory.SmGL hiding iwahori
open PositivityTheory.Rg.Tf.Geo (incFin galFin)
open UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.L

section Defs

variable {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] {n : ℕ}

def Near (r : ValueGroupWithZero E) (s : Fin n → Eˣ) : Prop := ∀ i, valuation E ((s i : E) - 1) ≤ r

def elemSet (r : ValueGroupWithZero E) (A : Set (Fin n → Eˣ)) : Set (GL (Fin n) E) :=
  {g | ∃ a ∈ ball n r, ∃ b ∈ ball n r, ∃ s ∈ A, g = a * diagT E (Fin n) s * b}

def sgT (σ : E ≃+* E) (u : Fin n → Eˣ) : Fin n → Eˣ := fun i => Units.map (σ : E →* E) (u i)

def Rel (σ : E ≃+* E) (r : ValueGroupWithZero E) (u ρ : Fin n → Eˣ) : Prop := ∃ p s, sgT σ p = p ∧ Near r s ∧ u = ρ * p * s

variable (k : Type) [Field k] [Algebra k E]

def nrmT (t : Fin n → Eˣ) : Fin n → kˣ := fun i => Units.map (Algebra.norm k : E →* k) (t i)

def nrmSet (r : ValueGroupWithZero E) (t : Fin n → Eˣ) : Set (Fin n → kˣ) := {x | ∃ u, Near r u ∧ x = nrmT k (t * u)}

end Defs

def SuppE : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∀ A : Set (Fin n → Eˣ), (∀ t ∈ A, Strict t) →
    (∀ δ g : GL (Fin n) E, g⁻¹ * δ * sg σ g ∈ elemSet r A → ∃ y, ∃ t ∈ A, ∃ s, Near r s ∧ Strict (t * s) ∧
      y⁻¹ * δ * sg σ y = diagT E (Fin n) (t * s)) ∧
    ∀ (δ y : GL (Fin n) E) (d : Fin n → Eˣ), Strict d → y⁻¹ * δ * sg σ y = diagT E (Fin n) d → ∀ g,
      g⁻¹ * δ * sg σ g ∈ elemSet r A ↔ ∃ u, (∃ t ∈ A, Near r (d * sgT σ u / u / t)) ∧ ∃ κ ∈ ball n r, g = y * diagT E (Fin n) u * κ

def CosetSum : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ K H : Subgroup G, IsOpen (K : Set G) → IsCompact (K : Set G) →
    IsClosed (H : Set G) → (∀ a ∈ H, ∀ b ∈ H, Commute a b) → ∀ ν : Measure H, ν.IsHaarMeasure →
    ∀ (ι : Type) (R : Finset ι) (x : ι → G) (V : Set H) (S : Set G), (∀ i ∈ R, ∀ h : H, h ∈ V ↔ (x i)⁻¹ * h * x i ∈ K) →
      (∀ g, g ∈ S ↔ ∃ i ∈ R, ∃ h ∈ H, ∃ κ ∈ K, g = h * x i * κ) →
      (∀ i ∈ R, ∀ j ∈ R, (∃ h ∈ H, ∃ κ ∈ K, x i = h * x j * κ) → i = j) →
      quotIntegral μ H ν (S.indicator 1) = (((R.card : ℝ) * μ.real K / ν.real V : ℝ) : ℂ)

def OneField : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∀ [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] (μ : Measure (GL (Fin n) E)), μ.IsHaarMeasure →
    ∀ A : Set (Fin n → Eˣ), (∀ t ∈ A, Strict t) → ∀ (δ y : GL (Fin n) E) (d : Fin n → Eˣ), Strict d →
      y⁻¹ * δ * sg σ y = diagT E (Fin n) d → ∀ H : Subgroup (GL (Fin n) E), (∀ c, c ∈ H ↔ c⁻¹ * δ * sg σ c = δ) →
    ∀ ν : Measure H, ν.IsHaarMeasure → ∀ R : Finset (Fin n → Eˣ),
      (∀ u, (∃ t ∈ A, Near r (d * sgT σ u / u / t)) ↔ ∃ ρ ∈ R, Rel σ r u ρ) → (∀ ρ ∈ R, ∀ ρ' ∈ R, Rel σ r ρ ρ' → ρ = ρ') →
      quotIntegral μ H ν (fun g => (elemSet r A).indicator 1 (g⁻¹ * δ * sg σ g)) =
        (((R.card : ℝ) * μ.real (ball n r) / ν.real {h : H | y⁻¹ * h * y ∈ ball n r} : ℝ) : ℂ)

def Reps : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (σ : E ≃+* E) (q : ℕ), Cyc σ q →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∃ R : Finset (Fin n → Eˣ), R.Nonempty ∧ (∀ u, Near r (sgT σ u / u) ↔ ∃ ρ ∈ R, Rel σ r u ρ) ∧
      (∀ ρ ∈ R, ∀ ρ' ∈ R, Rel σ r ρ ρ' → ρ = ρ') ∧ (∀ a b : Fin n → Eˣ, Near r a → Near r b → Near r (a * b) ∧ Near r a⁻¹) ∧
      ∀ z u ρ : Fin n → Eˣ, Rel σ r (z * u) (z * ρ) ↔ Rel σ r u ρ

def NormOpen : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∃ r₀ : ValueGroupWithZero k, 0 < r₀ ∧ r₀ < 1 ∧
      ∀ x : kˣ, valuation k ((x : k) - 1) ≤ r₀ → valuation E (algebraMap k E x - 1) ≤ r ∧
        ∃ u : Eˣ, valuation E ((u : E) - 1) ≤ r ∧ (x : k) = Algebra.norm k (u : E)

def NormDiag : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, (∀ d : Fin n → Eˣ, normGL σ (diagT E (Fin n) d) = incl (diagT k (Fin n) (nrmT k d)) ∧ (Strict d → Strict (nrmT k d)) ∧
        (Strict d → IsRegSemisimple (diagT k (Fin n) (nrmT k d)))) ∧
      (∀ (r : ValueGroupWithZero E) (d t : Fin n → Eˣ),
        (∃ u, Near r (d * sgT (σ : E ≃+* E) u / u / t)) ↔ nrmT k d ∈ nrmSet k r t) ∧
      ∀ r : ValueGroupWithZero E, r < 1 → ∀ t : Fin n → Eˣ, Strict t → (∀ x ∈ nrmSet k r t, Strict x) ∧ IsCompact (nrmSet k r t)

def Align : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (δ h y : GL (Fin n) E) (γ : GL (Fin n) k) (d : Fin n → Eˣ), Strict d → normGL σ δ = h * incl γ * h⁻¹ →
      y⁻¹ * δ * sigmaGL σ y = diagT E (Fin n) d → ∃ y' : GL (Fin n) k, y'⁻¹ * γ * y' = diagT k (Fin n) (nrmT k d) ∧
        ∀ t ∈ Subgroup.centralizer {γ}, y⁻¹ * (h * incl t * h⁻¹) * y = incl (y'⁻¹ * t * y')

def VolRatio : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] (r : ValueGroupWithZero E) (r' : ValueGroupWithZero k),
      0 < r → r < 1 → 0 < r' → r' < 1 → (∀ x : kˣ, valuation k ((x : k) - 1) ≤ r' → valuation E (algebraMap k E x - 1) ≤ r) →
      ∃ j : ℝ, 0 < j ∧ ∀ (γ y : GL (Fin n) k) (x : Fin n → kˣ), Strict x → y⁻¹ * γ * y = diagT k (Fin n) x →
        ∀ ν : Measure (Subgroup.centralizer {γ}), ν.IsHaarMeasure →
          ν.real {t | (incl (y⁻¹ * (t : GL (Fin n) k) * y) : GL (Fin n) E) ∈ ball n r} =
            j * ν.real {t | y⁻¹ * (t : GL (Fin n) k) * y ∈ ball n r'}

def ElemTest : Prop :=
  ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (n : ℕ) (r : ValueGroupWithZero E),
    0 < r → r < 1 → ∀ A : Set (Fin n → Eˣ), IsCompact A → IsOpen (elemSet r A) ∧ IsCompact (elemSet r A) ∧
      UpperTheory.ConvolutionTheory.C.Test ((elemSet r A).indicator (1 : GL (Fin n) E → ℂ)) ∧
      (elemSet r A).indicator (1 : GL (Fin n) E → ℂ) ∈ SB (GL (Fin n) E) ∧
      ∀ g ∈ elemSet r A, ∃ t ∈ A, ∃ x : Eˣ, valuation E ((x : E) - 1) ≤ r ∧ GeneralLinearGroup.det g = (∏ i, t i) * x

def ElemLoc : Prop :=
  ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E] (σ : E ≃ₐ[k] E), (∀ τ : E ≃ₐ[k] E, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) [MeasurableSpace (GL (Fin n) E)] [BorelSpace (GL (Fin n) E)] [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
      (μE : Measure (GL (Fin n) E)) (μk : Measure (GL (Fin n) k)), μE.IsHaarMeasure → μk.IsHaarMeasure →
    ∀ r : ValueGroupWithZero E, 0 < r → r < 1 → ∃ r₀ : ValueGroupWithZero k, 0 < r₀ ∧ r₀ < 1 ∧ ∀ r' ≤ r₀, 0 < r' →
      (∀ x : kˣ, valuation k ((x : k) - 1) ≤ r' → ∃ u : Eˣ, valuation E ((u : E) - 1) ≤ r ∧ (x : k) = Algebra.norm k (u : E)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : Fin n → Eˣ, Strict t →
        Match σ μE μk ((elemSet r {t}).indicator 1) ((c : ℂ) • (elemSet r' (nrmSet k r t)).indicator 1)

def NormLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime →
    ∀ (v : UpperTheory.ConvolutionTheory.Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
      ∀ η : Formalism.L2.Host.HChar F, IsNormChar E η → ∀ u : (w.1.adicCompletion E)ˣ,
        η.loc v (Units.map (Algebra.norm (v.adicCompletion F) : w.1.adicCompletion E →* v.adicCompletion F) u) = 1

def MatchSmul : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ) (v : UpperTheory.ConvolutionTheory.Pl F) (c : ℂ),
    c ≠ 0 → ∀ (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
      UpperTheory.ConvolutionTheory.GM.MatchAt σ v 1 φ (c • f) → UpperTheory.ConvolutionTheory.GM.MatchAt σ v c φ f

def ElemPair : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime →
    ∀ (v : UpperTheory.ConvolutionTheory.Pl F) (w : PlacesOver E v), (∀ w' : PlacesOver E v, w' = w) →
    ∀ [Algebra (v.adicCompletion F) (w.1.adicCompletion E)] [ValuativeExtension (v.adicCompletion F) (w.1.adicCompletion E)]
      [FiniteDimensional (v.adicCompletion F) (w.1.adicCompletion E)] [IsGalois (v.adicCompletion F) (w.1.adicCompletion E)],
      (∀ x, completionMap v w.1 x = algebraMap _ (w.1.adicCompletion E) x) →
    ∀ (n : ℕ) (r : ValueGroupWithZero (w.1.adicCompletion E)), 0 < r → r < 1 →
      ∃ r₀ : ValueGroupWithZero (v.adicCompletion F), 0 < r₀ ∧ r₀ < 1 ∧ ∀ r' ≤ r₀, 0 < r' →
      (∀ x : (v.adicCompletion F)ˣ, valuation _ ((x : v.adicCompletion F) - 1) ≤ r' → ∃ u : (w.1.adicCompletion E)ˣ,
        valuation _ ((u : w.1.adicCompletion E) - 1) ≤ r ∧ (x : v.adicCompletion F) = Algebra.norm _ (u : w.1.adicCompletion E)) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ t : Fin n → (w.1.adicCompletion E)ˣ, Strict t →
        UpperTheory.ConvolutionTheory.C.Test ((elemSet r {t}).indicator (1 : GL (Fin n) (w.1.adicCompletion E) → ℂ)) ∧
        UpperTheory.ConvolutionTheory.C.Test ((elemSet r' (nrmSet (v.adicCompletion F) r t)).indicator (1 : GL (Fin n) (v.adicCompletion F) → ℂ)) ∧
        UpperTheory.ConvolutionTheory.GM.MatchAt σ v c (fun g => (elemSet r {t}).indicator 1 (UpperTheory.ConvolutionTheory.GM.cmp w g))
          ((elemSet r' (nrmSet (v.adicCompletion F) r t)).indicator 1) ∧
        ∀ g ∈ elemSet r' (nrmSet (v.adicCompletion F) r t), g ∈ G.normSet E n v

end UpperTheory.Gal.InertialTypesAlt.L
end
end

