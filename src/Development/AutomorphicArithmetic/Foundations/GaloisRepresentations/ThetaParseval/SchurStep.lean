module

public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0010
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0013
public import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0005
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TP

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

def lift (M : Model σ X W) (om : Rep σ X W) (Φ : Fn F n d) (φ : UA σ X.J → ℂ) (h : UA σ W.J) : ℂ :=
  ∫ g in M.dom, theta om Φ g h * star (φ g) ∂M.μ

def mc (M : Model σ X W) (φ : UA σ X.J → ℂ) (g : UA σ X.J) : ℂ := pet M.μ M.dom (fun y => φ (y * g)) φ


variable (σ X) in
def gInf : Subgroup (UA σ X.J) := Subgroup.closure (UAt σ X (evI F))


variable (σ X) in
def gAt (S : Finset (Pl (F := F))) : Subgroup (UA σ X.J) := ⨆ v ∈ S, locGrp σ X v


variable (σ X) in
def gOff (S : Finset (Pl (F := F))) : Subgroup (UA σ X.J) :=
  Subgroup.closure {g | (∀ w : InfinitePlace F, (mat g).map (compInf F E w) = 1) ∧ ∀ v ∈ S, OffAt v g}

def IntAll (g : UA σ X.J) : Prop := ∀ v, IntAt v g

def IsFn (φ : UA σ X.J → ℂ) : Prop := Continuous φ ∧ ∀ γ ∈ ratU σ X.J, ∀ g, φ (γ * g) = φ g

def IsBump (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (v : Pl (F := F)) (H : Subgroup (UA σ X.J))
    (φ : (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  φ ∈ SB (Fin n × Fin d → Fv F v) ∧ φ ≠ 0 ∧ H ≤ locGrp σ X v ∧ (∀ g ∈ H, IntAt v g) ∧
    (∃ O : Set (UA σ X.J), IsOpen O ∧ 1 ∈ O ∧ ∀ g ∈ locGrp σ X v, g ∈ O → g ∈ H) ∧
    (∀ g ∈ H, Acts (evFin F v) (om (g, 1)) φ φ) ∧
    ∀ g ∈ locGrp σ X v, g ∉ H → ∃ (u : Matrix (Fin n) (Fin d) (AE F E)) (c c' : ℂ), At (evFin F v) u ∧ c ≠ c' ∧
      Acts (evFin F v) (M.co.rho B.ψ u) φ (c • φ) ∧ Acts (evFin F v) (M.co.rho B.ψ (mat g * u)) φ (c' • φ)

end Gen

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


variable (E) in
abbrev cj : E →ₐ[maximalRealSubfield E] E := (IsCMField.complexConj E).toAlgHom

structure IsBr {n : ℕ} (X : Spc (maximalRealSubfield E) E n) (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) : Prop where
  rat : ∀ g, e g ∈ ratU (cj E) X.J ↔ g ∈ GlobalTheory.UnitaryBC.ratU E n
  inf : ∀ g, e g ∈ gInf (cj E) X ↔ g ∈ GlobalTheory.UnitaryBC.infU E n
  fin : ∀ g, e g ∈ gOff (cj E) X ∅ ↔ g ∈ GlobalTheory.UnitaryBC.finU (E := E) (n := n)
  loc : ∀ (w : HeightOneSpectrum (𝓞 E)) g,
    e g ∈ locGrp (cj E) X (w.under (𝓞 (maximalRealSubfield E))) ↔ g ∈ GlobalTheory.UnitaryBC.locU n w
  emb : ∀ (w : InfinitePlace (maximalRealSubfield E)) (τ : EmbOver E w) g,
    (mat (e g)).map (piInf τ) = (GlobalTheory.UnitaryBC.cEmb τ.1 g).val
  spl : ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) g,
    ((mat (e g)).map (piW t)).map (complMap (splitPrime_under t)) = (GlobalTheory.UnitaryBC.cLoc (splitPrime t) g).val

abbrev CompAt {n : ℕ} (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (w : HeightOneSpectrum (𝓞 E))
    (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  GlobalTheory.UnitaryBC.IsCompAlong U (GlobalTheory.UnitaryBC.locU n w) ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype) τ.ρ

def LocPair {n d : ℕ} {v : Pl (maximalRealSubfield E)} (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v)
    (χX χW : Chr (maximalRealSubfield E) E) (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) ((splitPrime t).adicCompletion E)))
    (τ' : GlobalTheory.CuspRep.SmIrr (GL (Fin d) ((splitPrime t).adicCompletion E))) : Prop :=
  ∃ β : SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v)) →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] τ'.V, β ≠ 0 ∧
    ∀ (g : GL (Fin n) (Fv (maximalRealSubfield E) v)) (h : GL (Fin d) (Fv (maximalRealSubfield E) v))
      (Φ Φ₁ : SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v))),
      Φ₁.1 = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g h Φ.1 → ∀ x,
        β Φ₁ (τ.ρ (Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g) x) =
          τ'.ρ (Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) h) (β Φ x)

def IsLiftWt {n d : ℕ} (lam : DomWeight n) (mX mW : ℤ) (lam' : DomWeight d) : Prop :=
  ∀ k : Fin d, 2 * lam'.w k = (if h : (k : ℕ) < n then 2 * lam.w ⟨k, h⟩ - d - mW else 0) + n + mX

structure IsLift {n d : ℕ} (B : Base (maximalRealSubfield E) E) (χX χW : Chr (maximalRealSubfield E) E)
    (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n)
    (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)) : Prop where
  aut : GlobalTheory.UnitaryBC.IsAutRepU U'
  wt : ∀ w, ∃ lam' : DomWeight d, GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam' ∧ IsLiftWt (lam w) (mX w) (mW w) lam'
  loc : ∀ (v : Pl (maximalRealSubfield E)) (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) τ τ',
    CompAt U (splitPrime t) τ → CompAt U' (splitPrime t) τ' → LocPair t χX χW τ τ'

end CM

def TLift : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (B : Base (maximalRealSubfield E) E), B.IsGood (cj E) →
    ∀ (n : ℕ), 1 ≤ n → ∀ X : Spc (maximalRealSubfield E) E n, X.J = 1 → X.IsHerm (cj E) B n 0 →
    ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (W : Spc (maximalRealSubfield E) E d) (δ : E), W.J = δ • (1 : Matrix (Fin d) (Fin d) E) →
      W.IsSkew (cj E) B d 0 → ∀ (χX χW : Chr (maximalRealSubfield E) E) (mX mW : InfinitePlace (maximalRealSubfield E) → ℤ),
      IsHecke (maximalRealSubfield E) E χX → IsHecke (maximalRealSubfield E) E χW →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap (maximalRealSubfield E) (AF (maximalRealSubfield E))).toMonoidHom).range χW d →
      HasExp B.emb χX mX → HasExp B.emb χW mW →
      ∀ (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)) (lam : InfinitePlace (maximalRealSubfield E) → DomWeight n),
        GlobalTheory.UnitaryBC.IsAutRepU U → (∀ w, GlobalTheory.UnitaryBC.HasWeightAt U (B.emb w).1 (lam w)) →
        (∀ w k, (d : ℤ) + mW w ≤ 2 * (lam w).w k) → ∃ U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ), IsLift B χX χW mX mW lam U U'

def IsFin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (φ : ∀ v : Pl (F := F), (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = M.vac v

def BrEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (X : Spc (maximalRealSubfield E) E n) (δ : E), δ ≠ 0 →
    X.J = δ • (1 : Matrix (Fin n) (Fin n) E) → ∃ e, IsBr X e

def Datum : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W), IsPair B M χX χW om n 0 d 0 → 1 ≤ n →
    ∀ K a (e : UA σ X.J × UA σ X.J →* G2 σ X), IsStab2 B K → IsHgt K a → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ ν, @Measure.IsAddHaarMeasure _ _ _ (borel _) ν → ∀ S : Finset (Pl (F := F)), UnrOff χW (S : Set (Pl (F := F))) →
    ∀ (H : Pl (F := F) → Subgroup (UA σ X.J)) φ, IsFin M φ → (∀ v ∈ S, IsBump B M om v (H v) (φ v)) → (∀ v ∉ S, φ v = M.vac v) →
    ∀ f₀ ∈ M.Pol B.ψ B.emb, f₀ ≠ 0 → coef om ν (pure f₀ φ) 1 ≠ 0 ∧
      ∀ x ∈ gInf σ X, ∀ b ∈ gAt σ X S, ∀ c ∈ gOff σ X S, (b ∉ ⨆ v ∈ S, H v → coef om ν (pure f₀ φ) (x * b * c) = 0) ∧
        ∃ s : ℂ, ‖s‖ = a (e (c, 1)) ^ ((d : ℝ) / 2) ∧ (IntAll c → s = 1) ∧
          ∀ x' ∈ gInf σ X, ∀ b' ∈ ⨆ v ∈ S, H v, coef om ν (pure f₀ φ) (x' * b' * c) = s * coef om ν (pure f₀ φ) x'

def AbsNe : Prop :=
  ∀ (A B C : Type) [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] (μA : Measure A) (μB : Measure B) (μC : Measure C)
    [SFinite μA] [SFinite μB] [SFinite μC] (H : Set B) (K : Set C), MeasurableSet H → MeasurableSet K → μB H ≠ 0 → μB H ≠ ⊤ →
    μC K ≠ ⊤ → ∀ (f : A × B × C → ℂ) (m : A → C → ℂ) (s c₀ : C → ℂ) (κ : ℂ) (r : ℝ) (w : C → ENNReal), κ ≠ 0 → 0 < r →
    Integrable f (μA.prod (μB.prod μC)) → (∀ x b c, b ∉ H → f (x, b, c) = 0) → (∀ x c, ∀ b ∈ H, f (x, b, c) = s c * m x c) →
    (∀ c, ∫ x, m x c ∂μA = κ * c₀ c) → (∀ c ∈ K, s c = 1 ∧ c₀ c = r) → (∀ c, ‖c₀ c‖ ≤ r ∧ ‖s c‖ₑ ≤ w c) →
    ∫⁻ c in Kᶜ, w c ∂μC < μC K → ∫ y, f y ∂(μA.prod (μB.prod μC)) ≠ 0

def SameType {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
    (om : Rep (cj E) X W) (e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J) (U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ))
    (f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)) (φ : GlobalTheory.UnitaryBC.UA E n → ℂ) : Prop :=
  ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V) (ρ : Representation ℂ (GlobalTheory.UnitaryBC.infU E n) V)
    (i : V →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d)) (j : V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ)) (x₀ : V), ρ.IsIrreducible ∧
    i x₀ = f₀ ∧ j x₀ = φ ∧ (∀ x, j x ∈ U) ∧ (∀ k x, Acts (evI (maximalRealSubfield E)) (om (e k.1, 1)) (i x) (i (ρ k x))) ∧
    ∀ k x, j (ρ k x) = GlobalTheory.UnitaryBC.RU E n k.1 (j x)

def HasType {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
    (B : Base (maximalRealSubfield E) E) (M : Model (cj E) X W) (om : Rep (cj E) X W) (e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J)
    (f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)) (w : InfinitePlace (maximalRealSubfield E)) (lam' : DomWeight d) : Prop :=
  (GlobalTheory.Branching.sqRep ℂ d lam').IsIrreducible ∧ ∃ i : nablaSq ℂ d lam' →ₗ[ℂ] SInf (maximalRealSubfield E) (Fin n × Fin d),
    (∀ x, i x ∈ M.Pol B.ψ B.emb) ∧ (∃ x, i x = f₀) ∧ ∀ k ∈ GlobalTheory.UnitaryBC.embU d (B.emb w).1, ∀ x,
      Acts (evI (maximalRealSubfield E)) (om (1, e' k)) (i x) (i (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) x))

def ProjEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (d : ℕ) (ψ : GlobalTheory.UnitaryBC.UA E d → ℂ), GlobalTheory.UnitaryBC.IsAutFormU ψ → ψ ≠ 0 →
    ∃ (U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)) (pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)),
      GlobalTheory.UnitaryBC.IsAutRepU U' ∧ pr ψ ≠ 0 ∧ ∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧
        ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f)

def AbsIso : Prop :=
  ∀ (G V T : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup T] [Module ℂ T] (ρ : Representation ℂ G V)
    (U : Submodule ℂ V) (H : Subgroup G) (τ : Representation ℂ H T), (∀ g : G, ∃ h ∈ H, ∀ h' ∈ H, Commute (h⁻¹ * g) h') →
    (∀ g, ∀ u ∈ U, ρ g u ∈ U) → (∀ W ≤ U, (∀ g, ∀ u ∈ W, ρ g u ∈ W) → W = ⊥ ∨ W = U) → τ.IsIrreducible →
    ∀ f : T →ₗ[ℂ] V, f ≠ 0 → (∀ x, f x ∈ U) → (∀ (h : H) x, f (τ h x) = ρ h (f x)) → ∀ u ∈ U,
      (∃ (m : ℕ) (c : Fin m → T →ₗ[ℂ] V) (x : Fin m → T), (∀ i y, c i y ∈ U) ∧ (∀ i (h : H) y, c i (τ h y) = ρ h (c i y)) ∧
        u = ∑ i, c i (x i)) ∧
      (u ≠ 0 → ∃ p : V →ₗ[ℂ] T, p u ≠ 0 ∧ ∀ (h : H), ∀ y ∈ U, p (ρ h y) = τ h (p y))

end UpperTheory.TP

end
