module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.FibAbs
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob.Fib

open MulAction

def Decomp : Prop :=
  ∀ (H X I : Type) [Group H] [MulAction H X] (H₀ : Subgroup H) (k : X → ℂ) (Hi Yi : I → Type) [∀ i, Group (Hi i)]
    [∀ i, MulAction (Hi i) (Yi i)] (φ : ∀ i, Hi i →* H) (e : ∀ i, Yi i → X) (ki : ∀ i, Yi i → ℂ),
    H₀.Normal → (∀ (h : H) x, k (h • x) = k x) → (∃ T : Finset X, ∀ x, k x ≠ 0 → ∃ h : H, ∃ s ∈ T, x = h • s) →
    (∀ i (h : Hi i) y, e i (h • y) = φ i h • e i y) → (∀ i, Function.Injective (e i)) →
    (∀ i (h : Hi i) y, ki i (h • y) = ki i y) → (∀ i y, ki i y ≠ 0 → k (e i y) = ki i y) →
    (∀ x, k x ≠ 0 → ∃ i y, ∃ h : H, ki i y ≠ 0 ∧ x = h • e i y) →
    (∀ i j y y' (h : H), ki i y ≠ 0 → ki j y' ≠ 0 → h • e i y = e j y' → i = j ∧ h ∈ (φ i).range) →
    gq H₀ k = ∑ᶠ i, gq (H₀.comap (φ i)) (ki i)

def PushZero : Prop :=
  ∀ (H Y : Type) [Group H] [MulAction H Y] (H₀ : Subgroup H) (k : Y → ℂ), H₀.index ≠ 0 → (∀ z ∈ H₀, ∀ y : Y, z • y = y) →
    (∀ (h : H) y, k (h • y) = k y) → (Function.support k).Finite → gq H₀ k = (∑ᶠ y, k y) / (H₀.index : ℂ)

def Push : Prop :=
  ∀ (H X' X : Type) [Group H] [MulAction H X'] [MulAction H X] (H₀ : Subgroup H) (q : X' → X) (k : X' → ℂ), H₀.Normal →
    (∀ (h : H) y, q (h • y) = h • q y) → (∀ z ∈ H₀, ∀ y : X', z • y = y) → (∀ (h : H) y, k (h • y) = k y) →
    (∃ T : Finset X', ∀ y, k y ≠ 0 → ∃ h : H, ∃ s ∈ T, y = h • s) → (∀ x, {y | q y = x ∧ k y ≠ 0}.Finite) →
    (∀ y, k y ≠ 0 → H₀.relIndex (stabilizer H (q y)) ≠ 0) →
    gq H₀ k = gq H₀ fun x => ∑ᶠ (y : X') (_ : q y = x), k y

def Bot : Prop :=
  ∀ (H Y : Type) [Group H] [MulAction H Y] (H₀ : Subgroup H) (k : Y → ℂ), (∀ a : ℂ, gq H₀ (fun y => a * k y) = a * gq H₀ k) ∧
    (Nat.card H₀ ≠ 0 → (∀ z ∈ H₀, ∀ y : Y, z • y = y) → gq H₀ k = (Nat.card H₀ : ℂ) * gq (⊥ : Subgroup H) k)

def Pair : Prop :=
  ∀ (H G I : Type) [Group H] [Group G] (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (c : H → ℂ) (f : G → ℂ)
    (δ : I → H) (Hi : I → Type) [∀ i, Group (Hi i)] (φ : ∀ i, Hi i →* H),
    H₀ ≤ Subgroup.center H → (∀ z ∈ H₀, ∀ y : G ⧸ U, j z • y = y) → (∀ h γ, c (h * γ * h⁻¹) = c γ) →
    (∀ u ∈ U, ∀ g, f (u⁻¹ * g * u) = f g) → (∀ g, {γ | c γ * f (g⁻¹ * j γ * g) ≠ 0}.Finite) →
    (∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U, g = j γ * s * u) →
    (∀ y : G ⧸ U, H₀.relIndex ((stabilizer G y).comap j) ≠ 0) →
    (∀ i x, x ∈ (φ i).range ↔ x * δ i = δ i * x) → (∀ i i' h, δ i' = h * δ i * h⁻¹ → i = i') →
    (∀ γ g, c γ * f (g⁻¹ * j γ * g) ≠ 0 → ∃ i h, γ = h * δ i * h⁻¹) →
    gqOn j H₀ U (fun y => ∑ᶠ γ, c γ * f (y.out⁻¹ * j γ * y.out)) =
      ∑ᶠ i, c (δ i) * gqOn (j.comp (φ i)) (H₀.comap (φ i)) U fun y => f (y.out⁻¹ * j (δ i) * y.out)

def SuppFin : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V), B.Fin → B.Γ₀ = ⊥ →
    ∀ f : G → ℂ, (Base.Tw.one B).IsTest f → ∀ g, {γ | f (g⁻¹ * B.ι γ * g) ≠ 0}.Finite

def TrKer : Prop :=
  ∀ (Γ G V : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (B : Base Γ G V), B.Fin →
    B.ω = 1 → B.Γ₀ = ⊥ → ∀ f : G → ℂ, (Base.Tw.one B).IsTest f →
    LinearMap.trace ℂ B.Forms ((Base.Tw.one B).R f) =
      gqOn B.ι ⊥ B.U fun y => ∑ᶠ γ, LinearMap.trace ℂ V (B.W γ) * f (y.out⁻¹ * B.ι γ * y.out)

def CardFib : Prop :=
  ∀ (G : Type) [Group G] (S U U' : Subgroup G) (x : G) (Ux : Subgroup S) (s₀ : S), S.Normal → U ≤ U' →
    (∀ s : S, s ∈ Ux ↔ x⁻¹ * s * x ∈ U) →
    {s : S ⧸ Ux | (((s.out : G) * x : G) : G ⧸ U') = (((s₀ : G) * x : G) : G ⧸ U')}.ncard = U.relIndex (U' ⊓ S)

def Cover : Prop :=
  ∀ (H G : Type) [Group H] [Group G] (S U U' : Subgroup G) (x : G) (Ux : Subgroup S) (ι : H →* S) (Φ : G → ℂ), S.Normal → U ≤ U' →
    (∀ s : S, s ∈ Ux ↔ x⁻¹ * s * x ∈ U) → U.relIndex (U' ⊓ S) ≠ 0 → (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
    (∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u ∈ Ux, s = ι h * t * u) → (∀ g : G, {h | g⁻¹ * ι h * g ∈ U'}.Finite) →
    gqOn ι ⊥ Ux (fun s => Φ (s.out * x)) =
      (U.relIndex (U' ⊓ S) : ℂ) * gqOn (S.subtype.comp ι) ⊥ U' ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)

def SumFib : Prop :=
  ∀ (Γ G I : Type) [Group Γ] [Group G] [Fintype I] (ι : Γ →* G) (S U' : Subgroup G) (Γ₀ : Subgroup Γ) (x : I → G) (Φ : G → ℂ),
    (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → Γ₀.Normal → (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
    (∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u) →
    (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
    gqOn ι Γ₀ U' (fun y => Φ y.out) =
      ∑ i, gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
        ((orbit S (x i : G ⧸ U')).indicator fun y => Φ y.out)

def IndexFin : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ), S.Normal → Γ₁.Normal →
    (∃ T : Finset G, ∀ s ∈ S, ∃ h ∈ Γ₁, ∃ t ∈ T, ∃ u ∈ U', s = ι h * t * u) → Γ₀.relIndex (U'.comap ι) ≠ 0 →
    (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0

def StabFin : Prop :=
  ∀ (H G : Type) [Group H] [Group G] (S U U' : Subgroup G) (ι : H →* S) (x : G), S.Normal → U.relIndex (U' ⊓ S) ≠ 0 →
    {h | x⁻¹ * ι h * x ∈ U}.Finite → {h | x⁻¹ * ι h * x ∈ U'}.Finite

def Reps : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U' : Subgroup G) (Y : Finset G) (x₀ : G), S.Normal →
    (∀ g, ∃ γ, ∃ s ∈ S, ∃ y ∈ Y, ∃ u ∈ U', g = ι γ * s * y * u) →
    ∃ (n : ℕ) (x : Fin (n + 1) → G), x 0 = x₀ ∧ (∀ i, x i = x₀ ∨ x i ∈ Y) ∧
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) ∧ ∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u

def OneFib : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (x : G) (Φ : G → ℂ),
    (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → Γ₁ ≤ S.comap ι → Γ₀.Normal → (∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y) →
    (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
    (∃ T : Finset G, ∀ s ∈ S, ∃ h ∈ Γ₁, ∃ t ∈ T, ∃ u ∈ U', s * x = ι h * t * u) →
    (∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0) →
    (Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) ≠ 0 → Nat.card (Γ₀.subgroupOf Γ₁) ≠ 0 →
    (Nat.card (Γ₀.subgroupOf Γ₁) : ℂ) * gqOn (ι.comp Γ₁.subtype) ⊥ U' ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out) =
      ((Γ₁ ⊔ Γ₀).relIndex ((S ⊔ U').comap ι) : ℂ) *
        gqOn (ι.comp ((S ⊔ U').comap ι).subtype) (Γ₀.subgroupOf ((S ⊔ U').comap ι)) U'
          ((orbit S (x : G ⧸ U')).indicator fun y => Φ y.out)

def Master : Prop :=
  ∀ (Γ G : Type) [Group Γ] [Group G] (ι : Γ →* G) (S U U' : Subgroup G) (Γ₁ Γ₀ : Subgroup Γ) (ι₁ : Γ₁ →* S),
    (∀ γ, (ι₁ γ : G) = ι γ) → (∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S) → Γ₁.Normal → Γ₀.Normal →
    (∀ z ∈ Γ₀, ∀ y : G ⧸ U', ι z • y = y) → U ≤ U' → U.relIndex (U' ⊓ S) ≠ 0 →
    (∀ x : G, ∃ T : Finset S, ∀ s, ∃ h, ∃ t ∈ T, ∃ u : S, x⁻¹ * u * x ∈ U ∧ s = ι₁ h * t * u) →
    (∀ x : G, {h | x⁻¹ * ι₁ h * x ∈ U}.Finite) →
    (∃ T : Finset G, ∀ g, ∃ γ, ∃ s ∈ T, ∃ u ∈ U', g = ι γ * s * u) →
    (∀ y : G ⧸ U', Γ₀.relIndex ((stabilizer G y).comap ι) ≠ 0) →
    ∃ c : ℝ, 0 < c ∧ ∀ (I : Type) [Fintype I] (x : I → G) (Ux : I → Subgroup S) (Φ : G → ℂ),
      (∀ i j γ, ∀ s ∈ S, ∀ u ∈ U', x j = ι γ * s * x i * u → i = j) → (∀ g, ∃ i γ, ∃ s ∈ S, ∃ u ∈ U', g = ι γ * s * x i * u) →
      (∀ i (s : S), s ∈ Ux i ↔ (x i)⁻¹ * s * x i ∈ U) → (∀ h g, Φ (ι h * g) = Φ g) → (∀ u ∈ U', ∀ g, Φ (g * u) = Φ g) →
      ∑ i, gqOn ι₁ ⊥ (Ux i) (fun s => Φ (s.out * x i)) = c * gqOn ι Γ₀ U' fun y => Φ y.out

end UpperTheory.V.Z.Sym.Glob.Fib
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.SymbolEx
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Defs

variable {K : Type} [Field K]

def jstd (τ : K) : Etau K τ →ₐ[K] Matrix (Fin 2) (Fin 2) K := Algebra.leftMulMatrix (QuadraticAlgebra.basis (-1) τ)

def Cu (O : Type) [CommRing O] [Algebra O K] (τ : K) : Subgroup (Etau K τ)ˣ :=
  (Units.map ((integralClosure O (Etau K τ)).val : integralClosure O (Etau K τ) →* Etau K τ)).range

def scalE (τ : K) : Subgroup (Etau K τ)ˣ := (Units.map (algebraMap K (Etau K τ) : K →* Etau K τ)).range


open Classical in
def toUnit {R : Type} [Monoid R] (x : R) : Rˣ := by
  classical
  exact if h : IsUnit x then h.unit else 1

variable {F : Type} [Field F] [NumberField F]

abbrev TA (τ : F) : Type := RP (fun v : Pl F => (Etau (Kv v) (cv v τ))ˣ) fun v => Cu (Ov v) (cv v τ)

def IsDiagT (τ : F) (φ : (Etau F τ)ˣ →* TA τ) : Prop := ∀ z v, ((φ z).1 v : Etau (Kv v) (cv v τ)) = emap (cv v) τ z


open Classical in
def ms (τ : F) : ℂ := by
  classical
  exact if h : ∃ φ, IsDiagT τ φ then
    mass h.choose (scalE τ) ((rpg _ _).box fun v => Cint (Ov v) (cv v τ)) else 0

variable {Δ : F} (D : Dat Δ)

def Dat.Good (t : Dat.Par F) (τ : F) : Prop := (∀ σ : F →+* ℝ, σ (τ ^ 2 - 4) < 0) ∧ ∀ v ∈ D.Sg, Ind (D.S v).H (cv v τ) (t v)

def Dat.nS (τ : F) : ℂ := ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), gOrb (Ov v) (jstd (cv v τ)) 1 (toUnit QuadraticAlgebra.omega)

def Dat.nK (τ : F) : ℂ := ∏ᶠ (v : Pl F) (_ : v ∉ D.Sg), gOrb (Ov v) (jstd (cv v τ)) (D.χ v) (toUnit (1 + QuadraticAlgebra.omega))

def Dat.sumS (ch : F → ℂ) (t : Dat.Par F) : ℂ := ∑ᶠ τ, one (D.Good t τ) * (ch τ * ms τ * D.nS τ)

def Dat.sumK (ch : F → ℂ) (t : Dat.Par F) : ℂ := ∑ᶠ τ, one (D.Good t τ) * (ch τ * ms τ * D.nK τ)

def Dat.Off (x : DA Δ) : Prop := ∀ v ∈ D.Sg, x.1 v = 1

end Defs

def BaseG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (U3 Δ) V) (Θ : V →ₗ[ℂ] V) (ch : F → ℂ), (∀ γ v, Θ (W γ v) = W (theta Δ γ) (Θ v)) →
    (∀ δ τ, HasTau δ τ → LinearMap.trace ℂ V (W δ ∘ₗ Θ) = ch τ) →
    ∃ (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s ∧ B.W = W ∧ s.Θ = Θ

def BaseS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (SU Δ) V) (ch : F → ℂ), (∀ (γ : SU Δ) τ, HasTr (γ : DX Δ) τ → LinearMap.trace ℂ V (W γ) = ch τ) →
    ∀ x : DA Δ, ∃ B : Base (SU Δ) (SA Δ) V, D.IsBS ch x B ∧ B.W = W

def BaseK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (W : Representation ℂ (DX Δ) V) (ch : F → ℂ),
    (∀ z s, IsScal z s → ∀ v, W s v = ((Algebra.norm ℚ (z : F) : ℚ) : ℂ)⁻¹ • v) →
    (∀ (g : DX Δ) τ, (mt g).trace = algebraMap F _ (2 + τ) → (mt g).det = algebraMap F _ (2 + τ) → LinearMap.trace ℂ V (W g) = ch τ) →
    ∃ B : Base (DX Δ) (DA Δ) V, D.IsBK ch B ∧ B.W = W

def FinG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw), D.IsBG ch B s → B.Fin ∧ ∀ t, D.Cone t → s.IsTest (D.FG t)

def FinS : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (x : DA Δ) (B : Base (SU Δ) (SA Δ) V), D.IsBS ch x B → B.Fin ∧ ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FSx t x)

def FinK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ch : F → ℂ)
    (B : Base (DX Δ) (DA Δ) V), D.IsBK ch B → B.Fin ∧ ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FK t)

def SideG : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ c e : ℝ, 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Base (U3 Δ) (GA Δ) V) (s : B.Tw),
    D.IsBG ch B s → ∀ t, D.Cone t → LinearMap.trace ℂ B.Forms (s.R (D.FG t)) = c * (D.sumS ch t + e * D.sumK ch t)

def SideK : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∃ c : ℝ, 0 < c ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ch : F → ℂ) (B : Base (DX Δ) (DA Δ) V),
    D.IsBK ch B → ∀ t, D.Cone t → LinearMap.trace ℂ B.Forms ((Base.Tw.one B).R (D.FK t)) = c * D.sumK ch t

def Recip : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d x : F), d ≠ 0 → x ≠ 0 →
    {v : Pl F | hs (cv v d) (cv v x) ≠ 1}.Finite ∧ (∏ᶠ v : Pl F, hs (cv v d) (cv v x)) = ∏ σ : F →+* ℝ, hs (σ d) (σ x)

def SymbolEx : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d : F), d ≠ 0 → ∀ y : ∀ v : Pl F, (Kv v)ˣ, {v | hs (cv v d) (y v : Kv v) ≠ 1}.Finite →
    (∏ᶠ v : Pl F, hs (cv v d) (y v : Kv v)) = 1 →
    ∃ x : F, x ≠ 0 ∧ (∀ σ : F →+* ℝ, 0 < σ x) ∧ ∀ v, hs (cv v d) (cv v x) = hs (cv v d) (y v : Kv v)

def HsMul : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (d x y : Kv v), d ≠ 0 → x ≠ 0 → y ≠ 0 → hs d (x * y) = hs d x * hs d y

def HsHasse : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (d x : F), d ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, hs (σ d) (σ x) = 1) →
    (∀ v : Pl F, hs (cv v d) (cv v x) = 1) → hs d x = 1

end UpperTheory.V.Z.Sym.Glob
end
end

