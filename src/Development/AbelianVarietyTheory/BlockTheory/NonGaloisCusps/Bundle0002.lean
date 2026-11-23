module

public import Mathlib
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Objects

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

def IsEquivariant (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') :
    Prop :=
  ∀ g x, f (ρ g x) = ρ' g (f x)

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem actVB_mulVB (ρ : Representation LL G V) (g : G) (c : K₀) (x : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (actVB PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, mulVB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem comm_smul (c : K₀) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (c • x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v =>
    rw [TensorProduct.smul_tmul', Algebra.smul_def]
    simp [mulVB]
  | add a b ha hb => simp only [smul_add, map_add (f := _), ha, hb]

def DcrisK₀ (ρ : Representation LL G V) : Submodule K₀ (B ⊗[Qp] V) where
  carrier := {x | TensorProduct.comm Qp B V x ∈ Dcris PD ρ}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at ha hb ⊢
    exact (Dcris PD ρ).add_mem ha hb
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, mem_Dcris] at hx ⊢
    intro g
    rw [comm_smul (LL := LL), actVB_mulVB, hx]

def comparison (ρ : Representation LL G V) :
    B ⊗[K₀] ↥(DcrisK₀ PD ρ) →ₗ[B] B ⊗[Qp] V :=
  LinearMap.liftBaseChange B (DcrisK₀ PD ρ).subtype

theorem comparison_tmul (ρ : Representation LL G V) (b : B) (d : ↥(DcrisK₀ PD ρ)) :
    comparison PD ρ (b ⊗ₜ[K₀] d) = b • (d : B ⊗[Qp] V) := by
  simp [comparison]

def tensorB (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

theorem tensorB_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    tensorB (Qp := Qp) (B := B) f x ∈ Dcris PD ρ' := by
  have hm : ∀ g y, tensorB (Qp := Qp) (B := B) f (actVB PD ρ g y) =
      actVB PD ρ' g (tensorB (Qp := Qp) (B := B) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [tensorB, actVB, hf g]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [mem_Dcris] at hx ⊢
  intro g
  rw [← hm, hx]

def DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : IsEquivariant ρ ρ' f) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ') :=
  (tensorB (Qp := Qp) (B := B) f).restrict (tensorB_mem PD hf)

def prodB : (V ⊗[Qp] B) ⊗[LL] (V' ⊗[Qp] B) →ₗ[LL] (V ⊗[LL] V') ⊗[Qp] B :=
  (AlgebraTensorModule.map (LinearMap.id : V ⊗[LL] V' →ₗ[LL] V ⊗[LL] V')
      (LinearMap.mul' Qp B)).comp
    (AlgebraTensorModule.tensorTensorTensorComm Qp Qp LL LL V B V' B).toLinearMap

theorem prodB_tmul (v : V) (b : B) (v' : V') (b' : B) :
    prodB (LL := LL) ((v ⊗ₜ[Qp] b) ⊗ₜ[LL] (v' ⊗ₜ[Qp] b')) = (v ⊗ₜ[LL] v') ⊗ₜ[Qp] (b * b') := by
  simp [prodB]

end Objects

def InvariantsEq : Prop :=
  ∀ b : B, (∀ g, PD.actB g b = b) ↔ b ∈ Set.range (algebraMap K₀ B)

theorem invariantsEq : InvariantsEq PD := fun b =>
  ⟨fun h => PD.invB b h, by
    rintro ⟨c, rfl⟩ g
    exact (PD.actB g).commutes c⟩

variable (LL : Type) [Field LL] [Algebra Qp LL]

def DimLe : Prop :=
  FontaineLe PD LL ∧
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), FiniteDimensional LL ↥(Dcris PD ρ)

def ComparisonBij : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → Function.Bijective (comparison PD ρ)

def SubCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V' →ₗ[LL] V),
    IsEquivariant ρ' ρ f → Function.Injective f → IsCrys PD ρ → IsCrys PD ρ'

def QuotCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V') (f : V →ₗ[LL] V'),
    IsEquivariant ρ ρ' f → Function.Surjective f → IsCrys PD ρ → IsCrys PD ρ'

def SumCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.prod ρ')

def TensorCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V)
    (V' : Type) [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [FiniteDimensional LL V'] (ρ' : Representation LL G V'),
    IsCrys PD ρ → IsCrys PD ρ' → IsCrys PD (ρ.tprod ρ')

def DualCrys : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V),
    IsCrys PD ρ → IsCrys PD ρ.dual

def DcrisExact : Prop :=
  ∀ (V₀ : Type) [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [FiniteDimensional LL V₀] (ρ₀ : Representation LL G V₀)
    (V₁ : Type) [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [FiniteDimensional LL V₁] (ρ₁ : Representation LL G V₁)
    (V₂ : Type) [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [FiniteDimensional LL V₂] (ρ₂ : Representation LL G V₂)
    (i : V₀ →ₗ[LL] V₁) (p : V₁ →ₗ[LL] V₂) (hi : IsEquivariant ρ₀ ρ₁ i) (hp : IsEquivariant ρ₁ ρ₂ p),
    Function.Injective i → Function.Exact i p → Function.Surjective p →
    IsCrys PD ρ₀ → IsCrys PD ρ₁ → IsCrys PD ρ₂ →
    Function.Injective (DcrisMap PD hi) ∧ Function.Exact (DcrisMap PD hi) (DcrisMap PD hp) ∧
      Function.Surjective (DcrisMap PD hp)

def LetterDim : Prop :=
  Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀ →
  ∀ (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] (ρ : Representation LL G V), IsCrys PD ρ →
    ∀ τ₀ : K₀ →ₐ[Qp] LL,
      FiniteDimensional LL ↥(DcrisL PD ρ τ₀) ∧ finrank LL ↥(DcrisL PD ρ τ₀) = finrank LL V

def FormalismFor : Prop :=
  InvariantsEq PD ∧ DimLe PD LL ∧ ComparisonBij PD LL ∧ SubCrys PD LL ∧ QuotCrys PD LL ∧
    SumCrys PD LL ∧ TensorCrys PD LL ∧ DualCrys PD LL ∧ DcrisExact PD LL ∧ LetterDim PD LL

end Generic

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def LocInvariantsEq : Prop := ∀ K : FinExt l, InvariantsEq (P.PD K)

def LocDimLe : Prop := ∀ K LL : FinExt l, DimLe (P.PD K) ↥LL.1

def LocComparisonBij : Prop := ∀ K LL : FinExt l, ComparisonBij (P.PD K) ↥LL.1

def LocSubCrys : Prop := ∀ K LL : FinExt l, SubCrys (P.PD K) ↥LL.1

def LocQuotCrys : Prop := ∀ K LL : FinExt l, QuotCrys (P.PD K) ↥LL.1

def LocSumCrys : Prop := ∀ K LL : FinExt l, SumCrys (P.PD K) ↥LL.1

def LocTensorCrys : Prop := ∀ K LL : FinExt l, TensorCrys (P.PD K) ↥LL.1

def LocDualCrys : Prop := ∀ K LL : FinExt l, DualCrys (P.PD K) ↥LL.1

def LocDcrisExact : Prop := ∀ K LL : FinExt l, DcrisExact (P.PD K) ↥LL.1

def LocLetterDim : Prop := ∀ K LL : FinExt l, LetterDim (P.PD K) ↥LL.1

def FontaineFormalism : Prop :=
  LocInvariantsEq l P ∧ LocDimLe l P ∧ LocComparisonBij l P ∧ LocSubCrys l P ∧ LocQuotCrys l P ∧
    LocSumCrys l P ∧ LocTensorCrys l P ∧ LocDualCrys l P ∧ LocDcrisExact l P ∧ LocLetterDim l P

theorem fontaineFormalism_iff :
    FontaineFormalism l P ↔ ∀ K LL : FinExt l, FormalismFor (P.PD K) ↥LL.1 :=
  ⟨fun h K LL => ⟨h.1 K, h.2.1 K LL, h.2.2.1 K LL, h.2.2.2.1 K LL, h.2.2.2.2.1 K LL,
      h.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.1 K LL, h.2.2.2.2.2.2.2.2.1 K LL,
      h.2.2.2.2.2.2.2.2.2 K LL⟩,
    fun h => ⟨fun K => (h K K).1, fun K LL => (h K LL).2.1, fun K LL => (h K LL).2.2.1,
      fun K LL => (h K LL).2.2.2.1, fun K LL => (h K LL).2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.1, fun K LL => (h K LL).2.2.2.2.2.2.2.2.1,
      fun K LL => (h K LL).2.2.2.2.2.2.2.2.2⟩⟩

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DualExactSequence
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

variable {l : ℕ} [Fact l.Prime]

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

abbrev Emb (K LL : FinExt l) : Type := ↥K.1 →ₐ[ℚ_[l]] ↥LL.1

def embeddingRestrictMaxUnramified {K LL : FinExt l} (τ : Emb K LL) : ↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)

section Objects

variable (P : LocPrime l) {K LL : FinExt l}

abbrev iota (T : Lat K LL) : T.V ⊗[ℚ_[l]] P.R.B →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  ιV (P.PD K) (LL := ↥LL.1) (V := T.V)

abbrev filV (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  FilV (P.PD K) (LL := ↥LL.1) (V := T.V) a

abbrev mulK (T : Lat K LL) (c : ↥K.1) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T.V ⊗[ℚ_[l]] P.R.BdR :=
  mulVdR (Qp := ℚ_[l]) (K := ↥K.1) (BdR := P.R.BdR) (LL := ↥LL.1) (V := T.V) c

def filD (T : Lat K LL) (a : ℤ) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  DdR (P.PD K) T.ρ ⊓ filV P T a

def tdR (K : FinExt l) : P.R.BdRˣ := ((P.PD K).t_unit.map (P.PD K).ι).unit

def offComp (T : Lat K LL) (τ : Emb K LL) : Submodule ↥LL.1 (T.V ⊗[ℚ_[l]] P.R.BdR) :=
  Submodule.span ↥LL.1 {z | ∃ (c : ↥K.1), ∃ y ∈ DdR (P.PD K) T.ρ, z = mulK P T c y - τ c • y}

def mapdR {T T' : Lat K LL} (f : T.V →ₗ[↥LL.1] T'.V) :
    T.V ⊗[ℚ_[l]] P.R.BdR →ₗ[↥LL.1] T'.V ⊗[ℚ_[l]] P.R.BdR :=
  AlgebraTensorModule.map f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)

end Objects

section Shapes

variable {K LL : FinExt l}

def IsSES {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V) : Prop :=
  (∀ σ x, f (T₀.ρ σ x) = T₁.ρ σ (f x)) ∧ (∀ σ x, g (T₁.ρ σ x) = T₂.ρ σ (g x)) ∧
    Function.Injective f ∧ Function.Exact f g ∧ Function.Surjective g

def IsDualRep {T T' : Lat K LL} (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1) : Prop :=
  (∀ σ x y, β (T.ρ σ x) (T'.ρ σ y) = β x y) ∧ Function.Bijective β.flip

def IsTensorRep {T₁ T₂ T₃ : Lat K LL} (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V) : Prop :=
  ∀ σ x y, T₃.ρ σ (e (x ⊗ₜ[↥LL.1] y)) = e (T₁.ρ σ x ⊗ₜ[↥LL.1] T₂.ρ σ y)

def SubSES (P : LocPrime l) {T₀ T₁ T₂ : Lat K LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (g : T₁.V →ₗ[↥LL.1] T₂.V) (A₀ : Submodule ↥LL.1 (T₀.V ⊗[ℚ_[l]] P.R.BdR))
    (A₁ : Submodule ↥LL.1 (T₁.V ⊗[ℚ_[l]] P.R.BdR))
    (A₂ : Submodule ↥LL.1 (T₂.V ⊗[ℚ_[l]] P.R.BdR)) : Prop :=
  (∀ x ∈ A₀, mapdR P f x = 0 → x = 0) ∧
    (∀ y, (∃ x ∈ A₀, mapdR P f x = y) ↔ (y ∈ A₁ ∧ mapdR P g y = 0)) ∧
    (∀ z, (∃ y ∈ A₁, mapdR P g y = z) ↔ z ∈ A₂)

end Shapes

section At

variable (P : LocPrime l) (K LL : FinExt l)

def CrysDeRhamAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → IsDR (P.PD K) T.ρ

def DdRSpanAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    DdR (P.PD K) T.ρ = Submodule.span ↥LL.1
      {z | ∃ (c : ↥K.1), ∃ x ∈ Dcris (P.PD K) T.ρ, z = mulK P T c (iota P T x)}

def ComponentIsoAt : Prop :=
  ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ → ∀ τ : Emb K LL,
    ∃ e : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)) ≃ₗ[↥LL.1] ↥(DdRE (P.PD K) T.ρ τ),
      ∀ x : ↥(DcrisL (P.PD K) T.ρ (embeddingRestrictMaxUnramified τ)), iota P T (x : T.V ⊗[ℚ_[l]] P.R.B) - (e x : T.V ⊗[ℚ_[l]] P.R.BdR) ∈ offComp P T τ

def UnramOntoAt : Prop :=
  K.1 ≤ MaximalUnramifiedExtension l → ∀ T : Lat K LL, IsCrys (P.PD K) T.ρ →
    (Dcris (P.PD K) T.ρ).map (iota P T) = DdR (P.PD K) T.ρ

def FilZeroAt : Prop :=
  ∀ T : Lat K LL, IsDR (P.PD K) T.ρ →
    filV P T 0 = Submodule.span ↥LL.1
      {z | ∃ (a : ℤ), ∃ b ∈ (P.PD K).Fil 0, ∃ d ∈ filD P T a,
        z = mulVR T (((tdR P K ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b) d}

def StrictAt : Prop :=
  ∀ (T₀ T₁ T₂ : Lat K LL) (f : T₀.V →ₗ[↥LL.1] T₁.V) (g : T₁.V →ₗ[↥LL.1] T₂.V), IsSES f g →
    IsDR (P.PD K) T₀.ρ → IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    ∀ (τ : Emb K LL) (a : ℤ), SubSES P f g
      (FildR (P.PD K) T₀.ρ τ a) (FildR (P.PD K) T₁.ρ τ a) (FildR (P.PD K) T₂.ρ τ a)

def DualJumpsAt : Prop :=
  ∀ (T T' : Lat K LL) (β : T.V →ₗ[↥LL.1] T'.V →ₗ[↥LL.1] ↥LL.1), IsDualRep β →
    IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ a ↔ IsJumpV (P.PD K) T.ρ τ (-a)) ∧
        multV (P.PD K) T'.ρ τ a = multV (P.PD K) T.ρ τ (-a)

def TensorJumpsAt : Prop :=
  ∀ (T₁ T₂ T₃ : Lat K LL) (e : T₁.V ⊗[↥LL.1] T₂.V ≃ₗ[↥LL.1] T₃.V), IsTensorRep e →
    IsDR (P.PD K) T₁.ρ → IsDR (P.PD K) T₂.ρ →
    IsDR (P.PD K) T₃.ρ ∧ ∀ (τ : Emb K LL) (c : ℤ),
      (IsJumpV (P.PD K) T₃.ρ τ c ↔
        ∃ a b : ℤ, IsJumpV (P.PD K) T₁.ρ τ a ∧ IsJumpV (P.PD K) T₂.ρ τ b ∧ a + b = c) ∧
      ∀ S : Finset ℤ, JumpsInV (P.PD K) T₁.ρ τ (S : Set ℤ) →
        multV (P.PD K) T₃.ρ τ c =
          ∑ a ∈ S, multV (P.PD K) T₁.ρ τ a * multV (P.PD K) T₂.ρ τ (c - a)

def TwistJumpsAt : Prop :=
  ∀ T T' : Lat K LL, IsTwistRep (cycLL (P.PD K) ↥LL.1) T.ρ T'.ρ → IsDR (P.PD K) T.ρ →
    IsDR (P.PD K) T'.ρ ∧ ∀ (τ : Emb K LL) (a : ℤ),
      (IsJumpV (P.PD K) T'.ρ τ (a - 1) ↔ IsJumpV (P.PD K) T.ρ τ a) ∧
        multV (P.PD K) T'.ρ τ (a - 1) = multV (P.PD K) T.ρ τ a

def PotCrysDeRhamAt : Prop :=
  ∀ (T : Lat K LL) (K' : FinExt l) (hK : K.1 ≤ K'.1),
    IsCrys (P.PD K') (T.ρ.comp (Subgroup.inclusion (GK_le hK))) → IsDR (P.PD K) T.ρ

end At

def OverGood (C : FinExt l → FinExt l → Prop) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → C K LL

section Good

variable (l) (P : LocPrime l)

def CrysDeRham : Prop := OverGood (CrysDeRhamAt P)
def DdRSpan : Prop := OverGood (DdRSpanAt P)
def ComponentIso : Prop := OverGood (ComponentIsoAt P)
def UnramOnto : Prop := OverGood (UnramOntoAt P)
def FilZero : Prop := OverGood (FilZeroAt P)
def Strict : Prop := OverGood (StrictAt P)
def DualJumps : Prop := OverGood (DualJumpsAt P)
def TensorJumps : Prop := OverGood (TensorJumpsAt P)
def TwistJumps : Prop := OverGood (TwistJumpsAt P)
def PotCrysDeRham : Prop := OverGood (PotCrysDeRhamAt P)

def DeRhamComparison : Prop :=
  CrysDeRham l P ∧ DdRSpan l P ∧ ComponentIso l P ∧ UnramOnto l P ∧ FilZero l P ∧ Strict l P ∧
    DualJumps l P ∧ TensorJumps l P ∧ TwistJumps l P ∧ PotCrysDeRham l P

end Good

end GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Core

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Ops

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def mulPeriod (b : BdR) : V ⊗[Qp] BdR →ₗ[LL] V ⊗[Qp] BdR :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

def mapdR {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (f : V →ₗ[LL] V') : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR :=
  AlgebraTensorModule.map f (LinearMap.id : BdR →ₗ[Qp] BdR)

def tdR : BdRˣ := (PD.t_unit.map PD.ι).unit

variable (ρ : Representation LL G V)

def filDdR (a : ℤ) : Submodule LL (V ⊗[Qp] BdR) := DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a

def jumpMult (τ : K →ₐ[Qp] LL) (a : ℤ) : ℕ :=
  Module.finrank LL (↥(FildR PD ρ τ a) ⧸ (FildR PD ρ τ (a + 1)).comap (FildR PD ρ τ a).subtype)

end Ops

variable [TopologicalSpace G] (LL O : Type) [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL]
  [TopologicalSpace LL]

def CrysDeRhamCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → IsDR PD T.ρ

def SpanCore : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    DdR PD T.ρ = ⨆ c : K, ((Dcris PD T.ρ).map (ιV PD (LL := LL) (V := T.V))).map
      (mulVdR (Qp := Qp) (LL := LL) (V := T.V) (BdR := BdR) c)

def StrictCore : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (f : T₀.V →ₗ[LL] T₁.V) (g : T₁.V →ₗ[LL] T₂.V),
    (∀ s x, f (T₀.ρ s x) = T₁.ρ s (f x)) → (∀ s x, g (T₁.ρ s x) = T₂.ρ s (g x)) →
    Function.Injective f → Function.Exact f g → Function.Surjective g →
    IsDR PD T₀.ρ → IsDR PD T₁.ρ → IsDR PD T₂.ρ →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      (∀ x ∈ FildR PD T₀.ρ τ a, mapdR (Qp := Qp) (BdR := BdR) f x = 0 → x = 0) ∧
      (FildR PD T₀.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) f) =
        FildR PD T₁.ρ τ a ⊓ LinearMap.ker (mapdR (Qp := Qp) (BdR := BdR) g) ∧
      (FildR PD T₁.ρ τ a).map (mapdR (Qp := Qp) (BdR := BdR) g) = FildR PD T₂.ρ τ a

end Core

section Local

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

def CrysDeRham : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → CrysDeRhamCore (P.PD K) ↥LL.1 ↥(OL LL)

def Strictness : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → StrictCore (P.PD K) ↥LL.1 ↥(OL LL)

end Local

end GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual
end
end

