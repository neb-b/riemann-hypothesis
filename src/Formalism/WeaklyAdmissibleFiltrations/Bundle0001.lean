module

public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

-- bundled from Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

def CobF : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) [TopologicalSpace G] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousConstSMul LL V],
    (∀ x, Continuous fun g => ρ g x) → B1 ρ ≤ finiteCocycles PD ρ ∧ finiteCocycles PD ρ ≤ continuousCocycles ρ

def TorsFreeT : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    (ρ : Representation LL G V) [TopologicalSpace G] [TopologicalSpace V]
    [ContinuousAdd V] [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (c : G → V) (a : O),
    c ∈ latticeCocycles L → algebraMap O LL a ≠ 0 → a • c ∈ latticeFiniteCocycles PD L → c ∈ latticeFiniteCocycles PD L

def CocyclesFunctorial : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    (f : V →ₗ[LL] V'), Continuous f → (∀ g x, f (ρ g x) = ρ' g (f x)) →
    ∀ c, (c ∈ continuousCocycles ρ → f ∘ c ∈ continuousCocycles ρ') ∧ (c ∈ finiteCocycles PD ρ → f ∘ c ∈ finiteCocycles PD ρ')

def ImFLe : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul LL V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (F : LatHom L L'),
    (∀ x, Continuous fun g => ρ' g x) → F.ImF PD ≤ latticeFiniteCocycles PD L' ∧ (F.col PD = 0 ↔ F.LiftF PD 0)

def TrivCrys : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    [FiniteDimensional Qp LL] [FiniteDimensional Qp K₀],
    IsCrys PD (1 : Representation LL G LL)

def ExLattice : Prop :=
  ∀ (G : Type) [Group G] (LL : Type) [Field LL] (O : Type) [CommRing O] [IsDomain O]
    [Algebra O LL], Function.Injective (algebraMap O LL) →
    Nonempty (Lattice (O := O) (1 : Representation LL G LL))

def ExPD : Prop :=
  Nonempty (PeriodData (Multiplicative ℤ) ℚ ℚ ℚ (LaurentPolynomial ℚ) (LaurentPolynomial ℚ))

def WachCol : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (O : Type) [CommRing O] [Algebra O LL]
    (V V' : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module O V'] [IsScalarTower O LL V']
    (ρ : Representation LL G V) (ρ' : Representation LL G V') [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL V']
    (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (F : LatHom L L')
    (A D D' : Type) [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
    [IsScalarTower O A D] [AddCommGroup D'] [Module A D'] [Module O D'] [IsScalarTower O A D']
    (Bw : Formalism.CoboundaryTransfers.Base O A) (M : ℕ) (W : Formalism.CoboundaryTransfers.WachMod Bw M D)
    (W' : Formalism.CoboundaryTransfers.WachMod Bw M D') (Fw : Formalism.CoboundaryTransfers.Hom W W')
    (cl : W.Z1 →ₗ[O] LatticeCohomology L) (cl' : W'.Z1 →ₗ[O] LatticeCohomology L'),
    Bw.p = PD.p → WachLink PD L W cl → WachLink PD L' W' cl' →
    (∀ (pr : W.Z1) (pr' : W'.Z1), (pr' : D' × D') = Fw.f2 pr → F.H1map (cl pr) = cl' pr') →
    F.col PD = Fw.col ∧ ∀ e, F.LiftF PD e ↔ Fw.LiftF e

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.StatementPC
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

structure PotCrysData (G : Type) [Group G] (Qp K₀ K K₀' K' : Type) [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR] where
  H : Subgroup G
  normal : H.Normal
  finiteIndex : H.FiniteIndex
  PD : PeriodData G Qp K₀ K B BdR
  PD' : PeriodData H Qp K₀' K' B BdR
  actB_eq : ∀ (h : H) (b : B), PD'.actB h b = PD.actB (h : G) b
  actdR_eq : ∀ (h : H) (b : BdR), PD'.actdR h b = PD.actdR (h : G) b
  φ_eq : ∀ b : B, PD'.φ b = PD.φ b
  ι_eq : ∀ b : B, PD'.ι b = PD.ι b
  Fil_eq : ∀ a, (PD'.Fil a : Set BdR) = PD.Fil a
  p_eq : PD'.p = PD.p
  t_eq : PD'.t = PD.t
  χ_eq : ∀ h : H, PD'.χ h = PD.χ (h : G)
  stableK₀' : ∀ (g : G) (c : K₀'), ∃ c' : K₀', PD.actB g (algebraMap K₀' B c) = algebraMap K₀' B c'

namespace PotCrysData

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

def resH : Representation LL PC.H V := ρ.comp PC.H.subtype

def Dpcris : Submodule LL (V ⊗[Qp] B) := Dcris PC.PD' (PC.resH ρ)

def IsPotCrys : Prop := IsCrys PC.PD' (PC.resH ρ)

def Iner : Subgroup G where
  carrier := {g | ∀ c : K₀', PC.PD.actB g (algebraMap K₀' B c) = algebraMap K₀' B c}
  one_mem' := fun c => by simp
  mul_mem' := by
    intro a b ha hb c
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, AlgEquiv.mul_apply, hb c, ha c]
  inv_mem' := by
    intro a ha c
    simp only [Set.mem_setOf_eq] at ha ⊢
    conv_lhs => rw [← ha c]
    rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply]

def Eig (I : Subgroup G) (a : I →* LLˣ) : Submodule LL (V ⊗[Qp] B) :=
  PC.Dpcris ρ ⊓ ⨅ g : I, LinearMap.ker (actVB PC.PD ρ (g : G) - ((a g : LLˣ) : LL) • LinearMap.id)

def InertiaThrough (Sig : Finset (PC.Iner →* LLˣ)) : Prop :=
  (∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1) ∧
    (∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p) ∧ PC.Dpcris ρ = ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a

def IsFrob (F : G) : Prop :=
  ∀ c : K₀', PC.PD.actB F (algebraMap K₀' B c) = algebraMap K₀' B (PC.PD'.σ c)

end PotCrysData

def FrobStable {G : Type} [Group G] {LL : Type} [Field LL] (I : Subgroup G) (F : G)
    (Sig : Finset (I →* LLˣ)) : Prop :=
  ∀ a ∈ Sig, ∃ b ∈ Sig, ∀ g : I, ∀ h : I, (h : G) = F⁻¹ * g * F → b g = a h

end Formalism.WeaklyAdmissibleFiltrations
end
end

-- bundled from Formalism.WeaklyAdmissibleFiltrations.StatementTor
section
noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module TensorProduct

section Tor

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V}

def actT (L : Lattice (O := O) ρ) (g : G) : ↥L.T →ₗ[O] ↥L.T :=
  ((ρ g).restrictScalars O).restrict (L.stable g)

def StableSub (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) : Prop :=
  ∀ g, ∀ x ∈ I, actT L g x ∈ I

def actQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) (g : G) :
    (↥L.T ⧸ I) →ₗ[O] (↥L.T ⧸ I) :=
  I.mapQ I (actT L g) (fun x hx => hI g x hx)

def quotientCocycles [TopologicalSpace G] (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (G → ↥L.T ⧸ I) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actQ L I hI g (c h)}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨ha.comp (c • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, ha', map_smul, smul_add]

def BQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (G → ↥L.T ⧸ I) :=
  LinearMap.range (LinearMap.pi fun g => actQ L I hI g - LinearMap.id)

abbrev QuotientCohomology [TopologicalSpace G] (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T)
    (hI : StableSub L I) : Type :=
  ↥(quotientCocycles L I hI) ⧸ (BQ L I hI).comap (quotientCocycles L I hI).subtype

variable [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def evT (L : Lattice (O := O) ρ) (g : G) : ↥(latticeCocycles L) →ₗ[O] ↥L.T where
  toFun c := ⟨(c : G → V) g, c.2.2 g (Set.mem_univ g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def redT (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) : ↥(latticeCocycles L) →ₗ[O] (G → ↥L.T ⧸ I) :=
  LinearMap.pi fun g => I.mkQ ∘ₗ evT L g

def HfQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (G → ↥L.T ⧸ I) :=
  ((latticeFiniteCocycles PD L).comap (latticeCocycles L).subtype).map (redT L I) ⊔ BQ L I hI

def quotientFiniteCohomology (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (hI : StableSub L I) :
    Submodule O (QuotientCohomology L I hI) :=
  ((HfQ PD L I hI).comap (quotientCocycles L I hI).subtype).map (Submodule.mkQ _)

end Tor

section TorMore

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} [TopologicalSpace G]

def actD (L : Lattice (O := O) ρ) (g : G) : (V ⧸ L.T) →ₗ[O] (V ⧸ L.T) :=
  L.T.mapQ L.T ((ρ g).restrictScalars O) (fun x hx => L.stable g x hx)

def divisibleCocycles (L : Lattice (O := O) ρ) : Submodule O (G → V ⧸ L.T) where
  carrier := {c | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + actD L g (c h)}
  zero_mem' := ⟨IsLocallyConstant.const 0, fun g h => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨ha.add hb, fun g h => ?_⟩
    simp only [Pi.add_apply, ha', hb', map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, ha'⟩
    refine ⟨ha.comp (c • ·), fun g h => ?_⟩
    simp only [Pi.smul_apply, ha', map_smul, smul_add]

def BD (L : Lattice (O := O) ρ) : Submodule O (G → V ⧸ L.T) :=
  LinearMap.range (LinearMap.pi fun g => actD L g - LinearMap.id)

abbrev DivisibleCohomology (L : Lattice (O := O) ρ) : Type := ↥(divisibleCocycles L) ⧸ (BD L).comap (divisibleCocycles L).subtype

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def HfD (L : Lattice (O := O) ρ) : Submodule O (G → V ⧸ L.T) :=
  ((finiteCocycles PD ρ).restrictScalars O).map (LinearMap.compLeft L.T.mkQ G) ⊔ BD L

def divisibleFiniteCohomology (L : Lattice (O := O) ρ) : Submodule O (DivisibleCohomology L) :=
  ((HfD PD L).comap (divisibleCocycles L).subtype).map (Submodule.mkQ _)

end TorMore

end Formalism.WeaklyAdmissibleFiltrations
end
end

