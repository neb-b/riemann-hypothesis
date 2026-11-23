module

public import Formalism.SharpRestriction.ParConsts
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
public import Formalism.SharpRestriction.LevelLetterCocycles.BoundedNumeratorPowerSummability

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AlignN
section
noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def tameList {g m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Option (Fin m × Bool) → (ZMod g)ˣ
  | none => 1
  | some (j, true) => χ j
  | some (j, false) => (χ j)⁻¹

def TameDistinct (r g : ℕ) [Fact g.Prime] {m : ℕ} (χ : Fin m → (ZMod g)ˣ) : Prop :=
  Function.Injective (tameList χ) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ Formalism.CyclotomicNorms.BB r g →
    Function.Injective (fun o => Formalism.CyclotomicNorms.primeToPart ℓ
      (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) ((tameList χ o : (ZMod g)ˣ) : ZMod g)))) ∧
  ∀ j, IsSquare (χ j)

def TameDistinctF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (k : Fin 2) (v : (Fm.D x i).nd.PlG k),
    haveI : Fact ((Fm.D x i).host.g k).Prime := ⟨(Fm.D x i).host.g_prime k⟩
    TameDistinct (Fm.D x i).R.r ((Fm.D x i).host.g k) ((Fm.D x i).nd.chiT k v)

end Formalism.MainNotions
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.CardBasisEq
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem finrank_lat [IsDomain O] [IsFractionRing O LL] (T : LocLat G Qp LL O) :
    finrank O ↥T.L.T = finrank LL T.V := by
  have := T.L.free
  have hfg : Module.Finite O ↥T.L.T := ⟨(Submodule.fg_top _).mpr T.L.fg⟩
  let e := Module.Free.chooseBasis O ↥T.L.T
  let w : Module.Free.ChooseBasisIndex O ↥T.L.T → T.V := fun j => (e j : T.V)
  have hli : LinearIndependent O w := e.linearIndependent.map' T.L.T.subtype (Submodule.ker_subtype _)
  have hli' : LinearIndependent LL w := (LinearIndependent.iff_fractionRing O LL).mp hli
  have hspO : Submodule.span O (Set.range w) = T.L.T := by
    have : Set.range w = T.L.T.subtype '' Set.range e := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, e.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hsp : ⊤ ≤ Submodule.span LL (Set.range w) := by
    rw [← T.L.span, Submodule.span_le]
    intro x hx
    rw [← hspO] at hx
    exact Submodule.span_le_restrictScalars O LL _ hx
  rw [Module.finrank_eq_card_basis (Module.Basis.mk hli' hsp), Module.finrank_eq_card_chooseBasisIndex]

theorem card_basis_eq [Nontrivial O] [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) {r : ℕ} (b : Fin r → W.DD T) (hb : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j) :
    r = finrank O ↥T.L.T := by
  classical
  let w : Fin r → ↥(W.N T) := fun j => ⟨b j, hb j⟩
  have hli : LinearIndependent (LetA O n) w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : (0 : W.DD T) = ∑ j, g j • b j := by
      have := congrArg Subtype.val hg
      simpa [w, Submodule.coe_sum] using this.symm
    have h1 : (0 : W.DD T) = ∑ j, (0 : Fin r → LetA O n) j • b j := by simp
    obtain ⟨a, _, ha⟩ := huniq 0 (W.N T).zero_mem
    have e1 := ha g h0
    have e2 := ha 0 h1
    intro j
    rw [e1, ← e2]; rfl
  have hsp : ⊤ ≤ Submodule.span (LetA O n) (Set.range w) := by
    rintro ⟨x, hx⟩ -
    obtain ⟨a, ha, -⟩ := huniq x hx
    have : (⟨x, hx⟩ : ↥(W.N T)) = ∑ j, a j • w j := by
      apply Subtype.ext
      simp [w, Submodule.coe_sum, ha]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  let bN := Module.Basis.mk hli hsp
  let bD := (W.N_base T hT).basis bN
  have : Nontrivial W.EE := W.EE_inj.nontrivial
  have h1 := Module.finrank_eq_card_basis bD
  rw [(W.DD_free T).2, Fintype.card_fin] at h1
  exact h1.symm

end

end Formalism.MainNotions.RamifiedCoefficientChains.S9.RankN
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase)
open Formalism.MainNotions.LiftingTheory (qp pk Over CaseA JumpsLet)
open Formalism.MainNotions.WachCoordinates (FilLev)
open Formalism.MainNotions.DeltaInvariantLattices (ιDi)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def conv {M : Type} [AddCommGroup M] [Module LL M] (f : PowerSeries LL) (d : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • d (k - j)

def IsExp (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (x : W.DD T)
    (d : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  (∃ m : ℤ, ∀ k < m, d k = 0) ∧ ∃ (a : LetA O n) (ha : a • x ∈ W.N T), W.lev i ζ a ≠ 0 ∧
    ∀ k : ℤ, W.levN T i ζ ⟨a • x, ha⟩ k = conv (W.lev i ζ a) d k

def ExpRing (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∃ u : PowerSeries LL, IsUnit u ∧ W.lev i ζ (qp W) = u * PowerSeries.X) ∧
    PowerSeries.constantCoeff (W.lev i ζ W.π₀) = -(PD.p : LL) ∧ IsUnit (W.lev i ζ (pk W 1))

def ExpRules (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    (∀ (x : W.DD T) (a : LetA O n), a • x ∈ W.N T → W.lev i ζ a ≠ 0 → ∃! d, IsExp W T i ζ x d) ∧
    (∀ x d, DL W T i x → IsExp W T i ζ x d → ∀ k, d k ∈ ιDi W T i) ∧
    (∀ x y d e, IsExp W T i ζ x d → IsExp W T i ζ y e → IsExp W T i ζ (x + y) (d + e)) ∧
    (∀ (c : O) x d, IsExp W T i ζ x d → IsExp W T i ζ (c • x) (fun k => algebraMap O LL c • d k)) ∧
    (∀ (a : LetA O n) x d, IsExp W T i ζ x d → IsExp W T i ζ (a • x) (conv (W.lev i ζ a) d)) ∧
    (∀ x d, IsExp W T i ζ x d →
      IsExp W T i ζ (W.γ T x) (fun k => (algebraMap O LL (W.χΓ W.gam : O)) ^ k • d k)) ∧
    ∀ (T' : LocLat G Qp LL O) (F : LatHom T.L T'.L), IsCrys PD T'.ρ → ∀ x d, IsExp W T i ζ x d →
      IsExp W T' i ζ (W.map F x)
        (fun k => AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR) (d k))

def ExpCrit (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      ((∃ k : ℕ, qp W ^ k • x ∈ W.N T) → (x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k))) ∧
      ((∃ k : ℕ, qp W ^ k • x ∈ pullJ W T (i - 1) 1) → (x ∈ pullJ W T (i - 1) 1 ↔ ∀ k < 0, d k = 0))

def LemK (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (ζ : LL), IsPrimitiveRoot ζ PD.p →
    ∀ (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR), DL W T i x → IsExp W T i ζ x d →
      (∃ j : ℕ, ((PD.p : ℕ) : O) ^ j • (W.γ T x - x) ∈ W.N T) →
      (∀ k, k ≠ 0 → d k ∈ FilLev W T i 0 (-k)) ∧
      ∀ y : ℕ, qp W ^ y • x ∈ W.N T →
        d 0 ∈ FilLev W T i 0 (-(y : ℤ)) ∧ (x ∈ W.N T ↔ d 0 ∈ FilLev W T i 0 0)

def FilDim (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i →
    finrank LL ↥(ιDi W T i) = finrank LL T.V ∧
    ∀ a b : ℤ, a ≤ b → (finrank LL ↥(FilLev W T i 0 a) : ℤ) - finrank LL ↥(FilLev W T i 0 b) =
      ∑ u ∈ Finset.Ico a b, multV PD T.ρ τ u

def at0 (W : LocWach PD LL O v n) (f : PowerSeries O) : LetA O n := fun _ => PowerSeries.subst W.π₀₁ f

def IsBas (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {r : ℕ} (e : Fin r → W.DD T) : Prop :=
  (∀ k, e k ∈ W.N T ∧ DL W T i (e k)) ∧
    ∀ x ∈ W.N T, DL W T i x → ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • e k

def BasTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ i : ZMod n,
    (∃ e : Fin (finrank LL T.V) → W.DD T, IsBas W T i e) ∧
    ∀ (r : ℕ) (e : Fin r → W.DD T), IsBas W T i e → ∀ j : ℕ,
      (∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
        ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k)) ∧
      ∀ (x : W.DD T) (s : ℕ), ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T i j → x ∈ pullJ W T i j

def DetTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ → JumpsLet W T Mi hi →
    ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Over W τ i → ∀ (r : ℕ) (e e' : Fin r → W.DD T),
      IsBas W T i e → IsBas W T (i - 1) e' → ∀ (M : ℕ) (P : Matrix (Fin r) (Fin r) (PowerSeries O)),
        (∀ k, qp W ^ M • W.φD T (e' k) = ∑ m, at0 W (P m k) • e m) →
        ∃ (u : PowerSeries O) (w : ℕ), IsUnit u ∧
          P.det = u * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ w ∧
          (w : ℤ) = (M : ℤ) * r + ∑ a ∈ Finset.Icc (-(Mi i : ℤ)) (hi i : ℤ), a * multV PD T.ρ τ a

def ZTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  CaseA W → 11 ≤ PD.p → ∀ (j X σ : ℕ), TCase PD.p j 1 X σ →
    ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n) (r : ℕ) (e : Fin r → W.DD T) (he : IsBas W T i e),
      ∃ Z Z' R : Matrix (Fin r) (Fin r) (PowerSeries O),
        (∀ m k, PowerSeries.constantCoeff (Z m k) = if m = k then ((PD.p : ℕ) : O) ^ σ else 0) ∧
        Z * Z' = ((PD.p : ℕ) : PowerSeries O) ^ (2 * σ) • (1 : Matrix (Fin r) (Fin r) (PowerSeries O)) +
          (PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X) • R ∧
        ∀ k, (∃ p ∈ pullJ W T i j,
            W.γ T (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) - ∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m) =
              fMX W 1 X • p) ∧
          ∀ (ζ : LL), IsPrimitiveRoot ζ PD.p → ∀ d,
            IsExp W T (i + (j : ZMod n)) ζ (∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) d →
            ∀ s : ℤ, s < X → d s = if s = 0 then (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T.V)
              ((φVB PD (LL := LL) (V := T.V))^[j] (W.cmp T ⟨e k, (he.1 k).1⟩)) else 0

def ExtData (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ) (a N : ℕ) {FF : Type} [AddCommGroup FF]
    [Module O FF] (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T.L)) (y z : FF →ₗ[O] W.DD T) (μ ν : ZMod n → FF →ₗ[O] W.DD T) : Prop :=
  (∀ f, ∃ (x : ↥(W.wachCocyclesDelta T)) (hκ : (g f : G → T.V) ∈ latticeCocycles T.L), (x : W.DD T × W.DD T) = (y f, z f) ∧
    W.clK T x = Submodule.Quotient.mk (⟨(g f : G → T.V), hκ⟩ : ↥(latticeCocycles T.L))) ∧
  ∀ (i : ZMod n) (f : FF), DL W T i (μ i f) ∧ DL W T i (ν i f) ∧
    InPN W T 1 (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • z f) + (W.γ T (μ i f) - μ i f)) ∧
    qp W ^ Mi i • (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f) ∈ W.N T ∧
    (∃ s : ℕ, ((PD.p : ℕ) : O) ^ s • (qp W ^ hi i •
      (((PD.p : ℕ) : O) ^ N • ((letE i : LetA O n) • y f) + W.φD T (μ (i - 1) f) - μ i f)) ∈
        pullJ W T (i - 1) 1) ∧
    ((PD.p : ℕ) : O) ^ N • ν i f - qp W ^ a • μ i f ∈ W.N T

def ExtTool [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m →
    ∀ (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
      (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)),
      ∃ (N : ℕ) (y z : FF →ₗ[O] W.DD T₂) (μ ν : ZMod n → FF →ₗ[O] W.DD T₂),
        ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν

end Formalism.MainNotions.RamifiedCoefficientChains.Sh

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusIterateUniformizerUnitProducts
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section F2Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def unitQProds : Submonoid (LetA O n) where
  carrier := {f | ∃ (u : (LetA O n)ˣ) (J : Multiset ℕ), f = (u : LetA O n) * (J.map fun j => (W.φA ^ j) W.Q).prod}
  one_mem' := ⟨1, 0, by simp⟩
  mul_mem' := by
    rintro a b ⟨u, J, rfl⟩ ⟨u', J', rfl⟩
    refine ⟨u * u', J + J', ?_⟩
    rw [Multiset.map_add (f := _), Multiset.prod_add, Units.val_mul]
    ring

theorem ps_mem_unitQProds (hs : W.s = 1) (hq : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)))
    (s : ℕ) : (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨w, hw⟩ := hq
  have hQ : W.Q = W.q := by
    simp [LocWach.Q, hs]
  have e : W.π₀ + ((PD.p : ℕ) : LetA O n) = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.Q := by
    rw [hQ, hw, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨Units.map ((W.φA ^ s : LetA O n →ₐ[O] LetA O n) : LetA O n →* LetA O n) w⁻¹, {s}, ?_⟩
  rw [e, map_mul]
  simp

theorem pi0pow_mem_aN (T : LocLat G Qp LL O) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (hπ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)) (x : W.DD T) (hx : x ∈ W.N T) :
    W.π₀ ^ M • x ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
  obtain ⟨w, hw⟩ := hπ
  refine ⟨((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) • x, (W.N T).smul_mem _ hx, ?_⟩
  have e : W.π₀ ^ M = letπ * ((w : LetA O n) ^ M * letπ ^ ((PD.p - 1) * M - 1)) := by
    rw [hw, mul_pow, ← pow_mul]
    have : (PD.p - 1) * M = ((PD.p - 1) * M - 1) + 1 := by omega
    conv_lhs => rw [this]
    ring
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  rw [e]
  simp only [mul_smul]

theorem restriction_eq_restriction_H1 (H : Subgroup G) (T : LocLat G Qp LL O) (κ : LatticeCohomology T.L) :
    Formalism.MainNotions.DeltaInvariantLattices.res H T κ = resH1 T H κ := rfl

theorem wach_cocycle_class_mem_latticeFiniteCohomology (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr')
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (M : ℕ) (hM : 1 ≤ (PD.p - 1) * M)
    (x : ↥(W.wachCocyclesDelta T)) (hz : ∃ z' ∈ W.NΔ T, (x : W.DD T × W.DD T).2 = W.π₀ ^ M • z')
    (Λ : LetA O n) (hΛ : Λ ∈ unitQProds W) (hy : Λ • (x : W.DD T × W.DD T).1 ∈ W.N T) :
    W.clK T x ∈ latticeFiniteCohomology PD T.L := by
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  have hr := ((h9 T hT hs hp).2.2 hfr).1
  obtain ⟨_, _, hπ, _, hq, _⟩ := hr
  have hq' : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * (W.π₀ + ((PD.p : ℕ) : LetA O n)) := by
    obtain ⟨w, hw⟩ := hq
    refine ⟨w, ?_⟩
    rw [hw]
    congr 1
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]
  have hmem : (x : W.DD T × W.DD T) ∈ W.divisibleCocycles T := by
    have h1 := (Submodule.mem_inf.mp x.2).1
    rw [hg] at h1
    exact h1
  rw [h2b T hT, restriction_eq_restriction_H1, hres T x ⟨_, hmem⟩ rfl]
  obtain ⟨u, J, rfl⟩ := hΛ
  obtain ⟨z', hz', hzz⟩ := hz
  have hy' : (J.map fun j => (W.φA ^ j) W.Q).prod • (x : W.DD T × W.DD T).1 ∈ W.N T := by
    have := (W.N T).smul_mem ((u⁻¹ : (LetA O n)ˣ) : LetA O n) hy
    rwa [← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  have hzN : (x : W.DD T × W.DD T).2 ∈ Formalism.MainNotions.DeltaInvariantLattices.aN W T letπ := by
    rw [hzz]; exact pi0pow_mem_aN W T M hM hπ z' hz'.1
  have := h7 T hT J (x : W.DD T × W.DD T).1 (x : W.DD T × W.DD T).2 hy' hzN hmem
  exact this

theorem frobenius_iterate_uniformizer_unit_products (hs : W.s = 1) (hp : PD.p ≠ 2) (hfr : Module.finrank K₀ K = 1)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (s : ℕ) :
    (W.φA ^ s) (W.π₀ + ((PD.p : ℕ) : LetA O n)) ∈ unitQProds W := by
  obtain ⟨_, _, _, _, hq, _⟩ := ((h9 T hT hs hp).2.2 hfr).1
  refine ps_mem_unitQProds W hs ?_ s
  obtain ⟨w, hw⟩ := hq
  refine ⟨w, ?_⟩
  rw [hw]
  congr 1
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat]

end F2Core

section F2Rows

theorem caseA_of_le_Kur_of_ne_two {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l} (h : Good K 1 LL)
    (hK : K.1 ≤ MaximalUnramifiedExtension l) (hl : l ≠ 2) : Formalism.MainNotions.LiftingTheory.CaseA (H.W K 1 LL h) := by
  refine ⟨⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x, x.2, hK x.2⟩, rfl⟩⟩, H.W_s K 1 LL h, ?_⟩
  rw [P.PD_p]
  exact hl

theorem finrank_of_caseA {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) :
    Module.finrank K₀ K = 1 := by
  have e : K₀ ≃ₗ[K₀] K := LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1
  rw [← e.finrank_eq, Module.finrank_self]

end F2Rows

section F2At

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem wach_cohomology_class_unramified_functor (hC : Formalism.MainNotions.LiftingTheory.CaseA W) (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.WachCoordinates.F2 W := by
  intro hh M hM T hT _ c x hx hΛ
  have hfr := finrank_of_caseA W hC
  obtain ⟨Λ, ⟨k, m, rfl⟩, hΛy⟩ := hΛ
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b hres T hT M (by omega) x hx.2.2 _ ?_ hΛy.1
  exact Submonoid.prod_mem _ fun s _ => pow_mem (frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s) _

theorem wach_cohomology_class_at_functor (h7 : Formalism.MainNotions.DeltaInvariantLattices.WachCrystallineExtension W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W)
    (hres : W.gamK = W.gam → ∀ (T : LocLat G Qp LL O) (pr : ↥(W.wachCocyclesDelta T)) (pr' : ↥(W.divisibleCocycles T)),
      (pr' : W.DD T × W.DD T) = (pr : W.DD T × W.DD T) → resH1 T W.GKs (W.clK T pr) = W.cl T pr') :
    Formalism.MainNotions.ArcLiftingSetup.SecondWachFiltration W := by
  intro hC hh M hM T hT _ c y x Λ hΛ _ hΛy hcls
  have hfr := finrank_of_caseA W hC
  obtain ⟨z, hc, hz, rfl⟩ := hcls
  obtain ⟨y', hy', _, hyy⟩ := hΛy
  refine wach_cocycle_class_mem_latticeFiniteCohomology W hC.2.1 hC.2.2 hfr h7 h9 h2b (hres (W.gamK_eq_one hC.2.1 hC.2.2))
    T hT M (by omega) ⟨(y, z), hc⟩ hz Λ ?_ ?_
  · refine (Submonoid.closure_le.mpr ?_) hΛ
    rintro _ ⟨s, rfl⟩
    exact frobenius_iterate_uniformizer_unit_products W hC.2.1 hC.2.2 hfr h9 T hT s
  · show Λ • y ∈ W.N T
    rw [hyy, one_smul]
    exact hy'.1

end F2At

section F2Rows2

theorem wach_cohomology_class_unramified_case (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationEtale D HW F := fun l _ K LL hA _ =>
  wach_cohomology_class_unramified_functor ((HW l).W K 1 LL hA.2.2) (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    (h.1 l K 1 LL hA.2.2) (h.2.1 l K 1 LL hA.2.2) (h.2.2 l K 1 LL hA.2.2)
    (((F l).E K 1 LL hA.2.2).tie.clK_res
      (((HW l).W K 1 LL hA.2.2).gamK_eq_one (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.1
        (caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1).2.2))

theorem cohomology_class_unramified_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : FamilyMassExplicitOfVolumeAgreement D HW F :=
  fun h => wach_cohomology_class_unramified_case D HW F h.1

theorem second_filtration_case_a_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : SecondFiltrationHypotheses D HW F) :
    SecondFiltrationArcLifting D HW F := fun l _ K LL hG _ _ =>
  wach_cohomology_class_at_functor ((HW l).W K 1 LL hG) (h.1 l K 1 LL hG) (h.2.1 l K 1 LL hG) (h.2.2 l K 1 LL hG)
    ((F l).E K 1 LL hG).tie.clK_res

theorem second_filtration_theorem_arc_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : SecondFiltrationTheoremArcLifting D HW F :=
  fun h => second_filtration_case_a_of_hypotheses D HW F h.1

end F2Rows2

end Formalism.MainNotions.UnusedSlot80
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.KillerSecondTheoremHolds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem killer_first_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) {C : ℝ} (hC : 8 ≤ C) :
    KillerWithConstantTheorem D HW F C := by
  intro hA
  obtain ⟨hL, hP⟩ := hA
  exact Formalism.MainNotions.ArcLiftingSetup.pi_stability_content_clause D HW F hC hL (fun l _ K LL hG hc h5 =>
    hP l K LL hc h5 ((HW l).W K 1 LL hG).gam)

theorem killer_second_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : KillerWachCoordinatesTheorem D HW F := by
  intro hP
  exact Formalism.MainNotions.WachCoordinates.killer_conditions_of_stable D HW F hP

end Formalism.MainNotions.UnusedSlot80
end
end

