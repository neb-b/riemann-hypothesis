module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Formalism.CoboundaryTransfers.Statement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Series

variable {L M : Type} [Field L] [AddCommGroup M] [Module L M]

def IsLaurent (u : ℤ → M) : Prop := ∃ m : ℤ, ∀ k < m, u k = 0

def serMul (f : PowerSeries L) (u : ℤ → M) : ℤ → M :=
  fun k => ∑ᶠ j : ℕ, PowerSeries.coeff j f • u (k - (j : ℤ))


open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_finite (f : PowerSeries L) {u : ℤ → M}
    (hu : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.IsLaurent u) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • u (k - (j : ℤ))).Finite := by
  obtain ⟨m, hm⟩ := hu
  refine (Set.finite_Iic (k - m).toNat).subset ?_
  intro j hj
  rw [Function.mem_support] at hj
  rw [Set.mem_Iic]
  by_contra h
  push Not at h
  exact hj (by rw [hm _ (by omega), smul_zero])


open TensorProduct in
variable {L M : Type} [Field L] [AddCommGroup M] [Module L M] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one (u : ℤ → M) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul (1 : PowerSeries L) u = u := by
  funext k
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul
  rw [finsum_eq_single _ 0 (fun j hj => by simp [PowerSeries.coeff_one, hj])]
  simp

variable (L) in
def serSpan (S : Set (ℤ → M)) : Submodule L (ℤ → M) :=
  Submodule.span L {w | ∃ (f : PowerSeries L) (u : ℤ → M), u ∈ S ∧ IsLaurent u ∧ w = serMul f u}

def shiftSer (a : ℤ) (F : Submodule L M) : Submodule L (ℤ → M) where
  carrier := {u | (∀ k < -a, u k = 0) ∧ ∀ k, u k ∈ F}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => F.zero_mem⟩
  add_mem' := by
    rintro u w ⟨hu, hu'⟩ ⟨hw, hw'⟩
    exact ⟨fun k hk => by simp [hu k hk, hw k hk], fun k => F.add_mem (hu' k) (hw' k)⟩
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    exact ⟨fun k hk => by simp [hu k hk], fun k => F.smul_mem c (hu' k)⟩

def gradedSer (F : ℤ → Submodule L M) : Submodule L (ℤ → M) := ⨆ a : ℤ, shiftSer a (F a)

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def Dlet (i : ZMod n) : Submodule LL (T.V ⊗[Qp] B) := DcrisL PD T.ρ (W.emb i)

def FilLet (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ) : Submodule LL (T.V ⊗[Qp] B) :=
  Dlet W T i ⊓
    (FildR PD T.ρ τ a ⊔ ⨆ (τ' : K →ₐ[Qp] LL) (_ : τ' ≠ τ), DdRE PD T.ρ τ').comap
      (ιV PD (LL := LL) (V := T.V))

def toDR (F : Submodule LL (T.V ⊗[Qp] B)) : Submodule LL (T.V ⊗[Qp] BdR) :=
  F.map (ιV PD (LL := LL) (V := T.V))

def Nlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL (Set.range (W.levN T i ζ))

def IsExpansion (i : ZMod n) (ζ : LL) (y : W.DD T) (u : ℤ → T.V ⊗[Qp] BdR) : Prop :=
  IsLaurent u ∧ ∃ (m : ℕ) (hy : W.Q ^ m • y ∈ W.N T),
    serMul (W.lev i ζ (W.Q ^ m)) u = W.levN T i ζ ⟨W.Q ^ m • y, hy⟩

def phiNlev (i : ZMod n) (ζ : LL) : Submodule LL (ℤ → T.V ⊗[Qp] BdR) :=
  serSpan LL {u | ∃ y ∈ W.N T, IsExpansion W T i ζ (W.φD T y) u}

variable (PD) in
def phiSer (j : ℕ) (u : ℤ → T.V ⊗[Qp] B) : ℤ → T.V ⊗[Qp] BdR :=
  fun k => ιV PD (LL := LL) (V := T.V)
    ((((PD.p : LL) ^ j) ^ k) • ((φVB PD (LL := LL) (V := T.V)) ^ j) (u k))


open TensorProduct in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.levN_mem_Nlev (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) :
    W.levN T i ζ x ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.Nlev W T i ζ := by
  refine Submodule.subset_span ⟨1, W.levN T i ζ x, ⟨x, rfl⟩, ?_,
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.serMul_one _).symm⟩
  obtain ⟨m, hm⟩ := W.levN_supp T i ζ x
  exact ⟨m, hm⟩

end Generic

section Statement

variable {l : ℕ} [Fact l.Prime]

def resEmb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1) : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 :=
  τ.comp (IntermediateField.inclusion h.2.2.1)

def LatticeAtLevels (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (H : LocHW l P) (F : LocFon l P AI H) (C : LocCmpT l P AI H F) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      (∀ j : ℕ, j < s → IsPrimitiveRoot ζ (l ^ j) →
        Nlev (H.W K s LL h) T i ζ =
          shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i))) ∧
      (∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ →
        phiNlev (H.W K s LL h) T i ζ =
            shiftSer 0 (toDR (PD := P.PD K) T (Dlet (H.W K s LL h) T i)) ∧
          Nlev (H.W K s LL h) T i ζ =
            gradedSer fun a =>
              toDR (PD := P.PD K) T (FilLet (H.W K s LL h) T i (resEmb h τ) a)) ∧
      (∀ j : ℕ, 1 ≤ j → IsPrimitiveRoot ζ (l ^ (s + j)) →
        Nlev (H.W K s LL h) T i ζ =
            serSpan ↥LL.1 (phiSer (P.PD K) T j ''
              (serSpan ↥LL.1 (Set.range
                ((C.C K s LL h).tie.levB T (i - (j : ZMod _)) (ζ ^ (l ^ j)))) :
                  Set (ℤ → T.V ⊗[ℚ_[l]] P.R.B))) ∧
          ∀ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h (i - (j : ZMod _)) (ζ ^ (l ^ j)) τ →
            Nlev (H.W K s LL h) T i ζ =
              gradedSer fun a =>
                toDR (PD := P.PD K) T
                  ((FilLet (H.W K s LL h) T (i - (j : ZMod _)) (resEmb h τ) a).map
                    ((φVB (P.PD K) (LL := ↥LL.1) (V := T.V)) ^ j)))

end Statement

end GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

abbrev rk : ℕ := finrank O ↥T.L.T

abbrev letterModule (i : ZMod n) : Module (PowerSeries O) ↥(W.Nl T i) :=
  Module.compHom _ (Pi.constRingHom (ZMod n) (PowerSeries O))

attribute [local instance] letterModule


open Module in
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : _root_.Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : _root_.Formalism.BasicNotions.LocWach PD LL O v n) (T : _root_.Formalism.BasicNotions.LocLat G Qp LL O) in
attribute [local instance] _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul (i : ZMod n) (c : PowerSeries O)
    (x : ↥(W.Nl T i)) :
    ((c • x : ↥(W.Nl T i)) : W.DD T) = (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • (x : W.DD T) := by
  obtain ⟨x, hx⟩ := x
  have hx' : x ∈ Submodule.map (_root_.Formalism.BasicNotions.letE i • LinearMap.id) (W.N T) := hx
  obtain ⟨y, -, rfl⟩ := Submodule.mem_map.mp hx'
  change (Pi.constRingHom (ZMod n) (PowerSeries O) c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y) =
    (Pi.single i c : _root_.Formalism.BasicNotions.LetA O n) • ((_root_.Formalism.BasicNotions.letE i : _root_.Formalism.BasicNotions.LetA O n) • y)
  rw [smul_smul, smul_smul]
  congr 1
  unfold _root_.Formalism.BasicNotions.letE
  ext j : 1
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_apply, h]

abbrev LetterBasis (i : ZMod n) : Type := Basis (Fin (rk T)) (PowerSeries O) ↥(W.Nl T i)

def LettersDecompose : Prop := iSupIndep (W.Nl T) ∧ ⨆ i, W.Nl T i = W.N T

def LettersFree : Prop := ∀ i : ZMod n, Nonempty (LetterBasis W T i)

def GlobalBasis : Prop :=
  ∃ b : Basis (Fin (rk T)) (LetA O n) ↥(W.N T),
    LinearIndependent W.EE (fun j => (b j : W.DD T)) ∧
      Submodule.span W.EE (Set.range fun j => (b j : W.DD T)) = ⊤

variable {W T}

variable (W T)

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorLatticeUnitPart
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Bilinear

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

end Bilinear

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (i.f.coprod i'.f) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

variable (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnitDualParts
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (fun p : T.V × T'.V => i.f p.1 + i'.f p.2) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

def SumFor (W : LocWach PD LL O v n) : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    ∀ (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L), IsSumLat i i' →
      ∃ σ : (W.DD T × W.DD T') ≃ₗ[W.EE] W.DD T'',
        (∀ x y, σ (x, y) = W.map i x + W.map i' y) ∧
        (∀ x y, W.φD T'' (σ (x, y)) = σ (W.φD T x, W.φD T' y)) ∧
        (∀ (g : W.Gam) x y, W.γD T'' g (σ (x, y)) = σ (W.γD T g x, W.γD T' g y)) ∧
        ∀ x y, σ (x, y) ∈ W.N T'' ↔ (x ∈ W.N T ∧ y ∈ W.N T')

variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

def UnitFor (E : EtTie W RA RW inclR φR gR πA) : Prop :=
  ∀ e₀ : ↥W.one.L.T, Submodule.span O {e₀} = ⊤ →
    ∃ e : W.DD W.one,
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      Function.Bijective (fun c : W.EE => c • e) ∧
      W.φD W.one e = e ∧
      (∀ g : W.Gam, W.γD W.one g e = e) ∧
      W.N W.one = Submodule.span (LetA O n) {e}

end Generic

def UnitPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
    (F : LocFon l P AI H) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), UnitFor (F.E K s LL h).tie

def SumPart (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), SumFor (H.W K s LL h)

end GlobalTheory.IndefiniteRowSideFullHecke.UnitDualParts
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachCrystallineComparison
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def CmpIso (W : LocWach PD LL O v n) (l : ℕ) (T : LocLat G Qp LL O) : Prop :=
  (∀ x : ↥(W.N T), W.cmp T x = 0 ↔ ∃ y : ↥(W.N T), x = (letπ : LetA O n) • y) ∧
  Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T x) = Dcris PD T.ρ ∧
  (∀ i : ZMod n, Submodule.span LL (Set.range fun x : ↥(W.N T) => W.cmp T ((letE i : LetA O n) • x))
      = DcrisL PD T.ρ (W.emb i)) ∧
  (∀ (x : ↥(W.N T)) (m : ℕ) (hx : W.Q ^ m • W.φD T (x : W.DD T) ∈ W.N T),
    W.cmp T ⟨W.Q ^ m • W.φD T (x : W.DD T), hx⟩ =
      (l : LL) ^ m • φVB PD (LL := LL) (V := T.V) (W.cmp T x))

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.WachCrystallineComparison
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachLettersFree
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def IsLetterBasis (i : ZMod n) {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  (∀ k, b k ∈ W.Nl T i) ∧
    ∀ x ∈ W.Nl T i, ∃! c : Fin r → PowerSeries O,
      x = ∑ k, (Pi.single i (c k) : LetA O n) • b k

end Generic

end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
end
end

