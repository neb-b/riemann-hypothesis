module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0014
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InvariantsIsoOfGenerators
section
noncomputable section

namespace Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.tableLineDegreeTwo Formalism.MainNotions.LocalSituation TensorProduct

section Gen

variable (S : Sit)

def oneT (T : LocLat S.G S.Qp S.LL S.O) : ↥T.L.T →ₗ[S.O] TW S.RW T :=
  TensorProduct.mk S.O S.RW ↥T.L.T 1

def OneInj : Prop := ∀ T : LocLat S.G S.Qp S.LL S.O, Function.Injective (oneT S T)

def GenFix : Prop :=
  ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T),
    (∀ g, S.W.resΓ g = S.W.gamK → T.actT g t = t) →
    (∀ g, S.W.resΓ g ∈ S.W.DelF → T.actT g t = t) →
    (∀ g, S.W.resΓ g = 1 → T.actT g t = t) → ∀ g, T.actT g t = t

variable {S}

theorem oneT_apply (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T) : oneT S T t = (1 : S.RW) ⊗ₜ[S.O] t := rfl

theorem TWact_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (g : S.G) (t : ↥T.L.T) : TWact f T g ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] T.actT g t := by
  simp only [TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]

theorem TWmap_one {R : Type} [CommRing R] [Algebra S.O R] (f : R →ₐ[S.O] R) (T : LocLat S.G S.Qp S.LL S.O)
    (t : ↥T.L.T) : TWmap f T ((1 : R) ⊗ₜ[S.O] t) = (1 : R) ⊗ₜ[S.O] t := by
  simp only [TWmap, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one, LinearMap.id_apply]

theorem mem_H0Lat {T : LocLat S.G S.Qp S.LL S.O} (t : ↥T.L.T) : t ∈ invariantLattice T ↔ ∀ g, T.actT g t = t := by
  simp only [invariantLattice, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]
  first
  | rfl
  | exact Iff.rfl
  | (constructor <;> intro h g <;> exact h g)

theorem mem_fixDD {T : LocLat S.G S.Qp S.LL S.O} (x : S.W.DD T) : x ∈ fixDD S.W T ↔
    S.W.φD T x = x ∧ S.W.γD T S.W.gamK x = x ∧ ∀ δ ∈ S.W.DelF, S.W.γD T δ x = x := by
  simp only [fixDD, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, and_assoc]

private theorem nonempty_invariantLattice_equiv_fixDD (E : S.Comparison₂)
    (hin : ∀ (T : LocLat S.G S.Qp S.LL S.O) (t : ↥T.L.T), (∀ g, T.actT g t = t) →
      (1 : S.RW) ⊗ₜ[S.O] t ∈ Set.range (E.jD T))
    (hfix : ∀ (T : LocLat S.G S.Qp S.LL S.O) (b : TW S.RW T), TWmap S.φR T b = b →
      ∃ t : ↥T.L.T, b = (1 : S.RW) ⊗ₜ[S.O] t)
    (hi : OneInj S) (hg : GenFix S) (T : LocLat S.G S.Qp S.LL S.O) :
    Nonempty (↥(invariantLattice T) ≃ₗ[S.O] ↥(fixDD S.W T)) := by

  have key : (invariantLattice T).map (oneT S T) = (fixDD S.W T).map (E.jD T) := by
    ext b
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_H0Lat] at ht
      obtain ⟨d, hd⟩ := hin T t ht
      refine ⟨d, ?_, ?_⟩
      · rw [mem_fixDD]
        refine ⟨?_, ?_, ?_⟩
        · apply E.jD_inj T
          rw [E.jD_φ, hd, TWmap_one]
        · obtain ⟨g, hgg⟩ := S.W.resΓ_onto S.W.gamK
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
        · intro δ _
          obtain ⟨g, hgg⟩ := S.W.resΓ_onto δ
          apply E.jD_inj T
          rw [← hgg, E.jD_act, hd, TWact_one, ht g]
      · rw [oneT_apply, hd]
    · rintro ⟨d, hd, rfl⟩
      rw [mem_fixDD] at hd
      obtain ⟨hφ, hγ, hδ⟩ := hd
      obtain ⟨t, ht⟩ := hfix T (E.jD T d) (by rw [← E.jD_φ, hφ])
      have hact : ∀ g : S.G, S.W.γD T (S.W.resΓ g) d = d → T.actT g t = t := by
        intro g hgd
        apply hi T
        rw [oneT_apply, oneT_apply, ← TWact_one (S.gR g), ← ht, ← E.jD_act, hgd]
      refine ⟨t, ?_, ?_⟩
      · rw [mem_H0Lat]
        apply hg T t
        · intro g hgK
          exact hact g (by rw [hgK, hγ])
        · intro g hgD
          exact hact g (hδ _ hgD)
        · intro g h1
          exact hact g (by rw [h1, S.W.γD_one])
      · rw [oneT_apply, ht]
  exact ⟨(Submodule.equivMapOfInjective (oneT S T) (hi T) (invariantLattice T)).trans
    ((LinearEquiv.ofEq _ _ key).trans
      (Submodule.equivMapOfInjective (E.jD T) (E.jD_inj T) (fixDD S.W T)).symm)⟩

end Gen

theorem invariants_iso_of_generators (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (hi : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      OneInj (sit D.loc HW l (D.locA l) K 1 LL hA.2.2))
    (hg : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL),
      GenFix (sit D.loc HW l (D.locA l) K 1 LL hA.2.2)) :
    H0InvariantsTheorem D HW F := by
  intro hF l hl K LL hA T
  obtain ⟨hW, hD⟩ := hF l K 1 LL hA.2.2
  refine nonempty_invariantLattice_equiv_fixDD (S := sit D.loc HW l (D.locA l) K 1 LL hA.2.2) ((F l).E K 1 LL hA.2.2).tie
    (fun T t ht => ?_) (fun T b hb => (hW T).2.1 b hb) (hi l K LL hA) (hg l K LL hA) T

  refine Set.mem_range.mpr (LinearMap.mem_range.mp ((hD T).2 _ ?_ ?_))
  · intro g _
    rw [TWact_one, ht g]
  · rw [TWmap_one, sub_self]
    exact Submodule.zero_mem _

end Formalism.MainNotions.InvariantsGenerators.InvariantsFromGenerators
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LamPS
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def letS (c : ZMod n) : Submodule O (W.DD T) :=
  LinearMap.ker ((((letE c : LetA O n) • LinearMap.id - LinearMap.id :
    W.DD T →ₗ[LetA O n] W.DD T)).restrictScalars O)

def DelS : Submodule O (W.DD T) :=
  ⨅ δ ∈ W.DelF, LinearMap.ker (W.γD T δ - LinearMap.id)

def NcS (c : ZMod n) : Submodule O (W.DD T) :=
  (W.N T).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def PcS (c : ZMod n) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).restrictScalars O ⊓ DelS W T ⊓ letS W T c

def LamPS (Eπ : LetA O n) (h' : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  ((Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (c - 1))).comap (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (Eπ ^ h'))).restrictScalars O ⊓
    DelS W T ⊓ letS W T c

def PiNS (π' : LetA O n) (k : ℕ) : Submodule O (W.DD T) :=
  (Formalism.MainNotions.DeltaInvariantLattices.aN W T (π' ^ k)).restrictScalars O ⊓ DelS W T

def InvS (π' Eπ : LetA O n) (h' k : ℕ) (c : ZMod n) : Submodule O (W.DD T) :=
  LamPS W T Eπ h' c ⊓ (PiNS W T π' k).comap (W.γD T W.gamK - LinearMap.id)

abbrev LcQ (π' : LetA O n) (c : ZMod n) : Type :=
  ↥(NcS W T (c - 1)) ⧸ (PiNS W T π' 1).comap (NcS W T (c - 1)).subtype

def JCl (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Set (G → T.V) :=
  {κ | ∃ hκ : κ ∈ latticeCocycles T.L, ∃ w ∈ InvS W T π' Eπ h' M c, ∃ z ∈ PiNS W T π' M,
    ∃ hwz : (w, z) ∈ W.wachCocyclesDelta T,
      Submodule.mkQ ((latticeCoboundaries T.L).comap (latticeCocycles T.L).subtype) (⟨κ, hκ⟩ : ↥(latticeCocycles T.L)) = W.clK T ⟨(w, z), hwz⟩}

def JZ (π' Eπ : LetA O n) (h' M : ℕ) (c : ZMod n) : Submodule O (G → T.V) :=
  Submodule.span O (JCl W T π' Eπ h' M c)

end Local

section Record

variable {l : ℕ} [Fact l.Prime]

abbrev eK (K : FinExt l) : ℕ := finrank ↥(K0 K) ↥K.1

abbrev sK (l : ℕ) [Fact l.Prime] (K : FinExt l) : ℕ := (l - 1) / eK K

abbrev MK (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' : ℕ) : ℕ := ⌈(4 * h' : ℝ) / (sK l K : ℝ)⌉₊

abbrev y2K (l : ℕ) [Fact l.Prime] (K : FinExt l) (h' S η : ℕ) : ℕ :=
  2 * sigA l (sK l K) h' + kapA l (eK K) h' S + rhoA l (eK K) h' + max (2 * sigA l (sK l K) h') (ycA l h' η)

def HypN (P : LocPrime l) (K LL : FinExt l) (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (F : LatHom T₁.L T₂.L) (S η m h' : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) : Prop :=
  IsCrys (P.PD K) T₁.ρ ∧ IsCrys (P.PD K) T₂.ρ ∧ F.Onto ∧
    (∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, JumpsInV (P.PD K) T₂.ρ τ (deep (up τ) (b τ) S ∪ Set.Icc (-(η : ℤ)) η)) ∧
    (∀ τ, η < b τ) ∧ (∀ τ, b τ + S ≤ h') ∧ 1 ≤ h' ∧
    (∀ τ, ∑ a ∈ Finset.Icc (-(η : ℤ)) η, multV (P.PD K) T₂.ρ τ a ≤ m) ∧
    (finrank ↥(K0 K) ↥K.1 = 2 ∨ ∀ τ τ', intersection_update_fsHerm_neg_one K τ = intersection_update_fsHerm_neg_one K τ' → up τ = up τ')

end Record

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LemmaGsOfLemGAB
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

section LemGCut

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lemG_sig (l H : ℕ) : ℕ := ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉₊

def LemGPair [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (x la : W.DD T) : Prop :=
  x ∈ W.N T ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T i x ∧
    Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∃ (x la : W.DD T₂) (hP : LemGPair W T₂ b S η i x la),
        W.cmp T₂ ⟨x, hP.1⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

def LemGB [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∃ E : ℕ, (E : ℝ) ≤ (3 * aR PD.p (hpar n b S + η) + S + 2 * η) / ((PD.p : ℝ) - 1) +
        lam PD.p (hpar n b S + η) ∧
      ∀ x la : W.DD T₂, LemGPair W T₂ b S η i x la →
        ∃ y ∈ W.N T₁, Formalism.MainNotions.CrystallineLiftingInputs.DL W T₁ i y ∧ W.map F y = ((PD.p : O) ^ E) • x

theorem lemG_ceil_eq (l H E h b : ℕ) :
    (⌈(E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ)⌉ : ℤ) =
      (E : ℤ) + ((lemG_sig l H : ℤ) + (h : ℤ) - (b : ℤ)) := by
  have hs : Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H = ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by
    simp only [Formalism.MainNotions.CrystallineLiftingInputs.sig2]
    push_cast
    ring
  have h0 : 0 ≤ ((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1 := by positivity
  have hc : ((lemG_sig l H : ℕ) : ℤ) = ⌈((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1⌉ := by
    unfold lemG_sig
    exact Int.natCast_ceil_eq_ceil h0
  rw [show (E : ℝ) + Formalism.MainNotions.CrystallineLiftingInputs.sig2 l H + ((h : ℕ) : ℝ) - (b : ℝ) =
      (((2 * H : ℕ) : ℝ) / ((l : ℝ) - 1) ^ 2 + 1) + (((E : ℤ) + h - b : ℤ) : ℝ) by
        rw [hs]; push_cast; ring,
    Int.ceil_add_intCast, ← hc]
  ring

theorem lemmaGs_of_lemGAB [NeZero n] (W : LocWach PD LL O v n) (hA : LemGA W) (hB : LemGB W) :
    LemmaGs W := by
  intro d T₁ T₂ F b S η m hset i hi
  obtain ⟨E, hEb, hEx⟩ := hB d T₁ T₂ F b S η m hset i hi
  refine ⟨E, hEb, ?_⟩
  rintro _ ⟨_, ⟨y, hy, hyD, rfl⟩, rfl⟩ hfil
  obtain ⟨x, la, hP, hcmp⟩ := hA d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨y1, hy1N, hy1D, hmap⟩ := hEx x la hP
  have hp0 : (PD.p : LL) ≠ 0 := by
    obtain ⟨ζ, hζ⟩ := hset.2.2.2.2.1
    haveI : NeZero PD.p := ⟨by have := hset.2.1; omega⟩
    exact hζ.neZero'.out
  have hnat : ((PD.p : ℕ) : O) ^ E • x = (PD.p ^ E : ℕ) • x := by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  have hx' : W.map F y1 ∈ W.N T₂ := by
    rw [hmap, hnat]
    exact nsmul_mem hP.1 _
  refine ⟨y1, hy1N, hx', hy1D, ?_⟩
  rw [lemG_ceil_eq, zpow_add₀ hp0, mul_smul, ← hcmp]
  have hsub : (⟨W.map F y1, hx'⟩ : W.N T₂) = (PD.p ^ E : ℕ) • (⟨x, hP.1⟩ : W.N T₂) :=
    Subtype.ext (by show W.map F y1 = (PD.p ^ E : ℕ) • x; rw [hmap, hnat])
  rw [hsub, map_nsmul, zpow_natCast, ← Nat.cast_smul_eq_nsmul LL, Nat.cast_pow]

def LemGLa [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (b : ZMod n → ℕ)
    (S η : ℕ) (i : ZMod n) (y la : W.DD T) : Prop :=
  Formalism.MainNotions.CrystallineLiftingInputs.IsTrunc W T (i - 2) 2 1 (2 * (hpar n b S + η)) (lemG_sig PD.p (hpar n b S + η)) y la ∧
    Formalism.MainNotions.CrystallineLiftingInputs.DL W T i la ∧
    Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T (i - 1) 1 ∧
    ∃ z ∈ W.N T, Formalism.MainNotions.CrystallineLiftingInputs.DL W T i z ∧
      Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • (W.γ T la - la) =
        (W.π₀ * Formalism.MainNotions.LiftingTheory.qp W ^ (⌈aR PD.p (hpar n b S + η)⌉₊ + b i)) • z

def LemGA_la [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ y : W.DD T₂, y ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∃ la : W.DD T₂, LemGLa W T₂ b S η i y la

def GammaActionLemma [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩)) ∈
        FilCris PD T₂.ρ (b i : ℤ) →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
        ∃ x : W.DD T₂, x ∈ W.N T₂ ∧ Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x ∧
          Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la

def LemGA_0 [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
    SetCS W d T₁ T₂ F b S η m → ∀ i : ZMod n, (i.val + d) % 2 = 1 →
    ∀ (y : W.DD T₂) (hy : y ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 2) y →
      ∀ la : W.DD T₂, LemGLa W T₂ b S η i y la →
      ∀ (x : W.DD T₂) (hx : x ∈ W.N T₂), Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x →
        Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ (b (i - 1) + S) • la →
        W.cmp T₂ ⟨x, hx⟩ =
          (PD.p : LL) ^ ((lemG_sig PD.p (hpar n b S + η) : ℤ) + ((b (i - 1) + S : ℕ) : ℤ) - (b i : ℤ)) •
            φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨y, hy⟩))

theorem lemGA_of_pieces [NeZero n] (W : LocWach PD LL O v n) (hla : LemGA_la W) (hx : GammaActionLemma W)
    (h0 : LemGA_0 W) : LemGA W := by
  intro d T₁ T₂ F b S η m hset i hi y hy hyD hfil
  obtain ⟨la, hla⟩ := hla d T₁ T₂ F b S η m hset i hi y hy hyD
  obtain ⟨x, hxN, hxD, hxeq⟩ := hx d T₁ T₂ F b S η m hset i hi y hy hyD hfil la hla
  exact ⟨x, la, ⟨hxN, hxD, hxeq, hla.2.2.2⟩,
    h0 d T₁ T₂ F b S η m hset i hi y hy hyD la hla x hxN hxD hxeq⟩

end LemGCut

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.LiftFOf
section
noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T₁ T₂ : LocLat G Qp LL O}

theorem lc_pow (I : BaseId W) (e : ℕ) :
    I.Bs.lc ^ e = PowerSeries.C (((PD.p : ℕ) : O) ^ e) := by
  unfold Formalism.ExponentWindows.E.Base.lc
  rw [I.ℓ_eq, map_pow]

theorem map_mem_Z1DΔ (F : LatHom T₁.L T₂.L) (w : ↥(W.wachCocyclesDelta T₁)) :
    (W.map F (w : W.DD T₁ × W.DD T₁).1, W.map F (w : W.DD T₁ × W.DD T₁).2) ∈ W.wachCocyclesDelta T₂ := by
  obtain ⟨⟨x, y⟩, hw⟩ := w
  show (W.map F x, W.map F y) ∈ W.wachCocyclesDelta T₂
  simp only [Formalism.BasicNotions.LocWach.wachCocyclesDelta, Formalism.BasicNotions.herrZ1Δ, Formalism.BasicNotions.herrCocycles, Submodule.mem_inf,
    LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.coprod_apply, LinearMap.sub_apply,
    LinearMap.neg_apply, LinearMap.id_apply, LinearMap.prodMap_apply] at hw ⊢
  obtain ⟨h1, h2⟩ := hw
  refine ⟨?_, fun d hd => ?_⟩
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, ← map_neg, ← map_add (f := _), h1, map_zero]
  · have h3 := h2 d hd
    rw [← W.map_γ, ← W.map_γ]
    simp only [Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero] at h3 ⊢
    exact ⟨by rw [h3.1], by rw [h3.2]⟩

end Formalism.MainNotions.WachCoordinates.Br
end
end

