module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0010
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalRingCardinality.Bundle0002
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot35.DssRec

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem rec_exists {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    (F : ℕ → M → M) (y₀ : M) : ∃ s : ℕ → M, s 0 = y₀ ∧ ∀ k, p • s (k + 1) = F k (s k) := by
  obtain ⟨u, hu⟩ := hp
  let s : ℕ → M := fun k => Nat.rec y₀ (fun k sk => ((u⁻¹ : Eˣ) : E) • F k sk) k
  refine ⟨s, rfl, fun k => ?_⟩
  show p • (((u⁻¹ : Eˣ) : E) • F k (s k)) = F k (s k)
  rw [← algebraMap_smul E p, ← hu, smul_smul, Units.mul_inv, one_smul]

theorem smul_inj {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    {a b : M} (h : p • a = p • b) : a = b := by
  obtain ⟨u, hu⟩ := hp
  have h' : (u : E) • a = (u : E) • b := by
    rw [hu, algebraMap_smul, algebraMap_smul]
    exact h
  have := congrArg (fun m => ((u⁻¹ : Eˣ) : E) • m) h'
  simpa [smul_smul] using this

theorem rec_unique {R E O M : Type} [CommRing R] [CommRing E] [CommRing O] [Algebra R E]
    [AddCommGroup M] [Module R M] [Module E M] [Module O M] [IsScalarTower R E M] (p : R)
    (hp : IsUnit (algebraMap R E p)) (c : ℕ → O) (Gm : M → M) (L : ℕ) (s s' : ℕ → M)
    (h0 : s 0 = s' 0)
    (hs : ∀ k, k < L → p • (s (k + 1) + c k • s k) = Gm (s k))
    (hs' : ∀ k, k < L → p • (s' (k + 1) + c k • s' k) = Gm (s' k)) :
    ∀ k, k ≤ L → s k = s' k := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have ih' := ih (by omega)
    have h1 := hs k (by omega)
    have h2 := hs' k (by omega)
    rw [← ih'] at h2
    have := smul_inj (E := E) p hp (h1.trans h2.symm)
    exact add_right_cancel this

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem π₀_unit (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨w, hw⟩ := ((h9 T hT hA.2.1 hA.2.2).2.2 hK).1.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

def DssMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (Y : ℕ) (y₀ : W.DD T), Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi)
            (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • seq k) = W.γD T W.gam (seq k) - seq k) →
        seq (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length ∈ W.N T

theorem coreDss_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.LiftingTheory.coreDss W ↔ DssMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ s hs0 hrec⟩

def DssLetMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (i : ZMod n) (y' Y : ℕ) (y₀ : W.DD T), y' ≤ Y → Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.Nl T i →
      (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • seq k) =
            W.γD T W.gam (seq k) - seq k) →
        Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length ∈ W.Nl T i

theorem dssLet_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.RamifiedCoefficientChains.DssLet W ↔ DssLetMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ s hs0 hrec⟩

end Core

end Formalism.MainNotions.UnusedSlot35.DssRec
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TwGood
section
noncomputable section

namespace Formalism.MainNotions.IntegralHeckeForms

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

variable {Y}

variable (Y)

variable {Y}

end Formalism.MainNotions.IntegralHeckeForms

namespace Formalism.MainNotions

open NumberField Formalism.BasicNotions

def TwistedAt (D : D7) (w : D.what₂.places.Pl) : Prop := D.what₂.muAt w ≠ D.what₂.mu0

theorem twistedAt_conj (D : D7) (w : D.what₂.places.Pl) : TwistedAt D (D.what₂.places.conj w) ↔ TwistedAt D w := by
  unfold TwistedAt
  rw [D.what₂.muAt_conj]

structure TwIn (D : D7) where
  E : IntegralHeckeForms.XD D
  N0 : D.ntw.Tw → ℕ
  S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)

def TwIn.Sg {D : D7} (I : TwIn D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Set (D.nexp.Dat i j b) :=
  IntegralHeckeForms.SgJ D.nexp I.E i j b

def TwIn.Ok {D : D7} (I : TwIn D) (i : D.ntw.Tw) : Prop :=
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.FullRk D.nexp I.E i j b (I.Sg i j b)) ∧
  (∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, IntegralHeckeForms.BasisOf D.nexp i j b (I.Sg i j b) (I.S i j b))

def twEps (D : D7) (i : D.ntw.Tw) : ℝ := ((D.ntw.l i : ℝ) ^ 2)⁻¹

theorem twEps_pos (D : D7) (i : D.ntw.Tw) : 0 < twEps D i := by
  unfold twEps
  have hl : (0 : ℝ) < (D.ntw.l i : ℝ) := by exact_mod_cast (D.ntw.lPrime i).out.pos
  positivity

def rPrAv (D : D7) : ℕ :=
  sInf {p : ℕ | p.Prime ∧
    ¬ p ∣ LevelStarExponents.condE D * (D.host.pde - 1) * (D.host.pde' - 1) * Ideal.absNorm D.host.ccK}

def q0Av (D : D7) : ℕ := sInf {p : ℕ | p.Prime ∧ p % (rPrAv D * LevelStarExponents.condE D) = 1 ∧ ¬ p ∣ Ideal.absNorm D.host.ccK}

def avPrimes (D : D7) : Finset ℕ :=
  letI := D.wordFin
  ((insert 3 (insert 5 (insert (D.host.g 0) (insert (D.host.g 1) (insert D.host.pde (insert D.host.pde'
    (insert (q0Av D) (Finset.univ.image fun u => (D.mem u).A.T)))))))) ∪
    (Ideal.absNorm D.host.ccK).primeFactors).filter (· ≠ 0)

def AvSet (D : D7) : Set (PlE D.host) := ⋃ p ∈ avPrimes D, placesOver D.host.E p

theorem placesOver_finite_av (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hI : (Ideal.span {((p : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem avSet_finite (D : D7) : (AvSet D).Finite := by
  unfold AvSet
  exact Set.Finite.biUnion (Finset.finite_toSet _) fun p hp =>
    placesOver_finite_av _ p (Finset.mem_filter.mp hp).2

def AvRec (D : D7) : Finset (PlE D.host) := (avSet_finite D).toFinset

theorem mem_avRec {D : D7} (v : PlE D.host) : v ∈ AvRec D ↔ ∃ p ∈ avPrimes D, v ∈ placesOver D.host.E p := by
  simp only [AvRec, AvSet, Set.Finite.mem_toFinset, Set.mem_iUnion, exists_prop]


open Classical in
def TwGoodOne (D : D7) (I : TwIn D) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : Prop :=
  IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) I.E I.N0 i (twEps D i) (I.S i) (AvRec D) Q k' (BlochKatoReduction.Gen.psiAt b ψ)

def TwGoodAt (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    I.Ok (C.twI w) ∧ TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

abbrev TwPack (D : D7) : Type :=
  Σ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (k' : ℕ), D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ

def twPack (D : D7) (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k' : ℕ)
    (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k')ˣ) : TwPack D :=
  ⟨i, Q, k', BlochKatoReduction.Gen.psiAt b ψ⟩

def NChoicePack {D : D7} (C : NChoice D) (w : D.what₂.places.Pl) : TwPack D :=
  twPack D (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w)

def TwConjAt (D : D7) (C : NChoice D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
    NChoicePack C (D.what₂.places.conj w) = NChoicePack C w ∧
      (D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w)

def TwGoodE {eps : ℝ} (Fm : FamP eps) (E : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, IntegralHeckeForms.XD (Fm.D x i)) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch ⟨E x hx i, N0, S⟩

def twEOf {D : D7} (T : ThData D) : IntegralHeckeForms.XD D := ⟨T.xd0, T.thetaBase_invariant_action⟩

def twE {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : IntegralHeckeForms.XD (Fm.D x i) := twEOf (Fm.ex x hx i).xd

def TwGood {eps : ℝ} (Fm : FamP eps) : Prop := TwGoodE Fm (twE Fm)

theorem psiAt_psiAt {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) :
    BlochKatoReduction.Gen.psiAt b (BlochKatoReduction.Gen.psiAt b ψ) = ψ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]


end Formalism.MainNotions

end
end

