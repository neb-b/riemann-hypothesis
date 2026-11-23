module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleThreePrime
section
noncomputable section

namespace Formalism.MainNotions.AdmissibleThreePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def TheoremThreePrime (D : D7) : Prop := ArithmeticCylinders.TheoremThreePrime D

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def LabelDegreeHypotheses (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)),
    (∃ x, HasParamX D.nd D.naut i x Sig) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
        (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
          (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
        Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
              (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
            fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
        ∃ φ : G D.host.E D.nd.Om,
          redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k) ∧
      (∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
          (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
          (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
            (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
          Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
            ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
                (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
              fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
          D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
            ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂)

end Formalism.MainNotions.AdmissibleThreePrime
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.JInvJumpGen
section
noncomputable section

namespace Formalism.MainNotions.N.JsetEmb

open Formalism.WeaklyAdmissibleFiltrations Module Polynomial TensorProduct

section Inv

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem inv_one_mem_all (h1 : (1 : BdR) ∈ PD.Fil 1) : ∀ a : ℤ, (1 : BdR) ∈ PD.Fil a := by
  have hpos : ∀ n : ℕ, (1 : BdR) ∈ PD.Fil ((n : ℤ) + 1) := by
    intro n
    induction n with
    | zero => simpa using h1
    | succ n ih =>
      have := PD.Fil_mul 1 ((n : ℤ) + 1) 1 1 h1 ih
      rw [one_mul] at this
      convert this using 2
      push_cast; ring
  have hle : ∀ (a : ℤ) (n : ℕ), PD.Fil (a + n) ≤ PD.Fil a := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      intro x hx
      apply ih
      have hx' : x ∈ PD.Fil (a + n + 1) := by
        have e : a + ((n + 1 : ℕ) : ℤ) = a + n + 1 := by push_cast; ring
        rwa [e] at hx
      exact PD.Fil_anti (a + n) hx'
  intro a
  rcases le_or_gt a 1 with h | h
  · have e : (1 : ℤ) = a + ((1 - a).toNat : ℕ) := by omega
    have := hle a (1 - a).toNat
    rw [← e] at this
    exact this h1
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, a = (n : ℤ) + 1 := ⟨(a - 1).toNat, by omega⟩
    rw [hn]; exact hpos n

theorem field_inter_filtration_one_eq_zero (c : K) (hc : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hne
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ hc
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hne, map_one] at this
  have hall := inv_one_mem_all PD h1
  have h0 : (1 : BdR) = 0 := PD.Fil_sep 1 hall
  apply PD.not_mem_filtration_two
  have : PD.ι PD.t = 0 := by
    rw [← one_mul (PD.ι PD.t), h0, zero_mul]
  rw [this]
  exact (PD.Fil 2).zero_mem

end Inv

end Formalism.MainNotions.N.JsetEmb

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
section
noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def DeltaInvariantNormBound (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  WachLatticeFreeGlobal D HW F ∧ P2 D HW F ∧ P3 D HW F C ∧ P4 D HW F C ∧ P5 D HW F ∧ P6 D HW F ∧ P7 D HW F ∧
    P8 D HW F ∧ P9 D HW F ∧ WachCharacterisation D HW F ∧ gammaSemisimpleQuotientGlobal D HW F ∧ Pr2a D HW F ∧ Pr2b D HW F ∧ Pr2c D HW F ∧
    Pr2d D HW F ∧ lem3 D HW F ∧ ConclusionE D HW F

def DeltaInvariantLatticeCriterion {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop :=
  WachLatticeFree W ∧ P2W W ∧ P3W W ∧ P4W W Pt ∧ P5W W ∧ WachSaturationExactness W ∧ WachCrystallineExtension W ∧ WachMaxJumpBound W ∧ P9W W ∧ WachCharacterisationLattice W

def deltaInvariantLatticeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    DeltaInvariantLatticeCriterion ((HW l).W K s LL h) (ptK LT HW h)

def deltaInvariantLatticeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  deltaInvariantLatticeLocal D.loc HW D.locA F C

def UsedLocalConclusion (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  deltaInvariantLatticeGlobal D HW F C ∧ gammaSemisimpleQuotientGlobal D HW F ∧ prop2 D HW F ∧ lem3 D HW F

section Guard

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def ClKNatG (W : LocWach PD LL O v n) : Prop := (PD.p = 2 → ∃ i : K, i ^ 2 = -1) → W.ClKNat

end Guard

end Formalism.MainNotions.DeltaInvariantLattices
end
end

