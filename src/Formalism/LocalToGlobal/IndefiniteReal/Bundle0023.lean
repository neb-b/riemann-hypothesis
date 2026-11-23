module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0021
public import Formalism.LocalToGlobal.Columns.Bundle0002
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.RhoSpec
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0019
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Links

open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace RealDat

variable (R : RealDat D A Ks) (F : Face D A)

abbrev num (C CH : ℝ) : IndefNum A.fam.base := (F.fc (R.toCx F).zs).Z.num C CH

def LPos : Prop := ∀ b, (lv (F.fc (R.toCx F).zs) b).Pos

def LUnif : Prop :=
  ∀ i σ, (∀ (n : ℕ) (b : Fin n → (Fin (R.nW i) → D.what₂.LL)), LinearIndependent D.what₂.LL b →
      LinearIndependent ℂ fun k => (R.FW i).j σ (b k)) ∧
    Submodule.span ℂ (Set.range ((R.FW i).j σ)) = ⊤ ∧
    ∀ g x, (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ g x)) = σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) •
      postOn _ (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) ((R.HW i σ).e ((R.FW i).j σ x))

def LLevelW : Prop := ∀ b i σ, R.WS F b i σ = (R.Wat i σ (R.levL F b σ)).comap (R.HW i σ).e

def LIntegral : Prop := ∀ i, (R.FW i).IsKsForm ∧ (R.FW i).MKFull ∧ (R.FW i).MKStable

variable {R F}

end RealDat


namespace RealDat

variable {R : RealDat D A Ks} {F : Face D A}

theorem nP_pos (b : Bool) : 0 < nP F b := by
  unfold nP
  exact_mod_cast Nat.card_pos

theorem h0 (h : R.IsTup F) : (R.toCx F).H0 := by
  refine ⟨h.mu_conj, fun w => ⟨fun hw => h.mu_ne w hw, fun hne => ?_⟩⟩
  by_contra hw
  exact hne (h.mu_off w hw)

theorem ewNorm (b : Bool) : (R.toCx F).EWnorm b := by
  intro j x y
  show cj _ (inner ℂ ((((Real.sqrt (nP F b) : ℝ) : ℂ)) • ((Tw.out x : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))
      ((((Real.sqrt (nP F b) : ℝ) : ℂ)) • ((Tw.out y : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))) =
    ((nP F b : ℝ) : ℂ) * cj _ (inner ℂ ((Tw.out x : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H)
      ((Tw.out y : R.WS F b j (sg0 D A)) : (R.HW j (sg0 D A)).H))
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, ← mul_assoc, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (nP_pos b).le, map_mul, cj_ofReal]
  rfl

theorem kForm (hU : R.LUnif) (b : Bool) : (R.toCx F).KForm b := by
  intro j v
  have hc : (((Real.sqrt (nP F b))⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have := Real.sqrt_pos.2 (nP_pos (F := F) b)
    exact_mod_cast (inv_pos.2 this).ne'
  have hL : LinearIndependent D.what₂.LL (R.bL F b j) :=
    (Module.finBasis D.what₂.LL (R.WL F b j)).linearIndependent.map' (R.WL F b j).subtype (Submodule.ker_subtype _)
  have h1 : LinearIndependent ℂ (R.bC F b j (sgAt D.what₂.embLL v)) :=
    ((hU j _).1 _ _ hL).units_smul fun _ => Units.mk0 _ hc
  have h2 := linearIndependent_span h1
  have h3 : Submodule.span ℂ (Set.range fun k => (⟨R.bC F b j (sgAt D.what₂.embLL v) k, Submodule.subset_span ⟨k, rfl⟩⟩ :
      R.WS F b j (sgAt D.what₂.embLL v))) = ⊤ := Submodule.span_range_subtype_eq_top_iff _ _ |>.2 rfl
  exact ⟨Tw.linInd (E := R.WS F b j (sgAt D.what₂.embLL v)) _ h2, Tw.span_top (E := R.WS F b j (sgAt D.what₂.embLL v)) _ h3⟩

end RealDat

end Links

end Formalism.IndefR.Links

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
section
noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Conj

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

def conjSub (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ) where
  carrier := {f | (fun g => star (f g)) ∈ U}
  zero_mem' := by
    show (fun g => star ((0 : Formalism.AUTREP.GAf L n → ℂ) g)) ∈ U
    have : (fun g => star ((0 : Formalism.AUTREP.GAf L n → ℂ) g)) = 0 := by
      funext g
      simp
    rw [this]
    exact U.zero_mem
  add_mem' := by
    intro f f' hf hf'
    show (fun g => star ((f + f') g)) ∈ U
    have : (fun g => star ((f + f') g)) = (fun g => star (f g)) + (fun g => star (f' g)) := by
      funext g
      simp
    rw [this]
    exact U.add_mem hf hf'
  smul_mem' := by
    intro a f hf
    show (fun g => star ((a • f) g)) ∈ U
    have : (fun g => star ((a • f) g)) = star a • (fun g => star (f g)) := by
      funext g
      simp [mul_comm]
    rw [this]
    exact U.smul_mem _ hf

theorem mem_conjSub {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} {f : Formalism.AUTREP.GAf L n → ℂ} :
    f ∈ conjSub U ↔ (fun g => star (f g)) ∈ U := Iff.rfl

theorem conjSub_conjSub (U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) : conjSub (conjSub U) = U := by
  ext f
  have hf : (fun g => star (star (f g))) = f := by
    funext g
    simp
  show (fun g => star (star (f g))) ∈ U ↔ f ∈ U
  rw [hf]

theorem conjSub_mono {U U' : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (h : U ≤ U') : conjSub U ≤ conjSub U' :=
  fun _ hf => h hf

theorem conjSub_bot : conjSub (⊥ : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)) = ⊥ := by
  ext f
  rw [mem_conjSub, Submodule.mem_bot, Submodule.mem_bot]
  constructor
  · intro h
    funext g
    have := congrFun h g
    simpa using this
  · intro h
    subst h
    funext g
    simp

theorem conj_rt (h : Formalism.AUTREP.GAf L n) (f : Formalism.AUTREP.GAf L n → ℂ) :
    (fun g => star (Formalism.L2.NG.rt L n h f g)) = Formalism.L2.NG.rt L n h (fun g => star (f g)) := rfl

theorem conjSub_stable {U : Submodule ℂ (Formalism.AUTREP.GAf L n → ℂ)} (hU : ∀ h, ∀ f ∈ U, Formalism.L2.NG.rt L n h f ∈ U) :
    ∀ h, ∀ f ∈ conjSub U, Formalism.L2.NG.rt L n h f ∈ conjSub U := by
  intro h f hf
  rw [mem_conjSub] at hf ⊢
  rw [conj_rt]
  exact hU h _ hf

def FinTyp.conjT (π : Formalism.L2.NG.FinTyp L n) : Formalism.L2.NG.FinTyp L n where
  S := conjSub π.S
  stable := conjSub_stable π.stable
  smooth := by
    intro f hf
    obtain ⟨N, hN, hfix⟩ := π.smooth _ hf
    refine ⟨N, hN, fun κ hκ => ?_⟩
    funext g
    have := congrFun (hfix κ hκ) g
    rw [← conj_rt] at this
    simp only at this
    exact star_injective this
  ne := by
    intro h
    apply π.ne
    rw [← conjSub_conjSub π.S, h, conjSub_bot]
  irr := by
    intro S' hle hst
    rcases π.irr (conjSub S') (by rw [← conjSub_conjSub π.S]; exact conjSub_mono hle) (conjSub_stable hst) with h | h
    · left
      rw [← conjSub_conjSub S', h, conjSub_bot]
    · right
      rw [← conjSub_conjSub S', h]

theorem conjT_S (π : Formalism.L2.NG.FinTyp L n) : (FinTyp.conjT π).S = conjSub π.S := rfl

end Conj

section Act

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostI (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def rtA (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def actM (P : RowPsi V n) (M : Mult.DSModel V Sp) : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ (Mult.MMap M) where
  toFun h := Mult.postOn M (rtA (P.ψ h))
  map_one' := by
    apply LinearMap.ext
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    simp [Mult.postOn_apply, rtA, rTr]
  map_mul' a b := by
    apply LinearMap.ext
    intro T
    apply MultilinearMap.ext
    intro v
    funext g
    simp only [map_mul, Module.End.mul_apply, Mult.postOn_apply]
    show T v (g * (P.ψ a * P.ψ b)) = T v (g * P.ψ a * P.ψ b)
    rw [mul_assoc]

theorem actM_apply (P : RowPsi V n) (M : Mult.DSModel V Sp) (h : Formalism.AUTREP.GAf D.host.E n) (T : Mult.MMap M) (v : M.Vec)
    (g : GA D V) : actM P M h T v g = T v (g * P.ψ h) := rfl

def levN (P : RowPsi V n) (N : ℕ) : Set (GA D V) := P.ψ '' {κ | Formalism.L2.NG.Cong D.host.E n N κ}

def Minf (P : RowPsi V n) (M : Mult.DSModel V Sp) : Submodule ℂ (Mult.MMap M) :=
  ⨆ N : ℕ, Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

def isotIn {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ A) (C : Submodule ℂ A)
    (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ A :=
  ⨆ (Φ : π.S →ₗ[ℂ] A) (_ : IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C), LinearMap.range Φ

def isotL (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ (Mult.MMap M) :=
  Mult.goodPart θ M J χ e ⊓ isotIn (actM P M) (Minf θ P M) π

def isotE (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (π : Formalism.L2.NG.FinTyp D.host.E n) : Submodule ℂ (Mult.MMap M) :=
  isotL θ P M J χ e (FinTyp.conjT π)

def OccRows (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Set (Formalism.L2.NG.FinTyp D.host.E n) :=
  {π | ∃ b, isotE θ P M (J b) (χ b) (e b) π ≠ ⊥}

abbrev FTR (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Bool → Set (GA D V)) (χ : Bool → GA D V → ℂ)
    (e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Type :=
  Formalism.L2.Col.FinTypCls (OccRows θ P M J χ e)

def rowRepR {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ : FTR θ P M J χ e) : Formalism.L2.NG.FinTyp D.host.E n :=
  Formalism.L2.Col.finTypRep _ σ

theorem rowRepR_occ {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ : FTR θ P M J χ e) : rowRepR θ σ ∈ OccRows θ P M J χ e :=
  Formalism.L2.Col.finTypRep_mem _ σ

theorem rowRepR_inj {P : RowPsi V n} {M : Mult.DSModel V Sp} {J : Bool → Set (GA D V)} {χ : Bool → GA D V → ℂ}
    {e : Bool → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)} (σ σ' : FTR θ P M J χ e)
    (h : (rowRepR θ σ).Iso (rowRepR θ σ')) : σ = σ' :=
  Formalism.L2.Col.finTypRep_inj h

def IsEigOf (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (π : Formalism.L2.NG.FinTyp D.host.E n) (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Prop :=
  (∃ x ∈ π.S, x ≠ 0 ∧ IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x) ∧
  (∀ Pr d R, Mult.Hecke₂ V J χ Sb Pr d R → ∀ x ∈ π.S, IsTypeVec (P.ψ ⁻¹' J) (fun κ => χ (P.ψ κ)) x →
    Hecke₃ P R x = c Pr d • x) ∧
  ∀ Pr d, (¬ ∃ R, Mult.Hecke₂ V J χ Sb Pr d R) → c Pr d = 0


open Classical in
def cOfT (P : RowPsi V n) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (π : Formalism.L2.NG.FinTyp D.host.E n) : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ :=
  if h : ∃ c, IsEigOf P J χ Sb π c then h.choose else 0

structure IsIsomFin {Y W : Formalism.BasicNotions.TH.HSp D} (ι : ↥(GfC Y) →* ↥(GfC W)) : Prop where
  bij : Function.Bijective ι
  conj : ∃ (X : Matrix (Fin W.rank) (Fin Y.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (X' : Matrix (Fin Y.rank) (Fin W.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), X * X' = 1 ∧ X' * X = 1 ∧
      ∀ g : GfC Y, finMat D.sp.cm.sig W.gram ((ι g : GfC W) : GA D W) = X * finMat D.sp.cm.sig Y.gram (g : GA D Y) * X'
  lat : ∀ g : GfC Y, ((g : GA D Y) ∈ KsphC Y ∅ ↔ ((ι g : GfC W) : GA D W) ∈ KsphC W ∅)

def FrameMatch {Y W : Formalism.BasicNotions.TH.HSp D} (PY : RowPsi Y n) (PW : RowPsi W n) (ι : ↥(GfC Y) →* ↥(GfC W)) : Prop :=
  ∃ k : Formalism.AUTREP.GAf D.host.E n, ∀ h, PW.ψ (k⁻¹ * h * k) = ((ι ⟨PY.ψ h, PY.into h⟩ : GfC W) : GA D W)

end Act

end Formalism.IndefR.principalLevelFrame
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.CutPassage3
section
namespace Formalism.IndefR.CxPass

theorem steps3 : Steps3 := fun _ _ _ _ _ _ _ _ _ _ _ _ I =>
  ⟨I.pRho, I.pJ, I.pRange, I.pMet_of I.pJt I.pJ, I.pFrames, I.pUni_of I.pJt I.pRho, I.pLat_of I.pJt,
    I.pGLat_of I.pJt I.pRho, I.pSand_of I.pJt I.pJ I.pRho I.pRange, fun _ _ _ _ _ _ τ => I.pGood_of I.pJt I.pRho τ⟩

theorem cutPassage3S : CutPassage3S := cutPassage3S_of_steps steps3

end Formalism.IndefR.CxPass
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.FixNLeMulRight
section
noncomputable section

open NumberField

namespace Formalism.IndefR.principalLevelFrame

section SSP

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
variable {A : Type} [AddCommGroup A] [Module ℂ A]
variable {ρ : Formalism.AUTREP.GAf L n →* Module.End ℂ A} {B : A →ₗ⋆[ℂ] A →ₗ[ℂ] ℂ}

def Intw (π π' : Formalism.L2.NG.FinTyp L n) (T : π.S →ₗ[ℂ] π'.S) : Prop :=
  ∀ (h : Formalism.AUTREP.GAf L n) (f : π.S), T ⟨Formalism.L2.NG.rt L n h f, π.stable h f f.2⟩ =
    ⟨Formalism.L2.NG.rt L n h (T f), π'.stable h _ (T f).2⟩

end SSP

end Formalism.IndefR.principalLevelFrame
end
end

