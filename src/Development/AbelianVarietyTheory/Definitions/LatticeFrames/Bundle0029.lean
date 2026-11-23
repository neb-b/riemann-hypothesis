module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChartZero
section
noncomputable section

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeSaw GlobalTheory.Fam Matrix ValuativeRel IsLocalRing GlobalTheory.LocMod

namespace GlobalTheory.MiTop

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word} (f : FamCh W u)
  (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0))

def LevTrace : Prop :=
  ∀ κ ∈ GfC (D.sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (Formalism.L2.Forms.gramN D 0 (Nat.zero_le _))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    GlobalTheory.AdForm.finM (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) κ = y.1.1 →
    ((y : GL _ _) ∈ (F0 W u).cls0.lev.U ↔
      (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0) ∈ rJ W) ∧
    ∀ hy : (y : GL _ _) ∈ (F0 W u).cls0.lev.U, (((F0 W u).cls0.lev.chi ⟨_, hy⟩ : ℂˣ) : ℂ) *
      rChi W ((show GA D (D.sp.Y 0) from f.g.b 0)⁻¹ * embA B.d B.o κ * (show GA D (D.sp.Y 0) from f.g.b 0)) = 1

structure BotTie {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
    (v : VCom f.c) (o : TDat f.c k ι) {n : ℕ} (G : Fin n → GLoc v) : Prop where
  lev : ∀ h₀ : 0 + 2 * D.R.rS + 2 = D.R.m, B.lev = f.c.B 0 D.R.rS h₀
  adapted : B.Adapted (W.S.tr u).wt
  norm : ∃ μ lam : D.host.E, μ * lam = -D.host.xi0 ^ (D.R.m / 2) ∧
    (∀ r, (B.d.i₀ *ᵥ vecB B.o B.ζ) r = μ * W.S.X.ιE (W.S.X.zR u (Fin.cast (rank_eq W.S.X W.Q.instEq) r))) ∧
    ∀ j h, v.τ j h *ᵥ o.ζ₀ = lam • (f.c.bes j 0 h).ζ
  last : ∀ i, (G i).z₀ = fun r => (ofSplit (G i).q).pr (o.ζ₀ r)
  lat : ∀ p, p ∉ v.tP → GlobalTheory.FinPl.latV (D.sp.X 0) (f.g.x 0).L (· = p) = GlobalTheory.FinPl.latV (D.sp.X 0)
    ((F0 W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft D.host.E D.host.E
      (finCongr (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 D.host.E))) (· = p)
  trace : LevTrace f B

end GlobalTheory.MiTop

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.InfiniteQAtOfIs
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.QPl.PinTest
open GlobalTheory.QPl.Model

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n]

theorem prX_KO {c : ℕ} : prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  have key : ∀ g : GL n k, g ∈ prX (Cgrp (KO k (n ⊕ Fin c)) 1) → IntM g.val := by
    rintro g ⟨u, hu, h⟩ i j
    have h2 := (mem_KO.1 (mem_Cgrp.1 h).2).1 (Sum.inl i) (Sum.inl j)
    have h3 : (u * embX c g).val.toBlocks₁₁ = g.val := by
      rw [Units.val_mul, mul_toBlocks₁₁, Radical.toBlocks₁₁_of_mem hu]
      change 1 * (fromBlocks g.val 0 0 1).toBlocks₁₁ + _ * (fromBlocks g.val 0 0 1).toBlocks₂₁ = _
      simp
    rw [inv_one, one_mul, mul_one] at h2
    rw [← h3]; exact h2
  ext g
  refine ⟨fun h => mem_KO.2 ⟨key g h, key _ (inv_mem h)⟩, fun h => ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩⟩
  · rw [one_mul]; exact Subgroup.mem_sup_left ⟨g, rfl⟩
  · rw [inv_one, one_mul, one_mul, mul_one]
    refine mem_KO.2 ⟨intM_fromBlocks.2 ⟨(mem_KO.1 h).1, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩, ?_⟩
    rw [← map_inv]
    exact intM_fromBlocks.2 ⟨(mem_KO.1 h).2, intM_zero, intM_zero, intM_of_mem_KO (one_mem _)⟩

variable {s : ℕ} (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z : Type) [Fintype Z] [DecidableEq Z]



variable [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ν : Measure k} (hν : IsUnitVol ν)
include hψ hν

theorem isOneComb_sph {c P : ℕ} (h1 : 1 ≤ P) (h2 : P ≤ c) : IsOneComb ψ ν P (sph k (n ⊕ Fin c)) 1 (Finsupp.single 1 1) :=
  fun A _ _ σ hσ l hl v hv => by
  rw [map_one, Module.End.one_apply, GlobalTheory.PosOneSpherical.toOne_spherical k n c P h1 h2 ψ hψ.continuous hψ ν hν A σ hσ l hl v
    fun g hg => (hv ⟨g, hg⟩).trans (one_smul ℂ v)]
  simp [GlobalTheory.PosOne.comb]

end Local

section Rat
variable {D : D7}

end Rat

variable {D : D7} {c : Comm D} {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}

section Rel
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Rel


end GlobalTheory.QPl.PinTest
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotLineLatAtZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.LiftModel

variable {D : D7} {u : D.what₂.Word}

def lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) : Lat L :=
  (𝔠 : Submodule (𝓞 D.host.E) D.host.E).map
    ((LinearMap.toSpanSingleton D.host.E (Fin L.rank → D.host.E) ζ).restrictScalars (𝓞 D.host.E))

theorem tmul_mul_incA (α : AF D.host.F) (x z : D.host.E) :
    (α ⊗ₜ[D.host.F] x : AE D) * incA D z = α ⊗ₜ[D.host.F] (x * z) := by
  change (α ⊗ₜ[D.host.F] x : AE D) * (1 ⊗ₜ[D.host.F] z) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]

theorem latV_lineLat (L : HSp D) (ζ : Fin L.rank → D.host.E) (𝔠 : FI D) (v : Pl D) :
    latV L (lineLat L ζ 𝔠) (· = v) =
      (idV 𝔠 v).map (LinearMap.toSpanSingleton (AE D) (Fin L.rank → AE D) (ratV ζ)).toAddMonoidHom := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul idV
  rw [AddMonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨α, h1, h2, a, rfl, x, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]
  · rintro ⟨_, ⟨α, h1, h2, c, hc, rfl⟩, rfl⟩
    refine ⟨α, h1, h2, 1, rfl, _, ⟨c, hc, rfl⟩, ?_⟩
    funext i
    simp [ratV, tmul_mul_incA]

theorem lineLatAt_lineLat (L : HSp D) {ζ : Fin L.rank → D.host.E} (hζ : ζ ≠ 0) (𝔠 : FI D) (v : Pl D) :
    LineLatAt L ζ 𝔠 (lineLat L ζ 𝔠) v := by
  intro a _
  rw [latV_lineLat]
  refine ⟨?_, fun h => ⟨a, h, rfl⟩⟩
  rintro ⟨a', h, e⟩
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hζ
  have e1 : a' * incA D (ζ i) = a * incA D (ζ i) := congrFun e i
  have hu : IsUnit (incA D (ζ i)) := (IsUnit.mk0 _ hi).map _
  rwa [← hu.mul_right_cancel e1]

theorem idV_le_idAt (𝔞 : FI D) (v : Pl D) : ∀ a ∈ idV 𝔞 v, a ∈ idAt D (· = v) := by
  intro a ha
  refine (AddSubgroup.closure_le (idAt D (· = v)).toAddSubgroup).2 ?_ ha
  rintro _ ⟨α, -, h2, x, -, rfl⟩
  refine Ideal.mem_inf.2 ⟨?_, Ideal.mem_iInf.2 fun w => ?_⟩
  · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] x = 0
    exact TensorProduct.zero_tmul _ _
  · change (evalV D.host.F w.1 α) ⊗ₜ[D.host.F] x = 0
    rw [h2 _ w.2, TensorProduct.zero_tmul]

theorem one_tmul_one_ne (F A E : Type) [Field F] [Field A] [Field E] [Algebra F A] [Algebra F E] :
    (1 : A) ⊗ₜ[F] (1 : E) ≠ 0 := one_ne_zero (α := A ⊗[F] E)

theorem idV_ne_bot {𝔞 : FI D} (h : 𝔞 ≠ 0) (v : Pl D) : idV 𝔞 v ≠ ⊥ := by
  classical
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ 𝔞, x ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (FractionalIdeal.eq_zero_iff.2 hc)
  have ev : evalV D.host.F v (singleV D.host.F v 1) = 1 := by
    exact RestrictedProduct.single_eq_same (fun w : Pl D => w.adicCompletionIntegers D.host.F) v 1
  have ew : ∀ w, w ≠ v → evalV D.host.F w (singleV D.host.F v 1) = 0 := fun w hw => by
    exact RestrictedProduct.single_eq_of_ne (fun w : Pl D => w.adicCompletionIntegers D.host.F) 1 hw
  intro hb
  have hm : (pairA D.host.F 0 (singleV D.host.F v 1)) ⊗ₜ[D.host.F] x ∈ idV 𝔞 v := by
    refine AddSubgroup.subset_closure ⟨_, fun w => ?_, ew, x, hx, rfl⟩
    by_cases hw : w = v
    · subst hw; rw [ev]; exact one_mem _
    · rw [ew w hw]; exact zero_mem _
  rw [hb, AddSubgroup.mem_bot] at hm
  have h2 := congrArg (fun y => compAt D v (y * incA D x⁻¹)) hm
  simp only [tmul_mul_incA, mul_inv_cancel₀ hx0, zero_mul, map_zero] at h2
  change (evalV D.host.F v (singleV D.host.F v 1)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0 at h2
  rw [ev] at h2
  exact one_tmul_one_ne _ _ _ h2

theorem AA_ne (hP : FactPrincipalDatum) : D.host.AA ≠ 0 ∧ D.host.AAbar ≠ 0 ∧ D.host.xi0 ≠ 0 := by
  have h1 := hP D.R D.host
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> simp [h] at h1

variable {a : XPart D u} {b : YPart a}

theorem lineId_of_split {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (LA : Lat A) (LL : Lat L)
    (𝔠 : FI D) (v : Pl D) (h : LineLatAt L ζ 𝔠 LL v) (ho : OrthAt o M LA LL v) : LineId o ζ M 𝔠 v := by
  intro a ha
  have e : ratV (vecB o ζ) = o.jB *ᵥ ratV ζ := by
    funext i
    simp [ratV, vecB, OrthDec.jB, rat, mulVec, dotProduct]
  rw [ho, e, mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, ← h a ha]
  rw [o.pA_jB, o.pB_jB, zero_mulVec, smul_zero, one_mulVec]
  exact and_iff_right (zero_mem _)

end GlobalTheory.SeeSaw.LiftModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}

structure TwDat.Live {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) : Prop where
  inj : ∀ j, Function.Injective (ι j)
  first : Function.Surjective (ι 0)
  last : Function.Surjective (ι B.R.m)
  dead : ∀ j (hj : j + 1 ≤ B.R.m) γ, γ ∉ Set.range (ι (j + 1)) → ∀ α z, A.xi j hj α γ z = 0

def TwDat.RamL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) (j : ℕ) (φ : ColT I l u a j) : Prop :=
  RamT j φ ∧ ∀ c, A.chOf j c ∉ Set.range (ι j) → φ c = 0

structure PinColL {Ch₀ Ch : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j)
    (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))
    (x : ∀ j, DefSp ((I.rec7 l Z).sp.X j)) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (c₀ : ℕ → ℂ)
    (kom : ∀ j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)))
    (dd : ∀ j, Ch j → Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ)
    (w : ∀ j, Ch j → Ch (j + 1) → ℂ) (Ram : ∀ j, Set (ColT I l u a j))
    (rd : ∀ j, Ch j → ColT I l u a j → (I.chain l u a).Y j → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) (cK : ℕ → ℂ) : Prop where
  is : A.Is
  live : A.Live ι
  om : ∀ j, j < B.R.m → IsWeilDatumO ψ _ _ (A.chr (j + 1)) (A.chr (j + 1)) (kom j)
  dat : ∀ j (hj : j + 1 ≤ B.R.m) α γ, GlobalTheory.SeeSaw.IsFinComb (dd j α γ) ∧
    IsRatDatum ψ _ _ A.e (fun z => w j α γ * A.xi j hj (ι j α) (ι (j + 1) γ) z) (vac j) (comb ψ _ _ (dd j α γ) (vac j))
  cst : ∀ j (hj : j + 1 ≤ B.R.m) α γ, (∃ z, A.xi j hj (ι j α) (ι (j + 1) γ) z ≠ 0) →
    cK j = (volLev (x j).vol (A.U j (ι j α)) : ℂ) * w j α γ * c₀ j *
      (A.chr (j + 1) (A.xr j (ι j α)) : ℂ) * (A.chr (j + 1) (A.xr (j + 1) (ι (j + 1) γ)) : ℂ)⁻¹
  ram : ∀ j, j ≤ B.R.m → ∀ φ, φ ∈ Ram j ↔ A.RamL ι j φ
  rdq : ∀ j (hj : j ≤ B.R.m) β φ y, rd j β φ y = A.rd θ j hj (ι j β) φ y

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z))
  (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) {t : T} (r : RowCh R P u g t) (k : ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u a))
  (tl : ColT I l u a B.R.m → CXP R P t → ℂ)

@[reducible] def clsKL (s : ℕ → ℂ)
    (J : SmT R.MX → GA (I.rec7 l Z) (I.rec7 l Z).sp.X' → FrN (I.rec7 l Z) (B.R.N B.R.m - 1) → ℂ) {Ch₀ : ℕ → Type}
    (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) : ClsK (realOf u R g s J) (tupOf R P u g t r k tl) where
  cl := fun j β => {c // A.chOf j c = ι j β}
  fin := fun j _ => letI := (I.chain l u a).clsFin j; Subtype.fintype _
  U := fun j β => A.U j (ι j β)
  chi := fun j β => A.chi j (ι j β)
  h := fun j β => A.h j (ι j β)
  val := fun _ _ ψ c z => ψ c.1 ⟨z.1, z.2⟩
  abelian₂ := fun j _ _ c c' => A.abelian₂ j c.1 c'.1

def PinChL (c₀ : ℕ → ℂ) {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j)
    (w : ∀ j, k.Ch j → k.Ch (j + 1) → ℂ) : Prop :=
  PinColL A ι R.ψ R.θ g.x g.vac c₀ k.kom k.dd w k.Ram k.rd k.cK

structure PinTopL (UT : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) (ε : ℂ) : Prop where
  emb : IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  lev : ∀ h, h ∈ UT ↔ g.bT⁻¹ * h * g.bT ∈ levS _ R.βX (datXP R P t)
  eT : ∀ n h β, k.eT n h β = Finsupp.single g.bT ε
  cP : k.cP = ε * (volLev g.volT UT : ℂ)

end GlobalTheory.AdForm
end
end

