module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalModel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftModelsOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.Mem.Th

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

section Level

theorem mult_anti {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ}
    (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : Mult θ M J χ ≤ Mult θ M J' χ' :=
  Submodule.span_mono fun _ hX => ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩

theorem principal_le_level {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ)
    (k : GA D V) (hk : k ∈ levS V β (flag1L L)) :
    k ∈ levS V β (withP L P) ∧ levChi V β (withP L P) k = levChi V β (flag1L L) k := by
  have h1 : rTup β L (finE V k) = 1 := Subgroup.mem_bot.1 hk.2.2
  have h2 : rTup β L (finE V k) ∈ P.H := h1 ▸ P.H.one_mem
  refine ⟨⟨hk.1, hk.2.1, h2⟩, ?_⟩
  unfold levChi
  rw [levFn_withP, levFn_flag1, h1, extendOne_of_mem _ P.H.one_mem]
  exact congrArg Units.val ((congrArg (· * _) (map_one P.chi)).trans (one_mul _))

variable (R : RealDat D A Ks)

def multAt (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : Submodule ℂ (MMap (R.MY j)) :=
  Mult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P)) (levChi _ (R.βY j) (R.datYt t j P))

def toMM (t : T) (j : ℕ) : R.CC t j →ₗ[ℂ] MMap (R.MY j) :=
  (PiTensorProduct.lift.symm : (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ≃ₗ[ℂ] MMap (R.MY j)).toLinearMap ∘ₗ (R.CC t j).subtype

def lvlPart (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : Submodule ℂ (R.CC t j) := (multAt R P t j).comap (toMM R t j)

def ipCC (t : T) (j : ℕ) (U U' : R.CC t j) : ℂ := ipM (R.MY j) (R.νY t j) (R.fdY t j) (toMM R t j U) (toMM R t j U')

def topLift (t : T) : (R.HX t).H →ₗ[ℂ] R.CC t (D.R.m - 1) := R.ioX t ∘ₗ (R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict

def botLift (t : T) : R.CC t 1 →ₗ[ℂ] MMap (R.MY 0) := postOn (R.MY 0) R.e0 ∘ₗ toMM R t 0 ∘ₗ R.ioY t 0

theorem toMM_injective (t : T) (j : ℕ) : Function.Injective (toMM R t j) :=
  (PiTensorProduct.lift.symm : (SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ≃ₗ[ℂ] MMap (R.MY j)).injective.comp Subtype.val_injective

theorem range_toMM (t : T) (j : ℕ) : LinearMap.range (toMM R t j) = multAt R R.triv t j := by
  ext X
  constructor
  · rintro ⟨U, rfl⟩
    exact (mem_multT R.θ (R.MY j) _ _ _).1 U.2
  · intro hX
    exact ⟨⟨PiTensorProduct.lift X, Submodule.mem_map_of_mem hX⟩, PiTensorProduct.lift.symm_apply_apply X⟩

theorem multAt_le (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) : multAt R P t j ≤ multAt R R.triv t j :=
  mult_anti _ _ (principal_le_level (R.βY j) (R.datYt t j R.triv) P)

theorem multAt_zero (P : LevelP R.Pg D.R.r ℂ) (t : T) :
    multAt R P t 0 = Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 P)) (levChi _ (R.βY 0) (R.dat0 P)) := by
  have hr : (Yc D 0).rank = D.R.r := by
    rw [D.sp.Y_rank _ (min_le_right _ _)]
    simp [Ranks.rankY]
  have e := GlobalTheory.levG_twist_trivial_of_rank_eq (Yc D 0) (R.βY 0) D.R.r D.R.t (r_le_Y 0) hr R.Pg (R.Q t) P R.chi (R.xiR t)
  have e1 : levG (Yc D 0) (R.βY 0) (R.datYt t 0 P) = levG (Yc D 0) (R.βY 0) (R.dat0 P) := e.1
  have e2 : ∀ k ∈ levG (Yc D 0) (R.βY 0) (R.datYt t 0 P),
      levChi (Yc D 0) (R.βY 0) (R.datYt t 0 P) k = levChi (Yc D 0) (R.βY 0) (R.dat0 P) k := e.2
  exact le_antisymm (mult_anti _ _ fun k hk => ⟨e1.ge hk, e2 k (e1.ge hk)⟩) (mult_anti _ _ fun k hk => ⟨e1.le hk, (e2 k hk).symm⟩)

theorem EEat_le_triv (P : LevelP R.Pg D.R.r ℂ) : R.EEat P ≤ R.EEat R.triv :=
  inf_le_inf_right _ (mult_anti _ _ (principal_le_level (R.βY 0) (R.dat0 R.triv) P))

end Level

section Side

variable {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE)

theorem pred_m_add_one (D : D7) : D.R.m - 1 + 1 = D.R.m := by have := D.R.two_le_m; omega

def famCast (Sp : ℕ → Type) [∀ j, NormedAddCommGroup (Sp j)] [∀ j, InnerProductSpace ℂ (Sp j)] {i j : ℕ} (h : i = j) :
    Sp i ≃ₗᵢ[ℂ] Sp j := by
  subst h; exact LinearIsometryEquiv.refl ℂ _

def multCast (μ : D.what₂.Tup) {i j : ℕ} (h : i = j) : S.Mult μ i ≃ₗᵢ[ℂ] S.Mult μ j := famCast (S.Mult μ) h

def topEquiv (μ : D.what₂.Tup) : S.Mult μ (D.R.m - 1 + 1) ≃ₗᵢ[ℂ] S.Amb μ := (multCast S μ (pred_m_add_one D)).trans (S.multTop μ)

end Side

variable {R : RealDat D A Ks} {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
  [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE}


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure MultTie (Y : SideTie R F tup b S) where

  eM : ∀ t j, S.Mult (tup t) j →ₗ[ℂ] R.CC t j

  eM_zero : ∀ t x, toMM R t 0 (eM t 0 x) = R.HE.e (Y.eE (S.multZero (tup t) x))

  eM_range : ∀ t j, 0 < j → j < D.R.m → LinearMap.range (eM t j) = lvlPart R (R.levR F b) t j

  eM_inner : ∀ t j, 0 < j → j < D.R.m → ∀ x y, ipCC R t j (eM t j x) (eM t j y) = ((RealDat.nP F b : ℝ) : ℂ) * ⟪x, y⟫_ℂ

  io_zero : ∀ t x, toMM R t 0 (eM t 0 (S.io (tup t) 0 x)) = botLift R t (eM t 1 x)

  io_mid : ∀ t j, 0 < j → j + 1 < D.R.m → ∀ x, eM t j (S.io (tup t) j x) = R.ioY t j (eM t (j + 1) x)

  io_top : ∀ t x, eM t (D.R.m - 1) (S.io (tup t) (D.R.m - 1) x) = topLift R t (Y.eA t (topEquiv S (tup t) x))

section Inhabitant

theorem exists_factor {X Y Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (g : Y →ₗ[ℂ] Z) (hg : Function.Injective g) (f : X →ₗ[ℂ] Z) (hf : ∀ x, f x ∈ LinearMap.range g) :
    ∃ h : X →ₗ[ℂ] Y, ∀ x, g (h x) = f x :=
  ⟨(LinearEquiv.ofInjective g hg).symm.toLinearMap ∘ₗ f.codRestrict _ hf, fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective g hg).apply_symm_apply ⟨f x, hf x⟩)⟩

theorem haar_chain (hY : R.models_νY) (hY' : R.models_νY') (t : T) (j : ℕ) (hj : j < D.R.m) :
    (R.νY t j).IsHaarMeasure ∧ IsFundamentalDomain (GQ (Yc D j)) (R.fdY t j) (R.νY t j) := by
  by_cases h1 : j + 1 < D.R.m
  · exact ⟨(hY t j h1).1.1, (hY t j h1).2⟩
  · obtain rfl : j = D.R.m - 1 := by omega
    exact ⟨(hY' t).1.1, (hY' t).2⟩


set_option genInjectivity false in
set_option genSizeOfSpec false in
structure HChain (m : ℕ) (E B : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] where

  Sp : ℕ → Type
  [nSp : ∀ j, NormedAddCommGroup (Sp j)]
  [iSp : ∀ j, InnerProductSpace ℂ (Sp j)]
  [fSp : ∀ j, FiniteDimensional ℂ (Sp j)]

  bot : Sp 0 ≃ₗᵢ[ℂ] E

  top : Sp m ≃ₗᵢ[ℂ] B

  io : ∀ j, Sp (j + 1) →ₗ[ℂ] Sp j

attribute [instance] HChain.nSp HChain.iSp HChain.fSp


end Inhabitant

def MultTied {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0) : Prop := Function.Surjective Y.tup ∧ Nonempty (MultTie Y.sharp)

theorem isMultiplicityInner_mul_inner {V : HSp D} {Sp : D.what₂.Tau → SPar} {M : DSModel V Sp} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : H →ₗ[ℂ] MMap M) {d : ℂ} (hd : d ≠ 0)
    (h : ∀ x y, ipM M μ 𝓕 (e x) (e y) = d * ⟪x, y⟫_ℂ) (x y : H) : IsMultIP M μ 𝓕 (e x) (e y) (d * ⟪x, y⟫_ℂ) := by
  have key : ∀ x y : H, ⟪x, y⟫_ℂ ≠ 0 → IsMultIP M μ 𝓕 (e x) (e y) (d * ⟪x, y⟫_ℂ) := fun x y hxy => by
    rw [← h]
    refine ipM_spec M μ 𝓕 _ _ ?_
    by_contra hn
    exact mul_ne_zero hd hxy ((h x y).symm.trans (by rw [ipM, dite_eq_right hn]))
  by_cases hxy : ⟪x, y⟫_ℂ = 0
  swap
  · exact key x y hxy
  by_cases hx : x = 0
  · subst hx
    intro v v'
    simp
  have hxx : ⟪x, x⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hx
  have h₁ := key x x hxx
  have h₂ := key x (x + y) (by rwa [inner_add_right, hxy, add_zero])
  intro v v'
  have hf : (fun g => star (e x v g) * e y v' g) = fun g => star (e x v g) * e (x + y) v' g - star (e x v g) * e x v' g := by
    funext g
    simp only [map_add (f := _), add_apply, Pi.add_apply]
    ring
  rw [hf]
  refine ⟨(h₂ v v').1.sub (h₁ v v').1, ?_⟩
  rw [integral_sub (h₂ v v').1 (h₁ v v').1, (h₂ v v').2, (h₁ v v').2, inner_add_right]
  ring

namespace MultTie

variable {Y : SideTie R F tup b S} (M : MultTie Y)


end MultTie

namespace MultTied

variable {X0 : BaseLevelRowSide D} {Y : RowsTie R F X0}

end MultTied

end GlobalTheory.Mem.Th

end
