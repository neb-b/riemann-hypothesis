module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GqPtOfNeZeroIff
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.IntTerm

section Defs

variable {E : Type} [Field E] [NumberField E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)

def Col (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun Λ Λ' : FrameLats σ J P => ∃ s, InS σ J P s ∧ latMap s Λ.1 = Λ'.1

def Col.lat {σ : E →+* E} {J : Matrix (Fin n) (Fin n) E} {P : Matrix (Fin n) (Fin (r + 1)) E} (c : Col σ J P) :
    Submodule (𝓞 E) (Fin n → E) := (Quot.out c).1

def FrCls (T' : E) (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Quot fun A B : {A // admitted σ J T' g Λ P A} => Move σ J Λ P A.1 B.1

def Term (T' : E) (g : ℕ) (P : Matrix (Fin n) (Fin (r + 1)) E) : Type :=
  Σ c : Col σ J P, FrCls σ J T' g c.lat P



variable {σ J} {T' : E} {g : ℕ} {P : Matrix (Fin n) (Fin (r + 1)) E}

namespace Term

variable (t : Term σ J T' g P)

end Term

end Defs

section Basic

variable {E : Type} [Field E] [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E}
  {T T' : E} {P A B : Matrix (Fin n) (Fin (r + 1)) E} {Λ : Submodule (𝓞 E) (Fin n → E)}






namespace Term

variable (t : Term σ J T' g P)

variable {t}

variable (t)

end Term

end Basic

section Examples

variable {E : Type} [Field E] [NumberField E]

end Examples

section Spaces

open Formalism.BasicNotions

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def coMat (V : HSpace E) {a : Type} (x : a → V.V) : Matrix (Fin V.rank) a E :=
  Matrix.of fun i b => V.frame.repr (x b) i

theorem hT_eq_sum (V : HSpace E) (x y : V.V) :
    V.hT x y = ∑ j, (∑ i, star (V.frame.repr x i) * V.gram i j) * V.frame.repr y j := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    RingHom.id_apply, HSpace.gram, starRingEnd_apply, mul_comm]

end Spaces

section Record

open Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

variable {D} {u u' : D.what₂.Word}

end Record

end GlobalTheory.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open scoped InnerProductSpace

namespace GlobalTheory.Mem

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def lvlForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)
    (P : Subgroup G) (ψ : P →* Kˣ) : Set S.Forms := {f | ∀ h : P, r (h : G) f = ((ψ h : Kˣ) : K) • f}

def intForms {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) : Set S.Forms :=
  {f | ∀ c, (f : S.Cl → S.V) c ∈ S.Nab c}

def intSpan (D : D7) {V : Type} [AddCommGroup V] [Module ℂ V] (s : Set V) : AddSubgroup V :=
  AddSubgroup.closure {y | ∃ a : 𝓞 D.what₂.LL, ∃ x ∈ s, y = D.what₂.embLL (a : D.what₂.LL) • x}


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure SideTie (R : RealDat D A Ks) (F : Face D A) (tup : T → D.what₂.Tup) (b : Bool) {EE : Type} [NormedAddCommGroup EE]
    [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (S : RowSide D EE) where

  eE : EE →ₗ[ℂ] R.HE.H

  eE_range : LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e

  eE_norm : ∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2

  eA : ∀ t, S.Amb (tup t) →ₗ[ℂ] (R.HX t).H

  eA_range : ∀ t, LinearMap.range (eA t) =
    Submodule.span ℂ (R.jX t '' lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ)

  eA_norm : ∀ t x, ‖eA t x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2

  eOp_tie : ∀ t x (f : (A.MtildeCSD t).Forms), eA t x = R.jX t f →
    eA t (S.eOp (tup t) x) = R.jX t ((A.MtildeCSD t).gaOp (A.leftGroupActionRight t) (idemOf A.X) f)

  iota_tie : ∀ t x, eE (S.iota (tup t) x) = R.Th t (eA t x)

  lat_tie : ∀ t, eA t '' (S.Mtilde (tup t)).carrier =
    R.jX t '' (lvlForms (A.MtildeCSD t) (A.leftGroupActionRight t) (F.lvl b).P (F.lvl b).ψ ∩ intForms (A.MtildeCSD t))


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure RowsTieSum (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) where

  tup : T → D.what₂.Tup

  tup_inj : Function.Injective tup

  tup_zero : tup A.μ0 = D.what₂.mu0

  muAt_tie : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))

  sharp : SideTie R F tup true (RowSide.sharp D)

  base : SideTie R F tup false X0.s

  ty : D.what₂.FT → A.fam.base.Ix

  ft_tie : ∀ σ, sharp.eE (D.what₂.onb σ) ∈ R.EEp (ty (D.what₂.ft σ))

  framedRowBaseTie : ∀ σ, base.eE (D.what₂.onb0 σ) ∈ R.EEp (ty (D.what₂.ft0 σ))

  eV : ∀ (i : Fin D.R.m) t, D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HV i t).H

  eV_range : ∀ i t, LinearMap.range (eV i t) =
    Submodule.span ℂ (R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹)

  eV_norm : ∀ i t x, ‖eV i t x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eV_rat : ∀ i t, Set.range (fun x => eV i t (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) =
    R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹

  eV_lat : ∀ i t, intSpan D (eV i t '' (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier) =
    intSpan D (R.jV i t '' (lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ ∩ intForms (A.MtCSD i t)))

  eMt_tie : ∀ i t x (f : (A.MtCSD i t).Forms), eV i t x = R.jV i t f →
    eV i t (D.what₂.eMt (tup t) ((i : ℕ) + 1) x) = R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)

  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H

  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eW_lat : ∀ i, intSpan D (eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) =
    intSpan D ((R.FW i).j (sg0 D A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) : Set _))

  theta_tie : ∀ i t x, eW i (D.what₂.thetaP (tup t) ((i : ℕ) + 1) x) = R.thG i t (eV i t x)

  isot_sum : ∀ (i : Fin D.R.m) π,
    (⨆ π', ⨆ (_ : ty π' = ty π), D.what₂.isot ((i : ℕ) + 1) π') = (R.Wp i (ty π)).comap (eW i)

  lam_tie : ∀ (i : Fin D.R.m) t π, D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    D.what₂.lamP (tup t) ((i : ℕ) + 1) π = R.lam i t (ty π) A.v0

  etaJ_tie : ∀ (i : Fin D.R.m) w, D.what₂.muAt w ≠ D.what₂.mu0 → D.what₂.etaJ ((i : ℕ) + 1) w =
    A.fam.etaJ F.P0 F.ψ0 (R.toCx F).zs i (R.mu (D.plEq w)) (D.plEq w)


set_option genInjectivity false in
set_option genSizeOfSpec false in
set_option maxHeartbeats 2000000 in
structure RowsTie (R : RealDat D A Ks) (F : Face D A) (X0 : BaseLevelRowSide D) where

  tup : T → D.what₂.Tup

  tup_inj : Function.Injective tup

  tup_zero : tup A.μ0 = D.what₂.mu0

  muAt_tie : ∀ w, D.what₂.muAt w = tup (R.mu (D.plEq w))

  sharp : SideTie R F tup true (RowSide.sharp D)

  base : SideTie R F tup false X0.s

  ty : D.what₂.FT → A.fam.base.Ix

  ty_inj : Function.Injective ty

  ft_tie : ∀ σ, sharp.eE (D.what₂.onb σ) ∈ R.EEp (ty (D.what₂.ft σ))

  framedRowBaseTie : ∀ σ, base.eE (D.what₂.onb0 σ) ∈ R.EEp (ty (D.what₂.ft0 σ))

  eV : ∀ (i : Fin D.R.m) t, D.what₂.Mt (tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.HV i t).H

  eV_range : ∀ i t, LinearMap.range (eV i t) =
    Submodule.span ℂ (R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹)

  eV_norm : ∀ i t x, ‖eV i t x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eV_rat : ∀ i t, Set.range (fun x => eV i t (D.what₂.jMt (tup t) ((i : ℕ) + 1) x)) =
    R.jV i t '' lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹

  eV_lat : ∀ i t, intSpan D (eV i t '' (D.what₂.MtLat (tup t) ((i : ℕ) + 1)).carrier) =
    intSpan D (R.jV i t '' (lvlForms (A.MtCSD i t) (A.leftGroupActionLift i t) F.P0 F.ψ0⁻¹ ∩ intForms (A.MtCSD i t)))

  eMt_tie : ∀ i t x (f : (A.MtCSD i t).Forms), eV i t x = R.jV i t f →
    eV i t (D.what₂.eMt (tup t) ((i : ℕ) + 1) x) = R.jV i t ((A.MtCSD i t).gaOp (A.leftGroupActionLift i t) (idemOf A.X) f)

  eW : ∀ i : Fin D.R.m, D.what₂.Mj ((i : ℕ) + 1) →ₗ[ℂ] (R.HW i (sg0 D A)).H

  eW_range : ∀ i, LinearMap.range (eW i) = (R.Wat i (sg0 D A) (R.levL F false (sg0 D A))).comap (R.HW i (sg0 D A)).e

  eW_norm : ∀ i x, ‖eW i x‖ ^ 2 = RealDat.nP F false * ‖x‖ ^ 2

  eW_lat : ∀ i, intSpan D (eW i '' (D.what₂.MjLat ((i : ℕ) + 1)).carrier) =
    intSpan D ((R.FW i).j (sg0 D A) '' ((R.FW i).Mj F.P0 F.ψ0⁻¹ (fun g => (idemOf A.X).coeff g) : Set _))

  theta_tie : ∀ i t x, eW i (D.what₂.thetaP (tup t) ((i : ℕ) + 1) x) = R.thG i t (eV i t x)

  isot_tie : ∀ (i : Fin D.R.m) π, D.what₂.isot ((i : ℕ) + 1) π = (R.Wp i (ty π)).comap (eW i)

  lam_tie : ∀ (i : Fin D.R.m) t π, D.what₂.isot ((i : ℕ) + 1) π ≠ ⊥ →
    D.what₂.lamP (tup t) ((i : ℕ) + 1) π = R.lam i t (ty π) A.v0

  etaJ_tie : ∀ (i : Fin D.R.m) w, D.what₂.muAt w ≠ D.what₂.mu0 → D.what₂.etaJ ((i : ℕ) + 1) w =
    A.fam.etaJ F.P0 F.ψ0 (R.toCx F).zs i (R.mu (D.plEq w)) (D.plEq w)

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (r : Representation K G S.Forms)

end Basic

theorem inner_of_norm_sq {F : Face D A} {b : Bool} {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V →ₗ[ℂ] W) (h : ∀ x, ‖e x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) (x y : V) :
    ⟪e x, e y⟫_ℂ = ((RealDat.nP F b : ℝ) : ℂ) * ⟪x, y⟫_ℂ := by
  have h' : ∀ x, ((‖e x‖ : ℝ) : ℂ) ^ 2 = ((RealDat.nP F b : ℝ) : ℂ) * ((‖x‖ : ℝ) : ℂ) ^ 2 := fun x => by exact_mod_cast h x
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, ← map_add (f := _), ← map_sub, ← map_smul, ← map_sub, ← map_add (f := _)]
  simp only [Complex.coe_algebraMap, h']
  ring

namespace SideTie

variable {R : RealDat D A Ks} {F : Face D A} {tup : T → D.what₂.Tup} {b : Bool} {EE : Type} [NormedAddCommGroup EE]
  [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] {S : RowSide D EE} (Y : SideTie R F tup b S)

end SideTie

section Fibre

variable {V H I J : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup H] [Module ℂ H]

end Fibre

namespace RowsTieSum

variable {R : RealDat D A Ks} {F : Face D A} {X0 : BaseLevelRowSide D} (Y : RowsTieSum R F X0)

end RowsTieSum

namespace RowsTie

variable {R : RealDat D A Ks} {F : Face D A} {X0 : BaseLevelRowSide D} (Y : RowsTie R F X0)

end RowsTie

end GlobalTheory.Mem

end
end

