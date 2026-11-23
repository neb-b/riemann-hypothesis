module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0013

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MultGood
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem goodPar_dualPar {n p q : ℕ} {S : SPar} (h : GoodPar n p q S) : GoodPar n p q (dualPar S) := by
  obtain ⟨lam, ε, ⟨hanti, Q, hQ, rfl⟩, ⟨_, hint⟩, hp, hq⟩ := h
  refine ⟨fun a => -lam (Fin.rev a), fun a => ε (Fin.rev a),
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => -Q (Fin.rev a), fun a => by simp [hQ], ?_⟩,
    ⟨fun a b hab => neg_lt_neg (hanti (Fin.rev_lt_rev.mpr hab)), fun a => ?_⟩, ?_, ?_⟩
  · unfold dualPar
    rw [Finset.image_image]
    ext ⟨x, s⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply, Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨Fin.rev a, by simpa using ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨_, ha⟩
  · obtain ⟨z, hz⟩ := hint (Fin.rev a)
    refine ⟨-z - ((n : ℤ) - 1), ?_⟩
    push_cast
    linarith
  · rw [← hp]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)
  · rw [← hq]
    exact Finset.card_equiv Fin.revPerm (by intro i; simp)

theorem lamAt_strictAnti {R : Ranks} (h : HCParam R) : StrictAnti fun a : Fin R.r => lamAt h a := by
  intro a b hab
  have hab' : (a : ℕ) < b := hab
  have := lamAt_add_add_le h ((b : ℕ) - a) a (by omega)
  rw [show (a : ℕ) + ((b : ℕ) - a) = b by omega] at this
  have h1 : (1 : ℚ) ≤ (((b : ℕ) - a : ℕ) : ℚ) := by
    have : 1 ≤ (b : ℕ) - a := by omega
    exact_mod_cast this
  show lamAt h b < lamAt h a
  linarith

def sgA (R : Ranks) (a : ℕ) : Bool := decide (a < R.k - 1 ∨ Even (a - (R.k - 1)))

theorem holPar_kapW_eq {R : Ranks} (h : HCParam R) (p q : ℕ) (hpq : p + q = R.r) :
    holPar p q (kapW h p q) = Finset.univ.image fun a : Fin R.r => (lamAt h a, decide ((a : ℕ) < p)) := by
  have ho : Odd (p + q) := hpq ▸ odd_r R
  ext ⟨x, s⟩
  simp only [holPar, Finset.mem_image, Finset.mem_univ, true_and, Prod.mk.injEq, holEnt_kapW h p q ho]
  constructor
  · rintro ⟨a, rfl, rfl⟩
    cases a with
    | inl i => exact ⟨⟨i, by have := i.2; omega⟩, rfl, by simp⟩
    | inr c => exact ⟨⟨p + c, by have := c.2; omega⟩, rfl, by simp⟩
  · rintro ⟨a, rfl, rfl⟩
    by_cases hc : (a : ℕ) < p
    · exact ⟨Sum.inl ⟨a, hc⟩, rfl, by simp [hc]⟩
    · refine ⟨Sum.inr ⟨a - p, by have := a.2; omega⟩, ?_, by simp [hc]⟩
      simp only [Sum.elim_inr]
      rw [show p + ((a : ℕ) - p) = a by omega]

end Formalism.IndefR.Mult
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

theorem rder_zero (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    Rder θ V τ X (0 : GA D V → ℂ) = 0 := by
  funext g
  simp [Rder]

theorem rderC_zero (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (0 : GA D V → ℂ) = 0 := by
  simp [RderC, rder_zero]

theorem gelf_zero (τ : D.what₂.Tau) (k : ℕ) : gelf θ V τ k (0 : GA D V → ℂ) = 0 := by
  unfold gelf
  refine Finset.sum_eq_zero fun idx _ => ?_
  have h : ∀ l : List ((GA D V → ℂ) → GA D V → ℂ), (∀ f ∈ l, f 0 = 0) →
      l.foldr (fun f acc => f acc) 0 = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons f l ih =>
      rw [List.foldr_cons, ih (fun f' hf' => hl f' (by simp [hf']))]
      exact hl f (by simp)
  apply h
  intro f hf
  rw [List.mem_ofFn] at hf
  obtain ⟨a, rfl⟩ := hf
  exact rderC_zero θ V τ _

theorem foldr_rder_zero (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, ih]
    exact rder_zero θ V p.1 p.2

theorem isAutFunSm_zero : IsAutFunSm θ V (fun _ => 0) := {
  left _ _ _ := rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth _ _ _ _ _ := contDiff_const
  zfin := by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, fun τ k f hf => ?_⟩
    rw [Submodule.mem_bot] at hf
    subst hf
    rw [gelf_zero]
    exact Submodule.zero_mem _
  growth := by
    refine ⟨0, fun l _ x => ⟨0, fun g _ => ?_⟩⟩
    have h := foldr_rder_zero θ V l
    change ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) (0 : GA D V → ℂ)) (x * g)‖ ≤ _
    rw [h]
    simp }

theorem isCuspFun_zero : IsCuspFun V (fun _ => 0) := by
  intro r C _ μ 𝓕 _ _ g
  simp

variable {V} {S : D.what₂.Tau → SPar}

theorem isMultMap_zero (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) : IsMultMap θ M J χ 0 := {
  aut v := by
    show IsAutFunSm θ V (fun _ => 0)
    exact isAutFunSm_zero θ V
  cusp v := by
    show IsCuspFun V (fun _ => 0)
    exact isCuspFun_zero V
  lev v k _ g := by simp
  equiv τ g _ v w _ := by
    funext x
    simp [rTr]
  cont τ v x := by
    refine ⟨0, ⟨[], 0, by simp, fun w _ => by simp⟩, fun w => by simp⟩ }


variable (V) in
theorem rder_smul (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (c • φ) = c • Rder θ V τ X φ := by
  funext g
  simp only [Rder, Pi.smul_apply, smul_eq_mul]
  first
    | exact deriv_const_mul_field c
    | simp

variable (V) in
theorem foldr_rder_smul (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) (φ : GA D V → ℂ) :
    l.foldr (fun p f => Rder θ V p.1 p.2 f) (c • φ) = c • l.foldr (fun p f => Rder θ V p.1 p.2 f) φ := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih]
    exact rder_smul θ V p.1 p.2 c _


variable (V) in
theorem isAutFunSm_smul {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) (c : ℂ) : IsAutFunSm θ V (c • φ) := {
  left γ hγ g := by simp only [Pi.smul_apply, h.left γ hγ g]
  level := by
    obtain ⟨U, hU, hk⟩ := h.level
    exact ⟨U, hU, fun k hk1 hk2 g => by simp only [Pi.smul_apply, hk k hk1 hk2 g]⟩
  cont := h.cont.const_smul c
  smooth k τs Xs hX g := (h.smooth k τs Xs hX g).const_smul c
  zfin := by
    obtain ⟨W, hW, hφ, hg⟩ := h.zfin
    exact ⟨W, hW, W.smul_mem c hφ, hg⟩
  growth := by
    obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl x
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [foldr_rder_smul, Pi.smul_apply, norm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg c) }


variable (V) in
theorem isCuspFun_smul {φ : GA D V → ℂ} (h : IsCuspFun V φ) (c : ℂ) : IsCuspFun V (c • φ) := by
  intro r C hC μ 𝓕 hμ h𝓕 g
  simp only [Pi.smul_apply]
  rw [MeasureTheory.integral_smul, h r C hC μ 𝓕 hμ h𝓕 g, smul_zero]

theorem isMultMap_smul {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (hT : IsMultMap θ M J χ T) (c : ℂ) : IsMultMap θ M J χ (c • T) := {
  aut v := by
    show IsAutFunSm θ V (c • T v)
    exact isAutFunSm_smul θ V (hT.aut v) c
  cusp v := by
    show IsCuspFun V (c • T v)
    exact isCuspFun_smul V (hT.cusp v) c
  lev v k hk g := by
    simp only [_root_.smul_apply, Pi.smul_apply, smul_eq_mul, hT.lev v k hk g]
    ring
  equiv τ g hg v w hw := by
    rw [_root_.smul_apply, _root_.smul_apply, hT.equiv τ g hg v w hw]
    rfl
  cont τ v x := by
    obtain ⟨ℓ, ⟨L, C, hL, hC⟩, hℓ⟩ := hT.cont τ v x
    refine ⟨c • ℓ, ⟨L, ‖c‖ * C, hL, fun w hw => ?_⟩, fun w => ?_⟩
    · rw [LinearMap.smul_apply, norm_smul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC w hw) (norm_nonneg c)
    · simp only [LinearMap.smul_apply, _root_.smul_apply, Pi.smul_apply, hℓ w] }

end Formalism.IndefR.Mult

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PGoodOfRho
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem sum_eMat_eq {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)] [∀ s, Module K (Ws s)]
    (τ : ∀ s, Representation K G (Ws s))
    (hinj : ∀ s t, Formalism.IndefR.TransferLatticeStatement.charOf (τ s) = Formalism.IndefR.TransferLatticeStatement.charOf (τ t) → s = t) (hX : CharsX τ I.A.fam.X) :
    ∑ t, I.eMat (τ t) = ∑ g : G, (idemOf I.A.fam.X).coeff g • I.ρf g := by
  classical
  have hc : ∀ g : G, (idemOf I.A.fam.X).coeff g =
      ∑ χ ∈ I.A.fam.X, χ 1 / (Fintype.card G : K) * χ g⁻¹ := by
    intro g
    simp [idemOf, chiIdem, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finsetSum_apply,
      Finsupp.single_apply]
  simp only [eMat]
  rw [GoodPlacesAlt.sum_chars_eq τ I.A.fam.X hinj hX
    (fun χ => (χ 1 / (Fintype.card G : K)) • ∑ x : G, χ x⁻¹ • I.ρf x)]
  simp only [hc, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem iCg_cpt (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K) :
    I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) =
      I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x)) := by
  rw [CxData.iC_eq_comp, CxData.lin_uQ_cpt]
  rfl

theorem idemOf_fix {s : ℕ} (hok : I.A.fam.Ok s)
    (x : Fin ((I.A.fam.R I.A3.fam3.base3.μ0).dZ (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0)) → K) :
    ∑ g : G, (idemOf I.A.fam.X).coeff g •
        (I.A.fam.R I.A3.fam3.base3.μ0).r g ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x) =
      (I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x := by
  have hgood : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ = idemOf I.A.fam.X := by
    show idemOf I.A.fam.X * lvlIdem ⊥ 1 = _
    rw [level_idempotent_bot K G 1, mul_one]
  have hidem : goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ *
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ =
      goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ := by
    rw [hgood]
    exact (idempotent_central K G I.A.fam.X hok.irr).1
  have h : (I.A.fam.R I.A3.fam3.base3.μ0).S.gaOp (I.A.fam.R I.A3.fam3.base3.μ0).r
        (goodAt (I.A.fam.lvl ⊥ 1).X (I.A.fam.lvl ⊥ 1).P (I.A.fam.lvl ⊥ 1).ψ)
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x) =
      (I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x :=
    BlockDat.gaOp_fix (I.A.fam.R I.A3.fam3.base3.μ0) (I.A.fam.lvl ⊥ 1) hidem
      (((I.A.fam.R I.A3.fam3.base3.μ0).zE (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0)).mulVec x)
  rw [hgood] at h
  conv_rhs => rw [← h]
  simp only [CSD.gaOp, LinearMap.sum_apply, LinearMap.smul_apply]

theorem iCg_fix {s : ℕ} (hH : I.Hyp s)
    (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ I.A3.fam3.base3.μ0) → K) :
    ∑ g : G, I.A3.fam3.base3.v0.embedding ((idemOf I.A.fam.X).coeff g) •
        I.gE g (I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x)) =
      I.X.iC I.cg false I.A3.fam3.base3.μ0 (cpt I.A3.fam3.base3.v0.embedding x) := by
  have hq : ∀ (g : G) (f : I.A3.fam3.amb3.FR I.A3.fam3.base3.μ0),
      I.gE g (I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 f)) =
        I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 ((I.A.fam.R I.A3.fam3.base3.μ0).r g f)) :=
    fun g f => (hH.gequiv I.A3.fam3.base3.μ0 g f).symm
  have hq' : ∀ g : G, I.gE g (I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0
      ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x))) =
      I.X.Θ I.A3.fam3.base3.μ0 (I.X.jR I.A3.fam3.base3.μ0 ((I.A.fam.R I.A3.fam3.base3.μ0).r g
        ((I.A.fam.R I.A3.fam3.base3.μ0).toF (I.A.fam.lvl ⊥ 1) (I.X.zs.Z I.A3.fam3.base3.μ0) x))) := fun g => hq g _
  rw [I.iCg_cpt x]
  simp_rw [hq']
  conv_rhs => rw [← I.idemOf_fix hH.ok.ok2 x]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  erw [LinearMap.map_smulₛₗ, map_smul]
  first | done | rfl

theorem pGood_of_rho (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := by
  intro s hH hG hX
  rw [I.sum_eMat_eq τ hG.2.2.2 hX]
  obtain ⟨-, -, hρg⟩ := hρ s hH
  exact GoodPlacesAlt.sum_eq_one_of I.A3.fam3.base3.v0.embedding I.iCg hH.h2g.1 I.ρf (fun g => I.gE g) hρg
    (fun g => (idemOf I.A.fam.X).coeff g) (fun x => I.iCg_fix hH x)

theorem pGood_of (_hJt : I.PJt) (hρ : I.PRho) {S : Type} [Fintype S] {Ws : S → Type} [∀ s, AddCommGroup (Ws s)]
    [∀ s, Module K (Ws s)] [∀ s, FiniteDimensional K (Ws s)] (τ : ∀ s, Representation K G (Ws s)) : I.PGood τ := pGood_of_rho I hρ τ

end In3

end Formalism.IndefR.CxPass
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.WeilFull
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
  Formalism.IndefR.Fock.Sk MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.WeilFull

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SuppV (ε : AF D.host.F) (V : HSp D) (g : GA D V) : Prop :=
  ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = (mt V g - 1) i j

def UnrAtV (ε : AF D.host.F) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, (1 - algebraMap (AF D.host.F) (AE D) ε) * (x : AE D) = 1 - algebraMap (AF D.host.F) (AE D) ε →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def SphInertAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  S.rank ≠ T.rank → (Even S.rank ∨ Even T.rank) →
    ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
      IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)),
      Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
      (2 : 𝓞 D.host.F) ∉ v.asIdeal →
      (∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0) →
      UnrAtV ε χS → UnrAtV ε χT →
    ∀ (g : GA D S) (h : GA D T), SuppV ε S g → SuppV ε T h →
      Lev.finE S g ∈ Formalism.L2.DIV.St βS → Lev.finE T h ∈ Formalism.L2.DIV.St βT →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f → om (g, h) f = f

def RealAtO (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  LineAtExists D →
  ∀ (θ : InfFam D) sS sT BS BT (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (τ : D.what₂.Tau) (αS αT : ℚ), HasInfExp D χS τ αS → HasInfExp D χT τ αT →
    ∀ (XS : Matrix (Fin S.rank) (Fin S.rank) ℂ) (XT : Matrix (Fin T.rank) (Fin T.rank) ℂ),
      XS ∈ lieAt S τ → XT ∈ lieAt T τ →
        ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f →
          ∀ (P : MvPolynomial (FVar D T.rank S.rank) ℂ) (x : WO S T),
            HasDerivAt (fun t : ℝ => om (oneP θ S τ XS t, oneP θ T τ XT t) (pureTensorO ψ θ S T sS sT BS BT f P) x)
              (pureTensorO ψ θ S T sS sT BS BT f
                (quadOp τ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) P +
                  (halfTrJ (sS τ) (BS τ) XS (sT τ) (BT τ) XT (pS τ) (pT τ) + (αS : ℂ) * XT.trace -
                    (αT : ℂ) * XS.trace) • P) x) 0

structure IsWeilFull (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  datum : IsWeilDatumO ψ S T χS χT om
  inert : SphInertAtO ψ S T χS χT om
  real : RealAtO ψ S T χS χT om

def WeilExistsFull (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle),
    IsStdChar D ψ (-1) → IsHeckeChar D χS → IsHeckeChar D χT → ResEta D χS S.rank → ResEta D χT T.rank →
    ∃ om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ), IsWeilFull ψ S T χS χT om

def InertAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → SphInertAtO ψ S T χS χT om

def RealAllO (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → RealAtO ψ S T χS χT om

theorem weilExistsFull_of (h : AutomorphicFormsHyp.WeilExistsO D) (hi : InertAllO D) (hr : RealAllO D) : WeilExistsFull D := by
  intro ψ S T χS χT hψ hS hT hrS hrT
  obtain ⟨om, hom⟩ := h ψ S T χS χT hψ hS hT hrS hrT
  exact ⟨om, hom, hi ψ S T χS χT om hom, hr ψ S T χS χT om hom⟩

end Formalism.IndefR.WeilFull

end
end

