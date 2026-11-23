module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0300
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.LinksExistW
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatZOfTests
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeLevelIdempotentProductAndCentralProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRange

theorem range_sum_eq_eig {G M : Type} [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    (P : Subgroup G) (χ : P → ℂ) (E : G → ℂ) (k : ℂ) (hk : k ≠ 0) (h0 : ∀ g, g ∉ P → E g = 0)
    (h1 : ∀ g : P, E g * χ g = k) (hm : ∀ a b : P, χ (a * b) = χ a * χ b) :
    LinearMap.range (∑ g, E g • ρ g) = eig ρ P χ := by
  classical
  have hs : ∀ (p : P) (g : G), E g = χ p * E (p * g) := by
    intro p g
    by_cases hg : g ∈ P
    · have e1 := h1 ⟨g, hg⟩
      have e2 := h1 (p * ⟨g, hg⟩)
      rw [hm] at e2
      have hne : χ ⟨g, hg⟩ ≠ 0 := by
        intro h; rw [h, mul_zero] at e1; exact hk e1.symm
      apply mul_right_cancel₀ hne
      simp only [Subgroup.coe_mul] at e1 e2
      rw [e1, ← e2]; ring
    · have : (p : G) * g ∉ P := fun h => hg ((P.mul_mem_cancel_left p.2).1 h)
      rw [h0 g hg, h0 _ this, mul_zero]
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [mem_eig]
    intro p
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft (p : G)) (fun g => χ p • E g • ρ g y)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [hs p g, Equiv.coe_mulLeft, map_mul, Module.End.mul_apply, mul_smul]
  · intro x hx
    rw [mem_eig] at hx
    have hT : (∑ g, E g • ρ g) x = (∑ g : G, if g ∈ P then k else 0) • x := by
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_smul]
      refine Finset.sum_congr rfl fun g _ => ?_
      by_cases hg : g ∈ P
      · rw [if_pos hg, ← h1 ⟨g, hg⟩, mul_smul, ← hx ⟨g, hg⟩]
      · rw [if_neg hg, h0 g hg, zero_smul, zero_smul]
    have hne : (∑ g : G, if g ∈ P then k else 0) ≠ 0 := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      refine mul_ne_zero ?_ hk
      have : (Finset.univ.filter fun g : G => g ∈ P).Nonempty := ⟨1, by simp⟩
      exact_mod_cast this.card_pos.ne'
    refine ⟨(∑ g : G, if g ∈ P then k else 0)⁻¹ • x, ?_⟩
    rw [map_smul, hT, smul_smul, inv_mul_cancel₀ hne, one_smul]

theorem range_mul_eq_inf {M : Type} [AddCommGroup M] [Module ℂ M] (C T : Module.End ℂ M) (hC : C * C = C)
    (hc : C * T = T * C) : LinearMap.range (C * T) = LinearMap.range T ⊓ LinearMap.ker (C - LinearMap.id) := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨C y, ?_⟩, ?_⟩
    · rw [hc]; rfl
    · have : C (C (T y)) = C (T y) := by rw [← Module.End.mul_apply, hC]
      simp [this]
  · rintro _ ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, ?_⟩
    simpa [sub_eq_zero] using h

theorem op_comp {G H M : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup M] [Module ℂ M]
    (Φ : G ≃* H) (ρ : Representation ℂ G M) (e : H → ℂ) :
    GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) e = ∑ g, e (Φ g) • ρ g := by
  unfold GlobalTheory.BadShare.op
  rw [← Equiv.sum_comp Φ.toEquiv]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp

theorem tens_e_mul {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ * ∏ v, (L v).chi (γ v) = ∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹ := by
  unfold GlobalTheory.BadShare.tens
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  have := GlobalTheory.BadShare.Basic.chi_ne (L v) (γ v)
  simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_pos (h v)]
  field_simp

theorem tens_e_zero {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N)
    (γ : ι → GlobalTheory.BadShare.GG g N) (h : ¬ ∀ v, (L v).Mem (γ v)) :
    GlobalTheory.BadShare.tens (fun v => (L v).e) γ = 0 := by
  obtain ⟨v, hv⟩ := not_forall.1 h
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp only [GlobalTheory.BadShare.Lev.e, GlobalTheory.BadShare.eps, if_neg hv])

theorem prod_card_ne {g N : ℕ} [Fact g.Prime] {ι : Type} [Fintype ι] (L : ι → GlobalTheory.BadShare.Lev g N) :
    (∏ v, (Nat.card {u // (L v).Mem u} : ℂ)⁻¹) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.2 fun v _ => inv_ne_zero ?_
  haveI : Nonempty {u // (L v).Mem u} := ⟨⟨1, GlobalTheory.BadShare.Basic.mem_one (L v)⟩⟩
  exact_mod_cast Nat.card_pos.ne'

theorem ranges : ∀ (g₁ g₂ N : ℕ) [Fact g₁.Prime] [Fact g₂.Prime] (ι₁ ι₂ G M : Type) [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂] [Group G] [Fintype G] [AddCommGroup M] [Module ℂ M] (Φ : G ≃* (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N)) (L₁ : ι₁ → GlobalTheory.BadShare.Lev g₁ N) (L₂ : ι₂ → GlobalTheory.BadShare.Lev g₂ N) (P : Subgroup G) (χ : P → ℂ) (ρ : Representation ℂ G M) [Fintype ((ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N))] (c : (ι₁ → GlobalTheory.BadShare.GG g₁ N) × (ι₂ → GlobalTheory.BadShare.GG g₂ N) → ℂ), (∀ g : G, g ∈ P ↔ (∀ v, (L₁ v).Mem ((Φ g).1 v)) ∧ ∀ v, (L₂ v).Mem ((Φ g).2 v)) → (∀ g : P, χ g = (∏ v, (L₁ v).chi ((Φ g).1 v)) * ∏ v, (L₂ v).chi ((Φ g).2 v)) → GlobalTheory.BadShare.conv c c = c → (∀ a, GlobalTheory.BadShare.conv c a = GlobalTheory.BadShare.conv a c) → LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ ∧ LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.conv c (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e)))) = eig ρ P χ ⊓ LinearMap.ker ((∑ g : G, c (Φ g) • ρ g) - LinearMap.id) := by
  intro g₁ g₂ N _ _ ι₁ ι₂ G M _ _ _ _ _ _ _ _ Φ L₁ L₂ P χ ρ _ c hP hχ hcc hc
  have key : LinearMap.range (GlobalTheory.BadShare.op (M := M) (ρ.comp Φ.symm.toMonoidHom) (GlobalTheory.BadShare.tens2 (GlobalTheory.BadShare.tens fun v => (L₁ v).e) (GlobalTheory.BadShare.tens fun v => (L₂ v).e))) = eig ρ P χ := by
    rw [op_comp]
    refine range_sum_eq_eig ρ P χ _ _ (mul_ne_zero (prod_card_ne L₁) (prod_card_ne L₂)) ?_ ?_ ?_
    · intro g hg
      rw [hP, not_and_or] at hg
      unfold GlobalTheory.BadShare.tens2
      rcases hg with h | h
      · rw [tens_e_zero _ _ h, zero_mul]
      · rw [tens_e_zero L₂ _ h, mul_zero]
    · intro g
      obtain ⟨h1, h2⟩ := (hP g).1 g.2
      rw [hχ, ← tens_e_mul L₁ _ h1, ← tens_e_mul L₂ _ h2]
      unfold GlobalTheory.BadShare.tens2
      ring
    · intro a b
      obtain ⟨a1, a2⟩ := (hP a).1 a.2
      obtain ⟨b1, b2⟩ := (hP b).1 b.2
      rw [hχ, hχ, hχ]
      simp only [Subgroup.coe_mul, map_mul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply]
      simp only [fun v => GlobalTheory.BadShare.Basic.chi_mul (L₁ v) (a1 v) (b1 v),
        fun v => GlobalTheory.BadShare.Basic.chi_mul (L₂ v) (a2 v) (b2 v), Finset.prod_mul_distrib]
      ring
  refine ⟨key, ?_⟩
  rw [GlobalTheory.BadShare.Basic.op_conv, range_mul_eq_inf, key, op_comp]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hcc]
  · rw [← GlobalTheory.BadShare.Basic.op_conv, hc, GlobalTheory.BadShare.Basic.op_conv]

end GlobalTheory.LevRange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatOfOneMapOverL
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField.Read

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mult_inv {V : HSp D} {S : D.what₂.Tau → _} (θ) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) {Φ : MMap M}
    (hΦ : Φ ∈ Mult θ M J χ) (v : M.Vec) : ∀ γ ∈ GQ V, ∀ g, Φ v (γ * g) = Φ v g := by
  intro γ hγ g
  induction hΦ using Submodule.span_induction with
  | mem x hx => exact (hx.aut v).left γ hγ g
  | zero => rfl
  | add x y _ _ hx hy => simp only [_root_.add_apply, Pi.add_apply, hx, hy]
  | smul a x _ hx => simp only [_root_.smul_apply, Pi.smul_apply, hx]

theorem eq_of_out {W : HSp D} {Φ Ψ : GA D W → ℂ} (hΦ : ∀ γ ∈ GQ W, ∀ g, Φ (γ * g) = Φ g)
    (hΨ : ∀ γ ∈ GQ W, ∀ g, Ψ (γ * g) = Ψ g) (h : ∀ q : AutQ W, Φ q.out = Ψ q.out) : Φ = Ψ := by
  funext g
  let q : AutQ W := Quotient.mk _ g
  have hr : g * q.out⁻¹ ∈ GQ W := QuotientGroup.rightRel_apply.1 (Quotient.exact (Quotient.out_eq q))
  have h1 := hΦ _ hr q.out
  have h2 := hΨ _ hr q.out
  rw [inv_mul_cancel_right] at h1 h2
  rw [h1, h2, h q]

theorem ev_sum {L H Y : Type} [Field L] [AddCommGroup H] [Module ℂ H] [AddCommGroup Y] [Module L Y] {σ : L →+* ℂ}
    (j : Y →ₛₗ[σ] H) {V : HSp D} {S : D.what₂.Tau → _} {M : DSModel V S} (e : H →ₗ[ℂ] MMap M) (v : M.Vec) (g : GA D V) {m : ℕ}
    (a : Fin m → L) (y : Fin m → Y) : e (j (∑ l, a l • y l)) v g = ∑ l, σ (a l) * e (j (y l)) v g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, _root_.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smulₛₗ, map_smul]
  rfl

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem ev_base (fw : FWTie T R κ v₀) (hev : fw.Evaluates) {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat T.toCore R i Tp tup) (f : Cu T κ i) (h : GA D (Wc D i)) :
    (R.HW i (sg0 D A)).e (fw.jK i (sg0 D A) f) (v₀ i (sg0 D A)) h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
        O.phi (T.cE ((i : ℕ) + 1) O.s0) (f : T.R ((i : ℕ) + 1)) h := by
  have e : res T (sg0 D A) = O.s0 :=
    ((congrArg (res T) (show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0)).trans
      (res_embLL T fw.alg_eq fw.laws.pins.2.2.1)).trans (sOv_eq T.toCore O.c' O.hle).symm
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := (congrArg (T.V ((i : ℕ) + 1)) e).trans O.hV
  have h1 := hev i (sg0 D A) (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) hV f
  have key : ∀ (σ σ' : T.Q.c.F →+* ℂ) (_ : σ' = σ) (W : HSp D) (hV : T.V ((i : ℕ) + 1) σ = W)
      (hV' : T.V ((i : ℕ) + 1) σ' = W) (g : GA D W), phiC T hV' (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) g =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * adel W (castDict hV (T.dict ((i : ℕ) + 1) σ))
        (muPin W (castDict hV (T.dict ((i : ℕ) + 1) σ)) (castDict hV (T.mu ((i : ℕ) + 1) σ)) (T.cE ((i : ℕ) + 1) σ))
        (rdU (T.U ((i : ℕ) + 1) σ) (f : T.R ((i : ℕ) + 1))) g := by
    intro σ σ' e W hV hV' g
    subst e
    subst hV
    rfl
  exact (congrFun h1 h).trans (key _ _ e _ O.hV hV h)


set_option maxHeartbeats 1000000 in
theorem exists_comb {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec} {ι x₀} {ph : ℂ}
    (hn : κ.n = (Vc D i).rank) (O : OMDat T.toCore R i T0 id) (hP : O.Pins κ v ι x₀)
    (hrow : O.OneMapOf κ v (T.cE ((i : ℕ) + 1) O.s0) ph) (t : T0) (y : A.fam.amb.FL i t) :
    ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, ∃ (m : ℕ) (as : Fin m → O.c'.F) (fs : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      ∀ q : AutQ (Wc D i), ph * R.thF i t (R.jV i t y) v q.out =
        ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
          O.phi (T.cE ((i : ℕ) + 1) O.s0) (fs l : T.R ((i : ℕ) + 1)) q.out) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  have aux1 := h1 t
  obtain ⟨ze, a1, -, h1⟩ := aux1
  have aux2 := (hP.tuple t).reps
  obtain ⟨h, J', -, p2, p3, p4⟩ := aux2
  have aux3 := p2 y
  obtain ⟨x, hx⟩ := aux3
  have e := p3 _ x hx
  have aux4 := h1 x ((p4 x).2 ⟨y, hx⟩)
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := aux4
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h4 := h2 f hs hf'
  rw [← hn] at hf
  have aux5 := hC _ _ f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := aux5
  have aux6 := hP.lift.lev z
  obtain ⟨k, hk, -⟩ := aux6
  have h5 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  refine ⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩
  have h6 : ph * R.thF i t (R.jV i t y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) :=
    (congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)
  rw [h6, h5]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring


set_option maxHeartbeats 1000000 in
theorem ratAt_of_oneMap (fw : FWTie T R κ v₀) {ph : ℂ} {i : Fin D.R.m} (hW : R.models_HW) (hP : R.IsThP) (hU : R.LUnif)
    (hev : fw.Evaluates) (hinj : EvInj T R v₀) (h : OneMapOverL T R κ v₀ ph i) (t : T0) : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t := by
  intro x₀
  obtain ⟨O, hF, hpin, hrow⟩ := h
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have aux7 := exists_comb hn O hpin hrow t x₀
  obtain ⟨ze, hze, m, as, fs, hq⟩ := aux7
  have hs : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have ha : ∀ l, ∃ a : D.what₂.LL, sg0 D A a = ze * (as l : ℂ) := fun l => by
    have aux8 := AlgHom.mem_fieldRange.1 (mul_mem hze (hF.le (as l).2))
    obtain ⟨a, ha⟩ := aux8
    exact ⟨a, (RingHom.congr_fun hs a).trans ha⟩
  choose a ha using ha
  have hmem := (hW i (sg0 D A)).2.1.ge (hP.thF_mem i t (R.jV i t x₀))
  obtain ⟨w, hw⟩ := hmem
  have hinv : ∀ u : (R.HW i (sg0 D A)).H, ∀ γ ∈ GQ (Wc D i), ∀ g,
      evAt R i _ (v₀ i _) u (γ * g) = evAt R i _ (v₀ i _) u g := fun u =>
    mult_inv R.θ _ _ _ ((hW i _).2.1.le (LinearMap.mem_range_self _ u)) _
  have e0 : (R.HW i (sg0 D A)).e (ph • w) = ph • R.thF i t (R.jV i t x₀) :=
    (map_smul (R.HW i (sg0 D A)).e ph w).trans (congrArg (ph • ·) hw)
  have key : (R.FW i).j (sg0 D A) (∑ l, a l • ((fw.e i (fs l) : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) = ph • w := by
    refine hinj i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1) (eq_of_out (hinv _) (hinv _) fun q => ?_)
    have e1 : evAt R i _ (v₀ i _) (ph • w) q.out = ph * R.thF i t (R.jV i t x₀) (v₀ i _) q.out :=
      congrArg (fun Φ : MMap (R.MW i (sg0 D A)) => Φ (v₀ i _) q.out) e0
    refine (ev_sum _ _ _ _ _ _).trans (Eq.trans ?_ ((hq q).symm.trans e1.symm))
    exact Finset.sum_congr rfl fun l _ => congrArg₂ (· * ·) (ha l) (ev_base fw hev O (fs l) q.out)
  have h1 := (congrArg (R.HW i (sg0 D A)).e key).trans e0
  exact ⟨_, h1, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.proj_clause R i ph t hP.thG (hW i _).1 (hU i _).2.2 _ _ h1⟩

theorem rat_of_oneMapOverL : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T R κ v₀) (ph : ℂ) (i : Fin D.R.m), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → R.IsThP → R.LUnif → fw.Evaluates → EvInj T R v₀ → GlobalTheory.TwistField.OneMapOverL T R κ v₀ ph i → ∀ t : T0, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.RatAt R i ph t :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ fw _ _ _ _ hM hP hU hev hinj h t => ratAt_of_oneMap fw hM.HW hP hU hev hinj h t

end GlobalTheory.TwistField.Read
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.AdSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

def RealScal (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (a : GA D T) (z : ℂ) : Prop :=
  ∀ φ : TF S.rank C.g, SW.IsSB φ → om (1, a) (C.Th (C.xB B) φ) = z • C.Th (C.xB (C.mvB a B)) φ

def HolUpTo (C : Ctx S T) (B : C.Bas) (la : Wt C.X.Ψ T.rank) (z φ : GA D T → ℂ) : Prop :=
  ∀ g : GA D T, ∃ Q : Frame C.X.Ψ T.rank → ℂ, DifferentiableOn ℂ Q C.X.dom ∧
    (∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, Q (rmul x b) = bchar la b * Q x) ∧
    ∀ a ∈ GinfC T, φ (g * a) = z a * Q (C.xB (C.mvB a B))

def detPow (θ : InfFam D) (V : HSp D) (m : D.what₂.Tau → ℤ) (a : GA D V) : ℂ :=
  ∏ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V a)).det ^ m ρ

def torAt (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau)
    (t : Fin V.rank → ℝ) : GA D V :=
  atTau θ V ρ (B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹)

def LowKilled (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : Prop :=
  HolRead.SmoothReal θ V φ ∧ ∀ ρ (c d : Fin V.rank), d < c → RderC θ V ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) φ = 0

def revPos {n : ℕ} (p : ℕ) (a : Fin n) : Fin n :=
  if h : (a : ℕ) < p ∧ p ≤ n then ⟨p - 1 - a, by omega⟩ else a

theorem revPos_revPos {n : ℕ} (p : ℕ) (a : Fin n) : revPos p (revPos p a) = a := by
  by_cases h : (a : ℕ) < p ∧ p ≤ n
  · have h' : p - 1 - (a : ℕ) < p ∧ p ≤ n := ⟨by omega, h.2⟩
    ext
    simp only [revPos, dif_pos h, Fin.val_mk, dif_pos h']
    omega
  · simp only [revPos, dif_neg h]

def revB {ι : Type} {n : ℕ} (p : ℕ) (B : ι → Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ).submatrix id (revPos p)

def thetaSet (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (u : WO S T → ℂ)
    (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) : Set (GA D T → ℂ) :=
  {φ | ∃ (h : GA D S) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' ∧
    φ = fun g => om (h, g) (C.fvec B u Q) 0}

def ContT (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun g : GA D T => om (1, g) f w

abbrev reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : HSp D := StdFrame.reframe S b

def frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  S.frame.toMatrix b

def frPinv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  b.toMatrix S.frame

def reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO (reS S b) T) : WO S T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))

def reF (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : (WO S T → ℂ) →ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (reW S T b)

theorem reF_apply (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) (x : WO (reS S b) T) :
    reF S T b f x = f (reW S T b x) := rfl

theorem reF_zero (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) : reF S T b f 0 = f 0 := by
  rw [reF_apply]
  congr 1
  exact Matrix.zero_mul _

end GlobalTheory.AdSpan

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestComplexSideOfHilbertModels
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.IndefR.NX Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models

theorem rowTest_toCx3 : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.RowTestModel R.toRealDat → Formalism.IndefR.Rat.RowTest (R.toCx3 F) := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F h
  obtain ⟨n, ψ, hinj, hrat⟩ := (GlobalTheory.IndefiniteRowSideFullHecke.RationalRowTestKernel.test_tw_iff (E := R.HE.H) (twAt D.what₂.embLL A3.A.v0) R.emb0 (ι := T0)
    (X := fun t => A3.A.fam.amb.FR t) fun t x => R.Th t (R.jX t x)).2 h
  exact ⟨n, ψ, hinj, fun t i x => hrat t x i⟩

end GlobalTheory.Twist.rowTest_complexSide_of_hilbert_models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalConjBaseFacts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem scalConj_base_facts : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (s : ℕ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PHecke F → R.PGUnit F → R.PGEquiv F → (R.toCx3 F).zs.InBlock → Formalism.IndefR.Rat.RowTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTest (R.toCx3 F) → Formalism.IndefR.Rat.LiftTestB (R.toCx3 F) false → (∀ hW, HeckeIntertwiningLifts A3 (R.toCx3 F) hW → U2.OntoC A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 hW) → 0 < R.kap → (∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.toRealDat.LUnif → R.PLevW F → R.PThmA → (R.toCx3 F).PartsW false → (R.toCx3 F).H5 F.cr false ∧ (R.toCx3 F).RATth F.cr false ∧ (R.toCx3 F).H3W F.cr false ∧ (lv (F.fc (R.toCx3 F).zs) false).Proviso := by
  intro D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F s hOk hsep hC hR hL hH hU hE hblk hrt hlt hltb honto hk hl hun hlev hA hsum
  have kR := RealDat3.kFormR_of (F := F) hC.base.models
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jR := RealDat3.jIsoR_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have thR := hH.1.choose_spec
  have thL := hH.2.choose_spec
  have st : (R.toCx3 F).zs.Stable := CxData.cutStable (R.toCx3 F) kR kL
    (Formalism.IndefR.CxPass.definite_kernel_stable kR hE.1 thR) (Formalism.IndefR.CxPass.lift_kernel_stable kL hE.2 thL)
    (definite_adjoint_closed hOk hR kR jR) (lift_adjoint_closed hOk hL kL jL)
  have wf := A3.side_well_formed hOk F.P0 F.ψ0 (R.toCx3 F).zs st hblk hsep
  have rz : (R.toCx3 F).RatZ := Formalism.IndefR.Rat.ratZOfTests (R.toCx3 F) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) kR kL jR jL hrt hlt
  have eig0 := (U2.unitary_two_package A3 (R.toCx3 F) s F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc hH.2.choose (R.gWx F) hOk kR kL jR jL hrt hlt hL thL hU.2 hE.2 hlev hsum (honto _ thL)).1
  have kf := RealDat3.kForm_of (F := F) hun false
  let X' : CxData A3.fam3.amb3 := { R.toCx3 F with lam := fun j t p _ => (R.toCx3 F).lam j t p A3.fam3.base3.v0 }
  have h5 : (R.toCx3 F).H5 F.cr false := (CxData.cutLifts X' (crdOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc) (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false wf
    ⟨fun _ => hk, fun j t p _ => hl j t p, RealDat.nP_pos⟩ kf
    (lift_isometry_of_norms hOk jL ⟨rfl, rfl⟩ false) (lift_coordinates_in_subspaces (R.toCx3 F) false) (lift_coordinates_in_good_part_family (R.toCx3 F) false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hOk kL jL rz hU.2 hE.2 false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hOk kL jL rz hU.2 hE.2 hlev)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hOk kL jL hU.2 hE.2 hlev)
    (RealDat3.thmAop_of hC.phase hA false) hsum).1
  exact ⟨h5, Formalism.IndefR.Rat.ratThOfLiftTest (R.toCx3 F) _ false hltb h5 kf (RealDat3.ewNorm false) (RealDat.nP_pos false),
    lift_equivariance_of_primitive F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc kL st hOk thL false,
    proviso_of_lift_eigenvalues A3 (R.toCx3 F) hOk (fun j => hL j A3.A.fam.μ0) F.P0 F.ψ0 eig0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzIsometryInnerProductEq
section
open MeasureTheory

namespace GlobalTheory

theorem complex_mul_conj_eq_polarization (a b : ℂ) :
    a * starRingEnd ℂ b = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((‖a + Complex.I ^ k * b‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Complex.sq_norm]
  apply Complex.ext <;>
    simp [Complex.normSq_apply, pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem schwartz_integrable_sq_norm_of_addHaar {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (h : SchwartzMap V ℂ) :
    Integrable (fun x => ‖h x‖ ^ 2) μ := by
  have := (h.memLp 2 μ).integrable_norm_pow (by norm_num)
  simpa using this

theorem schwartz_integral_mul_conj_eq_polarization {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (u v : SchwartzMap V ℂ) :
    ∫ x, u x * starRingEnd ℂ (v x) ∂μ = (1 / 4 : ℂ) * ∑ k ∈ Finset.range 4,
      Complex.I ^ k * ((∫ x, ‖(u + (Complex.I ^ k) • v) x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  simp_rw [complex_mul_conj_eq_polarization (u _)]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    congr 1
    rw [← integral_complex_ofReal]
    simp [smul_eq_mul]
  · intro k _
    refine Integrable.const_mul ?_ _
    have := (schwartz_integrable_sq_norm_of_addHaar μ (u + (Complex.I ^ k) • v)).ofReal (𝕜 := ℂ)
    simpa using this

theorem schwartz_L2_isometry_preserves_inner {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) :
    (∀ f, ∫ x, ‖T f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ f g : SchwartzMap V ℂ, ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ = ∫ x, f x * starRingEnd ℂ (g x) ∂μ := by
  intro hT f g
  rw [schwartz_integral_mul_conj_eq_polarization, schwartz_integral_mul_conj_eq_polarization]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← map_smul, ← map_add (f := _), hT]

end GlobalTheory
end

