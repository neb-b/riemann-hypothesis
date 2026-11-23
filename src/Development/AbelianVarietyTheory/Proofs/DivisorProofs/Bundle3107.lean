module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0823
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1851
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvExp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ESDual

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}}

def scaleTate {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q} {w : ℕ → Q → Q → kˣ → Prop}
    (I : TateIsoO D k Q act w) (e : ℕ) : TateIsoO D k Q act w where
  ζ n := I.ζ n ^ ((p ^ e) ^ 2)
  ζ_prim n hn hp := (I.ζ_prim n hn hp).pow_of_coprime _ ((hp.symm.pow_left e).pow_left 2)
  ζ_pow n m hn hm h := by rw [pow_right_comm, I.ζ_pow n m hn hm h]
  ev n x := I.ev n (p ^ e • x)
  add n x y := by rw [smul_add, I.add]
  lin n c x := by rw [smul_comm, I.lin]
  ker n hn hp x := by
    rw [I.ker n hn hp]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • y + v • x, ?_⟩
      rw [smul_add, smul_comm n u, ← hy, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
        ← add_smul, huv, one_smul]
    · rintro ⟨y, rfl⟩
      exact ⟨p ^ e • y, smul_comm _ _ _⟩
  onto n hn hp q := by
    rw [I.onto n hn hp]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hp.symm.pow_left e)
      refine ⟨u • x, ?_⟩
      have e1 : x = p ^ e • u • x + n • v • x := by
        rw [smul_comm _ u, smul_comm n v, ← natCast_zsmul x, ← natCast_zsmul x, smul_smul, smul_smul,
          ← add_smul, huv, one_smul]
      have e2 := (I.ker n hn hp (n • v • x)).2 ⟨_, rfl⟩
      conv_rhs => rw [e1, I.add, e2, _root_.mul_one]
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  tower n m hn hm h x := I.tower n m hn hm h _
  isom n hn hp x y := by
    have h := I.isom n hn hp (p ^ e • x) (p ^ e • y)
    have e1 : (2 * D.EF (p ^ e • x) (p ^ e • y) : ℤ) = (((p ^ e) ^ 2 : ℕ) : ℤ) * (2 * D.EF x y) := by
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      push_cast
      ring
    rw [e1, zpow_mul, zpow_natCast] at h
    exact h

def scale {s : S ⟶ Sp R} (o : Obj b N s) (e : ℕ) {s' : S ⟶ Sp R} (h : s = s') : Obj b N s' where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie := h ▸ o.lie
  lieRank := h ▸ o.lieRank
  eta x := o.eta (p ^ e • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, o.eta_ker]
  geom k _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom k x β (h ▸ hx)
    exact ⟨scaleTate I e, fun y => hI _⟩

theorem eta_nsmul {s : S ⟶ Sp R} (o : Obj b N s) (n : ℕ) (x : D.La) : o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

theorem eta_congr {s : S ⟶ Sp R} (o : Obj b N s) {n : ℕ} (hn : n ≡ 1 [MOD N]) (hn0 : 0 < n) (x : D.La) :
    o.eta (n • x) = o.eta x := by
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hn0).1 hn.symm
  have : n = 1 + N * k := by omega
  rw [this, add_smul, one_smul, mul_smul, o.eta_add, o.eta_ker, _root_.mul_one]

theorem exists_inv_exp (hN : 0 < N) (hp : N.Coprime p) (e : ℕ) : ∃ f : ℕ, p ^ (e + f) ≡ 1 [MOD N] := by
  refine ⟨e * (N.totient - 1), ?_⟩
  have h1 : 1 ≤ N.totient := Nat.totient_pos.2 hN
  have : e + e * (N.totient - 1) = N.totient * e := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h1
    rw [hm]; simp; ring
  rw [this, pow_mul]
  simpa using (Nat.ModEq.pow_totient hp.symm).pow e

def idMap {s : S ⟶ Sp R} (o : Obj b N s) : ObjMap o o (𝟙 S) where
  φ := 𝟙 _
  φ₂ := 𝟙 _
  cart := GlobalTheory.SiegLower.isGrpPullback_id o.A
  sq := ⟨by simp, by simp⟩
  act c := by simp
  pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB
  eta y := by simp

def compMap {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ObjMap o₁ o₃ (f ≫ g) where
  φ := h₁.φ ≫ h₂.φ
  φ₂ := h₁.φ₂ ≫ h₂.φ₂
  cart := h₁.cart.comp h₂.cart
  sq := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  act c := by rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  pol := by
    have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
    have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
      LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
    exact LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  eta y := by rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]

theorem pow_left_comm {S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : ℕ) :
    ((𝟙 A') ^ c).left ≫ φ = φ ≫ ((𝟙 A) ^ c).left := by
  let u : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk φ h.1.w
  have key : ∀ n : ℕ, (u ^ n).left = ((𝟙 A') ^ n).left ≫ φ := by
    intro n
    induction n with
    | zero =>
      let v : Over.mk (A'.hom ≫ f) ⟶ A := Over.homMk ((1 : A' ⟶ A').left ≫ φ) (by
        rw [Category.assoc, h.1.w, Over.w_assoc]; rfl)
      have h1 := h.2 A' 1 1 v v rfl rfl
      rw [_root_.mul_one] at h1
      have h2 : v = 1 := mul_eq_left.1 (Over.OverMorphism.ext h1 : v * v = v)
      rw [pow_zero, pow_zero, ← h2]; rfl
    | succ n ih =>
      rw [pow_succ, pow_succ]
      exact h.2 A' _ _ _ _ ih (Category.id_comp _).symm
  rw [← key]
  have : u ^ c = u ≫ (𝟙 A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
  rw [this]; rfl

theorem square_dual {S' : Scheme.{0}} {A B : Over S} {A' B' : Over S'} [GrpObj A] [GrpObj A'] [GrpObj B'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (hB : IsAbelianScheme B') (φ' : B'.left ⟶ B.left) {c : ℕ}
    (hc : 0 < c) {ψ : A ⟶ B} {χ : B ⟶ A} {ψ' : A' ⟶ B'} {χ' : B' ⟶ A'} (h₁ : ψ ≫ χ = (𝟙 A) ^ c)
    (h₂ : ψ' ≫ χ' = (𝟙 A') ^ c) (h₃ : χ' ≫ ψ' = (𝟙 B') ^ c) (sq : φ ≫ ψ.left = ψ'.left ≫ φ') :
    φ' ≫ χ.left = χ'.left ≫ φ := by
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S' B' hB c hc
  haveI : Epi ((𝟙 B') ^ c).left := Flat.epi_of_flat_of_surjective _
  haveI : Epi (χ'.left ≫ ψ'.left) := by rw [← Over.comp_left, h₃]; infer_instance
  haveI : Epi ψ'.left := epi_of_epi χ'.left ψ'.left
  rw [← cancel_epi ψ'.left, ← Category.assoc, ← sq, Category.assoc, ← Over.comp_left, h₁, ← pow_left_comm h,
    ← h₂, Over.comp_left, Category.assoc]


open GlobalTheory.BirigidPow GlobalTheory.CechPic in
theorem val_adj {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S} (x : T ⟶ o'.A) (y : T ⟶ o.A) :
    BirigidPow.val o'.isLB x (y ≫ ψ) = BirigidPow.val o.isLB (x ≫ ψ') y := by
  have hc := hψ.pos
  obtain ⟨-, hm, -, -, ⟨hP⟩, -⟩ := hψ
  have nat : ∀ {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (G2 A).left} (hP : P.IsLB) {U V : Over S} (r : U ⟶ V)
      (x y : V ⟶ A), pull r.left (BirigidPow.val hP x y) = BirigidPow.val hP (r ≫ x) (r ≫ y) := by
    intro A _ _ P hP U V r x y
    rw [BirigidPow.val, BirigidPow.val, ← pull_comp, ← Over.comp_left, comp_lift]
  have hsq : ∀ {U : Over S} (x y : U ⟶ o.A), BirigidPow.val o'.isLB (x ≫ ψ) (y ≫ ψ) = c • BirigidPow.val o.isLB x y := by
    intro U x y
    have hL : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
    have e := (cls_eq_iff hL (pull_isLB o'.isLB _)).2 hP
    rw [BirigidPow.cls_lbPow o.isLB, cls_pull o'.isLB _ (pull_isLB o'.isLB _)] at e
    have e' := congrArg (pull (lift x y).left) e
    rw [map_nsmul] at e'
    refine Eq.trans ?_ e'.symm
    have := nat o'.isLB (lift x y) (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)
    rw [lift_fst_assoc, lift_snd_assoc] at this
    exact this.symm
  obtain ⟨hfl, hsu, hqc⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c hc
  have H : BirigidPow.val o'.isLB (snd o.A o'.A) (fst o.A o'.A ≫ ψ) - BirigidPow.val o.isLB (snd o.A o'.A ≫ ψ') (fst o.A o'.A) = 0 := by
    refine GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc _ ?_ ?_
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, MonObj.one_comp, val_one_right _ o'.rig₂,
        val_one_right _ o.rig₂, sub_zero]
    · rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      conv_lhs => rw [← h₂, ← Category.assoc, hsq]
      rw [← val_pow_left o.isLB o.ab o.ample o.rig₁ o.rig₂, MonObj.comp_pow, Category.comp_id, MonObj.pow_comp]
  have := congrArg (pull (lift y x).left) H
  rw [map_sub, nat, nat, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, map_zero, sub_eq_zero] at this
  exact this


open GlobalTheory.BirigidPow GlobalTheory.CechPic in
theorem dual_clauses {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A} (hψ : IsPIsog c o o' ψ)
    {ψ' : o'.A ⟶ o.A} [IsMonHom ψ'] (h₁ : ψ ≫ ψ' = (𝟙 o.A) ^ c) (h₂ : ψ' ≫ ψ = (𝟙 o'.A) ^ c) :
    (∀ a : D.O, o'.act.act a ≫ ψ' = ψ' ≫ o.act.act a) ∧ (∀ x, o.eta (c • x) = o'.eta x ≫ ψ') ∧
      Nonempty (LBIso (Hecke.lbPow o'.P c) (o.P.pull (sq2 ψ'))) := by
  have hc := hψ.pos
  refine ⟨fun a => ?_, fun x => ?_, ⟨?_⟩⟩
  · haveI := GlobalTheory.UPel.HT.MulEpi.epi_pow_of_isAbelianScheme S o'.A o'.ab c hc
    haveI : Epi (ψ' ≫ ψ) := by rw [h₂]; infer_instance
    haveI : Epi ψ := epi_of_epi ψ' ψ
    haveI := o.act.hom a
    rw [← cancel_epi ψ, ← Category.assoc, ← hψ.2.2.1, Category.assoc, h₁, ← Category.assoc, h₁, MonObj.comp_pow,
      MonObj.pow_comp, Category.comp_id, Category.id_comp]
  · rw [hψ.2.2.2.1, Category.assoc, h₁, MonObj.comp_pow, Category.comp_id, eta_nsmul]
  · have hL : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb o'.isLB _ _
    refine (cls_eq_iff hL (pull_isLB o.isLB _)).1 ?_
    rw [BirigidPow.cls_lbPow o'.isLB, cls_pull o.isLB _ (pull_isLB o.isLB _)]
    change _ = BirigidPow.val o.isLB (fst o'.A o'.A ≫ ψ') (snd o'.A o'.A ≫ ψ')
    rw [← val_adj hψ h₂, Category.assoc, h₂, MonObj.comp_pow, Category.comp_id,
      val_pow_right o'.isLB o'.ab o'.ample o'.rig₁ o'.rig₂, BirigidPow.val, lift_fst_snd, Over.id_left, pull_id]

end GlobalTheory.UPel.HT.ESDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfStep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLift

theorem ker_factor_sq {R : Type} [CommRing R] (J : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) :
      R ⧸ J ^ (e + 1 + 1) →+* R ⧸ J ^ (e + 1)) ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff]
  refine Ideal.mul_le.2 fun x hx y hy => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx hy
  rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h := Ideal.mul_mem_mul hx hy
  rw [← pow_add] at h
  exact Ideal.pow_le_pow_right (by omega) h

end GlobalTheory.MumLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalCutAngehrnSiuInductionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logCanonical_cut_angehrnSiu_induction : GlobalTheory.Published.Principalisation → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → 1 ≤ n →
    letI := algebraΓOfHom p;
    ∀ (Δ : X → ℚ) (r : ℕ) (N₀ : LB X) (x : X) (c : ℕ → ℝ),
      IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < r → N₀.IsLB → IsNef ℂ N₀ → IsBig ℂ N₀ →
      IsClosed ({x} : Set X) → (∀ e ∈ Finset.Icc 1 n, 0 < c e) →
      (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e →
        topologicalKrullDim (Z : Set X) = e →
        c e ^ e < (interNumRed ℂ Z fun _ : Fin e => N₀ : ℝ) / (r : ℝ) ^ e) →
      ∃ A : CartierDiv X, IsAmpleLB (toLB A) ∧ ∀ j, j < n → ∃ (j' : ℕ) (lam μ : ℚ) (m' : ℕ) (D₀ : CartierDiv X),
        j' ≤ j ∧ 0 < m' ∧ D₀.Eff ∧ 0 < μ ∧ (lam : ℝ) < ∑ e ∈ Finset.Icc (j' + 1) n, (e : ℝ) / c e ∧
        (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' =
          lam * interNumRed ℂ C ![N₀] / r - μ * interNumRed ℂ C ![toLB A]) ∧
        LcCut p n (Δ + qWeil D₀ m') x j' := by
  first | exact @GlobalTheory.PairStep.exists_lcCut_induction | exact GlobalTheory.PairStep.exists_lcCut_induction | (intros; apply GlobalTheory.PairStep.exists_lcCut_induction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderActionDescentAlongIsogeny
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_oAct_desc : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq hst
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  obtain ⟨hfin, het, hsurj⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B c ψ ψ' o.ab hB hc hq
  haveI : Surjective ψ.left := hsurj
  haveI : Flat ψ.left := inferInstance
  haveI : QuasiCompact ψ.left := inferInstance
  haveI : IsMonHom ψ := hq.1
  have : Epi ψ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ
  have : Epi (ψ ⊗ₘ ψ) := GlobalTheory.FlatQuotient.epi_tensorHom ψ ψ
  have hd : ∀ a : D.O, ∃ t : B ⟶ B, ψ ≫ t = o.act.act a ≫ ψ := fun a => by
    haveI := o.act.hom a
    refine GlobalTheory.AbelianQuotient.exists_desc ψ (o.act.act a ≫ ψ) fun W x₁ x₂ h => ?_
    have h1 : (x₁ / x₂) ≫ ψ = 1 := by rw [GrpObj.div_comp, h, div_self']
    have h2 : (x₁ / x₂) ≫ o.act.act a ≫ ψ = 1 := hst W W.hom (Category.comp_id _) _ h1 a
    rwa [GrpObj.div_comp, div_eq_one] at h2
  choose t ht using hd
  refine ⟨{ act := t, hom := fun a => ?_, one := ?_, mul := fun a a' => ?_, add := fun a a' => ?_ },
    fun a => (ht a).symm⟩
  · haveI := o.act.hom a
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom (f := ψ), Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]
    · rw [← cancel_epi (ψ ⊗ₘ ψ), ← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, ht,
        ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ht]
  · rw [← cancel_epi ψ, ht, o.act.one, Category.id_comp, Category.comp_id]
  · rw [← cancel_epi ψ, ht, o.act.mul, Category.assoc, ← ht, ← Category.assoc, ← ht, Category.assoc]
  · rw [← cancel_epi ψ, ht, o.act.add, Hom.mul_def, Hom.mul_def, comp_lift_assoc, ht, ht, ← lift_map, Category.assoc,
      Category.assoc, IsMonHom.mul_hom]

end GlobalTheory.UPel.HT.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfIsAlgClosedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_point_of_isAbelianScheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (n : ℕ), 0 < n → ∀ g : Over.mk x ⟶ A, ∃ g' : Over.mk x ⟶ A, g' ^ n = g := by
  first | (exact @GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed) | (exact GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed) | (intros; apply GlobalTheory.AbDivPt.exists_pow_eq_of_isAlgClosed  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstDeRhamHomology_projective_over_tensor_integers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  first | exact @GlobalTheory.CrysProj.hdR_projective | exact GlobalTheory.CrysProj.hdR_projective | (intros; apply GlobalTheory.CrysProj.hdR_projective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfDualHomomorphismKernelKilled
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualHomFlat

theorem geomFibre_flat (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left)
    (la : A ⟶ B) [IsMonHom la] (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hd : IsDual A B P)
    [LocallyQuasiFinite la.left] (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) :
    Flat ((Over.pullback s).map la).left := by
  letI : GrpObj ((Over.pullback s).obj A) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback s).obj B) := Functor.grpObjObj
  have hA' := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  have hB' := GlobalTheory.isAbelianScheme_pullback_obj s B hB
  obtain ⟨gA, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj A) hA'
  obtain ⟨gB, hgB⟩ := GlobalTheory.AbelianDim.exists_relDim K ((Over.pullback s).obj B) hB'
  let Ak : AV.AbVar K := { X := (Over.pullback s).obj A, ab := hA', dim := gA, smooth := hgA }
  let Bk : AV.AbVar K := { X := (Over.pullback s).obj B, ab := hB', dim := gB, smooth := hgB }
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback s).map a).left ≫ pullback.fst Y.hom s = pullback.fst X.hom s ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback s).obj A ⊗ (Over.pullback s).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback s) A B).left ≫ pullback.fst (A ⊗ B).hom s
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst A.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback s).obj A) ((Over.pullback s).obj B)).left ≫
      pullback.fst B.hom s := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback s) A B ≫ (Over.pullback s).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual Ak.X Bk.X (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A s)
    (isGrpPullback_pullback B s) h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have hdim : gB = gA := DualTower.dim_eq_of_isDual Ak Bk (P.pull h) hd'
  subst hdim
  have : LocallyQuasiFinite ((Over.pullback s).map la).left :=
    MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) (AbLaw.MulN.isPullback_baseChange s la)
      inferInstance
  exact (IsogenyQuasiInverse.flat_surjective_of_field _ _ gB hA' hB' hgA hgB _).1

end GlobalTheory.DualHomFlat

namespace GlobalTheory.DualHomFlat

theorem main : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (Q : LB (A ⊗ B).left)
    (la : A ⟶ B) (d : ℕ), IsAbelianScheme A → IsAbelianScheme B → IsDual A B Q →
    IsDual B A (swap Q) → IsMonHom la → 0 < d →
    (∀ (T : Over S) (x : T ⟶ A), x ≫ la = 1 → x ^ d = 1) → Flat la.left := by
  intro S A B _ _ Q la d hA hB hd _ hla hdpos hker
  have := hA.smooth
  have := hB.smooth
  have := hA.proper
  have := hB.proper
  have : LocallyOfFiniteType (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : LocallyOfFiniteType la.left := locallyOfFiniteType_of_comp _ B.hom
  have : QuasiCompact (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : QuasiCompact la.left := QuasiCompact.of_comp _ B.hom
  have hSA := isSemiAbelian_of_isAbelianScheme A hA
  have : LocallyQuasiFinite la.left :=
    locallyQuasiFinite_of_finite_geometric_ker _ A B la hla inferInstance inferInstance
      fun Ω _ _ t => by
        have := HomExt.finite_torsion_points hSA t hdpos
        exact Finite.of_injective (β := {x : Over.mk t ⟶ A // x ^ d = 1})
          (fun x => ⟨x.1, hker _ x.1 x.2⟩) fun a b e =>
            Subtype.ext (congrArg (fun z : {x : Over.mk t ⟶ A // x ^ d = 1} => z.1) e)
  have h1 : IsProper (la.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper la.left := IsProper.of_comp _ B.hom
  have hf : IsFinite la.left := .of_isProper_of_locallyQuasiFinite _
  exact flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S A B la inferInstance
    inferInstance inferInstance hf fun K _ _ t => geomFibre_flat S A B Q la hA hB hd K t

end GlobalTheory.DualHomFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderDeformationSkewStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (k : Type) [Field k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (φ : LinearMap.BilinForm k (HdR o₀.A)), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, ∀ x' y' : HdR o₀.A, IsFilLift m'.cart x x' → IsFilLift m'.cart y y' → φ x' y + φ x y' = 0 := by
  first | (exact @GlobalTheory.HTSkew.skew_of_isFilLift) | (exact GlobalTheory.HTSkew.skew_of_isFilLift) | (intros; apply GlobalTheory.HTSkew.skew_of_isFilLift  <;> assumption)
end

