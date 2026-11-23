module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0018

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MIsoOfKer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

namespace UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization

variable {S : Scheme.{0}}

private lemma pow_comp' {T A B : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    (x ^ n) ≫ f = (x ≫ f) ^ n := by
  exact (IsMonHom.monoidHom f T).map_pow x n

private lemma comp_pow' {T' T A : Over S} [GrpObj A] (t : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    t ≫ (x ^ n) = (t ≫ x) ^ n := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih => simp only [pow_succ, Hom.mul_def, comp_lift_assoc, ih]

private lemma self_pow {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    f ^ n = ((𝟙 A) ^ n) ≫ f := by
  rw [pow_comp', Category.id_comp]

private lemma cancel (hDiv : DivC) {A₀ A B : Over S} [GrpObj A₀] [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) {c : ℕ} (hc : 0 < c) (ψ : A₀ ⟶ A) (ψ' : A ⟶ A₀) (e : ψ' ≫ ψ = (𝟙 A) ^ c)
    (u v : A ⟶ B) [IsMonHom u] [IsMonHom v] (h : ψ ≫ u = ψ ≫ v) : u = v := by
  have h2 : ψ' ≫ ψ ≫ u = ψ' ≫ ψ ≫ v := by rw [h]
  rw [← Category.assoc, ← Category.assoc, e, ← self_pow, ← self_pow] at h2
  exact (hDiv S A B hA c hc).2 u v inferInstance inferInstance h2

private lemma factor (hDiv : DivC) {A₀ A₁ A₂ : Over S} [GrpObj A₀] [IsCommMonObj A₀] [GrpObj A₁] [IsCommMonObj A₁]
    [GrpObj A₂] [IsCommMonObj A₂] (h₀ : IsAbelianScheme A₀) (h₁ : IsAbelianScheme A₁) {c : ℕ} (hc : 0 < c)
    (ψ₁ : A₀ ⟶ A₁) (ψ₁' : A₁ ⟶ A₀) (ψ₂ : A₀ ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₁'] [IsMonHom ψ₂]
    (u : ψ₁ ≫ ψ₁' = (𝟙 A₀) ^ c) (v : ψ₁' ≫ ψ₁ = (𝟙 A₁) ^ c)
    (hk : ∀ (T : Over S) (g : T ⟶ A₀), g ≫ ψ₁ = 1 → g ≫ ψ₂ = 1) :
    ∃ ρ : A₁ ⟶ A₂, IsMonHom ρ ∧ ρ ^ c = ψ₁' ≫ ψ₂ ∧ ψ₁ ≫ ρ = ψ₂ := by
  obtain ⟨ν, hν, hνc⟩ := (hDiv S A₁ A₂ h₁ c hc).1 (ψ₁' ≫ ψ₂) inferInstance (by
    intro T g hg
    have : (g ≫ ψ₁') ≫ ψ₁ = 1 := by
      rw [Category.assoc, v, comp_pow', Category.comp_id, hg]
    rw [← Category.assoc]
    exact hk T _ this)
  haveI := hν
  refine ⟨ν, hν, hνc, ?_⟩
  refine (hDiv S A₀ A₂ h₀ c hc).2 (ψ₁ ≫ ν) ψ₂ inferInstance inferInstance ?_
  rw [← comp_pow', hνc, ← Category.assoc, u, ← self_pow]

variable {A T Y : Over S} [GrpObj A]

private lemma evc_pow_left {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (a : Y ⟶ A) (t : Y ⟶ T) (n : ℕ) :
    evc hM (a ^ n) t = n • evc hM a t := by
  induction n with
  | zero => simp [IsAdditive.evc_one hM h]
  | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hM).1 h, ih, succ_nsmul]

private lemma evc_add_right {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap (A := A) (B := B) P))
    (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hP a (b * b') = evc hP a b + evc hP a b' := by
  have hs : (swap (A := A) (B := B) P).IsLB := ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_pull hP _
  rw [← GlobalTheory.AbDual.evc_swap hP hs, ← GlobalTheory.AbDual.evc_swap hP hs, ← GlobalTheory.AbDual.evc_swap hP hs]
  exact (GlobalTheory.AbDual.isAdditive_iff hs).1 h Y b b' a

private lemma evc_pow_right {B : Over S} [GrpObj B] {P : LB (A ⊗ B).left} (hP : P.IsLB) (h : IsAdditive (swap (A := A) (B := B) P))
    (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hP a (b ^ n) = n • evc hP a b := by
  have hs : (swap (A := A) (B := B) P).IsLB := LB.isLB_pull hP _
  induction n with
  | zero =>
    rw [pow_zero, zero_smul, ← GlobalTheory.AbDual.evc_swap hP hs]
    exact IsAdditive.evc_one hs h a
  | succ n ih => rw [pow_succ, evc_add_right hP h, ih, succ_nsmul]

end UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization

open UpperTheory.Gal.crystallineComparison.Mod.IsoOfKernelFactorization in
theorem UpperTheory.Gal.crystallineComparison.Mod.isoOfKer_of :
    PairCalc → Adjoint → DivC → TorsFree → IsoOfKer := by
  intro hPC hAdj hDiv hTF
  intro p _ D R _ b N k _ s c o o₁ o₂ ψ₁ ψ₂ h1 h2 hker
  have hc : 0 < c := h1.pos
  obtain ⟨-, hm1, hact1, heta1, hpol1, ψ₁', hψ₁', u1, v1⟩ := h1
  obtain ⟨-, hm2, hact2, heta2, hpol2, ψ₂', hψ₂', u2, v2⟩ := h2
  haveI := hm1
  haveI := hm2
  haveI := hψ₁'
  haveI := hψ₂'
  obtain ⟨ρ, hρ, -, hρ1⟩ := factor hDiv o.ab o₁.ab hc ψ₁ ψ₁' ψ₂ u1 v1 (fun T g h => (hker T g).1 h)
  obtain ⟨ρ', hρ', -, hρ2⟩ := factor hDiv o.ab o₂.ab hc ψ₂ ψ₂' ψ₁ u2 v2 (fun T g h => (hker T g).2 h)
  haveI := hρ
  haveI := hρ'
  have hrr : ρ ≫ ρ' = 𝟙 o₁.A :=
    cancel hDiv o₁.ab hc ψ₁ ψ₁' v1 _ _ (by rw [← Category.assoc, hρ1, hρ2, Category.comp_id])
  have hr'r : ρ' ≫ ρ = 𝟙 o₂.A :=
    cancel hDiv o₂.ab hc ψ₂ ψ₂' v2 _ _ (by rw [← Category.assoc, hρ2, hρ1, Category.comp_id])
  have hP0 := hPC p D R b N (Sp k) s o
  have hP1 := hPC p D R b N (Sp k) s o₁
  have hP2 := hPC p D R b N (Sp k) s o₂
  have e1 := (hP0.2.2.2.2 o₁ ψ₁ c).1 hpol1
  have e2 := (hP0.2.2.2.2 o₂ ψ₂ c).1 hpol2
  have hLp : (o₂.P.pull (sq2 ρ)).IsLB := LB.isLB_pull o₂.isLB _
  have hL : ((o₂.P.pull (sq2 ρ)).div o₁.P).IsLB := LB.isLB_div hLp o₁.isLB
  have hlift : ∀ {Y : Over (Sp k)} (a t : Y ⟶ o₁.A), (lift a t).left ≫ sq2 ρ = (lift (a ≫ ρ) (t ≫ ρ)).left := by
    intro Y a t
    show (lift a t).left ≫ (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left = _
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  have hevL : ∀ {Y : Over (Sp k)} (a t : Y ⟶ o₁.A),
      evc hL a t = evc o₂.isLB (a ≫ ρ) (t ≫ ρ) - evc o₁.isLB a t := by
    intro Y a t
    unfold GlobalTheory.AbDual.evc
    rw [GlobalTheory.CechPic.cls_div hLp o₁.isLB hL, map_sub, GlobalTheory.CechPic.cls_pull o₂.isLB _ hLp,
      ← GlobalTheory.CechPic.pull_comp, hlift]
  have hadd1 := (GlobalTheory.AbDual.isAdditive_iff o₁.isLB).1 hP1.1
  have hadd2 := (GlobalTheory.AbDual.isAdditive_iff o₂.isLB).1 hP2.1
  have hmulρ : ∀ {Y : Over (Sp k)} (a a' : Y ⟶ o₁.A), (a * a') ≫ ρ = (a ≫ ρ) * (a' ≫ ρ) := by
    intro Y a a'
    exact (IsMonHom.monoidHom ρ Y).map_mul a a'
  have hLadd : IsAdditive ((o₂.P.pull (sq2 ρ)).div o₁.P) := by
    rw [GlobalTheory.AbDual.isAdditive_iff hL]
    intro Y a a' t
    rw [hevL, hevL, hevL, hmulρ, hadd2, hadd1]
    abel
  have hsL : (swap ((o₂.P.pull (sq2 ρ)).div o₁.P)).IsLB := LB.isLB_pull hL _
  have hLsadd : IsAdditive (swap ((o₂.P.pull (sq2 ρ)).div o₁.P)) := by
    rw [GlobalTheory.AbDual.isAdditive_iff hsL]
    intro Y b' b'' a
    rw [GlobalTheory.AbDual.evc_swap hL hsL, GlobalTheory.AbDual.evc_swap hL hsL, GlobalTheory.AbDual.evc_swap hL hsL, hevL, hevL, hevL, hmulρ,
      evc_add_right o₂.isLB hP2.2.1, evc_add_right o₁.isLB hP1.2.1]
    abel
  have hz : ∀ {Y : Over (Sp k)} (z w : Y ⟶ o.A), evc hL (z ≫ ψ₁) (w ≫ ψ₁) = 0 := by
    intro Y z w
    rw [hevL, Category.assoc, Category.assoc, hρ1, e1, e2, sub_self]
  have hxc : ∀ {Y : Over (Sp k)} (x : Y ⟶ o₁.A), x ^ c = (x ≫ ψ₁') ≫ ψ₁ := by
    intro Y x
    rw [Category.assoc, v1, comp_pow', Category.comp_id]
  have huniv : evc hL (fst o₁.A o₁.A) (snd o₁.A o₁.A) = GlobalTheory.CechPic.cls _ hL := by
    unfold GlobalTheory.AbDual.evc
    rw [lift_fst_snd, Over.id_left, GlobalTheory.CechPic.pull_id]
  have key : evc hL ((fst o₁.A o₁.A) ^ c) ((snd o₁.A o₁.A) ^ c) = 0 := by
    rw [hxc, hxc]
    exact hz _ _
  rw [evc_pow_left hL hLadd, evc_pow_right hL hLsadd, smul_smul, huniv] at key
  have hcls := hTF k o₁.A o₁.A o₁.ab o₁.ab _ hL hLadd hLsadd (c * c) (Nat.mul_pos hc hc) key
  rw [GlobalTheory.CechPic.cls_div hLp o₁.isLB hL, sub_eq_zero] at hcls
  have hpol : LBIso o₁.P (o₂.P.pull (sq2 ρ)) := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB hLp).1 hcls.symm
  haveI : IsIso ρ.left := ⟨⟨ρ'.left, by rw [← Over.comp_left, hrr, Over.id_left],
    by rw [← Over.comp_left, hr'r, Over.id_left]⟩⟩
  refine ⟨⟨ρ.left, sq2 ρ, ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, ?_⟩, ⟨?_, ?_⟩, ?_, hpol, ?_⟩, ?_⟩
  · intro T x y x₀ y₀ hx hy
    let i : Over.mk (T.hom ≫ 𝟙 (Sp k)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have hx' : x₀ = i ≫ x ≫ ρ := by
      ext1
      rw [hx]
      simp [i]
    have hy' : y₀ = i ≫ y ≫ ρ := by
      ext1
      rw [hy]
      simp [i]
    have hm : (i ≫ x ≫ ρ) * (i ≫ y ≫ ρ) = i ≫ (x * y) ≫ ρ := by
      rw [hmulρ x y, Hom.mul_def, Hom.mul_def, comp_lift_assoc]
    rw [hx', hy', hm]
    simp [i]
  · show (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left ≫ _ = _
    rw [← Over.comp_left, lift_fst, Over.comp_left]
  · show (lift (fst o₁.A o₁.A ≫ ρ) (snd o₁.A o₁.A ≫ ρ)).left ≫ _ = _
    rw [← Over.comp_left, lift_snd, Over.comp_left]
  · intro a
    haveI := o₁.act.hom a
    haveI := o₂.act.hom a
    have h : o₁.act.act a ≫ ρ = ρ ≫ o₂.act.act a :=
      cancel hDiv o₁.ab hc ψ₁ ψ₁' v1 _ _ (by
        rw [← Category.assoc, ← hact1 a, Category.assoc, hρ1, hact2 a, ← hρ1, Category.assoc])
    rw [← Over.comp_left, h, Over.comp_left]
  · intro y
    rw [← Over.comp_left, heta1 y, Category.assoc, hρ1, ← heta2 y, Category.id_comp]
  · rw [← Over.comp_left, hρ1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MKerFromU
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

section Helpers
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem cpow {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (h : T ⟶ A) (n : ℕ) :
    f ≫ (h ^ n) = (f ≫ h) ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Hom.one_def]
    rw [← Category.assoc, toUnit_unique (f ≫ toUnit T) (toUnit T')]
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih, Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem powc {A B T : Over S} [GrpObj A] [GrpObj B] (h : T ⟶ A) (f : A ⟶ B) [IsMonHom f] (n : ℕ) :
    (h ^ n) ≫ f = (h ≫ f) ^ n := by
  exact map_pow (IsMonHom.monoidHom f T) h n

private abbrev sc (o : Obj b N s) (x : 𝓞 D.F) : o.A ⟶ o.A := o.act.act (algebraMap (𝓞 D.F) D.O x)

private instance sc_hom (o : Obj b N s) (x : 𝓞 D.F) : IsMonHom (sc o x) := o.act.hom _

private theorem sc_add (o : Obj b N s) (x y : 𝓞 D.F) : sc o (x + y) = sc o x * sc o y := by
  show o.act.act (algebraMap (𝓞 D.F) D.O (x + y)) = _
  rw [map_add (f := _)]
  exact o.act.add _ _

private theorem sc_mul (o : Obj b N s) (x y : 𝓞 D.F) : sc o (x * y) = sc o y ≫ sc o x := by
  show o.act.act (algebraMap (𝓞 D.F) D.O (x * y)) = _
  rw [map_mul]
  exact o.act.mul _ _

private theorem sc_one (o : Obj b N s) : sc o 1 = 𝟙 o.A := by
  show o.act.act (algebraMap (𝓞 D.F) D.O 1) = _
  rw [map_one]
  exact o.act.one

private theorem sc_zero (o : Obj b N s) : sc o 0 = 1 := by
  have h := sc_add o 0 0
  rw [add_zero] at h
  open GrpObj in exact mul_eq_left.mp h.symm

private theorem sc_nat (o : Obj b N s) (n : ℕ) : sc o (n : 𝓞 D.F) = (𝟙 o.A) ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, sc_zero, pow_zero]
  | succ n ih => rw [Nat.cast_succ, sc_add, ih, sc_one, pow_succ]

private theorem sc_killed (o : Obj b N s) {T : Over S} (z : T ⟶ o.A) {c : ℕ} (hz : z ^ c = 1) (t : 𝓞 D.F) :
    z ≫ sc o (t * (c : 𝓞 D.F)) = 1 := by
  rw [sc_mul, sc_nat, ← Category.assoc, cpow, Category.comp_id, hz]
  have h := powc z (sc o t) 0
  rwa [pow_zero, pow_zero] at h

end Helpers

private theorem bar_bar {p : ℕ} [Fact p.Prime] (D : Datum p) (a : 𝓞 D.F) : D.bar (D.bar a) = a := by
  rw [RingOfIntegers.ext_iff, D.bar_eq, D.bar_eq, IsCMField.complexConj_apply_apply]

private theorem one_comp_monHom' {S : Scheme.{0}} {T A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B)
    [IsMonHom f] : (1 : T ⟶ A) ≫ f = 1 := by
  have h := powc (1 : T ⟶ A) f 0
  rwa [pow_zero, pow_zero] at h

private theorem comp_one_grpObj {S : Scheme.{0}} {X T A : Over S} [GrpObj A] (f : X ⟶ T) :
    f ≫ (1 : T ⟶ A) = 1 := by
  have h := cpow f (1 : T ⟶ A) 0
  rwa [pow_zero, pow_zero] at h

private theorem comp_mul_grpObj {S : Scheme.{0}} {T A B : Over S} [GrpObj B] (f : T ⟶ A)
    (h₁ h₂ : A ⟶ B) : f ≫ (h₁ * h₂) = (f ≫ h₁) * (f ≫ h₂) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem comp_id_pow_eq_pow {S : Scheme.{0}} {T A : Over S} [GrpObj A] (f : T ⟶ A) (n : ℕ) :
    f ≫ (𝟙 A ^ n) = f ^ n := by
  rw [cpow, Category.comp_id]

theorem UpperTheory.Gal.crystallineComparison.Mod.kerFromU_of :
    UElt → PairCalc → Adjoint → DivC → KerFromU := by
  intro hU hP hA hD p _ D R _ b N r w hw hle k _ s c o o₁ o₂ ψ₁ ψ₂ h1 h2 hiff T g hg
  have cpos := h1.pos
  obtain ⟨⟨e, rfl⟩, hm1, hl1, -, -, ψ₁', hm1', hψ₁a, hψ₁b⟩ := id h1
  obtain ⟨-, hm2, hl2, -, -, ψ₂', hm2', hψ₂a, hψ₂b⟩ := id h2
  haveI := hm1
  haveI := hm1'
  haveI := hm2
  haveI := hm2'
  obtain ⟨α, hα1, hα2, -⟩ := hU p D r w hw hle e
  have kill : ∀ {T' : Over (Sp k)} (u : T' ⟶ o.A), u ^ (p ^ e) = 1 → ∀ t : 𝓞 D.F,
      t ∈ Ideal.span {(p : 𝓞 D.F) ^ e} → u ≫ sc o t = 1 := by
    intro T' u hu t ht
    obtain ⟨t', rfl⟩ := Ideal.mem_span_singleton'.mp ht
    rw [← Nat.cast_pow]
    exact sc_killed o u hu t'
  have uk : ∀ (o' : Obj b N s) (ψ : o.A ⟶ o'.A) [IsMonHom ψ],
      (∀ c', o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') → ∀ (T' : Over (Sp k)) (u : T' ⟶ o.A),
      u ≫ ψ = 1 → u ^ (p ^ e) = 1 → UKer r o ψ T' (u ≫ sc o α) := by
    intro o' ψ _ hl T' u hu hpu
    refine ⟨?_, e, ?_⟩
    · have hl' : sc o α ≫ ψ = ψ ≫ sc o' α := hl _
      rw [Category.assoc, hl', ← Category.assoc, hu, one_comp_monHom']
    · intro a ha
      show (u ≫ sc o α) ≫ sc o a = 1
      rw [Category.assoc, ← sc_mul]
      exact kill u hpu _ (hα1 a ha)
  have gpow : g ^ (p ^ e) = 1 := by
    rw [← comp_id_pow_eq_pow g (p ^ e), ← hψ₁a, ← Category.assoc, hg, one_comp_monHom']
  have dec : g = (g ≫ sc o α) * (g ≫ sc o (D.bar α)) := by
    rw [← comp_mul_grpObj, ← sc_add]
    obtain ⟨t', ht'⟩ := Ideal.mem_span_singleton'.mp hα2
    have hsum : α + D.bar α = 1 + t' * ((p ^ e : ℕ) : 𝓞 D.F) := by
      rw [Nat.cast_pow, ht']
      ring
    rw [hsum, sc_add, comp_mul_grpObj, sc_one, Category.comp_id, sc_killed o g gpow t',
      _root_.mul_one]
  have hA1 : (g ≫ sc o α) ≫ ψ₂ = 1 := ((hiff T _).1 (uk o₁ ψ₁ hl1 T g hg gpow)).1
  obtain ⟨ν, hν, hνc⟩ := (hD (Sp k) o₂.A o₁.A o₂.ab (p ^ e) cpos).1 (ψ₂' ≫ sc o α ≫ ψ₁)
    inferInstance (by
      intro T' t ht
      have hu2 : (t ≫ ψ₂') ≫ ψ₂ = 1 := by
        rw [Category.assoc, hψ₂b, comp_id_pow_eq_pow, ht]
      have hu3 : (t ≫ ψ₂') ^ (p ^ e) = 1 := by
        rw [← powc, ht, one_comp_monHom']
      have h' := ((hiff T' _).2 (uk o₂ ψ₂ hl2 T' _ hu2 hu3)).1
      simpa only [Category.assoc] using h')
  haveI := hν
  have hfac : ν ≫ ψ₁' = ψ₂' ≫ sc o α := by
    refine (hD (Sp k) o₂.A o.A o₂.ab (p ^ e) cpos).2 _ _ inferInstance inferInstance ?_
    rw [← powc, hνc]
    simp only [Category.assoc, hψ₁a]
    rw [← Category.assoc, comp_id_pow_eq_pow]
  have h3 : ∀ (T' : Over (Sp k)) (x y : T' ⟶ o.A) (a : 𝓞 D.F),
      evc o.isLB (x ≫ sc o a) y = evc o.isLB x (y ≫ sc o (D.bar a)) :=
    (hP p D R b N (Sp k) s o).2.2.1
  have hB : (g ≫ sc o (D.bar α)) ≫ ψ₂ = 1 := by
    obtain ⟨e', hcop, hnd⟩ := (hP p D R b N (Sp k) s o₂).2.2.2.1
    have zc : ((g ≫ sc o (D.bar α)) ≫ ψ₂) ^ (p ^ e) = 1 := by
      rw [Category.assoc, ← powc, gpow, one_comp_monHom']
    have ze : ((g ≫ sc o (D.bar α)) ≫ ψ₂) ^ e' = 1 := by
      apply hnd
      have ad2 := (hA p D R b N k s (p ^ e) o o₂ ψ₂ ψ₂' h2 hm2' hψ₂b (o₂.A ⊗ T)
        (snd o₂.A T ≫ g ≫ sc o (D.bar α)) (fst o₂.A T)).1
      simp only [Category.assoc] at ad2 ⊢
      rw [ad2, ← Category.assoc, h3, bar_bar, Category.assoc, ← hfac, ← Category.assoc]
      have ad1 := (hA p D R b N k s (p ^ e) o o₁ ψ₁ ψ₁' h1 hm1' hψ₁b (o₂.A ⊗ T)
        (snd o₂.A T ≫ g) (fst o₂.A T ≫ ν)).1
      rw [← ad1, Category.assoc, hg, comp_one_grpObj]
      exact GlobalTheory.AbDual.IsAdditive.evc_one o₁.isLB (hP p D R b N (Sp k) s o₁).1 _
    have hgcd := pow_gcd_eq_one.2 ⟨ze, zc⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right e hcop), pow_one] at hgcd
  have mm : ∀ a a' : T ⟶ o.A, (a * a') ≫ ψ₂ = (a ≫ ψ₂) * (a' ≫ ψ₂) :=
    fun a a' => (IsMonHom.monoidHom ψ₂ T).map_mul a a'
  rw [dec, mm, hA1, hB, _root_.one_mul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameE
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.sameE_of :
    KillLocal → InfE → SameE := by
  intro hK hI p _ D R _ b N r κ _ _ s o o₁ o₂ ψ₁ ψ₂ hψ₂ hsub d hrep hcard hkill T g hg
  refine ⟨hK κ o.A o₂.A ψ₂ hψ₂ (UKer r o ψ₁) d hrep hsub hkill ?_ T g hg, hg.2⟩
  intro Λ _ _ _ ε g' hP hinf
  rw [hI κ o.A (UKer r o ψ₁) d hrep hcard Λ ε g' hP hinf]
  exact MonObj.one_comp _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSameW
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem isMonHom_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact inferInstanceAs (IsMonHom (toUnit A ≫ η[A]))
  | succ n ih =>
    rw [pow_succ]
    exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

private theorem pow_hom_comm {S : Scheme.{0}} {A : Over S} [GrpObj A] (h : A ⟶ A) [IsMonHom h] (n : ℕ) :
    h ≫ ((𝟙 A) ^ n) = ((𝟙 A) ^ n) ≫ h := by
  induction n with
  | zero => simp [Hom.one_def]
  | succ n ih =>
    simp only [pow_succ, Hom.mul_def, comp_lift_assoc, Category.assoc, IsMonHom.mul_hom, lift_map_assoc, Category.comp_id, Category.id_comp, ih]

theorem UpperTheory.Gal.crystallineComparison.Mod.sameW_of :
    KillLocal → InfW → FrobPass → KerU → RepOfFF → TanOne → SameW := by
  intro hKL hInf hFP hKU hRep hTan
  intro p _ D R _ b N hm ha r w hw hu f κ _ _ _ β hβ o o₁ o₂ o₃ ψ₁ ψ₂ F e h1 hψ₂ h3 hF d hd hR1 hc1 hR2 hc2 hcl T g
  have hp : Nat.Prime p := Fact.out
  obtain ⟨-, hm1, hact1, -, -, ψ₁', hψ₁', h11, h12⟩ := h1
  obtain ⟨-, hm3, hact3, -, -, χ', hχ', h31, h32⟩ := h3
  haveI := hm1
  haveI := hm3
  haveI := hψ₁'
  haveI := hχ'
  haveI := hψ₂
  haveI hpow : IsMonHom ((𝟙 o.A) ^ p ^ (e + 1)) := isMonHom_pow o.A _
  have hactP : ∀ a : D.O, o.act.act a ≫ ((𝟙 o.A) ^ p ^ (e + 1)) = ((𝟙 o.A) ^ p ^ (e + 1)) ≫ o.act.act a := by
    intro a
    haveI := o.act.hom a
    exact pow_hom_comm (o.act.act a) _
  have kP := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o ((𝟙 o.A) ^ p ^ (e + 1)) (𝟙 o.A) (e + 1)
    hpow inferInstance hactP (by simp) (by simp)
  obtain ⟨d', hRP⟩ := hRep κ o.A _ kP.1
  have k1 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₁ ψ₁ ψ₁' (e + 1) hm1 hψ₁' hact1 h11 h12
  have k3 := hKU p D R b N r w hw hu (Sp κ) (spMap β) o o₃ (ψ₂ ≫ F) χ' (e + 1) hm3 hχ' hact3 h31 h32
  obtain ⟨d₃, hR3⟩ := hRep κ o.A _ k3.1
  have sub1 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o ψ₁ T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h11, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have sub3 : ∀ (T : Over (Sp κ)) (g : T ⟶ o.A), UKer r o (ψ₂ ≫ F) T g → UKer r o ((𝟙 o.A) ^ p ^ (e + 1)) T g := by
    intro T g hg
    refine ⟨?_, hg.2⟩
    rw [← h31, ← Category.assoc, hg.1]
    simp [Hom.one_def]
  have hI := hInf p f hp κ o.A (UKer r o ψ₁) (UKer r o ((𝟙 o.A) ^ p ^ (e + 1))) d d' hR1 k1.2.1 hc1 hd hRP sub1
    (hTan p D R b N hm ha r w hu κ β hβ o e)
  have fp := hFP p D R b N r f κ (spMap β) o o₂ ψ₂ hψ₂ d hR2 hc2
  have hF1 : (1 : 𝟙_ (Over (Sp κ)) ⟶ o₂.A) ≫ F = 1 := (hF _ 1).2 (fun _ => rfl)
  constructor
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₃.A (ψ₂ ≫ F) hm3 (UKer r o ψ₁) (p ^ f * d) hR1 k1.2.1 ?_ ?_ T g hg
    · intro g' hg'
      rw [← Category.assoc, ((hcl g').1 hg').1, hF1]
    · intro Λ _ _ _ ε g' hg' hi
      rw [← Category.assoc]
      exact (hF _ _).2 ((fp.2 Λ ε g' hg'.2 hi).2 ((hI Λ ε g' (sub1 _ _ hg') hi).1 hg'))
  · intro hg
    refine ⟨?_, hg.2⟩
    refine hKL κ o.A o₁.A ψ₁ hm1 (UKer r o (ψ₂ ≫ F)) d₃ hR3 k3.2.1 ?_ ?_ T g hg
    · intro g' hg'
      have h2 : g' ≫ ψ₂ = 1 := fp.1 (g' ≫ ψ₂) ((hF _ _).1 (by rw [Category.assoc]; exact hg'.1))
      exact ((hcl g').2 ⟨h2, hg'.2⟩).1
    · intro Λ _ _ _ ε g' hg' hi
      have hk : FrobKill p f hp (g' ≫ ψ₂) := (hF _ _).1 (by rw [Category.assoc]; exact hg'.1)
      exact ((hI Λ ε g' (sub3 _ _ hg') hi).2 ((fp.2 Λ ε g' hg'.2 hi).1 hk)).1
end

