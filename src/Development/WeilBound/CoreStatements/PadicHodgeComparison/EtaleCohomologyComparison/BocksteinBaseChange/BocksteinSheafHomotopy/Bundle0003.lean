module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtProps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.ReductionLemmas
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.EqZeroOfCast
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace RootOfUnityLemmas

theorem pick_neg {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  rw [dite_eq_right h]

theorem cast_zero' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    (0 : Ht q E n i).cast hn hi = 0 := by
  subst hn; subst hi; rfl

theorem eq_zero_of_cast {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : x.cast hn hi = 0) : x = 0 := by
  subst hn; subst hi; exact h

theorem res_id {R : Type} [CommRing R] {F : Shv R} {X : Scheme.{0}} (a : Sec F X) : Sec.res (𝟙 X) a = a := by
  simp [Sec.res]

theorem resGen_closed (hF : FormalIn) (q : ℕ) (s : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) :
    Sec.map ((res _ (tw q s)).d 0 1) (resGen s ζ) = 0 := by
  obtain ⟨-, e, -, he⟩ := hF.a9 (ZMod q) (tw q s)
  obtain ⟨α, -, hα⟩ := he X (twGen s ζ)
  have h := ((hF.et.sch (ZMod q) X (res _ (tw q s)) (-1) 0 1 (by norm_num) (by norm_num)).2 α).1
  rw [hα] at h
  exact h

theorem ev_vanish {R : Type} [CommRing R] {X : Scheme.{0}} {I : GlobalTheory.EtC.Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj X)) I n)
    (h : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0) :
    ∀ (p : ℕ), p ≠ 0 → ∀ (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx (sch.obj X) p U), ev α p s h U x = 0 := by
  intro p hp
  obtain ⟨p', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  exact fun s h' U x => h p' s h' U x

theorem isAW_conc {R : Type} [CommRing R] {I J K : GlobalTheory.EtC.Cx R} (μ : Pair I J K) {X : Scheme.{0}}
    (α : Cochain ((chains R).obj (sch.obj X)) I 0) (β : Cochain ((chains R).obj (sch.obj X)) J 0)
    (γ : Cochain ((chains R).obj (sch.obj X)) K (0 + 0)) (a : Sec (I.X 0) X) (b : Sec (J.X 0) X) (c : Sec (K.X 0) X)
    (hc : μ.mul X 0 0 0 (add_zero 0) a b = c)
    (hα0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev α 0 0 (by simp) U x = Sec.res x a)
    (hα1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev α (p + 1) s h U x = 0)
    (hβ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev β 0 0 (by simp) U x = Sec.res x b)
    (hβ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + 0 = s) (U : Scheme.{0}) (x : U ⟶ X), ev β (p + 1) s h U x = 0)
    (hγ0 : ∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ 0 (0 + 0) (by simp) U x = Sec.res x c)
    (hγ1 : ∀ (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + (0 + 0) = s) (U : Scheme.{0}) (x : U ⟶ X), ev γ (p + 1) s h U x = 0) :
    μ.IsAW rfl α β γ := by
  intro N w h U x
  cases N with
  | zero =>
    subst h
    rw [Fin.sum_univ_one]
    have e1 : ev γ 0 (-((0 : ℕ) : ℤ) + (0 + 0)) rfl U x = μ.mul U 0 0 0 (add_zero 0) (ev α 0 0 (by simp) U x)
        (ev β 0 0 (by simp) U x) := by
      rw [hα0, hβ0, ← μ.nat, hc]
      exact hγ0 U x
    rw [e1]
    simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
    rfl
  | succ N =>
    rw [hγ1 N w h U x]
    refine (Finset.sum_eq_zero fun p _ => ?_).symm
    by_cases hp : (p : ℕ) = 0
    · rw [ev_vanish β hβ1 (N + 1 - p) (by omega)]
      simp
    · rw [ev_vanish α hα1 p hp]
      simp

theorem conc_eq_one (hF : FormalIn) (q : ℕ) [NeZero q] (X : Scheme.{0}) (ζ : Prim q Γ(X, ⊤)) (t : ℤ) (ht : (0 : ℤ) = t)
    (c : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q t)) (0 + 0))
    (hc : ev c.1 0 (0 + 0) (by simp) X (𝟙 X) = resGen t ζ) (hn : (0 : ℤ) = 0 + 0) :
    CohomologyClass.mk c = (one q (sch.obj X)).cast hn ht := by
  subst ht
  by_cases hw : ∃ c' : Ht q (sch.obj X) 0 0, ∃ α : Cocycle _ _ 0, CohomologyClass.mk α = c' ∧
      ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ'
  · obtain ⟨α, hα, hα'⟩ : ∃ α : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 0)) 0,
        CohomologyClass.mk α = one q (sch.obj X) ∧
        ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) (ζ' : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ' :=
      pick_spec hw
    rw [← hα]
    change CohomologyClass.mk c = CohomologyClass.mk α
    exact WeightedPowerFormIntegrability.mk_eq_of_ev hF.et.sch c α (hc.trans (hα' X (𝟙 X) ζ).symm)
  · have h1 : one q (sch.obj X) = 0 := pick_neg hw
    have hinv : Inv q (sch.obj X) := fun U ⟨x⟩ => (Prim.map (show U ⟶ X from x).appTop.hom ζ).2.1
    have h2 := (hF.a6ring q (sch.obj X)).1 hinv (CohomologyClass.mk c)
    rw [h1, map_zero, AddMonoidHom.zero_apply] at h2
    rw [h1, cast_zero', eq_zero_of_cast _ _ _ h2.symm]

end RootOfUnityLemmas


open RootOfUnityLemmas in
theorem root : RootsOfUnityFormal := by
  intro hF q _ X ⟨ζ⟩ i
  have hS := hF.et.sch
  obtain ⟨v, hv0, hv1⟩ := (hS (ZMod q) X (res _ (tw q (-i))) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen (-i) ζ) (resGen_closed hF q (-i) ζ)
  obtain ⟨u, hu0, hu1⟩ := (hS (ZMod q) X (res _ (tw q i)) (-1) 0 1 (by norm_num) (by norm_num)).1
    (resGen i ζ) (resGen_closed hF q i ζ)
  obtain ⟨c, hc0, hc1⟩ := (hS (ZMod q) X (res _ (tw q (-i + i))) (-1) (0 + 0) 1 (by norm_num) (by norm_num)).1
    (resGen (-i + i) ζ) (resGen_closed hF q (-i + i) ζ)
  refine ⟨CohomologyClass.mk u, CohomologyClass.mk v, ?_⟩
  have hcup : cup q (CohomologyClass.mk v) (CohomologyClass.mk u) = CohomologyClass.mk c :=
    Pair.cup_spec (twPair q (-i) i) (sch.obj X) rfl v u c
      (isAW_conc (twPair q (-i) i) v.1 u.1 c.1 (resGen (-i) ζ) (resGen i ζ) (resGen (-i + i) ζ)
        (hF.et.tw q (-i) i X ζ) hv0 hv1 hu0 hu1 hc0 hc1)
  rw [hcup]
  exact conc_eq_one hF q X ζ (-i + i) (by ring) c ((hc0 X (𝟙 X)).trans (res_id _)) (by ring)

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.PickNeg
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace CrystallineSemistableComparison

open GlobalTheory.EtC

namespace CyclicComplexMaps

def semiComp {T S R : Type} [CommRing T] [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx T} {J : GlobalTheory.EtC.Cx S} {L : GlobalTheory.EtC.Cx R}
    (τ : SemiMap I J) (ρ : SemiMap J L) : SemiMap I L where
  app U s := (ρ.app U s).comp (τ.app U s)
  nat g s a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.nat, τ.nat]
  comm U s t a := by simp only [AddMonoidHom.comp_apply]; rw [ρ.comm, τ.comm]

theorem pick_neg' {α : Type*} [Zero α] {P : α → Prop} (h : ¬ ∃ a, P a) : pick P = 0 := by
  unfold pick
  exact dif_neg h

theorem op_zero {S R : Type} [CommRing S] [CommRing R] {I : GlobalTheory.EtC.Cx S} {J : GlobalTheory.EtC.Cx R} (E : Spc) (n : ℤ)
    (x : CohomologyClass ((chains S).obj E) I n) : (0 : SemiMap I J).op.app E n x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [SemiMap.op_spec (0 : SemiMap I J) E n α 0 (fun p s h U x => ?_)]
  · rfl
  · rw [Cocycle.coe_zero, CupSpec.ev_zero]
    rfl

end CyclicComplexMaps

theorem redSh (hF : FormalIn) : InRedSh := by
  intro Q q _ _ h i π hπ E n z
  by_cases hρ : ∃ ρ : SemiMap (res (ZMod q) (tw q i)) (res (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))),
      ∀ (U : Scheme.{0}) (a : Sec (tw q i) U), ρ.app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
          (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a)
  · have hρ' : ∀ (U : Scheme.{0}) (a : Sec (tw q i) U),
        (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 (Sec.map (resι (ZMod q) (tw q i)) a) =
          Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)))
            (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from a) := pick_spec hρ
    have hτ := hF.et.red Q q h i
    let σ := CyclicComplexMaps.semiComp (redMap Q q i) (restrMap (ZMod.castHom h (ZMod q)) (tw q i))
    have hg : resι (ZMod Q) (tw Q i) ≫ (CyclicComplexMaps.cxHom σ).f 0 =
        π ≫ resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) := by
      refine CyclicComplexMaps.tw_ext _ _ (fun U ζ => ?_)
      obtain ⟨ξ, hξ⟩ := CyclicComplexMaps.prim_pow h ζ
      change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).app U 0 ((redMap Q q i).app U 0 (resGen i ζ)) =
        Sec.map (resι (ZMod Q) ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))) (Sec.map π (twGen i ζ))
      rw [hτ U ζ ξ hξ, hπ U ζ ξ hξ]
      exact hρ' U (twGen i ξ)
    obtain ⟨α, rfl⟩ := z.mk_surjective
    obtain ⟨β, hβ⟩ := SemiMap.image_exists (redMap Q q i) E n α
    obtain ⟨γ, hγ⟩ := SemiMap.image_exists (restrMap (ZMod.castHom h (ZMod q)) (tw q i)) E n β
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n ((redMap Q q i).op.app E n (CohomologyClass.mk α)) = _
    rw [SemiMap.op_spec _ E n α β hβ, SemiMap.op_spec _ E n β γ hγ,
      ← CyclicComplexMaps.cpost_of_aug _ π (CyclicComplexMaps.cxHom σ) hg n (CohomologyClass.mk α), cpost_mk]
    congr 1
    apply Cocycle.ext
    apply CupSpec.ev_ext
    intro p s hs U x
    rw [hγ, hβ]
    exact (CyclicComplexMaps.ev_comp α.1 (CyclicComplexMaps.cxHom σ) p s hs U x).symm
  · have h0 : restrMap (ZMod.castHom h (ZMod q)) (tw q i) = 0 := CyclicComplexMaps.pick_neg' hρ
    obtain ⟨y, hy⟩ := (hF.a8 (ZMod Q) (ZMod q) (ZMod.castHom h (ZMod q)) E (tw q i) n).2
      (HK.post _ ((chains _).obj E) π n z)
    rw [← hy]
    change (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _ = (restrMap (ZMod.castHom h (ZMod q)) (tw q i)).op.app E n _
    rw [h0, CyclicComplexMaps.op_zero, CyclicComplexMaps.op_zero]

theorem bock_tw (hS : InTwSeq) : BocksteinInputFromFormal := fun hF => bock_of hS (redSh hF) hF

end CrystallineSemistableComparison
end
end

-- bundled from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinSheafHomotopy.TwGenRes
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace CrystallineSemistableComparison.TwSeq

open GlobalTheory.EtC

theorem pow_self {Q : ℕ} {A : Type} [CommRing A] (ζ : Prim Q A) : ζ.1 ^ Q = 1 := by
  obtain ⟨c, hc⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one Q ℤ
  have := congrArg (Polynomial.aeval ζ.1) hc
  rw [map_mul, ζ.2.2, zero_mul, map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at this
  exact this

def pw {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : Prim q A :=
  ⟨ζ.1 ^ (Q / q), isUnit_of_dvd_unit (Nat.cast_dvd_cast h) ζ.2.1, by
    obtain ⟨c, hc⟩ := CyclicComplexMaps.cyc_dvd Q q (NeZero.ne Q) h
    have := congrArg (Polynomial.aeval ζ.1) hc
    rw [Polynomial.aeval_comp, map_mul, ζ.2.2, zero_mul] at this
    simpa using this⟩

theorem pw_val {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A : Type} [CommRing A] (ζ : Prim Q A) : (pw h ζ).1 = ζ.1 ^ (Q / q) := rfl

theorem pw_map {Q q : ℕ} [NeZero Q] (h : q ∣ Q) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (ζ : Prim Q A) :
    (pw h ζ).map f = pw h (ζ.map f) := Subtype.ext (map_pow f _ _)

theorem twGen_res {q : ℕ} (i : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen i ζ) = twGen i (ζ.map g.appTop.hom) := by
  have h := ConcreteCategory.congr_hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).naturality g.op)
    (Submodule.Quotient.mk (Finsupp.single ζ 1) : (Prim q Γ(U, ⊤) →₀ ULift.{1} (ZMod q)) ⧸ twRel q i Γ(U, ⊤))
  refine h.symm.trans ?_
  change ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q i)).app (op V)).hom
    (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map g.appTop.hom) (Finsupp.single ζ 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

theorem redSheaf (hG : E.InGen) {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) (i : ℤ) :
    ∃ π : tw Q i ⟶ (restr (ZMod.castHom h (ZMod q))).obj (tw q i), IsRedSh h i π ∧
      ∀ (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤)), Sec.map π (twGen i ζ) =
        (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)) := by
  obtain ⟨π, hπ⟩ := KummerTwistLemmas.twLift i ((restr (ZMod.castHom h (ZMod q))).obj (tw q i))
    (fun U ζ => (show Sec ((restr (ZMod.castHom h (ZMod q))).obj (tw q i)) U from twGen i (pw h ζ)))
    (fun g ζ => by
      change Sec.res g (twGen i (pw h ζ)) = twGen i (pw h (ζ.map g.appTop.hom))
      rw [twGen_res, pw_map])
    (fun U ζ ξ a ha => by
      let a' : (ZMod q)ˣ := ZMod.unitsMap h a
      have hξ : (pw h ξ).1 = (pw h ζ).1 ^ (a' : ZMod q).val := by
        rw [pw_val, pw_val, ha, ← pow_mul, mul_comm, pow_mul]
        have h1 : ((pw h ζ).1) ^ q = 1 := pow_self (pw h ζ)
        rw [← pw_val h ζ, pow_eq_pow_mod _ h1, pow_eq_pow_mod ((a' : ZMod q).val) h1]
        have hv : (a' : ZMod q).val = (a : ZMod Q).val % q := by
          change (ZMod.castHom h (ZMod q) (a : ZMod Q)).val = _
          rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]
        rw [hv, Nat.mod_mod]
      have := ((hG q i).2.2 U (pw h ζ) (pw h ξ) a' hξ)
      change twGen i (pw h ξ) = (ULift.up (ZMod.castHom h (ZMod q) ((a ^ i : (ZMod Q)ˣ) : ZMod Q)) : ULift.{1} (ZMod q)) • twGen i (pw h ζ)
      rw [this, ← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
      congr 1
      apply ULift.ext
      rw [ULift.down_natCast, ZMod.natCast_zmod_val]
      simp only [a', ZMod.unitsMap]
      rw [← map_zpow]
      rfl)
  refine ⟨π, fun U ζ ξ hξ => ?_, hπ⟩
  rw [hπ U ζ, show pw h ζ = ξ from Subtype.ext (show (pw h ζ).1 = ξ.1 from hξ.symm)]

end CrystallineSemistableComparison.TwSeq
end
end

