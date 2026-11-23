module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0828
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0021
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPullIsog
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

open GlobalTheory.CechPic GlobalTheory.UPel.HT.ES.PIsogExt

theorem UpperTheory.Gal.crystallineComparison.Mod.pullIsog_of :
    PullIsog := by
  intro p _ D R _ b N S S' s s' f hs c o o' ψ hψ o₁ m
  subst hs
  have hcpos : 0 < c := hψ.pos
  obtain ⟨hk, hmon, hact, heta, ⟨hiso⟩, ψ', hmon', h₁, h₂⟩ := hψ
  haveI := hmon
  haveI := hmon'
  obtain ⟨o₁', ⟨m'⟩⟩ := _root_.GlobalTheory.HTPull.exists_objMap_pull p D R b N S S' s f o'
  let ψ₁ : o₁.A ⟶ o₁'.A := Over.homMk (m'.cart.1.lift (m.φ ≫ ψ.left) o₁.A.hom
    (by rw [Category.assoc, Over.w ψ, m.cart.1.w])) (m'.cart.1.lift_snd _ _ _)
  let ψ₁' : o₁'.A ⟶ o₁.A := Over.homMk (m.cart.1.lift (m'.φ ≫ ψ'.left) o₁'.A.hom
    (by rw [Category.assoc, Over.w ψ', m'.cart.1.w])) (m.cart.1.lift_snd _ _ _)
  have e : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ := (m'.cart.1.lift_fst _ _ _).symm
  have e' : m'.φ ≫ ψ'.left = ψ₁'.left ≫ m.φ := (m.cart.1.lift_fst _ _ _).symm
  have pt : ∀ (T : Over S') (x : T ⟶ o₁.A), m'.ptEquiv T (x ≫ ψ₁) = m.ptEquiv T x ≫ ψ := fun T x =>
    Over.OverMorphism.ext (by
      rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, Category.assoc, e])
  have pt' : ∀ (T : Over S') (x : T ⟶ o₁'.A), m.ptEquiv T (x ≫ ψ₁') = m'.ptEquiv T x ≫ ψ' := fun T x =>
    Over.OverMorphism.ext (by
      rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, Category.assoc, e'])
  have mh : IsMonHom ψ₁ := GlobalTheory.GrpPullPow.isMonHom_of_mul_pts ψ₁ fun T x y => (m'.ptEquiv T).injective (by
    rw [map_mul, pt, pt, pt, map_mul, MonObj.mul_comp])
  have mh' : IsMonHom ψ₁' := GlobalTheory.GrpPullPow.isMonHom_of_mul_pts ψ₁' fun T x y => (m.ptEquiv T).injective (by
    rw [map_mul, pt', pt', pt', map_mul, MonObj.mul_comp])
  have hsq := isSquare_square_compatible_homs m.sq m'.sq e
  have hcL : ∀ {X : Scheme.{0}} (L : LB X) (hL : L.IsLB) (h : (Hecke.lbPow L c).IsLB), cls _ h = c • cls L hL :=
    fun {X} L hL h => (cls_linComb (L := L) hL (fun _ => 𝟙 X) (fun _ => 1) h).trans (by simp [pull_id])
  have hL₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
  have hM₁ : (o₁'.P.pull (sq2 ψ₁)).IsLB := pull_isLB o₁'.isLB _
  have e1 := (cls_eq_iff o₁'.isLB (pull_isLB o'.isLB _)).2 m'.pol
  have e2 := (cls_eq_iff o₁.isLB (pull_isLB o.isLB _)).2 m.pol
  have hL₀ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have e3 : cls _ hL₀ = cls _ (pull_isLB o'.isLB (sq2 ψ)) := (cls_eq_iff hL₀ (pull_isLB o'.isLB (sq2 ψ))).2 hiso
  have ext₁ : ∀ {T : Over S'} (g h : T ⟶ o₁.A), g.left ≫ m.φ = h.left ≫ m.φ → g = h := fun g h H =>
    Over.OverMorphism.ext (m.cart.1.hom_ext H (by simp))
  have ext₂ : ∀ {T : Over S'} (g h : T ⟶ o₁'.A), g.left ≫ m'.φ = h.left ≫ m'.φ → g = h := fun g h H =>
    Over.OverMorphism.ext (m'.cart.1.hom_ext H (by simp))
  have hcls : cls _ hL₁ = cls _ hM₁ := by
    calc cls _ hL₁ = c • cls o₁.P o₁.isLB := hcL _ _ _
      _ = c • pull m.φ₂ (cls o.P o.isLB) := by rw [e2, cls_pull o.isLB]
      _ = pull m.φ₂ (c • cls o.P o.isLB) := (map_nsmul _ _ _).symm
      _ = pull m.φ₂ (cls _ (pull_isLB o'.isLB (sq2 ψ))) := by
        rw [← hcL o.P o.isLB hL₀, e3]
      _ = pull (m.φ₂ ≫ sq2 ψ) (cls o'.P o'.isLB) := by rw [cls_pull o'.isLB, pull_comp]
      _ = pull (sq2 ψ₁) (pull m'.φ₂ (cls o'.P o'.isLB)) := by rw [hsq, pull_comp]
      _ = pull (sq2 ψ₁) (cls o₁'.P o₁'.isLB) := by rw [e1, cls_pull o'.isLB]
      _ = cls _ hM₁ := (cls_pull o₁'.isLB _ _).symm
  refine ⟨o₁', m', ψ₁, ⟨hk, mh, fun c' => ?_, fun x => ?_, ⟨(cls_eq_iff hL₁ hM₁).1 hcls⟩, ψ₁', mh', ?_, ?_⟩, e⟩
  · refine ext₂ _ _ ?_
    have h := congrArg (fun q => m.φ ≫ q.left) (hact c')
    simp only [Over.comp_left] at h ⊢
    rw [Category.assoc, ← e, ← Category.assoc, m.act c', Category.assoc, h, Category.assoc, m'.act c',
      ← Category.assoc (Over.Hom.left ψ₁), ← e, Category.assoc]
  · refine ext₂ _ _ ?_
    rw [m'.eta x, heta x, Over.comp_left, Over.comp_left, Category.assoc, ← e,
      ← Category.assoc (Over.Hom.left (o₁.eta x)), m.eta x, Category.assoc]
  · refine ext₁ _ _ ?_
    rw [Over.comp_left, Category.assoc, ← e', ← Category.assoc, ← e, Category.assoc, ← Over.comp_left, h₁,
      pow_comp_of_isGrpPullback m.cart c hcpos]
  · refine ext₂ _ _ ?_
    rw [Over.comp_left, Category.assoc, ← e, ← Category.assoc, ← e', Category.assoc, ← Over.comp_left, h₂,
      pow_comp_of_isGrpPullback m'.cart c hcpos]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MPulledRead
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.pulledRead_of :
    PullKer → PulledRead := by
  intro hKer p _ D R _ b N M r w j c T S x σ o₁ m₁ y hy P a
  have hw : (a.left ≫ P.m₀.φ) ≫ T.o.A.hom = y := by
    have h1 := P.m₀.cart.1.w
    have h2 : a.left ≫ o₁.A.hom = 𝟙 S := Over.w a
    rw [Category.assoc, h1, ← Category.assoc, h2]
    exact Category.id_comp y
  have htri : (a.left ≫ P.m₀.φ) ≫ T.ms.φ = a.left ≫ m₁.φ := by
    rw [Category.assoc, P.tri]
  let a₀ : Over.mk y ⟶ T.o.A := Over.homMk (a.left ≫ P.m₀.φ) hw
  have ha₀ : a₀.left = a.left ≫ P.m₀.φ := rfl
  have hk := ((hKer p D R b N T.Y S (T.s ≫ M.s) σ y T.o T.o' o₁ P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
    (𝟙_ (Over S)) (Over.mk y) rfl a a₀ (by simp [ha₀])).1
  refine ⟨⟨fun h a' ha' => ?_, fun h => ?_⟩, fun h => ?_⟩
  · have hEq : a' = a₀ := by
      apply Over.OverMorphism.ext
      apply T.ms.cart.1.hom_ext
      · rw [ha', ha₀, htri]
      · have h3 : a'.left ≫ T.o.A.hom = y := Over.w a'
        rw [h3, ha₀, hw]
    rw [hEq]
    exact hk.1 h
  · exact hk.2 (h a₀ (by rw [ha₀, htri]))
  · have hl : T.ms.cart.1.lift (a.left ≫ m₁.φ) y h = a.left ≫ P.m₀.φ := by
      apply T.ms.cart.1.hom_ext
      · rw [T.ms.cart.1.lift_fst, htri]
      · rw [T.ms.cart.1.lift_snd, hw]
    unfold TjD.img
    rw [hl, Over.comp_left]
    simp only [Category.assoc]
    rw [reassoc_of% P.sq]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecCard
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.secCard_of :
    SecCard := by
  intro p _ D R _ b N M r w j c T hm K _ _ hp x y hxy
  subst hxy
  let β : R →+* K := (Spec.preimage (y ≫ T.s ≫ M.s)).hom
  haveI : CharZero K := by
    rcases CharP.char_is_prime_or_zero K (ringChar K) with hq | hq
    · exfalso
      have hcast : ((ringChar K : ℕ) : K) = 0 := ringChar.Nat.cast_ringChar
      by_cases hqp : ringChar K = p
      · rw [hqp] at hcast
        exact hp hcast
      · have hcop : (ringChar K).Coprime p := (Nat.coprime_primes hq (Fact.out)).mpr hqp
        have hu := (b.unit _ hcop).map β
        rw [map_natCast, hcast] at hu
        exact not_isUnit_zero hu
    · haveI : CharP K 0 := ringChar.of_eq hq
      exact CharP.charP_to_charZero K
  obtain ⟨-, hcard⟩ := T.tj K y
  rw [hm, Nat.one_mul] at hcard
  rw [← hcard]
  symm
  have hK : ∀ a : Over.mk y ⟶ T.o.A,
      KilledBy T.o w a ↔ KilledBy M.univ w (T.ms.ptEquiv (Over.mk y) a) := by
    intro a
    unfold KilledBy
    refine forall₂_congr (fun c _ => ?_)
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]
  have hker : ∀ a : Over.mk y ⟶ T.o.A,
      KerAt T y (T.ms.ptEquiv (Over.mk y) a).left ↔ a ≫ T.ψ = 1 := by
    intro a
    rw [ObjMap.ptEquiv_left]
    constructor
    · intro h
      exact h a rfl
    · intro h a' ha'
      have ha : a' = a := by
        apply (T.ms.ptEquiv (Over.mk y)).injective
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left, ObjMap.ptEquiv_left, ha']
      rw [ha]
      exact h
  refine Nat.card_congr (Equiv.subtypeEquiv (T.ms.ptEquiv (Over.mk y)).toEquiv (fun a => ?_))
  exact ⟨fun h => ⟨(hK a).mp h.2, (hker a).mpr h.1⟩, fun h => ⟨(hker a).mp h.2, (hK a).mpr h.1⟩⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MSecEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem kerAt_sub {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N}
    {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (x : X ⟶ M.X) (hz : z ≫ T.s = x) :
    ∃ K : Subgroup (Over.mk x ⟶ M.univ.A), (∀ g, g ∈ K ↔ KerAt T z g.left) ∧
      ∀ g ∈ K, ∀ a : D.O, g ≫ M.univ.act.act a ∈ K := by
  subst hz
  obtain ⟨-, hmon, hact, -⟩ := T.isog
  haveI := hmon
  let e := T.ms.ptEquiv (Over.mk z)
  have key : ∀ g : Over.mk (z ≫ T.s) ⟶ M.univ.A, KerAt T z g.left ↔ e.symm g ≫ T.ψ = 1 := by
    intro g
    constructor
    · intro h
      apply h
      rw [← ObjMap.ptEquiv_left, MulEquiv.apply_symm_apply]
    · intro h a' ha'
      have hq : a' = e.symm g := by
        apply e.injective
        rw [MulEquiv.apply_symm_apply]
        apply Over.OverMorphism.ext
        rw [ObjMap.ptEquiv_left]
        exact ha'
      rw [hq]
      exact h
  let f : (Over.mk z ⟶ T.o.A) →* (Over.mk z ⟶ T.o'.A) :=
    { toFun := fun a => a ≫ T.ψ
      map_one' := MonObj.one_comp _
      map_mul' := fun a b => MonObj.mul_comp a b _ }
  refine ⟨f.ker.comap e.symm.toMonoidHom, fun g => (key g).symm, ?_⟩
  intro g hg a
  have hs : e.symm (g ≫ M.univ.act.act a) = e.symm g ≫ T.o.act.act a := by
    apply e.injective
    rw [MulEquiv.apply_symm_apply, ObjMap.ptEquiv_act, MulEquiv.apply_symm_apply]
  haveI := T.o'.act.hom a
  change e.symm (g ≫ M.univ.act.act a) ≫ T.ψ = 1
  change e.symm g ≫ T.ψ = 1 at hg
  rw [hs, Category.assoc, hact a, ← Category.assoc, hg, MonObj.one_comp]

theorem UpperTheory.Gal.crystallineComparison.Mod.secEquiv_of :
    WVal → RankN → ValPtsX → SecCard → SecInj → SecSurj → SecEquiv := by
  intro hW hR hV hC hI hS p _ D O _ _ _ _ f b N r w _ hstd M j hj T V _ _ _ _ hp x W
  obtain ⟨ρ, hρl, hρc, hρk, hρT⟩ := hW p D O b N M w V x
  let q : Sp (FractionRing V) ⟶ Sp V := spMap (algebraMap V (FractionRing V))
  let u : Over.mk (q ≫ x) ⟶ Over.mk x := Over.homMk q rfl
  have hρu : ∀ g, ρ g = u ≫ g := by
    intro g
    apply Over.OverMorphism.ext
    rw [hρl, Over.comp_left]
    rfl
  haveI : IsProper M.univ.A.hom := M.univ.ab.proper
  haveI := T.fin
  obtain ⟨hAu, hAe⟩ := hV _ _ M.univ.A.hom inferInstance V x
  obtain ⟨hYu, hYe⟩ := hV _ _ T.s inferInstance V x
  have uinj : ∀ g g' : Over.mk x ⟶ M.univ.A, u ≫ g = u ≫ g' → g = g' := by
    intro g g' hg
    apply Over.OverMorphism.ext
    apply hAu _ _ (Over.w g) (Over.w g')
    have := congrArg CommaMorphism.left hg
    simpa [u] using this
  have usurj : ∀ g' : Over.mk (q ≫ x) ⟶ M.univ.A, ∃ g, u ≫ g = g' := by
    intro g'
    obtain ⟨gl, hgl, hgl'⟩ := hAe g'.left (Over.w g')
    refine ⟨Over.homMk gl hgl, ?_⟩
    apply Over.OverMorphism.ext
    simpa [u] using hgl'
  have pt0 : W.pt 0 = 1 := by
    have h := W.add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hK := fun z : { z : Sp V ⟶ T.Y // z ≫ T.s = x } => kerAt_sub T z.1 x z.2
  choose Kz hKz hKa using hK
  let U : { z : Sp V ⟶ T.Y // z ≫ T.s = x } → Submodule (𝓞 D.F ⧸ w) W.H := fun z =>
    { carrier := {h | KerAt T z.1 (W.pt h).left}
      add_mem' := by
        intro a c ha hc
        change KerAt T z.1 (W.pt (a + c)).left
        rw [← hKz, W.add]
        exact mul_mem ((hKz z _).2 ha) ((hKz z _).2 hc)
      zero_mem' := by
        change KerAt T z.1 (W.pt 0).left
        rw [← hKz, pt0]
        exact one_mem _
      smul_mem' := by
        intro c h hh
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        change KerAt T z.1 (W.pt _).left
        rw [← hKz, W.smul]
        exact hKa z _ ((hKz z _).2 hh) _ }
  have hU : ∀ z h, h ∈ U z ↔ KerAt T z.1 (W.pt h).left := fun _ _ => Iff.rfl
  have hpK : ((p : ℕ) : FractionRing V) ≠ 0 := by
    intro h0
    apply hp
    apply IsFractionRing.injective V (FractionRing V)
    rw [map_natCast, map_zero]
    exact h0
  let Φ : W.H → (Over.mk (q ≫ x) ⟶ M.univ.A) := fun h => u ≫ W.pt h
  have hΦinj : Function.Injective Φ := fun a c h => W.inj (uinj _ _ h)
  have hΦrange : ∀ g', (∃ h, Φ h = g') ↔ KilledBy M.univ w g' := by
    intro g'
    obtain ⟨g, rfl⟩ := usurj g'
    constructor
    · rintro ⟨h, hh⟩
      have := uinj _ _ hh
      rw [← this, ← hρu, ← hρk]
      exact (W.range _).1 ⟨h, rfl⟩
    · intro hk
      rw [← hρu, ← hρk] at hk
      obtain ⟨h, hh⟩ := (W.range g).2 hk
      exact ⟨h, by simp only [Φ, hh]⟩
  have hΦT : ∀ z h, h ∈ U z ↔ KerAt T (q ≫ z.1) (Φ h).left := by
    intro z h
    rw [hU, hρT r j _ T z.1 z.2, hρu]
  have hcardU : ∀ z, Nat.card (U z) = Ideal.absNorm w ^ j := by
    intro z
    have e1 : (U z) ≃ {g' : Over.mk (q ≫ x) ⟶ M.univ.A //
        KilledBy M.univ w g' ∧ KerAt T (q ≫ z.1) g'.left} :=
      Equiv.ofBijective (fun h => ⟨Φ h.1, (hΦrange _).1 ⟨_, rfl⟩, (hΦT z h.1).1 h.2⟩) (by
        constructor
        · intro a c h
          apply Subtype.ext
          apply hΦinj
          exact congrArg Subtype.val h
        · rintro ⟨g', hk, hT⟩
          obtain ⟨h, rfl⟩ := (hΦrange g').2 hk
          exact ⟨⟨h, (hΦT z h).2 hT⟩, rfl⟩)
    rw [Nat.card_congr e1]
    exact hC p D O b N M r w j _ T hstd.m1 (FractionRing V) hpK (q ≫ x) (q ≫ z.1)
      (by rw [Category.assoc, z.2])
  haveI : Module.Finite (𝓞 D.F ⧸ w) W.H := (hR p D O f b N r w hstd M V hp x W).1
  have hck : Nat.card (𝓞 D.F ⧸ w) = Ideal.absNorm w := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 D.F ⧸ w) := by
    apply Nat.finite_of_card_ne_zero
    rw [hck, hstd.norm]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have h2 : 2 ≤ Ideal.absNorm w := by
    rw [← hck]
    exact Finite.one_lt_card
  have hrk : ∀ z, Module.finrank (𝓞 D.F ⧸ w) (U z) = j := by
    intro z
    apply Nat.pow_right_injective h2
    simp only
    rw [← hcardU z, ← hck, Module.natCard_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := U z)]
  have ptneg : ∀ a, W.pt (-a) = (W.pt a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_right
    rw [← W.add, add_neg_cancel, pt0]
  refine ⟨Equiv.ofBijective (fun z => ⟨U z, hrk z⟩) ⟨?_, ?_⟩, fun z h => Iff.rfl⟩
  · intro z1 z2 hz
    have hUe : U z1 = U z2 := congrArg Subtype.val hz
    apply Subtype.ext
    apply hYu _ _ z1.2 z2.2
    apply hI p D O f b N r w hstd M j hj T (FractionRing V) hpK (q ≫ x) (q ≫ z1.1) (q ≫ z2.1)
      (by rw [Category.assoc, z1.2]) (by rw [Category.assoc, z2.2])
    intro g' hk
    obtain ⟨h, rfl⟩ := (hΦrange g').2 hk
    rw [← hΦT, ← hΦT, hUe]
  · rintro ⟨Us, hrank⟩
    let GK : Subgroup (Over.mk (q ≫ x) ⟶ M.univ.A) :=
      { carrier := {g' | ∃ h ∈ Us, Φ h = g'}
        one_mem' := ⟨0, Us.zero_mem, by simp only [Φ, pt0, MonObj.comp_one]⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, rfl⟩ ⟨c, hc, rfl⟩
          exact ⟨a + c, Us.add_mem ha hc, by simp only [Φ, W.add, MonObj.comp_mul]⟩
        inv_mem' := by
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨-a, Us.neg_mem ha, by simp only [Φ, ptneg, GrpObj.comp_inv]⟩ }
    have hmem : ∀ h, Φ h ∈ GK ↔ h ∈ Us := by
      intro h
      constructor
      · rintro ⟨h', hh', he⟩
        rw [← hΦinj he]
        exact hh'
      · intro hh
        exact ⟨h, hh, rfl⟩
    have hcardG : Nat.card GK = Ideal.absNorm w ^ j := by
      have e2 : Us ≃ GK := Equiv.ofBijective (fun h => ⟨Φ h.1, (hmem h.1).2 h.2⟩) (by
        constructor
        · intro a c h
          apply Subtype.ext
          apply hΦinj
          exact congrArg Subtype.val h
        · rintro ⟨g', h, hh, rfl⟩
          exact ⟨⟨h, hh⟩, rfl⟩)
      rw [← Nat.card_congr e2, Module.natCard_eq_pow_finrank (K := 𝓞 D.F ⧸ w) (V := Us), hck, hrank]
    obtain ⟨y, hys, hyG⟩ := hS p D O f b N r w hstd M j hj T (FractionRing V) hpK (q ≫ x) GK
      (by
        rintro _ ⟨h, -, rfl⟩
        exact (hΦrange _).1 ⟨h, rfl⟩)
      (by
        rintro _ ⟨h, hh, rfl⟩ a
        refine ⟨Ideal.Quotient.mk w a • h, Us.smul_mem _ hh, ?_⟩
        simp only [Φ, W.smul, Category.assoc])
      hcardG
    obtain ⟨z, hzs, hzq⟩ := hYe y hys
    refine ⟨⟨z, hzs⟩, ?_⟩
    apply Subtype.ext
    ext h
    change h ∈ U ⟨z, hzs⟩ ↔ h ∈ Us
    rw [hΦT, ← hmem]
    change KerAt T (q ≫ z) _ ↔ _
    rw [hzq]
    exact hyG _ ((hΦrange _).1 ⟨h, rfl⟩)
end

