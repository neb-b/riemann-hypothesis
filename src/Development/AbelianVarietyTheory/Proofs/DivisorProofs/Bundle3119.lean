module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2645
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2106
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2960
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1386
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3115
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDescendingDivisorPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.DescentPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {C : UCompact Xo c}

theorem exists_uCTrait_norm_eqAt (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (φ : InvFun (𝓞 E)) (ι : ℕ) (D : EffCartierData Y.Z)
    (hord : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι)
    (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z) (hy : Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i)
    (z₁ : X₁.M.Z) (hz : πY (y (cPt p)) = z₁) :
    ∃ t : UCTrait X₁ p z₁, t.y = y ≫ πY ∧ ∀ f, EqAt Y D (y (cPt p)) f →
      ‖Y.val (gPt p ≫ y) f‖ = Real.exp (-(t.sc * (ι * φ.evalZ t.T.be))) := by
  obtain ⟨T, ι', j, ξ, hint, hj, hloc, hξ, hT⟩ := _root_.GlobalTheory.UTraitPt.exists_uTrait_of_classicalPoint E H Dw l Xo c C X₁ Y πY p y hy
  have hgen : gPt p ≫ y = spMap ι' ≫ jK T.V ≫ ξ := by
    rw [← hξ, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext v
    exact hj v
  refine ⟨⟨y ≫ πY, ?_, T, ι', hint, ?_⟩, rfl, fun f hf => ?_⟩
  · rw [Scheme.Hom.comp_apply]; exact hz
  · rw [← Category.assoc, ← Category.assoc, hgen]
    simp only [Category.assoc]
    rw [hT]
  · obtain ⟨tK, h1, h2⟩ := T.gen
    obtain ⟨a, ha, hI⟩ := hord T.V T.cdvr T.ϖ T.irr ξ T.y (by rw [← hT]) trivial T.t tK h1 h2 T.P T.be T.lev T.mono
    have hc : ξ (closedPoint T.V) = y (cPt p) := by
      rw [← hξ, Scheme.Hom.comp_apply]
      exact congrArg ξ (IsLocalRing.comap_closedPoint j).symm
    rw [← hc] at hf
    have key := _root_.GlobalTheory.Poinc.EqNormAt.norm_val_eqAt _ _ Y D T.V T.ϖ a ξ p ι' j hint hj hI f hf
    rw [hξ] at key
    have hpos : 0 < ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ := by
      refine norm_pos_iff.2 ?_
      rw [map_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact T.irr.ne_zero
    show _ = Real.exp (-(-Real.log ‖ι' (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (ι * φ.evalZ T.be)))
    rw [key, ← ha, neg_mul, neg_neg, mul_comm, Real.exp_nat_mul, Real.exp_log hpos]

theorem val_comp_of_centre (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z)
    (hHom : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY) {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z) {z : X₁.M.Z}
    (hz : πY (y (cPt q)) = z) {a : X₁.Ω₁} (ha : a ∈ X₁.M.O z) :
    Y.val (gPt q ≫ y) a = X₁.M.val (gPt q ≫ y ≫ πY) a := by
  have hs : πY ((gPt q ≫ y) (closedPoint (PadicAlgCl q))) ⤳ z :=
    hz ▸ (RatModel.gPt_specializes (M := Y) rfl _).map πY.continuous
  have := hHom.val_comp (gPt q ≫ y) (closedPoint (PadicAlgCl q)) (RatModel.O_le_of_specializes hs ha)
  rw [← Category.assoc]
  exact this.symm

theorem exists_idealSheaf_comap_uValThru : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (ι : ℕ) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (D : GlobalTheory.EffCartierData Y.Z), 1 ≤ ι → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → IsProper πY → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y.Z → (∀ y ∈ D.idealSheaf.support, X₁.π (πY y) ∉ Set.range C.i) → UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ D.idealSheaf ι → ∃ (ι' : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι' ∧ (∀ y ∈ (J₁.comap πY).support, X₁.π (πY y) ∉ Set.range C.i) ∧ UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (J₁.comap πY) ι' := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C X₁ ι Y πY D hι hHom hprop hnorm hsupp hord
  obtain ⟨d, hd, hA⟩ := _root_.GlobalTheory.UPoinc.exists_uApproxAt E H Dw hpq l Xo c C X₁ φ hφ
  obtain ⟨k, hk⟩ : ι ∣ Nat.lcm ι d := Nat.dvd_lcm_left ι d
  obtain ⟨m, hm⟩ : d ∣ Nat.lcm ι d := Nat.dvd_lcm_right ι d
  have hL0 : 0 < Nat.lcm ι d := Nat.lcm_pos hι hd
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hk; omega
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hm; omega
  have hAL : UApproxAt X₁ φ (Nat.lcm ι d) := hm ▸ _root_.GlobalTheory.UPoinc.uApproxAt_mul E H Dw l Xo c C X₁ φ d m hm0 hA

  have hord' : UValThru Xo c C.i (πY ≫ X₁.π) Set.univ φ (D.nsmul k).idealSheaf (Nat.lcm ι d) := by
    intro W _ _ _ hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono
    obtain ⟨a, ha, hI⟩ := hord W hW ϖ hϖ χ y hy hA' t tK h1 h2 P be hbe hmono
    refine ⟨k * a, ?_, ?_⟩
    · rw [hk]; push_cast; rw [ha]; ring
    · rw [GlobalTheory.TorRef.Scale.idlAlong_nsmul, hI, Ideal.span_singleton_pow, ← pow_mul, mul_comm a k]
  have hsub : ∀ y ∈ (D.nsmul k).idealSheaf.support, y ∈ D.idealSheaf.support := by
    intro y hy
    obtain ⟨j, hj⟩ := D.exists_mem y
    rw [(D.nsmul k).mem_support_iff j hj] at hy
    rw [D.mem_support_iff j hj]
    intro h
    apply hy
    change y ∈ Y.Z.basicOpen (D.f j ^ k)
    rw [Scheme.basicOpen_pow _ _ hk0]
    exact h

  obtain ⟨W, hWi, hWc⟩ := _root_.GlobalTheory.UPoinc.exists_open_generic_subset_moduli E H Dw l Xo c C
  let U : Y.Z.Opens := (πY ≫ X₁.π) ⁻¹ᵁ W ⊓ ⟨((D.nsmul k).idealSheaf.support : Set Y.Z)ᶜ, (D.nsmul k).idealSheaf.support.isClosed.isOpen_compl⟩
  have hU : (U : Set Y.Z).Nonempty := by
    have e : Y.pt ≫ πY ≫ X₁.π = spMap (AlgHom.id X₁.o₁ X₁.Ω₁).toRingHom ≫ spMap (ratHull X₁.S.R).val.toRingHom ≫ X₁.u ≫ C.i := by
      rw [← Category.assoc, hHom, Category.assoc, X₁.comp]
    have e' := congrArg (fun h : Sp X₁.Ω₁ ⟶ C.Z => h (closedPoint X₁.Ω₁)) e
    simp only [Scheme.Hom.comp_apply] at e'
    have hr : X₁.π (πY (Y.pt (closedPoint X₁.Ω₁))) ∈ Set.range C.i := ⟨_, e'.symm⟩
    refine ⟨Y.pt (closedPoint X₁.Ω₁), ?_, ?_⟩
    · show (πY ≫ X₁.π) _ ∈ (W : Set C.Z)
      rw [Scheme.Hom.comp_apply]
      exact hWi hr
    · intro hs
      exact hsupp _ (hsub _ hs) hr
  have hDU : ∀ x ∈ (D.nsmul k).idealSheaf.support, x ∉ U := fun x hx hxU => hxU.2 hx
  have hrange : ∀ {q : ℕ} [Fact q.Prime] (y : Sp (OO q) ⟶ Y.Z), Set.range (gPt q ≫ y) ⊆ U →
      Set.range (gPt q ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range C.i := by
    intro q _ y hy
    have h := hWc q (y ≫ πY ≫ X₁.π) (by
      rintro _ ⟨w, rfl⟩
      have h1 : (πY ≫ X₁.π) ((gPt q ≫ y) w) ∈ (W : Set C.Z) := (hy ⟨w, rfl⟩).1
      simpa only [Scheme.Hom.comp_apply] using h1)
    simpa only [Category.assoc] using h
  obtain ⟨J, hJ⟩ := _root_.GlobalTheory.Poinc.exists_idealSheaf_comap_eq_of_approx X₁.o₁ X₁.Ω₁ X₁.M Y πY hHom hprop (@GlobalTheory.IsNormalScheme.pred _ X₁.normal) hnorm U (D.nsmul k) hU hDU (by
    intro z₀ _ x hxz hx
    obtain ⟨p, hp, y₀, hcen⟩ := _root_.GlobalTheory.Poinc.exists_cen_main _ _ Y x hx U hU
    obtain ⟨c₀, hc₀y, hc₀⟩ := exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y₀ (hrange y₀ hcen.2) z₀
      (by rw [hcen.1, hxz])
    refine ⟨p, hp, y₀, hcen, fun e => ?_⟩
    obtain ⟨f, hf0, hfall⟩ := hAL p z₀ c₀ e
    have hfO : X₁.M.stalkHom z₀ f ∈ X₁.M.O z₀ := (X₁.M.stalkEquiv z₀ f).2
    refine ⟨X₁.M.stalkHom z₀ f, hfO, fun f' hf' => ?_, ?_⟩
    · rw [hc₀ f' (hcen.1 ▸ hf'), val_comp_of_centre X₁ Y πY hHom y₀ (by rw [hcen.1, hxz]) hfO, ← hf0]
      show _ = ‖X₁.M.val (gPt p ≫ c₀.y) _‖
      rw [hc₀y]
    · intro q hq y hyz hyU f' hf'
      have hpq : p = q := _root_.GlobalTheory.Poinc.eq_of_cPt_eq X₁.M.Z p q (y₀ ≫ πY) (y ≫ πY) (by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hcen.1, hxz, hyz])
      subst hpq
      obtain ⟨t, hty, ht⟩ := exists_uCTrait_norm_eqAt X₁ Y πY φ (Nat.lcm ι d) (D.nsmul k) hord' p y (hrange y hyU) z₀ hyz
      have hcv : ∀ a, t.val a = Y.val (gPt p ≫ y) (X₁.M.stalkHom z₀ a) := fun a => by
        rw [val_comp_of_centre X₁ Y πY hHom y hyz (a := X₁.M.stalkHom z₀ a) (X₁.M.stalkEquiv z₀ a).2]
        show X₁.M.val (gPt p ≫ t.y) _ = _
        rw [hty]
      rcases hfall t with h1 | ⟨h, hh, h2⟩
      · left
        rw [← hcv, ht f' hf']
        exact h1
      · right
        refine ⟨X₁.M.stalkHom z₀ h, ⟨(X₁.M.stalkEquiv z₀ h).2, ?_⟩, ?_⟩
        · by_contra hne
          push_neg at hne
          apply (IsLocalRing.mem_maximalIdeal _).1 hh
          have hu : IsUnit (X₁.M.stalkEquiv z₀ h) :=
            (RatModel.isUnit_O_iff _).2 ⟨hne.1, hne.2⟩
          exact (MulEquiv.isUnit_map (X₁.M.stalkEquiv z₀)).1 hu
        · rw [← hcv, ← hcv]
          exact h2)
  refine ⟨Nat.lcm ι d, J, hL0, ?_, ?_⟩
  · rw [hJ]
    intro y hy
    exact hsupp y (hsub y hy)
  · rw [hJ]
    exact hord'

end GlobalTheory.UPoinc.DescentPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsReferenceGeometrySameGeneric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.PadicTate

theorem exists_padic_similitude : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z)))) := by
  intro p _ D R _ b N hN3 hN S s o k _ _ _ x β hβ
  have hp : p.Prime := Fact.out
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hB : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ o.ab o.ab
  have ub := GlobalTheory.Ex.Specialise.unitOn_bijective (R := k)
  let Q := Over.mk x ⟶ o.A
  let act : D.O → Q → Q := fun c g => g ≫ o.act.act c
  let E : ℕ → Q → Q → kˣ → Prop := fun n g g' z =>
    Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)
  have amul : ∀ c a b, act c (a * b) = act c a * act c b := fun c a b => by
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have apow : ∀ c (a : Q) n, a ^ n = 1 → act c a ^ n = 1 := fun c a n h => by
    haveI := o.act.hom c
    show (a ≫ _) ^ n = 1
    rw [← MonObj.pow_comp, h, MonObj.one_comp]
  have powl : ∀ (n : ℕ) (a b : Q), (lift a b) ^ n = lift (a ^ n) (b ^ n) := by
    intro n a b
    ext <;> simp [MonObj.pow_comp]
  have ex : ∀ (n : ℕ) (a b : Q), ∃ c : kˣ, 0 < n → a ^ n = 1 → b ^ n = 1 →
      Out.WeilIs (G2 o.A) o.P n (lift a 1) (lift 1 b) (unitOn c) := fun n a b => by
    by_cases h : 0 < n ∧ a ^ n = 1 ∧ b ^ n = 1
    · obtain ⟨c, -, hc⟩ := GlobalTheory.ProdPairing.exists_weilIs_prod_root S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.ample n h.1 _
        (lift a 1) (lift 1 b) (by rw [powl, h.2.1, one_pow]; ext <;> simp) (by rw [powl, h.2.2, one_pow]; ext <;> simp)
      obtain ⟨c, rfl⟩ := ub.2 c
      exact ⟨c, fun _ _ _ => hc⟩
    · exact ⟨1, fun h₁ h₂ h₃ => absurd ⟨h₁, h₂, h₃⟩ h⟩
  choose W hW using ex
  have uq : ∀ {n : ℤ} {X Y : Over.mk x ⟶ G2 o.A} {c c' : kˣ}, Out.WeilIs (G2 o.A) o.P n X Y (unitOn c) →
      Out.WeilIs (G2 o.A) o.P n X Y (unitOn c') → c = c' := fun h h' =>
    ub.1 (CommutatorPairing.weilIs_unique hG hB o.isLB h h')
  have upow : ∀ (c : kˣ) (m : ℕ), unitOn (c ^ m) = unitOn c ^ m := fun c m => map_pow _ _ _
  have umul : ∀ c c' : kˣ, unitOn (c * c') = unitOn c * unitOn c' := fun c m => map_mul _ _ _
  have uone : unitOn (1 : kˣ) = 1 := map_one _
  have hE : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → E n a b (W n a b ^ 2) := fun n hn a b ha hb => by
    have h := GlobalTheory.DiagSqAxes.weilIs_diag_sq S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm k x n hn
      (Nat.cast_ne_zero.2 hn.ne') a b ha hb _ (hW n a b hn ha hb)
    rw [← upow] at h
    exact h
  have lev : ∀ n m, 0 < n → 0 < m → ∀ a b : Q, a ^ (n * m) = 1 → b ^ (n * m) = 1 →
      W n (a ^ m) (b ^ m) = W (n * m) a b ^ m := fun n m hn hm a b ha hb => by
    have h := GlobalTheory.LevelChangePairing.weilIs_levelChange S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ k x n m hn hm
      (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne') a b ha hb _ (hW (n * m) a b (Nat.mul_pos hn hm) ha hb)
    rw [← upow] at h
    exact uq (hW n _ _ hn (by rw [← pow_mul, mul_comm, ha]) (by rw [← pow_mul, mul_comm, hb])) h
  have wmul : ∀ n, 0 < n → ∀ a a' b : Q, a ^ n = 1 → a' ^ n = 1 → b ^ n = 1 →
      W n (a * a') b = W n a b * W n a' b := fun n hn a a' b ha ha' hb => by
    have h := GlobalTheory.SiegelTypings.weilIs_mul hB o.isLB (hW n a b hn ha hb) (hW n a' b hn ha' hb)
    have e : lift a (1 : Q) * lift a' 1 = lift (a * a') 1 := by ext <;> simp [MonObj.mul_comp]
    rw [← umul, e] at h
    exact uq (hW n _ _ hn (by rw [mul_pow, ha, ha', _root_.mul_one]) hb) h
  have wskew : ∀ n, 0 < n → ∀ a b : Q, a ^ n = 1 → b ^ n = 1 → W n a b * W n b a = 1 := fun n hn a b ha hb => by
    have h := GlobalTheory.SwapPairing.weilIs_swap_eq S o.A o.P o.ab o.isLB o.symm n _ a b _ _
      (CommPairing.weilIs_symm o.isLB (hW n b a hn hb ha)) (hW n a b hn ha hb)
    apply ub.1
    rw [umul, ← h, uone, inv_mul_cancel]
  have wadj : ∀ n, 0 < n → ∀ (c : D.O) (a b : Q), a ^ n = 1 → b ^ n = 1 →
      W n (act c a) b = W n a (act (D.star c).unop b) := fun n hn c a b ha hb =>
    ub.1 (GlobalTheory.AdjPairing.weilIs_adj_eq S o.A o.P o.ab o.isLB _ _ (o.act.hom c) (o.act.hom _) (o.rosati c) n _ a b _ _
      (hW n _ b hn (apow c a n ha) hb) (hW n a _ hn ha (apow _ b n hb)))
  have wnd : ∀ r, ∀ a : Q, a ^ (p ^ r) = 1 → (∀ b : Q, b ^ (p ^ r) = 1 → W (p ^ r) a b = 1) → a = 1 := by
    intro r a ha h
    have hq : 0 < p ^ r := pow_pos hp.pos r
    obtain ⟨e, he, hk⟩ := o.kerP
    have h1 := hk _ a (GlobalTheory.WeilKernel.triv_slice_of_forall_weilIs_one S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ k x (p ^ r) (Nat.cast_ne_zero.2 hq.ne') a ha
      fun b hb => by
        have := hW _ a b hq ha hb
        rwa [h b hb, uone] at this)
    have h2 := pow_gcd_eq_one.2 ⟨h1, ha⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right r he), pow_one] at h2
  obtain ⟨ζ, hζ, hζ'⟩ := GlobalTheory.T.exists_compatible_prime_power_roots p k
  obtain ⟨ev, hev, hev'⟩ := GlobalTheory.T.exists_compatible_similitude_level_tower p D k Q act (fun r => W (p ^ r)) ζ amul hζ'
    (fun r a b ha hb => lev (p ^ r) p (pow_pos hp.pos r) hp.pos a b ha hb) fun r => by
      obtain ⟨f, hf⟩ := GlobalTheory.T.exists_level_evaluation_hom p D R b N hN3 hN S s o k x β hβ r
      have hq : 0 < p ^ r := pow_pos hp.pos r
      exact GlobalTheory.T.exists_level_pairing_eq_alt p D k Q act r (W (p ^ r)) (ζ r) (hζ r) (wmul _ hq) (wskew _ hq) (wadj _ hq) (wnd r) f hf
  refine ⟨ζ, ev, hζ, hζ', fun r => (hev r).1.1, fun r => (hev r).1.2.1, fun r => (hev r).1.2.2.1,
    fun r => (hev r).1.2.2.2, hev', fun r y z => ?_⟩
  have hq : 0 < p ^ r := pow_pos hp.pos r
  have h := hE _ hq (ev r y) (ev r z) (((hev r).1.2.2.2 _).2 ⟨y, rfl⟩) (((hev r).1.2.2.2 _).2 ⟨z, rfl⟩)
  have e := (hev r).2 y z
  rw [e, ← zpow_natCast, ← zpow_mul, mul_comm] at h
  simp only [E, Nat.cast_pow] at h
  exact h

end GlobalTheory.UPel.HT.PadicTate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricPointAbelianVarietyAction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_point_abelian_variety_action : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  have push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
      (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A))
      (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
      (z : T ⟶ (Over.pullback x).obj A) :
      e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
    have map_fst : ((Over.pullback x).map f).left ≫ pullback.fst A.hom x =
        pullback.fst A.hom x ≫ f.left := by
      simp only [Over.pullback_map_left, pullback.lift_fst]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, map_fst, Category.assoc]
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseChaStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_structures_representable_siegel_baseChange : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  first | (exact @GlobalTheory.UPel.HT.relRep_siegel) | (exact GlobalTheory.UPel.HT.relRep_siegel) | (intros; apply GlobalTheory.UPel.HT.relRep_siegel  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTangentInjectiveAwayFromEtalePlaceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_tangent_injective_away_from_etalePlace : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (c : 𝓞 D.F), c ≠ 0 → (∀ w : Ideal (𝓞 D.F), w.IsMaximal → ((p : ℕ) : 𝓞 D.F) ∈ w → w ≠ w0 → c ∉ w) → ∀ v : epsPtR x ⟶ o.A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.TanInj.tan_eq_one_of_notMem) | (exact GlobalTheory.UPel.HT.EtLev.TanInj.tan_eq_one_of_notMem) | (intros; apply GlobalTheory.UPel.HT.EtLev.TanInj.tan_eq_one_of_notMem  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSemiAbelianUniformisationCompleteNormalBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isSemiAbelian_of_isGrpPullback' {S T : Scheme.{0}} {f : T ⟶ S} {G : Over S} [GrpObj G] {G' : Over T} [GrpObj G']
    [IsCommMonObj G'] {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

theorem has_of_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ D : DegData R (maximalIdeal R), Has D := by
  intro R _ _ _ hB D
  rcases subsingleton_or_nontrivial D.toPre.X with hX | hX
  · exact GlobalTheory.Mum.has_of_subsingleton R hB.1 D hX
  obtain ⟨E, _, _, _, H, Dm, D', hmod, o, hPel, F, hA⟩ := GlobalTheory.T.exists_unitaryPELType_factor_degData R hB D hX
  have hX' : Nontrivial D'.toPre.X :=
    (Function.LeftInverse.injective (g := F.xp) (f := F.xi) F.xp_xi).nontrivial
  obtain ⟨R', _, _, _, ρ, D'', hρ, hpull, hcov⟩ := GlobalTheory.T.exists_labelledCover_unitaryPELType_finiteExt R hB E H Dm D' o hX' hPel
  have hB' : Base R' := ⟨hρ.1, @charZero_of_injective_ringHom _ _ _ _ ρ hρ.2.1 hB.2⟩
  have hfin'' : HasFin D'' := _root_.GlobalTheory.Mum.hasFin_of_labCover R' hB' D'' hcov
  have hfin' : HasFin D' := GlobalTheory.Mum.hasFin_of_finExt R R' ρ hρ D' D'' hpull hfin''
  obtain ⟨G', _, _, A', hG', ⟨U'⟩⟩ := _root_.GlobalTheory.Mum.has_of_hasFin R hB D' hfin'
  obtain ⟨oA, oG, hlin⟩ := _root_.GlobalTheory.Mum.exists_oLinear_of_oAct R hB D' A' G' hG' U' F.O F.o
  have hidem : oG.act F.e ≫ oG.act F.e = oG.act F.e := by rw [← oG.map_mul, F.idem]
  obtain ⟨G, _, _, inc, pr, hG, hinc, hpr, hip, hpi⟩ :=
    GlobalTheory.Mum.IdemImage.isSemiAbelian_image (Sp R) G' hG' (oG.act F.e) (oG.hom F.e) hidem
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β, β₂, A₁, U₁, hρ₁, hpull₁, hgp, -, -⟩ :=
    _root_.GlobalTheory.Mum.factor_unif R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  exact _root_.GlobalTheory.Mum.has_of_hasFin R hB D
    ⟨R₁, _, _, _, ρ₁, D₁, hρ₁, hpull₁, G₁, _, _, A₁, isSemiAbelian_of_isGrpPullback' hgp hG, ⟨U₁⟩⟩
end GlobalTheory.Mum
end

