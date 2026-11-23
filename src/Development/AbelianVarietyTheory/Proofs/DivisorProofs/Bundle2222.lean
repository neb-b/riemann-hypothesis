module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0242
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilySurjectiveIffGeometricPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

namespace GlobalTheory.TorsCount

variable {κ Q : Type} [Fintype κ] [Group Q]

theorem map_zero_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c) :
    e 0 = 1 := by
  have h := hadd 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem map_sub_of_add {L : Type} [AddCommGroup L] (e : L → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (a c : L) : e (a - c) = e a * (e c)⁻¹ := by
  have h := hadd (a - c) c
  rw [sub_add_cancel] at h
  rw [h, mul_inv_cancel_right]

def red (M : ℕ) (e : (κ → ℤ) → Q) (hpow : ∀ a, e a ^ M = 1) : (κ → ZMod M) → {g : Q // g ^ M = 1} :=
  fun c => ⟨e fun i => ((c i).val : ℤ), hpow _⟩

theorem exists_red (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) (a : κ → ℤ) :
    ∃ c : κ → ZMod M, e (fun i => ((c i).val : ℤ)) = e a := by
  refine ⟨fun i => (a i : ZMod M), ?_⟩
  have h : e (a - fun i => (((a i : ZMod M)).val : ℤ)) = 1 := by
    refine (hker _).2 ⟨fun i => a i / (M : ℤ), funext fun i => ?_⟩
    simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, ZMod.val_intCast]
    have := Int.emod_add_mul_ediv (a i) (M : ℤ)
    linarith
  rw [map_sub_of_add e hadd, mul_inv_eq_one] at h
  exact h.symm

theorem red_injective (M : ℕ) [NeZero M] (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c) : Function.Injective (red M e hpow) := by
  intro c c' hcc
  have h1 : e (fun i => ((c i).val : ℤ)) = e (fun i => ((c' i).val : ℤ)) := congrArg Subtype.val hcc
  have h2 : e ((fun i => ((c i).val : ℤ)) - fun i => ((c' i).val : ℤ)) = 1 := by
    rw [map_sub_of_add e hadd, h1, mul_inv_cancel]
  obtain ⟨d, hd⟩ := (hker _).1 h2
  funext i
  have h3 := congrArg (fun x : κ → ℤ => ((x i : ℤ) : ZMod M)) hd
  simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val,
    Int.cast_mul, ZMod.natCast_self, zero_mul] at h3
  exact sub_eq_zero.1 h3

theorem card_tors (M : ℕ) (hM : 0 < M) (e : (κ → ℤ) → Q) (hadd : ∀ a c, e (a + c) = e a * e c)
    (hpow : ∀ a, e a ^ M = 1) (hker : ∀ a, e a = 1 ↔ ∃ c, a = M • c)
    (hon : ∀ g : Q, g ^ M = 1 → ∃ a, e a = g) : Nat.card {g : Q // g ^ M = 1} = M ^ Fintype.card κ := by
  classical
  haveI : NeZero M := ⟨hM.ne'⟩
  have hb : Function.Bijective (red M e hpow) := by
    refine ⟨red_injective M e hadd hpow hker, fun ⟨g, hg⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hon g hg
    obtain ⟨c, hc⟩ := exists_red M e hadd hker a
    exact ⟨c, Subtype.ext hc⟩
  rw [← Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]

end GlobalTheory.TorsCount

namespace GlobalTheory.HTSympCover

theorem onto_tors_iff : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M → M.Coprime p → ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ S) (e : (Fin h ⊕ Fin h → ℤ) → (Over.mk y ⟶ o.A)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → (∀ a, e a = 1 ↔ ∃ c, a = M • c) → ((∀ g : Over.mk y ⟶ o.A, g ^ M = 1 → ∃ a, e a = g) ↔ (M = 1 ∨ 2 * h = Module.finrank ℤ D.La)) := by
  intro p _ D R _ b N h M hM hcop S t o k _ _ y e hadd hpow hker
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (y ≫ t)
  obtain ⟨I, -⟩ := o.geom k y β hβ
  haveI := D.freeLa
  haveI := D.finLa
  let B := Module.Free.chooseBasis ℤ D.La
  let ev' : (Module.Free.ChooseBasisIndex ℤ D.La → ℤ) → (Over.mk y ⟶ o.A) := fun a => I.ev M (B.equivFun.symm a)
  have hadd' : ∀ a c, ev' (a + c) = ev' a * ev' c := fun a c => by
    simp only [ev', map_add (f := _)]
    exact I.add M _ _
  have hpow' : ∀ a, ev' a ^ M = 1 := fun a => (I.onto M hM hcop _).2 ⟨_, rfl⟩
  have hker' : ∀ a, ev' a = 1 ↔ ∃ c, a = M • c := fun a => by
    simp only [ev']
    rw [I.ker M hM hcop]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨B.equivFun c, by rw [← map_nsmul, ← hc, LinearEquiv.apply_symm_apply]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨B.equivFun.symm c, map_nsmul _ _ _⟩
  have hon' : ∀ g, g ^ M = 1 → ∃ a, ev' a = g := fun g hg => by
    obtain ⟨x, hx⟩ := (I.onto M hM hcop g).1 hg
    exact ⟨B.equivFun x, by simp only [ev', LinearEquiv.symm_apply_apply, hx]⟩
  have hcard := GlobalTheory.TorsCount.card_tors M hM ev' hadd' hpow' hker' hon'
  rw [← Module.finrank_eq_card_chooseBasisIndex] at hcard
  have hinj := GlobalTheory.TorsCount.red_injective M e hadd hpow hker
  have hdom : Nat.card (Fin h ⊕ Fin h → ZMod M) = M ^ (2 * h) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin, two_mul]
  rcases Nat.lt_or_ge M 2 with hM2 | hM2
  · have h1 : M = 1 := by omega
    subst h1
    simp only [true_or, iff_true]
    intro g hg
    rw [pow_one] at hg
    exact ⟨0, by rw [hg]; exact GlobalTheory.TorsCount.map_zero_of_add e hadd⟩
  · have hMne : M ≠ 1 := by omega
    simp only [hMne, false_or]
    haveI : Finite {g : Over.mk y ⟶ o.A // g ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
    constructor
    · intro hon
      have hb : Function.Bijective (GlobalTheory.TorsCount.red M e hpow) := by
        refine ⟨hinj, fun ⟨g, hg⟩ => ?_⟩
        obtain ⟨a, rfl⟩ := hon g hg
        obtain ⟨c, hc⟩ := GlobalTheory.TorsCount.exists_red M e hadd hker a
        exact ⟨c, Subtype.ext hc⟩
      have h2 := Nat.card_eq_of_bijective _ hb
      rw [hcard, hdom] at h2
      exact Nat.pow_right_injective hM2 h2
    · intro hr g hg
      have hs : Function.Surjective (GlobalTheory.TorsCount.red M e hpow) :=
        (hinj.bijective_of_nat_card_le (by rw [hcard, hdom, hr])).2
      obtain ⟨c, hc⟩ := hs ⟨g, hg⟩
      exact ⟨_, congrArg Subtype.val hc⟩

end GlobalTheory.HTSympCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibrePointTransferFixedModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsionTransfer

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (g : T.left ⟶ S)
    (hg : T.hom ≫ f = g) (x : T ⟶ G') (x₀ : Over.mk g ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  subst hg
  have e : x₀ = pushHom h T x := Over.OverMorphism.ext hx
  rw [e, ← map_pow]
  rfl

theorem torsion_transfer : ∀ (V₁ : Type) [CommRing V₁] (X : Over (Sp V₁)) [GrpObj X] (K : Type) [Field K] (ev : V₁ →+* K)
  (Z : Over (Sp K)) [GrpObj Z] (ψ : ((Over.pullback (spMap ev)).obj X).left ⟶ Z.left),
  IsGrpPullback ((Over.pullback (spMap ev)).obj X) Z (𝟙 _) ψ →
  ∀ (K₀ : Type) [Field K₀] (e : K₀ →+* K) (Y : Over (Sp K₀)) [GrpObj Y] (φ : Z.left ⟶ Y.left),
  IsGrpPullback Z Y (spMap e) φ →
  ∀ (n : ℕ) (y : Over.mk (spMap ev) ⟶ X), y ^ n = 1 →
  ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj X).left, q ≫ pullback.fst X.hom (spMap ev) = y.left →
    q ≫ pullback.snd X.hom (spMap ev) = 𝟙 _ →
    ∃ y' : Over.mk (spMap e) ⟶ Y, y' ^ n = 1 ∧ y'.left = q ≫ ψ ≫ φ := by
  intro V₁ _ X _ K _ ev Z _ ψ hψ K₀ _ e Y _ φ hφ n y hy q hq hs
  let P := (Over.pullback (spMap ev)).obj X
  let T0 : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have hqP : q ≫ P.hom = T0.hom := hs
  let qq : T0 ⟶ P := Over.homMk q hqP
  have hP := isGrpPullback_pullback X (spMap ev)

  have h1 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm n
  have h0 := pow_left_of_isGrpPullback hP T0 (spMap ev) (Category.id_comp _) qq y hq.symm 0
  rw [hy] at h1
  rw [pow_zero, pow_zero] at h0
  have hqn : (qq ^ n).left = (1 : T0 ⟶ P).left := by
    apply pullback.hom_ext
    · exact h1.symm.trans h0
    · exact (Over.w (qq ^ n)).trans (Over.w (1 : T0 ⟶ P)).symm

  have hzw : (q ≫ ψ) ≫ Z.hom = T0.hom := by
    have w := hψ.1.w
    rw [Category.assoc, w, Category.comp_id]; exact hs
  let zz : T0 ⟶ Z := Over.homMk (q ≫ ψ) hzw
  have k1 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl n
  have k0 := pow_left_of_isGrpPullback hψ T0 (𝟙 _) (Category.comp_id _) qq zz rfl 0
  rw [pow_zero, pow_zero] at k0
  have hzn : (zz ^ n).left = (1 : T0 ⟶ Z).left := by
    rw [k1, hqn]; exact k0.symm

  have hyw : (q ≫ ψ ≫ φ) ≫ Y.hom = spMap e := by
    have w := hφ.1.w
    rw [Category.assoc, Category.assoc, w, ← Category.assoc ψ, ← Category.assoc q, ← Category.assoc q, hzw]
    exact Category.id_comp _
  refine ⟨Over.homMk (q ≫ ψ ≫ φ) hyw, ?_, rfl⟩
  have m1 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) n
  have m0 := pow_left_of_isGrpPullback hφ T0 (spMap e) (Category.id_comp _) zz (Over.homMk (q ≫ ψ ≫ φ) hyw)
    (by simp [zz]) 0
  rw [pow_zero, pow_zero] at m0
  apply Over.OverMorphism.ext
  rw [m1, hzn, m0]

end GlobalTheory.TorsionTransfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFixedOfQuotientClassesFixed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorsFixed

theorem fixed_of_classes_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hB D A G _ _ hG U V _ _ φ _ hc k hk σ hσ hQ x hx
  haveI : CharZero R := hB.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws

  have sq : (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V) ≫ spMap φ =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    show (spMap _ ≫ spMap _) ≫ spMap φ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp]
    congr 1
    ext r
    exact (hc r).symm
  have wx : x.left ≫ pullback.snd G.hom (spMap φ) = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := Over.w x
  have w₁ : (x.left ≫ pullback.fst G.hom (spMap φ)) ≫ G.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx, sq]
  let xG : Over.mk (jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R) ⟶ G :=
    Over.homMk (x.left ≫ pullback.fst G.hom (spMap φ)) w₁
  have hxG : xG ^ k = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull sq (isGrpPullback_pullback G (spMap φ)) (x := xG) (x' := x) rfl).1 hx

  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  let x₀ : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (gp.1.lift (x.left ≫ pullback.fst G.hom (spMap φ)) (jFK (R := R) (AlgebraicClosure (FractionRing V))) w₁)
      (gp.1.lift_snd _ _ _)
  have e₀ : x₀.left ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) = x.left ≫ pullback.fst G.hom (spMap φ) :=
    gp.1.lift_fst _ _ _
  have hx₀ : x₀ ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := x₀) e₀).2 hxG

  have hσR : ∀ r : R, σ (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r => by
    rw [hc r, hσ]
  let σ' : AlgebraicClosure (FractionRing V) →ₐ[FractionRing R] AlgebraicClosure (FractionRing V) :=
    ⟨σ.toRingHom, fun a => RingHom.congr_fun
      (IsLocalization.ringHom_ext (nonZeroDivisors R)
        (j := σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))))
        (k := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) (RingHom.ext hσR)) a⟩
  have hσf : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) := RingHom.ext σ'.commutes

  obtain ⟨f, hf, hsurj, hfi, -, -⟩ :=
    GlobalTheory.TorsionIso.torsion_eq hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V)) k hk
  obtain ⟨p, hp⟩ := hsurj x₀ hx₀
  obtain ⟨q, hpq⟩ := qkExtExists R D.toPre (AlgebraicClosure (FractionRing V))
    (AlgebraicClosure (FractionRing V)) σ.toRingHom σ'.commutes k p
  have heq : f q = x₀ := ((hfi p q).2 (hQ p q hpq)).symm.trans hp
  have s₂ : spMap σ.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing V)) =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) := by
    refine (spMap_comp _ _).symm.trans ?_
    exact congrArg spMap hσf
  have wx₀ : x₀.left ≫ A.A.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) := Over.w x₀
  let x' : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (spMap σ.toRingHom ≫ x₀.left) (by rw [Category.assoc, wx₀, s₂]; rfl)
  have hq : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V))
      (AlgebraicClosure (FractionRing V)) σ' k hk p q x₀ x' hpq rfl).1 ((hf p x₀).2 hp.symm)
  have fix : spMap σ.toRingHom ≫ x₀.left = x₀.left := congrArg (fun z => z.left) (((hf q x').1 hq).trans heq)

  have sV : spMap σ.toRingHom ≫ jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := by
    show spMap _ ≫ spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext v
    exact hσ v
  refine pullback.hom_ext (f := G.hom) (g := spMap φ) ?_ ?_
  · rw [Category.assoc, ← e₀, ← Category.assoc, fix]
  · rw [Category.assoc, wx, sV]

end GlobalTheory.Mum.TorsFixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff

theorem exists_mulEquiv_points_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hF : IsGrpPullback G' G f F) {X : Scheme.{0}} (t : X ⟶ S') (g : X ⟶ S)
    (hg : t ≫ f = g) :
    ∃ e : (Over.mk t ⟶ G') ≃* (Over.mk g ⟶ G), ∀ z, (e z).left = z.left ≫ F := by
  subst hg
  let m : (Over.mk t ⟶ G') → (Over.mk (t ≫ f) ⟶ G) := fun z => Over.homMk (z.left ≫ F) (by
    have h : z.left ≫ G'.hom = t := Over.w z
    show (z.left ≫ F) ≫ G.hom = t ≫ f
    rw [Category.assoc, hF.1.w, ← Category.assoc, h])
  have hm : ∀ z, (m z).left = z.left ≫ F := fun _ => rfl
  have hmul : ∀ x y, m (x * y) = m x * m y := fun x y =>
    Over.OverMorphism.ext ((hm _).trans (hF.2 (Over.mk t) x y (m x) (m y) (hm x) (hm y)).symm)
  have hinj : Function.Injective m := fun x y h => by
    refine Over.OverMorphism.ext (hF.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    rw [← hm, ← hm, h]
  have hsurj : Function.Surjective m := fun z =>
    ⟨Over.homMk (hF.1.lift z.left t (Over.w z)) (hF.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hm _).trans (hF.1.lift_fst _ _ _))⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' m hmul) ⟨hinj, hsurj⟩, hm⟩

end GlobalTheory.GroupBplus.Aff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointClassAtStalkSmulAction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsSpec

theorem exists_geomPt_range_eq_singleton (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  refine ⟨AlgebraicClosure (X.residueField g), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) _)) ≫ X.fromSpecResidueField g, ?_⟩
  ext y
  have h := fun t => X.fromSpecResidueField_apply g
    (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField g) (AlgebraicClosure (X.residueField g)))) t)
  simp only [Set.mem_range, Set.mem_singleton_iff, Scheme.Hom.comp_apply]
  exact ⟨fun ⟨t, e⟩ => e.symm.trans (h t),
    fun e => ⟨IsLocalRing.closedPoint _, (h _).trans e.symm⟩⟩

theorem exists_geomPt_stalk_over {X' : Scheme.{0}} [IsIntegral X'] {T : Scheme.{0}} (f : T ⟶ X') [Flat f]
    {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ] (p : T) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (y : Sp Ω ⟶ Spec (T.presheaf.stalk p)) (z : Sp Ω ⟶ V),
      y ≫ T.fromSpecStalk p ≫ f = z ≫ ℓ := by
  obtain ⟨p', hp', hfp'⟩ := Flat.generalizingMap f (genericPoint_specializes (f p))
  have hmem : p' ∈ Set.range (T.fromSpecStalk p) := by rw [Scheme.range_fromSpecStalk]; exact hp'
  obtain ⟨d, hd⟩ := hmem
  obtain ⟨Ω, hF, hA, y, hy⟩ := exists_geomPt_range_eq_singleton _ d
  have hgen : genericPoint X' ∈ Set.range ℓ := by
    refine ((genericPoint_spec X').mem_open_set_iff (IsOpenImmersion.isOpen_range ℓ)).mpr ?_
    exact ⟨ℓ (Classical.arbitrary V), trivial, _, rfl⟩
  have hr : Set.range (y ≫ T.fromSpecStalk p ≫ f) ⊆ Set.range ℓ := by
    rintro _ ⟨t, rfl⟩
    have ht : y t = d := by
      have : y t ∈ Set.range y := ⟨t, rfl⟩
      rw [hy] at this
      exact this
    simp only [Scheme.Hom.comp_apply, ht, hd, hfp']
    exact hgen
  exact ⟨Ω, hF, hA, y, IsOpenImmersion.lift ℓ _ hr, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory.TorsSpec

namespace GlobalTheory.TorsSpec

theorem valAt_comp {X' : Scheme.{0}} (G : Over X') [GrpObj G] (n : ℕ) {V : Scheme.{0}} (ℓ : V ⟶ X') {M : Type}
    (w : M → (V ⟶ G.left)) (τ : torsion G n ⟶ torsion G n) (p q : (torsion G n).left) (hq : τ.left p = q) (c : M)
    (h : ValAt G n ℓ w q c) (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (y : Sp Ω ⟶ Spec ((torsion G n).left.presheaf.stalk p)) (z : Sp Ω ⟶ V)
    (hyz : y ≫ (torsion G n).left.fromSpecStalk p ≫ (torsion G n).hom = z ≫ ℓ) :
    y ≫ (torsion G n).left.fromSpecStalk p ≫ τ.left ≫ (torsion.ι G n).left = z ≫ w c := by
  subst hq
  have key := Scheme.SpecMap_stalkMap_fromSpecStalk τ.left (x := p)
  have hw : τ.left ≫ (torsion G n).hom = (torsion G n).hom := Over.w τ
  have h1 := h Ω (y ≫ Spec.map (τ.left.stalkMap p)) z (by
    simpa only [Category.assoc, reassoc_of% key, hw] using hyz)
  simpa only [Category.assoc, reassoc_of% key] using h1

theorem class_act : ∀ {E : Type} [Field E] {X' : Scheme.{0}} [IsIntegral X'] [GlobalTheory.IsNormalScheme X'] (G : Over X') [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] (n : ℕ) (hn : IsUnit (n : Γ(X', ⊤))) {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X')
    [IsOpenImmersion ℓ] {M : Type} (w : M → (V ⟶ G.left)) (hw : ∀ c, w c ≫ G.hom = ℓ) [AddCommGroup M] [Module (𝓞 E) M] (hun : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (c c' : M), x ≫ w c = x ≫ w c' → c = c') (act : OAct (𝓞 E) G)
    (hlin : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ V) (a : M) (r : 𝓞 E) (A B : Over.mk (x ≫ ℓ) ⟶ G),
      A.left = x ≫ w a → B.left = x ≫ w (r • a) → B = A ≫ act.act r)
    (K : Type) [Field K] [IsAlgClosed K] (t : Sp K ⟶ X') (P : Over.mk t ⟶ G) (r : 𝓞 E)
    (PT RT : Sp K ⟶ (torsion G n).left) (hPT : PT ≫ (torsion.ι G n).left = P.left)
    (hRT : RT ≫ (torsion.ι G n).left = (P ≫ act.act r).left) (x : Sp K) (cP cR : M)
    (hcP : GlobalTheory.TorsSpec.ValAt G n ℓ w (PT x) cP) (hcR : GlobalTheory.TorsSpec.ValAt G n ℓ w (RT x) cR), cR = r • cP := by
  intro E _ X' _ _ G _ _ _ n hn V _ ℓ _ M w hw _ _ hun act hlin K _ _ t P r PT RT hPT hRT x cP cR hcP hcR
  haveI := GrpTangent.etale_torsion G hn
  haveI := mono_torsion_ι G n
  have hι : torsion.ι G n ≫ mulN G n = 1 := by
    rw [Hom.one_def]
    exact pullback.condition.trans (congrArg (· ≫ (MonObj.one : 𝟙_ (Over X') ⟶ G)) (CartesianMonoidalCategory.toUnit_unique _ _))
  have hτ : (torsion.ι G n ≫ act.act r) ≫ mulN G n = 1 := by
    haveI := act.hom r
    rw [← act_natCast act n, Category.assoc, ← act.mul, mul_comm, act.mul, ← Category.assoc,
      act_natCast act n, hι, Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  obtain ⟨τ, hτι⟩ := exists_lift_torsion n _ hτ
  have hτl : τ.left ≫ (torsion.ι G n).left = (torsion.ι G n).left ≫ (act.act r).left := by
    rw [← Over.comp_left, hτι, Over.comp_left]
  have hPR : PT ≫ τ.left = RT := by
    rw [← cancel_mono (torsion.ι G n).left, Category.assoc, hτl, reassoc_of% hPT, hRT, Over.comp_left]
  have hq : τ.left (PT x) = RT x := by rw [← hPR, Scheme.Hom.comp_apply]
  obtain ⟨Ω, hF, hA, y, z, hyz⟩ := exists_geomPt_stalk_over (torsion G n).hom ℓ (PT x)
  have h1 := hcP Ω y z hyz
  have h2 := valAt_comp G n ℓ w τ (PT x) (RT x) hq cR hcR Ω y z hyz
  rw [hτl, reassoc_of% h1] at h2
  let A : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w cP) (by rw [Category.assoc, hw]; rfl)
  let B : Over.mk (z ≫ ℓ) ⟶ G := Over.homMk (z ≫ w (r • cP)) (by rw [Category.assoc, hw]; rfl)
  have h3 := congrArg (fun q => q.left) (hlin Ω z cP r A B rfl rfl)
  simp only [A, B, Over.homMk_left, Over.comp_left] at h3
  exact (hun Ω z _ _ (h3.trans ((Category.assoc _ _ _).trans h2))).symm

end GlobalTheory.TorsSpec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilVacuumNotMemAugmentationInertPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_vacuum_not_mem_augmentation_inert_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    G.M'.vac v ∉ augAt om' v := by
  first | exact @GlobalTheory.InertVacLag.vac_not_mem_augAt | exact GlobalTheory.InertVacLag.vac_not_mem_augAt | (intros; apply GlobalTheory.InertVacLag.vac_not_mem_augAt <;> assumption)
end

