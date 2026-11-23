module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1983
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1154
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2298
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLevelLoweringQuotientRepresentsReduced
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.QuotFamRep

theorem spMap_rid (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _

section Calc

variable {h n n' n'' : ℕ} {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] {ζ : B} {ζ' : B'} {ζ'' : B''}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {s'' : S'' ⟶ Sp B''}
  {c : SiegPre h n ζ s} {c' : SiegPre h n' ζ' s'} {c'' : SiegPre h n'' ζ'' s''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
  {d d' d'' : ℕ}

theorem sRel_comp (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c' d'' d' f') : SRel c'' c d'' d (f' ≫ f) :=
  ((_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).1 h₂

theorem sRel_cancel (h₁ : SRel c' c d' d f) (h₂ : SRel c'' c d'' d (f' ≫ f)) : SRel c'' c' d'' d' f' :=
  ((_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n'' B B' B'' ζ ζ' ζ'' S S' S'' s s' s'' c c' c'' f f' d d' d'' h₁).1).2 h₂

theorem sRel_principal (h₁ : SRel c' c d' d f) (hc : c.Principal) : c'.Principal :=
  (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') d d' d' h₁).2.1 hc

theorem sRel_scale (h₁ : SRel c' c 1 1 f) (e : ℕ) : SRel c' c e e f := by
  simpa using (_root_.GlobalTheory.SiegLevCalc.sRel_calculus h n n' n' B B' B' ζ ζ' ζ' S S' S' s s' s' c c' c' f (𝟙 S') 1 1 1 h₁).2.2 e

end Calc

theorem exists_pull {h k : ℕ} {B : Type} [CommRing B] {ζ : B} {S S' : Scheme.{0}} {s : S ⟶ Sp B}
    (c : SiegPre h k ζ s) (f : S' ⟶ S) : ∃ c' : SiegPre h k ζ (f ≫ s), SiegPB c' c f :=
  (_root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h k B B ζ ζ (RingHom.id B) S S' s (f ≫ s) f rfl (by rw [spMap_rid, Category.comp_id])).1 c

theorem asIdeal_eq_bot_iff {A A' : Type} [CommRing A] [CommRing A'] [IsDomain A] [IsDomain A'] (j : A →+* A')
    (hj : Function.Injective j) (hf : IsFinite (spMap j)) (y : Sp A') :
    ((spMap j) y).asIdeal = ⊥ ↔ y.asIdeal = ⊥ := by
  algebraize [j]
  have hm : Module.Finite A A' := by rw [IsFinite.SpecMap_iff] at hf; exact hf
  have : Algebra.IsIntegral A A' := inferInstance
  show Ideal.comap (algebraMap A A') y.asIdeal = ⊥ ↔ _
  refine ⟨fun e => Ideal.eq_bot_of_comap_eq_bot e, fun e => ?_⟩
  rw [e]; exact Ideal.comap_bot_of_injective (algebraMap A A') hj

end GlobalTheory.QuotFamRep

namespace GlobalTheory


open QuotFamRep in
theorem quotFam_represents : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N) (Q : SQuot F n (zetaAway n) j), 3 ≤ n → Odd N → n ∣ N → Function.Injective j → j (zetaAway n) = zetaAway N ^ (N / n) → IsFinite (spMap j) → Etale (spMap j) → Surjective (spMap j) → ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Q.X, f ≫ Q.s = s' ∧ SiegPB c Q.univ f := by
  intro h n N F j Q hn hN hnN hj hjz hfin het hsurj S s' c hS hd hc
  have hN0 : N ≠ 0 := hN.pos.ne'
  have hn0 : n ≠ 0 := by omega

  let S' := pullback s' (spMap j)
  let q : S' ⟶ S := pullback.fst s' (spMap j)
  let t : S' ⟶ Sp (cycAway N) := pullback.snd s' (spMap j)
  have hq := _root_.GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n (cycAway n) (cycAway n) (zetaAway n) (zetaAway n) (RingHom.id _) S S' s' (t ≫ spMap j) q
    rfl (by rw [spMap_rid, Category.comp_id]; exact pullback.condition)
  obtain ⟨c', hc'⟩ := hq.1 c
  have hc'P : c'.Principal := hq.2.1 c c' hc' hc

  obtain ⟨S₁, π₁, C, hπf, hπe, hπs, hCrel, -⟩ := _root_.GlobalTheory.SiegCover.exists_levelCover h n N (cycAway n) (cycAway N) (zetaAway n)
    (cycBase hN0) j S' t c' hn hN hnN (by rw [cycBase_ζ]; exact hjz) hc'P
  let p : S₁ ⟶ S := π₁ ≫ q
  have : IsFinite p := by dsimp [p, q]; infer_instance
  have : Etale p := by dsimp [p, q]; infer_instance
  have : Surjective p := by dsimp [p, q]; infer_instance
  have hp : p ≫ s' = (π₁ ≫ t) ≫ spMap j := by
    simp only [p, q, t, Category.assoc, pullback.condition]
  have hred : IsReduced S₁ := GlobalTheory.isReduced_of_smooth_of_isReduced p
  have hden : Dense {x : S₁ | ((π₁ ≫ t) x).asIdeal = ⊥} := by
    have : UniversallyOpen p := UniversallyOpen.of_flat p
    have e : ∀ x, s' (p x) = spMap j ((π₁ ≫ t) x) := fun x => by
      rw [← Scheme.Hom.comp_apply, hp, Scheme.Hom.comp_apply]
    convert hd.preimage p.isOpenMap using 1
    ext x
    show ((π₁ ≫ t) x).asIdeal = ⊥ ↔ (s' (p x)).asIdeal = ⊥
    rw [e, asIdeal_eq_bot_iff j hj hfin]
  have hCP : C.Principal := sRel_principal hCrel hc'P
  obtain ⟨f₁, hf₁s, hf₁⟩ := F.rep S₁ (π₁ ≫ t) C hred hden hCP

  obtain ⟨c₀, hC0, h0C⟩ := _root_.GlobalTheory.SiegLower.exists_lower h n N (cycAway n) (cycAway N) (zetaAway n) (zetaAway N) j S₁ (π₁ ≫ t) C hN0
    (isUnit_natCast hN0) hnN hjz
  have hf₁N : SRel C F.univ (N / n) (N / n) f₁ := sRel_scale ((sRel_one_one_iff _ _ _).2 hf₁) _
  have h0F : SRel c₀ F.univ 1 (N / n) f₁ := by simpa using sRel_comp hf₁N h0C
  obtain ⟨g, hg⟩ : ∃ g : S₁ ⟶ Q.X, g = f₁ ≫ Q.π := ⟨_, rfl⟩
  have hgQ : SRel C Q.univ (N / n) 1 g := hg ▸ sRel_comp Q.low hf₁N
  have h0Q : SiegPB c₀ Q.univ g := (sRel_one_one_iff _ _ _).1 (by simpa using sRel_comp hgQ h0C)
  have hCc : SRel C c (N / n) 1 p := sRel_comp ((sRel_one_one_iff _ _ _).2 hc') hCrel
  have h0c₁ : SRel c₀ c 1 1 p := by simpa using sRel_comp hCc h0C
  have hf₁p : f₁ ≫ F.s ≫ spMap j = p ≫ s' := by rw [← Category.assoc, hf₁s, hp]
  have hgs : g ≫ Q.s = p ≫ s' := by rw [hg, Category.assoc, Q.base]; exact hf₁p

  have key : pullback.fst p p ≫ g = pullback.snd p p ≫ g := by
    have : IsReduced (pullback p p) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst p p)
    have : IsSeparated Q.s := isSeparated_of_isQProjOver Q.qproj
    refine (GlobalTheory.hom_eq_iff_forall_isAlgClosed Q.s ?_).2 fun K _ _ x => ?_
    · simp only [Category.assoc, hgs, pullback.condition_assoc]
    obtain ⟨cx, hcx⟩ := exists_pull c₀ (x ≫ pullback.fst p p)
    have hx₁ := (sRel_one_one_iff _ _ _).2 hcx
    have hx₂ : SRel cx c₀ 1 1 (x ≫ pullback.snd p p) := by
      refine sRel_cancel h0c₁ ?_
      have := sRel_comp h0c₁ hx₁
      convert this using 1
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e := Q.fibre K (x ≫ pullback.fst p p ≫ f₁) (x ≫ pullback.snd p p ≫ f₁) _ cx
      (by simp only [Category.assoc, hf₁p, pullback.condition_assoc])
      (by simpa only [Category.assoc] using sRel_comp h0F hx₁)
      (by simpa only [Category.assoc] using sRel_comp h0F hx₂)
    simpa only [hg, Category.assoc] using e
  have hcoeq : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ S₁), g₁ ≫ p = g₂ ≫ p → g₁ ≫ g = g₂ ≫ g := fun g₁ g₂ e => by
    have := pullback.lift g₁ g₂ e ≫= key
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  have hfac : p ≫ EffectiveEpi.desc p g hcoeq = g := EffectiveEpi.fac p g hcoeq
  refine ⟨EffectiveEpi.desc p g hcoeq, ?_, ?_⟩
  · rw [← cancel_epi p, ← Category.assoc, hfac, hgs]
  · exact _root_.GlobalTheory.siegPB_of_finite_etale_cover h n (cycAway n) (cycBase hn0) S S₁ Q.X s' ((π₁ ≫ t) ≫ spMap j) Q.s c c₀ Q.univ p _ hn
      (hN.of_dvd_nat hnN) Q.princ inferInstance inferInstance inferInstance ((sRel_one_one_iff _ _ _).1 h0c₁)
      (hfac.symm ▸ h0Q)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelModuliTraitPeriodsMonomialPosDef
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.Poinc.TraitTau

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem exists_tauCoord {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (a b : Q.X) :
    ∃ k, Q.TauCoord a b k := by
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε), u.IsGen :=
    DVR.exists_gen_of_local (V := R) Q.M.L Q.M.isLB _ _
  have hφ : lamPts (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b) =
      fun k => (toUnit (TK R)).left ≫ lamPts (Q.c a) (Q.c b) k := by
    funext k
    fin_cases k
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_mul (toUnit (TK R)) (Q.c a) (Q.c b))).symm
    · rfl
    · rfl
    · exact (congrArg (fun q : TK R ⟶ Q.B => q.left) (MonObj.comp_one (toUnit (TK R)))).symm
  obtain ⟨ρ, hρ⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_ratio Q.M.isLB hφ (Q.tau a b)
    (LB.pullGen Q.M.L _ negε u (toUnit (TK R)).left) (Q.tau_gen a b) (DVR.pullGen_isGen _ _ _ _ hu _)
  let k : (FractionRing R)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom.toMonoidHom ρ
  have hk : unitOn k = ρ := Units.ext ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom_inv_id_apply ρ.val)
  refine ⟨k, u, hu, fun z J hJ => ?_⟩
  rw [hρ _ _ z J hJ, val_pull hJ, Category.id_comp, hk]

theorem isMonomialTau_ofDeg {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult) {m : ℕ}
    {t : Fin m → R} {β : Fin m → LinearMap.BilinForm ℤ D.X} (h : IsMonomial D t β) (hs : ∀ i y z, β i y z = β i z y)
    (ht : ∀ i, t i ≠ 0) : (Wit.ofDeg D hB).IsMonomialTau t β := by
  intro (a : D.X) (b : D.X)
  obtain ⟨k, hk⟩ := exists_tauCoord (Wit.ofDeg D hB) a b
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R D a b
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.RefTauCoord.main R R (Wit.ofDeg D hB) (RingHom.id R) D (AddEquiv.refl _) Function.injective_id
    (Wit.refines_ofDeg D hB) a b k hk x hx
  have hl : ∀ σ : FractionRing R →+* FractionRing R,
      (∀ r, σ (algebraMap R (FractionRing R) r) = algebraMap R (FractionRing R) (RingHom.id R r)) → ∀ y, σ y = y :=
    fun σ hσ => RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors R) (k := RingHom.id _) (RingHom.ext hσ))
  rw [hl _ (fun r => by rw [IsFractionRing.lift_algebraMap]; rfl)] at hu₁
  obtain ⟨_, _, -, ha⟩ := h a
  obtain ⟨_, _, -, hb⟩ := h b
  obtain ⟨_, _, -, hab⟩ := h (a + b)
  obtain ⟨u₃, hu₃⟩ := h.tau hs ht ha hb hab
  obtain ⟨xa, ha₁, ha₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D a _).1 ha
  obtain ⟨xb, hb₁, hb₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D b _).1 hb
  obtain ⟨xab, hab₁, hab₂⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D (a + b) _).1 hab
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.TauCoordQuot.main R D a b x xab xa xb hx hab₁ ha₁ hb₁
  rw [← ha₂, ← hb₂, ← hab₂] at hu₃
  have hc := Taut.tauCoord_mul_unit hk (u₁ * u₂⁻¹ * u₃⁻¹)
  refine ⟨k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) (u₁ * u₂⁻¹ * u₃⁻¹), ?_, hc⟩
  refine Eq.trans (b := ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) ?_ rfl
  clear hc hk hl
  have hu : ∀ u : Rˣ, algebraMap R (FractionRing R) (u : R) ≠ 0 := fun u =>
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 u.ne_zero
  have e : algebraMap R (FractionRing R) u₁ * (k : FractionRing R) = algebraMap R (FractionRing R) u₂ *
      (algebraMap R (FractionRing R) u₃ * ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b) := by
    rw [← hu₃, ← hu₁, hu₂, div_eq_mul_inv, mul_inv]
    ring
  have h₂ := hu u₂
  have h₃ := hu u₃
  generalize ∏ i, algebraMap R (FractionRing R) (t i) ^ β i a b = P at e ⊢
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_mul, map_mul, map_units_inv]
  field_simp
  linear_combination e

theorem finrank_le {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} (T : Trait F) (hn : 2 ≤ n) (hζ : IsUnit ζ) :
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  let K := AlgebraicClosure (FractionRing T.V)
  haveI : CharZero (FractionRing T.V) :=
    (RingHom.charZero_iff (IsFractionRing.injective T.V (FractionRing T.V))).1 inferInstance
  have hK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let κ : Sp K ⟶ Sp (FractionRing T.V) := spMap (algebraMap _ K)
  have hp := IsPullback.of_hasPullback F.univ.A.hom (κ ≫ T.y)
  have hq : IsPullback (T.cart.1.lift (pullback.fst F.univ.A.hom (κ ≫ T.y)) (pullback.snd F.univ.A.hom (κ ≫ T.y) ≫ κ)
      (by rw [Category.assoc]; exact hp.w)) (pullback.snd F.univ.A.hom (κ ≫ T.y)) T.A.A.hom κ :=
    IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hp) (T.cart.1.lift_snd _ _ _) T.cart.1
  have hd : SmoothOfRelativeDimension T.A.g (pullback.snd F.univ.A.hom (κ ≫ T.y)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange T.A.g).of_isPullback hq T.A.smoothDim
  have e : T.A.g = g := GlobalTheory.SiegDim.dim_geometric_fibre F.univ hn hζ hK (κ ≫ T.y) hd
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (T : Trait F), (GlobalTheory.PolDeg.Wit.ofDeg T.D.toPre T.D.tau_bimult).IsMonomialTau ![T.ϖ] ![T.β] ∧ (∀ a, 0 ≤ T.β a a) ∧ (∀ a, a ≠ 0 → 0 < T.β a a) ∧ (2 ≤ n → IsUnit ζ → Module.finrank ℤ T.D.toPre.X ≤ g) := by
  intro g n o _ ζ F T
  refine ⟨isMonomialTau_ofDeg _ _ T.mono (fun i => ?_) (fun i => ?_), T.mono.nonneg 0, fun a ha => ?_, finrank_le T⟩
  · fin_cases i
    exact T.symm
  · fin_cases i
    exact T.irr.ne_zero
  · obtain ⟨i, hi⟩ := T.mono.exists_pos (maximalIdeal.isMaximal _).ne_top ha
    fin_cases i
    exact hi

end GlobalTheory.Poinc.TraitTau
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountLogTwistContinuityAbove
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem log_add_log_le_of_mul_le_mul (a b c d e : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a * b ≤ c * d) (hce : c ≤ e) :
    Real.log a + Real.log b ≤ Real.log e + Real.log d := by
  have hab : 1 ≤ a * b := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hcd : 1 ≤ c * d := hab.trans h
  have hc : c ≠ 0 := by rintro rfl; simp at hcd
  have hd : d ≠ 0 := by rintro rfl; simp at hcd
  have he : e ≠ 0 := by omega
  have h1 : Real.log ((a : ℝ) * b) ≤ Real.log ((e : ℝ) * d) := by
    apply Real.log_le_log
    · have : (1 : ℝ) ≤ (a : ℝ) * b := by exact_mod_cast hab
      linarith
    · have : a * b ≤ e * d := h.trans (Nat.mul_le_mul_right d hce)
      exact_mod_cast this
  rwa [Real.log_mul (by exact_mod_cast (by omega : a ≠ 0)) (by exact_mod_cast (by omega : b ≠ 0)),
    Real.log_mul (by exact_mod_cast he) (by exact_mod_cast hd)] at h1

theorem lc_add_div_sub_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, GenAt P c →
    Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop,
    P.lc M ((M / n : ℕ) - c) 1 ≤ P.lc M (-c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  intro k _ X _ p D hD P b s t hG c hgen hreg ε hε
  have hfin : ∀ (a c : ℤ) (R : ℝ), (P.Bl a c R).Finite := _root_.GlobalTheory.HSNef.bl_finite k X p D hD P
  have hball : ∀ a c : ℤ, IsBallFam (P.H a c) (P.Bl a c) := _root_.GlobalTheory.VolBr.Pair.isBallFam k X p P
  have hpos : ∀ (a c : ℤ) (R : ℝ), 0 ≤ R → 1 ≤ (P.Bl a c R).ncard := fun a c R hR =>
    Nat.one_le_iff_ne_zero.mpr ((Set.ncard_pos (hfin a c R)).mpr ⟨0, (hball a c).zero_mem R hR⟩).ne'
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.HSNef.crude_upper_lc_twist k X p D hD P b s t hG c hreg
  obtain ⟨δ, hδ, hrad⟩ := _root_.GlobalTheory.VolBr.log_ncard_ball_exp_le X.functionField (fun N => P.H (N : ℤ) (-c)) (fun N => P.Bl (N : ℤ) (-c))
    (D + 1) (Nat.succ_pos D) (fun N => hball N _) (fun N R => hfin N _ R) C0 hC0 (ε / 2) (by positivity)
  obtain ⟨C, hC, hdiv⟩ := _root_.GlobalTheory.HSNef.MpDivTwist.mem_Bl_of_mul_pow_twist k X p D hD P c hgen s hG.s_mem.1 hG.s_ne (δ / 3) (by positivity)
  have hdA := _root_.GlobalTheory.HSNef.lc_nearby_le k X p D hD P b c hG.pos hreg (ε / 2) (by positivity)
  have hn : ∀ᶠ n : ℕ in atTop, 3 * C / δ ≤ (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hdA, hn] with n hdAn hnC
  filter_upwards [hdAn, hrad, hn] with M hdm hradm hMC
  have hnδ : 3 * C ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp hnC
  have hMδ : 3 * C ≤ (M : ℝ) * δ := (div_le_iff₀ hδ).mp hMC
  have hmn : ((M / n : ℕ) : ℝ) * n ≤ M := by exact_mod_cast Nat.div_mul_le_self M n
  generalize M / n = m at *
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m

  have hrad_le : Real.exp (δ / 3 * (M : ℝ) + C * m + C) ≤ Real.exp (δ * (M : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hnδ hm0, mul_le_mul_of_nonneg_right hmn hδ.le]
  have hSsub : {f | f ∈ P.H M (-c) ∧ f * s ^ m ∈ P.Bl M (m - c) 2} ⊆ P.Bl M (-c) (Real.exp (δ * (M : ℝ))) := by
    rintro f ⟨hf1, hf2⟩
    have hf := hdiv M m f hf1 hf2
    exact ⟨hf.1, fun σ y => (hf.2 σ y).trans hrad_le⟩
  have hEfin := hfin M (-c) (Real.exp (δ * (M : ℝ)))
  have hSfin := hEfin.subset hSsub
  have hlev := _root_.GlobalTheory.HSNef.encard_mul_le_at_level_twist k X p D hD P b s t hG c M m
  rw [← (hfin _ _ _).cast_ncard_eq, ← (hfin _ _ _).cast_ncard_eq, ← hSfin.cast_ncard_eq,
    ← (hfin _ _ _).cast_ncard_eq] at hlev
  have hnat : ∀ x y z w : ℕ, (x : ℕ∞) * y ≤ z * w → x * y ≤ z * w := fun x y z w h => by exact_mod_cast h
  have hkey := log_add_log_le_of_mul_le_mul _ _ _ _ _ (hpos _ _ _ zero_le_one) (hpos _ _ _ zero_le_one)
    (hnat _ _ _ _ hlev)
    (Set.ncard_le_ncard hSsub hEfin)
  simp only [Pair.lc] at hdm ⊢
  linarith

end GlobalTheory.HSNef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulEighthPowerDiag
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory

theorem smul_eighth_power_diag : ∀ (X₀ X : Type) [AddCommGroup X₀] [AddCommGroup X] (K : (Fin 8 → X₀) ≃+ (Fin 8 → X)), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) → ∃ k : X₀ ≃+ X, ∀ mu, K mu = fun u => k (mu u) := by
  intro X₀ X _ _ K hK
  have hsel : ∀ (Y : Type) [AddCommGroup Y] (w : Fin 8) (nu : Fin 8 → Y),
      (fun u : Fin 8 => ∑ v, (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) u v • nu v)
        = fun _ => nu w := by
    intro Y _ w nu
    funext u
    simp [Matrix.of_apply]
  have hc : ∀ (mu : Fin 8 → X₀) (w : Fin 8), K (fun _ => mu w) = fun _ => K mu w := by
    intro mu w
    have h := hK (Matrix.of fun (_ : Fin 8) (v : Fin 8) => if v = w then (1:ℤ) else 0) mu
    rw [hsel, hsel] at h
    exact h
  let f : X₀ →+ X :=
    { toFun := fun x => K (fun _ => x) 0
      map_zero' := by
        show K 0 0 = 0
        simp
      map_add' := by
        intro x y
        show K ((fun _ => x) + (fun _ => y)) 0 = _
        rw [map_add (f := _)]
        rfl }
  have hform : ∀ (mu : Fin 8 → X₀) (u : Fin 8), K mu u = f (mu u) := by
    intro mu u
    show K mu u = K (fun _ => mu u) 0
    rw [hc]
  have inj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    have h1 : K (fun _ => x) = 0 := by
      funext u
      rw [hform]
      exact hx
    have h2 : (fun _ : Fin 8 => x) = 0 := K.injective (h1.trans (map_zero K).symm)
    exact congrFun h2 0
  have surj : Function.Surjective f := by
    intro y
    refine ⟨K.symm (fun _ => y) 0, ?_⟩
    have h := hform (K.symm fun _ => y) 0
    rw [← h]
    simp
  refine ⟨AddEquiv.ofBijective f ⟨inj, surj⟩, fun mu => funext fun u => ?_⟩
  exact hform mu u

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyResidueFieldFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh.CohBaseChange

theorem main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s :=
  of_parts (@GlobalTheory.AbCoh.exists_finite_projective_model) (@GlobalTheory.AbCoh.projective_coker_of_liftsAt) (@GlobalTheory.AbCoh.cohom_split_baseChange)

end GlobalTheory.AbCoh.CohBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureH1RankDescendsField
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem finrank_HO1_descend_field : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : Over (Sp K)) [GrpObj A] (B : Over (Sp L)) [GrpObj B] (φ : B.left ⟶ A.left), IsGrpPullback B A (spMap (algebraMap K L)) φ → IsAbelianScheme A → ∀ g : ℕ, Module.Finite L (HO1 B.hom) → Module.finrank L (HO1 B.hom) = g → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g := by
  intro K L _ _ _ A _ B _ φ hpb hA g hfin hrank
  haveI := hA.proper
  obtain ⟨⟨e, -⟩, -⟩ := flat_baseChange_HO K L A.left B.left A.hom B.hom φ hpb.1 inferInstance inferInstance
  haveI : Module.Finite L (L ⊗[K] HO1 A.hom) := Module.Finite.equiv e.symm
  have hr : Module.rank L (L ⊗[K] HO1 A.hom) = Cardinal.lift (Module.rank K (HO1 A.hom)) :=
    Module.rank_baseChange
  have hfinA : Module.Finite K (HO1 A.hom) := by
    rw [← Module.rank_lt_aleph0_iff]
    have h1 : Module.rank L (L ⊗[K] HO1 A.hom) < Cardinal.aleph0 := Module.rank_lt_aleph0 L _
    rw [hr] at h1
    simpa using h1
  refine ⟨hfinA, ?_⟩
  rw [← hrank, ← e.finrank_eq, Module.finrank_baseChange]

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointExtendsOverNormalDomainStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionPoint_extends_over_normal_domain : Laws → ∀ (R : Type) [CommRing R] [IsDomain R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (P : PolAV (Spec (CommRingCat.of R))) (N : ℕ), 1 ≤ N → ∀ x : TF (R := R) (FractionRing R) ⟶ P.A, x ^ N = 1 → ∃ b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ P.A, b ^ N = 1 ∧ x = toUnit _ ≫ b := by
  first | exact @GlobalTheory.Poinc.Tors.torsion_extend | exact GlobalTheory.Poinc.Tors.torsion_extend | (intros; apply GlobalTheory.Poinc.Tors.torsion_extend <;> assumption)
end

