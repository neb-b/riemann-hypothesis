module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.MemOfIsIntegralElem
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EvalTwistTxEqZeroOfAevalArcTx
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelMapKernelEqIntegralTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqZeroOfSumV
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.TorsionUnit
open GlobalTheory.TorusExt

theorem eq_zero_of_sumV {F : Type} [Field F] {v : AddValuation F (WithTop ℚ)} {Ix : Type} {x : Ix → F} {s : F}
    (h : SumV v x s) {q : ℚ} (q0 : 0 < q) (i₀ : Ix) (h₀ : v (x i₀) = 0)
    (hq : ∀ i, i ≠ i₀ → (q : WithTop ℚ) ≤ v (x i)) : v s = 0 := by
  classical
  obtain ⟨S, hS⟩ := h q
  have a := v.map_le_add (hS (insert i₀ S) (Finset.subset_insert _ _))
    (v.map_le_sum (s := (insert i₀ S).erase i₀) (f := x) fun i hi => hq i (Finset.ne_of_mem_erase hi))
  have e : s = x i₀ + (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [← Finset.add_sum_erase _ x (Finset.mem_insert_self i₀ S)]; ring
  have lt : v (x i₀) < v (s - ∑ i ∈ insert i₀ S, x i + ∑ i ∈ (insert i₀ S).erase i₀, x i) := by
    rw [h₀]
    exact lt_of_lt_of_le (by exact_mod_cast q0) a
  rw [e, v.map_add_eq_of_lt_left lt, h₀]

attribute [local instance] gtGroup

theorem unit_value : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th₀ : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th₀ ϑ → Prim D Q v ϑ → ∀ (k : ℕ), 2 ≤ k → IsUnit (k : V) → ∃ pk : QkPt D.toPre F k, pk.y = 0 ∧ ∀ x, QkToAkU U.toUnifPre F k pk x → ∀ e : FrAt x, IsTorsFrame A ρ k x e → ∀ c : F, ValAt th₀ x e c → v c = 0 := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP k hk hu
  have hB := D.tau_bimult
  have k1 : 1 ≤ k := by omega
  obtain ⟨h, o, g₂, ho, hh, hg₂, hv₂⟩ := GlobalTheory.UT.ExactTerm.exact_term_after_torsion hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv
    ϑ hP k hk hu 0 0
  rw [isZero_iff_eq] at ho
  rw [isNsmul_iff_eq] at hh
  rw [isAdd_iff_eq, zero_add] at hg₂
  subst hg₂
  have z : k • g₂ = iota hB F 0 := by rw [map_zero, ← hh, ho]
  refine ⟨qkMk hB 0 g₂ z, rfl, fun x hx e he c hval => ?_⟩
  obtain ⟨w₁, hw₁, hv₁, hsum⟩ := GlobalTheory.T.section_value_at_torsionPoint_eq_sum_terms hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN k k1 _ x hx e he
  have hS : SumV v (coef ϑ g₂ w₁) c := hsum 1 le_rfl w₁ ⟨hw₁, fun z J _ => (pow_one _).symm⟩ th ϑ c hE hval
  obtain ⟨-, -, -, -, hqk, -, hterm⟩ := GlobalTheory.UT.CoefVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv g₂
  have hl := hqk k k1 (qkMk hB 0 g₂ z)
  have q0 : Q 0 = 0 := QForm.Q_zero hϖ D hQ
  have b0 : ∀ χ, QForm.bOf D.toPre Q 0 χ = 0 := fun χ => by
    rw [QForm.bOf, zero_add, q0]; ring
  have hv₁ : GenV hϖ hv w₁ 0 := by
    have e0 : ((Q (qkMk hB 0 g₂ z).y : ℚ) / (k : ℚ) ^ 2) = 0 := by rw [qkMk_y, q0]; simp
    rwa [e0] at hv₁
  have hl : GtV hϖ hv g₂ fun _ => 0 := by
    intro χ
    have a := hl χ
    have e0 : ((QForm.bOf D.toPre Q (qkMk hB 0 g₂ z).y χ : ℚ) / (k : ℚ)) = 0 := by rw [qkMk_y, b0]; simp
    simp only [e0] at a
    exact a
  refine eq_zero_of_sumV hS one_pos 0 ?_ fun χ hχ => ?_
  · rw [hv₂ w₁ _ _ hw₁ hl hv₁, q0]
    simp
  · refine le_trans (WithTop.coe_le_coe.2 ?_) ((hterm 1 le_rfl w₁ ϑ hw₁).2 _ 0 0 hl hv₁ hP.1 χ)
    have b : (1 : ℚ) ≤ (Q χ : ℚ) := by exact_mod_cast QForm.Q_pos hϖ D hQ hχ
    simpa using b

end GlobalTheory.ZH.TorsionUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.PrincIsog

theorem pow_eq_one_of_etale {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [GrpObj A] [GrpObj B]
    [IsSeparated A.hom] [LocallyOfFiniteType A.hom] (ψ : A ⟶ B) [Etale ψ.left] (n : ℕ)
    (h : ∀ y : Over.mk (𝟙 (Sp k)) ⟶ A, y ≫ ψ = 1 → y ^ n = 1) (T : Over (Sp k)) (x : T ⟶ A)
    (hx : x ≫ ψ = 1) : x ^ n = 1 := by
  let K := pullback ψ η[B]
  let inc : K ⟶ A := pullback.fst ψ η[B]
  have hinc : inc ≫ ψ = 1 := by
    rw [pullback.condition, toUnit_unique (pullback.snd ψ η[B]) (toUnit K)]; rfl
  have hp := (IsPullback.of_hasPullback ψ η[B]).map (Over.forget (Sp k))
  have he : Etale (pullback.snd ψ η[B]).left := MorphismProperty.of_isPullback (P := @Etale) hp ‹_›
  have hw : (pullback.snd ψ η[B]).left = K.hom := by
    simpa using Over.w (pullback.snd ψ η[B])
  rw [hw] at he
  have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
  have key : inc ^ n = 1 := by
    refine Over.OverMorphism.ext ?_
    have : LocallyOfFiniteType ((inc ^ n).left ≫ A.hom) := by rw [Over.w]; infer_instance
    refine ext_of_apply_eq A.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
      ((Over.w _).trans (Over.w _).symm)
    let p : Over.mk (𝟙 (Sp k)) ⟶ K := Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
    have e : p ≫ inc ^ n = p ≫ 1 := by
      rw [MonObj.comp_pow, MonObj.comp_one]
      exact h _ (by rw [Category.assoc, hinc, MonObj.comp_one])
    have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint k)) e
    have hz' : p.left (IsLocalRing.closedPoint k) = z := pointOfClosedPoint_apply K.hom z hz _
    simp only [Over.comp_left] at e'
    rw [← hz']
    exact e'
  have hx' : x ≫ ψ = toUnit T ≫ η[B] := hx
  rw [← pullback.lift_fst x (toUnit T) hx', ← MonObj.comp_pow]
  change _ ≫ inc ^ n = 1
  rw [key, MonObj.comp_one]

theorem exists_lift_point {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

theorem exists_isogeny_of_ncard (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (g N : ℕ) :
    ∀ (A : Over (Sp k)) [GrpObj A] (L : LB A.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      L.IsLB → Out.RelAmple A L → {x : 𝟙_ (Over (Sp k)) ⟶ A | GlobalTheory.MemKL A L x}.ncard = N →
      ∃ (B : Over (Sp k)) (_ : GrpObj B) (M : LB B.left) (i : A ⟶ B) (r : B ⟶ A) (m : ℕ),
        IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ M.IsLB ∧ Out.RelAmple B M ∧ Out.KTriv B M ∧
          IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro A _ L hA hg hL hamp hN
  obtain ⟨hfin, hmul, htriv⟩ := GlobalTheory.KTrivPoints.finite_mul_kTriv k A hA L hL hamp
  by_cases h1 : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, GlobalTheory.MemKL A L x → x = 1
  · exact ⟨A, inferInstance, L, 𝟙 A, 𝟙 A, 1, hA, hg, hL, hamp, htriv h1, inferInstance, inferInstance, le_rfl,
      by simp⟩
  push Not at h1
  obtain ⟨x, hxK, hx1⟩ := h1
  have hfin' : {x : 𝟙_ (Over (Sp k)) ⟶ A | GlobalTheory.MemKL A L x}.Finite := hfin
  have hord : IsOfFinOrder x := by
    refine finite_powers.1 (hfin'.subset ?_)
    rintro _ ⟨j, rfl⟩
    induction j with
    | zero => simpa using GlobalTheory.memKL_one hL _
    | succ j hj => simpa [pow_succ] using hmul _ _ hj hxK
  have hn : 1 ≤ orderOf x := hord.orderOf_pos
  obtain ⟨A', _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ :=
    GlobalTheory.exists_quotient_abelian_by_finite_points k A hA (Subgroup.zpowers x) (finite_zpowers.2 hord)
  obtain ⟨M, hM, hLM⟩ := GlobalTheory.CyclicDescent.exists_descent k A A' hA L hL x _ hn rfl hxK ψ hψ hψf hψe hψs hker
  have hamp' := GlobalTheory.SS.relAmple_of_finite_etale_isogeny k A A' hA hA' ψ hψ hψf hψe hψs L M hL hM hLM hamp
  have := hA.proper
  have := hA'.proper
  have := hA.comm
  have := hA'.comm
  have hg' : SmoothOfRelativeDimension g A'.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover k _ _ ψ.left A'.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hg)
  have hxψ : x ≫ ψ = 1 := (hker k (𝟙 _) x).2 ⟨x, Subgroup.mem_zpowers x, by
    rw [show toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 (𝟙_ (Over (Sp k))) from toUnit_unique _ _]
    exact (Category.id_comp x).symm⟩
  have hlt : {y : 𝟙_ (Over (Sp k)) ⟶ A' | GlobalTheory.MemKL A' M y}.ncard < N := by
    rw [← hN]
    refine lt_of_le_of_lt ?_ (Set.ncard_sdiff_singleton_lt_of_mem (a := x) hxK hfin')
    refine (Set.ncard_le_ncard ?_ ((hfin'.sdiff).image (· ≫ ψ))).trans (Set.ncard_image_le hfin'.sdiff)
    intro y hy
    obtain ⟨b, hb⟩ := exists_lift_point (F := k) ψ.left y.left
    let b' : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = y := Over.OverMorphism.ext hb
    by_cases hbx : b' = x
    · exact ⟨1, ⟨GlobalTheory.memKL_one hL _, fun h => hx1 (Eq.symm h)⟩, by
        rw [← hb', hbx, hxψ]; exact MonObj.one_comp ψ⟩
    · exact ⟨b', ⟨GlobalTheory.memKL_of_hom _ A A' ψ hψ L M hL hM hLM _ b' (hb' ▸ hy), hbx⟩, hb'⟩
  obtain ⟨B, _, M', i, r, m, hB, hgB, hM', hampB, hK, hi, hr, hm, hri⟩ := ih _ hlt A' M hA' hg' hM hamp' rfl
  have hmon : IsMonHom (𝟙 A ^ orderOf x) := GlobalTheory.GrpTangent.mulN_eq_pow A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN A _
  obtain ⟨⟨ψ', hψ', hc⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A' A ψ (𝟙 A ^ orderOf x) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine pow_eq_one_of_etale ψ _ (fun y hy => ?_) T z hz
      obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := (hker k (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one,
        one_zpow, MonObj.comp_one]
  have hc' : ψ' ≫ ψ = 𝟙 A' ^ orderOf x := by
    rw [← cancel_epi ψ, ← Category.assoc, hc, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp,
      Category.comp_id]
  refine ⟨B, inferInstance, M', ψ ≫ i, r ≫ ψ', m * orderOf x, hB, hgB, hM', hampB, hK, inferInstance,
    inferInstance, Nat.mul_pos hm hn, ?_⟩
  rw [Category.assoc, ← Category.assoc ψ', hc', MonObj.pow_comp, Category.id_comp, MonObj.comp_pow, hri, pow_mul]

theorem exists_isogeny_kTriv : ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (A : Over (Sp k)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (B : Over (Sp k)) (_ : GrpObj B) (M : LB B.left) (i : A ⟶ B) (r : B ⟶ A) (m : ℕ), IsAbelianScheme B ∧ SmoothOfRelativeDimension g B.hom ∧ M.IsLB ∧ Out.RelAmple B M ∧ Out.KTriv B M ∧ IsMonHom i ∧ IsMonHom r ∧ 1 ≤ m ∧ r ≫ i = 𝟙 _ ^ m := by
  intro k _ _ _ A _ g hA hg
  obtain ⟨L, m, s, hL, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple k A hA
  have := hA.proper
  exact exists_isogeny_of_ncard k g _ A L hA hg hL
    ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hL).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)) rfl

end GlobalTheory.SS.PrincIsog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsObjectWithThetaPointOfDegenerationSeries
section
namespace GlobalTheory.Ex.OneLevel
section Arith
open Polynomial

theorem dvd_pow_sub {z : ℂ} {d k : ℕ} (hd : d.Prime) (hz : z ^ d ^ k = z) (y : Algebra.adjoin ℤ {z}) :
    (d : Algebra.adjoin ℤ {z}) ∣ y ^ d ^ k - y := by
  obtain ⟨y, hy⟩ := y
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain rfl : x = z := hx
    exact ⟨0, Subtype.ext (by simp [hz])⟩
  | algebraMap r =>
    haveI := Fact.mk hd
    have h : (d : ℤ) ∣ r ^ d ^ k - r := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ZMod.pow_card_pow, sub_self]
    have := map_dvd (algebraMap ℤ (Algebra.adjoin ℤ {z})) h
    rwa [map_natCast, map_sub, map_pow] at this
  | add x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ + ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ + ⟨y, hy⟩)
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hd (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) ⟨y, hy⟩ k
    rw [hr]
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s + t + a * b * r, by linear_combination hs + ht⟩
  | mul x y hx hy ihx ihy =>
    change _ ∣ ((⟨x, hx⟩ * ⟨y, hy⟩ : Algebra.adjoin ℤ {z})) ^ _ - (⟨x, hx⟩ * ⟨y, hy⟩)
    generalize (⟨x, hx⟩ : Algebra.adjoin ℤ {z}) = a at *
    generalize (⟨y, hy⟩ : Algebra.adjoin ℤ {z}) = b at *
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s * b ^ d ^ k + a * t, by rw [mul_pow]; linear_combination b ^ d ^ k * hs + a * ht⟩

theorem dvd_of_dvd_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (y : Algebra.adjoin ℤ {z}) (h : (d : Algebra.adjoin ℤ {z}) ∣ y ^ 2) : (d : Algebra.adjoin ℤ {z}) ∣ y := by
  have hc : d.Coprime N := (Nat.Prime.coprime_iff_not_dvd hd).2 hdN
  have h1 : z ^ d ^ N.totient = z := by
    have := pow_eq_pow_of_modEq (Nat.ModEq.pow_totient hc) hz
    rwa [pow_one] at this
  have h2 : 2 ≤ d ^ N.totient := hd.two_le.trans (Nat.le_self_pow (Nat.totient_pos.2 hN).ne' d)
  have h3 := dvd_sub (h.trans (pow_dvd_pow y h2)) (dvd_pow_sub hd h1 y)
  rwa [sub_sub_cancel] at h3

theorem eq_zero_of_sq {z : ℂ} {d N : ℕ} (hd : d.Prime) (hN : 0 < N) (hdN : ¬ d ∣ N) (hz : z ^ N = 1)
    (B : Algebra.adjoin ℤ {z}) : ∀ A : Algebra.adjoin ℤ {z}, A ^ 2 = -d * B ^ 2 → B = 0 := by
  have hi : IsIntegral ℤ z := IsIntegral.of_pow hN (hz ▸ isIntegral_one)
  haveI : Module.Finite ℤ (Algebra.adjoin ℤ {z}) := Algebra.finite_adjoin_simple_of_isIntegral hi
  haveI : IsNoetherianRing (Algebra.adjoin ℤ {z}) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hd0 : (d : Algebra.adjoin ℤ {z}) ≠ 0 := Nat.cast_ne_zero.2 hd.ne_zero
  have hu : ¬ IsUnit (d : Algebra.adjoin ℤ {z}) := fun hu => by
    rw [← map_natCast (algebraMap ℤ (Algebra.adjoin ℤ {z}))] at hu
    exact (Nat.prime_iff_prime_int.1 hd).not_unit (IsUnit.of_map _ _ hu)
  induction B using (wellFounded_dvdNotUnit (α := Algebra.adjoin ℤ {z})).induction with
  | _ B ih =>
    intro A hA
    obtain ⟨A', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz A ⟨-B ^ 2, by rw [hA]; ring⟩
    have h1 : B ^ 2 = d * -A' ^ 2 := mul_left_cancel₀ hd0 (by linear_combination hA)
    obtain ⟨B', rfl⟩ := dvd_of_dvd_sq hd hN hdN hz B ⟨_, h1⟩
    by_contra h0
    have hB' : B' ≠ 0 := right_ne_zero_of_mul h0
    exact hB' (ih B' ⟨hB', d, hu, mul_comm _ _⟩ A' (mul_left_cancel₀ hd0 (by linear_combination h1)))

theorem exists_linear (d : ℕ) (c : MvPolynomial (Fin 2) ℤ) : ∃ a b : ℤ[X], ∀ (K : Type) [CommRing K] (ζ ρ : K),
    ρ ^ 2 = -(d : K) → cf ζ ρ c = aeval ζ a + ρ * aeval ζ b := by
  induction c using MvPolynomial.induction_on with
  | C r => exact ⟨C r, 0, fun K _ ζ ρ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, h⟩ := hp
    obtain ⟨a', b', h'⟩ := hq
    exact ⟨a + a', b + b', fun K _ ζ ρ e => by rw [map_add (f := _), h K ζ ρ e, h' K ζ ρ e, map_add (f := _), map_add (f := _)]; ring⟩
  | mul_X p i hp =>
    obtain ⟨a, b, h⟩ := hp
    fin_cases i
    · exact ⟨a * X, b * X, fun K _ ζ ρ e => by rw [map_mul, h K ζ ρ e]; simp; ring⟩
    · exact ⟨-d * b, a, fun K _ ζ ρ e => by
        rw [map_mul, h K ζ ρ e]; simp; linear_combination aeval ζ b * e⟩

theorem compat_of_not_dvd {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {N : ℕ} (hN : 0 < N) (hdN : ¬ H.d ∣ N) {K : Type} [Field K] {ζ ρ : K}
    (hζ : IsPrimitiveRoot ζ N) (hρ : ρ ^ 2 = -(H.d : K)) : Compat H N ζ ρ := by
  intro c hc
  obtain ⟨a, b, h⟩ := exists_linear H.d c
  have hz : IsPrimitiveRoot (ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N) N := Complex.isPrimitiveRoot_exp N hN.ne'
  generalize ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta N = z at hc hz
  rw [h ℂ _ _ H.sqrt_neg_disc_sq] at hc
  have hb : aeval z b = 0 := congrArg Subtype.val (eq_zero_of_sq H.d_prime hN hdN hz.pow_eq_one
    ⟨aeval z b, aeval_mem_adjoin_singleton _ _⟩ ⟨aeval z a, aeval_mem_adjoin_singleton _ _⟩ (Subtype.ext (by
      have := H.sqrt_neg_disc_sq
      push_cast
      linear_combination (aeval z a - H.rt0 * aeval z b) * hc + aeval z b ^ 2 * this)))
  have ha : aeval z a = 0 := by rwa [hb, mul_zero, add_zero] at hc
  have key : ∀ p : ℤ[X], aeval z p = 0 → aeval ζ p = 0 := fun p hp => by
    have h1 := minpoly.isIntegrallyClosed_dvd (hz.isIntegral hN) hp
    rw [← cyclotomic_eq_minpoly hz hN] at h1
    refine aeval_eq_zero_of_dvd_aeval_eq_zero h1 ?_
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hN
  rw [h K _ _ hρ, key a ha, key b hb, mul_zero, add_zero]
end Arith

def scaleForm {O : Type} [CommRing O] {N : NumD O} {k : ℕ} (β : N.Form k) (j : ℕ) (hj : 0 < j) : N.Form j where
  be := (j : ℤ) • β.be
  symm y z := congrArg ((j : ℤ) * ·) (β.symm y z)
  pos y hy := mul_pos (Int.natCast_pos.2 hj) (β.pos y hy)
  dvd y z := by
    change _ ∣ (j : ℤ) * β.be y z
    rw [mul_comm 2]
    exact mul_dvd_mul_left _ ((Dvd.intro _ rfl).trans (β.dvd y z))

theorem tx_congr {O : Type} [CommRing O] [TopologicalSpace O] (N : NumD O) (ψ ψ' : N.X → Oˣ) (e b e' b') (h : ψ = ψ')
    (m : ℕ) (p : ({ N with ψ := ψ, even := e, bimult := b } : NumD O).QT (m ^ 2))
    (p' : ({ N with ψ := ψ', even := e', bimult := b' } : NumD O).QT (m ^ 2))
    (h1 : p.1.1 = p'.1.1) (h2 : p.1.2.b = p'.1.2.b) (h3 : p.1.2.s = p'.1.2.s) :
    NumD.tx _ m p = NumD.tx _ m p' := by
  subst h
  rw [show p = p' from Subtype.ext (Prod.ext h1 (NumD.Gt.ext h2 h3))]

theorem tx_scale {O : Type} [CommRing O] [TopologicalSpace O] {N : NumD O} {k : ℕ} (β : N.Form k) (m : ℕ)
    (hm : 0 < m ^ 2) (u r : Oˣ) (hr : r ^ m ^ 2 = u) (q : N.QT (m ^ 2)) (p : (N.twist β u).QT (m ^ 2))
    (h : TwRel β u r q p) :
    (N.twist β u).tx m p =
      (N.twist (scaleForm β _ hm) r).tx m (N.twQ (scaleForm β _ hm) r dvd_rfl q) := by
  refine tx_congr N _ _ _ _ _ _ (funext fun χ => ?_) m _ _ h.1 h.2.1 (funext fun χ => (h.2.2 χ).trans ?_)
  · change _ = _ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be χ χ / 2)
    rw [Int.mul_ediv_assoc _ ((Dvd.intro _ rfl).trans (β.dvd χ χ)), zpow_mul, zpow_natCast, hr]
  · change _ = q.1.2.s χ * r ^ (((m ^ 2 : ℕ) : ℤ) * β.be q.1.1.toAdd χ / ((m ^ 2 : ℕ) : ℤ))
    rw [Int.mul_ediv_cancel_left _ (Int.natCast_pos.2 hm).ne']

theorem eval_mul_of_isHomogeneous {ι C : Type} [CommRing C] {G : MvPolynomial ι C} {d : ℕ} (hG : G.IsHomogeneous d)
    (s : C) (v : ι → C) : MvPolynomial.eval (fun i => s * v i) G = s ^ d * MvPolynomial.eval v G := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have h := hG (MvPolynomial.mem_support_iff.1 he)
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← h, Finsupp.weight_apply]
  simp only [Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
  ring
end GlobalTheory.Ex.OneLevel

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.OneLevel

theorem exists_full_theta : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing O') K] [Algebra (PowerSeries O') K] [FaithfulSMul (PowerSeries O') K] [Algebra.IsAlgebraic (PowerSeries O') K], (∀ x, algebraMap (FractionRing O') K (algebraMap O' _ x) = algebraMap (PowerSeries O') K (PowerSeries.C x)) → ∀ (S : Ser a K (algebraMap _ K)) (n j : ℕ), n.Prime → Odd n → IsUnit (n : O') → ¬ n ∣ H.d → 2 ≤ j → ∃ o : Full D K, o.ρ = S.A.ρ ∧ o.I.ζ ((n ^ j) ^ 2) = S.A.I.ζ ((n ^ j) ^ 2) ∧ o.Theta (n ^ j) (S.v (n ^ j)) := by
  intro h1 h2 h3 h4 h5 h6 h7 E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hb K _ _ _ _ _ _ _ S n j hn ho hu hd hj
  haveI : CharZero K := S.A.arc.charZero
  have hm : Odd (n ^ j) := ho.pow
  have hm2 : 0 < (n ^ j) ^ 2 := pow_pos hm.pos 2
  have hdN : ¬ H.d ∣ (n ^ j) ^ 2 := fun h => hd (by
    rw [(Nat.prime_dvd_prime_iff_eq H.d_prime hn).1 (H.d_prime.dvd_of_dvd_pow (H.d_prime.dvd_of_dvd_pow h))])
  obtain ⟨o, e1, e2, e3⟩ := _root_.GlobalTheory.Ex.ClosurePoint.exists_full_of_closure_of_cosets h1 h2 h3 h4 h5 h6 h7 E H D l Xo c W₀ Y K n j S.A.ρ
    (S.A.I.ζ ((n ^ j) ^ 2)) (S.v (n ^ j)) hn ho hj
    (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (S.A.I.ζ_prim _ hm2)) S.A.ρ_sq)
    (fun G hG => by_contra fun hne => S.base.not_allC_false fun C _ _ _ _ _ gam u c1 c2 c3 c4 => hne (by
      obtain ⟨A', r', i1, ⟨_, o1, o2, -⟩, i3, i4⟩ := S.val C gam u c1 c2 c3 c4
      haveI : CharZero C := A'.arc.charZero
      have hr : r' ((n ^ j) ^ 2) ^ (n ^ j) ^ 2 = u := Units.ext (by
        rw [Units.val_pow_eq_pow_val, i3, ← map_pow, ← Units.val_pow_eq_pow_val, S.roots.pow hm2, S.r_one, c3]; rfl)
      have hr1 : ‖(r' ((n ^ j) ^ 2) : C)‖ < 1 := by
        rw [← hr, Units.val_pow_eq_pow_val, norm_pow] at c4
        exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hm2.ne').1 c4
      choose p hp using fun x => (existsUnique_twRel A'.be u _ hr (A'.q _ x)).exists
      obtain ⟨⟨s, hs⟩, -⟩ := i4 _ hm p hp
      have hbal : A'.arc.Bal (scaleForm A'.be _ hm2) := fun x y z => by
        refine congrArg ((((n ^ j) ^ 2 : ℕ) : ℤ) * ·) ((A'.be_eq _ _).trans (Eq.trans ?_ (A'.be_eq _ _).symm))
        refine (congrArg (a.be · _) (A'.ν.eX.apply_symm_apply _)).trans ((a.be_adj _ _ _).trans ?_)
        exact congrArg (a.be _ ·) (A'.ν.eX.apply_symm_apply _).symm
      have k1 := _root_.GlobalTheory.ArcIdentity.aeval_arcTx_eq_zero_of_vanishC h1 h2 h3 h4 h5 h6 h7 E H D O' C A'.arc _ (scaleForm A'.be _ hm2) hbal _ dvd_rfl hm
        (compat_of_not_dvd H hm2 hdN (IsPrimitiveRoot.coe_units_iff.2 (A'.I.ζ_prim _ hm2)) A'.ρ_sq) G hG
      have hC : CExt O' ⊥ C := ⟨fun x => by rw [c1]; exact c2 _, fun x hx => by
        rw [(Submodule.mem_bot _).1 hx, map_zero, map_zero, norm_zero]; exact one_pos⟩
      have k2 := GlobalTheory.eval_twist_tx_eq_zero_of_aeval_arcTx C A'.N _ (scaleForm A'.be _ hm2) _ dvd_rfl hm D.La (A'.q _)
        (fun x => (GlobalTheory.Ex.UnitNorm.norms_of_arc_input E H D l Xo c W₀ Y O' b ϖ a hb C hC A' i1).2.1 _ hm _) _ k1 _ hr1
      obtain ⟨d, hGd⟩ := hG.2.1
      apply gam.injective
      have ec : gam.comp (cf (S.A.I.ζ ((n ^ j) ^ 2) : K) S.A.ρ) = cf (A'.I.ζ ((n ^ j) ^ 2) : C) A'.ρ := by
        refine MvPolynomial.ringHom_ext (fun x => by simp) fun i => ?_
        fin_cases i
        · simpa [Lift.arc] using o2 _ hm2
        · simpa [Lift.arc] using o1
      rw [map_zero, MvPolynomial.eval₂_comp_left, ec, MvPolynomial.eval₂_eq_eval_map]
      have ev : gam ∘ S.v (n ^ j) = fun x => (s : C) * (A'.N.twist (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2))).tx (n ^ j)
          (A'.N.twQ (scaleForm A'.be _ hm2) (r' ((n ^ j) ^ 2)) dvd_rfl (A'.q _ x)) := funext fun x =>
        (hs x).trans (congrArg _ (tx_scale A'.be _ hm2 u _ hr _ _ (hp x)))
      rw [ev, eval_mul_of_isHomogeneous (hGd.map _)]
      exact mul_eq_zero_of_right _ k2))
    (fun x => by
      have hX : algebraMap (PowerSeries O') K PowerSeries.X ≠ 0 := by rw [← S.r_one]; exact Units.ne_zero _
      obtain ⟨h, hh⟩ := (S.int n j hn ho hu (by omega) ⊤ fun _ => trivial).2.2
        ((ValuationSubring.valuation_eq_one_iff (⊤ : ValuationSubring K) ⟨_, trivial⟩).1
          (IsUnit.of_mul_eq_one ⟨_⁻¹, trivial⟩ (Subtype.ext (mul_inv_cancel₀ hX)))) x
      exact ⟨h, fun e => by rw [e, map_zero] at hh; exact zero_ne_one hh⟩)
  exact ⟨o, e1, Units.ext e2, e3⟩
end GlobalTheory.Ex.OneLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusTorsionPointStandardAlternatingFormStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_torsionPoint_standardAlternatingForm : LL → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → (∀ a b, x (a + b) = x a * x b) → (∀ z : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, z ^ (S.r * S.N) = 1 → ∃ a, z = x a) → ∀ t ∈ S.perp l.yy.ker, ∃ (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ), pk.y = 0 ∧ IsTor τ pk.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk (x t) ∧ ∀ (a : S.Gam) (α : u.D.toPre.X), l.yy a = QuotientAddGroup.mk α → (τ (Multiplicative.ofAdd α)).val = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ t a).val))) := by
  first | exact @GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | exact GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd | (intros; apply GlobalTheory.ZH.PerpCharacter.exists_torus_point_eStd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HvHolds
section
namespace GlobalTheory.Ex

theorem hv_holds : GlobalTheory.Ex.HV :=
  GlobalTheory.TestFibre.laws_all GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1

end GlobalTheory.Ex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LabelMapKernelEqIntegralTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.label_map_kernel_eq_integral_torsion : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ a, a ∈ yy.ker ↔ u.Integral a := by
  first | exact @GlobalTheory.ZH.LabelKernel.main | exact GlobalTheory.ZH.LabelKernel.main | (intros; apply GlobalTheory.ZH.LabelKernel.main <;> assumption)
end

