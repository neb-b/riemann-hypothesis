module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdealOfLocally
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NearCOfPolFamOfKTriv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem nearC_of_polFam_of_kTriv : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Ideal.span (Set.range v) = ⊤ → PolFam b Mat κ β v A L act Q → Out.KTriv A L → NearC b Mat κ β v q₀ := by
  intro h1 h2 g n j J hn hodd hj o _ b Mat κ R _ _ _ β v A _ L act Q q₀ hD hv hP hK
  obtain ⟨hD1, hD2⟩ := hD
  obtain ⟨hAb, hdim, hLB, hrig, hsym, hamp, hlab, hgood⟩ := hP
  obtain ⟨hl1, hl2, hl3⟩ := hlab
  let P : Out.PolAV (Sp R) :=
    { A := A, isAb := hAb, g := g, smoothDim := hdim, L := L, isLB := hLB, rigid := hrig, sym := hsym,
      ample := hamp, ktriv := hK }
  have hpos : 0 < n ^ j := pow_pos hn.pos j

  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, ⟨hpb₁, hL₁, hact₁, hpt₁⟩, huniv⟩ :=
    GlobalTheory.exists_finiteEtale_level_cover h1 h2 o g (n ^ j) J b R β P act Q hpos ⟨rfl, hl1, hl2, hl3⟩
  have hG₁ : GLies A act Q (spMap (algebraMap R R₁)) t₁ ψ₁ := And.intro hpb₁ (And.intro hact₁ hpt₁)
  have h3 : 3 ≤ n ^ j := by
    have := Nat.odd_iff.1 hodd
    have := hn.two_le
    have : n ≤ n ^ j := Nat.le_self_pow (by omega) n
    omega

  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff h1 h2 o g (n ^ j) J b R₁
    (spMap (algebraMap R R₁) ≫ spMap β) t₁ (fun a => algebraMap R R₁ (v a)) hodd.pow h3
    (GlobalTheory.ThetaClosed.span_map_eq_top (algebraMap R R₁) hv)

  have kill : ∀ (K : Type) [Field K] (x : R →+* K) (t : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      (y₁ : R₁ →+* K), y₁.comp (algebraMap R R₁) = x → TMap t t₁ (spMap y₁) →
      t.HasTh (𝟙 _) (fun a => x (v a)) → ∀ r ∈ 𝔞, y₁ r = 0 := by
    intro K _ x t y₁ hc hT hth
    apply (h𝔞 K y₁).1
    have h := (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp K) _ t (spMap y₁) K (𝟙 _) (fun a => x (v a)) hT).1 hth
    rw [Category.id_comp] at h
    have hw : (fun a => x (v a)) = fun a => y₁ (algebraMap R R₁ (v a)) := by
      funext a; rw [← hc]; rfl
    rw [hw] at h
    exact h

  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = y'.comp (algebraMap R R₁) →
      (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) → y = y' := by
    intro K _ _ y y' hyy hy hy'
    have th := (h𝔞 K y).2 hy
    have th' := (h𝔞 K y').2 hy'
    have hw : (fun a => y' (algebraMap R R₁ (v a))) = fun a => y (algebraMap R R₁ (v a)) := by
      funext a; exact (RingHom.congr_fun hyy (v a)).symm
    have hc : spMap y ≫ spMap (algebraMap R R₁) = spMap y' ≫ spMap (algebraMap R R₁) := by
      rw [← spMap_comp, ← spMap_comp, hyy]
    have heq := level_eq_of_gLies_of_hasTh h1 h2 g n j J hn hodd hj o b (Sp R) (Sp R₁) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ K (spMap y) (spMap y')
      (fun a => y (algebraMap R R₁ (v a))) hLB hG₁ hL₁ hc
      (by rw [← Category.assoc, ← Category.assoc, hc]) th (by rw [← hw]; exact th')
    obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y)
      (spMap (y.comp (algebraMap R R₁)) ≫ spMap β) hLB hG₁ hL₁
      (by rw [spMap_comp, Category.assoc])
    have hc' : spMap y' ≫ spMap (algebraMap R R₁) = spMap (y.comp (algebraMap R R₁)) := by
      rw [← hc, spMap_comp]
    have hGu' : GLies A act Q (spMap (y.comp (algebraMap R R₁))) u ψ := by
      have ⟨g1, g2, g3⟩ := hGu
      rw [← spMap_comp y (algebraMap R R₁)] at g1 g3
      exact And.intro g1 (And.intro g2 g3)
    have hTu' : TMap u t₁ (spMap y') := tmap_of_glies o g (n ^ j) J b (Sp R) (Sp R₁) (Sp K) A L act Q
      (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β) t₁ ψ₁ (spMap y') _ u ψ hLB hG₁ hL₁
      (by rw [hc']; exact hGu') hLu (fun i => (hptu i).trans (heq i))
    have ⟨hg1, hg2, hg3⟩ := hGu'
    obtain ⟨y₀, -, huq⟩ := huniv K (y.comp (algebraMap R R₁)) u ψ ⟨hg1, hLu, hg2, hg3⟩
    exact (huq y ⟨rfl, hptu, hTu⟩).trans (huq y' ⟨hyy.symm, fun i => (hptu i).trans (heq i), hTu'⟩).symm
  have hqa : algebraMap R (R₁ ⧸ 𝔞) = (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) :=
    IsScalarTower.algebraMap_eq R R₁ (R₁ ⧸ 𝔞)
  have : Module.Finite R (R₁ ⧸ 𝔞) := Module.Finite.trans R₁ (R₁ ⧸ 𝔞)
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) := inferInstance

  have hup : ∀ q ∈ objPrimes b Mat κ β v, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : R₁ ⧸ 𝔞 →+* K, y.comp (algebraMap R (R₁ ⧸ 𝔞)) = x := by
    intro q hq
    obtain ⟨K, _, _, x, t, hker, hsh, hth⟩ := hq
    obtain ⟨ψ, hG, hLψ⟩ := hgood K x _ t (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K x t ψ ⟨hg1, hLψ, hg2, hg3⟩
    have hk := kill K x t y₁ hy₁c hy₁T hth
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y₁ hk, ?_, ?_⟩
    · beta_reduce
      rw [hqa, ← RingHom.comp_assoc, Ideal.Quotient.lift_comp_mk, hy₁c]
    · intro y hy
      apply Ideal.Quotient.ringHom_ext
      rw [Ideal.Quotient.lift_comp_mk]
      apply key K (y.comp (Ideal.Quotient.mk 𝔞)) y₁
      · rw [RingHom.comp_assoc, ← hqa, hy, hy₁c]
      · intro r hr
        rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
      · exact hk

  obtain ⟨f, hfq, r, hr, -⟩ := exists_retraction_near_of_unique_point R (R₁ ⧸ 𝔞)
    (objPrimes b Mat κ β v) hD1 hup q₀ hD2
  obtain ⟨z, hzdef⟩ : ∃ z : R₁ →+* Localization.Away f, z = r.comp (Ideal.Quotient.mk 𝔞) := ⟨_, rfl⟩
  have hz : z.comp (algebraMap R R₁) = loc f := by
    rw [hzdef, RingHom.comp_assoc, ← hqa, hr]
  have hzk : ∀ x ∈ 𝔞, z x = 0 := by
    intro x hx
    rw [hzdef, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

  obtain ⟨u, ψ, hTu, hGu, hLu, hptu⟩ := gLies_pull o g (n ^ j) J b (Sp R) (Sp R₁)
    (Sp (Localization.Away f)) A L act Q (spMap (algebraMap R R₁)) (spMap (algebraMap R R₁) ≫ spMap β)
    t₁ ψ₁ (spMap z) (spMap ((loc f).comp β)) hLB hG₁ hL₁
    (by rw [← hz, spMap_comp (z.comp (algebraMap R R₁)) β, spMap_comp z (algebraMap R R₁), Category.assoc])
  refine Exists.intro f (And.intro hfq (Exists.intro u (And.intro ?_ ?_)))
  · have h := (h𝔞 _ z).2 hzk
    apply (GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b (Sp R₁) (spMap (algebraMap R R₁) ≫ spMap β) t₁
      (Sp (Localization.Away f)) _ u (spMap z) (Localization.Away f) (𝟙 _) (fun a => loc f (v a)) hTu).2
    rw [Category.id_comp]
    have hw : (fun a => loc f (v a)) = fun a => z (algebraMap R R₁ (v a)) := by
      funext a; rw [← hz]; rfl
    rw [hw]; exact h
  · intro K _ _ x s t' hg
    obtain ⟨rfl, hsh, hth⟩ := (good_comp (loc f) x t').1 hg
    obtain ⟨ψ', hG', hLψ'⟩ := hgood K (x.comp (loc f)) _ t' (And.intro rfl (And.intro hsh hth))
    have ⟨hg1, hg2, hg3⟩ := hG'
    obtain ⟨y₁, ⟨hy₁c, -, hy₁T⟩, -⟩ := huniv K (x.comp (loc f)) t' ψ' ⟨hg1, hLψ', hg2, hg3⟩
    have hk := kill K (x.comp (loc f)) t' y₁ hy₁c hy₁T hth
    have hyz : y₁ = x.comp z := key K y₁ (x.comp z) (by rw [hy₁c, RingHom.comp_assoc, hz]) hk
      (by intro r' hr'; rw [RingHom.comp_apply, hzk r' hr', map_zero])
    rw [hyz, spMap_comp x z] at hy₁T
    exact TMap.cancel hTu hy₁T

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelUp

theorem eq_constPt_of_formallyUnramified {k : Type} [Field k] {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    (x : Sp (DualNumber k) ⟶ X) (h : x ≫ f = Geo.Tor.constPt (x ≫ f)) : x = Geo.Tor.constPt x := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k := CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hn : IsNilpotent (RingHom.ker π.hom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha c hc
    have ha' : a.fst = 0 := ha
    have hc' : c.fst = 0 := hc
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hc']
  have := IsClosedImmersion.spec_of_surjective π hπ
  refine FormallyUnramified.hom_ext (Spec.map π) (isNilpotent_ker_specMap π hn) f ?_
    (h.trans (by simp only [Geo.Tor.constPt, Category.assoc]))
  have e : Spec.map π ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  rw [Geo.Tor.constPt, ← Category.assoc, e, Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l l₂ : Level H}

theorem finiteDimensional_KA (l : Level H) : FiniteDimensional ℚ (KA l) := by
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  rcases hx with rfl | rfl
  · refine IsIntegral.of_pow two_pos ?_
    rw [H.sqrt_neg_disc_sq]
    exact (isIntegral_algebraMap (x := (H.d : ℚ))).neg
  · refine IsIntegral.of_pow l.A_pos ?_
    rw [show zeta l.A ^ l.A = 1 from (Complex.isPrimitiveRoot_exp l.A l.A_pos.ne').pow_eq_one]
    exact isIntegral_one

theorem formallyUnramified_spMap (j : KA l →+* KA l₂) : FormallyUnramified (spMap j) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := finiteDimensional_KA l₂
  have : Algebra.FormallyUnramified ℚ (KA l₂) := Algebra.FormallyUnramified.of_isSeparable ℚ (KA l₂)
  let _ : Algebra (KA l) (KA l₂) := j.toAlgebra
  exact Algebra.FormallyUnramified.of_restrictScalars ℚ (KA l) (KA l₂)

theorem exists_obj_of_eq {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s s' : S ⟶ Sp B} (e : s = s')
    (o : Obj D l b s) : ∃ o' : Obj D l b s', Nonempty (ObjMap o' o (𝟙 S)) := by
  subst e
  exact ⟨o, ⟨ObjComp.objMapId o⟩⟩

theorem nonempty_objMap_of_eq {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B} {b' : Base l B'}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} {s' : S' ⟶ Sp B'} {o : Obj D l b s} {o' : Obj D l b' s'} {f g : S' ⟶ S}
    (e : f = g) (m : ObjMap o' o f) : Nonempty (ObjMap o' o g) := by
  subst e
  exact ⟨m⟩

theorem exists_objMap_lower {B : Type} [CommRing B] {b : Base l B} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj D l b s} {o₂ : Obj D l₂ b₂ s₂} {o' : Obj D l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    ∃ n : ObjMap (ObjLower.lower o' h hρ hζ) o (g ≫ π), n.toSABMap.φ = u.toSABMap.φ ≫ m.φ := by
  obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩, hn⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₁ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.eta_add, ← ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine ObjComp.sec_comp (h₂ a) ?_
    rw [← ObjLower.map_nsmul_of_add _ o'.etaA_add, ← ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

end GlobalTheory.LevelUp

namespace GlobalTheory

open LevelUp

theorem nonempty_moduli_of_dvd : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H), 1 ≤ D.p + D.q → l.Dvd l₂ → Nonempty (Moduli D l) → Nonempty (Moduli D l₂) := by
  intro hL _ E _ _ _ H D l l₂ hpq hd ⟨Xo⟩
  have hA : l.A ∣ l₂.A := hd.2.2
  let j := levelFieldIncl hA
  let b := baseOfFinerLevel hA
  have hρ : b.ρ = (baseKA l₂).ρ := baseOfFinerLevel_rho hA
  have hζ : b.ζ = (baseKA l₂).ζ ^ (l₂.A / l.A) := baseOfFinerLevel_zeta hA
  have jρ : j (baseKA l).ρ = b.ρ := levelFieldIncl_rho hA
  have jζ : j (baseKA l).ζ = b.ζ := levelFieldIncl_zeta hA
  obtain ⟨o₁, ⟨m₀⟩⟩ := obj_pull E H D l _ _ (baseKA l) b j _ _ Xo.s (pullback.snd Xo.s (spMap j))
    (pullback.fst Xo.s (spMap j)) jρ jζ pullback.condition Xo.univ
  obtain ⟨S₂, π, o₂, m, hfin, het, -, ⟨h₁, h₂⟩, huniv⟩ :=
    _root_.GlobalTheory.LevCover.levelCover_closed hL E H D l l₂ _ b (baseKA l₂) _ _ o₁ hpq hd hρ hζ
  have hsm : SmoothOfRelativeDimension D.dim (pullback.snd Xo.s (spMap j)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth
  refine ⟨{ X := S₂, s := π ≫ pullback.snd Xo.s (spMap j), qproj := ?_, smooth := ?_, univ := o₂,
            rep := ?_, unram := ?_ }⟩
  · exact isQProjOver_comp_of_isFinite_noetherian _ _ _ _ _ hfin
      ((isQProjOver_baseChange_and_finite_restrict _ _ j _ Xo.s).1 Xo.qproj)
  · have : SmoothOfRelativeDimension (0 + D.dim) (π ≫ pullback.snd Xo.s (spMap j)) := inferInstance
    rwa [zero_add] at this
  · intro S t hS o
    obtain ⟨f₀, ⟨hf₀, ⟨n⟩⟩, hu₀⟩ := moduli_rep_of_base ObjMaps.id_comp_cancel E H D l Xo _ b j S t
      (ObjLower.lower o hd hρ hζ) hS jρ jζ
    obtain ⟨f, hf₁, hf₂⟩ : ∃ f : S ⟶ pullback Xo.s (spMap j), f ≫ pullback.fst _ _ = f₀ ∧ f ≫ pullback.snd _ _ = t :=
      ⟨pullback.lift f₀ t hf₀, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    subst hf₁ hf₂
    obtain ⟨m', -⟩ := ObjComp.objMap_cancel m₀ n
    obtain ⟨h, ⟨hh, u, -⟩, hu⟩ := huniv S f o m'.toSABMap ⟨m'.eta, m'.etaA⟩
    refine ⟨h, ⟨by rw [← Category.assoc, hh], ⟨u⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨v⟩⟩
    obtain ⟨w, hw⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ v
    obtain ⟨w', -⟩ := ObjComp.objMap_comp m₀ w
    have e : g ≫ π = f := by
      refine pullback.hom_ext (hu₀ _ ⟨?_, ⟨w'⟩⟩) (by rw [Category.assoc, hg])
      rw [Category.assoc, pullback.condition, ← hg]
      simp only [Category.assoc]
    subst e
    refine hu g ⟨rfl, v, hw.symm.trans ?_⟩
    exact obj_rigid_closed hL E H D l _ _ b b _ _ _ _ o₁ (ObjLower.lower o hd hρ hζ) (g ≫ π) (Or.inl hS)
      w.toSABMap m'.toSABMap fun a => ⟨_, w.eta a, m'.eta a⟩
  · rintro k _ x o ⟨u⟩ ⟨u'⟩
    have hj := formallyUnramified_spMap j
    have hp : FormallyUnramified (pullback.fst Xo.s (spMap j)) :=
      (HasRingHomProperty.isStableUnderBaseChange (P := @FormallyUnramified.{0})
        RingHom.FormallyUnramified.isStableUnderBaseChange).of_isPullback (IsPullback.of_hasPullback _ _).flip hj
    have hr : FormallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hp
    refine eq_constPt_of_formallyUnramified (π ≫ pullback.fst Xo.s (spMap j)) x ?_
    obtain ⟨w, -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u
    obtain ⟨w', -⟩ := exists_objMap_lower hd hρ hζ m h₁ h₂ u'
    have e : (x ≫ π ≫ pullback.snd Xo.s (spMap j)) ≫ spMap j = (x ≫ π ≫ pullback.fst Xo.s (spMap j)) ≫ Xo.s := by
      simp only [Category.assoc, pullback.condition]
    obtain ⟨o', ⟨i⟩⟩ := exists_obj_of_eq e (objRestrictBase j (ObjLower.lower o hd hρ hζ) jρ jζ)
    let i' : ObjMap o' (ObjLower.lower o hd hρ hζ) (𝟙 _) := ⟨i.toSABMap, i.eta, i.etaA⟩
    obtain ⟨n, -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w).choose i'
    obtain ⟨n', -⟩ := ObjComp.objMap_comp (ObjComp.objMap_comp m₀ w').choose i'
    exact Xo.unram k _ o' (nonempty_objMap_of_eq (by simp only [Category.assoc, Category.id_comp]) n)
      (nonempty_objMap_of_eq (by simp only [Geo.Tor.constPt, Category.assoc, Category.id_comp]) n')

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

variable {S X T₁ T₂ X₁ X₂ : Scheme.{0}} {f : X ⟶ S} {M : LB X} {π₁ : X₁ ⟶ X} {f₁ : X₁ ⟶ T₁} {t₁ : T₁ ⟶ S}
  {π₂ : X₂ ⟶ X} {f₂ : X₂ ⟶ T₂} {t₂ : T₂ ⟶ S}

theorem exists_isPullback (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂) (u : T₂ ⟶ T₁)
    (hu : u ≫ t₁ = t₂) : ∃ φ : X₂ ⟶ X₁, π₂ = φ ≫ π₁ ∧ IsPullback φ f₂ f₁ u := by
  have w : π₂ ≫ f = (f₂ ≫ u) ≫ t₁ := by rw [Category.assoc, hu, h₂.w]
  refine ⟨h₁.lift _ _ w, (h₁.lift_fst _ _ _).symm, IsPullback.of_right ?_ (h₁.lift_snd _ _ _) h₁⟩
  rw [h₁.lift_fst, hu]
  exact h₂

theorem lbIso_pull_comp {φ : X₂ ⟶ X₁} (hφ : π₂ = φ ≫ π₁) {L₁ : LB X₁} (e : LBIso L₁ (M.pull π₁)) :
    LBIso (M.pull π₂) (L₁.pull φ) :=
  LBIso.chartPull (chartPullSame M (fun _ : PUnit => π₂) (fun _ => π₁) (fun _ => 1) φ fun _ => hφ)
    (Geo.Tor.chartPullPull L₁ φ φ rfl) e.symm

theorem lbIso_pull_pull (hM : M.IsLB) (φ : X₂ ⟶ X₁) (π₁ : X₁ ⟶ X) :
    LBIso ((M.pull π₁).pull φ) (M.pull (φ ≫ π₁)) :=
  (lbIso_pull_comp rfl (GlobalTheory.lbIso_refl (LB.isLB_pull hM π₁))).symm

theorem relAmple_of_factor [IsProper f] (hM : M.IsLB) (h₁ : IsPullback π₁ f₁ f t₁) (h₂ : IsPullback π₂ f₂ f t₂)
    (u : T₂ ⟶ T₁) (hu : u ≫ t₁ = t₂) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₁) L₁) : Out.RelAmple (Over.mk f₂) (M.pull π₂) := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ u hu
  have hp : IsProper (Over.mk f₂).hom := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  refine AmpleLocal.relAmple_of_locally T₂ (Over.mk f₂) (M.pull π₂) (LB.isLB_pull hM π₂)
    inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := T₁) (U := ⊤) (x := u s) trivial
  exact ⟨u ⁻¹ᵁ V, hs, PolPull.relAmple_restrict (G := Over.mk f₁) (G' := Over.mk f₂) H hL₁ (LB.isLB_pull hM π₂)
    (lbIso_pull_comp hφ e) hA V hV⟩

theorem relAmple_of_fieldExtension [IsProper f] (hM : M.IsLB) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K)
    {f₁ : X₁ ⟶ Sp K₀} {t₁ : Sp K₀ ⟶ S} {f₂ : X₂ ⟶ Sp K} (h₁ : IsPullback π₁ f₁ f t₁)
    (h₂ : IsPullback π₂ f₂ f (spMap i ≫ t₁)) {L₁ : LB X₁} (hL₁ : L₁.IsLB) (e : LBIso L₁ (M.pull π₁))
    (hA : Out.RelAmple (Over.mk f₂) (M.pull π₂)) : Out.RelAmple (Over.mk f₁) L₁ := by
  obtain ⟨φ, hφ, H⟩ := exists_isPullback h₁ h₂ _ rfl
  have : Subsingleton (Spec (CommRingCat.of K₀)) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Spec (CommRingCat.of K)) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have : Flat (Out.specOf i) := inferInstance
  have : Surjective (Out.specOf i) := inferInstance
  have hp : IsProper f₁ := MorphismProperty.of_isPullback (P := @IsProper) h₁ ‹_›
  have : IsProper (Over.mk f₁).hom := hp
  have : IsProper f₂ := MorphismProperty.of_isPullback (P := @IsProper) h₂ ‹_›
  have : CompactSpace X₁ := QuasiCompact.compactSpace_of_compactSpace f₁
  have : QuasiSeparatedSpace X₁ := quasiSeparatedSpace_of_quasiSeparated f₁
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₁) hL₁).2 (AmpleDescent.isAmpleLB_of_pull i H hL₁ ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine (Over.mk f₂) (LB.isLB_pull hM π₂) hA).of_lbIso (LB.isLB_pull hL₁ φ)
    (lbIso_pull_comp hφ e).symm

theorem residueField_fraction {R : Type} [CommRing R] (p : Ideal R) [p.IsPrime] (y : p.ResidueField) :
    ∃ a b : R, algebraMap R p.ResidueField b ≠ 0 ∧
      y * algebraMap R p.ResidueField b = algebraMap R p.ResidueField a := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R ⧸ p) y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb' : algebraMap (R ⧸ p) p.ResidueField (Ideal.Quotient.mk p b) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  exact ⟨a, b, hb', div_mul_cancel₀ _ hb'⟩

theorem relAmple_of_geometricFibres : Out.Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), Out.RelAmple (Over.mk (pullback.snd P.A.hom y)) (M.pull (pullback.fst P.A.hom y))) → Out.RelAmple P.A M := by
  intro _ S _ P M hM hfib
  have := P.isAb.proper
  have := P.isAb.smooth
  refine AmpleLocal.relAmple_of_locally S P.A M hM inferInstance inferInstance fun s => ?_
  obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := s) trivial
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let t : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV.fromSpec
  obtain ⟨p, hp⟩ : s ∈ Set.range t := by rw [hV.range_fromSpec]; exact hs
  have hB := IsPullback.of_hasPullback P.A.hom t
  have hL := LB.isLB_pull hM (pullback.fst P.A.hom t)
  have := p.isPrime
  let g := algebraMap Γ(S, V) p.asIdeal.ResidueField
  let i := algebraMap p.asIdeal.ResidueField (AlgebraicClosure p.asIdeal.ResidueField)
  obtain ⟨r, hr, hA⟩ := GlobalTheory.T.relAmple_near_fibre_flat_projective Γ(S, V) (Over.mk (pullback.snd P.A.hom t)) (M.pull (pullback.fst P.A.hom t))
    (inferInstanceAs (Flat (pullback.snd P.A.hom t)))
    (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S P.A P.L P.isAb P.isLB P.ample _ t _ _ _ hB).1
    hL _ g (residueField_fraction p.asIdeal)
    (relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) (spMap g)).paste_horiz hB)
      (IsPullback.of_hasPullback P.A.hom _) (LB.isLB_pull hL _) (lbIso_pull_pull hM _ _) (hfib _ _))
  let D : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  have hD : p ∈ D := fun h => hr (Ideal.algebraMap_residueField_eq_zero.2 h)
  have hrange : Set.range (t ''ᵁ D).ι ⊆ Set.range (D.ι ≫ t) := by
    rintro _ ⟨⟨_, x, hx, rfl⟩, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨t ''ᵁ D, ⟨p, hD, hp⟩, ?_⟩
  exact relAmple_of_factor hM ((IsPullback.of_hasPullback (pullback.snd P.A.hom t) D.ι).paste_horiz hB)
    (isPullback_morphismRestrict P.A.hom (t ''ᵁ D)).flip (IsOpenImmersion.lift (D.ι ≫ t) _ hrange)
    (IsOpenImmersion.lift_fac _ _ _) (LB.isLB_pull hL _) (lbIso_pull_pull hM _ _) hA

end GlobalTheory.FibreAmple
end
end

