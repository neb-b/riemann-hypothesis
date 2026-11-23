module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0591
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericFibreNormalLocalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpleGenericLocal

theorem exists_relAmple (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) :
    ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  obtain ⟨V, hV, hmem, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := eSec A (IsLocalRing.closedPoint O : Sp O)) trivial
  refine GlobalTheory.ProjNormal.exists_relAmple_of_affine O A hA V hV fun s => ⟨eSec A s, ?_, ?_⟩
  · exact ((IsLocalRing.specializes_closedPoint (R := O) s).map (eSec A).continuous).mem_open V.isOpen hmem
  · rw [← Scheme.Hom.comp_apply, show eSec A ≫ A.hom = 𝟙 _ from Over.w η[A]]
    rfl

theorem exists_sec_fibre {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) (A' : Over (Sp K))
    (φ : A'.left ⟶ A.left) (hpb : IsPullback φ A'.hom A.hom (spMap (algebraMap O K))) (N : LB A.left)
    (hN : N.IsLB) (t : (N.pull φ).Sec) (ht : ∃ j, t.f j ≠ 0) (K' : Type) [Field K'] (y : Sp K' ⟶ Sp O) :
    ∃ (s : (N.pull (pullback.fst A.hom y)).Sec) (j : _), s.f j ≠ 0 := by
  haveI := hA.proper
  haveI := hA.smooth
  obtain ⟨F⟩ := GlobalTheory.ProperFinite.nonempty_perf_of_isProper A.hom (pull_isLB hN (𝟙 A.left))
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  obtain ⟨v, hv0, hv⟩ := (GlobalTheory.GenericSection.exists_sec_iff F (algebraMap O K) hpb
    (Category.comp_id φ).symm).1 ⟨t, ht⟩
  let g' : O →+* K' := (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom g') = y := by simp [g']
  have H' : IsPullback (pullback.fst A.hom y) (pullback.snd A.hom y) A.hom
      (Spec.map (CommRingCat.ofHom g')) := by
    rw [hy]
    exact IsPullback.of_hasPullback A.hom y
  exact (GlobalTheory.GenericSection.exists_sec_iff F g' H' (Category.comp_id _).symm).2
    (GlobalTheory.GenericSection.exists_ker_ne_zero _ g' hinj _ v hv0 hv)

section Cube

open ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.EffectiveCube

theorem exists_sections_cube_cover {K : Type} [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B]
    (hB : IsAbelianScheme B) {H₀ : LB B.left} (hH : H₀.IsLB) (hamp : Out.RelAmple B H₀) (N : LB B.left)
    (s : N.Sec) (hN : N.IsLB) (hs : ∃ j, s.f j ≠ 0) :
    ∃ (r : ℕ) (u : Fin r → (lbPow N 3).Sec), ⨆ i, Out.nonzeroLocus (u i) = ⊤ := by
  obtain ⟨j, hj⟩ := hs
  haveI := hB.comm
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hB hH hamp hN
  have := hB.smooth
  have := hB.proper
  have := hB.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres B.hom
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  let T : Over (Sp K) := Over.mk (𝟙 (Sp K))
  have : IsIntegral (T ⊗ B).left :=
    GeometricallyIntegral.geometrically_isIntegral (𝟙 (Sp K)) _ _ (IsPullback.of_hasPullback (𝟙 (Sp K)) B.hom).flip
  have : JacobsonSpace B.left := LocallyOfFiniteType.jacobsonSpace B.hom
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  let π : B ⟶ T := Over.homMk B.hom (Category.comp_id _)
  have hD : (((snd T B).left ⁻¹ᵁ Out.nonzeroLocus s : (T ⊗ B).left.Opens) : Set (T ⊗ B).left).Nonempty := by
    obtain ⟨d, hd⟩ : ((B.left.basicOpen (s.f j) : B.left.Opens) : Set B.left).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      exact hj ((basicOpen_eq_bot_iff _).1 (SetLike.coe_injective h))
    refine ⟨(lift π (𝟙 _)).left d, ?_⟩
    show (snd T B).left ((lift π (𝟙 _)).left d) ∈ Out.nonzeroLocus s
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hd⟩
  refine exists_fin_cover _ fun y hy => ?_
  let x : T ⟶ B := Over.homMk (pointOfClosedPoint B.hom y hy) (pointOfClosedPoint_comp B.hom y hy)
  let p : T.left := IsLocalRing.closedPoint K
  have hx : x.left p = y := pointOfClosedPoint_apply B.hom y hy p
  have hxπ : x ≫ π = 𝟙 T := Over.OverMorphism.ext (pointOfClosedPoint_comp B.hom y hy)
  have good : ∀ a : T ⟶ B, (Out.ptSecT B (a * x)).left p ∈ (snd T B).left ⁻¹ᵁ Out.nonzeroLocus s →
      UnitAt N (K := PUnit) (fun _ => ((π ≫ a) * 𝟙 B).left) (fun _ => 1) y := fun a ha => by
    apply unitAt_pull s _ y
    have e : x ≫ ((π ≫ a) * 𝟙 B) = Out.ptSecT B (a * x) ≫ snd T B := by
      simp [Out.ptSecT, MonObj.comp_mul, reassoc_of% hxπ]
    rw [← hx, ← Scheme.Hom.comp_apply, ← Over.comp_left, e]
    exact ha
  obtain ⟨a, ha, -⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x x
  obtain ⟨b, hb, hc⟩ := NoBasePoint.exists_two_points (𝟙 (Sp K)) _ hD x (a⁻¹ * x)
  rw [← _root_.mul_assoc] at hc
  choose i hi using fun k : Fin 4 => exists_chart hN ((![a, b, b⁻¹ * a⁻¹, 1] k).left p)
  obtain ⟨w, hw⟩ := SepPoints.exists_gen_three hN t ht (π ≫ a) (π ≫ b) (π ≫ (b⁻¹ * a⁻¹)) (𝟙 B) 1
    (by rw [pow_one, ← MonObj.comp_mul, ← MonObj.comp_mul]; simp) i (fun k z => by
      have e : (![(π ≫ a).left, (π ≫ b).left, (π ≫ (b⁻¹ * a⁻¹)).left, (1 : B ⟶ B).left] k) =
          π.left ≫ (![a, b, b⁻¹ * a⁻¹, 1] k).left := by
        fin_cases k
        · rfl
        · rfl
        · rfl
        · exact congrArg (fun q : B ⟶ B => q.left) (MonObj.comp_one π).symm
      rw [e, Scheme.Hom.comp_apply, spec_pt_eq (k := K) (π.left z) p]
      exact hi k)
  have hw' : UnitAt N _ _ y := ⟨genSec w hw, fun J hJ => by
    rw [sval_genSec w hw _ y hJ]; exact Units.isUnit _⟩
  refine' exists_mem_of_unitAt hN (UnitAt.congr hN (formEq_of_add fun U _ hh => ?_)
    (((hw'.mul (good a (ha p))).mul (good b (hb p))).mul (good _ (hc p))))
  simp [Fin.sum_univ_succ]
  module

end Cube

theorem relAmple_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → ∀ (M : LB A.left) (M' : LB A'.left), M.IsLB → M'.IsLB → LBIso M' (M.pull φ) → Out.RelAmple A' M' → Out.RelAmple A M := by
  intro O K _ _ _ _ _ _ _ _ A _ A' _ φ hA hpb M M' hM hM' e hamp
  obtain ⟨L, hL, hLa⟩ := exists_relAmple O A hA
  haveI := hA.proper
  haveI := hA.smooth
  have hpb' : IsPullback φ A'.hom A.hom (spMap (algebraMap O K)) := hpb.1
  haveI hA'p : IsProper A'.hom := MorphismProperty.of_isPullback hpb' hA.proper
  have hampφ : Out.RelAmple A' (M.pull φ) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' (pull_isLB hM φ)).2
      ((GlobalTheory.isAmpleLB_congr hM' (pull_isLB hM φ) e).1 ((GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A' hM').1 hamp))
  have hne : Nonempty A'.left := ⟨eSec A' (Classical.arbitrary (Sp K))⟩
  obtain ⟨a, s, ha, hs⟩ := GlobalTheory.AmpleDivSec.exists_sec_pow_div_ne_zero K A' (L.pull φ) (M.pull φ) hA'p hne
    (pull_isLB hL φ) (pull_isLB hM φ) hampφ
  have hN : (LB.div (lbPow M a) L).IsLB := LB.isLB_div (LB.isLB_linComb hM _ _) hL
  have hN' : ∀ {Y : Scheme.{0}} (f : Y ⟶ A.left), (LB.div (lbPow (M.pull f) a) (L.pull f)).IsLB := fun f =>
    LB.isLB_div (LB.isLB_linComb (pull_isLB hM f) _ _) (pull_isLB hL f)
  obtain ⟨t, ht⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (pull_isLB hN φ) (hN' φ)
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM φ a) ⟨s, hs⟩
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K' _ _ y => ?_
  obtain ⟨t', j, ht'⟩ := exists_sec_fibre A hA A' φ hpb' _ hN t ht K' y
  have hB : IsAbelianScheme ((Over.pullback y).obj A) := Out.TLinPf.isAb_pullback y A hA
  have hpbB : IsPullback (pullback.fst A.hom y) ((Over.pullback y).obj A).hom A.hom y :=
    IsPullback.of_hasPullback A.hom y
  have hLB : Out.RelAmple ((Over.pullback y).obj A) (L.pull (pullback.fst A.hom y)) :=
    GlobalTheory.AmpleLocalBase.relAmple_baseChange hpbB hL (pull_isLB hL _) (GlobalTheory.lbIso_refl (pull_isLB hL _)) hLa
  obtain ⟨t'', ht''⟩ := GlobalTheory.AmpleSpecialisation.exists_sec_ne_zero_of_lbIso (hN' _) (pull_isLB hN _)
    (GlobalTheory.AmpleSpecialisation.lbIso_pull_div_lbPow hL hM (pullback.fst A.hom y) a).symm ⟨t', j, ht'⟩
  obtain ⟨r, u, hu⟩ := exists_sections_cube_cover ((Over.pullback y).obj A) hB (pull_isLB hL _) hLB _ t''
    (hN' _) ht''
  exact GlobalTheory.isAmpleLB_of_relAmple_of_isAffine _ (pull_isLB hM _)
    (GlobalTheory.relAmple_of_cube_div_generated K' ((Over.pullback y).obj A) (L.pull (pullback.fst A.hom y))
      (M.pull (pullback.fst A.hom y)) a r u hB.proper (pull_isLB hL _) (pull_isLB hM _) ha hLB hu)

end GlobalTheory.AmpleGenericLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueModelAtPrime
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open GlobalTheory.UPel.HT.Hecke

section GeomAux

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem liftSq_mul' {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

theorem liftSq_pow' {T : Over S} (a b : T ⟶ A) (n : ℕ) :
    (lift a b : T ⟶ G2 A) ^ n = lift (a ^ n) (b ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.pow_comp]; simp
  · rw [MonObj.pow_comp]; simp

end GeomAux

theorem weilIs_heckeSubA_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ v : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 g₂ : 𝟙_ (Over S) ⟶ G2 o.A)) v → v = 1 := by

  intro p _ D R _ b h u c k N hc hk hN hNp hck _hlin hcomp hsim _hsurj S s o g₁ hg₁ g₂ hg₂ K _ _ x β hx v hv
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hPL : o.P.IsLB := o.isLB
  obtain ⟨I, hI⟩ := o.geom K x β hx
  obtain ⟨x₁, rfl⟩ := hg₁
  obtain ⟨x₂, rfl⟩ := hg₂
  have hpp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; exact absurd (Nat.coprime_zero_left p |>.1 hk) hpp.one_lt.ne'
    · exact h0
  have hN0 : 0 < N := by omega
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; exact absurd (Nat.eq_zero_of_zero_dvd hck) (pow_ne_zero 2 hk0.ne')
    · exact h0

  have hNk0 : 0 < N * k := Nat.mul_pos hN0 hk0
  have hNkp : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  have hn'p : (N * k * c).Coprime p := Nat.Coprime.mul_left hNkp hc
  have hn'0 : 0 < N * k * c := Nat.mul_pos hNk0 hc0
  have hmove : ∀ z : D.La, o.eta (N • h (N * k) z) = o.eta (N • h (N * k * c) z) := fun z => by
    obtain ⟨z', hz'⟩ := (hcomp (N * k) c hNk0 hc0 hn'p).1 z
    rw [hz', smul_add, o.eta_add, smul_comm N (N * k) z', o.eta_ker, _root_.mul_one]
  rw [hmove, hmove] at hv
  have hdivE : ((c : ℕ) : ℤ) ∣ D.EF (h (N * k * c) x₁) (h (N * k * c) x₂) := by
    have h1 := (hsim (N * k * c) hn'0 hn'p).2 x₁ x₂
    have h2 : ((c : ℕ) : ℤ) ∣ ((N * k * c : ℕ) : ℤ) := by
      exact_mod_cast Dvd.intro_left (N * k) rfl
    have h3 := h2.trans h1
    have h4 : ((c : ℕ) : ℤ) ∣ (c : ℤ) * u (N * k * c) * D.EF x₁ x₂ :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
    have h5 := dvd_add h3 h4
    rwa [sub_add_cancel] at h5
  obtain ⟨e', he'⟩ := hdivE
  obtain ⟨f, hf⟩ : ∃ f, f = h (N * k * c) := ⟨_, rfl⟩
  rw [← hf] at hv he'
  obtain ⟨m, hm⟩ : ∃ m, m = k ^ 2 / c := ⟨_, rfl⟩
  rw [← hm] at hv
  have hmc : m * c = k ^ 2 := by rw [hm]; exact Nat.div_mul_cancel hck
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hmc; exact absurd hmc.symm (pow_ne_zero 2 hk0.ne')
    · exact h0
  obtain ⟨j, hj0, hjp, hjpar⟩ : ∃ j : ℕ, 0 < j ∧ (j * k ^ 2).Coprime p ∧ (Even j ∨ Odd (j * k ^ 2)) := by
    by_cases h2 : p = 2
    · subst h2
      have hko : Odd k := Nat.coprime_two_right.1 hk
      exact ⟨1, one_pos, by rw [_root_.one_mul]; exact Nat.Coprime.pow_left 2 hk,
        Or.inr (by rw [_root_.one_mul]; exact hko.pow)⟩
    · refine ⟨2, two_pos, Nat.coprime_mul_iff_left.2 ⟨?_, Nat.Coprime.pow_left 2 hk⟩, Or.inl even_two⟩
      exact (Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm h2)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = j * k ^ 2 := ⟨_, rfl⟩
  rw [← hn₀] at hjp hjpar
  have hn0 : 0 < n₀ := by rw [hn₀]; positivity
  have ev0 : ∀ n, I.ev n 0 = 1 := fun n => by
    have h0 := I.add n 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.1 h0.symm)
  have evs : ∀ n (z : D.La) (r : ℕ), I.ev n (r • z) = I.ev n z ^ r := fun n z r => by
    induction r with
    | zero => rw [zero_smul, pow_zero, ev0]
    | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hdown : ∀ z : D.La, toUnit (Over.mk x) ≫ o.eta (N • z) = I.ev n₀ z ^ (j * k) := fun z => by
    have t1 := I.tower k N hk0 hN0 (Nat.coprime_mul_iff_left.2 ⟨hk, hNp⟩) z
    have e : k * (j * k) = n₀ := by rw [hn₀]; ring
    have t2 := I.tower k (j * k) hk0 (by positivity) (by rw [e]; exact hjp) z
    rw [Nat.mul_comm k N] at t1
    rw [hI, evs, t1, ← t2, e]
  obtain ⟨w, hw⟩ : ∃ w, w = I.ev n₀ (f x₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = I.ev n₀ (f x₂) := ⟨_, rfl⟩
  have ha : toUnit (Over.mk x) ≫ (lift (o.eta (N • f x₁)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (w ^ (j * k)) (1 ^ (j * k)) := by
    rw [comp_lift, hdown, ← hw, one_pow, MonObj.comp_one]
  have hb : toUnit (Over.mk x) ≫ (lift 1 (o.eta (N • f x₂)) : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (1 ^ (j * k)) (y ^ (j * k)) := by
    rw [comp_lift, hdown, ← hy, one_pow, MonObj.comp_one]
  rw [ha, hb] at hv
  have e1 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ m (j * k) (j * k) 1 (Over.mk x) w 1 1 y v hv
  have hwn : w ^ n₀ = 1 := (I.onto n₀ hn0 hjp w).2 ⟨f x₁, hw.symm⟩
  have hyn : y ^ n₀ = 1 := (I.onto n₀ hn0 hjp y).2 ⟨f x₂, hy.symm⟩
  have hK : ((n₀ : ℕ) : K) ≠ 0 := by
    have := (b.unit n₀ hjp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have tor : ∀ a a' : Over.mk x ⟶ o.A, a ^ n₀ = 1 → a' ^ n₀ = 1 →
      (lift a a' : Over.mk x ⟶ G2 o.A) ^ n₀ = 1 := fun a a' h1 h1' => by
    rw [liftSq_pow', h1, h1']
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have one_n : (1 : Over.mk x ⟶ o.A) ^ n₀ = 1 := one_pow _
  have ex : ∀ X Y : Over.mk x ⟶ G2 o.A, X ^ n₀ = 1 → Y ^ n₀ = 1 →
      ∃ e : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) X Y e := fun X Y hX hY =>
    GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 o.A) o.P hA2 hPL K x n₀ hn0 hK X Y hX hY
  obtain ⟨F, hF⟩ := ex _ _ (tor w 1 hwn one_n) (tor 1 y one_n hyn)
  have hFp : ∀ r : ℕ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (r + 1)) 1) (lift 1 y) (F ^ (r + 1)) := by
    intro r
    induction r with
    | zero => simpa using hF
    | succ r ih =>
      have := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL ih hF
      rwa [liftSq_mul', _root_.mul_one, ← pow_succ, ← pow_succ] at this
  have hjm : j * m = (j * m - 1) + 1 := (Nat.sub_add_cancel (Nat.mul_pos hj0 hm0)).symm
  have hFjm : Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (j * m)) 1) (lift 1 y) (F ^ (j * m)) := by
    rw [hjm]; exact hFp _
  have hl1 : (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1).IsLB := LB.isLB_linComb hPL _ _
  have iso1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (o.P.pull (Over.Hom.left (𝟙 (G2 o.A)))) := by
    have c1 := GlobalTheory.CechPic.cls_linComb hPL (fun _ : Fin 1 => 𝟙 (G2 o.A).left) (fun _ => (1 : ℤ)) hl1
    have c2 := GlobalTheory.CechPic.cls_pull hPL (Over.Hom.left (𝟙 (G2 o.A))) (pull_isLB hPL _)
    refine (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB hPL _)).1 (c1.trans (Eq.trans ?_ c2.symm))
    simp
  have e2' : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (n₀ : ℤ) (lift (w ^ (j * m)) (1 ^ 1))
      (lift (1 ^ (j * m)) (y ^ 1)) (F ^ (j * m)) := by
    rw [one_pow, one_pow, pow_one]
    exact GlobalTheory.PELFamily.weilIs_of_lbIso hG hA2 hl1 hPL iso1 hFjm
  have e2 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ 1 (j * m) 1 (n₀ : ℤ) (Over.mk x) w 1 1 y _ e2'
  have hlev : (1 : ℤ) * ((m * (j * k) * (j * k) : ℕ) : ℤ) = (n₀ : ℤ) * ((1 * (j * m) * 1 : ℕ) : ℤ) := by
    rw [hn₀]; push_cast; ring
  have hv' : v = F ^ (j * m) := GlobalTheory.CommutatorPairing.weilIs_unique hG hA2 hPL e1 (hlev ▸ e2)
  have hgeo := I.isom n₀ hn0 hjp (f x₁) (f x₂)
  rw [← hw, ← hy] at hgeo
  obtain ⟨c11, h11⟩ := ex (lift w 1) (lift y 1) (tor w 1 hwn one_n) (tor y 1 hyn one_n)
  obtain ⟨c21, h21⟩ := ex (lift 1 w) (lift y 1) (tor 1 w one_n hwn) (tor y 1 hyn one_n)
  obtain ⟨c22, h22⟩ := ex (lift 1 w) (lift 1 y) (tor 1 w one_n hwn) (tor 1 y one_n hyn)
  have hA := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL h11 h21
  have hB := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL hF h22
  rw [liftSq_mul', _root_.mul_one, _root_.one_mul] at hA hB
  have hs := GlobalTheory.CommPairing.weilIs_symm hPL (GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL
    (GlobalTheory.CommPairing.weilIs_symm hPL hA) (GlobalTheory.CommPairing.weilIs_symm hPL hB))
  rw [liftSq_mul', _root_.mul_one, _root_.one_mul] at hs
  have hd := GlobalTheory.T.weilPairing_diagonal_pullback_eq S o.A o.P o.ab hPL _ (Over.mk x) w y _ _ hs hgeo
  have e11 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c11).1 h11
  have e22 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c22).2 h22
  have e21 := GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant S o.A o.P o.ab hPL o.symm _ (Over.mk x) w y c21 F h21 hF
  rw [e11, e22, e21] at hd
  have hF2 : F ^ 2 = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * e'))) := by
    rw [← he', ← hd]; group
  have hζ : I.ζ n₀ ^ n₀ = 1 := (I.ζ_prim n₀ hn0 hjp).pow_eq_one
  have hz : ∀ z : ℤ, I.ζ n₀ ^ ((n₀ : ℤ) * z) = 1 := fun z => by
    rw [zpow_mul, zpow_natCast, hζ, one_zpow]
  have hmcZ : (m : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hmc
  have hnZ : (n₀ : ℤ) = j * (k : ℤ) ^ 2 := by rw [hn₀]; push_cast; ring
  have uPow : ∀ (a : Kˣ) (n : ℕ), unitOn (a ^ n) = unitOn a ^ n := fun a n => map_pow (Units.map _) a n
  have uOne : unitOn (1 : Kˣ) = 1 := map_one (Units.map _)
  have hpw : ∀ t : ℕ, F ^ (2 * t) = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * e') * (t : ℤ))) := fun t => by
    rw [pow_mul, hF2, ← uPow, ← zpow_natCast, ← zpow_mul]
  rcases hjpar with ⟨i, hi⟩ | hodd
  · have e : j * m = 2 * (i * m) := by rw [hi]; ring
    rw [hv', e, hpw]
    have ex' : 2 * ((c : ℤ) * e') * ((i * m : ℕ) : ℤ) = (n₀ : ℤ) * e' := by
      rw [hnZ, ← hmcZ, hi]; push_cast; ring
    rw [ex', hz, uOne]
  · have h2 : v ^ 2 = 1 := by
      rw [hv', ← pow_mul, Nat.mul_comm, hpw]
      have ex' : 2 * ((c : ℤ) * e') * ((j * m : ℕ) : ℤ) = (n₀ : ℤ) * (2 * e') := by
        rw [hnZ, ← hmcZ]; push_cast; ring
      rw [ex', hz, uOne]
    have hFn : F ^ n₀ = 1 := GlobalTheory.SiegelTypings.weil_pow_eq_one hA2 hPL (tor w 1 hwn one_n) hF
    have hn : v ^ n₀ = 1 := by rw [hv', ← pow_mul, Nat.mul_comm, pow_mul, hFn, one_pow]
    have hgcd := pow_gcd_eq_one.2 ⟨h2, hn⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), pow_one] at hgcd

end GlobalTheory.UPel.HT.HeckeAd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueUnitFrameConjPointEqPhaseConj
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

def conjPt {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} (y : CxPts p σ) :
    CxPts p ((starRingEnd ℂ).comp σ) :=
  ⟨spMap (starRingEnd ℂ) ≫ y.1, by
    have e : spMap ((starRingEnd ℂ).comp σ) = spMap (starRingEnd ℂ) ≫ spMap σ := by
      rw [spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    rw [Category.assoc, y.2, e]⟩

theorem ratVal_conj {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp k} {σ σ' : k →+* ℂ}
    {f : X.functionField} {y : CxPts q σ} {y' : CxPts q σ'}
    (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hf : RegAt (under y) f) :
    ratVal f y' = starRingEnd ℂ (ratVal f y) := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hy : y ∈ ptsIn q σ U := mem_ptsIn.2 hU
  rw [ratVal_fnOf hy, ratVal_fnOf (CxPts.mem_ptsIn_conj h hy), CxPts.ev_conj h hy]

theorem val_conj : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ), ∃ (σ' : k →+* ℂ) (y' : CxPts p σ') (θ : ℂ), ‖θ‖ = 1 ∧ ∀ f ∈ P.H a b, val P a b σ' y' f = θ * (starRingEnd ℂ) (val P a b σ y f) := by
  intro k _ X _ p P a b σ y
  have h : (conjPt y).1 = spMap (starRingEnd ℂ) ≫ y.1 := rfl
  have hi := mem_pick (P.L.φ σ).isLB y
  have hj := mem_pick (P.A.φ σ).isLB y
  obtain ⟨θ₁, h₁, e₁⟩ := _root_.GlobalTheory.HSAmp.val_frame k X p P a b σ y _ _ hi hj
  obtain ⟨θ₂, h₂, e₂⟩ := _root_.GlobalTheory.HSAmp.val_frame k X p P a b _ (conjPt y) _ _
    (CxPts.mem_ptsIn_conj h hi) (CxPts.mem_ptsIn_conj h hj)
  refine ⟨_, conjPt y, θ₂ * θ₁, by rw [norm_mul, h₁, h₂, one_mul], fun f hf => ?_⟩
  have hreg := hf _ _ _ (mem_ptsIn.1 hi) (mem_ptsIn.1 hj)
  rw [e₁ f hf, e₂ f hf, ratVal_conj h hreg, P.L.conj σ _ _ y _ h hi, P.A.conj σ _ _ y _ h hj]
  have hθ : θ₁ * starRingEnd ℂ θ₁ = 1 := by
    rw [Complex.mul_conj', h₁]
    simp
  simp only [map_mul, Complex.conj_ofReal]
  linear_combination (-(θ₂ * starRingEnd ℂ (ratVal (P.loc a b f (pick (P.L.φ σ).isLB y) (pick (P.A.φ σ).isLB y)) y) *
    ((Real.exp (-(a * (P.L.φ σ).φ (pick (P.L.φ σ).isLB y) y + b * (P.A.φ σ).φ (pick (P.A.φ σ).isLB y) y) / 2) : ℝ) : ℂ))) * hθ

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortSeriesTraceTermAtEvaluationVector
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.OneTermEval


set_option maxHeartbeats 4000000 in
theorem series_term_at_eval : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∃ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) ∧ (∀ lam : HeightOneSpectrum (𝓞 D.what₂.LL), Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) → ∃ s : 𝓞 D.what₂.LL, s ∉ lam.asIdeal ∧ IsIntegral ℤ ((s : D.what₂.LL) * c)) ∧ ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → ∀ u : U, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hC i hOM hβ hU hIo hRow hPh hCS v hv hmu hQG hFO hVal hdel hMb hRun ℓ hLev hAct U hdet χ ξR ω φ hK Λ h hSp hLa N x₀ P x f y h1 h2 h3 h4 h5 h6 h7 h8
  have base := GlobalTheory.T.shortSeries_baseDatum_adelicForm_multiple D G Pl0 T0 A T R F κ v₀ fw O hT hC i hOM hβ hU hIo hRow hPh hCS v hv hmu hQG hFO hVal hdel hMb hRun ℓ hLev hAct χ ξR ω φ hK Λ h hSp hLa N x₀ P y h1 h2 h3 h4 h5 h6 h8
  rcases base with ⟨y₀, c, hr, hc, hmain⟩
  refine ⟨y₀, c, hr, hc, fun φ' hφ' w hw u => ?_⟩
  obtain ⟨F₀, hF₀, he⟩ := GlobalTheory.LevelMoveShort.short_translate D G Pl0 T0 A T R F κ v₀ fw hT hC i hU ℓ hLev hAct v (ownAt D v) hRun hMb U hdet Λ N x₀ P x f h1 h2 h3 h4 h5 h6 h7 u
  have e := (hU i (sg0 D A)).2.2 ((u : G)⁻¹) (cuspTo hT.p fw i F₀)
  have hc1 : (R.FW i).chi ((u : G)⁻¹) = 1 := by
    apply Units.ext
    apply D.what₂.embLL.injective
    rw [hC.grp.chiW, Units.val_one, map_one]
    refine Finset.prod_eq_one fun PP _ => ?_
    have hd : Matrix.GeneralLinearGroup.det (R.eG ((u : G)⁻¹) PP) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      exact hdet u⁻¹ PP
    rw [hd, map_one, Units.val_one]
  rw [hc1, Units.val_one, map_one, one_smul] at e
  have e2 : adForm R i ((R.FW i).ρ ((u : G)⁻¹) (cuspTo hT.p fw i F₀)) (fun ρ => w ρ) =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (adForm R i (cuspTo hT.p fw i F₀) (fun ρ => w ρ)) :=
    congrArg (fun T => T (fun ρ => w ρ)) e
  rw [he, e2, hmain φ' hφ' w hw F₀ hF₀, map_smul]

end GlobalTheory.OneTermEval
end
end

