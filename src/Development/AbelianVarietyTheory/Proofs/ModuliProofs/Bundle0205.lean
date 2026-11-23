module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ExtensionMul

section General

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

theorem exists_isPullback_pow [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P P' Q : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q)
    {p : P' ⟶ P} {y : P' ⟶ G} (hP' : IsPullback y p q b)
    {s : Q ⟶ P'} {r : Q ⟶ G} (hQ : IsPullback s r p φ) :
    ∃ (c : P' ⟶ T) (t : Q ⟶ T), IsPullback s t c ((𝟙 T) ^ N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  obtain ⟨c, hc⟩ := ex ((p ≫ a) / y ^ N) (by
    rw [GrpObj.div_comp, Category.assoc, hP.w, MonObj.pow_comp, hP'.w, ← Category.assoc, MonObj.comp_pow,
      Category.comp_id, div_self'])
  have hsr : s ≫ y ≫ q = r ≫ q := by
    rw [hP'.w, ← Category.assoc, hQ.w, Category.assoc, hφb]
  have hsa : s ≫ p ≫ a = r ^ N := by
    rw [← Category.assoc, hQ.w, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id]
  obtain ⟨t, ht⟩ := ex (r / (s ≫ y)) (by
    rw [GrpObj.div_comp, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, ht, div_pow, Category.assoc, hc, GrpObj.comp_div, hsa,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, MonObj.comp_pow, Category.comp_id]
    have hl : W.fst ≫ p = ((W.snd ≫ i) * (W.fst ≫ y)) ≫ φ := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id, mul_pow,
          ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, GrpObj.comp_div, MonObj.comp_pow, div_mul_cancel]
      · rw [Category.assoc, Category.assoc, hφb, MonObj.mul_comp, Category.assoc, Category.assoc, hiq,
          MonObj.comp_one, _root_.one_mul, hP'.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, hQ.lift_fst, hQ.lift_snd, mul_div_cancel_right]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      rw [hQ.lift_snd, ← h1, ← h2, Category.assoc, Category.assoc, ht, GrpObj.comp_div, div_mul_cancel]

theorem of_pow_kernel (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q) (h : Pr ((𝟙 T) ^ N : T ⟶ T).left) :
    Pr φ.left := by
  have hP' := IsPullback.of_hasPullback q b
  have hQ := IsPullback.of_hasPullback (pullback.snd q b) φ
  obtain ⟨c, t, H⟩ := exists_isPullback_pow i q hk N hP hφa hφb hP' hQ
  have hP'' := hP'.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end General

theorem pow_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : E.IsGt G)
    (N : ℕ) (hN : 1 ≤ N) (h1 : IsFinite ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) (h2 : Flat ((𝟙 E.B) ^ N : E.B ⟶ E.B).left)
    (h3 : Surjective ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) :
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left ∧ Flat ((𝟙 G) ^ N : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ N : G ⟶ G).left := by
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have hs : Surjective (mulN (splitTorus S E.X) N).left := Diag.surjective_mulN S E.X hN'
  rw [MulEtaleDvr.mulN_eq_pow] at hf hl hs
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 E.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 E.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a0 : Surjective (hP.lift _ _ w).left := of_pow_kernel @Surjective D.i D.q D.isKernel N hP ha hb hs
  have a1 : Flat (hP.lift _ _ w).left := of_pow_kernel @Flat D.i D.q D.isKernel N hP ha hb hl
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget S)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  have b2 : Flat (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @Flat) hP' h2
  have b3 : Surjective (pullback.fst D.q ((𝟙 E.B) ^ N)).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hP' h3
  rw [← ha, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

theorem exists_represents_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ ∧ Smooth Gt.hom ∧ IsSeparated Gt.hom ∧ ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left := by
  intro R _ _ _ D
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hL.globalFns (TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := TorusModel.exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ,
    (UnitRigidity.smooth_geometricallyConnected_of_isGt _ H hH).1, ?_, fun k hk => ?_⟩
  · obtain ⟨d⟩ := hH
    have := d.q_affine
    have := (TorusModel.splitExt D).isAbelian.proper
    rw [← Over.w d.q]
    infer_instance
  · obtain ⟨h₁, h₂, h₃, -⟩ := hL.mulN _ D.P k hk
    exact pow_of_isGt _ H hH k hk h₁ h₂ h₃

end GlobalTheory.ExtensionMul
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrime
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

section
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R : Type} [CommRing R] {β : o →+* R} {v : Ix g (N' ^ 2) → R}

theorem nearC_of_den_loc (h2 : Out.Laws2) {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀)
    (H : ∀ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ →
      NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁) : NearC b Mat κ β v q₀ := by
  obtain ⟨q₁, hq₁, rfl⟩ := h.loc hf
  exact GlobalTheory.ZM.NearBuild.nearC_of_loc h2 o g N' J b Mat κ R β v f q₁ (isPrime_of_mem hq₁.2) (H q₁ hq₁)

theorem span_map {R' I : Type} [CommRing R'] (ρ : R →+* R') {w : I → R} (h : Ideal.span (Set.range w) = ⊤) :
    Ideal.span (Set.range fun a => ρ (w a)) = ⊤ := by
  have := congrArg (Ideal.map ρ) h
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem span_of_unit {R' I : Type} [CommRing R'] {w : I → R'} (a : I) (h : IsUnit (w a)) :
    Ideal.span (Set.range w) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) h

theorem isUnit_loc {f a : R} (h : a ∣ f) : IsUnit (loc f a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit f)
end

section
variable (h1 : Out.Laws) (h2 : Out.Laws2) {g : ℕ} {J : Type} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
  {κ n j : ℕ} (hn : n.Prime) (hodd : Odd n) (hj : 2 ≤ j) {o : Type} [CommRing o] {b : TBase o ((n ^ j) ^ 2)}
include h1 h2 hn hodd hj

theorem nearC_of_grpFam {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {A : Over (Sp R)} [GrpObj A] {M : LB A.left} {act : J → (A ⟶ A)}
    {Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hA : GrpFam b Mat κ β v (n ^ 2) A M act Q) : NearC b Mat κ β v q₀ := by
  obtain ⟨L, hL⟩ := GlobalTheory.ZM.NearBuild.exists_polFam_of_grpFam h1 h2 o g _ J b Mat κ R β v (n ^ 2) A M act Q (pow_ne_zero _ hn.ne_zero) hodd.pow
    (pow_dvd_pow n hj) h.1 hA
  obtain ⟨f, hf, hK⟩ := GlobalTheory.ZM.NearBuild.kTriv_near_good_prime o g _ J b Mat κ R β v A L act Q q₀ h.2 hL
  obtain ⟨act', Q', hL'⟩ := GlobalTheory.ZM.NearBuild.polFam_baseChange o g _ J b Mat κ R β v A L act Q _ (loc f) hL
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ =>
    GlobalTheory.ZM.NearBuild.nearC_of_polFam_of_kTriv h1 h2 g n j J hn hodd hj o b Mat κ _ _ _ _ _ act' Q' q₁ hq₁ (span_map _ hv) hL' hK

theorem nearC_of_smooth [Finite J]
    (hadd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu)
    (hend : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc)
    (hs : SmoothOfRelativeDimension g Z.hom) : NearC b Mat κ β v q₀ := by
  classical
  have := Fintype.ofFinite J
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  have hs' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have hq := isPrime_of_mem h.2
  obtain ⟨f₁, hf₁, hmu⟩ := hadd R β v Z M th sc q₀ h hZ hs'
  choose f₂ hf₂ hF using fun i => hend R β v Z M th sc q₀ i h hZ hs'
  obtain ⟨f₃, hf₃, hc⟩ : ∃ f, f ∉ q₀ ∧ GeometricallyConnected (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ConnSpread.exists_geometricallyConnected_away_of_fibre R _ Z.hom K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).1 hs' ?_
    have := t.ab.geomConnected
    refine MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) this
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  let f := f₁ * f₃ * ∏ i, f₂ i
  have hf : f ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact (hq.mem_or_mem hh).elim hf₁ hf₃
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact hf₂ i hi
  let Z' : Over (Sp (Localization.Away f)) := Over.mk (pullback.snd Z.hom (spMap (loc f)))
  have hpb : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom (spMap (loc f)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨mu, hmu⟩ := hmu _ (loc f) (isUnit_loc ((dvd_mul_right f₁ f₃).mul_right _)) Z' _ hpb
  choose F hF using fun i => hF i _ (loc f)
    (isUnit_loc ((Finset.dvd_prod_of_mem f₂ (Finset.mem_univ i)).mul_left _)) Z' _ hpb
  obtain ⟨th', sc', hZ', hfib⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f) Z' _ hpb hZ
  have hs₁ : SmoothOfRelativeDimension g Z'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb hs
  have hc₁ : GeometricallyConnected Z'.hom := by
    have hu : IsUnit (loc f f₃) := isUnit_loc ((dvd_mul_left f₃ f₁).mul_right _)
    have e : spMap (loc f) = spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃) := by
      rw [← spMap_comp, IsLocalization.Away.lift_comp]
    have hpb' : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom
        (spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃)) := by
      rw [← e]; exact hpb
    have hp₃ := IsPullback.of_hasPullback Z.hom (spMap (loc f₃))
    have := IsPullback.of_right (h₁₁ := hp₃.lift _ _ (hpb'.w.trans (Category.assoc _ _ _).symm))
      (by rw [IsPullback.lift_fst]; exact hpb') (hp₃.lift_snd _ _ _) hp₃
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) this hc
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨_, hG⟩ := GlobalTheory.ZM.NearBuild.grpFam_of_dense_fibres h1 h2 o g _ J b Mat κ _ _ _ _ Z' _ th' sc' mu F (pow_ne_zero _ hn.ne_zero) hq₁.1 hZ' hs₁ hc₁
    (fun K _ _ x s t φ ht hφ => hmu K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
    (fun i K _ _ x s t φ ht hφ => hF i K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
  exact nearC_of_grpFam h1 h2 hn hodd hj hq₁ (span_map _ hv) hG


omit h1 hodd hj in
theorem nearC_of_fam
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → SmoothOfRelativeDimension g Z.hom →
      NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, hs⟩ : ∃ f, f ∉ q₀ ∧ SmoothOfRelativeDimension g (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ProperFlatNearFibre.exists_away_smoothOfRelativeDimension R _ Z.hom g K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).2.1 hZ.2.1 ?_
    refine (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) t.dim
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  obtain ⟨th', sc', hZ', -⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f)
    (Over.mk (pullback.snd Z.hom (spMap (loc f)))) _ (IsPullback.of_hasPullback _ _) hZ
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ => H hq₁ (span_map _ hv) hZ' hs


omit h1 hodd hj in
theorem nearC_of_unimodular
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R} {Hh : Type} [Finite Hh]
    {hh : Hh → Ix g ((n ^ j) ^ 2)} {Q : Polynomial ℚ} {d : ℕ} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hp : ∀ c, Ideal.span (Set.range (p c)) = ⊤)
    (hD : FibData b Mat κ β v (n ^ 2) p hh Q d) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, Z, M, th, hrep, hfl, hfib⟩ := GlobalTheory.ZM.NearCut.exists_away_flat_projRep R _ Hh (fun c => p (hh c)) Q d _ h.1 (fun q hq => by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨σ, I, -, -, -, hc, -⟩ := hD K x s t ht
    exact ⟨K, inferInstance, x, I, rfl, hc⟩) q₀ h.2
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨sc, hZ⟩ := GlobalTheory.ZM.FamOf.exists_sections_fam o g _ J b Mat κ _ _ _ _ _ Hh hh Q d Z M th hq₁.1 (hD.comp (loc f))
    (fun c => span_map _ (hp c)) hrep hfl hfib
  exact H hq₁ (span_map _ hv) hZ
end

theorem exists_tObj_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  classical
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, H₁⟩ := _root_.GlobalTheory.ZM.GoodFibre.exists_fibData h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₂, H₂⟩ := _root_.GlobalTheory.ZM.NearBuild.exists_add_near h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₃, H₃⟩ := _root_.GlobalTheory.ZM.NearBuild.exists_endomorphism_near h1 h2 g J Mat κ n hn hodd
  refine ⟨j₁ + j₂ + j₃ + 2, fun j hj o _ b R _ _ _ β v hd q₀ hq₀ => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  suffices H : NearC b Mat κ β v q₀ by
    obtain ⟨f, hf, t, ht, H⟩ := H
    exact ⟨f, t, hf, ht, fun K _ _ x t' k₁ k₂ => H K x _ t' ⟨rfl, k₁, k₂⟩⟩
  obtain ⟨p, Hh, _, hh, Q, d, hD⟩ := H₁ j (by omega) o b R β v
  have hq := isPrime_of_mem hq₀
  obtain ⟨⟨a₀, ha₀⟩, hp⟩ : (∃ a, v a ∉ q₀) ∧ ∀ c, ∃ a, p c a ∉ q₀ := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq₀
    constructor
    · obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh h1 h2 o g _ J b _ s t n K _ _ ⊥ hn.two_le (dvd_pow_self n (by omega)) ht.2.2
        Ideal.isPrime_bot 0
      exact ⟨_, hc⟩
    · intro c
      obtain ⟨σ, I, -, hrep, -, -, hc⟩ := hD K x s t ht
      have := (hrep.2.1 K (RingHom.id K) _ _ (by
        rw [← Over.comp_left, lift_fst]
        exact (Spec.map_id _).symm) (hc c)).1
      by_contra hne
      push Not at hne
      refine (Ideal.isPrime_bot (α := K)).ne_top (eq_top_iff.2 (this ▸ Ideal.span_le.2 ?_))
      rintro _ ⟨a, rfl⟩
      exact hne a
  choose a ha using hp
  have hf : v a₀ * ∏ c, p c (a c) ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact ha₀ hh
    · obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact ha c hc
  refine nearC_of_den_loc h2 ⟨hd, hq₀⟩ hf fun q₁ hq₁ => ?_
  refine nearC_of_unimodular h2 hn (nearC_of_fam h2 hn (nearC_of_smooth h1 h2 hn hodd (by omega)
    (H₂ j (by omega) o b) (H₃ j (by omega) o b))) hq₁
    (span_of_unit a₀ (isUnit_loc (dvd_mul_right _ _))) (fun c => span_of_unit (a c) (isUnit_loc
      ((Finset.dvd_prod_of_mem (fun c => p c (a c)) (Finset.mem_univ c)).mul_left _))) (hD.comp _)

end GlobalTheory.ZM.NearBuild
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionToG
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors

open GlobalTheory.TorusModel GlobalTheory.TorsionFormCompare GlobalTheory.KernelNoTorsion

theorem exists_torsion_toG : AllFlat fun {E} _ _ _ {H} {R} _ _ _ {t} P {W} ψW k => ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), IsFinite N.hom ∧ Flat N.hom ∧ Etale (pullback.snd N.hom (jK R)) ∧ GtTors k g₀ ∧ (∀ (T : Over (Sp R)) (g : GtPt P.D.toPre T), GtTors k g → ∃! h : T ⟶ N, GtPt.IsPull h.left g₀ g) ∧ x₀ ^ k = 1 ∧ FormalEq P.U.toUnifPre x₀ g₀ := by
  intro E _ _ _ H R _ _ _ _ hR t P W _ _ ψW k hk
  obtain ⟨_, -, -, hc⟩ := hR
  have hL := abelianSchemeLaws_all.1
  obtain ⟨Gt, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt P.D.toPre)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  have hΦ : Represents Φ := hΦ
  have hfin : IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
    obtain ⟨h₁, h₂, -⟩ := hL.mulN _ P.D.toPre.P k hk
    have h₁' : IsFinite (𝟙 P.D.toPre.P.A ^ k).left := h₁
    have h₂' : Flat (𝟙 P.D.toPre.P.A ^ k).left := h₂
    rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
    have Q := MulEtaleDvr.isPullback_torsion P.D.toPre.P.A k
    exact isFinite_flat_torsion_of_isGt _ (splitExt P.D.toPre) Gt hH k hk
      (MorphismProperty.of_isPullback (P := @IsFinite) Q h₁') (MorphismProperty.of_isPullback (P := @Flat) Q h₂')
  obtain ⟨hf, hl⟩ := hfin
  have hs := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ hH).1
  haveI : CharZero (FractionRing R) := (RingHom.charZero_iff (IsFractionRing.injective R _)).1 inferInstance
  have hu : IsUnit (k : Γ(Sp (FractionRing R), ⊤)) :=
    MulEtaleDvr.isUnit_natCast_sections (Nat.cast_ne_zero.mpr (by omega)).isUnit
  have het : Etale (pullback.snd (torsion Gt k).hom (jK R)) := GlobalTheory.LamF.etale_pullback_torsion (jK R) Gt hu
  obtain ⟨J, hJ⟩ := exists_mulEquiv P.U.toUnifPre hL.globalFns hΦ
  have hN := isAdicColimit_of_isFinite hc (torsion Gt k)
  refine ⟨torsion Gt k, Φ _ (torsion.ι Gt k), J _ hN (torsion.ι Gt k), hf, hl, het,
    (tors_iff hΦ k _).2 (torsionι_pow Gt k), fun T g hg => ?_, ?_,
    (formalEq_iff _ _ _).2 ((hJ _ hN _ _).1 rfl)⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← map_pow, torsionι_pow, map_one]

end GlobalTheory.FlatTors
end

