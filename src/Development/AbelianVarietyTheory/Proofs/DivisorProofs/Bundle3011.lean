module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2962
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2988
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2995
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2984
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoFamThrough
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartTrait

theorem exists_cdvr_through {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [IsLocallyNoetherian S] (x : S) (hx : x ∉ Set.range j) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ S) (y₀ : Sp (FractionRing W) ⟶ U),
      y₀ ≫ j = jK W ≫ a ∧ a (closedPoint W) = x := by
  have : IsDominant j := ⟨hd⟩
  let O := S.presheaf.stalk x
  obtain ⟨ge, hge, hs⟩ := exists_mem_genericPoints_specializes x
  have hge' := genericPoints_subset_range_of_isDominant j hge
  have h1 : ge ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hs
  obtain ⟨q, rfl⟩ := h1
  have hop : IsOpen (S.fromSpecStalk x ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage (S.fromSpecStalk x).continuous
  obtain ⟨_, ⟨f, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) hge' hop
  have hfm : f ∈ maximalIdeal O := by
    by_contra hn
    have : S.fromSpecStalk x (closedPoint O) ∈ Set.range j :=
      hf (show closedPoint O ∈ PrimeSpectrum.basicOpen f from hn)
    rw [Scheme.fromSpecStalk_closedPoint] at this
    exact hx this
  let Ω := AlgebraicClosure (ResidueField O)
  let φ : O →+* Ω := (algebraMap (ResidueField O) Ω).comp (residue O)
  have : IsLocalHom φ := ⟨fun a ha => by
    by_contra h
    have : residue O a = 0 := (residue_eq_zero_iff a).2 h
    simp [φ, this] at ha⟩
  obtain ⟨W, _, _, _, _, ψ, ιW, hψ, hιW⟩ := GlobalTheory.GeomTrait.exists_dvr (O := O) (Ω := Ω) hfm q.asIdeal q.isPrime hqf φ
  let a : Sp W ⟶ S := Spec.map (CommRingCat.ofHom ψ) ≫ S.fromSpecStalk x
  obtain ⟨y, hy⟩ := GlobalTheory.HomExt.exists_lift_of_range_subset j
    (spMap (algebraMap W (FractionRing W)) ≫ a) (by
      rintro _ ⟨t, rfl⟩
      have : spMap (algebraMap W (FractionRing W)) t = (⊥ : PrimeSpectrum W) := by
        apply PrimeSpectrum.ext
        change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
        rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
        exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
      rw [Scheme.Hom.comp_apply, this]
      exact hf (a := PrimeSpectrum.comap ψ ⊥) hψ)
  have hloc : IsLocalHom ψ := ⟨fun r hr => by
    by_contra h
    have h2 : φ r = ιW (residue W (ψ r)) := by rw [← hιW]; rfl
    have : residue W (ψ r) ≠ 0 := by
      rw [Ne, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff, not_not]; exact hr
    have h3 : φ r ≠ 0 := by rw [h2]; exact (map_ne_zero ιW).2 this
    exact h (isUnit_of_map_unit φ r (IsUnit.mk0 _ h3))⟩
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, a, y, hy, ?_⟩
  change S.fromSpecStalk x (Spec.map (CommRingCat.ofHom ψ) (closedPoint W)) = x
  have : Spec.map (CommRingCat.ofHom ψ) (closedPoint W) = closedPoint O :=
    IsLocalRing.comap_closedPoint ψ
  rw [this, Scheme.fromSpecStalk_closedPoint]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem trait_be_pos (T : UPoinc.UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨i, hi⟩ := IsMonomial.exists_pos (maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases i
  exact hi

theorem trait_finrank_le {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R]
    {y : Sp (FractionRing R) ⟶ Xo.XF c} {t : SAB H (Sp R)} (hg : UPoinc.GenOf Xo c y t) (P : PELUnif (maximalIdeal R) t) :
    Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q := by
  obtain ⟨tK, ⟨m⟩, ⟨m'⟩⟩ := hg
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let x' : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hx : x' ≫ jK R = spMap f := by
    rw [← GlobalTheory.TorRef.DomFine.spMap_comp']
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((x' ≫ y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K (x' ≫ y ≫ pullback.fst _ _) β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (x' ≫ y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m'.cart tK.act Xo.univ.t.act m'.act x' τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m.cart tK.act t.act m.act x' τ N).1 h₅
    rw [hx] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R t P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem bal_diag_eq {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {β : LinearMap.BilinForm ℤ X}
    (hβ : β ∈ balForms (H.bar : 𝓞 E → 𝓞 E) X) (y : X) : β y y = 2 * β (H.w0 • y) y := by
  obtain ⟨h1, h2⟩ := hβ
  have h := h2 H.w0 y y
  rw [GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator, sub_smul, one_smul, map_sub, h1 y (H.w0 • y)] at h
  linarith

theorem spMap_sq {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] (f : A →+* B) (g : A →+* C)
    (f' : B →+* D) (g' : C →+* D) (h : ∀ a, f' (f a) = g' (g a)) : spMap f' ≫ spMap f = spMap g' ≫ spMap g := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  exact h a

theorem spMap_comp_ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem exists_monoFam_through : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpol hnsi Z zs i OZ N d J S π j _ BD hU hsep x hx
  obtain ⟨⟨-, -, -, -, hizs, -, -⟩, -, -, -, ⟨-, hproj, -, hdense, hjπ, -, -, -⟩, -⟩ := hU
  haveI : LocallyOfFiniteType (π ≫ zs) := _root_.GlobalTheory.isProjOver_locallyOfFiniteType c.F S (π ≫ zs) hproj
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  obtain ⟨W, _, _, _, _, a, y₀, hy₀, hax⟩ := exists_cdvr_through j hdense x hx
  let b₀ : c.F →+* W := (Spec.preimage (a ≫ π ≫ zs)).hom
  have hb₀ : spMap b₀ = a ≫ π ≫ zs := Spec.map_preimage _
  haveI : CharZero W := charZero_of_injective_ringHom b₀.injective
  have hW : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨T, f₁, fK₁, -, hloc₁, -, hc₁, hTy⟩ := _root_.GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c W hW inferInstance y₀

  haveI := hloc₁
  obtain ⟨_, _, _⟩ := T.cdvr
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) T.P.D.toPre.X
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  have hpolT : IsPolFanOn (H.bar : 𝓞 E → 𝓞 E) φ T.P.D.toPre.X := hpol _ (trait_finrank_le T.gen T.P)
  have hbal : T.be ∈ balForms (H.bar : 𝓞 E → 𝓞 E) T.P.D.toPre.X :=
    (balForms_eq_levelForms H T.P.D.toPre.X).symm ▸ T.lev
  obtain ⟨r, gm, k, cc, hgm, hk, hcc, hsum⟩ := GlobalTheory.Poinc.Cover.exists_cone (𝓞 E) (H.bar : 𝓞 E → 𝓞 E) φ
    T.P.D.toPre.X hpolT T.be hbal (fun y hy => trait_be_pos T hy)
  have hM : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  obtain ⟨T₂, g, gK, e, q, -, hgloc, hgK, hT₂y, hq, hbe⟩ := _root_.GlobalTheory.UPoinc.uTrait_ramExt T (k * l.M') (Nat.mul_pos hk hM)
  haveI := hgloc
  obtain ⟨_, _, _⟩ := T₂.cdvr

  have hW₁ : spMap fK₁ ≫ jK W = jK T.V ≫ spMap f₁ := spMap_sq (algebraMap W _) f₁ fK₁ (algebraMap T.V _) hc₁
  have hT₁ : spMap gK ≫ jK T.V = jK T₂.V ≫ spMap g := spMap_sq (algebraMap T.V _) g gK (algebraMap T₂.V _) hgK
  have hy0s : y₀ ≫ pullback.snd _ _ = jK W ≫ spMap b₀ := by
    rw [hb₀, ← hizs, ← hjπ]
    simp only [Category.assoc]
    rw [reassoc_of% hy₀]
  let bb : c.F →+* T₂.V := g.comp (f₁.comp b₀)
  have hover : T₂.y ≫ pullback.snd _ _ = jK T₂.V ≫ spMap bb := by
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy0s, reassoc_of% hW₁, reassoc_of% hT₁]
    simp only [bb, spMap_comp_, Category.assoc]
  have hev : ∀ i z, gm i z z = 2 * gm i (H.w0 • z) z := fun i z => bal_diag_eq (hgm.mem i) z
  have hnn : ∀ i z, 0 ≤ gm i (H.w0 • z) z := fun i z => by
    have := hgm.nonneg i z
    rw [hev] at this
    omega
  have hsumz : ∀ z, (k : ℤ) * T.be z z = ∑ i, (cc i : ℤ) * gm i z z := fun z => by
    have := congrArg (fun β : LinearMap.BilinForm ℤ T.P.D.toPre.X => β z z) hsum
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using this
  have hmono : IsMonomial T₂.P.D.toPre (fun i => T₂.ϖ ^ (q * cc i))
      (fun i => (l.M' : ℤ) • pull e.symm.toLinearMap (gm i)) := by
    intro y
    obtain ⟨u, n₀, hn₀, hψ⟩ := T₂.mono y
    have hy : y = e (e.symm y) := (e.apply_symm_apply y).symm
    set z := e.symm y
    refine ⟨u, fun i => (l.M' * gm i (H.w0 • z) z).toNat, fun i => ?_, ?_⟩
    · simp only [LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, smul_eq_mul]
      rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z)), hev]
      ring
    · convert hψ using 2
      rw [Fin.prod_univ_one]
      simp only [Matrix.cons_val_zero, ← pow_mul, Finset.prod_pow_eq_pow_sum]
      congr 1
      have h0 : T₂.be y y = 2 * n₀ 0 := by simpa using hn₀ 0
      rw [hy, hbe] at h0
      have hz := hsumz z
      have hcast : ((∑ i, q * cc i * (l.M' * gm i (H.w0 • z) z).toNat : ℕ) : ℤ) =
          ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Int.toNat_of_nonneg (mul_nonneg (by positivity) (hnn i z))]
      have hz2 : (k : ℤ) * T.be z z = 2 * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [hz, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hev]
        ring
      have hS : ∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z) =
          (q * l.M') * ∑ i, (cc i : ℤ) * gm i (H.w0 • z) z := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      have h2 : (2 : ℤ) * (∑ i, (q : ℤ) * cc i * (l.M' * gm i (H.w0 • z) z)) = 2 * (n₀ 0 : ℤ) := by
        rw [← h0, hS]
        push_cast
        linear_combination (-((q : ℤ) * l.M')) * hz2
      have h3 := mul_left_cancel₀ (two_ne_zero) h2
      exact_mod_cast hcast.trans h3
  let C : MonoFam Xo c φ T₂.V :=
    { b := bb, t := T₂.t, P := T₂.P, y := T₂.y, y_over := hover, gen := T₂.gen, m := r,
      s := fun i => T₂.ϖ ^ (q * cc i),
      s_mem := fun i => Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 T₂.irr.not_isUnit) _
        (Nat.mul_pos hq (hcc i)),
      δ := fun i => pull e.symm.toLinearMap (gm i), cone := hgm.pull_equiv e.symm,
      rank := trait_finrank_le T₂.gen T₂.P, mono := hmono }
  have hcomp : C.y ≫ j = jK T₂.V ≫ (spMap (g.comp f₁) ≫ a) := by
    show T₂.y ≫ j = _
    rw [hT₂y, hTy]
    simp only [Category.assoc]
    rw [hy₀, reassoc_of% hW₁, reassoc_of% hT₁, spMap_comp_]
    simp only [Category.assoc]
  have hcl : (spMap (g.comp f₁) ≫ a) (closedPoint T₂.V) = x := by
    have h1 : spMap (g.comp f₁) (closedPoint T₂.V) = closedPoint W := IsLocalRing.comap_closedPoint (g.comp f₁)
    change a (spMap (g.comp f₁) (closedPoint T₂.V)) = x
    rw [h1, hax]
  exact ⟨T₂.V, inferInstance, inferInstance, inferInstance, C, spMap (g.comp f₁) ≫ a,
    ⟨⟨inferInstance, inferInstance, inferInstance, ‹_›⟩, ‹_›⟩, hcomp, hcl⟩

end GlobalTheory.UChartTrait
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedBlowupFiniteNormalCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USepCov

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c), ∀ (J : C.Z.IdealSheafData), (∀ x ∈ J.support, x ∉ Set.range C.i) → ∀ (S : Scheme.{0}) (π : S ⟶ pullback C.z (spMap C.b)), IsNormBl π (J.comap (pullback.fst C.z (spMap C.b))) → ∀ (M : Scheme.{0}) [IsIntegral M] (g : M ⟶ C.Z) (z₁ : M) (ζ : Sp (M.presheaf.stalk z₁) ⟶ pullback C.z (spMap C.b)), IsCov C g z₁ ζ → ∃ (S₁ : Scheme.{0}) (_ : IsIntegral S₁) (p₁ : S₁ ⟶ M) (sM : M ⟶ Sp ℤ) (U₁ : S₁.Opens), LocallyOfFiniteType sM ∧ QuasiCompact sM ∧ Flat (p₁ ≫ sM) ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S₁ ∧ IsProper p₁ ∧ IsDominant p₁ ∧ FinalTheorems.EffCartier (J.comap (p₁ ≫ g)) ∧ (U₁ : Set S₁).Nonempty ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S₁) (ev : M.presheaf.stalk z₁ →+* K), x ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ → Set.range x ⊆ (U₁ : Set S₁) → ∃ y : Sp K ⟶ Xo.XF c, y ≫ C.iF = spMap ev ≫ ζ) ∧ ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ S) (ev : M.presheaf.stalk z₁ →+* R), a ≫ π = spMap ev ≫ ζ → Set.range (jK R ≫ a ≫ π) ⊆ Set.range C.iF → ∃ ξ₁ : Sp R ⟶ S₁, ξ₁ ≫ p₁ = spMap ev ≫ M.fromSpecStalk z₁ ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (ev' : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ p, (spMap ev' ≫ a) p = a (closedPoint R)) → GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ a) → (∀ p, (spMap ev' ≫ ξ₁) p = ξ₁ (closedPoint R)) ∧ GlobalTheory.UChart.DefOver k₀ (spMap ev' ≫ ξ₁) := by
  intro E _ _ _ H Dw _ l Xo c C J hJi S π hNB M _ g z₁ ζ hcov
  obtain ⟨hMn, ⟨U, g', hg'fin, hg'U, hUF⟩, hζ, hgen⟩ := hcov
  haveI := hg'fin
  haveI := C.ft
  haveI : Algebra.FiniteType ℤ (CommRingCat.of C.o) := ‹Algebra.FiniteType ℤ C.o›
  haveI : IsNoetherianRing C.o := Algebra.FiniteType.isNoetherianRing ℤ _
  haveI := C.iF_open
  obtain ⟨Z', b, hB, hBproj, -⟩ := GlobalTheory.ProjBlowup.exists_blowup C.z C.proj J
  haveI : IsProper C.z := by
    obtain ⟨m, e, he, he'⟩ := C.proj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper (b ≫ C.z) := by
    obtain ⟨m, e, he, he'⟩ := hBproj
    haveI := he
    have := isProper_str C.o m
    rw [← he']
    infer_instance
  haveI : IsProper b := IsProper.of_comp b C.z
  obtain ⟨-, S₀, π₀, ν, -, hB₀, hνπ, -, -, -, -⟩ := hNB
  obtain ⟨ψ₀, hψ₀, -⟩ := hB.2 S₀ (π₀ ≫ pullback.fst C.z (spMap C.b))
    (by rw [Scheme.IdealSheafData.comap_comp]; exact hB₀.1)
  have hψU : Set.range ψ₀ ⊆ Set.range (b ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨s, rfl⟩
    show b (ψ₀ s) ∈ U
    rw [← Scheme.Hom.comp_apply, hψ₀, Scheme.Hom.comp_apply]
    exact hUF ⟨_, rfl⟩
  let ψU : S₀ ⟶ (b ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (b ⁻¹ᵁ U).ι ψ₀ hψU
  have hψUf : ψU ≫ (b ⁻¹ᵁ U).ι = ψ₀ := IsOpenImmersion.lift_fac _ _ _
  have hψUb : ψU ≫ (b ∣_ U) ≫ U.ι = π₀ ≫ pullback.fst C.z (spMap C.b) := by
    rw [morphismRestrict_ι, ← Category.assoc, hψUf, hψ₀]
  have hpt : ∀ q : Sp (M.presheaf.stalk z₁), g (M.fromSpecStalk z₁ q) = pullback.fst C.z (spMap C.b) (ζ q) := by
    intro q
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hζ]
  haveI := hMn
  haveI : IsDomain (M.presheaf.stalk z₁) := inferInstance
  let p0 : Sp (M.presheaf.stalk z₁) := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨y0, hy0⟩ := hgen p0 rfl
  let m0 : M := M.fromSpecStalk z₁ p0
  have hm0 : g m0 = C.i y0 := by
    rw [hpt, ← hy0]; rfl
  have hgm : ∀ m, g m ∈ Set.range C.i → (g' ≫ U.ι) m ∉ J.support := by
    intro m ⟨y, hy⟩ hJ
    rw [hg'U] at hJ
    exact hJi _ hJ ⟨y, hy⟩
  have hm0J : (g' ≫ U.ι) m0 ∉ J.support := hgm m0 ⟨y0, hm0.symm⟩
  obtain ⟨S₁, hS₁i, p₁, ν₁, hS₁n, hp₁P, hν₁fin, hcomm, hEff, hrange, hlift⟩ :=
    _root_.GlobalTheory.USep.exists_normalisation_pullback_cover (o := CommRingCat.of C.o) C.z b J hB U g' ⟨m0, hm0J⟩
  haveI := hν₁fin

  haveI : IsPreimmersion (spMap C.b) := by
    letI := C.b.toAlgebra
    haveI := C.isFractionRing
    exact IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  obtain ⟨W', hW'o, hW'⟩ := ((IsPreimmersion.isEmbedding (pullback.fst C.z (spMap C.b))).isInducing.isOpen_iff).mp
    C.iF.isOpenMap.isOpen_range
  let sM : M ⟶ Sp ℤ := g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))
  obtain ⟨x0, hx0⟩ := hrange m0 hm0J
  haveI hSpecZ : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine ⟨S₁, hS₁i, p₁, sM, (p₁ ≫ g) ⁻¹ᵁ ⟨W', hW'o⟩, ?_, ?_, ?_, hS₁n, hp₁P, ?_, ?_, ?_, ?_, ?_⟩
  · show LocallyOfFiniteType (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · show QuasiCompact (g ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    haveI : IsLocallyNoetherian C.Z := LocallyOfFiniteType.isLocallyNoetherian (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)))
    rw [← hg'U]
    infer_instance
  · apply _root_.GlobalTheory.IntFlat.flat_of_generic_zero _ x0
    have eM : C.i ≫ C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o)) =
        (C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) := by
      simp only [UCompact.i, Category.assoc, pullback.condition_assoc]
      rw [← Spec.map_comp]; rfl
    have e : (p₁ ≫ sM) x0 = Spec.map (CommRingCat.ofHom (C.b.comp (algebraMap ℤ C.o))) ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0) := by
      rw [← Scheme.Hom.comp_apply, ← eM]
      show (C.z ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ C.o))) (g (p₁ x0)) = _
      rw [hx0, hm0]
      rfl
    rw [e]
    show Ideal.comap _ _ = ⊥
    haveI := ((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).isPrime
    rw [Ideal.eq_bot_of_prime (((C.iF ≫ pullback.snd C.z (spMap C.b)) y0).asIdeal), Ideal.comap_bot_of_injective]
    exact fun u v h => Int.cast_injective (α := c.F) (by simpa using h)
  · constructor
    have hVo : IsOpen {m : M | (g' ≫ U.ι) m ∉ J.support} :=
      (g' ≫ U.ι).continuous.isOpen_preimage _ J.support.isClosed.isOpen_compl
    exact (hVo.dense ⟨m0, hm0J⟩).mono fun m hm => hrange m hm
  · rw [← hg'U]; exact hEff
  · refine ⟨x0, ?_⟩
    show g (p₁ x0) ∈ W'
    rw [hx0, hpt]
    show ζ p0 ∈ pullback.fst C.z (spMap C.b) ⁻¹' W'
    rw [hW']; exact ⟨y0, hy0⟩
  · intro K _ x ev hx hxU
    have hr : Set.range (spMap ev ≫ ζ) ⊆ Set.range C.iF := by
      rintro _ ⟨w, rfl⟩
      rw [← hW']
      show pullback.fst C.z (spMap C.b) (ζ (spMap ev w)) ∈ W'
      rw [← hpt, ← Scheme.Hom.comp_apply (spMap ev), ← hx, Scheme.Hom.comp_apply]
      exact hxU ⟨w, rfl⟩
    exact ⟨IsOpenImmersion.lift C.iF _ hr, IsOpenImmersion.lift_fac _ _ _⟩
  · intro R _ _ _ _ a ev ha hgR
    let β : Sp R ⟶ M := spMap ev ≫ M.fromSpecStalk z₁
    have hβg : β ≫ g = a ≫ π ≫ pullback.fst C.z (spMap C.b) := by
      simp only [β, Category.assoc, ← hζ]
      rw [← Category.assoc a π, ha, Category.assoc]
    have hab : (a ≫ ν ≫ ψU) ≫ (b ∣_ U) = β ≫ g' := by
      rw [← cancel_mono U.ι, Category.assoc, Category.assoc, Category.assoc, hψUb, Category.assoc, hg'U, hβg,
        ← hνπ, Category.assoc]
    have hgw : ∀ w, (jK R ≫ β ≫ g' ≫ U.ι) w ∉ J.support := by
      intro w
      have e : jK R ≫ β ≫ g' ≫ U.ι = (jK R ≫ a ≫ π) ≫ pullback.fst C.z (spMap C.b) := by
        rw [hg'U, hβg]; simp only [Category.assoc]
      rw [e]
      obtain ⟨y, hy⟩ := hgR ⟨w, rfl⟩
      intro hJ
      refine hJi _ hJ ⟨y, ?_⟩
      show _ = pullback.fst C.z (spMap C.b) ((jK R ≫ a ≫ π) w)
      rw [← hy]; rfl
    obtain ⟨ξ₁, hξν, hξp⟩ := hlift R (a ≫ ν ≫ ψU) β hab hgw
    refine ⟨ξ₁, hξp, ?_⟩
    intro K _ _ ev' k₀ hk₀ hcl hdef
    refine ⟨fun p => ?_, ?_⟩
    · have e1 : ∀ t, ν₁ (ξ₁ t) = ψU (ν (a t)) := fun t => by
        rw [← Scheme.Hom.comp_apply, hξν]; rfl
      apply _root_.GlobalTheory.eq_of_specializes_of_isIntegralHom ν₁
      · exact (IsLocalRing.specializes_closedPoint _).map ξ₁.continuous
      · have e2 := e1 (closedPoint R)
        have e3 : a ((spMap ev') p) = a (closedPoint R) := hcl p
        rw [Scheme.Hom.comp_apply, e1, e3]
        exact e2.symm
    · apply _root_.GlobalTheory.DefOverIntegral.defOver_of_isIntegralHom ν₁ k₀ hk₀
      obtain ⟨P₀, hP₀⟩ := hdef
      refine ⟨P₀ ≫ ν ≫ ψU, ?_⟩
      simp only [Category.assoc, hξν]
      rw [reassoc_of% hP₀]

end GlobalTheory.USepCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSectionNonvanishingClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem spMap_eq_closedPoint_iff {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (ρ : R →+* R') (hρ : ρ.Finite) (y : Sp R') : spMap ρ y = closedPoint R ↔ y = closedPoint R' := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hρ
  haveI : Algebra.IsIntegral R R' := inferInstance
  constructor
  · intro h
    have hc : (y.asIdeal.comap (algebraMap R R')).IsMaximal := by
      have : (spMap ρ y).asIdeal = y.asIdeal.comap ρ := rfl
      rw [h] at this
      change (y.asIdeal.comap ρ).IsMaximal
      rw [← this]; exact IsLocalRing.maximalIdeal.isMaximal R
    haveI : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (y : PrimeSpectrum R')
    have hm : y.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under y.asIdeal hc
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hm)
  · rintro rfl
    have hc : ((maximalIdeal R').comap (algebraMap R R')).IsMaximal :=
      Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal R')
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hc)

theorem exists_open_secNz_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ θ : U'.LG.L.Sec, (∃ g' : G'.left, G'.hom g' = closedPoint R' ∧ g' ∈ secNz θ) → ∃ O : G.left.Opens, (∃ g ∈ O, G.hom g = closedPoint R) ∧ ∀ g' : G'.left, β g' ∈ O → G.hom (β g') = closedPoint R → g' ∈ secNz θ := by
  intro R _ _ _ hB R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hact θ ⟨g0, hg0c, hg0⟩
  have hfin : IsFinite (spMap ρ) := by rw [IsFinite.SpecMap_iff]; exact hF.2.2
  haveI hβfin : IsFinite β := MorphismProperty.of_isPullback hβ.1.flip hfin
  have hcl : IsClosedMap β := β.isClosedMap
  have hsq : ∀ g' : G'.left, G.hom (β g') = spMap ρ (G'.hom g') := fun g' => by
    change (β ≫ G.hom) g' = (G'.hom ≫ spMap ρ) g'
    rw [hβ.1.w]

  obtain ⟨s, hs⟩ : ∃ s : (Sp R' : Scheme.{0}), s = closedPoint R' := ⟨_, rfl⟩
  rw [← hs] at hg0c
  haveI hirr : IrreducibleSpace (G'.hom.fiber s) :=
    GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G' hS' _ ((Sp R').fromSpecResidueField s)
  obtain ⟨η', hη'⟩ : ∃ η' : G'.left, η' = G'.hom.fiberι s (genericPoint (G'.hom.fiber s)) := ⟨_, rfl⟩
  have hspec : ∀ g' : G'.left, G'.hom g' = s → η' ⤳ g' := by
    intro g' hg'
    obtain ⟨z, hz⟩ : g' ∈ Set.range (G'.hom.fiberι s) := (Scheme.Hom.range_fiberι G'.hom s).ge hg'
    rw [← hz, hη']
    exact ((genericPoint_spec (G'.hom.fiber s)).specializes trivial).map (G'.hom.fiberι s).continuous
  have hηs : G'.hom η' = s := by
    rw [hη']; exact (Scheme.Hom.range_fiberι G'.hom s).le ⟨_, rfl⟩
  have hηnz : η' ∈ secNz θ := (hspec g0 hg0c).mem_open (secNz θ).isOpen hg0
  refine ⟨⟨farSet β θ, isOpen_farSet β hcl θ⟩, ⟨β η', ?_, ?_⟩, ?_⟩
  · show ∀ g', β g' = β η' → g' ∈ secNz θ
    intro g' hg'
    have hg's : G'.hom g' = s := by
      rw [hs, ← spMap_eq_closedPoint_iff ρ hF.2.2, ← hsq, hg', hsq, hηs]
      exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
    have := GlobalTheory.eq_of_specializes_of_isIntegralHom β (hspec g' hg's) hg'.symm
    rw [← this]; exact hηnz
  · rw [hsq, hηs]; exact (spMap_eq_closedPoint_iff ρ hF.2.2 s).2 hs
  · intro g' hg' _
    exact hg' g' rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivialStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (exact GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (intros; apply GlobalTheory.ZarhinFam.zarhin_kernel_trivial  <;> assumption)
end

