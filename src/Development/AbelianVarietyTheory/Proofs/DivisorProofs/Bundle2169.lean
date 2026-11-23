module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveRat
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open scoped UpperHalfPlane

namespace GlobalTheory.IdealTheta

theorem exists_primitive_rat {K : Type} [Field K] [CharZero K] (a₁ a₂ : K) (r s : ℚ)
    (h : (r : K) * a₁ + (s : K) * a₂ = 1) :
    ∃ (c : ℚ) (p q u v : ℤ), 0 < c ∧ p * v - q * u = 1 ∧ (p : K) * a₁ + (q : K) * a₂ = (c : K) := by
  set A : ℤ := r.num * s.den with hA
  set B : ℤ := s.num * r.den with hB
  have hr : (r : K) * (r.den : K) = (r.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num r)
    push_cast at this; exact this
  have hs : (s : K) * (s.den : K) = (s.num : K) := by
    have := congrArg (fun t : ℚ => (t : K)) (Rat.mul_den_eq_num s)
    push_cast at this; exact this
  have hAB : (A : K) * a₁ + (B : K) * a₂ = (r.den : K) * (s.den : K) := by
    rw [hA, hB]; push_cast
    rw [← hr, ← hs]
    linear_combination ((r.den : K) * (s.den : K)) * h
  have hN : (r.den : K) * (s.den : K) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr r.den_nz) (Nat.cast_ne_zero.mpr s.den_nz)
  have hg : Int.gcd A B ≠ 0 := by
    intro h0
    rw [Int.gcd_eq_zero_iff] at h0
    rw [h0.1, h0.2] at hAB
    apply hN
    rw [← hAB]; simp
  obtain ⟨p, hp⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ A := Int.gcd_dvd_left A B
  obtain ⟨q, hq⟩ : ((Int.gcd A B : ℕ) : ℤ) ∣ B := Int.gcd_dvd_right A B
  have hbez := Int.gcd_eq_gcd_ab A B
  set g : ℕ := Int.gcd A B with hgdef
  have hgZ : (g : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  have hgK : (g : K) ≠ 0 := Nat.cast_ne_zero.mpr hg
  refine ⟨((r.den : ℚ) * (s.den : ℚ)) / (g : ℚ), p, q, -Int.gcdB A B, Int.gcdA A B, ?_, ?_, ?_⟩
  · have h1 : (0 : ℚ) < r.den := Nat.cast_pos.mpr r.den_pos
    have h2 : (0 : ℚ) < s.den := Nat.cast_pos.mpr s.den_pos
    have h3 : (0 : ℚ) < g := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg)
    positivity
  · apply mul_left_cancel₀ hgZ
    linear_combination -hbez - Int.gcdA A B * hp - Int.gcdB A B * hq
  · have hpK : (A : K) = (g : K) * (p : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hp
    have hqK : (B : K) = (g : K) * (q : K) := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hq
    push_cast
    rw [eq_div_iff hgK, ← hAB, hpK, hqK]
    ring

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) → 𝔞 ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → ∃ (c : ℚ) (θ : K) (τ : ℍ), 0 < c ∧ ι θ = (τ : ℂ) ∧ IsTauOf Λ (c : ℂ) τ ∧ ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
  intro K _ _ d δ ι 𝔞 Λ hK _ _ _ hΛ
  obtain ⟨c₀, τ₀, hc₀, hlat⟩ := latTau Λ
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice ↔ ∃ y : K, y ∈ 𝔞 ∧ ι y = z := by
    intro z
    have : z ∈ (Λ.lattice : Set ℂ) ↔ z ∈ ι '' (𝔞 : Set K) := by rw [hΛ]
    exact this
  obtain ⟨a₁, -, ha₁⟩ := (hmem (c₀ * τ₀)).mp ((hlat _).mpr ⟨1, 0, by simp⟩)
  obtain ⟨a₂, -, ha₂⟩ := (hmem c₀).mp ((hlat _).mpr ⟨0, 1, by simp⟩)
  have hA : ∀ x : K, x ∈ 𝔞 ↔ ∃ m n : ℤ, x = (m : K) * a₁ + (n : K) * a₂ := by
    intro x
    have h1 : x ∈ 𝔞 ↔ ι x ∈ Λ.lattice := by
      rw [hmem]
      exact ⟨fun h => ⟨x, h, rfl⟩, fun ⟨y, hy, e⟩ => ι.injective e ▸ hy⟩
    rw [h1, hlat]
    refine exists_congr fun m => exists_congr fun n => ?_
    rw [← ι.injective.eq_iff]
    simp only [map_add (f := _), map_mul, map_intCast, ha₁, ha₂]
    constructor <;> intro h <;> rw [h] <;> ring
  have hli : LinearIndependent ℚ ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff]
    intro r s h
    rw [Rat.smul_def, Rat.smul_def] at h
    have h1 := congrArg ι h
    simp only [map_add (f := _), map_mul, map_ratCast, ha₁, ha₂, map_zero] at h1
    have h2 : (r : ℂ) * τ₀ + (s : ℂ) = 0 := by
      apply mul_left_cancel₀ hc₀
      linear_combination h1
    have h3 := congrArg Complex.im h2
    have hr : r = 0 := by
      have := τ₀.im_ne_zero
      simpa [this] using h3
    subst hr
    simpa using h2
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
    (show (1 : K) ∈ Submodule.span ℚ (Set.range ![a₁, a₂]) by rw [hspan]; trivial)
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Rat.smul_def] at hw
  obtain ⟨c, p, q, u, v, hc, hdet, hcK⟩ := exists_primitive_rat a₁ a₂ (w 0) (w 1) hw
  have hcK0 : (c : K) ≠ 0 := by exact_mod_cast hc.ne'
  have hcC0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdetK : (p : K) * v - q * u = 1 := by exact_mod_cast congrArg (fun t : ℤ => (t : K)) hdet
  have hdetR : (p : ℝ) * v - q * u = 1 := by exact_mod_cast hdet
  set θ : K := -((u : K) * a₁ + (v : K) * a₂) / (c : K) with hθ
  have hcθ : (c : K) * θ = -((u : K) * a₁ + (v : K) * a₂) := by
    rw [hθ]; field_simp
  have hcC : (c : ℂ) = c₀ * ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcK
    simp only [map_add (f := _), map_mul, map_ratCast, map_intCast, ha₁, ha₂] at h1
    linear_combination -h1
  have hz : ((p : ℂ) * τ₀ + q) ≠ 0 := by
    intro h0; apply hcC0; rw [hcC, h0, mul_zero]
  have hιθ : ι θ = -((u : ℂ) * τ₀ + v) / ((p : ℂ) * τ₀ + q) := by
    have h1 := congrArg ι hcθ
    simp only [map_add (f := _), map_mul, map_neg, map_ratCast, map_intCast, ha₁, ha₂] at h1
    rw [eq_div_iff hz]
    apply mul_left_cancel₀ hc₀
    rw [hcC] at h1
    linear_combination h1
  have him : 0 < (ι θ).im := by
    rw [hιθ, Complex.div_im, ← sub_div]
    refine div_pos ?_ (Complex.normSq_pos.mpr hz)
    have hy : 0 < (τ₀ : ℂ).im := τ₀.im_pos
    simp only [Complex.neg_im, Complex.neg_re, Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
      Complex.intCast_im, Complex.intCast_re]
    have : -(↑u * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) * (↑p * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑q) -
        -(↑u * (τ₀ : ℂ).re - 0 * (τ₀ : ℂ).im + ↑v) * (↑p * (τ₀ : ℂ).im + 0 * (τ₀ : ℂ).re + 0) = (τ₀ : ℂ).im := by
      linear_combination (τ₀ : ℂ).im * hdetR
    rw [this]; exact hy
  have hmain : ∀ x : K, x ∈ 𝔞 ↔ ∃ a b : ℤ, x = (c : K) * ((a : K) * θ + (b : K)) := by
    intro x
    rw [hA]
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * q - n * p, m * v - n * u, ?_⟩
      push_cast
      linear_combination (-((m : K) * q - n * p)) * hcθ + ((m : K) * v - n * u) * hcK
        - ((m : K) * a₁ + (n : K) * a₂) * hdetK
    · rintro ⟨a, b, rfl⟩
      refine ⟨b * p - a * u, b * q - a * v, ?_⟩
      push_cast
      linear_combination (a : K) * hcθ - (b : K) * hcK
  refine ⟨c, θ, ⟨ι θ, him⟩, hc, rfl, ⟨hcC0, fun z => ?_⟩, hmain⟩
  rw [hmem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, b, rfl⟩ := (hmain y).mp hy
    exact ⟨a, b, by simp⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨_, (hmain _).mpr ⟨a, b, rfl⟩, by simp⟩

end GlobalTheory.IdealTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveAlgebraisationFormalEmbeddingCom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

noncomputable section

theorem GlobalTheory.FormalAlg.exists_projective_of_formal_embedding : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (H e) ((H (e + 1)).pull (β e))), (∀ e, (H e).IsLB ∧ (v e).IsGen) → ∀ (n : ℕ) (s : ∀ e, Fin (n + 1) → LB.Sec (H e)), (∀ e j, Rel (β e) (v e) (s (e + 1) j) (s e j)) → VeryAmpleBy (Y 0).hom (H 0) (s 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (H' : LB B.left) (s' : Fin (n + 1) → LB.Sec H') (b : ∀ e, (Y e).left ⟶ B.left) (w : ∀ e, LB.Iso (H e) (H'.pull (b e))), H'.IsLB ∧ VeryAmpleBy B.hom H' s' ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ (∀ e, (w e).IsGen ∧ ∀ j, Rel (b e) (w e) (s' j) (s e j)) ∧ ∀ (t : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous t → (∀ e, F ∈ vanIdeal ((Y e).hom ≫ thick R I e) (s e)) → F ∈ vanIdeal B.hom s' := by
  intro V _ _ I hc Y β hβ H v hH n s hs hva
  have hVA : ∀ e, VeryAmpleBy (Y e).hom (H e) (s e) := by
    rintro (_ | e)
    · exact hva
    · obtain ⟨j₀, hj, w, hw, hr⟩ := tower _ Y β hβ H v hH s hs e
      exact GlobalTheory.AbLaw.veryAmpleBy_of_isNilpotent _ _ _ (Ideal.Quotient.factor_surjective _)
        (GlobalTheory.Degen.isNilpotent_ker_factor_pow I _)
        _ _ _ _ j₀ hj _ _ w n _ _ (hH _).1 (hH _).1 ((isGen_iff _).2 hw) hr hva
  have c₁ : ∀ e, β e ≫ (Y (e + 1)).hom ≫ thick V I (e + 1) = (Y e).hom ≫ thick V I e := fun e => by
    rw [← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  let K : ℕ → Ideal (MvPolynomial (Fin (n + 1)) V) := fun e => vanIdeal ((Y e).hom ≫ thick V I e) (s e)
  let S : Set (MvPolynomial (Fin (n + 1)) V) := {F | (∃ t, F.IsHomogeneous t) ∧ ∀ e, F ∈ K e}
  have hS : ∀ e, Ideal.span S ≤ K e := fun e => Ideal.span_le.2 fun F hF => hF.2 e
  obtain ⟨B, f, H', s', hH', hva', hB⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n (Ideal.span S)
    (component_mem_span S fun F hF => hF.1)
  have hB' : ∀ t (F : MvPolynomial (Fin (n + 1)) V), F.IsHomogeneous t → (∀ e, F ∈ K e) → ∀ k : H'.ι,
      MvPolynomial.eval₂Hom (cst f (H'.U k)) (fun j => (s' j).f k) F = 0 := fun t F hF h =>
    (hB t F hF).2 fun i => ⟨0, by rw [pow_zero, _root_.one_mul]; exact Ideal.subset_span ⟨⟨t, hF⟩, h⟩⟩
  choose b w hb hw hr using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V B f H' n s' hH' hva' _
    ((Y e).hom ≫ thick V I e) (H e) (s e) (hH e).1 (hVA e).1 (fun t F hF h =>
      (mem_vanIdeal _ _ _).1 (mem_vanIdeal_of_sat _ _ (hVA e).1 fun i =>
        ((hB t F hF).1 h i).imp fun _ hm => hS e hm))
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.FormalAlg.exists_homogeneous_correction_succ V I Y β hβ H v hH n s hs hva
  refine ⟨Over.mk f, H', s', b, w, hH', hva', fun e => ?_, fun e => ?_, fun e => ⟨hw e, hr e⟩,
    fun t F hF h => (mem_vanIdeal _ _ _).2 (hB' t F hF h)⟩
  · refine GlobalTheory.ProjBaseChange.isPullback_of_equations_lift V B f H' n s' hH' hva' _ _ Ideal.Quotient.mk_surjective
      _ (Y e).hom (H e) (s e) (b e) (w e) (hH e).1 (hVA e) (hb e) (hw e) (hr e) t₀ fun t ht F hF h => ?_
    obtain ⟨F₁, hF₁, hK, hG⟩ := GlobalTheory.Degen.exists_form_limit_ideal V I hc _ K t
      (fun e F hF h => by
        have := mem_vanIdeal_pull (hH (e + 1)).1 (hs e) _ hF h
        rwa [c₁] at this)
      (fun e a ha => (mem_vanIdeal _ _ _).2 fun k => by
        rw [MvPolynomial.eval₂Hom_C, cst_comp_spec, RingHom.comp_apply,
          Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero])
      (fun e F hF h => ht₀ t ht e F hF h) e F hF ((mem_vanIdeal _ _ _).2 h)
    refine ⟨F₁, hF₁, hB' t F₁ hF₁ hK, ?_⟩
    rw [eq_comm, ← sub_eq_zero, ← map_sub]
    ext d
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hG d)
  · have hv := (isGen_iff _).1 (hH e).2
    have hw' := (isGen_iff _).1 (hw (e + 1))
    obtain ⟨w'', T⟩ := exists_comp (hH (e + 1)).1 (w (e + 1)) (v e) hw' hv hH' (hH e).1
    exact GlobalTheory.MapUniq.hom_eq_of_pull_sections V B f H' n s' hH' hva' _ (H e) (s e) _ _ w'' (w e) (hH e).1
      (by rw [Category.assoc, hb, hb, c₁]) ((isGen_iff _).2 (T.pgen_comp (hH (e + 1)).1 hw' hv)) (hw e)
      (fun j => Rel.comp T (hH (e + 1)).1 (hr (e + 1) j) (hs e j)) (hr e)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGroupOLinearTorsionLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.UPel.HT.LevPull

theorem exists_pull_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (N : ℕ) (H : Scheme.{0}) (AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (Y : Over H) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → (∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c) → (∀ x, u (N • x) = 1) → ∃ (AE : Over Y.left) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ AH.left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE)), IsGrpPullback AE AH Y.hom φE ∧ (∀ a : D.O, (actE.act a).left ≫ φE = φE ≫ (actH.act a).left) ∧ EtaOK D N actE ηE ∧ ∀ y, (ηE y).left ≫ φE = (u y).left := by
  intro p _ D N H AH _ _ actH Y u hadd hlin htor
  let AE : Over Y.left := (Over.pullback Y.hom).obj AH
  letI iG : GrpObj AE := Functor.grpObjObj
  letI iC : IsCommMonObj AE := Functor.isCommMonObj_obj
  let φE : AE.left ⟶ AH.left := pullback.fst AH.hom Y.hom
  have hg : IsGrpPullback AE AH Y.hom φE := isGrpPullback_pullback AH Y.hom
  have inj : ∀ {T : Over Y.left} {x y : T ⟶ AE}, x.left ≫ φE = y.left ≫ φE → x = y := fun {T x y} h =>
    Over.OverMorphism.ext (hg.1.hom_ext h (by rw [Over.w, Over.w]))
  have pm : ∀ {T : Over Y.left} (x y : T ⟶ AE), (x * y).left ≫ φE = (pushPt hg.1.w x * pushPt hg.1.w y).left :=
    fun x y => (hg.2 _ x y _ _ rfl rfl).symm

  let act' : D.O → (AE ⟶ AE) := fun a => Over.homMk (hg.1.lift (φE ≫ (actH.act a).left) AE.hom
    (by rw [Category.assoc, Over.w, hg.1.w])) (hg.1.lift_snd _ _ _)
  have ha : ∀ a, (act' a).left ≫ φE = φE ≫ (actH.act a).left := fun a => hg.1.lift_fst _ _ _
  have pa : ∀ {T : Over Y.left} (x : T ⟶ AE) a, pushPt hg.1.w (x ≫ act' a) = pushPt hg.1.w x ≫ actH.act a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, ha, Category.assoc])
  have injP : ∀ {T : Over Y.left} {x y : T ⟶ AE}, pushPt hg.1.w x = pushPt hg.1.w y → x = y := fun h =>
    inj (congrArg (fun q => q.left) h)
  have pm' : ∀ {T : Over Y.left} (x y : T ⟶ AE), pushPt hg.1.w (x * y) = pushPt hg.1.w x * pushPt hg.1.w y :=
    fun x y => map_mul (pushHom hg _) x y
  let actE : OActN D.O AE :=
    { act := act'
      hom := fun a => isMonHom_of_mul _ fun T x y => injP (by
        have := actH.hom a
        rw [pa, pm', pm', pa, pa, MonObj.mul_comp])
      one := injP (by rw [← Category.id_comp (act' 1), pa, actH.one, Category.comp_id])
      mul := fun a b => injP (by
        rw [← Category.id_comp (act' (a * b)), pa, pa, actH.mul, ← Category.id_comp (act' b), pa, Category.assoc])
      add := fun a b => injP (by
        refine Eq.trans ?_ (pm' (act' a) (act' b)).symm
        rw [← Category.id_comp (act' (a + b)), ← Category.id_comp (act' a), ← Category.id_comp (act' b), pa, pa, pa,
          actH.add]
        exact MonObj.comp_mul _ _ _) }

  let ηE : D.La → (𝟙_ (Over Y.left) ⟶ AE) := fun y =>
    Over.homMk (hg.1.lift (u y).left (𝟙_ (Over Y.left)).hom (by rw [Over.w (u y)]; simp)) (hg.1.lift_snd _ _ _)
  have hη : ∀ y, (ηE y).left ≫ φE = (u y).left := fun y => hg.1.lift_fst _ _ _
  have hT : (𝟙_ (Over Y.left)).hom ≫ Y.hom = Y.hom := by simp
  have one_congr : ∀ {a b : Y.left ⟶ H}, a = b → (1 : Over.mk a ⟶ AH).left = (1 : Over.mk b ⟶ AH).left := by
    intro a b h; subst h; rfl
  refine ⟨AE, inferInstance, inferInstance, φE, actE, ηE, hg, ha, ⟨fun x y => inj ?_, fun c x => inj ?_,
    fun x => inj ?_⟩, hη⟩
  · rw [hη, pm, hadd]
    exact (mul_left_congr hT (pushPt hg.1.w (ηE x)) (pushPt hg.1.w (ηE y)) (u x : Over.mk Y.hom ⟶ AH) (u y) (hη x) (hη y)).symm
  · show (ηE (c • x)).left ≫ φE = ((ηE x).left ≫ (act' c).left) ≫ φE
    rw [hη, hlin, Category.assoc, ha, ← Category.assoc, hη]; rfl
  · rw [hη, htor]
    have e := congrArg (fun q => q.left) (map_one (pushHom hg (𝟙_ (Over Y.left))))
    refine Eq.trans ?_ e.symm
    exact (one_congr hT).symm

end GlobalTheory.UPel.HT.LevPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushforwardRegularIdeal
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.PullIdeal

open CartierDiv

theorem exists_pow_regularAt {Y : Scheme.{0}} [IsIntegral Y] (D : CartierDiv Y) {V : Y.Opens}
    (hV : IsCompact (V : Set Y)) (hηV : genericPoint Y ∈ V) (t : Γ(Y, V)) (F : Y.functionField)
    (hF : ∀ z ∈ Y.basicOpen t, D.RegularAt z F) :
    ∃ n : ℕ, ∀ z ∈ V, D.RegularAt z (fnOf V hηV t ^ n * F) := by
  by_cases ht : genericPoint Y ∈ Y.basicOpen t
  swap
  · refine ⟨1, fun z _ => ?_⟩
    have h0 : fnOf V hηV t = 0 := by
      by_contra h
      exact ht ((unitAt_fnOf_iff hηV hηV t).1 (unitAt_genericPoint h))
    rw [h0, pow_one, zero_mul]
    exact (D.vanishesAt_zero z).regularAt
  have loc : ∀ y : V, ∃ W : Y.Opens, y.1 ∈ W ∧ ∃ n : ℕ,
      ∀ z ∈ W, D.RegularAt z (fnOf V hηV t ^ n * F) := by
    intro y
    obtain ⟨V', hyV', g, hg⟩ := D.exists_isEqn_nhds y.1
    obtain ⟨W, hW, hyW, hWV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
      (show y.1 ∈ V ⊓ V' from ⟨y.2, hyV'⟩)
    have hWV1 : W ≤ V := hWV.trans inf_le_left
    set t' : Γ(Y, W) := Y.presheaf.map (homOfLE hWV1).op t
    have hB : Y.basicOpen t' = W ⊓ Y.basicOpen t := Y.basicOpen_res t _
    have hgen : genericPoint Y ∈ Y.basicOpen t' := hB ▸ memInf (gen_mem hyW) ht
    obtain ⟨b, hb⟩ := exists_fnOf_eq (f := F * (g : Y.functionField)) hgen fun z hz => by
      rw [hB] at hz
      exact (hg z (hWV hz.1).2).regularAt_iff.1 (hF z hz.2)
    obtain ⟨n, a, ha⟩ := exists_eq_pow_mul_of_isAffineOpen Y W hW t' b
    have key : fnOf W (gen_mem hyW) a = fnOf V hηV t ^ n * (F * (g : Y.functionField)) := by
      have e := congrArg (fnOf _ hgen) ha
      rw [map_mul, map_pow, hb] at e
      erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at e
      exact e
    refine ⟨W, hyW, n, fun z hz => (hg z (hWV hz).2).regularAt_iff.2 ?_⟩
    rw [mul_assoc, ← key]
    exact regAt_fnOf hz _ a
  choose W hyW n hn using loc
  obtain ⟨T, hT⟩ := hV.elim_finite_subcover (fun y : V => (W y : Set Y)) (fun y => (W y).isOpen)
    (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hyW _⟩)
  refine ⟨T.sup n, fun z hz => ?_⟩
  obtain ⟨y, hyT, hzy⟩ := Set.mem_iUnion₂.1 (hT hz)
  have hle : n y ≤ T.sup n := Finset.le_sup hyT
  have hr := regAt_fnOf hz hηV (t ^ (T.sup n - n y))
  rw [map_pow] at hr
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
  exact (hn y z hzy).regAt_mul hr

theorem regAt_pull {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    {U : X.Opens} {y : Y} (hy : s y ∈ U) (c : Γ(X, U)) :
    RegAt y (functionFieldMap s (fnOf U (gen_mem hy) c)) := by
  have hy' : y ∈ s ⁻¹ᵁ U := hy
  rw [← PullPres.fnOf_app s (gen_mem hy') c]
  exact regAt_fnOf hy' _ _

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
  (D : CartierDiv Y)

def pullIdeal (U : X.Opens) : Ideal Γ(X, U) where
  carrier := {f | ∀ (y : Y) (hy : s y ∈ U), D.RegularAt y (functionFieldMap s (fnOf U (gen_mem hy) f))}
  zero_mem' y hy := by rw [map_zero, map_zero]; exact (D.vanishesAt_zero y).regularAt
  add_mem' hf hg y hy := by rw [map_add (f := _), map_add (f := _)]; exact (hf y hy).add (hg y hy)
  smul_mem' c f hf y hy := by
    rw [smul_eq_mul, map_mul, map_mul]
    exact (hf y hy).regAt_mul (regAt_pull s hy c)

def pullIdealSheaf [QuasiCompact s] : X.IdealSheafData where
  ideal U := pullIdeal s D U.1
  map_ideal_basicOpen U a := by
    show Ideal.map (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom (pullIdeal s D U.1) =
      pullIdeal s D (X.basicOpen a)
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      rw [Ideal.mem_comap]
      intro y hy
      have := hf y (X.basicOpen_le a hy)
      convert this using 3
      exact SecPowLoc.fnOf_map _ _ _
    · intro h hh
      by_cases hg : genericPoint X ∈ X.basicOpen a
      swap
      · have : h = 0 := fn_ext fun h' => (hg h').elim
        rw [this]; exact zero_mem _
      obtain ⟨n, b, hb⟩ := exists_eq_pow_mul_of_isAffineOpen X U.1 U.2 a h
      have hU0 : genericPoint X ∈ U.1 := X.basicOpen_le a hg
      have e' : fnOf U.1 hU0 b = fnOf U.1 hU0 a ^ n * fnOf _ hg h := by
        have := congrArg (fnOf _ hg) hb
        rw [map_mul, map_pow] at this
        erw [SecPowLoc.fnOf_map, SecPowLoc.fnOf_map] at this
        exact this
      obtain ⟨M, hM⟩ : ∃ M : ℕ, a ^ M * b ∈ pullIdeal s D U.1 := by
        by_cases hηV : genericPoint Y ∈ s ⁻¹ᵁ U.1
        · obtain ⟨M, hM⟩ := exists_pow_regularAt D (s.isCompact_preimage U.2.isCompact) hηV
            ((s.app U.1).hom a) (functionFieldMap s (fnOf U.1 hU0 b)) (fun z hz => by
              rw [← Scheme.preimage_basicOpen] at hz
              rw [e', map_mul, map_pow]
              have hr := regAt_pull s (U := U.1) (X.basicOpen_le a hz) (a ^ n)
              rw [map_pow, map_pow] at hr
              exact (hh z hz).regAt_mul hr)
          refine ⟨M, fun y hy => ?_⟩
          have := hM y hy
          rw [PullPres.fnOf_app] at this
          rw [map_mul, map_mul, map_pow, map_pow]
          exact this
        · exact ⟨0, fun y hy => (hηV (gen_mem (x := y) hy)).elim⟩
      have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le a)).op a) :=
        X.toRingedSpace.isUnit_res_basicOpen a
      have hb' : X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) =
          h * (hu.unit : Γ(X, X.basicOpen a)) ^ (n + M) := by
        have hb2 : X.presheaf.map (homOfLE (X.basicOpen_le a)).op b =
            X.presheaf.map (homOfLE (X.basicOpen_le a)).op a ^ n * h := hb
        rw [map_mul, map_pow, hb2]
        rw [IsUnit.unit_spec, pow_add]
        ring
      have : h = X.presheaf.map (homOfLE (X.basicOpen_le a)).op (a ^ M * b) *
          ((hu.unit⁻¹ ^ (n + M) : (Γ(X, X.basicOpen a))ˣ) : Γ(X, X.basicOpen a)) := by
        rw [hb', mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, mul_inv_cancel,
          one_pow, Units.val_one, mul_one]
      rw [this]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hM)

theorem exists_idealSheaf : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s]
    [QuasiCompact s] (D : CartierDiv Y), ∃ J : X.IdealSheafData, (∀ (U : X.affineOpens) (f : Γ(X, U.1)),
    f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) := by
  intro X Y _ _ s _ _ D
  exact ⟨pullIdealSheaf s D, fun _ _ => Iff.rfl⟩

end GlobalTheory.Cartier.PullIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMTypeRestrict

theorem exists_equiv_realEmbeddings : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I),
    ∃ e : Fin (Module.finrank ℚ (FR E)) ≃ (FR E →+* ℝ), ∀ j (x : FR E), (e j x : ℂ) = φ (e₀ j) (x : E) := by
  intro E _ _ _ I _ φ hφ e₀
  have hreal : ∀ i, ComplexEmbedding.IsReal ((φ i).comp (algebraMap (FR E) E)) := fun i =>
    InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _)
  let g : Fin (Module.finrank ℚ (FR E)) → (FR E →+* ℝ) := fun j => (hreal (e₀ j)).embedding
  have hg : ∀ j (x : FR E), (g j x : ℂ) = φ (e₀ j) (x : E) := fun j x =>
    (hreal (e₀ j)).coe_embedding_apply x
  have hinj : Function.Injective g := by
    intro j k hjk
    have hc : (φ (e₀ j)).comp (algebraMap (FR E) E) = (φ (e₀ k)).comp (algebraMap (FR E) E) := by
      ext x
      have h1 := hg j x
      have h2 := hg k x
      rw [hjk] at h1
      simp only [RingHom.comp_apply]
      exact h1.symm.trans h2
    have hm : IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ j))) =
        IsCMField.equivInfinitePlace E (InfinitePlace.mk (φ (e₀ k))) := by
      rw [IsCMField.equivInfinitePlace_apply, IsCMField.equivInfinitePlace_apply,
        InfinitePlace.comap_mk, InfinitePlace.comap_mk, hc]
    have := (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ).1 ((IsCMField.equivInfinitePlace E).injective hm)
    exact e₀.injective this
  have hcard : Fintype.card (Fin (Module.finrank ℚ (FR E))) = Fintype.card (FR E →+* ℝ) := by
    rw [Fintype.card_fin, GlobalTheory.card_realEmbeddings]
  exact ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).2 ⟨hinj, hcard⟩), fun j x => hg j x⟩

end GlobalTheory.CMTypeRestrict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersSurjectiveOfRankOne
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integers_surjective_of_rank_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  first | (exact @GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one) | (exact GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one) | (intros; apply GlobalTheory.UPel.HT.Datum.algebraMap_surjective_of_m_eq_one  <;> assumption)
end

