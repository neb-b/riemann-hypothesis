module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0421
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0419
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0429
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MayerVietorisEquivalenceOfCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.MayerVietorisEqv

theorem a4 : GlobalTheory.EtC.A4 := by
  intro R _ U V E U' V' E' f g f' g' p u v hu hv F hc hc' hU hV hW
  obtain ⟨d, hex, hnat⟩ := GlobalTheory.T.exists_mayerVietoris_connecting_exact R F
  have hwf : pullback.map f g f' g' u v p hu hv ≫ pullback.fst f' g' = pullback.fst f g ≫ u := pullback.lift_fst _ _ _
  have hwg : pullback.map f g f' g' u v p hu hv ≫ pullback.snd f' g' = pullback.snd f g ≫ v := pullback.lift_snd _ _ _
  have cf : ∀ n x, pull R f F n (pull R p F n x) = pull R u F n (pull R f' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hu]
  have cg : ∀ n x, pull R g F n (pull R p F n x) = pull R v F n (pull R g' F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hv]
  have cfst : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.fst f' g') F n x) =
      pull R (pullback.fst f g) F n (pull R u F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwf]
  have csnd : ∀ n x, pull R (pullback.map f g f' g' u v p hu hv) F n (pull R (pullback.snd f' g') F n x) =
      pull R (pullback.snd f g) F n (pull R v F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, hwg]
  have hcond : ∀ n x, pull R (pullback.fst f g) F n (pull R f F n x) =
      pull R (pullback.snd f g) F n (pull R g F n x) := by
    intro n x; rw [← pull_comp, ← pull_comp, pullback.condition]
  intro n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  constructor
  · rw [injective_iff_map_eq_zero]
    intro y hy
    have h1 : pull R f' F (m + 1) y = 0 := by
      apply (hU (m + 1)).1
      rw [← cf, hy, map_zero, map_zero]
    have h2 : pull R g' F (m + 1) y = 0 := by
      apply (hV (m + 1)).1
      rw [← cg, hy, map_zero, map_zero]
    obtain ⟨c, rfl⟩ := ((hex f' g' hc' m).2.2 y).1 ⟨h1, h2⟩
    have hd : d f g hc m (pull R (pullback.map f g f' g' u v p hu hv) F m c) = 0 := by
      rw [← hnat f g f' g' p u v hu hv hc hc' m c]; exact hy
    obtain ⟨a, b, hab⟩ := ((hex f g hc m).2.1 _).1 hd
    obtain ⟨a', rfl⟩ := (hU m).2 a
    obtain ⟨b', rfl⟩ := (hV m).2 b
    have hc1 : c = pull R (pullback.fst f' g') F m a' - pull R (pullback.snd f' g') F m b' := by
      apply (hW m).1
      rw [hab, map_sub, cfst, csnd]
    exact ((hex f' g' hc' m).2.1 c).2 ⟨a', b', hc1⟩
  · intro z
    obtain ⟨a', ha'⟩ := (hU (m + 1)).2 (pull R f F (m + 1) z)
    obtain ⟨b', hb'⟩ := (hV (m + 1)).2 (pull R g F (m + 1) z)
    have hab : pull R (pullback.fst f' g') F (m + 1) a' = pull R (pullback.snd f' g') F (m + 1) b' := by
      apply (hW (m + 1)).1
      rw [cfst, csnd, ha', hb', hcond]
    obtain ⟨y, hy1, hy2⟩ := ((hex f' g' hc' (m + 1)).1 a' b').1 hab
    have k1 : pull R f F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cf, hy1, ha', sub_self]
    have k2 : pull R g F (m + 1) (z - pull R p F (m + 1) y) = 0 := by
      rw [map_sub, cg, hy2, hb', sub_self]
    obtain ⟨c, hc0⟩ := ((hex f g hc m).2.2 _).1 ⟨k1, k2⟩
    obtain ⟨c', rfl⟩ := (hW m).2 c
    refine ⟨y + d f' g' hc' m c', ?_⟩
    rw [map_add (f := _), hnat f g f' g' p u v hu hv hc hc' m c', hc0]
    abel

end GlobalTheory.MayerVietorisEqv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegersOfMemHatO
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.Conv

variable {E : Type} [Field E] [NumberField E]

theorem mem_integers_of_mem_hatO {c : Ideal (OF E)} {y : Af E} (hy : y ∈ hatO c) (v : HeightOneSpectrum (𝓞 E)) :
    y v ∈ v.adicCompletionIntegers E := by
  have hc : IsClosed {y : Af E | y v ∈ v.adicCompletionIntegers E} :=
    (Valued.isClosed_valuationSubring (v.adicCompletion E)).preimage (RestrictedProduct.continuous_eval v)
  refine closure_minimal (t := {y : Af E | y v ∈ v.adicCompletionIntegers E}) ?_ hc hy
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, b, -, rfl⟩ := mem_orderC.1 hx
  have : algebraMap (OF E) E a + algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a + b) := by
    rw [map_add (f := _)]; rfl
  rw [this]
  refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).trans_le (v.valuation_le_one _)

theorem exists_denominator (c : Ideal (OF E)) (y : (Af E)ˣ) :
    ∃ n : ℕ, 0 < n ∧ ∀ x ∈ lattice c y, ∃ b : 𝓞 E, algebraMap (𝓞 E) E b = n * x := by
  obtain ⟨n, hn, hy⟩ := PI.AdCpctDenWork.exists_nat_adele (y : Af E)
  refine ⟨n, hn, fun x hx => ?_⟩
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 E) E _ fun v => ?_
  have h1 := mul_mem (hy v) (mem_integers_of_mem_hatO hx v)
  have h2 : ((n : Af E) * (y : Af E)) * (algebraMap E (Af E) x * (↑y⁻¹ : Af E)) = algebraMap E (Af E) (n * x) := by
    rw [map_mul, map_natCast]
    linear_combination ((n : Af E) * algebraMap E (Af E) x) * y.mul_inv
  have h3 : (algebraMap E (Af E) (n * x)) v ∈ v.adicCompletionIntegers E := by
    rw [← h2]; exact h1
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _).symm.trans_le
    ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h3)


omit [NumberField E] in
theorem exists_generator : ∃ g : Ideal (𝓞 E) → 𝓞 E, ∀ b : 𝓞 E, ∃ u : (𝓞 E)ˣ, g (Ideal.span {b}) * u = b := by
  classical
  refine ⟨fun I => if h : ∃ b, Ideal.span {b} = I then h.choose else 0, fun b => ?_⟩
  have h : ∃ b', Ideal.span {b'} = Ideal.span {b} := ⟨b, rfl⟩
  simp only [dif_pos h]
  exact Ideal.span_singleton_eq_span_singleton.1 h.choose_spec

theorem summable_norm_rpow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ) (t : ℝ), c ≠ ⊥ → 1 < t → Summable fun q : modUnits (lattice c y) => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-t) := by
  intro E _ _ _ c y t _ ht
  obtain ⟨n, hn, hL⟩ := exists_denominator c y
  choose b hb using fun q : modUnits (lattice c y) => hL _ (out_mem_lattice q).1
  obtain ⟨g, hg⟩ := exists_generator (E := E)
  choose u hu using hg
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  let f : modUnits (lattice c y) → Units.torsion E × Ideal (𝓞 E) :=
    fun q => (IsCMField.unitsMulComplexConjInv E (u (b q)), Ideal.span {b q})
  have hf : Function.Injective f := by
    intro q q' h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    have h3 : u (b q') * (u (b q))⁻¹ ∈ IsCMField.realUnits E := by
      rw [← IsCMField.unitsMulComplexConjInv_ker, MonoidHom.mem_ker, map_mul, map_inv, h1, mul_inv_cancel]
    obtain ⟨v, hv⟩ := (IsCMField.mem_realUnits_iff E _).1 h3
    have h4 : b q' = algebraMap (OF E) (𝓞 E) v * b q := by
      rw [hv]
      have e1 := hu (b q)
      have e2 := hu (b q')
      rw [← h2] at e2
      rw [Units.val_mul]
      linear_combination (-1 : 𝓞 E) * e2 + ((u (b q') : 𝓞 E) * (↑(u (b q))⁻¹ : 𝓞 E)) * e1
        - (g (Ideal.span {b q}) * (u (b q') : 𝓞 E)) * (u (b q)).mul_inv
    have h5 : (q'.1.out : E) = algebraMap (OF E) E v * q.1.out := by
      apply mul_left_cancel₀ hn'
      rw [← hb q', h4, map_mul, hb q, mul_left_comm]; rfl
    apply Subtype.ext
    rw [← Quotient.out_eq q.1, ← Quotient.out_eq q'.1]
    exact Quotient.sound ⟨v, h5⟩
  have hI := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow E).2 t ht).1
  have hP : Summable fun p : Units.torsion E × Ideal (𝓞 E) => (Ideal.absNorm p.2 : ℝ) ^ (-t) := by
    refine (summable_prod_of_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg _) _).2 ⟨fun _ => hI, ?_⟩
    exact Summable.of_finite
  have hN : (0 : ℝ) < |(Algebra.norm ℚ (n : E) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast (Algebra.norm_ne_zero_iff.2 hn')
  refine ((hP.comp_injective hf).mul_left (|(Algebra.norm ℚ (n : E) : ℝ)| ^ t)).congr fun q => ?_
  have h1 : (Ideal.absNorm (Ideal.span {b q}) : ℝ) =
      |(Algebra.norm ℚ (n : E) : ℝ)| * |(Algebra.norm ℚ (q.1.out : E) : ℝ)| := by
    rw [Ideal.absNorm_span_singleton, ← abs_mul, ← Rat.cast_mul, ← map_mul, ← hb q, Nat.cast_natAbs, Int.cast_abs,
      ← Algebra.coe_norm_int]
    simp
  show _ * (Ideal.absNorm (Ideal.span {b q}) : ℝ) ^ (-t) = _
  rw [h1, Real.mul_rpow hN.le (abs_nonneg _), ← mul_assoc, ← Real.rpow_add hN]
  simp

end GlobalTheory.CMVal.Conv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMapSurjectiveFiniteField
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_map_surjective_finite_field : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F', (δ : Matrix (Fin n) (Fin n) F') ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧ nrm s δ = incl F F' n γ := by
  first | (exact @GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (exact GlobalTheory.Shin.NormSurj.nrm_surj_adjoin) | (intros; apply GlobalTheory.Shin.NormSurj.nrm_surj_adjoin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormEqZeroOfVanishingOnPairsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oneForm_eq_zero_of_vanishing_on_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (ω : Ω[(OAff s').obj (op W)⁄R']), (∀ (p : Pair φ) (hp : p.1.1 ≤ W), p1 (OAff s') (homOfLE hp).op ω = 0) → ω = 0 := by
  first | exact @GlobalTheory.CechDR.form_eq_zero_of_pair | exact GlobalTheory.CechDR.form_eq_zero_of_pair | (intros; apply GlobalTheory.CechDR.form_eq_zero_of_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneFormsTwoCocycleCoboundaryOfRestrict
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FormExt

attribute [local instance] GlobalTheory.Cris.opModule GlobalTheory.Cris.isCentralScalar_kaehler GlobalTheory.Cris.isScalarTower_kaehler

theorem inr_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x + y = z + w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) + TrivSqZeroExt.inr y =
      TrivSqZeroExt.inr z + TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_add, ← TrivSqZeroExt.inr_add, h]

theorem inr_sub_add_inr_eq {A M : Type} [AddCommGroup A] [AddCommGroup M] {x y z w : M}
    (h : x - y + z = w) :
    (TrivSqZeroExt.inr x : TrivSqZeroExt A M) - TrivSqZeroExt.inr y + TrivSqZeroExt.inr z =
      TrivSqZeroExt.inr w := by
  rw [← TrivSqZeroExt.inr_sub, ← TrivSqZeroExt.inr_add, h]

theorem snd_sub_add {A M : Type} [AddCommGroup A] [AddCommGroup M] (a b c : TrivSqZeroExt A M) :
    (a - b + c).snd = a.snd - b.snd + c.snd := by
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub]

theorem mp_omExt_inr {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    {T T' : C} (φ : T ⟶ T') (x : Ω[F.obj T⁄R]) :
    mp (omExt F) φ (TrivSqZeroExt.inr x : (omExt F).obj T) =
      (TrivSqZeroExt.inr (p1 F φ x) : (omExt F).obj T') :=
  TrivSqZeroExt.ext ((fst_extMap F φ _).trans (by rw [TrivSqZeroExt.fst_inr, map_zero]; rfl))
    ((snd_extMap F φ _).trans (by rw [TrivSqZeroExt.snd_inr]; rfl))

theorem coboundary_of_restrict_forms : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), Function.Injective (CoefMap.restrict (FormExt.omExt F) G).pull2 → (∀ κ : A2 F, (∀ ⦃T T' T'' T''' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T'''), p1 F χ (κ T T' T'' φ ψ) + κ T T'' T''' (φ ≫ ψ) χ = κ T T' T''' φ (ψ ≫ χ) + κ T' T'' T''' ψ χ) → ∀ β' : ∀ t t', (t ⟶ t') → Ω[F.obj (G.obj t')⁄R], (∀ ⦃t t' t'' : C'⦄ (a : t ⟶ t') (b : t' ⟶ t''), κ _ _ _ (G.map a) (G.map b) = p1 F (G.map b) (β' t t' a) - β' t t'' (a ≫ b) + β' t' t'' b) → ∃ β : A1 F, ∀ ⦃T T' T'' : C⦄ (φ : T ⟶ T') (ψ : T' ⟶ T''), κ T T' T'' φ ψ = p1 F ψ (β T T' φ) - β T T'' (φ ≫ ψ) + β T' T'' ψ) := by
  intro R _ C _ C' _ F G hinj κ hκ β' hβ'
  let z : Z2 (omExt F) := ⟨fun T T' T'' φ ψ ↦ TrivSqZeroExt.inr (κ T T' T'' φ ψ),
    fun T T' T'' T''' φ ψ χ ↦ by
      simp only []
      rw [mp_omExt_inr]
      exact inr_add_inr_eq (hκ φ ψ χ)⟩
  have h0 : (CoefMap.restrict (omExt F) G).pull2 (H2.mk (omExt F) z) = 0 := by
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]
    refine ⟨fun t t' a ↦ (TrivSqZeroExt.inr (β' t t' a) : (omExt F).obj (G.obj t')), ?_⟩
    funext t t' t'' a b
    exact (congrArg (fun x : TrivSqZeroExt (F.obj (G.obj t'')) Ω[F.obj (G.obj t'')⁄R] ↦
      x - TrivSqZeroExt.inr (β' t t'' (a ≫ b)) + TrivSqZeroExt.inr (β' t' t'' b))
      (mp_omExt_inr F (G.map b) (β' t t' a))).trans (inr_sub_add_inr_eq (hβ' a b).symm)
  have h1 : H2.mk (omExt F) z = 0 := hinj (h0.trans (map_zero _).symm)
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 h1
  refine ⟨fun T T' φ ↦ (f T T' φ).snd, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrArg TrivSqZeroExt.snd
    (congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ)
  have e2 := (snd_sub_add (mp (omExt F) ψ (f T T' φ)) (f T T'' (φ ≫ ψ)) (f T' T'' ψ)).symm.trans
    (e.trans (TrivSqZeroExt.snd_inr _ _))
  rw [show (mp (omExt F) ψ (f T T' φ)).snd = p1 F ψ (f T T' φ).snd from snd_extMap F ψ _] at e2
  exact e2.symm

end GlobalTheory.CechDR.FormExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveSemilinearLiftBaseChangeBijectiveStatement
section
open Coalgebra GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.primitive_semilinearLift_baseChange_bijective
    {R A : Type} (R' : Type) [CommRing R] [CommRing A] [Bialgebra R A]
    [Module.Finite R A] [Module.Projective R A] [IsCocomm R A] [CommRing R']
    [Algebra R R'] (hC : Module.Projective R (Cot R (CartierDual R A))) :
    Function.Bijective (liftSemi (toBaseChange R R' A).prim) :=
  liftSemi_prim_toBaseChange_bijective R' hC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq
section
open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMVal.TermUnit

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]


omit [NumberField E] [Fintype I] in
theorem bijective_mk {φ : I → E →+* ℂ} (h : IsCMType φ) :
    Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
  constructor
  · intro i j hij
    have hj := InfinitePlace.mk_eq_iff.mp hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have e1 : i = k := hk i (hj.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm))
    have e2 : j = k := hk j (Or.inl rfl)
    rw [e1, e2]
  · intro w
    obtain ⟨i, hi, -⟩ := h w.embedding
    refine ⟨i, ?_⟩
    show InfinitePlace.mk (φ i) = w
    rcases hi with hi | hi
    · rw [← hi, InfinitePlace.mk_embedding]
    · rw [← InfinitePlace.mk_conjugate_eq (φ i), ← hi, InfinitePlace.mk_embedding]

theorem prod_norm_sq [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (x : E) :
    ∏ i, ‖φ i x‖ ^ 2 = |(Algebra.norm ℚ x : ℝ)| := by
  calc ∏ i, ‖φ i x‖ ^ 2 = ∏ w : InfinitePlace E, w x ^ InfinitePlace.mult w :=
        Fintype.prod_bijective _ (bijective_mk h) _ _ fun i => by
          rw [IsTotallyComplex.mult_eq, InfinitePlace.apply]
    _ = _ := by rw [InfinitePlace.prod_eq_abs_norm]; push_cast; rfl

theorem prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (z : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ z = ((∏ j ∈ t, f j : ℝ) : ℂ) ^ z := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem term_unit [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (u : (OF E)ˣ) :
    term φ (2 * s) κ σ (algebraMap (OF E) E u) = 1 := by
  set x := algebraMap (OF E) E (u : OF E) with hxdef
  have hxmem : x ∈ maximalRealSubfield E := by
    rw [hxdef, IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
    exact (algebraMap (OF E) (maximalRealSubfield E) u).2
  have hreal : ∀ i, starRingEnd ℂ (φ i x) = φ i x := fun i => by
    rw [starRingEnd_apply]
    exact (mem_maximalRealSubfield_iff x).mp hxmem (φ i)
  have hx0 : x ≠ 0 := (u.isUnit.map (algebraMap (OF E) E)).ne_zero
  have hN : |(Algebra.norm ℚ x : ℝ)| = 1 := by
    have hv := NumberField.isUnit_iff_norm.mp (u.isUnit.map (algebraMap (OF E) (𝓞 E)))
    have hc : ((algebraMap (OF E) (𝓞 E) u : 𝓞 E) : E) = x :=
      (IsScalarTower.algebraMap_apply (OF E) (𝓞 E) E u).symm
    rw [RingOfIntegers.coe_norm, hc] at hv
    exact_mod_cast hv
  have hprod : ∏ i, ‖φ i x‖ = 1 := by
    have hsq : (∏ i, ‖φ i x‖) ^ 2 = 1 := by rw [← Finset.prod_pow, prod_norm_sq h x, hN]
    exact (pow_eq_one_iff_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _) two_ne_zero).mp hsq
  have hfac : ∀ i, (φ i x)⁻¹ ^ (2 * s + κ i) * starRingEnd ℂ (φ i x) ^ κ i * ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖φ i x‖ : ℝ) : ℂ) ^ (-2 * ((s : ℂ) + σ)) := fun i => by
    have hr : φ i x ≠ 0 := (map_ne_zero (φ i)).mpr hx0
    have ha : ((‖φ i x‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hr)
    have hsq : ((‖φ i x‖ : ℝ) : ℂ) ^ 2 = φ i x ^ 2 := by
      have hm := Complex.mul_conj (φ i x)
      rw [hreal, Complex.normSq_eq_norm_sq] at hm
      rw [sq (φ i x), hm]
      push_cast
      ring
    rw [show -2 * ((s : ℂ) + σ) = -((2 * s : ℕ) : ℂ) + -2 * σ by push_cast; ring,
      Complex.cpow_add _ _ ha, Complex.cpow_neg, Complex.cpow_natCast, hreal]
    congr 1
    rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hr, one_pow, mul_one, inv_pow, pow_mul, pow_mul, hsq]
  simp only [term]
  rw [Finset.prod_congr rfl fun i _ => hfac i, prod_cpow _ _ (fun i => norm_nonneg _), hprod]
  simp

theorem norm_term [IsCMField E] {φ : I → E →+* ℂ} (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) {x : E} (hx : x ≠ 0) :
    ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re)) := by
  have hpos : ∀ i, 0 < ‖φ i x‖ := fun i => norm_pos_iff.mpr ((map_ne_zero (φ i)).mpr hx)
  rw [← prod_norm_sq h x, ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  simp only [term, norm_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have ha := hpos i
  rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_inv, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos ha, inv_pow, ← Real.rpow_natCast _ (2 * s + κ i),
    ← Real.rpow_natCast _ (κ i), ← Real.rpow_neg ha.le, ← Real.rpow_add ha, ← Real.rpow_add ha,
    ← Real.rpow_natCast _ 2, ← Real.rpow_mul ha.le]
  congr 1
  simp
  ring

private theorem term_mul' (φ : I → E →+* ℂ) (k : ℕ) (κ : I → ℕ) (σ : ℂ) (y x : E) :
    term φ k κ σ (y * x) = term φ k κ σ y * term φ k κ σ x := by
  simp only [term, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [map_mul, mul_inv, norm_mul, mul_pow]
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

theorem term_unit_and_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (h : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (x : E) :
    (∀ u : (OF E)ˣ, term φ (2 * s) κ σ (algebraMap (OF E) E u * x) = term φ (2 * s) κ σ x) ∧
      (x ≠ 0 → ‖term φ (2 * s) κ σ x‖ = |(Algebra.norm ℚ x : ℝ)| ^ (-((s : ℝ) + σ.re))) := by
  refine ⟨fun u => ?_, fun hx => norm_term h s κ σ hx⟩
  rw [term_mul', term_unit h s κ σ u, one_mul]

end GlobalTheory.CMVal.TermUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullAwChainsBijective
section
noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ
universe u v

theorem ez_nat {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (Y : SimplicialObject (SimplicialObject C)) :
    ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  obtain ⟨G, h0, hG⟩ := GlobalTheory.T.exists_bisimplicial_shuffle_operators
  obtain ⟨H, hH⟩ := GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id G h0 hG
  obtain ⟨K, hK⟩ := GlobalTheory.T.alexander_whitney_homotopy_formula G h0 hG
  exact GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv Y G H K h0 hG hH hK

variable (R : Type) [CommRing R]

theorem ez (X : SimplicialObject GlobalTheory.EtC.Spc) :
    ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X),
      ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n :=
  GlobalTheory.T.eilenberg_zilber_homotopy_equivalence R X (ez_nat _)

def ezEquiv (X : SimplicialObject GlobalTheory.EtC.Spc) :
    HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X) := (ez R X).choose

def awChains (X : SimplicialObject GlobalTheory.EtC.Spc) : (GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X) ⟶ totChains R X :=
  (ezEquiv R X).hom

theorem awChains_f (X : SimplicialObject GlobalTheory.EtC.Spc) (n : ℕ) : (awChains R X).f (-(n : ℤ)) = awZ R X n :=
  (ez R X).choose_spec n

theorem pull_awChains_bijective (X : SimplicialObject GlobalTheory.EtC.Spc) (I : GlobalTheory.EtC.Cx R) (k : ℤ) :
    Function.Bijective (GlobalTheory.EtC.cpull (awChains R X) I k) :=
  GlobalTheory.EtC.LevelCmp.cpull_bij_of_heq (ezEquiv R X) I k

end GlobalTheory.EZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTopFormPoleOrderHeightOnePrimeStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_topForm_pole_order_height_one_prime : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ (Q : Ideal B), Q.IsPrime → Q.height = 1 → ∀ (t : A) (s : B) (e : ℕ), Irreducible t → 1 ≤ e → s ∈ Q → (∀ y ∈ Q, ∃ c r : B, r ∉ Q ∧ r * y = c * s) → (∃ a r : B, a ∉ Q ∧ r ∉ Q ∧ (r : K) * algebraMap F K t = a * s ^ e) → ∀ z : K, (∃ r : B, r ∉ Q ∧ ∃ y ∈ omB k K B d, τ y = r * z) ↔ ∃ c r : B, r ∉ Q ∧ (r : K) * s ^ (e - 1) * z = c := by
  first | (exact @GlobalTheory.PD.omB_top_coeff_iff_pole) | (exact GlobalTheory.PD.omB_top_coeff_iff_pole) | (intros; apply GlobalTheory.PD.omB_top_coeff_iff_pole  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpecStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) (U : Scheme.{0}) (a : Sec F U), (restrMap φ F).app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  first | (exact @GlobalTheory.EtC.restrMap_spec') | (exact GlobalTheory.EtC.restrMap_spec') | (intros; apply GlobalTheory.EtC.restrMap_spec'  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecLocallyConstantStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_exists_of_isLocallyConstant_locallyConstant : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] (B : Type) [CommRing B], (∀ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), IsLocallyConstant (fun x : X => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t)) ∧ Function.Injective (fun (t : Sec F (Spec (CommRingCat.of (LocallyConstant X B)))) (x : X) => Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t) ∧ ∀ ψ : X → Sec F (Spec (CommRingCat.of B)), IsLocallyConstant ψ → ∃ t : Sec F (Spec (CommRingCat.of (LocallyConstant X B))), ∀ x, Sec.res (Spec.map (CommRingCat.ofHom (LocallyConstant.evalRingHom x))) t = ψ x := by
  first | (exact @GlobalTheory.EtC.sec_locallyConstant) | (exact GlobalTheory.EtC.sec_locallyConstant) | (intros; apply GlobalTheory.EtC.sec_locallyConstant  <;> assumption)
end

