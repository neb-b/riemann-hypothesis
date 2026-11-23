module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEltPrescribedValuationsBalancedArchimedean
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem sum_embeddings_eq_sum_places {K : Type} [Field K] [NumberField K] (g : (K →+* ℂ) → ℝ)
    (hg : ∀ σ, g ((starRingEnd ℂ).comp σ) = g σ) :
    ∑ σ, g σ = ∑ w : InfinitePlace K, (w.mult : ℝ) * g w.embedding := by
  rw [← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : ∀ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ => InfinitePlace.mk σ = w), g σ = g w.embedding := by
    intro σ hσ
    rw [Finset.mem_filter] at hσ
    rw [← hσ.2]
    rcases embedding_mk_eq σ with h | h
    · rw [h]
    · rw [h]
      have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
        RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
      rw [this, hg]
  rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

theorem t_embedding_mk {K : Type} [Field K] (t : (K →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (σ : K →+* ℂ) : t (InfinitePlace.mk σ).embedding = t σ := by
  rcases embedding_mk_eq σ with h | h
  · rw [h]
  · have : ComplexEmbedding.conjugate σ = (starRingEnd ℂ).comp σ :=
      RingHom.ext fun x => ComplexEmbedding.conjugate_coe_eq σ x
    rw [h, this, ht]

theorem minkowskiBound_eq_absNorm_mul {K : Type} [Field K] [NumberField K] (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    minkowskiBound K I = ENNReal.ofReal (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
      minkowskiBound K 1 := by
  unfold minkowskiBound
  rw [volume_fundamentalDomain_fractionalIdealLatticeBasis, volume_fundamentalDomain_fractionalIdealLatticeBasis]
  simp [mul_assoc]

end GlobalTheory.CovHt

namespace GlobalTheory.CovHt

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped nonZeroDivisors

theorem exists_elt_balanced : ∀ (K : Type) [Field K] [NumberField K] (e : HeightOneSpectrum (𝓞 K) →₀ ℝ)
    (t : (K →+* ℂ) → ℝ), (∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) → ∃ C : ℝ, ∀ τ : ℕ, ∃ α : K, α ≠ 0 ∧
      (∀ la, (τ : ℝ) * e la ≤ (vLa la α : ℝ)) ∧ ∀ σ : K →+* ℂ, Real.log ‖σ α‖ ≤ τ * (cost e t - t σ) + C := by
  intro K _ _ e t ht

  have hNpos : ∀ la : HeightOneSpectrum (𝓞 K), (0 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have : Ideal.absNorm la.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact la.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hNone : ∀ la : HeightOneSpectrum (𝓞 K), (1 : ℝ) ≤ (Ideal.absNorm la.asIdeal : ℝ) := by
    intro la
    have h := hNpos la
    have : (1 : ℕ) ≤ Ideal.absNorm la.asIdeal := by exact_mod_cast h
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
  set S : ℝ := e.sum fun la a => a * Real.log (Ideal.absNorm la.asIdeal : ℝ) with hS
  set A : ℝ := ∑ la ∈ e.support, Real.log (Ideal.absNorm la.asIdeal : ℝ) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun la _ => Real.log_nonneg (hNone la)
  set V0 : ℝ := (minkowskiBound K 1).toReal with hV0
  have hV0nn : 0 ≤ V0 := ENNReal.toReal_nonneg
  set c : ℝ := |Real.log V0| + A + 1 with hc
  refine ⟨c, fun τ => ?_⟩
  set m : HeightOneSpectrum (𝓞 K) → ℤ := fun la => ⌈(τ : ℝ) * e la⌉ with hm
  have hm0 : ∀ la, la ∉ e.support → m la = 0 := by
    intro la hla
    rw [Finsupp.notMem_support_iff] at hla
    simp [hm, hla]
  have hmfin : ∀ᶠ v in Filter.cofinite, m v = 0 := by
    rw [Filter.eventually_cofinite]
    refine e.support.finite_toSet.subset fun v hv => ?_
    by_contra h
    exact hv (hm0 v h)
  set I : (FractionalIdeal (𝓞 K)⁰ K)ˣ := ∏ᶠ v, GroundTheory.Global.primeIdealUnit v ^ m v with hI
  have hcount : ∀ v, FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K) = m v :=
    GroundTheory.Global.count_finprod_primeIdealUnit_zpow m hmfin

  have hnorm : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) =
      ∏ la ∈ e.support, (Ideal.absNorm la.asIdeal : ℝ) ^ m la := by
    rw [hI, GroundTheory.Global.coe_finprod_primeIdealUnit_zpow m hmfin,
      finprod_eq_prod_of_mulSupport_subset (s := e.support)]
    · rw [map_prod, Rat.cast_prod]
      refine Finset.prod_congr rfl fun la _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
    · intro v hv
      by_contra h
      exact hv (by simp [hm0 v h])
  have hnormle : ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) ≤ Real.exp (τ * S + A) := by
    rw [hnorm]
    have hS' : S = ∑ la ∈ e.support, e la * Real.log (Ideal.absNorm la.asIdeal : ℝ) := rfl
    rw [hS', hA, Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun la _ => by positivity) fun la _ => ?_
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos (hNpos la)]
    refine Real.exp_le_exp.2 ?_
    have h1 : ((m la : ℤ) : ℝ) ≤ τ * e la + 1 := (Int.ceil_lt_add_one _).le
    have h2 := Real.log_nonneg (hNone la)
    nlinarith

  set g : InfinitePlace K → ℝ := fun w => (τ : ℝ) * (cost e t - t w.embedding) + c with hg
  set f : InfinitePlace K → NNReal := fun w => ⟨Real.exp (g w), (Real.exp_pos _).le⟩ with hf
  have hsum : ∑ w : InfinitePlace K, (w.mult : ℝ) * g w = τ * S + (Module.finrank ℚ K : ℝ) * c := by
    have h := sum_embeddings_eq_sum_places (K := K) (fun σ => (τ : ℝ) * (cost e t - t σ) + c)
      (fun σ => by simp only [ht])
    rw [show (∑ w : InfinitePlace K, (w.mult : ℝ) * g w) =
        ∑ w : InfinitePlace K, (w.mult : ℝ) * ((τ : ℝ) * (cost e t - t w.embedding) + c) from rfl, ← h]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
      Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul, nsmul_eq_mul]
    have hn0 : (Module.finrank ℚ K : ℝ) ≠ 0 := by positivity
    have hcost : (Module.finrank ℚ K : ℝ) * cost e t = S + ∑ σ, t σ := by
      rw [cost, mul_div_cancel₀ _ hn0]
    rw [hcost]; ring
  have hprod : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
    rw [NNReal.coe_prod, ← hsum, Real.exp_sum]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [NNReal.coe_pow, Real.exp_nat_mul]
    rfl
  have hmink : minkowskiBound K I < MeasureTheory.volume (convexBodyLT K f) := by
    rw [convexBodyLT_volume, minkowskiBound_eq_absNorm_mul]
    have h1 : minkowskiBound K 1 = ENNReal.ofReal V0 := (ENNReal.ofReal_toReal (minkowskiBound_lt_top K 1).ne).symm
    rw [h1, ← ENNReal.ofReal_mul (by
      rw [hnorm]; exact Finset.prod_nonneg fun la _ => by positivity)]
    refine lt_of_lt_of_le ?_ (le_mul_of_one_le_left zero_le' (by exact_mod_cast one_le_convexBodyLTFactor K))
    rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff (by rw [hprod]; positivity), hprod]
    have hV : V0 ≤ Real.exp |Real.log V0| := by
      rcases hV0nn.eq_or_lt with h | h
      · rw [← h]; positivity
      · calc V0 = Real.exp (Real.log V0) := (Real.exp_log h).symm
          _ ≤ Real.exp |Real.log V0| := Real.exp_le_exp.2 (le_abs_self _)
    calc ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℚ) : ℝ) * V0
        ≤ Real.exp (τ * S + A) * Real.exp |Real.log V0| :=
          mul_le_mul hnormle hV hV0nn (Real.exp_pos _).le
      _ = Real.exp (τ * S + (A + |Real.log V0|)) := by rw [← Real.exp_add]; ring_nf
      _ < Real.exp (τ * S + (Module.finrank ℚ K : ℝ) * c) := by
          refine Real.exp_lt_exp.2 ?_
          have hc0 : 0 ≤ c := by positivity
          nlinarith
  obtain ⟨α, hαI, hα0, hlt⟩ := exists_ne_zero_mem_ideal_lt K I hmink
  refine ⟨α, hα0, fun la => ?_, fun σ => ?_⟩
  · have hsp : FractionalIdeal.spanSingleton (𝓞 K)⁰ α ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0
    have hle := FractionalIdeal.count_mono K la hsp (FractionalIdeal.spanSingleton_le_iff_mem.2 hαI)
    rw [hcount, GroundTheory.Global.count_spanSingleton la hα0] at hle
    have hv : vLa la α = -WithZero.log (la.valuation K α) := rfl
    calc (τ : ℝ) * e la ≤ (m la : ℝ) := Int.le_ceil _
      _ ≤ (vLa la α : ℝ) := by rw [hv]; exact_mod_cast hle
  · have h := hlt (InfinitePlace.mk σ)
    rw [InfinitePlace.apply] at h
    have hpos : 0 < ‖σ α‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hα0)
    have : Real.log ‖σ α‖ ≤ Real.log (f (InfinitePlace.mk σ) : ℝ) := Real.log_le_log hpos h.le
    rw [show ((f (InfinitePlace.mk σ)) : ℝ) = Real.exp (g (InfinitePlace.mk σ)) from rfl, Real.log_exp] at this
    rw [hg] at this
    simp only [t_embedding_mk t ht σ] at this
    exact this

end GlobalTheory.CovHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivialisationCompMonHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.CubTrivComp

theorem val_cast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (h ▸ t : LB.Gen (LB.LinComb L φ' ε)) r z J = val t r z J := by
  subst h; rfl

theorem isGen_cast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) :
    (h ▸ t : LB.Gen (LB.LinComb L φ' ε)).IsGen := by
  subst h; exact ht

theorem exists_even_comp : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H']
    (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i,
    GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  intro S G H H' _ _ _ _ P i e he σ hσ
  have hφ : (fun k => e.left ≫ (![i.left, (1 : H' ⟶ G).left] : Fin 2 → (H'.left ⟶ G.left)) k) =
      ![(e ≫ i).left, (1 : H ⟶ G).left] := by
    funext k
    fin_cases k
    · exact (Over.comp_left _ _ _ e i).symm
    · show e.left ≫ (1 : H' ⟶ G).left = (1 : H ⟶ G).left
      rw [← Over.comp_left, MonObj.comp_one]
  let s₁ : LB.Gen (LB.LinComb P.L.L (K := Fin 2) ![(e ≫ i).left, (1 : H ⟶ G).left] ![1, -1]) :=
    hφ ▸ LB.pullGen P.L.L _ _ σ.s e.left
  have v : ∀ {T : Over S} (x : T ⟶ H) {z : T.left} {J}, Good P.L.L z J →
      val s₁ x.left z J = val σ.s (x ≫ e).left z J := fun x z J hJ =>
    (val_cast hφ _ _ _ _).trans ((val_pull hJ σ.s e.left x.left).trans (by rw [Over.comp_left]))
  refine ⟨⟨s₁, isGen_cast hφ (DVR.pullGen_isGen _ _ _ _ σ.gen _), fun T x y u z J hJ => ?_⟩, fun T x z J hJ => ?_⟩
  · have c := σ.cub T (x ≫ e) (y ≫ e) (u ≫ e) z J hJ
    simp only [← MonObj.mul_comp, Category.assoc] at c
    simp only [v _ hJ]
    exact c
  · show val s₁ (x⁻¹).left z J = val P.sym (x ≫ e ≫ i).left z J * val s₁ x.left z J
    rw [v _ hJ, v _ hJ, GrpObj.inv_comp, hσ T (x ≫ e) z J hJ, Category.assoc]

end GlobalTheory.CubTrivComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionSquareOfAxesTrivial
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.AxisTrivExt

variable {S S' : Scheme.{0}}

theorem isPullback_sq {A : Over S'} {G : Over S} {b : S' ⟶ S} {f : A.left ⟶ G.left}
    (m : IsPullback f A.hom G.hom b) {h : (A ⊗ A).left ⟶ (G ⊗ G).left}
    (h₁ : h ≫ (fst G G).left = (fst A A).left ≫ f) (h₂ : h ≫ (snd G G).left = (snd A A).left ≫ f) :
    IsPullback h (A ⊗ A).hom (G ⊗ G).hom b := by
  have p : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  have p' : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have q := p'.paste_horiz m
  rw [← h₁, ← m.w] at q
  have r := (IsPullback.of_right q h₂ p).paste_vert m
  rwa [Over.w, Over.w] at r

theorem unit_comp {A : Over S'} {G : Over S} [GrpObj A] [GrpObj G] {f : S' ⟶ S} {a : A.left ⟶ G.left}
    (ha : IsGrpPullback A G f a) : η[A].left ≫ a = f ≫ η[G].left := by
  let p : (𝟙_ (Over S') ⟶ A) → (Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ a) (by
      rw [Category.assoc, ha.1.w, ← Category.assoc, Over.w x]; rfl)
  have hp : p 1 * p 1 = p 1 := by
    apply Over.OverMorphism.ext
    rw [ha.2 _ 1 1 (p 1) (p 1) rfl rfl, _root_.mul_one]; rfl
  have h1 : p 1 = 1 := by simpa using hp
  have e := congrArg (fun z => z.left) h1
  have e₁ : (1 : 𝟙_ (Over S') ⟶ A) = η[A] := by rw [Hom.one_def]; simp
  simp only [p, e₁, Hom.one_def] at e
  refine e.trans ?_
  simp

theorem one_comm {A : Over S'} {G : Over S} [GrpObj A] [GrpObj G] {f : S' ⟶ S} {a : A.left ⟶ G.left}
    (ha : IsGrpPullback A G f a) : (1 : A ⟶ A).left ≫ a = a ≫ (1 : G ⟶ G).left := by
  rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Category.assoc, unit_comp ha]
  have e₁ : (toUnit A).left = A.hom := by simpa using Over.w (toUnit A)
  have e₂ : (toUnit G).left = G.hom := by simpa using Over.w (toUnit G)
  rw [e₁, e₂, ← Category.assoc, ← Category.assoc, ha.1.w]

theorem lift_match {A : Over S'} {X : Over S} {i : A.left ⟶ X.left} {l : (A ⊗ A).left ⟶ (X ⊗ X).left}
    (hl₁ : l ≫ (fst X X).left = (fst A A).left ≫ i) (hl₂ : l ≫ (snd X X).left = (snd A A).left ≫ i)
    (u v : A ⟶ A) (U V : X ⟶ X) (hu : i ≫ U.left = u.left ≫ i) (hv : i ≫ V.left = v.left ≫ i) :
    (lift u v).left ≫ l = i ≫ (lift U V).left := by
  have p : IsPullback (fst X X).left (snd X X).left X.hom X.hom := IsPullback.of_hasPullback _ _
  symm
  apply p.hom_ext
  · rw [Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc, hl₁, ← Category.assoc, ← Over.comp_left,
      lift_fst]
  · rw [Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc, hl₂, ← Category.assoc, ← Over.comp_left,
      lift_snd]

theorem exists_extension_square_of_axes_trivial : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∃ P' : LB (G2 G).left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) ∧ LBIso P (P'.pull φ₂) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hA hsq P hP h₁ h₂
  have h2 : IsPullback φ₂ (G2 A).hom (G2 G).hom (spMap (algebraMap W L)) := isPullback_sq hA.1 hsq.1 hsq.2
  have hG2 : IsAbelianScheme (G2 G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have he : h2.isoPullback.hom ≫ pullback.fst _ _ = φ₂ := h2.isoPullback_hom_fst
  obtain ⟨M, w, hM, hw⟩ := exists_lineBundle_extension_of_genericFibre_dvr W L (G2 G) hG2
    (P.pull h2.isoPullback.inv) (pull_isLB hP _)
  have i1 : LBIso ((P.pull h2.isoPullback.inv).pull h2.isoPullback.hom) (M.pull φ₂) :=
    GenSpread.lbIso_pull_of_lbIso (LBIso.symm ⟨w, hw⟩) h2.isoPullback.hom he.symm
  have i0 : LBIso (P.pull (𝟙 _)) ((P.pull h2.isoPullback.inv).pull h2.isoPullback.hom) :=
    GenSpread.lbIso_pull_pull hP h2.isoPullback.hom (by simp)
  have iP : LBIso P (M.pull φ₂) :=
    LBIso.trans hP (pull_isLB (pull_isLB hP _) _) (pull_isLB hM _)
      (LBIso.trans hP (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (lbIso_pull_id hP).symm i0) i1
  have hT := LB.isLB_triv G.left
  have axis : ∀ (iA : A.left ⟶ (G2 A).left) (iG : G.left ⟶ (G2 G).left), iA ≫ φ₂ = φ ≫ iG →
      (∃ t : (P.pull iA).Gen, t.IsGen) → ∃ t : (M.pull iG).Gen, t.IsGen := by
    intro iA iG hc hgen
    let c : LB.Gen (LB.triv G.left) := ⟨fun _ => 1⟩
    have hcg : c.IsGen := fun _ _ => by simp [c]
    have a1 : LBIso (LB.triv A.left) ((LB.triv G.left).pull φ) :=
      (GlobalTheory.CechPic.iso_triv_iff _).2 ⟨LB.genPull _ c φ, LB.isGen_genPull _ c hcg φ⟩
    have a2 : LBIso (LB.triv A.left) (P.pull iA) := (GlobalTheory.CechPic.iso_triv_iff _).2 hgen
    have a3 : LBIso (P.pull iA) ((M.pull φ₂).pull iA) := GenSpread.lbIso_pullback iP iA
    have b1 : LBIso (M.pull (φ ≫ iG)) ((M.pull φ₂).pull iA) := GenSpread.lbIso_pull_pull hM iA hc.symm
    have b2 : LBIso (M.pull (φ ≫ iG)) ((M.pull iG).pull φ) := GenSpread.lbIso_pull_pull hM φ rfl
    have lTA := LB.isLB_triv A.left
    have q1 : LBIso ((M.pull iG).pull φ) (LB.triv A.left) :=
      LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hM _) lTA b2.symm
        (LBIso.trans (pull_isLB hM _) (pull_isLB (pull_isLB hM _) _) lTA b1
          (LBIso.trans (pull_isLB (pull_isLB hM _) _) (pull_isLB hP _) lTA a3.symm a2.symm))
    have q2 : LBIso ((M.pull iG).pull φ) ((LB.triv G.left).pull φ) :=
      LBIso.trans (pull_isLB (pull_isLB hM _) _) lTA (pull_isLB hT _) q1 a1
    have q3 : LBIso (M.pull iG) (LB.triv G.left) :=
      _root_.GlobalTheory.GenericIsoAb.lbIso_of_generic_pullback W L G A.left A.hom φ hG hA.1 (M.pull iG) (LB.triv G.left) (pull_isLB hM _) hT q2
    exact (GlobalTheory.CechPic.iso_triv_iff _).1 q3.symm
  refine ⟨M, hM, axis _ _ ?_ h₁, axis _ _ ?_ h₂, iP⟩
  · exact lift_match hsq.1 hsq.2 _ _ _ _ (one_comm hA).symm (by simp)
  · exact lift_match hsq.1 hsq.2 _ _ _ _ (by simp) (one_comm hA).symm

end GlobalTheory.AxisTrivExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatPowEq
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtCover

theorem exists_faithfullyFlat_pow_eq :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ n : ℕ, 0 < n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D') (ψ : D →ₐ[R] D') (z : Pt A D'),
        (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x := by
  intro R _ A _ hA n hn D _ _ x
  obtain ⟨hf, hfl⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA n hn
  have hs := AbelianLimit.surjective_pow A hA n hn
  let m : A.left ⟶ A.left := ((𝟙 A) ^ n : A ⟶ A).left
  have : IsFinite m := hf
  have : Flat m := hfl
  have : Surjective m := hs
  let x₀ : Spec (CommRingCat.of D) ⟶ A.left := x.left
  let Y := Limits.pullback x₀ m
  have : IsAffine Y := isAffine_of_isAffineHom (Limits.pullback.fst x₀ m)
  let q : Spec Γ(Y, ⊤) ⟶ Spec (CommRingCat.of D) := Y.isoSpec.inv ≫ Limits.pullback.fst x₀ m
  let φ : CommRingCat.of D ⟶ Γ(Y, ⊤) := Spec.preimage q
  have hφ : Spec.map φ = q := Spec.map_preimage q
  have hff : φ.hom.FaithfullyFlat := (flat_and_surjective_SpecMap_iff φ).1 (by
    rw [hφ]; exact ⟨inferInstance, inferInstance⟩)
  letI : Algebra R Γ(Y, ⊤) := (φ.hom.comp (algebraMap R D)).toAlgebra
  let ψ : D →ₐ[R] Γ(Y, ⊤) := { φ.hom with commutes' := fun _ ↦ rfl }
  have hψ : (spOver ψ).left = q := hφ
  have hc : (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) ≫ m = (spOver ψ ≫ x).left := by
    rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc, Over.comp_left, hψ]
  let z : Pt A Γ(Y, ⊤) := Over.homMk (Y.isoSpec.inv ≫ Limits.pullback.snd x₀ m) (by
    rw [← Over.w (spOver ψ ≫ x), ← hc]
    simp only [Category.assoc]
    rw [Over.w ((𝟙 A) ^ n : A ⟶ A)])
  refine ⟨Γ(Y, ⊤), inferInstance, inferInstance, ψ, z, hff, ?_⟩
  rw [← Category.comp_id z, ← MonObj.comp_pow]
  exact Over.OverMorphism.ext hc

end GlobalTheory.PtCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAgreementLocusSeparated
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.EqLocus

theorem exists_fin (H : Scheme.{0}) (G : Over H) [IsSeparated G.hom] :
    ∀ (n : ℕ) (Z : Over H), IsFinite Z.hom → ∀ (a b : Fin n → (Z ⟶ G)),
      ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧
        ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro n
  induction n with
  | zero =>
    intro Z hZ a b
    refine ⟨Z, 𝟙 Z, hZ, fun k => k.elim0, fun T h _ => ⟨h, by simp, fun g hg => by simpa using hg⟩⟩
  | succ n ih =>
    intro Z hZ a b
    let e := equalizer.ι (a 0) (b 0)
    have hE : IsFinite (equalizer (a 0) (b 0)).hom := by
      rw [← Over.w e]
      infer_instance
    obtain ⟨Y, i', hY, hi', hu⟩ := ih _ hE (fun k => e ≫ a k.succ) (fun k => e ≫ b k.succ)
    refine ⟨Y, i' ≫ e, hY, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Category.assoc]
        rw [equalizer.condition]
      · simpa only [Category.assoc] using hi' k
    · intro T h hh
      let l : T ⟶ equalizer (a 0) (b 0) := equalizer.lift h (hh 0)
      have hl : l ≫ e = h := equalizer.lift_ι _ _
      obtain ⟨h'', hh'', hu''⟩ := hu T l (fun k => by
        simp only [← Category.assoc, hl]
        exact hh k.succ)
      refine ⟨h'', show h'' ≫ i' ≫ e = h by rw [← Category.assoc, hh'', hl], fun g hg => hu'' g ?_⟩
      change g ≫ i' ≫ e = h at hg
      change g ≫ i' = l
      apply (cancel_mono e).1
      rw [Category.assoc, hg, hl]

theorem exists_finite_eqLocus : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom →
    ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧
      (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) →
        ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro H Z G hZ hG Ix _ a b
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin Ix
  obtain ⟨Y, i, hY, hi, hu⟩ := exists_fin H G n Z hZ (fun k => a (σ.symm k)) (fun k => b (σ.symm k))
  refine ⟨Y, i, hY, fun k => by simpa using hi (σ k), fun T h hh => hu T h (fun k => hh _)⟩

end GlobalTheory.EqLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGloballyGeneratedAmplePowerToroidalPullbac
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullPowGen

theorem exists_isGenerated_and_isAmpleLB : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (Z S : Scheme.{0}) (z : Z ⟶ Sp o) (π : S ⟶ Z) (OZ : LB Z) (W M : LB S) (a N : ℕ), IsProjOver z → OZ.IsLB → GlobalTheory.IsAmpleLB OZ → W.IsLB → M.IsLB → 1 ≤ a → 1 ≤ N → LBIso (lbPow W N) (lbPow (OZ.pull π) a) → (∃ k₀ : ℕ, ∀ k, k₀ ≤ k → GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow (OZ.pull π) k) M)) → ∃ N' : ℕ, 1 ≤ N' ∧ GlobalTheory.IsGenerated (lbPow W N') ∧ ∃ k : ℕ, GlobalTheory.IsAmpleLB (GlobalTheory.CechPic.tens (lbPow W (N' * k)) M) := by
  intro o _ _ Z S z π OZ W M a N _ hO hA hW hM ha hN H ⟨k₀, hk₀⟩
  obtain ⟨b, hb, hgen⟩ := hA.exists_isGenerated_pow
  have hP : (OZ.pull π).IsLB := LB.isLB_pull hO π
  have hcls : N • CechPic.cls W hW = a • CechPic.cls (OZ.pull π) hP := by
    have := (CechPic.cls_eq_iff (isLB_lbPow hW N) (isLB_lbPow hP a)).2 H
    rwa [CechPic.cls_lbPow hW, CechPic.cls_lbPow hP] at this
  refine ⟨N * b, Nat.mul_pos hN hb, ?_, k₀, ?_⟩
  · have hg := (hgen.pull π).pow a
    have hOb := isLB_lbPow hO b
    have hPb := LB.isLB_pull hOb π
    refine hg.of_lbIso (isLB_lbPow hW _) ((CechPic.cls_eq_iff (isLB_lbPow hW _) hg.isLB).1 ?_)
    have e : CechPic.cls ((lbPow OZ b).pull π) hPb = b • CechPic.cls (OZ.pull π) hP := by
      rw [CechPic.cls_pull hOb, CechPic.cls_pull hO, CechPic.cls_lbPow hO, map_nsmul]
    rw [CechPic.cls_lbPow hW, CechPic.cls_lbPow hPb, e, mul_nsmul, hcls, ← mul_nsmul, ← mul_nsmul, mul_comm]
  · have hamp := hk₀ (a * (b * k₀)) (Nat.le_mul_of_pos_left _ ha |>.trans' (Nat.le_mul_of_pos_left _ hb))
    have hT := CechPic.isLB_tens (isLB_lbPow hW (N * b * k₀)) hM
    refine hamp.of_lbIso hT ((CechPic.cls_eq_iff hT hamp.isLB).1 ?_)
    rw [CechPic.cls_tens (isLB_lbPow hW _) hM, CechPic.cls_tens (isLB_lbPow hP _) hM, CechPic.cls_lbPow hW,
      CechPic.cls_lbPow hP, Nat.mul_assoc, mul_nsmul, hcls, ← mul_nsmul]

end GlobalTheory.PullPowGen
end

