module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0030
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0029
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0028
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhTwoValHolds
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0025
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0012
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqGlue
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0002
public import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0013

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndVerb
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj CIndFrFix

def FrTruncFixBSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y),
    ∃ (e' : ∀ m, FrTy y C.d C.x m) (hfr : IsFrame y C.d C.x C.B.G.F C.B.A.act C.B.ph1 C.B.ph2 C.B.sy C.B.ad e')
      (hrig : LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (eL y C.d C.x C.B.A.act e' C.wP 0)
          (homAt y.x (jetAug : Jet S (Fin 1 × Fin C.d) 0 →ₐ[S] S)).left)
        (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (overAt y.x S) 1))
      (cc : ℕ → Fin C.d → Fin C.d → S),
      FrTruncC y { C with e := e', frame := hfr, rig0 := hrig } ∧ cc 0 = 0 ∧ (∀ m i j, cc m i j = cc m j i) ∧
      (∀ m (ℓ ℓ' : Lt1 Dw), ∑ i, ∑ j, cc m i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 →
        ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) ∧
      ∀ m, ∃ u : (Jet S (Fin 2 × Fin C.d) m)ˣ,
        (u : Jet S (Fin 2 × Fin C.d) m) = psJet m (expP (-bilL C.B.G (cc m))) ∧
        LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ (e' m) (scaleGen (Xo := Xo) _ _ (unitΓ u) (C.e m))

def HarmInvSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y)
    (cc : Fin C.d → Fin C.d → S), (∀ i j, cc i j = cc j i) →
    (∀ ℓ ℓ' : Lt1 Dw, ∑ i, ∑ j, cc i j * C.uvec ℓ i * C.uvec ℓ' j ≠ 0 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) →
    ∀ (k n D : ℕ) (f f' : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S),
    (∀ b, psJet D (f' b) = psJet D (f b * expP ((k : S) • diagL C.B H.w0 cc))) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      (∀ m ∈ P.support, m.degree ≤ D) → chartVal C k f' P = chartVal C k f P

theorem chartIndep2_verb (hTr : ChartIndepTruncSt) (hFix : FrTruncFixBSt) (hGerm : GermFixSt)
    (hInv : HarmInvSt) : ChartIndepSt2 := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C C' k n F f f' hf hf' a P hP

  have hD : ∀ m ∈ P.support, m.degree ≤ P.support.sup (fun m => m.degree) :=
    fun m hm => Finset.le_sup (f := fun m => m.degree) hm

  have step : ∀ (C₀ : ChartAt Xo c y) (f₀ : Fin n → MvPowerSeries (Fin 1 × Fin C₀.d) S),
      (∀ b, IsGerm y C₀.d C₀.x C₀.B.A.act C₀.e C₀.wP k (F b) (f₀ b)) →
      ∃ (C₁ : ChartAt Xo c y) (f₁ : Fin n → MvPowerSeries (Fin 1 × Fin C₁.d) S),
        FrTruncC y C₁ ∧ (∀ b, IsGerm y C₁.d C₁.x C₁.B.A.act C₁.e C₁.wP k (F b) (f₁ b)) ∧
        chartVal C₁ k f₁ P = chartVal C₀ k f₀ P := by
    intro C₀ f₀ hf₀
    obtain ⟨e', hfr, hrig, cc, hT1, -, hsym, hbal, hu⟩ := hFix E H Dw l Xo c hstar S y C₀
    choose f₁ hf₁ hj using fun b =>
      hGerm E H Dw l Xo c hstar S y C₀ e' hfr hrig cc hT1 hu k (F b) (f₀ b) (hf₀ b)
    exact ⟨{ C₀ with e := e', frame := hfr, rig0 := hrig }, f₁, hT1, hf₁,
      hInv E H Dw l Xo c hstar S y C₀ (cc (P.support.sup fun m => m.degree)) (hsym _) (hbal _) k n
        (P.support.sup fun m => m.degree) f₀ f₁ (fun b => hj b _) a P hP hD⟩
  obtain ⟨C₁, f₁, hC₁, hf₁, e₁⟩ := step C f hf
  obtain ⟨C₂, f₂, hC₂, hf₂, e₂⟩ := step C' f' hf'
  rw [← e₁, ← e₂]
  exact hTr E H Dw l Xo c hstar S y C₁ C₂ hC₁ hC₂ k n F f₁ f₂ hf₁ hf₂ a P hP

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpGauge
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGauge

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

theorem expGaugeOf_of (hA : ExpActOfSt) : ExpGaugeOfSt := by
  intro E _ _ _ H Dw l Xo c _ hs S _ _ _ y C htr φ hφ hx
  have hact : ∀ (a : 𝓞 E) (j : Fin C.d), MvPowerSeries.subst (fun p : Fin 1 × Fin C.d => φ p.2) (C.B.A.act a j) =
      MvPowerSeries.subst (ExpGU.actPS (Dw := Dw) c a) (φ j) := hA E H Dw l Xo c S y C φ hφ
  obtain ⟨τ, u, _, hτc, hu, hgen, hof⟩ := ExpGA.exists_eG C φ hφ.const
  refine ⟨ExpGA.eG C φ τ u, ⟨hgen, fun m => ExpGB.trunc_eG C htr φ τ u hτc hu m,
    ExpGB.rig_eG C φ hφ.const τ u hτc hu, fun a => ?_⟩, hof⟩
  have hbb : H.bar (H.bar a) = a := by rw [← hs, ← hs, star_star]
  obtain ⟨wLa, hwa, hra⟩ := ExpGD.exists_adRel C a
  obtain ⟨wLb, hwb, hrb⟩ := ExpGD.exists_adRel C (H.bar a)
  obtain ⟨β, hβ, hβ0, hβv⟩ := ExpGE.exists_beta C.wP C.prim a hbb wLa hwa wLb hwb
  exact ⟨β, hβ, hβ0, fun m => ExpGL.coc_chart ExpGJPh1.phOneVal_holds ExpGJ.phTwoVal_holds ExpGJ.adVal
    ExpGU.unitId ExpGO.bqOrigin hs C φ hφ hx hact τ u hτc hu a wLa hra wLb hrb β hβv m⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGauge
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqChart

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

theorem epsMul_zero {S : Type} [CommRing S] :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · first
    | simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    | (simp [epsMul]; rfl)
  · first
    | simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
    | (simp [epsMul]; rfl)

theorem epsMul_one {S : Type} [CommRing S] : epsMul (1 : S) = RingHom.id (DualNumber S) := by
  refine RingHom.ext fun x => TrivSqZeroExt.ext ?_ ?_ <;> simp [epsMul]

theorem fst_comp_tan {S : Type} [CommRing S] (d : ℕ) (j : Fin d) :
    (TrivSqZeroExt.fstHom S S S).comp
      (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin d) (0 + 1) →ₐ[S] DualNumber S) = jetAug := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  first
  | (simp only [AlgHom.comp_apply, Formalism.L2.Pj.jetTan, Formalism.L2.Pj.jetAug, Formalism.L2.Pj.liftJet, Ideal.Quotient.liftₐ_apply,
      Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_toRingHom]
     erw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk]
     by_cases h : i = (0, j) <;> simp [h])
  | (show TrivSqZeroExt.fst ((MvPolynomial.aeval _) (MvPolynomial.X i)) = (MvPolynomial.aeval _) (MvPolynomial.X i)
     by_cases h : i = (0, j) <;> simp [h])

theorem comp_one_gen {X : Scheme.{0}} {Y Z M : Over X} [GrpObj M] (f : Y ⟶ Z) : f ≫ (1 : Z ⟶ M) = 1 := by
  first
  | simp
  | (rw [MonObj.Hom.one_def, MonObj.Hom.one_def, ← Category.assoc]; congr 1; exact toUnit_unique _ _)
  | simp [MonObj.Hom.one_def]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S]

theorem tan_eq (y : FrPt Xo c S) (x : ∀ m, jO y (dL Dw) m 1 ⟶ Xo.univ.t.G) (hx : IsExpChart y x)
    (j : Fin (dL Dw)) :
    (Formalism.L2.Pj.homAt y.x (jetTan ((0 : Fin 1), j) : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left =
      y.u ((ltIdx Dw).symm j).1 ((ltIdx Dw).symm j).2 := by
  obtain ⟨u, hu, hprod⟩ := hx.tan ((ltIdx Dw).symm j)
  have hj : ltIdx Dw ((ltIdx Dw).symm j) = j := Equiv.apply_symm_apply _ _
  have hone : ∀ i, i ≠ j → u i = 1 := by
    intro i hi
    have e : u i = Formalism.L2.Pj.homAt y.x (Algebra.ofId S (DualNumber S)) ≫
        (Formalism.L2.Pj.homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] S) ≫ x 1) := by
      apply Over.OverMorphism.ext
      simp only [hu i, hj, if_neg hi, epsMul_zero, ← fst_comp_tan (dL Dw) i]
      simp only [Over.comp_left, Formalism.L2.Pj.homAt, Over.homMk_left]
      simp only [spMap, ← Category.assoc]
      congr 1
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl
    rw [e, hx.zero 1, comp_one_gen]
  have huj : (u j).left = (Formalism.L2.Pj.homAt y.x (jetTan ((0 : Fin 1), j) :
      Jet S (Fin 1 × Fin (dL Dw)) (0 + 1) →ₐ[S] DualNumber S) ≫ x 1).left := by
    simp [hu j, hj, epsMul_one, spMap, CommRingCat.ofHom_id, Spec.map_id]
  rw [← hprod, ← huj]
  congr 1
  rw [List.prod_ofFn]
  exact (Finset.prod_eq_single j (fun i _ hi => hone i hi) (fun h => absurd (Finset.mem_univ j) h)).symm

theorem expUniqTan : ExpUniqTanSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x x' hx hx'
  refine ExpUniqGlue.expUniq E H Dw l Xo c S y (dL Dw) x x' ⟨hx.trunc, hx.law⟩ ⟨hx'.trunc, hx'.law⟩ ?_
  intro j
  apply Over.OverMorphism.ext
  rw [tan_eq y x hx j, tan_eq y x' hx' j]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpUniqChart
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.KillAddVal
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace KAVal

theorem degree_eq_two {σ : Type} (e : σ →₀ ℕ) (he : e.degree = 2) :
    ∃ s t, e = Finsupp.single s 1 + Finsupp.single t 1 := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finsupp.ext h)
  have hle : Finsupp.single s 1 ≤ e := by
    intro x
    by_cases hx : x = s
    · subst hx
      simp only [Finsupp.single_eq_same]
      omega
    · simp [Ne.symm hx]
  have hsplit : e = (e - Finsupp.single s 1) + Finsupp.single s 1 := (tsub_add_cancel_of_le hle).symm
  have he' : (e - Finsupp.single s 1).degree = 1 := by
    have h2 := congrArg Finsupp.degree hsplit
    rw [map_add (f := _), Finsupp.degree_single] at h2
    omega
  obtain ⟨t, ht⟩ := Formalism.FG.SolveVAux.degree_eq_one (e - Finsupp.single s 1) he'
  refine ⟨s, t, ?_⟩
  rw [hsplit, ht, add_comm]

end KAVal

namespace KAVal

variable {S : Type} [CommRing S] {N : ℕ}

def qβ (q : MvPowerSeries (Fin 1 × Fin N) S) (i j : Fin N) : S :=
  if i ≤ j then coeff (Finsupp.single ((0 : Fin 1), i) 1 + Finsupp.single ((0 : Fin 1), j) 1) q else 0

theorem coeff_XX (e : Fin 1 × Fin N →₀ ℕ) (s t : Fin 1 × Fin N) :
    coeff e (X s * X t : MvPowerSeries (Fin 1 × Fin N) S) =
      if e = Finsupp.single s 1 + Finsupp.single t 1 then 1 else 0 := by
  rw [X, X, monomial_mul_monomial, mul_one, coeff_monomial]

theorem single_add_single_at (a b x : Fin 1 × Fin N) :
    (Finsupp.single a 1 + Finsupp.single b 1 : Fin 1 × Fin N →₀ ℕ) x = (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
  simp [Finsupp.single_apply]

theorem quad_form (q : MvPowerSeries (Fin 1 × Fin N) S) (hq0 : constantCoeff q = 0)
    (hq2 : ∀ m, coeff m q ≠ 0 → m.degree = 2) :
    q = ∑ i, ∑ j, C (qβ q i j) * X ((0 : Fin 1), i) * X ((0 : Fin 1), j) := by
  classical
  ext e
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, mul_assoc, coeff_C_mul, coeff_XX]
  by_cases hdeg : e.degree = 2
  · obtain ⟨s, t, hst⟩ := degree_eq_two e hdeg
    obtain ⟨o1, p⟩ := s
    obtain ⟨o2, p'⟩ := t
    have h1 : o1 = 0 := Subsingleton.elim _ _
    have h2 : o2 = 0 := Subsingleton.elim _ _
    subst h1 h2

    obtain ⟨a, b, hab, hee⟩ : ∃ a b : Fin N, a ≤ b ∧
        e = Finsupp.single ((0 : Fin 1), a) 1 + Finsupp.single ((0 : Fin 1), b) 1 := by
      rcases le_total p p' with h | h
      · exact ⟨p, p', h, hst⟩
      · exact ⟨p', p, h, by rw [hst, add_comm]⟩
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [if_pos hee, mul_one, qβ, if_pos hab, ← hee]
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        have := congrArg (fun f => f ((0 : Fin 1), b)) (hee.symm.trans h)
        simp only [single_add_single_at, Prod.mk.injEq, true_and] at this
        split_ifs at this <;> simp_all
      · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : e = Finsupp.single ((0 : Fin 1), i) 1 + Finsupp.single ((0 : Fin 1), j) 1
      · have hi' := congrArg (fun f => f ((0 : Fin 1), i)) (hee.symm.trans h)
        have hj' := congrArg (fun f => f ((0 : Fin 1), j)) (hee.symm.trans h)
        simp only [single_add_single_at] at hi' hj'
        have hbi : b = i := by
          by_contra hb
          simp [Ne.symm hi, hb] at hi'
          split_ifs at hi' <;> omega
        subst hbi
        have haj : a = j := by
          by_contra ha
          split_ifs at hj' <;> simp_all
        subst haj
        have hlt : ¬ b ≤ a := fun h' => hi (le_antisymm h' hab)
        rw [qβ, if_neg hlt, zero_mul]
      · rw [if_neg h, mul_zero]
    · simp
  · have hz : coeff e q = 0 := by
      by_contra h
      exact hdeg (hq2 e h)
    rw [hz]
    symm
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    apply hdeg
    rw [map_add (f := _), Finsupp.degree_single, Finsupp.degree_single]

end KAVal

namespace KAVal

variable {S : Type} [CommRing S] [Algebra ℚ S]

theorem rename_expS {σ τ : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    (h : MvPowerSeries σ S) (hh : constantCoeff h = 0) :
    MvPowerSeries.rename f (PowerSeries.subst h (PowerSeries.exp S)) =
      PowerSeries.subst (MvPowerSeries.rename f h) (PowerSeries.exp S) := by
  have ha : HasSubst (fun _ : Unit => h) := hasSubst_of_constantCoeff_zero fun _ => hh
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply ha (HasSubst.X_comp _)]

theorem prod_expS {τ : Type} {ι : Type} (s : Finset ι) (x : ι → MvPowerSeries τ S)
    (hx : ∀ i, constantCoeff (x i) = 0) :
    ∏ i ∈ s, PowerSeries.subst (x i) (PowerSeries.exp S) = PowerSeries.subst (∑ i ∈ s, x i) (PowerSeries.exp S) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one]
    simp
  | insert a s ha ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
      ← Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.expS_add _ _ (hx a) (by rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hx i)]

end KAVal

theorem killAddVal_of (hPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), PsiCoverSt H) :
    KillAddValSt := by
  intro E _ _ _ H Dw l c S _ _ _ k n g q hq0 hq2 hqp a P hP
  classical
  set β := KAVal.qβ q with hβdef
  have hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j h
    simp only [hβdef, KAVal.qβ] at h
    split_ifs at h with hij
    · apply hqp ((ltIdx Dw).symm i) ((ltIdx Dw).symm j)
      simpa using h
    · exact absurd rfl h
  let ren : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S →ₐ[S] MvPowerSeries (Fin n × Fin (dL Dw)) S :=
    fun b => MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
  have hq_form := KAVal.quad_form q hq0 hq2
  have hren_q : ∀ b, ren b q = ∑ i, ∑ j, MvPowerSeries.C (β i j) * MvPowerSeries.X (b, i) * MvPowerSeries.X (b, j) := by
    intro b
    conv_lhs => rw [hq_form]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [ren, map_sum, map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
    rfl
  have hquad : (TB.quadCol (n := n) β : MvPowerSeries (Fin n × Fin (dL Dw)) S) = ∑ b, ren b q := by
    unfold TB.quadCol
    exact Finset.sum_congr rfl fun b _ => (hren_q b).symm
  have hcq : ∀ b, constantCoeff (ren b (-((k : S) • q))) = 0 := by
    intro b
    have : constantCoeff (-((k : S) • q)) = 0 := by simp [hq0]
    rw [MvPowerSeries.rename_eq_subst]
    exact constantCoeff_subst_eq_zero (HasSubst.X_comp _) (fun _ => by simp) this
  have hkey : ∏ b, ren b (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) =
      Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) β) * ∏ b, ren b (g b) := by
    simp only [map_mul, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_congr rfl fun b _ => KAVal.rename_expS _ _ (by simp [hq0]), KAVal.prod_expS _ _ hcq, Germ.FB.expS,
      hquad, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_neg, map_smul, neg_smul]
  have hPC := prodCol_holds E H Dw S n
  calc ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, expVal (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) (colOf m b)
      = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) β) * ∏ b, ren b (g b)) m := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← hkey, hPC]
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * mVal (∏ b, ren b (g b)) m :=
        killAddValCol_of ReciprocityTheory.ChartRestriction.G.TB.kernel_additive E H Dw l c S k n _ β (hPsi E H) hβ a P hP
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hPC]

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

