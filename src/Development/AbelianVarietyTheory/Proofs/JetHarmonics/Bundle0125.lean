module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0120
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecLinIffComb
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHarishChandraParamOfTypeOfUnitaryW
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem besType_continuous_blockW (k r : ℕ) : Continuous (PI.UpqRep.blockW k r) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold PI.UpqRep.blockW
  split_ifs
  · exact continuous_apply_apply _ _
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const

theorem besType_hcParam : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → Q.IsType k r z π u → ∃ u₀, PI.UpqRep.IsHCTypeW k r z u₀ π := by
  intro k r Wp _ _ _ z π u hz hT hπ
  obtain ⟨g, hg, hin, honto⟩ := _root_.GlobalTheory.BesselFrame.frame_exists k r z hz hT
  obtain ⟨hnt, ⟨h1, hmul⟩, hcont, hnorm, hirr, -⟩ := hπ
  have hgg : g * g⁻¹ = 1 := PI.HwUniqW.mul_inv_UH hg.1
  have hgg' : g⁻¹ * g = 1 := PI.HwUniqW.inv_mul_UH' hg.1
  have hc : Continuous (fun x : Matrix (Fin k) (Fin k) ℂ => g * PI.UpqRep.blockW k r x * g⁻¹) :=
    (continuous_const.matrix_mul (besType_continuous_blockW k r)).matrix_mul continuous_const
  haveI := hnt
  obtain ⟨u₀, hu₀⟩ := _root_.GlobalTheory.UnitaryHighestWeight.exists_isHCTypeU k Wp (fun x => π (g * PI.UpqRep.blockW k r x * g⁻¹))
    (by
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · show π (g * PI.UpqRep.blockW k r 1 * g⁻¹) = 1
        rw [PI.HwUniqW.blockW_one, Matrix.mul_one, hgg]
        exact h1
      · intro x hx y hy
        have e : g * PI.UpqRep.blockW k r (x * y) * g⁻¹ =
            g * PI.UpqRep.blockW k r x * g⁻¹ * (g * PI.UpqRep.blockW k r y * g⁻¹) := by
          rw [← PI.HwUniqW.blockW_mul]
          calc g * (PI.UpqRep.blockW k r x * PI.UpqRep.blockW k r y) * g⁻¹
              = g * PI.UpqRep.blockW k r x * (g⁻¹ * g) * PI.UpqRep.blockW k r y * g⁻¹ := by
                rw [hgg', Matrix.mul_one]; simp only [Matrix.mul_assoc]
            _ = _ := by simp only [Matrix.mul_assoc]
        show π (g * PI.UpqRep.blockW k r (x * y) * g⁻¹) = _
        rw [e]
        exact hmul _ (hin x hx) _ (hin y hy)
      · intro x hx v
        exact hnorm _ (hin x hx) v
      · intro v
        have h2 : ContinuousOn (fun x : Matrix (Fin k) (Fin k) ℂ => π (g * PI.UpqRep.blockW k r x * g⁻¹))
            (PI.UpqRep.UJset (PI.UpqRep.allPos k)) :=
          hcont.comp hc.continuousOn (fun x hx => hin x hx)
        exact h2.clm_apply continuousOn_const)
    (by
      intro S hS
      refine hirr S ?_
      intro h hh v hv
      obtain ⟨x, hx, rfl⟩ := honto h hh
      exact hS x hx v hv)
  exact ⟨u₀, g, hg, hu₀⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIdempotentFrobeniusOrbitUnramified
section
open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.UnrIdem

theorem exists_idem (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l.Prime)
    (hd : ¬ (l : ℤ) ∣ NumberField.discr E) (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hlP : (l : 𝓞 E) ∈ P) :
    ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (l : 𝓞 E) * y) ∧ ε - 1 ∈ P ∧ ∀ x ∈ P, ∃ y, ε * x = (l : 𝓞 E) * y := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hun : Algebra.IsUnramifiedAt ℤ P :=
    (NumberField.not_dvd_discr_iff_forall_mem E (𝓞 E) hp).mp hd P hP (by simpa using hlP)
  have hov : P.LiesOver (Ideal.span {(l : ℤ)}) :=
    (Ideal.liesOver_span_iff hP.ne_top hp).mpr (by simpa using hlP)
  have hmap : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) = Ideal.span {(l : 𝓞 E)} := by
    rw [Ideal.map_span]; simp
  have hl0 : (l : 𝓞 E) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hne : (Ideal.span {(l : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := by
    rw [hmap]; simpa using hl.ne_zero
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hl0 (by simpa using hlP)
  have := hP.isMaximal hP0
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hne P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count _ _ hne,
    Ideal.ramificationIdx_eq_one P ℤ, pow_one, hmap] at h₂
  obtain ⟨p, hpP, q, hqQ, hpq⟩ := Submodule.mem_sup.mp ((Ideal.eq_top_iff_one _).mp h₁)
  have key : ∀ x ∈ P, ∃ y, q * x = (l : 𝓞 E) * y := by
    intro x hx
    have : x * q ∈ Ideal.span {(l : 𝓞 E)} := h₂ ▸ Ideal.mul_mem_mul hx hqQ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp this
    exact ⟨y, by rw [mul_comm, hy]⟩
  have hq1 : q - 1 ∈ P := by
    have : q - 1 = -p := by rw [← hpq]; ring
    rw [this]; exact P.neg_mem hpP
  refine ⟨q, ?_, hq1, key⟩
  obtain ⟨y, hy⟩ := key _ hq1
  exact ⟨y, by rw [← hy]; ring⟩

variable {C : Type} [Field C] {V : VF C}

theorem ge_int {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  have h1 : IsIntegral (Valuation.integer (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))) x := hx.tower_top
  exact (Valuation.integer.integers (V.v : Valuation C (Multiplicative (WithTop ℝ)ᵒᵈ))).mem_of_integral h1

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) := V.v.map_lt_add ha hb

theorem mm_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left (by simpa using ha))

def ker (V : VF C) {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : Ideal R where
  carrier := {x | V.MM (f x)}
  add_mem' := fun {a b} ha hb => by
    show V.MM (f (a + b))
    rw [map_add (f := _)]; exact GlobalTheory.UnrIdem.mm_add ha hb
  zero_mem' := by
    show V.MM (f 0)
    simp [VF.MM]
  smul_mem' := fun c x hx => by
    show V.MM (f (c * x))
    rw [map_mul]; exact mm_mul (hf c) hx

theorem ker_isPrime {R : Type} [CommRing R] (f : R →+* C) (hf : ∀ x, V.Ge 0 (f x)) : (ker V f hf).IsPrime := by
  refine ⟨(Ideal.ne_top_iff_one _).mpr ?_, fun {a b} hab => ?_⟩
  · show ¬ V.MM (f 1)
    simp [VF.MM]
  · change V.MM (f (a * b)) at hab
    show V.MM (f a) ∨ V.MM (f b)
    have ha := hf a
    have hb := hf b
    unfold VF.MM VF.Ge at *
    rw [map_mul, V.v.map_mul] at hab
    by_contra hc
    push Not at hc
    exact absurd hab (not_lt.mpr (add_nonpos hc.1 hc.2))

end GlobalTheory.UnrIdem

open GlobalTheory.UnrIdem in
theorem GlobalTheory.exists_idempotent_of_unramified_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (lv : Level H) (c : Coeff lv) (T : CDVR) (io : c.F →+* T.Fr) (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι → ¬ (V.l : ℤ) ∣ NumberField.discr E → ∀ (d : ℕ) [NeZero d] (tau : ZMod d → (E →+* ℂ)), FrobOrd V io ι tau → ∃ ε : 𝓞 E, (∃ y, ε * ε - ε = (V.l : 𝓞 E) * y) ∧ (∀ a, V.MM (emA3 io ι (tau a) ε - 1)) ∧ ∀ x : 𝓞 E, (∀ a, V.MM (emA3 io ι (tau a) x)) → ∃ y, ε * x = (V.l : 𝓞 E) * y := by
  intro E _ _ _ H lv c T io C _ _ V ι _ hd d _ tau hF
  have hint : ∀ τ x, V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_int ((RingOfIntegers.isIntegral x).map (emA3 io ι τ).toIntAlgHom)
  have hstep : ∀ x s, V.MM (emA3 io ι (tau s) x) → V.MM (emA3 io ι (tau (s + 1)) x) := by
    intro x s hs
    have h1 := hF s x
    have h2 : V.MM (emA3 io ι (tau s) x ^ V.l) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero V.l_prime.ne_zero
      rw [hk, pow_succ]
      exact mm_mul ((hint _ _).pow k) hs
    simpa using GlobalTheory.UnrIdem.mm_add h1 h2
  have hall : ∀ x, V.MM (emA3 io ι (tau 0) x) → ∀ a, V.MM (emA3 io ι (tau a) x) := by
    intro x h0 a
    have : ∀ n : ℕ, V.MM (emA3 io ι (tau (n : ZMod d)) x) := by
      intro n
      induction n with
      | zero => simpa using h0
      | succ n ih => push_cast; exact hstep x _ ih
    simpa using this a.val
  have hP := ker_isPrime (V := V) (emA3 io ι (tau 0)) (hint _)
  obtain ⟨ε, h1, h2, h3⟩ := exists_idem E V.l V.l_prime hd (ker V (emA3 io ι (tau 0)) (hint _)) (by
    show V.MM (emA3 io ι (tau 0) (V.l : 𝓞 E))
    rw [map_natCast]
    unfold VF.MM
    rw [V.v_l]
    exact zero_lt_one)
  refine ⟨ε, h1, fun a => ?_, fun x hx => h3 x (hx 0)⟩
  have := hall _ h2 a
  rwa [map_sub, map_one] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLevelPointEqOfKilledByHalfLevel
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem LevelPoints.comp_act_natCast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {S : Scheme.{0}} (t : SAB H S) {T : Over S} (x : T ⟶ t.G) (n : ℕ) :
    x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
  induction n with
  | zero =>
    have h := t.act.add 0 0
    rw [add_zero] at h
    have h0 : t.act.act 0 = 1 := by simpa using h
    rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
  | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]

theorem exists_levPt_eq_of_killedBy : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra c.F F] (yF : FrPt Xo c F) (t : ptO Xo yF.x ⟶ Xo.univ.t.G), KilledBy Xo l.Mb t → ∃ a : Dw.La, levPt Xo yF.x a = t := by
  intro E _ _ _ H Dw l Xo c F _ _ _ yF t ht
  obtain ⟨-, I, -, -, hI⟩ := Xo.univ.geom F yF.x (Spec.preimage (yF.x ≫ Xo.s)).hom (Spec.map_preimage _).symm
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have hpow : t ^ l.M = 1 := by
    rw [← LevelPoints.comp_act_natCast]
    exact ht _ (LevelPoints.natCast_mem l)
  obtain ⟨a, ha⟩ := (I.onto l.M hM t).1 hpow
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (l.coprime ▸ Submodule.mem_top :
    (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
  refine ⟨v • a, (hI _ (Submodule.smul_mem_smul hv Submodule.mem_top)).trans ?_⟩
  have h1 : I.ev l.M (u • a) = 1 := by
    rw [I.lin, ha]
    exact ht u hu
  have h2 := I.add l.M (u • a) (v • a)
  rw [← add_smul, huv, one_smul, h1, _root_.one_mul] at h2
  exact h2.symm.trans ha

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLiftPointTranslationFieldPoint
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_translT_general {S S' : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] (f : S' ⟶ S)
    (P : Over S') (x : P ⟶ (Over.pullback f).obj G) (T : Over S) (e : T.left ⟶ P.left) (r g : T ⟶ G)
    (hg : g.left = e ≫ x.left ≫ pullback.fst G.hom f) :
    ∃ ρ : T.left ⟶ (P ⊗ (Over.pullback f).obj G).left,
      ρ ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      ρ ≫ (snd P ((Over.pullback f).obj G)).left ≫ pullback.fst G.hom f = r.left ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (fst P ((Over.pullback f).obj G)).left = e ∧
      (ρ ≫ (translT ((Over.pullback f).obj G) x).left) ≫ (snd P ((Over.pullback f).obj G)).left ≫
        pullback.fst G.hom f = (r * g).left := by
  have hx : x.left ≫ pullback.snd G.hom f = P.hom := Over.w x
  have hT : T.hom = (e ≫ P.hom) ≫ f := by
    rw [← Over.w g, hg, ← hx]
    simp only [Category.assoc, pullback.condition]
  let T' : Over S' := Over.mk (e ≫ P.hom)
  let e' : T' ⟶ P := Over.homMk e rfl
  let r' : T' ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift r.left (e ≫ P.hom) ((Over.w r).trans hT)) (pullback.lift_snd _ _ _)
  have hr' : r'.left ≫ pullback.fst G.hom f = r.left := pullback.lift_fst _ _ _
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans hT)
  have hU : ∀ z : T ⟶ G, (U ≫ z).left = z.left := fun z => Category.id_comp _
  have h1 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ fst _ _ = e' := by
    simp [translT]
  have h2 : lift e' r' ≫ translT ((Over.pullback f).obj G) x ≫ snd _ _ = (e' ≫ x) * r' := by
    simp only [translT, translPt, lift_snd, Hom.mul_def]
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have h3 := (isGrpPullback_pullback G f).2 T' (e' ≫ x) r' (U ≫ g) (U ≫ r)
    ((hU g).trans (hg.trans (Category.assoc _ _ _).symm)) ((hU r).trans hr'.symm)
  refine ⟨(lift e' r').left, congrArg (fun z => z.left) (lift_fst e' r'), ?_, ?_, ?_⟩
  · exact ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z : T' ⟶ (Over.pullback f).obj G => z.left ≫ pullback.fst G.hom f) (lift_snd e' r'))).trans hr'
  · exact (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h1)
  · have h4 : ((lift e' r').left ≫ (translT ((Over.pullback f).obj G) x).left) ≫
        (snd P ((Over.pullback f).obj G)).left = ((e' ≫ x) * r').left :=
      (Category.assoc _ _ _).trans (congrArg (fun z => z.left) h2)
    refine ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ pullback.fst G.hom f) h4)).trans (h3.symm.trans ?_)
    rw [← MonObj.comp_mul, hU, mul_comm]

theorem exists_lift_translT : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] [Algebra (FractionRing R) F] (x : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (T : Over (Spec (CommRingCat.of R))) (e : T.left ⟶ Spec (CommRingCat.of F)) (r g : T ⟶ G), g.left = e ≫ x.left ≫ pullback.fst G.hom (jK R) → ∃ ρ : T.left ⟶ (UnifPre.GF (G := G) F).left, ρ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ ρ ≫ UnifPre.gFK (G := G) F = r.left ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = e ∧ (ρ ≫ (translT ((Over.pullback (jK R)).obj G) x).left) ≫ UnifPre.gFK (G := G) F = (r * g).left := by
  intro R _ _ G _ _ F _ _ x T e r g hg
  exact exists_lift_translT_general G (jK R) (TFK (R := R) F) x T e r g hg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivUniformisedPointsUniversal
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PtTie

theorem exists_mulEquiv_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (Z : Over S') :
    ∃ e : (Z ⟶ G') ≃* (Over.mk (Z.hom ≫ f) ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  let Φ₀ : (Z ⟶ G') → (Over.mk (Z.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      show (x.left ≫ φ) ≫ G.hom = Z.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let Φ : (Z ⟶ G') →ₙ* (Over.mk (Z.hom ≫ f) ⟶ G) :=
    ⟨Φ₀, fun x y => Over.OverMorphism.ext (h.2 Z x y (Φ₀ x) (Φ₀ y) rfl rfl).symm⟩
  have hinj : Function.Injective Φ := fun x y hxy =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y]))
  have hsurj : Function.Surjective Φ := fun x₀ =>
    ⟨Over.homMk (h.1.lift x₀.left Z.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  exact ⟨MulEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun x => rfl⟩


open scoped CategoryTheory.Obj in
theorem exists_mulEquiv_ptTieF : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (I : IntData Xo c T io y) (P : PELUnif (maximalIdeal T.V) I.G) (F : Type) [Field F] [Algebra T.Fr F] (xF : Sp F ⟶ Xo.X), xF = spMap (algebraMap T.Fr F) ≫ (letI := io.toAlgebra; y.x) → ∃ e : (TFK (R := T.V) F ⟶ P.A.A) ≃* (ptO Xo xF ⟶ Xo.univ.t.G), (∀ x b, PtTieF I P F xF x b ↔ b = e x) ∧ ∀ (a : 𝓞 E) x, e (x ≫ P.oA.act a) = e x ≫ Xo.univ.t.act.act a := by
  intro E _ _ _ H Dw l Xo c T io y I P F _ _ xF hxF
  letI := H.starRing
  subst hxF
  have := P.U.gen_hom
  have gpG : IsGrpPullback P.A.A I.G.G (jK T.V) (P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V)) := by
    have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback I.G.G (jK T.V))).congr
      (Category.id_comp _) rfl
  have actA : ∀ a, (P.oA.act a).left ≫ P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) =
      P.U.gen.inv.left ≫ pullback.fst I.G.G.hom (jK T.V) ≫ (I.G.act.act a).left := by
    intro a
    have e : P.oA.act a ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (I.G.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext a)).symm
    rw [← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  obtain ⟨eA, hA⟩ := exists_mulEquiv_of_isGrpPullback gpG (TFK (R := T.V) F)
  obtain ⟨e2, h2⟩ := exists_mulEquiv_of_isGrpPullback I.m2.cart (TFK (R := T.V) F)
  obtain ⟨e1, h1⟩ := exists_mulEquiv_of_isGrpPullback I.m1.cart (TFK (R := T.V) F)
  refine ⟨(eA.trans e2.symm).trans e1, fun x b => ⟨?_, ?_⟩, fun a x => ?_⟩
  · rintro ⟨r, hr, hr1, hr2⟩
    let r' : TFK (R := T.V) F ⟶ I.t'.G := Over.homMk r hr
    have h3 : e2 r' = eA x := Over.OverMorphism.ext (by
      rw [h2, hA]
      exact hr2.trans (by rw [Over.comp_left, Category.assoc]))
    show b = e1 (e2.symm (eA x))
    rw [← h3, e2.symm_apply_apply]
    exact Over.OverMorphism.ext (hr1.symm.trans (h1 r').symm)
  · rintro rfl
    refine ⟨(e2.symm (eA x)).left, Over.w _, (h1 _).symm, ?_⟩
    refine (h2 _).symm.trans ?_
    rw [e2.apply_symm_apply, hA, Over.comp_left, Category.assoc]
  · have h3 : e2.symm (eA (x ≫ P.oA.act a)) = e2.symm (eA x) ≫ I.t'.act.act a := by
      rw [MulEquiv.symm_apply_eq]
      apply Over.OverMorphism.ext
      rw [hA, h2, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, actA, I.m2.act a,
        ← Category.assoc _ I.m2.cm.F, ← h2, e2.apply_symm_apply, hA, Category.assoc, Category.assoc]
    show e1 (e2.symm (eA (x ≫ P.oA.act a))) = e1 (e2.symm (eA x)) ≫ Xo.univ.t.act.act a
    rw [h3]
    apply Over.OverMorphism.ext
    rw [h1, Over.comp_left, Over.comp_left, h1, Category.assoc, Category.assoc, I.m1.act a]

end GlobalTheory.PtTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSecTieFModel
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Move
open GlobalTheory.FieldBaseChange
variable {X' X X₁ X₂ Y Y₁ : Scheme.{0}} {L' : LB X'}

def isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) : LB.Iso (L'.pull (𝟙 X')) (L.pull m) :=
  ⟨fun p => res (fun _ hy => ⟨hy.1, mem_pull.1 hy.2⟩ :
    (L.pull m).U p.1 ⊓ (L'.pull (𝟙 X')).U p.2 ≤ (L.pull m).U p.1 ⊓ L'.U (p.2 PUnit.unit)) (w.s (p.1, p.2 PUnit.unit))⟩

theorem isoVal_isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z)
    (j : L.ι) (k : L'.ι) (hj : m (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    isoVal (isoFromPullId w) r z j k = gv w r z (fun _ => j) k := by
  have hm : r z ∈ (L.pull m).U (fun _ => j) ⊓ (L'.pull (𝟙 X')).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  show gm r z _ (res _ (w.s (fun _ => j, k))) = _
  exact gm_res r z _ hm _

theorem isoFromPullId_isGen {L : LB X} {m : X' ⟶ X} {w : LB.Iso L' (L.pull m)} (hw : w.IsGen) :
    (isoFromPullId w).IsGen := by
  refine (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_
  have ik : r z ∈ L'.U (k PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk
  have ik' : r z ∈ L'.U (k' PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk'
  have a := isoVal_isoFromPullId w r z j (k PUnit.unit) hj ik
  have a' := isoVal_isoFromPullId w r z j' (k' PUnit.unit) hj' ik'
  have b := (isGen_iff w).1 hw Z r z j j' _ _ hj hj' ik ik'
  have c := (gm_pull_g L' (𝟙 X') r z k k' hk hk').trans
    (congrArg (fun f : Z ⟶ X' => gm f z _ (L'.g (k PUnit.unit) (k' PUnit.unit))) (Category.comp_id r))
  refine a.trans (b.trans ?_)
  exact congrArg₂ (fun s t => _ * s⁻¹ * t) c.symm a'.symm

end Move

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  {I : IntData Xo c T io y} {F : Type} [Field F] [Algebra T.Fr F] {xF : Sp F ⟶ Xo.X}

variable (I) (P : PELUnif (maximalIdeal T.V) I.G)

end Comparison₂

end GlobalTheory.PtTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HalfEXIffOriented
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

theorem barE_piG_eq_piBarO {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D (EX.piG i)

theorem halfEX_iff_oriented : ∀ (D : D7) (T : Top D), LawsP T → ∀ EX : ErrX D, HalfEX T.toCore EX ↔ Oriented T EX := by
  intro D T h EX
  rw [GlobalTheory.Survey.PiTwistNegation.halfEX_iff_le T.toCore h.toLawsCore.toLawsM EX]
  exact forall_congr' fun i => by rw [barE_piG_eq_piBarO]

end GlobalTheory.PtTie
end
end

