module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfInputs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0384

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialFiniteAdeles
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.G8
open scoped Classical

namespace GlobalTheory.CompanionTheory.TwistCent

theorem map_thetaR {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaR c n g) = thetaR c' n (GeneralLinearGroup.map f g) := by
  apply Units.ext
  ext i j
  rw [GeneralLinearGroup.map_apply, thetaR_val, thetaR_val, ← map_inv]
  simp only [Matrix.transpose_apply, Matrix.map_apply, GeneralLinearGroup.map_apply, h]

theorem map_phiU {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (PhiU n R) = PhiU n S := by
  apply Units.ext
  ext i j
  simp only [GeneralLinearGroup.map_apply, phiU_val, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem map_thetaGL {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R →+* R) (c' : S →+* S)
    (h : ∀ x, f (c x) = c' (f x)) (n : ℕ) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (thetaGL n c g) = thetaGL n c' (GeneralLinearGroup.map f g) := by
  rw [thetaGL_eq, thetaGL_eq, map_mul, map_mul, map_inv, map_phiU, map_thetaR f c c' h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_ratF (g : GL (Fin n) E) : thF E n (ratF E n g) = ratF E n (thE E n g) :=
  (map_thetaGL (algebraMap E (Af E)) _ _
    (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) n g).symm

theorem nontrivial_finiteAdeles : Nontrivial (Af E) := by
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (𝓞 E)
  let v₀ : HeightOneSpectrum (𝓞 E) :=
    ⟨m₀, hm₀.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm₀ (RingOfIntegers.not_isField E)⟩
  exact ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun x : Af E => x v₀) h)⟩⟩

theorem ratF_injective : Function.Injective (ratF E n) := by
  haveI : Nontrivial (Af E) := nontrivial_finiteAdeles
  intro g h e
  apply Units.ext
  ext i j
  have := congrArg (fun x : GL (Fin n) (Af E) => x.val i j) e
  exact (algebraMap E (Af E)).injective this

theorem pFin_ratGL (g : GL (Fin n) E) : GeneralLinearGroup.map (pFin E) (ratGL E n g) = ratF E n g := by
  apply Units.ext
  ext i j
  rfl

theorem cV_ratGL (v : InfinitePlace E) (g : GL (Fin n) E) :
    GeneralLinearGroup.map (cV v) (ratGL E n g) = GeneralLinearGroup.map v.embedding g := by
  apply Units.ext
  ext i j
  exact pInf_algebraMap (g.val i j) v

theorem mem_twCent_iff {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔ g * (d * u⁻¹) = d * u⁻¹ * thE E n g := by
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent, hu.1 g]
  constructor
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (g⁻¹ * d * thetaE E n g) := by rw [h]
        _ = d * thetaE E n g := by group
    calc g * (d * u⁻¹) = g * d * u⁻¹ := by group
      _ = d * thetaE E n g * u⁻¹ := by rw [h']
      _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) := by group
  · intro h
    have h' : g * d = d * thetaE E n g := by
      calc g * d = g * (d * u⁻¹) * u := by group
        _ = d * u⁻¹ * (u * thetaE E n g * u⁻¹) * u := by rw [h]
        _ = d * thetaE E n g := by group
    calc g⁻¹ * d * thetaE E n g = g⁻¹ * (d * thetaE E n g) := by group
      _ = g⁻¹ * (g * d) := by rw [h']
      _ = d := by group

theorem mem_twCent_iff_ratF {u : GL (Fin n) E} (hu : IsTransl u) (g d : GL (Fin n) E) :
    g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d ↔
      ratF E n g * ratF E n (d * u⁻¹) = ratF E n (d * u⁻¹) * thF E n (ratF E n g) := by
  rw [mem_twCent_iff hu, thF_ratF, ← map_mul, ← map_mul]
  exact ratF_injective.eq_iff.symm

theorem map_mem_twCent (v : InfinitePlace E) {g d : GL (Fin n) E}
    (h : g ∈ PositivityTheory.Rg.Tf.Loc.twCent (thetaE E n) d) :
    GeneralLinearGroup.map v.embedding g ∈
      PositivityTheory.Rg.Tf.Loc.twCent (thetaR (starRingEnd ℂ) n) (GeneralLinearGroup.map v.embedding d) := by
  have h' : g⁻¹ * d * thetaE E n g = d := h
  rw [PositivityTheory.Rg.Tf.Loc.mem_twCent]
  rw [← map_thetaR v.embedding (conjE E) (starRingEnd ℂ)
    (fun x => IsCMField.complexEmbedding_complexConj E v.embedding x) n g, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h'

theorem centEq : CentEq := by
  intro E _ _ _ a b u₁ u₂ h₁ h₂ d₁ d₂
  refine ⟨fun y => ⟨?_, ?_⟩, ?_⟩
  · rintro ⟨⟨⟨g₁, g₂⟩, rfl⟩, hc⟩
    have hc' := Prod.ext_iff.1 hc
    refine ⟨(ratGL E a g₁, ratGL E b g₂), ?_, ?_⟩
    · exact ⟨⟨g₁, (mem_twCent_iff_ratF h₁ g₁ d₁).2 hc'.1, rfl⟩, ⟨g₂, (mem_twCent_iff_ratF h₂ g₂ d₂).2 hc'.2, rfl⟩⟩
    · exact Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
  · rintro ⟨⟨γ₁, γ₂⟩, ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩, rfl⟩
    have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
      Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
    rw [e]
    exact ⟨⟨(g₁, g₂), rfl⟩, Prod.ext ((mem_twCent_iff_ratF h₁ g₁ d₁).1 hg₁) ((mem_twCent_iff_ratF h₂ g₂ d₂).1 hg₂)⟩
  · rintro ⟨γ₁, γ₂⟩ ⟨⟨g₁, hg₁, rfl⟩, ⟨g₂, hg₂, rfl⟩⟩
    refine ⟨fun h => ?_, fun v => ?_⟩
    · have e : (comps (ratGL E a g₁, ratGL E b g₂)).2 = (ratF E a g₁, ratF E b g₂) :=
        Prod.ext (pFin_ratGL g₁) (pFin_ratGL g₂)
      rw [e] at h
      have e₁ : g₁ = 1 := ratF_injective ((congrArg Prod.fst h).trans (map_one _).symm)
      have e₂ : g₂ = 1 := ratF_injective ((congrArg Prod.snd h).trans (map_one _).symm)
      subst e₁ e₂
      exact Prod.ext (map_one _) (map_one _)
    · constructor
      · show GeneralLinearGroup.map (cV v) (ratGL E a g₁) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₁
      · show GeneralLinearGroup.map (cV v) (ratGL E b g₂) ∈ _
        rw [cV_ratGL]
        exact map_mem_twCent v hg₂

end GlobalTheory.CompanionTheory.TwistCent

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormaliserUnconj
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.QConjug

variable {G : Type} [Group G]

def conjEquiv {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H) : H' ≃ H where
  toFun x := ⟨g * x * g⁻¹, (hH' x).1 x.2⟩
  invFun y := ⟨g⁻¹ * y * g, (hH' _).2 (by
    have : g * (g⁻¹ * (y : G) * g) * g⁻¹ = y := by group
    rw [this]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp only []; group)
  right_inv y := Subtype.ext (by simp only []; group)

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSingletonClass G]

theorem normaliser_conj {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H Measure.count ρ) :
    IsQuotNormaliser H' Measure.count (fun x => ρ (g * x)) := by
  unfold IsQuotNormaliser at hρ ⊢
  refine ⟨hρ.1.comp (measurable_const_mul g), fun y => ?_⟩
  have h1 := hρ.2 (g * y)
  rw [lintegral_count] at h1 ⊢
  rw [← h1, ← (conjEquiv hH').tsum_eq]
  refine tsum_congr fun x => ?_
  show ρ (g * ((x : G) * y)) = ρ (g * (x : G) * g⁻¹ * (g * y))
  congr 1
  group

theorem normaliser_unconj {H H' : Subgroup G} {g : G} (hH' : ∀ x, x ∈ H' ↔ g * x * g⁻¹ ∈ H)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H' Measure.count ρ) :
    IsQuotNormaliser H Measure.count (fun x => ρ (g⁻¹ * x)) := by
  have h2 : ∀ x, x ∈ H ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ H' := by
    intro x
    rw [hH', show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group]
  exact normaliser_conj h2 hρ

theorem qConjOf_holds : QConjOf := by
  intro hI G _ _ _ _ _ μ _ _ H H' _ F g hF hFH hH'
  haveI : Countable H' := Countable.of_equiv _ (conjEquiv hH').symm
  by_cases hex : ∃ ρ, IsQuotNormaliser H Measure.count ρ
  · obtain ⟨ρ, hρ⟩ := hex
    have hρ' := normaliser_conj hH' hρ
    have hmeas : Measurable fun x => F (g * x) := hF.comp (measurable_const_mul g)
    have hinv : ∀ h ∈ H', ∀ x, F (g * (h * x)) = F (g * x) := by
      intro h hh x
      have := hFH (g * h * g⁻¹) ((hH' h).1 hh) (g * x)
      rw [← this]
      congr 1
      group
    rw [hI G μ H' (fun x => F (g * x)) (fun x => ρ (g * x)) hmeas hinv hρ',
      hI G μ H F ρ hF hFH hρ]
    exact integral_mul_left_eq_self (fun x => F x * ((ρ x).toReal : ℂ)) g
  · have hex' : ¬ ∃ ρ, IsQuotNormaliser H' Measure.count ρ := by
      rintro ⟨ρ, hρ⟩
      exact hex ⟨_, normaliser_unconj hH' hρ⟩
    unfold quotIntegral
    rw [dite_eq_right hex, dite_eq_right hex']

end GlobalTheory.CompanionTheory.QConjug

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS

variable {n : ℕ}

def SmF (n : ℕ) : Submodule ℂ (Mat n → ℂ) where
  carrier := {h | ContDiffOn ℝ ∞ h (GLs n) ∧ ∀ g, g ∉ GLs n → h g = 0}
  add_mem' {a b} ha hb := ⟨ha.1.add hb.1, fun g hg => by simp [ha.2 g hg, hb.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' c a ha := ⟨contDiffOn_const.smul ha.1, fun g hg => by simp [ha.2 g hg]⟩

theorem indicator_Rd_mem (X : Mat n) (h : SmF n) : (GLs n).indicator (Rd X h.1) ∈ SmF n := by
  refine ⟨(GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X h.2.1).congr fun g hg => Set.indicator_of_mem hg _,
    fun g hg => Set.indicator_of_notMem hg _⟩

def DR (X : Mat n) : Module.End ℂ (SmF n) where
  toFun h := ⟨(GLs n).indicator (Rd X h.1), indicator_Rd_mem X h⟩
  map_add' a b := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      have db := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth b.2.1 hg
      simp only [Submodule.coe_add, Pi.add_apply, Set.indicator_of_mem hg, Rd]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_add_apply' da db _
    · simp [Set.indicator_of_notMem hg]
  map_smul' c a := by
    apply Subtype.ext
    funext g
    by_cases hg : g ∈ GLs n
    · have da := GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth a.2.1 hg
      simp only [Submodule.coe_smul, Pi.smul_apply, Set.indicator_of_mem hg, Rd, RingHom.id_apply, smul_eq_mul]
      exact GlobalTheory.CompanionTheory.RCalc.fderiv_csmul_apply da c _
    · simp [Set.indicator_of_notMem hg]

def Kf (a b : Fin n) : Module.End ℂ (SmF n) := e1 DR a b + e2 DR a b

def ev1 : SmF n →ₗ[ℂ] ℂ where
  toFun h := h.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def Pb (lev : Fin n → ℕ) : Set (Mat n) := {p | p ∈ GLs n ∧ ∀ a b, lev a < lev b → p a b = 0}

def Eqv (lev : Fin n → ℕ) (φ : Mat n → ℂ) : Submodule ℂ (SmF n) where
  carrier := {h | ∀ p ∈ Pb lev, ∀ g ∈ GLs n, h.1 (p * g) = φ p * h.1 g}
  add_mem' {a b} ha hb p hp g hg := by
    simp only [Submodule.coe_add, Pi.add_apply, ha p hp g hg, hb p hp g hg, mul_add]
  zero_mem' p _ g _ := by simp
  smul_mem' c a ha p hp g hg := by
    simp only [Submodule.coe_smul, Pi.smul_apply, ha p hp g hg, smul_eq_mul]
    ring

def muZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a =>
  2 * lam a + ((univ.filter fun b => lev a < lev b).card : ℤ) - ((univ.filter fun b => lev b < lev a).card : ℤ)

def yZ (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Fin n → ℤ := fun a => lam a - muZ lam lev a

def dif (v : Fin n → ℤ) (j : Fin n) : ℤ := v j - if h : (j : ℕ) + 1 < n then v ⟨j + 1, h⟩ else 0

def ini (j : Fin n) : Fin (j + 1) → Fin n := Fin.castLE j.isLt

def lm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) (ini j)).det

def gm (j : Fin n) (g : Mat n) : ℂ := (g.submatrix (ini j) id * (g.submatrix (ini j) id)ᴴ).det

def fRaw (lam : Fin n → ℤ) (lev : Fin n → ℕ) : Mat n → ℂ :=
  (GLs n).indicator fun g => ∏ j, lm j g ^ dif (muZ lam lev) j * gm j g ^ dif (yZ lam lev) j

def cyc (f : SmF n) : Submodule ℂ (SmF n) :=
  (Algebra.adjoin ℂ {T : Module.End ℂ (SmF n) | ∃ a b, T = e1 DR a b ∨ T = e2 DR a b}).toSubmodule.map
    (LinearMap.applyₗ f)

theorem unit_mem (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n :=
  (Matrix.UnitaryGroup.det_isUnit k).ne_zero

theorem DR_apply (X : Mat n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (DR X h).1 g = Rd X h.1 g :=
  Set.indicator_of_mem hg _

theorem orderedCechToCatCochainsOne_apply_valueAtSubset (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (e1 DR a b h).1 g = Eu true a b h.1 g := by
  simp only [e1, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub, Pi.smul_apply,
    Pi.sub_apply, DR_apply _ _ hg, Eu, Pi.add_apply, if_true, smul_eq_mul]
  ring

theorem liftOneFormsToCompatible_apply (a b : Fin n) (h : SmF n) {g : Mat n} (hg : g ∈ GLs n) : (f1 DR a b h).1 g = Eu false a b h.1 g := by
  simp [f1, DR_apply _ _ hg, Eu]
  ring

section K

variable [MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ)]

def ipK (κ : Measure (Matrix.unitaryGroup (Fin n) ℂ)) (x y : SmF n) : ℂ := ∫ k, conj (x.1 k.1) * y.1 k.1 ∂κ

end K

end GlobalTheory.CompanionTheory.ModelS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSp
section
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.PairSpProof

theorem pairSp : PositivityTheory.Rg.BcB.E.E3.PairSp := by
  intro E _ _ _ a b F U₁ U₂ h₁ h₂ hfd
  classical
  set A : Submodule ℂ (GA E a → ℂ) := Submodule.span ℂ (Set.range fun y x => F (x, y)) with hA
  have : FiniteDimensional ℂ A := hfd
  obtain ⟨S, c, hc⟩ := PositivityTheory.Rg.Rs.SliceTensor.interp A

  let V : Submodule ℂ (GA E a → ℂ) := (U₁.map (Submodule.subtype _))
  have hAV : A ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    obtain ⟨φ, hφ, e⟩ := h₁ y
    exact ⟨φ, hφ, e⟩
  have hF : F = ∑ κ : S, fun x : GA E a × GA E b => (c κ : GA E a → ℂ) x.1 * F (κ.1, x.2) := by
    funext ⟨x, y⟩
    have hy : (fun x => F (x, y)) ∈ A := Submodule.subset_span ⟨y, rfl⟩
    have := congrFun (hc _ hy) x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this]
    exact Finset.sum_congr rfl fun κ _ => mul_comm _ _
  rw [hF]
  refine Submodule.sum_mem _ fun κ _ => Submodule.subset_span ?_
  obtain ⟨φ, hφ, e⟩ := hAV (c κ).2
  obtain ⟨ψ, hψ, e'⟩ := h₂ κ.1
  refine ⟨φ, hφ, ψ, hψ, ?_⟩
  funext x
  have e1 : φ.1 = (c κ : GA E a → ℂ) := e
  rw [e1, e']

end GlobalTheory.CompanionTheory.PairSpProof
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicProjEmbeddingCompat
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.IotaProj

theorem blockIndex_succ_false (m j : ℕ) (a : Fin m) :
    eGP m (j + 1) ⟨false, a⟩ = (Fin.castSucc (eGP m j ⟨false, a⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]

theorem blockIndex_succ_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ = (Fin.castSucc (eGP m j ⟨true, b⟩) : Fin (m + j + 1 + 1)) := by
  apply Fin.ext
  first
    | rfl
    | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]
    | (simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum]; omega)

theorem blockIndex_succ_true_last (m j : ℕ) :
    eGP m (j + 1) ⟨true, Fin.last (j + 1)⟩ = (Fin.last (m + j + 1) : Fin (m + j + 1 + 1)) := by
  exact GlobalTheory.BZMir.Leib.blockIndex_true_last m (j + 1)

theorem glEmbMat_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem gpProj_iotaM : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (m j : ℕ) (y : GlobalTheory.BZMir.Leib.MirabolicParabolic k m j)
    (hh : embedding₂ k (m + j) y ∈ GlobalTheory.BZMir.Leib.MirabolicParabolic k m (j + 1)),
    GlobalTheory.BZMir.Leib.gpProj k m (j + 1) ⟨_, hh⟩ =
      ((GlobalTheory.BZMir.Leib.gpProj k m j y).1,
        embedding₂ k j (GlobalTheory.BZMir.Leib.gpProj k m j y).2) := by
  intro k _ _ _ _ m j y hh
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) false a b).trans
      (Eq.trans ?_ (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
        (GlobalTheory.BZMir.Leib.hgpIncl k m j y) false a b).symm)
    rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j a, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_false m j b]
    exact GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
      ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
        Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _
  · apply Subtype.ext
    refine Units.ext (Matrix.ext fun a b => ?_)
    refine (GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m (j + 1))
      (GlobalTheory.BZMir.Leib.hgpIncl k m (j + 1) ⟨_, hh⟩) true a b).trans ?_
    have hR := fun a b => GlobalTheory.SmGL.leviProj_apply k (GlobalTheory.BZMir.Leib.eGP m j)
      (GlobalTheory.BZMir.Leib.hgpIncl k m j y) true a b
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k)).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k)).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_last_castSucc k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) b).symm
    | cast a =>
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_last, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _).trans
          (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc_last k (j + 1)
            ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
              Matrix (Fin (j + 1)) (Fin (j + 1)) k) a).symm
      | cast b =>
        rw [GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc, GlobalTheory.CompanionTheory.LeibPhi.IotaProj.blockIndex_succ_true_castSucc]
        exact (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (m + j + 1)
          ((((y : GlobalTheory.BZMir.Mir k (m + j)) : GL (Fin (m + j + 1)) k)) :
            Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _).trans
          ((hR a b).symm.trans
            (GlobalTheory.CompanionTheory.LeibPhi.IotaProj.glEmbMat_castSucc k (j + 1)
              ((((GlobalTheory.BZMir.Leib.gpProj k m j y).2 : GL (Fin (j + 1)) k)) :
                Matrix (Fin (j + 1)) (Fin (j + 1)) k) a b).symm)

end GlobalTheory.CompanionTheory.LeibPhi.IotaProj

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacterStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_trace_weyl_character : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective (fun a => z a ^ 2) → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | exact GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | (intros; apply GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv <;> assumption)
end

