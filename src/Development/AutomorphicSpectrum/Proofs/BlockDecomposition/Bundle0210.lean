module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniqueEmbeddingExtension
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.EmbUniq

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_algHom {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (x : ↥K.1) :
    ‖((τ x : ↥L.1) : Om l)‖ = ‖(x : Om l)‖ := by
  have a := minpoly.algHom_eq (L.1.val.comp τ) (RingHom.injective (L.1.val.comp τ : ↥K.1 →+* Om l)) x
  have b := minpoly.algHom_eq K.1.val (RingHom.injective (K.1.val : ↥K.1 →+* Om l)) x
  have c : minpoly ℚ_[l] ((τ x : ↥L.1) : Om l) = minpoly ℚ_[l] (x : Om l) := a.trans b.symm
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, c]

theorem norm_le_one_of_isIntegral {x : Om l} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := Om l)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Om l))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

variable {E : Type} [Field E] [NumberField E]

theorem continuous_withVal (w : HeightOneSpectrum (𝓞 E)) (f : E →+* Om l)
    (h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1) (y : E) (hy0 : y ≠ 0) (hy : ‖f y‖ < 1) :
    Continuous (f.comp (WithVal.equiv (w.valuation E)).toRingHom) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hy
  let x0 : WithVal (w.valuation E) := WithVal.toVal _ (y ^ n)
  have hx0' : x0 ≠ 0 := by
    intro h
    exact pow_ne_zero n hy0 ((WithVal.equiv (w.valuation E)).symm.map_eq_zero_iff.1 h)
  have h0 : Valued.v.restrict x0 ≠ 0 := by simp [hx0']
  filter_upwards [Valued.mem_nhds_zero.2 ⟨Units.mk0 _ h0, subset_rfl⟩] with z hz
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
  have hz' : w.valuation E (WithVal.equiv (w.valuation E) z) < w.valuation E (y ^ n) := hz
  have hv : 0 < w.valuation E (y ^ n) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (pow_ne_zero n hy0))
  have hu : w.valuation E (WithVal.equiv (w.valuation E) z / y ^ n) ≤ 1 := by
    rw [map_div₀]
    exact (div_le_one₀ hv).2 hz'.le
  have h2 := h1 _ hu
  have hp : 0 < ‖f y‖ ^ n := pow_pos (norm_pos_iff.2 ((map_ne_zero f).2 hy0)) n
  rw [map_div₀, map_pow, norm_div, norm_pow, div_le_one₀ hp] at h2
  rw [dist_zero_right]
  exact lt_of_le_of_lt h2 hn

def toKw {Ω : Type} [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) : E →+* ↥Bw.Kw.1 :=
  (Bw.j.comp (algebraMap E Ω)).codRestrict Bw.Kw.1 Bw.j_E

theorem existsUnique_continuous_induced : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw → ∀ (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      ∃! j : {j : w.adicCompletion E →+* Qbar l // Continuous j},
        IsInduced Bw (j.1.comp (algebraMap E (w.adicCompletion E))) τ' := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hj LL' τ'
  let g : E →+* ↥LL'.1 := (τ' : ↥Bw.Kw.1 →+* ↥LL'.1).comp (toKw Bw)
  let f : E →+* Om l := (algebraMap ↥LL'.1 (Om l)).comp g
  have hfn : ∀ x, ‖f x‖ = ‖Bw.j (algebraMap E Ω x)‖ := fun x => norm_coe_algHom τ' (toKw Bw x)
  have hlt : ∀ y : 𝓞 E, ‖f (y : E)‖ < 1 ↔ y ∈ w.asIdeal := fun y => by
    rw [hfn, ← hj.valuation_lt_one_iff]
    exact hA y
  have hint : ∀ y : 𝓞 E, ‖f (y : E)‖ ≤ 1 := fun y =>
    norm_le_one_of_isIntegral (by
      convert map_isIntegral_int f (RingOfIntegers.isIntegral_coe y)
      exact Subsingleton.elim _ _)
  have h1 : ∀ x, w.valuation E x ≤ 1 → ‖f x‖ ≤ 1 := fun x hx => by
    obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
    have hd : 1 ≤ ‖f ((d : 𝓞 E) : E)‖ := not_lt.1 fun hl => d.2 ((hlt _).1 hl)
    have h2 : ‖f x‖ * ‖f ((d : 𝓞 E) : E)‖ = ‖f (n : E)‖ := by
      rw [← norm_mul, ← map_mul]
      exact congrArg (fun z => ‖f z‖) h
    have h3 := hint n
    nlinarith [norm_nonneg (f x)]
  obtain ⟨y, hyw, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have hc := continuous_withVal w f h1 (y : E) (by simpa using hy0) ((hlt y).2 hyw)
  have hcg : Continuous (g.comp (WithVal.equiv (w.valuation E)).toRingHom) :=
    Topology.IsInducing.subtypeVal.continuous_iff.2 hc
  haveI : FiniteDimensional ℚ_[l] ↥LL'.1 := LL'.2
  haveI : CompleteSpace ↥LL'.1 := FiniteDimensional.complete ℚ_[l] ↥LL'.1
  let ext : w.adicCompletion E →+* ↥LL'.1 :=
    (UniformSpace.Completion.extensionHom _ hcg).comp (HeightOneSpectrum.adicCompletion.equiv E w).toRingHom
  have hextc : Continuous ext := UniformSpace.Completion.continuous_extension.comp
    (HeightOneSpectrum.adicCompletion.continuous_toCompletion E w)
  have hext : ∀ x : E, ext (algebraMap E _ x) = g x := fun k =>
    UniformSpace.Completion.extensionHom_coe _ hcg (WithVal.toVal _ k)
  have hval : ∀ x : E, ((ext (algebraMap E _ x) : ↥LL'.1) : Om l) = f x := fun x =>
    congrArg (Subtype.val) (hext x)
  refine ⟨⟨(algebraMap ↥LL'.1 (Om l)).comp ext, continuous_subtype_val.comp hextc⟩, fun x => (hval x), ?_⟩
  rintro ⟨j', hj'c⟩ hj'
  refine Subtype.ext (DFunLike.coe_injective ((HeightOneSpectrum.denseRange_algebraMap E w).equalizer hj'c
    (continuous_subtype_val.comp hextc) (funext fun x => ?_)))
  exact (hj' x).trans (hval x).symm

end GlobalTheory.CompanionTheory.EmbUniq
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryChamberDecomposition
section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.ChamberInd

variable {m : ℕ}

def nrm (χ : Fin m → ℂˣ) : Fin m → ℝ := fun i => ‖(χ i : ℂ)‖

def wt (a : Fin m → ℝ) : ℝ := ∑ i : Fin m, ((m : ℝ) - (i.val : ℝ)) * Real.log (a i)

theorem nrm_pos (χ : Fin m → ℂˣ) (i : Fin m) : 0 < nrm χ i := by
  exact norm_pos_iff.mpr (Units.ne_zero _)

theorem wt_swap_gt (a : Fin m → ℝ) (ha : ∀ i, 0 < a i) (i j : Fin m) (hij : i.val + 1 = j.val)
    (hlt : a i < a j) : wt a < wt (a ∘ Equiv.swap i j) := by
  have hne : i ≠ j := by
    intro h
    rw [h] at hij
    omega
  have hsub : wt (a ∘ Equiv.swap i j) - wt a =
      ((m : ℝ) - (i.val : ℝ)) * (Real.log (a j) - Real.log (a i)) +
        ((m : ℝ) - (j.val : ℝ)) * (Real.log (a i) - Real.log (a j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_add i j hne (fun k hk => by
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hk.1 hk.2, sub_self])]
    simp only [Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]
    ring
  have hj : (j.val : ℝ) = (i.val : ℝ) + 1 := by
    rw [← hij]
    push_cast
    ring
  have hlog : Real.log (a i) < Real.log (a j) := Real.log_lt_log (ha i) hlt
  have hd : wt (a ∘ Equiv.swap i j) - wt a = Real.log (a j) - Real.log (a i) := by
    rw [hsub, hj]
    ring
  linarith

theorem wt_update_gt (χ : Fin m → ℂˣ) (j : Fin m) (hj : j.val + 1 = m) (hlt : ‖(χ j : ℂ)‖ < 1) :
    wt (nrm χ) < wt (nrm (Function.update χ j (χ j)⁻¹)) := by
  have hpos : 0 < ‖(χ j : ℂ)‖ := norm_pos_iff.mpr (Units.ne_zero _)
  have hn : nrm (Function.update χ j (χ j)⁻¹) = Function.update (nrm χ) j (‖(χ j : ℂ)‖⁻¹) := by
    funext k
    by_cases hk : k = j
    · subst hk
      simp [nrm]
    · simp [nrm, Function.update_of_ne hk]
  rw [hn]
  have hdiff : wt (Function.update (nrm χ) j ‖(χ j : ℂ)‖⁻¹) - wt (nrm χ) =
      ((m : ℝ) - (j.val : ℝ)) * (Real.log ‖(χ j : ℂ)‖⁻¹ - Real.log (nrm χ j)) := by
    unfold wt
    rw [← Finset.sum_sub_distrib, Fintype.sum_eq_single j (fun k hk => by
      simp only [Function.update_of_ne hk, sub_self])]
    simp only [Function.update_self]
    ring
  have hm : (m : ℝ) - (j.val : ℝ) = 1 := by
    have hj' : (j.val : ℝ) + 1 = (m : ℝ) := by exact_mod_cast hj
    linarith
  have hlog : Real.log ‖(χ j : ℂ)‖ < 0 := Real.log_neg hpos hlt
  have e : nrm χ j = ‖(χ j : ℂ)‖ := rfl
  rw [Real.log_inv, hm, e] at hdiff
  linarith

theorem weylConj_swap {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (i j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (χ ∘ Equiv.swap i j) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨(Equiv.swap i j).trans w, fun k => hw _⟩

theorem weylConj_update {α χ : Fin m → ℂˣ} (h : GlobalTheory.LGrp.WeylConjU α χ) (j : Fin m) :
    GlobalTheory.LGrp.WeylConjU α (Function.update χ j (χ j)⁻¹) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨w, fun k => ?_⟩
  by_cases hk : k = j
  · subst hk
    rw [Function.update_self]
    rcases hw k with h | h
    · right
      rw [h]
    · left
      rw [h, inv_inv]
  · rw [Function.update_of_ne hk]
    exact hw k

theorem finite_nrm (α : Fin m → ℂˣ) (T : Set (Fin m → ℂˣ)) (hT : ∀ β ∈ T, GlobalTheory.LGrp.WeylConjU α β) :
    (nrm '' T).Finite := by
  classical
  let S : Set ℝ := (Set.range fun k => ‖(α k : ℂ)‖) ∪ Set.range fun k => ‖(((α k)⁻¹ : ℂˣ) : ℂ)‖
  have hS : S.Finite := (Set.finite_range _).union (Set.finite_range _)
  refine (Set.Finite.pi (t := fun _ : Fin m => S) (fun _ => hS)).subset ?_
  rintro _ ⟨β, hβ, rfl⟩
  rw [Set.mem_univ_pi]
  intro i
  obtain ⟨w, hw⟩ := hT β hβ
  rcases hw i with h | h
  · exact Or.inl ⟨w i, by simp only [nrm, h]⟩
  · exact Or.inr ⟨w i, by simp only [nrm, h]⟩

theorem exists_chamber (P : (Fin m → ℂˣ) → Prop)
    (hs : ∀ (χ : Fin m → ℂˣ) (i j : Fin m), i.val + 1 = j.val → ‖(χ i : ℂ)‖ < ‖(χ j : ℂ)‖ → P χ →
      P (χ ∘ Equiv.swap i j))
    (hv : ∀ (χ : Fin m → ℂˣ) (j : Fin m), j.val + 1 = m → ‖(χ j : ℂ)‖ < 1 → P χ →
      P (Function.update χ j (χ j)⁻¹))
    (α χ : Fin m → ℂˣ) (hα : GlobalTheory.LGrp.WeylConjU α χ) (hχ : P χ) :
    ∃ β : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α β ∧ (∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖) ∧
      (∀ i, 1 ≤ ‖(β i : ℂ)‖) ∧ P β := by
  classical
  obtain ⟨T, hTdef⟩ : ∃ T : Set (Fin m → ℂˣ), T = {β | GlobalTheory.LGrp.WeylConjU α β ∧ P β} := ⟨_, rfl⟩
  have hfin : (nrm '' T).Finite := finite_nrm α T (fun β hβ => by rw [hTdef] at hβ; exact hβ.1)
  have hne : (nrm '' T).Nonempty := ⟨nrm χ, χ, by rw [hTdef]; exact ⟨hα, hχ⟩, rfl⟩
  obtain ⟨_, ⟨β, hβT, rfl⟩, hmax⟩ := Set.exists_max_image (nrm '' T) wt hfin hne
  rw [hTdef] at hβT
  obtain ⟨hβα, hβP⟩ := hβT
  have hmax' : ∀ γ : Fin m → ℂˣ, GlobalTheory.LGrp.WeylConjU α γ → P γ → wt (nrm γ) ≤ wt (nrm β) :=
    fun γ h1 h2 => hmax _ ⟨γ, by rw [hTdef]; exact ⟨h1, h2⟩, rfl⟩
  have hadj : ∀ i j : Fin m, i.val + 1 = j.val → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    by_contra hcon
    rw [not_le] at hcon
    have h1 := hmax' _ (weylConj_swap hβα i j) (hs β i j hij hcon hβP)
    have h2 := wt_swap_gt (nrm β) (nrm_pos β) i j hij hcon
    exact absurd h1 (not_le.mpr h2)
  have key : ∀ d : ℕ, ∀ i j : Fin m, j.val = i.val + d → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro d
    induction d with
    | zero =>
      intro i j h
      rw [show j = i from Fin.ext (by omega)]
    | succ d ih =>
      intro i j h
      have hk : i.val + d < m := by
        have := j.isLt
        omega
      exact le_trans (hadj ⟨i.val + d, hk⟩ j (by show i.val + d + 1 = j.val; omega))
        (ih i ⟨i.val + d, hk⟩ rfl)
  have hmono : ∀ i j : Fin m, i ≤ j → ‖(β j : ℂ)‖ ≤ ‖(β i : ℂ)‖ := by
    intro i j hij
    have h' : i.val ≤ j.val := hij
    exact key (j.val - i.val) i j (by omega)
  have hone : ∀ i, 1 ≤ ‖(β i : ℂ)‖ := by
    intro i
    have hi := i.isLt
    have hlast : (⟨m - 1, by omega⟩ : Fin m).val + 1 = m := by
      show m - 1 + 1 = m
      omega
    have hl : 1 ≤ ‖(β ⟨m - 1, by omega⟩ : ℂ)‖ := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 := hmax' _ (weylConj_update hβα _) (hv β _ hlast hcon hβP)
      have h2 := wt_update_gt β _ hlast hcon
      exact absurd h1 (not_le.mpr h2)
    exact le_trans hl (hmono i _ (by show i.val ≤ m - 1; omega))
  exact ⟨β, hβα, hmono, hone, hβP⟩

theorem chamberU : PositivityTheory.SphericalProduct.ChamberU := by
  unfold ChamberU
  intro hsw hinv
  unfold SwapStepU at hsw
  unfold InvStepU at hinv
  intro L _ _ _ ϖ σ q n hU V _ _ ρ hadm hirr hsph α χ hα f hf hfeq
  obtain ⟨β, h1, h2, h3, hP⟩ := exists_chamber (m := n / 2)
    (fun χ => ∃ f : V →ₗ[ℂ] ↥(GlobalTheory.LFun.psSpaceU σ q χ), Function.Injective f ∧
      ∀ (g : ↥(Formalism.UG.GU σ n)) (v : V), f (ρ g v) = (GlobalTheory.LFun.psFunU σ q χ g) (f v))
    (fun χ i j hij hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hsw L ϖ σ q n hU V ρ hadm hirr hsph χ i j hij
        (by rw [norm_div, div_lt_one (norm_pos_iff.mpr (Units.ne_zero _))]; exact hlt) f hf hfeq)
    (fun χ j hj hlt hP => by
      obtain ⟨f, hf, hfeq⟩ := hP
      exact hinv L ϖ σ q n hU V ρ hadm hirr hsph χ j hj hlt f hf hfeq)
    α χ hα ⟨f, hf, hfeq⟩
  exact ⟨β, h1, h2, h3, hP⟩

end GlobalTheory.CompanionTheory.ChamberInd

end
end

