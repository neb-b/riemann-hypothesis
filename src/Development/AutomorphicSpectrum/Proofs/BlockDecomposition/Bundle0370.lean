module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.RightHolRightHolEq
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0282
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0358
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContDiffOnInvReal
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ENNReal
open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

variable {n : ℕ}

theorem contDiffOn_inv_real : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) :=
  ReciprocityTheory.ChartRestriction.DS.Lap.LemK.contDiffOn_inv_det_ne_zero.restrict_scalars ℝ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

end GlobalTheory.CompanionTheory.WaveCp.Rep.Frame

namespace GlobalTheory.CompanionTheory.WaveCp.Rep

end GlobalTheory.CompanionTheory.WaveCp.Rep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousArchimedeanSmoothing
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc

theorem continuous_sm_of_ker : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ)
    [MeasurableSpace (archGroup K n)] [BorelSpace (archGroup K n)] (ν : Measure (archGroup K n))
    [ν.IsHaarMeasure] (β : archGroup K n → ℝ) (f : AdelicGLn.AdelicGL K n → ℂ),
    Ker ν β → Continuous f → Continuous (sm ν β f) := by
  intro K _ _ n _ _ ν _ β f hβ hf
  have hs : IsCompact (tsupport β) := hβ.cpt
  set F : AdelicGLn.AdelicGL K n × archGroup K n → ℂ :=
    fun p => (β p.2 : ℂ) * f (p.1 * infEmb K n p.2) with hFdef
  have hF : Continuous F :=
    (Complex.continuous_ofReal.comp (hβ.cont.comp continuous_snd)).mul
      (hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd)))
  have hFx : ∀ x, Continuous fun y => F (x, y) := fun x =>
    hF.comp (continuous_const.prodMk continuous_id)
  have hint : ∀ x, IntegrableOn (fun y => F (x, y)) (tsupport β) ν := fun x =>
    (hFx x).continuousOn.integrableOn_compact hs
  have e : ∀ x, sm ν β f x = ∫ y in tsupport β, F (x, y) ∂ν := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      simp [hFdef, image_eq_zero_of_notMem_tsupport hy]).symm
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hc : 0 ≤ ν.real (tsupport β) := measureReal_nonneg
  set δ : ℝ := ε / (ν.real (tsupport β) + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hopen : IsOpen {p : AdelicGLn.AdelicGL K n × archGroup K n | dist (F p) (F (x₀, p.2)) < δ} :=
    isOpen_lt (hF.dist (hF.comp (continuous_const.prodMk continuous_snd))) continuous_const
  obtain ⟨u, v, hu, -, hxu, hsv, huv⟩ := generalized_tube_lemma (isCompact_singleton (x := x₀)) hs hopen (by
    rintro ⟨x, y⟩ ⟨hx, -⟩
    obtain rfl : x = x₀ := hx
    simpa using hδ)
  filter_upwards [hu.mem_nhds (hxu rfl)] with x hx
  rw [e, e, dist_eq_norm, ← integral_sub (hint x) (hint x₀)]
  have hb : ‖∫ y in tsupport β, (F (x, y) - F (x₀, y)) ∂ν‖ ≤ δ * ν.real (tsupport β) := by
    refine norm_setIntegral_le_of_norm_le_const hs.measure_lt_top fun y hy => ?_
    have := huv (Set.mk_mem_prod hx (hsv hy))
    simp only [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  refine lt_of_le_of_lt hb ?_
  rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
  nlinarith

end GlobalTheory.CompanionTheory.Conc
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContraIsSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.ContraSq

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isSmooth_sub {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ) :
    IsSmooth S.toRepresentation := fun s => by
  have e : {g : G | S.toRepresentation g s = s} = {g : G | ρ g (s : V) = s} := by
    ext g
    exact Subtype.ext_iff
  rw [e]
  exact hρ s

theorem exists_smooth_extension {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (S : Subrepresentation ρ)
    {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G))
    (l₀ : Module.Dual ℂ S.toSubmodule) (hl₀ : ∀ h ∈ K, ∀ s, l₀ (S.toRepresentation h s) = l₀ s) :
    ∃ l : smoothPart ρ.dual, (∀ h ∈ K, contra ρ h l = l) ∧
      ∀ s : S.toSubmodule, (l : Module.Dual ℂ V) s = l₀ s := by
  have hmem : ∀ x : fixed S.toRepresentation K,
      (S.toSubmodule.subtype ∘ₗ (fixed S.toRepresentation K).subtype) x ∈ fixed ρ K := by
    intro x
    refine GlobalTheory.ContraRefl.mem_fix.2 fun h hh => ?_
    exact congrArg Subtype.val (GlobalTheory.ContraRefl.mem_fix.1 x.2 h hh)
  let ι : fixed S.toRepresentation K →ₗ[ℂ] fixed ρ K := LinearMap.codRestrict _ _ hmem
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h1 : ((x : S.toSubmodule) : V) = 0 := congrArg Subtype.val hx
    exact Subtype.ext (Subtype.ext h1)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  obtain ⟨l, hl1, hl2⟩ := GlobalTheory.ContraRefl.exists_fixed_contra hρ ho hc
    ((l₀ ∘ₗ (fixed S.toRepresentation K).subtype) ∘ₗ r)
  refine ⟨l, hl1, fun s => ?_⟩
  have key : (l : Module.Dual ℂ V) ∘ₗ S.toSubmodule.subtype = l₀ := by
    refine GlobalTheory.ContraRefl.form_ext (isSmooth_sub hρ S) hc (fun h hh w => ?_) hl₀ fun w hw => ?_
    · have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (w : V))
        (hl1 h⁻¹ (inv_mem hh))
      simp only [contra_apply, inv_inv] at h1
      exact h1
    · have h2 := hl2 (ι ⟨w, hw⟩)
      have h3 : r (ι ⟨w, hw⟩) = ⟨w, hw⟩ := LinearMap.congr_fun hr ⟨w, hw⟩
      simp only [LinearMap.comp_apply, h3] at h2
      exact h2
  exact LinearMap.congr_fun key s

def annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} (S : Subrepresentation ρ)
    (f : S.toRepresentation.IntertwiningMap τ) : Subrepresentation (contra ρ) :=
  ⟨{ carrier := {l | ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0}
     add_mem' := fun {a b} ha hb s hs => by simp [ha s hs, hb s hs]
     zero_mem' := fun s _ => by simp
     smul_mem' := fun c a ha s hs => by simp [ha s hs] }, by
    intro h l hl s hs
    have h0 : f (S.toRepresentation h⁻¹ s) = 0 := by
      rw [f.isIntertwining, hs, map_zero]
    exact hl _ h0⟩

theorem mem_annih {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {l : smoothPart ρ.dual} :
    l ∈ (annih S f).toSubmodule ↔ ∀ s : S.toSubmodule, f s = 0 → (l : Module.Dual ℂ V) s = 0 :=
  Iff.rfl

def pull {ρ : Representation ℂ G V} (S : Subrepresentation ρ) (g : W →ₗ[ℂ] S.toSubmodule) :
    Module.Dual ℂ V →ₗ[ℂ] Module.Dual ℂ W :=
  (S.toSubmodule.subtype ∘ₗ g).dualMap

theorem pull_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} {g : W →ₗ[ℂ] S.toSubmodule}
    (hg : ∀ w, f (g w) = w) {l : smoothPart ρ.dual} (hl : l ∈ (annih S f).toSubmodule)
    (s : S.toSubmodule) : pull S g (l : Module.Dual ℂ V) (f s) = (l : Module.Dual ℂ V) s := by
  have h0 : f (g (f s) - s) = 0 := by
    have : f (g (f s) - s) = f (g (f s)) - f s := map_sub f.toLinearMap _ _
    rw [this, hg, sub_self]
  have h1 := mem_annih.1 hl _ h0
  have h2 : (l : Module.Dual ℂ V) ((g (f s) : V) - s) = 0 := h1
  rw [map_sub, sub_eq_zero] at h2
  exact h2

def restrLin {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toSubmodule →ₗ[ℂ] smoothPart τ.dual where
  toFun l := ⟨pull S g ((l : smoothPart ρ.dual) : Module.Dual ℂ V),
    mem_smoothPart_of_nhds (Filter.mem_of_superset
      ((isSmooth_contra ρ (l : smoothPart ρ.dual)).mem_nhds (by simp)) fun h hh => by
        have hh' : contra ρ h (l : smoothPart ρ.dual) = l := hh
        refine LinearMap.ext fun w => ?_
        obtain ⟨s, rfl⟩ := hf w
        show pull S g _ (τ h⁻¹ (f s)) = pull S g _ (f s)
        rw [← f.isIntertwining, pull_apply_map hg l.2, pull_apply_map hg l.2]
        have h1 := congrArg (fun x : smoothPart ρ.dual => (x : Module.Dual ℂ V) (s : V)) hh'
        simp only [contra_apply] at h1
        exact h1)⟩
  map_add' a b := Subtype.ext (by simp)
  map_smul' c a := Subtype.ext (by simp)

theorem restrLin_apply_map {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (l : (annih S f).toSubmodule) (s : S.toSubmodule) :
    (restrLin hf hg l : Module.Dual ℂ W) (f s) = ((l : smoothPart ρ.dual) : Module.Dual ℂ V) s :=
  pull_apply_map hg l.2 s

theorem restrLin_comm {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    {S : Subrepresentation ρ} {f : S.toRepresentation.IntertwiningMap τ}
    (hf : Function.Surjective f) {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w)
    (h : G) (l : (annih S f).toSubmodule) (w : W) :
    (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) w =
      (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ w) := by
  have e : ∀ s : S.toSubmodule,
      (restrLin hf hg ((annih S f).toRepresentation h l) : Module.Dual ℂ W) (f s) =
        (restrLin hf hg l : Module.Dual ℂ W) (τ h⁻¹ (f s)) := fun s => by
    rw [← f.isIntertwining, restrLin_apply_map, restrLin_apply_map]
    rfl
  have := e (g w)
  rwa [hg w] at this

def restr {ρ : Representation ℂ G V} {τ : Representation ℂ G W} {S : Subrepresentation ρ}
    {f : S.toRepresentation.IntertwiningMap τ} (hf : Function.Surjective f)
    {g : W →ₗ[ℂ] S.toSubmodule} (hg : ∀ w, f (g w) = w) :
    (annih S f).toRepresentation.IntertwiningMap (contra τ) where
  toLinearMap := restrLin hf hg
  isIntertwining' h :=
    LinearMap.ext fun l => Subtype.ext (LinearMap.ext fun w => restrLin_comm hf hg h l w)

theorem contra_isSubquotient : ∀ {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) →
    ∀ (ρ : Representation ℂ G V) (τ : Representation ℂ G W),
      IsSmooth ρ → IsSubquotient τ ρ → IsSubquotient (contra τ) (contra ρ) := by
  intro G V W _ _ _ _ _ _ _ hG ρ τ hρ ⟨S, f, hf⟩
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective f.toLinearMap
    (LinearMap.range_eq_top.2 hf)
  have hg' : ∀ w, f (g w) = w := fun w => LinearMap.congr_fun hg w
  refine ⟨annih S f, restr hf hg', fun m => ?_⟩
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra τ m).mem_nhds (by simp))
  have hfix : ∀ h ∈ K, ∀ s, (m : Module.Dual ℂ W) (f (S.toRepresentation h s)) =
      (m : Module.Dual ℂ W) (f s) := by
    intro h hh s
    have h1 : contra τ h⁻¹ m = m := hKs (inv_mem hh)
    have h2 := congrArg (fun x : smoothPart τ.dual => (x : Module.Dual ℂ W) (f s)) h1
    simp only [contra_apply, inv_inv] at h2
    rw [f.isIntertwining]
    exact h2
  obtain ⟨l, -, hl⟩ := exists_smooth_extension hρ S ho hc
    ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) hfix
  have hmem : l ∈ (annih S f).toSubmodule := fun s hs => by
    have h1 := hl s
    have h2 : ((m : Module.Dual ℂ W) ∘ₗ f.toLinearMap) s = (m : Module.Dual ℂ W) (f s) := rfl
    rw [h1, h2, hs, map_zero]
  refine ⟨⟨l, hmem⟩, Subtype.ext (LinearMap.ext fun w => ?_)⟩
  obtain ⟨s, rfl⟩ := hf w
  show pull S g (l : Module.Dual ℂ V) (f s) = _
  rw [pull_apply_map hg' hmem]
  exact hl s

end GlobalTheory.CompanionTheory.ContraSq

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContractingDoubleCosetVolumeBoundStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open ValuativeRel Matrix MeasureTheory GroundTheory.Automorphic.GLnLocal
open GlobalTheory.CompanionTheory.ContractVolume

private theorem leviEmbZjDiagonal {k : Type} [Field k] {h N : ℕ}
    (d : Fin h → ℕ) (hd : ∑ a, d a = N) (t : kˣ) (j : Fin h) :
    leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) =
      diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then t else 1) := by
  apply Units.ext
  rw [val_diagT]
  ext i l
  obtain ⟨⟨a, x⟩, rfl⟩ := (stdBlocks d hd).surjective i
  obtain ⟨⟨b, y⟩, rfl⟩ := (stdBlocks d hd).surjective l
  by_cases hab : a = b
  · subst hab
    rw [leviEmb_apply_same]
    by_cases hxy : x = y
    · subst hxy
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, Zl.JC.blockIdx, ha, Matrix.GeneralLinearGroup.scalar]
    · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨a, y⟩ := fun e => hxy (by
        have := (stdBlocks d hd).injective e
        simpa using this)
      rw [Matrix.diagonal_apply_ne _ hne]
      by_cases ha : a ≤ j <;> simp [Zl.JC.zj, ha, Matrix.GeneralLinearGroup.scalar, hxy]
  · have hne : stdBlocks d hd ⟨a, x⟩ ≠ stdBlocks d hd ⟨b, y⟩ := fun e => hab (by
      have := (stdBlocks d hd).injective e
      exact congrArg Sigma.fst this)
    rw [Matrix.diagonal_apply_ne _ hne, leviEmb_apply_ne k _ _ hab]

theorem _root_.GlobalTheory.T.contracting_double_coset_volume_bound :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      ∀ (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N), (∀ a, 0 < d a) →
        ∀ (t : kˣ), valuation k (t : k) < 1 → ∀ (j : Fin h), j.val + 1 < h →
          ∀ (m : ℕ), 1 ≤ m → ∀ [MeasurableSpace (AdGL k N)] [BorelSpace (AdGL k N)]
            (μ : Measure (AdGL k N)), μ.IsHaarMeasure →
              ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ,
                ENNReal.ofReal (c * (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ ^ r) ≤
                  μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
                    {g | ∃ x ∈ congruenceSubgroup k N m, ∃ y ∈ congruenceSubgroup k N m,
                      g = x * (leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j)) ^ r * y}) := by
  intro k _ _ _ _ h N d hd _ t ht j _ m hm _ _ μ hμ
  have := hμ
  obtain ⟨n, p, u, hp, hu, htu⟩ := exists_decomp t ht
  have hK := coe_congruenceSubgroup k N m hm
  rw [← hp] at hK
  have hϖ1 : valuation k (p : k) < 1 := hp ▸ valuation_uniformizer_lt_one k
  have hunif : ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k) := fun x hx =>
    hp ▸ le_valuation_uniformizer k x hx
  obtain ⟨hpos, hfin⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.measure_image_principal_pos_lt_top k N (p : k) m
    p.ne_zero hϖ1 hunif hm μ hμ
  rw [← hK] at hpos hfin
  let a : Fin N → ℤ := fun i => if Zl.JC.blockIdx d hd i ≤ j then (n : ℤ) else 0
  have ha : Antitone a := by
    intro x y hxy
    have hmono := GlobalTheory.CompanionTheory.BlockIndex.blockIdx_monotone h N d hd hxy
    show (if _ then _ else _) ≤ (if _ then _ else _)
    by_cases hy : Zl.JC.blockIdx d hd y ≤ j
    · simp [hy, hmono.trans hy]
    · simp [hy]
      split_ifs <;> simp
  let D : GL (Fin N) k := diagT k (Fin N) (fun i => p ^ a i)
  have hD : (D : Matrix (Fin N) (Fin N) k) = Matrix.diagonal (fun i => (p : k) ^ a i) := by
    simp [D, val_diagT]
  let w : GL (Fin N) k := diagT k (Fin N) (fun i => if Zl.JC.blockIdx d hd i ≤ j then u else 1)
  have hw : w ∈ integralGL k N := by
    refine diagT_mem_integralGL _ fun i => ?_
    split_ifs
    · exact hu
    · simp
  have hfac : leviEmb k (stdBlocks d hd) (Zl.JC.zj d t j) = D * w := by
    rw [leviEmbZjDiagonal, ← map_mul]
    congr 1
    funext i
    by_cases hi : Zl.JC.blockIdx d hd i ≤ j
    · simp [a, hi, htu]
    · simp [a, hi]
  have hcomm : Commute D w := by
    show D * w = w * D
    rw [← map_mul, ← map_mul, mul_comm]
  have hmod : (modulus k (fun a => Fin (d a)) (Zl.JC.zj d t j))⁻¹ =
      (resCard k : ℝ) ^ (n * ((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0)) := by
    have h1 : nabs k t = ((resCard k : ℝ)⁻¹) ^ n := by
      have h2 := nabs_uniformiser (irreducible_uniformizer k) hp
      have h3 := nabs_eq_one_of_valuation_eq_one hu
      rw [htu, show nabs k (p ^ n * u) = nabs k (p ^ n) * nabs k u from nabs_mul k _ _, nabs_pow', h2, h3,
        mul_one]
    have h4 : (∑ a, if a ≤ j then (d a : ℤ) else 0) * (∑ b, if j < b then (d b : ℤ) else 0) =
        (((∑ a, if a ≤ j then d a else 0) * ∑ b, if j < b then d b else 0 : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [modulus_zj, sum_modExp, h4, h1, zpow_natCast, ← pow_mul, inv_pow, inv_inv]
  refine ⟨(μ ((QuotientGroup.mk : GL (Fin N) k → AdGL k N) ''
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m : Set (GL (Fin N) k)))).toReal,
    ENNReal.toReal_pos hpos.ne' hfin.ne, fun r => ?_⟩
  have hvol := GlobalTheory.CompanionTheory.DoubleCosetVolume.measure_image_doubleCoset k N (p : k) m a p.ne_zero hϖ1 hunif
    hm ha D hD μ hμ r
  rw [← hK, sum_toNat d hd j n] at hvol
  have hle := measure_le_translate μ (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m) (D ^ r) (w ^ r)
    (hcomm.pow_pow r r) (fun x hx => conj_mem_congruenceSubgroup k N ((integralGL k N).pow_mem hw r) hx)
  rw [hfac, hcomm.mul_pow, hmod]
  refine le_trans (le_of_eq ?_) hle
  simp only [SetLike.mem_coe] at hvol
  rw [hvol, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne, mul_comm,
    ← pow_mul, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast, mul_comm _ r]
  rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.ContraSub

open GlobalTheory.ContraRefl

section General

variable {G V X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

def incl {π : Representation ℂ G V} (S : Subrepresentation π) :
    S.toRepresentation.IntertwiningMap π where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by ext _; rfl

theorem isSmooth_sub {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    IsSmooth S.toRepresentation := fun x => by
  have : {g : G | S.toRepresentation g x = x} = {g : G | π g x.1 = x.1} := by
    ext g; exact Subtype.ext_iff
  rw [this]; exact hπ x.1

theorem contraMap_incl_surjective
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {π : Representation ℂ G V} (hπ : IsSmooth π) (S : Subrepresentation π) :
    Function.Surjective (contraMap (incl S)) := by
  intro l
  obtain ⟨K, ho, hc, hKs⟩ := hG _ ((isSmooth_contra S.toRepresentation l).mem_nhds (by simp))
  have hlK : l ∈ fixed (contra S.toRepresentation) K := mem_fix.2 fun h hh => hKs hh
  obtain ⟨l₀, hl₀⟩ := LinearMap.exists_extend (l : Module.Dual ℂ S.toSubmodule)
  obtain ⟨l', h1, h2⟩ := exists_fixed_contra hπ ho hc (l₀ ∘ₗ (fixed π K).subtype)
  have hl'K : l' ∈ fixed (contra π) K := mem_fix.2 h1
  refine ⟨l', Subtype.ext (form_ext (isSmooth_sub hπ S) hc (fun h hh w => ?_) (fun h hh w => ?_)
    fun w hw => ?_)⟩
  · exact invariant_of_fixed ⟨l', hl'K⟩ h hh (w : V)
  · exact invariant_of_fixed ⟨l, hlK⟩ h hh w
  · have hwK : (w : V) ∈ fixed π K :=
      mem_fix.2 fun h hh => congrArg Subtype.val (mem_fix.1 hw h hh)
    have e1 := h2 ⟨w, hwK⟩
    have e2 := LinearMap.congr_fun hl₀ w
    exact e1.trans e2

theorem contraMap_injective {Y : Type} [AddCommGroup Y] [Module ℂ Y] {σ : Representation ℂ G X}
    {τ : Representation ℂ G Y} (f : σ.IntertwiningMap τ) (hf : Function.Surjective f) :
    Function.Injective (contraMap f) := by
  intro l l' h
  refine Subtype.ext (LinearMap.ext fun y => ?_)
  obtain ⟨x, rfl⟩ := hf y
  exact LinearMap.congr_fun (congrArg Subtype.val h) x

theorem isSubquotient_contra
    (hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    {σ : Representation ℂ G X} {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (h : IsSubquotient σ ρ) : IsSubquotient (contra σ) (contra ρ) := by
  obtain ⟨S, f, hf⟩ := h
  exact (IsSubquotient.of_injective (contraMap f) (contraMap_injective f hf)).trans
    (IsSubquotient.of_surjective (contraMap (incl S)) (contraMap_incl_surjective hG hρ S))

end General

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin N) k) V) (ρ : Representation ℂ (GL (Fin N) k) W),
    IsSmooth σ → IsSmooth ρ → IsSubquotient σ ρ → IsSubquotient (contra σ) (contra ρ) := by
  intro k _ _ _ _ N V W _ _ _ _ σ ρ _ hρ h
  refine isSubquotient_contra (fun U hU => ?_) hρ h
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k (Fin N) U hU
  exact ⟨J, h1, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end GlobalTheory.CompanionTheory.ContraSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel

namespace GlobalTheory.CompanionTheory.IwJac

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

variable {k n}

def tor (ϖ : kˣ) (x : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => ϖ ^ x i

end GlobalTheory.CompanionTheory.IwJac

end
end

