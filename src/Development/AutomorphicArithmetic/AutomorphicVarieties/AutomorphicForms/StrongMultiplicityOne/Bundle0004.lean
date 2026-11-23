module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.PrSLocNe
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem pr_comm {S : Finset (HeightOneSpectrum (𝓞 E))} {x k : GL (Fin n) (Af E)} (hx : SuppIn S x)
    (hk : Away S k) : k * x = x * k := by
  refine cmp_ext fun w => ?_
  rw [map_mul, map_mul]
  by_cases h : w ∈ S
  · rw [hk w h, mul_one, one_mul]
  · rw [hx w h, mul_one, one_mul]

private theorem pr_sLoc (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E) : pLoc E w (sLoc E w x) = x := by
  classical
  exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x

private theorem pr_sLoc_ne {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (x : w.adicCompletion E) :
    pLoc E v (sLoc E w x) = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) h x

private theorem pr_loc {S : Finset (HeightOneSpectrum (𝓞 E))} {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S)
    {k : GL (Fin n) (w.adicCompletion E)} (hk : k ∈ GlobalTheory.LFun.KGL w (n := n)) : InKS S (locGL E n w k) := by
  have h1 : ∀ v, v ≠ w → cmp v (locGL E n w k) = 1 := fun v hv =>
    GlobalTheory.CuspRep.map_cornerGL_of_zero _ _ (pr_sLoc_ne hv) k
  have h2 : cmp w (locGL E n w k) = k :=
    GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) (pr_sLoc w) k
  refine ⟨fun v hv => h1 v fun e => hw (e ▸ hv), fun v => ?_⟩
  by_cases h : v = w
  · subst h; rw [h2]; exact hk
  · rw [h1 v h]; exact one_mem _

private theorem pr_fop {S : Finset (HeightOneSpectrum (𝓞 E))} {c : GL (Fin n) (Af E) →₀ ℂ}
    (hc : ∀ x ∈ c.support, SuppIn S x) {f : GA E n → ℂ} (hf : ∀ g k, InKS S k → f (g * finGL E n k) = f g)
    (g : GA E n) (k : GL (Fin n) (Af E)) (hk : InKS S k) : fop c f (g * finGL E n k) = fop c f g := by
  unfold fop
  refine Finsupp.sum_congr fun x hx => ?_
  rw [mul_assoc, ← map_mul, pr_comm (hc x hx) hk.1, map_mul, ← mul_assoc, hf _ _ hk]

private theorem pr_wh {f : GA E n → ℂ} {u : GA E n} (hf : ∀ g, f (g * u) = f g) (g : GA E n) :
    whittaker f (g * u) = whittaker f g := by
  unfold whittaker
  simp only [← mul_assoc, hf]

private theorem pr_conv [_root_.NumberField.IsTotallyComplex E] {f : GA E n → ℂ} {k : GL (Fin n) (Af E)} (hf : ∀ g, f (g * finGL E n k) = f g)
    (α : Lie E n → ℂ) (g : GA E n) : conv f α (g * finGL E n k) = conv f α g := by
  unfold Af.StrongMultiplicityOne.conv
  congr 1
  funext x
  congr 1
  unfold chart
  split_ifs with h
  · rw [mul_assoc, ← GlobalTheory.CuspRep.infGL_comm, ← mul_assoc, hf]
  · rfl

private theorem pr_mem {U : Submodule ℂ (cuspForms E n)} (sU : Fb.Stab U) (c : GL (Fin n) (Af E) →₀ ℂ)
    {φ : cuspForms E n} (hφ : φ ∈ U) : ∃ ψ ∈ U, ψ.1 = fop c φ.1 := by
  refine ⟨∑ x ∈ c.support, c x • finRepCusp E n x φ, U.sum_mem fun x _ => U.smul_mem _ (sU.τ _ _ hφ), ?_⟩
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply, fop, ← Fb.finEmb_eq]
  rfl

end

theorem UpperTheory.V.Af.StrongMultiplicityOne.pair :
    UpperTheory.V.Af.StrongMultiplicityOne.Seed → UpperTheory.V.Af.StrongMultiplicityOne.SetUp → UpperTheory.V.Af.StrongMultiplicityOne.KillP → UpperTheory.V.Af.StrongMultiplicityOne.Vanish → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.Smo.WhLin → UpperTheory.V.Af.StrongMultiplicityOne.ConvNice → UpperTheory.V.Af.StrongMultiplicityOne.NiceOf → UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Pair := by
  intro hSeed hSet hKill hVan hWB hWL hCN hES hEM E _ _ _ n hn π π' h0 h0' hc hc' st st' hs
  have hN : ∀ φ ∈ π, Nice φ.1 := fun φ hφ => (hES E n φ).2 (hc hφ)
  have hN' : ∀ φ ∈ π', Nice φ.1 := fun φ hφ => (hES E n φ).2 (hc' hφ)
  obtain ⟨φ, hφ, α, hα⟩ := hSeed E n π h0 hc st
  obtain ⟨φ', hφ', α', hα'⟩ := hSeed E n π' h0' hc' st'
  obtain ⟨S, B, hS, hK, hK'⟩ := hSet E n π π' hs φ φ'
  obtain ⟨V, hV⟩ := (hN φ hφ).level
  obtain ⟨V', hV'⟩ := (hN' φ' hφ').level
  obtain ⟨c, H, hH, hc, hop⟩ := hKill E n hn S (V ⊓ V')

  have side : ∀ (σ : Submodule ℂ (cuspForms E n)), Fb.Stab σ → (∀ φ ∈ σ, Nice φ.1) → (∀ w ∉ S, Sat w (B w) σ) → ∀ φ ∈ σ,
      ∀ α : 𝓢(Lie E n, ℂ), conv (whittaker φ.1) α 1 = 1 → (∀ g k, InKS S k → φ.1 (g * finGL E n k) = φ.1 g) →
      (∀ g, ∀ u ∈ V ⊓ V', φ.1 (g * finGL E n u) = φ.1 g) →
      ∃ ψ ∈ σ, ∃ β : 𝓢(Lie E n, ℂ), Nice (conv ψ.1 β) ∧ (∀ w ∉ S, EigAt w (B w) (conv ψ.1 β)) ∧
        (∀ g k, InKS S k → conv ψ.1 β (g * finGL E n k) = conv ψ.1 β g) ∧
        ∀ p, InPS S p → whittaker (conv ψ.1 β) p = H p := by
    intro σ sσ hN hsat φ hφ α hα hK hU
    obtain ⟨ψ, hψ, e⟩ := pr_mem sσ c hφ
    obtain ⟨β, hβ⟩ := hop α
    have hK₁ : ∀ g k, InKS S k → ψ.1 (g * finGL E n k) = ψ.1 g := by
      rw [e]; exact pr_fop hc hK
    refine ⟨ψ, hψ, β, (hCN E n _ (hN ψ hψ) β).1, fun w hw => ?_, fun g k hk => pr_conv (fun g => hK₁ g k hk) _ g,
      fun p hp => ?_⟩
    · exact (hEM E n w (B w) _ (hsat w hw ψ hψ
        fun g k hk => hK₁ g _ (pr_loc hw hk))).2.1 (hN ψ hψ) β
    · obtain ⟨b1, b2, b3⟩ := hWB E n _ (hN φ hφ)
      rw [(hCN E n _ (hN ψ hψ) β).2, e, ((hWL E n _ (hN φ hφ)).1 c).2,
        hβ _ b1 b2 b3 (fun g u hu => pr_wh (fun g => hU g u hu) g) p hp, hα, mul_one]
  obtain ⟨ψ, hψ, β, n1, e1, k1, w1⟩ := side π st hN (fun w hw => (hS w hw).2.1) φ hφ α hα hK
    fun g u hu => hV g u hu.1
  obtain ⟨ψ', hψ', β', n2, e2, k2, w2⟩ := side π' st' hN' (fun w hw => (hS w hw).2.2) φ' hφ' α' hα' hK'
    fun g u hu => hV' g u hu.2
  obtain ⟨n3, w3⟩ := (hWL E n _ n1).2 _ n2
  refine ⟨ψ, hψ, ψ', hψ', β, β', sub_eq_zero.1 (hVan E n hn S B _ n3
    (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) _ (e1 w hw)).2.2 _ (e2 w hw)⟩) (fun g k hk => ?_) fun p hp => ?_),
    fun h00 => ?_⟩
  · rw [Pi.sub_apply, Pi.sub_apply, k1 g k hk, k2 g k hk]
  · rw [w3, Pi.sub_apply, w1 p hp, w2 p hp, sub_self]
  · have h1 : InPS S (1 : GA E n) := by
      refine ⟨fun i _ => ⟨by simp, fun j hj => ?_⟩, fun w _ => by rw [map_one, map_one]⟩
      exact Matrix.one_apply_ne hj.ne'
    have h2 := w1 1 h1
    rw [h00, hH] at h2
    simp [whittaker] at h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.SeedConv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem exists_schwartz_integral_eq_one {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (F : X → ℂ) (U : Set X) (x₀ : X)
    (hU : U ∈ 𝓝 x₀) (hF : ContinuousOn F U) (h0 : F x₀ ≠ 0) : ∃ α : 𝓢(X, ℂ), ∫ x, F x * α x ∂μ = 1 := by
  have hc : ContinuousAt (fun x => (F x / F x₀).re) x₀ :=
    Complex.continuous_re.continuousAt.comp ((hF.continuousAt hU).div_const _)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < (F x / F x₀).re :=
    hc.eventually (lt_mem_nhds (by simp [div_self h0]))
  obtain ⟨r, hr, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem (interior_mem_nhds.2 hU) hp)
  let b : ContDiffBump x₀ := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  have hs : tsupport b = Metric.closedBall x₀ r := b.tsupport_eq
  have hs' : Function.support b = Metric.ball x₀ r := b.support_eq
  have hG : Continuous fun x => b x • (F x / F x₀) := by
    refine continuous_of_tsupport fun x hx => ?_
    have hx' : x ∈ Metric.closedBall x₀ r := hs ▸ tsupport_smul_subset_left _ _ hx
    exact b.continuous.continuousAt.smul ((hF.continuousAt (mem_interior_iff_mem_nhds.1 (hb hx').1)).div_const _)
  have hK : HasCompactSupport fun x => b x • (F x / F x₀) := b.hasCompactSupport.smul_right
  have hI : Integrable (fun x => b x • (F x / F x₀)) μ := hG.integrable_of_hasCompactSupport hK
  have hpos : 0 < ∫ x, (b x • (F x / F x₀)).re ∂μ := by
    refine (Complex.continuous_re.comp hG).integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x₀)
      (hK.comp_left (g := Complex.re) rfl) (fun x => ?_) ?_
    · by_cases hx : b x = 0
      · simp [hx]
      · have hx' : x ∈ Metric.closedBall x₀ r := Metric.ball_subset_closedBall (hs' ▸ hx)
        have h1 : 0 < (F x / F x₀).re := (hb hx').2
        simpa using mul_nonneg b.nonneg h1.le
    · have h1 : b x₀ = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simp [h1, div_self h0]
  have hne : ∫ x, b x • (F x / F x₀) ∂μ ≠ 0 := by
    intro h
    have h2 := integral_re hI
    rw [h] at h2
    simp only [RCLike.re_to_complex, Complex.zero_re] at h2
    exact hpos.ne' h2
  set c := ∫ x, b x • (F x / F x₀) ∂μ with hc'
  have hd : ContDiff ℝ ∞ fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.contDiff.smul contDiff_const
  have hk : HasCompactSupport fun x => b x • ((F x₀)⁻¹ * c⁻¹) := b.hasCompactSupport.smul_right
  refine ⟨hk.toSchwartzMap hd, ?_⟩
  have e : ∀ x, F x * (hk.toSchwartzMap hd) x = (b x • (F x / F x₀)) * c⁻¹ := fun x => by
    change F x * (b x • ((F x₀)⁻¹ * c⁻¹)) = _
    simp only [Complex.real_smul, div_eq_mul_inv]
    ring
  simp only [e]
  rw [integral_mul_const, ← hc', mul_inv_cancel₀ hne]

theorem UpperTheory.V.Af.StrongMultiplicityOne.seedConv :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.SeedConv := by
  intro h E _ _ _ n W hW y hy
  haveI i1 : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  refine exists_schwartz_integral_eq_one volume (chart W 1) (invSet E n) (toL y.val) ?_ ?_ ?_
  · exact GlobalTheory.CuspRep.isOpen_invSet.mem_nhds (GlobalTheory.CuspRep.val_mem_invSet y)
  · exact (h E n W hW).1.comp (f := fun x => ((1 : GA E n), x)) (by fun_prop) fun x hx => ⟨trivial, hx⟩
  · rw [GlobalTheory.CuspRep.chart_val, one_mul]
    exact hy
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.SphAll
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem comm_loc {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {n : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (g : GA E n) (hg : cmp w (GeneralLinearGroup.map (pFin E) g) = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    g * finGL E n (locGL E n w y) = finGL E n (locGL E n w y) * g := by
  refine GlobalTheory.CuspRep.ga_ext ?_ ?_
  · rw [map_mul, map_mul, GlobalTheory.CuspRep.pInf_finGL, mul_one, one_mul]
  · rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL]
    refine cmp_ext fun v => ?_
    rw [map_mul, map_mul]
    by_cases h : v = w
    · subst h
      rw [hg, mul_one, one_mul]
    · have : cmp v (locGL E n w y) = 1 := GlobalTheory.CuspRep.pLoc_locGL_of_ne h y
      rw [this, mul_one, one_mul]

theorem UpperTheory.V.Af.StrongMultiplicityOne.sphAll :
    UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.SphZero → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.SphAll := by
  intro hA hZ hE E _ _ _ n S B W hW hS hK p hp h0
  refine hA E n S (fun k => W (p * finGL E n k) = 0) (fun k hk => (hK p k hk).trans h0) ?_
  intro w hw k _ hk hP y
  have hc : cmp w (GeneralLinearGroup.map (pFin E) (p * finGL E n k)) = 1 := by
    rw [map_mul, map_mul, GlobalTheory.CuspRep.pFin_finGL, hp w hw, hk, mul_one]
  obtain ⟨e1, e2, -, -⟩ := hE E n 0
  have hz := hZ E n w (psiL w) (hS w hw).1 (B w) _ ?_ ((hS w hw).2 (p * finGL E n k)) (by simpa using hP)
  · have := congrFun hz y
    simpa [mul_assoc] using this
  · intro ν hν g
    obtain ⟨a1, a2⟩ := e1 w ν hν
    obtain ⟨b1, b2⟩ := e2 _ a1
    have := hW _ b1 (p * finGL E n k * finGL E n (locGL E n w g))
    rw [b2, a2] at this
    show W _ = _
    rw [map_mul, map_mul, ← mul_assoc, comm_loc w _ hc ν, mul_assoc, this]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Vanish
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R T : Type} [CommRing R] [CommRing T] {n m : ℕ} (φ : R →+* T) {p : GL (Fin n) R}
    (h : IsY m p.val) : IsY m (GeneralLinearGroup.map φ p).val := fun i hi =>
  ⟨by change φ (p.val i i) = 1; rw [(h i hi).1, map_one],
    fun j hj => by change φ (p.val i j) = 0; rw [(h i hi).2 j hj, map_zero]⟩

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := fun i _ =>
  ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_mul {R : Type} [CommRing R] {n m : ℕ} {p q : GL (Fin n) R}
    (hp : IsY m p.val) (hq : IsY m q.val) : IsY m (p * q).val := by
  intro i hi
  have key : ∀ j, j ≤ i → (p * q).val i j = q.val i j := by
    intro j hj
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single i, (hp i hi).1, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hp i hi).2 k h, zero_mul]
      · rw [(hq k (hi.trans h.le)).2 j (hj.trans_lt h), mul_zero]
    · simp
  exact ⟨by rw [key i le_rfl, (hq i hi).1], fun j hj => by rw [key j hj.le, (hq i hi).2 j hj]⟩

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private theorem exists_part (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GL (Fin n) (Af E)) :
    ∃ s : GL (Fin n) (Af E), SuppIn S s ∧ ∀ w ∈ S, cmp w s = cmp w g := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun w _ => map_one _, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  | insert v S hv ih =>
    obtain ⟨s, h1, h2⟩ := ih
    refine ⟨s * locGL E n v (cmp v g), fun w hw => ?_, fun w hw => ?_⟩
    · rw [Finset.mem_insert, not_or] at hw
      rw [map_mul, h1 w hw.2, one_mul]
      exact GlobalTheory.CuspRep.pLoc_locGL_of_ne hw.1 _
    · rw [map_mul]
      rcases Finset.mem_insert.1 hw with rfl | h
      · rw [h1 w hv, one_mul]
        exact GlobalTheory.CuspRep.pLoc_locGL _ _
      · rw [h2 w h, show cmp w (locGL E n v (cmp v g)) = 1 from
          GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : w = v => hv (e ▸ h)) _, mul_one]

private theorem af_ext {x y : Af E} (h : ∀ w, pLoc E w x = pLoc E w y) : x = y :=
  DFunLike.ext _ _ h

private theorem isY_af {m : ℕ} {s : GL (Fin n) (Af E)} (h : ∀ w, IsY m (cmp w s).val) : IsY m s.val := fun i hi =>
  ⟨af_ext fun w => by rw [map_one]; exact (h w i hi).1,
    fun j hj => af_ext fun w => by rw [map_zero]; exact (h w i hi).2 j hj⟩

private theorem pFin_finGL (k : GL (Fin n) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E n k) = k := by
  rw [finGL, GlobalTheory.CuspRep.map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]
  rfl

variable [_root_.NumberField.IsTotallyComplex E]

private theorem isY_ad {m : ℕ} {g : GA E n} (h1 : IsY m (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : IsY m (GeneralLinearGroup.map (pFin E) g).val) : IsY m g.val := fun i hi =>
  ⟨GlobalTheory.CuspRep.ad_ext (by rw [map_one]; exact (h1 i hi).1) (by rw [map_one]; exact (h2 i hi).1),
    fun j hj => GlobalTheory.CuspRep.ad_ext (by rw [map_zero]; exact (h1 i hi).2 j hj) (by rw [map_zero]; exact (h2 i hi).2 j hj)⟩

private theorem exists_dec (S : Finset (HeightOneSpectrum (𝓞 E))) (g : GA E n)
    (h1 : IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val)
    (h2 : ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val) :
    ∃ p k, InPS S p ∧ Away S k ∧ g = p * finGL E n k := by
  obtain ⟨s, hs, hg⟩ := exists_part S (GeneralLinearGroup.map (pFin E) g)
  have e : GeneralLinearGroup.map (pFin E) (infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s) = s := by
    rw [map_mul, GlobalTheory.CuspRep.pFin_infGL, pFin_finGL, one_mul]
  refine ⟨infGL E n (GeneralLinearGroup.map (pInf E) g) * finGL E n s, s⁻¹ * GeneralLinearGroup.map (pFin E) g,
    ⟨isY_ad ?_ ?_, ?_⟩, fun w hw => ?_, ?_⟩
  · rw [map_mul, GlobalTheory.CuspRep.pInf_infGL, GlobalTheory.CuspRep.pInf_finGL, mul_one]
    exact h1
  · rw [e]
    refine isY_af fun w => ?_
    by_cases hw : w ∈ S
    · rw [hg w hw]; exact h2 w hw
    · rw [hs w hw]; exact isY_one
  · rw [e]; exact hs
  · rw [map_mul, map_inv, hg w hw, inv_mul_cancel]
  · rw [mul_assoc, ← map_mul, mul_inv_cancel_left, GlobalTheory.CuspRep.infGL_mul_finGL]

end

theorem UpperTheory.V.Af.StrongMultiplicityOne.vanish :
    UpperTheory.V.Af.StrongMultiplicityOne.SphAll → UpperTheory.V.Af.Smo.InjP → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.WhBasic → UpperTheory.V.Af.StrongMultiplicityOne.EigMap → UpperTheory.V.Af.StrongMultiplicityOne.Vanish := by
  intro hSA hI hD hWB hEM E _ _ _ n hn S B f hf hS hK h0
  have hW : ∀ p, InPS S p → ∀ k, Away S k → whittaker f (p * finGL E n k) = 0 := fun p hp =>
    hSA E n S B (whittaker f) (hWB E n f hf).2.2
      (fun w hw => ⟨(hS w hw).1, (hEM E n w (B w) f (hS w hw).2).1 hf⟩)
      (fun g k hk => by
        unfold whittaker
        simp only [← mul_assoc, hK _ k hk]) p hp.2 (h0 p hp)
  have hX := hI E n hn f hf {g | IsY (n - 1) (GeneralLinearGroup.map (pInf E) g).val ∧
      ∀ w ∈ S, IsY (n - 1) (cmp w (GeneralLinearGroup.map (pFin E) g)).val}
    (fun γ hγ g hg => by
      have h : IsY (n - 1) (ratGL E n γ).val := isY_map _ hγ
      refine ⟨?_, fun w hw => ?_⟩
      · rw [map_mul]; exact isY_mul (isY_map _ h) hg.1
      · rw [map_mul, map_mul]; exact isY_mul (isY_map _ (isY_map _ h)) (hg.2 w hw))
    (fun g hg => by
      obtain ⟨p, k, hp, hk, rfl⟩ := exists_dec S g hg.1 hg.2
      exact hW p hp k hk)
  refine Continuous.ext_on (hD E n S) hf.cont continuous_const ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : f (finGL E n k) = 0 := hX _ ⟨by rw [GlobalTheory.CuspRep.pInf_finGL]; exact isY_one, fun w hw => by
    rw [pFin_finGL, hk w hw]; exact isY_one⟩
  exact (hf.left γ _).trans h
end

