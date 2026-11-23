module

public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceA
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceB
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermUnipotentIntegralVariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermLeviParabolicFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1225
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.EContJoin
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

theorem E_lift {X Y : Type*} (L : ℝ → (X → ℂ) →ₗ[ℂ] (X → ℂ)) (L' : ℝ → (Y → ℂ) →ₗ[ℂ] (Y → ℂ))
    (hL0 : ∀ f, L 0 f = f) (hLL : ∀ s t f, L s (L t f) = L (t + s) f) (f₀ : X → ℂ)
    [FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun t => L t f₀))] (B : (X → ℂ) → (Y → ℂ))
    (hadd : ∀ v ∈ Submodule.span ℂ (Set.range fun t => L t f₀), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (v + w) = B v + B w)
    (hsmul : ∀ (a : ℂ), ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀), B (a • w) = a • B w)
    (c d : ℂ) (hB : ∀ t : ℝ, ∀ w ∈ Submodule.span ℂ (Set.range fun t => L t f₀),
      B (L t w) = Complex.exp (d * t) • L' t (B w))
    (F' : Y → ℂ) (hF' : F' ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀))) (hne : F' ≠ 0)
    (heig : ∀ t : ℝ, L' t F' = Complex.exp (c * t) • F') :
    ∃ F ∈ Submodule.span ℂ (Set.range fun t => L t f₀), F ≠ 0 ∧
      ∀ t : ℝ, L t F = Complex.exp ((c + d) * t) • F := by
  set W := Submodule.span ℂ (Set.range fun t => L t f₀) with hWdef
  have hf₀ : f₀ ∈ W := by
    have h0 : L 0 f₀ ∈ W := Submodule.subset_span ⟨0, rfl⟩
    rwa [hL0] at h0
  have hW : ∀ t, ∀ w ∈ W, L t w ∈ W := by
    intro t w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, rfl⟩ := hx
      rw [hLL]
      exact Submodule.subset_span ⟨u + t, rfl⟩
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact W.smul_mem a hx
  have hL : ∀ s t, ∀ w ∈ W, L s (L t w) = L t (L s w) := fun s t w _ => by rw [hLL, hLL, add_comm]
  have hB0 : B 0 = 0 := by
    have := hsmul 0 0 W.zero_mem
    rwa [zero_smul, zero_smul] at this
  have key : ∀ x ∈ Submodule.span ℂ (Set.range fun t => L' t (B f₀)), ∃ w ∈ W, B w = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine ⟨Complex.exp (-(d * t)) • L t f₀, W.smul_mem _ (Submodule.subset_span ⟨t, rfl⟩), ?_⟩
      rw [hsmul _ _ (Submodule.subset_span ⟨t, rfl⟩), hB t f₀ hf₀, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    | zero => exact ⟨0, W.zero_mem, hB0⟩
    | add x y _ _ hx hy =>
      obtain ⟨v, hv, rfl⟩ := hx
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨v + w, W.add_mem hv hw, hadd v hv w hw⟩
    | smul a x _ hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨a • v, W.smul_mem a hv, hsmul a v hv⟩
  obtain ⟨w₀, hw₀, hBw₀⟩ := key F' hF'
  exact eig_lift W L hL hW L' B hadd hsmul c d hB w₀ hw₀ (hBw₀ ▸ hne) (hBw₀ ▸ heig)

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

def E_vol (E : Type) [Field E] [NumberField E] (N r : ℕ) : ℂ :=
  (((unipMeasure E N r).real (unipFundamentalDomain E N r) : ℝ) : ℂ)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_vol_ne (N r : ℕ) : E_vol E N r ≠ 0 := by
  have := JDict.vol_pos E N r
  unfold E_vol
  exact_mod_cast this.ne'

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_ctn_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    An.ctn r u g = (E_vol E N r)⁻¹ * constantTerm r u g := rfl

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_ct_eq {N : ℕ} (r : ℕ) (u : GA E N → ℂ) (g : GA E N) :
    constantTerm r u g = E_vol E N r * An.ctn r u g := by
  rw [E_ctn_eq, ← mul_assoc, mul_inv_cancel₀ (E_vol_ne N r), one_mul]

theorem E_cont_ctn {N : ℕ} (r : ℕ) {u : GA E N → ℂ} (hc : Continuous u)
    (hl : ∀ γ g, u (ratGL E N γ * g) = u g) : Continuous (An.ctn r u) := by
  have : BorelSpace (BlockIx N r → Ad E) := ⟨JDict.pi_eq_borel E N r⟩
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.ConstNotCusp.exists_compact_ratN E N r
  have hfin : unipMeasure E N r (unipFundamentalDomain E N r) ≠ ⊤ := by
    obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := N) (r := r)
    exact ((measure_mono hDC).trans_lt hC.measure_lt_top).ne
  have h := GlobalTheory.CompanionTheory.CuspL2.continuous_constTerm (unipMeasure E N r) hfin hK hcov hc hl
  refine continuous_const.mul ?_
  convert h using 2 with g
  simp only [constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem E_cont_span {N : ℕ} (r : ℕ) {f : GA E N → ℂ} (hf : Continuous f) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => f (aT E N r t * g)), Continuous w := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, rfl⟩ := hx
    exact hf.comp (continuous_const.mul continuous_id)
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul a x _ hx => exact continuous_const.smul hx

def E_B {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N) (κ : ℂ) (τs : Finset ℝ)
    (a : ℝ → ℂ) (f : GA E N → ℂ) (m : Y) : ℂ :=
  κ * ∑ t ∈ τs, a t * ∫ b, f (P b * Q t m) ∂(Measure.pi fun _ : ι => boxMeasure E)

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_B_add {N : ℕ} {Y ι : Type*} [Fintype ι] {P : (ι → Ad E) → GA E N} (hP : Continuous P) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    E_B P Q κ τs a (f + g) = E_B P Q κ τs a f + E_B P Q κ τs a g := by
  funext m
  simp only [E_B, Pi.add_apply]
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  have hi : ∀ u : GA E N → ℂ, Continuous u →
      Integrable (fun b => u (P b * Q t m)) (Measure.pi fun _ : ι => boxMeasure E) := fun u hu =>
    integrable_box (hu.comp (hP.mul continuous_const))
  rw [← mul_add, ← integral_add (hi f hf) (hi g hg)]

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_B_smul {N : ℕ} {Y ι : Type*} [Fintype ι] (P : (ι → Ad E) → GA E N) (Q : ℝ → Y → GA E N)
    (κ : ℂ) (τs : Finset ℝ) (a : ℝ → ℂ) (c : ℂ) (f : GA E N → ℂ) :
    E_B P Q κ τs a (c • f) = c • E_B P Q κ τs a f := by
  funext m
  simp only [E_B, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [integral_const_mul]
  ring

omit [_root_.NumberField.IsTotallyComplex E] in
theorem E_cont_join {n : ℕ} {S : Finset ℕ} (q : ℕ) :
    Continuous fun b : {x : PPos n S // ¬ IsTop q x} → Ad E => (parGL (joinPos (r := q) 0 b) : GA E n) := by
  refine continuous_parGL.comp (continuous_pi fun x => ?_)
  by_cases hx : IsTop q x
  · simp only [joinPos, dif_pos hx]
    exact continuous_const
  · simp only [joinPos, dif_neg hx]
    exact continuous_apply _

theorem E_pos_top {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop q x) :
    (x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ) ∧ (x.1.2 : ℕ) < q := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_pos_bot {N p q : ℕ} (hpq : p < q) (x : PPos N {p, q}) (hx : ¬ IsTop p x) :
    p ≤ (x.1.1 : ℕ) ∧ (x.1.1 : ℕ) < q ∧ q ≤ (x.1.2 : ℕ) := by
  obtain ⟨s, hs, h1, h2⟩ := x.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at hs
  have hx' : ¬ ((x.1.1 : ℕ) < p ∧ p ≤ (x.1.2 : ℕ)) := hx
  rcases hs with rfl | rfl <;> omega

theorem E_exp_iff (hD : Dict) {N r : ℕ} (φ : Sm E N) (hφ : IsAutForm φ) (h0 : 0 < r) (h1 : r < N) (c : ℂ) :
    c ∈ Exp r φ.1 ↔ ∃ F ∈ Submodule.span ℂ (Set.range fun t : ℝ => fun g => An.ctn r φ.1 (aT E N r t * g)),
      F ≠ 0 ∧ ∀ (t : ℝ) g, F (aT E N r t * g) = Complex.exp (c * t) * F g := by
  have hd := (hD E N).2.2.2 φ hφ r h0 h1
  constructor
  · rintro ⟨F₀, hct, F, hF, hne, heig⟩
    obtain ⟨κ, -, rfl⟩ := hd.2 F₀ hct
    refine ⟨F, Submodule.span_le.2 ?_ hF, hne, heig⟩
    rintro _ ⟨t, rfl⟩
    have e : (fun g => κ * An.ctn r φ.1 (aT E N r t * g)) = κ • fun g => An.ctn r φ.1 (aT E N r t * g) := rfl
    simp only [e]
    exact Submodule.smul_mem _ κ (Submodule.subset_span ⟨t, rfl⟩)
  · rintro ⟨F, hF, hne, heig⟩
    exact ⟨An.ctn r φ.1, hd.1, F, hF, hne, heig⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceD
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.SliceClasses

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}

theorem D_chart_left (F : GA E N → ℂ) (h g : GA E N) : chart (fun x => F (h * x)) g = chart F (h * g) := by
  funext x
  simp only [chart, mul_assoc]

def ltS (h : GA E N) : Sm E N →ₗ[ℂ] Sm E N where
  toFun F := ⟨fun g => F.1 (h * g), fun g => by rw [D_chart_left]; exact F.2 (h * g)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem ltS_apply (h : GA E N) (F : Sm E N) (g : GA E N) : (ltS h F).1 g = F.1 (h * g) := rfl

theorem ltS_act (h : GA E N) (o : Op E N) (F : Sm E N) : ltS h (act o F) = act o (ltS h F) := by
  cases o with
  | fin k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * finGL E N k) = F.1 (h * (g * finGL E N k))
    rw [mul_assoc]
  | cpt k =>
    refine Subtype.ext (funext fun g => ?_)
    change F.1 (h * g * _) = F.1 (h * (g * _))
    rw [mul_assoc]
  | lie X =>
    refine Subtype.ext (funext fun g => ?_)
    change lieD X F.1 (h * g) = lieD X (fun x => F.1 (h * x)) g
    simp only [lieD, D_chart_left]

theorem D_ct_smooth (r : ℕ) (φ : Sm E N) (hl : ∀ γ g, φ.1 (ratGL E N γ * g) = φ.1 g)
    (hlev : IsOpen {k | finRep E N k φ = φ}) :
    ∃ F : Sm E N, F.1 = An.ctn r φ.1 ∧ ∀ X, (lie E N X F).1 = An.ctn r (lie E N X φ).1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  obtain ⟨F, h1, h2⟩ := GlobalTheory.CompanionTheory.CTSmooth.ct_smooth E N r φ hl hlev μ _ hμ hD
  have key : ∀ (f : GA E N → ℂ) g, ∫ x in unipFundamentalDomain E N r, f (unip x * g) ∂μ = An.ctn r f g := by
    intro f g
    rw [hint]
    simp only [An.ctn, constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]
  exact ⟨F, funext fun g => (h1 g).trans (key _ g), fun X => funext fun g => (h2 X g).trans (key _ g)⟩


open Classical in
def ctSm (r : ℕ) (φ : Sm E N) : Sm E N := if h : An.ctn r φ.1 ∈ Sm E N then ⟨_, h⟩ else 0

theorem ctSm_val (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) : (ctSm r φ).1 = An.ctn r φ.1 := by
  obtain ⟨F, hF, -⟩ := D_ct_smooth r φ hφ.left hφ.level
  have h : An.ctn r φ.1 ∈ Sm E N := hF ▸ F.2
  simp only [ctSm, dif_pos h]

theorem ctn_add (r : ℕ) {f g : GA E N → ℂ} (hf : Continuous f) (hg : Continuous g) :
    An.ctn r (f + g) = An.ctn r f + An.ctn r g := by
  funext x
  simp only [An.ctn, Pi.add_apply, constantTerm_add hf hg, mul_add]

theorem ctn_smul (r : ℕ) (c : ℂ) (f : GA E N → ℂ) : An.ctn r (c • f) = c • An.ctn r f := by
  funext x
  simp only [An.ctn, Pi.smul_apply, constantTerm_smul, smul_eq_mul]
  ring

theorem ctSm_act (r : ℕ) {φ : Sm E N} (hφ : IsAutForm φ) (o : Op E N) (hφ' : IsAutForm (act o φ)) :
    ctSm r (act o φ) = act o (ctSm r φ) := by
  obtain ⟨F, hF, hX⟩ := D_ct_smooth r φ hφ.left hφ.level
  have e : ctSm r φ = F := Subtype.ext ((ctSm_val r hφ).trans hF.symm)
  refine Subtype.ext ?_
  rw [ctSm_val r hφ', e]
  cases o with
  | fin k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * finGL E N k)) g = F.1 (g * finGL E N k)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | cpt k =>
    funext g
    change An.ctn r (fun x => φ.1 (x * _)) g = F.1 (g * _)
    rw [hF]
    simp only [An.ctn, constantTerm, mul_assoc]
  | lie X => exact (hX X).symm

def Aop (N r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) : Module.End ℂ (Sm E N) := ∑ t ∈ τs, a t • ltS (aT E N r t)

theorem Aop_apply (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (F : Sm E N) (g : GA E N) :
    (Aop N r τs a F).1 g = ∑ t ∈ τs, a t * F.1 (aT E N r t * g) := by
  simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply, ltS_apply, smul_eq_mul]

theorem Aop_act (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) (o : Op E N) (F : Sm E N) :
    Aop N r τs a (act o F) = act o (Aop N r τs a F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Aop, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, ltS_act]

theorem exists_strictHenselian_absolutely_closed_local_ring (V : Submodule ℂ (Sm E N)) (hV : ∀ φ ∈ V, IsAutForm φ) (r : ℕ) (τs : Finset ℝ) (a : ℝ → ℂ) :
    ∃ T : Sm E N →ₗ[ℂ] Sm E N, ∀ φ ∈ V, T φ = Aop N r τs a (ctSm r φ) := by
  let T₁ : V →ₗ[ℂ] Sm E N :=
    { toFun := fun φ => Aop N r τs a (ctSm r φ.1)
      map_add' := fun φ ψ => by
        have e : ctSm r (φ.1 + ψ.1) = ctSm r φ.1 + ctSm r ψ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_add, ctSm_val r (hV _ (V.add_mem φ.2 ψ.2)), ctSm_val r (hV _ φ.2),
            ctSm_val r (hV _ ψ.2)]
          exact ctn_add r (ContAut.continuous_of_isOpen_stab E N _ (hV _ φ.2).level)
            (ContAut.continuous_of_isOpen_stab E N _ (hV _ ψ.2).level)
        simp only [Submodule.coe_add, e, map_add (f := _)]
      map_smul' := fun c φ => by
        have e : ctSm r (c • φ.1) = c • ctSm r φ.1 := by
          refine Subtype.ext ?_
          rw [Submodule.coe_smul, ctSm_val r (hV _ (V.smul_mem c φ.2)), ctSm_val r (hV _ φ.2)]
          exact ctn_smul r c _
        simp only [Submodule.coe_smul, e, map_smul, RingHom.id_apply] }
  obtain ⟨T, hT⟩ := LinearMap.exists_extend T₁
  exact ⟨T, fun φ hφ => LinearMap.congr_fun hT ⟨φ, hφ⟩⟩

end PositivityTheory.Rg.Rs.SliceClasses

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStringStepB
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs.StrStepB

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem absC_unrAt (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (GlobalTheory.CuspRep.Model.absC E s).UnrAt w := by
  intro x hx
  apply Units.ext
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = 1
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x 0 (by simpa [IsUnitAt] using hx)]
  simp

theorem absC_val (s : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((GlobalTheory.CuspRep.Model.absC E s).val w : ℂˣ) : ℂ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (-s) := by
  change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w (atFin w (unif w)))) = _
  have h0 : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w _ 1 (unif_spec w), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
    ← Complex.natCast_log]
  congr 1; push_cast; ring

theorem absC_add (s t : ℂ) :
    GlobalTheory.CuspRep.Model.absC E (s + t) = GlobalTheory.CuspRep.Model.absC E s * GlobalTheory.CuspRep.Model.absC E t := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change Complex.exp ((s + t) * _) = Complex.exp (s * _) * Complex.exp (t * _)
  rw [← Complex.exp_add, add_mul]

theorem absC_zero : GlobalTheory.CuspRep.Model.absC E 0 = 1 := by
  refine Subtype.ext (MonoidHom.ext fun x => Units.ext ?_)
  change Complex.exp (0 * _) = 1
  simp

theorem hasSat_twist_absC {a : ℕ} (π : CuspSub E a) {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (h : (CG.mk π).HasSat w B) (x : ℂ) :
    ((CG.mk π).twist (GlobalTheory.CuspRep.Model.absC E x)).HasSat w (B.map (· * (GlobalTheory.CuspRep.Model.absC E x).val w)) :=
  GlobalTheory.SphGal.hasSatGL_twist E a π _ w B (absC_unrAt x w) h

abbrev dC (b : ℕ) : Lie E b := fun i j => if i = j then (1 : Cinf E) else 0

theorem lie_dC_eq_zero {b : ℕ} {ρ : CuspSub E b} (h : IsNormalised ρ) {φ : Sm E b} (hφ : φ ∈ ρ.V) :
    lie E b (dC b) φ = 0 := by
  refine Subtype.ext (funext fun g => ?_)
  have h1 := GlobalTheory.CuspRep.SplitDeriv.hasDerivAt_splitCentre φ g 0
  have h2 : (fun t : ℝ => φ.1 (g * splitCentre E b t)) = fun _ => φ.1 g := funext fun t => by
    rw [← GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm]; exact h φ hφ t g
  rw [h2, GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_zero, mul_one] at h1
  rw [h1.unique (hasDerivAt_const 0 _)]
  rfl

theorem opAdd_dC (c : ℂ) (b : ℕ) :
    opAdd (GlobalTheory.CuspRep.Model.absC E c) (.lie (dC b) : Op E b) = c * (2 * b * Fintype.card (InfinitePlace E)) := by
  change dchi (GlobalTheory.CuspRep.Model.absC E c) (Matrix.of (dC (E := E) b)).trace = _
  rw [GlobalTheory.GKCoh.Tests.dchi_absC]
  have e : ∀ w, (Matrix.of (dC (E := E) b)).trace w = b := fun w => by
    simp [Matrix.trace, dC, Finset.sum_apply]
  simp only [e, Complex.natCast_re]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  push_cast
  ring

theorem eq_zero_of_iso_twist {b : ℕ} (hb : 1 ≤ b) {ρ ρ' : CuspSub E b} (h : IsNormalised ρ) (h' : IsNormalised ρ')
    {c : ℂ} (e : ρ.Iso (ρ'.twist (GlobalTheory.CuspRep.Model.absC E c))) : c = 0 := by
  obtain ⟨T, hT⟩ := e
  have := Submodule.nontrivial_iff_ne_bot.2 ρ.ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : ρ.V)
  obtain ⟨ψ, hψ⟩ := (ρ'.toTwist (GlobalTheory.CuspRep.Model.absC E c)).surjective (T φ)
  have h1 := hT (.lie (dC b)) φ
  have h2 : ρ.op (.lie (dC b)) φ = 0 := Subtype.ext (lie_dC_eq_zero h φ.2)
  have h3 : ρ'.op (.lie (dC b)) ψ = 0 := Subtype.ext (lie_dC_eq_zero h' ψ.2)
  rw [h2, T.map_zero, ← hψ, CuspSub.op_toTwist, h3, opAdd_dC, smul_zero, zero_add] at h1
  have h4 : (c * (2 * b * Fintype.card (InfinitePlace E)) : ℂ) • ψ = 0 :=
    (ρ'.toTwist _).injective (h1.symm.trans (ρ'.toTwist _).map_zero.symm)
  have hψ0 : ψ ≠ 0 := fun e0 => hφ (T.injective (by rw [← hψ, e0, (ρ'.toTwist _).map_zero, T.map_zero]))
  have hK : (2 * b * Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
    have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hc' : (Fintype.card (InfinitePlace E) : ℂ) ≠ 0 := by exact_mod_cast this.ne'
    exact mul_ne_zero (mul_ne_zero two_ne_zero hb') hc'
  rcases smul_eq_zero.1 h4 with h5 | h5
  · exact (mul_eq_zero.1 h5).resolve_right hK
  · exact absurd h5 hψ0

theorem match_twist {b b' : ℕ} (hb : 1 ≤ b) (ρ : CuspSub E b) (ρ' : CuspSub E b') (h : IsNormalised ρ)
    (h' : IsNormalised ρ') {u u' : ℂ}
    (e : (⟨b, (CG.mk ρ).twist (GlobalTheory.CuspRep.Model.absC E u)⟩ : Σ c, CG E c) =
      ⟨b', (CG.mk ρ').twist (GlobalTheory.CuspRep.Model.absC E u')⟩) :
    u = u' ∧ (⟨b, CG.mk ρ⟩ : Σ c, CG E c) = ⟨b', CG.mk ρ'⟩ := by
  obtain ⟨rfl, e2⟩ := Sigma.mk.inj_iff.1 e
  have e3 : CG.mk ρ = CG.mk (ρ'.twist (GlobalTheory.CuspRep.Model.absC E (u' - u))) := by
    have := congrArg (fun π : CG E b => π.twist (GlobalTheory.CuspRep.Model.absC E (-u))) (eq_of_heq e2)
    simp only [← CG.twist_mul, ← absC_add] at this
    rw [add_neg_cancel, absC_zero, CG.twist_one] at this
    rw [this, CG.twist_mk, sub_eq_add_neg]
  have hI : ρ.Iso (ρ'.twist (GlobalTheory.CuspRep.Model.absC E (u' - u))) := Quotient.exact e3
  have h0 := eq_zero_of_iso_twist hb h h' hI
  obtain rfl : u = u' := by linear_combination -h0
  refine ⟨rfl, ?_⟩
  rw [e3, sub_self, absC_zero, CuspSub.twist_one]

end PositivityTheory.Rg.Rs.StrStepB

end
end

