module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PositionOf

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ArchSlotEx
section
open MeasureTheory
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]

private theorem asx_cvPow {a : G → ℂ} (ha : Continuous a) (ha' : HasCompactSupport a) (k : ℕ) :
    Continuous (cvPow μ a k) ∧ HasCompactSupport (cvPow μ a k) := by
  induction k with
  | zero => exact ⟨ha, ha'⟩
  | succ k ih =>
    have h := cvBasic G μ a (cvPow μ a k) a ha ha' ih.1 ih.2 ha ha'
    exact ⟨h.1, h.2.1⟩

private theorem asx_star {b : G → ℂ} (hb : Continuous b) (hb' : HasCompactSupport b) :
    Continuous (fun x => conj (b x⁻¹)) ∧ HasCompactSupport (fun x => conj (b x⁻¹)) := by
  refine ⟨by fun_prop, ?_⟩
  have h : HasCompactSupport (fun x => b x⁻¹) := hb'.comp_homeomorph (Homeomorph.inv G)
  exact h.comp_left (g := fun z : ℂ => conj z) (map_zero _)

end

end UpperTheory.ConvolutionTheory.L1

open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.L1 in
theorem UpperTheory.ConvolutionTheory.L1.archPositionEx :
    UpperTheory.ConvolutionTheory.L1.ArchSlotEx := by
  intro F E _ _ _ _ _ σ m D n νF _ b hs hf hn
  obtain ⟨-, -, -, -, -, -, hHaar, hTens⟩ := archBasic F E σ m D n
  have hb : Continuous (fun g => b g) := map_continuous b
  have hb' : HasCompactSupport (fun g => b g) := b.hasCompactSupport
  obtain ⟨h1, h2⟩ := asx_star hb hb'
  have hc := cvBasic _ νF (fun g => b g) (fun x => conj (b x⁻¹)) (fun g => b g) hb hb' h1 h2 hb hb'
  let a : TI F n := ⟨⟨cv νF (fun g => b g) (fun x => conj (b x⁻¹)), hc.1⟩, hc.2.1⟩
  obtain ⟨aE, haE⟩ := hTens fun _ => a
  obtain ⟨h3, h4⟩ := asx_cvPow νF (a := fun g => a g) (map_continuous a) a.hasCompactSupport m
  let aF : TI F n := ⟨⟨cvPow νF (fun g => a g) m, h3⟩, h4⟩
  exact ⟨_, hHaar νF, a, aE, aF,
    { meas := rfl, smooth := hs, fin := hf, norm := hn, sq := fun _ => rfl, tens := haE, pow := fun _ => rfl }⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchSplit
section
open MeasureTheory PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.L1

private theorem prod_ofFn_single {G : Type*} [Monoid G] : ∀ (n : ℕ) (f : Fin n → G) (k : Fin n),
    (∀ i, i ≠ k → f i = 1) → (List.ofFn f).prod = f k
  | 0, _, k, _ => k.elim0
  | n + 1, f, k, h => by
    rw [List.ofFn_succ, List.prod_cons]
    cases k using Fin.cases with
    | zero =>
      rw [List.prod_eq_one, mul_one]
      exact List.forall_mem_ofFn_iff.2 fun i => h _ (Fin.succ_ne_zero i)
    | succ k =>
      rw [h 0 (Fin.succ_ne_zero k).symm, one_mul,
        prod_ofFn_single n (fun i => f i.succ) k fun i hi => h _ fun h' => hi (Fin.succ_injective _ h')]

private theorem transport (X Y T : Type) [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] [Group T] [MeasurableSpace T]
    [MeasurableInv T] [Group Y] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure X) [μ.IsHaarMeasure] (ν : Measure T) [SFinite ν] [ν.IsInvInvariant] (i : T →* X) (hi : Measurable i)
    (e : X ≃ₜ Y) (he : ∀ a b, e (a * b) = e a * e b) (j : T → Y) (hj : ∀ t, j t = e (i t)) (Φ : Y → ℂ)
    (hΦ : Measurable fun x => Φ (e x)) (hinv : ∀ t x, Φ (e (i t * x)) = Φ (e x))
    (hfin : ∀ ρ, IsNormAlong id i ν ρ → ∫⁻ x, ‖Φ (e x)‖ₑ * ρ x ∂μ < ⊤) (c : ℝ) (hc : 0 ≤ c) :
    quotInt (ENNReal.ofReal c • μ.map e) id j ν Φ = c * quotInt μ id i ν fun x => Φ (e x) := by
  by_cases h : ∃ ρ, IsNormAlong id j ν ρ
  · have hρ := h.choose_spec
    have h' : IsNormAlong id i ν fun x => h.choose (e x) := by
      refine ⟨hρ.1.comp e.continuous.measurable, fun x => ?_⟩
      have := hρ.2 (e x)
      simpa only [id, he, hj] using this
    rw [quotAny X T μ ν i hi _ _ hΦ hinv h' (hfin _ h'), quotInt, dite_eq_left h, integral_smul_measure,
      e.measurableEmbedding.integral_map, ENNReal.toReal_ofReal hc]
    simp
  · have h' : ¬ ∃ ρ, IsNormAlong id i ν ρ := by
      rintro ⟨ρ, hρ⟩
      refine h ⟨fun y => ρ (e.symm y), hρ.1.comp e.symm.continuous.measurable, fun y => ?_⟩
      obtain ⟨x, rfl⟩ := e.surjective y
      have := hρ.2 x
      simpa only [id, hj, ← he, e.symm_apply_apply] using this
    rw [quotInt, dite_eq_right h, quotInt, dite_eq_right h', mul_zero]

private theorem invInv {T : Type} [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] (h : ∀ a b : T, a * b = b * a) (ν : Measure T)
    [ν.IsHaarMeasure] : ν.IsInvInvariant := by
  letI : CommGroup T := { (inferInstance : Group T) with mul_comm := h }
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular ν

theorem matchSplit :
    UpperTheory.ConvolutionTheory.L1.MatchSplit := by
  intro R S _ _ _ _ _ _ _ _ _ ι s m D n _ _ _ _ μS μR hS hR hreg
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := glueBasic R S ι s m D n
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin n) R) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) R) := Units.isEmbedding_embedProduct.secondCountableTopology
  let e : (Fin (m + 1) → GL (Fin n) R) ≃ₜ GL (Fin n) S :=
    { toFun := D.glue n
      invFun := fun x i => D.comp n i x
      left_inv := fun g => funext (h1 g)
      right_inv := h2
      continuous_toFun := h4
      continuous_invFun := continuous_pi h5 }
  let e' : (Fin (m + 1) → GL (Fin n) R) ≃* GL (Fin n) S := { e.toEquiv with map_mul' := h3 }
  haveI : LocallyCompactSpace (GL (Fin n) S) := e.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) S) := e.symm.isEmbedding.secondCountableTopology
  haveI hH : (Measure.map (D.glue n) (Measure.pi fun _ : Fin (m + 1) => μR)).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map (Measure.pi fun _ : Fin (m + 1) => μR) e' h4 (continuous_pi h5)
  set c := Measure.haarScalarFactor μS (Measure.map (D.glue n) (Measure.pi fun _ : Fin (m + 1) => μR)) with hc
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hμ : μS = ENNReal.ofReal (c : ℝ) • Measure.map (D.glue n) (Measure.pi fun _ : Fin (m + 1) => μR) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨c, hcpos, hμ, fun φ hφ hφc => ?_⟩
  have hΦ : Continuous fun g => φ (D.glue n g) := hφ.comp h4
  have hΦc : HasCompactSupport fun g => φ (D.glue n g) := hφc.comp_homeomorph e
  obtain ⟨p1, p2, -⟩ := pushTest _ μR m _ hΦ hΦc
  refine ⟨p1, p2, fun γ hγ ν hν => ⟨fun δ hδ => ?_, fun hn => (hn ?_).elim⟩⟩
  · obtain ⟨r1, r2⟩ := hreg γ hγ
    obtain ⟨d1, d2, -⟩ := (h8 δ γ).1 hδ
    obtain ⟨g1, g2⟩ := geoAbs _ μR m γ r1 r2 ν (fun i => D.comp n i δ) d1 d2 _ hΦ hΦc
    have hcl : IsClosed (Subgroup.centralizer {γ} : Set (GL (Fin n) R)) := by
      have : (Subgroup.centralizer {γ} : Set (GL (Fin n) R)) = {x | γ * x = x * γ} := by
        ext x
        simp [Subgroup.mem_centralizer_iff]
      rw [this]
      exact isClosed_eq (by fun_prop) (by fun_prop)
    haveI : LocallyCompactSpace (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) R)) := hcl.locallyCompactSpace
    haveI : SecondCountableTopology (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) R)) :=
      TopologicalSpace.Subtype.secondCountableTopology _
    haveI : ν.IsInvInvariant := invInv (fun a b => Subtype.ext (r2 _ a.2 _ b.2)) ν
    let i : (Subgroup.centralizer {γ} : Subgroup (GL (Fin n) R)) →* (Fin (m + 1) → GL (Fin n) R) :=
      MonoidHom.pi fun _ => Subgroup.subtype _
    have hi : Continuous i := continuous_pi fun _ => continuous_subtype_val
    have key : ∀ x, (e x)⁻¹ * δ * mapGL n s (e x) = D.glue n fun k => (x k)⁻¹ * D.comp n k δ * x (k + 1) := by
      intro x
      rw [← h2 ((e x)⁻¹ * δ * mapGL n s (e x))]
      congr 1
      funext k
      rw [map_mul, map_mul, map_inv, h7]
      exact congrArg₂ (· * ·) (congrArg (fun y => y⁻¹ * _) (h1 x k)) (h1 x (k + 1))
    have := transport _ (GL (Fin n) S) _ (Measure.pi fun _ : Fin (m + 1) => μR) ν i hi.measurable e h3
      (fun t => mapGL n ι (t : GL (Fin n) R)) (fun t => by
        rw [← h2 (mapGL n ι (t : GL (Fin n) R))]
        exact congrArg (D.glue n) (funext fun k => h6 _ k))
      (fun x => φ (x⁻¹ * δ * mapGL n s x)) (by
        simp only [key]
        exact (hΦ.comp (by fun_prop)).measurable) (fun t x => by
        simp only [key]
        congr 2
        funext k
        have := (Subgroup.mem_centralizer_iff.1 t.2)
        have h := r2 _ t.2 _ (d1 k)
        show ((t : GL (Fin n) R) * x k)⁻¹ * _ * ((t : GL (Fin n) R) * x (k + 1)) = _
        rw [mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc (D.comp n k δ), ← h, mul_assoc, inv_mul_cancel_left,
          mul_assoc]) (by
        simp only [key]
        exact g1) c c.2
    simp only [key] at this
    rw [twOrb, orb, hμ]
    exact this.trans (congrArg _ g2)
  · have hs : ∀ j : Fin (m + 1),
        (List.ofFn fun i => D.comp n (j + i) (D.glue n (Pi.mulSingle 0 γ))).prod = γ := by
      intro j
      rw [prod_ofFn_single _ _ (-j) fun i hi => by
        rw [h1, Pi.mulSingle_eq_of_ne fun h => hi (eq_neg_of_add_eq_zero_right h)]]
      rw [h1, add_neg_cancel, Pi.mulSingle_eq_same]
    refine ⟨D.glue n (Pi.mulSingle 0 γ), (h8 _ _).2 ⟨fun k => ?_, by simpa only [zero_add] using hs 0, hs⟩⟩
    rw [h1]
    by_cases hk : k = 0
    · subst hk
      rw [Pi.mulSingle_eq_same]
      simp [Subgroup.mem_centralizer_iff]
    · rw [Pi.mulSingle_eq_of_ne hk]
      exact one_mem _

end UpperTheory.ConvolutionTheory.L1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensOp
section
open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

section General

variable {G Γ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem ofFn_prod_single {M : Type} [Monoid M] :
    ∀ (k : ℕ) (a : Fin k → M) (j : Fin k), (∀ i, i ≠ j → a i = 1) → (List.ofFn a).prod = a j := by
  intro k
  induction k with
  | zero => intro a j; exact j.elim0
  | succ k ih =>
    intro a j h
    rw [List.ofFn_succ, List.prod_cons]
    refine Fin.cases ?_ (fun j' => ?_) j (motive := fun j => (∀ i, i ≠ j → a i = 1) → a 0 * (List.ofFn fun i => a i.succ).prod = a j) h
    · intro h
      rw [List.prod_eq_one, mul_one]
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact h _ (Fin.succ_ne_zero i)
    · intro h
      rw [h 0 (Fin.succ_ne_zero j').symm, one_mul]
      exact ih (fun i => a i.succ) j' fun i hi => h _ (fun e => hi (Fin.succ_injective _ e))

private theorem ofFn_mulSingle {k : ℕ} (g : Fin k → G) :
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin k → G)).prod = g := by
  funext j
  have e := map_list_prod (Pi.evalMonoidHom (fun _ : Fin k => G) j)
    (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin k → G))
  simp only [Pi.evalMonoidHom_apply] at e
  rw [e, List.map_ofFn]
  refine (ofFn_prod_single k _ j fun i hi => ?_).trans ?_
  · simp [Pi.mulSingle_eq_of_ne hi.symm]
  · simp

private theorem continuous_ofFn_prod : ∀ (k : ℕ) (s : Fin k → G →* Γ), (∀ i, Continuous (s i)) →
    Continuous fun g : Fin k → G => (List.ofFn fun i => s i (g i)).prod := by
  intro k
  induction k with
  | zero => intro s _; simpa using continuous_const
  | succ k ih =>
    intro s hs
    simp only [List.ofFn_succ, List.prod_cons]
    exact ((hs 0).comp (continuous_apply 0)).mul
      ((ih (fun i => s i.succ) fun i => hs _).comp
        (continuous_pi fun i => continuous_apply i.succ))

private theorem inner_cc (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (π : UnitaryRep G H)
    (f : CompactlySupportedContinuousMap G ℂ) (w v : H) :
    ⟪w, π.integrated μ (UnitaryRep.ccToL1 μ f) v⟫_ℂ = ∫ g, f g * ⟪w, π g v⟫_ℂ ∂μ := by
  have hint : Integrable (fun g => f g • π g v) μ :=
    (f.continuous.smul (π.continuous_orbit v)).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  rw [UnitaryRep.integrated_ccToL1_apply, ← integral_inner hint]
  simp only [inner_smul_right]

private theorem inner_ofFn_prod (μ : Measure G) [SigmaFinite μ] [IsFiniteMeasureOnCompacts μ]
    (π : UnitaryRep Γ H) : ∀ (k : ℕ) (s : Fin k → G →* Γ) (hs : ∀ i, Continuous (s i))
    (φ : Fin k → CompactlySupportedContinuousMap G ℂ) (w v : H),
    ⟪w, (List.ofFn fun i => (π.compHom (s i) (hs i)).integrated μ (UnitaryRep.ccToL1 μ (φ i))).prod v⟫_ℂ =
      ∫ g : Fin k → G, (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ
        ∂(Measure.pi fun _ => μ) := by
  intro k
  induction k with
  | zero =>
    intro s hs φ w v
    rw [Measure.pi_of_empty (fun _ : Fin 0 => μ) (fun i => i.elim0), integral_dirac]
    simp
  | succ k ih =>
    intro s hs φ w v
    have hint : ∀ i, Integrable (φ i) μ := fun i =>
      (φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport
    have hF : Integrable (fun g : Fin (k + 1) → G =>
        (∏ i, φ i (g i)) * ⟪w, π (List.ofFn fun i => s i (g i)).prod v⟫_ℂ)
        (Measure.pi fun _ => μ) := by
      refine (Integrable.fintype_prod (f := fun i => (φ i : G → ℂ)) hint).mul_bdd
        (c := ‖w‖ * ‖v‖) ?_ (Filter.Eventually.of_forall fun g => π.norm_inner_orbit_le w v _)
      exact (continuous_const.inner ((π.continuous_orbit v).comp
        (continuous_ofFn_prod _ s hs))).aestronglyMeasurable
    have mp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => μ) 0).symm
    rw [← mp.integral_comp' _]
    refine Eq.trans ?_ (integral_prod _ (mp.integrable_comp_of_integrable hF)).symm
    rw [List.ofFn_succ, List.prod_cons, ContinuousLinearMap.mul_apply, inner_cc]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [UnitaryRep.compHom_apply]
    rw [UnitaryRep.inner_map_right, ih (fun i => s i.succ) (fun i => hs _) (fun i => φ i.succ),
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.prod_univ_succ, List.ofFn_succ,
      List.prod_cons, Fin.insertNthEquiv_zero, Fin.cons_zero, Fin.cons_succ]
    show _ = (φ 0 x * ∏ i, φ i.succ (g i)) *
      ⟪w, π (s 0 x * (List.ofFn fun i => s i.succ (g i)).prod) v⟫_ℂ
    rw [UnitaryRep.map_mul_apply, UnitaryRep.inner_map_right π (s 0 x) w]
    ring

end General

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensOp :
    UpperTheory.ConvolutionTheory.L1.TensOp := by
  intro F E _ _ _ _ _ σ m D n νE _ νF _ hν s hs hposition H _ _ _ π φ β hβ
  obtain ⟨hcg, -, hmul, hcont, -⟩ := UpperTheory.ConvolutionTheory.L1.archBasic F E σ m D n
  have hglue : ∀ g : Fin (m + 1) → archGroup F n,
      UpperTheory.ConvolutionTheory.L1.glueA D n g = (List.ofFn fun i => s i (g i)).prod := by
    intro g
    have e := map_list_prod (MonoidHom.mk' (UpperTheory.ConvolutionTheory.L1.glueA D n) hmul)
      (List.ofFn fun i => (Pi.mulSingle i (g i) : Fin (m + 1) → archGroup F n))
    rw [UpperTheory.ConvolutionTheory.L1.ofFn_mulSingle, List.map_ofFn] at e
    refine e.trans ?_
    congr 1
    congr 1
    funext i
    exact (hposition i (g i)).symm
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun w => ?_
  rw [UpperTheory.ConvolutionTheory.L1.inner_ofFn_prod, UpperTheory.ConvolutionTheory.L1.inner_cc]
  have hm : Continuous fun x : archGroup E n => β x * ⟪w, π x v⟫_ℂ :=
    β.continuous.mul (continuous_const.inner (π.continuous_orbit v))
  have e1 : ∫ x, β x * ⟪w, π x v⟫_ℂ ∂νE = ∫ x, β x * ⟪w, π x v⟫_ℂ
      ∂(Measure.map (UpperTheory.ConvolutionTheory.L1.glueA D n) (Measure.pi fun _ => νF)) := by
    rw [← hν]
  rw [e1, integral_map hcont.aemeasurable hm.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  rw [hβ, hglue g]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hglue g, hcg]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmoothAlt
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory
open scoped ContDiff

namespace UpperTheory.ConvolutionTheory.L1

private theorem fin_prod {ι X : Type} [Fintype ι] {Y : ι → Type} (p : ∀ i, X → Y i) (S : ∀ i, Set (Y i → ℂ))
    (hS : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ (S i))) :
    FiniteDimensional ℂ (Submodule.span ℂ
      {f : X → ℂ | ∃ s : ∀ i, Y i → ℂ, (∀ i, s i ∈ S i) ∧ f = fun x => ∏ i, s i (p i x)}) := by
  classical
  let T : (∀ i, Y i → ℂ) →ₘₗ[ℂ] (X → ℂ) :=
    (MultilinearMap.mkPiAlgebra ℂ ι (X → ℂ)).compLinearMap (fun i => LinearMap.funLeft ℂ ℂ (p i))
  have hT : ∀ s x, T s x = ∏ i, s i (p i x) := by
    intro s x
    simp [T, MultilinearMap.compLinearMap_apply, Finset.prod_apply, LinearMap.funLeft_apply]
  let d : ι → ℕ := fun i => Module.finrank ℂ (Submodule.span ℂ (S i))
  let b : ∀ i, Module.Basis (Fin (d i)) ℂ (Submodule.span ℂ (S i)) := fun i => Module.finBasis ℂ _
  let R : Set (X → ℂ) := Set.range fun r : ∀ i, Fin (d i) => T fun i => ((b i (r i) : Submodule.span ℂ (S i)) : Y i → ℂ)
  have hR : R.Finite := Set.finite_range _
  have hle : Submodule.span ℂ {f : X → ℂ | ∃ s : ∀ i, Y i → ℂ, (∀ i, s i ∈ S i) ∧ f = fun x => ∏ i, s i (p i x)} ≤
      Submodule.span ℂ R := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨s, hs, rfl⟩
    have hs' : ∀ i, s i ∈ Submodule.span ℂ (S i) := fun i => Submodule.subset_span (hs i)
    let c : ∀ i, Fin (d i) → ℂ := fun i j => (b i).repr ⟨s i, hs' i⟩ j
    have hsum : ∀ i, s i = ∑ j, c i j • ((b i j : Submodule.span ℂ (S i)) : Y i → ℂ) := by
      intro i
      have h := (b i).sum_repr ⟨s i, hs' i⟩
      calc s i = ((⟨s i, hs' i⟩ : Submodule.span ℂ (S i)) : Y i → ℂ) := rfl
        _ = ((∑ j, c i j • b i j : Submodule.span ℂ (S i)) : Y i → ℂ) := by rw [h]
        _ = _ := by rw [AddSubmonoidClass.coe_finsetSum]; rfl
    have e : (fun x => ∏ i, s i (p i x)) = T s := funext fun x => (hT s x).symm
    have e2 : T s = T fun i => ∑ j, c i j • ((b i j : Submodule.span ℂ (S i)) : Y i → ℂ) :=
      congrArg T (funext hsum)
    show (fun x => ∏ i, s i (p i x)) ∈ (Submodule.span ℂ R : Set (X → ℂ))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, e2, MultilinearMap.map_sum]
    refine Submodule.sum_mem _ fun r _ => ?_
    rw [MultilinearMap.map_smul_univ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ R) := FiniteDimensional.span_of_finite ℂ hR
  exact Submodule.finiteDimensional_of_le hle

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {m : ℕ}

private def cR (D : InfD σ m) (i : Fin (m + 1)) : InfiniteAdeleRing E →+* InfiniteAdeleRing F :=
  (Pi.evalRingHom (fun _ : Fin (m + 1) => InfiniteAdeleRing F) i).comp D.e.toRingHom

private theorem continuous_cR (D : InfD σ m) (i : Fin (m + 1)) : Continuous (cR D i) :=
  (continuous_apply i).comp D.cont

private def thetaR (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : ArchMatrix E n →+* ArchMatrix F n :=
  (archMatrixEquiv F n).toRingHom.comp ((RingHom.mapMatrix (cR D i)).comp (archMatrixEquiv E n).symm.toRingHom)

private theorem continuous_thetaR (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : Continuous (thetaR D n i) := by
  have h1 : Continuous fun M : Matrix (Fin n) (Fin n) (InfiniteAdeleRing E) => M.map (cR D i) :=
    continuous_id.matrix_map (continuous_cR D i)
  exact (continuous_archMatrixEquiv F n).comp (h1.comp (continuous_archMatrixEquiv_symm E n))

private theorem compA_val (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (g : archGroup E n) :
    (((compA D n i g : archGroup F n) : (ArchMatrix F n)ˣ) : ArchMatrix F n) =
      thetaR D n i ((g : (ArchMatrix E n)ˣ) : ArchMatrix E n) := rfl

private theorem thetaR_exp (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (X : ArchMatrix E n) :
    thetaR D n i (NormedSpace.exp X) = NormedSpace.exp (thetaR D n i X) := by
  letI : NormedAlgebra ℚ (ArchMatrix E n) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (ArchMatrix F n) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (thetaR D n i) (continuous_thetaR D n i) X

private def thetaL (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) : archLie E n →L[ℝ] archLie F n where
  toFun Y := ⟨thetaR D n i (Y : ArchMatrix E n), Submodule.mem_top⟩
  map_add' X Y := Subtype.ext (map_add (thetaR D n i) _ _)
  map_smul' c X := Subtype.ext (map_real_smul (thetaR D n i) (continuous_thetaR D n i) c _)
  cont := ((continuous_thetaR D n i).comp continuous_subtype_val).subtype_mk _

private theorem compA_expG (D : InfD σ m) (n : ℕ) (i : Fin (m + 1)) (Y : archLie E n) :
    compA D n i ((isExpLieAlgebra E n).expG Y) = (isExpLieAlgebra F n).expG (thetaL D n i Y) := by
  apply Subtype.ext
  apply Units.ext
  rw [compA_val, IsExpLieAlgebra.coe_expG, IsExpLieAlgebra.coe_expG]
  exact thetaR_exp D n i _

private theorem tens_smooth (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n) (hβ : IsTens D φ β)
    (hφ : ∀ i, SmoothT (φ i)) : SmoothT β := by
  refine (IsExpLieAlgebra.isSmoothFun_iff (isExpLieAlgebra E n)).2 fun g => ?_
  have e : (fun Y : archLie E n => β (g * (isExpLieAlgebra E n).expG Y)) = fun Y => ∏ i,
      (fun Z : archLie F n => φ i (compA D n i g * (isExpLieAlgebra F n).expG Z)) (thetaL D n i Y) := by
    funext Y
    rw [hβ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_mul, compA_expG]
  rw [e]
  refine contDiff_prod fun i _ => ?_
  exact ((IsExpLieAlgebra.isSmoothFun_iff (isExpLieAlgebra F n)).1 (hφ i) _).comp (thetaL D n i).contDiff

private theorem tens_fin [_root_.NumberField.IsTotallyComplex F] (D : InfD σ m) (n : ℕ) (φ : Fin (m + 1) → TI F n) (β : TI E n)
    (hβ : IsTens D φ β) (hφ : ∀ i, LeftFin (φ i)) : LeftFin β := by
  haveI := fin_prod (ι := Fin (m + 1)) (X := archGroup E n) (Y := fun _ => archGroup F n) (fun i => compA D n i)
    (fun i => Set.range fun k : archCompact F n => fun g : archGroup F n => φ i ((k : archGroup F n) * g)) hφ
  have hsub : (Set.range fun k : archCompact E n => fun g : archGroup E n => β ((k : archGroup E n) * g)) ⊆
      {f | ∃ s : Fin (m + 1) → archGroup F n → ℂ, (∀ i, s i ∈ Set.range fun k : archCompact F n =>
        fun g : archGroup F n => φ i ((k : archGroup F n) * g)) ∧ f = fun x => ∏ i, s i (compA D n i x)} := by
    rintro f ⟨k, rfl⟩
    have hk := ((positionOf F E σ m D).2 n (k : archGroup E n)).1 k.2
    refine ⟨fun i g => φ i (compA D n i k * g), fun i => ⟨⟨_, hk i⟩, rfl⟩, ?_⟩
    funext x
    show β ((k : archGroup E n) * x) = _
    rw [hβ]
    exact Finset.prod_congr rfl fun i _ => by rw [map_mul]
  exact Submodule.finiteDimensional_of_le (Submodule.span_mono hsub)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.tensSmooth :
    UpperTheory.ConvolutionTheory.L1.TensSmooth := by
  intro F E _ _ _ _ _ _ σ m D n φ β hβ
  exact ⟨UpperTheory.ConvolutionTheory.L1.tens_smooth D n φ β hβ, UpperTheory.ConvolutionTheory.L1.tens_fin D n φ β hβ⟩
end
end

