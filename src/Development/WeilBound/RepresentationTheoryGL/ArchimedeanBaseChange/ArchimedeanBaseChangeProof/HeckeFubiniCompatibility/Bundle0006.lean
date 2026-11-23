module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PActEq
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace ActEq

open prime_not_mem_section_base_place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

theorem gInf_infP_inv_mul (y : InfinitePlace E → G n) (w : InfinitePlace E) (z : GA E n) :
    gInf w ((infP n y)⁻¹ * z) = (y w)⁻¹ * gInf w z := by
  rw [map_mul, map_inv, gInf_infP]

theorem gFin_infP_inv_mul (y : InfinitePlace E → G n) (z : GA E n) : gFin ((infP n y)⁻¹ * z) = gFin z := by
  rw [map_mul, map_inv, gFin_infP, inv_one, one_mul]

theorem entA_place [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (v : InfinitePlace E)
    (u : Matrix.unitaryGroup (Fin n) ℂ) (I J : IxA M) (z : GA E n) :
    entA k I J ((infP n (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * z) =
      ∑ l, ent (M v) ((M v).ρ u⁻¹) (I v) l * entA k (Function.update I v l) J z := by
  simp only [entA, gInf_infP_inv_mul]
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v]
  have hv : ent (M v) (k v (((Pi.mulSingle v (Unitary.toUnits u) : InfinitePlace E → G n) v)⁻¹ * gInf v z).val) (I v) (J v) =
      ∑ l, ent (M v) ((M v).ρ u⁻¹) (I v) l * ent (M v) (k v (gInf v z).val) l (J v) := by
    rw [Pi.mulSingle_eq_same]
    have h2 := mult_equivariant_val (hk v) (gInf v z) u⁻¹ 1
    simp only [OneMemClass.coe_one, map_one, mul_one] at h2
    have e : ((Unitary.toUnits u)⁻¹ * gInf v z).val = (u⁻¹ : Matrix.unitaryGroup (Fin n) ℂ).1 * (gInf v z).val := by
      rw [Units.val_mul]
      rfl
    rw [e, h2, PMul.ent_mul]
  have hw : ∀ w : {w // w ≠ v}, ent (M w) (k w (((Pi.mulSingle v (Unitary.toUnits u) : InfinitePlace E → G n) w)⁻¹ * gInf w z).val) (I w) (J w) =
      ent (M w) (k w (gInf w z).val) (I w) (J w) := by
    intro w
    rw [Pi.mulSingle_eq_of_ne w.2, inv_one, one_mul]
  rw [hv, Finset.prod_congr rfl fun w _ => hw w, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ v, Function.update_self]
  have hw' : ∀ w : {w // w ≠ v}, ent (M w) (k w (gInf w z).val) (Function.update I v l w) (J w) =
      ent (M w) (k w (gInf w z).val) (I w) (J w) := fun w => by
    rw [Function.update_of_ne w.2]
  rw [Finset.prod_congr rfl fun w _ => hw' w]
  ring

end ActEq

open prime_not_mem_section_base_place ActEq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem equiv_a (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ] {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hR : Repr D ka kb ψ f) (v : InfinitePlace E) (u : Matrix.unitaryGroup (Fin a) ℂ) (I : Io Ma Mb κ)
    (x : H E a b) :
    f I (x * (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1)) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x := by
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hRx : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  set p : H E a b := (infP a (Pi.mulSingle v (Unitary.toUnits u)), 1) with hp
  have hΦ : ∀ j y, tens ka kb ψ I j (p⁻¹ * y) =
      ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y := by
    intro j y
    have hF : hFin (p⁻¹ * y) = hFin y :=
      Prod.ext (gFin_infP_inv_mul _ y.1) (by show gFin (1⁻¹ * y.2) = gFin y.2; rw [inv_one, one_mul])
    show entA ka I.1.1 j.1.1 ((infP a (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * y.1) *
        entA kb I.1.2 j.1.2 (1⁻¹ * y.2) * ψ I.2 j.2 (hFin (p⁻¹ * y)) = _
    rw [hF, inv_one, one_mul, entA_place hka, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [tens]
    ring
  apply mul_left_cancel₀ hc
  rw [f_mul D _ f hconv I x p]
  calc ∑ j, ∫ y, tens ka kb ψ I j (p⁻¹ * y) * f j (x * y) ∂D.μ
      = ∑ j, ∫ y, ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l *
          (tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y * f j (x * y)) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hΦ, Finset.sum_mul, mul_assoc]
    _ = ∑ j, ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l *
          ∫ y, tens ka kb ψ ((Function.update I.1.1 v l, I.1.2), I.2) j y * f j (x * y) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint _ j x).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ = ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * (c * f ((Function.update I.1.1 v l, I.1.2), I.2) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hRx, Finset.mul_sum]
    _ = c * ∑ l, ent (Ma v) ((Ma v).ρ u⁻¹) (I.1.1 v) l * f ((Function.update I.1.1 v l, I.1.2), I.2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

theorem equiv_b (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ] {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    {f : Io Ma Mb κ → H E a b → ℂ} (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hψ : IsFinM ψ)
    (hR : Repr D ka kb ψ f) (v : InfinitePlace E) (u : Matrix.unitaryGroup (Fin b) ℂ) (I : Io Ma Mb κ)
    (x : H E a b) :
    f I (x * (1, infP b (Pi.mulSingle v (Unitary.toUnits u)))) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x := by
  obtain ⟨hfc, c, hc, hconv⟩ := hR
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hRx : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  set p : H E a b := (1, infP b (Pi.mulSingle v (Unitary.toUnits u))) with hp
  have hΦ : ∀ j y, tens ka kb ψ I j (p⁻¹ * y) =
      ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y := by
    intro j y
    have hF : hFin (p⁻¹ * y) = hFin y :=
      Prod.ext (by show gFin (1⁻¹ * y.1) = gFin y.1; rw [inv_one, one_mul]) (gFin_infP_inv_mul _ y.2)
    show entA ka I.1.1 j.1.1 (1⁻¹ * y.1) *
        entA kb I.1.2 j.1.2 ((infP b (Pi.mulSingle v (Unitary.toUnits u)))⁻¹ * y.2) * ψ I.2 j.2 (hFin (p⁻¹ * y)) = _
    rw [hF, inv_one, one_mul, entA_place hkb, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [tens]
    ring
  apply mul_left_cancel₀ hc
  rw [f_mul D _ f hconv I x p]
  calc ∑ j, ∫ y, tens ka kb ψ I j (p⁻¹ * y) * f j (x * y) ∂D.μ
      = ∑ j, ∫ y, ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l *
          (tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y * f j (x * y)) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [hΦ, Finset.sum_mul, mul_assoc]
    _ = ∑ j, ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l *
          ∫ y, tens ka kb ψ ((I.1.1, Function.update I.1.2 v l), I.2) j y * f j (x * y) ∂D.μ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint _ j x).const_mul _]
        exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
    _ = ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * (c * f ((I.1.1, Function.update I.1.2 v l), I.2) x) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hRx, Finset.mul_sum]
    _ = c * ∑ l, ent (Mb v) ((Mb v).ρ u⁻¹) (I.1.2 v) l * f ((I.1.1, Function.update I.1.2 v l), I.2) x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        ring

end PositivityTheory.Rg.BcB.CG

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PRepro
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

namespace PositivityTheory.Rg.BcB.CG

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def pInfH (N : ℕ) : GA E N →* (InfinitePlace E → G N) := MonoidHom.pi fun v => gInf v

def infPH (N : ℕ) : (InfinitePlace E → G N) →* GA E N where
  toFun := infP N
  map_one' := by simp [infP]
  map_mul' := infinitePart_mul N

theorem continuous_pInfH (N : ℕ) : Continuous (pInfH (E := E) N) :=
  continuous_pi fun v => continuous_gInf N v

theorem continuous_smooth_infP (N : ℕ) (φ : Sm E N) (x : GA E N) :
    Continuous fun t : InfinitePlace E → G N => φ.1 (x * infP N t) := by
  set M : (InfinitePlace E → G N) → GL (Fin N) (Cinf E) := fun t =>
    Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
      (MulEquiv.piUnits.symm t) with hMdef
  have hM : Continuous M := by
    refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
      Matrix (Fin N) (Fin N) ℂ)).symm.continuous
    exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  have e : (fun t : InfinitePlace E → G N => φ.1 (x * infP N t)) = fun t => chart φ.1 x (toL (M t).val) := by
    funext t
    rw [chart_val]
    rfl
  rw [e]
  have hc : Continuous fun t => ((M t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) :=
    Units.continuous_val.comp hM
  have hc' : Continuous fun t => toL (M t).val := hc
  exact (φ.2 x).continuousOn.comp_continuous hc' fun t => val_mem_invSet (M t)

theorem hasCompactSupport_prod {ι X : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] (a : ι → X → ℂ)
    (ha : ∀ i, HasCompactSupport (a i)) : HasCompactSupport fun t : ι → X => ∏ i, a i (t i) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun i => ha i) fun t ht => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at ht
  obtain ⟨i, hi⟩ := ht
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

theorem reproEx (hK : KerEx) (hM : MultAlg) (hB : Bridge.BridgeSt) : ReproEx := by
  intro E _ _ _ N _ _ ν _ K W R hKo hW
  let _ : MeasurableSpace (G N) := borel _
  have : BorelSpace (G N) := ⟨rfl⟩
  set μ0 : Measure (G N) := Measure.haar
  choose a ha hac hrep using fun v : InfinitePlace E => ReproL.local_repro hK hM hB W hW R v μ0
  obtain ⟨K0, hK0K, hK0o, hK0c⟩ := ReproA.exists_compact_open_le E N K hKo
  set U0 : Subgroup (GA E N) := K0.comap gFin with hU0def
  have hU0o : IsOpen (U0 : Set (GA E N)) := hK0o.preimage (continuous_gFin N)
  have hσ : ∀ t, pInfH N (infPH (E := E) N t) = t := fun t => funext fun v => gInf_infP N t v
  have hσU : ∀ t, infPH (E := E) N t ∈ U0 := fun t => by
    change gFin (infP N t) ∈ K0
    rw [gFin_infP]; exact K0.one_mem
  have hsplit : ∀ y : GA E N, y = splitGA N (pInfH N y, gFin y) := fun y => (infinitePart_mul_finGL N y).symm
  have hprop : ∀ C : Set (InfinitePlace E → G N), IsCompact C → ∃ D : Set (GA E N), IsCompact D ∧
      (U0 : Set (GA E N)) ∩ pInfH N ⁻¹' C ⊆ D := fun C hC =>
    ⟨splitGA N '' (C ×ˢ (K0 : Set _)), (hC.prod hK0c).image (splitGA N).continuous, fun y hy =>
      ⟨(pInfH N y, gFin y), ⟨hy.2, hy.1⟩, (hsplit y).symm⟩⟩
  haveI := ReproA.pi_isHaar (ι := InfinitePlace E) μ0
  obtain ⟨c, hc, hcF⟩ := ReproA.haar_restrict_eq ν (Measure.pi fun _ : InfinitePlace E => μ0) (pInfH N)
    (continuous_pInfH N) (infPH N) hσ U0 hU0o hσU hprop
  set A : (InfinitePlace E → G N) → ℂ := fun t => ∏ v, a v (t v) with hAdef
  have hAc : Continuous A := continuous_finsetProd _ fun v _ => (ha v).comp (continuous_apply v)
  have hAs : HasCompactSupport A := hasCompactSupport_prod a hac
  refine ⟨(U0 : Set (GA E N)).indicator (fun y => A (pInfH N y)), c * (1 / 2) ^ Fintype.card (InfinitePlace E),
    ?_, ?_, by positivity, ?_⟩
  · have hcl : IsClopen (U0 : Set (GA E N)) := ⟨U0.isClosed_of_isOpen hU0o, hU0o⟩
    refine continuous_indicator (by rw [hcl.frontier_eq]; simp) (hAc.comp (continuous_pInfH N)).continuousOn
  · set C : Set (InfinitePlace E → G N) := Set.pi Set.univ fun v => tsupport (a v) with hCdef
    have hCc : IsCompact C := isCompact_univ_pi fun v => hac v
    have hCcl : IsClosed C := isClosed_set_pi fun v _ => isClosed_tsupport (a v)
    refine HasCompactSupport.intro' ((hCc.prod hK0c).image (splitGA N).continuous)
      ((splitGA N).toHomeomorph.isClosedMap _ (hCcl.prod (K0.isClosed_of_isOpen hK0o))) fun y hy => ?_
    by_cases hyU : y ∈ (U0 : Set (GA E N))
    · rw [Set.indicator_of_mem hyU]
      by_contra hne
      refine hy ⟨(pInfH N y, gFin y), ⟨fun v _ => subset_tsupport _ fun h0 => hne ?_, hyU⟩, (hsplit y).symm⟩
      exact Finset.prod_eq_zero (Finset.mem_univ v) h0
    · exact Set.indicator_of_notMem hyU _
  · intro φ _ hT hR
    choose s hs1 hs2 using fun v => hrep v φ hT.2 hR
    refine ⟨c * ∏ v, s v, ?_, fun x => ?_⟩
    · rw [norm_mul, Complex.norm_of_nonneg hc.le, norm_prod]
      gcongr
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) fun v _ => hs1 v
    · set f : (InfinitePlace E → G N) → ℂ := fun t => φ.1 (x * infP N t) with hfdef
      have hfc : Continuous f := continuous_smooth_infP N φ x
      have e1 : (fun y => (U0 : Set (GA E N)).indicator (fun y => A (pInfH N y)) y * φ.1 (x * y)) =
          (U0 : Set (GA E N)).indicator (fun y => (A * f) (pInfH N y)) := by
        funext y
        by_cases hyU : y ∈ (U0 : Set (GA E N))
        · rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyU, Pi.mul_apply]
          congr 1
          have hk : gFin y ∈ K := hK0K hyU
          conv_lhs => rw [hsplit y, splitGA_apply, ← mul_assoc, hT.1 _ hk]
        · rw [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hyU, zero_mul]
      rw [e1, hcF (A * f) (hAc.mul hfc) hAs.mul_right]
      have h := ReproA.integral_pi_repro μ0 a ha hac f hfc s fun v y => by
        have e2 : (fun t => a v t * f (y * Pi.mulSingle v t)) =
            fun t => a v t * φ.1 ((x * infP N y) * infP N (Pi.mulSingle v t)) := by
          funext t
          simp only [hfdef, infinitePart_mul, mul_assoc]
        rw [e2, hs2 v (x * infP N y)]
      have e3 : f 1 = φ.1 x := by
        simp only [hfdef]
        rw [show infP (E := E) N 1 = 1 from (infPH (E := E) N).map_one, mul_one]
      simp only [Pi.mul_apply]
      rw [h, e3, mul_assoc]

end PositivityTheory.Rg.BcB.CG
end
end

