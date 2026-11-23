module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Bundle0019
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0023
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0026
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVRPropMV
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
namespace UpperTheory.Esk.PropMVAux
variable {l : ℕ} [Fact l.Prime]
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
end UpperTheory.Esk.PropMVAux
open UpperTheory.Esk.PropMVAux in
open Classical in
theorem UpperTheory.Esk.pf_PropMV_sv_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Sd.PropMHol → UpperTheory.Esk.HolWC → UpperTheory.Esk.HRep → UpperTheory.Esk.PropMV := by
  intro hPH hMH hWC hHR F Ω _ _ _ _ _ _ l _ hl2 hd hsplit ι ξ ho hodd hunr hram P hP1 hP2
  have : IsGalois F Ω := {}
  obtain ⟨art, ha⟩ := hPH.litN.aut.art F Ω
  have hc := continuous_of_isOpen_ker' ξ ho
  have : Finite (G F Ω ⧸ ξ.ker) := ξ.ker.quotient_finite_of_isOpen ho
  have hm : 0 < ξ.ker.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hξm : ξ ^ ξ.ker.index = 1 := MonoidHom.ext fun g => by
    rw [MonoidHom.pow_apply, ← map_pow]
    exact ξ.ker.pow_index_mem g
  have hn : ∀ s, ‖(ξ s : Qbar l)‖ = 1 := fun s => by
    have h2 : ξ s ^ ξ.ker.index = 1 := DFunLike.congr_fun hξm s
    have h3 : ‖(ξ s : Qbar l)‖ ^ ξ.ker.index = 1 := by rw [← norm_pow, ← Units.val_pow_eq_pow_val, h2]; simp
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 h3
  obtain ⟨ω, ⟨hω, hL⟩, -⟩ := exists_unique_hchar_of_finite_order ha ι ξ hc hm hξm
  have hfo : IsOfFinOrder ω := isOfFinOrder_iff_pow_eq_one.2 ⟨_, hm, hω⟩
  obtain ⟨c, hcond, hc0, hfin⟩ := cond_ex ω hm hω
  have hine : ∀ (w : Pl F) (A : ValuationSubring Ω), IsPlaceOver A w → (Ine (F := F) A ≤ ξ.ker ↔ c w = 0) := fun w A hA =>
    (hL.unr_iff ha (Or.inr rfl) hA).trans (hc0 w).symm
  have hcl : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → c w = 0 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact (hine w A hA).1 (hunr A (by simpa using (hA _).2 hw))
  have hfr : ∀ (w : Pl F), c w = 0 → ∀ A, IsPlaceOver A w → ∀ σ : G F Ω, IsFrob A (normV w) σ →
      ι.symm (ω.val w : ℂˣ) = (ξ σ⁻¹ : (Qbar l)ˣ) := fun w hw A hA σ hσ => by
    rw [map_inv, Units.val_inv_eq_inv_val, hL.frob_unr ha (Or.inr rfl) ((hc0 w).1 hw) hA hσ, inv_inv]
  have hsg : ∀ v, ω.locInf v (-1) = -1 := fun v => by
    obtain ⟨j, σ, hσ, rfl⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) v (IsTotallyReal.isReal v)
    have e := hL _ σ (GlobalTheory.HilbertFromArtin.art_sign_eq ha j σ hσ)
    rw [infPow_zero, lPow_zero, inv_one, mul_one, mul_one, hodd σ ⟨j, hσ⟩] at e
    refine Units.ext (ι.symm.injective (e.symm.trans ?_))
    simp
  have hex : ∃ w, c w ≠ 0 := by
    obtain ⟨u, A, -, hA, hnA⟩ := hram
    exact ⟨u, fun h => hnA ((hine u A hA).2 h)⟩
  have hnc : ∀ w : Pl F, (((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ∃ A, IsPlaceOver A w ∧ ∃ σ ∈ Dec (F := F) A, ¬ Cong (ξ σ) 1) →
      ((l : ℕ) : 𝓞 F) ∈ w.asIdeal ∧ ¬ ‖ι.symm (ω.val w : ℂˣ) - 1‖ < 1 := by
    rintro w ⟨hw, A, hA, σ, hσ, h⟩
    exact ⟨hw, fun h' => h (dec_cong ha hc hL ((hc0 w).1 (hcl w hw)) h' hA hσ)⟩
  obtain ⟨k, hkB, hk, φ, lam, hφ, hcu, hlam⟩ := hMH F l hl2 ι ω c hfo hsg hcond hex hcl P
    (hP1.imp fun w h => ⟨h.1, hnc w h.2⟩) (hP2.imp fun w h => ⟨h.1, hnc w h.2⟩) 3
  have hlev : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → levL l c w = c w := fun w hw => if_neg hw
  have hlev1 : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → levL l c w = 1 := fun w hw => if_pos hw
  have hfinL : {w | levL l c w ≠ 0}.Finite := by
    refine (hfin.union (fin_l (l := l))).subset fun w hw => ?_
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
    exact hw ((hlev w h.2).trans h.1)
  have heu : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ‖ι.symm (eisT l ω c P w)‖ = 1 := fun w hw => by
    obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    obtain ⟨σ, hσ⟩ := exists_isFrob hA
    rw [eisT, if_pos hw]
    split_ifs
    · rw [hfr w (hcl w hw) A hA σ hσ, hn]
    · simp
  obtain ⟨D⟩ := Wc.exL F l ι hsplit
  have hu2 : ∃ u, levL l c u ≠ 0 ∧ normV u = 2 := by
    obtain ⟨u, A, h2, hA, hnA⟩ := hram
    refine ⟨u, ?_, h2⟩
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ u.asIdeal
    · rw [hlev1 u hl]; exact one_ne_zero
    · rw [hlev u hl]; exact fun h => hnA ((hine u A hA).2 h)
  have hunit : ∀ v, Wc.nu ι (lam (D.pl v)) = 1 := fun v => by
    rw [nu_eq]
    refine norm_eq_one (heu _ (D.mem v)) ?_
    rw [← map_sub]
    exact hlam _
  obtain ⟨t, htB, ht, φ', lam', hV, hne, hcusp, heig, hcong⟩ :=
    hWC F hd l hl2 ι D (k + 1) (by omega) (levL l c) hfinL (fun v => hlev1 _ (D.mem v)) hu2 ω hfo φ lam hφ hcu hunit
      {v | D.pl v ∈ P} 2
  have hlam' : ∀ w, ‖ι.symm ((∏ v, if D.pl v = w ∧ v ∈ {v | D.pl v ∈ P} then (l : ℂ) ^ t else 1) * lam' w -
      eisT l ω c P w)‖ < 1 := fun w => by
    rw [← sub_add_sub_cancel _ (lam w), map_add (f := _)]
    exact add_lt (nu_lt.1 (hcong w)) (hlam w)
  have haway : ∀ w : Pl F, ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ‖ι.symm (lam' w - eisT l ω c P w)‖ < 1 := fun w hw => by
    have h := hlam' w
    rwa [prod_away D _ t w hw, one_mul] at h
  obtain ⟨π, hreg, ⟨χ, hpol⟩, hinf, hU, hsat⟩ := hHR F (k + 1) (by omega) (fun v => if v ∈ {v | D.pl v ∈ P} then t else 0)
    (levL l c) ω hfo φ' lam' hV hne heig hcusp
  obtain ⟨r, wt, HT, hG, hatt, -⟩ := _root_.UpperTheory.Gal.SV.exRS_alt hPH.toClassicalTheorems F Ω l ι 2 one_le_two π χ hreg hpol
  obtain ⟨hdet, hres⟩ := det_res ξ hc r hG.cont k hk hn
    (((Filter.eventually_cofinite.1 hatt.2).union hfin).union (fin_l (l := l))) fun w hw A hA σ hσ => by
      simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
      obtain ⟨⟨⟨B₁, hB₁, hF⟩, h0⟩, hl⟩ := hw
      obtain ⟨B₂, hB₂, e⟩ := hsat w ((hlev w hl).trans h0)
      obtain rfl := hB₁.unique hB₂
      obtain ⟨h2, h3⟩ := tr_det ι _ _ _ (((hF A hA).2 σ hσ).trans e)
      have h4 := haway w hl
      rw [eisT, if_neg hl, if_pos h0, map_sub, map_add (f := _), map_one, hfr w h0 A hA σ hσ] at h4
      rw [h2, h3, map_mul, hfr w h0 A hA σ hσ, map_pow, map_natCast, cyc_frob hl hA hσ]
      exact ⟨h4, rfl⟩
  refine ⟨k, t, by omega, htB, hk, ht, levL l c, fun w => ι.symm (eisT l ω c P w), π, r,
    ⟨hreg, ⟨χ, hpol⟩, hG.cont, hatt, hdet, ho, hfinL, fun w A hA => ?_, fun w hw => ?_, fun w hw hl => ?_, fun w hw => ?_⟩,
    hres, fun w hw A hA σ hσ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hine w A hA]
    by_cases hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · simp [hl, hcl w hl]
    · simp [hl, hlev w hl]
  · obtain ⟨v, h1, h2, -⟩ := hU w
    rw [hw] at h2
    exact ⟨v, h1, h2⟩
  · refine ⟨lam' w, hU w, norm_one_of ?_⟩
    have h4 := haway w hl
    rwa [eisT, if_neg hl, if_neg (hlev w hl ▸ hw), map_sub, map_one] at h4
  · obtain ⟨v₀, hv₀⟩ := D.surj w hw
    have hnorm : normV w = l := hv₀ ▸ D.norm v₀
    have hc' := hlam' w
    rw [prod_at D _ t w v₀ hv₀] at hc'
    refine ⟨hlev1 w hw, ?_, ?_, heu w hw, ⟨lam' w, hlev1 w hw ▸ hU w, ?_⟩, fun τ hτ => ?_⟩
    · by_cases h : w ∈ P <;> simp [h] <;> omega
    · by_cases h : w ∈ P <;> simp [h] <;> ring
    · rw [hnorm]
      by_cases h : w ∈ P
      · have hv : v₀ ∈ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_pos hv, map_sub, map_mul, map_pow, map_natCast, mul_comm] at hc'
        rw [if_pos h]
        simpa using hc'
      · have hv : v₀ ∉ {v | D.pl v ∈ P} := by simpa [hv₀] using h
        rw [if_neg hv, one_mul, map_sub] at hc'
        rw [if_neg h]
        simpa using hc'
    · obtain ⟨v, hvd⟩ : ∃ v, InfinitePlace.mk (ι.toRingHom.comp τ) = v := ⟨_, rfl⟩
      have hv : D.pl v = w := hvd ▸ (D.embAt τ w).1 hτ
      rw [hvd]
      convert hinf v using 3
      by_cases h : w ∈ P
      · have hS : v ∈ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
      · have hS : v ∉ {v | D.pl v ∈ P} := by simpa [hv] using h
        ext i; fin_cases i <;> simp [h, hS] <;> omega
  · simp only [eisT, if_pos hw, if_pos h]
    exact hfr w (hcl w hw) A hA σ hσ
  · simp only [eisT, if_pos hw, if_neg h, map_one]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAboveW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc Lp)
open scoped Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.GalN.V UpperTheory.V.Z.Win UpperTheory.Zero.LLC
open UpperTheory.V.Z.Sym.AboveWeight
section
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}
private theorem noLk_of {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (u : kˣ →* ℂˣ) (H : ∀ i j : Fin 3, i ≠ j → (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j ∧
      (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) i ≠ (![u, 1, u⁻¹] : Fin 3 → kˣ →* ℂˣ) j * absPow k 1) :
    UpperTheory.V.Z.Sym.W.NoLk u := by
  intro j hj e he hE
  have e1 : absPow k (((1 : ℤ) : ℂ)) = absPow k 1 := by simp
  have e2 : absPow k (((-1 : ℤ) : ℂ)) = (absPow k 1)⁻¹ := by
    rw [show (((-1 : ℤ) : ℂ)) = -1 by simp, absPow_neg]
  rcases hj with rfl | rfl <;> rcases he with rfl | rfl
  · rw [pow_one, e1] at hE
    exact (H 0 1 (by decide)).2 (by simpa using hE)
  · rw [pow_one, e2] at hE
    exact (H 1 0 (by decide)).2 (by simp [hE])
  · rw [e1] at hE
    refine (H 0 2 (by decide)).2 ?_
    simp [← hE, pow_two]
  · rw [e2] at hE
    refine (H 2 0 (by decide)).2 ?_
    have hp : absPow k 1 = (u ^ 2)⁻¹ := by rw [hE, inv_inv]
    simp [hp, pow_two]
private theorem noLk_above (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (ha : IsLocalArtin h a) (hv : A.valuation (l : Ω) < 1) {m : ℕ} (hm : 2 ≤ m) {b : ℤ} {k : ℕ} (hk : 0 < k)
    {ω₀ ω₁ : (w.adicCompletion L)ˣ →* ℂˣ} {κ₀ κ₁ : Dec (F := L) A →* (Qbar l)ˣ}
    (h₀ : OrdChar ι a ω₀ (fun _ => -(b + m)) κ₀) (h₁ : OrdChar ι a ω₁ (fun _ => -b) κ₁)
    (hκ : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
      κ₀ s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ₁ s ^ k = (cycBar L Ω l s ^ b) ^ k) :
    UpperTheory.V.Z.Sym.W.NoLk (ω₀ / ω₁) := by
  let u := ω₀ / ω₁
  let c : Fin 3 → ℤ := ![m, 0, -m]
  let ψ : Fin 3 → Dec (F := L) A →* (Qbar l)ˣ := ![κ₀ / κ₁, 1, κ₁ / κ₀]
  let hh : Fin 3 → (L →+* Qbar l) → ℤ := fun i _ => (![-(m : ℤ), 0, (m : ℤ)] : Fin 3 → ℤ) i
  have hq : ∀ {p q y : (Qbar l)ˣ} {e f : ℤ}, p ^ k = (y ^ e) ^ k → q ^ k = (y ^ f) ^ k →
      (p / q) ^ k = (y ^ (e - f)) ^ k := fun h1 h2 => by
    rw [div_pow, h1, h2, ← div_pow, zpow_sub, div_eq_mul_inv]
  have hp : ∀ (i : Fin 3) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A →
      ψ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := fun i s hs => by
    obtain ⟨h1, h2⟩ := hκ s hs
    fin_cases i
    · have := hq h1 h2
      simpa [ψ, c] using this
    · simp [ψ, c]
    · have := hq h2 h1
      simpa [ψ, c] using this
  have hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := fun i j => by
    refine not_link hv hk (hp i) (hp j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  have H0 : OrdChar ι a u (fun _ => -(m : ℤ)) (κ₀ / κ₁) := by
    have := ord_div h₀ h₁
    have e : ((fun _ => -(b + m)) - fun _ => -b : (L →+* Qbar l) → ℤ) = fun _ => -(m : ℤ) := by
      funext t
      simp
    rwa [e] at this
  have H1 : OrdChar ι a (1 : (w.adicCompletion L)ˣ →* ℂˣ) (fun _ => 0) (1 : Dec (F := L) A →* (Qbar l)ˣ) := by
    have := ord_div h₀ h₀
    rw [div_self', div_self', sub_self] at this
    exact this
  have H2 : OrdChar ι a u⁻¹ (fun _ => (m : ℤ)) (κ₁ / κ₀) := by
    have := ord_div h₁ h₀
    have e : ((fun _ => -b) - fun _ => -(b + m) : (L →+* Qbar l) → ℤ) = fun _ => (m : ℤ) := by
      funext t
      simp
    rw [e] at this
    rwa [show u⁻¹ = ω₁ / ω₀ from inv_div _ _]
  have hO : ∀ i, OrdChar ι a ((![u, 1, u⁻¹] : Fin 3 → (w.adicCompletion L)ˣ →* ℂˣ) i) (hh i) (ψ i) := fun i => by
    fin_cases i
    · exact H0
    · exact H1
    · exact H2
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 3 => hh j t := fun t => by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> simp [hh] <;> omega
  exact noLk_of u (not_linked H ι hw ha hmono hO hne)
private theorem above' (P : _root_.UpperTheory.V.Af.Hypotheses') (hl : l ≠ 2) {n : ℕ} {ι : Qbar l ≃+* ℂ} {ρ : G L Ω →* GL (Fin n) (Qbar l)}
    {HT : (L →+* Qbar l) → Multiset ℤ} (hρ : Continuous ρ) (HG : HasHTAt ρ HT w) (h : IsPlaceOver A w)
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {τ : SmIrr (GL (Fin n) (w.adicCompletion L))} (H : LocGlobT ι ρ w τ)
    {rc : IrrGL (k := w.adicCompletion L) → WD h} (hrc : IsRecT h rc)
    (hp : GlobalTheory.RoadU.PlainTor (IrrGL.of τ.ρ τ.smooth τ.irred)) (hg : Gd (rc (algNorm τ)))
    {hh : Fin n → (L →+* Qbar l) → ℤ} (hm : ∀ t, StrictMono fun j => hh j t) {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hψ : ∀ i, W.IsLocAlg h (ψ i) fun t => hh i (t.1.comp (algebraMap L _)))
    (hf : W.HasFlag (ρ.comp (Dec (F := L) A).subtype) ψ)
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) :
    ∃ (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a ∧
    (∃ ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι a (ω i) (hh i) (ψ i)) ∧
    ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = Finset.univ.val.map fun i => hh i (j.1.comp (algebraMap L _)) := by
  obtain ⟨a, ha⟩ : ∃ a, IsLocalArtin h a := by
    obtain ⟨a, ha, -⟩ := hrc
    exact ⟨a, ha⟩
  have hc : Continuous (ρ.comp (Dec (F := L) A).subtype) := hρ.comp continuous_subtype_val
  choose ω hω using fun i => (Loc.ordCharIff P.litN.aut.art h ι _ ha (hh i) (ψ i)).1.2 ⟨flag_cont' hc hf i, hψ i⟩
  have hD : DRat ι h (ρ.comp (Dec (F := L) A).subtype) HT fun s => (rc (algNorm τ)).charPol s := fun O _ _ _ Bw hj =>
    have h1 := HG A h O Bw hj
    ⟨h1.1, h1.2, fun s => by rw [((H A h rc hrc).2 O Bw hj hg).2]⟩
  have hD' := _root_.UpperTheory.V.Loc.flag_weil_deligne_of_literal_automorphy_n P.litN L Ω l hl ι n w hw A h _ ha _ hc _ ω ψ hω hf _ _ hD
  refine ⟨a, ha, ⟨ω, ?_, hω⟩, jumps_eq h hw hD hD'⟩
  have hs : IsSubquotient τ.ρ (PS ω) := by
    obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
    exact _root_.UpperTheory.V.Z.Desc.W.pseudo_local_langlands_descent P.litN L Ω n w A h _ ha rc hrc τ hp ω (fun i => (hω i).smooth) fun s =>
      ((hD O Bw hj).2.2 s).symm.trans ((hD' O Bw hj).2.2 s)
  exact (_root_.UpperTheory.V.Hi.prin_series_irreducible_and_unique_subquotient P.litN _ n ω (fun i => (hω i).smooth)
    (not_linked P.litN.aut.art ι hw ha (fun t i j hij => hm t hij) hω hne)).2 _ τ.ρ τ.irred hs
end
end
theorem UpperTheory.V.Z.Sym.W.above_w_statement : _root_.UpperTheory.V.Z.Sym.W.AboveWAlt := by
  intro P L Ω _ _ _ _ _ l _ ι hl r hr m hm w hw HT hHT A h ⟨b, k, κ, hk, hf, hκ⟩ τ H hPT
  have hv : A.valuation (l : Ω) < 1 := by
    have := (h ((l : ℕ) : 𝓞 L)).2 hw
    simpa only [map_natCast] using this
  let c : Fin 2 → ℤ := ![b + m, b]
  have hκ' : ∀ (i : Fin 2) (s : ↥(Dec (F := L) A)), (s : G L Ω) ∈ Ine (F := L) A → κ i s ^ k = (cycBar L Ω l s ^ c i) ^ k := by
    intro i s hs
    fin_cases i
    · exact (hκ s hs).1
    · exact (hκ s hs).2
  have hcont : Continuous (r.comp (Dec (F := L) A).subtype) := hr.comp continuous_subtype_val
  have hfc : ∀ i, Continuous (κ i) := flag_cont' hcont hf
  have hmono : ∀ t : L →+* Qbar l, StrictMono fun j : Fin 2 => (fun (i : Fin 2) (_ : L →+* Qbar l) => -c i) j t := by
    intro t
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i
    simp [c]
    omega
  have hne : ∀ i j, κ i ≠ κ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
    intro i j
    refine not_link hv hk (hκ' i) (hκ' j) ?_
    fin_cases i <;> fin_cases j <;> simp [c] <;> omega
  obtain ⟨rc, hrc⟩ := _root_.UpperTheory.V.Z.Win.exRec'_alt P.litN h
  have hg : Gd (rc (algNorm τ)) := UpperTheory.V.Z.Win.Gu.plainGd L Ω A w h rc hrc 2 τ hPT
  obtain ⟨a, ha, ⟨ω, he, hO⟩, hj⟩ := above' P hl hr hHT h hw H hrc hPT hg hmono
    (fun i => locAlg P.litN.aut.art h hw (κ i) (hfc i) hk (c i) (hκ' i)) hf hne
  refine ⟨⟨_, fun i => (hO i).smooth.mul (isSmoothChar_of_isUnram (isUnram_absPow _ _)), he, ?_⟩, -(b + m), fun j => ?_⟩
  · have := noLk_above P.litN.aut.art ι hw ha hv hm hk (hO 0) (hO 1) hκ
    simpa [mul_div_mul_right_eq_div] using this
  · rw [hj j]
    simp [c]
    rfl
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPlainOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Z.Sym.W.plain_of_statement :
    _root_.UpperTheory.V.Z.Sym.W.PlainOfAlt := by
  intro _ L _ _ n w τ ψ hψ hs hl
  refine ⟨GlobalTheory.RoadU.chars ψ hψ, ?_, ?_, ?_⟩
  · exact (GlobalTheory.IwahoriSupport.hasSupport_chars τ.irred ψ hψ hs).of_equiv (IrrGL.equivOf τ.ρ τ.smooth τ.irred)
  · intro y hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · intro y hy z hz h
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at h
    exact hl i j h
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open UpperTheory.V.HV (Coef)
section Alg
variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (n : ℕ) {V : Type} [Fintype V] (S : V → Plc L)
variable {n S}
end Alg
namespace HSet
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)
variable (A : Type) [CommRing A] [Algebra c.O A]
variable {A} (θ : H.X.I.T →* Aˣ)
variable (ι : Qbar l ≃+* ℂ)
structure PartAltAlt (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) : Type 1 where
  Y : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)
  le : Y ≤ H.Big ι ξ
  ne : Y ≠ ⊥
  σl : ∀ v : H.V, SmIrr (GLw n (H.Sl v))
  isoL : ∀ v, IsoSum (H.atV d v) Y (σl v)
  σq : ∀ q : H.Q, SmIrr (GLw n (H.wq q))
  isoQ : ∀ q : H.Q, IsoSum (H.atW ι d (H.wq q)) Y (σq q)
  a : H.Wp → ℕ → ℂ
  a_zero : ∀ w, a w 0 = 1
  sph : ∀ (w : H.Wp) j, ∀ F ∈ Y, sphOp (H.atW ι d w.1) j F = a w j • F
  r : H.Gq →* GL (Fin n) (Qbar l)
  cont : Continuous r
  ss : IsSSRep r
  frob : ∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    (r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) (a w)
  atL : ∀ v, _root_.UpperTheory.V.Z.Ord.AtLT ι (H.ovr v) (r.comp (H.dec v)) lam (σl v)
  atQ : ∀ (q : H.Q) (B : ValuationSubring Ω) (h : IsPlaceOver B (H.wq q)) (rc : IrrGL (k := (H.wq q).adicCompletion L) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (r.comp H.prj) (rc (algNorm (σq q)))
def AutomorphicHeckeSet (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y
variable [IsLocalRing A] (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
end HSet
end UpperTheory.V.Hi
end
end
end

