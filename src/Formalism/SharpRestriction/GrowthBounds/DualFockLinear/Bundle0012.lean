module

public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.Bundle0011
public import Formalism.LocalToGlobal.GroupLattices.FockModels.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.RhoAtGOfPair
section
noncomputable section

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 MvPolynomial

section At

variable (p n' : ℕ) {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [Field Kf]
  [Algebra O Kf] (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ)
  (rest lam : Fin n' → Fin (m + 1) → ℤ)

def PairAt (c0 : ℕ) (bK : ℝ) (e : Edge W Qq (m + 1)) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d))) : Prop :=
  ∃ (κ0 κf : ℕ) (Ψ0 : Module.Dual Kf (Vsp Kf lam) ≃ₗ[Kf] Vsp Kf lam)
    (Ψf : Module.Dual Kf (Vsp Kf (flW (m := m) d)) ≃ₗ[Kf] Vsp Kf (flW (m := m) d)),
    ((κ0 + κf : ℕ) : ℝ) ≤ bK ∧
    (∀ T ∈ dualLat O Kf (HL (O := O) ι σ (flW d) e.tgt), Ψf T ∈ HL (O := O) ι σ (flW d) (latDual e.tgt)) ∧
    (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ T ∈ Re' p ι σ w r (flW d) e',
      Ψf T ∈ Re p ι σ w r (flW d) e'.dual) ∧
    (∀ y ∈ Re p ι σ w r (flW d) e.dual, Ψf.symm ((p : Kf) ^ κf • y) ∈ Re' p ι σ w r (flW d) e) ∧
    (∀ y ∈ HL (O := O) ι σ lam (latDual e.tgt), Ψ0.symm ((p : Kf) ^ κ0 • y) ∈ dualLat O Kf (HL (O := O) ι σ lam e.tgt)) ∧
    (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ y ∈ Re p ι σ w r lam e'.dual,
      Ψ0.symm ((p : Kf) ^ κ0 • y) ∈ Re' p ι σ w r lam e') ∧
    (∀ G ∈ Re' p ι σ w r lam e, Ψ0 G ∈ Re p ι σ w r lam e.dual) ∧
    (Re p ι σ w r lam e.dual ≤ Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e.dual,
      ∃ β ∈ Re p ι σ w r rest e.dual, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)}) ∧
    (∀ (β : Vsp Kf rest) (F : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O)) (s : Vsp Kf rest) (u : Vsp Kf lam),
      ((u : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Θ F : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * ((s : Vsp Kf rest) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
      ∃ F' : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O),
        (F' : MvPolynomial (Fin n' × Fin (m + 1)) (KK O)) ∈
          OpCl TT c0 (Submodule.span (KK O) {(F : MvPolynomial (Fin n' × Fin (m + 1)) (KK O))}) ∧
        ∀ (T : Module.Dual Kf (Vsp Kf (flW (m := m) d))) (z : Vsp Kf lam),
          (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = ((Ψf T : Vsp Kf (flW (m := m) d)) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) →
          (p : Kf) ^ Ar r rest * ((p : Kf) ^ κ0 * Ψ0.symm z u) = T (Θ F'))

end At

theorem HL_refl {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ}
    (X : Fin n' → Fin (m + 1) → ℤ) (hd : IsDominant X) (L : Submodule W (Fin (m + 1) → Qq)) (hL : IsLattice W L)
    (y : Vsp Kf X) (hy : ∀ T ∈ dualLat O Kf (HL (O := O) ι σ X L), T y ∈ Set.range (algebraMap O Kf)) :
    y ∈ HL (O := O) ι σ X L := by
  obtain ⟨x, hx⟩ := Formalism.L2.G.Model.hlSpans p n' W Qq O Kf ι σ j w h m X hd L hL
  have hc : ∀ i, x.coord i ∈ dualLat O Kf (HL (O := O) ι σ X L) := by
    intro i v hv
    rw [← hx] at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      by_cases hik : k = i
      · exact ⟨1, by simp [hik]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, hik]⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add (f := _), map_add (f := _), ha', hb']⟩
    | smul t a _ ha =>
      obtain ⟨a', ha'⟩ := ha
      exact ⟨t * a', by rw [LinearMap.map_smul_of_tower, ← ha', map_mul, Algebra.smul_def]⟩
  rw [← hx, ← x.sum_repr y]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨a, ha⟩ := hy _ (hc i)
  rw [Module.Basis.coord_apply] at ha
  rw [← ha, algebraMap_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)


set_option maxHeartbeats 1600000 in
theorem rhoAtG_of_pair (D : Formalism.BasicNotions.D7) {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} (h : HidaSetting p n' W Qq O Kf ι σ j w) {m : ℕ}
    (r : ℕ) (TT : Finset (Fin n')) (d : Fin n' → ℕ) (rest lam : Fin n' → Fin (m + 1) → ℤ) (hlam : lam = flW d + rest)
    (hdr : IsDominant rest) (c0 loss : ℕ) (hord : ordMax r rest ≤ loss) (bK : ℝ) (e : Edge W Qq (m + 1))
    (he : IsEdge p n' r e) (Θ : ↥((Pol (KK O) (ι := Fin n') (m + 1) d).restrictScalars O) ≃ₗ[O] ↥(Vsp Kf (flW (m := m) d)))
    (hP : PairAt p n' ι σ w r TT d rest lam c0 bK e Θ) :
    ∃ κ : ℕ, (κ : ℝ) ≤ bK ∧ RhoAtG p n' ι σ w r TT d rest lam c0 loss κ e Θ := by
  classical
  obtain ⟨κ0, κf, Ψ0, Ψf, hκ, a1, a2, a3, b1, b2, b3, hon, hop⟩ := hP
  have hw := w_ne_zero h
  have hp0 : (p : Kf) ≠ 0 := by rw [Formalism.L2.G.Model.p_eq h]; exact pow_ne_zero _ hw
  have hfd : IsDominant (flW (m := m) d) := flW_dom _
  have hdl : IsDominant lam := by rw [hlam]; exact isDominant_add hfd hdr
  have hAr : Ar r lam = Ar r (flW (m := m) d) + Ar r rest := by rw [hlam]; exact Ar_add r _ _
  have hM := Formalism.L2.G.Model.products_sections_integral D
  set cw : Kf := algebraMap O Kf w with hcw
  have bpl := fun e' (he' : IsEdge p n' r e') => Formalism.L2.G.Model.bePerfect p n' W Qq O Kf ι σ j w h m r lam hdl e' he'
  have bpf := fun e' (he' : IsEdge p n' r e') =>
    Formalism.L2.G.Model.bePerfect p n' W Qq O Kf ι σ j w h m r (flW (m := m) d) hfd e' he'
  obtain ⟨xb, -⟩ := Formalism.L2.G.Model.hlSpans p n' W Qq O Kf ι σ j w h m (flW (m := m) d) hfd e.tgt he.2.1
  have : Module.Finite Kf (Vsp Kf (flW (m := m) d)) := Module.Finite.of_basis xb
  let mulR : Vsp Kf rest → (Vsp Kf (flW (m := m) d) →ₗ[Kf] Vsp Kf lam) := fun β =>
    (LinearMap.mulRight Kf (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)).restrict (fun x hx => V_mul Kf hlam hfd hdr hx β.2)
  have hmulR : ∀ β y, ((mulR β y : Vsp Kf lam) : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) := fun β y => rfl
  let Λ : Vsp Kf rest → (Module.Dual Kf (Vsp Kf (flW (m := m) d)) →ₗ[Kf] Module.Dual Kf (Vsp Kf lam)) := fun β =>
    ((p : Kf) ^ κ0) • (Ψ0.symm.toLinearMap ∘ₗ mulR β ∘ₗ Ψf.toLinearMap)
  have hΛ : ∀ β T, Λ β T = Ψ0.symm ((p : Kf) ^ κ0 • mulR β (Ψf T)) := by
    intro β T
    simp only [Λ, LinearMap.smul_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_smul]
  have hΛs : ∀ (c : Kf) β T, Λ (c • β) T = c • Λ β T := by
    intro c β T
    have e : mulR (c • β) (Ψf T) = c • mulR β (Ψf T) := Subtype.ext (by
      rw [hmulR, Submodule.coe_smul, Submodule.coe_smul, hmulR, mul_smul_comm])
    rw [hΛ, hΛ, e, smul_comm ((p : Kf) ^ κ0) c, map_smul]
  let ρ : Vsp Kf rest → (Vsp Kf lam →ₗ[Kf] Vsp Kf (flW (m := m) d)) := fun β =>
    (Module.evalEquiv Kf (Vsp Kf (flW (m := m) d))).symm.toLinearMap ∘ₗ
      (((p : Kf) ^ Ar r rest) • Λ β).dualMap ∘ₗ Module.Dual.eval Kf (Vsp Kf lam)
  have hρ : ∀ β T u, T (ρ β u) = (p : Kf) ^ Ar r rest * Λ β T u := by
    intro β T u
    simp only [ρ, LinearMap.comp_apply, LinearEquiv.coe_coe, Module.apply_evalEquiv_symm_apply,
      LinearMap.dualMap_apply, Module.Dual.eval_apply, LinearMap.smul_apply, smul_eq_mul]
  have hI : ∀ β u T, be p r (flW d) (ρ β u) T = be p r lam u (Λ β T) := by
    intro β u T
    unfold be
    rw [map_smul, map_smul, hρ, smul_eq_mul, smul_eq_mul, hAr, zpow_add₀ hp0, mul_assoc]

  have hmem : ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → ∀ β ∈ Re p ι σ w r rest e'.dual,
      ∀ T ∈ Re' p ι σ w r (flW d) e', Λ β T ∈ Re' p ι σ w r lam e' := by
    intro e' he' htg β hβ T hT
    rw [hΛ]
    exact b2 e' he' htg _ (edge_lattice_mul_of_weight_sum D hM p ι σ w hw r hlam hfd hdr e'.dual (hmulR β _) (a2 e' he' htg T hT) hβ)
  have hed := fun e' (he' : IsEdge p n' r e') => (Formalism.L2.G.Model.dual_edge h m r e' he').1

  have hβH : ∀ β ∈ Re p ι σ w r rest e.dual, ∃ β' ∈ HL (O := O) ι σ rest (latDual e.tgt), cw ^ (-(loss : ℤ)) • β' = β :=
    fun β hβ => mem_scale.1 (Re_le_scale_HL h m r rest hdr e.dual (hed e he) loss hord hβ)
  refine ⟨κ0 + κf, hκ, {β : Vsp Kf rest // β ∈ Re p ι σ w r rest e.dual}, fun β => ρ β.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro β u hu
    rw [(bpf e he).2]
    intro T hT
    rw [hI]
    exact ((bpl e he).1 _).1 (hmem e he rfl β.1 β.2 T hT) u hu
  · intro β e' he' htg u hu
    obtain ⟨β', hβ', hβe⟩ := hβH β.1 β.2
    have hβ'' : β' ∈ Re p ι σ w r rest e'.dual :=
      (Formalism.L2.G.Model.dualInclusionLattices p n' W Qq O Kf ι σ j w h m r rest hdr e'.dual (hed e' he')).1 (by
        show β' ∈ HL (O := O) ι σ rest (latDual e'.tgt)
        rw [htg]; exact hβ')
    refine mem_scale.2 ⟨cw ^ (loss : ℤ) • ρ β.1 u, ?_, by
      rw [smul_smul, ← zpow_add₀ hw]; simp⟩
    rw [(bpf e' he').2]
    intro T hT
    rw [be_smulK_left, hI, ← hβe, hΛs, be_smulK_right, ← mul_assoc, ← zpow_add₀ hw]
    simp only [add_neg_cancel, zpow_zero, one_mul]
    exact ((bpl e' he').1 _).1 (hmem e' he' htg β' hβ'' T hT) u hu
  · intro β u hu
    obtain ⟨β', hβ', hβe⟩ := hβH β.1 β.2
    refine mem_scale.2 ⟨((p : Kf) ^ Ar r rest * cw ^ (-(loss : ℤ)))⁻¹ • ρ β.1 u, ?_, by
      rw [smul_smul, mul_inv_cancel₀ (mul_ne_zero (zpow_ne_zero _ hp0) (zpow_ne_zero _ hw)), one_smul]⟩
    apply HL_refl h _ hfd e.tgt he.2.1
    intro T hT
    rw [map_smul, hρ, ← hβe, hΛs, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    have e1 : ((p : Kf) ^ Ar r rest * cw ^ (-(loss : ℤ)))⁻¹ * ((p : Kf) ^ Ar r rest * (cw ^ (-(loss : ℤ)) * Λ β' T u)) =
        Λ β' T u := by
      have h1 := zpow_ne_zero (Ar r rest) hp0
      have h2 := zpow_ne_zero (-(loss : ℤ)) hw
      field_simp
    rw [e1, hΛ]
    have h3 : mulR β' (Ψf T) ∈ HL (O := O) ι σ lam (latDual e.tgt) := by
      have := HL_mul D hM ι σ hlam hfd hdr (latDual e.tgt) cw hw 0 0 (hmulR β' (Ψf T))
        (mem_scale.2 ⟨_, a1 T hT, by simp⟩) (mem_scale.2 ⟨_, hβ', by simp⟩)
      obtain ⟨z, hz, hze⟩ := mem_scale.1 this
      rw [← hze]
      simpa using hz
    exact b1 _ h3 u hu
  · intro β F s u hu
    obtain ⟨F', hF', hT⟩ := hop β.1 F s u hu
    refine ⟨F', hF', ?_⟩
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Kf]
    intro T
    rw [map_sub, sub_eq_zero, hρ, hΛ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact hT T _ (hmulR β.1 (Ψf T))
  · intro u hu hall
    refine mem_scale.2 ⟨cw ^ (-(1 : ℤ)) • u, ?_, by rw [smul_smul, ← zpow_add₀ hw]; simp⟩
    rw [(bpl e he).2]
    intro G hG
    have key : ∀ z ∈ Submodule.span O {z : Vsp Kf lam | ∃ y ∈ Re p ι σ w r (flW d) e.dual,
        ∃ β ∈ Re p ι σ w r rest e.dual, (z : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) = (y : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) * (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf)},
        be p r lam (cw ^ (-(1 : ℤ)) • u) (Ψ0.symm z) ∈ Set.range (algebraMap O Kf) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨y, hy, β, hβ, hzy⟩ := hz
        have hT := a3 y hy
        obtain ⟨z', hz', hz'e⟩ := mem_scale.1 (hall ⟨β, hβ⟩)
        obtain ⟨a, ha⟩ := ((bpf e he).1 _).1 hT z' hz'
        have e1 : Λ β (Ψf.symm ((p : Kf) ^ κf • y)) = ((p : Kf) ^ κ0 * (p : Kf) ^ κf) • Ψ0.symm z := by
          rw [hΛ, Ψf.apply_symm_apply, map_smul, map_smul, map_smul, smul_smul]
          congr 2
          apply Subtype.ext
          rw [hmulR, hzy]
        have e2 := hI β u (Ψf.symm ((p : Kf) ^ κf • y))
        rw [e1, be_smulK_right] at e2
        have e2' : be p r (flW d) (ρ β u) (Ψf.symm ((p : Kf) ^ κf • y)) =
            cw ^ ((2 * (κ0 + κf) + 1 : ℕ) : ℤ) * algebraMap O Kf a := by
          rw [← hz'e, be_smulK_left, ha]
        rw [e2'] at e2
        refine ⟨a, ?_⟩
        rw [be_smulK_left]
        have e3 : (p : Kf) ^ κ0 * (p : Kf) ^ κf = cw ^ ((2 * (κ0 + κf) : ℕ) : ℤ) := by
          rw [← pow_add, Formalism.L2.G.Model.p_eq h, ← pow_mul, zpow_natCast]
        rw [e3] at e2
        have e4 : cw ^ ((2 * (κ0 + κf) + 1 : ℕ) : ℤ) = cw ^ ((2 * (κ0 + κf) : ℕ) : ℤ) * cw := by
          rw [zpow_natCast, zpow_natCast, pow_succ]
        rw [e4, mul_assoc] at e2
        have e5 := mul_left_cancel₀ (zpow_ne_zero _ hw) e2
        rw [← e5, ← mul_assoc, zpow_neg, zpow_one, inv_mul_cancel₀ hw, one_mul]
      | zero => exact ⟨0, by simp [be]⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', ha'⟩ := ha
        obtain ⟨b', hb'⟩ := hb
        exact ⟨a' + b', by rw [map_add (f := _), map_add (f := _), be_add_right, ha', hb']⟩
      | smul t a _ ha =>
        obtain ⟨a', ha'⟩ := ha
        exact ⟨t * a', by rw [← algebraMap_smul Kf t a, map_smul, be_smulK_right, ← ha', map_mul]⟩
    have := key _ (hon (b3 G hG))
    rwa [Ψ0.symm_apply_apply] at this

end Formalism.MainNotions.TestSideCounting
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.DualFockLinear.XiStepNOfP
section
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.TestSideCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.G.WittFrameLocaliserOrders
open Formalism.L2.G.Model (Lin)

def symP (p : ℕ) {n' m r K : ℕ} [NeZero n'] (O : Type) [CommRing O] [IsDomain O] (hk : m + 1 = r + K) (hrk : r ≤ m + 1)
    (F : Frames n' r) (c' Q : ℕ) (P : RRing O n' (r + K)) : MvPolynomial (TV n' (m + 1)) (KK O) :=
  MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) P * SPR O p F hrk c' Q)

def XiAtP (p : ℕ) {n' : ℕ} [NeZero n'] {O : Type} [CommRing O] [IsDomain O] (w : O) {m : ℕ} (r : ℕ)
    (TT : Finset (Fin n')) (d deg : Fin n' → ℕ) (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1)
    (Fr : Frames n' r) (N₁ G' : ℕ) (Y : ℝ) (c0 cP κ : ℕ) (bD : ℝ) {nb : ℕ} (B : Fin nb → RRing O n' (r + K)) : Prop :=
  ∃ DX : ℕ, (DX : ℝ) ≤ bD ∧
    ∀ G : MvPolynomial (TV n' (m + 1)) (KK O),
      G ∈ OpCl TT c0 (Submodule.span (KK O) (Set.range fun b => symP p O hk hrk Fr cP (p ^ G') (B b))) →
      HasMultideg G d → InWj w G 0 → ¬ InWj w G 1 →
      ∃ (nq : ℕ) (o : Fin nq → ℕ) (sig : Fin nq → MvPolynomial (TV n' (m + 1)) (KK O)),
        (∀ q, HasMultideg (sig q) d ∧ OneSidedLemma4Element p K O Fr N₁ G' cP deg Y hk (o q) (sig q)) ∧
        ValLe (Kf := KK O) (p : O) DX
          ((p : KK O) ^ κ * fock G (∑ q, sig q) / (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O))

def XiStepP (C CD CLa : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) [Fact p.Prime] [NeZero n'] (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ (K : ℕ) [NeZero r] [NeZero K] (hk : m + 1 = r + K) (hrk : r ≤ m + 1),
    ∀ F : Frames n' r, FramesOK TT L₁ L₂ (orbitWindowCount r de h x) (goodG' r de h x) F →
    ∀ E' : Fin n' → ℕ,
      (∀ t ∈ F.TT, E' t ≤ E0 p r (r + K) (orbitWindowCount r de h x) (goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar) ∧
        E' t ≤ flatDeg lam0 t) →
    ∀ (nb : ℕ) (B : Fin nb → RRing O n' (r + K)),
      (∀ i, B i ∈ Gen O p K F
        (symbolSpaces CLa p n' O r K F (flatDeg lam0) L₁ (min (orbitWindowCount r de h x) (2 * TT.card))
          (mStar p F (r + K) (orbitWindowCount r de h x) (p ^ goodG' r de h x) (cPrime n' r TT.card c0 cpp cStar)) a Y)
        (G2d F (flatDeg lam0) E')) →
      LinearIndependent O B → (∃ T : Submodule O (RRing O n' (r + K)), IsCompl (Submodule.span O (Set.range B)) T) →
        XiAtP p w r TT (dT TT lam0) (flatDeg lam0) K hk hrk F (orbitWindowCount r de h x) (goodG' r de h x) Y c0
          (cPrime n' r TT.card c0 cpp cStar) (kapFl p (m + 1) (dT TT lam0))
          (CD * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a) B

def RestXiP (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ CDf C₁ : ℝ, 0 < CDf ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → XiStepP C CDf CLa

set_option maxHeartbeats 1000000 in
theorem xiStepN_of_P (C CD CLa : ℝ) (hP : XiStepP C CD CLa) : XiStepN C CD CLa := by
  intro p W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ j w n' m r _ _ TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H φ hφ K
    _ _ hk hrk F hF E' hE' nb B hB hli hc e he htgt hm g hhm hg hbasis
  letI : Algebra (WF p n') O := algOfIdent j φ
  intro FsB hFsB Θ hΘ
  have hkr : orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r := H.2.2.2.2.2.2.2.1
  have hr2 : 2 ≤ r := H.2.1
  obtain ⟨Θ', hΘ1, hΘ2⟩ := theta_exists p n' W Qq O Kf ι σ j w hSet.1 φ hφ m r (vecE n') (dT TT lam0) (flW (dT TT lam0))
    (by omega) (by omega) (isFlat_flW _) hm hhm
  have hΘeq : Θ = Θ' := LinearEquiv.ext fun G => Subtype.ext (by rw [hΘ G, hΘ2 G])
  have hw : algebraMap O (KK O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 hSet.2.1.ne_zero
  obtain ⟨DX, hDX, hP⟩ := hP p W Qq O Kf ι σ j w n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar hSet H K hk hrk F hF
    E' hE' nb B hB hli hc
  refine ⟨DX, hDX, fun F1 h1 h2 h3 => ?_⟩
  refine hP (subst p n' O w n' r g (F1 : MvPolynomial (TV n' (m + 1)) (KK O))) ?_ ?_ ?_ ?_
  · rw [subst_eq_Lin]
    refine Lin_OpCl (Nsub p n' O w r g) (NsubInv p n' O w r g) (Nsub_mul p n' O w r hw hg) TT c0 _ _ ?_ _ h1
    intro f0 hf0
    induction hf0 using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      refine Submodule.subset_span ⟨b, ?_⟩
      show symP p O hk hrk F _ _ (B b) = _
      rw [← subst_eq_Lin, hFsB b]
      unfold symB toK symP
      rw [subst_SPtrue w F hF.2.1 hSet.1.even (by omega) hrk hg, map_mul]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  · exact substPol p n' W Qq O Kf ι σ j w hSet.1 φ hφ (m + 1) r (dT TT lam0) g hg _ F1.2
  · have h4 : Θ' F1 ∈ scale (algebraMap O Kf w ^ ((0 : ℕ) : ℤ)) (Re p ι σ w r (flW (dT TT lam0)) e) := by
      rw [← hΘeq]
      exact mem_scale.2 ⟨Θ F1, h2, by simp⟩
    exact (hΘ1.2 g hg e hbasis F1 0).2 h4
  · intro hI
    apply h3
    have h4 := (hΘ1.2 g hg e hbasis F1 1).1 hI
    rw [← hΘeq] at h4
    simpa using h4

theorem restXiN_of_P (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hP : RestXiP D CLa Ck Crk Cdeg CH CE C6 C18) : RestXiN D CLa Ck Crk Cdeg CH CE C6 C18 := by
  intro hA h14b
  obtain ⟨CDf, C₁, h1, h2, h3⟩ := hP hA h14b
  exact ⟨CDf, C₁, h1, h2, fun C hC => xiStepN_of_P C CDf CLa (h3 C hC)⟩

theorem restXi_of_P (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CH CE C6 C18 : ℝ)
    (hP : RestXiP D CLa Ck Crk Cdeg CH CE C6 C18) : RestXi D CLa Ck Crk Cdeg CH CE C6 C18 :=
  restXi_of_N D CLa Ck Crk Cdeg CH CE C6 C18 (restXiN_of_P D CLa Ck Crk Cdeg CH CE C6 C18 hP)

end Formalism.MainNotions.TestSideCounting
end
end

