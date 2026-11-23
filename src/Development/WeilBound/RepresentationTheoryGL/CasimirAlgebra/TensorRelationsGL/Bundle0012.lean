module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAnti
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace ColumnAntisymmetry

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ}

def Q (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (σ : Equiv.Perm (Fin m)) : Prop :=
  L ∘ₗ pm σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • L

theorem Q_mul (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {σ τ : Equiv.Perm (Fin m)} (h1 : Q L σ) (h2 : Q L τ) :
    Q L (σ * τ) := by
  unfold Q at *
  rw [pm_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h1, LinearMap.smul_comp, h2, smul_smul,
    Equiv.Perm.sign_mul]
  push_cast
  ring_nf

theorem Q_one (L : TV n M (Fin m) →ₗ[ℂ] ℂ) : Q L 1 := by
  unfold Q
  simp [Module.End.one_eq_id]

theorem Q_swap_iff (L : TV n M (Fin m) →ₗ[ℂ] ℂ) {p q : Fin m} (h : p ≠ q) :
    Q L (Equiv.swap p q) ↔ L ∘ₗ pm (Equiv.swap p q) = -L := by
  unfold Q
  rw [Equiv.Perm.sign_swap h]
  simp

theorem pm_top (σ : Equiv.Perm (Fin m)) (top : Fin n) (g : TV n M (Fin m)) :
    pm σ g (fun _ => top) = g (fun _ => top) := rfl

theorem Q_adj (E : Fin n → Fin n → Module.End ℂ M) (ℓ : M →ₗ[ℂ] ℂ) (top : Fin n) (col : Fin m → ℕ)
    (hmono : Monotone col) (hc : ∀ i j : Fin m, Commute (xJ E i) (xJ E j))
    (hP : ∀ i j : Fin m, (i : ℕ) + 1 = j →
      xJ E j * pm (Equiv.swap i j) = pm (Equiv.swap i j) * xJ E i + 1 ∧
      ∀ k : Fin m, k ≠ i → k ≠ j → Commute (xJ E k) (pm (Equiv.swap i j)))
    (i j : Fin m) (hij : (i : ℕ) + 1 = j) (hcol : col i = col j) :
    Q (ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col) (Equiv.swap i j) := by
  have hne : i ≠ j := by intro h; rw [h] at hij; omega
  rw [Q_swap_iff _ hne]
  obtain ⟨R, hD, hR⟩ := split E col hmono hc hP i j hij hcol
  set P : Module.End ℂ (TV n M (Fin m)) := pm (Equiv.swap i j) with hPdef
  have hx := (hP i j hij).1
  have PP : P * P = 1 := by rw [hPdef, ← pm_mul, Equiv.swap_mul_self, pm_one]
  have h2 : xJ E i * P = P * xJ E j - 1 := by
    calc xJ E i * P = (P * P) * xJ E i * P := by rw [PP, one_mul]
      _ = P * (P * xJ E i + 1) * P - P * P := by noncomm_ring
      _ = P * (xJ E j * P) * P - 1 := by rw [← hx, PP]
      _ = P * xJ E j - 1 := by rw [mul_assoc, mul_assoc, PP, mul_one]
  have hTP : (xJ E i - xJ E j + 1) * P = P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1) := by
    calc (xJ E i - xJ E j + 1) * P = xJ E i * P - xJ E j * P + P := by noncomm_ring
      _ = (P * xJ E j - 1) - (P * xJ E i + 1) + P := by rw [h2, hx]
      _ = _ := by noncomm_ring
  have key : colD E col * P = P * (R + R - colD E col) - (R + R) := by
    rw [hD]
    calc (xJ E i - xJ E j + 1) * R * P = (xJ E i - xJ E j + 1) * P * R := by
          rw [mul_assoc, hR, ← mul_assoc]
      _ = (P * (1 + 1 - (xJ E i - xJ E j + 1)) - (1 + 1)) * R := by rw [hTP]
      _ = _ := by noncomm_ring
  refine LinearMap.ext fun f => ?_
  have e : colD E col (P f) = (colD E col * P) f := rfl
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.proj_apply]
  rw [e, key]
  simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply, Pi.sub_apply, Pi.add_apply,
    pm_top, map_sub, map_add]
  simp only [hPdef, pm_top]
  ring

theorem Q_lt (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (col : Fin m → ℕ) (hmono : Monotone col)
    (hadj : ∀ i j : Fin m, (i : ℕ) + 1 = j → col i = col j → Q L (Equiv.swap i j)) :
    ∀ d (p q : Fin m), (q : ℕ) = p + d + 1 → col p = col q → Q L (Equiv.swap p q) := by
  intro d
  induction d with
  | zero => intro p q h hc; exact hadj p q (by omega) hc
  | succ d ih =>
    intro p q h hc
    let r : Fin m := ⟨(q : ℕ) - 1, by omega⟩
    have hpr : col p = col r := le_antisymm (hmono (show p ≤ r from Fin.le_def.mpr (by simp [r]; omega)))
      (hc ▸ hmono (show r ≤ q from Fin.le_def.mpr (by simp [r])))
    have hrq : col r = col q := hpr ▸ hc
    have h1 : p ≠ r := fun e => by rw [Fin.ext_iff] at e; simp [r] at e; omega
    have h2 : p ≠ q := fun e => by rw [Fin.ext_iff] at e; omega
    have hs : Equiv.swap p q = Equiv.swap r q * Equiv.swap p r * Equiv.swap r q := by
      rw [Equiv.swap_mul_swap_mul_swap h1 h2, Equiv.swap_comm]
    rw [hs]
    have A := hadj r q (by simp [r]; omega) hrq
    exact Q_mul L (Q_mul L A (ih p r (by simp [r]; omega) hpr)) A

theorem Q_colG (L : TV n M (Fin m) →ₗ[ℂ] ℂ) (col : Fin m → ℕ)
    (hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q)) :
    ∀ σ ∈ colG col, Q L σ := by
  intro σ hσ
  induction h : σ.support.card using Nat.strong_induction_on generalizing σ with
  | _ k ih =>
    by_cases h1 : σ = 1
    · rw [h1]; exact Q_one L
    · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
        by_contra hh; push Not at hh; exact h1 (Equiv.ext hh)
      have hmem : ∀ p, col (σ p) = col p := by simpa [colG] using hσ
      have hτ : Equiv.swap x (σ x) * σ ∈ colG col := by
        simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.Perm.mul_apply]
        intro p
        rw [Equiv.swap_apply_def]
        split_ifs with e1 e2
        · rw [hmem x, ← e1, hmem]
        · rw [← hmem x, ← e2, hmem]
        · exact hmem p
      have hlt := Equiv.Perm.card_support_swap_mul hx
      have hq := ih _ (h ▸ hlt) _ hτ rfl
      have hs := hsw x (σ x) hx.symm (hmem x).symm
      have := Q_mul L hs hq
      rwa [← mul_assoc, Equiv.swap_mul_self, one_mul] at this

theorem pm_single (σ : Equiv.Perm (Fin m)) (I : Fin m → Fin n) (v : M) :
    pm σ (Pi.single I v : TV n M (Fin m)) = Pi.single (I ∘ ⇑σ⁻¹) v := by
  funext J
  simp only [pm_apply, Pi.single_apply]
  congr 1
  apply propext
  constructor
  · rintro rfl; funext x; simp
  · rintro rfl; funext x; simp

end ColumnAntisymmetry

open ColumnAntisymmetry in
theorem colAnti_of : TensorGl → JMComm → Height → ColAnti := by
  intro _ hJM hH n M _ _ E hE ℓ hWh top htop m col b hmono hb
  obtain ⟨hc, hP, _⟩ := hJM n M E hE m
  obtain ⟨hH1, _, _⟩ := hH n M E hE ℓ hWh top htop
  have hdeg := hH1 (Fin m) (npairs col) (colD E col) (deg_colD E col)
  set L : TV n M (Fin m) →ₗ[ℂ] ℂ := ℓ ∘ₗ LinearMap.proj (fun _ => top) ∘ₗ colD E col with hL
  have hLs : ∀ I v, L (Pi.single I v) = ℓ (colD E col (Pi.single I v) fun _ => top) := fun _ _ => rfl
  have hsw : ∀ p q : Fin m, p ≠ q → col p = col q → Q L (Equiv.swap p q) := by
    have hadj := fun i j hij hcol => Q_adj E ℓ top col hmono hc hP i j hij hcol
    intro p q hpq hcol
    rcases lt_or_gt_of_ne hpq with h | h
    · exact Q_lt L col hmono hadj ((q : ℕ) - p - 1) p q (by omega) hcol
    · rw [Equiv.swap_comm]
      exact Q_lt L col hmono hadj ((p : ℕ) - q - 1) q p (by omega) hcol.symm
  have hQ := Q_colG L col hsw
  have hbinj : ColInj col b := hb.1
  obtain ⟨c, hcb⟩ : ∃ c : ℂ, ∀ v, L (Pi.single b v) = c * ℓ v := by
    rcases (npairs_le col top htop b hbinj).lt_or_eq with hlt | heq
    · exact ⟨0, fun v => by rw [hLs, (hdeg b).1 hlt v]; simp⟩
    · obtain ⟨c, hc⟩ := (hdeg b).2 heq
      exact ⟨c, fun v => by rw [hLs, hc v]⟩
  have hmemG : ∀ σ ∈ colG col, ∀ p, col (σ p) = col p := fun σ hσ => by simpa [colG] using hσ
  have hval : ∀ σ ∈ colG col, ∀ v, L (Pi.single (b ∘ σ) v) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * (c * ℓ v) := by
    intro σ hσ v
    have hσ' : σ⁻¹ ∈ colG col := by
      simp only [colG, Finset.mem_filter, Finset.mem_univ, true_and]
      intro p
      have := hmemG σ hσ (σ⁻¹ p)
      simp at this
      exact this.symm
    have e : (Pi.single (b ∘ σ) v : TV n M (Fin m)) = pm σ⁻¹ (Pi.single b v) := by
      rw [pm_single, inv_inv]
    rw [e, ← LinearMap.comp_apply, hQ _ hσ', LinearMap.smul_apply, hcb, Equiv.Perm.sign_inv, smul_eq_mul]
  have hzero : ∀ I : Fin m → Fin n, I ∉ (colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ) → ∀ v, L (Pi.single I v) = 0 := by
    intro I hI v
    by_cases hinj : ColInj col I
    · have hle := npairs_le col top htop I hinj
      rcases hle.lt_or_eq with hlt | heq
      · rw [hLs, (hdeg I).1 hlt v]
      · exfalso
        obtain ⟨σ, hσ, e⟩ := eq_of_le col top htop b I hb hinj heq.ge
        exact hI (Finset.mem_image.mpr ⟨σ, hσ, e.symm⟩)
    · simp only [ColInj, not_forall] at hinj
      obtain ⟨p, q, hcol, hIpq, hpq⟩ := hinj
      have hfix : (Pi.single I v : TV n M (Fin m)) = pm (Equiv.swap p q) (Pi.single I v) := by
        rw [pm_single, Equiv.swap_inv]
        congr 1
        funext x
        simp only [Function.comp_apply, Equiv.swap_apply_def]
        split_ifs with h1 h2
        · simpa [h1] using hIpq
        · simpa [h2] using hIpq.symm
        · rfl
      have h := (Q_swap_iff L hpq).mp (hsw p q hpq hcol)
      have h2 : L (Pi.single I v) = -L (Pi.single I v) := by
        conv_lhs => rw [hfix]
        rw [← LinearMap.comp_apply, h, LinearMap.neg_apply]
      have h3 : (2 : ℂ) * L (Pi.single I v) = 0 := by linear_combination h2
      simpa using h3
  refine ⟨c, LinearMap.ext fun f => ?_⟩
  show L f = c * ℓ (cA col b f)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [cA_apply, alt_apply, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← Finset.univ_sum_single f, map_sum]
  rw [← Finset.sum_subset (Finset.subset_univ ((colG col).image (fun σ : Equiv.Perm (Fin m) => b ∘ ⇑σ)))
    (fun I _ hI => hzero I hI (f I))]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [hval σ hσ, map_smul, smul_eq_mul]
    ring
  · intro σ hσ τ hτ e
    refine Equiv.ext fun p => hb.1 _ _ ?_ (congrFun e p)
    rw [hmemG σ hσ, hmemG τ hτ]

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContract
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

open CtrX

theorem contract_of : TensorGl → QdetFacts → WallAlg → TensorGK → LieInv → WallQuot → Contract := by
  intro _ hQ hW hT hL hWQ
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ m hm hS
  classical
  obtain ⟨lab, c, ξ, hlab, hξ, I, w, hw, hφw⟩ := hS
  obtain ⟨N, F, hFgl, hFc, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u; rw [hφ τ u]; simp [Finset.prod_const])
  obtain ⟨τ0, hτ0⟩ : ∃ τ0, lab ⟨0, hm⟩ = τ0 := ⟨_, rfl⟩
  let O := {p : Fin m // ¬ lab p = τ0}
  let e1 := Fintype.equivFin {p : Fin m // lab p = τ0}
  let e : Fin m ≃ O ⊕ Fin (Fintype.card {p : Fin m // lab p = τ0}) :=
    (Equiv.sumCompl (fun p : Fin m => lab p = τ0)).symm.trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCongr (Equiv.refl O) e1))
  let labO : O → ι := fun o => lab o.1
  have hle : lab ∘ e.symm = Sum.elim labO (fun _ => τ0) := by
    funext x
    rcases x with o | j
    · rfl
    · exact (e1.symm j).2
  have hm1 : 0 < Fintype.card {p : Fin m // lab p = τ0} := Fintype.card_pos_iff.2 ⟨⟨⟨0, hm⟩, hτ0⟩⟩
  set ζ := cur (reIx e ξ) with hζdef
  have hζS : ∀ γ, actT (fun _ : Fin (Fintype.card {p : Fin m // lab p = τ0}) => τ0) κ (actT labO κ ρ) γ ζ =
      (∏ τ, (κ τ γ).det ^ c τ) • ζ := by
    intro γ
    apply unc_inj
    rw [← actT_unc, unc_smul, hζdef, unc_cur, ← hle, actT_reIx, hξ γ, reIx_smul]
  obtain ⟨hGO, -⟩ := hT n M ι Γ bar κ E ρ hK hG O labO
  let I0 : O → Fin n := I ∘ e.symm ∘ Sum.inl
  let q : TV n M O →ₗ[ℂ] M ⧸ N := N.mkQ ∘ₗ LinearMap.proj I0
  have hf0 : fib labO τ0 = ∅ := by
    ext o
    simp [fib, labO, o.2]
  have hf1 : fib labO (bar τ0) = ∅ := by
    ext o
    have := hlab o.1 ⟨0, hm⟩
    rw [hτ0] at this
    simp [fib, labO, this]
  have hq : ∀ τ, fib labO τ = ∅ → ∀ a b, q ∘ₗ tE (fib labO τ) (E τ) a b = F τ a b ∘ₗ q := by
    intro τ h a b
    apply LinearMap.ext
    intro f
    show N.mkQ (tE (fib labO τ) (E τ) a b f I0) = F τ a b (N.mkQ (f I0))
    rw [tE_apply, h, Finset.sum_empty, add_zero]
    exact LinearMap.congr_fun (hFE τ a b) (f I0)
  have hξN : ξ I ∉ N := by
    intro h
    exact hφw ((hN _).1 h w hw)
  have hz : q (ζ (I ∘ e.symm ∘ Sum.inr)) ≠ 0 := by
    have h3 : Sum.elim (I ∘ e.symm ∘ Sum.inl) (I ∘ e.symm ∘ Sum.inr) = I ∘ e.symm :=
      Sum.elim_comp_inl_inr (I ∘ e.symm)
    have h4 : ζ (I ∘ e.symm ∘ Sum.inr) I0 = ξ I := by
      simp only [hζdef, cur, reIx, I0, h3]
      congr 1
      funext x
      simp
    show N.mkQ (ζ (I ∘ e.symm ∘ Sum.inr) I0) ≠ 0
    rw [h4, Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero]
    exact hξN
  obtain ⟨m2, hm2, ζ2, hζ2, I2, hI2⟩ := core hQ hW hT hL hK hGO τ0 q (F τ0) (F (bar τ0)) s (hFgl _) (hFgl _)
    (hFc _ _ (Ne.symm (hK.ne τ0))) (hFch τ0) (hFch (bar τ0)) (hq τ0 hf0) (hq _ hf1) hn _ hm1 c ζ hζS
    ⟨_, hz⟩
  let e3 := Fintype.equivFin (O ⊕ Fin m2)
  have hcard : m = Fintype.card O + Fintype.card {p : Fin m // lab p = τ0} := by
    have := Fintype.card_congr e
    simpa [Fintype.card_sum] using this
  refine ⟨Fintype.card (O ⊕ Fin m2), ?_, (Sum.elim labO (fun _ => τ0)) ∘ e3.symm,
    Function.update c τ0 (c τ0 - 1), reIx e3 (unc ζ2), ?_, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_fin]
    omega
  · have hex : ∀ x : O ⊕ Fin m2, ∃ p, Sum.elim labO (fun _ => τ0) x = lab p := by
      rintro (o | j)
      · exact ⟨o.1, rfl⟩
      · exact ⟨⟨0, hm⟩, hτ0.symm⟩
    intro p p'
    obtain ⟨r, hr⟩ := hex (e3.symm p)
    obtain ⟨r', hr'⟩ := hex (e3.symm p')
    simp only [Function.comp_apply]
    rw [hr, hr']
    exact hlab r r'
  · intro γ
    rw [actT_reIx, actT_unc, hζ2 γ, unc_smul, reIx_smul]
  · have hv : reIx e3 (unc ζ2) (Sum.elim I0 I2 ∘ e3.symm) = ζ2 I2 I0 := by
      show unc ζ2 ((Sum.elim I0 I2 ∘ e3.symm) ∘ e3) = _
      rw [show (Sum.elim I0 I2 ∘ e3.symm) ∘ e3 = Sum.elim I0 I2 from by funext x; simp]
      rfl
    have hnot : ζ2 I2 I0 ∉ N := by
      have h5 : N.mkQ (ζ2 I2 I0) ≠ 0 := hI2
      rwa [Submodule.mkQ_apply, Ne, Submodule.Quotient.mk_eq_zero] at h5
    rw [hN] at hnot
    push_neg at hnot
    obtain ⟨w', hw', hφ'⟩ := hnot
    exact ⟨_, w', hw', by rwa [hv]⟩

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStart
section
noncomputable section

open Formalism.REAL Matrix MeasureTheory

namespace PositivityTheory.Rg.Cz

namespace SWS

variable {n : ℕ} {ι Γ : Type} [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ]
  {bar : ι → ι} {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ}

section Int

variable [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] (μ : Measure Γ) [IsFiniteMeasure μ]

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem int_exists (ρ : Γ → Module.End ℂ M) (y : M)
    (hfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun γ => ρ γ y)))
    (hcont : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun γ => lam (ρ γ y)) {g : Γ → ℂ} (hg : Continuous g) :
    ∃ x : M, ∀ lam : M →ₗ[ℂ] ℂ, lam x = ∫ k, g k * lam (ρ k y) ∂μ := by
  classical
  haveI := hfin
  set V := Submodule.span ℂ (Set.range fun γ => ρ γ y) with hV
  let b := Module.finBasis ℂ V
  have hext : ∀ i, ∃ f : M →ₗ[ℂ] ℂ, f ∘ₗ V.subtype = b.coord i := fun i => LinearMap.exists_extend _
  choose e he using hext
  have hmem : ∀ k, ρ k y ∈ V := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hrepr : ∀ k, ρ k y = ∑ i, e i (ρ k y) • (b i : M) := by
    intro k
    have hc : ∀ i, e i (ρ k y) = b.repr ⟨ρ k y, hmem k⟩ i := fun i => by
      have := LinearMap.congr_fun (he i) ⟨ρ k y, hmem k⟩
      simpa using this
    simp_rw [hc]
    have h := congrArg Subtype.val (b.sum_repr ⟨ρ k y, hmem k⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    exact h.symm
  have hint : ∀ i, Integrable (fun k => g k * e i (ρ k y)) μ := fun i =>
    integrable_of_cont μ (hg.mul (hcont (e i)))
  refine ⟨∑ i, (∫ k, g k * e i (ρ k y) ∂μ) • (b i : M), fun lam => ?_⟩
  have hpt : ∀ k, g k * lam (ρ k y) = ∑ i, g k * e i (ρ k y) * lam (b i) := by
    intro k
    conv_lhs => rw [hrepr k]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, Finset.mul_sum, mul_assoc]
  simp_rw [hpt]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => (hint i).mul_const _)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]

omit [MeasurableSpace Γ] [BorelSpace Γ] [CompactSpace Γ] in
theorem mono_left (hK : IsKD bar κ) {m : ℕ} (lab : Fin m → ι) (c : ι → ℤ) (I K : Fin m → Fin n) (γ k : Γ) :
    ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k =
      (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
  have hd : ∀ τ, (κ τ γ).det ≠ 0 := fun τ => det_ne hK τ γ
  have hc : (∏ τ, (κ τ γ).det ^ (-c τ)) * ∏ τ, (κ τ γ).det ^ (c τ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro τ _
    rw [← zpow_add₀ (hd τ)]
    simp
  calc ∑ J : Fin m → Fin n, (∏ p, κ (lab p) γ (I p) (J p)) * mono κ lab c J K k
      = ∑ J : Fin m → Fin n, (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, (κ (lab p) γ (I p) (J p) * κ (lab p) k (J p) (K p)) := by
        apply Finset.sum_congr rfl
        intro J _
        simp only [mono, Finset.prod_mul_distrib]
        ring
    _ = (∏ τ, (κ τ k).det ^ (c τ)) *
          ∏ p, ∑ j, κ (lab p) γ (I p) j * κ (lab p) k j (K p) := by
        rw [Fintype.prod_sum, Finset.mul_sum]
    _ = (∏ τ, (κ τ γ).det ^ (-c τ)) * mono κ lab c I K (γ * k) := by
        simp only [mono, hK.mul, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib, Matrix.mul_apply]
        rw [← mul_assoc, ← mul_assoc, hc, one_mul]

theorem tensor_exists [IsTopologicalGroup Γ] [μ.IsMulLeftInvariant] {E : ι → Fin n → Fin n → Module.End ℂ M}
    {ρ : Γ → Module.End ℂ M} (hK : IsKD bar κ) (hG : IsGK bar κ E ρ) (y : M) {m : ℕ} (lab : Fin m → ι)
    (c : ι → ℤ) (K : Fin m → Fin n) :
    ∃ ξ : TV n M (Fin m), (∀ γ, actT lab κ ρ γ ξ = (∏ τ, (κ τ γ).det ^ (-c τ)) • ξ) ∧
      ∀ I (lam : M →ₗ[ℂ] ℂ), lam (ξ I) = ∫ k, mono κ lab c I K k * lam (ρ k y) ∂μ := by
  classical
  choose ξ hξ using fun I : Fin m → Fin n =>
    int_exists μ ρ y (hG.fin y) (hG.cont y) (g := mono κ lab c I K) (mono_cont hK lab c I K)
  refine ⟨ξ, fun γ => ?_, hξ⟩
  have hLc : ∀ lam : M →ₗ[ℂ] ℂ, Continuous fun k => lam (ρ (γ * k) y) := by
    intro lam
    simpa [hG.mul, Module.End.mul_apply] using hG.cont y (lam ∘ₗ ρ γ)
  have hD : (∏ τ, (κ τ γ).det ^ (-c τ)) = (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ := by
    simp [_root_.zpow_neg, Finset.prod_inv_distrib]
  funext I
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro lam
  rw [map_sub, sub_eq_zero]
  have h1 : ∀ J, lam (ρ γ (ξ J)) = ∫ k, mono κ lab c J K k * lam (ρ (γ * k) y) ∂μ := by
    intro J
    have := hξ J (lam ∘ₗ ρ γ)
    simpa [hG.mul, Module.End.mul_apply] using this
  simp [actT, h1, hξ I lam]
  simp_rw [← integral_const_mul]
  rw [← MeasureTheory.integral_finsetSum]
  · rw [← integral_mul_left_eq_self
      (fun x => (∏ τ, (κ τ γ).det ^ (c τ))⁻¹ * (mono κ lab c I K x * lam (ρ x y))) γ]
    congr 1
    funext k
    rw [← mul_assoc, ← hD, ← mono_left hK lab c I K γ k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro J _
    ring
  · intro J _
    exact integrable_of_cont μ (continuous_const.mul ((mono_cont hK lab c J K).mul (hLc lam)))

end Int

end SWS

theorem swStart_holds : SWStart := by
  unfold SWStart
  intro n M _ _ ι _ _ Γ _ _ _ _ _ bar κ E ρ hK hG φ hφ
  classical
  letI : MeasurableSpace Γ := borel Γ
  haveI : BorelSpace Γ := ⟨rfl⟩
  obtain ⟨H, hH⟩ := SWS.exists_half bar hK.invol hK.ne
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  have hf : Continuous fun k => φ (ρ k y) := hG.cont y φ
  have h1 : φ (ρ 1 y) ≠ 0 := by simpa [hG.one] using hy
  obtain ⟨g, ⟨m, lab, c, I, K, hlab, rfl⟩, hg⟩ :=
    SWS.nonvanish (Measure.haar : Measure Γ) hK hH hf 1 h1
  obtain ⟨ξ, hξ1, hξ2⟩ := SWS.tensor_exists (Measure.haar : Measure Γ) hK hG y lab c K
  refine ⟨m, lab, -c, ξ, ?_, ?_, I, 1, Subalgebra.one_mem _, ?_⟩
  · intro p q h
    exact (hH (lab q)).1 (hlab q) (h ▸ hlab p)
  · intro γ
    rw [hξ1 γ]
    simp
  · simpa [hξ2 I φ] using hg

end PositivityTheory.Rg.Cz

end
end

