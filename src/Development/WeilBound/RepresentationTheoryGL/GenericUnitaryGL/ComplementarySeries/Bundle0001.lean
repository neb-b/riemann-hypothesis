module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0642
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ComplementaryOf
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace Compl

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem irr_sub {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) (W : Submodule ℂ V)
    (hW : ∀ g, ∀ v ∈ W, ρ g v ∈ W) : W = ⊥ ∨ W = ⊤ :=
  (eq_bot_or_eq_top (⟨W, hW⟩ : Subrepresentation ρ)).imp (congrArg Subrepresentation.toSubmodule)
    (congrArg Subrepresentation.toSubmodule)

theorem irr_nontrivial {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  exact bot_ne_top this

def starF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) :
    M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => starRingEnd ℂ (B w v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

def resF {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ) (W : Submodule ℂ M) :
    W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => B v w)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)

@[simp] theorem resF_apply {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ[ℂ] M →ₛₗ[starRingEnd ℂ] ℂ)
    (W : Submodule ℂ M) (v w : W) : resF B W v w = B v w := rfl

theorem exists_herm {ρ : Representation ℂ G V} (h : HasSesq ρ) :
    ∃ B : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ, B ≠ 0 ∧ (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧
      ∀ g v w, B (ρ g v) (ρ g w) = B v w :=
  _root_.UpperTheory.Reformulated.B.SesquilinearFlipConj.main h

def stabG (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem nondeg {ρ : Representation ℂ G V} (hi : ρ.IsIrreducible) (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hC0 : C ≠ 0)
    (hCi : ∀ g v w, C (ρ g v) (ρ g w) = C v w) (v : V) (hv : v ≠ 0) : ∃ x, C v x ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  let R : Submodule ℂ V :=
    { carrier := {v | ∀ x, C v x = 0}
      add_mem' := fun {a b} ha hb x => by simp [ha x, hb x]
      zero_mem' := fun x => by simp
      smul_mem' := fun c a ha x => by simp [ha x] }
  have hR : ∀ g, ∀ y ∈ R, ρ g y ∈ R := by
    intro g y hy x
    have := hCi g y (ρ g⁻¹ x)
    rw [← Module.End.mul_apply (ρ g), ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
    rw [this]; exact hy _
  rcases irr_sub hi R hR with h1 | h1
  · have : v ∈ R := hcon
    rw [h1, Submodule.mem_bot] at this
    exact hv this
  · apply hC0
    ext a b
    have : a ∈ R := h1 ▸ Submodule.mem_top
    simpa using this b

end Compl

open _root_.PositivityTheory.RgGu.NR.Compl in
theorem complementary_of (h : Signature) : Complementary := by
  intro G V _ _ _ _ _ K₀ hK₀o hK₀c F hF hall h0 s hs
  have hsm : IsSmooth (F 0) := (hall 0 le_rfl).2.1
  have hirr : (F s).IsIrreducible := (hall s hs).2.2.1
  haveI := irr_nontrivial hirr
  obtain ⟨H, hH0, hHh, hHi⟩ := exists_herm (hall s hs).2.2.2
  obtain ⟨B₀, hB₀h, hB₀p, hB₀i⟩ := h0
  have key : ∀ K : Subgroup G, IsOpen (K : Set G) → K ≤ K₀ → fixed (F 0) K ≠ ⊥ →
      (∀ w ∈ fixed (F 0) K, w ≠ 0 → 0 < (H w w).re) ∨ (∀ w ∈ fixed (F 0) K, w ≠ 0 → (H w w).re < 0) := by
    intro K hKo hKle hW
    have hKc : IsCompact (K : Set G) := hK₀c.of_isClosed_subset (Subgroup.isClosed_of_isOpen K hKo) hKle
    set W := fixed (F 0) K with hWdef
    haveI : FiniteDimensional ℂ W := (hall 0 le_rfl).1.2 K hKo hKc
    set e := idem hsm hKc with he
    have hconst : ∀ t, ∀ x ∈ K, F t x = F 0 x := fun t x hx => hF.const t x (hKle hx)
    have hker : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ y ∈ twKer (F 0) K 1, ∀ w ∈ W, C y w = 0 ∧ C w y = 0 := by
      intro t C hC y hy w hw
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨n, u, rfl⟩ := hx
        have hn : (F 0) (n : G) w = w := GlobalTheory.Parabolic.mem_fixed.1 hw _ n.2
        have hn' : F t (n : G) = F 0 (n : G) := hconst t _ n.2
        simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, LinearMap.sub_apply]
        constructor
        · rw [← hn, ← hn', hC, hn', hn, sub_self]
        · rw [← hn, ← hn', hC, hn', hn, sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp [hx.1, hy.1, hx.2, hy.2]
      | smul c x _ hx => simp [hx.1, hx.2]
    have hsub : ∀ x : V, x - e x ∈ twKer (F 0) K 1 := fun x => by
      rw [← idem_eq_zero_iff hsm hKc, map_sub, idem_of_mem hsm hKc (idem_mem hsm hKc x), sub_self]
    have hleft : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ x, ∀ w ∈ W, C (e x) w = C x w ∧ C w (e x) = C w x := by
      intro t C hC x w hw
      obtain ⟨h1, h2⟩ := hker t C hC _ (hsub x) w hw
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero] at h1
      rw [map_sub, sub_eq_zero] at h2
      exact ⟨h1.symm, h2.symm⟩
    let T : ℝ → G → Module.End ℂ W := fun t g =>
      (e ∘ₗ (F t g) ∘ₗ W.subtype).codRestrict W (fun v => idem_mem hsm hKc _)
    have hT : ∀ t g (v : W), ((T t g v : W) : V) = e (F t g v) := fun _ _ _ => rfl
    have hinvW : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        ∀ (g : G) (v w : W), resF C W (T t g v) w = resF C W v (T t g⁻¹ w) := by
      intro t C hC g v w
      simp only [resF_apply, hT]
      rw [(hleft t C hC _ w w.2).1, (hleft t C hC _ v v.2).2]
      conv_lhs => rw [← hC g⁻¹]
      rw [← Module.End.mul_apply (F t g⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have hcont : ∀ (g : G) (w : W) (l : Module.Dual ℂ W), Continuous fun t => l (T t g w) := by
      intro g w l
      obtain ⟨m, r, u, hu⟩ := hF.expo g w
      have e1 : ∀ t, T t g w = ∑ i, ((Real.exp (r i * t) : ℝ) : ℂ) • (⟨e (u i), idem_mem hsm hKc _⟩ : W) := by
        intro t
        apply Subtype.ext
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hT, hu t, map_sum, Submodule.coe_sum]
        simp only [map_smul, Submodule.coe_smul]
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [e1, map_sum, map_smul, smul_eq_mul]
      refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hsimple : ∀ t, 0 ≤ t → ∀ U : Submodule ℂ W, (∀ g, ∀ w ∈ U, T t g w ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro t ht U hU
      by_cases hU0 : U = ⊥
      · exact Or.inl hU0
      right
      obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      let S : Submodule ℂ V := Submodule.span ℂ (Set.range fun g => F t g u)
      have hS : ∀ g, ∀ x ∈ S, F t g x ∈ S := by
        intro g x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨g', rfl⟩ := hy
          exact Submodule.subset_span ⟨g * g', by simp only [map_mul, Module.End.mul_apply]⟩
        | zero => simp
        | add x y _ _ hx hy => rw [map_add (f := _)]; exact S.add_mem hx hy
        | smul c x _ hx => rw [map_smul]; exact S.smul_mem c hx
      have hSt : S = ⊤ := by
        rcases irr_sub (hall t ht).2.2.1 S hS with h1 | h1
        · exfalso
          apply hu0
          apply Subtype.ext
          have : ((u : W) : V) ∈ S := Submodule.subset_span ⟨1, by simp⟩
          rw [h1, Submodule.mem_bot] at this
          simpa using this
        · exact h1
      have hmem : ∀ x ∈ S, (⟨e x, idem_mem hsm hKc x⟩ : W) ∈ U := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨g, rfl⟩ := hy
          exact hU g u huU
        | zero =>
          convert U.zero_mem using 1
          exact Subtype.ext (by simp)
        | add x y _ _ hx hy =>
          have : (⟨e (x + y), idem_mem hsm hKc _⟩ : W) = ⟨e x, idem_mem hsm hKc _⟩ + ⟨e y, idem_mem hsm hKc _⟩ :=
            Subtype.ext (by simp)
          rw [this]; exact U.add_mem hx hy
        | smul c x _ hx =>
          have : (⟨e (c • x), idem_mem hsm hKc _⟩ : W) = c • ⟨e x, idem_mem hsm hKc _⟩ := Subtype.ext (by simp)
          rw [this]; exact U.smul_mem c hx
      refine eq_top_iff.2 fun w _ => ?_
      have hw : (⟨e w, idem_mem hsm hKc _⟩ : W) = w := Subtype.ext (idem_of_mem hsm hKc w.2)
      rw [← hw]
      exact hmem w (hSt ▸ Submodule.mem_top)
    haveI : Nontrivial W := (Submodule.nontrivial_iff_ne_bot).2 hW
    have hresne : ∀ t (C : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ), (∀ g v w, C (F t g v) (F t g w) = C v w) →
        (F t).IsIrreducible → C ≠ 0 → resF C W ≠ 0 := by
      intro t C hCi hi hC0 h0'
      obtain ⟨w, hw0⟩ := exists_ne (0 : W)
      obtain ⟨x, hx⟩ := nondeg hi C hC0 hCi w (fun e0 => hw0 (Subtype.ext e0))
      apply hx
      rw [← (hleft t C hCi x w w.2).2]
      have := congrArg (fun f => f w ⟨e x, idem_mem hsm hKc x⟩) h0'
      simpa using this
    have hforms : ∀ t, 0 ≤ t → ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, C ≠ 0 ∧
        (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧ ∀ g v w, C (T t g v) w = C v (T t g⁻¹ w) := by
      intro t ht
      obtain ⟨C, hC0, hCh, hCi⟩ := exists_herm (hall t ht).2.2.2
      exact ⟨resF C W, hresne t C hCi (hall t ht).2.2.1 hC0, fun v w => hCh v w, hinvW t C hCi⟩
    have hpos0 : ∃ C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ, (∀ v w, C w v = starRingEnd ℂ (C v w)) ∧
        (∀ v, v ≠ 0 → 0 < (C v v).re) ∧ ∀ g v w, C (T 0 g v) w = C v (T 0 g⁻¹ w) :=
      ⟨resF B₀ W, fun v w => hB₀h v w, fun v hv => hB₀p v (fun e0 => hv (Subtype.ext e0)), hinvW 0 B₀ hB₀i⟩
    rcases h G W (fun g => g⁻¹) T (fun i w l => hcont i w l) hsimple hforms hpos0 inv_surjective s hs (resF H W)
        (hresne s H hHi hirr hH0) (fun v w => hHh v w) (hinvW s H hHi) with h1 | h1
    · exact Or.inl fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))
    · exact Or.inr fun w hw hw0 => h1 ⟨w, hw⟩ (fun e0 => hw0 (congrArg Subtype.val e0))
  obtain ⟨v₁, hv₁⟩ := exists_ne (0 : V)
  have hopen : ∀ v : V, IsOpen ((stabG (F 0) v : Subgroup G) : Set G) := fun v => hsm v
  let K₁ : Subgroup G := K₀ ⊓ stabG (F 0) v₁
  have hK₁o : IsOpen (K₁ : Set G) := hK₀o.inter (hopen v₁)
  have hv₁K : ∀ K : Subgroup G, K ≤ K₁ → v₁ ∈ fixed (F 0) K :=
    fun K hK => GlobalTheory.Parabolic.mem_fixed.2 fun g hg => (hK hg).2
  have hne : ∀ K : Subgroup G, K ≤ K₁ → fixed (F 0) K ≠ ⊥ := fun K hK h' => by
    have := hv₁K K hK
    rw [h', Submodule.mem_bot] at this
    exact hv₁ this
  have hloc : ∀ v : V, v ≠ 0 → ((0 < (H v₁ v₁).re → 0 < (H v v).re) ∧ ((H v₁ v₁).re < 0 → (H v v).re < 0)) := by
    intro v hv
    let Kv : Subgroup G := K₁ ⊓ stabG (F 0) v
    have hKvo : IsOpen (Kv : Set G) := hK₁o.inter (hopen v)
    have hvK : v ∈ fixed (F 0) Kv := GlobalTheory.Parabolic.mem_fixed.2 fun g hg => hg.2
    rcases key Kv hKvo (inf_le_left.trans inf_le_left) (hne Kv inf_le_left) with h1 | h1
    · have a := h1 v hvK hv
      have b := h1 v₁ (hv₁K Kv inf_le_left) hv₁
      exact ⟨fun _ => a, fun hb => absurd b (not_lt.2 hb.le)⟩
    · have a := h1 v hvK hv
      have b := h1 v₁ (hv₁K Kv inf_le_left) hv₁
      exact ⟨fun hb => absurd b (not_lt.2 hb.le), fun _ => a⟩
  rcases key K₁ hK₁o inf_le_left (hne K₁ le_rfl) with h1 | h1
  · have hp := h1 v₁ (hv₁K K₁ le_rfl) hv₁
    exact ⟨H, fun v w => hHh v w, fun v hv => (hloc v hv).1 hp, hHi⟩
  · have hn := h1 v₁ (hv₁K K₁ le_rfl) hv₁
    refine ⟨-H, fun v w => ?_, fun v hv => ?_, fun g v w => ?_⟩
    · simp [hHh v w]
    · have := (hloc v hv).2 hn
      simp only [LinearMap.neg_apply, Complex.neg_re]
      linarith
    · simp [hHi]

end PositivityTheory.RgGu.NR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.ConjDual
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace ConjDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm' : GlobalTheory.Published.IrreducibleAdmissibleGL := by
  intro k _ _ _ _ n V _ _ π hs hi
  exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hs hi

theorem conj_chi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    starRingEnd ℂ ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) := by
  simp only [detChar, absPow, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Complex.ofReal_cpow (GlobalTheory.SmGL.nabs_pos' k _).le, Complex.conj_ofReal]

end ConjDual

open ConjDual in
theorem conjDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjDual k := by
  intro n V _ _ ρ hs hi hu s
  obtain ⟨B, -, hBpos, hBinv⟩ := hu
  have hinv : ∀ (g : GL (Fin n) k) (w : V), ρ g (ρ g⁻¹ w) = w := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let L : V → Module.Dual ℂ V := fun v =>
    { toFun := fun w => B w v
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  have hL : ∀ v w, L v w = B w v := fun v w => rfl
  have hmem : ∀ v, L v ∈ smoothPart ρ.dual := by
    intro v
    apply GlobalTheory.SmGL.mem_smoothPart_of_nhds
    apply Filter.mem_of_superset ((hs v).mem_nhds (by simp))
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hv' : ρ g⁻¹ v = v := by
      conv_lhs => rw [← hg]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    ext w
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hL, hL]
    rw [← hBinv g⁻¹ w v, hv']
  let φ : V →ₗ⋆[ℂ] smoothPart ρ.dual :=
    { toFun := fun v => ⟨L v, hmem v⟩
      map_add' := by
        intro a b
        ext w
        simp [hL]
      map_smul' := by
        intro c a
        ext w
        simp [hL] }
  have hφ : ∀ v w, (φ v : Module.Dual ℂ V) w = B w v := fun v w => rfl
  have hint : ∀ (g : GL (Fin n) k) (v : V), φ (ρ g v) = contra ρ g (φ v) := by
    intro g v
    ext w
    rw [contra_apply, hφ, hφ, ← hBinv g (ρ g⁻¹ w) v, hinv]
  refine ⟨φ, ⟨?_, ?_⟩, fun g v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h0 := hBpos v hne
    have : B v v = 0 := by
      rw [← hφ, hv]
      rfl
    rw [this] at h0
    simp at h0
  · have hadm := irrAdm' k n V ρ hs hi
    have hbasis : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
        IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
      intro U hU
      obtain ⟨J, hJo, hJU, hJK, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (Fin n) U hU
      exact ⟨J, hJo, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo)
        (fun x hx => hJK hx), hJU⟩
    have hci := GlobalTheory.ContraRefl.contra_isIrreducible hbasis hadm hi
    let S : Subrepresentation (contra ρ) :=
      ⟨LinearMap.range φ, by
        rintro g x ⟨v, rfl⟩
        exact ⟨ρ g v, hint g v⟩⟩
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hi
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hm : φ v ∈ S.toSubmodule := LinearMap.mem_range_self φ v
      rw [h] at hm
      have hz : φ v = 0 := (Submodule.mem_bot ℂ).1 hm
      have h0 := hBpos v hv
      have : B v v = 0 := by
        rw [← hφ, hz]
        rfl
      rw [this] at h0
      simp at h0
    · have hr : LinearMap.range φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  · rw [twist_apply, twist_apply, map_smulₛₗ, conj_chi, hint]

end PositivityTheory.RgGu.NR

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.PiTensorTwist
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
  GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.RgGu.NR

namespace Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem prodIrr_congr {h N : ℕ} {y z : Fin h → IrrGL (k := k)} (e : y = z) (hy : ∑ a, (y a).1 = N) (hz : ∑ a, (z a).1 = N) :
    Nonempty ((prodIrr y hy).Equiv (prodIrr z hz)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

theorem piTensor_twist (x : IrrGL (k := k)) (s : ℝ) :
    piTensor (fun a : Fin 2 => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))) =
      twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) := by
  ext g : 1
  refine PiTensorProduct.ext (MultilinearMap.ext fun v => ?_)
  have ht : ∀ {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
      (χ : GL (Fin n) k →* ℂˣ) (g : GL (Fin n) k), twist ρ χ g = ((χ g : ℂ) • ρ g) := fun _ _ _ => rfl
  have ht2 : ∀ (g : Levi k fun _ : Fin 2 => Fin x.1), twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s) g =
      ((chi k x.1 s g : ℂ) • (piTensor fun _ : Fin 2 => x.rep) g) := fun _ => rfl
  simp only [LinearMap.compMultilinearMap_apply, piTensor_tprod, ht, ht2, LinearMap.smul_apply]
  rw [MultilinearMap.map_smul_univ]
  congr 1
  simp [chi, Fin.prod_univ_two, Units.val_mul]

end Model

open Model in
theorem prodModel (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ProdModel k := by
  intro x s hd
  let π : ∀ a : Fin 2, Representation ℂ (GL (Fin x.1) k) x.2.rep.V :=
    fun a => twist x.rep (detChar (Fin x.1) (absPow k (![-(s : ℂ), (s : ℂ)] a)))
  have hs : ∀ a, IsSmooth (π a) := fun a => isSmooth_twist x.2.rep.smooth (isSmoothChar_absPow _).detChar
  have hi : ∀ a, (π a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have e1 := prodIrrEquiv (d := fun _ : Fin 2 => x.1) (sum_two x.1) π hs hi
  have hy : (fun a => IrrGL.of (π a) (hs a) (hi a)) = ![x.nu (-(s : ℂ)), x.nu (s : ℂ)] := by
    funext a
    have key : ∀ c : ℂ, IrrGL.of (twist x.rep (detChar (Fin x.1) (absPow k c))) (isSmooth_twist x.2.rep.smooth
        (isSmoothChar_absPow c).detChar) (isIrreducible_twist x.2.rep.irr _) = x.nu c := fun c =>
      (IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr (absPow k c) (isSmoothChar_absPow c)).symm.trans
        (congrArg (fun y => IrrGL.tw y (absPow k c) (isSmoothChar_absPow c)) (IrrGL.of_rep x))
    fin_cases a
    · exact key _
    · exact key _
  obtain ⟨e2⟩ := prodIrr_congr hy (sum_two x.1) hd
  have e3 : (multiProd (stdBlocks (fun _ : Fin 2 => x.1) (sum_two x.1)) π).Equiv
      (parInd (blk2 x.1) (twist (piTensor fun _ : Fin 2 => x.rep) (chi k x.1 s))) :=
    parIndEquiv (blk2 x.1) ((piTensor_twist x s) ▸ Representation.Equiv.refl _)
  exact ⟨(e2.symm.trans e1.symm).trans e3⟩

theorem cuspUnit (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CuspUnit k := by
  intro y hy
  obtain ⟨ω, hωs, hω⟩ := exists_smooth_hasCentralChar y.2.rep.smooth y.2.rep.irr
  obtain ⟨s, hs⟩ := GlobalTheory.SmoothCharNorm.norm_eq_nabs_rpow k ω hωs
  have hN : (y.1 : ℝ) ≠ 0 := by exact_mod_cast hy.1.ne'
  refine ⟨y.nu ((-(s / y.1) : ℝ) : ℂ), s / y.1, hy.nu _, ?_, ?_⟩
  · have hρc : (y.nu ((-(s / y.1) : ℝ) : ℂ)).IsCusp := hy.nu _
    have hcc := UnitaryOrder.hasCentralChar_nu y hω ((-(s / y.1) : ℝ) : ℂ)
    have hi := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.irr
    have hsm := (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.smooth
    haveI := GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible hi
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : (y.nu ((-(s / y.1) : ℝ) : ℂ)).2.rep.V)
    obtain ⟨l, hl⟩ := GlobalTheory.ContraRefl.exists_smooth_form_ne hsm (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv₀
    refine GlobalTheory.isUnitarisable_of_isSupercuspidal _ _ _ (l : Module.Dual ℂ _) l.2
      (fun e => hl (by rw [e]; rfl)) hi (GlobalTheory.CuspCoef.isSupercuspidal_of_isCuspidal k _ _ _ hρc.2) ?_
    intro g hg
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨a, rfl⟩ := hg
    refine ⟨_, ?_, hcc a⟩
    have h1 := UnitaryOrder.log_norm_mul_absPow ω (-(s / y.1)) y.1 a
    have hpos := nabs_pos' k a
    rw [hs a, Real.log_rpow hpos] at h1
    have h2 : Real.log ‖(((ω * absPow k ((-(s / y.1) : ℝ) : ℂ) ^ y.1) a : ℂˣ) : ℂ)‖ = 0 := by
      rw [h1]; field_simp; ring
    exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.2 (Units.ne_zero _)) h2
  · rw [IrrGL.nu_nu, show ((-(s / y.1) : ℝ) : ℂ) + ((s / y.1 : ℝ) : ℂ) = 0 by push_cast; ring, IrrGL.nu_zero]

end PositivityTheory.RgGu.NR

end
end

