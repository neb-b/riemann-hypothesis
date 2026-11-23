module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AbsMain
section
open UpperTheory.V.Lit.Dr

private def UpperTheory.V.Lit.Dr.kerRep {Γ A B : Type} [Group Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρ : Representation ℂ Γ A) (σ : Representation ℂ Γ B) (f : A →ₗ[ℂ] B) (hf : ∀ γ x, f (ρ γ x) = σ γ (f x)) :
    Representation ℂ Γ (LinearMap.ker f) where
  toFun γ := (ρ γ).restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hf, hx, map_zero])
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

private theorem UpperTheory.V.Lit.Dr.absPos (q : ℕ) :
    ∀ (Γ M : Type) (Ω : ℕ → Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [∀ q, AddCommGroup (Ω q)] [∀ q, Module ℂ (Ω q)]
    (ρM : Representation ℂ Γ M) (ρ : ∀ q, Representation ℂ Γ (Ω q)) (ι : M →ₗ[ℂ] Ω 0) (d : ∀ q, Ω q →ₗ[ℂ] Ω (q + 1)),
    (∀ γ m, ι (ρM γ m) = ρ 0 γ (ι m)) → (∀ q γ x, d q (ρ q γ x) = ρ (q + 1) γ (d q x)) → Function.Injective ι →
    Function.Exact ι (d 0) → (∀ q, Function.Exact (d q) (d (q + 1))) → (∀ q, HasAverage (ρ q)) →
    ∀ (n : ℕ) (w : Fin n → Ω (q + 1)), (∀ i γ, ρ (q + 1) γ (w i) = w i) → (∀ i, d (q + 1) (w i) = 0) →
    (∀ c : Fin n → ℂ, (∃ y, (∀ γ, ρ q γ y = y) ∧ d q y = ∑ i, c i • w i) → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) (q + 1)) := by
  induction q with
  | zero =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine shiftOne Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) n (fun i => ⟨w i, hdw i⟩)
      (fun i γ => Subtype.ext (hw i γ)) ?_
    rintro c ⟨y, hy, hy'⟩
    refine hind c ⟨y, hy, ?_⟩
    have h : (π y).1 = ∑ i, c i • w i := by rw [hy']; simp
    exact h
  | succ q ih =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine le_trans (ih Γ (LinearMap.ker (d 1)) (fun k => Ω (k + 1)) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1))
      (fun k => ρ (k + 1)) (LinearMap.ker (d 1)).subtype (fun k => d (k + 1)) (fun γ m => rfl)
      (fun k => hd (k + 1)) Subtype.val_injective (LinearMap.exact_subtype_ker_map _) (fun k => hex (k + 1))
      (fun k => hav (k + 1)) n w hw hdw hind) ?_
    exact shiftUp Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) (acyclic Γ (Ω 0) (ρ 0) (hav 0)) q

theorem UpperTheory.V.Lit.Dr.absMain :
    AbsMain := by
  intro q Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
  cases q with
  | zero =>
    choose m hm using fun i => (hex0 (w i)).1 (hdw i)
    refine shiftZero Γ M ρM n m (fun i γ => hinj (by rw [hι, hm, hw])) (fun c hc => hind c ?_)
    have := congrArg ι hc
    simpa [InvExact, hm] using this
  | succ q => exact absPos q Γ M Ω ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Average
section
noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Geo Γ V S d} {u : S → V → ℝ}

end

theorem average : Average := by
  intro Γ V S _ _ _ d G u hu q
  have hu' := hu
  obtain ⟨hsm, hfin, hone⟩ := hu
  have hfs : ∀ (c : Γ → G.Om q) s p, Function.HasFiniteSupport
      (fun g => u (G.σ g⁻¹ s) (G.ρ g⁻¹ p) • (c g).1 s p) := by
    intro c s p
    by_cases hp : p ∈ G.Y
    · obtain ⟨N, hN, hNfin⟩ := hfin s p hp
      refine hNfin.subset ?_
      intro g hg
      refine ⟨p, mem_of_mem_nhds hN, ?_⟩
      intro h0
      apply hg
      simp only [h0, zero_smul]
    · refine Set.finite_empty.subset ?_
      intro g hg
      apply hg
      simp only [((c g).2 _).2 _ hp, smul_zero]
  let A : (Γ → G.Om q) →ₗ[ℂ] G.Om q :=
    { toFun := fun c => ⟨fun s p => ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c γ).1 s p,
        avgMem Γ V S d G u hu' q c⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ + b γ).1 s p =
          ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ).1 s p + ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (b γ).1 s p
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        exact finsum_add_distrib (hfs a s p) (hfs b s p)
      map_smul' := by
        intro z a
        apply Subtype.ext
        funext s p
        show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (z • a γ).1 s p =
          z • ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ).1 s p
        have hm := map_finsum (DistribSMul.toAddMonoidHom (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) z)
          (hfs a s p)
        simp only [DistribSMul.toAddMonoidHom_apply] at hm
        rw [hm]
        congr 1
        funext i
        simp only [Submodule.coe_smul, Pi.smul_apply]
        exact smul_comm _ _ _ }
  refine ⟨A, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext s p
    show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • x.1 s p = x.1 s p
    by_cases hp : p ∈ G.Y
    · rw [← finsum_smul, hone s p hp, one_smul]
    · have hx0 : x.1 s p = 0 := (x.2 s).2 p hp
      simp [hx0]
  · intro γ c
    apply Subtype.ext
    funext s p
    show G.tr q γ (∑ᶠ g, u (G.σ g⁻¹ (G.σ γ⁻¹ s)) (G.ρ g⁻¹ (G.ρ γ⁻¹ p)) • (c g).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
      = ∑ᶠ g, u (G.σ g⁻¹ s) (G.ρ g⁻¹ p) • G.tr q γ ((c (γ⁻¹ * g)).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [map_finsum (G.tr q γ) (hfs c _ _)]
    conv_rhs => rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
    congr 1
    funext h
    simp [_root_.mul_inv_rev, map_mul, Equiv.Perm.mul_apply]

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Poincare
section
open UpperTheory.V.Lit.Dr
open Set ContinuousAlternatingMap
open scoped ContDiff

theorem UpperTheory.V.Lit.Dr.poincare :
    Poincare := by
  intro V F _ _ _ _ _ _ Y hY hconv q w hw hd
  rcases Y.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨0, contDiffOn_empty, fun p hp => hp.elim⟩
  have hseg : ContDiff ℝ ∞ (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) := by fun_prop
  set U : Set (V × ℝ) := (fun z : V × ℝ => p₀ + z.2 • (z.1 - p₀)) ⁻¹' Y with hU
  have hUo : IsOpen U := hY.preimage hseg.continuous
  have hmem : ∀ p ∈ Y, ∀ t ∈ Icc (0 : ℝ) 1, p₀ + t • (p - p₀) ∈ Y :=
    fun p hp t ht => hconv.add_smul_sub_mem hp₀ hp ht
  let Φ : V × ℝ → V [⋀^Fin q]→L[ℝ] F :=
    fun z => z.2 ^ q • (w (p₀ + z.2 • (z.1 - p₀))).curryLeft (z.1 - p₀)
  have hΦ : ContDiffOn ℝ ∞ Φ U := by
    have h1 : ContDiffOn ℝ ∞ (fun z : V × ℝ => w (p₀ + z.2 • (z.1 - p₀))) U :=
      hw.comp hseg.contDiffOn fun z hz => hz
    have h2 : ContDiffOn ℝ ∞ (fun z : V × ℝ => (w (p₀ + z.2 • (z.1 - p₀))).curryLeft) U :=
      (curryLeftLI (𝕜 := ℝ) (E := V) (F := F) (n := q)).toContinuousLinearMap.contDiff.comp_contDiffOn h1
    exact (contDiff_snd.pow q).contDiffOn.smul
      (h2.clm_apply (contDiff_fst.sub contDiff_const).contDiffOn)
  refine ⟨fun p => ∫ t in (0 : ℝ)..1, Φ (p, t),
    paramSmooth V _ Y U Φ hY hUo (fun z hz => hmem z.1 hz.1 z.2 hz.2) hΦ, fun p hp => ?_⟩
  obtain ⟨hc, hD⟩ := paramDeriv V _ p U Φ hUo (hmem p hp) hΦ
  have hI := hc.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) zero_le_one
  have hI' := ((alternatizeUncurryFinCLM ℝ V F).continuous.comp_continuousOn hc).intervalIntegrable_of_Icc
    (μ := MeasureTheory.volume) zero_le_one
  have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => r ^ (q + 1) • w (p₀ + r • (p - p₀)))
      (alternatizeUncurryFinCLM ℝ V F (fderiv ℝ (fun x => Φ (x, t)) p)) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hm := hmem p hp t ht
    exact poinPt V F q w p₀ p t
      ((hw.contDiffAt (hY.mem_nhds hm)).differentiableAt (by simp)) (hd _ hm)
  have h3 := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hI'
  rw [(alternatizeUncurryFinCLM ℝ V F).intervalIntegral_comp_comm hI, ← hD.fderiv] at h3
  refine Eq.trans h3 ?_
  simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.PullB
section
noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem pullB : PullB := by
  intro V F _ _ _ _ _ _ Y hY hC l hl q w hw
  obtain ⟨hlsm, hlpos, _⟩ := hl
  have hφY : ∀ p ∈ Y, l p • p ∈ Y := fun p hp => hC _ (hlpos p hp) p hp
  have hφ : ∀ p ∈ Y, ContDiffAt ℝ ∞ (fun x => l x • x) p := fun p hp =>
    (hlsm.contDiffAt (hY.mem_nhds hp)).smul contDiffAt_id
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w (l p • p) := fun p hp =>
    hw.contDiffAt (hY.mem_nhds (hφY p hp))
  refine ⟨?_, ?_⟩
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply altSmooth V V F q (pull l w) p
    intro v
    have hcomp : ContDiffAt ℝ ∞ (fun y => w (l y • y)) p :=
      ContDiffAt.comp (g := w) (f := fun x => l x • x) p (hwat p hp) (hφ p hp)
    have h := applySmooth V V F q (fun y => w (l y • y))
      (fun i y => fderiv ℝ (fun x => l x • x) y (v i)) p hcomp
      (fun i => ((hφ p hp).fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact h
  · intro p hp
    exact extDeriv_pullback ((hwat p hp).differentiableAt (by simp)) (hφ p hp)
      (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))

end UpperTheory.V.Lit.Dr
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Window
section
noncomputable section

namespace UpperTheory.V.Lit.Dr

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}

private def stab (G : Geo Γ V S d) (s : S) : Subgroup Γ where
  carrier := {γ | G.σ γ s = s}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Equiv.Perm.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, Equiv.Perm.inv_eq_iff_eq, ha]

private def geoStab (G : Geo Γ V S d) (s : S) : Geo (stab G s) V Unit d where
  ρ := G.ρ.comp (stab G s).subtype
  σ := 1
  ξ := 1
  Y := G.Y
  isOpen := G.isOpen
  maps γ := G.maps γ.1

private theorem geoStab_proper (G : Geo Γ V S d) (hG : G.Proper) (s : S) : (geoStab G s).Proper := by
  intro K hK hKc u u'
  refine ((hG K hK hKc s s).preimage (f := fun γ : stab G s => γ.1) Subtype.val_injective.injOn).subset ?_
  rintro γ ⟨-, h⟩
  exact ⟨γ.2, h⟩

private theorem exists_rep (G : Geo Γ V S d) :
    ∃ r : S → S, (∀ s, ∃ δ : Γ, G.σ δ⁻¹ s = r s) ∧ ∀ (γ : Γ) s, r (G.σ γ s) = r s := by
  let R : Setoid S :=
    { r := fun a b => ∃ γ : Γ, G.σ γ a = b
      iseqv :=
        ⟨fun a => ⟨1, by simp⟩,
          fun ⟨γ, h⟩ => ⟨γ⁻¹, by rw [map_inv, Equiv.Perm.inv_eq_iff_eq, h]⟩,
          fun ⟨γ, h⟩ ⟨δ, h'⟩ => ⟨δ * γ, by rw [map_mul, Equiv.Perm.mul_apply, h, h']⟩⟩ }
  refine ⟨fun s => (Quotient.mk R s).out, fun s => ?_, fun γ s => ?_⟩
  · obtain ⟨γ, h⟩ : R.r (Quotient.mk R s).out s := Quotient.exact (Quotient.out_eq _)
    exact ⟨γ, by rw [map_inv, Equiv.Perm.inv_eq_iff_eq, h]⟩
  · have h : Quotient.mk R s = Quotient.mk R (G.σ γ s) := Quotient.sound ⟨γ, rfl⟩
    beta_reduce
    rw [← h]

theorem window : Window := by
  intro Γ V S _ _ _ _ d G hG
  classical
  obtain ⟨r, hr, hrr⟩ := exists_rep G
  choose W hW using fun s => windowOne _ V Unit d (geoStab G s) inferInstance (geoStab_proper G hG s)
  refine ⟨fun s => if r s = s then W s () else ∅, fun s => ?_, fun s p hp => ?_, fun s p hp => ?_⟩
  · beta_reduce
    split_ifs
    · exact (hW s).1 ()
    · exact ⟨isOpen_empty, Set.empty_subset _⟩
  · obtain ⟨δ, hδ⟩ := hr s
    obtain ⟨h, hh⟩ := (hW (r s)).2.1 () _ (G.maps δ⁻¹ p hp)
    have h1 : G.σ (δ * h.1)⁻¹ s = r s := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply, hδ]
      exact (h⁻¹).2
    have h2 : r (r s) = r s := by
      conv_lhs => rw [← hδ]
      exact hrr _ _
    refine ⟨δ * h.1, ?_⟩
    beta_reduce
    rw [h1, if_pos h2, mul_inv_rev, map_mul]
    exact hh
  · obtain ⟨δ, hδ⟩ := hr s
    obtain ⟨N, hN, hfin⟩ := (hW (r s)).2.2 () _ (G.maps δ⁻¹ p hp)
    refine ⟨G.ρ δ⁻¹ ⁻¹' N, (G.ρ δ⁻¹).continuous.continuousAt.preimage_mem_nhds hN,
      (hfin.image fun h => δ * h.1).subset ?_⟩
    rintro γ ⟨x, hx, hγ⟩
    beta_reduce at hγ
    split_ifs at hγ with h0
    · have h1 : G.σ γ⁻¹ s = r s := by rw [← h0, hrr]
      have h2 : δ⁻¹ * γ ∈ stab G (r s) := by
        change G.σ (δ⁻¹ * γ) (r s) = r s
        have h3 : G.σ γ (r s) = s := by rw [← h1, map_inv]; simp
        rw [map_mul, Equiv.Perm.mul_apply, h3, hδ]
      refine ⟨⟨_, h2⟩, ⟨_, hx, ?_⟩, by simp⟩
      rw [h1] at hγ
      change G.ρ (δ⁻¹ * γ)⁻¹ (G.ρ δ⁻¹ x) ∈ W (r s) ()
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_rev, inv_inv, mul_inv_cancel_right]
      exact hγ
    · exact hγ.elim

end UpperTheory.V.Lit.Dr
end
end

