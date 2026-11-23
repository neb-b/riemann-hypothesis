module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicIntegral
section
open MeasureTheory

namespace GlobalTheory.HaarAlg

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]

omit [Group K] [IsTopologicalGroup K] in
theorem integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f κ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def avg (F : K → Matrix ι ι ℂ) : Matrix ι ι ℂ := Matrix.of fun a b => ∫ g, F g a b ∂κ

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem mul_avg {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    M * avg κ F = avg κ fun g => M * F g := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ => (integral_const_mul _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [DecidableEq ι] in
theorem avg_mul {F : K → Matrix ι ι ℂ} (hF : Continuous F) (M : Matrix ι ι ℂ) :
    avg κ F * M = avg κ fun g => F g * M := by
  ext a b
  simp only [avg, Matrix.mul_apply, Matrix.of_apply]
  rw [MeasureTheory.integral_finsetSum]
  · exact Finset.sum_congr rfl fun c _ => (integral_mul_const _ _).symm
  · exact fun c _ => integrable_of_continuous κ (by fun_prop)

omit [Group K] [IsTopologicalGroup K] [TopologicalSpace K] [CompactSpace K] [BorelSpace K] [Fintype ι] [DecidableEq ι] in
theorem avg_const (M : Matrix ι ι ℂ) : avg κ (fun _ => M) = M := by
  ext a b
  simp [avg]

variable [κ.IsMulLeftInvariant]

omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι] in
theorem avg_left (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by
  ext a b
  exact integral_mul_left_eq_self (fun g => F g a b) h

theorem rho_mul_avg (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by
  rw [mul_avg κ hρ, ← avg_left κ ρ h]
  simp only [map_mul]

theorem avg_mul_rho (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by
  have hc : Continuous fun g : K => ρ g⁻¹ := hρ.comp continuous_inv
  have h1 : ∀ h, avg κ (fun g => ρ g⁻¹) * ρ h = avg κ fun g => ρ g⁻¹ := fun h => by
    rw [avg_mul κ hc, ← avg_left κ (fun g => ρ g⁻¹) h⁻¹]
    simp only [mul_inv_rev, inv_inv, map_mul]
  have h2 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ ρ := by
    rw [avg_mul κ hc]
    simp only [rho_mul_avg κ ρ hρ, avg_const]
  have h3 : avg κ (fun g => ρ g⁻¹) * avg κ ρ = avg κ fun g => ρ g⁻¹ := by
    rw [mul_avg κ hρ]
    simp only [h1, avg_const]
  rw [h2.symm.trans h3, h1]

theorem isAlgebraic_integral (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (Γ : Set K) (hΓ : Dense Γ)
    (halg : ∀ γ ∈ Γ, ∀ a b, IsAlgebraic ℚ (ρ γ a b)) (a b : ι) : IsAlgebraic ℚ (∫ g, ρ g a b ∂κ) := by
  set P := avg κ ρ with hP
  let Q := algebraicClosure ℚ ℂ
  have key : ∀ s : ℂ ≃ₐ[Q] ℂ, P * P.map s = P.map s ∧ P.map s * P = P.map s := fun s => by
    have hfix : ∀ γ ∈ Γ, (ρ γ).map s = ρ γ := fun γ hγ => by
      ext a b
      exact s.commutes (⟨ρ γ a b, mem_algebraicClosure_iff.2 (halg γ hγ a b)⟩ : Q)
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    have l : ∀ g, ρ g * P.map s = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => ρ g * P.map s) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show ρ γ * P.map s = P.map s
          rw [← hfix γ hγ, ← hm, hP, rho_mul_avg κ ρ hρ]) g
    have r : ∀ g, P.map s * ρ g = P.map s := fun g =>
      congrFun (Continuous.ext_on hΓ (f := fun g => P.map s * ρ g) (g := fun _ => P.map s) (by fun_prop) continuous_const
        fun γ hγ => by
          show P.map s * ρ γ = P.map s
          rw [← hfix γ hγ, ← hm, hP, avg_mul_rho κ ρ hρ]) g
    constructor
    · conv_lhs => rw [hP]
      rw [avg_mul κ hρ]
      simp only [← hP, l, avg_const]
    · conv_lhs => rw [hP]
      rw [mul_avg κ hρ]
      simp only [← hP, r, avg_const]
  have fix : ∀ s : ℂ ≃ₐ[Q] ℂ, P.map s = P := fun s => by
    have h1 := congrArg (fun M : Matrix ι ι ℂ => M.map s) (key s.symm).1
    have e : (P.map s.symm).map s = P := by ext a b; simp
    have hm : ∀ M N : Matrix ι ι ℂ, (M * N).map s = M.map s * N.map s := fun M N => Matrix.map_mul
    simp only [hm, e] at h1
    rw [← (key s).2, h1]
  obtain ⟨q, hq⟩ := GlobalTheory.GaloisDescent.mem_range_algebraMap_of_forall_algEquiv (K := Q) (P a b)
    fun s => congrFun (congrFun (fix s) a) b
  have : P a b ∈ Q := hq ▸ q.2
  exact mem_algebraicClosure_iff.1 this

end GlobalTheory.HaarAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeKerOfLocalFiniteLengthToSimple
section
open scoped TensorProduct

namespace GlobalTheory.TensHead

section HeadKill

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def MinStab (A : Set (Module.End ℂ W)) (T : Submodule ℂ W) : Prop :=
  Stab A T ∧ ∀ U : Submodule ℂ W, Stab A U → U ≤ T → U = ⊥ ∨ U = T

theorem MinStab.map {A : Set (Module.End ℂ W)} {T : Submodule ℂ W} (hT : MinStab A T)
    (b : Module.End ℂ W) (hb : ∀ a ∈ A, a * b = b * a) : MinStab A (T.map b) := by
  obtain ⟨hTs, hTmin⟩ := hT
  have hcomm' : ∀ a ∈ A, ∀ x, a (b x) = b (a x) := fun a ha x =>
    LinearMap.congr_fun (hb a ha) x
  refine ⟨?_, ?_⟩
  · intro a ha y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    rw [hcomm' a ha x]
    exact Submodule.mem_map_of_mem (hTs a ha x hx)
  · intro U hU hUle
    have hU' : Stab A (T ⊓ U.comap b) := by
      intro a ha x hx
      refine ⟨hTs a ha x hx.1, ?_⟩
      show b (a x) ∈ U
      rw [← hcomm' a ha x]
      exact hU a ha (b x) hx.2
    rcases hTmin _ hU' inf_le_left with h | h
    · left
      rw [eq_bot_iff]
      intro u hu
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp (hUle hu)
      have hx' : x ∈ T ⊓ U.comap b := ⟨hx, hu⟩
      rw [h] at hx'
      rw [(Submodule.mem_bot ℂ).mp hx', map_zero]
      exact Submodule.zero_mem _
    · right
      refine le_antisymm hUle ?_
      rw [Submodule.map_le_iff_le_comap]
      intro x hx
      have hx' : x ∈ T ⊓ U.comap b := by rw [h]; exact hx
      exact hx'.2

theorem exists_stab_compl {A : Set (Module.End ℂ W)}
    (htop : sSup {T | MinStab A T} = ⊤) (K : Submodule ℂ W) (hK : Stab A K) :
    ∃ C : Submodule ℂ W, Stab A C ∧ C ⊓ K = ⊥ ∧ C ⊔ K = ⊤ := by
  have hsup : ∀ N N' : Submodule ℂ W, Stab A N → Stab A N' → Stab A (N ⊔ N') := by
    intro N N' hN hN' a ha x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hN a ha y hy) (hN' a ha z hz)
  let S : Set (Submodule ℂ W) := {C | Stab A C ∧ C ⊓ K = ⊥}
  obtain ⟨C, hCmax⟩ : ∃ C, Maximal (· ∈ S) C := by
    refine zorn_le₀ S ?_
    intro c hcS hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ⟨?_, bot_inf_eq _⟩, by simp⟩
      intro a _ x hx
      rw [(Submodule.mem_bot ℂ).mp hx, map_zero]
      exact Submodule.zero_mem _
    · refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · intro a ha x hx
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx ⊢
        obtain ⟨y, hy, hxy⟩ := hx
        exact ⟨y, hy, (hcS hy).1 a ha x hxy⟩
      · rw [eq_bot_iff]
        intro x hx0
        obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
        rw [Submodule.mem_sSup_of_directed hne hc.directedOn] at hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hx' : x ∈ y ⊓ K := ⟨hxy, hxK⟩
        rwa [(hcS hy).2] at hx'
  obtain ⟨⟨hCs, hCK⟩, hCm⟩ := hCmax
  refine ⟨C, hCs, hCK, ?_⟩
  by_contra hne
  have hex : ∃ T, MinStab A T ∧ ¬ T ≤ C ⊔ K := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    exact hne (top_unique (by rw [← htop]; exact sSup_le fun T hT => h T hT))
  obtain ⟨T, ⟨hTs, hTmin⟩, hTn⟩ := hex
  have hI : Stab A (T ⊓ (C ⊔ K)) := fun a ha x hx =>
    ⟨hTs a ha x hx.1, hsup C K hCs hK a ha x hx.2⟩
  rcases hTmin _ hI inf_le_left with h | h
  · have hmem : C ⊔ T ∈ S := by
      refine ⟨hsup C T hCs hTs, ?_⟩
      rw [eq_bot_iff]
      intro x hx0
      obtain ⟨hx, hxK⟩ := Submodule.mem_inf.mp hx0
      obtain ⟨c, hc, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
      have ht' : t ∈ T ⊓ (C ⊔ K) := by
        refine ⟨ht, ?_⟩
        simpa using Submodule.sub_mem _ (Submodule.mem_sup_right hxK : c + t ∈ C ⊔ K)
          (Submodule.mem_sup_left hc : c ∈ C ⊔ K)
      have ht0 : t = 0 := by
        rw [h] at ht'
        exact (Submodule.mem_bot ℂ).mp ht'
      subst ht0
      rw [add_zero] at hxK ⊢
      have hc' : c ∈ C ⊓ K := ⟨hc, hxK⟩
      rwa [hCK] at hc'
    have hle : C ⊔ T ≤ C := hCm hmem le_sup_left
    exact hTn ((le_sup_right.trans hle).trans le_sup_left)
  · exact hTn (inf_eq_left.mp h)

end HeadKill

theorem le_ker_of_simple_commuting {M W : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup W]
    [Module ℂ W]
    (Op : Set (Module.End ℂ M)) (Rel K : Submodule ℂ M) (φ : M →ₗ[ℂ] W)
    (act : Module.End ℂ M → Module.End ℂ W) (B : Set (Module.End ℂ W))
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L)
    (hmax : ∀ N : Submodule ℂ M, Rel ≤ N → Stab Op N → N ≠ ⊤ → N ≤ K)
    (hKtop : K ≠ ⊤) (hK : Stab Op K) (hRel : Rel ≤ LinearMap.ker φ)
    (hφ : ∀ g ∈ Op, φ ∘ₗ g = act g ∘ₗ φ)
    (hcomm : ∀ g ∈ Op, ∀ b ∈ B, act g * b = b * act g)
    (hsimple : ∀ U : Submodule ℂ W, Stab (act '' Op ∪ B) U → U = ⊥ ∨ U = ⊤) :
    K ≤ LinearMap.ker φ := by
  classical
  have hint : ∀ g ∈ Op, ∀ x, φ (g x) = act g (φ x) := fun g hg x =>
    LinearMap.congr_fun (hφ g hg) x
  by_cases hφ0 : LinearMap.range φ = ⊥
  · intro x _
    have hx : φ x ∈ LinearMap.range φ := LinearMap.mem_range_self φ x
    rw [hφ0] at hx
    exact (Submodule.mem_bot ℂ).mp hx
  have hrange : Stab (act '' Op) (LinearMap.range φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    exact LinearMap.mem_range.mpr ⟨g x, hint g hg x⟩
  have hcomap : ∀ U : Submodule ℂ W, Stab (act '' Op) U → Stab Op (U.comap φ) := by
    intro U hU g hg x hx
    show φ (g x) ∈ U
    rw [hint g hg x]
    exact hU _ ⟨g, hg, rfl⟩ _ hx
  have hRelc : ∀ U : Submodule ℂ W, Rel ≤ U.comap φ := by
    intro U x hx
    show φ x ∈ U
    rw [LinearMap.mem_ker.mp (hRel hx)]
    exact U.zero_mem
  obtain ⟨L, hL⟩ := hL
  let P : Set (Submodule ℂ W) := {U | U ≤ LinearMap.range φ ∧ Stab (act '' Op) U ∧ U ≠ ⊥}
  have hwf : P.WellFoundedOn (· < ·) := by
    rw [Set.wellFoundedOn_iff_no_descending_seq]
    intro f hf
    have hlt : ∀ m n : ℕ, m < n → f n < f m := fun m n h => f.map_rel_iff.mpr h
    have hmono : StrictMono (fun i : Fin (L + 1) => (f (L - i.val)).comap φ) := by
      intro i j hij
      have hij' : (i : ℕ) < j := hij
      have hj := j.isLt
      have hlt' : f (L - i.val) < f (L - j.val) := hlt _ _ (by omega)
      show (f (L - i.val)).comap φ < (f (L - j.val)).comap φ
      refine lt_of_le_of_ne (Submodule.comap_mono hlt'.le) ?_
      intro heq
      have hmap := congrArg (Submodule.map φ) heq
      rw [Submodule.map_comap_eq_self (hf _).1, Submodule.map_comap_eq_self (hf _).1] at hmap
      exact hlt'.ne hmap
    have hbound := hL (L + 1) _ hmono (fun j => ⟨hRelc _, hcomap _ (hf _).2.1⟩)
    omega
  have hPne : LinearMap.range φ ∈ P := ⟨le_rfl, hrange, hφ0⟩
  obtain ⟨T, hTP, hTmin⟩ := (Set.wellFoundedOn_iff.mp hwf).has_min P ⟨_, hPne⟩
  have hTms : MinStab (act '' Op) T := by
    refine ⟨hTP.2.1, fun U hU hUT => ?_⟩
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · right
      by_contra hne
      have hUP : U ∈ P := ⟨hUT.trans hTP.1, hU, hU0⟩
      exact hTmin U hUP ⟨lt_of_le_of_ne hUT hne, hUP, hTP⟩
  have hbcomm : ∀ b ∈ B, ∀ a ∈ act '' Op, a * b = b * a := by
    rintro b hb _ ⟨g, hg, rfl⟩
    exact hcomm g hg b hb
  have hstop : sSup {T | MinStab (act '' Op) T} = ⊤ := by
    have hst : Stab (act '' Op ∪ B) (sSup {T | MinStab (act '' Op) T}) := by
      intro a ha
      rcases ha with ha | ha
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy => (le_sSup hT' : T' ≤ _) (hT'.1 a ha y hy)
        exact fun x hx => hle hx
      · have hle : sSup {T | MinStab (act '' Op) T} ≤ (sSup {T | MinStab (act '' Op) T}).comap a :=
          sSup_le fun T' hT' y hy =>
            (le_sSup (MinStab.map hT' a (hbcomm a ha)) : T'.map a ≤ _) (Submodule.mem_map_of_mem hy)
        exact fun x hx => hle hx
    rcases hsimple _ hst with h | h
    · exact absurd (eq_bot_iff.mpr ((le_sSup (show T ∈ {T | MinStab (act '' Op) T} from hTms)).trans h.le)) hTP.2.2
    · exact h
  have hKs : Stab (act '' Op) (K.map φ) := by
    intro a ha y hy
    obtain ⟨g, hg, rfl⟩ := ha
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    rw [← hint g hg k]
    exact Submodule.mem_map_of_mem (hK g hg k hk)
  obtain ⟨C, hCs, hCK, hCtop⟩ := exists_stab_compl hstop (K.map φ) hKs
  have hNK : C.comap φ ⊔ K = ⊤ := by
    rw [eq_top_iff]
    intro m _
    have hm : φ m ∈ C ⊔ K.map φ := by rw [hCtop]; exact Submodule.mem_top
    obtain ⟨c, hc, y, hy, hcy⟩ := Submodule.mem_sup.mp hm
    obtain ⟨k, hk, rfl⟩ := Submodule.mem_map.mp hy
    have hmk : m - k ∈ C.comap φ := by
      show φ (m - k) ∈ C
      rw [map_sub, ← hcy, add_sub_cancel_right]
      exact hc
    simpa using Submodule.add_mem_sup hmk hk
  by_cases hN : C.comap φ = ⊤
  · intro k hk
    have h1 : k ∈ C.comap φ := by rw [hN]; exact Submodule.mem_top
    have h2 : φ k ∈ C ⊓ K.map φ := ⟨h1, Submodule.mem_map_of_mem hk⟩
    rw [hCK] at h2
    exact (Submodule.mem_bot ℂ).mp h2
  · exact absurd (top_unique (hNK.symm.le.trans
      (sup_le (hmax _ (hRelc C) (hcomap C hCs) hN) le_rfl))) hKtop

end GlobalTheory.TensHead
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapSwapShearedProductMeasureUnimodular
section
open MeasureTheory Function
open scoped Pointwise

namespace GlobalTheory.UnfoldNormal

theorem map_swap_map_shear (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H]
    [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] (N : Subgroup H) (hNc : IsClosed (N : Set H))
    (κ : Measure N) (hκ : κ.IsHaarMeasure) (hinv : κ.map (fun n => n⁻¹) = κ) :
    ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)).map Prod.swap
      = (κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N) := by
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology (N : Set H)
  haveI := hκ
  have hsh : Measurable (shear N) := (measurableEmbedding_shear hNc).measurable
  have hT : MeasurePreserving (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) (κ.prod ν) (κ.prod ν) := by
    refine MeasurePreserving.skew_product (f := fun n : N => n⁻¹) (g := fun (n : N) (h : H) => (n : H) * h)
      ⟨measurable_inv, hinv⟩ ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd) ?_
    exact Filter.Eventually.of_forall fun n => (measurePreserving_mul_left ν (n : H)).map_eq
  have hcomm : Prod.swap ∘ shear N = shear N ∘ (fun p : N × H => (p.1⁻¹, (p.1 : H) * p.2)) := by
    funext p
    simp [shear]
  rw [Measure.map_map measurable_swap hsh, hcomm, ← Measure.map_map hsh hT.measurable, hT.map_eq]

end GlobalTheory.UnfoldNormal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixConjTransposeBySymmetricTausskyZassenhaus
section
open Polynomial

namespace GlobalTheory.SymmetricSimilarTranspose

theorem exists_bilin_cyclic {k : Type} [Field k] (f : k[X]) (hf : f ≠ 0) :
    ∃ B : (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] (k[X] ⧸ Submodule.span k[X] {f}) →ₗ[k] k,
      (∀ x y, B ((X : k[X]) • x) y = B x ((X : k[X]) • y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
        ∀ x y, B x y = B y x := by
  obtain ⟨l, h1, h2⟩ := GlobalTheory.SimilarTranspose.exists_form f hf
  let l' : (k[X] ⧸ Ideal.span {f}) →ₗ[k] k :=
    (((Ideal.span {f}).restrictScalars k).liftQ l
      (fun a ha => h1 a (Ideal.mem_span_singleton.mp ha))).comp
      (Submodule.Quotient.restrictScalarsEquiv k (Ideal.span {f})).symm.toLinearMap
  refine ⟨(LinearMap.mul k (k[X] ⧸ Ideal.span {f})).compr₂ l', ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l ((X * a) * b) = l (a * (X * b))
    congr 1; ring
  · intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    refine Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h2 b fun a => ?_))
    have := hy (Ideal.Quotient.mk (Ideal.span {f}) a)
    rw [mul_comm]
    exact this
  · intro x y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {f}) y
    change l (a * b) = l (b * a)
    rw [mul_comm]

theorem exists_bilin {k W : Type} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (T : W →ₗ[k] W) :
    ∃ B : W →ₗ[k] W →ₗ[k] k, (∀ x y, B (T x) y = B x (T y)) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) ∧
      ∀ x y, B x y = B y x := by
  classical
  have htor : Module.IsTorsion k[X] (Module.AEval' T) :=
    Module.AEval.isTorsion_of_finiteDimensional k W T
  obtain ⟨ι, _, p, hp, n, ⟨e⟩⟩ := Module.equiv_directSum_of_isTorsion htor
  choose B hB1 hB2 hB3 using
    fun i => exists_bilin_cyclic (p i ^ n i) (pow_ne_zero _ (hp i).ne_zero)
  let π : ∀ i, W →ₗ[k] (k[X] ⧸ Submodule.span k[X] {p i ^ n i}) := fun i =>
    (((DirectSum.component k[X] ι _ i).comp e.toLinearMap).restrictScalars k).comp
      (Module.AEval'.of T).toLinearMap
  have hπ : ∀ i x, π i x = e (Module.AEval'.of T x) i := fun i x => rfl
  have hT : ∀ i x, π i (T x) = (X : k[X]) • π i x := by
    intro i x
    rw [hπ, hπ, ← Module.AEval'.X_smul_of, map_smul]
    rfl
  refine ⟨∑ i, (B i).compl₁₂ (π i) (π i), ?_, ?_, ?_⟩
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply, hT, hB1]
  · intro y hy
    have h0 : e (Module.AEval'.of T y) = 0 := by
      ext i
      rw [← hπ, DirectSum.zero_apply]
      refine hB2 i _ fun z => ?_
      have := hy ((Module.AEval'.of T).symm (e.symm (DirectSum.lof k[X] ι _ i z)))
      simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply] at this
      rw [Finset.sum_eq_single i] at this
      · rw [hπ i ((Module.AEval'.of T).symm _)] at this
        simpa using this
      · intro j _ hj
        rw [hπ j ((Module.AEval'.of T).symm _)]
        simp [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hj]
      · simp
    simpa using h0
  · intro x y
    simp only [LinearMap.sum_apply, LinearMap.compl₁₂_apply]
    exact Finset.sum_congr rfl fun i _ => hB3 i _ _

theorem main : ∀ (k ι : Type) [Field k] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι k),
    ∃ P : Matrix ι ι k, IsUnit P ∧ P.transpose = P ∧ P * A = A.transpose * P := by
  intro k ι _ _ _ A
  obtain ⟨B, h1, h2, h3⟩ := exists_bilin (Matrix.toLin' A)
  obtain ⟨P, rfl⟩ := (Matrix.toBilin' (R₁ := k) (n := ι)).surjective B
  simp only [Matrix.toBilin'_apply', Matrix.toLin'_apply] at h1 h2 h3
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    refine (injective_iff_map_eq_zero P.mulVecLin).mpr fun y hy => h2 y fun x => ?_
    rw [Matrix.mulVecLin_apply] at hy
    rw [hy, dotProduct_zero]
  · ext i j
    have := h3 (Pi.single j 1) (Pi.single i 1)
    simpa using this
  · apply (Matrix.toBilin' (R₁ := k) (n := ι)).injective
    refine LinearMap.ext₂ fun x y => ?_
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', ← Matrix.mulVec_mulVec, ← h1,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

end GlobalTheory.SymmetricSimilarTranspose
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OperatorStablePiTensorPureKernelSpan
section
open scoped TensorProduct

namespace GlobalTheory.TensHead


open scoped TensorProduct in
theorem _root_.GlobalTheory.TensHead.stab_piOps_piKer {ι : Type} [DecidableEq ι] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    [∀ i, Module ℂ (M i)]
    (Op : ∀ i, Set (Module.End ℂ (M i))) (K : ∀ i, Submodule ℂ (M i))
    (h : ∀ i, _root_.GlobalTheory.TensHead.Stab (Op i) (K i)) :
    _root_.GlobalTheory.TensHead.Stab (_root_.GlobalTheory.TensHead.piOps Op) (_root_.GlobalTheory.TensHead.piKer K) := by
  unfold _root_.GlobalTheory.TensHead.Stab at h ⊢
  rintro _ ⟨i, g, hg, rfl⟩ x hx
  unfold _root_.GlobalTheory.TensHead.piKer at hx ⊢
  have hle : Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}
      ≤ (Submodule.span ℂ {t | ∃ y : ∀ j, M j, (∃ j, y j ∈ K j) ∧ t = PiTensorProduct.tprod ℂ y}).comap
        (_root_.GlobalTheory.TensHead.piOp i g) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, ⟨j, hj⟩, rfl⟩
    refine Submodule.subset_span ⟨fun k => Function.update (fun _ => LinearMap.id) i g k (y k), ⟨j, ?_⟩, ?_⟩
    · by_cases hji : j = i
      · subst hji
        simpa using h j g hg _ hj
      · simpa [Function.update_of_ne hji] using hj
    · simp [_root_.GlobalTheory.TensHead.piOp]
  exact hle hx

end GlobalTheory.TensHead
end

