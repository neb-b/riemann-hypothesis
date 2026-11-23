module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0018
public import Formalism.LocalToGlobal.IndefiniteReal.CxPassSand

@[expose] public section

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.PeterssonHilbertSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure IsHermPos {N : Type} [AddCommGroup N] [Module ℂ N] (C : Submodule ℂ N) (ip : N → N → ℂ) : Prop where
  fd : FiniteDimensional ℂ C
  add : ∀ x x' y : C, ip ((x : N) + x') y = ip x y + ip x' y
  smul : ∀ (s : ℂ) (x y : C), ip (s • (x : N)) y = starRingEnd ℂ s * ip x y
  herm : ∀ x y : C, starRingEnd ℂ (ip x y) = ip y x
  pos : ∀ x : C, x ≠ 0 → 0 < (ip x x).re

section Gen

variable {N : Type} [AddCommGroup N] [Module ℂ N] {C : Submodule ℂ N} {ip : N → N → ℂ}

theorem isHermPos_scale (h : IsHermPos C ip) {s : ℝ} (hs : 0 < s) :
    IsHermPos C (fun x y => (s : ℂ) * ip x y) := by
  refine ⟨h.fd, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    simp only [h.add x x' y, mul_add]
  · intro a x y
    simp only [h.smul a x y]
    ring
  · intro x y
    simp only [map_mul, Complex.conj_ofReal, h.herm x y]
  · intro x hx
    simp only [Complex.re_ofReal_mul]
    exact mul_pos hs (h.pos x hx)

theorem IsHermPos.map_equiv {N' : Type} [AddCommGroup N'] [Module ℂ N'] (h : IsHermPos C ip) (e : N ≃ₗ[ℂ] N') :
    IsHermPos (C.map (e : N →ₗ[ℂ] N')) (fun x y => ip (e.symm x) (e.symm y)) := by
  have hm : ∀ z : C.map (e : N →ₗ[ℂ] N'), e.symm (z : N') ∈ C := by
    intro z
    obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.mp z.2
    rw [← hyz]
    simpa using hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · haveI := h.fd
    infer_instance
  · intro x x' y
    show ip (e.symm ((x : N') + x')) (e.symm y) = ip (e.symm x) (e.symm y) + ip (e.symm x') (e.symm y)
    rw [map_add (f := _)]
    exact h.add ⟨_, hm x⟩ ⟨_, hm x'⟩ ⟨_, hm y⟩
  · intro s x y
    show ip (e.symm (s • (x : N'))) (e.symm y) = starRingEnd ℂ s * ip (e.symm x) (e.symm y)
    rw [map_smul]
    exact h.smul s ⟨_, hm x⟩ ⟨_, hm y⟩
  · intro x y
    exact h.herm ⟨_, hm x⟩ ⟨_, hm y⟩
  · intro x hx
    refine h.pos ⟨_, hm x⟩ ?_
    intro h0
    apply hx
    apply Subtype.ext
    have h1 : e.symm (x : N') = 0 := congrArg Subtype.val h0
    simpa using h1

end Gen

section MultSec

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def PetPos (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ F : GA D V → ℂ, Continuous F → (∀ γ ∈ GQ V, ∀ g, F (γ * g) = F g) → F ≠ 0 →
    IntegrableOn (fun g => ‖F g‖ ^ 2) 𝓕 μ → 0 < ∫ g in 𝓕, ‖F g‖ ^ 2 ∂μ

def SmNonzero (M : DSModel V S) : Prop := ∀ τ, ∃ w : M.sm τ, w ≠ 0

variable (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem isMultiplicityInner_add_left {T T' T'' : MMap M} {a b : ℂ} (h : IsMultIP M μ 𝓕 T T'' a)
    (h' : IsMultIP M μ 𝓕 T' T'' b) : IsMultIP M μ 𝓕 (T + T') T'' (a + b) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v v'
  obtain ⟨i2, e2⟩ := h' v v'
  simp only [MultilinearMap.add_apply, Pi.add_apply, star_add, add_mul]
  exact ⟨Integrable.add i1 i2, by rw [integral_add i1 i2, e1, e2]⟩

theorem isMultiplicityInner_smul_left {T T' : MMap M} {a : ℂ} (s : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M μ 𝓕 (s • T) T' (starRingEnd ℂ s * a) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v v'
  have hf : ∀ g, star ((s • T) v g) * T' v' g = starRingEnd ℂ s * (star (T v g) * T' v' g) := by
    intro g
    rw [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]
    rfl
  simp only [hf]
  exact ⟨Integrable.const_mul i1 _, by rw [integral_const_mul, e1, mul_assoc]⟩

theorem isMultiplicityInner_swap {T T' : MMap M} {a : ℂ} (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M μ 𝓕 T' T (starRingEnd ℂ a) := by
  intro v v'
  obtain ⟨i1, e1⟩ := h v' v
  have hf : ∀ g, star (T' v g) * T v' g = starRingEnd ℂ (star (T v' g) * T' v g) := by
    intro g
    show _ = star (star (T v' g) * T' v g)
    rw [star_mul', star_star, mul_comm]
  simp only [hf]
  refine ⟨((Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp i1).congr (ae_of_all _ fun g => ?_), ?_⟩
  · simp
  rw [integral_conj, e1, map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => inner_conj_symm _ _

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V)) (χ : GA D V → ℂ)

theorem mult_cont_left {T : MMap M} (hT : T ∈ Mult θ M J χ) (v : M.Vec) :
    Continuous (T v) ∧ ∀ γ ∈ GQ V, ∀ g, T v (γ * g) = T v g := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT =>
    have hA := (show IsMultMap θ M J χ T from hT).aut v
    exact ⟨hA.cont, hA.left⟩
  | zero =>
    refine ⟨?_, fun _ _ _ => rfl⟩
    simp only [MultilinearMap.zero_apply]
    exact continuous_const
  | add T T' _ _ h1 h2 =>
    refine ⟨?_, fun γ hγ g => ?_⟩
    · rw [MultilinearMap.add_apply]
      exact h1.1.add h2.1
    · simp only [MultilinearMap.add_apply, Pi.add_apply, h1.2 γ hγ g, h2.2 γ hγ g]
  | smul a T _ h1 =>
    refine ⟨?_, fun γ hγ g => ?_⟩
    · rw [MultilinearMap.smul_apply]
      exact h1.1.const_smul a
    · simp only [MultilinearMap.smul_apply, Pi.smul_apply, h1.2 γ hγ g]

theorem isHermPos_mult (hθ : IsInfFam θ) (hfin : HCFinite θ M J χ)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    (hS : SchurMult θ M J χ μ 𝓕) (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hP : PetPos V μ 𝓕) (hne : SmNonzero M) : IsHermPos (Mult θ M J χ) (ipM M μ 𝓕) := by
  have hfd : FiniteDimensional ℂ (Mult θ M J χ) := hfin hθ hU

  have huniq : ∀ (T T' : MMap M) (c c' : ℂ), IsMultIP M μ 𝓕 T T' c → IsMultIP M μ 𝓕 T T' c' → c = c' := by
    intro T T' c c' h h'
    have hne' : ∀ τ, ∃ w : M.sm τ, w ≠ 0 := hne
    choose w hw using hne'
    have hp : (∏ τ, ⟪((w τ : M.sm τ) : M.H τ), ((w τ : M.sm τ) : M.H τ)⟫_ℂ) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro τ _
      rw [inner_self_ne_zero]
      intro h0
      exact hw τ (Subtype.ext h0)
    have e := (h w w).2
    have e' := (h' w w).2
    exact mul_right_cancel₀ hp (e.symm.trans e')
  have hval : ∀ (T T' : MMap M) (c : ℂ), IsMultIP M μ 𝓕 T T' c → ipM M μ 𝓕 T T' = c := by
    intro T T' c h
    have hex : ∃ c, IsMultIP M μ 𝓕 T T' c := ⟨c, h⟩
    unfold ipM
    rw [dite_eq_left hex]
    exact huniq _ _ _ _ hex.choose_spec h
  have hE : ∀ x y : Mult θ M J χ, ∃ c, IsMultIP M μ 𝓕 x y c := fun x y => hS hθ hH hF _ x.2 _ y.2
  refine ⟨hfd, ?_, ?_, ?_, ?_⟩
  · intro x x' y
    obtain ⟨a, ha⟩ := hE x y
    obtain ⟨b, hb⟩ := hE x' y
    rw [hval _ _ _ ha, hval _ _ _ hb]
    exact hval _ _ _ (isMultiplicityInner_add_left M μ 𝓕 ha hb)
  · intro s x y
    obtain ⟨a, ha⟩ := hE x y
    rw [hval _ _ _ ha]
    exact hval _ _ _ (isMultiplicityInner_smul_left M μ 𝓕 s ha)
  · intro x y
    obtain ⟨a, ha⟩ := hE x y
    rw [hval _ _ _ ha, hval _ _ _ (isMultiplicityInner_swap M μ 𝓕 ha)]
  · intro x hx
    obtain ⟨c, hc⟩ := hE x x
    rw [hval _ _ _ hc]
    have hx' : (x : MMap M) ≠ 0 := fun h0 => hx (Subtype.ext h0)
    obtain ⟨v, hv⟩ : ∃ v, (x : MMap M) v ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx' (MultilinearMap.ext hcon)
    obtain ⟨hi, he⟩ := hc v v
    have hcl := mult_cont_left M θ J χ x.2 v
    have hI : IntegrableOn (fun g => ‖(x : MMap M) v g‖ ^ 2) 𝓕 μ := by
      refine (Integrable.norm hi).congr (ae_of_all _ fun g => ?_)
      simp only [norm_mul, norm_star, sq]
    have hpos := hP ((x : MMap M) v) hcl.1 hcl.2 hv hI

    have hvne : ∀ τ, ((v τ : M.sm τ) : M.H τ) ≠ 0 := by
      intro τ h0
      apply hv
      exact (x : MMap M).map_coord_zero τ (Subtype.ext h0)
    have hL : ∫ g in 𝓕, star ((x : MMap M) v g) * (x : MMap M) v g ∂μ =
        ((∫ g in 𝓕, ‖(x : MMap M) v g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      refine Eq.trans ?_ (integral_ofReal (𝕜 := ℂ) (μ := μ.restrict 𝓕) (f := fun g => ‖(x : MMap M) v g‖ ^ 2))
      congr 1
      funext g
      rw [RCLike.ofReal_pow]
      exact RCLike.conj_mul _
    have hR : (∏ τ, ⟪((v τ : M.sm τ) : M.H τ), ((v τ : M.sm τ) : M.H τ)⟫_ℂ) =
        ((∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.prod_congr rfl fun τ _ => inner_self_eq_norm_sq_to_K _
    have hRpos : 0 < ∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 :=
      Finset.prod_pos fun τ _ => pow_pos (norm_pos_iff.mpr (hvne τ)) 2
    rw [hL, hR] at he
    have hc' : c = (((∫ g in 𝓕, ‖(x : MMap M) v g‖ ^ 2 ∂μ) / ∏ τ, ‖((v τ : M.sm τ) : M.H τ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, he, mul_div_assoc, div_self (by exact_mod_cast hRpos.ne'), mul_one]
    rw [hc', Complex.ofReal_re]
    exact div_pos hpos hRpos

def ipMT' (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V))
    (x y : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) : ℂ :=
  ipM M μ 𝓕 (PiTensorProduct.lift.symm x) (PiTensorProduct.lift.symm y)

theorem isHermPos_multT (hθ : IsInfFam θ) (hfin : HCFinite θ M J χ)
    (hU : ∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → k ∈ J ∧ χ k = 1)
    (hS : SchurMult θ M J χ μ 𝓕) (hH : μ.IsHaarMeasure) (hF : IsFundamentalDomain (GQ V) 𝓕 μ)
    (hP : PetPos V μ 𝓕) (hne : SmNonzero M) : IsHermPos (MultT θ M J χ) (ipMT' M μ 𝓕) :=
  (isHermPos_mult M μ 𝓕 θ J χ hθ hfin hU hS hH hF hP hne).map_equiv PiTensorProduct.lift

end MultSec

end Formalism.IndefR.PeterssonHilbertSpace

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.RowGSurj
section
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem mem_RRg {x : Fin I.Sg.D → K} : x ∈ I.Sg.RR ↔ ∀ w : HeightOneSpectrum (𝓞 K), ∃ c ∈ w.asIdeal.primeCompl,
    ∃ z ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ (I.X.μ w),
      I.X.rowMat I.cg false (I.X.μ w) *ᵥ z = c • x := by
  simp only [Formalism.L2.Indef.IndefData.RR, Formalism.DivisionValues.glueLat, Submodule.mem_iInf, Formalism.HermitianLatticesTheory.localization₂, Formalism.HermitianLatticesTheory.locS,
    Formalism.DivisionValues.matLat, Submodule.mem_map]
  rfl

theorem mem_RRb (b : Bool) {x : Fin (I.Sb b).D → K} : x ∈ (I.Sb b).RR ↔ ∀ w : HeightOneSpectrum (𝓞 K),
    ∃ c ∈ w.asIdeal.primeCompl, ∃ z ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ (I.X.μ w),
      I.X.rowMat I.cr b (I.X.μ w) *ᵥ z = c • x := by
  simp only [Formalism.L2.Indef.IndefData.RR, Formalism.DivisionValues.glueLat, Submodule.mem_iInf, Formalism.HermitianLatticesTheory.localization₂, Formalism.HermitianLatticesTheory.locS,
    Formalism.DivisionValues.matLat, Submodule.mem_map]
  rfl

section Prin

variable {I} {s : ℕ} (hH : I.Hyp s)
include hH

theorem hZ_of (t : T) : ∀ g : G, I.X.Z t ≤ (I.X.Z t).comap ((I.A.fam.R t).r g) :=
  fun g _ hz => hH.stable.1 t (Sum.inr g) (Submodule.mem_map_of_mem hz)

theorem key_g (t : T) (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t) → K) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ x)) =
      I.X.Θ t (I.X.jR t (I.cg.toR I.X.zs false t x)) := by
  have h1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ x)) =
      I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding x) := by
    rw [cpt_mulVec, CxData.rowMat, kMat_map _ (hH.ratMug t)]
    refine relMat_spec _ _ (fun k => ?_) _
    have e : LinearMap.range (I.X.iC I.cg false t) = LinearMap.range I.iCg := (hH.h2g.2 t).2
    rw [← e]
    exact ⟨_, rfl⟩
  rw [h1, CxData.iC_eq_comp, CxData.lin_uQ_cpt]

theorem inj_g {x y : Fin I.Sg.D → K}
    (h : I.iCg (cpt I.A3.fam3.base3.v0.embedding x) = I.iCg (cpt I.A3.fam3.base3.v0.embedding y)) : x = y := by
  have h1 : cpt I.A3.fam3.base3.v0.embedding x = cpt I.A3.fam3.base3.v0.embedding y := by
    first
    | exact hH.h2g.1 h
    | exact (hH.h2g.2 I.A3.fam3.base3.μ0).1 h
  funext i
  have h2 := congrFun h1 i
  simp only [cpt] at h2
  exact I.A3.fam3.base3.v0.embedding.injective h2

theorem rowG_surj (t : T) : Function.Surjective (I.X.rowMat I.cg false t).mulVec :=
  (bij_of_map I.A3.fam3.base3.v0.embedding _ (by
    rw [CxData.rowMat, kMat_map _ (hH.ratMug t)]
    exact relMat_bij _ _ hH.h2g.1 (hH.h2g.2 t).1 (hH.h2g.2 t).2)).2

theorem epM_idem (hρ : I.PRho) (P : Subgroup G) (ψ : P →* Kˣ) : I.epM P ψ * I.epM P ψ = I.epM P ψ := by
  obtain ⟨h1, hm, -⟩ := hρ s hH
  letI : Fintype P := Fintype.ofFinite P
  have hmul : ∀ h k : P, ((((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)) * ((((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G)) =
      (((ψ (h * k))⁻¹ : Kˣ) : K) • I.ρf ((h * k : P) : G) := by
    intro h k
    first
    | rw [smul_mul_smul_comm]
    | rw [smul_mul_smul]
    rw [← hm, Subgroup.coe_mul, map_mul, mul_inv, Units.val_mul]
  have hSS : (∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)) * (∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)) =
      (Fintype.card P : K) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, hmul]
    have e : ∀ h : P, ∑ k : P, (((ψ (h * k))⁻¹ : Kˣ) : K) • I.ρf ((h * k : P) : G) =
        ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G) :=
      fun h => Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun k => rfl)
    simp_rw [e]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]
  unfold epM
  first
  | rw [smul_mul_smul_comm, hSS, smul_smul]
  | rw [smul_mul_smul, hSS, smul_smul]
  congr 1
  have hne : (Fintype.card P : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card]
  field_simp

theorem toRg_inj (t : T) : Function.Injective (I.cg.toR I.X.zs false t) :=
  BlockDat.toF_injective (I.A.fam.R t) (Lvl.full I.A.fam.X) (I.X.Z t)

theorem sub_g (t : T) (P : Subgroup G) (ψ : P →* Kˣ)
    (J : Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((I.A.fam.R t).dZ (I.A.fam.lvl P ψ) (I.X.Z t))) K)
    (hJ : ∀ x, I.cg.toR I.X.zs false t (J *ᵥ x) = (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) x) :
    ∀ y ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
      J *ᵥ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hy
  obtain ⟨f', hf', he⟩ := Sand.sub_toF (B := I.A.fam.R t) (hv0 := hH.ok.ok2.conj) (hOk := hH.ok.ok2.what₂ t)
    (hX := hH.ok.ok2.irr) (Z := I.X.Z t) (hZ := hZ_of hH t) (P := P) (ψ := ψ) f hf
  have hex : ∃ z ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      I.cg.toR I.X.zs false t z =
        (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) ((I.A.fam.R t).Pq (I.A.fam.lvl P ψ) (I.X.Z t) *ᵥ f) :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨f', hf', rfl⟩, he.symm⟩
  obtain ⟨z, hz, hze⟩ := hex
  have e : J *ᵥ ((I.A.fam.R t).Pq (I.A.fam.lvl P ψ) (I.X.Z t) *ᵥ f) = z := toRg_inj hH t (by rw [hJ, hze])
  rw [e]
  exact hz

theorem avg_g (hρ : I.PRho) (t : T) (P : Subgroup G) (ψ : P →* Kˣ)
    (J : Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((I.A.fam.R t).dZ (I.A.fam.lvl P ψ) (I.X.Z t))) K)
    (hJ : ∀ x, I.cg.toR I.X.zs false t (J *ᵥ x) = (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) x) :
    ∀ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      ∃ z ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
        (Nat.card P : K) • (I.epM P ψ *ᵥ (I.X.rowMat I.cg false t *ᵥ y)) = I.X.rowMat I.cg false t *ᵥ (J *ᵥ z) := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hy
  let _ : Fintype P := Fintype.ofFinite P
  obtain ⟨fb, hfb, he⟩ := Sand.avg_toF (B := I.A.fam.R t) (hv0 := hH.ok.ok2.conj) (hOk := hH.ok.ok2.what₂ t)
    (hX := hH.ok.ok2.irr) (Z := I.X.Z t) (hZ := hZ_of hH t) (P := P) (ψ := ψ) f hf
  have hex : ∃ z ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
      ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • (I.A.fam.R t).r (k : G)
        (I.cg.toR I.X.zs false t ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f)) =
        (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) z :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨fb, hfb, rfl⟩, he⟩
  obtain ⟨z, hz, hze⟩ := hex
  refine ⟨z, hz, ?_⟩
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hep : I.epM P ψ = (Nat.card P : K)⁻¹ • ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G) := rfl
  apply inj_g hH
  rw [key_g hH, hJ, ← hze, hep, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  erw [Sand.cpt_sum_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  erw [map_smul, (hρ s hH).2.2 (k : G) (I.X.rowMat I.cg false t *ᵥ ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f)),
    key_g hH t ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f), LinearMap.map_smulₛₗ, map_smul]
  exact congrArg _ (hH.gequiv t k _).symm

theorem sub_b (hJt : I.PJt) (b : Bool) (t : T) :
    ∀ y ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ t,
      I.Jt b t *ᵥ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t := by
  cases b
  · exact sub_g hH t I.P0 I.ψ0 (I.Jt false t) (fun x => (hJt s hH false t).2.1 x)
  · exact sub_g hH t I.P1 I.ψ1 (I.Jt true t) (fun x => (hJt s hH true t).2.1 x)

theorem avg_b (hJt : I.PJt) (hρ : I.PRho) (b : Bool) (t : T) :
    ∀ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      ∃ z ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ t,
        (Nat.card (I.lvP b) : K) • (I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false t *ᵥ y)) =
          I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ z) := by
  cases b
  · exact avg_g hH hρ t I.P0 I.ψ0 (I.Jt false t) (fun x => (hJt s hH false t).2.1 x)
  · exact avg_g hH hρ t I.P1 I.ψ1 (I.Jt true t) (fun x => (hJt s hH true t).2.1 x)

end Prin

theorem pLat_of (_hJt : I.PJt) : I.PLat := by
  intro s hH
  have : Finite T := hH.ok.ok2.tup_fin
  exact Sand.glue_lattice I.A3.fam3.base3.μ0 I.X.μ
    (fun t => matLat (I.X.rowMat I.cg false t) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t))
    (fun t => GluingInclusion.matLat_lattice' _ (rowG_surj hH t) _
      (show Submodule.IsLattice K ((I.A.fam.R t).abelian₂ (Lvl.full I.A.fam.X) (I.X.Z t)) from
        BlockDat.Lam_lat hH.ok.ok2.conj (hH.ok.ok2.what₂ t) hH.ok.ok2.irr))

theorem pGLat_of (_hJt : I.PJt) (hρ : I.PRho) : I.PGLat := by
  intro s hH g x hx
  rw [mem_RRg] at hx ⊢
  intro w
  obtain ⟨c, hc, z, hz, hzx⟩ := hx w
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hz
  obtain ⟨f', hf', he⟩ := Sand.act_toF (B := I.A.fam.R (I.X.μ w)) (hv0 := hH.ok.ok2.conj) (hOk := hH.ok.ok2.what₂ _)
    (hX := hH.ok.ok2.irr) (Z := I.X.Z (I.X.μ w)) (hZ := hZ_of hH _) g f hf
  have hex : ∃ z ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ (I.X.μ w),
      (I.A.fam.R (I.X.μ w)).r g (I.cg.toR I.X.zs false (I.X.μ w)
        ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f)) =
        I.cg.toR I.X.zs false (I.X.μ w) z :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨f', hf', rfl⟩, he⟩
  obtain ⟨z', hz', hze⟩ := hex
  refine ⟨c, hc, z', hz', ?_⟩
  rw [← exponent_index_lattice.mulVec_osmul, ← hzx]
  apply inj_g hH
  erw [key_g hH, (hρ s hH).2.2 g (I.X.rowMat I.cg false (I.X.μ w) *ᵥ ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f)),
    key_g hH (I.X.μ w) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f), ← hze]
  exact hH.gequiv _ g _

theorem pSand_of (hJt : I.PJt) (hJ : I.PJ) (hρ : I.PRho) (hR : I.PRange) : I.PSand := by
  intro s hH b
  refine ⟨fun x hx => ?_, fun y hy hyr => ?_⟩
  · rw [mem_RRb] at hx
    rw [mem_RRg]
    intro w
    obtain ⟨c, hc, z, hz, hzx⟩ := hx w
    refine ⟨c, hc, I.Jt b (I.X.μ w) *ᵥ z, sub_b hH hJt b _ z hz, ?_⟩
    exact ((hJt s hH b _).2.2 z).symm.trans
      ((congrArg (fun v => I.Jm b *ᵥ v) hzx).trans (exponent_index_lattice.mulVec_osmul _ _ _))
  · obtain ⟨z0, hz0⟩ := LinearMap.mem_range.mp hyr
    have hyr' := hyr
    rw [← hR s hH b] at hyr'
    obtain ⟨x0, hx0⟩ := LinearMap.mem_range.mp hyr'
    rw [Matrix.mulVecLin_apply] at hz0 hx0
    have hidem : I.epM (I.lvP b) (I.lvψ b) *ᵥ y = y := by
      rw [← hz0, Matrix.mulVec_mulVec, epM_idem hH hρ]
    refine ⟨((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • x0, ?_, by rw [exponent_index_lattice.mulVec_osmul, hx0]⟩
    rw [mem_RRg] at hy
    rw [mem_RRb]
    intro w
    obtain ⟨c, hc, z, hz, hzy⟩ := hy w
    obtain ⟨zb, hzb, he⟩ := avg_b hH hJt hρ b (I.X.μ w) z hz
    refine ⟨c, hc, zb, hzb, ?_⟩
    apply (hJ s hH b).2
    have h3 : (Nat.card (I.lvP b) : K) •
        (I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false (I.X.μ w) *ᵥ z)) =
        I.Jm b *ᵥ (c • (((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • x0)) := by
      have h4 : I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false (I.X.μ w) *ᵥ z) = c • y :=
        (congrArg (fun v => I.epM (I.lvP b) (I.lvψ b) *ᵥ v) hzy).trans (by rw [exponent_index_lattice.mulVec_osmul, hidem])
      rw [h4]
      simp only [exponent_index_lattice.mulVec_osmul]
      rw [hx0, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K), smul_comm]
    exact ((hJt s hH b _).2.2 zb).trans (he.symm.trans h3)

end In3

end Formalism.IndefR.CxPass
end
end

