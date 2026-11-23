module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ParabolicLowerBlockZero

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CoreX
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem coreX : CoreX := by
  intro ok vac c hT hA hS hU hW hD F E _ _ _ _ _ σ d R hok hE Φ hΦ P gf hpg hv x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨dd, J, T', bs, ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c', C, hDat, hAn, ⟨e, he⟩, hC, ⟨t, ht⟩,
    μH, 𝓕, hH, hF, horb⟩ := hD hT hA F E σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t', ht'⟩ := hU F E σ d (s0 d.m d.n) (d.sec0 Φ) (hS F E σ d Φ hΦ) (hE Φ hΦ)
  have hG := hW F E σ d.m d.n dd J T' bs ψ (InfinitePlace F) θ l εs fr g P lv L₁ L₂ Φg Φf Φv μ ν hDat hok
    (Or.inr hAn) (fun h => ⟨fun i => congrFun (hv h) i, e, he⟩)
    ⟨max t t', fun z hz => (ht z (lt_of_le_of_lt (le_max_left _ _) hz)).1
      ((ht' z (lt_of_le_of_lt (le_max_right _ _) hz) nb lam 𝓖 hcd ε w hw x).1)⟩ μH 𝓕 hH hF
  rw [horb, mul_left_comm]
  exact ((holValueAt_const_mul_cpow c' hC (s0 d.m d.n)).mul hG).congr ⟨t, fun z hz => ((ht z hz).2).symm⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.ExistsRationalMatrixUnipotent
section
noncomputable section

open scoped TensorProduct NNReal Matrix ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem rel_algebraMap_injective : Function.Injective (algebraMap F (AF F)) := by
  intro x y h
  have := congrArg Prod.fst h
  exact (algebraMap F (NumberField.InfiniteAdeleRing F)).injective this

theorem rel_inclR_injective : Function.Injective (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective rel_algebraMap_injective

theorem rel_incM_injective {a b : Type} : Function.Injective (incM F (E := E) (m := a) (n := b)) := by
  intro X Y h
  ext i j
  exact rel_inclR_injective (congrFun (congrFun h i) j)

theorem rel_sigR_eq_cA (z : AE F E) : HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z = cA σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [HeckeCharacterZeroLocus.SiegelWeilU.sigR, cA, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem rel_definite {m r s : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (h : HasSig M r s) (h0 : min r s = 0)
    (z : Fin m → ℂ) (hz : z ≠ 0) : z ⬝ᵥ M *ᵥ star z ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  set S : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hS
  have hSS : S * S = 1 := by
    simp [S, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hSu : IsUnit S := ⟨⟨S, S, hSS, hSS⟩, rfl⟩
  have hrank : A.rank = m := by
    apply le_antisymm ((Matrix.rank_le_card_height A).trans (by simp))
    have h1 : S.rank = r + s := by
      rw [Matrix.rank_of_isUnit S hSu]
      simp
    have h2 : S.rank ≤ Aᵀ.rank := by
      rw [← hA]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_left _ _)
    rw [Matrix.rank_transpose] at h2
    omega
  have hsurj : ∃ w, A *ᵥ w = z := by
    have : LinearMap.range A.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank, hrank]
      simp
    exact LinearMap.range_eq_top.mp this z
  obtain ⟨w, rfl⟩ := hsurj
  have hw : w ≠ 0 := by
    rintro rfl
    simp at hz
  have hst : star (A *ᵥ w) = A.map star *ᵥ star w := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : (A *ᵥ w) ⬝ᵥ M *ᵥ star (A *ᵥ w) = w ⬝ᵥ S *ᵥ star w := by
    rw [hst, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
      ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hA]
  rw [key]
  have hne : w ⬝ᵥ star w ≠ 0 := by
    rw [dotProduct_comm]
    exact fun h => hw (dotProduct_star_self_eq_zero.mp h)
  rcases Nat.min_eq_zero_iff.mp h0 with hr | hs
  · subst hr
    have : S *ᵥ star w = -star w := by
      ext k
      rcases k with i | j
      · exact i.elim0
      · simp [S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
    rw [this, dotProduct_neg]
    exact neg_ne_zero.mpr hne
  · subst hs
    have : S *ᵥ star w = star w := by
      ext k
      rcases k with i | j
      · simp [S, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type, Matrix.one_apply]
      · exact j.elim0
    rw [this]
    exact hne

theorem rel_aniso (d : SD σ) (η : E) (hη : η ≠ 0) (y : Fin d.m → E)
    (hy : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = 0) : y = 0 := by
  by_contra hy0
  let w : InfinitePlace F := Classical.arbitrary _
  let τ : E →+* ℂ := (d.B.emb w).1
  have hτ : ∀ x, τ (σ x) = star (τ x) := d.ok.good.cm.2.2.2 τ
  let z : Fin d.m → ℂ := fun i => τ (y i)
  have hz : z ≠ 0 := by
    intro h
    apply hy0
    funext i
    apply τ.injective
    simpa [z] using congrFun h i
  have key : τ (HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y) = τ η * (z ⬝ᵥ (d.A.J.map τ) *ᵥ star z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Jd, Matrix.mulVec, dotProduct, map_sum, map_mul,
      Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, Finset.mul_sum, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [z]
    rw [show ((σ : E →+* E) (y j)) = σ (y j) from rfl, hτ]
    ring
  rw [hy, map_zero] at key
  have hQ : z ⬝ᵥ (d.A.J.map τ) *ᵥ star z ≠ 0 := by
    rcases d.ok.sign with ⟨hA, -⟩ | ⟨hA, -⟩
    · exact rel_definite _ (hA.sig w) d.ok.aniso z hz
    · have h1 := rel_definite _ (hA.sig w) d.ok.aniso z hz
      intro h0
      apply h1
      simp only [Matrix.smul_mulVec, dotProduct_smul]
      change Complex.I • (z ⬝ᵥ d.A.J.map τ *ᵥ star z) = 0
      rw [h0, smul_zero]
  have hτη : τ η ≠ 0 := (map_ne_zero τ).mpr hη
  exact (mul_ne_zero hτη hQ) key.symm

theorem exists_rational_matrix_unipotent (d : SD σ) (T : nF σ d.Y d.b) : ∃ T₀ : Matrix (Fin d.n) (Fin d.n) E, T.1.1 = incM F T₀ := by
  obtain ⟨T, hT⟩ := T
  induction hT using AddSubgroup.closure_induction with
  | mem x hx => exact hx
  | zero => exact ⟨0, by ext i j; simp [incM]⟩
  | add x y _ _ hx hy =>
    obtain ⟨X, hX⟩ := hx
    obtain ⟨Y, hY⟩ := hy
    refine ⟨X + Y, ?_⟩
    change x.1 + y.1 = _
    rw [hX, hY]
    ext i j
    simp [incM]
  | neg x _ hx =>
    obtain ⟨X, hX⟩ := hx
    refine ⟨-X, ?_⟩
    change -x.1 = _
    rw [hX]
    ext i j
    simp [incM]

def relH (d : SD σ) (η : E) (β : nA σ d.Y d.b) : Matrix (Fin d.n) (Fin d.n) (AE F E) :=
  -(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹ • β.1ᵀ)

theorem relH_mem (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (β : nA σ d.Y d.b) :
    relH d η β ∈ HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n := by
  intro a b
  have hn := congrFun (congrFun (rel_nA_cond d ε hε β) a) b
  simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    Matrix.zero_apply] at hn
  have he2 : ((ε : ℤ) : E) * ((ε : ℤ) : E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have hinv : σ η⁻¹ = -(((ε : ℤ) : E) * η⁻¹) := by
    rw [map_inv₀, hση, inv_neg, mul_inv, inv_eq_of_mul_eq_one_right he2]
  have hc : ∀ x : E, cA σ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (σ x) := by
    intro x
    simp [cA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]
  simp only [relH, Matrix.neg_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [map_neg, map_mul, rel_sigR_eq_cA, rel_sigR_eq_cA, hc, hinv, map_neg, map_mul, map_intCast]
  linear_combination (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹) * hn

theorem relH_eq (d : SD σ) (η : E) (hη : η ≠ 0) (β : nA σ d.Y d.b) :
    β.1 = -(incM F (Matrix.scalar (Fin d.n) η) * (relH d η β)ᵀ) := by
  have h1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) η⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hη, map_one]
  ext i j
  simp [relH, incM, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, ← mul_assoc, h1]
  rw [mul_comm (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (AF F) η⁻¹), h1, one_mul]

theorem rel_Td (d : SD σ) (ε : ℤˣ)
    (hε : d.b.1ᵀ * dbl d.Y.J * d.b.1.map σ = Matrix.fromBlocks 0 1 (((ε : ℤ) : E) • 1) 0) (η : E) (hη : η ≠ 0)
    (hση : σ η = -(((ε : ℤ) : E) * η)) (T : nF σ d.Y d.b) (hT : IsND T) (T₀ : Matrix (Fin d.n) (Fin d.n) E)
    (h0 : T.1.1 = incM F T₀) : (∀ a b, σ (Td η T₀ b a) = Td η T₀ a b) ∧ (Td η T₀).det ≠ 0 := by
  have hn := rel_nA_cond d ε hε T.1
  rw [h0, rel_cA_incM] at hn
  have hn' : incM F (T₀ᵀ + ((ε : ℤ) : E) • T₀.map σ) = incM F 0 := by
    have e0 : incM F (0 : Matrix (Fin d.n) (Fin d.n) E) = 0 := by
      ext i j
      simp [incM]
    rw [e0, ← hn]
    ext i j
    simp [incM]
  have hz := rel_incM_injective hn'
  refine ⟨fun a b => ?_, ?_⟩
  · have he := congrFun (congrFun hz a) b
    simp only [Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at he
    simp only [Td, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    rw [map_mul, map_mul, map_neg, map_ofNat, hση]
    linear_combination (2 * η) * he
  · have hdet : T₀.det ≠ 0 := by
      intro h
      apply hT
      show (T.1.1).det = 0
      rw [h0, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
    simp only [Td, Matrix.det_transpose, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr two_ne_zero) hη)) hdet

theorem relAlg_pf : RelAlg := by
  intro F E _ _ _ _ _ σ d
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨η, hη, hση, hherm⟩ := rel_eta d ε hε
  refine ⟨η, fun β => ⟨relH d η β, relH_mem d ε hε η hη hση β⟩, hη, hherm, fun β => relH_eq d η hη β,
    fun y hy => rel_aniso d η hη y hy, d.ok.good.cm, ⟨fun i j => ?_, ?_⟩, fun T hT => ?_⟩
  · simp only [Jd, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
    exact hherm j i
  · intro h0
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hy0
    apply rel_aniso d η hη y
    have h2 : HeckeCharacterZeroLocus.SiegelWeilU.hE σ (Jd d η) y y = ∑ i, σ (y i) * (Jd d η *ᵥ y) i := by
      simp only [HeckeCharacterZeroLocus.SiegelWeilU.hE, HeckeCharacterZeroLocus.SiegelWeilU.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rfl
    rw [h2, hy]
    simp
  · obtain ⟨T₀, h0⟩ := exists_rational_matrix_unipotent d T
    exact ⟨T₀, h0, rel_Td d ε hε η hη hση T hT T₀ h0⟩

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IwaRedOfC
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

theorem kFinK : KFinK := fun _ _ _ _ _ _ _ _ d Φ hΦ k hk => kfin_om d hΦ hk

theorem iwaRedC : IwaRedC := by
  intro hT c F E _ _ _ _ _ σ d Q hQs hQK hL Φ hΦ x nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨p, t, hp, k, hk, rfl⟩ := d.ok.hgt.iwa x
  obtain ⟨n0, m0, β₀, hn, hm, rfl⟩ := par_decomp d p t hp
  have key := hL (d.om k Φ) (hQK Φ hΦ k hk) m0 hm nb lam 𝓖 hcd ε w hw T hTnd
  have e1 : (fun z => ∫ β, flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * (n0 * m0 * k)) *
      d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam) = fun z => d.B.ψ (d.tt (T.1.1 * β₀)) *
      ∫ β, flat d.a (d.sec0 (d.om k Φ)) (s0 d.m d.n) z (w * nb β * m0) * d.B.ψ (-d.tt (T.1.1 * β.1)) ∂lam := by
    funext z
    rw [← int_n d nb lam 𝓖 hcd T w n0 m0 β₀ hn]
    congr 1
    funext β
    rw [show w * nb β * (n0 * m0 * k) = (w * nb β * (n0 * m0)) * k by simp only [mul_assoc]]
    simp only [flat, a_mul_K d _ k hk, section_mul_weil_action]
  have e2 : d.orb T (d.om (n0 * m0 * k) Φ) = d.B.ψ (d.tt (T.1.1 * β₀)) * d.orb T (d.om m0 (d.om k Φ)) := by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
    exact orb_n hT d T (om_mem_sch d _ (om_mem_sch d _ (hQs Φ hΦ))) n0 β₀ hn
  show HolValueAt _ _ _
  rw [e1, e2, mul_left_comm]
  exact holValueAt_const_mul _ key

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.VacIsPureBy
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def vac_gen {d : SD σ} (R : RD d) : Set (Mx F E d.m d.n → ℂ) :=
  {f | ∃ φ, Dense.Good φ ∧ f = genF R (fun _ => 1) (Dense.pf φ)}

theorem vac_gen_sub {d : SD σ} (R : RD d) : vac_gen R ⊆ R.vac := by
  rintro _ ⟨φ, hφ, rfl⟩
  exact Submodule.subset_span ⟨Dense.pf φ, Dense.pf_mem hφ, rfl⟩

theorem vac_le_span {d : SD σ} (R : RD d) : R.vac ≤ Submodule.span ℂ (vac_gen R) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  have := Dense.mem_span_pf hg
  clear hg
  have key : genL R (fun _ => 1) g ∈ Submodule.span ℂ (vac_gen R) := by
    induction this using Submodule.span_induction with
    | mem x hx => obtain ⟨φ, hφ, rfl⟩ := hx; exact Submodule.subset_span ⟨φ, hφ, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  exact key

theorem vac_isPureBy {d : SD σ} (R : RD d)
    (φ : ∀ u : HeightOneSpectrum (𝓞 F), (Fin d.m × Fin d.n × Fin 2 → Fv F u) → ℂ) (hφ : Dense.Good φ) (Φ : d.Fn)
    (h : d.T Φ = genF R (fun _ => 1) (Dense.pf φ)) : ∃ gf, IsPureBy R Φ (fun _ => 1) gf := by
  refine ⟨φ, fun v => hφ.1 v, hφ.2.mono fun v hv => hv, ?_⟩
  rw [h]
  rfl

theorem vacSpan : VacSpan := by
  intro hT hF hPK hVK F E _ _ _ _ _ σ d R Φ hΦ hTΦ
  have hB := hT.1 F E σ d
  have hvf : R.vac ≤ R.fock := (hVK F E σ d R).2.1
  have h1 : d.T Φ ∈ Submodule.span ℂ (vac_gen R) := vac_le_span R hTΦ
  obtain ⟨k, c, gs, hsum⟩ := Submodule.mem_span_set'.1 h1
  have hpre : ∀ i : Fin k, ∃ Ψ ∈ d.sch, d.T Ψ = (gs i : Mx F E d.m d.n → ℂ) := fun i =>
    hB.2.1 _ ((hF F E σ d R).1 (hvf (vac_gen_sub R (gs i).2)))
  choose Φs hΦs hTs using hpre
  refine ⟨k, c, Φs, fun i => ⟨hPK F E σ d R (Φs i) (hΦs i) (hTs i ▸ hvf (vac_gen_sub R (gs i).2)),
    hTs i ▸ vac_gen_sub R (gs i).2, ?_⟩, ?_⟩
  · obtain ⟨φ, hφ, e⟩ := (gs i).2
    exact vac_isPureBy R φ hφ (Φs i) ((hTs i).trans e)
  · have hmem : Φ - ∑ i, c i • Φs i ∈ d.sch :=
      sub_mem hΦ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hΦs i))
    have h0 : d.T (Φ - ∑ i, c i • Φs i) = 0 := by
      rw [T_sub, T_sum, ← hsum]
      simp only [hTs, sub_self]
    exact (sub_eq_zero.1 (hB.2.2 _ hmem h0))

end PositivityTheory.SiegelWeilFormula.KWhit

end
end

