module

public import Mathlib
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalRingCardinality.DataForms
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitPosMeanOfPositivePart
section
noncomputable section

namespace GlobalTheory.Theta0MeanCompare

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

theorem bound_eq (D : D7) : SignedLogMeans.bound D = AbsoluteLogMeanBounds.kronBound D := rfl

theorem one_le_d (D : D7) : (1 : ℝ) ≤ D.host.d := by
  have h := D.host.qd_big.2
  exact_mod_cast (by omega : 1 ≤ D.host.d)

theorem two_sqrt_le_rd (D : D7) : 2 * Real.sqrt D.host.d ≤ D.host.rdE := by
  refine le_trans ?_ (factRd D.R D.host).1
  have he : (2 : ℝ) ≤ D.R.e := by exact_mod_cast D.host.two_le_e
  have h1 : (2 : ℝ) ^ (-(D.R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) := by
    calc (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)

theorem one_le_sqrt_d (D : D7) : 1 ≤ Real.sqrt D.host.d := Real.one_le_sqrt.mpr (one_le_d D)

theorem kronBound_le (D : D7) {L : ℝ} (h : Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * L) :
    AbsoluteLogMeanBounds.kronBound D ≤ L := by
  have h1 := two_sqrt_le_rd D
  have h2 := one_le_sqrt_d D
  have h3 : Real.log (Real.sqrt D.host.d) ≤ Real.log D.host.rdE :=
    Real.log_le_log (by linarith) (by linarith)
  have h4 := Real.one_half_lt_eulerMascheroniConstant
  have h5 := le_abs_self (logDerivativeAtOne D)
  unfold AbsoluteLogMeanBounds.kronBound
  linarith

end GlobalTheory.Theta0MeanCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InfPowConjDiagUnits
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem infPow_infDiag {E : Type} [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ) :
    infPow n (infDiag k) = infPow n (diagUnits E k) := by
  have h : ((infDiag k : Ideles E) : AdeleRing (𝓞 E) E).1 = ((diagUnits E k : Ideles E) : AdeleRing (𝓞 E) E).1 := by
    rw [infDiag_eq]
    rfl
  simp only [infPow, h]

end GlobalTheory.HeckeGal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegersMemInverseHalfDifferent
section
open NumberField

namespace GlobalTheory.InverseHalfDifferent

theorem exists_single_mem_span {E M ι : Type} [Field E] [NumberField E] [Field M] [NumberField M]
    [Finite ι] [DecidableEq ι] (f : ι → E →+* M) (hf : Function.Injective f) (i : ι) :
    ∃ s : M, s ≠ 0 ∧ (Pi.single i s : ι → M) ∈
      Submodule.span (𝓞 M) (Set.range fun a : 𝓞 E => fun j => f j (a : E)) := by
  classical
  cases nonempty_fintype ι

  let χ : ι → (𝓞 E →* M) := fun j => ((f j).comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro j k h
    apply hf
    apply IsFractionRing.ringHom_ext (A := 𝓞 E)
    intro x
    exact DFunLike.congr_fun h x
  have hli : LinearIndependent M (fun j => (χ j : 𝓞 E → M)) :=
    (linearIndependent_monoidHom (𝓞 E) M).comp χ hχ

  have htop : Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    apply hφ0
    have hc : ∀ j, φ (fun k => if j = k then 1 else 0) = 0 := by
      have key : ∑ j, φ (fun k => if j = k then 1 else 0) • (χ j : 𝓞 E → M) = 0 := by
        funext a
        have ha : φ (fun j => f j (a : E)) = 0 := hφ (Submodule.subset_span ⟨a, rfl⟩)
        rw [LinearMap.pi_apply_eq_sum_univ] at ha
        simpa [χ, Finset.sum_apply, mul_comm] using ha
      exact Fintype.linearIndependent_iff.mp hli _ key
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [hc]

  have h1 : (Pi.single i 1 : ι → M) ∈ Submodule.span M (Set.range fun a : 𝓞 E => fun j => f j (a : E)) := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 M))).mp h1
  refine ⟨algebraMap (𝓞 M) M z, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2, ?_⟩
  have hy' : y = algebraMap (𝓞 M) M z • (Pi.single i 1 : ι → M) := by
    rw [hz, smul_smul, IsLocalization.mk'_spec', map_one, one_smul]
  have : (Pi.single i (algebraMap (𝓞 M) M z) : ι → M) = y := by
    rw [hy']
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [this]
  exact hy

open Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem integers_mem_inverse_half_different {R : Ranks} (H : Host R) (a : 𝓞 H.E) :
    (a : H.E) ∈ (H.AA0 : Submodule (𝓞 H.E) H.E) := by

  have hb : H.𝔟 ≠ ⊥ := by
    intro h
    have h2 := H.𝔟_spec.2
    simp [h] at h2
  have hle : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hne : (H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb

  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≤ H.AA0 := by
    have := FractionalIdeal.inv_anti_mono hne hle
    simpa [Host.AA0] using this
  exact h1 ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩)

theorem emb_injective {R : Ranks} (H : Host R) : Function.Injective H.emb := by
  intro g g' h
  have hσ : H.sigmaOf g = H.sigmaOf g' := by
    ext x
    have hx := DFunLike.congr_fun h x
    simp only [Host.emb, RingHom.comp_apply] at hx
    exact H.φ₀.injective hx
  exact H.gal.symm.injective hσ

theorem embT_injective (D : D7) : Function.Injective (embT D) := by
  intro τ τ' h
  exact D.eTau.injective (Subtype.ext (emb_injective D.host h))

theorem ellT_ne_bot {D : D7} {M : IntermediateField ℚ ℂ} [NumberField M]
    (hM : ∀ (τ : D.what₂.Tau) (x : D.host.E), (embT D τ : D.host.E → ℂ) x ∈ M)
    (τ : D.what₂.Tau) : ellT D M τ ≠ ⊥ := by
  classical

  let f : D.what₂.Tau → D.host.E →+* M := fun σ => (embT D σ).codRestrict M (hM σ)
  have hf : Function.Injective f := by
    intro σ σ' h
    apply embT_injective D
    ext x
    exact congrArg Subtype.val (DFunLike.congr_fun h x)
  obtain ⟨s, hs0, hs⟩ := exists_single_mem_span f hf τ

  have hle : Submodule.span (𝓞 M) (Set.range fun a : 𝓞 D.host.E => fun j => f j (a : D.host.E)) ≤ mmM D M := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine Submodule.subset_span ⟨(a : D.host.E), integers_mem_inverse_half_different D.host a, ?_⟩
    funext j
    unfold Formalism.MainNotions.TaylorLogMetric.liftM
    rw [dite_eq_left (hM j _)]
    rfl
  intro h
  have hs' : s ∈ ellT D M τ := by
    rw [ellT, Submodule.mem_comap]
    simpa using hle hs
  rw [h, Submodule.mem_bot] at hs'
  exact hs0 hs'

end GlobalTheory.InverseHalfDifferent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeNormalFormCoordinates
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.lattice_normal_form_coordinates

open GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect

variable {F : Type} [Field F] {n c : ℕ}

theorem eN_eq_zero {N i : ℕ} (h : N ≤ i) : Loc.eN F N i = 0 := by
  funext l
  unfold Loc.eN
  have := l.2
  rw [if_neg (by omega)]
  rfl

theorem sum_eN_apply (g : Fin c → F) (l : Fin (n + c)) :
    (∑ i : Fin c, g i • Loc.eN F (n + c) (n + i.1)) l = if h : l.1 < n then 0 else g ⟨l.1 - n, by omega⟩ := by
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Loc.eN, smul_eq_mul]
  split_ifs with h
  · exact Finset.sum_eq_zero fun i _ => by rw [if_neg (by omega), mul_zero]
  · rw [Finset.sum_eq_single ⟨l.1 - n, by omega⟩]
    · rw [if_pos (by simp; omega), mul_one]
    · intro b _ hb
      rw [if_neg, mul_zero]
      intro hl
      exact hb (Fin.ext (by simp; omega))
    · simp

theorem decomp (v : Fin (n + c) → F) :
    v = Loc.inX F n c (fun a => v (Fin.castAdd c a)) +
      ∑ i : Fin c, v (Fin.natAdd n i) • Loc.eN F (n + c) (n + i.1) := by
  funext l
  rw [Pi.add_apply, inX_apply, sum_eN_apply]
  split_ifs with h
  · rw [add_zero]
    rfl
  · rw [zero_add]
    congr 1
    exact Fin.ext (by simp; omega)

theorem isFrame : IsFrame (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    have := congrFun hg (Fin.natAdd n i)
    rw [sum_eN_apply, dite_eq_right (by simp)] at this
    simpa using this
  · rw [Submodule.disjoint_def]
    rintro _ ⟨x, rfl⟩ hv
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hv
    funext l
    have h1 := congrFun hg l
    rw [sum_eN_apply] at h1
    by_cases h : l.1 < n
    · rw [dite_eq_left h] at h1
      exact h1.symm
    · rw [inX_apply, dite_eq_right h]
      rfl
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [decomp v]
    exact Submodule.add_mem_sup ⟨_, rfl⟩
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

theorem flag_le (i : Fin c) :
    flag (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) i ≤ Loc.Ufl F n c i.1 := by
  refine sup_le ?_ (Submodule.span_le.2 ?_)
  · rintro _ ⟨x, rfl⟩
    exact inX_mem_Ufl _ x
  · rintro _ ⟨l, hl, rfl⟩
    have : l.1 < i.1 := hl
    exact eN_mem_Ufl (by omega)

theorem R1cond_of {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (h1 : ∀ x, r (Loc.inX F n c x) ∈ Loc.Ufl F n c 0)
    (h2 : ∀ i : Fin c, i.1 = 0 → r (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1))
    (h3 : ∀ i : Fin c, r (Loc.eN F (n + c) (n + i.1)) - Loc.eN F (n + c) (n + i.1) ∈ Loc.Ufl F n c i.1) :
    Loc.R1cond F n c r := by
  refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
  · rw [decomp v, map_add (f := _), map_sum]
    refine add_mem (Ufl_mono (Nat.zero_le i) (h1 _)) (Submodule.sum_mem _ fun j _ => ?_)
    by_cases hj : j.1 < i
    · rw [map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := add_mem (Ufl_mono hj.le (h3 j)) (eN_mem_Ufl (F := F) (n := n) (c := c) (i := i) (s := n + j.1) (by omega))
      rwa [sub_add_cancel] at this
    · rw [mem_Ufl.1 hv (Fin.natAdd n j) (by simp; omega), zero_smul, map_zero]
      exact zero_mem _
  · rcases Nat.eq_zero_or_pos c with hc | hc
    · rw [eN_eq_zero (by omega), map_zero]
    · exact h2 ⟨0, hc⟩ rfl
  · by_cases hi : i < c
    · exact h3 ⟨i, hi⟩
    · rw [eN_eq_zero (by omega), map_zero, sub_zero]
      exact zero_mem _

theorem R1cond_inv {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)} (hr : Loc.R1cond F n c r) :
    Loc.R1cond F n c r⁻¹ := by
  have key : ∀ i, ∀ v ∈ Loc.Ufl F n c i, r⁻¹ v ∈ Loc.Ufl F n c i := by
    intro i v hv
    have hle : (Loc.Ufl F n c i).map r.toLinearMap ≤ Loc.Ufl F n c i := by
      rintro _ ⟨w, hw, rfl⟩
      exact hr.1 i w hw
    have heq := Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
    rw [← heq] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have : r⁻¹ (r.toLinearMap w) = w := r.symm_apply_apply w
    rwa [this]
  refine ⟨key, ?_, fun i => ?_⟩
  · show r.symm _ = _
    rw [LinearEquiv.symm_apply_eq, hr.2.1]
  · have h := neg_mem (key i _ (hr.2.2 i))
    have e : r⁻¹ (r (Loc.eN F (n + c) (n + i))) = Loc.eN F (n + c) (n + i) := r.symm_apply_apply _
    rwa [map_sub, e, neg_sub] at h

theorem mem_unipotentRadical_of_isSemidirect {r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hr : IsSemidirect (LinearMap.range (Loc.inX F n c)) (fun i : Fin c => Loc.eN F (n + c) (n + i.1)) r) :
    r ∈ Loc.R1 F n c := by
  obtain ⟨γ, g, u, hg, hu, rfl⟩ := hr
  have h1 : Loc.R1cond F n c g := by
    refine R1cond_of (fun x => ?_) (fun i _ => hg.2 i) (fun i => ?_)
    · have := hg.1 ⟨Loc.inX F n c x, x, rfl⟩
      obtain ⟨y, hy⟩ := (γ ⟨Loc.inX F n c x, x, rfl⟩).2
      rw [show g (Loc.inX F n c x) = Loc.inX F n c y from this.trans hy.symm]
      exact inX_mem_Ufl 0 y
    · rw [show g (Loc.eN F (n + c) (n + i.1)) = Loc.eN F (n + c) (n + i.1) from hg.2 i, sub_self]
      exact zero_mem _
  have h2 : Loc.R1cond F n c u := by
    refine R1cond_of (fun x => ?_) hu.2.1 (fun i => flag_le i (hu.2.2 i))
    rw [hu.1 _ ⟨x, rfl⟩]
    exact inX_mem_Ufl 0 x
  exact ⟨h1.mul h2, R1cond_inv (h1.mul h2)⟩

theorem isLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type} [AddCommGroup V] [Module F V] [Module O V]
    [IsScalarTower O F V] [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W] (φ : V ≃ₗ[F] W)
    (L : Submodule O V) (hL : Submodule.IsLattice F L) :
    Submodule.IsLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  refine ⟨hL.fg.map _, ?_⟩
  have h : ((L.map (φ.toLinearMap.restrictScalars O) : Submodule O W) : Set W) = φ.toLinearMap '' (L : Set V) := rfl
  intro s hs hli
  have hs' : φ.symm '' s ⊆ (L : Set V) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, rfl⟩ := h ▸ hs hy
    simpa using hz
  have hi : LinearIndepOn O id (φ.symm '' s) := by
    apply (linearIndepOn_id_imageₛ_iff (f := φ.symm.toLinearMap.restrictScalars O) φ.symm.injective.injOn).2
    exact hli
  have hf := hL.linearIndepOn (φ.symm '' s) hs' hi
  have hm := (linearIndepOn_id_imageₛ_iff (f := φ.toLinearMap) φ.injective.injOn).2 hf
  simpa [Set.image_image, Function.comp_def] using hm

theorem isFullLattice_map {O : Type} [CommRing O] [Algebra O F] {V W : Type}
    [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]
    [AddCommGroup W] [Module F W] [Module O W] [IsScalarTower O F W]
    (φ : V ≃ₗ[F] W) (L : Submodule O V) (hL : Submodule.IsFullLattice F L) :
    Submodule.IsFullLattice F (L.map (φ.toLinearMap.restrictScalars O)) := by
  haveI := isLattice_map φ L hL.toIsLattice
  refine { span_eq_top := ?_ }
  change Submodule.span F (φ.toLinearMap '' (L : Set V)) = ⊤
  rw [← Submodule.map_span φ.toLinearMap, hL.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem latticeNormalFormCoord_of : GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalForm → GlobalTheory.IndefiniteRowSideFullHecke.FlagUnipotentSemidirect.LatticeNormalFormCoord := by
  intro H O F _ _ _ _ _ _ q hq n c L hL Λ hΛ
  let φ := LinearEquiv.ofInjective (Loc.inX F n c) inX_injective
  obtain ⟨r, e, z, hr, ⟨z', rfl⟩, h⟩ := H O F (Fin (n + c) → F) q hq c _ _ isFrame _ (by
    first | exact isFullLattice_map φ L hL | exact isLattice_map φ L hL) Λ hΛ
  refine ⟨r, mem_unipotentRadical_of_isSemidirect hr, e, z', ?_⟩
  rw [h]
  congr 1
  unfold inY
  rw [← Submodule.map_comp]
  rfl

end GlobalTheory.Proof.lattice_normal_form_coordinates
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelEqParahoricCategory
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.level_eq_parahoric_category

theorem conj_res {k : Type} [CommRing k] {n c : ℕ} {ρ r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    {γ g : (Fin n → k) ≃ₗ[k] (Fin n → k)} (hγ : ∀ x, ρ (Loc.inX k n c x) = Loc.inX k n c (γ x))
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (x : Fin n → k) :
    (ρ⁻¹ * r * ρ) (Loc.inX k n c x) = Loc.inX k n c ((γ⁻¹ * g * γ) x) := by
  show ρ.symm (r (ρ _)) = Loc.inX k n c (γ.symm (g (γ x)))
  rw [hγ, hg, LinearEquiv.symm_apply_eq, hγ, LinearEquiv.apply_symm_apply]

theorem n1Arg_conj_eq {F : Type} [Field F] {n c : ℕ} {ρ r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hρ : ρ ∈ Loc.R1 F n c) (hr : r ∈ Loc.R1 F n c) : Loc.n1Arg (ρ⁻¹ * r * ρ) = Loc.n1Arg r := by
  have h1 := unipotentCharacterArgument_mul_stabilizer hρ.1 (mul_mem (mul_mem (inv_mem hρ) hr) hρ).1
  have h2 := unipotentCharacterArgument_mul_stabilizer hr.1 hρ.1
  have e : ρ * (ρ⁻¹ * r * ρ) = r * ρ := by group
  rw [e, h2] at h1
  linear_combination -h1

end GlobalTheory.Proof.level_eq_parahoric_category
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharacterNeZeroOfNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero

variable {E : Type} [Field E] [NumberField E]

theorem isUnit_reduction_of_valuation_eq_one (P : HeightOneSpectrum (𝓞 E)) {b : E} (hb : P.valuation E b = 1) :
    IsUnit (redP P b) := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hb
  have h1 : IntAt P b := (IntegralPowerExpansion.intAt_iff_val P b).2 hb.le
  have h2 : IntAt P b⁻¹ := (IntegralPowerExpansion.intAt_iff_val P _).2 (by rw [map_inv₀, hb, inv_one])
  have h3 := reduction_mul h1 h2
  have h4 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [mul_inv_cancel₀ hb0, h4] at h3
  exact IsUnit.of_mul_eq_one _ h3.symm

theorem exists_isUnit_reduction_div_pow {P : HeightOneSpectrum (𝓞 E)} (hP : GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {a : E} (ha : a ≠ 0) :
    ∃ z : ℤ, IsUnit (redP P (a / (qOf P : E) ^ z)) := by
  have hv : P.valuation E a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  refine ⟨-WithZero.log (P.valuation E a), isUnit_reduction_of_valuation_eq_one P ?_⟩
  rw [map_div₀, map_zpow₀, IntegralPowerExpansion.val_q hP, ← WithZero.exp_zsmul]
  simp only [smul_neg, neg_smul, neg_neg, smul_eq_mul, mul_one, mul_neg, neg_mul]
  rw [WithZero.exp_log hv, div_self hv]

theorem locChar_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)),
    GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E), cq ≠ 0 → a ≠ 0 →
      LocE.locChar (qOf P) cq χ a ≠ 0 := by
  intro E _ _ K _ P hP cq χ a hcq ha
  have h : IsUnit (redP P (a / (qOf P : E) ^ LocE.vP P (qOf P) a)) :=
    Classical.epsilon_spec (exists_isUnit_reduction_div_pow hP ha)
  unfold LocE.locChar LocE.unitV
  rw [dite_eq_left h]
  exact mul_ne_zero (zpow_ne_zero _ hcq) (Units.ne_zero _)

end GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero
end

