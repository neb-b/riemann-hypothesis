module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0351
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0025
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.DiscreteSeriesHilbert.StepSqInt
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0056
public import GroundTheory.PAdicHodge.AInfGalois
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0354
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
public import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFiltrationExhaustive
section
noncomputable section

open Matrix ValuativeRel GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZMirExhaust

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def ballSub (s : kˣ) : AddSubgroup k where
  carrier := cball s
  zero_mem' := by simp [cball]
  add_mem' {a b} ha hb := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    have hb' : valuation k b ≤ valuation k (s : k) := hb
    exact (Valuation.map_add _ a b).trans (max_le ha' hb')
  neg_mem' {a} ha := by
    have ha' : valuation k a ≤ valuation k (s : k) := ha
    show valuation k (-a) ≤ valuation k (s : k)
    rwa [Valuation.map_neg]

theorem exists_ball_of_finset (T : Finset k) : ∃ s : kˣ, ∀ x ∈ T, x ∈ cball s := by
  classical
  refine Finset.induction_on T ?_ ?_
  · exact ⟨1, by simp⟩
  · intro a T _ ih
    obtain ⟨s, hs⟩ := ih
    by_cases h : valuation k a ≤ valuation k (s : k)
    · refine ⟨s, fun x hx => ?_⟩
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact h
      · exact hs x hx
    · have ha0 : a ≠ 0 := by
        rintro rfl
        exact h (by simp)
      refine ⟨Units.mk0 a ha0, fun x hx => ?_⟩
      show valuation k x ≤ valuation k a
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact le_rfl
      · have hx' : valuation k x ≤ valuation k (s : k) := hs x hx
        exact le_trans hx' (le_of_lt (not_le.1 h))

def unipMir (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

theorem continuous_colMat (n : ℕ) : Continuous (colMat k n) := by
  refine continuous_matrix fun i j => ?_
  unfold GlobalTheory.BZMir.colMat
  by_cases hj : j = Fin.last n
  · simp only [if_pos hj]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl
    · simp only [Fin.lastCases_castSucc]
      exact continuous_apply i
    · simp only [Fin.lastCases_last]
      exact continuous_const
  · simp only [if_neg hj]
    exact continuous_const

theorem continuous_unipMir (n : ℕ) :
    Continuous (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) := by
  have hval : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n v :=
    continuous_const.add (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hinv : Continuous fun v : Fin n → k =>
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - GlobalTheory.BZMir.colMat k n v :=
    continuous_const.sub (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_colMat n)
  have hGL : Continuous fun v : Fin n → k =>
      GlobalTheory.BZMir.unip k n (Multiplicative.ofAdd v) :=
    Units.continuous_iff.2 ⟨hval, hinv⟩
  exact hGL.subtype_mk _

def ballGroup (n : ℕ) (s : kˣ) : Subgroup (Mir k n) :=
  (AddSubgroup.toSubgroup (AddSubgroup.pi Set.univ fun _ : Fin n => ballSub s)).map (unipMir n)

theorem ballGroup_le (n : ℕ) (s : kˣ) : ballGroup (k := k) n s ≤ MirUin k n := by
  rintro _ ⟨v, -, rfl⟩
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU]
  exact ⟨v, rfl⟩

theorem coe_ballGroup (n : ℕ) (s : kˣ) : (ballGroup (k := k) n s : Set (Mir k n)) =
    (fun v : Fin n → k => unipMir (k := k) n (Multiplicative.ofAdd v)) '' Set.univ.pi fun _ => cball s := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.coe_map]
  ext g
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.toAdd v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨Multiplicative.ofAdd v, hv, rfl⟩

theorem isCompact_ballGroup (n : ℕ) (s : kˣ) : IsCompact (ballGroup (k := k) n s : Set (Mir k n)) := by
  rw [GlobalTheory.CompanionTheory.BZMirExhaust.coe_ballGroup]
  exact (isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_cball s).image
    (GlobalTheory.CompanionTheory.BZMirExhaust.continuous_unipMir n)

theorem exhaust (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZMir.Fun.Exhaust k := by
  classical
  intro n S hS
  obtain ⟨s, hs⟩ := GlobalTheory.CompanionTheory.BZMirExhaust.exists_ball_of_finset
    ((S ×ˢ (Finset.univ : Finset (Fin n))).image fun p =>
      ((p.1 : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc p.2) (Fin.last n))
  refine ⟨GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup n s, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup_le n s, ?_,
    GlobalTheory.CompanionTheory.BZMirExhaust.isCompact_ballGroup n s⟩
  intro g hg
  have hgU := hS hg
  rw [SetLike.mem_coe, GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hgU
  obtain ⟨v, hv⟩ := hgU
  rw [Finset.mem_coe] at hg
  rw [SetLike.mem_coe, GlobalTheory.CompanionTheory.BZMirExhaust.ballGroup, Subgroup.mem_map]
  refine ⟨v, ?_, Subtype.ext hv⟩
  show ∀ i ∈ Set.univ, Multiplicative.toAdd v i ∈ GlobalTheory.CompanionTheory.BZMirExhaust.ballSub s
  intro i _
  have hvi := GlobalTheory.BZMir.unip_apply_castSucc_last k n v i
  rw [hv] at hvi
  show Multiplicative.toAdd v i ∈ GlobalTheory.SplitWeil.cball s
  rw [← hvi]
  exact hs _ (Finset.mem_image.2 ⟨(g, i), Finset.mem_product.2 ⟨hg, Finset.mem_univ i⟩, rfl⟩)

end GlobalTheory.CompanionTheory.BZMirExhaust

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicRestrictionUnipotentSmooth
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.BZMir GroundTheory.LocalField Matrix GlobalTheory.CompanionTheory.MirFourier

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colMat_toAdd (n : ℕ) :
    Continuous fun x : Multiplicative (Fin n → k) => colMat k n x.toAdd := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  by_cases hj : j = Fin.last n
  · subst hj
    induction i using Fin.lastCases with
    | last => simpa [colMat] using continuous_const
    | cast i =>
      have h : Continuous fun a : Multiplicative (Fin n → k) => Multiplicative.toAdd a i :=
        (continuous_apply i).comp continuous_toAdd
      simpa [colMat] using h
  · simpa [colMat, hj] using continuous_const

theorem continuous_unipMir (n : ℕ) : Continuous (unipMir k n) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_const.add (continuous_colMat_toAdd n)
  · have h : Continuous fun x : Multiplicative (Fin n → k) => (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) - colMat k n x.toAdd :=
      continuous_const.sub (continuous_colMat_toAdd n)
    exact h

theorem isSmooth_comp_unipMir : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (Mir k n) V), IsSmooth τ → IsSmooth (τ.comp (unipMir k n)) := by
  intro k _ _ _ _ n V _ _ τ h w
  exact (h w).preimage (continuous_unipMir n)

end GlobalTheory.CompanionTheory.MirFourier

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusTrivialOnLeviCompact
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.HalfModCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_nabs_le_of_isCompact {C : Set k} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ u : kˣ, (u : k) ∈ C → nabs k u ≤ B := by
  classical
  have hopen : ∀ y : kˣ, IsOpen {x : k | valuation k x ≤ valuation k (y : k)} := by
    intro y
    have hy : valuation k (y : k) ≠ 0 := by simp
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 (valuation k (y : k)) hy, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_ofPred_eq] at hz hx ⊢
    calc valuation k (x + z) ≤ max (valuation k x) (valuation k z) := Valuation.map_add _ _ _
      _ ≤ valuation k (y : k) := max_le hx (le_of_lt (by simpa using hz))
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun y : kˣ => {x : k | valuation k x ≤ valuation k (y : k)})
    hopen (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases hx : x = 0
      · exact ⟨1, by simp [hx]⟩
      · exact ⟨Units.mk0 x hx, by simp⟩)
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image (insert 1 t) (fun y : kˣ => valuation k (y : k))
    (Finset.insert_nonempty _ _)
  refine ⟨nabs k y, fun u hu => nabs_le_of_valuation_le ?_⟩
  obtain ⟨z, hz, hzu⟩ := Set.mem_iUnion₂.1 (ht hu)
  exact le_trans hzu (hy z (Finset.mem_insert_of_mem hz))

theorem nabs_pow_eq (y : kˣ) (n : ℕ) : nabs k (y ^ n) = nabs k y ^ n := by
  unfold nabs
  rw [map_pow, NNReal.coe_pow]

theorem nabs_inv_eq (y : kˣ) : nabs k y⁻¹ = (nabs k y)⁻¹ := by
  unfold nabs
  rw [map_inv, NNReal.coe_inv]

theorem nabs_eq_one_of_pow_le (y : kˣ) (B : ℝ) (h₁ : ∀ n : ℕ, nabs k (y ^ n) ≤ B)
    (h₂ : ∀ n : ℕ, nabs k (y⁻¹ ^ n) ≤ B) : nabs k y = 1 := by
  have hpos : 0 < nabs k y := (nabs_properties k).2.1 y
  rcases lt_trichotomy (nabs k y) 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < (nabs k y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
    have h3 := h₂ n
    rw [nabs_pow_eq, nabs_inv_eq] at h3
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have h3 := h₁ n
    rw [nabs_pow_eq] at h3
    linarith

def blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (g : GL (Fin N) k) : k :=
  Matrix.det (Matrix.of fun i j : Fin (d a) =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩))

theorem continuous_blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) :
    Continuous (blockDet (k := k) d hd a) := by
  unfold blockDet
  first
    | fun_prop
    | exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
        (Units.continuous_val.matrix_elem _ _))

theorem blockDet_leviEmb {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h)
    (x : Levi k (Bl d)) :
    blockDet d hd a (leviEmb k (stdBlocks d hd) x) =
      ((Matrix.GeneralLinearGroup.det (x a) : kˣ) : k) := by
  unfold blockDet
  have hm : (Matrix.of fun i j : Fin (d a) =>
      ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) =
      ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k) := by
    ext i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [hm, Matrix.GeneralLinearGroup.val_det_apply]

theorem nabs_det_eq_one_of_mem_KM {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {J : Subgroup (GL (Fin N) k)} (hJ : IsCompact (J : Set (GL (Fin N) k)))
    {x : Levi k (Bl d)} (hx : x ∈ KM k N J d hd) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (x a)) = 1 := by
  have hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈
      blockDet (k := k) d hd a '' (J : Set (GL (Fin N) k)) :=
    fun z hz => ⟨_, hz, rfl⟩
  obtain ⟨B, hB⟩ := exists_nabs_le_of_isCompact (hJ.image (continuous_blockDet d hd a))
  apply nabs_eq_one_of_pow_le _ B
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem hx n)
    have e : (x ^ n) a = x a ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow] at h1
    exact h1
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)
    have e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow, map_inv] at h1
    exact h1

theorem deltaHalf_eq_one_of_mem_KM :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)),
      IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  intro k _ _ _ _ N h d hd J hJ x hx
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro a _
  rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  unfold detChar
  rw [MonoidHom.comp_apply]
  apply Units.ext
  simp [absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]

end GlobalTheory.CompanionTheory.HalfModCompact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MollifierApproximationHilbert
section
noncomputable section

open MeasureTheory ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.HilbMoll

variable {n : ℕ}

theorem opConv_mem_of_isClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (W : Submodule ℂ H) (hWc : IsClosed (W : Set H)) (hWs : ∀ g ∈ UJset ε, ∀ x ∈ W, σ g x ∈ W)
    {x : H} (hx : x ∈ W) : opConv ε σ α x ∈ W := by
  have : CompleteSpace W := hWc.completeSpace_coe
  unfold opConv
  by_cases hint : Integrable (fun g : Formalism.REAL.UJ ε => α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x)
      (Formalism.REAL.muG ε)
  · have hfix : ∀ g : Formalism.REAL.UJ ε, W.starProjection (α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x) =
        α (Formalism.MainNotions.S.umat g) • σ (Formalism.MainNotions.S.umat g) x := fun g =>
      Submodule.starProjection_eq_self_iff.2 (W.smul_mem _ (hWs _ (arb_umat_mem g) x hx))
    have h := W.starProjection.integral_comp_comm hint
    simp only [hfix] at h
    rw [h]
    exact W.starProjection_apply_mem _
  · rw [integral_undef hint]
    exact W.zero_mem

theorem stepMoll : PositivityTheory.RgDs.Hilb.StepMoll := by
  intro n ε W S hWc hWs hSf hSW _
  have := hSf
  obtain ⟨α, hadd, hsmul, hαK, hαsm, hαS⟩ := exists_moll_data (rreg_isURepOn ε) S
  let A : L2 ε →ₗ[ℂ] L2 ε := { toFun := opConv ε (rreg ε) α, map_add' := hadd, map_smul' := hsmul }
  have hAv : ∀ v, A v = opConv ε (rreg ε) α v := fun v => rfl
  refine ⟨A, fun k hk x => (hαK k hk x).symm, ?_, ?_, ?_⟩
  · intro w hw h0
    have h1 := hαS w hw
    rw [← hAv, h0, zero_sub, norm_neg] at h1
    have h2 : ‖w‖ ≤ 0 := by linarith
    exact norm_le_zero_iff.1 h2
  · rintro _ ⟨w, _, rfl⟩
    exact (mem_smD_iff ε (rreg ε) _).2 (hαsm w)
  · rintro _ ⟨w, hw, rfl⟩
    exact opConv_mem_of_isClosed ε (rreg ε) α W hWc hWs (hSW hw)

end GlobalTheory.CompanionTheory.HilbMoll
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsInterleaveSum
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

namespace GlobalTheory.CompanionTheory.ZcMerge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def fromA (a : Comb.ASeg (CuspT k)) : Segment k := Segment.ofFirst a.start.1 a.start.2 a.len a.len_pos

theorem toA_fromA (a : Comb.ASeg (CuspT k)) : toA (fromA a) = a := rfl

theorem fromA_toA (Δ : Segment k) : fromA (toA Δ) = Δ := Segment.ext_first rfl rfl

theorem carrier_subset_of_image {Δ Δ' : Segment k} (h : (toA Δ).carrier sNu ⊆ (toA Δ').carrier sNu) :
    Δ.carrier ⊆ Δ'.carrier := by
  rw [← ZcWords.image_carrier, ← ZcWords.image_carrier]
  exact Set.image_mono h

theorem aPrecedes_of_precedes {Δ Δ' : Segment k} (h : Δ.Precedes Δ') : Comb.APrecedes sNu (toA Δ) (toA Δ') := by
  obtain ⟨⟨⟨Γ, hΓ⟩, h1, h2⟩, j, hj, hs⟩ := h
  refine ⟨⟨⟨toA Γ, ?_⟩, fun e => h1 (carrier_subset_of_image e), fun e => h2 (carrier_subset_of_image e)⟩, j, hj,
    Subtype.ext ?_⟩
  · apply Set.image_injective.2 (Subtype.val_injective (p := fun x : IrrGL (k := k) => x.IsCusp))
    rw [Set.image_union, ZcWords.image_carrier, ZcWords.image_carrier, ZcWords.image_carrier, hΓ]
  · exact hs.trans (ZcWords.val_sNu_iterate (toA Δ).start j).symm

theorem map_toA_map_fromA (L : List (Comb.ASeg (CuspT k))) : (L.map fromA).map toA = L := by
  rw [List.map_map]
  exact List.map_id'' toA_fromA L

theorem isOrderedForm_get {L : List (Comb.ASeg (CuspT k))} {𝔪 : Multiset (Segment k)}
    (hL : (L : Multiset (Comb.ASeg (CuspT k))) = 𝔪.map toA) (hO : Comb.AOrdered sNu L) :
    IsOrderedForm (L.map fromA).get 𝔪 := by
  constructor
  · rw [Fin.univ_val_map, List.ofFn_get, ← Multiset.map_coe, hL, Multiset.map_map]
    exact (Multiset.map_congr rfl fun Δ _ => fromA_toA Δ).trans (Multiset.map_id' 𝔪)
  · intro i j hij hp
    rw [Comb.AOrdered, ← map_toA_map_fromA L, List.pairwise_map] at hO
    exact List.pairwise_iff_get.1 hO i j hij (aPrecedes_of_precedes hp)

theorem wtW_get (L : List (Comb.ASeg (CuspT k))) :
    wtW (L.map fromA).get = (Comb.wt sNu L).map Subtype.val := by
  rw [ZcWords.wtW_eq, List.ofFn_get, map_toA_map_fromA]

theorem exists_common_orderedForm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL), ∀ (𝔪 𝔫 : Multiset (Segment k)),
    ∃ (h₁ h₂ h : ℕ) (Δ₁ : Fin h₁ → Segment k) (Δ₂ : Fin h₂ → Segment k) (Δ : Fin h → Segment k),
      IsOrderedForm Δ₁ 𝔪 ∧ IsOrderedForm Δ₂ 𝔫 ∧ IsOrderedForm Δ (𝔪 + 𝔫) ∧
        Zc.Comb.Interleave (wtW Δ₁) (wtW Δ₂) (wtW Δ) := by
  intro k _ _ _ _ _ 𝔪 𝔫
  obtain ⟨L₁, L₂, L, h1, h2, h3, o1, o2, o3, hI⟩ := GlobalTheory.CompanionTheory.SegOrder.exists_common_ordered_form (sNu (k := k)) ZcWords.sNu_injective
    ZcWords.sNu_aperiodic (𝔪.map toA) (𝔫.map toA)
  refine ⟨_, _, _, (L₁.map fromA).get, (L₂.map fromA).get, (L.map fromA).get, isOrderedForm_get h1 o1,
    isOrderedForm_get h2 o2, isOrderedForm_get (by rw [h3, Multiset.map_add (f := _)]) o3, ?_⟩
  rw [wtW_get, wtW_get, wtW_get]
  exact ZcWords.interleave_map _ hI

end GlobalTheory.CompanionTheory.ZcMerge

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivialStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pi_tensor_irreducible_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL (k := k)), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  first | exact @GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | exact GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | (intros; apply GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyBall
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.MirFourier

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def polyBall (n : ℕ) (s : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ i, x.toAdd i ∈ cball s}
  mul_mem' := fun ha hb i => add_mem_cball (ha i) (hb i)
  one_mem' := fun i => by simp [cball]
  inv_mem' := fun {x} hx i => by
    have h := hx i
    simpa [cball, Valuation.map_neg] using h

def resChr (ψ : AddChar k Circle) {n : ℕ} (a : Fin n → k) (L : Subgroup (Multiplicative (Fin n → k))) : L →* ℂˣ :=
  (chrA k ψ a).comp L.subtype

def unipIn (k : Type) [Field k] (n : ℕ) : Multiplicative (Fin n → k) →* Mir k n :=
  (unip k n).codRestrict (Mir k n) (fun v => MirU_le_Mir k n ⟨v, rfl⟩)

def ann (ψ : AddChar k Circle) (n : ℕ) (t : kˣ) : Subgroup (Multiplicative (Fin n → k)) where
  carrier := {x | ∀ a ∈ polyBall n t, ψ (a.toAdd ⬝ᵥ x.toAdd) = 1}
  mul_mem' := fun {x y} hx hy a ha => by
    rw [toAdd_mul, dotProduct_add, AddChar.map_add_eq_mul, hx a ha, hy a ha, one_mul]
  one_mem' := fun a _ => by simp
  inv_mem' := fun {x} hx a ha => by
    rw [toAdd_inv, dotProduct_neg, AddChar.map_neg_eq_inv, hx a ha, inv_one]

end GlobalTheory.CompanionTheory.MirFourier

end
end

