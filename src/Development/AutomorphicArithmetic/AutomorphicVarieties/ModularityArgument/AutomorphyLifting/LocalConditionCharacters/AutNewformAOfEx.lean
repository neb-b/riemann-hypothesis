module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocalConditionCharacters.NewDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.RankTwoDescentSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicLiftRankTwoOfCyclicBaseChange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AUpDownOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.FlagLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WindowMul
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0181

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.Zero.LLC UpperTheory.V.Z.Win UpperTheory.Gal.SV UpperTheory.V.Z.Win.RR
open scoped Matrix Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.RR

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]

private theorem alg0 (P : HypothesesH) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) (m : ℤ) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ m) := by
  obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
  rw [zpow_zero, one_mul] at hθ
  have hfinite : ∃ k : ℕ, 0 < k ∧ ∀ s, χ s ^ k = 1 := by
    have : NeZero M := ⟨by omega⟩
    have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot Ω M
    refine ⟨Fintype.card (ZMod M)ˣ, Fintype.card_pos, fun s => ?_⟩
    rw [← map_pow]
    refine hχ _ fun ζ h => ?_
    have h1 := hμ.autToPow_spec ℚ (s ^ Fintype.card (ZMod M)ˣ)
    rw [map_pow, pow_card_eq_one, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ hμ.pow_eq_one, pow_one] at h1
    obtain ⟨i, -, rfl⟩ := hμ.eq_pow_of_pow_eq_one h
    rw [map_pow, ← h1]
  obtain ⟨k, hk, hpow⟩ := hfinite
  refine (algOfCyc P ℚ Ω l ι).1 _ ?_ fun w _ => ?_
  · have hcyc : Continuous (cycBar ℚ Ω l) :=
      UpperTheory.Reformulated.B.CyclotomicCharacterAtPrimeContinuous.cyc_cont ℚ Ω l
    exact (Matrix.GeneralLinearGroup.continuous_det.comp hW).mul ((continuous_zpow _).comp hcyc)
  · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
    refine ⟨A, hA, m, k, hk, fun s _ => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.zpow_apply, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one, hθ, hpow]

private theorem alg_det (P : HypothesesH) (ι : Qbar l ≃+* ℂ) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) (hW : Continuous W)
    (hdet : IsCycWt l 0 (Matrix.GeneralLinearGroup.det.comp W)) :
    IsAlgChar ι (Matrix.GeneralLinearGroup.det.comp W * cycBar ℚ Ω l ^ (((2 : ℕ) : ℤ) - 1)) := alg0 P ι W hW hdet _

private theorem flag_all {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l)) {B : ValuationSubring Ω}
    (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∃ N : Subgroup (G ℚ Ω), IsOpen (N : Set (G ℚ Ω)) ∧ ∀ w : HeightOneSpectrum (𝓞 ℚ), ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal →
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∃ s ∈ N ⊓ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1) ∧
        ∃ κ, IsFlagOn W (Dec (F := ℚ) A) κ ∧ ∀ i (s : ↥(Dec (F := ℚ) A)), (s : G ℚ Ω) ∈ N ⊓ Ine (F := ℚ) A →
          κ i s = cycBar ℚ Ω l s ^ (![(e : ℤ), -(e : ℤ)] i) := by
  have : IsGalois ℚ Ω := {}
  have := Subgroup.quotient_finite_of_isOpen H hH
  have : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hn : H.normalCore.Normal := H.normalCore_normal
  have hH' : IsOpen (H.normalCore : Set (G ℚ Ω)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (H.normalCore_isClosed (H.isClosed_of_isOpen hH))
  have hk : H.normalCore.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  refine ⟨H.normalCore, hH', fun w hw A hA => ?_⟩
  have hAl : A.valuation (l : Ω) < 1 := ((UpperTheory.V.Base.places ℚ Ω l A).2.2.1 w hA).2 hw
  have hcyc : ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
    have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
    obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hAl hu.unit
    refine ⟨s, hs, fun k hk h => ?_⟩
    have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
      change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
      rw [he, hu.unit_spec, map_natCast, map_natCast]
    have h3 := congrArg Units.val h
    rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
    have := hl.out.pos
    omega
  obtain ⟨s, hs, hs'⟩ := hcyc
  have hs0 : s ^ H.normalCore.index ∈ H.normalCore ⊓ Ine (F := ℚ) A :=
    ⟨@Subgroup.pow_index_mem _ _ _ hn s, Subgroup.pow_mem _ hs _⟩
  have hinf : ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l (s ^ H.normalCore.index) ^ k ≠ 1 := fun k hk0 h => by
    rw [map_pow, ← pow_mul] at h
    exact hs' _ (mul_ne_zero hk hk0) h
  refine ⟨⟨_, hs0, hinf⟩, ?_⟩
  have hBw : IsPlaceOver B w := by
    obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω l B
    obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hB
    have hpr : Prime (l : 𝓞 ℚ) := by
      have e : (l : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (l : ℤ) := by simp
      rw [e]
      exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hl.out)
    have hm : (Ideal.span {(l : 𝓞 ℚ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
    have e : v = w := HeightOneSpectrum.ext
      ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hB))).symm.trans
        (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
    exact e ▸ hv
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isPlaceOver hBw hA
  have hfl' : IsFlagOn W (H.normalCore ⊓ Ine (F := ℚ) (g • B))
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H.normalCore ⊓ Ine (F := ℚ) (g • B)).subtype) := by
    obtain ⟨p, hp⟩ := hfl
    refine ⟨p * (W g)⁻¹, fun t => ?_⟩
    have hm : g⁻¹ * (t : G ℚ Ω) * g ∈ H ⊓ Ine (F := ℚ) B :=
      ⟨H.normalCore_le (hn.conj_mem' _ t.2.1 g), GlobalTheory.PointIrredCompare.conj_mem_Ine_of_smul t.2.2⟩
    have e1 : p * (W g)⁻¹ * W t * (p * (W g)⁻¹)⁻¹ = p * W (g⁻¹ * (t : G ℚ Ω) * g) * p⁻¹ := by
      rw [map_mul, map_mul, map_inv]; group
    obtain ⟨h1, h2⟩ := hp ⟨_, hm⟩
    rw [e1]
    refine ⟨h1, fun i => (h2 i).trans ?_⟩
    congr 1
    change ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (g⁻¹ * (t : G ℚ Ω) * g) = ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) t
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  have flagStable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
      (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
      (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
    obtain ⟨g, hg⟩ := h
    obtain ⟨s0, hs0, hne⟩ := hne
    let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
    have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
    have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
    have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
      rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
      have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
      have e2 := hmul s0 d 1 0
      have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
      rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
      have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
      apply mul_left_cancel₀ this
      linear_combination e2
    refine ⟨fun i => MonoidHom.toHomUnits
      { toFun := fun s => M s i i
        map_one' := by simp
        map_mul' := fun s t => by
          rw [Subgroup.coe_mul, hmul]
          fin_cases i
          · simp [h3 _ t.2]
          · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
    fin_cases i <;> fin_cases j
    · exact absurd hij (by decide)
    · exact absurd hij (by decide)
    · exact h3 _ s.2
    · exact absurd hij (by decide)
  exact flagStable W (Dec (F := ℚ) (g • B)) (H.normalCore ⊓ Ine (F := ℚ) (g • B)) _ le_rfl
    (fun d hd s hs => ⟨hn.conj_mem' s hs.1 d, by simpa using conj_mem_Ine ((Dec (F := ℚ) (g • B)).inv_mem hd) hs.2⟩)
    (fun i => (cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)) (by
      refine ⟨_, hs0, fun h1 => hinf (e + e) (by omega) ?_⟩
      rw [MonoidHom.zpow_apply, MonoidHom.zpow_apply] at h1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast] at h1
      rw [pow_add]
      exact mul_eq_one_iff_eq_inv.2 h1) hfl'

private theorem zpow_ne {C : Type} [Group C] {x : C} (h : ∀ k : ℕ, k ≠ 0 → x ^ k ≠ 1) {a b : ℤ} (e : x ^ a = x ^ b) : a = b := by
  by_contra hne
  have h1 : x ^ (a - b) = 1 := by rw [zpow_sub, e, mul_inv_cancel]
  refine h (a - b).natAbs (by omega) ?_
  rcases Int.natAbs_eq (a - b) with h2 | h2
  · rw [← zpow_natCast, ← h2, h1]
  · rw [← zpow_natCast, ← inv_inj, ← zpow_neg, ← h2, h1, inv_one]

private theorem inf_char (P : HypothesesH) (hC : CompatT) (ι : Qbar l ≃+* ℂ) {e : ℕ} (he : 1 ≤ e) (W : G ℚ Ω →* GL (Fin 2) (Qbar l))
    (hW : Continuous W) (π : TR.CuspSub ℚ 2) (hreg : π.IsRegAlg) (hatt : AttR ι W π) (hU : WitUp ι W)
    {B : ValuationSubring Ω} (hB : B.valuation (l : Ω) < 1) (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω)))
    (hfl : IsFlagOn W (H ⊓ Ine (F := ℚ) B)
      (fun i => ((cycBar ℚ Ω l) ^ (![(e : ℤ), -(e : ℤ)] i)).comp (H ⊓ Ine (F := ℚ) B).subtype)) :
    ∀ v, π.HasInfChar v (infOf ![(e : ℤ), -(e : ℤ)]) := by
  intro v
  obtain ⟨hdet, L, _, _, _, _, _, hirr, ⟨η, σ₀, hσ₀, hησ, hηL⟩, ka, hka, hWit⟩ := hU
  haveI : Module.IsTorsionFree L Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
  obtain ⟨K, hK, hKC⟩ := Z.Bc.exists_quad L Ω η σ₀ hσ₀ hησ hηL
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  haveI a : IsAbelianGalois K L := IsAbelianGalois.tower_top ℚ K L
  haveI : Group.IsSolvable (L ≃ₐ[K] L) := isSolvable_of_comm a.is_comm.comm
  have ec : W.comp (galEmb ℚ L Ω) = (W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω) := MonoidHom.ext fun _ => rfl
  have hirr' : IsIrr ((W.comp (galEmb ℚ K Ω)).comp (galEmb K L Ω)) := ec ▸ hirr
  obtain ⟨P₁, a1, a2, a3⟩ := Z.Bc.upQuadI_of P.toClassicalTheorems (Z.Bc.quadLiftRealToComplex_of_base_change P.bc) ℚ K Ω l ι hK W π hW hreg hatt
    ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hirr')
  obtain ⟨Q, b1, b2, b3⟩ := Z.Bc.upSolI_of P.toClassicalTheorems (Z.Bc.cyclicLiftRankTwo_of_cyclic_base_change P.cyc) K L Ω l ι _ P₁
    (hW.comp (continuous_restrictScalarsHom ℚ K Ω)) a1 a2 hirr'
  rw [← ec] at b2
  have hWL : Continuous (W.comp (galEmb ℚ L Ω)) := hW.comp (continuous_restrictScalarsHom ℚ L Ω)
  have hpol : Sol.Pol ι W := by
    have halg := alg0 P ι W hW hdet 0
    rw [zpow_zero, mul_one] at halg
    obtain ⟨M, χ, hM, hχ, hθ⟩ := hdet
    rw [zpow_zero, one_mul] at hθ
    have hconj : ∃ c : G ℚ Ω, IsConjEl c := by
      have : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
      let j : Ω →ₐ[ℚ] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      let : Algebra Ω ℂ := j.toRingHom.toAlgebra
      have : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
      let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
      exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
    obtain ⟨c, hc⟩ := hconj
    have hpairing : ∃ J, IsPairing c W ((Matrix.GeneralLinearGroup.det.comp W).comp (resG ℚ ℚ Ω)) J := by
      let J : GL (Fin 2) (Qbar l) := Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; -1, 0] (by simp [Matrix.det_fin_two])
      refine ⟨J * W c⁻¹, fun s s' h => ?_⟩
      have h' : s' = c * s * c⁻¹ := h
      have e : W c⁻¹ * W s' = W s * W c⁻¹ := by rw [h', ← map_mul, ← map_mul]; congr 1; group
      have e' : (W c⁻¹).val * (W s').val = (W s).val * (W c⁻¹).val := congrArg Units.val e
      have hp : (W s).valᵀ * J.val * (W s).val = (W s).val.det • J.val := by
        change (W s).valᵀ * !![0, 1; -1, 0] * (W s).val =
          (W s).val.det • (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) (Qbar l))
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.det_fin_two] <;> ring
      have hd : (((Matrix.GeneralLinearGroup.det.comp W).comp (resG ℚ ℚ Ω) s : (Qbar l)ˣ) : Qbar l) = (W s).val.det := rfl
      rw [hd, Units.val_mul, ← Matrix.smul_mul, ← hp]
      simp only [Matrix.mul_assoc, e']
    obtain ⟨J, hJ⟩ := hpairing
    refine ⟨ℚ, _, _, _, _, inferInstance, inferInstance, inferInstance, _, c, J, halg, ?_, hc, hJ⟩
    intro c₁ c₂ hc₁ hc₂
    rw [hθ]
    have conj_root {d : G ℚ Ω} (hd : IsConjEl d) {ζ : Ω} (hζ : ζ ^ M = 1) : d ζ = ζ⁻¹ := by
      obtain ⟨j, hj⟩ := hd
      apply j.injective
      have h1 : (j ζ) ^ M = 1 := by rw [← map_pow, hζ, map_one]
      rw [hj, map_inv₀, Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 (by omega))]
    have hfix := hχ (c₁⁻¹ * c₂) fun ζ hζ => by
      rw [AlgEquiv.mul_apply, conj_root hc₂ hζ, ← conj_root hc₁ hζ]
      exact c₁.symm_apply_apply ζ
    rwa [map_mul, map_inv, inv_mul_eq_one] at hfix
  have hQ : ∃ χ, GlobalTheory.ContraPair.PolarizedPair Q χ := by
    have : IsAlgClosure (maximalRealSubfield L) Ω :=
      ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.tower_top (K := ℚ) (maximalRealSubfield L)⟩
    obtain ⟨μ, χ, c, J, hμ, hs, hc, hJ⟩ :=
      UpperTheory.cyclotomicCharacter_plusPart (algOfCyc P) UpperTheory.cyclotomic_char_conj_invariant L Ω l ι 2 _
        (UpperTheory.solvable_polarized_restriction ℚ L Ω l ι 2 W hpol)
    have hd := selfDualC P L Ω l ι 2 one_le_two _ Q b2 χ μ hμ c J hc hJ
    have hsign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel _ Ω l ι χ μ hμ hs
    obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield L)) := inferInstance
    have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
      rcases sq_eq_one_iff.1 h3 with e | e
      · exact ⟨0, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
      · exact ⟨1, fun u => (hsign u v₀).trans (Units.ext (by simpa using e))⟩
    have hN : compNorm L (χ * quadChar L ^ (m + 2)) = compNorm L χ := by
      rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
    refine ⟨χ * quadChar L ^ (m + 2), fun v => ?_, hN ▸ hd⟩
    change χ.locInf v (-1) * (quadChar L ^ (m + 2)).locInf v (-1) = (-1) ^ (2 : ℕ)
    rw [locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
    simp
  have hka' : IsAlgChar ι ka := by
    obtain ⟨h1, art, χ, a, h2, h3, h4⟩ := hka
    exact ⟨χ, h1, art, a, h2, h3, h4⟩
  have hWA : WitA ι (W.comp (galEmb ℚ L Ω)) := by
    have := (aIsoTwOf flagLaws ImaginaryQuadraticEtaCharacter.winTw P.toClassicalTheorems L Ω l ι 2 _ hWit).2 ka⁻¹ ((algOfCyc P L Ω l ι).2.1 ka ka hka' hka').2
    have htw : tw (tw (W.comp (galEmb ℚ L Ω)) ka) ka⁻¹ = W.comp (galEmb ℚ L Ω) := by
      refine MonoidHom.ext fun s => Units.ext ?_
      rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
        inv_mul_cancel₀ (Units.ne_zero _), one_smul]
    rwa [htw] at this
  obtain ⟨N, hN, hall⟩ := flag_all he W hB H hH hfl
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places L Ω l B
  obtain ⟨w, h⟩ := p1 fun h0 => (p2 h0).2 hB
  have hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := (p3 w h).1 hB
  have hw0 : ((l : ℕ) : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]; exact hw
  have hpot : PotUnl W (w.under (𝓞 ℚ)) := fun A hA => by
    obtain ⟨⟨s, hs, hs'⟩, κ, hκ, hI⟩ := hall _ hw0 A hA
    refine ⟨κ, hκ, fun i j m hm e0 => ?_⟩
    have e1 := DFunLike.congr_fun e0 ⟨s, Ine_le_Dec A hs.2⟩
    rw [MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.mul_apply, hI i _ hs, hI j _ hs] at e1
    change (cycBar ℚ Ω l s ^ _) ^ m = (cycBar ℚ Ω l s ^ _ * cycBar ℚ Ω l s) ^ m at e1
    rw [← zpow_add_one, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at e1
    have e2 := mul_right_cancel₀ (show (m : ℤ) ≠ 0 by omega) (zpow_ne hs' e1)
    fin_cases i <;> fin_cases j <;> simp at e2 <;> omega
  have hpotL : PotUnl (W.comp (galEmb ℚ L Ω)) w := (((flagLaws ℚ Ω l 2 W).2.2.2 L).2.2 w hw).1 hpot
  obtain ⟨HT, hwt, hloc⟩ := hC L Ω l ι 2 one_le_two _ Q hWL b1 hQ b2
  obtain ⟨⟨σ, hσ⟩, -⟩ := locCompC P.toClassicalTheorems L 2 Q w
  obtain ⟨rc, hrc⟩ := recTExists L Ω B w h
  have hpl := (guard_of plainRec b1 b2 hWA (Or.inr (Or.inr hpotL)) hrc hσ).1
  obtain ⟨j, L0, hj, hBw⟩ := GlobalTheory.PlaceBridge.exists_locBridge l L Ω w B hw h
  obtain ⟨Bw, hBj, -⟩ := hBw L0 le_rfl
  have hInd : Induces Bw := fun x => by rw [hBj]; exact hj x
  have hJ := ((hloc w σ hσ).2 hpl B h _ Bw hInd).2 (Bw.j.comp (algebraMap L Ω)) Bw.Kw (AlgHom.id _ _) fun _ => rfl
  have hBQ : IsPlaceOver B (w.under (𝓞 ℚ)) := fun x => by
    rw [IsScalarTower.algebraMap_apply ℚ L Ω]
    exact h (algebraMap (𝓞 ℚ) (𝓞 L) x)
  obtain ⟨-, κ, ⟨g, hg⟩, hI⟩ := hall _ hw0 B hBQ
  let ρ : ↥(Dec (F := L) B) →* ↥(Dec (F := ℚ) B) :=
    ((galEmb ℚ L Ω).comp (Dec (F := L) B).subtype).codRestrict _ fun s => s.2
  have hH2 := jumpsOpen ![(e : ℤ), -(e : ℤ)] _ hWL B Bw hInd (fun i => (κ i).comp ρ) (N.comap (galEmb ℚ L Ω))
    (hN.preimage (continuous_restrictScalarsHom ℚ L Ω)) ⟨g, fun s => hg (ρ s)⟩ (fun i s hs => hI i (ρ s) ⟨hs.1, hs.2⟩) _ _ hJ
  obtain ⟨μ, hμ, -⟩ := hreg v
  have hμQ : Q.HasInfChar (ι.toRingHom.comp (Bw.j.comp (algebraMap L Ω))) μ :=
    b3 _ μ (a3 _ μ (by rwa [Subsingleton.elim (InfinitePlace.mk _) v]))
  have hW2 := hwt (Bw.j.comp (algebraMap L Ω))
  rw [hH2, CG.HasInfChar.infChar_eq (π := CG.mk Q) hμQ] at hW2
  have hμeq : μ = infOf ![(e : ℤ), -(e : ℤ)] := by
    have h := congrArg (Multiset.map fun z : ℂ => (((2 : ℕ) : ℂ) - 1) / 2 - z) hW2
    simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id', Int.cast_neg, sub_neg_eq_add] at h
    exact h.symm
  rwa [hμeq] at hμ

end UpperTheory.V.Z.Win.RR
