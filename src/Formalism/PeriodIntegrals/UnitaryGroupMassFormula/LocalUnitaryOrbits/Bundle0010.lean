module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.TwoNeZeroV
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfRedU
section
noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem countU_of_redU
    (hFull : ∃ L : Submodule (𝓞 E) (Fin n → E),
      Submodule.IsFullLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (a : ℕ) (Y : TupV (E := E) v n a) (hR : RedU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y :=
  countU_of_bas' σ J ψ v Λ a Y (latBasO_holds σ J ψ v Λ hFull a Y) (resIdx_holds v) hR

end PI.OmLocU
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ExistsPerpNeZero
section
noncomputable section

namespace PI.OmLocU.UnN

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG PI.OmLocU.Orb PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

theorem hR_smul_right_F (x w : Fin n → Fv F v ⊗[F] E) (c : Fv F v) :
    hR (Fv F v) σ J x (c • w) = c • hR (Fv F v) σ J x w := by
  rw [← algebraMap_smul (Fv F v ⊗[F] E) c w, hR_smul_right, Algebra.smul_def]

def perpMap {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) :
    (Fin n → Fv F v ⊗[F] E) →ₗ[Fv F v] (ι → Fv F v ⊗[F] E) where
  toFun w i := hR (Fv F v) σ J (X i) w
  map_add' x y := funext fun i => hR_add_right' σ J v (X i) x y
  map_smul' c w := funext fun i => hR_smul_right_F σ J v (X i) w c

theorem exists_perp_ne_zero (hcm : IsCMExt F E σ) {ι : Type} [Fintype ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hc : Fintype.card ι < n) : ∃ w : Fin n → Fv F v ⊗[F] E, w ≠ 0 ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0 := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h2 : Module.finrank F E = 2 := hcm.2.2.1
  have hlt : Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E) < Module.finrank (Fv F v) (Fin n → Fv F v ⊗[F] E) := by
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
    simp only [Module.finrank_baseChange, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    omega
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := perpMap σ J v X) hlt
  obtain ⟨w, hw, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨w, hne, fun i => congrFun (LinearMap.mem_ker.1 hw) i⟩

theorem primPerp_holds : PrimPerp σ J ψ v Λ := by
  classical
  intro hstd hL hsd hun ι _ _ X hX hUX hc
  obtain ⟨ϖ, hϖ⟩ := unifEx_holds v
  have hv : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  obtain ⟨L, hLat, rfl⟩ := hL
  let M := latLoc (E := E) v (L : Set (Fin n → E))
  have hfg : M.FG := basLat_fg v L hLat
  have hspan : Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) = ⊤ := by
    have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
    have hopen := LocMassOrdLat.isOpen_latLoc σ J v (L : Set (Fin n → E)) hsd hfg
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht, htx⟩ := LocMassOrdLat.exists_scale v
      (hopen.mem_nhds M.zero_mem) (fun _ : Unit => x)
    have hmem : t • x ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
      Submodule.subset_span (htx ())
    have hx : t⁻¹ • (t • x) ∈ Submodule.span (Fv F v) (M : Set (Fin n → Fv F v ⊗[F] E)) :=
      Submodule.smul_mem _ t⁻¹ hmem
    rwa [inv_smul_smul₀ ht] at hx
  have : Submodule.IsFullLattice (Fv F v) M :=
    { toIsLattice := Submodule.IsLattice.of_fg (Fv F v) hfg, span_eq_top := hspan }
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 hfg
  have : Module.Free (v.adicCompletionIntegers F) M := Submodule.IsLattice.free (Fv F v) M
  let m := Module.finrank (v.adicCompletionIntegers F) M
  let b : Module.Basis (Fin m) (v.adicCompletionIntegers F) M := Module.finBasis _ _
  let B := b.extendOfIsFullLattice (Fv F v)
  have hB (i : Fin m) : B i = (b i : Fin n → Fv F v ⊗[F] E) :=
    Module.Basis.extendOfIsFullLattice_apply (Fv F v) b i
  have hmem (x : Fin n → Fv F v ⊗[F] E) : x ∈ M ↔
      ∃ c : Fin m → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • B i := by
    constructor
    · intro hx
      refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg (fun y : M => (y : Fin n → Fv F v ⊗[F] E)) (b.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => by
        rw [hB]
        rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem M fun i _ => by
        rw [hB]
        exact M.smul_mem (c i) (b i).2
  have hsymm := Module.Basis.equivFun_symm_apply B
  obtain ⟨w, hw0, hwp⟩ := exists_perp_ne_zero σ J v hstd.1 X hc
  set c := B.equivFun w with hcdef
  have hcw : w = ∑ i, c i • B i := by rw [← hsymm, hcdef, LinearEquiv.symm_apply_apply]
  have hcne : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    rw [hcw]
    simp [h]
  obtain ⟨i0, hi0⟩ := hcne
  have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i0, Finset.mem_univ _⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (c i)) hne
  have hcj : c j ≠ 0 := by
    intro h
    have h1 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h1
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h1 zero_le))
  have hvj : Valued.v (c j) ≠ 0 := (Valuation.ne_zero_iff _).2 hcj
  set p := (c j)⁻¹ • w with hp
  have hcp : B.equivFun p = (c j)⁻¹ • c := by rw [hp, map_smul]
  have hpmem : p ∈ latLoc (E := E) v (L : Set (Fin n → E)) := by
    refine (hmem p).2 ⟨fun i => ⟨(c j)⁻¹ * c i, ?_⟩, ?_⟩
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
      calc (Valued.v (c j))⁻¹ * Valued.v (c i) ≤ (Valued.v (c j))⁻¹ * Valued.v (c j) :=
            mul_le_mul' le_rfl (hj i (Finset.mem_univ _))
        _ = 1 := inv_mul_cancel₀ hvj
    · rw [← hsymm]
      change p = B.equivFun.symm ((c j)⁻¹ • c)
      rw [← hcp, LinearEquiv.symm_apply_apply]
  refine ⟨ϖ, hϖ, p, ⟨hpmem, fun i => ?_⟩, ?_⟩
  · rw [hp, hR_smul_right_F, hwp i, smul_zero]
  · intro hin
    rw [sc_eq, algebraMap_smul] at hin
    obtain ⟨d, hd⟩ := (hmem _).1 hin
    have hd' : ϖ⁻¹ • p = B.equivFun.symm (fun i => (d i : Fv F v)) := by rw [hsymm]; exact hd
    have hcoord := congrFun (congrArg B.equivFun hd') j
    rw [LinearEquiv.apply_symm_apply, map_smul, hcp] at hcoord
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    rw [inv_mul_cancel₀ hcj, mul_one] at hcoord
    have hint : ϖ⁻¹ ∈ v.adicCompletionIntegers F := by rw [hcoord]; exact (d j).2
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hint
    have h1 : Valued.v (ϖ * ϖ⁻¹) ≤ WithZero.exp (-1 : ℤ) := by
      rw [map_mul, hv]
      calc WithZero.exp (-1 : ℤ) * Valued.v ϖ⁻¹ ≤ WithZero.exp (-1 : ℤ) * 1 := mul_le_mul' le_rfl hint
        _ = _ := mul_one _
    rw [mul_inv_cancel₀ hϖ0, map_one] at h1
    exact absurd h1 (by decide)

end PI.OmLocU.UnN
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OBas1OfUnitV
section
noncomputable section

namespace PI.OmLocU.Red

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Formalism.UG
open PI.VolStabSW PI.OmLocU
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def OBas1 : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∃ e : Fin n → Fin n → Fv F v ⊗[F] E, Orb.IsOBas v Λ e ∧ gramR (Fv F v) σ J e = 1

def ResAlg : Prop :=
  StdHyp σ J ψ → UnramAt (E := E) v → ∀ ϖ : Fv F v, IsUnif v ϖ →
    ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Ideal.absNorm v.asIdeal ∧
      ((etaV (E := E) v = -1 ∧ ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ' : K ≃ₐ[k] K)
          (π : OR (E := E) v →+* K),
          (∀ x, σ' (σ' x) = x) ∧ Module.finrank k K = 2 ∧ σ' ≠ AlgEquiv.refl ∧
          IsRes σ v ϖ (σ' : K →+* K) π) ∨
       (etaV (E := E) v = 1 ∧ ∃ π : OR (E := E) v →+* k × k,
          IsRes σ v ϖ (RingEquiv.prodComm (R := k) (S := k)).toRingHom π))

theorem oBas1_of_unitV (hU : Orb.UnitV σ J ψ v Λ) : OBas1 σ J ψ v Λ := by
  intro hstd hL hsd hun
  obtain ⟨e, he, -, he1, hsp⟩ := Orb.orthoGen σ J ψ v Λ hU hstd hL hsd hun n (Fin 0)
    (fun i => i.elim0) (by simp) (fun i => i.elim0) ⟨1, (Orb.oSub v).1, by simp [Matrix.det_isEmpty]⟩
  refine ⟨e, fun x => ⟨fun hx => hsp x ⟨hx, fun i => i.elim0⟩, ?_⟩, he1⟩
  rintro ⟨c, hc, rfl⟩
  exact Submodule.sum_mem _ fun i _ => Orb.oSmul v Λ hL (c i) (hc i) (e i) (he i).1

theorem det_red {K : Type} [CommRing K] (π : OR (E := E) v →+* K) {a : ℕ}
    (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) (hT : ∀ i j, T i j ∈ OR (E := E) v)
    {w : Fv F v ⊗[F] E} (hw : w ∈ OEv (E := E) v) (hd : T.det * w = 1) :
    IsUnit (Matrix.det (fun i j => π ⟨T i j, hT i j⟩)) := by
  set Ts : Matrix (Fin a) (Fin a) (OR (E := E) v) := fun i j => ⟨T i j, hT i j⟩
  have hdet : ((Ts.det : OR (E := E) v) : Fv F v ⊗[F] E) = T.det := by
    rw [show ((Ts.det : OR (E := E) v) : Fv F v ⊗[F] E) = (OR (E := E) v).subtype Ts.det from rfl,
      RingHom.map_det]
    rfl
  have hm : Ts.det * ⟨w, hw⟩ = 1 := by
    apply Subtype.ext
    rw [Subring.coe_mul, hdet]
    exact hd
  have hu : IsUnit Ts.det := ⟨⟨Ts.det, ⟨w, hw⟩, hm, by rw [mul_comm]; exact hm⟩, rfl⟩
  have := hu.map π
  rw [RingHom.map_det] at this
  exact this

theorem redU_of (hU : Orb.UnitV σ J ψ v Λ) (hR : ResAlg σ J ψ v) (a : ℕ) (Y : TupV (E := E) v n a) :
    RedU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hstd := hG.1
  have hcm := hstd.1
  have hJ : ∀ i j, σ (J j i) = J i j := hstd.2.1.1
  obtain ⟨e, he, he1⟩ := oBas1_of_unitV σ J ψ v Λ hU hstd hG.2.1 hG.2.2.1 hG.2.2.2.1
  have hT := gY_mem σ J ψ v Λ hG
  obtain ⟨w, hw, -, hd⟩ := hG.2.2.2.2.2.2
  have hconj : ∀ i j, gramR (Fv F v) σ J Y i j = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (gramR (Fv F v) σ J Y j i) := fun i j =>
    (Orb.hR_conj σ J v hcm hJ (Y j) (Y i)).symm
  obtain ⟨k, _, _, hk, h⟩ := hR hstd hG.2.2.2.1 ϖ hϖ
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  rcases h with ⟨hη, K, _, _, σ', π, hσ, h2, hne, hπ⟩ | ⟨hη, π, hπ⟩
  · refine Or.inl ⟨hη, K, inferInstance, inferInstance, σ', 1, fun i j => π ⟨_, hT i j⟩, hσ, h2, hne, ?_,
      by simp, ?_, det_red v π _ hT hw hd,
      card_cls σ J v Λ hcm hJ hG.2.2.1 he he1 (σ' : K →+* K) π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm
  · refine Or.inr ⟨hη, 1, fun i j => π ⟨_, hT i j⟩, ?_, by simp, ?_, det_red v π _ hT hw hd,
      card_cls σ J v Λ hcm hJ hG.2.2.1 he he1 (RingEquiv.prodComm (R := k) (S := k)).toRingHom π hπ _ hT⟩
    · intro i j
      by_cases h : i = j
      · subst h; ext <;> simp
      · ext <;> simp [h, Ne.symm h]
    · intro i j
      exact (hπ.2.2 _ _ (hconj i j)).symm

end PI.OmLocU.Red
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermSmulRight
section
noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

section DualH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem b_tr_sig (hcm : IsCMExt F E σ) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ w) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  apply (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective
  rw [trace_v v σ hinv hnt hfin, trace_v v σ hinv hnt hfin, sigR_sigR v σ hinv, add_comm]

def hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i j c + Matrix.single j i (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c), fun p q => by
    simp only [Matrix.add_apply, Matrix.single_apply]
    rw [map_add (f := _), apply_ite (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ), apply_ite (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ), map_zero, sigR_sigR v σ hinv, add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl⟩

theorem coe_hm {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) (c : Fv F v ⊗[F] E) :
    (hm σ v hinv i j c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) =
      Matrix.single i j c + Matrix.single j i (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ c) := rfl

theorem hm_mem {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (i j : Fin a) {c : Fv F v ⊗[F] E}
    (hc : c ∈ OEv (E := E) v) : hm σ v hinv i j c ∈ HO σ v a := by
  intro p q
  rw [coe_hm, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  refine Submodule.add_mem _ ?_ ?_
  · split_ifs
    · exact hc
    · exact Submodule.zero_mem _
  · split_ifs
    · exact b_sigR_mem v σ hc
    · exact Submodule.zero_mem _

theorem sum_eq_trace {a : ℕ} (M N : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :
    ∑ p, ∑ q, M p q * N q p = (M * N).trace := by
  rfl

theorem half_two : algebraMap F (Fv F v) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, one_div, inv_mul_cancel₀ two_ne_zero, map_one]

theorem half_mul (t : Fv F v) : algebraMap F (Fv F v) (1 / 2) * (t + t) = t := by
  rw [← two_mul, ← mul_assoc, half_two, one_mul]

theorem pair_hm (hcm : IsCMExt F E σ) {a : ℕ} (i j : Fin a) (c : Fv F v ⊗[F] E) (T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a (hm σ v (b_sig_sig σ hcm) i j c) T =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c * (T : Matrix (Fin a) (Fin a) _) j i) := by
  unfold pairHerm
  rw [sum_eq_trace, coe_hm, add_mul, Matrix.trace_add, Matrix.trace_single_mul, Matrix.trace_single_mul,
    smul_eq_mul, smul_eq_mul, ← T.2 i j, ← map_mul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ), map_add, b_tr_sig σ v hcm, half_mul]

theorem pairHerm_smul_right' {a : ℕ} (s : Fv F v) (S T : HermR (Fv F v) σ a) :
    pairHerm (Fv F v) σ a S (s • T) = s * pairHerm (Fv F v) σ a S T := by
  simp only [pairHerm, coe_hermSMul, Matrix.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul,
    smul_eq_mul]
  ring

theorem pair_int (hcm : IsCMExt F E σ) {a : ℕ} {S T : HermR (Fv F v) σ a} (hS : S ∈ HO σ v a) (hT : T ∈ HO σ v a) :
    pairHerm (Fv F v) σ a S T ∈ v.adicCompletionIntegers F := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin : Module.finrank F E = 2 := hcm.2.2.1
  set u := ∑ p, ∑ q, (S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) p q * (T : Matrix (Fin a) (Fin a) _) q p
    with hudef
  have hu : u ∈ OEv (E := E) v :=
    sum_mem fun p _ => sum_mem fun q _ => b_mul_mem v (hS p q) (hT q p)
  have hfix : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ u = u := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hudef, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [← S.2 p q, ← T.2 q p]
  have hsc : sc (E := E) v (pairHerm (Fv F v) σ a S T) = u := by
    have htr : sc (E := E) v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) u) = u + u := by
      rw [b_sc_eq, trace_v v σ hinv hnt hfin, hfix]
    have h2 : sc (E := E) v (algebraMap F (Fv F v) (1 / 2)) * 2 = 1 := by
      have e2 : (2 : Fv F v ⊗[F] E) = sc (E := E) v 2 := by rw [b_sc_eq, map_ofNat]
      rw [e2, b_sc_eq, b_sc_eq, ← map_mul, half_two, map_one]
    have hm2 : ∀ x y : Fv F v, sc (E := E) v (x * y) = sc (E := E) v x * sc (E := E) v y := fun x y => by
      simp only [b_sc_eq, map_mul]
    unfold pairHerm
    rw [← hudef, hm2, htr, ← two_mul, ← mul_assoc, h2, one_mul]
  exact b_int_of_sc v (hsc ▸ hu)

theorem dualH_of_perf (a : ℕ) (hP : TrPerf σ J ψ v) : DualH σ J ψ v a := by
  intro hS hU
  have hcm := hS.1
  have hd0 := dV_ne_zero v
  ext T
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_smulSub]
  constructor
  · intro h
    refine ⟨dV v • T, fun i j => ?_, by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]⟩
    rw [coe_hermSMul, Matrix.smul_apply, Algebra.smul_def]
    refine hP hS hU _ fun c hc => ?_
    have h1 := h _ (hm_mem σ v (b_sig_sig σ hcm) j i hc)
    rw [pair_hm σ v hcm] at h1
    rw [mul_left_comm, ← b_sc_eq, b_tr_sc]
    exact h1
  · rintro ⟨T', hT', rfl⟩ S hS'
    rw [pairHerm_smul_right', ← mul_assoc, mul_inv_cancel₀ hd0, one_mul]
    exact pair_int σ v hcm hS' hT'

end DualH

end PI.OmLocU.SdB
end
end

