module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfAssembleMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurent
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct
namespace GlobalTheory.RedPhiProof

theorem ringHom_eq_of_agree {O k : Type} [CommRing O] [CommRing k] (f g : O⟦X⟧ →+* k⟦X⟧)
    (hC : ∀ c : O, f (PowerSeries.C c) = g (PowerSeries.C c))
    (hX : f PowerSeries.X = g PowerSeries.X) (hd : PowerSeries.X ∣ f PowerSeries.X) (a : O⟦X⟧) :
    f a = g a := by

  have hpoly : ∀ p : Polynomial O, f (p : O⟦X⟧) = g (p : O⟦X⟧) := by
    intro p
    have hfg : f.comp (Polynomial.coeToPowerSeries.ringHom) = g.comp (Polynomial.coeToPowerSeries.ringHom) :=
      Polynomial.ringHom_ext (fun c => by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hC c)
        (by simpa [Polynomial.coeToPowerSeries.ringHom_apply] using hX)
    simpa [Polynomial.coeToPowerSeries.ringHom_apply] using RingHom.congr_fun hfg p
  refine PowerSeries.ext fun n => ?_
  rw [← sub_eq_zero, ← map_sub]

  have htail : PowerSeries.X ^ (n + 1) ∣ a - (PowerSeries.trunc (n + 1) a : O⟦X⟧) := by
    refine PowerSeries.X_pow_dvd_iff.mpr fun m hm => ?_
    rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]
  obtain ⟨b, hb⟩ := htail
  have ha : a = (PowerSeries.trunc (n + 1) a : O⟦X⟧) + PowerSeries.X ^ (n + 1) * b := by
    rw [← hb]; ring

  have hdiv : PowerSeries.X ^ (n + 1) ∣ f a - g a := by
    have e : f a - g a = f PowerSeries.X ^ (n + 1) * (f b - g b) := by
      conv_lhs => rw [ha]
      rw [map_add (f := _), map_add (f := _), hpoly, map_mul, map_mul, map_pow, map_pow, ← hX]
      ring
    rw [e]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hd _) _
  exact PowerSeries.X_pow_dvd_iff.mp hdiv n (Nat.lt_succ_self n)

theorem red_phi (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [Field k] [Algebra O k] [CharP k l]
    (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (h : φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1) (a : O⟦X⟧) :
    ((PowerSeries.map (algebraMap O k) (φ₀ a) : k⟦X⟧) : k⸨X⸩) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l ((PowerSeries.map (algebraMap O k) a : k⟦X⟧) : k⸨X⸩) := by
  have hc : PowerSeries.constantCoeff ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) = 0 := by simp
  have hs : PowerSeries.HasSubst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hc

  have key : PowerSeries.map (algebraMap O k) (φ₀ a) =
      (PowerSeries.map (algebraMap O k) a).subst ((1 + PowerSeries.X : k⟦X⟧) ^ l - 1) := by
    have e := ringHom_eq_of_agree ((PowerSeries.map (algebraMap O k)).comp φ₀.toRingHom)
      ((PowerSeries.substAlgHom hs).toRingHom.comp (PowerSeries.map (algebraMap O k)))
      (fun c => by
        have h1 : φ₀ (PowerSeries.C c) = PowerSeries.C c := by simpa using φ₀.commutes c
        have h2 := (PowerSeries.substAlgHom hs).commutes (algebraMap O k c)
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, PowerSeries.map_C]
        simpa using h2.symm)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h, PowerSeries.map_X,
          PowerSeries.substAlgHom_X]
        simp)
      (by
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h]
        exact PowerSeries.X_dvd_iff.mpr (by simp))
      a
    simpa [PowerSeries.coe_substAlgHom] using e
  rw [key, GlobalTheory.PsiShiftProof.phi_eq_subst, GlobalTheory.PsiLemmaCompare.substHom_coe]

end GlobalTheory.RedPhiProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualRepKerIsOpen
section
noncomputable section

namespace GlobalTheory.TypeLeaf

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem isOpen_ker_map_of_isOpen_ker {Γ A B : Type} [Group Γ] [TopologicalSpace Γ] [CommRing A] [CommRing B]
    [TopologicalSpace A] [IsTopologicalRing A] {n : ℕ} (f : A →+* B) (hf : IsOpen ((RingHom.ker f : Ideal A) : Set A))
    (ρ : Γ →* GL (Fin n) A) (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A))) :
    IsOpen (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) := by
  classical

  let U : Set (Matrix (Fin n) (Fin n) A) :=
    {M | ∀ i j, M i j - (1 : Matrix (Fin n) (Fin n) A) i j ∈ RingHom.ker f}
  have hU : IsOpen U := by
    have : U = ⋂ i, ⋂ j, (fun M : Matrix (Fin n) (Fin n) A =>
        M i j - (1 : Matrix (Fin n) (Fin n) A) i j) ⁻¹' ((RingHom.ker f : Ideal A) : Set A) := by
      ext M; simp [U]
    rw [this]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact hf.preimage ((continuous_id.matrix_elem i j).sub continuous_const)

  have hker : (((Matrix.GeneralLinearGroup.map f).comp ρ).ker : Set Γ) =
      (fun g => ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A)) ⁻¹' U := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.comp_apply, Set.mem_preimage, U,
      Set.mem_ofPred_eq, RingHom.mem_ker, map_sub, sub_eq_zero]
    rw [Units.ext_iff]
    change f.mapMatrix ((ρ g : GL _ _) : Matrix (Fin n) (Fin n) A) =
      ((1 : GL (Fin n) B) : Matrix (Fin n) (Fin n) B) ↔ _
    rw [Units.val_one, ← Matrix.ext_iff]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [hker]
  exact hU.preimage hρ

theorem redF_ker_isOpen (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i))
    (hρ : Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))) :
    IsOpen ((redF D i ρ).ker : Set (G D.host.E D.nd.Om)) := by

  have hk : ((RingHom.ker ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) : Ideal (D.nd.O i)) :
      Set (D.nd.O i)) = (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    ext x
    simp [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff]
  have hm : IsOpen (IsLocalRing.maximalIdeal (D.nd.O i) : Set (D.nd.O i)) := by
    simpa using (isAdic_iff.mp (D.nd.O_adic i)).1 1
  exact isOpen_ker_map_of_isOpen_ker _ (hk ▸ hm) ρ hρ

end GlobalTheory.TypeLeaf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.CycRing

theorem letφ_pow_const {O : Type} [CommRing O] {n : ℕ} (f : PowerSeries O →ₐ[O] PowerSeries O)
    (k : ℕ) (c : PowerSeries O) :
    (letφ (n := n) f ^ k) (fun _ => c) = fun _ => (f ^ k) c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih]
    funext i
    simp [letφ]

theorem XX_ne_zero (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (hl : (l : O) ≠ 0) (s : ℕ) : GlobalTheory.Cyc.XX l O s ≠ 0 := by
  intro h
  have h1 := congrArg (PowerSeries.coeff 1) h
  rw [GlobalTheory.Cyc.XX, map_sub, PowerSeries.coeff_one_pow] at h1
  simp [PowerSeries.coeff_one] at h1
  exact hl h1.1


set_option maxHeartbeats 1000000 in
theorem rings_cyclotomic : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ (∀ g, W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l])) ∧ (∀ i, W.X i = GlobalTheory.Cyc.XX l ↥(OL LL) s) ∧ (∀ i, W.Q i = GlobalTheory.Cyc.QQ l ↥(OL LL) s) ∧ ‖(χ W.gam : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) ∧ ∀ u : ℤ_[l]ˣ, ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(s : ℤ)) → ∃ g, χ g = u := by
  intro D HW l _ K s LL h W
  obtain ⟨χ₀, hχ₀, -, honto⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l (D.loc l)
  obtain ⟨hdvr, hcomp, hl0, hlu, -⟩ := GlobalTheory.Per.integers_completeDVR l LL
  have hWs : W.s = s := (HW l).W_s K s LL h
  clear_value W
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hcoe : ∀ z : ℤ_[l], algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z)
      = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
    intro z
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    rfl
  have hinjO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    have := congrArg (algebraMap ↥(OL LL) ↥LL.1) hab
    rw [hcoe, hcoe] at this
    exact Subtype.ext ((algebraMap ℚ_[l] ↥LL.1).injective this)
  have hres : ∀ g : ↥(GK K), algebraMap ℤ_[l] ↥(OL LL) (χ₀ (g : GQ l) : ℤ_[l])
      = (W.χΓ (W.resΓ g) : ↥(OL LL)) := by
    intro g
    apply hinjO
    rw [hcoe, W.χΓ_res, hχ₀, (D.loc l).PD_χ]
  choose sec hsec using W.resΓ_onto
  have hsec' : ∀ g : W.Gam, algebraMap ℤ_[l] ↥(OL LL) (χ₀ (sec g : GQ l) : ℤ_[l])
      = (W.χΓ g : ↥(OL LL)) := fun g => by rw [hres, hsec]
  let χ : W.Gam →* ℤ_[l]ˣ := MonoidHom.mk' (fun g => χ₀ (sec g : GQ l)) (fun a b => by
    apply Units.ext
    apply hinj
    rw [Units.val_mul, map_mul, hsec', hsec', hsec', map_mul, Units.val_mul])
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL)) := hsec'
  have hφX : W.φ₀ PowerSeries.X = (1 + PowerSeries.X) ^ l - 1 := by
    rw [W.φ₀_X, W.q₀_def, hp]
  have hact : ∀ g, W.φ₀ = GlobalTheory.Cyc.phi l ↥(OL LL) ∧ W.γ₀ g = GlobalTheory.Cyc.act l ↥(OL LL) (χ g : ℤ_[l]) :=
    fun g => GlobalTheory.Cyc.act_unique l ↥(OL LL) hl0 hlu (W.γ₀ g) W.φ₀ (χ g : ℤ_[l]) hφX (W.γ₀_comm g)
      (W.γ₀_X g).1 (by rw [(W.γ₀_X g).2, hχ])
  have hφ := (hact 1).1
  have hX : W.X = fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s := by
    rw [← GlobalTheory.Cyc.Series.phi_pow_X, ← hφ, ← letφ_pow_const, LocWach.X, hWs]
    rfl
  refine ⟨χ, hχ, hφ, fun g => (hact g).2, fun i => by rw [hX], fun i => ?_, ?_, ?_⟩
  · have h1 := congrFun W.φA_X i
    rw [hX, Pi.mul_apply] at h1
    have h2 : W.φA (fun _ => GlobalTheory.Cyc.XX l ↥(OL LL) s) i = W.φ₀ (GlobalTheory.Cyc.XX l ↥(OL LL) s) := by
      simp [LocWach.φA, letφ]
    rw [h2, hφ, GlobalTheory.Cyc.Series.phi_XX] at h1
    exact (mul_left_cancel₀ (XX_ne_zero l _ hl0 s) h1).symm
  · have h1 := W.gam_gen
    rw [hWs, ← hχ, hcoe] at h1
    have h2 := ((GlobalTheory.HWL.NormVal.locPrime_v_normalised l (D.loc l) LL).1 _ (s : ℚ)).1 (by exact_mod_cast h1)
    have h3 : ((algebraMap ℚ_[l] ↥LL.1 ((χ W.gam : ℤ_[l]) : ℚ_[l]) - 1 : ↥LL.1) : Om l)
        = algebraMap ℚ_[l] (Om l) (((χ W.gam : ℤ_[l]) - 1 : ℤ_[l]) : ℚ_[l]) := by
      rw [PadicInt.coe_sub, PadicInt.coe_one, map_sub, map_one]
      rfl
    rw [h3, norm_algebraMap'] at h2
    rw [PadicInt.norm_def, h2, ← Real.rpow_intCast]
    push_cast
    rfl
  · intro u hu
    have hd : (l : ℤ_[l]) ^ s ∣ (u : ℤ_[l]) - 1 :=
      Ideal.mem_span_singleton.1 ((PadicInt.norm_le_pow_iff_mem_span_pow _ s).1 hu)
    obtain ⟨g, hg, hgu⟩ := honto K s h.2.2.1 u hd
    refine ⟨W.resΓ ⟨g, hg⟩, Units.ext (hinj ?_)⟩
    rw [hχ, ← hres, hgu]

end GlobalTheory.NL.CycRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistableLinearFormOnConstants
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem exists_phiSt_invariant_nondegenerate_linearForm :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), ∃ lam : Bst P →ₗ[ℚ_[l]] ℚ_[l], (∀ c : ↥(K0 K), lam (phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) = lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c))) ∧ ∀ c : ↥(K0 K), (∀ c' : ↥(K0 K), lam (Polynomial.C (algebraMap ↥(K0 K) P.R.B c') * Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = 0) → c = 0 := by
  intro l _ P K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := (P.PD K).finK₀
  haveI : Nontrivial P.R.B := by
    refine ⟨⟨(P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h, map_zero]
    exact Submodule.zero_mem _

  let ι : ↥(K0 K) →ₗ[ℚ_[l]] Bst P :=
    ((Polynomial.monomial 0 : P.R.B →ₗ[P.R.B] Polynomial P.R.B).restrictScalars ℚ_[l]).comp
      (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) P.R.B).toLinearMap
  have hι : ∀ c, ι c = Polynomial.C (algebraMap ↥(K0 K) P.R.B c) := fun c => by
    simp [ι, Polynomial.monomial_zero_left]
  have hinj : Function.Injective ι := by
    intro a b hab
    rw [hι, hι] at hab
    exact (algebraMap ↥(K0 K) P.R.B).injective (Polynomial.C_injective hab)

  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.mpr hinj)
  have hgι : ∀ c, g (ι c) = c := fun c => LinearMap.congr_fun hg c
  refine ⟨(Algebra.trace ℚ_[l] ↥(K0 K)).comp g, ?_, ?_⟩
  ·
    intro c
    have hφ : phiSt P (Polynomial.C (algebraMap ↥(K0 K) P.R.B c)) = ι ((P.PD K).σ c) := by
      have hC : ∀ b : P.R.B, phiSt P (Polynomial.C b) = Polynomial.C (P.φB b) := fun b => by
        simp [phiSt, stHom]
      rw [hC, ← P.PD_φ K, (P.PD K).φ_K₀, hι]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hφ, ← hι, hgι, hgι]
    exact Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective (P.PD K).σ (P.PD K).σ_bij) c
  ·
    intro c h
    by_contra hc
    have h1 := h c⁻¹
    rw [← map_mul, ← map_mul, ← hι, LinearMap.comp_apply, hgι, inv_mul_cancel₀ hc] at h1
    have h2 : Algebra.trace ℚ_[l] ↥(K0 K) 1 = (Module.finrank ℚ_[l] ↥(K0 K) : ℚ_[l]) := by
      rw [← map_one (algebraMap ℚ_[l] ↥(K0 K)), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
    rw [h2] at h1
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') h1

end GlobalTheory.PMon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShiftedJumpUpperBoundLeTwistBound
section
namespace GlobalTheory

open GlobalTheory.PositionData

theorem hS_le_bound : ∀ (t : ℕ) (up : Bool) (Fl Fc : Finset ℤ) (η S B W0 : ℝ), 1 ≤ t → (t : ℝ) ≤ η → 0 ≤ B → 0 ≤ S →
    (∀ z ∈ Fl, |(z : ℝ) - ((t : ℝ) - 1) / 2| ≤ η ∧ 2 * B + (t : ℝ) / 2 + 3 ≤ |(z : ℝ) - ((t : ℝ) - 1) / 2|) →
    (∀ z ∈ Fc, W0 ≤ (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ∧
      (if up then (z : ℝ) - ((t : ℝ) - 1) / 2 else ((t : ℝ) - 1) / 2 - z) ≤ W0 + S + η + 1) →
    2 * B + (t : ℝ) / 2 + 3 ≤ W0 →
    ((GlobalTheory.PositionData.hS up t Fl Fc : ℕ) : ℝ) ≤ W0 + S + 2 * η + 3 := by
  intro t up Fl Fc η S B W0 ht htη hB hS0 hFl hFc hW
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hFl' : ∀ z ∈ Fl, ((t : ℝ) - 1) / 2 - η ≤ (z : ℝ) ∧ (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    intro z hz
    have h := (hFl z hz).1
    rw [abs_le] at h
    constructor <;> linarith [h.1, h.2]
  have castToNat : ∀ x : ℤ, ((x.toNat : ℕ) : ℝ) = max (x : ℝ) 0 := by
    intro x
    have h : ((x.toNat : ℕ) : ℤ) = max x 0 := Int.toNat_eq_max x
    rw [← Int.cast_natCast, h]
    push_cast
    rfl
  have hmn : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, a ≤ (y : ℝ)) →
      a ≤ ((s.min' H : ℤ) : ℝ) := fun s H a h => h _ (Finset.min'_mem s H)
  have hmx : ∀ (s : Finset ℤ) (H : s.Nonempty) (a : ℝ), (∀ y ∈ s, (y : ℝ) ≤ a) →
      ((s.max' H : ℤ) : ℝ) ≤ a := fun s H a h => h _ (Finset.max'_mem s H)

  have hmxLo : ((mxLo t Fl : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + η := by
    apply hmx
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hy
    · push_cast; linarith
    · exact (hFl' y hy).2
  cases up
  ·
    have hFc' : ∀ z ∈ Fc, ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ (z : ℝ) := by
      intro z hz
      have h := (hFc z hz).2
      simp only [Bool.false_eq_true, if_false] at h
      linarith
    have h1 : ((t : ℝ) - 1) / 2 - W0 - S - η - 1 ≤ ((mnAll Fl Fc : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).1]
      · exact hFc' y hy
    have h0 : mnAll Fl Fc ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS false Fl Fc : ℕ) : ℤ) = 1 - mnAll Fl Fc := by
      simp only [wS, Bool.false_eq_true, if_false]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, Bool.false_eq_true, if_false]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith
  ·
    have hFc' : ∀ z ∈ Fc, (z : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      intro z hz
      have h := (hFc z hz).2
      simp only [if_true] at h
      linarith
    have h1 : ((mxAll t Fl Fc : ℤ) : ℝ) ≤ ((t : ℝ) - 1) / 2 + W0 + S + η + 1 := by
      apply hmx
      intro y hy
      rw [Finset.mem_insert, Finset.mem_union] at hy
      rcases hy with rfl | hy | hy
      · push_cast; linarith
      · linarith [(hFl' y hy).2]
      · exact hFc' y hy
    have h2 : ((t : ℝ) - 1) / 2 - η ≤ ((mnLo Fl : ℤ) : ℝ) := by
      apply hmn
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · push_cast; linarith
      · exact (hFl' y hy).1
    have h0 : mnLo Fl ≤ 0 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
    have hw : ((wS true Fl Fc : ℕ) : ℤ) = 1 - mnLo Fl := by
      simp only [wS, if_true]
      exact Int.toNat_of_nonneg (by omega)
    simp only [PositionData.hS, if_true]
    rw [castToNat, hw]
    apply max_le
    · push_cast; linarith
    · linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableLeSpanInvariantsOfSemilinearFamily
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present GlobalTheory.RedFun Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries TensorProduct

namespace GlobalTheory

private lemma span_range_eval_embeddings_eq_whole (F D : Type) [Field F] [Fintype D] (σ : D → (F →+* F))
    (hσ : Function.Injective σ) :
    Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) = ⊤ := by

  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli : LinearIndependent F (fun d : D => ((σ d : F →* F) : F → F)) := by
    refine (linearIndependent_monoidHom F F).comp (fun d => (σ d : F →* F)) ?_
    intro a b h
    apply hσ
    ext x
    exact congrArg (fun g : F →* F => g x) h
  rw [Fintype.linearIndependent_iff] at hli
  have hzero : ∑ d, f (Pi.single d 1) • ((σ d : F →* F) : F → F) = 0 := by
    funext c
    have hc : (fun d : D => σ d c) ∈ LinearMap.ker f := hle (Submodule.subset_span ⟨c, rfl⟩)
    rw [LinearMap.mem_ker] at hc
    have hdecomp : (fun d : D => σ d c) = ∑ d, σ d c • Pi.single d (1 : F) := by
      ext e
      simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hdecomp, map_sum] at hc
    simp only [map_smul, smul_eq_mul] at hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hc]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [mul_comm]
  have hall := hli _ hzero
  apply hf0
  ext d
  simpa using hall d

theorem stable_le_span_invariants_of_semilinear_family :
    ∀ (F M D : Type) [Field F] [AddCommGroup M] [Module F M] [Fintype D] (σ : D → (F →+* F)) (t : D → (M →+ M)) (V : Submodule F M), Function.Injective σ → (∀ d (c : F), ∀ y ∈ V, t d (c • y) = σ d c • t d y) → (∀ d, ∀ y ∈ V, t d y ∈ V) → (∀ d, ∀ y ∈ V, t d (∑ d', t d' y) = ∑ d', t d' y) → (∃ d, ∀ y ∈ V, t d y = y) → V ≤ Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y} := by
  classical
  rintro F M D _ _ _ _ σ t V hσ hsemi hV hinv ⟨d₀, hd₀⟩ y hy
  let W := Submodule.span F {y | y ∈ V ∧ ∀ d, t d y = y}
  let Φ : (D → F) →ₗ[F] M :=
    { toFun := fun w => ∑ d, w d • t d y
      map_add' := by
        intro a b
        simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp [Finset.smul_sum, smul_smul] }
  have hmem : ∀ c : F, (∑ d, σ d c • t d y) ∈ W := by
    intro c
    apply Submodule.subset_span
    have hcy : c • y ∈ V := V.smul_mem c hy
    have heq : ∑ d, σ d c • t d y = ∑ d, t d (c • y) :=
      Finset.sum_congr rfl fun d _ => (hsemi d c y hy).symm
    rw [heq]
    exact ⟨V.sum_mem fun d _ => hV d _ hcy, fun d => hinv d _ hcy⟩
  have hle : Submodule.span F (Set.range (fun c : F => fun d : D => σ d c)) ≤ W.comap Φ := by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact hmem c
  rw [span_range_eval_embeddings_eq_whole F D σ hσ] at hle
  have h1 : Φ (Pi.single d₀ 1) ∈ W := hle Submodule.mem_top
  have h2 : Φ (Pi.single d₀ 1) = y := by
    show ∑ d, (Pi.single d₀ (1 : F) : D → F) d • t d y = y
    rw [Finset.sum_eq_single d₀]
    · simp [hd₀ y hy]
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [h2] at h1
  exact h1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinfStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wach_lattice_sandwich_Ainf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (M0 h0 : ℕ) (N : Submodule (LetA S.O S.n) (S.W.DD T)), WClauses S E T M0 h0 N → (∀ y ∈ N, (S.inclR (E.io S.W.X)) ^ M0 • E.jD T y ∈ LinearMap.range (TWincl S.inclR T)) ∧ ∀ t : ↥T.L.T, (S.inclR (E.io S.W.X)) ^ h0 • ((1 : S.RW) ⊗ₜ[S.O] t) ∈ Submodule.span S.O {z : TW S.RW T | ∃ (a : S.RA), ∃ y ∈ N, z = S.inclR a • E.jD T y} := by
  first | exact @GlobalTheory.Sandwich.sandwich | exact GlobalTheory.Sandwich.sandwich | (intros; apply GlobalTheory.Sandwich.sandwich <;> assumption)
end

