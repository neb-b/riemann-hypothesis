module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeCharTrivOnRealSubfieldInfinityType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AutomorphicArithmetic.CyclotomicBounds.RootsOfUnity.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyLocalDensityStandardLatticeBound
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFibreFamilyHermitianLengthInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Host Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.AntiChar

theorem exists_split_place (R : Ranks) (H : Formalism.BasicNotions.Host R) :
    ∃ w : HeightOneSpectrum (𝓞 H.E), ¬ GlobalTheory.Mem.Chr.ConjPl H.conj.toRingEquiv w w ∧
      ∃ p : ℕ, p.Prime ∧ Units.torsionOrder H.E + 1 < p ∧ (p : 𝓞 H.E) ∈ w.asIdeal := by
  obtain ⟨p, hp, hp2, hmod⟩ := Nat.exists_prime_gt_modEq_one (k := H.QS * H.q * H.d) (Units.torsionOrder H.E + 1) H.condN_ne_zero
  have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p hp hmod
  have hne : {v : HeightOneSpectrum (𝓞 H.E) | ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hs]
    exact Module.finrank_pos.ne'
  obtain ⟨w, hw⟩ := hne
  obtain ⟨-, -, ⟨x, hx, hx'⟩, -⟩ := GlobalTheory.Mem.Chr.splitsC_main R H p hp hs w hw
  refine ⟨w, fun h => ?_, p, hp, hp2, hw⟩
  · have h' := (GlobalTheory.Mem.Chr.conjPl_main.2.1 R H w w).2 h
    let y : 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv x
    exact hx' y rfl ((h' x y rfl).1 hx)

theorem exists_hchar (R : Ranks) (H : Formalism.BasicNotions.Host R) (I : Type) [Fintype I] (e : I ≃ R.Psi) (z : I → ℤ) :
    ∃ χ : HChar H.E, χ.IsUnitary ∧ χ.TrivOn H.F ∧ χ.HasInf (fun i => embPsi H (e i)) (fun i => -2 * z i) ∧
      ∃ T : Finset (HeightOneSpectrum (𝓞 H.E)), ∀ v, v ∉ T → χ.UnrAt v := by
  classical
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hce : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
  have hcm' : GlobalTheory.Mem.Chr.CMData H.F c (fun i => embPsi H (e i)) :=
    ⟨hcm.real, hcm.cplx, hcm.rank, hcm.ne, hcm.bij.comp e.bijective⟩
  obtain ⟨w, hw, p, hp, hp2, hpw⟩ := exists_split_place R H
  rw [← hce] at hw
  obtain ⟨ω, -, hω⟩ := UpperTheory.Mu.tame_par w hp hp2 hpw (fun i => embPsi H (e i)) (fun i => -z i)
  obtain ⟨w', -, hw'⟩ := GlobalTheory.Mem.Chr.conjPl_main.1 H.E c.toRingEquiv w
  let θ0 : ∀ v : HeightOneSpectrum (𝓞 H.E), (𝓞 H.E ⧸ v.asIdeal)ˣ →* ℂˣ :=
    Function.update (fun _ => 1) w ω
  obtain ⟨χ, hu, ht, hi, -, hunr, -⟩ := GlobalTheory.Mem.Chr.AntiExist.exists_hecke_trivOn H.F H.E c I _ hcm' z {w} θ0
    (by
      intro v hv v' h hv'
      rw [Finset.mem_singleton] at hv hv'
      subst hv hv'
      exact hw h)
    (fun ζ hζ => by
      rw [Finset.prod_singleton]
      simp only [θ0, Function.update_self]
      exact hω ζ hζ)
  refine ⟨χ, hu, ht, hi, {w, w'}, fun v hv => hunr v ?_ ?_⟩
  · intro h
    exact hv (by rw [Finset.mem_singleton.1 h]; simp)
  · intro u hu' h
    rw [Finset.mem_singleton.1 hu'] at h
    exact hv (by rw [hw' v h]; simp)

theorem val_fin_principal (D : D7) (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (k : D.host.Eˣ) (x : (AE D)ˣ)
    (h1 : infPart D (x : AE D) = 1) (h2 : finPart D (x : AE D) = finPart D (incA D k)) :
    ((χ.inf k : ℂˣ) : ℂ) * ((c x : Circle) : ℂ) = 1 := by
  classical
  obtain ⟨ι, i1, i2, i3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι i1 i2 (GlobalTheory.PlaceIdem.exists_isPlIdem D ι i1 i2 i3) c χ hc
  obtain ⟨S, -, -, hS⟩ := GlobalTheory.finiteIdele_exists_local_approx D.host.E N hN
    (Units.map (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E)).toMonoidHom k)
  have hx : ∀ P, ι (finPart D (x : AE D)) P = algebraMap D.host.E (P.adicCompletion D.host.E) k := fun P => by
    rw [h2]
    exact congrArg (fun y : FiniteAdeleRing (𝓞 D.host.E) D.host.E => y P) (i1 k)
  have hS' : ∀ P, P ∉ S ∪ T → P.valuation D.host.E (k : D.host.E) = 1 ∧ (N : 𝓞 D.host.E) ∉ P.asIdeal := fun P hP => by
    have := hS P fun h => hP (Finset.mem_union_left _ h)
    exact ⟨(GlobalTheory.BaseIdeleTriv.val_algebraMap P (k : D.host.E)).symm.trans this.1, this.2⟩
  have h3 := hprod x h1 (S ∪ T) (fun _ => k)
    (fun P _ => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap], by rw [hx, sub_self, map_zero]; exact zero_le⟩)
    (fun P hP => ⟨by rw [hx, GlobalTheory.BaseIdeleTriv.val_algebraMap]; exact (hS' P hP).1, (hS' P hP).2⟩)
  have h4 := GlobalTheory.HeckeProduct.hchar_productRule D.host.E χ (S ∪ T)
    (fun v hv => hT v fun h => hv (Finset.mem_union_right _ h)) k
  have h5 : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S ∪ T), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => (finprod_congr fun hv => by
      show χ.val v ^ ordF v k = 1
      rw [ordF, (hS' v hv).1]; simp).trans finprod_one
  rw [h5, mul_one] at h4
  rw [h3, ← Units.coe_prod, ← Units.val_mul, h4, Units.val_one]


set_option maxHeartbeats 1000000 in
open GlobalTheory.FockCompare in
theorem val_inf (D : D7) [Fintype D.what₂.Tau] (c : IdC D) (χ : HChar D.host.E) (hc : ChrEq c χ)
    (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hT : ∀ v, v ∉ T → χ.UnrAt v) (n : D.what₂.Tau → ℤ)
    (hn : χ.HasInf (tauE D) n) (θ : InfF D) (hθ : IsInfFam θ) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) :
    ((c x : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  obtain ⟨s, hs⟩ := GlobalTheory.FockCompare.exists_chart hθ
  obtain ⟨-, a, b, -, -, hab, ha, hb⟩ := GlobalTheory.IdeleParts.congr_open_and_parts D
  haveI : Nonempty D.what₂.Tau := ⟨D.eTau.symm 1⟩
  have ext : ∀ a b : AE D, finPart D a = finPart D b → (∀ τ, θ τ (infPart D a) = θ τ (infPart D b)) → a = b := by
    intro a b h1 h2
    rw [← sub_eq_zero]
    exact hs.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
      rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]
  let t : (D.what₂.Tau → ℂˣ) → AE D := fun z => s (fun τ => (z τ : ℂ)) + (1 - s 1)
  have tf : ∀ z, finPart D (t z) = 1 := fun z => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.fin, zero_add, sub_zero]
  have ti : ∀ z τ, θ τ (infPart D (t z)) = z τ := fun z τ => by
    simp only [t, RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_one, hs.comp, Pi.one_apply, sub_self, add_zero]
  have tc : Continuous t :=
    (hs.cont.comp (continuous_pi fun τ => Units.continuous_val.comp (continuous_apply τ))).add continuous_const
  let U : (D.what₂.Tau → ℂˣ) →* AE D :=
    { toFun := t
      map_one' := ext _ _ (by rw [tf, RingHom.map_one]) fun τ => by
        rw [ti, RingHom.map_one, RingHom.map_one]; rfl
      map_mul' := fun x y => ext _ _ (by rw [RingHom.map_mul, tf, tf, tf, mul_one]) fun τ => by
        rw [RingHom.map_mul, RingHom.map_mul, ti, ti, ti]; rfl }
  have Uc : Continuous U.toHomUnits := Units.continuous_iff.2 ⟨tc, tc.comp continuous_inv⟩
  have hU : ∀ y : (AE D)ˣ, finPart D (y : AE D) = 1 →
      y = U.toHomUnits fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y := fun y hy =>
    Units.ext (ext _ _ (hy.trans (tf _).symm) fun τ =>
      (ti (fun τ => Units.map ((θ τ).comp (infPart D)).toMonoidHom y) τ).symm)
  have hd : DenseRange fun (k : D.host.E) τ => tauE D τ k := by
    intro z
    have := GlobalTheory.HeckeFinTrivial.mem_closure_range (tauE D) θ (fun τ => (hθ τ).1) (fun τ => (hθ τ).2) (infPart D (s z))
    rwa [show (fun i => θ i (infPart D (s z))) = z from funext fun τ => hs.comp z τ] at this
  have key : ∀ z : D.what₂.Tau → ℂˣ, ((c (U.toHomUnits z) : Circle) : ℂ) = ∏ τ, ((z τ : ℂ) / (‖(z τ : ℂ)‖ : ℂ)) ^ n τ := by
    intro z
    refine (GlobalTheory.HeckeFinTrivial.denseRange_units (tauE D) hd).induction_on z
      (isClosed_eq (continuous_subtype_val.comp (hc.1.1.comp Uc)) ?_) fun k => ?_
    · refine continuous_finsetProd _ fun τ _ => ?_
      have h1 : Continuous fun z : D.what₂.Tau → ℂˣ => (z τ : ℂ) := Units.continuous_val.comp (continuous_apply τ)
      have h3 : ∀ z : D.what₂.Tau → ℂˣ, (‖(z τ : ℂ)‖ : ℂ) ≠ 0 := fun z => by
        exact_mod_cast norm_ne_zero_iff.2 (z τ).ne_zero
      exact (h1.div (Complex.continuous_ofReal.comp h1.norm) h3).zpow₀ _
        fun z => Or.inl (div_ne_zero (z τ).ne_zero (h3 z))
    · let y : (AE D)ˣ := Units.map (incA D).toMonoidHom k
      have e1 : a y = U.toHomUnits fun τ => Units.map (tauE D τ).toMonoidHom k := by
        rw [hU (a y) (ha y).2]
        congr 1
        funext τ
        exact Units.ext ((congrArg (θ τ) (ha y).1).trans ((hθ τ).1 k))
      have e2 := val_fin_principal D c χ hc T hT k (b y) (hb y).1 (hb y).2
      have e3 : c (a y) * c (b y) = 1 := by rw [← map_mul, ← hab y]; exact hc.1.2 k
      have e4 : ((c (a y) : Circle) : ℂ) * ((c (b y) : Circle) : ℂ) = 1 := by rw [← Circle.coe_mul, e3, Circle.coe_one]
      rw [← e1]
      exact (mul_right_cancel₀ (Circle.coe_ne_zero _) (e4.trans e2.symm)).trans (hn k)
  exact (congrArg (fun y => ((c y : Circle) : ℂ)) (hU x hx)).trans (key _)

theorem sign_zpow_even {w : ℂ} (hw : starRingEnd ℂ w = w) (h0 : w ≠ 0) (m : ℤ) : (w / (‖w‖ : ℂ)) ^ (-2 * m) = 1 := by
  have h1 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 h0
  have h2 : (w / (‖w‖ : ℂ)) ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', hw, sq]
    exact div_self (mul_ne_zero h0 h0)
  rw [show -2 * m = 2 * -m by ring, _root_.zpow_mul, h2, _root_.one_zpow]


set_option maxHeartbeats 1000000 in
theorem exists_char : ∀ (D : D7) (j : Fin D.R.m),
    ∃ χ : IdC D, IsHeckeChar D χ ∧ (∀ τ, HasInfExp D χ τ (-(D.hc τ).e j)) ∧ ResEta D χ 0 := by
  intro D j
  classical
  letI : Fintype D.what₂.Tau := Fintype.ofEquiv _ D.eTau.symm
  choose z hz using fun τ => (D.hc τ).e_int j
  obtain ⟨χ, hu, ht, hi, T, hT⟩ := exists_hchar D.R D.host D.what₂.Tau D.eTau z
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CharTransport.exists_chrEq D χ hu
  have hv := val_inf D c χ hc T hT _ hi
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.Member.exists_isInfFam_family D
  refine ⟨c, hc.1, fun τ => ⟨-2 * z τ, by rw [hz]; push_cast; ring, ⟨θ₀, hθ₀⟩, fun θ hθ x h1 h2 => ?_⟩,
    GlobalTheory.VolHeckeCompare.exists_isEta D, fun η _ a => ?_⟩
  · rw [hv θ hθ x h1, Finset.prod_eq_single τ (fun τ' _ h => by rw [h2 τ' h]; simp) (by simp)]
  · let p : AF D.host.F →* AF D.host.F := (MonoidHom.inl (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.fst (Ainf D.host.F) (Af D.host.F))
    let q : AF D.host.F →* AF D.host.F := (MonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp
      (MonoidHom.snd (Ainf D.host.F) (Af D.host.F))
    have e : a = Units.map p a * Units.map q a := Units.ext (Prod.ext (mul_one _).symm (one_mul _).symm)
    have e1 : c (idF D (Units.map q a)) = 1 := GlobalTheory.BaseIdeleTriv.finite_idele_base_trivial D c χ hc ht _ rfl
    have e2 : c (idF D (Units.map p a)) = 1 := by
      apply Circle.ext
      rw [hv θ₀ hθ₀ _ rfl, Circle.coe_one]
      refine Finset.prod_eq_one fun τ _ => sign_zpow_even (GlobalTheory.FockCompare.conj_tmul_one hθ₀ τ _) ?_ _
      exact (Units.map ((θ₀ τ).comp (infPart D)).toMonoidHom (idF D (Units.map p a))).ne_zero
    rw [pow_zero, e, map_mul, map_mul, e1, e2, one_mul]

end GlobalTheory.Mem.AntiChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSumUnitarySubstitutionsEqRowLie
section
noncomputable section

open MvPolynomial GlobalTheory.DefLift

namespace GlobalTheory.DefLift

section RowLie

variable {ι : Type} {m n : ℕ}


open Classical in
def rowSubst (n : ℕ) (τ : ι) (g : Matrix (Fin m) (Fin m) ℂ) : Pol ι m n →ₐ[ℂ] Pol ι m n :=
  subst (fun _ => 1) (fun ρ => if ρ = τ then g else 1)

theorem rowSubst_X_self (τ : ι) (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) (c : Fin n) :
    rowSubst n τ g (X (τ, j, c)) = ∑ i, g i j • X (τ, i, c) := by
  simp [rowSubst, subst, Matrix.one_apply]

theorem rowSubst_X_ne {τ ρ : ι} (h : ρ ≠ τ) (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) (c : Fin n) :
    rowSubst n τ g (X (ρ, j, c)) = X (ρ, j, c) := by
  simp [rowSubst, subst, Matrix.one_apply, h]

theorem rowSubst_one (τ : ι) (P : Pol ι m n) : rowSubst n τ 1 P = P := by
  have : rowSubst n τ (1 : Matrix (Fin m) (Fin m) ℂ) = AlgHom.id ℂ _ := by
    refine MvPolynomial.algHom_ext fun ⟨ρ, j, c⟩ => ?_
    by_cases h : ρ = τ
    · subst h
      simp [rowSubst_X_self, Matrix.one_apply]
    · simp [rowSubst_X_ne h]
  rw [this]; rfl

theorem rowLie_mul (τ : ι) (k l : Fin m) (P Q : Pol ι m n) :
    rowLie n τ k l (P * Q) = rowLie n τ k l P * Q + P * rowLie n τ k l Q := by
  simp only [rowLie_apply, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

theorem rowLie_X_self (τ : ι) (k l j : Fin m) (c : Fin n) :
    rowLie n τ k l (X (τ, j, c)) = if j = l then X (τ, k, c) else 0 := by
  classical
  rw [rowLie_apply]
  by_cases h : j = l
  · subst h
    simp [pderiv_X, Pi.single_apply]
  · simp [pderiv_X, Pi.single_apply, h]

theorem rowLie_X_ne {τ ρ : ι} (h : ρ ≠ τ) (k l j : Fin m) (c : Fin n) :
    rowLie n τ k l (X (ρ, j, c)) = 0 := by
  classical
  simp [rowLie_apply, pderiv_X, Pi.single_apply, h]

theorem exists_poly_rowSubst_coef (τ : ι) (k l : Fin m) (f : Pol ι m n) (φ : Module.Dual ℂ (Pol ι m n)) :
    ∃ Q : MvPolynomial (Fin m × Fin m) ℂ,
      (∀ g : Matrix (Fin m) (Fin m) ℂ, φ (rowSubst n τ g f) = eval (fun x => g x.1 x.2) Q) ∧
      φ (rowLie n τ k l f) = eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (pderiv (k, l) Q) := by
  induction f using MvPolynomial.induction_on generalizing φ with
  | C a => exact ⟨C (φ (C a)), fun g => by simp [rowSubst, subst], by simp [rowLie_apply]⟩
  | add p q hp hq =>
    obtain ⟨P, hP, hP'⟩ := hp φ
    obtain ⟨Q, hQ, hQ'⟩ := hq φ
    exact ⟨P + Q, fun g => by simp only [map_add (f := _), hP, hQ], by simp only [map_add (f := _), hP', hQ']⟩
  | mul_X p v hp =>
    obtain ⟨ρ, j, c⟩ := v
    by_cases h : ρ = τ
    · subst h
      choose P hP hP' using fun b : Fin m => hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, b, c)))
      refine ⟨∑ b, X (b, j) * P b, fun g => ?_, ?_⟩
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, rowSubst_X_self, Finset.mul_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mul_smul_comm, map_smul, map_mul (eval _), eval_X, ← hP b g]
        rfl
      · have h1 : ∀ b, eval (fun x => (1 : Matrix (Fin m) (Fin m) ℂ) x.1 x.2) (P b) = φ (p * X (ρ, b, c)) := by
          intro b
          rw [← hP b 1, rowSubst_one]; rfl
        set_option synthInstance.maxHeartbeats 100000 in
          rw [rowLie_mul, rowLie_X_self, map_add (f := _), map_sum, map_sum]
        simp only [Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, eval_X, ← hP', h1, Finset.sum_add_distrib,
          pderiv_X]
        congr 1
        · simp [Matrix.one_apply]
        · by_cases hj : j = l
          · subst hj
            simp [Pi.single_apply, apply_ite]
          · simp [Pi.single_apply, hj]
    · obtain ⟨P, hP, hP'⟩ := hp (φ ∘ₗ LinearMap.mulRight ℂ (X (ρ, j, c)))
      refine ⟨P, fun g => ?_, ?_⟩
      · rw [map_mul, rowSubst_X_ne h, ← hP g]; rfl
      · rw [rowLie_mul, rowLie_X_ne h, mul_zero, add_zero, ← hP']; rfl

theorem rowLie_mem_span_rowSub {J : Type} [Fintype J] (f : J → Pol ι m n) (τ : ι) (k l : Fin m) :
    (fun j => rowLie n τ k l (f j)) ∈
      Submodule.span ℂ (Set.range fun (u : Matrix.unitaryGroup (Fin m) ℂ) (j : J) => rowSub n τ u (f j)) := by
  classical
  by_contra hn
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have hs : ∀ x : J → Pol ι m n, φ x = ∑ j, (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j) (x j) := by
    intro x
    conv_lhs => rw [← Finset.univ_sum_single x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; rfl
  choose Q hQ hQ' using fun j =>
    exists_poly_rowSubst_coef τ k l (f j) (φ ∘ₗ LinearMap.single ℂ (fun _ : J => Pol ι m n) j)
  have h0 : ∑ j, Q j = 0 := by
    refine GlobalTheory.Branching.eq_zero_of_vanish_unitaryGroup m _ fun u hu => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [← hQ]
    have hm : φ (fun j => rowSub n τ ⟨u, hu⟩ (f j)) ∈ (⊥ : Submodule ℂ ℂ) :=
      hφ0 ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)
    rw [Submodule.mem_bot, hs] at hm
    exact hm
  apply hφ
  rw [hs]
  simp only [hQ']
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sum, h0, map_zero, map_zero]

end RowLie

theorem exists_sum_rowSub_eq_rowLie (ι : Type) [Fintype ι] (m n d : ℕ) (τ : ι) (k l : Fin m) :
    ∃ (s : Finset (Matrix.unitaryGroup (Fin m) ℂ)) (c : Matrix.unitaryGroup (Fin m) ℂ → ℂ),
      ∀ P : Pol ι m n, P.totalDegree ≤ d → ∑ u ∈ s, c u • rowSub n τ u P = rowLie n τ k l P := by
  obtain ⟨S, hS⟩ : (restrictTotalDegree (ι × Fin m × Fin n) ℂ d).FG := Module.Finite.iff_fg.1 inferInstance
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1
    (rowLie_mem_span_rowSub (fun j : S => (j : Pol ι m n)) τ k l)
  refine ⟨c.support, c, fun P hP => ?_⟩
  have hP' : P ∈ Submodule.span ℂ (S : Set (Pol ι m n)) := hS ▸ (mem_restrictTotalDegree _ _ _).2 hP
  have key : Set.EqOn (∑ u ∈ c.support, c u • rowSub n τ u : Pol ι m n →ₗ[ℂ] Pol ι m n) (rowLie n τ k l)
      (S : Set (Pol ι m n)) := by
    intro x hx
    have := congrFun hc ⟨x, hx⟩
    simpa [Finsupp.sum, LinearMap.sum_apply, Finset.sum_apply] using this
  have := LinearMap.eqOn_span key hP'
  simpa [LinearMap.sum_apply] using this

end GlobalTheory.DefLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThre
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem isAddHaarMeasure_tupMeas_of_lc {S : Type} [AddCommGroup S] [TopologicalSpace S]
    [IsTopologicalAddGroup S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace S] [BorelSpace S] (lam : Measure S) (h : lam.IsAddHaarMeasure) (n M : ℕ) :
    (tupMeas lam n M).IsAddHaarMeasure := by
  unfold tupMeas
  haveI : (Measure.pi fun _ : Fin M => lam).IsAddHaarMeasure := inferInstance
  infer_instance

theorem setOf_isUnit_ainf (F : Type) [Field F] [NumberField F] :
    {c : Ainf F | IsUnit c} = {c : Ainf F | ∀ w, c w ≠ 0} := by
  ext c
  simp only [Set.mem_setOf_eq]
  refine (Pi.isUnit_iff (x := c)).trans (forall_congr' fun w => isUnit_iff_ne_zero)

theorem existsUnique_isStdX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (β : F), 3 ≤ M → IsHermND σ J → β ≠ 0 → ∃! ν, IsStdX s σ J β ν := by
  intro F E _ _ _ _ _ σ hσ d b s M J β hM hJ hβ
  have hM1 : 1 ≤ M := by omega
  obtain ⟨nI, nV⟩ := GlobalTheory.GaugeEx.nice_ainf_fv F
  have uI : IsUnit (algebraMap F (Ainf F) β) := (isUnit_iff_ne_zero.2 hβ).map _
  have uV : ∀ v, IsUnit (algebraMap F (Fv F v) β) := fun v => (isUnit_iff_ne_zero.2 hβ).map _
  have bI := fun m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Ainf F) nI M J (tupMeas s.lamI 1 M) s.nuI _ m s.haar_nuI uI
  have bV := fun v m => GlobalTheory.GaugeEx.FibBasic.fibAt_basic F E σ (Fv F v) (nV v) M J (tupMeas (s.lamV v) 1 M) (s.nuV v) _ m
    (s.haar_nuV v) (uV v)
  obtain ⟨mi, hmi⟩ : ∃ mi, FibAt (Ainf F) σ J (tupMeas s.lamI 1 M) s.nuI (algebraMap F _ β) mi := by
    obtain ⟨fib, hfib⟩ := _root_.GlobalTheory.GaugeEx.FibExist.exists_fibreFamily_ainf F E σ hσ M J (tupMeas s.lamI 1 M) s.nuI hM1 hJ
      (isAddHaarMeasure_tupMeas_of_lc _ s.haar_lamI 1 M) s.haar_nuI
    exact ⟨_, fib, by rw [setOf_isUnit_ainf]; exact hfib, rfl⟩
  have hex : ∀ v, ∃ m, FibAt (Fv F v) σ J (tupMeas (s.lamV v) 1 M) (s.nuV v) (algebraMap F _ β) m := by
    intro v
    obtain ⟨-, fib, hfib⟩ := GlobalTheory.LocalDensityCompare.null_and_exists v σ J hσ hM1 hJ
      (tupMeas (s.lamV v) 1 M) (isAddHaarMeasure_tupMeas_of_lc _ (s.haar_lamV v) 1 M) (s.nuV v)
      (s.haar_nuV v)
    refine ⟨_, fib, ?_, rfl⟩
    simp only [isUnit_iff_ne_zero]
    exact hfib
  choose mv hmv using hex
  have hconv : Conv b mi mv := by
    refine ⟨(bI mi hmi).2.1, fun v => (bV v _ (hmv v)).2.1, ?_⟩
    have hs := ((GlobalTheory.countable_ideal_and_summable_absNorm_rpow F).2 2 (by norm_num)).2
    refine Summable.of_norm_bounded_eventually hs ?_
    filter_upwards [_root_.GlobalTheory.GaugeDensity.local_density_bound F E σ hσ d b s M J β hM1 hJ hβ] with v hv
    have h := hv _ (hmv v)
    have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
      have : Ideal.absNorm v.asIdeal ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
      exact_mod_cast Nat.one_le_iff_ne_zero.2 this
    set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ)
    set a : ℝ := |(mv v (latV b v)).toReal - 1|
    have ha : 0 ≤ a := abs_nonneg _
    have hq0 : 0 < q := by linarith
    have h3 : a * q ^ 3 ≤ q := (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hM) ha).trans h
    have h2 : a * q ^ 2 ≤ 1 := by
      refine le_of_mul_le_mul_right ?_ hq0
      calc a * q ^ 2 * q = a * q ^ 3 := by ring
        _ ≤ 1 * q := by rw [one_mul]; exact h3
    rw [Real.norm_of_nonneg ha, Real.rpow_neg hq0.le, Real.rpow_two, ← one_div,
      le_div_iff₀ (by positivity)]
    exact h2
  obtain ⟨ν, hν⟩ := _root_.GlobalTheory.GaugeEx.exists_isProd F E d b 1 M mi mv hconv
  refine ⟨ν, ⟨mi, mv, hmi, hmv, hν⟩, ?_⟩
  rintro ν' ⟨mi', mv', hmi', hmv', hν'⟩
  obtain rfl : mi' = mi := (bI mi hmi).2.2 _ hmi'
  obtain rfl : mv' = mv := funext fun v => (bV v _ (hmv v)).2.2 _ (hmv' v)
  exact (_root_.GlobalTheory.GaugeEx.isProd_basic F E d b 1 M ν _ _ hν).2.2.1 _ hν'

end GlobalTheory.GaugeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtMatInjective
section
noncomputable section

open NumberField Matrix GlobalTheory.SgAlg GlobalTheory.SgGlob Formalism.MainNotions.S

namespace GlobalTheory.IntTerm

variable {E : Type} [Field E]

theorem ptEntry_inj : ∀ (bs cs : List (E × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) → (∀ b ∈ cs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    (bs.map Prod.snd).sum = (cs.map Prod.snd).sum →
    (∀ a < (bs.map Prod.snd).sum, ∀ b < (bs.map Prod.snd).sum, ptEntry bs a b = ptEntry cs a b) → bs = cs
  | [], [], _, _, _, _ => rfl
  | [], (t, s) :: cs, _, h, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, [], h, _, e, _ => by
    have := (h (t, s) (by simp)).2
    simp only [List.map_cons, List.sum_cons, List.map_nil, List.sum_nil] at e
    omega
  | (t, s) :: bs, (t', s') :: cs, h, h', e, k => by
    have ht : t ≠ 0 := (h (t, s) (by simp)).1
    have hs : 1 ≤ s := (h (t, s) (by simp)).2
    have hs' : 1 ≤ s' := (h' (t', s') (by simp)).2
    simp only [List.map_cons, List.sum_cons] at e k
    have k0 := k 0 (by omega) (s - 1) (by omega)
    simp only [ptEntry] at k0
    rw [ite_eq_left (by omega), ite_eq_left (by omega)] at k0
    have hss : s = s' ∧ t = t' := by
      split_ifs at k0
      · exact ⟨by omega, k0⟩
      · exact absurd k0 ht
      · omega
      · exact absurd k0 ht
    rcases hss with ⟨rfl, rfl⟩
    apply congrArg (List.cons (t, s))
    refine ptEntry_inj bs cs (fun b hb => h b (by simp [hb])) (fun b hb => h' b (by simp [hb])) (by omega)
      fun a ha b hb => ?_
    have shifted := k (a + s) (by omega) (b + s) (by omega)
    have outside : ¬ (a + s < s ∧ b + s < s) := by omega
    have inside : s ≤ a + s ∧ s ≤ b + s := by omega
    simpa only [ptEntry, ite_eq_right outside, ite_eq_left inside, Nat.add_sub_cancel] using shifted

theorem ptMat_injective {m : ℕ} : Function.Injective (ptMat : Point E m → Matrix (Fin m) (Fin m) E) := by
  intro w w' h
  refine Subtype.ext (ptEntry_inj _ _ w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) fun a ha b hb => ?_)
  rw [w.2.2] at ha hb
  exact congrFun (congrFun h ⟨a, ha⟩) ⟨b, hb⟩

variable [NumberField E] {σ : E →+* E} {n r g : ℕ} {J : Matrix (Fin n) (Fin n) E} {T' : E}
  {P : Matrix (Fin n) (Fin (r + 1)) E}

end GlobalTheory.IntTerm
end
end

