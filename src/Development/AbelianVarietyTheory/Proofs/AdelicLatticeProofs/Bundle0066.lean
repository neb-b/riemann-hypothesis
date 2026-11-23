module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
section
noncomputable section

namespace GlobalTheory.IdeleParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isOpen_nsmul_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 0 < N) :
    letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    IsOpen {z : GlobalTheory.AdLat.RA F E | ∃ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), z = N • y} := by
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    (1 : Submodule (𝓞 E) E).comap (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0)
  have hL : ∀ x : Fin 1 → E, x ∈ L ↔ x 0 ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro x
    simp only [L, Submodule.mem_comap, Submodule.mem_one, LinearMap.proj_apply, Set.mem_range]
  have hspan : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (fun _ => (1 : E)) ∈ L := (hL _).2 ⟨1, map_one _⟩
    have : x = x 0 • (fun _ : Fin 1 => (1 : E)) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have ho := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 1 L hspan).1 N hN
  have hc : Continuous (fun z : GlobalTheory.AdLat.RA F E => fun _ : Fin 1 => z) := continuous_pi fun _ => continuous_id
  have h1 : ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)),
      y 0 ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, x 0, (hL x).1 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  have h2 : ∀ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)),
      (fun _ : Fin 1 => y) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, fun _ => x, (hL _).2 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  convert ho.preimage hc using 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, h2 y hy, rfl⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y 0, h1 y hy, congrFun h 0⟩

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem exists_units_parts {R A B : Type} [Ring R] [Ring A] [Ring B] [TopologicalSpace R] [TopologicalSpace A]
    [TopologicalSpace B] (e : R ≃+* A × B) (hec : Continuous e) (hes : Continuous e.symm)
    (f : R → A) (g : R → B) (he : ∀ z, (e z).1 = f z ∧ (e z).2 = g z) :
    ∃ a b : Rˣ →* Rˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧
      (∀ x, f (a x : R) = f (x : R) ∧ g (a x : R) = 1) ∧ ∀ x, f (b x : R) = 1 ∧ g (b x : R) = g (x : R) := by
  let a0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp ((MonoidHom.fst _ _).comp e.toRingHom.toMonoidHom))
  let b0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inr _ _).comp ((MonoidHom.snd _ _).comp e.toRingHom.toMonoidHom))
  have ha0 : ∀ z, a0 z = e.symm ((e z).1, 1) := fun z => rfl
  have hb0 : ∀ z, b0 z = e.symm (1, (e z).2) := fun z => rfl
  have hac : Continuous a0 := by
    rw [show (a0 : R → R) = fun z => e.symm ((e z).1, 1) from funext ha0]
    exact hes.comp ((continuous_fst.comp hec).prodMk continuous_const)
  have hbc : Continuous b0 := by
    rw [show (b0 : R → R) = fun z => e.symm (1, (e z).2) from funext hb0]
    exact hes.comp (continuous_const.prodMk (continuous_snd.comp hec))
  refine ⟨Units.map a0, Units.map b0, Continuous.units_map a0 hac, Continuous.units_map b0 hbc,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.coe_map, Units.coe_map, ha0, hb0, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    exact (e.symm_apply_apply _).symm
  · rw [Units.coe_map, ha0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨(he _).1, rfl⟩
  · rw [Units.coe_map, hb0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨rfl, (he _).2⟩

theorem congr_open_and_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  intro D
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  refine ⟨fun N hN => ?_, ?_⟩
  · haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.toContinuousAdd (Af D.host.F) _
    have hN' : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ intAE D, z = N • y} := by
      rw [integralFiniteAdeles_eq_adelicCompletion_integers]
      exact isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
      have := isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
      rw [← integralFiniteAdeles_eq_adelicCompletion_integers] at this
      convert this using 1
      ext z
      simp
    have c1 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) := hfc.comp Units.continuous_val
    have c2 : Continuous fun x : (AE D)ˣ => finPart D ((x⁻¹ : (AE D)ˣ) : AE D) :=
      hfc.comp Units.continuous_coe_inv
    have c3 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) - 1 := by
      simp only [sub_eq_add_neg]
      exact c1.add continuous_const
    exact (h1.preimage c1).inter ((h1.preimage c2).inter (hN'.preimage c3))
  · exact exists_units_parts e hec hes (infPart D) (finPart D) he

end GlobalTheory.IdeleParts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealSymplecticFormAlternatingInvariantDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.RealSymplForm

section Mat

open scoped ComplexOrder MatrixOrder

variable {k m n : ℕ}

theorem cartan_swap {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : sᴴ * G = G * s := by
  calc sᴴ * G = sᴴ * G * (s * s) := by rw [h.1, Matrix.mul_one]
    _ = G * s := by rw [← Matrix.mul_assoc, h.2.1]

theorem cartan_herm {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : Gᴴ = G := by
  have h1 : (G * s)ᴴ = G * s := h.2.2.1
  have h2 : sᴴ * sᴴ = 1 := by rw [← conjTranspose_mul, h.1, conjTranspose_one]
  rw [conjTranspose_mul, ← cartan_swap h] at h1
  calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = G := by rw [h1, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem cartanInvolution_inv_eq_self {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : s⁻¹ = s :=
  Matrix.inv_eq_left_inv h.1

theorem cartan_inv_mul {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : (G * s)⁻¹ = s * G⁻¹ := by
  rw [Matrix.mul_inv_rev, cartanInvolution_inv_eq_self h]

theorem cartan_inv_conj {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) : s * G⁻¹ * sᴴ = G⁻¹ := by
  conv_rhs => rw [← h.2.1]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, cartanInvolution_inv_eq_self h, Matrix.mul_assoc]

theorem trace_pos {P : Matrix (Fin n) (Fin n) ℂ} {Q : Matrix (Fin m) (Fin m) ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    {x : Matrix (Fin m) (Fin n) ℂ} (hx : x ≠ 0) : 0 < (P * xᴴ * Q * x).trace.re := by
  obtain ⟨B, hB, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hQ.isStrictlyPositive
  have e : (star B * B * xᴴ * (star C * C) * x).trace = ((C * x * Bᴴ)ᴴ * (C * x * Bᴴ)).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hy : C * x * Bᴴ ≠ 0 := by
    intro h0
    apply hx
    have hB' : IsUnit (Bᴴ).det := (Matrix.isUnit_iff_isUnit_det _).1 hB.star
    have hC' : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det _).1 hC
    calc x = C⁻¹ * (C * x * Bᴴ) * (Bᴴ)⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hB',
            Matrix.nonsing_inv_mul_cancel_left _ _ hC']
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  rw [e]
  have h1 := (posSemidef_conjTranspose_mul_self (C * x * Bᴴ)).trace_nonneg
  have h2 : ((C * x * Bᴴ)ᴴ * (C * x * Bᴴ)).trace ≠ 0 := fun h0 =>
    hy (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.1 h0)
  exact (Complex.pos_iff.1 (lt_of_le_of_ne h1 h2.symm)).1

theorem cplxO_cplxO {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s * s = 1) (ht : t * t = 1)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (cplxO s t x) = -x := by
  have e : t * (t * x * s) * s = x := by
    calc _ = (t * t) * x * (s * s) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hs, ht, Matrix.one_mul, Matrix.mul_one]
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul, smul_smul, e, Complex.I_mul_I, neg_smul, one_smul]

theorem tr_conj {G : Matrix (Fin n) (Fin n) ℂ} {H : Matrix (Fin m) (Fin m) ℂ} (hG : Gᴴ = G) (hH : Hᴴ = H)
    (x y : Matrix (Fin m) (Fin n) ℂ) : (G⁻¹ * xᴴ * H * y).trace = star (G⁻¹ * yᴴ * H * x).trace := by
  rw [← Matrix.trace_conjTranspose]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hG, hH, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem tr_J_left {G s : Matrix (Fin n) (Fin n) ℂ} {H t : Matrix (Fin m) (Fin m) ℂ} (hG : IsCartanInv G s)
    (x y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * yᴴ * H * cplxO s t x).trace = Complex.I * ((G * s)⁻¹ * yᴴ * (H * t) * x).trace := by
  rw [cplxO, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, cartan_inv_mul hG, ← Matrix.mul_assoc,
    Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem tr_J_J {G s : Matrix (Fin n) (Fin n) ℂ} {H t : Matrix (Fin m) (Fin m) ℂ} (hG : IsCartanInv G s)
    (hH : IsCartanInv H t) (x y : Matrix (Fin m) (Fin n) ℂ) :
    (G⁻¹ * (cplxO s t y)ᴴ * H * cplxO s t x).trace = (G⁻¹ * yᴴ * H * x).trace := by
  have e : (G * s)⁻¹ * (t * y * s)ᴴ * (H * t) * x = G⁻¹ * yᴴ * H * x := by
    calc _ = (s * G⁻¹ * sᴴ) * yᴴ * (tᴴ * H * t) * x := by
          simp only [cartan_inv_mul hG, conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [cartan_inv_conj hG, hH.2.1]
  rw [tr_J_left hG, cplxO, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.trace_smul, e,
    smul_eq_mul, ← mul_assoc]
  simp

end Mat

theorem realPlace_imaginaryGenerator_re_eq_zero (D : D7) (τ : D.what₂.Tau) : (tauE D τ D.host.xi0).re = 0 := by
  unfold Host.xi0
  rw [map_div₀, map_neg, map_one, map_mul, map_natCast, tauE_sqrtMinusD, Complex.div_re]
  simp

theorem omAt_zero_right {D : D7} (S T : HSp D) (τ : D.what₂.Tau) (x : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {y : Matrix (Fin T.rank) (Fin S.rank) ℂ} (h : y = 0) : omAt S T τ x y = 0 := by
  simp [omAt, hAt, h]

open scoped ComplexOrder in
theorem omAt_J_neg {D : D7} (S T : HSp D) (τ : D.what₂.Tau) {s : Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {t : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hs : IsCartanInv (gramAt D S τ) s) (ht : IsCartanInv (gramAt D T τ) t)
    {x : Matrix (Fin T.rank) (Fin S.rank) ℂ} (hx : x ≠ 0) : omAt S T τ (cplxO s t x) x < 0 := by
  have e : hAt S T τ (cplxO s t x) x = Complex.I *
      ((gramAt D S τ * s)⁻¹ * xᴴ * (gramAt D T τ * t) * x).trace := tr_J_left hs _ _
  have p := mul_pos (xi_zero_im_pos D τ) (trace_pos hs.2.2.inv ht.2.2 hx)
  simp only [omAt, e, Complex.mul_re, Complex.mul_im, realPlace_imaginaryGenerator_re_eq_zero, Complex.I_re, Complex.I_im]
  linarith

theorem form_alt_inv_def : ∀ (D : D7) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ x, jO S T sS sT (jO S T sS sT x) = -x) ∧ (∀ x y, omO S T x y = -omO S T y x) ∧ (∀ x y, omO S T (jO S T sS sT x) (jO S T sS sT y) = omO S T x y) ∧ ∀ x, x ≠ 0 → omO S T (jO S T sS sT x) x < 0 := by
  intro D S T sS sT hS hT
  refine ⟨fun x => ?_, fun x y => ?_, fun x y => ?_, fun x hx => ?_⟩
  · funext τ
    exact cplxO_cplxO (hS τ).1 (hT τ).1 _
  · rw [omO_apply, omO_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : hAt S T τ (y τ) (x τ) = star (hAt S T τ (x τ) (y τ)) :=
      tr_conj (cartan_herm (hS τ)) (cartan_herm (hT τ)) _ _
    simp only [omAt, e, Complex.mul_re, realPlace_imaginaryGenerator_re_eq_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  · rw [omO_apply, omO_apply]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e : hAt S T τ (jO S T sS sT x τ) (jO S T sS sT y τ) = hAt S T τ (x τ) (y τ) :=
      tr_J_J (hS τ) (hT τ) _ _
    simp only [omAt, e]
  · obtain ⟨τ₀, h0⟩ := Function.ne_iff.1 hx
    rw [omO_apply]
    refine Finset.sum_neg' (fun τ _ => ?_) ⟨τ₀, Finset.mem_univ _, omAt_J_neg S T τ₀ (hS τ₀) (hT τ₀) h0⟩
    by_cases h : x τ = 0
    · exact (omAt_zero_right S T τ _ h).le
    · exact (omAt_J_neg S T τ (hS τ) (hT τ) h).le

end GlobalTheory.RealSymplForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharacterHalfSymplecticFormRealPoint
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.OrientedChar

theorem map_inv_field {E : Type} [Field E] (τ : E →+* ℂ) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (h : G.det ≠ 0) :
    (G.map τ)⁻¹ = G⁻¹.map τ := by
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h),
    Matrix.map_one _ τ.map_zero τ.map_one]

theorem ringHom_map_quadrupleSum_products {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {m n : ℕ}
    (P : Fin n → Fin n → A) (y : Fin m → Fin n → A) (Q : Fin m → Fin m → A) (x : Fin m → Fin n → A) :
    φ (∑ a, ∑ b, ∑ c, ∑ d, P a b * y c b * Q c d * x d a) =
      ∑ a, ∑ b, ∑ c, ∑ d, φ (P a b) * φ (y c b) * φ (Q c d) * φ (x d a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul]

theorem trace_four {m n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (y : Matrix (Fin m) (Fin n) ℂ)
    (Q : Matrix (Fin m) (Fin m) ℂ) (x : Matrix (Fin m) (Fin n) ℂ) :
    (P * yᴴ * Q * x).trace = ∑ a, ∑ b, ∑ c, ∑ d, P a b * starRingEnd ℂ (y c b) * Q c d * x d a := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Complex.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]

variable {D : D7}

theorem comp_hO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    θ τ (infPart D (hO S T x y)) = hAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  have hi : ∀ e, ((θ τ).comp (infPart D)) (incA D e) = tauE D τ e := comp_incA hθ τ
  have hc : ∀ z, ((θ τ).comp (infPart D)) (cA D z) = starRingEnd ℂ (((θ τ).comp (infPart D)) z) := comp_cA hθ τ
  have hg : (gramAt D S τ)⁻¹ = S.gram⁻¹.map (tauE D τ) := map_inv_field _ _ (Formalism.L2.Theta.gram_det_ne S)
  unfold hO hAt
  refine (ringHom_map_quadrupleSum_products ((θ τ).comp (infPart D)) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  rw [hg]
  refine Eq.trans ?_ (trace_four _ _ _ _).symm
  simp only [hi, hc]
  rfl

theorem valTau_symplO {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D) (τ : D.what₂.Tau) (x y : WO S T) :
    valTau θ τ (symplO S T x y) = omAt S T τ (piW θ T S x τ) (piW θ T S y τ) := by
  unfold valTau symplO omAt
  rw [SymplVal.trace_AE, RingHom.map_add (f := _), RingHom.map_add (f := _), comp_cA hθ, RingHom.map_mul, RingHom.map_mul,
    comp_incA hθ, comp_hO hθ, Complex.add_re, Complex.conj_re, two_mul]

theorem finPart_cA_eq_zero {z : AE D} (hz : finPart D z = 0) : finPart D (cA D z) = 0 := by
  have h : ∀ w : AE D, finPart D (cA D w) = sigR (Af D.host.F) D.sp.cm.sig (finPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a e => rfl
  rw [h, hz, map_zero]

theorem finPart_hO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    finPart D (hO S T x y) = 0 := by
  unfold hO
  refine (ringHom_map_quadrupleSum_products (finPart D) (fun a b => incA D (S.gram⁻¹ a b)) (fun c b => cA D (y c b))
    (fun c d => incA D (T.gram c d)) x).trans ?_
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rcases h with h | h
  · have e : finPart D (x d a) = 0 := congrFun (congrFun h d) a
    rw [e, mul_zero]
  · have e : finPart D (y c b) = 0 := congrFun (congrFun h c) b
    rw [finPart_cA_eq_zero e, mul_zero, zero_mul, zero_mul]

theorem sndA_symplO (S T : HSp D) {x y : WO S T} (h : x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) :
    sndA D.host.F (symplO S T x y) = 0 := by
  have h0 : finPart D (incA D D.host.xi0 * hO S T x y) = 0 := by
    rw [RingHom.map_mul, finPart_hO S T h, mul_zero]
  have h1 : finPart D (algebraMap (AF D.host.F) (AE D) (symplO S T x y)) = 0 := by
    unfold symplO
    rw [SymplVal.trace_AE, RingHom.map_add (f := _), h0, finPart_cA_eq_zero h0, add_zero]
  have hinj := Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F)
    (B := D.host.E) (algebraMap D.host.F D.host.E).injective
  apply hinj
  rw [map_zero]
  exact h1

theorem char_symplOH : ∀ (D : D7) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (x y : WO S T), (x.map (finPart D) = 0 ∨ y.map (finPart D) = 0) →
      ψ (symplOH S T x y) =
        Complex.exp (-(Real.pi * Complex.I) * (omO S T (piW θ T S x) (piW θ T S y) : ℂ)) := by
  intro D θ ψ hθ hψ S T x y h
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have e := (real_adele_ext_and_char D θ σ hσ _ (sndA_symplO S T h)).2 ψ hψ
  rw [Finset.sum_congr rfl fun τ _ => valTau_symplO hθ S T τ x y] at e
  exact e

end GlobalTheory.OrientedChar
end

