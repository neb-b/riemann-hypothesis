module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
public import Formalism.LocalToGlobal.IndefiniteReal.HeckeTupleStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSelfDualAdelicFrameLevelOne
section
noncomputable section

namespace GlobalTheory.AdelicFrame

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_idem_adele (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ Formalism.UG.intAd F, f * f = f ∧ (∃ w ∈ Formalism.UG.intAd F, f = (m : FiniteAdeleRing (𝓞 F) F) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ Formalism.UG.intAd F, 1 - f = (n : FiniteAdeleRing (𝓞 F) F) * w := by
  obtain ⟨h1, h2⟩ := integral_finiteAdele_complete_separated F
  refine GlobalTheory.IdealIdele.exists_idem (Formalism.UG.intAd F) (fun y hy => h1 y fun N hN => ?_) (fun x hx hc => ?_) m hm
  · obtain ⟨w, hw, e⟩ := hy N hN
    exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
  · obtain ⟨y, hy⟩ := h2 x hx fun N k hN hk => by
      obtain ⟨w, hw, e⟩ := hc N k hN hk
      exact ⟨w, hw, by rw [nsmul_eq_mul]; exact e⟩
    refine ⟨y, ?_, fun N hN => ?_⟩
    · obtain ⟨a, ha, e⟩ := hy 1 one_pos
      rw [e, one_smul]
      exact add_mem (hx 1) ha
    · obtain ⟨a, ha, e⟩ := hy N hN
      exact ⟨a, ha, by rw [← nsmul_eq_mul]; exact e⟩

theorem exists_generator_int (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F ((B : FractionalIdeal (𝓞 E)⁰ E) : Set E) ∧
      y' ∈ hat1 F (((B : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := GlobalTheory.IdealIdele.exists_local_generator B hB
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem_adele F m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hβE : (β : E) ≠ 0 := by simpa using hβ0
  have hnat : ∀ (k : ℕ) (a : FiniteAdeleRing (𝓞 F) F) (x : E),
      ((k : FiniteAdeleRing (𝓞 F) F) * a) ⊗ₜ[F] x = a ⊗ₜ[F] ((k : E) * x) := by
    intro k a x
    rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F,
      TensorProduct.smul_tmul]
  refine ⟨(1 - f) ⊗ₜ (β : E) + f ⊗ₜ 1, (1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1, ?_, add_mem ?_ ?_, ?_⟩
  · have e1 : (1 - f) * (1 - f) = 1 - f := by linear_combination hff
    have e2 : (1 - f) * f = 0 := by linear_combination -hff
    have e3 : f * (1 - f) = 0 := by linear_combination -hff
    simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul, e1, e2, e3, hff, TensorProduct.zero_tmul,
      mul_inv_cancel₀ hβE, mul_one, add_zero, zero_add]
    rw [← TensorProduct.add_tmul, sub_add_cancel, Algebra.TensorProduct.one_def]
  · exact tmul_mem_adelicCompletion_of_integral F (sub_mem (one_mem _) hf : _ ∈ Formalism.UG.intAd F)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hβB)
  · rw [hfw, hnat, mul_one]
    refine tmul_mem_adelicCompletion_of_integral F hw ?_
    have := FractionalIdeal.mem_coeIdeal_of_mem (P := E) (𝓞 E)⁰ hmB
    rwa [map_natCast] at this
  · have := mem_adelicCompletion_mul_inv_fractionalIdeal F (B : FractionalIdeal (𝓞 E)⁰ E) 1 ((1 - f) ⊗ₜ (β : E)⁻¹ + f ⊗ₜ 1)
      (FractionalIdeal.coeIdeal_ne_zero.2 hB) fun x hx => by
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        obtain ⟨d, hd⟩ := hdvd b hb
        have hd' : (n : E) * algebraMap (𝓞 E) E b = algebraMap (𝓞 E) E β * algebraMap (𝓞 E) E d := by
          rw [← map_mul, ← hd, map_mul, map_natCast]
        simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        refine add_mem ?_ (tmul_mem_adelicCompletion_of_integral F hf ((FractionalIdeal.mem_one_iff _).2 ⟨b, rfl⟩))
        rw [hfv, hnat]
        refine tmul_mem_adelicCompletion_of_integral F hv ((FractionalIdeal.mem_one_iff _).2 ⟨d, ?_⟩)
        rw [mul_left_comm, hd']
        exact (inv_mul_cancel_left₀ hβE _).symm
    rwa [one_mul] at this

theorem exists_generator (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) :
    ∃ y y' : RA F E, y * y' = 1 ∧ y ∈ hat1 F (I : Set E) ∧
      y' ∈ hat1 F ((I⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨a, B, ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hB : B ≠ ⊥ := by
    rintro rfl
    simp at hI
  have haE : algebraMap (𝓞 E) E a ≠ 0 := by simpa using ha
  obtain ⟨y, y', h, hy, hy'⟩ := exists_generator_int F B hB
  refine ⟨(1 ⊗ₜ (algebraMap (𝓞 E) E a)⁻¹) * y, (1 ⊗ₜ (algebraMap (𝓞 E) E a)) * y', ?_, ?_, ?_⟩
  · rw [mul_mul_mul_comm, h, Algebra.TensorProduct.tmul_mul_tmul, inv_mul_cancel₀ haE, mul_one, mul_one,
      Algebra.TensorProduct.one_def]
  · exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy
  · rw [mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    exact (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.mem_spanSingleton_self _ _)) _ hy'

theorem mem_integral_adelic_lattice_iff (z : RA F E) :
    z ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) ↔
      Algebra.TensorProduct.comm F _ E z ∈ Formalism.L2.Herm.intAf F E := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
      have h1 : (1 : E) ⊗ₜ[F] a ∈ Formalism.L2.Herm.intAf F E := Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (algebraMap (𝓞 E) E c) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ Formalism.L2.Herm.intAf F E :=
        Subring.subset_closure (Or.inl ⟨⟨_, c, rfl⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at this
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  · intro hz
    have key : ∀ t ∈ Formalism.L2.Herm.intAf F E, (Algebra.TensorProduct.comm F _ E).symm t ∈
        hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
      intro t ht
      induction ht using Subring.closure_induction with
      | mem z hz =>
        rcases hz with ⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩
        · exact one_tmul_mem_adelicCompletionOfElementSet F ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
        · exact tmul_mem_adelicCompletion_of_integral F b.2 (FractionalIdeal.one_mem_one _)
      | zero => rw [map_zero]; exact zero_mem _
      | one => rw [map_one]; exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
      | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
      | neg a _ ha => rw [map_neg]; exact neg_mem ha
      | mul a b _ _ ha hb =>
        rw [map_mul]
        have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ ha _ hb
        rwa [mul_one] at this
    simpa only [AlgEquiv.symm_apply_apply] using key _ hz

theorem exists_basis_hat {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ P Q : Matrix (Fin n) (Fin n) (RA F E), P * Q = 1 ∧ Q * P = 1 ∧ ∀ z, z ∈ hat F (L : Set (Fin n → E)) ↔
      ∀ a, (Q *ᵥ z) a ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  choose y y' hyy hy hy' using fun a => exists_generator F (cI a) (hc a)
  have hD : Matrix.diagonal y * Matrix.diagonal y' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    exact hyy a
  have h1 : P * Matrix.diagonal y * (Matrix.diagonal y' * Q) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ Q, hD, Matrix.one_mul, hPQ]
  refine ⟨_, _, h1, mul_eq_one_comm.1 h1, fun z => ?_⟩
  have hz : z = P *ᵥ (Q *ᵥ z) := by rw [Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
  conv_lhs => rw [hz, hP, key]
  refine forall_congr' fun a => ?_
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  constructor
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy' a) _ h
    rwa [inv_mul_cancel₀ (hc a)] at this
  · intro h
    have := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy a) _ h
    rwa [mul_one, ← mul_assoc, hyy, one_mul] at this

theorem exists_isFrame {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F), Formalism.L2.DIV.IsFrame β L := by
  obtain ⟨P, Q, hPQ, hQP, h⟩ := exists_basis_hat F L hfg hsp
  let s := Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E
  have hm : ∀ A B : Matrix (Fin n) (Fin n) (RA F E), A * B = 1 → A.map s * B.map s = 1 := fun A B hAB => by
    rw [← Matrix.map_mul, hAB, Matrix.map_one _ (map_zero _) (map_one _)]
  refine ⟨⟨P.map s, Q.map s, hm _ _ hPQ, hm _ _ hQP⟩, fun x => ?_⟩
  have e : ∀ i, (Q.map s *ᵥ x) i = s ((Q *ᵥ fun j => s.symm (x j)) i) := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, AlgEquiv.apply_symm_apply, Matrix.map_apply]
  change _ ↔ ∀ i, (Q.map s *ᵥ x) i ∈ _
  simp only [e]
  constructor
  · intro hx i
    exact (mem_integral_adelic_lattice_iff F _).1 ((h _).1 (GlobalTheory.PrincInLevel.swap_symm_mem_hat L x hx) i)
  · intro hx
    have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ ((h _).2 fun i => (mem_integral_adelic_lattice_iff F _).2 (hx i))
    simpa only [s, AlgEquiv.apply_symm_apply] using this

end General

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isSDFrame : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → Formalism.L2.Herm.dualL D.sp.cm V Λ = Λ → ∃ β, IsSDFrame V β Λ 1 := by
  intro D V Λ hΛ hd
  have hl : Λ = GlobalTheory.Member.latC V := SetLike.coe_injective (hΛ.trans (GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq V).symm)
  have hfg : Λ.FG := hl ▸ V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have h1 : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
      rw [hl]; rfl
    rw [h1, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨β, hβ⟩ := exists_isFrame D.host.F Λ hfg hsp
  refine ⟨β, 0, hβ, hd, one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pow_zero, Nat.cast_one, one_smul]
    rw [← hΛ] at hx
    exact hx
  · rw [pow_zero, Nat.cast_one, one_smul, ← hΛ]
    exact hx

end GlobalTheory.AdelicFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaFunNeZero
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.WeilTransport
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.Mem.ThetaNonzero

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_isCartanInv {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : IsUnit G.det) :
    ∃ s, IsCartanInv G s := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ?_, ?_, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this

theorem exists_thetaO_ne_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D) :
    ∃ f, IsThetaFunO ψ S T f ∧ f ≠ 0 := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.Member.exists_isInfFam_family D
  have hc : ∀ (V : HSp D) τ, ∃ s, IsCartanInv (gramAt D V τ) s := fun V τ =>
    exists_isCartanInv (GlobalTheory.SmoothForms.RealPts.gramAt_herm V τ) (GlobalTheory.SmoothForms.RealPts.gramAt_unit V τ)
  choose s hs using hc
  obtain ⟨f, f0, hf⟩ := GlobalTheory.VacuumO.exists_ne_zero ψ θ hψ hθ S T (s S) (s T) (hs S) (hs T) _ _
    (GlobalTheory.PlaceModel.isSelfDualC_latFrame S) (GlobalTheory.PlaceModel.isSelfDualC_latFrame T)
  refine ⟨f, ?_, f0⟩
  simpa only [one_mul] using (hf 1).1

theorem exists_of_isCoord {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T V W : HSp D}
    {E : WO S T ≃+ WA V W} (hE : IsCoord S T V W E) : ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0 := by
  obtain ⟨f, hf, f0⟩ := exists_thetaO_ne_zero hψ S T
  have e : (f ∘ E.symm) ∘ E = f := by
    funext x
    simp
  refine ⟨f ∘ E.symm, (hE.theta_iff ψ _).1 (by rwa [e]), fun h => f0 ?_⟩
  rw [← e, h]
  rfl

theorem isCoord_of_le (S T : HSp D) (hr : S.rank ≤ T.rank) :
    IsCoord S T S T ((mulGramInv S T).trans (Matrix.transposeAddEquiv _ _ _)) := {
  cont := (continuous_id.matrix_mul continuous_const).matrix_transpose
  cont' := continuous_id.matrix_transpose.matrix_mul continuous_const
  sympl x y := by
    unfold symplOH symplH
    rw [(GlobalTheory.OrientedSmall.bridgeSmall D S T hr).1]
    rfl
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      have h : (γ * S.gram⁻¹).map (incA D) = mulGramInv S T (γ.map (incA D)) := Matrix.map_mul (f := incA D)
      exact ⟨(γ * S.gram⁻¹).transpose, congrArg Matrix.transpose h⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : γ.transpose.map (incA D) = mulGramInv S T x := congrArg Matrix.transpose hγ
      refine ⟨γ.transpose * S.gram, (Matrix.map_mul (f := incA D)).trans ?_⟩
      rw [← (mulGramInv S T).symm_apply_apply x, ← hγ']
      rfl
  inf x := (map_mulGramInv _ S T x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  fin x := (map_mulGramInv _ S T x).trans
    ⟨fun h => congrArg Matrix.transpose h, fun h => congrArg Matrix.transpose h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem exists_thetaFun_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D), ∃ f, IsThetaFun ψ V W f ∧ f ≠ 0 := by
  intro D ψ hψ V W
  rcases le_or_gt V.rank W.rank with hr | hr
  · exact exists_of_isCoord hψ (isCoord_of_le V W hr)
  · exact exists_of_isCoord hψ (isCoord_large W V hr)

end GlobalTheory.Mem.ThetaNonzero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.PlaceVec

open GlobalTheory.AdelicLatMove

variable {D : D7} (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))

theorem frMapAdj_eq (x : WO S T) : frMapAdj S T βS βT x =
    ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) * ((x.map (toEAf D)).map (cF D))ᵀ * (T.gram.map (eToEAf D) * βT.val) := by
  have e : ((x.map (cA D))ᵀ).map (toEAf D) = ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => toEAf_cA _
  unfold frMapAdj
  rw [Matrix.map_mul, Matrix.map_mul, e]
  simp only [Matrix.mul_assoc]
  rfl

theorem frMapAdj_add (x y : WO S T) : frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  have e : (((x + y).map (toEAf D)).map (cF D))ᵀ = ((x.map (toEAf D)).map (cF D))ᵀ + ((y.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => ((cF D).comp (toEAf D)).map_add (x j i) (y j i)
  rw [frMapAdj_eq, frMapAdj_eq, frMapAdj_eq, e, Matrix.mul_add, Matrix.add_mul]

theorem cF_cF_toEAf (a : AE D) : cF D (cF D (toEAf D a)) = toEAf D a := by
  rw [← toEAf_cA, ← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]

theorem sandwich_cancel {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (hA : A * A' = 1) (hG : G * G' = 1)
    (hB : B * B' = 1) (hH : H * H' = 1) : (G * A) * ((A' * G') * N * (H * B)) * (B' * H') = N := by
  calc _ = (G * (A * A') * G') * N * (H * (B * B') * H') := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hA, hB, Matrix.mul_one, Matrix.mul_one, hG, hH, Matrix.one_mul, Matrix.mul_one]

theorem gram_map_mul_inv : S.gram.map (eToEAf D) * (S.gram⁻¹).map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem frMapAdj_up : ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (x.map (toEAf D)) → IsIntM (k • frMapAdj S T βS βT x) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int ((βS⁻¹).val * (S.gram⁻¹).map (eToEAf D)) (T.gram.map (eToEAf D) * βT.val)
  refine ⟨k, hk, fun x hx => ?_⟩
  rw [frMapAdj_eq]
  exact h _ fun i j => cF_mem_int (hx j i)

theorem frMapAdj_down :
    ∃ k : ℕ, 0 < k ∧ ∀ x : WO S T, IsIntM (frMapAdj S T βS βT x) → IsIntM (k • x.map (toEAf D)) := by
  obtain ⟨k, hk, h⟩ := exists_nsmul_mul_int (S.gram.map (eToEAf D) * βS.val) ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))
  refine ⟨k, hk, fun x hx i j => ?_⟩
  have h1 := h _ hx
  rw [frMapAdj_eq, sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv (gram_map_mul_inv S) βT.mul_inv
    (gram_map_mul_inv T)] at h1
  have h2 : cF D (k • cF D (toEAf D (x i j))) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := cF_mem_int (h1 j i)
  rw [nsmul_eq_mul, RingHom.map_mul, map_natCast, cF_cF_toEAf, ← nsmul_eq_mul] at h2
  exact h2

theorem thPVecExists : ∀ D : D7, ThPVecExists D := by
  intro D ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ hS hT _ _ _ ⟨e, he⟩ f₀ hf₀
  classical
  have hinf := infPart_cA (idemSum_infPart he)
  have hSfull := selfDual_isFullLattice S ΛS hS
  have hTfull := selfDual_isFullLattice T ΛT hT
  obtain ⟨f, hf⟩ := exists_isThetaAt hf₀.1 hS hT (a := cA D e) (by rw [← RingHom.map_mul, idemSum_mul_self he]) hinf
    (GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hf₀.1 S T ΛS ΛT hS hT _ e he f₀ hf₀.2.theta hf₀.2.lat).2
    (isSBHalf_of_red hSfull hTfull hinf (frMapAdj S T βS βT) (frMapAdj_add S T βS βT) (frMapAdj_up S T βS βT)
      (frMapAdj_down S T βS βT) (Pg ∪ Q) (fun y => omegaK Pg y * omegaQ Q T.rank ξ (-1) y) fun y y' h => by
        rw [omegaK_congr Pg fun PP hPP => h PP (Finset.mem_union_left _ hPP),
          omegaQ_congr Q _ ξ _ fun PP hPP => h PP (Finset.mem_union_right _ hPP)])
  exact ⟨f, hf₀, e, he, hf⟩

end GlobalTheory.PlaceVec

end
end

