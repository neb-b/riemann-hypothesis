module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1089
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLatticeIsLatticeSelfDualHermitianModel
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

noncomputable section

namespace GlobalTheory.InertUnitOrb.SelfDualLat

theorem stdH_eq_dot (K : UQ) {n : ℕ} (a b : Fin n → K.E) :
    stdH K n a b = a ⬝ᵥ (fun k => K.c (b k)) := rfl

theorem stdH_mulVec (K : UQ) {n : ℕ} (P : Matrix (Fin n) (Fin n) K.E)
    (hP : Pᵀ * P.map K.c = 1) (u v : Fin n → K.E) :
    stdH K n (P *ᵥ u) (P *ᵥ v) = stdH K n u v := by
  have hv : (fun k => K.c ((P *ᵥ v) k)) = P.map K.c *ᵥ (fun k => K.c (v k)) := by
    funext k
    exact RingHom.map_mulVec (K.c : K.E →+* K.E) P v k
  rw [stdH_eq_dot, stdH_eq_dot, hv, dotProduct_mulVec, ← vecMul_transpose, vecMul_vecMul, hP, vecMul_one]

theorem intVec_eq_range (K : UQ) (n : ℕ) :
    intVec K n = LinearMap.range ((Algebra.linearMap K.O K.E).compLeft (Fin n)) := by
  ext v
  constructor
  · intro hv
    have h := fun i => RingHom.mem_range.mp (hv i)
    choose o ho using h
    exact ⟨o, funext fun i => ho i⟩
  · rintro ⟨o, rfl⟩ i
    exact ⟨o i, rfl⟩

theorem intVec_fg (K : UQ) (n : ℕ) : (intVec K n).FG := by
  rw [intVec_eq_range, LinearMap.range_eq_map]
  exact Submodule.FG.map _ Module.Finite.fg_top

theorem single_mem_intVec (K : UQ) {n : ℕ} (i : Fin n) : (Pi.single i (1 : K.E) : Fin n → K.E) ∈ intVec K n := by
  intro j
  by_cases h : j = i
  · subst h; exact ⟨1, by simp⟩
  · exact ⟨0, by simp [Pi.single_apply, h]⟩

theorem unitLat_isLat_selfDual : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (n : ℕ) (B : InvAlg K) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), ∀ (x : B.Aˣ), B.σ (x : B.A) = x → (∀ y z, stdH K n (ψ y) (ψ z) = B.herm x y z) → ∀ q : UL n w, IsLat K.O K.E (unitLat e B ψ q) ∧ ∀ y, y ∈ unitLat e B ψ q ↔ ∀ z ∈ unitLat e B ψ q, B.herm x y z ∈ (algebraMap K.O K.E).range := by
  intro E _ _ _ _ w hns K e he hint n B ψ x hx hψ q
  set Qm : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
    (((q⁻¹ : UL n w) : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) with hQm
  have hmem : ∀ g : GLw n w, g ∈ UL n w → g ∈ UJ (cj w) 1 := by
    intro g hg
    simpa [UL, hns] using hg
  have hQ : cT (cj w) Qm * 1 * Qm = 1 := hmem _ (q⁻¹).2
  have h2 : (Qm.map (cj w))ᵀ * Qm = 1 := by simpa [cT] using hQ
  set P : Matrix (Fin n) (Fin n) K.E := Qm.map e.symm with hPdef
  have hPc : P.map K.c = (Qm.map (cj w)).map e.symm := by
    ext i j
    apply e.injective
    simp [hPdef, he]
  have hP1 : (P.map K.c)ᵀ * P = 1 := by
    have h3 := congrArg (e.symm.toRingHom.mapMatrix) h2
    simp only [map_mul, map_one, RingHom.mapMatrix_apply] at h3
    rw [hPc, hPdef, ← Matrix.transpose_map]
    simpa using h3
  have hPR : P * (P.map K.c)ᵀ = 1 := mul_eq_one_comm.mp hP1
  have hPT : Pᵀ * P.map K.c = 1 := by
    have h4 := congrArg Matrix.transpose hP1
    simpa [Matrix.transpose_mul] using h4
  let G : (Fin n → K.E) →ₗ[K.E] B.A := ψ.symm.toLinearMap ∘ₗ Matrix.toLin' (P.map K.c)ᵀ
  have hGP : ∀ y, G (P *ᵥ ψ y) = y := by
    intro y
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hP1]
  have hPG : ∀ a, P *ᵥ ψ (G a) = a := by
    intro a
    simp [G, Matrix.toLin'_apply, mulVec_mulVec, hPR]
  have hmemL : ∀ y, y ∈ unitLat e B ψ q ↔ P *ᵥ ψ y ∈ intVec K n := fun y => Iff.rfl
  have hmap : unitLat e B ψ q = (intVec K n).map (G.restrictScalars K.O) := by
    ext y
    rw [hmemL]
    constructor
    · intro hy
      exact ⟨P *ᵥ ψ y, hy, hGP y⟩
    · rintro ⟨a, ha, rfl⟩
      rw [LinearMap.restrictScalars_apply, hPG]
      exact ha
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hmap]
    exact (intVec_fg K n).map _
  · apply top_unique
    intro y _
    rw [← hGP y, ← Finset.univ_sum_single (P *ᵥ ψ y), map_sum]
    apply Submodule.sum_mem
    intro i _
    have hi : G (Pi.single i (1 : K.E)) ∈ unitLat e B ψ q := by
      rw [hmemL, hPG]
      exact single_mem_intVec K i
    have hs : G (Pi.single i (1 : K.E)) ∈ Submodule.span K.E (unitLat e B ψ q : Set B.A) :=
      Submodule.subset_span hi
    have heq : Pi.single i ((P *ᵥ ψ y) i) = (P *ᵥ ψ y) i • Pi.single i (1 : K.E) := by
      ext j
      simp [Pi.single_apply]
    rw [heq, map_smul]
    exact Submodule.smul_mem _ _ hs
  · intro y
    rw [hmemL]
    constructor
    · intro hy z hz
      rw [hmemL] at hz
      rw [← hψ, ← stdH_mulVec K P hPT]
      unfold stdH
      apply Subring.sum_mem
      intro k _
      apply Subring.mul_mem _ (hy k)
      obtain ⟨o, ho⟩ := hz k
      obtain ⟨o', ho'⟩ := K.c_int o
      exact ⟨o', by rw [← ho, ho']⟩
    · intro h i
      have h5 := h (G (Pi.single i 1)) (by rw [hmemL, hPG]; exact single_mem_intVec K i)
      rw [← hψ, ← stdH_mulVec K P hPT, hPG] at h5
      simpa [stdH, Pi.single_apply, apply_ite] using h5

end GlobalTheory.InertUnitOrb.SelfDualLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalSignEqOneOfIntegralSeparableReductio
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT

theorem kapSign_eq_one_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E),
    (∀ x, cj w (cj w x) = x) → (∀ x, Valued.v (cj w x) = Valued.v x) →
    ∀ P₀ : (w.adicCompletionIntegers E)[X], IsCoprime P₀ (derivative P₀) →
    ∀ γ : UL n w, γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    γ ∈ KL n w → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ n w hinv hv P₀ hcop γ hchar hK Q₁ hdvd
  unfold kapSign
  split_ifs with hs
  · rfl
  simp only
  have hU : (γ.1.val.map (cj w))ᵀ * γ.1.val = 1 := by
    have h2 : (UL n w : Subgroup (GLw n w)) = UJ (cj w) 1 := by unfold UL; rw [if_neg hs]
    have h : γ.1 ∈ UJ (cj w) 1 := by rw [← h2]; exact γ.2
    simpa [UJ, cT] using h
  set K := w.adicCompletion E
  set f := algebraMap (w.adicCompletionIntegers E) K with hf
  have finj : Function.Injective f := fun a b h => Subtype.ext h
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.1.val Q₁)) with hV₁
  set G := (Matrix.of fun i j => ∑ k, cj w ((Module.finBasis K V₁ i).1 k) * (Module.finBasis K V₁ j).1 k) with hG
  by_cases h0 : G.det = 0
  · rw [h0]; simp [ordL]
  obtain ⟨g, hg⟩ := hK
  have hγ : γ.1.val = g.val.map (fun x => (x : K)) := by
    have := congrArg (fun u => (u : GLw n w).val) hg
    simpa [bc] using this.symm
  have hmon : P₀.Monic := by
    apply Polynomial.monic_of_injective finj
    rw [← hchar]; exact Matrix.charpoly_monic _
  obtain ⟨Q₁₀, Q₂₀, A, B, c, hc, hP, hAB, hQ⟩ := _root_.GlobalTheory.monic_dvd_integral_factor_bezout E w P₀ hmon hcop Q₁ hdvd
  set q₁ := Q₁₀.map f
  set q₂ := Q₂₀.map f
  have hAB' : A.map f * q₁ + B.map f * q₂ = 1 := by
    have := congrArg (Polynomial.map f) hAB
    simpa [Polynomial.map_add (f := _), Polynomial.map_mul] using this
  have hCH : aeval γ.1.val (q₁ * q₂) = 0 := by
    rw [← Polynomial.map_mul, ← hP, ← hchar]; exact Matrix.aeval_self_charpoly _
  have hmem : ∀ x, x ∈ V₁ ↔ aeval γ.1.val q₁ *ᵥ x = 0 := by
    intro x
    rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply, hQ, map_mul, aeval_C]
    rw [show (algebraMap K (Matrix (Fin n) (Fin n) K) c) = c • (1 : Matrix (Fin n) (Fin n) K) from
      (Algebra.algebraMap_eq_smul_one c)]
    rw [smul_mul_assoc, one_mul, Matrix.smul_mulVec, smul_eq_zero]
    simp [hc]
  set e := aeval γ.1.val (q₂ * B.map f) with he
  have heint : ∀ i j, Valued.v (e i j) ≤ 1 := by
    intro i j
    have : e = (aeval g.val (Q₂₀ * B)).map (fun x => (x : K)) := by
      rw [he, ← Polynomial.map_mul, Polynomial.aeval_map_algebraMap, hγ,
        show g.val.map (fun x => (x : K)) = (Algebra.ofId (w.adicCompletionIntegers E) K).mapMatrix g.val from rfl,
        Polynomial.aeval_algHom_apply]
      rfl
    rw [this, Matrix.map_apply]
    exact ((aeval g.val (Q₂₀ * B)) i j).2
  have hcomm1 : ∀ x, aeval γ.1.val q₁ *ᵥ (e *ᵥ x) = 0 := by
    intro x
    rw [Matrix.mulVec_mulVec, he, ← map_mul, ← mul_assoc, map_mul, hCH, zero_mul, Matrix.zero_mulVec]
  have he1 : e = 1 - aeval γ.1.val (A.map f) * aeval γ.1.val q₁ := by
    rw [he, ← map_mul, mul_comm q₂, eq_sub_iff_add_eq, ← map_add (f := _), add_comm, hAB', map_one]
  have hfix : ∀ x ∈ V₁, e *ᵥ x = x := by
    intro x hx
    rw [he1, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, (hmem x).1 hx,
      Matrix.mulVec_zero, sub_zero]
  have hker2 : ∀ y, aeval γ.1.val q₂ *ᵥ (y - e *ᵥ y) = 0 := by
    intro y
    rw [he1, Matrix.sub_mulVec, Matrix.one_mulVec, sub_sub_cancel, Matrix.mulVec_mulVec, ← map_mul, ← map_mul,
      show q₂ * (A.map f * q₁) = A.map f * (q₁ * q₂) by ring, map_mul, hCH, mul_zero, Matrix.zero_mulVec]
  have horth := _root_.GlobalTheory.UnitaryOrth.ker_orthogonal_of_coprime K (cj w) n γ.1.val hU q₁ q₂ (A.map f) (B.map f) hAB' hCH V₁ hmem (Module.finBasis K V₁) h0
  obtain ⟨s, fb, hfb⟩ := _root_.GlobalTheory.IdempotentUnimodular.main E w (cj w) hinv hv n V₁ e heint (fun x => (hmem _).2 (hcomm1 x)) hfix
    (fun x hx y => horth x hx _ (hker2 y))
  exact _root_.GlobalTheory.GramParity.gram_det_parity E w (cj w) hv n V₁ (Module.finBasis K V₁) fb hfb

end GlobalTheory.BCT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMassLowerBoundOfOrthonormalLatticeFrames
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.StdMass

variable {D : D7}

theorem coord_isIntegral (V : HSp D) (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame))
    {x : Fin V.rank → D.host.E} (hx : x ∈ L0c D V) (k : Fin V.rank) : IsIntegral ℤ (x k) := by
  have key : ∀ y ∈ V.L0, ∃ a : 𝓞 D.host.E, (a : D.host.E) = V.frame.repr y k := by
    intro y hy
    rw [hL] at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      by_cases h : j = k
      · exact ⟨1, by simp [h]⟩
      · exact ⟨0, by simp [Finsupp.single_apply, h]⟩
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by simp [ha, hb]⟩
    | smul r y _ hy =>
      obtain ⟨a, ha⟩ := hy
      refine ⟨r * a, ?_⟩
      rw [← algebraMap_smul D.host.E r y, map_smul]
      simp [ha, Algebra.smul_def]
  have hx' : ∑ i, x i • V.frame i ∈ V.L0 := hx
  obtain ⟨a, ha⟩ := key _ hx'
  have e : V.frame.repr (∑ i, x i • V.frame i) k = x k := by
    rw [← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← e, ← ha]
  exact RingOfIntegers.isIntegral_coe a

theorem mem_lattice_of_rational_mem_completion (V : HSp D) (v : Fin V.rank → D.host.E)
    (h : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] v k) ∈ latHat D.host.F D.host.E (L0c D V)) : v ∈ L0c D V := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hw
      refine ⟨V.frame.equivFun.symm w, ?_, V.frame.equivFun.apply_symm_apply w⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hw
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
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective w
    have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
      rw [hfull]; trivial
    have := Submodule.mem_map_of_mem (f := f) hx
    rw [Submodule.map_span] at this
    exact this
  have hr := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L (V.standardTuple_isLattice.fg.map _) hsp).1 v
  rw [← hL]
  refine hr.1 ?_
  have hle : latHat D.host.F D.host.E (L0c D V) ≤ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    rw [← hL] at hx
    exact AddSubgroup.subset_closure ⟨a, fun w => ha w, x, hx, rfl⟩
  exact hle h

theorem card_stab_le (V : HSp D) (hg : V.gram = 1)
    (hL : V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame)) :
    Nat.card (Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1) ≤ NumberField.Units.torsionOrder D.host.E ^ V.rank * V.rank.factorial := by
  obtain ⟨hSf, hSc⟩ := _root_.GlobalTheory.LowRow.SignedPerm.finite_and_ncard_le D V.rank
  have hx : ∀ x : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1, ∃ u : GL (Fin V.rank) D.host.E,
        u ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram ∧
        Formalism.UG.bc (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) u =
          HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 := fun x => by
    obtain ⟨u, hu, e⟩ := Subgroup.mem_map.1 x.1.2
    exact ⟨u, hu, e⟩
  choose u hu hue using hx
  have hunit : ∀ x, (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E)ᴴ * (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 :=
    fun x => by
    have h := hu x
    change Formalism.UG.cT _ (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = V.gram at h
    rw [hg, Matrix.mul_one] at h
    convert h using 2
    ext a b
    rfl
  have hint : ∀ x a b, IsIntegral ℤ ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) a b) := fun x a b => by
    have hK : x.1.1 ∈ GlobalTheory.Mass.Levels.latStab V := by
      have := x.2
      simpa [Formalism.UG.stabAt] using this
    have hej : (Pi.single b 1 : Fin V.rank → D.host.E) ∈ L0c D V := by
      show ∑ i, (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) i • V.frame i ∈ V.L0
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [hc]) (by simp), hL]
      rw [Pi.single_eq_same, one_smul]
      exact Submodule.subset_span ⟨b, rfl⟩
    have hy : (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) ∈
        latHat D.host.F D.host.E (L0c D V) :=
      AddSubgroup.subset_closure ⟨1, fun w => by rw [map_one]; exact one_mem _, _, hej, rfl⟩
    have h2 := ((GlobalTheory.Mass.Levels.mem_latStab V x.1.1).1 hK _).1 hy
    have e : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1).1 *ᵥ
        (fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (Pi.single b (1 : D.host.E) : Fin V.rank → D.host.E) k) =
        fun k => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b := by
      rw [← hue x]
      funext k
      change ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) *ᵥ
        ((inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ∘ (Pi.single b 1))) k =
          (inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F)) ((u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) k b)
      rw [← RingHom.map_mulVec]
      simp [Matrix.mulVec_single_one]
    rw [e] at h2
    exact coord_isIntegral V hL (mem_lattice_of_rational_mem_completion V _ h2) a
  let f : Formalism.UG.stabAt (GlobalTheory.Mass.ratIn (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram)
      (GlobalTheory.Mass.Levels.latStab V) 1 →
      {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
    fun x => ⟨(u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E), hunit x, hint x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (u x : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = u y := congrArg Subtype.val hxy
    have h2 : u x = u y := Units.ext h1
    have h3 : HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram x.1.1 =
        HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig V.gram y.1.1 := by
      rw [← hue x, ← hue y, h2]
    have h4 : x.1.1 = y.1.1 := Subtype.ext h3
    exact Subtype.ext (Subtype.ext h4)
  haveI := hSf.to_subtype
  calc Nat.card _ ≤ Nat.card {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_le_card_of_injective f hf
    _ = Set.ncard {g : Matrix (Fin V.rank) (Fin V.rank) D.host.E | gᴴ * g = 1 ∧ ∀ a b, IsIntegral ℤ (g a b)} :=
        Nat.card_coe_set_eq _
    _ ≤ _ := hSc

theorem massLower_of_stdV : ∀ D : D7, StdV D → MassLower D := by
  intro D hS i _
  obtain ⟨h1, h2⟩ := hS i
  have hg : (Vc D i).gram = 1 := Matrix.ext fun a b => by
    rw [Matrix.one_apply]
    exact h1 a b
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ => by
    have e : gramAt D (Vc D i) τ = 1 := Matrix.ext fun a b => by
      simp [gramAt, hg, Matrix.one_apply]
    rw [e]
    exact Matrix.PosDef.one
  have hK := GlobalTheory.Mass.Levels.latStab_compact_open (Vc D i)
  have hfc := GlobalTheory.Mass.finiteClasses_unitary (GlobalTheory.DefiniteQuotient.cmExt D)
    (GlobalTheory.DefiniteQuotient.gram_hermND (Vc D i)) (GlobalTheory.DefiniteQuotient.isTotDef_of_posDef (Vc D i) hpd) hK.1 hK.2
  have hle := hfc.inv_card_le 1
  have hpos := hfc.stabOrder_pos (DoubleCoset.mk _ _ 1)
  rw [GlobalTheory.Mass.stabOrder_mk] at hpos
  have hc := card_stab_le (Vc D i) hg h2
  have hr : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  unfold GlobalTheory.Mass.unitaryMass
  refine le_trans ?_ hle
  rw [one_div, ← hr]
  exact inv_anti₀ (by exact_mod_cast hpos) (by exact_mod_cast hc)

end GlobalTheory.LowRow.StdMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStringForcesLongPart
section
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_string_forces_long_part : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (c : ℕ) (d : Fin c → ℕ)
    (S : Fin c → Multiset ℂˣ) (T : Multiset ℂˣ) (t : ℕ) (ν : ℂ),
  1 ≤ t → (∀ i, ∀ s ∈ S i, ‖(s : ℂ)‖ = 1) → ‖ν‖ = 1 →
  ∑ i, ∑ k : Fin (d i), (S i).map (fun z => (z : ℂ) * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
    T.map (fun z => (z : ℂ)) →
  (Multiset.range t).map (fun c : ℕ => ν * ((Ideal.absNorm w.asIdeal : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - c)) ≤
    T.map (fun z => (z : ℂ)) →
  ∃ i, t ≤ d i := by
  intro E _ _ w c d S T t ν ht hS hν hsum hle
  have hN1 : 1 < Ideal.absNorm w.asIdeal := by
    have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
    have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
    omega
  set N := Ideal.absNorm w.asIdeal with hN
  have hmem : ν * ((N : ℕ) : ℂ) ^ (((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ)) ∈ T.map (fun z => (z : ℂ)) :=
    Multiset.mem_of_le hle (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩)
  rw [← hsum] at hmem
  obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 hmem
  obtain ⟨k, -, hk⟩ := Multiset.mem_sum.1 hi
  obtain ⟨s, hs, hsk⟩ := Multiset.mem_map.1 hk
  have hs1 : ‖s‖ = 1 := by
    simp only [Multiset.bind_def, Multiset.pure_def, Multiset.mem_bind, Multiset.mem_singleton] at hs
    obtain ⟨u, hu, rfl⟩ := hs
    exact hS i u hu
  have hNpos : 0 < N := by omega
  have hn := congrArg (fun z : ℂ => ‖z‖) hsk
  simp only [norm_mul, hs1, hν, one_mul, Complex.norm_natCast_cpow_of_pos hNpos] at hn
  have hre : ((((d i : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))).re = ((d i : ℝ) - 1) / 2 - (k : ℕ) := by simp
  have hre2 : ((((t : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))).re = ((t : ℝ) - 1) / 2 := by simp
  rw [hre, hre2] at hn
  have hN1' : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
  have hle' := (Real.rpow_le_rpow_left_iff hN1').1 hn.ge
  have hk' : ((k : ℕ) : ℝ) ≥ 0 := by positivity
  refine ⟨i, ?_⟩
  have : (t : ℝ) ≤ d i := by linarith
  exact_mod_cast this

end GlobalTheory
end

