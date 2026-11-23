module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormCoprimeOfSup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionMaxCompactInterConjRadicalContainsConj
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

noncomputable section

namespace GlobalTheory.RadRedLift

theorem exists_lift_unipRad (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) (v : GL n 𝓀[k]) (hv : v ∈ unipRad 𝓀[k] e) :
    ∃ w : KO k n, (w : GL n k) ∈ unipRad k e ∧ GlobalTheory.LocGL.redK k n w = v := by
  classical
  choose A hA using fun i j => IsLocalRing.residue_surjective (R := 𝒪[k]) ((v : Matrix n n 𝓀[k]) i j)
  let B : Matrix n n 𝒪[k] := Matrix.of fun i j => if blk e i < blk e j then A i j else (1 : Matrix n n 𝒪[k]) i j
  have h1 : (IsLocalRing.residue 𝒪[k]).mapMatrix B = v := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, B, Matrix.of_apply]
    split_ifs with hij
    · exact hA i j
    · rw [CuspMax.mem_unipRad_iff_entries.1 hv i j hij]
      simp only [Matrix.one_apply]
      split_ifs <;> simp
  have hd : IsUnit B.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, h1]
    exact (Matrix.GeneralLinearGroup.det v).ne_zero
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hd
  refine ⟨GlobalTheory.LocGL.toKO k n u, CuspMax.mem_unipRad_iff_entries.2 fun i j hij => ?_, Units.ext ?_⟩
  · change algebraMap 𝒪[k] k ((u : Matrix n n 𝒪[k]) i j) = _
    rw [hu]
    simp only [B, Matrix.of_apply, if_neg hij, Matrix.one_apply]
    split_ifs <;> simp
  · simp only [GlobalTheory.LocGL.redK, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rw [← h1, ← hu]; rfl

theorem red_lift : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {r a b : ℕ} (h : a + b = r) (g₀ : GL (Fin r) k), ∃ c : GL (Fin r) 𝓀[k], ∀ v ∈ stdMaxRad 𝓀[k] h,
    ∃ (u : GL (Fin r) k) (hu : u ∈ KO k (Fin r)), u ∈ conjBy g₀ (stdMaxRad k h) ∧
      GlobalTheory.LocGL.redK k (Fin r) ⟨u, hu⟩ = c * v * c⁻¹ := by
  intro k _ _ _ _ r a b h g₀
  obtain ⟨k₀, p, hp, rfl⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k r g₀
  let κ : KO k (Fin r) := ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀, k₀, rfl⟩
  have hpP : p ∈ stdMaxParab k h := (mem_stdMaxParab h).2 fun i j hj hi => hp (show j < i from by
    rw [Fin.lt_def]; omega)
  refine ⟨GlobalTheory.LocGL.redK k (Fin r) κ, fun v hv => ?_⟩
  obtain ⟨w, hw, rfl⟩ := exists_lift_unipRad k _ v hv
  refine ⟨(κ * w * κ⁻¹ : KO k (Fin r)), (κ * w * κ⁻¹).2, ?_, ?_⟩
  · rw [mem_conjBy]
    have hn := parab_le_normalizer k _ (inv_mem hpP)
    have := (Subgroup.mem_normalizer_iff.1 hn (w : GL (Fin r) k)).1 hw
    have e : ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ : GL (Fin r) k) * p)⁻¹ *
        ((κ * w * κ⁻¹ : KO k (Fin r)) : GL (Fin r) k) * (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀ * p) =
        p⁻¹ * w * p⁻¹⁻¹ := by
      change ((κ : GL (Fin r) k) * p)⁻¹ * ((κ : GL (Fin r) k) * w * (κ : GL (Fin r) k)⁻¹) * ((κ : GL (Fin r) k) * p) = _
      group
    rw [e]
    exact this
  · rw [← map_inv, ← map_mul, ← map_mul]

end GlobalTheory.RadRedLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisable
section
noncomputable section

namespace GlobalTheory.LFun.UnitaryParam

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.LFun.ConjPlace

theorem esymm_map_conj (s : Multiset ℂ) (j : ℕ) :
    (s.map (starRingEnd ℂ)).esymm j = starRingEnd ℂ (s.esymm j) := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, map_multiset_sum, map_multiset_prod, Multiset.map_map,
    Function.comp_def]

theorem satEig_map_star (q n : ℕ) (B : Multiset ℂˣ) (j : ℕ) :
    satEig q n (B.map star) j = starRingEnd ℂ (satEig q n B j) := by
  have h : ((q : ℂ)).arg ≠ Real.pi := by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm
  have h2 := Complex.conj_cpow (q : ℂ) (((j : ℂ) * ((n : ℂ) - j)) / 2) h
  rw [satEig, satEig, map_mul, ← esymm_map_conj, Multiset.map_map, Multiset.map_map]
  congr 1
  rw [map_natCast, map_div₀, map_mul, map_sub, map_natCast, map_natCast, map_ofNat] at h2
  exact h2

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {h : G → ℂ} {x : V}

theorem form_heckeVec_comp (hK : IsCommensurated K) (hh : h ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K)
    (β : V →ₗ[ℂ] V →ₛₗ[starRingEnd ℂ] ℂ) (hβ : ∀ v w, β w v = starRingEnd ℂ (β v w))
    (hi : ∀ g v w, β (ρ g v) (ρ g w) = β v w) (θ : G →* G) (hθ : ∀ k ∈ K, θ k ∈ K)
    (hr : ∀ g, starRingEnd ℂ (h g) = h g)
    (ht : ∀ g, h g ≠ 0 → ∃ a ∈ K, ∃ b ∈ K, ∃ t, θ t = t⁻¹ ∧ g = a * t * b) :
    β (heckeVec (ρ.comp θ) K h x) x = starRingEnd ℂ (β (heckeVec ρ K h x) x) := by
  have hf := GlobalTheory.LGrp.mem_fixed.1 hx
  have bi : ∀ a ∈ K, ∀ b ∈ K, ∀ t, β (ρ (a * t * b) x) x = β (ρ t x) x := fun a ha b hb t => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf b hb]
    exact (congrArg (β _) (hf a ha).symm).trans (hi a _ _)
  have inv : ∀ t, β (ρ t⁻¹ x) x = starRingEnd ℂ (β (ρ t x) x) := fun t => by
    rw [← hβ, ← hi t]; simp
  have e1 := (β.flip x).toAddMonoidHom.map_finsum (finite_heckeVec hK hh (ρ.comp θ) x)
  have e2 := ((starRingEnd ℂ).toAddMonoidHom.comp (β.flip x).toAddMonoidHom).map_finsum (finite_heckeVec hK hh ρ x)
  refine e1.trans (Eq.trans (finsum_congr fun c => ?_) e2.symm)
  change β (h c.out • ρ (θ c.out) x) x = starRingEnd ℂ (β (h c.out • ρ c.out x) x)
  rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, hr]
  by_cases h0 : h c.out = 0
  · simp [h0]
  obtain ⟨a, ha, b, hb, t, htt, e⟩ := ht _ h0
  congr 1
  rw [e, map_mul θ, map_mul θ, bi _ (hθ a ha) _ (hθ b hb), bi _ ha _ hb, htt, inv]

end General

theorem map_star_eq_map_inv (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (V : Type)
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (x : V)
    (B : Multiset ℂˣ) (hU : GlobalTheory.LGrp.IsUnitarisable ρ) (hx : IsSatVecGL w ρ x B) :
    B.map star = B.map (·⁻¹) := by
  classical
  obtain ⟨β, hβ, hpos, hi⟩ := hU
  let c := RingEquiv.refl (w.adicCompletion E)
  have hc : ∀ a, Valued.v (c a) = Valued.v a := fun _ => rfl
  have hx' := isSatVecGL_invT c hc rfl hx
  have hK := mem_iff_invT (n := n) c (map_mem_Ov_iff c hc)
  obtain ⟨p, hp⟩ := exists_isUnifV w
  obtain ⟨ϖ, rfl⟩ : ∃ ϖ : (w.adicCompletion E)ˣ, ϖ = p :=
    ⟨Units.mk0 p fun e => by simp [IsUnifV, e] at hp, rfl⟩
  have hne : β x x ≠ 0 := fun h0 => by simpa [h0] using hpos x hx.1
  refine eq_of_satEig_eq (qV_ne_zero w) (by simpa using hx.2.2.1) hx'.2.2.1 fun j hj => ?_
  have key := form_heckeVec_comp (Final.GLintComm E w n) (Tj_mem_hecke hp j) hx.2.1 β hβ hi
    (invT c n).symm.toMonoidHom (fun k hk => (hK _).2 (by simpa using hk))
    (fun g => by rw [Tj_apply]; split_ifs <;> simp)
    (fun g hg => by
      rw [Tj_apply] at hg
      obtain ⟨a, ha, b, hb, e⟩ : ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
          g = a * dGL n ϖ j * b := by
        by_contra hn
        exact hg (if_neg hn)
      exact ⟨a, ha, b, hb, _, (invT c n).symm_apply_eq.2 (invT_dGL c ϖ j).symm, e⟩)
  rw [hx'.2.2.2 _ hp j hj, hx.2.2.2 _ hp j hj, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, smul_eq_mul, map_mul, ← hβ] at key
  rw [satEig_map_star]
  exact (mul_right_cancel₀ hne key).symm

end GlobalTheory.LFun.UnitaryParam

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeHasRigidification
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.ConstRatio

namespace GlobalTheory.RigExists

theorem exists_cartan_onb {k p q : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (h : Formalism.UG.HasSignature G p q) :
    ∃ s B : Matrix (Fin k) (Fin k) ℂ, IsCartanInv G s ∧ IsONBasis G s B p := by
  obtain ⟨e, P, hP⟩ := h
  have hk : k = p + q := by simpa using Fintype.card_congr e
  subst hk
  set f : Fin (p + q) ≃ Fin p ⊕ Fin q := finSumFinEquiv.symm with hf
  set ε : Fin (p + q) → ℝ := fun a => if a.val < p then 1 else -1 with hε
  set B : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := (P : Matrix _ _ ℂ).submatrix e f with hB
  set A : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := ((P⁻¹ : GL _ ℂ) : Matrix _ _ ℂ).submatrix f e with hA
  set Dg : Matrix (Fin (p + q)) (Fin (p + q)) ℂ := Matrix.diagonal fun a => (ε a : ℂ) with hDg
  have e1 : B * A = 1 := by
    rw [hB, hA, ← Matrix.submatrix_mul _ _ _ _ _ f.bijective, Units.mul_inv, Matrix.submatrix_one_equiv]
  have e2 : A * B = 1 := by
    rw [hB, hA, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, Units.inv_mul, Matrix.submatrix_one_equiv]
  have hG : G = (G.reindex e e).submatrix e e := by
    ext i j; simp
  have hcT : Formalism.UG.cT (starRingEnd ℂ) (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (P : Matrix _ _ ℂ)ᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT] at hP
  have hD : Bᴴ * G * B = Dg := by
    have : Bᴴ * G * B = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * G.reindex e e *
        (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)).submatrix f f := by
      rw [hB, Matrix.conjTranspose_submatrix, hG, ← Matrix.submatrix_mul _ _ _ _ _ e.bijective,
        ← Matrix.submatrix_mul _ _ _ _ _ e.bijective, ← hG]
    rw [this, hP]
    ext i j
    refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun b => ?_) (fun b => ?_) j <;>
      simp [Formalism.UG.Jpq, hf, hDg, hε, Matrix.diagonal_apply, Matrix.one_apply, Fin.ext_iff] <;> (try omega) <;> split_ifs <;> simp
  have hDD : Dg * Dg = 1 := by
    rw [hDg, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; simp only [hε]; split_ifs <;> simp
  have hDh : Dgᴴ = Dg := by
    rw [hDg, Matrix.diagonal_conjTranspose]
    congr 1; funext a; simp [hε]
  have e3 : Bᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
  have e4 : Aᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
  have hGA : G = Aᴴ * Dg * A := by
    rw [← hD]
    calc G = (Aᴴ * Bᴴ) * G * (B * A) := by rw [e4, e1, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  refine ⟨B * Dg * A, B, ⟨?_, ?_, ?_⟩, ε, fun a => ?_, hD, ?_⟩
  · calc B * Dg * A * (B * Dg * A) = B * (Dg * (A * B) * Dg) * A := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e2, Matrix.mul_one, hDD, Matrix.mul_one, e1]
  · conv_lhs => rw [hGA]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ Aᴴ, e3, Matrix.one_mul, ← Matrix.mul_assoc A B, e2, Matrix.one_mul,
      ← Matrix.mul_assoc Dg Dg, hDD, Matrix.one_mul, hGA, Matrix.mul_assoc]
  · have : G * (B * Dg * A) = Aᴴ * A := by
      rw [hGA]
      calc Aᴴ * Dg * A * (B * Dg * A) = Aᴴ * (Dg * (A * B) * Dg) * A := by simp only [Matrix.mul_assoc]
        _ = Aᴴ * A := by rw [e2, Matrix.mul_one, hDD, Matrix.mul_one]
    rw [this]
    exact Matrix.PosDef.conjTranspose_mul_self A
      (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse e1)))
  · simp only [hε]; split_ifs with h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr ⟨rfl, not_lt.1 h⟩
  · calc B * Dg * A * B = B * Dg * (A * B) := by simp only [Matrix.mul_assoc]
      _ = B * Dg := by rw [e2, Matrix.mul_one]

theorem exists_rig : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    IsSelfDualC V Λ → ∃ r : Rig V, r.Λ = Λ ∧ r.Is := by
  intro D V Λ hV hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E V.rank Λ hfull
  have hτ : ∀ τ : D.what₂.Tau, ∃ s B : Matrix (Fin V.rank) (Fin V.rank) ℂ,
      IsCartanInv (gramAt D V τ) s ∧ ∃ p, IsONBasis (gramAt D V τ) s B p := fun τ => by
    obtain ⟨s, B, h1, h2⟩ := exists_cartan_onb (gramAt D V τ) (hV (tauE D τ))
    exact ⟨s, B, h1, _, h2⟩
  choose s B hsB using hτ
  exact ⟨⟨Λ, β, s, B⟩, rfl, hΛ, hβ, hsB⟩

end GlobalTheory.RigExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitProjAdeleComponentChartProperties
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitProjChart

variable {D : D7} {v : FinPl D}

def emb (φ : SplitProj D v) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  (φ.restrictScalars D.host.F).comp Algebra.TensorProduct.includeRight

theorem emb_apply (φ : SplitProj D v) (x : D.host.E) : emb φ x = rdQ φ x := rfl

theorem splitProj_emb (φ : SplitProj D v) : GlobalTheory.AdelicU.splitProj (emb φ) = φ := by
  refine AlgHom.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    rw [GlobalTheory.AdelicU.splitProj_tmul, emb_apply, rdQ, ← smul_eq_mul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]

theorem chart_idem (φ : SplitProj D v) : GlobalTheory.SplitHecke.Chart (GlobalTheory.EmbChart.idem (emb φ)) v (rdA φ) := by
  have h := GlobalTheory.EmbChart.chart_idem (emb φ)
  rw [splitProj_emb] at h
  exact h

theorem rdA_idem (φ : SplitProj D v) : rdA φ (GlobalTheory.EmbChart.idem (emb φ)) = 1 := by
  change φ (GlobalTheory.AdelicU.compFin D.host.F D.host.E v (GlobalTheory.EmbChart.idem (emb φ))) = 1
  rw [GlobalTheory.EmbChart.compFin_idem]
  nth_rewrite 1 [← splitProj_emb φ]
  exact GlobalTheory.AdelicU.splitProj_splitIdem _ _

theorem eq_idem {φ : SplitProj D v} {e : AE D} (he : IsIdemOf φ e) : e = GlobalTheory.EmbChart.idem (emb φ) := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero he.1 (GlobalTheory.EmbChart.isSplitIdem_idem _)).resolve_right fun h => ?_
  have := congrArg (rdA φ) h
  rw [map_mul, he.2.2, rdA_idem, map_zero, mul_one] at this
  exact one_ne_zero this

theorem rdE_toEAf (φ : SplitProj D v) (a : AE D) : rdE φ (toEAf D a) = rdA φ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem rdA_incA (φ : SplitProj D v) (x : D.host.E) : rdA φ (incA D x) = rdQ φ x := by
  change φ (GlobalTheory.AdelicU.evFin D.host.F v 1 ⊗ₜ x) = _
  rw [map_one]; rfl

theorem continuous_rdA (φ : SplitProj D v) : Continuous (rdA φ) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  refine IsModuleTopology.continuous_of_ringHom (R := AF D.host.F) (rdA φ) ?_
  have h1 : Continuous (GlobalTheory.AdelicU.evFin D.host.F v) := (RestrictedProduct.continuous_eval v).comp continuous_snd
  exact h1.congr fun y => ((chart_idem φ).2.2.1 y).symm

theorem chart_rdA : ∀ (D : D7) (v : FinPl D) (φ : SplitProj D v) (e : AE D), IsIdemOf φ e → GlobalTheory.SplitHecke.Chart e v (rdA φ) ∧ (∀ a : AE D, rdE φ (toEAf D a) = rdA φ a) ∧ (∀ x : D.host.E, rdA φ (incA D x) = rdQ φ x) ∧ Continuous (rdA φ) ∧ ∀ e', IsIdemOf φ e' → e' = e :=
  fun _ _ φ _ he => ⟨eq_idem he ▸ chart_idem φ, rdE_toEAf φ, rdA_incA φ, continuous_rdA φ,
    fun _ he' => (eq_idem he').trans (eq_idem he).symm⟩

end GlobalTheory.SplitProjChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
section
open MeasureTheory ValuativeRel GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.StandardMaximalParabolic

namespace GlobalTheory.RadRev

open Matrix

variable {R : Type} [CommRing R] {α β n : Type} {m : α → Type} {m' : β → Type}
  [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype β] [LinearOrder β] [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
  [Fintype n] [DecidableEq n]

theorem mem_unipRad_entries {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, ¬ blk e i < blk e j → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad, mem_parab]
  constructor
  · rintro ⟨hP, hD⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.mp hij) with hlt | heq
    · have hne : i ≠ j := fun hh => (ne_of_lt hlt) (by rw [hh])
      rw [hP i j hlt, Matrix.one_apply_ne hne]
    · obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at heq
      subst heq
      rw [hD]
      by_cases hs : i' = j'
      · subst hs
        simp
      · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]
  · intro H
    refine ⟨fun i j hji => ?_, fun a i j => ?_⟩
    · have hne : i ≠ j := fun hh => (ne_of_lt hji) (by rw [hh])
      rw [H i j (not_lt.mpr hji.le), Matrix.one_apply_ne hne]
    · rw [H _ _ (by simp)]
      by_cases hs : i = j
      · subst hs
        simp
      · rw [Matrix.one_apply_ne hs, Matrix.one_apply_ne (fun hh => hs (by simpa using e.injective hh))]


omit [Fintype α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype β] [∀ a, Fintype (m' a)]
  [∀ a, DecidableEq (m' a)] in
theorem blk_lt_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') {i j : n} (hij : blk e' j < blk e' i) : blk e j < blk e i := by
  have hne : i ≠ j := fun hh => (ne_of_lt hij) (by rw [hh])
  by_contra hc
  have hdet : IsUnit (Matrix.transvection i j (1 : R)).det := by
    rw [Matrix.det_transvection_of_ne _ _ hne]
    exact isUnit_one
  obtain ⟨t, ht⟩ : ∃ t : GL n R, (t : Matrix n n R) = Matrix.transvection i j (1 : R) :=
    ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩
  have hent : ∀ k l, (t : Matrix n n R) k l = (1 : Matrix n n R) k l + if i = k ∧ j = l then 1 else 0 := by
    intro k l
    rw [ht]
    simp [Matrix.transvection, Matrix.single_apply]
  have hmem : t ∈ parab R e := by
    change (t : Matrix n n R).BlockTriangular (blk e)
    intro k l hkl
    have hkl' : k ≠ l := fun hh => (ne_of_lt hkl) (by rw [hh])
    rw [hent, Matrix.one_apply_ne hkl', zero_add, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hc hkl
  have hzero : (t : Matrix n n R) i j = 0 := (h hmem) hij
  rw [hent, Matrix.one_apply_ne hne, zero_add, if_pos ⟨rfl, rfl⟩] at hzero
  exact one_ne_zero hzero

theorem unipRad_le_of_parab_le [Nontrivial R] {e : (Σ a, m a) ≃ n} {e' : (Σ a, m' a) ≃ n}
    (h : parab R e ≤ parab R e') : unipRad R e' ≤ unipRad R e := by
  intro g hg
  rw [mem_unipRad_entries] at hg ⊢
  intro i j hij
  exact hg i j (fun hlt => hij (blk_lt_of_parab_le h hlt))

theorem stdMaxRad_le_unipRad : ∀ (F : Type) [Field F] {r a b s : ℕ} (h : a + b = r) (d : Fin s → ℕ)
    (hd : ∑ i, d i = r),
    parab F (stdBlocks d hd) ≤ stdMaxParab F h → stdMaxRad F h ≤ unipRad F (stdBlocks d hd) := by
  intro F _ r a b s h d hd hle
  exact unipRad_le_of_parab_le hle

end GlobalTheory.RadRev
end

