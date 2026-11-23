module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SmoothAt
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.smoothAt_pf :
    UpperTheory.Gal.Gen.SmoothAt := by
  intro E _ _ _ a w₀ hw W f
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w₀ hw
  let p : GL (Fin a) (w₀.adicCompletion E) → finU (E := E) (n := a) := fun y =>
    ⟨(e.symm y).1, (Subgroup.mem_inf.1 (e.symm y).2).1⟩
  have hp : Continuous p :=
    Continuous.subtype_mk (continuous_subtype_val.comp e.symm.continuous) _
  have hp1 : p 1 = 1 := by
    apply Subtype.ext
    simp [p]
  have hS : IsOpen {k : finU (E := E) (n := a) | algRep W k f = f} := GlobalTheory.DefU.isSmooth_algRep W f
  refine ⟨p ⁻¹' {k : finU (E := E) (n := a) | algRep W k f = f},
    (hS.preimage hp).mem_nhds (by simp [hp1]), fun x hx hxN v g => ?_⟩
  have h1 : e.symm (cLoc w₀ x) = ⟨x, hx⟩ := by
    rw [← he ⟨x, hx⟩]
    exact e.symm_apply_apply _
  have h2 : algRep W (p (cLoc w₀ x)) f = f := hxN
  have h3 : (p (cLoc w₀ x)).1 = x := by
    simp only [p, h1]
  have h4 := congrArg (fun F : algForms W => F.1 v g) h2
  change f.1 v (g * (p (cLoc w₀ x)).1) = f.1 v g at h4
  rwa [h3] at h4
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepCore
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.stepCore_pf :
    UpperTheory.Gal.Gen.AlgC → UpperTheory.Gal.Gen.Codim → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.StepCore := by
  intro hAlg hCod hPF E _ _ _ l _ ι a W C C' hCfin H _ _ hH lam hsurj hC'C hker ℓ hinf hright haut P hfd hcard f hf
  letI : Fintype H := Fintype.ofFinite H
  have hex : ∀ φ : H → ℂ, ∃ F : algForms W, ∀ v g, F.1 v g = φ (ℓ g) * f.1 v g := fun φ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => φ (ℓ g)) (haut φ) (fun g x hx => by simp only [hinf g x hx])
  choose Ψ₀ hΨ₀ using hex
  let Ψ : (H → ℂ) →ₗ[ℂ] algForms W :=
    { toFun := Ψ₀
      map_add' := fun φ ψ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_add, LinearMap.add_apply, Pi.add_apply, hΨ₀]
        ring
      map_smul' := fun c φ => Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        simp only [Submodule.coe_smul, LinearMap.smul_apply, Pi.smul_apply, hΨ₀, RingHom.id_apply, smul_eq_mul]
        ring }
  have hΨ : ∀ φ v g, (Ψ φ).1 v g = φ (ℓ g) * f.1 v g := hΨ₀
  have hfix : ∀ φ, Ψ φ ∈ fixedBy W C' := fun φ k hk v g => by
    have hkC : k ∈ C := hC'C hk
    have h1 : lam ⟨k, hkC⟩ = 1 := (hker ⟨k, hkC⟩).1 hk
    have h2 : ℓ (g * k) = ℓ g := by
      have := hright g ⟨k, hkC⟩
      rw [h1, mul_one] at this
      exact this
    rw [hΨ, hΨ, h2, hf k hkC v g]
  obtain ⟨h1, -, -, h4, -⟩ := hPF E a W C' P
  have hdim := hCod ℂ (H → ℂ) (algForms W) Ψ (part W C' P) (part W C' fun U => ¬ P U) (fun φ => h1 (hfix φ))
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  rw [Nat.card_eq_fintype_card] at hcard
  have hA : Fintype.card H ≤ 2 * Module.finrank ℂ ((part W C' P).comap Ψ) := by omega
  have hstable : ∀ c ∈ (part W C' P).comap Ψ, ∀ u, (fun h => c (h * u)) ∈ (part W C' P).comap Ψ := by
    intro φ hφ u
    obtain ⟨c, rfl⟩ := hsurj u
    have hnorm : ∀ c' ∈ C', (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C' := by
      intro c' hc'
      have hc'C : c' ∈ C := hC'C hc'
      have hm : (c.1 : UA E a)⁻¹ * c' * c.1 ∈ C := C.mul_mem (C.mul_mem (C.inv_mem c.2) hc'C) c.2
      refine (hker ⟨_, hm⟩).2 ?_
      have e1 : (⟨_, hm⟩ : C) = c⁻¹ * ⟨c', hc'C⟩ * c := Subtype.ext rfl
      rw [e1, map_mul, map_mul, (hker ⟨c', hc'C⟩).1 hc', mul_one, map_inv, inv_mul_cancel]
    have hrep : Ψ (fun h => φ (h * lam c)) = algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ) :=
      Subtype.ext <| LinearMap.ext fun v => funext fun g => by
        have e2 : (algRep W ⟨c.1, hCfin c.2⟩ (Ψ φ)).1 v g = (Ψ φ).1 v (g * c.1) := rfl
        rw [e2, hΨ, hΨ, hright g c, hf c.1 c.2 v g]
    change Ψ _ ∈ part W C' P
    rw [hrep]
    exact h4 ⟨c.1, hCfin c.2⟩ hnorm _ hφ
  obtain ⟨φ, hφ, hnorm⟩ := hAlg l ι H hH _ hstable hA
  exact ⟨Ψ φ, hφ, fun g => 1 - φ (ℓ g), fun g => hnorm (ℓ g), fun v g => by rw [hΨ]; ring⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StepPf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.step_pf :
    UpperTheory.Gal.Gen.SmoothAt → UpperTheory.Gal.Gen.Tower → UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.CountGen → UpperTheory.Gal.Gen.StepCore → UpperTheory.Gal.Gen.PartFacts → UpperTheory.Gal.Gen.Step := by
  intro hSm hTw hLev hEll hCG hSC hPF E _ _ _ l _ ι a ha w₀ hl hs K hK W S Φ hS f hf
  obtain ⟨N, hN, hfN⟩ := hSm E a w₀ hs W f
  obtain ⟨J, hJ, hJN, htf, hpow⟩ := hTw E w₀ a l (Fact.out) hl ha N hN
  obtain ⟨n, hfd, hcard⟩ := hCG E a w₀ hs K hK J hJ W S Φ hS
  obtain ⟨lv0, mem0, inJ0, -, sec0, tr0⟩ := hLev E a w₀ hs K hK (J 0) (hJ.isOpen 0) (hJ.compact 0)
  obtain ⟨-, memn, inJn, -, -, -⟩ := hLev E a w₀ hs K hK (J n) (hJ.isOpen n) (hJ.compact n)
  haveI hnorm : ((J n).subgroupOf (J 0)).Normal := ⟨fun x hx g => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hJ.normal n g.1 g.2 x.1 hx⟩
  haveI : CompactSpace (J 0) := isCompact_iff_compactSpace.1 (hJ.compact 0)
  haveI hfin : Finite (J 0 ⧸ (J n).subgroupOf (J 0)) :=
    Subgroup.quotient_finite_of_isOpen _ ((hJ.isOpen n).preimage continuous_subtype_val)
  have hp : IsPGroup l (J 0 ⧸ (J n).subgroupOf (J 0)) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hpow n x.1 x.2
  let φ : lev K w₀ (J 0) →* J 0 :=
    ((cLoc w₀).comp (lev K w₀ (J 0)).subtype).codRestrict (J 0) (fun c => inJ0 c.1 c.2)
  let lam : lev K w₀ (J 0) →* (J 0 ⧸ (J n).subgroupOf (J 0)) := (QuotientGroup.mk' _).comp φ
  have hlam : ∀ c : lev K w₀ (J 0), lam c = 1 ↔ cLoc w₀ c.1 ∈ J n := fun c => by
    change ((φ c : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hsurj : Function.Surjective lam := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, hxy⟩ := sec0 y.1
    have hxC : x ∈ lev K w₀ (J 0) :=
      (mem0 x).2 ⟨1, one_mem _, x, hx, hxy ▸ y.2, (one_mul x).symm⟩
    refine ⟨⟨x, hxC⟩, ?_⟩
    change ((φ ⟨x, hxC⟩ : J 0) : J 0 ⧸ (J n).subgroupOf (J 0)) = _
    congr 1
    exact Subtype.ext hxy
  have hle : lev K w₀ (J n) ≤ lev K w₀ (J 0) := fun c hc => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (memn c).1 hc
    exact (mem0 _).2 ⟨k, hk, x, hx, hJ.anti (Nat.zero_le n) hxJ, rfl⟩
  have hiff : ∀ c : lev K w₀ (J 0), c.1 ∈ lev K w₀ (J n) ↔ lam c = 1 := fun c => by
    rw [hlam]
    exact ⟨inJn c.1, tr0 (J n) c.1 c.2⟩
  obtain ⟨ℓ, hℓ₁, hℓ₂, hℓ₃⟩ := hEll E a (lev K w₀ (J 0)) lv0 _ lam
    ⟨cLoc w₀ ⁻¹' (J n : Set (GL (Fin a) (w₀.adicCompletion E))), (hJ.isOpen n).preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀),
      by simp [one_mem], fun c hc => (hlam c).2 hc⟩
    (fun c hc => by
      have h1 : cLoc w₀ c.1 = 1 :=
        htf _ (inJ0 c.1 c.2) (MonoidHom.isOfFinOrder ((cLoc w₀).comp (lev K w₀ (J 0)).subtype) hc)
      exact (hlam c).2 (h1 ▸ one_mem _))
  have hfC : f ∈ fixedBy W (lev K w₀ (J 0)) := fun c hc v g => by
    obtain ⟨k, hk, x, hx, hxJ, rfl⟩ := (mem0 c).1 hc
    rw [← mul_assoc, hfN x hx (hJN hxJ) v (g * k)]
    exact hf k hk v g
  obtain ⟨G, hG, e, he, hfe⟩ := hSC E l ι a W (lev K w₀ (J 0)) (lev K w₀ (J n)) lv0.fin _ hp lam hsurj hle hiff
    ℓ hℓ₁ hℓ₂ hℓ₃ (fun U => ∀ w ∈ S, GenAt w (Φ w) U) hfd hcard f hfC
  exact ⟨G, (hPF E a W (lev K w₀ (J n)) _).2.2.1 K le_sup_left hG, e, he, hfe⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TowerPf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tower_pf :
    UpperTheory.Gal.Gen.CongSub → UpperTheory.Gal.Gen.Tower := by
  intro hC E _ _ w a l hl hw ha N hN
  obtain ⟨m, -, J', lam, hJo, hJc, hJN, hJtf, -, -⟩ := _root_.GlobalTheory.CuspType.exists_type E w a l hl hw ha N hN 0
  obtain ⟨J, hT, hp⟩ := hC E w a l hl hw
  obtain ⟨s, hs⟩ := hT.small _ (hJo.mem_nhds J'.one_mem)
  refine ⟨fun n => J (s + n), ⟨fun n => hT.isOpen _, fun n => hT.compact _, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact hT.anti (Nat.add_le_add_left hij s)
  · intro n g hg x hx
    exact hT.normal (s + n) g (hT.anti (Nat.zero_le (s + 0)) hg) x hx
  · intro M hM
    obtain ⟨n, hn⟩ := hT.small M hM
    exact ⟨n, fun x hx => hn (hT.anti (Nat.le_add_left n s) hx)⟩
  · exact fun x hx => hJN (hs hx)
  · exact fun g hg ho => hJtf g (hs hg) ho
  · intro n x hx
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      rw [pow_succ, pow_mul]
      exact hp (s + n) _ ih
end

