module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1804
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1810

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFullLevelGroupIffCongruenceLcm
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.EqCovol.FullLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma cc_cc' (a : E) : cc (cc a) = a := IsCMField.complexConj_apply_apply E a

lemma herm_sub_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (u v y : Fin r → E) :
    herm G (u - v) y = herm G u y - herm G v y := by
  simp [herm, sub_mul, Finset.sum_sub_distrib]

lemma herm_sub_right' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (x u v : Fin r → E) :
    herm G x (u - v) = herm G x u - herm G x v := by
  simp [herm, cc, mul_sub, Finset.sum_sub_distrib]

lemma herm_smul_left'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (u y : Fin r → E) :
    herm G (c • u) y = c * herm G u y := by
  simp [herm, Finset.mul_sum, mul_assoc]

lemma herm_smul_right'' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x v : Fin r → E) :
    herm G x (c • v) = cc c * herm G x v := by
  simp only [herm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma oe_smul {r : ℕ} (c : 𝓞 E) (y : Fin r → E) : c • y = (c : E) • y := by
  ext i; rfl

end GlobalTheory.EqCovol.FullLevel


open GlobalTheory.EqCovol.FullLevel in
theorem GlobalTheory.EqCovol.mem_iff_congr_lcm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (l : Level H) (r : ℕ) (Y : Data E r), GlobalTheory.EqCovol.IsLevGrp l Y → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∀ γ : GL (Fin r) E, γ ∈ Y.Γ ↔ IsUStab Y.Gm Y.Λ γ ∧ ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ,
      (γ : Matrix (Fin r) (Fin r) E).mulVec x - x = l.M' • y := by
  intro E _ _ _ H l r Y hL hS γ
  have hM0 : (l.M : E) ≠ 0 := by
    have : l.M ≠ 0 := by have := l.three_le; omega
    exact_mod_cast this
  have hA0 : (l.A : E) ≠ 0 := by exact_mod_cast l.A_pos.ne'
  constructor
  · intro hγ
    obtain ⟨hU, hM, hA⟩ := (hL γ).1 hγ
    obtain ⟨-, hMinv, -⟩ := (hL γ⁻¹).1 (Y.Γ.inv_mem hγ)
    set g : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hg
    set gi : Matrix (Fin r) (Fin r) E := ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) with hgi
    have hggi : ∀ v, g.mulVec (gi.mulVec v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, hg, hgi, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have hunit : ∀ u v, herm Y.Gm (g.mulVec u) v = herm Y.Gm u (gi.mulVec v) := by
      intro u v
      have := hU.1 u (gi.mulVec v)
      rwa [hggi] at this
    have hcop : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by
      rw [l.coprime]; exact Submodule.mem_top
    obtain ⟨b', hb', b, hb, hsum⟩ := Submodule.mem_sup.1 hcop
    have hsumE : (b' : E) + (b : E) = 1 := by exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) hsum

    have key : ∀ x ∈ Y.Λ, ∃ y ∈ Y.Λ, g.mulVec x - x = l.M • y := by
      intro x hx
      obtain ⟨y1, hy1, e1⟩ := hM (b • x) (Submodule.smul_mem_smul hb hx)
      set z : Fin r → E := (l.M : E)⁻¹ • ((b' : E) • (g.mulVec x - x)) with hz
      have hzmem : z ∈ Y.Λ := by
        refine (hS z).2 fun y hy => ?_
        have hc : H.bar b' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem _ hb'
        obtain ⟨w, hw, ew⟩ := hMinv (H.bar b' • y) (Submodule.smul_mem_smul hc hy)
        have hbarE : ((H.bar b' : 𝓞 E) : E) = cc (b' : E) := H.bar_eq b'
        rw [oe_smul, hbarE, ← Nat.cast_smul_eq_nsmul E] at ew
        have h1 : herm Y.Gm z y = herm Y.Gm x w := by
          have h2 := congrArg (herm Y.Gm x) ew
          rw [herm_sub_right', ← hunit, herm_smul_right'', herm_smul_right'', herm_smul_right'',
            cc_cc', cc, map_natCast] at h2
          rw [hz, herm_smul_left'', herm_smul_left'', herm_sub_left']
          field_simp
          linear_combination h2
        obtain ⟨n, hn⟩ := (hS x).1 hx w hw
        exact ⟨n, by rw [h1, hn]⟩
      refine ⟨z + y1, Y.Λ.add_mem hzmem hy1, ?_⟩
      rw [oe_smul, Matrix.mulVec_smul] at e1
      rw [smul_add, ← e1, ← Nat.cast_smul_eq_nsmul E, hz, smul_smul,
        mul_inv_cancel₀ hM0, one_smul, ← smul_sub, ← add_smul, hsumE, one_smul]
    refine ⟨hU, fun x hx => ?_⟩
    obtain ⟨y, hy, ey⟩ := key x hx
    obtain ⟨y', hy', ey'⟩ := hA x hx
    refine ⟨Nat.gcdA l.M l.A • y' + Nat.gcdB l.M l.A • y,
      Y.Λ.add_mem (Y.Λ.toAddSubgroup.zsmul_mem hy' _) (Y.Λ.toAddSubgroup.zsmul_mem hy _), ?_⟩
    set t := g.mulVec x - x with ht
    rw [← Nat.cast_smul_eq_nsmul E] at ey ey'
    have hy1 : y = (l.M : E)⁻¹ • t := by rw [ey, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    have hy2 : y' = (l.A : E)⁻¹ • t := by rw [ey', smul_smul, inv_mul_cancel₀ hA0, one_smul]
    have hG : ((Nat.gcd l.M l.A : ℕ) : E) = (l.M : E) * (Nat.gcdA l.M l.A : E) + (l.A : E) * (Nat.gcdB l.M l.A : E) := by
      have := congrArg (Int.cast : ℤ → E) (Nat.gcd_eq_gcd_ab l.M l.A)
      push_cast at this
      exact this
    have hGL : ((Nat.gcd l.M l.A : ℕ) : E) * (l.M' : E) = (l.M : E) * (l.A : E) := by
      unfold Level.M'
      exact_mod_cast Nat.gcd_mul_lcm l.M l.A
    rw [← Nat.cast_smul_eq_nsmul E, ← Int.cast_smul_eq_zsmul E, ← Int.cast_smul_eq_zsmul E, hy1, hy2,
      smul_smul, smul_smul, ← add_smul, smul_smul]
    conv_lhs => rw [← one_smul E t]
    congr 1
    field_simp
    linear_combination hGL.symm + (l.M' : E) * hG
  · rintro ⟨hU, h⟩
    refine (hL γ).2 ⟨hU, fun x hx => ?_, fun x hx => ?_⟩
    · obtain ⟨y, hy, e⟩ := h x (Submodule.smul_le_right hx)
      obtain ⟨k, hk⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
    · obtain ⟨y, hy, e⟩ := h x hx
      obtain ⟨k, hk⟩ : l.A ∣ l.M' := Nat.dvd_lcm_right _ _
      exact ⟨k • y, Y.Λ.toAddSubmonoid.nsmul_mem hy k, by rw [e, hk, mul_smul]⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulTopOfDualWeylTensorReductionEqZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWtEmb

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HighWtEmb

theorem exists_basis_reduction_linearIndependent : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → GlobalTheory.HighWt.BaseChange →
    ∀ (N : ℕ) (ν : Fin N → ℕ), Antitone ν → ∃ (n : ℕ) (b : Module.Basis (Fin n) O (dualWeyl O N N ν)),
      LinearIndependent (O ⧸ Ideal.span {ϖ})
        (fun i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b i : MvPolynomial (Fin N × Fin N) O)) := by
  intro O _ _ _ ϖ hϖ hBC N ν hν
  haveI := GlobalTheory.NablaFin.dualWeyl_finite O N ν
  haveI : Module.Free O (dualWeyl O N N ν) := Module.free_of_finite_type_torsion_free'
  let b := (Module.Free.chooseBasis O (dualWeyl O N N ν)).reindex (Fintype.equivFin _)
  refine ⟨_, b, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  choose c hc using fun j => Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}) (a j)
  let g : dualWeyl O N N ν := ∑ j, c j • b j
  have hg : MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (g : MvPolynomial (Fin N × Fin N) O) = 0 := by
    rw [← ha]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, Submodule.coe_sum, Submodule.coe_smul, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, map_C, hc]
  obtain ⟨h, hh, hgh⟩ := (hBC O ϖ hϖ N ν hν).2 g g.2 hg
  have hgh' : g = ϖ • (⟨h, hh⟩ : dualWeyl O N N ν) := Subtype.ext (by simpa using hgh)
  have hci : c i = ϖ * b.repr ⟨h, hh⟩ i := by
    have h2 := congrArg (fun x => b.repr x i) hgh'
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul] at h2
    rw [← h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [g, map_sum, Finsupp.single_apply]
  rw [← hc i, hci, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), zero_mul]

theorem exists_dual_family (k : Type) [Field k] (σ : Type) (κ : Type) [DecidableEq κ] (v : κ → MvPolynomial σ k)
    (hv : LinearIndependent k v) : ∃ ψ : κ → (MvPolynomial σ k →ₗ[k] k), ∀ i l, ψ l (v i) = if i = l then 1 else 0 := by
  let B := Module.Basis.span hv
  refine ⟨fun l => (LinearMap.exists_extend (B.coord l)).choose, fun i l => ?_⟩
  have h := (LinearMap.exists_extend (B.coord l)).choose_spec
  have hvi : v i ∈ Submodule.span k (Set.range v) := Submodule.subset_span ⟨i, rfl⟩
  have h1 := LinearMap.congr_fun h ⟨v i, hvi⟩
  have hBi : B i = ⟨v i, hvi⟩ := Module.Basis.span_apply hv i
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
  rw [h1, ← hBi, B.coord_apply, B.repr_self, Finsupp.single_apply]

theorem curry_sum_mapDomain {ι σ : Type} [Fintype ι] [DecidableEq ι] (F : ι → σ →₀ ℕ) (τ : ι) :
    (∑ ρ, Finsupp.mapDomain (fun s : σ => ((ρ, s) : ι × σ)) (F ρ)).curry τ = F τ := by
  classical
  ext s
  rw [Finsupp.curry_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply_of_injective (fun _ _ h => congrArg Prod.snd h) _ _
  · intro ρ _ hρ
    apply Finsupp.mapDomain_notin_range
    rintro ⟨t, ht⟩
    exact hρ (congrArg Prod.fst ht)
  · simp

theorem exists_prod_functional : ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type)
    (φ : ι → (MvPolynomial σ k →ₗ[k] k)), ∃ Φ : MvPolynomial (ι × σ) k →ₗ[k] k,
      ∀ f : ι → MvPolynomial σ k, Φ (∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ)) = ∏ τ, φ τ (f τ) := by
  intro k _ ι _ _ σ φ
  classical
  let w : ((ι × σ) →₀ ℕ) → k := fun M => ∏ τ, φ τ (monomial (M.curry τ) 1)
  let Φ := (MvPolynomial.basisMonomials (ι × σ) k).constr k w
  have hmono : ∀ M c, Φ (monomial M c) = c * w M := by
    intro M c
    have : (monomial M c : MvPolynomial (ι × σ) k) = c • (MvPolynomial.basisMonomials (ι × σ) k M) := by
      rw [MvPolynomial.coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hφ : ∀ τ m c, φ τ (monomial m c) = c * φ τ (monomial m 1) := by
    intro τ m c
    rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  refine ⟨Φ, fun f => ?_⟩
  have h1 : ∀ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (f τ) =
      ∑ m ∈ (f τ).support, monomial (Finsupp.mapDomain (fun s : σ => ((τ, s) : ι × σ)) m) (AddMonoidAlgebra.coeff (f τ) m) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, rename_monomial]
  have h2 : ∀ τ, φ τ (f τ) = ∑ m ∈ (f τ).support, AddMonoidAlgebra.coeff (f τ) m * φ τ (monomial m 1) := by
    intro τ
    conv_lhs => rw [as_sum (f τ)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hφ τ m _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.prod_congr rfl (fun τ _ => h1 τ), Finset.prod_congr rfl (fun τ _ => h2 τ), Finset.prod_univ_sum,
    Finset.prod_univ_sum, map_sum]
  refine Finset.sum_congr rfl fun F _ => ?_
  rw [← monomial_sum_prod, hmono]
  simp only [w, curry_sum_mapDomain, Finset.prod_mul_distrib]

theorem linearIndependent_prod_rename : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (v : ∀ τ, κ τ → MvPolynomial σ k), (∀ τ, LinearIndependent k (v τ)) →
    LinearIndependent k (fun p : (∀ τ, κ τ) => ∏ τ, rename (fun s : σ => ((τ, s) : ι × σ)) (v τ (p τ))) := by
  intro k _ ι _ _ σ κ _ v hv
  classical
  choose ψ hψ using fun τ => exists_dual_family k σ (κ τ) (v τ) (hv τ)
  rw [Fintype.linearIndependent_iff]
  intro a ha l
  obtain ⟨Φ, hΦ⟩ := exists_prod_functional k ι σ (fun τ => ψ τ (l τ))
  have h := congrArg Φ ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h
  simp only [map_smul, hΦ, hψ, smul_eq_mul] at h
  rw [Finset.sum_eq_single l] at h
  · simpa using h
  · intro p _ hp
    obtain ⟨τ, hτ⟩ : ∃ τ, p τ ≠ l τ := by
      by_contra hc
      push_neg at hc
      exact hp (funext hc)
    rw [Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ), mul_zero]
  · simp

theorem blockRed_eq (O : Type) [CommRing O] (N : ℕ) {ι : Type} (ϖ : O) (τ : ι) (g : MvPolynomial (Fin N × Fin N) O) :
    blockRed O N ϖ τ g = rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι)) (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [blockRed, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp, blockRed] at *

theorem mem_smul_top_of_redT_eq_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (N : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (mu : ι → ℕ → ℕ) (ϖ : O), Irreducible ϖ → (∀ τ, Antitone (res N (mu τ))) → GlobalTheory.HighWt.BaseChange →
    ∀ y : NablaT O N mu, redT O N mu ϖ y = 0 → y ∈ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu)) := by
  intro O _ _ _ N ι _ _ mu ϖ hϖ hanti hBC y hy
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  have hb := fun τ => exists_basis_reduction_linearIndependent O ϖ hϖ hBC N (res N (mu τ)) (hanti τ)
  choose n b hli using hb
  let B := Basis.piTensorProduct b
  have hred : ∀ p, redT O N mu ϖ (B p) = ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) := by
    intro p
    simp only [B, Basis.piTensorProduct_apply, redT, PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, AlgHom.toLinearMap_apply]
    exact Finset.prod_congr rfl fun τ _ => blockRed_eq O N ϖ τ _
  have hL := linearIndependent_prod_rename (O ⧸ Ideal.span {ϖ}) ι (Fin N × Fin N) (fun τ => Fin (n τ))
    (fun τ i => MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ i : MvPolynomial (Fin N × Fin N) O)) hli
  rw [Fintype.linearIndependent_iff] at hL
  have hy' : ∑ p, Ideal.Quotient.mk (Ideal.span {ϖ}) (B.repr y p) • ∏ τ, rename (fun s : Fin N × Fin N => ((τ, s) : BVar N ι))
      (MvPolynomial.map (Ideal.Quotient.mk (Ideal.span {ϖ})) (b τ (p τ) : MvPolynomial (Fin N × Fin N) O)) = 0 := by
    rw [← hy]
    conv_rhs => rw [← B.sum_repr y]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [LinearMap.map_smul, hred]
    exact algebraMap_smul (O ⧸ Ideal.span {ϖ}) (B.repr y p) _
  have hc := hL _ hy'
  rw [← B.sum_repr y]
  refine Submodule.sum_mem _ fun p _ => ?_
  have hp : B.repr y p ∈ Ideal.span {ϖ} := Ideal.Quotient.eq_zero_iff_mem.mp (hc p)
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hp
  rw [← hd, mul_comm, mul_smul]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self ϖ) Submodule.mem_top

end GlobalTheory.HighWtEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylLatticeAddIffDetPowMul
section
set_option autoImplicit false

noncomputable section

open Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead

namespace GlobalTheory.WeylShift

variable (R : Type) [CommRing R]

theorem rowGen_detPol (n : ℕ) (a b : Fin n) :
    rowGen R a b (detPol R n) =
      (1 + (if a = b then Polynomial.X else 0)) * Polynomial.C (detPol R n) := by
  have hC : (Polynomial.C (detPol R n) : Polynomial (MvPolynomial (Fin n × Fin n) R)) =
      Matrix.det (Matrix.of fun p s : Fin n =>
        (Polynomial.C (X (p, s)) : Polynomial (MvPolynomial (Fin n × Fin n) R))) := by
    unfold detPol
    rw [RingHom.map_det]
    rfl
  rw [hC]
  set A := (Matrix.of fun p s : Fin n =>
        (Polynomial.C (X (p, s)) : Polynomial (MvPolynomial (Fin n × Fin n) R))) with hA
  have h1 : rowGen R a b (detPol R n) =
      Matrix.det (A.updateRow b (A b + (Polynomial.X : Polynomial (MvPolynomial (Fin n × Fin n) R)) • A a)) := by
    unfold detPol
    rw [AlgHom.map_det]
    congr 1
    ext1 p s
    by_cases hp : p = b
    · subst hp
      simp [rowGen, hA]
    · simp [rowGen, hA, hp, Matrix.updateRow_ne hp]
  rw [h1]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self, if_pos rfl]
    ring
  · rw [Matrix.det_updateRow_add_smul_self A (Ne.symm hab), if_neg hab]
    ring

theorem rowDiv_det_mul_zero (n : ℕ) (a b : Fin n) (g : MvPolynomial (Fin n × Fin n) R) :
    rowDiv R a b 0 (detPol R n * g) = detPol R n * rowDiv R a b 0 g := by
  unfold rowDiv
  rw [map_mul, rowGen_detPol]
  split_ifs <;> simp [add_mul, mul_assoc]

theorem rowDiv_det_mul_succ (n : ℕ) (a b : Fin n) (j : ℕ) (g : MvPolynomial (Fin n × Fin n) R) :
    rowDiv R a b (j + 1) (detPol R n * g) =
      detPol R n * rowDiv R a b (j + 1) g + (if a = b then detPol R n * rowDiv R a b j g else 0) := by
  unfold rowDiv
  rw [map_mul, rowGen_detPol]
  split_ifs
  · rw [add_mul, add_mul, one_mul, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_X_mul,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  · simp

theorem lpMinor_full (n s : ℕ) (h : s = n) (h1 h2 : s ≤ n) : lpMinor R s h1 h2 = detPol R n := by
  subst h
  rfl

theorem hw_add_one (n : ℕ) (ν : Fin n → ℕ) :
    hw R (le_refl n) (fun a => ν a + 1) = detPol R n * hw R (le_refl n) ν := by
  cases n with
  | zero => simp [hw, detPol]
  | succ m =>
    unfold hw
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have h1 : ∀ s : Fin m, (ν s.castSucc + 1) - nuNext (fun a => ν a + 1) s.castSucc
        = ν s.castSucc - nuNext ν s.castSucc := by
      intro s
      have hs : s.castSucc.val + 1 < m + 1 := by have := s.2; simp
      simp only [nuNext, dif_pos hs]
      omega
    have h2 : ∀ μ : Fin (m + 1) → ℕ, nuNext μ (Fin.last m) = 0 := by
      intro μ
      simp [nuNext]
    simp only [h1, h2, Nat.sub_zero]
    rw [lpMinor_full R (m + 1) ((Fin.last m).val + 1) (by simp)]
    ring

theorem mem_weyl_add_one (n : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    f ∈ weyl R n n le_rfl (fun a => ν a + 1) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n * g := by
  have key : weyl R n n le_rfl (fun a => ν a + 1) =
      (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n)) := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      induction w with
      | nil =>
        exact ⟨hw R le_rfl ν, Submodule.subset_span ⟨[], rfl⟩, (hw_add_one R n ν).symm⟩
      | cons x w ih =>
        obtain ⟨g, hg, hge⟩ := ih
        obtain ⟨a, b, j⟩ := x
        have he : applyWord R ((a, b, j) :: w) (hw R le_rfl fun a => ν a + 1) =
            rowDiv R a b j (detPol R n * g) := by
          have : detPol R n * g = applyWord R w (hw R le_rfl fun a => ν a + 1) := hge
          rw [this]; rfl
        show applyWord R ((a, b, j) :: w) (hw R le_rfl fun a => ν a + 1) ∈
          (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n))
        rw [he]
        have hm : ∀ i, detPol R n * rowDiv R a b i g ∈
            (weyl R n n le_rfl ν).map (LinearMap.mulLeft R (detPol R n)) := fun i =>
          ⟨_, weylModuleRowDividedPowerStable R n n le_rfl ν a b i g hg, rfl⟩
        cases j with
        | zero => rw [rowDiv_det_mul_zero]; exact hm 0
        | succ j =>
          rw [rowDiv_det_mul_succ]
          refine Submodule.add_mem _ (hm _) ?_
          split_ifs
          · exact hm _
          · exact Submodule.zero_mem _
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨w, rfl⟩
      show detPol R n * applyWord R w (hw R le_rfl ν) ∈ weyl R n n le_rfl (fun a => ν a + 1)
      induction w with
      | nil =>
        exact Submodule.subset_span ⟨[], hw_add_one R n ν⟩
      | cons x w ih =>
        obtain ⟨a, b, j⟩ := x
        show detPol R n * rowDiv R a b j (applyWord R w (hw R le_rfl ν)) ∈ _
        generalize applyWord R w (hw R le_rfl ν) = g at ih ⊢
        have hm : ∀ i, rowDiv R a b i (detPol R n * g) ∈ weyl R n n le_rfl (fun a => ν a + 1) := fun i =>
          weylModuleRowDividedPowerStable R n n le_rfl _ a b i _ ih
        induction j with
        | zero => rw [← rowDiv_det_mul_zero]; exact hm 0
        | succ j ihj =>
          have h := hm (j + 1)
          rw [rowDiv_det_mul_succ] at h
          refine (Submodule.add_mem_iff_left _ ?_).1 h
          split_ifs
          · exact ihj
          · exact Submodule.zero_mem _
  rw [key, Submodule.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨g, hg, rfl⟩

theorem mem_weyl_add (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R) :
    f ∈ weyl R n n le_rfl (fun a => ν a + k) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n ^ k * g := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have h := mem_weyl_add_one R n (fun a => ν a + k) f
    refine Iff.trans h ?_
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := (ih g).1 hg
      exact ⟨g', hg', by ring⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨_, (ih _).2 ⟨g, hg, rfl⟩, by ring⟩

end GlobalTheory.WeylShift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreeLeOfMemDualWeylLattice
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.DualWeylDeg

theorem weight_colW_apply {N : ℕ} (m : Fin N × Fin N →₀ ℕ) (t : Fin N) :
    (Finsupp.weight (colW N N) m) t = ∑ a : Fin N, m (a, t) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, colW, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp only [Pi.single_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb; simp; intro h; exact absurd h.symm hb
  · simp

theorem totalDegree_le_of_mem_dualWeyl : ∀ (O : Type) [CommRing O] (N : ℕ) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O), f ∈ dualWeyl O N N ν → f.totalDegree ≤ ∑ a, ν a := by
  intro O _ N ν f hf
  have h1 : f ∈ weightedHomogeneousSubmodule O (colW N N) ν := (Submodule.mem_inf.mp hf).1
  rw [mem_weightedHomogeneousSubmodule] at h1
  rw [totalDegree]
  refine Finset.sup_le fun m hm => ?_
  have h2 : Finsupp.weight (colW N N) m = ν := h1 (mem_support_iff.mp hm)
  have h3 : m.sum (fun _ e => e) = ∑ t, ∑ a : Fin N, m (a, t) := by
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type, Finset.sum_comm]
  rw [h3]
  refine le_of_eq (Finset.sum_congr rfl fun t _ => ?_)
  rw [← weight_colW_apply, h2]

end GlobalTheory.DualWeylDeg
end

