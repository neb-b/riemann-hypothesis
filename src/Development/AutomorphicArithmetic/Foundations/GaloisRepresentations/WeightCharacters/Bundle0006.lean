module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0109
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundTheorem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TopUpOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.topUp_of :
    UpperTheory.Gal.Wt.TopUp := by
  intro a κ b hb
  have hbt : (b : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := fun i j h => hb i j h
  have hdiag : ∀ i, (b : Matrix (Fin a) (Fin a) ℂ) i i ≠ 0 := by
    have hdet : (b : Matrix (Fin a) (Fin a) ℂ).det ≠ 0 :=
      ((Matrix.isUnit_iff_isUnit_det _).mp b.isUnit).ne_zero
    rw [Matrix.det_of_upperTriangular hbt] at hdet
    exact fun i => (Finset.prod_ne_zero_iff.mp hdet) i (Finset.mem_univ i)
  let t : Fin a → ℂˣ := fun i => Units.mk0 _ (hdiag i)
  set D := diagGL ℂ a t with hD
  set u := D⁻¹ * b with hu
  have hbu : b = D * u := by rw [hu, mul_inv_cancel_left]
  have hDinv : ((D⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal fun i => (((t i)⁻¹ : ℂˣ) : ℂ) := rfl
  have hucoe : (u : Matrix (Fin a) (Fin a) ℂ) =
      Matrix.diagonal (fun i => (((t i)⁻¹ : ℂˣ) : ℂ)) * (b : Matrix (Fin a) (Fin a) ℂ) := by
    rw [hu, Units.val_mul, hDinv]
  have hut : (u : Matrix (Fin a) (Fin a) ℂ).BlockTriangular id := by
    rw [hucoe]
    exact (Matrix.blockTriangular_diagonal _).mul hbt
  have hu1 : ∀ i, (u : Matrix (Fin a) (Fin a) ℂ) i i = 1 := by
    intro i
    rw [hucoe, Matrix.diagonal_mul]
    simp [t, hdiag i]
  have hfix : (sqRep ℂ a κ u) (top κ) = top κ := by
    apply Subtype.ext
    exact (factSqHighestWeight ℂ a κ).2 u hut hu1
  have hscal : (sqRep ℂ a κ D) (top κ) = chi κ b • top κ := by
    apply Subtype.ext
    have h := (factSqHighestWeight ℂ a κ).1 t
    have hc : (((∏ i, t i ^ κ.w i : ℂˣ)) : ℂ) = chi κ b := by
      rw [Units.coe_prod]
      simp only [Units.val_zpow_eq_zpow_val, chi, t, Units.val_mk0]
    rw [hc] at h
    exact h
  calc (sqRep ℂ a κ b) (top κ) = (sqRep ℂ a κ D) ((sqRep ℂ a κ u) (top κ)) := by
        rw [hbu, map_mul, Module.End.mul_apply]
    _ = chi κ b • top κ := by rw [hfix, hscal]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TorFacts
section
noncomputable section

open Formalism.BasicNotions GlobalTheory.Branching

namespace UpperTheory.Gal.Wt

private theorem tor_isUp (a k : ℕ) (z : Circle) : IsUp (tor a k z) := by
  intro i j hij
  rw [tor_coe]
  exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)

private theorem circ_mul_conj (z : Circle) : (starRingEnd ℂ) (z : ℂ) * (z : ℂ) = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self]
  simp

private theorem tor_unitary (a k : ℕ) (z : Circle) :
    ∃ u : Matrix.unitaryGroup (Fin a) ℂ, unitaryIncl a u = tor a k z := by
  set d : Fin a → ℂ := fun i => if (i : ℕ) < k then (z : ℂ) else 1 with hd
  have hdd : ∀ i, d i * (starRingEnd ℂ) (d i) = 1 := by
    intro i
    simp only [hd]
    split_ifs
    · rw [mul_comm]
      exact circ_mul_conj z
    · simp
  have hmem : Matrix.diagonal d ∈ Matrix.unitaryGroup (Fin a) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hdd i
  refine ⟨⟨Matrix.diagonal d, hmem⟩, ?_⟩
  ext : 1
  rw [unitaryIncl_coe, tor_coe]

private theorem tor_chi {a : ℕ} (k : ℕ) (z : Circle) (κ : DomWeight a) :
    chi κ (tor a k z) = (z : ℂ) ^ psum κ k := by
  have hz : (z : ℂ) ≠ 0 := by simp
  simp only [chi, psum, tor_coe, Matrix.diagonal_apply_eq]
  rw [Finset.sum_filter]
  have key : ∀ s : Finset (Fin a), ∏ i ∈ s, (if (i : ℕ) < k then (z : ℂ) else 1) ^ κ.w i =
      (z : ℂ) ^ ∑ i ∈ s, (if (i : ℕ) < k then κ.w i else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add₀ hz]
      split_ifs <;> simp
  exact key _

private theorem tor_conj (a k : ℕ) (z : Circle) :
    Matrix.GeneralLinearGroup.map (starRingEnd ℂ) (tor a k z) = tor a k z⁻¹ := by
  have hinv : (starRingEnd ℂ) (z : ℂ) = ((z⁻¹ : Circle) : ℂ) := by
    rw [Circle.coe_inv]
    exact eq_inv_of_mul_eq_one_left (circ_mul_conj z)
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, tor_coe, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp [hinv]

theorem torFacts_of : TorFacts := fun a k z =>
  ⟨tor_isUp a k z, tor_unitary a k z, fun κ => tor_chi k z κ, tor_conj a k z⟩

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistBd
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)

namespace UpperTheory.Gal.Wt

private theorem isOpen_subgroupOf {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}
    {C C₀ : Subgroup (UA E a)} (hC : IsLevel C) (hC₀ : IsLevel C₀) :
    IsOpen ((C₀.subgroupOf C : Subgroup C) : Set C) := by
  obtain ⟨N, hNo, h1N, hNC⟩ := hC₀.isOpen
  refine Subgroup.isOpen_of_mem_nhds (g := 1) _ ?_
  refine Filter.mem_of_superset
    ((hNo.preimage continuous_subtype_val).mem_nhds (show ((1 : C) : UA E a) ∈ N from h1N)) ?_
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, hC.fin x.2⟩)

theorem twistBd_of : Twist → TwistBd := by
  intro hT E _ _ _ l _ ι a C hC ℓ hℓ W f X b hb
  classical
  obtain ⟨C₀, hC₀, hf⟩ := UpperTheory.Gal.Gen.levelEx_holds E a W f
  have hHo := isOpen_subgroupOf hC hC₀
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC.compact
  haveI : Finite (C ⧸ C₀.subgroupOf C) := Subgroup.quotient_finite_of_isOpen _ hHo
  letI := Fintype.ofFinite (C ⧸ C₀.subgroupOf C)
  have hq : ∀ q : C ⧸ C₀.subgroupOf C, ∃ R : ℝ, ∀ g i,
      ‖ι.symm (f.1 (b g i) (g * ((ℓ g)⁻¹ * q.out : C)))‖ ≤ R := by
    intro q
    obtain ⟨F, -, hF⟩ := hT E a C hC ℓ hℓ W f q.out
    obtain ⟨R, hR⟩ := hb F
    exact ⟨R, fun g i => by rw [← hF]; exact hR g i⟩
  choose R hR using hq
  refine ⟨1 + ∑ q, |R q|, by positivity, fun c g i => ?_⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (C₀.subgroupOf C) c
  have hhC : ((h : C) : UA E a) ∈ C₀ := Subgroup.mem_subgroupOf.1 h.2
  have e : f.1 (b g i) (g * ((ℓ g)⁻¹ * (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C).out : C)) =
      f.1 (b g i) (g * ((ℓ g)⁻¹ * c : C)) := by
    rw [hh]
    have : (((ℓ g)⁻¹ * (c * (h : C)) : C) : UA E a) = (((ℓ g)⁻¹ * c : C) : UA E a) * ((h : C) : UA E a) := by
      simp [mul_assoc]
    rw [this, ← mul_assoc]
    exact hf _ hhC _ _
  rw [← e]
  refine (hR _ g i).trans ((le_abs_self _).trans ?_)
  have := Finset.single_le_sum (f := fun q => |R q|) (fun q _ => abs_nonneg _)
    (Finset.mem_univ (QuotientGroup.mk c : C ⧸ C₀.subgroupOf C))
  linarith

end UpperTheory.Gal.Wt

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.TwistOf
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.twist_of :
    UpperTheory.Gal.Wt.AutCrit → UpperTheory.Gal.Wt.Twist := by
  intro hA E _ _ _ a C hC ℓ hℓ W f c
  let e : UA E a → UA E a := fun g => (((ℓ g)⁻¹ * c : C) : UA E a)
  have he : ∀ g, e g ∈ finU (E := E) (n := a) := fun g => hC.fin ((ℓ g)⁻¹ * c).2
  let F : W.Sp →ₗ[ℂ] (UA E a → ℂ) :=
    { toFun := fun v g => f.1 v (g * e g)
      map_add' := fun v w => by funext g; simp
      map_smul' := fun r v => by funext g; simp }
  have hF : ∀ v g, F v g = f.1 v (g * e g) := fun _ _ => rfl
  have hleft : ∀ γ ∈ ratU E a, ∀ v g, F v (γ * g) = F v g := by
    intro γ hγ v g
    have h : e (γ * g) = e g := by simp only [e, hℓ.left γ hγ g]
    rw [hF, hF, h, mul_assoc]
    exact (f.2.1 v).left γ hγ _
  have hlev : ∀ k ∈ C, ∀ v g, F v (g * k) = F v g := by
    intro k hk v g
    have h : g * k * e (g * k) = g * e g := by
      simp only [e, hℓ.lev ⟨k, hk⟩ g, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hF, hF, h]
  have hinf : ∀ x ∈ infU E a, ∀ v g, F v (g * x) = f.1 v (g * x * e g) := by
    intro x hx v g
    have h : e (g * x) = e g := by simp only [e, hℓ.inf x hx g]
    rw [hF, h]
  have heqv : ∀ (x : infU E a) v, F (W.rep x v) = RU E a x (F v) := by
    intro x v
    funext g
    rw [RU_apply, hinf x x.2, hF, f.2.2 x v, RU_apply, mul_assoc g, mul_assoc g, fin_mul_inf (he g) x.2]
  have haut : ∀ v, IsAutFormU (F v) := by
    intro v
    refine hA E a C hC (F v) (fun γ hγ g => hleft γ hγ v g) (fun k hk g => hlev k hk v g) ?_
      (LinearMap.range F) inferInstance fun x hx => ⟨W.rep ⟨x, hx⟩ v, heqv ⟨x, hx⟩ v⟩
    intro g
    have h : (fun x : infU E a => F v (g * x)) = fun x : infU E a => f.1 v (g * x * e g) :=
      funext fun x => hinf x x.2 v g
    rw [h]
    exact (f.2.1 v).cont.comp ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  exact ⟨⟨F, haut, heqv⟩, UpperTheory.Gal.Gen.mem_fixedBy.2 fun k hk v g => hlev k hk v g, fun _ _ => rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.WExpH
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

theorem UpperTheory.Gal.Wt.wExp_h : ExpBasic → SqExp → TorFacts → WExp := by
  intro hB hS hT E _ _ _ a τ W
  classical
  obtain ⟨-, -, hmono, -, -, hinv⟩ := hB
  set v₀ := InfinitePlace.mk τ with hv₀
  let d : ℕ := ∑ i, ((W v₀).w i).natAbs + a * (W v₀).detShift.natAbs
  have hps : ∀ k, psum (W v₀) k ≤ d := fun k => by
    have h1 : psum (W v₀) k ≤ ∑ i, (((W v₀).w i).natAbs : ℤ) :=
      (Finset.sum_le_sum fun i _ => Int.le_natAbs).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _)
    have h2 : (0 : ℤ) ≤ ((a * (W v₀).detShift.natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
    simp only [d, Nat.cast_add, Nat.cast_sum]
    omega
  have h1 : ∀ k w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpGe (-d) := fun k w L =>
    ⟨(hmono _ _ (hps k)).1 (hS a k _ w L).1, (hmono _ _ (neg_le_neg (by exact_mod_cast Nat.le_add_left _ _))).2 (hS a k _ w L).2⟩
  refine ⟨d, fun k x hx v L => ?_⟩
  have h2 : (∀ z, (x z).1 ∈ embU a v₀.embedding) ∧ ∀ w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ),
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpGe (-d) := by
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · rw [hv₀, e]
      refine ⟨fun z => (hx z).1, fun w L => ?_⟩
      simp only [(hx _).2]
      exact h1 k w L
    · rw [hv₀, e]
      refine ⟨fun z => by rw [GlobalTheory.DefiniteBC.embU_conjugate]; exact (hx z).1, fun w L => ?_⟩
      have e2 : ∀ z, cEmb (ComplexEmbedding.conjugate τ) (x z).1 = tor a k z⁻¹ := fun z => by
        rw [← (hT a k z).2.2.2, ← (hx z).2]
        ext i j
        simp [cEmb, GlobalTheory.DefiniteBC.coord_conjugate]
      simp only [e2]
      have h3 := (hinv _ _).2 (h1 k w L).2
      rw [neg_neg] at h3
      exact ⟨h3, (hinv _ _).1 (h1 k w L).1⟩
  let Φ : W.Sp →ₗ[ℂ] (Circle → ℂ) := LinearMap.pi fun z => L ∘ₗ W.rep (x z)
  let N : Submodule ℂ W.Sp := (ExpLe d ⊓ ExpGe (-d)).comap Φ
  have hN : ∀ e, GlobalTheory.CoefIrred.tenMul W e ∈ N := fun e => by
    have h := h2.2 (e v₀) (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
    have e3 : Φ (GlobalTheory.CoefIrred.tenMul W e) = fun z => (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
        (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) (e v₀)) := by
      funext z
      have := rep_tenMul_update W v₀ (x z) (h2.1 z) e (e v₀)
      rw [Function.update_eq_self] at this
      exact congrArg L this
    change Φ _ ∈ ExpLe d ⊓ ExpGe (-d)
    rw [e3]
    exact h
  have h0 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (W.Sp ⧸ N) 0).unique (y₁ := N.mkQ) (y₂ := 0)
    (fun u => (Submodule.Quotient.mk_eq_zero N).2 (hN u)) (fun u => rfl)
  exact (Submodule.Quotient.mk_eq_zero N).1 (LinearMap.congr_fun h0 v)
end

