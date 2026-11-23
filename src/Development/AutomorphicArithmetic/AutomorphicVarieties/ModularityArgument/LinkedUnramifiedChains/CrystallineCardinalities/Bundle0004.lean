module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.UnitStep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.Bundle0001
public import Mathlib.Algebra.Module.PID

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.NormCnt
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem jtj {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (Jmat R 3 * Xᵀ * Jmat R 3) i j = X j.rev i.rev := by
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.transpose_apply] <;> decide

private theorem count {A Q : Type} [AddCommGroup A] [AddCommGroup Q] [Finite Q] (S T : Set A) (H : AddSubgroup A)
    (hH : (H : Set A) = S) (hS : S.Finite) (hT : T ⊆ S) (f : A →+ Q) (hf : ∀ x ∈ S, f x = 0 → x ∈ T) :
    S.ncard ≤ T.ncard * Nat.card Q := by
  subst hH
  haveI : Finite H := hS.to_subtype
  have hTf : T.Finite := hS.subset hT
  haveI : Finite T := hTf.to_subtype
  let g : H →+ Q := f.comp H.subtype
  have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup g.ker
  have h2 : Nat.card (H ⧸ g.ker) = Nat.card g.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g).toEquiv
  have h3 : Nat.card g.range ≤ Nat.card Q :=
    Nat.card_le_card_of_injective (fun x => x.1) Subtype.val_injective
  have h4 : Nat.card g.ker ≤ Nat.card T := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1.1, hf x.1.1 x.1.2 (AddMonoidHom.mem_ker.mp x.2)⟩) ?_
    intro x y hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext (Subtype.ext hxy)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq T]
  change Nat.card H ≤ _
  rw [h1, h2, mul_comm]
  exact Nat.mul_le_mul h4 h3

private theorem core {R Γ : Type} [CommRing R] [Group Γ] (r : Γ →* GG (m := 3) (R := R)) (c g : Γ)
    (hc : c * c = 1) (hc1 : (r c).mat = 1) (hc2 : (r c).right = -1) (hg : (r g).right = 1)
    (z : Γ → Matrix (Fin 3) (Fin 3) R) (hz : ∀ s t, z (s * t) = z s + (r s).adFun (z t))
    (e : z c 0 0 = 0 ∧ z c 0 1 = 0 ∧ z c 1 0 = 0 ∧ z c 0 2 = 0 ∧ z c 2 0 = 0 ∧ z c 1 1 = 0)
    (e1 : (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) 0 1 = 0)
    (e2 : (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) 1 0 = 0) :
    z c = 0 ∧ ∀ i j, i ≠ j → (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) i j = 0 := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  have hleft : (r c).left = 1 := Units.ext hc1
  have ad1 : ∀ (x : GG (m := 3) (R := R)) X, x.right = 1 →
      x.adFun X = x.mat * X * ((x.left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := by
    intro x X hx
    unfold GG.adFun
    rw [if_pos hx]
  have adc : ∀ X, (r c).adFun X = thetaLie X := by
    intro X
    unfold GG.adFun
    rw [if_neg (by rw [hc2]; exact hne), hc1, hleft, inv_one, Units.val_one, one_mul, mul_one]
  have ad0 : ∀ (x : GG (m := 3) (R := R)), x.adFun 0 = 0 := by
    intro x
    unfold GG.adFun thetaLie
    simp
  have z1 : z 1 = 0 := by
    have h := hz 1 1
    rw [mul_one, map_one, ad1 _ _ (by simp)] at h
    simpa [GG.mat] using h
  have hsym : ∀ i j, z c i j = z c j.rev i.rev := by
    have h := hz c c
    rw [hc, z1, adc] at h
    intro i j
    have h2 : z c = Jmat R 3 * (z c)ᵀ * Jmat R 3 := by
      unfold thetaLie at h
      rw [eq_comm, add_neg_eq_zero] at h
      exact h
    have h3 := congrFun (congrFun h2 i) j
    rwa [jtj] at h3
  have r0 : (0 : Fin 3).rev = 2 := rfl
  have r1 : (1 : Fin 3).rev = 1 := rfl
  have r2 : (2 : Fin 3).rev = 0 := rfl
  have hzc : z c = 0 := by
    obtain ⟨e00, e01, e10, e02, e20, e11⟩ := e
    have s22 := hsym 2 2
    have s12 := hsym 1 2
    have s21 := hsym 2 1
    simp only [r1, r2] at s22 s12 s21
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.zero_apply] <;> first | exact e00 | exact e01 | exact e10 | exact e02 | exact e20 | exact e11 | exact s22.trans e00 | exact s12.trans e01 | exact s21.trans e10
  refine ⟨hzc, ?_⟩
  set A : GL (Fin 3) R := (r g).left with hA
  have hgi : (r g⁻¹).right = 1 := by rw [map_inv, SemidirectProduct.inv_right, hg, inv_one]
  have hgil : (r g⁻¹).left = A⁻¹ := by
    rw [map_inv, SemidirectProduct.inv_left, hg, inv_one, map_one, MulAut.one_apply]
  have zgi : z g⁻¹ = -(((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * z g * (A : Matrix (Fin 3) (Fin 3) R)) := by
    have h := hz g⁻¹ g
    rw [inv_mul_cancel, z1, ad1 _ _ hgi, GG.mat, hgil, inv_inv] at h
    rw [eq_comm, ← eq_neg_iff_add_eq_zero] at h
    exact h
  have zh : z (c * g⁻¹ * c) = -(Jmat R 3 * (z g⁻¹)ᵀ * Jmat R 3) := by
    rw [hz, hzc, ad0, add_zero, hz, hzc, zero_add, adc]
    rfl
  have Mh : (r (c * g⁻¹ * c)).mat = Jmat R 3 * (A : Matrix (Fin 3) (Fin 3) R)ᵀ * Jmat R 3 := by
    rw [GG.mat, map_mul, map_mul, SemidirectProduct.mul_left, hleft, map_one, mul_one,
      SemidirectProduct.mul_left, hleft, one_mul, hc2, hgil, map_inv, sgnAct_neg_one, theta_inv_val]
  have hD : z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat =
      z g * (A : Matrix (Fin 3) (Fin 3) R) - Jmat R 3 * (z g * (A : Matrix (Fin 3) (Fin 3) R))ᵀ * Jmat R 3 := by
    rw [zh, Mh, zgi]
    have hJ := Jmat_mul_Jmat (R := R) 3
    have hAA : ((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ * (A : Matrix (Fin 3) (Fin 3) R)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
    simp only [Matrix.transpose_neg, Matrix.transpose_mul, neg_neg, Matrix.mul_neg, Matrix.neg_mul, GG.mat,
      Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Jmat R 3) (Jmat R 3), hJ, Matrix.one_mul,
      ← Matrix.mul_assoc ((A⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)ᵀ (A : Matrix (Fin 3) (Fin 3) R)ᵀ,
      hAA, Matrix.one_mul]
  have hDe : ∀ i j, (z g * (r g).mat - z (c * g⁻¹ * c) * (r (c * g⁻¹ * c)).mat) i j =
      (z g * (A : Matrix (Fin 3) (Fin 3) R)) i j - (z g * (A : Matrix (Fin 3) (Fin 3) R)) j.rev i.rev := by
    intro i j
    rw [hD, Matrix.sub_apply, jtj]
  intro i j hij
  rw [hDe] at e1 e2 ⊢
  rw [r0, r1] at e1 e2
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact sub_self _ | exact e1 | exact e2 | exact (show (z g * (A : Matrix (Fin 3) (Fin 3) R)) 1 2 - (z g * (A : Matrix (Fin 3) (Fin 3) R)) 0 1 = 0 by linear_combination -e1) | exact (show (z g * (A : Matrix (Fin 3) (Fin 3) R)) 2 1 - (z g * (A : Matrix (Fin 3) (Fin 3) R)) 1 0 = 0 by linear_combination -e2)

private def zlGrp {l : ℕ} [Fact l.Prime] {κ : Type} [Field κ] (F : Frame l κ) {N : Type} [AddCommGroup N]
    (ρ : Representation ℤ F.Γ N) (Z : ∀ v, AddSubgroup (F.Gv v → N)) : AddSubgroup (F.Γ → N) where
  carrier := ZL F ρ fun v => Z v
  add_mem' := by
    rintro x y ⟨⟨a1, a2⟩, a3⟩ ⟨⟨b1, b2⟩, b3⟩
    refine ⟨⟨a1.add b1, fun s t => ?_⟩, fun v => (Z v).add_mem (a3 v) (b3 v)⟩
    simp only [Pi.add_apply, a2, b2, map_add (f := _)]; abel
  zero_mem' := ⟨⟨IsLocallyConstant.const 0, by simp⟩, fun v => (Z v).zero_mem⟩
  neg_mem' := by
    rintro x ⟨⟨a1, a2⟩, a3⟩
    refine ⟨⟨a1.neg, fun s t => ?_⟩, fun v => (Z v).neg_mem (a3 v)⟩
    simp only [Pi.neg_apply, a2, map_neg]; abel

private def ent {R Γ : Type} [CommRing R] (c g h : Γ) (P Q : Matrix (Fin 3) (Fin 3) R) :
    (Γ → Matrix (Fin 3) (Fin 3) R) →+ (Fin 8 → R) :=
  AddMonoidHom.mk' (fun z => ![z c 0 0, z c 0 1, z c 1 0, z c 0 2, z c 2 0, z c 1 1,
    (z g * P - z h * Q) 0 1, (z g * P - z h * Q) 1 0]) fun x y => by
      have e : (x + y) g * P - (x + y) h * Q = (x g * P - x h * Q) + (y g * P - y h * Q) := by
        simp only [Pi.add_apply, Matrix.add_mul]; abel
      rw [e]
      ext i
      fin_cases i <;> rfl

end UpperTheory.V.Z.J

theorem UpperTheory.V.Z.J.normCnt :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → (l : O) ≠ 0 → ∀ (ρ : NRep F 3 O) (B : Box F 3 O), UpperTheory.V.Fr.IsLift O ρ → B.Of ρ → B.Cont (maximalIdeal O) → ∀ k, 0 < k → (∀ v, ∃ Z : AddSubgroup (F.Gv v → Matrix (Fin 3) (Fin 3) (Ok l O k)), (Z : Set _) = Zv B k v) → (ZL F (adK B k) (Zv B k)).Finite → (ZL F (adK B k) (Zv B k)).ncard ≤ (ZN B k).ncard * Nat.card (Ok l O k) ^ 8 := by
  intro l _ O _ _ _ _ _ F C₀ hF hl ρ B _ hB _ k _ hZ hfin
  haveI : Finite (Ok l O k) := (okFin l O hl).1 k
  choose Z hZ using hZ
  have hc : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right hF.c_sq
  have hs : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c := by
    simp [Frame.star, Frame.conj, hc, mul_assoc]
  have h := count (ZL F (adK B k) (Zv B k)) (ZN B k) (zlGrp F (adK B k) Z)
    (congrArg (ZL F (adK B k)) (funext hZ)) hfin (fun z hz => hz.1)
    (ent F.c F.g0 (F.star F.g0) ((boxK B k).r F.g0).mat ((boxK B k).r (F.star F.g0)).mat) (fun z hz h0 => by
      refine ⟨hz, ?_⟩
      have e6 := congrFun h0 6
      have e7 := congrFun h0 7
      rw [hs] at e6 e7 ⊢
      have hatc : ((boxK B k).r F.c).mat = 1 := by
        let q : O →+* Ok l O k := Ideal.Quotient.mk _
        change q.mapMatrix (B.r F.c).mat = 1
        rw [hB.atc, map_one]
      exact core (boxK B k).r F.c F.g0 hF.c_sq hatc (((boxK B k).nu _).trans hF.del_c)
        (((boxK B k).nu _).trans F.g0.2) z hz.1.2
        ⟨congrFun h0 0, congrFun h0 1, congrFun h0 2, congrFun h0 3, congrFun h0 4, congrFun h0 5⟩ e6 e7)
  rwa [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.RankTwo
section
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Z.J

namespace UpperTheory.V.Z.J

private theorem tors_card {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)] (c : O)
    [Finite (O ⧸ Ideal.span {c})] :
    Nat.card {x : O ⧸ I // c • x = 0} ≤ Nat.card (O ⧸ Ideal.span {c}) := by
  let φ : (O ⧸ I) →ₗ[O] (O ⧸ I) := c • LinearMap.id
  have hφ : ∀ x, φ x = c • x := fun x => rfl
  have hker : Nat.card {x : O ⧸ I // c • x = 0} = Nat.card (LinearMap.ker φ) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => by rw [LinearMap.mem_ker, hφ]))
  have hA1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
  have hA2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range φ)
  have hq : Nat.card ((O ⧸ I) ⧸ LinearMap.ker φ) = Nat.card (LinearMap.range φ) :=
    Nat.card_congr (φ.quotKerEquivRange).toEquiv
  have hpos : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
  have heq : Nat.card (LinearMap.ker φ) = Nat.card ((O ⧸ I) ⧸ LinearMap.range φ) := by
    rw [hq] at hA1
    have h : Nat.card (LinearMap.range φ) * Nat.card (LinearMap.ker φ) =
        Nat.card (LinearMap.range φ) * Nat.card ((O ⧸ I) ⧸ LinearMap.range φ) := by
      rw [mul_comm, ← hA1, hA2]
    exact Nat.eq_of_mul_eq_mul_left hpos h
  rw [hker, heq]
  let g : O →ₗ[O] (O ⧸ I) ⧸ LinearMap.range φ := (LinearMap.range φ).mkQ ∘ₗ (Submodule.mkQ I)
  have hg : Submodule.span O {c} ≤ LinearMap.ker g := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    simp only [g, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨Submodule.Quotient.mk 1, ?_⟩
    rw [hφ, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  refine Nat.card_le_card_of_surjective ((Submodule.span O {c}).liftQ g hg) ?_
  intro z
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨o, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨Submodule.Quotient.mk o, rfl⟩

private theorem hom_alt {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    (hfin : ∀ c : O, c ≠ 0 → Finite (O ⧸ Ideal.span {c}))
    (Q : Type) [AddCommGroup Q] [Module O Q] [Module.Finite O Q] :
    (∃ f g : Q →ₗ[O] O, ∃ x y : Q, f x = 1 ∧ g x = 0 ∧ f y = 0 ∧ g y = 1) ∨
    ∃ C : ℕ, ∀ I : Ideal O, Finite (O ⧸ I) → Nat.card (Q →ₗ[O] O ⧸ I) ≤ Nat.card (O ⧸ I) * C := by
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨E⟩⟩ := Module.equiv_free_prod_directSum O Q
  by_cases hn : 2 ≤ n
  · left
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, by omega⟩
    refine ⟨(Finsupp.lapply i0) ∘ₗ (LinearMap.fst O _ _) ∘ₗ E.toLinearMap,
      (Finsupp.lapply i1) ∘ₗ (LinearMap.fst O _ _) ∘ₗ E.toLinearMap,
      E.symm (Finsupp.single i0 1, 0), E.symm (Finsupp.single i1 1, 0), ?_, ?_, ?_, ?_⟩ <;>
    simp [i0, i1, Finsupp.single_apply]
  · right
    have hq : ∀ i, p i ^ e i ≠ 0 := fun i => pow_ne_zero _ (hp i).ne_zero
    haveI : ∀ i, Finite (O ⧸ Ideal.span {p i ^ e i}) := fun i => hfin _ (hq i)
    refine ⟨∏ i, Nat.card (O ⧸ Ideal.span {p i ^ e i}), fun I hI => ?_⟩
    have htor : ∀ (φ : Q →ₗ[O] O ⧸ I) (i : ι), (p i ^ e i) • φ (E.symm (0,
        DirectSum.lof O ι (fun i => O ⧸ O ∙ p i ^ e i) i (Submodule.Quotient.mk 1))) = 0 := by
      intro φ i
      rw [← map_smul, ← map_smul, Prod.smul_mk, smul_zero, ← map_smul, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        map_zero, Prod.mk_zero_zero, map_zero, map_zero]
    let F : (Q →ₗ[O] O ⧸ I) → (Fin n → O ⧸ I) × ((i : ι) → {x : O ⧸ I // (p i ^ e i) • x = 0}) :=
      fun φ => (fun j => φ (E.symm (Finsupp.single j 1, 0)), fun i => ⟨_, htor φ i⟩)
    have hF : Function.Injective F := by
      intro φ ψ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      have key : φ ∘ₗ E.symm.toLinearMap = ψ ∘ₗ E.symm.toLinearMap := by
        apply LinearMap.prod_ext
        · apply Finsupp.lhom_ext
          intro j b
          have hj := congrFun h1 j
          rw [← Finsupp.smul_single_one, map_smul, map_smul]
          exact congrArg (b • ·) hj
        · apply DirectSum.linearMap_ext
          intro i
          apply Submodule.linearMap_qext
          apply LinearMap.ext_ring
          exact congrArg Subtype.val (congrFun h2 i)
      ext x
      simpa using LinearMap.congr_fun key (E x)
    have hcard := Nat.card_le_card_of_injective F hF
    rw [Nat.card_prod, Nat.card_pi, Nat.card_pi, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hcard
    have hP : ∏ i, Nat.card {x : O ⧸ I // (p i ^ e i) • x = 0} ≤
        ∏ i, Nat.card (O ⧸ Ideal.span {p i ^ e i}) :=
      Finset.prod_le_prod' (fun i _ => tors_card I (p i ^ e i))
    have hpos : 0 < Nat.card (O ⧸ I) := Nat.card_pos
    have hpow : Nat.card (O ⧸ I) ^ n ≤ Nat.card (O ⧸ I) :=
      calc Nat.card (O ⧸ I) ^ n ≤ Nat.card (O ⧸ I) ^ 1 := Nat.pow_le_pow_right hpos (by omega)
        _ = Nat.card (O ⧸ I) := pow_one _
    exact hcard.trans (Nat.mul_le_mul hpow hP)

private def rel {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (ξ : R →ₐ[O] O) (T : Set R) : Submodule O R :=
  Submodule.span O ({x | ∃ a b, x = a * b - (ξ a • b + ξ b • a)} ∪ T)

private theorem rel_le {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (ξ : R →ₐ[O] O) (T : Set R)
    {X : Type} [AddCommGroup X] [Module O X] (δ : R →ₗ[O] X) :
    rel ξ T ≤ LinearMap.ker δ ↔ (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ a ∈ T, δ a = 0 := by
  unfold rel
  rw [Submodule.span_le, Set.union_subset_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b => ?_, fun a ha => LinearMap.mem_ker.mp (h2 ha)⟩
    have h := h1 ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero] at h
    exact h
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun a ha => LinearMap.mem_ker.mpr (h2 a ha)⟩
    rintro x ⟨a, b, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_add (f := _), map_smul, map_smul, sub_eq_zero]
    exact h1 a b

private theorem rel_fin {O R : Type} [CommRing O] [CommRing R] [Algebra O R] [IsNoetherianRing R] (ξ : R →ₐ[O] O)
    (T : Set R) : Module.Finite O (R ⧸ rel ξ T) := by
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (RingHom.ker ξ) : (RingHom.ker ξ).FG)
  have hS' : Ideal.span (S : Set R) = RingHom.ker ξ := hS
  have hrel : ∀ a b, a * b - (ξ a • b + ξ b • a) ∈ rel ξ T := fun a b =>
    Submodule.subset_span (Or.inl ⟨a, b, rfl⟩)
  have hmm : ∀ a b, ξ a = 0 → ξ b = 0 → a * b ∈ rel ξ T := by
    intro a b ha hb
    have h := hrel a b
    rwa [ha, hb, zero_smul, zero_smul, add_zero, sub_zero] at h
  have hker : ∀ x, x ∈ Ideal.span (S : Set R) → x ∈ Submodule.span O (S : Set R) ⊔ rel ξ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.mem_sup_left (Submodule.subset_span hx)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x hxS hx =>
      have hxk : ξ x = 0 := by
        have h := hxS
        rw [hS, RingHom.mem_ker] at h
        exact h
      have h1 : r • x = ξ r • x + (r - ξ r • 1) * x := by
        rw [smul_eq_mul, sub_mul, smul_mul_assoc, one_mul]
        abel
      rw [h1]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.mem_sup_right (hmm _ _ ?_ hxk))
      simp
  have h1 : (1 : R) ∈ rel ξ T := by
    have h := hrel 1 1
    rw [map_one, one_smul, mul_one] at h
    have h2 : (1 : R) - (1 + 1) = -1 := by ring
    rw [h2] at h
    exact neg_mem_iff.mp h
  have htop : ∀ r : R, r ∈ Submodule.span O (S : Set R) ⊔ rel ξ T := by
    intro r
    have hmem : r - ξ r • 1 ∈ Ideal.span (S : Set R) := by
      rw [hS', RingHom.mem_ker]
      simp
    rw [← sub_add_cancel r (ξ r • 1)]
    exact Submodule.add_mem _ (hker _ hmem) (Submodule.mem_sup_right (Submodule.smul_mem _ _ h1))
  haveI : Module.Finite O (Submodule.span O (S : Set R)) := Module.Finite.span_of_finite O S.finite_toSet
  refine Module.Finite.of_surjective ((rel ξ T).mkQ ∘ₗ (Submodule.span O (S : Set R)).subtype) ?_
  intro q
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨n, hn, m, hm, hnm⟩ := Submodule.mem_sup.mp (htop r)
  refine ⟨⟨n, hn⟩, ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, Submodule.mkQ_apply]
  rw [← hnm]
  exact (Submodule.Quotient.eq _).mpr (by simpa using hm)

end UpperTheory.V.Z.J

private theorem finite_linearMap_of_finite_module_finite {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N]
    [Module O N] [Module.Finite O M] [Finite N] : Finite (M →ₗ[O] N) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine Finite.of_injective (fun φ : M →ₗ[O] N => fun x : (s : Set M) => φ x) ?_
  intro φ ψ h
  exact LinearMap.ext_on hs (fun x hx => congrFun h ⟨x, hx⟩)

theorem UpperTheory.V.Z.J.rankTwo :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] [IsNoetherianRing R] (ξ : R →ₐ[O] O) (T : Set R) (C : ℕ), (l : O) ≠ 0 → (∀ k, 0 < k → ∀ X : Set (R →ₗ[O] Ok l O k), X = {δ | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ ∀ a ∈ T, δ a = 0} → X.Finite → Nat.card (Ok l O k) ^ 2 ≤ C * X.ncard) → ∃ δ δ' : R →ₗ[O] O, (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧ (∀ a ∈ T, δ a = 0) ∧ (∀ a b, δ' (a * b) = ξ a • δ' b + ξ b • δ' a) ∧ (∀ a ∈ T, δ' a = 0) ∧ LinearIndependent O ![δ, δ'] := by
  intro l _ O _ _ _ _ _ R _ _ _ ξ T C hl hX
  obtain ⟨hOk, hfin, -, h2k, -, -, -⟩ := okFin l O hl
  haveI : Module.Finite O (R ⧸ rel ξ T) := rel_fin ξ T
  have hder : ∀ {Y : Type} [AddCommGroup Y] [Module O Y] (φ : (R ⧸ rel ξ T) →ₗ[O] Y),
      (∀ a b, (φ ∘ₗ (rel ξ T).mkQ) (a * b) =
        ξ a • (φ ∘ₗ (rel ξ T).mkQ) b + ξ b • (φ ∘ₗ (rel ξ T).mkQ) a) ∧
      ∀ a ∈ T, (φ ∘ₗ (rel ξ T).mkQ) a = 0 := by
    intro Y _ _ φ
    refine (rel_le ξ T (φ ∘ₗ (rel ξ T).mkQ)).mp ?_
    intro x hx
    simp [LinearMap.mem_ker, (Submodule.Quotient.mk_eq_zero _).mpr hx]
  rcases hom_alt hfin (R ⧸ rel ξ T) with ⟨f, g, x, y, hfx, hgx, hfy, hgy⟩ | ⟨C', hC'⟩
  · obtain ⟨x0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    refine ⟨f ∘ₗ (rel ξ T).mkQ, g ∘ₗ (rel ξ T).mkQ, (hder f).1, (hder f).2, (hder g).1, (hder g).2, ?_⟩
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun δ => δ x0) hst
    have h2 := congrArg (fun δ => δ y0) hst
    simp [hfx, hgx, hfy, hgy] at h1 h2
    exact ⟨h1, h2⟩
  · exfalso
    obtain ⟨D, hD⟩ : ∃ D, D = C * C' := ⟨_, rfl⟩
    obtain ⟨k, hkD⟩ : ∃ k, k = D + 1 := ⟨_, rfl⟩
    have hk : 0 < k := by omega
    haveI := hOk k
    haveI : Finite ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) := finite_linearMap_of_finite_module_finite
    let Φ : ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) → (R →ₗ[O] Ok l O k) := fun φ => φ ∘ₗ (rel ξ T).mkQ
    have hΦinj : Function.Injective Φ := fun φ ψ h => Submodule.linearMap_qext _ h
    have hrange : Set.range Φ = {δ : R →ₗ[O] Ok l O k | (∀ a b, δ (a * b) = ξ a • δ b + ξ b • δ a) ∧
        ∀ a ∈ T, δ a = 0} := by
      ext δ
      constructor
      · rintro ⟨φ, rfl⟩
        exact hder φ
      · intro hδ
        exact ⟨(rel ξ T).liftQ δ ((rel_le ξ T δ).mpr hδ), Submodule.liftQ_mkQ _ _ _⟩
    have hcard := hX k hk (Set.range Φ) hrange (Set.finite_range Φ)
    rw [Set.ncard_range_of_injective hΦinj] at hcard
    have hbound := hC' (Ideal.span {(l : O) ^ k}) (hOk k)
    have hpos : 0 < Nat.card (Ok l O k) := Nat.card_pos
    have h2 := h2k k
    have hle : Nat.card (Ok l O k) ≤ D := by
      have h3 : Nat.card (Ok l O k) * Nat.card (Ok l O k) ≤ Nat.card (Ok l O k) * D := by
        calc Nat.card (Ok l O k) * Nat.card (Ok l O k) = Nat.card (Ok l O k) ^ 2 := (sq _).symm
          _ ≤ C * Nat.card ((R ⧸ rel ξ T) →ₗ[O] Ok l O k) := hcard
          _ ≤ C * (Nat.card (Ok l O k) * C') := Nat.mul_le_mul_left _ hbound
          _ = Nat.card (Ok l O k) * D := by rw [hD]; ring
      exact Nat.le_of_mul_le_mul_left h3 hpos
    have h4 : k < 2 ^ k := Nat.lt_two_pow_self
    omega
end

