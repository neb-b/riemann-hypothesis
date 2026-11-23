module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0021

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Gl2LocalToAdelicEmbedding
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section SlopeTestRemainingChoices

open UpperTheory.V.Af.Fin GroundTheory.Automorphic.AutomorphicForm

variable {R S : Type} [CommRing R] [CommRing S]

private theorem corner_sub_one {a : ℕ} (s : R →ₙ+* S) (g : GL (Fin a) R) (i j : Fin a) :
    ((cornerGL a s g).val - 1) i j = s ((g.val - 1) i j) := by
  change (1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g.val i j)
    - (1 : Matrix (Fin a) (Fin a) S) i j = s (g.val i j - (1 : Matrix (Fin a) (Fin a) R) i j)
  rw [map_sub]
  ring

private theorem corner_emb {a n : ℕ} (e : Fin a ↪ Fin n) (s : R →ₙ+* S) (g : GL (Fin a) R) :
    cornerGL n s (emb e g) = emb e (cornerGL a s g) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one, coe_emb, coe_emb, add_sub_cancel_left, add_sub_cancel_left]
  by_cases hi : ∃ k, i = e k
  · obtain ⟨k, rfl⟩ := hi
    by_cases hj : ∃ l, j = e l
    · obtain ⟨l, rfl⟩ := hj
      rw [matrixExtendByZero_apply, matrixExtendByZero_apply, corner_sub_one]
    · push Not at hj
      rw [matrixExtendByZero_apply_of_outside_col e _ _ hj, matrixExtendByZero_apply_of_outside_col e _ _ hj, map_zero]
  · push Not at hi
    rw [extendByZero_apply_eq_zero_of_row_not_mem e _ hi, extendByZero_apply_eq_zero_of_row_not_mem e _ hi, map_zero]

private theorem corner_blk {r t : ℕ} (s : R →ₙ+* S) (g : GL (Fin r) R) (h : GL (Fin t) R) :
    cornerGL (r + t) s (blk g h) = blk (cornerGL r s g) (cornerGL t s h) := by
  rw [blk, blk, map_mul, corner_emb, corner_emb]

private theorem corner_unip {n r : ℕ} (s : R →ₙ+* S) (X : UPos n r → R) :
    cornerGL n s (unipGL X) = unipGL fun p => s (X p) := by
  refine Units.ext (sub_left_injective (b := (1 : Matrix (Fin n) (Fin n) S)) ?_)
  ext i j
  beta_reduce
  rw [corner_sub_one]
  change s ((1 + blockEntry X - 1) i j) = (1 + blockEntry (fun p => s (X p)) - 1) i j
  rw [add_sub_cancel_left, add_sub_cancel_left, blockEntry_apply, blockEntry_apply]
  split_ifs
  · rfl
  · exact map_zero s

private theorem emb_mem {L : Type} [Field L] (O : Subring L) {a n : ℕ} (e : Fin a ↪ Fin n) {k : GL (Fin a) L}
    (hk : k ∈ GLint (Fin a) O) : emb e k ∈ GLint (Fin n) O := by
  obtain ⟨k, rfl⟩ := hk
  exact ⟨emb e k, emb_map e O.subtype k⟩

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.S.gl2_local_to_adelic_embedding :
    UpperTheory.V.Cj.S.HeckeLocalBlock := by
  intro E _ _ w r s
  refine ⟨fun b₁ b₂ => ?_, fun X => ?_, fun x y Y => ?_, fun k₁ h₁ k₂ h₂ => ?_⟩
  · simp only [finGL, locGL, corner_blk]
  · simp only [finGL, locGL, corner_unip]
    exact ⟨_, rfl⟩
  · obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (Ad E) r s x y
    exact ⟨_, hc (Ad E) (RingHom.id _) Y⟩
  · exact mul_mem (emb_mem _ _ h₁) (emb_mem _ _ h₂)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkLocal
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.hkLocal :
    UpperTheory.V.Cj.S.SumInner → UpperTheory.V.Cj.S.MatBlock → UpperTheory.V.Cj.S.HkLocal := by
  intro hSum hMat E _ _ w r s ϖ hϖ hu _ j Φ hΦ
  have hπ0 : ((⟨ϖ, hϖ⟩ : Ov E w) : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h0
    have h1 : Valued.v ϖ = 0 := by
      have h2 : ϖ = 0 := h0
      rw [h2, map_zero]
    rw [hu] at h1
    exact WithZero.coe_ne_zero h1
  have hq : Fintype.card (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) = qV E w := by
    have key : ∀ z : WithZero (Multiplicative ℤ), z < 1 → z ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
      intro z hz
      induction z using WithZero.recZeroCoe with
      | zero => exact zero_le'
      | coe a =>
        rw [← WithZero.coe_one, WithZero.coe_lt_coe] at hz
        rw [WithZero.coe_le_coe]
        have h1 : (Multiplicative.toAdd a : ℤ) < 0 := hz
        change (Multiplicative.toAdd a : ℤ) ≤ -1
        omega
    have hlt : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.coe_one, WithZero.coe_lt_coe]
      change (-1 : ℤ) < 0
      omega
    have hint := Valuation.valuationSubring.integers
      (Valued.v : Valuation (HeightOneSpectrum.adicCompletion E w) (WithZero (Multiplicative ℤ)))
    have hmax : Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)} =
        IsLocalRing.maximalIdeal (HeightOneSpectrum.adicCompletionIntegers E w) := by
      ext x
      rw [Ideal.mem_span_singleton]
      constructor
      · intro h
        have h2 := hint.le_of_dvd h
        exact (Valuation.mem_maximalIdeal_iff (v := Valued.v)).2 (lt_of_le_of_lt (h2.trans_eq hu) hlt)
      · intro h
        have h2 := (Valuation.mem_maximalIdeal_iff (v := Valued.v)).1 h
        exact hint.dvd_of_le ((key _ h2).trans_eq hu.symm)
    rw [Fintype.card_eq_nat_card, ← tjcosets_card_residue w]
    show Nat.card (↥(HeightOneSpectrum.adicCompletionIntegers E w) ⧸
      Ideal.span {(⟨ϖ, hϖ⟩ : HeightOneSpectrum.adicCompletionIntegers E w)}) = _
    rw [hmax]
    rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin r) → Finset (Fin s) → ℂ, ∀ A B, T A B =
      ∑ c₁ : satakePairs A → satakeRes (Ov E w) ⟨ϖ, hϖ⟩, ∑ c₂ : satakePairs B → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (blk (satakeGL (Ov E w) hπ0 A (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
          (satakeGL (Ov E w) hπ0 B (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))) :=
    ⟨_, fun _ _ => rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : Finset (Fin r) × Finset (Fin s) → Fin (r + 1) × Fin (s + 1),
      ∀ AB, κ AB = (⟨AB.1.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.1)⟩,
        ⟨AB.2.card, Nat.lt_succ_of_le (by simpa using Finset.card_le_univ AB.2)⟩) :=
    ⟨_, fun _ => rfl⟩
  have hS : ∀ S : Finset (Fin (r + s)),
      ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
        Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) =
      (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) := by
    intro S
    rw [hT]
    have h := hSum r s (satakeRes (Ov E w) ⟨ϖ, hϖ⟩) S (fun c₁ c₂ =>
      Φ (blk (satakeGL (Ov E w) hπ0 (sub1 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
        (satakeGL (Ov E w) hπ0 (sub2 S) (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₂ p)))))
    rw [hq] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    obtain ⟨X, hX⟩ := hMat _ (Ov E w) r s _ hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))
    rw [hX, hΦ]
    rfl
  have hcard : ∀ S : Finset (Fin (r + s)), S.card = (sub1 S).card + (sub2 S).card := by
    intro S
    calc S.card = ∑ i : Fin (r + s), if i ∈ S then 1 else 0 := by simp [Finset.sum_boole]
      _ = _ := Fin.sum_univ_add _
      _ = _ := by simp [sub1, sub2, Finset.sum_boole]
  let e : Finset (Fin (r + s)) ≃ Finset (Fin r) × Finset (Fin s) :=
    { toFun := fun S => (sub1 S, sub2 S)
      invFun := fun AB => AB.1.map (Fin.castAddEmb s) ∪ AB.2.map (Fin.natAddEmb r)
      left_inv := by
        intro S
        ext x
        refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp [sub1, sub2] <;>
          intro y hy h <;> rw [← h] <;> exact hy
      right_inv := by
        rintro ⟨A, B⟩
        ext i <;> simp [sub1, sub2] <;> intro y _ h <;> exfalso <;> rw [Fin.ext_iff] at h <;>
          simp at h <;> have := i.isLt <;> have := y.isLt <;> omega }
  have hsubj : ∀ F : Finset (Fin (r + s)) → ℂ,
      ∑ S : {S : Finset (Fin (r + s)) // S.card = j}, F S.1 =
        ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j), F S :=
    fun F => (Finset.sum_subtype _ (fun S => by simp) F).symm
  have hG : ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i) =
      ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 := by
    calc ∑ i : SatakeIdx (n := r + s) w hϖ j, Φ (satakeB w hϖ hu i)
        = ∑ S : {S : Finset (Fin (r + s)) // S.card = j},
            ∑ c : satakePairs S.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          Fintype.sum_sigma (fun i => Φ (satakeB w hϖ hu i))
      _ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin (r + s)) => S.card = j),
            ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))) :=
          hsubj (fun S => ∑ c : satakePairs S → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
              Φ (satakeGL (Ov E w) hπ0 S (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c p))))
      _ = ∑ S : Finset (Fin (r + s)), if S.card = j then
            (qV E w : ℂ) ^ ((sub1 S).card * (s - (sub2 S).card)) * T (sub1 S) (sub2 S) else 0 := by
          rw [Finset.sum_filter]
          simp only [hS]
      _ = ∑ S, coef (qV E w) r s j (κ (e S)) * T (e S).1 (e S).2 := by
          refine Finset.sum_congr rfl (fun S _ => ?_)
          simp only [e, Equiv.coe_fn_mk, hκ, coef, hcard S]
          split_ifs <;> simp
      _ = ∑ AB, coef (qV E w) r s j (κ AB) * T AB.1 AB.2 :=
          Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hR : ∀ a b : ℕ, ∑ i₁ : SatakeIdx (n := r) w hϖ a, ∑ i₂ : SatakeIdx (n := s) w hϖ b,
      Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)) =
      ∑ AB ∈ (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = b)), T AB.1 AB.2 := by
    intro a b
    rw [Finset.sum_product]
    calc _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ c₁ : satakePairs A.1 → satakeRes (Ov E w) ⟨ϖ, hϖ⟩,
            ∑ i₂ : SatakeIdx (n := s) w hϖ b,
              Φ (blk (satakeGL (Ov E w) hπ0 A.1 (fun p => satakeSec (Ov E w) ⟨ϖ, hϖ⟩ (c₁ p)))
                (satakeB w hϖ hu i₂)) :=
          Fintype.sum_sigma (fun i₁ => ∑ i₂ : SatakeIdx (n := s) w hϖ b,
            Φ (blk (satakeB w hϖ hu i₁) (satakeB w hϖ hu i₂)))
      _ = ∑ A : {A : Finset (Fin r) // A.card = a}, ∑ B : {B : Finset (Fin s) // B.card = b}, T A.1 B.1 := by
          refine Finset.sum_congr rfl (fun A _ => ?_)
          simp only [hT]
          refine (Finset.sum_congr rfl (fun c₁ _ => Fintype.sum_sigma _)).trans ?_
          exact Finset.sum_comm
      _ = _ := by
          rw [← Finset.sum_subtype (Finset.univ.filter (fun A : Finset (Fin r) => A.card = a)) (by simp)
            (fun A => ∑ B : {B : Finset (Fin s) // B.card = b}, T A B.1)]
          refine Finset.sum_congr rfl (fun A _ => ?_)
          exact (Finset.sum_subtype _ (by simp) _).symm
  rw [hG]
  simp only [hR]
  rw [← Finset.sum_fiberwise Finset.univ κ]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.mul_sum]
  have hfib : Finset.univ.filter (fun AB => κ AB = p) =
      (Finset.univ.filter (fun A : Finset (Fin r) => A.card = (p.1 : ℕ))) ×ˢ
        (Finset.univ.filter (fun B : Finset (Fin s) => B.card = (p.2 : ℕ))) := by
    ext ⟨A, B⟩
    simp [hκ, Prod.ext_iff, Fin.ext_iff]
  rw [hfib]
  refine Finset.sum_congr rfl (fun AB hAB => ?_)
  have hp : κ AB = p := by
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hAB
    rw [hκ]
    ext <;> simp [hAB]
  rw [hp]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HkSum
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host
open GlobalTheory.PRep (fixed)

namespace UpperTheory.V.Cj.S

theorem hkSum : HkSum := by
  intro E _ _ w n V _ _ ρ ϖ hϖ hu _ j hj x hx
  classical
  have hr := satake_range_eq (n := n) w hϖ hu Final.TjCosets hj
  unfold heckeVec
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun i : SatakeIdx w hϖ (n := n) j =>
      ((satakeB w hϖ hu i : GL (Fin n) (w.adicCompletion E)) :
        GL (Fin n) (w.adicCompletion E) ⧸ KGL w (n := n)))) ?_]
  · rw [Finset.sum_image (fun i _ i' _ h => satakeB_inj w hϖ hu h)]
    refine Finset.sum_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KGL w (n := n)) (satakeB w hϖ hu i)
    have hfix : ρ (k : GL (Fin n) (w.adicCompletion E)) x = x := GlobalTheory.LGrp.mem_fixed.1 hx _ k.2
    rw [hk, satake_Tj_eq, Set.indicator_of_mem (satake_Tset_right w (satakeB_mem w hϖ hu i) k.2),
      Pi.one_apply, one_smul, map_mul, Module.End.mul_apply, hfix]
  · intro y hy
    have hT : Tj ℂ n (Ov E w) ϖ j y.out ≠ 0 := fun h0 => hy (by simp only [h0, zero_smul])
    have hy' : y ∈ Set.range _ := hr.ge ((satake_Tj_ne_zero_iff w ℂ ϖ j _).1 hT)
    obtain ⟨i, rfl⟩ := hy'
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ i))

end UpperTheory.V.Cj.S
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullBdd
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hull_le {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {S U : Submodule ℂ (Sm E a)} (h : ∀ T ∈ Comm E a, ∀ φ ∈ S, T φ ∈ U) : hull S ≤ U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, φ, hφ, rfl⟩
  exact h T hT φ hφ

private theorem smEq_aeval {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (z : GroundTheory.Automorphic.AutomorphicForm.UEnv E a) (p : Polynomial ℂ) (φ : Sm E a) :
    Polynomial.aeval (GroundTheory.Automorphic.AutomorphicForm.uAction z) p (UpperTheory.V.Cm.smEq E a φ) =
      UpperTheory.V.Cm.smEq E a (Polynomial.aeval (UpperTheory.V.Cm.uTC E a z) p φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, UpperTheory.V.Cm.smEq_uTC]

private theorem commute_aeval {A : Type} [Ring A] [Algebra ℂ A] {T z : A} (h : Commute T z) (p : Polynomial ℂ) :
    Commute T (Polynomial.aeval z p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial]
    exact (Algebra.commute_algebraMap_right c T).mul_right (h.pow_right n)

theorem UpperTheory.V.Cj.S.hullBdd :
    UpperTheory.V.Cj.S.TypesComm → UpperTheory.V.Cj.S.HullBdd := by
  intro hTC E _ _ _ a S hS L hL
  have haut : ∀ φ ∈ hull S, GroundTheory.Automorphic.AutomorphicForm.IsAutomorphicForm φ.1 := fun φ hφ =>
    (Cm.isAutForm_iff φ).1 (Cm.mem_range_ofAut.1 (hull_le (U := LinearMap.range (Cm.ofAut E a))
      (fun T hT ψ hψ => Cm.mem_range_ofAut.2 (hT.2.2 ψ ((Cm.isAutForm_iff ψ).2
        (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hS _ ⟨ψ, hψ, rfl⟩)))) hφ))
  refine ⟨?_, ?_, ⟨L, hL, ?_⟩, ?_, fun z hz => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ.1).isLeftInvariant
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ.1).hasModerateGrowth
  · rintro _ ⟨φ, hφ, rfl⟩ u hu g
    rw [Fb.finEmb_eq]
    have h1 : finRep E a u φ = φ := (hφ.2 ⟨u, hu⟩).trans (by simp)
    exact congrFun (congrArg Subtype.val h1) g
  · obtain ⟨V, hV, hst, hm⟩ := hS.types
    refine ⟨V, hV, hst, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩ g
    let U : Submodule ℂ (Sm E a) :=
      { carrier := {ψ | (fun k : archCompact E a => ψ.1 (g * infEmb E a k.1)) ∈ V}
        zero_mem' := V.zero_mem
        add_mem' := fun hx hy => V.add_mem hx hy
        smul_mem' := fun c _ hx => V.smul_mem c hx }
    exact hull_le (U := U) (fun T hT ψ hψ => hTC E a V hV T hT.1 ψ (hm _ ⟨ψ, hψ, rfl⟩) g) hφ.1
  · obtain ⟨p, hp, hm⟩ := hS.centre z hz
    refine ⟨p, hp, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have h0 : φ ∈ LinearMap.ker (Polynomial.aeval (Cm.uTC E a z) p) := by
      refine hull_le (fun T hT ψ hψ => ?_) hφ.1
      have h1 := hm _ ⟨ψ, hψ, rfl⟩
      rw [Submodule.mem_bot, LinearEquiv.coe_coe, smEq_aeval] at h1
      have h1 : Polynomial.aeval (Cm.uTC E a z) p ψ = 0 :=
        (Cm.smEq E a).injective (h1.trans (Cm.smEq E a).map_zero.symm)
      rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← (commute_aeval (hT.2.1 z hz) p).eq, Module.End.mul_apply, h1,
        map_zero]
    rw [Submodule.mem_bot, LinearEquiv.coe_coe, smEq_aeval, LinearMap.mem_ker.1 h0, (Cm.smEq E a).map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HullOps
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

section

open UpperTheory.V

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem hull_stable {T : Module.End ℂ (Sm E a)} (hT : T ∈ Comm E a) (S : Submodule ℂ (Sm E a)) :
    ∀ φ ∈ hull S, T φ ∈ hull S := by
  have : hull S ≤ (hull S).comap T := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨T', hT', φ, hφ, rfl⟩
    exact Submodule.subset_span ⟨T * T', ⟨fun k => (hT.1 k).mul_left (hT'.1 k),
      fun z hz => (hT.2.1 z hz).mul_left (hT'.2.1 z hz), fun ψ h => hT.2.2 _ (hT'.2.2 ψ h)⟩, φ, hφ, rfl⟩
  exact fun φ hφ => this hφ

private theorem aut_cap (t : E →+* ℂ) (u : ℂ) (φ : Sm E a) (h : IsAutForm φ) : IsAutForm (cap t u φ) := by
  obtain ⟨p, -, q, -, e⟩ := Cm.mem_Zalg_iff.1 (Cm.cap_mem_Zalg (a := a) t u)
  obtain ⟨ψ, rfl⟩ := Cm.mem_range_ofAut.2 h
  refine Cm.mem_range_ofAut.1 ⟨GroundTheory.Automorphic.AutomorphicForm.uActionAF E a p ψ +
    Complex.I • GroundTheory.Automorphic.AutomorphicForm.uActionAF E a q ψ, ?_⟩
  rw [e, map_add (f := _), map_smul]
  rfl

private theorem smEq_fin (g : GL (Fin a) (Af E)) (φ : Sm E a) :
    Cm.smEq E a (finRep E a g φ) = GroundTheory.Automorphic.AutomorphicForm.rtFin g (Cm.smEq E a φ) :=
  Subtype.ext (funext fun x => (congrArg (fun f : GL (Fin a) (Af E) →* GA E a => φ.1 (x * f g)) Fb.finEmb_eq).symm)

private theorem fin_mem (g : GL (Fin a) (Af E)) : finRep E a g ∈ Comm E a := by
  refine ⟨fun k => ?_, fun z _ => ?_, fun φ h => ?_⟩
  · exact Commute.map (show Commute (finGL E a g) (infGL E a (Unitary.toUnits k)) from (infGL_comm _ _).symm) (rt E a)
  · refine LinearMap.ext fun φ => (Cm.smEq E a).injective ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, smEq_fin, Cm.smEq_uTC, Cm.smEq_uTC, smEq_fin,
      GroundTheory.Automorphic.AutomorphicForm.uAction_rtFin]
  · refine (Cm.isAutForm_iff _).2 ?_
    rw [← Cm.coe_smEq, smEq_fin]
    exact ((Cm.isAutForm_iff _).1 h).rightTranslate_finEmb g

end

theorem UpperTheory.V.Cj.S.hullOps :
    UpperTheory.V.Cj.S.CapAct → UpperTheory.V.Cj.S.HullOps := by
  intro hc E _ _ _ a S
  refine ⟨fun φ hφ => Submodule.subset_span ⟨1, ⟨fun _ => Commute.one_left _, fun _ _ => Commute.one_left _,
    fun _ h => h⟩, φ, hφ, rfl⟩, fun t u => hull_stable ⟨fun k => (hc E a t u).2.1 (.cpt k),
      fun z _ => (hc E a t u).2.2.1 z, aut_cap t u⟩ S, fun g => hull_stable (fin_mem g) S⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Imports
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.iwa :
    UpperTheory.V.Cj.S.RtK → UpperTheory.V.Cj.S.Iwa := by
  intro hK E _ _ _ r s φ m B hφ ⟨g, hg⟩
  obtain ⟨b, hb, k, hk, rfl⟩ := GroundTheory.Automorphic.Reduction.exists_adelicBorel_mul_maxCompact (K := E) (n := r + s) g
  obtain ⟨X, m₁, m₂, rfl⟩ := UpperTheory.upperTriangular_eq_unipotent_mul_levi _ r s b (GroundTheory.Automorphic.Reduction.mem_adelicBorel.1 hb)
  refine ⟨_, hK E (r + s) φ m B hφ k hk, m₁, m₂, ?_⟩
  have hl : GroundTheory.Automorphic.AutomorphicForm.IsLeftInvariant φ.1 := hφ.aut.left
  rw [mul_assoc, UpperTheory.constantTerm_unipotent_left_invariant E (r + s) r φ.1 hl] at hg
  rw [← GroundTheory.Automorphic.AutomorphicForm.constantTerm_rightTranslate] at hg
  exact hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.ImportsAlt
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

theorem UpperTheory.V.Cj.S.step :
    UpperTheory.V.Cj.S.PairEig → UpperTheory.V.Cj.S.SliceBdd → UpperTheory.V.Cj.S.Iwa → UpperTheory.V.Cj.S.CtCap → UpperTheory.V.Cj.S.CtSat → UpperTheory.V.Cj.S.CapRel → UpperTheory.V.Cj.S.HkRel → UpperTheory.V.Cj.S.CapArith → UpperTheory.V.Cj.S.SatArith → UpperTheory.V.Cj.S.Step := by
  intro hPair hSlice hIwa hCtCap hCtSat hCapRel hHkRel hCapA hSatA E _ _ _ r s φ₀ m B h₀ hne₀
  obtain ⟨φ, hφ, hne⟩ := hIwa E r s φ₀ m B h₀ hne₀
  obtain ⟨S₁, S₂, hS₁, hS₂, hs₁, hs₂⟩ := hSlice E r s φ hφ.aut
  obtain ⟨ψ, hψ, hNI, hcap⟩ := hCtCap E (r + s) r φ hφ.aut
  rw [← hψ] at hne hs₁ hs₂
  have hψ0 : ψ ≠ 0 := by
    rintro rfl
    obtain ⟨x, y, h⟩ := hne
    exact h rfl
  obtain ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, hc, hs⟩ := hPair E r s (res ψ.1) S₁ S₂ hS₁ hS₂ hne hs₁ hs₂
  refine ⟨φ₁, φ₂, m₁, m₂, B₁, B₂, h₁, h₂, fun t => ?_, fun ν ν' hν hν' => ?_⟩
  · refine hCapA (m t) (m₁ t) (m₂ t) _ _ fun u => ?_
    have e1 : u + ((-((s : ℝ) / 2) : ℝ) : ℂ) = u - (s : ℂ) / 2 := by push_cast; ring
    have e2 : u + (((r : ℝ) / 2 : ℝ) : ℂ) = u + (r : ℂ) / 2 := by push_cast; ring
    rw [e1, e2]
    refine hc t _ _ _ _ (hCapRel E r s ψ hNI t u) fun x y => ?_
    rw [hcap t u, (hφ.cap t).2 u, hψ]
    simp only [res, constantTerm, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    exact MeasureTheory.integral_const_mul _ _
  · filter_upwards [hφ.sat, h₁.sat, h₂.sat, hs] with w hw hw₁ hw₂ hw₃
    have hv := hCtSat E (r + s) r φ ψ hφ.aut hψ hψ0 w (B w) hw
    obtain ⟨ϖ, hu⟩ := exists_isUnifV w
    refine hSatA (qV E w) r s (qV_ne_zero w) (B w) (B₁ w) (B₂ w) hw.2.2.1 hw₁.2.2.1 hw₂.2.2.1 (fun j hj => ?_) _ _ ?_ ?_
    · obtain ⟨G, hG, hsum⟩ := hHkRel E r s ψ hNI w hv.2.1 ϖ hu j hj
      refine hw₃ ϖ hu _ G _ hG fun x y => ?_
      rw [hsum x y]
      have : tOp (r + s) w hu j ψ = satEig (qV E w) (r + s) (B w) j • ψ := hv.2.2.2 ϖ hu j hj
      rw [this]
      rfl
    · rw [hν.2.1 w]
      congr 1
      push_cast; ring
    · rw [hν'.2.1 w]
      congr 1
      push_cast; ring
end

