module

public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.SliceShift
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.AbsTaylor
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.SubEqZeroIff
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.AbsKill
section
open NumberField MvPolynomial PositivityTheory.Rg.Fx

private theorem vars_pieceK {ι κ : Type} [Fintype ι] (k : ℕ) (F : KF ι κ) : ∀ j ∈ (pieceK k F).vars, j ∈ F.vars := by
  classical
  intro j hj
  rw [mem_vars_iff_mem_support] at hj ⊢
  obtain ⟨d, hd, hjd⟩ := hj
  refine ⟨d, ?_, hjd⟩
  by_contra hn
  apply mem_support_iff.mp hd
  unfold pieceK
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun β hβ => ?_
  rw [coeff_monomial, if_neg]
  rintro rfl
  exact hn hβ

private theorem congr_mod {σ κ A : Type} [CommRing A] [Algebra ℂ A] (J : Ideal A) (Z X : σ → A) (e : σ → MvPolynomial σ ℂ)
    (H H' : κ → A) (G P : MvPolynomial κ (MvPolynomial σ ℂ)) (hZ : ∀ p, Z p - aeval X (e p) ∈ J)
    (hH : ∀ k ∈ P.vars, H k - H' k ∈ J)
    (hG : map (aeval e : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom G = P) :
    eval₂ (aeval Z).toRingHom H G - eval₂ (aeval X).toRingHom H' P ∈ J := by
  rw [← Ideal.Quotient.eq]
  have h1 : (Ideal.Quotient.mkₐ ℂ J).comp (aeval Z) = ((Ideal.Quotient.mkₐ ℂ J).comp (aeval X)).comp (aeval e) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
    exact Ideal.Quotient.eq.mpr (hZ p)
  have h2 : (Ideal.Quotient.mk J).comp (aeval Z).toRingHom =
      ((Ideal.Quotient.mk J).comp (aeval X).toRingHom).comp
        (aeval e : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ).toRingHom :=
    RingHom.ext fun p => DFunLike.congr_fun h1 p
  rw [eval₂_comp_left, eval₂_comp_left, h2, ← eval₂_map, hG]
  refine eval₂Hom_congr' rfl (fun j hj _ => ?_) rfl
  exact Ideal.Quotient.eq.mpr (hH j hj)

theorem UpperTheory.ConvolutionTheory.BW.absKill :
    UpperTheory.ConvolutionTheory.BW.AbsKill := by
  intro τ κ A V _ _ n r _ _ _ _ _ _ Z H I t c idx Λ h good C hS F G hgood hev hG φ x
  classical
  obtain ⟨τ₀⟩ := ‹Nonempty τ›
  choose s hs using hS.surj
  let b : Fam (τ × Fin n) κ :=
    { r := r
      Λ := Λ
      emb := Matrix.of fun p j => if idx p.2 = j then 1 else 0
      pr := Matrix.of fun j p => if p = (τ₀, s j) then 1 else 0
      pr_emb := by
        ext i j
        rw [Matrix.mul_apply, Finset.sum_eq_single (τ₀, s i) (fun p _ hp => by simp [hp]) (by simp)]
        simp [hs, Matrix.one_apply]
      h := h }
  have hsub : b.sub F = 0 := by
    rw [UpperTheory.ConvolutionTheory.FX.sub_eq_zero_iff]
    rintro Λ' h' ⟨z, h1, h2⟩
    have e1 : Λ' = fun p => Λ p + z (idx p.2) := by
      funext p
      rw [h1]
      simp [b, apply_ite ((↑) : ℝ → ℂ)]
    have e2 : h' = fun k => ev z (h k) := funext h2
    rw [e1, e2]
    exact hev z
  have key := UpperTheory.ConvolutionTheory.FX.rearrange (τ × Fin n) κ b A V I t ((LinearMap.proj x).comp c)
    (fun v m => UpperTheory.ConvolutionTheory.FX.abs_taylor τ κ A V n r Z H I t c idx Λ h good C hS v x m) F φ
  rw [hsub, map_zero, zero_smul, map_zero] at key
  let J : Ideal A :=
    { carrier := {a | ∀ ψ, c (a • ψ) = 0}
      add_mem' := fun {a a'} ha ha' ψ => by rw [add_smul, map_add (f := _), ha, ha', add_zero]
      zero_mem' := fun ψ => by rw [zero_smul, map_zero]
      smul_mem' := fun a a' ha ψ => by rw [smul_eq_mul, mul_comm, mul_smul]; exact ha _ }
  have hJ : ∀ a a' : A, a - a' ∈ J ↔ ∀ ψ, c (a • ψ) = c (a' • ψ) := fun a a' =>
    forall_congr' fun ψ => by rw [sub_smul, map_sub, sub_eq_zero]
  have hX : (fun i : τ × Fin n => algebraMap ℂ A (b.Λ i) + ∑ j, (b.emb i j : ℂ) • I j) =
      fun q => algebraMap ℂ A (Λ q) + I (idx q.2) := by
    funext p
    simp [b, apply_ite ((↑) : ℝ → ℂ)]
  rw [hX] at key
  convert key using 2 with k
  have := congr_mod J Z (fun q => algebraMap ℂ A (Λ q) + I (idx q.2)) blockE H (fun k' => lift I t (h k')) (G k)
    (pieceK k F) (fun p => (hJ _ _).mpr (hS.cen p))
    (fun j hj => (hJ _ _).mpr (hS.hecke j (hgood j (vars_pieceK k F j hj)))) (hG k)
  exact congrFun ((hJ _ _).mp this φ) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.CuspidalNormBounds.NearDat
section
open NumberField UpperTheory.ConvolutionTheory.BW

noncomputable section

section
variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {S : Set (Pl E)}

private abbrev Pt (E : Type) [Field E] [NumberField E] (n : ℕ) : Type :=
  ((E →+* ℂ) × Fin n → ℂ) × (Pl E → Multiset ℂ)

open Classical in
private def inv {n : ℕ} (d : Dat S n) : ℕ × Set (Pt E n) :=
  (d.len, Set.range fun z => (d.ptL z, fun w => if w ∈ S then 0 else d.ptS z w))

private def glue (r s : ℕ) (p : ((E →+* ℂ) → Fin r → ℂ) × (Pl E → Multiset ℂˣ)) (x : ℕ × Set (Pt E s)) :
    ℕ × Set (Pt E (r + s)) :=
  (x.1 + 1, {y | ∃ z : ℂ, ∃ q ∈ x.2, y = (fun a => Fin.addCases (fun i => p.1 a.1 i + z) (fun i => q.1 (a.1, i)) a.2,
    fun w => ((p.2 w).map fun b : ℂˣ => (b : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z)) + q.2 w)})

open Classical in
private theorem pt_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) (z₀ : ℂ) (z : Fin d.len → ℂ) :
    (((Dat.cons b d).ptL (Fin.cons z₀ z : Fin (d.len + 1) → ℂ),
      fun w => if w ∈ S then 0 else (Dat.cons b d).ptS (Fin.cons z₀ z : Fin (d.len + 1) → ℂ) w) : Pt E (r + s)) =
    (fun a => Fin.addCases (fun i => b.Λ a.1 i + z₀) (fun i => d.ptL z (a.1, i)) a.2,
      fun w => ((if w ∈ S then 0 else b.sat w).map fun b : ℂˣ => (b : ℂ) * ((Formalism.UG.qV E w : ℕ) : ℂ) ^ (-z₀)) +
        if w ∈ S then 0 else d.ptS z w) := by
  refine Prod.ext (funext fun ⟨τ, i⟩ => ?_) (funext fun w => ?_)
  · induction i using Fin.addCases with
    | left i =>
      have e : (Dat.cons b d).idx (Fin.castAdd s i) = (0 : Fin (d.len + 1)) :=
        Fin.addCases_left (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      simp only [Dat.ptL, Dat.lam, Fin.addCases_left, e, Fin.cons_zero]
    | right i =>
      have e : (Dat.cons b d).idx (Fin.natAdd r i) = ((d.idx i).succ : Fin (d.len + 1)) :=
        Fin.addCases_right (motive := fun _ => Fin (d.len + 1)) (left := fun _ => 0) (right := fun i => (d.idx i).succ) i
      simp only [Dat.ptL, Dat.lam, Fin.addCases_right, e, Fin.cons_succ]
  · dsimp only
    split_ifs
    · simp
    · exact Fin.sum_univ_succ (n := d.len) _

open Classical in
private theorem inv_cons {r s : ℕ} (b : Blo S r) (d : Dat S s) :
    inv (Dat.cons b d) = glue r s (b.Λ, fun w => if w ∈ S then 0 else b.sat w) (inv d) := by
  refine Prod.ext rfl (Set.ext fun y => ⟨?_, ?_⟩)
  · rintro ⟨z, rfl⟩
    refine ⟨z (0 : Fin (d.len + 1)), _, ⟨Fin.tail (n := d.len) (α := fun _ => ℂ) z, rfl⟩, ?_⟩
    have := pt_cons b d (z (0 : Fin (d.len + 1))) (Fin.tail (n := d.len) (α := fun _ => ℂ) z)
    rw [Fin.cons_self_tail (n := d.len) (α := fun _ => ℂ) z] at this
    exact this
  · rintro ⟨z₀, _, ⟨z, rfl⟩, rfl⟩
    exact ⟨_, pt_cons b d z₀ z⟩

private theorem dat_cases {n : ℕ} (d : Dat S n) :
    (∃ h : 0 = n, d = h ▸ Dat.nil) ∨ ∃ (r s : ℕ) (h : r + s = n) (b : Blo S r) (d' : Dat S s), d = h ▸ Dat.cons b d' := by
  cases d with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons b d' => exact Or.inr ⟨_, _, rfl, b, d', rfl⟩

private theorem finite_inv (S : Set (Pl E)) (B : ℝ) (n : ℕ) : ∀ ρ : Typ E n,
    (inv '' {d : Dat S n | d.HasTyp ρ.ρ ∧ ∀ τ i, ‖d.lam τ i‖ ≤ B}).Finite := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ρ
  have h0 : {x | ∃ h : 0 = n, x = inv (h ▸ Dat.nil : Dat S n)}.Finite :=
    Set.Subsingleton.finite (by rintro _ ⟨h, rfl⟩ _ ⟨h', rfl⟩; rfl)
  have h1 : ∀ p ∈ Set.Iic n ×ˢ Set.Iic n, {x | ∃ (h : p.1 + p.2 = n) (b : Blo S p.1) (d' : Dat S p.2),
      (h ▸ Dat.cons b d' : Dat S n).HasTyp ρ.ρ ∧ (∀ τ i, ‖(h ▸ Dat.cons b d' : Dat S n).lam τ i‖ ≤ B) ∧
        x = inv (h ▸ Dat.cons b d' : Dat S n)}.Finite := by
    rintro ⟨r, s⟩ -
    by_cases hp : r + s = n
    swap
    · exact Set.finite_empty.subset (by rintro _ ⟨h, -⟩; exact hp h)
    subst hp
    by_cases hr : 0 < r
    swap
    · exact Set.finite_empty.subset (by rintro _ ⟨-, b, -⟩; exact hr b.pos)
    obtain ⟨⟨ρ₁, c₁, e₁⟩, ⟨ρ₂, c₂, e₂⟩, -⟩ := resTyp E r s ρ
    refine (Set.Finite.image2 (glue r s) (nearBlo E S r ⟨ρ.d, ρ₁, c₁⟩ B) (ih s (by omega) ⟨ρ.d, ρ₂, c₂⟩)).subset ?_
    rintro _ ⟨h, b, d', ⟨k₁, k₂⟩, hB, rfl⟩
    refine ⟨_, ⟨b, ?_, fun τ i => ?_, rfl, fun _ => rfl⟩, _, ⟨d', ⟨?_, fun τ i => ?_⟩, rfl⟩, (inv_cons b d').symm⟩
    · change Killed ρ₁ _
      rw [e₁]; exact k₁
    · simpa only [Dat.lam, Fin.addCases_left] using hB τ (Fin.castAdd s i)
    · change d'.HasTyp ρ₂
      rw [e₂]; exact k₂
    · simpa only [Dat.lam, Fin.addCases_right] using hB τ (Fin.natAdd r i)
  refine (h0.union (((Set.finite_Iic n).prod (Set.finite_Iic n)).biUnion h1)).subset ?_
  rintro _ ⟨d, ⟨hd, hB⟩, rfl⟩
  rcases dat_cases d with ⟨h, rfl⟩ | ⟨r, s, h, b, d', rfl⟩
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr (Set.mem_biUnion (x := (r, s)) ⟨show r ≤ n by omega, show s ≤ n by omega⟩ ⟨h, b, d', hd, hB, rfl⟩)

end

theorem UpperTheory.ConvolutionTheory.BW.nearDat :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], UpperTheory.ConvolutionTheory.BW.NearDat E := by
  intro E _ _ _ S n ρ B
  obtain ⟨D, -, hD⟩ := Set.exists_subset_bijOn {d : Dat S n | d.HasTyp ρ.ρ ∧ ∀ τ i, ‖d.lam τ i‖ ≤ B} inv
  refine ⟨D, Set.Finite.of_finite_image (by rw [hD.image_eq]; exact finite_inv S B n ρ) hD.injOn, fun d hd hB => ?_⟩
  obtain ⟨d', hd', he⟩ := hD.surjOn ⟨d, ⟨hd, hB⟩, rfl⟩
  refine ⟨d', hd', congrArg Prod.fst he, fun F hF hK z => ?_⟩
  obtain ⟨z', hz⟩ : _ ∈ (inv d').2 := by rw [he]; exact ⟨z, rfl⟩
  rw [← hK z']
  have e₁ : d'.ptL z' = d.ptL z := congrArg Prod.fst hz
  rw [e₁]
  refine MvPolynomial.eval₂Hom_congr' rfl (fun x hx _ => ?_) rfl
  have e₂ := congrFun (congrArg Prod.snd hz) x.1
  simp only [ite_eq_right (hF x hx)] at e₂
  rw [Dat.ptH, Dat.ptH, e₂]
end
end

