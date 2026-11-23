module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0045
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0063
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ZEqDimE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0048
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0053
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJRing
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
section Abstract
open UpperTheory.V.W
private theorem jr_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)
private theorem jr_isTeich {l : ℕ} [hl : Fact l.Prime] {F : GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1 := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := jr_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩, fun i g h => ?_⟩
  · rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  · rw [MonoidHom.comp_apply, h, map_one]
private theorem jr_abs {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B) {ι : Type} (K : Type) [CommRing K] [Algebra O K]
    (x : ι → B.B →ₐ[O] K) (hJ : ∀ i, ∀ b ∈ J, x i b = 0) (sep : ∀ b, (∀ i, x i b = 0) → b ∈ J)
    (ρ : ι → F.G₀ →* GL (Fin n) K) (hD : ∀ i, B.u.D.map (x i : B.B →+* K) = GDet.ofRep (mat (ρ i)))
    (form : ∀ i, ∃ P, F.IsForm O n (ρ i) P)
    (flag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (x i : B.B →+* K) (B.u.ψ v j))
    (type : ∀ i t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
      ((g * ρ i y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y))
    (unr : r.V0ok → ∀ i, ∀ g ∈ F.I0, ρ i g = 1)
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1)
    (fin : ((Ideal.Quotient.mk J).comp (Λ.toPair B.u : Λ.Λ →+* B.B)).Finite)
    (tf : ∀ a : Λ.Λ, a ≠ 0 → ∀ b : B.B, Λ.toPair B.u a * b ∈ J → b ∈ J) : B.RingProps Λ J := by
  let f : ι → (B.B ⧸ J) →ₐ[O] K := fun i => Ideal.Quotient.liftₐ J (x i) (hJ i)
  have hf : ∀ i, (f i : B.B ⧸ J →+* K).comp (Ideal.Quotient.mk J) = x i := fun i => rfl
  have hinj : ∀ a, (∀ i, f i a = 0) → a = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (sep b ha)
  have hD' : ∀ i, (B.DD J).map (f i : B.B ⧸ J →+* K) = GDet.ofRep (mat (ρ i)) := fun i => by
    rw [UniversalOrdinaryDeterminantRing.DD, (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1, hf, hD]
  have hflag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) := flag
  have hP : F.IsPolar O (B.DD J) := UpperTheory.V.AlgebraTools.Det.polarInj F O _ n _ (fun _ => K) f hinj fun i => by
    obtain ⟨P, hP⟩ := form i
    rw [hD' i]
    exact (UpperTheory.V.AlgebraTools.Det.formRep F O K n (ρ i) P hP).2.2
  have hker : ∀ g, (∀ i, ρ i g = 1) → (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) ∧
      (B.DD J).Kills (F.star O _ n (MonoidAlgebra.single g 1) - 1) := fun g hg => by
    have hk : (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      rw [map_sub, map_sub, map_one, map_one, MonoidAlgebra.mapRingHom_single, map_one]
      simp [GDet.repAlg, mat, hg i]
    refine ⟨hk, ?_⟩
    have h1 := UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk
    have h2 : F.star O (B.B ⧸ J) n (MonoidAlgebra.single g 1 - 1) = F.star O _ n (MonoidAlgebra.single g 1) - 1 := by
      simp [GFrame.star]
    rwa [h2] at h1
  refine ⟨fin, tf, hP, fun v g => ?_, fun v g => ?_, fun u g hg => hker g fun i => ?_, fun t ht u => ?_,
    fun h g hg => hker g fun i => unr h i g hg⟩
  · ext k
    rw [← sub_eq_zero]
    apply hinj
    intro i
    have h1 := (UpperTheory.V.AlgebraTools.Det.mapApi (B.DD J) (f i : B.B ⧸ J →+* K)).1 (MonoidAlgebra.single (F.φ v g) 1)
    rw [hD' i, MonoidAlgebra.mapRingHom_single, map_one, (UpperTheory.V.AlgebraTools.Det.repApi (mat (ρ i))).2.1] at h1
    have h2 := (UpperTheory.V.AlgebraTools.Det.flagRel _ _ (hflag i v)).1 g
    have h3 : mat ((ρ i).comp (F.φ v)) g = mat (ρ i) (F.φ v g) := rfl
    rw [h3, h1] at h2
    have h4 : (∏ j, (X - C ((B.psiT J v j g : (B.B ⧸ J)ˣ) : B.B ⧸ J))).map (f i : B.B ⧸ J →+* K) =
        ∏ j, (X - C ((pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) g : Kˣ) : K)) := by
      rw [Polynomial.map_prod]
      simp
    have h5 := congrArg (fun p => p.coeff k) (h2.trans h4.symm)
    simp only [Polynomial.coeff_map] at h5
    rw [map_sub, sub_eq_zero]
    exact h5
  · have hk : (B.DD J).Kills (F.oEl v (B.psiT J v) g) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      have h1 : MonoidAlgebra.mapRingHom F.G₀ (f i : B.B ⧸ J →+* K) (F.oEl v (B.psiT J v) g) =
          F.oEl v (fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j)) g := by
        unfold GFrame.oEl
        rw [map_list_prod, List.map_ofFn]
        apply congrArg (fun terms => (List.ofFn terms).prod)
        funext j
        simp only [Function.comp_apply, map_sub, MonoidAlgebra.mapRingHom_single, map_one,
          pushCh, MonoidHom.comp_apply, Units.coe_map]
        rfl
      rw [h1]
      exact UpperTheory.V.AlgebraTools.Det.oElRep F O K n (ρ i) v _ (hflag i v) g
    exact ⟨hk, UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk⟩
  · obtain ⟨t, ht, ht1⟩ := hT
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 := hQ g hg.1
    have h2 : ∀ j, t j g = 1 := fun j => ht1 j g (Subgroup.mem_iInf.1 hg.2 j)
    simp only [h2, Units.val_one, map_one, Matrix.diagonal_one] at h1
    have h3 : Q * ρ i g * Q⁻¹ = 1 := Units.ext h1
    simpa using h3
  · refine (UpperTheory.V.AlgebraTools.Det.injTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) hinj).1 _ _ fun i => ?_
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 : ((B.DD J).comap (F.Iu u).subtype).map (f i : B.B ⧸ J →+* K) =
        ((B.DD J).map (f i : B.B ⧸ J →+* K)).comap (F.Iu u).subtype := rfl
    rw [h1, hD', (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.1, (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.1]
    refine (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q fun y => ?_
    have h2 : (RingHom.mapMatrix (f i : B.B ⧸ J →+* K)).toMonoidHom.comp
        (diagRep fun j => pushCh (algebraMap O (B.B ⧸ J)) ((t j).comp (F.Iu u).subtype)) y =
        Matrix.diagonal fun j => algebraMap O K (t j y) := by
      change (Matrix.diagonal _).map (f i) = _
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext j
      exact (f i).commutes _
    rw [h2, ← hQ y y.2, ← Units.val_mul, inv_mul_cancel_right]
    rfl
private theorem jr_surj {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T] [Algebra Λ.Λ T] (f : B.B →ₐ[O] T)
    (hsurj : Function.Surjective f) (hlam : ∀ b, f (Λ.toPair B.u b) = algebraMap Λ.Λ T b) (K : Type) [CommRing K] [Algebra O K]
    (good : (T →ₐ[O] K) → Prop) (sep : ∀ t, (∀ x, good x → x t = 0) → t = 0)
    (pt : ∀ x, good x → ∃ ρ : F.G₀ →* GL (Fin n) K, (B.u.D.map f.toRingHom).map x.toRingHom = GDet.ofRep (mat ρ) ∧
      (∃ P, F.IsForm O n ρ P) ∧
      (∀ v, HasFlag (ρ.comp (F.φ v)) fun j => pushCh x.toRingHom (pushCh f.toRingHom (B.u.ψ v j))) ∧
      (∀ t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
        ((g * ρ y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y)) ∧
      (r.V0ok → B.u.D.map (x.comp f : B.B →+* K) = GDet.ofRep (mat ρ) → ∀ g ∈ F.I0, ρ g = 1))
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1) (hfin : (algebraMap Λ.Λ T).Finite)
    (htf : ∀ b : Λ.Λ, b ≠ 0 → ∀ t : T, algebraMap Λ.Λ T b * t = 0 → t = 0) : B.RingProps Λ (RingHom.ker f) := by
  choose ρ hD hform hfl hty hun using fun x : {x // good x} => pt x.1 x.2
  have hD' : ∀ x : {x // good x}, B.u.D.map (x.1.comp f : B.B →+* K) = GDet.ofRep (mat (ρ x)) := fun x => by
    rw [← hD x]
    exact ((UpperTheory.V.AlgebraTools.Det.mapApi B.u.D f.toRingHom).2.2.2.2.2.2.1 x.1.toRingHom).symm
  refine jr_abs B Λ _ K (fun x : {x // good x} => x.1.comp f) (fun x b hb => ?_) (fun b hb => ?_) ρ hD' hform hfl hty
    (fun h x => hun x h (hD' x)) hT ?_ ?_
  · rw [AlgHom.comp_apply, (RingHom.mem_ker).1 hb, map_zero]
  · exact sep (f b) fun x hx => hb ⟨x, hx⟩
  · let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
    have he : (Ideal.Quotient.mk (RingHom.ker f)).comp (Λ.toPair B.u : Λ.Λ →+* B.B) =
        (e.symm : T →+* B.B ⧸ RingHom.ker f).comp (algebraMap Λ.Λ T) := by
      refine RingHom.ext fun b => ?_
      change _ = e.symm (algebraMap Λ.Λ T b)
      rw [AlgEquiv.eq_symm_apply]
      exact (Ideal.quotientKerAlgEquivOfSurjective_mk hsurj _).trans (hlam b)
    rw [he]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp hfin
  · intro a ha b hb
    refine htf a ha (f b) ?_
    rw [← hlam, ← map_mul]
    exact hb
end Abstract
theorem UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → B.RingProps Λ J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K _ J hJ
  rcases hJ with ⟨-, rfl⟩ | ⟨hcomm, hco, f, hne, hmap, hsurj, hlam, rfl⟩
  · refine jr_abs B Λ ⊤ (ι := Empty) (Qbar l) Empty.elim (fun i => i.elim) (fun _ _ => trivial) Empty.elim (fun i => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun _ i => i.elim) (jr_isTeich c r) ?_ fun _ _ _ _ => trivial
    exact RingHom.Finite.of_surjective _ fun b => ⟨0, Subsingleton.elim _ _⟩
  have hAx := _root_.UpperTheory.V.Hi.axU_s hP.litN l L Ω s n hn V Q c R.m R.τ₀
  obtain ⟨hdom, hden⟩ := _root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hP.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta
  obtain ⟨-, hfin, htf, -⟩ := hiAlg L Ω l n c (hset Q R.τ₀) hAx Λ.Λ R.θ R.isWt R.a K hne
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have hAut := _root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor
    hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type
  have hLam : lam ∈ (hset Q R.τ₀).admitted := Set.mem_univ _
  have hout := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight
    hP.litN L Ω l n c (hset Q R.τ₀) hAx Λ.Λ R.θ R.isWt ι _ hAut lam hLam
    (hden lam) R.a K _ _ hmap
  refine jr_surj B Λ f hsurj hlam (Qbar l) _ (hout.sep lam hLam (hden lam)) (fun x hx => ?_) (jr_isTeich c r) hfin (htf hdom)
  obtain ⟨ρ, hc, -, hPU, hD, hfl⟩ := hout.pt lam hLam x hx.2.1
  exact ⟨ρ, hD, hPU.form, fun v => (hfl hx v).1, hPU.type, fun h h' => point_rep_unramified_at_auxiliary_place hn B h _ _ hc h'⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TNumJE
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z.Desc.V0
section SlopeTestRemainingChoices
open Formalism.MainNotions.N
variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}
private theorem inv_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) (r : Γ →* GL (Fin n) k) (M : Submodule k (Fin n → k)) :
    IsInv (r.comp φ) M ↔ IsInv r M :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩
private theorem ss_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) {r : Γ →* GL (Fin n) k} (h : IsSSRep r) :
    IsSSRep (r.comp φ) := fun M hM => by
  obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM)
  exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩
private theorem irr_of_comp (φ : Γ' →* Γ) {r : Γ →* GL (Fin n) k} (h : Af.IsIrr (r.comp φ)) : Af.IsIrr r :=
  ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M hM hi => h.2.2 M hM fun g => hi (φ g)⟩
private theorem ss_of_irr {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp
private theorem irr_iso {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r') (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let E : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this
    change (P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec] at this
  have hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective E.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h0
  · left; rw [hm, h0, Submodule.map_bot]
  · right; rw [hm, h0, Submodule.map_top, LinearEquiv.range]
private theorem iso_of_det {r r' : Γ →* GL (Fin n) k} (h : IsSSRep r) (h' : IsSSRep r')
    (e : W.GDet.ofRep (W.mat r) = W.GDet.ofRep (W.mat r')) : Af.RepIso r' r := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm
private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩
private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl
private theorem datEnd {O A B M : Type} [CommRing O] [CommRing A] [IsDomain A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M] (j : A →ₐ[O] B) (φ : B →+* Module.End A M)
    (hj : ∀ a, φ (j a) = algebraMap A _ a) (J : Ideal B) (hJ : ∀ b, b ∈ J ↔ φ b = 0) (hr : J.IsRadical) :
    ∃ _ : Module B M, (∀ (b : B) (m : M), b • m = φ b m) ∧ UpperTheory.V.J.Dat j J M := by
  letI : Module B M := Module.compHom M φ
  have h0 : ∀ (b : B) (m : M), b • m = φ b m := fun _ _ => rfl
  have h1 : Module.annihilator B M = J := by
    ext b
    rw [Module.mem_annihilator, hJ, LinearMap.ext_iff]
    rfl
  refine ⟨inferInstance, h0, fun a m => ?_, inferInstance, inferInstance, hr, fun p _ => by rw [h1], fun c hc a ha => ?_⟩
  · rw [h0, hj]
    rfl
  · rw [hJ] at ha ⊢
    rw [map_mul, hj] at ha
    ext m
    have h2 : c • φ a m = 0 := LinearMap.congr_fun ha m
    refine (Module.Free.chooseBasis A M).repr.injective (Finsupp.ext fun i => ?_)
    have h3 := congrArg (fun v => (Module.Free.chooseBasis A M).repr v i) h2
    simp only [map_smul, map_zero, Finsupp.smul_apply, smul_eq_mul, Finsupp.zero_apply] at h3
    rw [(mul_eq_zero.1 h3).resolve_left hc, LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
private theorem datHecke {O A B N κ : Type} [CommRing O] [CommRing A] [IsDomain A] [CommRing B] [Algebra O A] [Algebra O B]
    [AddCommGroup N] [Module A N] (Y : Submodule A N) (op : κ → Module.End A N) [Fact (CommOn Y op)] [Module.Free A Y]
    [Module.Finite A Y] (j : A →ₐ[O] B) (f : B →+* heckeAlg Y op) (hj : ∀ a, f (j a) = algebraMap A _ a)
    (hr : (RingHom.ker f).IsRadical) :
    ∃ _ : Module B Y, (∀ (b : B) (m : Y), b • m = (f b).1 m) ∧ UpperTheory.V.J.Dat j (RingHom.ker f) Y :=
  datEnd j ((heckeAlg Y op).val.toRingHom.comp f) (fun a => congrArg Subtype.val (hj a)) _
    (fun _ => RingHom.mem_ker.trans Subtype.ext_iff) hr
private theorem datTop {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (j : A →ₐ[O] B) :
    UpperTheory.V.J.Dat j ⊤ PUnit :=
  ⟨fun _ _ => rfl, Module.Free.of_subsingleton A PUnit, ⟨⟨∅, Subsingleton.elim _ _⟩⟩, le_top, fun p _ => by
    rw [Module.annihilator_eq_top_iff.2 ⟨fun _ _ => rfl⟩], fun _ _ _ _ => Submodule.mem_top⟩
end SlopeTestRemainingChoices
private theorem unitN {l : ℕ} [Fact l.Prime] {c : Coef l} {A : Type} [CommRing A] [Algebra c.O A] {N : ℕ} (h : ¬ l ∣ N) :
    IsUnit (N : A) := by
  have h0 : IsUnit (N : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact (PadicInt.norm_natCast_eq_one_iff).2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)
  have h1 := (h0.map (algebraMap ℤ_[l] c.O)).map (algebraMap c.O A)
  simpa using h1
set_option maxHeartbeats 2000000 in
private theorem absDimE (hMu : MuZ) (hME : MuZE) (hSp : Spec2) (hU : UnitEv) (hP : _root_.UpperTheory.V.Z.J.D.PartRepAlt) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) {A : Type} [CommRing A]
    [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ) (ι : Qbar l ≃+* ℂ)
    (a₀ : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a₀ K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a₀ K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a₀ K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a₀ K)ˣ} (out : H.Out θ a₀ K P I (D₀.map f.toRingHom) ψ)
    [Module R (H.MK θ a₀ K)] (hs : ∀ (b : A) (m : H.MK θ a₀ K), b • m = j b • m)
    (hact : ∀ (b : R) (m : H.MK θ a₀ K), b • m = (f b).1 m)
    {G : Type} [Group G] {K₀ K₁ : Subgroup G} (β : G →* H.Ga) (a : G →₀ ℤ) (N : ℕ) (hNK : NormK H K₀ K₁ β) (hE : IsE K₀ K₁ a N)
    (hu : IsUnit (N : A)) (e : Module.End A (H.MK θ a₀ K)) (hep : IsProj H θ β a N e)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam)
    (hρ : ∀ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ → Formalism.MainNotions.N.IsSSRep ρ →
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) → Af.IsIrr ρ) :
    _root_.UpperTheory.V.Z.Desc.V0.IsDimEAlt H θ ι lam K β a N (muE j (H.MK θ a₀ K) hs e x) := by
  obtain ⟨-, hfi, hfr⟩ := (hiComm L Ω l n c H hA A θ hθ K).2.2.2 a₀
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hss, -, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  have hi := hρ ρ hc hss ((map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD)
  obtain ⟨d, ξ, c0, sp, hsp, htr⟩ := hSp L Ω l n c H hA A θ hθ ι (x.comp j) lam har
  obtain ⟨hne, -⟩ := hMu L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp K a₀ R j f hf hs hact y e1
  have hmu := hME L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp htr K a₀ R j f hf hs hact y e1 G K₀ K₁ β a N hNK hE hu e hep
  have e2 : y.comp f = x := AlgHom.ext hy
  rw [e2] at hmu
  refine ⟨x.comp j, d, ξ, c0, sp, _, hsp, fun v i => ?_, hne, fun Y hY => ?_, hmu⟩
  · rw [RingEquiv.symm_apply_apply]
    exact hU L Ω l n c H hA A θ hθ ι K a₀ I _ ψ out.univ y v i
  · obtain ⟨g, hg⟩ := hP L Ω l n c H hA A θ hθ ι (x.comp j) lam d ξ c0 sp hsp K a₀ y e1 I _ ψ out.univ ρ hc hi hD Y hY
    exact irr_iso ⟨g, hg⟩ hi
set_option maxHeartbeats 1000000 in
private theorem irrOf {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} {c : Coef l}
    {r : Resid V.frame c.O n} {B : UniversalOrdinaryDeterminantRing r} (x : B.Pt) (hx : UpperTheory.V.J.IrrPt x)
    (ρ₀ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (hs : Formalism.MainNotions.N.IsSSRep ρ₀)
    (hD : B.u.D.map (x : B.B →+* Qbar l) = W.GDet.ofRep (W.mat ρ₀)) : Af.IsIrr ρ₀ := by
  have hpr : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  obtain ⟨ρ, -, hρ, hi⟩ := hx
  have hr : x.IsRep (ρ₀.comp V.pr) := by
    replace hD : x.D = W.GDet.ofRep (W.mat ρ₀) := hD
    change x.D.comap V.pr = _
    rw [hD]
    exact (AlgebraTools.Det.repApi (W.mat ρ₀)).2.2.2.2.2.2.1 V.pr
  have e : Af.RepIso (ρ₀.comp V.pr) ρ := iso_of_det (ss_of_irr hi) (ss_comp hpr hs) (hρ.symm.trans hr)
  exact irr_of_comp V.pr (irr_iso e.symm' hi)
set_option maxHeartbeats 2000000 in
theorem UpperTheory.V.Z.Desc.V0.numJE_alt :
    UpperTheory.V.Z.J.D.MuZ → MuZE → EEx → Spec2 → NormS → _root_.UpperTheory.V.Z.Desc.V0.ZEqDimEAlt → UpperTheory.V.Z.J.D.UnitEv → _root_.UpperTheory.V.Z.J.D.PartRepAlt → _root_.UpperTheory.V.Z.Desc.V0.NumJEAlt := by
  intro hMu hME hEx hSp hNS hZ hU hP H hM hC l _ L Ω _ _ _ _ _ _ s n hn V hV h4 Q c r ι B Λ R K J hdom hJ hrad
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact ⟨PUnit, inferInstance, inferInstance, inferInstance, datTop _, 0, ⟨by simp, fun _ _ => by simp⟩, fun x _ _ hx =>
      absurd (hx (Submodule.mem_top (x := 1))) (by simp)⟩
  have hA := _root_.UpperTheory.V.Hi.axU_s H.litN l L Ω s n hn V Q c R.m R.τ₀
  obtain ⟨-, hfi, hfr⟩ := (hiComm L Ω l n c (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt K).2.2.2 R.a
  obtain ⟨i3, hact, hdat⟩ := datHecke ((hset Q R.τ₀).MK R.θ R.a K) ((hset Q R.τ₀).op Λ.Λ) (Λ.toPair B.u) f.toRingHom hlam hrad
  obtain ⟨a, N, hE, hlN, hz⟩ := hZ H hM hC l L Ω s n hn V hV h4
  have hNK := hNS l L Ω s n hn V hV Q c R.m R.τ₀
  have hu : IsUnit (N : Λ.Λ) := unitN (c := c) hlN
  obtain ⟨e, hep, hee, hec⟩ := hEx L Ω l n c (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt K R.a _ _ _ (sec0 n s) a N hNK hE hu
  refine ⟨_, inferInstance, i3, inferInstance, hdat, e, ⟨hee, fun b m => ?_⟩, fun x y w hx hy ha hg ix iy => ?_⟩
  · rw [hact, hact]
    exact LinearMap.congr_fun (hec (f b)) m
  obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta w ha.1
  have out := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight H.litN L Ω l n c (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _)
    ((_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  have h := hz Q c r ι R.m R.τ₀ R.type Λ.Λ R.θ R.isWt lam K _ _
    (absDimE hMu hME hSp hU hP (hset Q R.τ₀) hA R.θ R.isWt ι R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out hdat.hs hact
      (sec0 n s) a N hNK hE hu e hep x hx lam (Set.mem_univ _) ((hb lam hl x).1.1 ha)
      fun ρ _ hs hD => irrOf x ix ρ hs hD)
    (absDimE hMu hME hSp hU hP (hset Q R.τ₀) hA R.θ R.isWt ι R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out hdat.hs hact
      (sec0 n s) a N hNK hE hu e hep y hy lam (Set.mem_univ _) ((hb lam hl y).2.1 hg).2.1
      fun ρ _ hs hD => irrOf y iy ρ hs hD)
  exact ⟨h.1, h.2.le⟩
end
end

