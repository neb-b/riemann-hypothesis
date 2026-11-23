module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0032
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RawChartFormalBiextensionBaseChange
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsotropicGroupLatticeClassRepresentatives
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.ZCount

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have key : ∀ (K : Type) [Field K] [Algebra O K], Module.finrank K (K ⊗[O] M) =
      Module.rankAtStalk M (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O) := fun K _ _ => by
    have h := Module.rankAtStalk_baseChange (R := O) (M := M) (S := K) ⟨⊥, Ideal.isPrime_bot⟩
    rw [Module.rankAtStalk_eq_finrank_of_free] at h
    exact h.trans ((Module.isLocallyConstant_rankAtStalk (R := O) (M := M)).apply_eq_of_preconnectedSpace _ _)
  rw [key k, ← key (FractionRing O), (TensorProduct.isBaseChange O M (FractionRing O)).finrank_eq]

theorem exists_basis_mod (O M : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] (m : O) [Finite (O ⧸ Ideal.span {m})] (r : ℕ)
    (hr : Module.finrank O M = r) :
    ∃ e : Fin r → M, (∀ x : M, ∃ (c : Fin r → O) (y : M), x = ∑ k, c k • e k + m • y) ∧
      ∀ (c : Fin r → O) (y : M), ∑ k, c k • e k = m • y → ∀ k, m ∣ c k := by
  set I : Ideal O := Ideal.span {m} with hI
  have : Finite (Ideal (O ⧸ I)) := Finite.of_injective _ SetLike.coe_injective
  have : Finite (MaximalSpectrum (O ⧸ I)) :=
    Finite.of_injective (fun P => P.asIdeal) fun _ _ h => MaximalSpectrum.ext h
  obtain ⟨B⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (O ⧸ I) ((O ⧸ I) ⊗[O] M) r fun P => by
    let := P.isMaximal
    let := Ideal.Quotient.field P.asIdeal
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O (O ⧸ I) ((O ⧸ I) ⧸ P.1) ((O ⧸ I) ⧸ P.1) M).finrank_eq,
      finrank_fibre, hr]
  have hs : Function.Surjective (TensorProduct.mk O (O ⧸ I) M 1) :=
    TensorProduct.mk_surjective O M (O ⧸ I) Ideal.Quotient.mk_surjective
  have hk : ∀ x : M, TensorProduct.mk O (O ⧸ I) M 1 x = 0 ↔ ∃ y, x = m • y := fun x => by
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff, TensorProduct.mk_apply,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero, hI,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨y, _, h⟩ => ⟨y, h.symm⟩, fun ⟨y, h⟩ => ⟨y, trivial, h.symm⟩⟩
  choose e he using fun k => hs (B k)
  have hc : ∀ c : Fin r → O, TensorProduct.mk O (O ⧸ I) M 1 (∑ k, c k • e k) =
      ∑ k, Ideal.Quotient.mk I (c k) • B k := fun c => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, he, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
  refine ⟨e, fun x => ?_, fun c y h k => ?_⟩
  · choose c hc' using fun k => Ideal.Quotient.mk_surjective (B.repr (TensorProduct.mk O (O ⧸ I) M 1 x) k)
    obtain ⟨y, hy⟩ := (hk (x - ∑ k, c k • e k)).1 (by
      rw [map_sub, hc]
      simp only [hc']
      rw [B.sum_repr, sub_self])
    exact ⟨c, y, by rw [← hy]; abel⟩
  · have h0 := (hk _).2 ⟨y, h⟩
    rw [hc] at h0
    have := Fintype.linearIndependent_iff.1 B.linearIndependent _ h0 k
    rwa [Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton] at this

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem mem_stdLat (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (u b : E) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  constructor
  · intro h
    choose u hu using h
    exact ⟨u, fun b => (hu b).symm⟩
  · rintro ⟨u, hu⟩ b
    exact ⟨u b, (hu b).symm⟩

theorem mem_smul_stdLat (N : ℕ) (v : Fin n → E) :
    v ∈ Ideal.span {(N : 𝓞 E)} • stdLat E n ↔ ∃ u : Fin n → 𝓞 E, ∀ b, v b = (N : E) * (u b : E) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨u, hu⟩ := (mem_stdLat w).1 hw
    exact ⟨u, fun b => by simp [hu, Algebra.smul_def]⟩
  · rintro ⟨u, hu⟩
    exact ⟨fun b => u b, (mem_stdLat _).2 ⟨u, fun _ => rfl⟩, funext fun b => by simp [hu, Algebra.smul_def]⟩

theorem mul_integral [IsCMField E] (Λ : GenLat E n) (N : ℕ) (hU : Λ.Unimod)
    (hN : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La) (w : Fin n → E) (hw : w ∈ Λ.La) :
    ∃ v : Fin n → 𝓞 E, ∀ b, (v b : E) = (N : E) * w b := by
  have h : ∀ b, ∃ a : 𝓞 E, (a : E) = (N : E) * w b := fun b => by
    have hb : (Pi.single b (N : E) : Fin n → E) ∈ Λ.La := hN ((mem_smul_stdLat N _).2
      ⟨Pi.single b 1, fun j => by
        by_cases hj : j = b
        · subst hj; simp
        · simp [hj]⟩)
    obtain ⟨a, ha⟩ := (hU _).1 hb w hw
    refine ⟨a, ha.trans ?_⟩
    rw [Finset.sum_eq_single b (fun j _ hj => by simp [hj]) (by simp)]
    simp
  choose v hv using h
  exact ⟨v, hv⟩

end

theorem exists_class_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∃ zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → Dw.La, (∀ i₀, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • zz i₀ j))) ∧ (∀ i i', (∀ b, Dw.ModN (N ^ 2) (zz i b - zz i' b)) → i = i') ∧ ∀ a : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) → ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) → ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • a j)) → ∃ i, ∀ b, Dw.ModN (N ^ 2) (a b - zz i b) := by
  intro E _ _ _ H Dw n Λ N hU hN0 hN
  have := Dw.fin
  have := Dw.proj
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have hNO : (N : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hN0.ne'
  have : Finite (𝓞 E ⧸ Ideal.span {(N : 𝓞 E) ^ 2}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hN0.ne')
  obtain ⟨e, he1, he2⟩ := exists_basis_mod (𝓞 E) Dw.La ((N : 𝓞 E) ^ 2) (Dw.p + Dw.q) Dw.rank
  set K := (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup with hK
  choose V hV using fun w : Λ.La.toAddSubgroup => mul_integral Λ N hU hN w.1 w.2
  have hKV : ∀ w w' : Λ.La.toAddSubgroup, (w : Λ.La.toAddSubgroup ⧸ K) = w' ↔
      ∀ b, (N : 𝓞 E) ^ 2 ∣ V w' b - V w b := fun w w' => by
    rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      mem_smul_stdLat]
    constructor
    · rintro ⟨u, hu⟩ b
      refine ⟨u b, RingOfIntegers.ext ?_⟩
      have := hu b
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply] at this
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2]
      linear_combination (N : E) * this
    · intro h
      choose u hu using h
      refine ⟨u, fun b => mul_left_cancel₀ hNE ?_⟩
      have := congrArg (algebraMap (𝓞 E) E) (hu b)
      have e1 := hV w b
      have e2 := hV w' b
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      rw [map_sub, map_mul, map_pow, map_natCast, e1, e2] at this
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, Pi.add_apply, Pi.neg_apply]
      linear_combination this
  have : Finite (Λ.La.toAddSubgroup ⧸ K) :=
    Finite.of_injective (fun q b => Ideal.Quotient.mk (Ideal.span {(N : 𝓞 E) ^ 2}) (V q.out b))
      fun q q' h => by
        rw [← q.out_eq, ← q'.out_eq]
        refine (hKV _ _).2 fun b => ?_
        rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
        exact (congrFun h b).symm
  have hcard : Nat.card (Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup ⧸ K) = Λ.zCard N (Dw.p + Dw.q) := by
    rw [Nat.card_fun, Nat.card_fin]
    rfl
  let σ := (Finite.equivFinOfCardEq hcard).symm
  have hM : ∀ x : Dw.La, Dw.ModN (N ^ 2) x ↔ ∃ y, x = ((N : 𝓞 E) ^ 2) • y := fun x => by
    simp only [Datum.ModN, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine ⟨fun i b => ∑ k, V (σ i k).out b • e k, fun i => ?_, fun i i' h => ?_, fun a ha => ?_⟩
  · exact (_root_.GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN0 hN _).2
      ⟨_, e, fun k => V (σ i k).out, fun k => ⟨_, (σ i k).out.2, hV _⟩, fun _ => rfl⟩
  · refine σ.injective (funext fun k => ?_)
    rw [← (σ i k).out_eq, ← (σ i' k).out_eq]
    refine ((hKV _ _).2 fun b => ?_).symm
    obtain ⟨y, hy⟩ := (hM _).1 (h b)
    refine he2 (fun k => V (σ i k).out b - V (σ i' k).out b) y ?_ k
    rw [← hy, ← Finset.sum_sub_distrib]
    simp only [sub_smul]
  · obtain ⟨m, x, v, hv, hav⟩ := (_root_.GlobalTheory.modN_sq_iff_exists_genLat_sum E H Dw n Λ N hU hN0 hN a).1 ha
    choose w hw hvw using hv
    choose c y hcy using fun i => he1 (x i)
    let W : Fin (Dw.p + Dw.q) → Λ.La.toAddSubgroup := fun k =>
      ⟨∑ i, c i k • w i, Λ.La.sum_mem fun i _ => Λ.La.smul_mem _ (hw i)⟩
    have hW : ∀ k b, V (W k) b = ∑ i, v i b * c i k := fun k b => by
      refine RingOfIntegers.ext ?_
      rw [hV]
      simp only [RingOfIntegers.coe_eq_algebraMap] at *
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [W, map_sum, map_mul, hvw, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    refine ⟨σ.symm fun k => (W k : Λ.La.toAddSubgroup ⧸ K), fun b => (hM _).2 ?_⟩
    simp only [Equiv.apply_symm_apply]
    choose t ht using fun k => (hKV _ (W k)).1 (QuotientAddGroup.out_eq' (W k : Λ.La.toAddSubgroup ⧸ K)) b
    refine ⟨∑ k, t k • e k + ∑ i, v i b • y i, ?_⟩
    have h1 : a b = ∑ k, V (W k) b • e k + (N : 𝓞 E) ^ 2 • ∑ i, v i b • y i := by
      rw [hav b]
      simp only [hW, Finset.sum_smul]
      rw [Finset.sum_comm, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcy i, smul_add, Finset.smul_sum, smul_comm (v i b)]
      simp only [mul_smul]
    rw [h1, smul_add, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← sub_smul, ht, mul_smul]

end GlobalTheory.ZCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPullback

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (hz : r z ∈ V)
    (a : Γ(X, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  have key : X.presheaf.map (homOfLE hle).op ≫ r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z hz =
      r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z (hle hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res pullU
  rw [dite_eq_left hz, dite_eq_left (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom (a : Γ(X, U))) key

private theorem exists_isGen_linComb_val_eq_of_eq {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val t' r z J = val t r z J := by
  subst hφ
  exact ⟨t, ht, fun _ _ _ _ => rfl⟩

theorem whiskerRight_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  unfold translPt
  rw [← Category.assoc, comp_lift]
  simp

theorem translT_whiskerRight {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  ext <;> simp [translT, whiskerRight_translPt]

theorem negT_whiskerRight {T T' : Over S} (h : T' ⟶ T) :
    negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  ext <;> simp [negT]

theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j : Fin n,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  have e : ∀ j : Fin n, val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J =
      val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j : ℕ))).left) r z J := fun j => (val_pull hJ _ _ r).symm
  rw [Finset.prod_congr rfl fun j _ => e j]
  unfold powGen val
  dsimp only
  erw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact gm_res_eq_gm _ _ _ (hJ.mem _ r) _

theorem val_symGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J *
        (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  rw [val_mul hJ, val_mul hJ, val_inv]
  have e1 := val_mul hJ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) ν r
  have e2 := val_pull hJ θ.φ (translT A θ.pt⁻¹).left r
  have e3 := val_pull hJ θ.φ (negT A T).left r
  have e4 := val_pull hJ ν (translT A θ.pt⁻¹).left r
  rw [e1, e2, e3, e4]

theorem exists_thetaGrp_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  intro S A _ _ L hL k T T' h θ
  have hφ : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) b) =
      ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left] := by
    funext b
    fin_cases b
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, whiskerRight_snd]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← Over.comp_left, whiskerRight_translPt]
  obtain ⟨φ', gφ', vφ'⟩ :=
    exists_isGen_linComb_val_eq_of_eq hφ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ θ.φ θ.3 (h ▷ A).left)
  have vθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val φ' r z J = val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (h ▷ A).left) z J :=
    fun Z r z J hJ => (vφ' Z r z J).trans (val_pull hJ _ _ r)
  have hcorr : LB.Gen.Corr L _ _ _ _ φ' (LB.pullGen L _ _ θ.φ (h ▷ A).left) :=
    corr_of_val hL fun y J _ => vφ' _ _ y J
  have hpow : ∀ j : ℕ, h ≫ θ.pt ^ j = (h ≫ θ.pt) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, comp_mul, ih]
  have hinv : h ≫ θ.pt⁻¹ = (h ≫ θ.pt)⁻¹ := GrpObj.comp_inv h θ.pt
  refine ⟨⟨h ≫ θ.pt, φ', gφ'⟩, rfl, hcorr, ?_, ?_⟩
  · intro n x hs
    obtain ⟨hpt, hpw, nu, gnu, hsym⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · show h ≫ θ.pt = h ≫ x
      rw [hpt]
    · refine corr_of_val hL fun y J hJ => ?_
      have hθ1 := val_corr hJ hpw (h ▷ A).left
      rw [val_one, val_powGen _ _ _ hJ] at hθ1
      rw [val_one, val_powGen _ _ _ hJ, ← hθ1]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only
      rw [vθ _ _ _ _ hJ]
      have e : (𝟙 _ ≫ (translT A ((h ≫ θ.pt) ^ (j : ℕ))).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A (θ.pt ^ (j : ℕ))).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hpow, translT_whiskerRight]
      rw [e]
    · have hφn : (fun b => (h ▷ A).left ≫
            (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) b) =
          ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] := by
        funext b
        fin_cases b
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [← Over.comp_left, whiskerRight_snd]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← Over.comp_left, whiskerRight_snd_assoc]
      obtain ⟨nu', gnu', vnu'⟩ :=
        exists_isGen_linComb_val_eq_of_eq hφn _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ nu gnu (h ▷ A).left)
      have vnu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
          val nu' r z J = val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
            (ε := ![k, -k]) nu (r ≫ (h ▷ A).left) z J :=
        fun Z r z J hJ => (vnu' Z r z J).trans (val_pull hJ _ _ r)
      refine ⟨nu', gnu', corr_of_val hL fun y J hJ => ?_⟩
      have hθ2 := val_corr hJ hsym (h ▷ A).left
      rw [val_one, val_symGen _ _ _ hJ] at hθ2
      rw [val_one]
      refine (val_symGen _ _ _ hJ).trans ?_
      rw [← hθ2]
      dsimp only
      rw [vθ _ _ _ _ hJ, vθ _ _ _ _ hJ, vnu _ _ _ _ hJ, vnu _ _ _ _ hJ]
      have e1 : (𝟙 _ ≫ (translT A (h ≫ θ.pt)⁻¹).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hinv, translT_whiskerRight]
      have e3 : (𝟙 _ ≫ (negT A T').left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (negT A T).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, negT_whiskerRight]
      rw [e1, e3, Category.id_comp]
  · intro s t s' t' hact hs ht
    unfold IsActOf at hact ⊢
    exact GlobalTheory.TwistBaseChange.isTwistPull_baseChange S A L hL T T' h _ _ _ _ _ _
      (translT_whiskerRight h θ.pt) k k θ.φ φ' θ.3 gφ' hcorr s t s' t' hact hs ht

end GlobalTheory.ThetaPullback
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HarmonicValueBaseChange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HarmonicValueBaseChange


set_option maxHeartbeats 1000000 in
theorem sum_map_of_harmA (hC : ChartIndepSt2) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] (nab : NabV Xo c)
    (hnab : IsNab Xo c nab) {S S' : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S]
    [CommRing S'] [Algebra c.F S'] [Algebra ℚ S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S')
    (hm : FrMap ψ y y') (h : ptO Xo y'.x ⟶ ptO Xo y.x) (hh : h.left = spMap ψ.toRingHom)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) (K : ℤ) (k : ℕ)
    (hK : K = k) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y.x)))
    (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L K (ptO Xo y'.x)))
    (hF' : ∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L K (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) :
    ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y K (F b) (colOf m b)) =
      ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' K (F' b) (colOf m b) := by
  subst hK
  obtain ⟨hstar, hnabC⟩ := hnab
  obtain ⟨C, hex, hval⟩ := hnabC S y
  choose f hf using fun b => hex k (F b)
  rcases y' with ⟨x1, xo, u1, tn, eg, bs, s1, gn⟩
  obtain ⟨hx, hu, -⟩ := hm
  subst hx
  have hu' : u1 = fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i := by
    funext τ i
    exact hu τ i
  subst hu'
  have hh' : h = ptBC ψ.toRingHom y.x := by
    apply Over.OverMorphism.ext
    rw [hh]
    rfl
  subst hh'
  obtain ⟨B', x', e', -, hG, hA, -, -, -, -, hch, hfr, hga, hrig, hgerm⟩ :=
    _root_.GlobalTheory.rawChart_baseChange E H Dw l Xo c S S' ψ y.x y.u (Formalism.MainNotions.ModuliIntegralCharts.H1.ChartAt.toRaw C)
  let C' : ChartAt Xo c ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') :=
    { d := C.d, B := B', uvec := fun ℓ j => ψ (C.uvec ℓ j), x := x', e := e', wP := C.wP, h := MvPowerSeries.map ψ.toRingHom C.h, chart := ⟨hch.zero, hch.trunc, hch.law, hch.act, hch.tan, hch.basis⟩, frame := ⟨hfr.gen, hfr.ph1, hfr.ph2, hfr.sy, hfr.ad⟩, prim := C.prim, gauge := hga, rig0 := hrig }
  have hf' : ∀ b, IsGerm ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') C'.d C'.x C'.B.A.act C'.e C'.wP k (F' b)
      (MvPowerSeries.map ψ.toRingHom (f b)) := by
    intro b
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.isGerm_iff_raw]
    exact hgerm k (F b) (F' b) (f b) (hF' b)
      ((Formalism.MainNotions.ModuliIntegralCharts.H1.isGerm_iff_raw y C.d C.x C.B.A.act C.e C.wP k (F b) (f b)).1 (hf b))
  obtain ⟨C2, hex2, hval2⟩ := hnabC S' ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S')
  choose f2 hf2 using fun b => hex2 k (F' b)
  have hCI := hC E H Dw l Xo c hstar S' ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') C' C2 k n F' (fun b => MvPowerSeries.map ψ.toRingHom (f b)) f2
    hf' hf2 a P hP
  unfold Formalism.MainNotions.ModuliIntegralCharts.H1.chartVal at hCI
  have e1 : ∀ b α, nab y (k : ℤ) (F b) α =
      C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial α 1) :=
    fun b α => hval k (F b) (f b) (hf b) α
  have e2 : ∀ b α, nab ({ x := spMap ψ.toRingHom ≫ y.x, x_over := xo, u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i, tan := tn, eig := eg, basis := bs, s := s1, gen := gn } : FrPt Xo c S') (k : ℤ) (F' b) α =
      C2.B.nabVal S' C2.h H.w0 k (f2 b) C2.uvec (MvPolynomial.monomial α 1) :=
    fun b α => hval2 k (F' b) (f2 b) (hf2 b) α
  simp only [e1, e2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hCI, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_prod, AlgHom.commutes]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  have hmap := nabMap_holds S S' ψ.toRingHom C.d (𝓞 E) C.B B' hG hA C.h C.gauge H.w0 k (f b) (Lt1 Dw)
    C.uvec (MvPolynomial.monomial (colOf m b) 1)
  rw [MvPolynomial.map_monomial, map_one] at hmap
  exact hmap.symm

end GlobalTheory.HarmonicValueBaseChange

namespace GlobalTheory

theorem harmonicValue_baseChange : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (nab : NabV Xo c), IsNab Xo c nab → ∀ (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra c.F S'] (ψ : S →ₐ[c.F] S') (y : FrPt Xo c S) (y' : FrPt Xo c S'), FrMap ψ y y' → ∀ (h : ptO Xo y'.x ⟶ ptO Xo y.x), h.left = spMap ψ.toRingHom → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∀ (N : ℕ) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))) (F' : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y'.x))), (∀ b, IsPullSec Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (h ▷ Xo.univ.t.G) (whiskerRight_snd _ _) (F b) (F' b)) → ψ (∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y ((N : ℤ) ^ 2) (F b) (colOf m b)) = ∑ m ∈ P.support, algebraMap c.F S' (P.coeff m) * ∏ b, nab y' ((N : ℤ) ^ 2) (F' b) (colOf m b) := by
  intro hC E _ _ _ H Dw l Xo c _ nab hnab S S' _ _ _ _ ψ y y' hm h hh a n P hP N F F' hF'
  let _ : Algebra ℚ S := ((algebraMap c.F S).comp (algebraMap ℚ c.F)).toAlgebra
  let _ : Algebra ℚ S' := ((algebraMap c.F S').comp (algebraMap ℚ c.F)).toAlgebra
  obtain ⟨D, hD0, hDi⟩ := exists_integral_multiples ℤ ℚ (P.support.image fun m => P.coeff m)
  have hsupp : (D • P).support = P.support := MvPolynomial.support_smul_eq hD0 P
  have hQ1 : D • P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) := by
    unfold HHa at hP ⊢
    simp only [Set.mem_ofPred_eq] at hP ⊢
    obtain ⟨hker, hrow, hdeg⟩ := hP
    refine ⟨zsmul_mem hker D, fun σ i i' hi t => ?_, fun m hm => hdeg m (hsupp ▸ hm)⟩
    rw [map_zsmul, hrow σ i i' hi t]
  have hQ : D • P ∈ harmA c a n := by
    unfold harmA HaO
    simp only [Set.mem_ofPred_eq]
    refine ⟨hQ1, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul]
    by_cases hmem : m ∈ P.support
    · exact hDi _ (Finset.mem_image_of_mem _ hmem)
    · have h0 : P.coeff m = 0 := by simpa using hmem
      rw [h0, smul_zero]
      exact zero_mem _
  have key := HarmonicValueBaseChange.sum_map_of_harmA hC nab hnab ψ y y' hm h hh a n (D • P) hQ
    ((N : ℤ) ^ 2) (N ^ 2) (by push_cast; ring) F F' hF'
  rw [hsupp] at key
  simp only [MvPolynomial.coeff_smul, map_zsmul, smul_mul_assoc, ← Finset.smul_sum] at key
  simp only [zsmul_eq_mul] at key
  have hu : IsUnit (D : S') := by
    rw [← map_intCast (algebraMap c.F S') D]
    exact (IsUnit.mk0 _ (Int.cast_ne_zero.2 hD0)).map _
  exact hu.mul_left_cancel key

end GlobalTheory
end

